/*
 * TinyEXR v3 WASM viewer — application logic.
 *
 * Flow:
 *   file/drop -> read bytes (with progress) -> exrv_open + header JSON
 *             -> exrv_select(part,level) -> per-block decode loop (progress)
 *             -> copy RGBA floats out of the WASM heap -> WebGL2 float texture.
 *
 * Tone-mapping (exposure / gamma / sRGB), channel isolation, and zoom/pan all
 * happen in the fragment shader, so they are instant and never re-decode. The
 * pixel picker reads raw floats straight from the JS-side copy of the buffer.
 */

import createModule from "./exr_viewer.mjs";
import { unzipSync } from "./fflate.module.js";

/* ------------------------------------------------------------------ globals */
let M = null;             // emscripten module
let handle = 0;           // current exrv session handle
let header = null;        // parsed header JSON
let sel = { part: 0, lx: 0, ly: 0, view: 0 };
let views = [];           // channel-view options for the current part

let mode = "2d";          // "2d" flat image, "3d" deep cloud, or "spectral"
// spectral state (mode === "spectral"): the WASM side holds the wavelength cube
let specWl = null;        // Float32Array of wavelengths (nm), ascending
let specNwl = 0;          // number of wavelength bands
let specWi = 0;           // current wavelength index
let specColor = false;    // CIE→sRGB composite vs single-wavelength grayscale
let specDims = { w: 0, h: 0 };
let lastSpecPixel = null; // { x, y, spec: Float32Array } last hovered pixel
// deep 3D state
let prog3d = null, uni3d = null, vbo3d = null, deepN = 0, deepBounds = null;
let cam = { az: 0.5, el: -0.32, dist: 2.2, panX: 0, panY: 0 };
let deepCtl = { pointSize: 2, rgb: false, exposure: 0 };
let img = null;           // { w, h, data: Float32Array(rgba) }
let fileName = null;      // name of the currently loaded file (for info panel)
let dwMin = { x: 0, y: 0 };
let dispWin = null;       // {minX,minY,maxX,maxY} of selected part

// view transform, in device pixels: screen = pan + imagePx * zoom
let view = { zoom: 1, panX: 0, panY: 0 };

// display controls
let ctl = { exposure: 0, gamma: 2.2, srgb: true, channel: 0,
            falseColor: false, showDisp: true, cropDisp: false };

// region of interest, in image pixels (level space), or null
let roi = null;

const dpr = () => window.devicePixelRatio || 1;
const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
const raf = () => new Promise((r) => requestAnimationFrame(r));

/* ------------------------------------------------------------------- WebGL */
let gl, prog, vbo, tex, uni;

const VS = `#version 300 es
in vec2 aPos; in vec2 aUV; out vec2 vUV;
void main(){ vUV = aUV; gl_Position = vec4(aPos, 0.0, 1.0); }`;

const FS = `#version 300 es
precision highp float;
in vec2 vUV; out vec4 frag;
uniform sampler2D uTex;
uniform float uExposure, uGamma;
uniform int uSRGB, uChannel, uFalse;
vec3 toSRGB(vec3 c){
  c = clamp(c, 0.0, 1.0);
  return mix(12.92*c, 1.055*pow(c, vec3(1.0/2.4)) - 0.055, step(0.0031308, c));
}
// Perceptually-uniform viridis colormap (polynomial approximation).
vec3 viridis(float t){
  t = clamp(t, 0.0, 1.0);
  const vec3 c0 = vec3(0.2777273272234177, 0.005407344544966578, 0.3340998053353061);
  const vec3 c1 = vec3(0.1050930431085774, 1.404613529898575, 1.384590162594685);
  const vec3 c2 = vec3(-0.3308618287255563, 0.214847559468213, 0.09509516302823659);
  const vec3 c3 = vec3(-4.634230498983486, -5.799100973351585, -19.33244095627987);
  const vec3 c4 = vec3(6.228269936347081, 14.17993336680509, 56.69055260068105);
  const vec3 c5 = vec3(4.776384997670288, -13.74514537774601, -65.35303263337234);
  const vec3 c6 = vec3(-5.435455855934631, 4.645852612178535, 26.3124352495832);
  return c0+t*(c1+t*(c2+t*(c3+t*(c4+t*(c5+t*c6)))));
}
// Tone-map a scalar to display [0,1] using the same curve as the RGB path.
float tone(float s){
  s = max(s, 0.0);
  return (uSRGB == 1) ? toSRGB(vec3(s)).r : pow(clamp(s, 0.0, 1.0), 1.0 / uGamma);
}
void main(){
  vec4 t = texture(uTex, vUV);
  float e = uExposure;
  if (uChannel == 0) {                               // RGB
    vec3 c = max(t.rgb * e, 0.0);
    c = (uSRGB == 1) ? toSRGB(c) : pow(clamp(c, 0.0, 1.0), vec3(1.0 / uGamma));
    frag = vec4(c, 1.0);
    return;
  }
  float s;                                           // single scalar channel
  if      (uChannel == 1) s = t.r * e;
  else if (uChannel == 2) s = t.g * e;
  else if (uChannel == 3) s = t.b * e;
  else if (uChannel == 4) s = t.a;                   // alpha: no exposure
  else                    s = dot(t.rgb, vec3(0.2126,0.7152,0.0722)) * e;
  float d = tone(s);
  frag = (uFalse == 1) ? vec4(viridis(d), 1.0) : vec4(vec3(d), 1.0);
}`;

function compile(type, src) {
  const s = gl.createShader(type);
  gl.shaderSource(s, src);
  gl.compileShader(s);
  if (!gl.getShaderParameter(s, gl.COMPILE_STATUS))
    throw new Error("shader: " + gl.getShaderInfoLog(s));
  return s;
}

function initGL() {
  const canvas = document.getElementById("gl");
  gl = canvas.getContext("webgl2", { antialias: false, premultipliedAlpha: false });
  if (!gl) { showError("WebGL2 is not available in this browser."); return; }

  prog = gl.createProgram();
  gl.attachShader(prog, compile(gl.VERTEX_SHADER, VS));
  gl.attachShader(prog, compile(gl.FRAGMENT_SHADER, FS));
  gl.bindAttribLocation(prog, 0, "aPos");
  gl.bindAttribLocation(prog, 1, "aUV");
  gl.linkProgram(prog);
  if (!gl.getProgramParameter(prog, gl.LINK_STATUS))
    throw new Error("link: " + gl.getProgramInfoLog(prog));

  uni = {
    tex: gl.getUniformLocation(prog, "uTex"),
    exposure: gl.getUniformLocation(prog, "uExposure"),
    gamma: gl.getUniformLocation(prog, "uGamma"),
    srgb: gl.getUniformLocation(prog, "uSRGB"),
    channel: gl.getUniformLocation(prog, "uChannel"),
    falseColor: gl.getUniformLocation(prog, "uFalse"),
  };

  vbo = gl.createBuffer();
  tex = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, tex);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
}

function uploadTexture() {
  gl.bindTexture(gl.TEXTURE_2D, tex);
  gl.pixelStorei(gl.UNPACK_ALIGNMENT, 1);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA32F, img.w, img.h, 0,
                gl.RGBA, gl.FLOAT, img.data);
}

function syncCanvasSize() {
  const c = document.getElementById("gl");
  const o = document.getElementById("overlay");
  const w = Math.round(c.clientWidth * dpr());
  const h = Math.round(c.clientHeight * dpr());
  if (c.width !== w || c.height !== h) { c.width = w; c.height = h; }
  if (o.width !== w || o.height !== h) { o.width = w; o.height = h; }
}

function render() {
  if (!gl) return;
  if (mode === "3d") return render3d();
  syncCanvasSize();
  const W = gl.canvas.width, H = gl.canvas.height;
  gl.viewport(0, 0, W, H);
  gl.clearColor(0, 0, 0, 0);
  gl.clear(gl.COLOR_BUFFER_BIT);
  if (!img) { drawOverlay(); return; }

  // image rect in device pixels
  const x0 = view.panX, y0 = view.panY;
  const x1 = x0 + img.w * view.zoom, y1 = y0 + img.h * view.zoom;
  const cx = (x) => (x / W) * 2 - 1;
  const cy = (y) => 1 - (y / H) * 2;
  // strip: TL, TR, BL, BR  (pos.xy, uv.xy)
  const v = new Float32Array([
    cx(x0), cy(y0), 0, 0,
    cx(x1), cy(y0), 1, 0,
    cx(x0), cy(y1), 0, 1,
    cx(x1), cy(y1), 1, 1,
  ]);
  gl.useProgram(prog);
  gl.bindBuffer(gl.ARRAY_BUFFER, vbo);
  gl.bufferData(gl.ARRAY_BUFFER, v, gl.DYNAMIC_DRAW);
  gl.enableVertexAttribArray(0);
  gl.vertexAttribPointer(0, 2, gl.FLOAT, false, 16, 0);
  gl.enableVertexAttribArray(1);
  gl.vertexAttribPointer(1, 2, gl.FLOAT, false, 16, 8);

  gl.activeTexture(gl.TEXTURE0);
  gl.bindTexture(gl.TEXTURE_2D, tex);
  gl.uniform1i(uni.tex, 0);
  gl.uniform1f(uni.exposure, Math.pow(2, ctl.exposure));
  gl.uniform1f(uni.gamma, ctl.gamma);
  gl.uniform1i(uni.srgb, ctl.srgb ? 1 : 0);
  gl.uniform1i(uni.channel, ctl.channel);
  gl.uniform1i(uni.falseColor, (ctl.falseColor && ctl.channel !== 0) ? 1 : 0);
  gl.drawArrays(gl.TRIANGLE_STRIP, 0, 4);

  drawOverlay();
  updateZoomLabel();
  updateLegend();
}

// Set the active display channel and sync the segmented-button UI.
function setChannel(ch) {
  ctl.channel = ch;
  const seg = document.getElementById("channels");
  for (const x of seg.children)
    x.classList.toggle("active", parseInt(x.dataset.ch, 10) === ch);
  // False color only applies to a single scalar channel (not RGB).
  document.getElementById("falseColor").disabled = ch === 0;
}

// Channel labels for the false-color legend (index matches the channel buttons).
const CHANNEL_NAMES = ["RGB", "R", "G", "B", "A", "Lum"];

// Viridis colormap in JS — must match the shader's viridis() so the legend is
// an accurate key for the rendered false-color image.
function viridisRGB(t) {
  t = Math.min(Math.max(t, 0), 1);
  const c0 = [0.2777273272234177, 0.005407344544966578, 0.3340998053353061];
  const c1 = [0.1050930431085774, 1.404613529898575, 1.384590162594685];
  const c2 = [-0.3308618287255563, 0.214847559468213, 0.09509516302823659];
  const c3 = [-4.634230498983486, -5.799100973351585, -19.33244095627987];
  const c4 = [6.228269936347081, 14.17993336680509, 56.69055260068105];
  const c5 = [4.776384997670288, -13.74514537774601, -65.35303263337234];
  const c6 = [-5.435455855934631, 4.645852612178535, 26.3124352495832];
  const out = [];
  for (let i = 0; i < 3; i++) {
    const v = c0[i] + t * (c1[i] + t * (c2[i] + t * (c3[i] + t * (c4[i] + t * (c5[i] + t * c6[i])))));
    out.push(Math.round(Math.min(Math.max(v, 0), 1) * 255));
  }
  return out;
}

function initLegendGradient() {
  const stops = [];
  for (let i = 0; i <= 16; i++) {
    const t = i / 16;
    const [r, g, b] = viridisRGB(t);
    stops.push(`rgb(${r},${g},${b}) ${(t * 100).toFixed(1)}%`);
  }
  document.getElementById("legendBar").style.background =
    `linear-gradient(90deg, ${stops.join(", ")})`;
}

function updateLegend() {
  const legend = document.getElementById("legend");
  const show = !!img && ctl.falseColor && ctl.channel !== 0;
  legend.classList.toggle("hidden", !show);
  if (show)
    document.getElementById("legendChan").textContent = CHANNEL_NAMES[ctl.channel] || "";
}

/* image-pixel (level space) -> device-pixel screen coords */
function imgToScreen(ix, iy) {
  return [view.panX + ix * view.zoom, view.panY + iy * view.zoom];
}
function screenToImg(sx, sy) {
  return [(sx - view.panX) / view.zoom, (sy - view.panY) / view.zoom];
}

function drawOverlay() {
  const o = document.getElementById("overlay");
  const ctx = o.getContext("2d");
  ctx.clearRect(0, 0, o.width, o.height);
  if (!img) return;

  // crop-to-display mask: darken everything outside the display window
  if (ctl.cropDisp && dispWin) {
    const [mx0, my0] = imgToScreen(dispWin.minX - dwMin.x, dispWin.minY - dwMin.y);
    const [mx1, my1] = imgToScreen(dispWin.maxX - dwMin.x + 1, dispWin.maxY - dwMin.y + 1);
    ctx.save();
    ctx.fillStyle = "rgba(0,0,0,0.6)";
    ctx.beginPath();
    ctx.rect(0, 0, o.width, o.height);
    ctx.rect(mx0, my0, mx1 - mx0, my1 - my0);
    ctx.fill("evenodd");
    ctx.restore();
  }

  // display-window outline
  if (ctl.showDisp && dispWin) {
    const [dx0, dy0] = imgToScreen(dispWin.minX - dwMin.x, dispWin.minY - dwMin.y);
    const [dx1, dy1] = imgToScreen(dispWin.maxX - dwMin.x + 1, dispWin.maxY - dwMin.y + 1);
    ctx.strokeStyle = "#ffd24c";
    ctx.lineWidth = 1.5;
    ctx.setLineDash([6, 4]);
    ctx.strokeRect(dx0 + .5, dy0 + .5, dx1 - dx0 - 1, dy1 - dy0 - 1);
    ctx.setLineDash([]);
  }

  // region of interest
  if (roi) {
    const [rx0, ry0] = imgToScreen(roi.x0, roi.y0);
    const [rx1, ry1] = imgToScreen(roi.x1, roi.y1);
    ctx.strokeStyle = "#4c9aff";
    ctx.lineWidth = 1.5;
    ctx.strokeRect(rx0 + .5, ry0 + .5, rx1 - rx0 - 1, ry1 - ry0 - 1);
    ctx.fillStyle = "rgba(76,154,255,0.12)";
    ctx.fillRect(rx0, ry0, rx1 - rx0, ry1 - ry0);
  }
}

/* --------------------------------------------------------------- view ops */
function fitView() {
  if (!img) return;
  const c = gl.canvas;
  const z = Math.min(c.width / img.w, c.height / img.h) * 0.96;
  view.zoom = z > 0 ? z : 1;
  view.panX = (c.width - img.w * view.zoom) / 2;
  view.panY = (c.height - img.h * view.zoom) / 2;
  render();
}
function oneToOne() {
  if (!img) return;
  const c = gl.canvas;
  view.zoom = dpr(); // 1 image px = 1 css px
  view.panX = (c.width - img.w * view.zoom) / 2;
  view.panY = (c.height - img.h * view.zoom) / 2;
  render();
}
function zoomToRegion() {
  if (!roi || !img) return;
  const c = gl.canvas;
  const rw = roi.x1 - roi.x0, rh = roi.y1 - roi.y0;
  if (rw < 1 || rh < 1) return;
  view.zoom = Math.min(c.width / rw, c.height / rh) * 0.95;
  view.panX = (c.width - (roi.x0 + roi.x1) * view.zoom) / 2;
  view.panY = (c.height - (roi.y0 + roi.y1) * view.zoom) / 2;
  render();
}
function updateZoomLabel() {
  const pct = Math.round((view.zoom / dpr()) * 100);
  document.getElementById("zoomLabel").textContent = pct + "%";
}

/* ----------------------------------------------------------------- decode */
function setProgress(pct, label) {
  const wrap = document.getElementById("progressWrap");
  wrap.classList.toggle("hidden", pct >= 100 || pct < 0);
  document.getElementById("progressBar").style.width = clamp(pct, 0, 100) + "%";
  document.getElementById("progressLabel").textContent = label || "";
}

function readFileWithProgress(file) {
  return new Promise((resolve, reject) => {
    const fr = new FileReader();
    fr.onprogress = (e) => {
      if (e.lengthComputable)
        setProgress((e.loaded / e.total) * 100, "Reading… " +
          Math.round((e.loaded / e.total) * 100) + "%");
    };
    fr.onload = () => resolve(new Uint8Array(fr.result));
    fr.onerror = () => reject(fr.error || new Error("read failed"));
    fr.readAsArrayBuffer(file);
  });
}

// Fetch a URL into a Uint8Array, streaming download progress when the server
// reports a Content-Length (e.g. the remote asakusa.exr).
async function fetchUrlWithProgress(url, what) {
  const resp = await fetch(url);
  if (!resp.ok) throw new Error(resp.status + " " + resp.statusText);
  const total = +resp.headers.get("content-length");
  if (!resp.body || !total) {
    setProgress(0, "Fetching " + what + "…");
    return new Uint8Array(await resp.arrayBuffer());
  }
  const reader = resp.body.getReader();
  const buf = new Uint8Array(total);
  let off = 0;
  for (;;) {
    const { done, value } = await reader.read();
    if (done) break;
    buf.set(value, off);
    off += value.length;
    setProgress((off / total) * 100,
      "Fetching " + what + "… " + Math.round((off / total) * 100) + "%");
  }
  return off === total ? buf : buf.subarray(0, off);
}

async function loadBytes(bytes, name) {
  hideError();
  fileName = name || null;
  if (handle) { M._exrv_close(handle); handle = 0; img = null; }

  const p = M._malloc(bytes.length);
  M.HEAPU8.set(bytes, p);
  handle = M._exrv_open(p, bytes.length);
  M._free(p);
  if (!handle) { setProgress(-1); showError("Not a valid EXR file."); return; }

  const jp = M._exrv_header_json(handle);
  header = JSON.parse(M.UTF8ToString(jp));
  M._exrv_free(jp);

  document.getElementById("dropzone").classList.add("hidden");
  document.getElementById("ctrls").classList.remove("hidden");
  document.getElementById("info").classList.remove("hidden");
  document.getElementById("viewbar").classList.remove("hidden");

  buildPartSelector();
  views = [];                 // force a fresh channel-view list for the new file
  if (header.parts[0] && header.parts[0].deep) await enterDeepMode(0);
  else if (header.parts[0] && header.parts[0].spectral) await enterSpectralMode(0);
  else await selectAndDecode(0, 0, 0, true);
}

async function selectAndDecode(part, lx, ly, doFit, viewIdx) {
  // Clear the canvas immediately so a part/view switch doesn't leave the old
  // image (or a partially-decoded frame) on screen while the new one decodes.
  set2DMode();
  img = null; render();

  roi = null;
  updateRoiUI();
  const ph = header.parts[part];
  dwMin = { x: ph.dataWindow.minX, y: ph.dataWindow.minY };
  dispWin = ph.displayWindow;

  // Rebuild the channel-view list when the part changes; otherwise keep it.
  const partChanged = sel.part !== part || views.length === 0;
  if (partChanged) { views = buildViews(ph); buildChannelSelector(); }
  if (viewIdx === undefined) viewIdx = partChanged ? 0 : (sel.view || 0);
  if (viewIdx < 0 || viewIdx >= views.length) viewIdx = 0;
  sel = { part, lx, ly, view: viewIdx };
  document.getElementById("channelSel").value = String(viewIdx);

  const v = views[viewIdx];
  // Reconstructed luminance-chroma color goes through a dedicated entry point
  // (whole-part decode); if it can't reconstruct, fall back to the grayscale-Y
  // channel mapping in v.c.
  let total;
  if (v.ycc) {
    total = M._exrv_select_ycc(handle, part, lx, ly);
    if (total < 0)
      total = M._exrv_select_channels(handle, part, lx, ly,
        v.c[0], v.c[1], v.c[2], v.c[3]);
  } else {
    total = M._exrv_select_channels(handle, part, lx, ly,
      v.c[0], v.c[1], v.c[2], v.c[3]);
  }
  if (total < 0) {
    setProgress(-1);
    img = null; render();
    showError(ph.deep ? "Deep EXR parts are not supported by this viewer."
                      : "Unable to decode this part/level.");
    renderInfo();
    return;
  }
  const w = M._exrv_level_width(handle), h = M._exrv_level_height(handle);

  setProgress(0, "Decoding 0%");
  const chunk = Math.max(1, Math.ceil(total / 100));
  for (let i = 0; i < total; i++) {
    if (M._exrv_decode_block(handle, i) < 0) {
      setProgress(-1); showError("Decode error in block " + i + "."); break;
    }
    if (i % chunk === 0 || i === total - 1) {
      const pct = ((i + 1) / total) * 100;
      setProgress(pct, "Decoding " + Math.round(pct) + "%");
      await raf();
    }
  }
  setProgress(100);

  const ptr = M._exrv_rgba(handle);
  // copy out of the heap: HEAPF32 can detach on memory growth
  const data = M.HEAPF32.slice(ptr >> 2, (ptr >> 2) + w * h * 4);
  img = { w, h, data };
  uploadTexture();
  buildLevelSelector();
  renderInfo();
  if (doFit) fitView(); else render();
}

/* ----------------------------------------------------------------- picker */
function updatePixel(sx, sy) {
  const el = document.getElementById("pixel");
  if (!img) { el.classList.add("hidden"); return; }
  const [fx, fy] = screenToImg(sx, sy);
  const ix = Math.floor(fx), iy = Math.floor(fy);
  if (ix < 0 || iy < 0 || ix >= img.w || iy >= img.h) {
    el.classList.add("hidden");
    return;
  }
  const o = (iy * img.w + ix) * 4;
  const r = img.data[o], g = img.data[o + 1], b = img.data[o + 2], a = img.data[o + 3];
  const ax = ix + dwMin.x, ay = iy + dwMin.y;
  const f = (x) => (Math.abs(x) >= 1e4 || (Math.abs(x) < 1e-4 && x !== 0))
    ? x.toExponential(3) : x.toFixed(4);
  if (mode === "spectral") {
    el.textContent = specColor
      ? `x ${ax}  y ${ay}\nsRGB ${f(r)} ${f(g)} ${f(b)}`
      : `x ${ax}  y ${ay}\n${specWl[specWi].toFixed(1)} nm  ${f(r)}`;
    updateSpecPixel(ix, iy);
  } else {
    el.textContent =
      `x ${ax}  y ${ay}\nR ${f(r)}\nG ${f(g)}\nB ${f(b)}\nA ${f(a)}`;
  }
  el.classList.remove("hidden");
}

/* --------------------------------------------------------------- info ui */
function buildPartSelector() {
  const partSel = document.getElementById("partSel");
  partSel.innerHTML = "";
  header.parts.forEach((p, i) => {
    const opt = document.createElement("option");
    opt.value = i;
    opt.textContent = `${i}: ${p.name || "(unnamed)"} — ${p.type}`;
    partSel.appendChild(opt);
  });
  partSel.value = "0";
  partSel.parentElement.style.display = header.numParts > 1 ? "" : "none";
}

// Derive the selectable channel "views" for a part: conventional RGB(A),
// luminance-chroma (Y/RY/BY → color), named layers (prefix.R/G/B), a generic
// leading-channels-to-RGB for data parts, and every channel as grayscale.
// View.c holds header channel indices (matching p.channels order); -1 = unused.
function buildViews(p) {
  const ch = p.channels;
  const idx = (name) => ch.findIndex((c) => c.name === name);
  const primary = [];
  const R = idx("R"), G = idx("G"), B = idx("B"), A = idx("A");
  if (R >= 0 && G >= 0 && B >= 0)
    primary.push({ label: A >= 0 ? "RGBA" : "RGB", c: [R, G, B, A] });
  const Y = idx("Y");
  // Luminance-chroma (Y + subsampled RY/BY): offer a reconstructed full-color
  // view. ycc:true routes through _exrv_select_ycc (whole-part decode +
  // exr_part_yc_to_rgba_float) instead of the per-channel scatter. The c array
  // is the grayscale-Y fallback used if reconstruction is unavailable.
  const RY = idx("RY"), BY = idx("BY");
  if (Y >= 0 && RY >= 0 && BY >= 0 && R < 0 && G < 0 && B < 0)
    primary.push({ label: "Color (Y/RY/BY)", c: [Y, Y, Y, A], ycc: true });

  // Named layers: group channels by the prefix before the last '.'.
  const layers = new Map();
  ch.forEach((c, i) => {
    const dot = c.name.lastIndexOf(".");
    if (dot > 0) {
      const pre = c.name.slice(0, dot), suf = c.name.slice(dot + 1);
      if (!layers.has(pre)) layers.set(pre, {});
      layers.get(pre)[suf] = i;
    }
  });
  for (const [pre, m] of layers) {
    if (m.R !== undefined && m.G !== undefined && m.B !== undefined)
      primary.push({ label: `${pre} (RGB)`,
        c: [m.R, m.G, m.B, m.A !== undefined ? m.A : -1] });
  }

  if (!primary.length) {
    if (Y >= 0) primary.push({ label: "Y (luminance)", c: [Y, Y, Y, -1] });
    else if (ch.length >= 2) // motion vectors / disparity / generic data
      primary.push({ label: "Channels → RGB", c: [0, 1, ch.length >= 3 ? 2 : -1, -1] });
  }

  const individual = ch.map((c, i) => ({ label: `${c.name} (gray)`, c: [i, i, i, -1] }));
  return [...primary, ...individual];
}

function buildChannelSelector() {
  const channelSel = document.getElementById("channelSel");
  channelSel.innerHTML = "";
  views.forEach((v, i) => {
    const opt = document.createElement("option");
    opt.value = i;
    opt.textContent = v.label;
    channelSel.appendChild(opt);
  });
  channelSel.value = "0";
  // Hide the combo when there's only one trivial view (e.g. a plain RGB image).
  document.getElementById("channelView").style.display = views.length > 1 ? "" : "none";
}

function buildLevelSelector() {
  const levelSel = document.getElementById("levelSel");
  const p = header.parts[sel.part];
  levelSel.innerHTML = "";
  const levels = p.levels && p.levels.length ? p.levels : [[0, 0]];
  levels.forEach(([lx, ly]) => {
    const opt = document.createElement("option");
    opt.value = lx + "," + ly;
    opt.textContent = (lx === 0 && ly === 0) ? "0 (full)" : `${lx},${ly}`;
    levelSel.appendChild(opt);
  });
  levelSel.value = sel.lx + "," + sel.ly;
  levelSel.parentElement.style.display = levels.length > 1 ? "" : "none";
}

function esc(s) {
  return String(s).replace(/[&<>"]/g, (c) =>
    ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));
}
function kv(k, v) { return `<div class="kv"><span class="k">${k}</span><span class="v">${v}</span></div>`; }
function box(b) { return `[${b.minX}, ${b.minY}] → [${b.maxX}, ${b.maxY}]`; }

function renderInfo() {
  const p = header.parts[sel.part];
  const body = document.getElementById("infoBody");
  let h = "";
  if (fileName) h += kv("File", esc(fileName));
  h += kv("Parts", header.numParts);
  h += kv("Type", p.type + (p.tiled ? ` (${p.tileXSize}×${p.tileYSize} tiles, ${p.levelMode})` : ""));
  h += kv("Compression", p.compression);
  h += kv("Line order", p.lineOrder);
  h += kv("Resolution", `${p.width} × ${p.height}`);
  if (img && (img.w !== p.width || img.h !== p.height))
    h += kv("Level size", `${img.w} × ${img.h}`);
  h += kv("Data window", box(p.dataWindow));
  h += kv("Display window", box(p.displayWindow));
  h += kv("Pixel aspect", p.pixelAspect);
  h += `<div class="subhead">Channels (${p.channels.length})</div>`;
  h += `<table class="chan-table">`;
  for (const c of p.channels)
    h += `<tr><td>${c.name}</td><td>${c.type}${(c.xSampling !== 1 || c.ySampling !== 1) ? ` ${c.xSampling}×${c.ySampling}` : ""}</td></tr>`;
  h += `</table>`;
  body.innerHTML = h;
}

function updateRoiUI() {
  const wrap = document.getElementById("roiInfo");
  const btn = document.getElementById("btnZoomRegion");
  if (roi && (roi.x1 - roi.x0) >= 1 && (roi.y1 - roi.y0) >= 1) {
    wrap.classList.remove("hidden");
    btn.disabled = false;
    const ax0 = Math.round(roi.x0) + dwMin.x, ay0 = Math.round(roi.y0) + dwMin.y;
    const w = Math.round(roi.x1 - roi.x0), hh = Math.round(roi.y1 - roi.y0);
    document.getElementById("roiText").textContent =
      `origin ${ax0}, ${ay0}   size ${w} × ${hh}`;
  } else {
    wrap.classList.add("hidden");
    btn.disabled = true;
  }
}

/* ----------------------------------------------------------------- errors */
let errTimer = 0;
function showError(msg) {
  const t = document.getElementById("errorToast");
  t.textContent = msg;
  t.classList.remove("hidden");
  clearTimeout(errTimer);
  errTimer = setTimeout(() => t.classList.add("hidden"), 5000);
}
function hideError() { document.getElementById("errorToast").classList.add("hidden"); }

/* ------------------------------------------------------------------ input */
function setupInput() {
  const stage = document.getElementById("stage");
  const glc = document.getElementById("gl");

  // file picker
  document.getElementById("file").addEventListener("change", async (e) => {
    const f = e.target.files[0];
    if (f) loadBytes(await readFileWithProgress(f), f.name);
  });

  // sample
  document.getElementById("btnSample").addEventListener("click", async () => {
    try {
      setProgress(0, "Fetching sample.exr…");
      const resp = await fetch("sample.exr");
      if (!resp.ok) throw new Error("sample.exr not found");
      loadBytes(new Uint8Array(await resp.arrayBuffer()), "sample.exr");
    } catch (err) {
      setProgress(-1);
      showError("Place an EXR named sample.exr next to index.html (see README).");
    }
  });

  // bundled spectral sample (16-band emissive), next to index.html
  document.getElementById("btnSpectralSample").addEventListener("click", async () => {
    try {
      setProgress(0, "Fetching spectral_sample.exr…");
      const resp = await fetch("spectral_sample.exr");
      if (!resp.ok) throw new Error("spectral_sample.exr not found");
      loadBytes(new Uint8Array(await resp.arrayBuffer()), "spectral_sample.exr");
    } catch (err) {
      setProgress(-1);
      showError("Could not load spectral_sample.exr (" + err.message + ").");
    }
  });

  // asakusa — fetched over HTTP from the tinyexr repo (release branch)
  const ASAKUSA_URL =
    "https://raw.githubusercontent.com/syoyo/tinyexr/release/asakusa.exr";
  document.getElementById("btnAsakusa").addEventListener("click", async () => {
    try {
      loadBytes(await fetchUrlWithProgress(ASAKUSA_URL, "asakusa.exr"), "asakusa.exr");
    } catch (err) {
      setProgress(-1);
      showError("Could not fetch asakusa.exr (" + err.message + ").");
    }
  });

  // drag & drop
  ["dragenter", "dragover"].forEach((ev) =>
    stage.addEventListener(ev, (e) => {
      e.preventDefault();
      document.getElementById("dropzone").classList.remove("hidden");
      document.getElementById("dropzone").classList.add("drag");
    }));
  ["dragleave", "drop"].forEach((ev) =>
    stage.addEventListener(ev, (e) => {
      e.preventDefault();
      document.getElementById("dropzone").classList.remove("drag");
      if (ev === "dragleave" && img)
        document.getElementById("dropzone").classList.add("hidden");
    }));
  stage.addEventListener("drop", async (e) => {
    const f = e.dataTransfer.files[0];
    if (f) loadBytes(await readFileWithProgress(f), f.name);
  });

  // wheel zoom (to cursor)
  glc.addEventListener("wheel", (e) => {
    if (!img) return;
    e.preventDefault();
    const r = glc.getBoundingClientRect();
    const mx = (e.clientX - r.left) * dpr(), my = (e.clientY - r.top) * dpr();
    const [ix, iy] = screenToImg(mx, my);
    view.zoom = clamp(view.zoom * Math.exp(-e.deltaY * 0.0015), 0.01, 5000);
    view.panX = mx - ix * view.zoom;
    view.panY = my - iy * view.zoom;
    render();
  }, { passive: false });

  // drag: pan, or shift-drag: ROI
  let drag = null;
  glc.addEventListener("mousedown", (e) => {
    if (!img) return;
    const r = glc.getBoundingClientRect();
    const mx = (e.clientX - r.left) * dpr(), my = (e.clientY - r.top) * dpr();
    if (e.shiftKey) {
      const [ix, iy] = screenToImg(mx, my);
      drag = { mode: "roi", ix, iy };
      glc.classList.add("roi");
    } else {
      drag = { mode: "pan", mx, my, panX: view.panX, panY: view.panY };
      glc.classList.add("panning");
    }
  });
  window.addEventListener("mousemove", (e) => {
    const r = glc.getBoundingClientRect();
    const mx = (e.clientX - r.left) * dpr(), my = (e.clientY - r.top) * dpr();
    if (drag && drag.mode === "pan") {
      view.panX = drag.panX + (mx - drag.mx);
      view.panY = drag.panY + (my - drag.my);
      render();
    } else if (drag && drag.mode === "roi") {
      const [ix, iy] = screenToImg(mx, my);
      roi = {
        x0: clamp(Math.min(drag.ix, ix), 0, img.w),
        y0: clamp(Math.min(drag.iy, iy), 0, img.h),
        x1: clamp(Math.max(drag.ix, ix), 0, img.w),
        y1: clamp(Math.max(drag.iy, iy), 0, img.h),
      };
      updateRoiUI();
      render();
    } else {
      updatePixel(mx, my);
    }
  });
  window.addEventListener("mouseup", () => {
    drag = null;
    glc.classList.remove("panning", "roi");
  });
  glc.addEventListener("mouseleave", () =>
    document.getElementById("pixel").classList.add("hidden"));

  // --- 3D orbit controls (active only in deep/3D mode) ---
  glc.addEventListener("wheel", (e) => {
    if (mode !== "3d") return;
    e.preventDefault();
    cam.dist = clamp(cam.dist * Math.exp(e.deltaY * 0.0015), 0.2, 50);
    render3d();
  }, { passive: false });
  let d3 = null;
  glc.addEventListener("mousedown", (e) => {
    if (mode !== "3d") return;
    e.preventDefault();
    d3 = { x: e.clientX, y: e.clientY, az: cam.az, el: cam.el,
           panX: cam.panX, panY: cam.panY, pan: e.shiftKey || e.button === 2 };
  });
  window.addEventListener("mousemove", (e) => {
    if (!d3) return;
    const dx = e.clientX - d3.x, dy = e.clientY - d3.y;
    if (d3.pan) {
      cam.panX = d3.panX + dx * 0.0025 * cam.dist;
      cam.panY = d3.panY - dy * 0.0025 * cam.dist;
    } else {
      cam.az = d3.az + dx * 0.01;
      cam.el = clamp(d3.el + dy * 0.01, -1.55, 1.55);
    }
    render3d();
  });
  window.addEventListener("mouseup", () => { d3 = null; });
  glc.addEventListener("contextmenu", (e) => { if (mode === "3d") e.preventDefault(); });

  // --- touch controls (2D pan/pinch + tap-pick, 3D orbit/pinch/pan) ---
  let tState = null;
  const tPos = (t) => {
    const r = glc.getBoundingClientRect();
    return [(t.clientX - r.left) * dpr(), (t.clientY - r.top) * dpr()];
  };
  const tDist = (a, b) => Math.hypot(a.clientX - b.clientX, a.clientY - b.clientY);
  const tMid = (a, b) => {
    const r = glc.getBoundingClientRect();
    return [((a.clientX + b.clientX) / 2 - r.left) * dpr(),
            ((a.clientY + b.clientY) / 2 - r.top) * dpr()];
  };
  function initTouch(touches) {
    if (mode === "3d") {
      if (touches.length === 1)
        tState = { k: "orbit", x: touches[0].clientX, y: touches[0].clientY,
                   az: cam.az, el: cam.el };
      else if (touches.length >= 2)
        tState = { k: "tp3d", d: tDist(touches[0], touches[1]), dist: cam.dist,
                   mx: (touches[0].clientX + touches[1].clientX) / 2,
                   my: (touches[0].clientY + touches[1].clientY) / 2,
                   panX: cam.panX, panY: cam.panY };
      else tState = null;
      return;
    }
    if (!img) { tState = null; return; }
    if (touches.length === 1) {
      const [mx, my] = tPos(touches[0]);
      tState = { k: "pan", mx, my, sx: mx, sy: my,
                 panX: view.panX, panY: view.panY, moved: false };
    } else if (touches.length >= 2) {
      const [mx, my] = tMid(touches[0], touches[1]);
      const [ix, iy] = screenToImg(mx, my);
      tState = { k: "pinch", d: tDist(touches[0], touches[1]), zoom: view.zoom, ix, iy };
    } else tState = null;
  }
  glc.addEventListener("touchstart", (e) => {
    if (mode !== "3d" && !img) return;
    e.preventDefault();
    initTouch(e.touches);
  }, { passive: false });
  glc.addEventListener("touchmove", (e) => {
    if (!tState) return;
    e.preventDefault();
    const st = tState, T = e.touches;
    if (st.k === "orbit") {
      cam.az = st.az + (T[0].clientX - st.x) * 0.01;
      cam.el = clamp(st.el + (T[0].clientY - st.y) * 0.01, -1.55, 1.55);
      render3d();
    } else if (st.k === "tp3d" && T.length >= 2) {
      const d = tDist(T[0], T[1]);
      if (st.d > 0) cam.dist = clamp(st.dist * st.d / d, 0.2, 50);
      const mx = (T[0].clientX + T[1].clientX) / 2, my = (T[0].clientY + T[1].clientY) / 2;
      cam.panX = st.panX + (mx - st.mx) * 0.0025 * cam.dist;
      cam.panY = st.panY - (my - st.my) * 0.0025 * cam.dist;
      render3d();
    } else if (st.k === "pan") {
      const [mx, my] = tPos(T[0]);
      view.panX = st.panX + (mx - st.mx);
      view.panY = st.panY + (my - st.my);
      if (Math.abs(mx - st.sx) + Math.abs(my - st.sy) > 6 * dpr()) st.moved = true;
      render();
    } else if (st.k === "pinch" && T.length >= 2) {
      const d = tDist(T[0], T[1]);
      const [mx, my] = tMid(T[0], T[1]);
      if (st.d > 0) view.zoom = clamp(st.zoom * d / st.d, 0.01, 5000);
      view.panX = mx - st.ix * view.zoom;
      view.panY = my - st.iy * view.zoom;
      render();
    }
  }, { passive: false });
  glc.addEventListener("touchend", (e) => {
    if (tState && tState.k === "pan" && !tState.moved && mode !== "3d")
      updatePixel(tState.sx, tState.sy); // tap = pixel pick
    if (e.touches.length > 0) initTouch(e.touches); // re-seat for remaining fingers
    else tState = null;
  }, { passive: false });
  glc.addEventListener("touchcancel", () => { tState = null; }, { passive: false });

  // view buttons
  document.getElementById("btnFit").addEventListener("click", fitView);
  document.getElementById("btn11").addEventListener("click", oneToOne);
  document.getElementById("btnZoomRegion").addEventListener("click", zoomToRegion);
  document.getElementById("clearRoi").addEventListener("click", () => {
    roi = null; updateRoiUI(); render();
  });

  // controls
  const exp = document.getElementById("exposure");
  exp.addEventListener("input", () => {
    ctl.exposure = parseFloat(exp.value);
    document.getElementById("expVal").textContent =
      (ctl.exposure >= 0 ? "+" : "") + ctl.exposure.toFixed(1) + " EV";
    render();
  });
  const gam = document.getElementById("gamma");
  gam.addEventListener("input", () => {
    ctl.gamma = parseFloat(gam.value);
    document.getElementById("gammaVal").textContent = ctl.gamma.toFixed(2);
    render();
  });
  document.getElementById("srgb").addEventListener("change", (e) => {
    ctl.srgb = e.target.checked;
    document.getElementById("gamma").disabled = ctl.srgb;
    render();
  });
  document.getElementById("channels").addEventListener("click", (e) => {
    const b = e.target.closest("button");
    if (!b) return;
    setChannel(parseInt(b.dataset.ch, 10));
    render();
  });
  document.getElementById("falseColor").addEventListener("change", (e) => {
    ctl.falseColor = e.target.checked;
    render();
  });
  document.getElementById("showDisp").addEventListener("change", (e) => {
    ctl.showDisp = e.target.checked; render();
  });
  document.getElementById("cropDisp").addEventListener("change", (e) => {
    ctl.cropDisp = e.target.checked; render();
  });
  document.getElementById("partSel").addEventListener("change", (e) => {
    const part = parseInt(e.target.value, 10);
    if (header.parts[part] && header.parts[part].deep) enterDeepMode(part);
    else if (header.parts[part] && header.parts[part].spectral)
      enterSpectralMode(part);
    else selectAndDecode(part, 0, 0, true);
  });

  // wavelength scrubber (spectral mode)
  document.getElementById("wavelength").addEventListener("input", (e) => {
    showWavelength(parseInt(e.target.value, 10), false);
  });
  // CIE color composite toggle (spectral mode)
  document.getElementById("spectralColor").addEventListener("change", (e) => {
    specColor = e.target.checked;
    document.getElementById("wavelength").disabled = specColor;
    document.getElementById("wavelengthCtrl").classList.toggle("dim", specColor);
    applySpectralView(false);
  });
  document.getElementById("levelSel").addEventListener("change", (e) => {
    const [lx, ly] = e.target.value.split(",").map(Number);
    selectAndDecode(sel.part, lx, ly, true);
  });
  document.getElementById("channelSel").addEventListener("change", (e) => {
    selectAndDecode(sel.part, sel.lx, sel.ly, false, parseInt(e.target.value, 10));
  });

  // deep (3D) sample images, fetched over HTTP from the tinyexr repo
  const DEEP_BASE = "https://raw.githubusercontent.com/syoyo/tinyexr/release/data/";
  const loadDeepSample = async (file) => {
    try {
      loadBytes(await fetchUrlWithProgress(DEEP_BASE + file, file), file);
    } catch (err) {
      setProgress(-1);
      showError("Could not fetch " + file + " (" + err.message + ").");
    }
  };
  document.getElementById("btnDeep").addEventListener("click",
    () => loadDeepSample("deepscanline.exr"));
  document.getElementById("btnDeepTiled").addEventListener("click",
    () => loadDeepSample("deep_tiled_sample.exr"));

  // deep 3D controls
  const pt = document.getElementById("ptSize");
  pt.addEventListener("input", () => {
    deepCtl.pointSize = parseFloat(pt.value);
    document.getElementById("ptVal").textContent = deepCtl.pointSize.toFixed(1);
    if (mode === "3d") render3d();
  });
  const dexp = document.getElementById("deepExposure");
  dexp.addEventListener("input", () => {
    deepCtl.exposure = parseFloat(dexp.value);
    document.getElementById("deepExpVal").textContent =
      (deepCtl.exposure >= 0 ? "+" : "") + deepCtl.exposure.toFixed(1) + " EV";
    if (mode === "3d") render3d();
  });
  document.getElementById("deepColorMode").addEventListener("change", (e) => {
    deepCtl.rgb = e.target.checked;
    if (mode === "3d") render3d();
  });
  document.getElementById("resetView").addEventListener("click", () => {
    resetCam(); render3d();
  });

  window.addEventListener("resize", () => { syncCanvasSize(); render(); });
}

/* -------------------------------------------------------------------- boot */
/* ----------------------------------------------- openexr-images browser ---- */
// Browse the official OpenEXR sample-image library and load any image over HTTP.
// One GitHub tree API call lists every .exr; images are fetched from raw.*.
const OEXR_REPO = "AcademySoftwareFoundation/openexr-images";
const OEXR_TREE_API =
  "https://api.github.com/repos/" + OEXR_REPO + "/git/trees/main?recursive=1";
const OEXR_RAW_BASE = "https://raw.githubusercontent.com/" + OEXR_REPO + "/main/";

function humanSize(b) {
  if (b < 1024) return b + " B";
  if (b < 1048576) return Math.round(b / 1024) + " KB";
  return (b / 1048576).toFixed(1) + " MB";
}

function setupBrowser() {
  const modal = document.getElementById("browser");
  const treeEl = document.getElementById("browserTree");
  const filterEl = document.getElementById("browserFilter");
  let allFiles = null; // cached [{path, name, size}] after first load

  const msg = (text, err) => {
    const d = document.createElement("div");
    d.className = "msg" + (err ? " err" : "");
    d.textContent = text;
    treeEl.replaceChildren(d);
  };

  const close = () => modal.classList.add("hidden");
  const open = () => {
    modal.classList.remove("hidden");
    if (allFiles === null) load();
    filterEl.focus();
  };

  // Build a nested {dirs:Map, files:[]} tree from flat paths.
  function buildTree(files) {
    const root = { dirs: new Map(), files: [] };
    for (const f of files) {
      const parts = f.path.split("/");
      let node = root;
      for (let i = 0; i < parts.length - 1; i++) {
        if (!node.dirs.has(parts[i]))
          node.dirs.set(parts[i], { dirs: new Map(), files: [] });
        node = node.dirs.get(parts[i]);
      }
      node.files.push(f);
    }
    return root;
  }
  const countFiles = (n) =>
    n.files.length + [...n.dirs.values()].reduce((s, c) => s + countFiles(c), 0);

  async function loadRepoFile(f) {
    close();
    try {
      const url = OEXR_RAW_BASE + f.path.split("/").map(encodeURIComponent).join("/");
      loadBytes(await fetchUrlWithProgress(url, f.name), f.path);
    } catch (err) {
      setProgress(-1);
      showError("Could not fetch " + f.name + " (" + err.message + ").");
    }
  }

  function renderNode(node, openAll) {
    const frag = document.createDocumentFragment();
    for (const [name, child] of [...node.dirs.entries()].sort((a, b) =>
      a[0].localeCompare(b[0]))) {
      const det = document.createElement("details");
      det.open = openAll;
      const sum = document.createElement("summary");
      sum.textContent = name;
      const cnt = document.createElement("span");
      cnt.className = "count";
      cnt.textContent = countFiles(child) + (countFiles(child) === 1 ? " file" : " files");
      sum.appendChild(cnt);
      const kids = document.createElement("div");
      kids.className = "children";
      kids.appendChild(renderNode(child, openAll));
      det.append(sum, kids);
      frag.appendChild(det);
    }
    for (const f of [...node.files].sort((a, b) => a.name.localeCompare(b.name))) {
      const btn = document.createElement("button");
      btn.className = "tree-file";
      btn.title = "Load " + f.path;
      let thumb;
      if (f.thumb) {
        thumb = document.createElement("img");
        thumb.className = "thumb";
        thumb.loading = "lazy";
        thumb.decoding = "async";
        thumb.alt = "";
        thumb.width = 46; thumb.height = 30;
        thumb.src = f.thumb;
        // Fall back to the checker placeholder if the preview fails to load.
        thumb.addEventListener("error", () => {
          thumb.removeAttribute("src");
          thumb.classList.add("noimg");
        });
      } else {
        thumb = document.createElement("span");
        thumb.className = "thumb noimg";
      }
      const nm = document.createElement("span");
      nm.className = "nm";
      nm.textContent = f.name;
      const sz = document.createElement("span");
      sz.className = "sz";
      sz.textContent = humanSize(f.size);
      btn.append(thumb, nm, sz);
      btn.addEventListener("click", () => loadRepoFile(f));
      frag.appendChild(btn);
    }
    return frag;
  }

  function rerender() {
    const q = filterEl.value.trim().toLowerCase();
    const files = q ? allFiles.filter((f) => f.path.toLowerCase().includes(q)) : allFiles;
    if (!files.length) { msg("No matching .exr files."); return; }
    treeEl.replaceChildren(renderNode(buildTree(files), !!q));
  }

  async function load() {
    msg("Loading image list…");
    try {
      const resp = await fetch(OEXR_TREE_API);
      if (!resp.ok) throw new Error(resp.status + " " + resp.statusText);
      const data = await resp.json();
      // Each .exr in this repo has a sibling full-res .jpg preview; use it as a
      // browser-native thumbnail (lazy-loaded). Note which siblings exist.
      const blobs = new Set(data.tree.filter((b) => b.type === "blob").map((b) => b.path));
      const rawUrl = (p) => OEXR_RAW_BASE + p.split("/").map(encodeURIComponent).join("/");
      allFiles = data.tree
        .filter((b) => b.type === "blob" && b.path.toLowerCase().endsWith(".exr"))
        .map((b) => {
          const jpg = b.path.replace(/\.exr$/i, ".jpg");
          return {
            path: b.path,
            name: b.path.split("/").pop(),
            size: b.size || 0,
            thumb: blobs.has(jpg) ? rawUrl(jpg) : null,
          };
        });
      rerender();
    } catch (err) {
      allFiles = null;
      msg("Failed to load list (" + err.message + "). The GitHub API may be rate-limited; try again later.", true);
    }
  }

  document.getElementById("btnBrowse").addEventListener("click", open);
  document.getElementById("browserClose").addEventListener("click", close);
  modal.addEventListener("click", (e) => { if (e.target === modal) close(); });
  document.addEventListener("keydown", (e) => {
    if (e.key === "Escape" && !modal.classList.contains("hidden")) close();
  });
  filterEl.addEventListener("input", () => { if (allFiles) rerender(); });
}

/* ============================================================ deep 3D view */
const VS3D = `#version 300 es
precision highp float;
layout(location=0) in vec3 aPos;
layout(location=1) in vec3 aCol;
layout(location=2) in float aT;
uniform mat4 uMVP; uniform float uPointSize, uExposure; uniform int uRGB;
out vec3 vCol;
vec3 toSRGB(vec3 c){ c=clamp(c,0.0,1.0);
  return mix(12.92*c, 1.055*pow(c,vec3(1.0/2.4))-0.055, step(0.0031308,c)); }
vec3 viridis(float t){ t=clamp(t,0.0,1.0);
  const vec3 c0=vec3(0.2777273272234177,0.005407344544966578,0.3340998053353061);
  const vec3 c1=vec3(0.1050930431085774,1.404613529898575,1.384590162594685);
  const vec3 c2=vec3(-0.3308618287255563,0.214847559468213,0.09509516302823659);
  const vec3 c3=vec3(-4.634230498983486,-5.799100973351585,-19.33244095627987);
  const vec3 c4=vec3(6.228269936347081,14.17993336680509,56.69055260068105);
  const vec3 c5=vec3(4.776384997670288,-13.74514537774601,-65.35303263337234);
  const vec3 c6=vec3(-5.435455855934631,4.645852612178535,26.3124352495832);
  return c0+t*(c1+t*(c2+t*(c3+t*(c4+t*(c5+t*c6))))); }
void main(){
  gl_Position = uMVP * vec4(aPos, 1.0);
  gl_PointSize = uPointSize;
  if (uRGB == 1) vCol = toSRGB(max(aCol * uExposure, 0.0));
  else           vCol = viridis(aT);
}`;
const FS3D = `#version 300 es
precision highp float;
in vec3 vCol; out vec4 frag;
void main(){ vec2 d = gl_PointCoord*2.0-1.0; if (dot(d,d) > 1.0) discard; frag = vec4(vCol, 1.0); }`;

// --- minimal column-major mat4 helpers ---
function m4ident() { const o = new Float32Array(16); o[0]=o[5]=o[10]=o[15]=1; return o; }
function m4mul(a, b) {
  const o = new Float32Array(16);
  for (let c = 0; c < 4; c++) for (let r = 0; r < 4; r++) {
    let s = 0; for (let k = 0; k < 4; k++) s += a[k*4+r] * b[c*4+k];
    o[c*4+r] = s;
  }
  return o;
}
function m4persp(fovy, asp, n, f) {
  const t = 1/Math.tan(fovy/2), o = new Float32Array(16);
  o[0]=t/asp; o[5]=t; o[10]=(f+n)/(n-f); o[11]=-1; o[14]=2*f*n/(n-f); return o;
}
function m4trans(x, y, z) { const o = m4ident(); o[12]=x; o[13]=y; o[14]=z; return o; }
function m4rotX(a) { const c=Math.cos(a), s=Math.sin(a), o=m4ident(); o[5]=c; o[6]=s; o[9]=-s; o[10]=c; return o; }
function m4rotY(a) { const c=Math.cos(a), s=Math.sin(a), o=m4ident(); o[0]=c; o[2]=-s; o[8]=s; o[10]=c; return o; }

function initGL3D() {
  prog3d = gl.createProgram();
  gl.attachShader(prog3d, compile(gl.VERTEX_SHADER, VS3D));
  gl.attachShader(prog3d, compile(gl.FRAGMENT_SHADER, FS3D));
  gl.linkProgram(prog3d);
  if (!gl.getProgramParameter(prog3d, gl.LINK_STATUS))
    throw new Error("link3d: " + gl.getProgramInfoLog(prog3d));
  uni3d = {
    mvp: gl.getUniformLocation(prog3d, "uMVP"),
    pointSize: gl.getUniformLocation(prog3d, "uPointSize"),
    exposure: gl.getUniformLocation(prog3d, "uExposure"),
    rgb: gl.getUniformLocation(prog3d, "uRGB"),
  };
  vbo3d = gl.createBuffer();
}

function resetCam() { cam = { az: 0.5, el: -0.32, dist: 2.2, panX: 0, panY: 0 }; }

function render3d() {
  if (!gl || !prog3d) return;
  syncCanvasSize();
  const W = gl.canvas.width, H = gl.canvas.height;
  gl.viewport(0, 0, W, H);
  gl.clearColor(0.05, 0.06, 0.07, 1);
  gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
  gl.enable(gl.DEPTH_TEST);

  const proj = m4persp(45 * Math.PI / 180, W / H, 0.01, 100);
  const view = m4mul(m4trans(cam.panX, cam.panY, -cam.dist),
                     m4mul(m4rotX(cam.el), m4rotY(cam.az)));
  const mvp = m4mul(proj, view);

  gl.useProgram(prog3d);
  gl.uniformMatrix4fv(uni3d.mvp, false, mvp);
  gl.uniform1f(uni3d.pointSize, deepCtl.pointSize * dpr());
  gl.uniform1f(uni3d.exposure, Math.pow(2, deepCtl.exposure));
  gl.uniform1i(uni3d.rgb, deepCtl.rgb ? 1 : 0);

  gl.bindBuffer(gl.ARRAY_BUFFER, vbo3d);
  gl.enableVertexAttribArray(0); gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 28, 0);
  gl.enableVertexAttribArray(1); gl.vertexAttribPointer(1, 3, gl.FLOAT, false, 28, 12);
  gl.enableVertexAttribArray(2); gl.vertexAttribPointer(2, 1, gl.FLOAT, false, 28, 24);
  gl.drawArrays(gl.POINTS, 0, deepN);

  gl.disableVertexAttribArray(2);
  gl.disable(gl.DEPTH_TEST);
  updateZoomLabel3d();
}

function updateZoomLabel3d() { /* viewbar hidden in 3D; nothing to do */ }

// Switch the panel/HUD back to flat-image mode.
function set2DMode() {
  mode = "2d";
  document.getElementById("ctrls").classList.remove("hidden");
  document.getElementById("deepCtrls").classList.add("hidden");
  document.getElementById("spectralCtrls").classList.add("hidden");
  document.getElementById("channelView").style.display = "";
  document.getElementById("overlay").style.display = "";
}

// Decode a deep part into a point cloud and show it in the 3D view.
async function enterDeepMode(part) {
  setProgress(0, "Decoding deep samples…");
  await raf();
  const n = M._exrv_deep_load(handle, part);
  if (n <= 0) {
    setProgress(-1);
    showError("Could not decode this deep part (needs a Z channel).");
    return;
  }
  const ptr = M._exrv_deep_points(handle);
  const src = M.HEAPF32.subarray(ptr >> 2, (ptr >> 2) + n * 6);

  const ph = header.parts[part];
  const W = ph.width, Hh = ph.height;
  let zmin = Infinity, zmax = -Infinity;
  for (let i = 0; i < n; i++) { const z = src[i*6+2]; if (z < zmin) zmin = z; if (z > zmax) zmax = z; }
  if (!(zmax > zmin)) zmax = zmin + 1;
  const maxXY = Math.max(W, Hh), zr = zmax - zmin;

  // Interleave normalized [x, y, z, r, g, b, depthT(0..1)]; center + scale to ~unit.
  const arr = new Float32Array(n * 7);
  for (let i = 0; i < n; i++) {
    const x = src[i*6], y = src[i*6+1], t = (src[i*6+2] - zmin) / zr;
    arr[i*7+0] = (x - W/2) / maxXY;
    arr[i*7+1] = -(y - Hh/2) / maxXY;
    arr[i*7+2] = -(t - 0.5) * 0.8;
    arr[i*7+3] = src[i*6+3];
    arr[i*7+4] = src[i*6+4];
    arr[i*7+5] = src[i*6+5];
    arr[i*7+6] = t;
  }
  if (!prog3d) initGL3D();
  gl.bindBuffer(gl.ARRAY_BUFFER, vbo3d);
  gl.bufferData(gl.ARRAY_BUFFER, arr, gl.STATIC_DRAW);
  deepN = n; deepBounds = { w: W, h: Hh, zmin, zmax };
  setProgress(100);

  mode = "3d";
  sel = { part, lx: 0, ly: 0, view: 0 };
  img = null; roi = null;
  dwMin = { x: ph.dataWindow.minX, y: ph.dataWindow.minY };
  document.getElementById("dropzone").classList.add("hidden");
  document.getElementById("ctrls").classList.add("hidden");
  document.getElementById("deepCtrls").classList.remove("hidden");
  document.getElementById("spectralCtrls").classList.add("hidden");
  document.getElementById("info").classList.remove("hidden");
  document.getElementById("viewbar").classList.add("hidden");
  document.getElementById("pixel").classList.add("hidden");
  document.getElementById("overlay").style.display = "none";
  document.getElementById("deepInfo").textContent =
    `${n.toLocaleString()} samples · ${W}×${Hh} · Z ${zmin.toFixed(2)}–${zmax.toFixed(2)}`;
  resetCam();
  renderInfo();
  render3d();
}

/* ========================================================== spectral view */
function spectrumLabel(ph) {
  switch (ph.spectrumType) {
    case "reflective": return "Reflective";
    case "emissive": return "Emissive";
    case "polarised": return "Polarised (S0)";
    default: return "Spectral";
  }
}

// Decode all wavelength planes of a spectral part and switch to spectral mode:
// a grayscale view of one wavelength at a time (scrubbed with the slider) plus
// a per-pixel spectrum plot. Uses the flat 2D render path (exposure/gamma apply).
async function enterSpectralMode(part) {
  setProgress(0, "Decoding spectral planes…");
  await raf();
  const nwl = M._exrv_spectral_open_part(handle, part);
  if (nwl <= 0) {
    setProgress(-1);
    showError("Could not decode this spectral image.");
    return;
  }
  const w = M._exrv_spectral_width(handle), h = M._exrv_spectral_height(handle);
  specDims = { w, h };
  specNwl = nwl;
  const wp = M._exrv_spectral_wavelengths(handle);
  specWl = M.HEAPF32.slice(wp >> 2, (wp >> 2) + nwl); // copy out of the heap
  specWi = 0;
  setProgress(100);

  mode = "spectral";
  sel = { part, lx: 0, ly: 0, view: 0 };
  roi = null;
  const ph = header.parts[part];
  dwMin = { x: 0, y: 0 };
  dispWin = ph.displayWindow;

  document.getElementById("dropzone").classList.add("hidden");
  document.getElementById("ctrls").classList.remove("hidden");
  document.getElementById("deepCtrls").classList.add("hidden");
  document.getElementById("spectralCtrls").classList.remove("hidden");
  document.getElementById("channelView").style.display = "none";
  document.getElementById("info").classList.remove("hidden");
  document.getElementById("viewbar").classList.remove("hidden");
  document.getElementById("overlay").style.display = "";

  const slider = document.getElementById("wavelength");
  slider.min = "0";
  slider.max = String(nwl - 1);
  slider.step = "1";
  slider.value = "0";

  document.getElementById("spectralInfo").textContent =
    `${spectrumLabel(ph)} · ${w}×${h} · ${nwl} bands · ` +
    `${specWl[0].toFixed(1)}–${specWl[nwl - 1].toFixed(1)} nm`;

  // Reset to single-wavelength grayscale on each new spectral image.
  specColor = false;
  document.getElementById("spectralColor").checked = false;
  document.getElementById("wavelength").disabled = false;
  document.getElementById("wavelengthCtrl").classList.remove("dim");

  lastSpecPixel = null;
  clearSpecPlot();
  document.getElementById("specPixelPos").textContent = "—";
  applySpectralView(true);
  renderInfo();
}

// Show either the CIE-composite color image or the current wavelength plane.
function applySpectralView(doFit) {
  if (specColor) showComposite(doFit);
  else showWavelength(specWi, doFit);
}

// Composite the whole spectral cube to an sRGB color preview (CIE 1931 → sRGB,
// computed in WASM into the shared RGBA buffer; the shader applies exposure +
// the sRGB curve, so we force the RGB channel view).
function showComposite(doFit) {
  if (mode !== "spectral") return;
  if (M._exrv_spectral_composite(handle) < 0) {
    showError("CIE composite failed.");
    return;
  }
  setChannel(0);
  const ptr = M._exrv_rgba(handle);
  const w = specDims.w, h = specDims.h;
  img = { w, h, data: M.HEAPF32.slice(ptr >> 2, (ptr >> 2) + w * h * 4) };
  uploadTexture();
  document.getElementById("wlVal").textContent = "CIE";
  if (doFit) fitView(); else render();
  redrawSpecPlot();
}

// Upload the grayscale plane for wavelength index `wi` and refresh the view.
function showWavelength(wi, doFit) {
  if (mode !== "spectral") return;
  wi = clamp(wi | 0, 0, specNwl - 1);
  specWi = wi;
  if (M._exrv_spectral_show(handle, wi) < 0) {
    showError("Wavelength decode failed.");
    return;
  }
  const ptr = M._exrv_rgba(handle);
  const w = specDims.w, h = specDims.h;
  const data = M.HEAPF32.slice(ptr >> 2, (ptr >> 2) + w * h * 4);
  img = { w, h, data };
  uploadTexture();
  document.getElementById("wlVal").textContent = specWl[wi].toFixed(1) + " nm";
  document.getElementById("wavelength").value = String(wi);
  if (doFit) fitView(); else render();
  redrawSpecPlot();
}

// Read a pixel's full spectrum from WASM and draw it.
function updateSpecPixel(ix, iy) {
  const ptr = M._exrv_spectral_pixel(handle, ix, iy);
  if (!ptr) return;
  const spec = M.HEAPF32.slice(ptr >> 2, (ptr >> 2) + specNwl);
  lastSpecPixel = { x: ix, y: iy, spec };
  document.getElementById("specPixelPos").textContent = `x ${ix}  y ${iy}`;
  drawSpecPlot(spec);
}

function clearSpecPlot() {
  const cv = document.getElementById("specPlot");
  const ctx = cv.getContext("2d");
  ctx.fillStyle = "#0d1117";
  ctx.fillRect(0, 0, cv.width, cv.height);
}
function redrawSpecPlot() {
  if (lastSpecPixel) drawSpecPlot(lastSpecPixel.spec);
  else clearSpecPlot();
}

// Plot value-vs-wavelength for the hovered pixel, with a marker at the current
// wavelength. Y axis auto-scales to the pixel's peak.
function drawSpecPlot(spec) {
  const cv = document.getElementById("specPlot");
  const ctx = cv.getContext("2d");
  const W = cv.width, H = cv.height;
  ctx.fillStyle = "#0d1117";
  ctx.fillRect(0, 0, W, H);
  if (!spec || !specNwl) return;

  const padL = 38, padR = 8, padT = 8, padB = 18;
  const plotW = W - padL - padR, plotH = H - padT - padB;
  let vmax = 0;
  for (let i = 0; i < spec.length; i++) if (spec[i] > vmax) vmax = spec[i];
  if (!(vmax > 0)) vmax = 1;
  const wl0 = specWl[0], wl1 = specWl[specNwl - 1];
  const wlr = (wl1 > wl0) ? (wl1 - wl0) : 1;
  const xOf = (wl) => padL + ((wl - wl0) / wlr) * plotW;
  const yOf = (v) => padT + plotH - (Math.max(v, 0) / vmax) * plotH;

  ctx.strokeStyle = "#30363d";
  ctx.lineWidth = 1;
  ctx.beginPath();
  ctx.moveTo(padL, padT);
  ctx.lineTo(padL, padT + plotH);
  ctx.lineTo(padL + plotW, padT + plotH);
  ctx.stroke();

  // current-wavelength marker
  ctx.strokeStyle = "#4c9aff";
  ctx.setLineDash([3, 3]);
  ctx.beginPath();
  const xm = xOf(specWl[specWi]);
  ctx.moveTo(xm, padT);
  ctx.lineTo(xm, padT + plotH);
  ctx.stroke();
  ctx.setLineDash([]);

  // spectrum polyline + points
  ctx.strokeStyle = "#ffd24c";
  ctx.lineWidth = 1.5;
  ctx.beginPath();
  for (let i = 0; i < specNwl; i++) {
    const x = xOf(specWl[i]), y = yOf(spec[i]);
    if (i === 0) ctx.moveTo(x, y); else ctx.lineTo(x, y);
  }
  ctx.stroke();
  ctx.fillStyle = "#ffd24c";
  for (let i = 0; i < specNwl; i++) {
    ctx.beginPath();
    ctx.arc(xOf(specWl[i]), yOf(spec[i]), 1.6, 0, 6.283);
    ctx.fill();
  }

  ctx.fillStyle = "#8b949e";
  ctx.font = "10px system-ui, sans-serif";
  ctx.textAlign = "center";
  ctx.fillText(wl0.toFixed(0) + " nm", padL, H - 5);
  ctx.fillText(wl1.toFixed(0), padL + plotW, H - 5);
  ctx.textAlign = "right";
  ctx.fillText(vmax >= 1e4 || vmax < 1e-2 ? vmax.toExponential(1)
                                          : vmax.toFixed(2), padL - 3, padT + 8);
  ctx.fillText("0", padL - 3, padT + plotH);
}

/* ------------------------------------- JCGT spectral sample-image browser -- */
const JCGT_ZIP = "https://jcgt.org/published/0010/03/01/sample-images.zip";
// jcgt.org likely sends no CORS headers, so try direct first then public
// proxies. Proxies can be slow or rate-limited; this is best-effort.
const CORS_PROXIES = [
  (u) => u,
  (u) => "https://corsproxy.io/?url=" + encodeURIComponent(u),
  (u) => "https://api.allorigins.win/raw?url=" + encodeURIComponent(u),
];

function setupSpecBrowser() {
  const modal = document.getElementById("specBrowser");
  const treeEl = document.getElementById("specBrowserTree");
  const filterEl = document.getElementById("specBrowserFilter");
  let entries = null; // { name -> Uint8Array } of .exr files, cached

  const msg = (text, err) => {
    const d = document.createElement("div");
    d.className = "msg" + (err ? " err" : "");
    d.textContent = text;
    treeEl.replaceChildren(d);
  };
  const close = () => modal.classList.add("hidden");
  const open = () => {
    modal.classList.remove("hidden");
    if (entries === null) load();
    filterEl.focus();
  };

  async function fetchZip() {
    let lastErr;
    for (const mk of CORS_PROXIES) {
      try {
        return await fetchUrlWithProgress(mk(JCGT_ZIP), "sample-images.zip");
      } catch (e) { lastErr = e; }
    }
    throw lastErr || new Error("fetch failed");
  }

  async function load() {
    msg("Fetching + unzipping sample-images.zip…");
    try {
      const zip = await fetchZip();
      setProgress(100);
      const files = unzipSync(zip);
      entries = {};
      for (const name of Object.keys(files))
        if (/\.exr$/i.test(name) && files[name].length) entries[name] = files[name];
      if (!Object.keys(entries).length) { msg("No .exr files in the archive.", true); return; }
      rerender();
    } catch (err) {
      entries = null;
      setProgress(-1);
      msg("Could not fetch/unzip the archive (" + err.message +
          "). jcgt.org may block cross-origin requests and the proxies may be " +
          "rate-limited; try again later or download the zip and drag a file in.",
          true);
    }
  }

  function rerender() {
    const q = filterEl.value.trim().toLowerCase();
    const names = Object.keys(entries)
      .filter((n) => !q || n.toLowerCase().includes(q))
      .sort((a, b) => a.localeCompare(b));
    if (!names.length) { msg("No matching .exr files."); return; }
    const frag = document.createDocumentFragment();
    for (const name of names) {
      const btn = document.createElement("button");
      btn.className = "tree-file";
      btn.title = "Load " + name;
      const nm = document.createElement("span");
      nm.className = "nm";
      nm.textContent = name;
      const sz = document.createElement("span");
      sz.className = "sz";
      sz.textContent = humanSize(entries[name].length);
      btn.append(nm, sz);
      btn.addEventListener("click", () => {
        close();
        loadBytes(entries[name].slice(), name.split("/").pop());
      });
      frag.appendChild(btn);
    }
    treeEl.replaceChildren(frag);
  }

  document.getElementById("btnSpectral").addEventListener("click", open);
  document.getElementById("specBrowserClose").addEventListener("click", close);
  modal.addEventListener("click", (e) => { if (e.target === modal) close(); });
  document.addEventListener("keydown", (e) => {
    if (e.key === "Escape" && !modal.classList.contains("hidden")) close();
  });
  filterEl.addEventListener("input", () => { if (entries) rerender(); });
}

/* ------------------------------------------- fullscreen + panel collapse -- */
function setupChrome() {
  const app = document.getElementById("app");
  const toggleBtn = document.getElementById("panelToggle");
  const backdrop = document.getElementById("panelBackdrop");
  const fsBtn = document.getElementById("btnFullscreen");
  const isMobile = () => window.matchMedia("(max-width: 760px)").matches;

  const reflow = () => {
    // resize the canvas to the new stage size, now and after the CSS transition
    requestAnimationFrame(() => { syncCanvasSize(); render(); });
    setTimeout(() => { syncCanvasSize(); render(); }, 240);
  };
  function syncPanel() {
    const collapsed = app.classList.contains("panel-collapsed");
    toggleBtn.setAttribute("aria-expanded", String(!collapsed));
    toggleBtn.textContent = collapsed ? "☰" : "⮞";
    toggleBtn.title = collapsed ? "Show panel" : "Hide panel";
    backdrop.classList.toggle("hidden", collapsed || !isMobile());
    reflow();
  }
  const setCollapsed = (c) => { app.classList.toggle("panel-collapsed", c); syncPanel(); };

  toggleBtn.addEventListener("click", () =>
    setCollapsed(!app.classList.contains("panel-collapsed")));
  backdrop.addEventListener("click", () => setCollapsed(true));

  // start collapsed on small screens (panel opens on demand)
  if (isMobile()) app.classList.add("panel-collapsed");
  syncPanel();

  // fullscreen on the whole document
  fsBtn.addEventListener("click", () => {
    const el = document.documentElement;
    if (!document.fullscreenElement)
      (el.requestFullscreen || el.webkitRequestFullscreen)?.call(el);
    else
      (document.exitFullscreen || document.webkitExitFullscreen)?.call(document);
  });
  document.addEventListener("fullscreenchange", reflow);
  document.addEventListener("webkitfullscreenchange", reflow);
  window.addEventListener("orientationchange", reflow);
}

(async function main() {
  setupInput();
  setupBrowser();
  setupSpecBrowser();
  setupChrome();
  initLegendGradient();
  document.getElementById("gamma").disabled = ctl.srgb;
  try {
    M = await createModule();
  } catch (e) {
    showError("Failed to load WASM module. Did you run ./build.sh and serve over HTTP?");
    return;
  }
  initGL();
  render();
})();
