/*
 * tocio web demo: decode an EXR, build an OCIO processor (ACES 2.0 capable),
 * JIT-compile it to a GLSL shader, and render on WebGL2. Wide-gamut (Display-P3)
 * output when the device supports it. No external dependencies.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
import factory from "./tocio_demo.mjs";

const $ = (id) => document.getElementById(id);
const enc = new TextEncoder();

// Deployed commit: ../build-info.json is written by .github/workflows/gh-pages.yml
// at the Pages site root. It is absent when served from a local checkout.
async function showBuildInfo() {
  const el = $("buildInfo");
  if (!el) return;
  let info = null;
  try {
    const r = await fetch("../build-info.json", { cache: "no-store" });
    if (r.ok) info = await r.json();
  } catch (_) { /* local / offline */ }
  const sha = info && typeof info.commit === "string" ? info.commit : "";
  if (/^[0-9a-f]{40}$/.test(sha)) {
    const repo = typeof info.repo === "string" && /^[\w.-]+\/[\w.-]+$/.test(info.repo)
      ? info.repo : "syoyo/tinyexr";
    const date = typeof info.date === "string" ? info.date.slice(0, 10) : "";
    el.textContent = "commit " + sha.slice(0, 7) + (date ? " \u00b7 " + date : "");
    el.href = "https://github.com/" + repo + "/commit/" + sha;
    el.title = "Deployed from " + sha + (typeof info.ref === "string" ? " (" + info.ref + ")" : "");
  } else {
    el.textContent = "local build";
    el.removeAttribute("href");
    el.title = "build-info.json not found (not a Pages deployment)";
  }
  el.hidden = false;
}
showBuildInfo();

let M;                         // wasm module
let cfgPtr = 0;                // parsed toc_config*
let img = null;               // { w, h, data: Float32Array(RGBA) }
let gl, tex, quadProg = null, blitProg, vbo, texFilter;
let p3Supported = false;

/* ---- wasm string/buffer helpers ----------------------------------------- */
function cstr(s) {
  const b = enc.encode(s);
  const p = M._malloc(b.length + 1);
  M.HEAPU8.set(b, p);
  M.HEAPU8[p + b.length] = 0;
  return p;
}
function ustr(p) { return p ? M.UTF8ToString(p) : ""; }

/* ---- WebGL setup --------------------------------------------------------- */
/* fullscreen triangle; flip V so EXR row 0 is at the top */
const VERT2 = `#version 300 es
in vec2 aPos; out vec2 vUV;
void main(){ vUV = vec2(aPos.x*0.5+0.5, 1.0-(aPos.y*0.5+0.5)); gl_Position = vec4(aPos,0.0,1.0); }`;
/* passthrough (CPU fallback / Raw) fragment shader */
const FRAG_BLIT = `#version 300 es
precision highp float;
uniform sampler2D uTex; uniform float uExposure;
in vec2 vUV; out vec4 o;
void main(){ vec4 c = texture(uTex, vUV); c.rgb *= uExposure; o = c; }`;

function initGL() {
  const canvas = $("gl");
  gl = canvas.getContext("webgl2", { antialias: false, premultipliedAlpha: false });
  if (!gl) { setStatus("WebGL2 not available", true); return false; }
  // wide-gamut feature detection
  try {
    if ("drawingBufferColorSpace" in gl) {
      gl.drawingBufferColorSpace = "display-p3";
      p3Supported = gl.drawingBufferColorSpace === "display-p3";
      gl.drawingBufferColorSpace = "srgb";
    }
  } catch (e) { p3Supported = false; }
  $("p3").disabled = !p3Supported;
  $("p3state").textContent = p3Supported ? "(supported)" : "(not supported here)";

  gl.getExtension("EXT_color_buffer_float");
  texFilter = gl.getExtension("OES_texture_float_linear") ? gl.LINEAR : gl.NEAREST;

  vbo = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER, vbo);
  gl.bufferData(gl.ARRAY_BUFFER,
    new Float32Array([-1, -1, 3, -1, -1, 3]), gl.STATIC_DRAW); // big triangle
  tex = gl.createTexture();
  blitProg = makeProgram(VERT2, FRAG_BLIT);
  return true;
}

function compileShader(type, src) {
  const s = gl.createShader(type);
  gl.shaderSource(s, src);
  gl.compileShader(s);
  if (!gl.getShaderParameter(s, gl.COMPILE_STATUS)) {
    const log = gl.getShaderInfoLog(s);
    gl.deleteShader(s);
    throw new Error(log || "shader compile failed");
  }
  return s;
}
function makeProgram(vsrc, fsrc) {
  const p = gl.createProgram();
  const vs = compileShader(gl.VERTEX_SHADER, vsrc);
  const fs = compileShader(gl.FRAGMENT_SHADER, fsrc);
  gl.attachShader(p, vs); gl.attachShader(p, fs);
  gl.bindAttribLocation(p, 0, "aPos");
  gl.linkProgram(p);
  gl.deleteShader(vs); gl.deleteShader(fs);
  if (!gl.getProgramParameter(p, gl.LINK_STATUS)) {
    const log = gl.getProgramInfoLog(p);
    gl.deleteProgram(p);
    throw new Error(log || "link failed");
  }
  return p;
}

function uploadTexture() {
  if (!img) return;
  gl.bindTexture(gl.TEXTURE_2D, tex);
  gl.pixelStorei(gl.UNPACK_ALIGNMENT, 1);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA32F, img.w, img.h, 0,
    gl.RGBA, gl.FLOAT, img.data);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, texFilter);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, texFilter);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
}

function fitCanvas() {
  if (!img) return;
  const vp = $("viewport").getBoundingClientRect();
  const s = Math.min(vp.width / img.w, vp.height / img.h, 1) || 1;
  $("gl").width = img.w; $("gl").height = img.h;
  $("gl").style.width = Math.round(img.w * s) + "px";
  $("gl").style.height = Math.round(img.h * s) + "px";
}

function render() {
  if (!img || !gl) return;
  const prog = quadProg || blitProg;
  gl.viewport(0, 0, $("gl").width, $("gl").height);
  gl.clearColor(0, 0, 0, 1); gl.clear(gl.COLOR_BUFFER_BIT);
  gl.useProgram(prog);
  gl.bindBuffer(gl.ARRAY_BUFFER, vbo);
  gl.enableVertexAttribArray(0);
  gl.vertexAttribPointer(0, 2, gl.FLOAT, false, 0, 0);
  gl.activeTexture(gl.TEXTURE0);
  gl.bindTexture(gl.TEXTURE_2D, tex);
  const ut = gl.getUniformLocation(prog, "uTex");
  if (ut) gl.uniform1i(ut, 0);
  const ue = gl.getUniformLocation(prog, "uExposure");
  if (ue) gl.uniform1f(ue, Math.pow(2, parseFloat($("exposure").value)));
  gl.drawArrays(gl.TRIANGLES, 0, 3);
}

/* ---- EXR decode --------------------------------------------------------- */
function decodeEXR(bytes) {
  const p = M._malloc(bytes.length);
  M.HEAPU8.set(bytes, p);
  const wp = M._malloc(4), hp = M._malloc(4);
  const rgba = M._exrw_decode_rgba(p, bytes.length, wp, hp);
  const w = M.HEAP32[wp >> 2], h = M.HEAP32[hp >> 2];
  M._free(p); M._free(wp); M._free(hp);
  if (!rgba || w <= 0 || h <= 0) return null;
  const data = M.HEAPF32.slice(rgba >> 2, (rgba >> 2) + w * h * 4);
  M._exrw_free(rgba);
  return { w, h, data };
}

async function loadEXRBytes(bytes, name) {
  const decoded = decodeEXR(bytes);
  if (!decoded) { setStatus("failed to decode " + (name || "EXR"), true); return; }
  img = decoded;
  $("viewport").classList.add("has-image");
  $("imginfo").textContent = `${name || "image"} — ${img.w}×${img.h}, float RGBA`;
  fitCanvas();
  uploadTexture();
  rebuild();
}

/* ---- config introspection + UI population -------------------------------- */
function reparseConfig() {
  const text = $("editor").value;
  if (cfgPtr) { M._tocw_free_config(cfgPtr); cfgPtr = 0; }
  const cp = cstr(text);
  cfgPtr = M._tocw_parse(cp, M.lengthBytesUTF8(text));
  M._free(cp);
  return cfgPtr !== 0;
}
function fillSelect(sel, items, keep) {
  const prev = keep && [...sel.options].some(o => o.value === keep) ? keep : null;
  sel.innerHTML = "";
  for (const it of items) {
    const o = document.createElement("option");
    o.value = it; o.textContent = it; sel.appendChild(o);
  }
  if (prev) sel.value = prev;
}
function populateFromConfig() {
  // colorspaces
  const ncs = M._tocw_num_colorspaces(cfgPtr);
  const css = [];
  for (let i = 0; i < ncs; i++) css.push(ustr(M._tocw_colorspace_name(cfgPtr, i)));
  const slRole = ustr(M._tocw_role(cfgPtr, cstr("scene_linear")));
  fillSelect($("srccs"), css, slRole || $("srccs").value);
  if (slRole && css.includes(slRole)) $("srccs").value = slRole;
  // displays
  const nd = M._tocw_num_displays(cfgPtr);
  const disp = [];
  for (let i = 0; i < nd; i++) disp.push(ustr(M._tocw_display_name(cfgPtr, i)));
  fillSelect($("display"), disp, $("display").value);
  populateViews();
}
function populateViews() {
  const d = $("display").value;
  if (!d) { fillSelect($("view"), []); return; }
  const dp = cstr(d);
  const nv = M._tocw_num_views(cfgPtr, dp);
  const vs = [];
  for (let i = 0; i < nv; i++) vs.push(ustr(M._tocw_view_name(cfgPtr, dp, i)));
  M._free(dp);
  fillSelect($("view"), vs, $("view").value);
}

/* ---- build processor + JIT compile the shader --------------------------- */
function rebuild() {
  if (!cfgPtr || !img) return;
  const src = $("srccs").value, disp = $("display").value, view = $("view").value;
  let ops = 0;
  const sp = cstr(src);
  if (disp && view) {
    const d2 = cstr(disp), v2 = cstr(view);
    ops = M._tocw_processor_view(cfgPtr, sp, d2, v2);
    M._free(d2); M._free(v2);
  } else {
    ops = M._tocw_processor(cfgPtr, sp, sp);
  }
  M._free(sp);
  if (!ops) {
    setCompile(`build failed for ${src} → ${disp}/${view} (transform unsupported)`, true);
    quadProg = null; render(); return;
  }
  // JIT -> GLSL
  const gp = M._tocw_jit_glsl(ops);
  const glsl = ustr(gp);
  if (gp) M._tocw_free_str(gp);
  M._tocw_free_ops(ops);
  if (!glsl) { setCompile("GLSL emit failed", true); quadProg = null; render(); return; }

  if (glsl.includes("ociolut")) {
    // pipeline needs LUT textures -> not wired in this demo; fall back to CPU.
    cpuFallback(); return;
  }
  const frag = glsl +
    "\nuniform sampler2D uTex;\nuniform float uExposure;\nin vec2 vUV;\nout vec4 oCol;\n" +
    "void main(){ vec4 c = texture(uTex, vUV); c.rgb *= uExposure; oCol = OCIOMain(c); }\n";
  try {
    const np = makeProgram(VERT2, frag);
    if (quadProg) gl.deleteProgram(quadProg);
    quadProg = np;
    // re-upload original image (CPU fallback may have replaced the texture)
    uploadTexture();
    setCompile(`compiled GPU shader — ${(glsl.length / 1024).toFixed(1)} KB GLSL`, false);
  } catch (e) {
    setCompile("shader compile error: " + e.message, true);
    quadProg = null;
  }
  render();
}

/* CPU fallback for pipelines that need LUT textures (rare in this demo). */
function cpuFallback() {
  const src = $("srccs").value, disp = $("display").value, view = $("view").value;
  const sp = cstr(src);
  let ops;
  if (disp && view) { const d = cstr(disp), v = cstr(view); ops = M._tocw_processor_view(cfgPtr, sp, d, v); M._free(d); M._free(v); }
  else ops = M._tocw_processor(cfgPtr, sp, sp);
  M._free(sp);
  if (!ops) { setCompile("CPU build failed", true); return; }
  const n = img.w * img.h * 4;
  const buf = M._malloc(n * 4);
  M.HEAPF32.set(img.data, buf >> 2);
  M._tocw_apply(ops, buf, img.w * img.h, 4);
  const out = M.HEAPF32.slice(buf >> 2, (buf >> 2) + n);
  M._free(buf); M._tocw_free_ops(ops);
  gl.bindTexture(gl.TEXTURE_2D, tex);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA32F, img.w, img.h, 0, gl.RGBA, gl.FLOAT, out);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, texFilter);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, texFilter);
  quadProg = null; // blit
  setCompile("applied on CPU (LUT pipeline; GPU LUT upload not wired)", false);
  render();
}

/* ---- status helpers ----------------------------------------------------- */
function setStatus(s, err) { const e = $("status"); e.textContent = s; e.className = "status " + (err ? "err" : ""); }
function setCompile(s, err) { const e = $("compilestatus"); e.textContent = s; e.className = "status mono " + (err ? "err" : "ok"); }

/* ---- editor gutter ------------------------------------------------------- */
function syncGutter() {
  const n = $("editor").value.split("\n").length;
  let g = "";
  for (let i = 1; i <= n; i++) g += i + "\n";
  $("gutter").textContent = g;
  $("gutter").scrollTop = $("editor").scrollTop;
}

/* ---- wide gamut toggle --------------------------------------------------- */
function applyP3() {
  const on = $("p3").checked && p3Supported;
  try { gl.drawingBufferColorSpace = on ? "display-p3" : "srgb"; } catch (e) {}
  // pick a matching display if present
  const want = on ? "Display P3" : "sRGB";
  const opts = [...$("display").options].map(o => o.value);
  if (opts.includes(want)) { $("display").value = want; populateViews(); }
  rebuild();
}

/* ---- samples / fetch ----------------------------------------------------- */
const SAMPLES = [
  { name: "scene_linear.exr (synthetic ACEScg)", url: "./scene_linear.exr" },
  { name: "openexr-images: ScanLines/CrissyField", url: "../../../openexr-images/ScanLines/CrissyField.exr" },
  { name: "openexr-images: ScanLines/Cannon", url: "../../../openexr-images/ScanLines/Cannon.exr" },
  { name: "openexr-images: Chromaticities/Rec709", url: "../../../openexr-images/Chromaticities/Rec709.exr" },
];
async function fetchSample(url, name) {
  setStatus("fetching " + name + " …");
  try {
    const r = await fetch(url);
    if (!r.ok) throw new Error("HTTP " + r.status);
    const buf = new Uint8Array(await r.arrayBuffer());
    await loadEXRBytes(buf, name);
    setStatus("loaded " + name);
  } catch (e) { setStatus("fetch failed: " + e.message + " (serve openexr-images alongside, or drop a file)", true); }
}

/* ---- init --------------------------------------------------------------- */
async function init() {
  M = await factory();
  if (!initGL()) return;

  // default config + sample list
  const cfgText = await (await fetch("./default.ocio")).text();
  $("editor").value = cfgText;
  syncGutter();
  reparseConfig();
  populateFromConfig();

  for (const s of SAMPLES) {
    const o = document.createElement("option");
    o.value = s.url; o.textContent = s.name; $("sample").appendChild(o);
  }

  // events
  $("file").addEventListener("change", async (e) => {
    const f = e.target.files[0]; if (!f) return;
    await loadEXRBytes(new Uint8Array(await f.arrayBuffer()), f.name);
  });
  $("loadsample").addEventListener("click", () => {
    const o = $("sample").selectedOptions[0];
    if (o) fetchSample(o.value, o.textContent);
  });
  const vp = $("viewport");
  vp.addEventListener("dragover", (e) => { e.preventDefault(); vp.classList.add("drag"); });
  vp.addEventListener("dragleave", () => vp.classList.remove("drag"));
  vp.addEventListener("drop", async (e) => {
    e.preventDefault(); vp.classList.remove("drag");
    const f = e.dataTransfer.files[0]; if (!f) return;
    await loadEXRBytes(new Uint8Array(await f.arrayBuffer()), f.name);
  });
  $("srccs").addEventListener("change", rebuild);
  $("display").addEventListener("change", () => { populateViews(); rebuild(); });
  $("view").addEventListener("change", rebuild);
  $("exposure").addEventListener("input", () => {
    $("evlabel").textContent = parseFloat($("exposure").value).toFixed(1) + " EV";
    render();
  });
  $("p3").addEventListener("change", applyP3);
  $("compile").addEventListener("click", () => {
    if (!reparseConfig()) { setCompile("config parse error", true); return; }
    populateFromConfig();
    rebuild();
  });
  $("editor").addEventListener("input", syncGutter);
  $("editor").addEventListener("scroll", () => { $("gutter").scrollTop = $("editor").scrollTop; });
  window.addEventListener("resize", () => { fitCanvas(); render(); });

  // load the bundled synthetic image to start
  await fetchSample(SAMPLES[0].url, SAMPLES[0].name);
}
init();
