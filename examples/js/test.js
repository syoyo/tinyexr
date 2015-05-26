var fs = require('fs');
var tinyexr = require('../../tinyexr')

var data = new Uint8Array(fs.readFileSync("../../asakusa.exr"))
console.log(data.length)

ParseEXRHeaderFromMemory = tinyexr.cwrap(
  'ParseEXRHeaderFromMemory', 'number', ['number', 'number', 'number']
);

LoadEXRFromMemory = tinyexr.cwrap(
  'LoadEXRFromMemory', 'number', ['number', 'number', 'string']
);

var widthPtr = tinyexr._malloc(4);
var widthHeap = new Uint8Array(tinyexr.HEAPU8.buffer, widthPtr, 4);
var heightPtr = tinyexr._malloc(4);
var heightHeap = new Uint8Array(tinyexr.HEAPU8.buffer, heightPtr, 4);
var ptr = tinyexr._malloc(data.length)
var dataHeap = new Uint8Array(tinyexr.HEAPU8.buffer, ptr, data.length);
dataHeap.set(new Uint8Array(data.buffer))

var ret  = ParseEXRHeaderFromMemory(widthHeap.byteOffset, heightHeap.byteOffset, dataHeap.byteOffset);
console.log(ret)

var width = (new Int32Array(widthHeap.buffer, widthHeap.byteOffset, 1))[0];
var height = (new Int32Array(heightHeap.buffer, heightHeap.byteOffset, 1))[0];
console.log(width, height)

var imgDataLen = width * height * 4 * 4;
var img = tinyexr._malloc(imgDataLen)
var imgHeap = new Float32Array(tinyexr.HEAPU8.buffer, img, imgDataLen/4);
ret = LoadEXRFromMemory(imgHeap.byteOffset, dataHeap.byteOffset, null)

// Now imgHeap contains HDR image: float x RGBA x width x height


//console.log(imgHeap[0])

