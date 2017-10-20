var fs = require('fs');
var tinyexr = require('./tinyexr.js')

var data = new Uint8Array(fs.readFileSync("../../asakusa.exr"))
console.log(data.length)

var instance = new tinyexr.EXRLoader(data);

console.log(instance.ok())
console.log(instance.width())
console.log(instance.height())

var image = instance.getBytes()
console.log(image[0])
