/* Any copyright is dedicated to the Public Domain.
 * http://creativecommons.org/publicdomain/zero/1.0/ */

 var fs = require('fs'),
    path = require('path'),
    lzma = require('../LzmaSpec.js');

var inputFile = process.argv[2] ||
                path.resolve(path.dirname(process.argv[1]), 'demo.lzma');
var compressed = new Uint8Array(fs.readFileSync(inputFile));

var decompressed = lzma.decodeLzma(compressed);

console.log(new Buffer(decompressed).toString('ascii'));
