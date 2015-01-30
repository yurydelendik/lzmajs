/* Any copyright is dedicated to the Public Domain.
 * http://creativecommons.org/publicdomain/zero/1.0/ */

 var fs = require('fs'),
    lzma = require('../LzmaSpec.js');

if (process.argv.length < 4) {
  console.log('Usage: node decompressswf.js <inputfile> <outputfile>');
  exit(1);
}

var inputFile = process.argv[2];
var outputFile = process.argv[3];

var compressed = new Uint8Array(fs.readFileSync(inputFile));

if (compressed[0] !== 0x5a || compressed[1] !== 0x57 && compressed[2] !== 0x53) {
  console.error('Invalid input file header');
}

var newHeader = new Uint8Array(compressed.subarray(0, 8));
newHeader[0] = 0x46;

// Fixing the header based on
// http://helpx.adobe.com/flash-player/kb/exception-thrown-you-decompress-lzma-compressed.html
var lzmaHeader = new Uint8Array(13);
lzmaHeader.set(compressed.subarray(12, 17), 0);
lzmaHeader.set(compressed.subarray(4, 8), 5);
for (var c = 8, i = 5; i < 9; i++) {
  if (lzmaHeader[i] >= c) {
    lzmaHeader[i] -= c;
    break;
  }
  lzmaHeader[i] = 256 + lzmaHeader[i] - c;
  c = 1;
}
compressed.set(lzmaHeader, 4);

var decompressed = lzma.decodeLzma(compressed.subarray(4));

fs.writeFileSync(outputFile, new Buffer(newHeader));
fs.appendFileSync(outputFile, new Buffer(decompressed));
