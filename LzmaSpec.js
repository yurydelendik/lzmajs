/* Any copyright is dedicated to the Public Domain.
 * http://creativecommons.org/publicdomain/zero/1.0/ */

// Direct port with small improvements to JavaScript of the reference code.

/* LzmaSpec.c -- LZMA Reference Decoder
2013-07-28 : Igor Pavlov : Public domain */

// This code implements LZMA file decoding according to LZMA specification.
// This code is not optimized for speed.

'use strict';

function InputStream(buffer) {
  this.buffer = buffer;
  this.processed = 0;
}
InputStream.prototype = {
  get available() {
    return this.buffer.length - this.processed;
  },
  readByte: function () {
    if (this.processed >= this.buffer.length) {
      throw new Error("Unexpected end of file");
    }
    return this.buffer[this.processed++];
  }
};

function OutputStream() {
  this.buffer = new Uint8Array(128);
  this.processed = 0;
}

OutputStream.prototype = {
  writeBytes: function (data) {
    var needLength = this.processed + data.length;
    if (needLength > this.buffer.length) {
      var newLength = this.buffer.length * 2;
      while (newLength < needLength) {
        newLength *= 2;
      }
      var newBuffer = new Uint8Array(newLength);
      newBuffer.set(this.buffer);
      this.buffer = newBuffer;
    }
    this.buffer.set(data, this.processed);
    this.processed = needLength;
  },
  toUint8Array: function () {
    return this.buffer.subarray(0, this.processed);
  }
};

function OutWindow(outStream) {
  this.outStream = outStream;
  this.buf = null;
  this.pos = 0;
  this.size = 0;
  this.isFull = false;
  this.writePos = 0;

  this.totalPos = 0;
}
OutWindow.prototype = {
  create: function(dictSize) {
    this.buf = new Uint8Array(dictSize);
    this.pos = 0;
    this.size = dictSize;
    this.isFull = false;
    this.writePos = 0;
    this.totalPos = 0;
  },
  putByte: function(b) {
    this.totalPos++;
    this.buf[this.pos++] = b;
    if (this.pos === this.size) {
      this.flush();
      this.pos = 0;
      this.isFull = true;
    }
  },
  getByte: function (dist) {
    return this.buf[dist <= this.pos ? this.pos - dist : this.size - dist + this.pos];
  },
  flush: function () {
    if (this.writePos < this.pos) {
      this.outStream.writeBytes(this.buf.subarray(this.writePos, this.pos));
      this.writePos = this.pos === this.size ? 0 : this.pos;
    }
  },
  copyMatch: function (dist, len) {
    var pos = this.pos;
    var size = this.size;
    var buffer = this.buf;
    var getPos = dist <= pos ? pos - dist : size - dist + pos;
    var left = len;
    while (left > 0) {
      var chunk = Math.min(Math.min(left, size - pos), size - getPos);
      for (var i = 0; i < chunk; i++) {
        var b = buffer[getPos++];
        buffer[pos++] = b;
      }
      if (pos === size) {
        this.pos = pos;
        this.flush();
        pos = 0;
        this.isFull = true;
      }
      if (getPos === size) {
        getPos = 0;
      }
      left -= chunk;
    }
    this.pos = pos;
    this.totalPos += len;
  },
  checkDistance: function(dist) {
    return dist <= this.pos || this.isFull;
  },
  isEmpty: function() {
    return this.pos === 0 && !this.isFull;
  }
};

var kNumBitModelTotalBits = 11;
var kNumMoveBits = 5;

var PROB_INIT_VAL = ((1 << kNumBitModelTotalBits) >> 1);

function createProbsArray(length) {
  var p = new Uint16Array(length);
  for (var i = 0; i < length; i++) {
    p[i] = PROB_INIT_VAL;
  }
  return p;
}

var kTopValue = 1 << 24;

function RangeDecoder(inStream) {
  this.inStream = inStream;
  this.range = 0;
  this.code = 0;
  this.corrupted = false;
}
RangeDecoder.prototype = {
  init: function () {
    if (this.inStream.readByte() !== 0) {
      this.corrupted = true;
    }

    this.range = 0xFFFFFFFF | 0;
    var code = 0;
    for (var i = 0; i < 4; i++) {
      code = (code << 8) | this.inStream.readByte();
    }

    if (code === this.range) {
      this.corrupted = true;
    }
    this.code = code;
  },
  isFinishedOK: function () {
    return this.code === 0;
  },
  decodeDirectBits: function (numBits) {
    var res = 0;
    var range = this.range;
    var code = this.code;
    do {
      range = (range >>> 1) | 0;
      code = (code - range) | 0;
      var t = code >> 31; // if high bit set -1, otherwise 0
      code = (code + (range & t)) | 0;

      if (code === range) {
        this.corrupted = true;
      }

      if (range >= 0 && range < kTopValue) {
        range = range << 8;
        code = (code << 8) | this.inStream.readByte();
      }

      res = ((res << 1) + t + 1) | 0;
    } while (--numBits);
    this.range = range;
    this.code = code;
    return res;
  },
  decodeBit: function (prob, index) {
    var range = this.range;
    var code = this.code;
    var v = prob[index];
    var bound = (range >>> kNumBitModelTotalBits) * v; // keep unsigned
    var symbol;
    if ((code >>> 0) < bound) {
      v = (v + (((1 << kNumBitModelTotalBits) - v) >> kNumMoveBits)) | 0;
      range = bound | 0;
      symbol = 0;
    } else {
      v = (v - (v >> kNumMoveBits)) | 0;
      code = (code - bound) | 0;
      range = (range - bound) | 0;
      symbol = 1;
    }
    prob[index] = v & 0xFFFF;

    if (range >= 0 && range < kTopValue) {
      range = range << 8;
      code = (code << 8) | this.inStream.readByte();
    }
    this.range = range;
    this.code = code;

    return symbol;
  }
};

function bitTreeReverseDecode(probs, offset, numBits, rc) {
  var m = 1;
  var symbol = 0;
  for (var i = 0; i < numBits; i++) {
    var bit = rc.decodeBit(probs, m + offset);
    m = (m << 1) + bit;
    symbol |= bit << i;
  }
  return symbol;
}

function BitTreeDecoder(numBits) {
  this.numBits = numBits;
  this.probs = createProbsArray(1 << numBits);
}
BitTreeDecoder.prototype = {
  decode: function (rc) {
    var m = 1;
    for (var i = 0; i < this.numBits; i++) {
      m = (m << 1) + rc.decodeBit(this.probs, m);
    }
    return m - (1 << this.numBits);
  },
  reverseDecode: function (rc) {
    return bitTreeReverseDecode(this.probs, 0, this.numBits, rc);
  }
};

function createBitTreeDecoderArray(numBits, length) {
  var p = [];
  p.length = length;
  for (var i = 0; i < length; i++) {
    p[i] = new BitTreeDecoder(numBits);
  }
  return p;
}

var kNumPosBitsMax = 4;

var kNumStates = 12;
var kNumLenToPosStates = 4;
var kNumAlignBits = 4;
var kStartPosModelIndex = 4;
var kEndPosModelIndex = 14;
var kNumFullDistances = 1 << (kEndPosModelIndex >> 1);
var kMatchMinLen = 2;

function LenDecoder() {
  this.choice = createProbsArray(2);
  this.lowCoder = createBitTreeDecoderArray(3, 1 << kNumPosBitsMax);
  this.midCoder = createBitTreeDecoderArray(3, 1 << kNumPosBitsMax);
  this.highCoder = new BitTreeDecoder(8);
}
LenDecoder.prototype = {
  decode: function(rc, posState) {
    if (rc.decodeBit(this.choice, 0) === 0) {
      return this.lowCoder[posState].decode(rc);
    }
    if (rc.decodeBit(this.choice, 1) === 0) {
      return 8 + this.midCoder[posState].decode(rc);
    }
    return 16 + this.highCoder.decode(rc);
  }
};

function updateState_Literal(state) {
  if (state < 4) {
    return 0;
  } else if (state < 10) {
    return state - 3;
  } else {
    return state - 6;
  }
}
function updateState_Match(state) {
  return state < 7 ? 7 : 10;
}
function updateState_Rep(state) {
  return state < 7 ? 8 : 11;
}
function updateState_ShortRep(state) {
  return state < 7 ? 9 : 11;
}

var LZMA_DIC_MIN = 1 << 12;

var MAX_DECODE_BITS_CALLS = 48;

function LzmaDecoder(inStream, outStream) {
  this.rangeDec = new RangeDecoder(inStream);
  this.outWindow = new OutWindow(outStream);

  this.markerIsMandatory = false;
  this.lc = 0;
  this.pb = 0;
  this.lp = 0;
  this.dictSize = 0;
  this.dictSizeInProperties = 0;
  this.unpackSize = undefined;
  this.leftToUnpack = undefined;

  this.reps = new Int32Array(4);
  this.state = 0;
}
LzmaDecoder.prototype = {
  decodeProperties: function(properties) {
    var d = properties[0];
    if (d >= (9 * 5 * 5)) {
      throw new Error("Incorrect LZMA properties");
    }
    this.lc = d % 9;
    d = (d / 9) | 0;
    this.pb = (d / 5) | 0;
    this.lp = d % 5;
    this.dictSizeInProperties = 0;
    for (var i = 0; i < 4; i++) {
      this.dictSizeInProperties |= properties[i + 1] << (8 * i);
    }
    this.dictSize = this.dictSizeInProperties;
    if (this.dictSize < LZMA_DIC_MIN) {
      this.dictSize = LZMA_DIC_MIN;
    }
  },
  create: function() {
    this.outWindow.create(this.dictSize);

    this.init();
    this.rangeDec.init();

    this.reps[0] = 0;
    this.reps[1] = 0;
    this.reps[2] = 0;
    this.reps[3] = 0;
    this.state = 0;
    this.leftToUnpack = this.unpackSize;
  },
  decodeLiteral: function (state, rep0) {
    var outWindow = this.outWindow;
    var rangeDec = this.rangeDec;

    var prevByte = 0;
    if (!outWindow.isEmpty()) {
      prevByte = outWindow.getByte(1);
    }

    var symbol = 1;
    var litState = ((outWindow.totalPos & ((1 << this.lp) - 1)) << this.lc) + (prevByte >> (8 - this.lc));
    var probsIndex = 0x300 * litState;

    if (state >= 7) {
      var matchByte = outWindow.getByte(rep0 + 1);
      do {
        var matchBit = (matchByte >> 7) & 1;
        matchByte <<= 1;
        var bit = rangeDec.decodeBit(this.litProbs, probsIndex + (((1 + matchBit) << 8) + symbol));
        symbol = (symbol << 1) | bit;
        if (matchBit !== bit) {
          break;
        }
      } while (symbol < 0x100);
    }
    while (symbol < 0x100) {
      symbol = (symbol << 1) | rangeDec.decodeBit(this.litProbs, probsIndex + symbol);
    }
    return (symbol - 0x100) & 0xFF;
  },
  decodeDistance: function (len) {
    var lenState = len;
    if (lenState > kNumLenToPosStates - 1) {
      lenState = kNumLenToPosStates - 1;
    }
    var rangeDec = this.rangeDec;
    var posSlot = this.posSlotDecoder[lenState].decode(rangeDec);
    if (posSlot < 4) {
      return posSlot;
    }
    var numDirectBits = (posSlot >> 1) - 1;
    var dist = (2 | (posSlot & 1)) << numDirectBits;
    if (posSlot < kEndPosModelIndex) {
      dist = (dist + bitTreeReverseDecode(this.posDecoders, dist - posSlot, numDirectBits, rangeDec)) | 0;
    } else {
      dist = (dist + (rangeDec.decodeDirectBits(numDirectBits - kNumAlignBits) << kNumAlignBits)) | 0;
      dist = (dist + this.alignDecoder.reverseDecode(rangeDec)) | 0;
    }
    return dist;
  },
  init: function () {
    this.litProbs = createProbsArray(0x300 << (this.lc + this.lp));

    this.posSlotDecoder = createBitTreeDecoderArray(6, kNumLenToPosStates);
    this.alignDecoder = new BitTreeDecoder(kNumAlignBits);
    this.posDecoders = createProbsArray(1 + kNumFullDistances - kEndPosModelIndex);

    this.isMatch = createProbsArray(kNumStates << kNumPosBitsMax);
    this.isRep = createProbsArray(kNumStates);
    this.isRepG0 = createProbsArray(kNumStates);
    this.isRepG1 = createProbsArray(kNumStates);
    this.isRepG2 = createProbsArray(kNumStates);
    this.isRep0Long = createProbsArray(kNumStates << kNumPosBitsMax);

    this.lenDecoder = new LenDecoder();
    this.repLenDecoder = new LenDecoder();
  },
  decode: function(notFinal) {
    var rangeDec = this.rangeDec;
    var outWindow = this.outWindow;
    var pb = this.pb;
    var dictSize = this.dictSize;
    var markerIsMandatory = this.markerIsMandatory;
    var leftToUnpack = this.leftToUnpack;

    var isMatch = this.isMatch;
    var isRep = this.isRep;
    var isRepG0 = this.isRepG0;
    var isRepG1 = this.isRepG1;
    var isRepG2 = this.isRepG2;
    var isRep0Long = this.isRep0Long;
    var lenDecoder = this.lenDecoder;
    var repLenDecoder = this.repLenDecoder;

    var rep0 = this.reps[0];
    var rep1 = this.reps[1];
    var rep2 = this.reps[2];
    var rep3 = this.reps[3];
    var state = this.state;

    while (true) {
      // Based on worse case scenario one byte consumed per decodeBit calls,
      // reserving keeping some amount of bytes in the input stream for
      // non-final data blocks.
      if (notFinal && rangeDec.inStream.available < MAX_DECODE_BITS_CALLS) {
        this.outWindow.flush();
        break;
      }

      if (leftToUnpack === 0 && !markerIsMandatory) {
        this.outWindow.flush();
        if (rangeDec.isFinishedOK()) {
          return LZMA_RES_FINISHED_WITHOUT_MARKER;
        }
      }

      var posState = outWindow.totalPos & ((1 << pb) - 1);

      if (rangeDec.decodeBit(isMatch, (state << kNumPosBitsMax) + posState) === 0) {
        if (leftToUnpack === 0) {
          return LZMA_RES_ERROR;
        }
        outWindow.putByte(this.decodeLiteral(state, rep0));
        state = updateState_Literal(state);
        leftToUnpack--;
        continue;
      }

      var len;
      if (rangeDec.decodeBit(isRep, state) !== 0) {
        if (leftToUnpack === 0) {
          return LZMA_RES_ERROR;
        }
        if (outWindow.isEmpty()) {
          return LZMA_RES_ERROR;
        }
        if (rangeDec.decodeBit(isRepG0, state) === 0) {
          if (rangeDec.decodeBit(isRep0Long, (state << kNumPosBitsMax) + posState) === 0) {
            state = updateState_ShortRep(state);
            outWindow.putByte(outWindow.getByte(rep0 + 1));
            leftToUnpack--;
            continue;
          }
        } else {
          var dist;
          if (rangeDec.decodeBit(isRepG1, state) === 0) {
            dist = rep1;
          } else {
            if (rangeDec.decodeBit(isRepG2, state) === 0) {
              dist = rep2;
            } else {
              dist = rep3;
              rep3 = rep2;
            }
            rep2 = rep1;
          }
          rep1 = rep0;
          rep0 = dist;
        }
        len = repLenDecoder.decode(rangeDec, posState);
        state = updateState_Rep(state);
      } else {
        rep3 = rep2;
        rep2 = rep1;
        rep1 = rep0;
        len = lenDecoder.decode(rangeDec, posState);
        state = updateState_Match(state);
        rep0 = this.decodeDistance(len);
        if (rep0 === -1) {
          this.outWindow.flush();
          return rangeDec.isFinishedOK() ?
            LZMA_RES_FINISHED_WITH_MARKER :
            LZMA_RES_ERROR;
        }

        if (leftToUnpack === 0) {
          return LZMA_RES_ERROR;
        }
        if (rep0 >= dictSize || !outWindow.checkDistance(rep0)) {
          return LZMA_RES_ERROR;
        }
      }
      len += kMatchMinLen;
      var isError = false;
      if (leftToUnpack !== undefined && leftToUnpack < len) {
        len = leftToUnpack;
        isError = true;
      }
      outWindow.copyMatch(rep0 + 1, len);
      leftToUnpack -= len;
      if (isError) {
        return LZMA_RES_ERROR;
      }
    }

    this.state = state;
    this.reps[0] = rep0;
    this.reps[1] = rep1;
    this.reps[2] = rep2;
    this.reps[3] = rep3;
    this.leftToUnpack = leftToUnpack;
    return LZMA_RES_NOT_COMPLETE;
  }
};

var LZMA_RES_ERROR = 0;
var LZMA_RES_FINISHED_WITH_MARKER = 1;
var LZMA_RES_FINISHED_WITHOUT_MARKER = 2;
var LZMA_RES_NOT_COMPLETE = 3;

function decodeLzma(buffer) {
  if (!buffer) {
    throw new Error("input data is not specified");
  }

  var inStream = new InputStream(buffer);
  var outStream = new OutputStream();

  var lzmaDecoder = new LzmaDecoder(inStream, outStream);

  var header = new Uint8Array(13);
  var i;
  for (i = 0; i < 13; i++) {
    header[i] = inStream.readByte();
  }
  lzmaDecoder.decodeProperties(header);

  var unpackSize = 0;
  var unpackSizeDefined = false;
  for (i = 0; i < 8; i++)
  {
    var b = header[5 + i];
    if (b !== 0xFF) {
      unpackSizeDefined = true;
    }
    unpackSize |= b << (8 * i);
  }

  lzmaDecoder.markerIsMandatory = !unpackSizeDefined;
  lzmaDecoder.unpackSize = unpackSizeDefined ? unpackSize : undefined;
  lzmaDecoder.create();

  var res = lzmaDecoder.decode(false);

  if (res === LZMA_RES_ERROR) {
    throw new Error("LZMA decoding error");
  } else if (res === LZMA_RES_NOT_COMPLETE) {
    throw new Error("Decoding is not complete");
  } else if (res === LZMA_RES_FINISHED_WITH_MARKER) {
    if (unpackSizeDefined) {
      if (lzmaDecoder.outWindow.outStream.processed != unpackSize) {
        throw new Error("Finished with end marker before than specified size");
      }
    }
  } else {
    throw new Error("Internal Error");
  }

  return outStream.toUint8Array();
}

if (typeof exports !== 'undefined') {
  exports.decodeLzma = decodeLzma;
}
