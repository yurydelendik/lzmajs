// Direct port to JavaScript from the reference code

/* LzmaSpec.c -- LZMA Reference Decoder
2013-07-28 : Igor Pavlov : Public domain */

// This code implements LZMA file decoding according to LZMA specification.
// This code is not optimized for speed.

function InputStream() {
  this.file = undefined;
  this.processed = 0;
}
InputStream.prototype = {
  init: function () {
    this.processed = 0;
  },
  readByte: function () {
    var c = this.file.getc();
    if (c < 0) {
      throw new Error("Unexpected end of file");
    }
    this.processed++;
    return c | 0;
  }
};

function OutStream() {
  this.file = undefined;
  this.processed = 0;
}

OutStream.prototype = {
  init: function () {
    this.processed = 0;
  },
  writeByte: function (b) {
    if (!this.file.putc(b)) {
      throw new Error("File writing error");
    }
    this.processed++;
  }
};

function OutWindow() {
  this.outStream = new OutStream();
  this.buf = null;
  this.pos = 0;
  this.size = 0;
  this.isFull = false;

  this.totalPos = 0;
}
OutWindow.prototype = {
  create: function(dictSize) {
    this.buf = new Uint8Array(dictSize);
    this.pos = 0;
    this.size = dictSize;
    this.isFull = false;
    this.totalPos = 0;
  },
  putByte: function(b) {
    this.totalPos++;
    this.buf[this.pos++] = b;
    if (this.pos === this.size) {
      this.pos = 0;
      this.isFull = true;
    }
    this.outStream.writeByte(b);
  },
  getByte: function (dist) {
    return this.buf[dist <= this.pos ? this.pos - dist : this.size - dist + this.pos];
  },
  copyMatch: function (dist, len) {
    for (; len > 0; len--) {
      this.putByte(this.getByte(dist));
    }
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

function initProbs(p) {
  for (var i = 0; i < p.length; i++) {
    p[i] = PROB_INIT_VAL;
  }
}

var kTopValue = 1 << 24;

function RangeDecoder() {
  this.range = 0;
  this.code = 0;

  this.inStream = null;
}
RangeDecoder.prototype = {
  normalize: function () {
    if (this.range >= 0 && this.range < kTopValue) {
      this.range = (this.range << 8);
      this.code = (this.code << 8) | this.inStream.readByte();
    }
  },
  init: function () {
    this.corrupted = false;

    if (this.inStream.readByte() !== 0) {
      this.corrupted = true;
    }

    this.range = 0xFFFFFFFF | 0;
    this.code = 0;
    for (var i = 0; i < 4; i++) {
      this.code = (this.code << 8) | this.inStream.readByte();
    }

    if (this.code === this.range) {
      this.corrupted = true;
    }
  },
  isFinishedOK: function () {
    return this.code === 0;
  },
  decodeDirectBits: function (numBits) {
    var res = 0;
    do {
      this.range = (this.range >>> 1) | 0;
      this.code = (this.code - this.range) | 0;
      var t = this.code >> 31; // if high bit set -1, otherwise 0
      this.code = (this.code + (this.range & t)) | 0;

      if (this.code === this.range) {
        this.corrupted = true;
      }

      this.normalize();
      res = ((res << 1) + t + 1) | 0;
    } while (--numBits);
    return res;
  },
  decodeBit: function (prob, index) {
    var v = prob[index];
    var bound = (this.range >>> kNumBitModelTotalBits) * v; // keep unsigned
    var symbol;
    if ((this.code >>> 0) < bound) {
      v = (v + (((1 << kNumBitModelTotalBits) - v) >> kNumMoveBits)) | 0;
      this.range = bound | 0;
      symbol = 0;
    } else {
      v = (v - (v >> kNumMoveBits)) | 0;
      this.code = (this.code - bound) | 0;
      this.range = (this.range - bound) | 0;
      symbol = 1;
    }
    prob[index] = v & 0xFFFF;
    this.normalize();
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
  this.probs = new Uint16Array(1 << numBits);
}
BitTreeDecoder.prototype = {
  init: function () {
    initProbs(this.probs);
  },
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

var kNumPosBitsMax = 4;

var kNumStates = 12;
var kNumLenToPosStates = 4;
var kNumAlignBits = 4;
var kStartPosModelIndex = 4;
var kEndPosModelIndex = 14;
var kNumFullDistances = 1 << (kEndPosModelIndex >> 1);
var kMatchMinLen = 2;

function LenDecoder() {
  this.choice = new Uint16Array(2);
  this.lowCoder = []; this.lowCoder.length = 1 << kNumPosBitsMax;
  this.midCoder = []; this.midCoder.length = 1 << kNumPosBitsMax;
  for (var i = 0; i < this.lowCoder.length; i++) {
    this.lowCoder[i] = new BitTreeDecoder(3);
    this.midCoder[i] = new BitTreeDecoder(3);
  }
  this.highCoder = new BitTreeDecoder(8);
}
LenDecoder.prototype = {
  init: function () {
    initProbs(this.choice);
    for (var i = 0; i < this.lowCoder.length; i++) {
      this.lowCoder[i].init();
      this.midCoder[i].init();
    }
    this.highCoder.init();
  },
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

function LzmaDecoder() {
  this.rangeDec = new RangeDecoder();
  this.outWindow = new OutWindow();

  this.markerIsMandatory = false;
  this.lc = 0;
  this.pb = 0;
  this.lp = 0;
  this.dictSize = 0;
  this.dictSizeInProperties = 0;
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
  },
  decodeLiteral: function (state, rep0) {
    var prevByte = 0;
    if (!this.outWindow.isEmpty()) {
      prevByte = this.outWindow.getByte(1);
    }

    var symbol = 1;
    var litState = ((this.outWindow.totalPos & ((1 << this.lp) - 1)) << this.lc) + (prevByte >> (8 - this.lc));
    var probsIndex = 0x300 * litState;

    if (state >= 7) {
      var matchByte = this.outWindow.getByte(rep0 + 1);
      do {
        var matchBit = (matchByte >> 7) & 1;
        matchByte <<= 1;
        var bit = this.rangeDec.decodeBit(this.litProbs, probsIndex + (((1 + matchBit) << 8) + symbol));
        symbol = (symbol << 1) | bit;
        if (matchBit !== bit) {
          break;
        }
      } while (symbol < 0x100);
    }
    while (symbol < 0x100) {
      symbol = (symbol << 1) | this.rangeDec.decodeBit(this.litProbs, probsIndex + symbol);
    }
    this.outWindow.putByte((symbol - 0x100) & 0xFF);
  },
  initDist: function () {
    this.posSlotDecoder = []; this.posSlotDecoder.length = kNumLenToPosStates;
    for (var i = 0; i < kNumLenToPosStates; i++) {
      this.posSlotDecoder[i] = new BitTreeDecoder(6);
      this.posSlotDecoder[i].init();
    }
    this.alignDecoder = new BitTreeDecoder(kNumAlignBits);
    this.alignDecoder.init();
    this.posDecoders = new Uint16Array(1 + kNumFullDistances - kEndPosModelIndex);
    initProbs(this.posDecoders);
  },
  decodeDistance: function (len) {
    var lenState = len;
    if (lenState > kNumLenToPosStates - 1) {
      lenState = kNumLenToPosStates - 1;
    }
    var posSlot = this.posSlotDecoder[lenState].decode(this.rangeDec);
    if (posSlot < 4) {
      return posSlot;
    }
    var numDirectBits = (posSlot >> 1) - 1;
    var dist = (2 | (posSlot & 1)) << numDirectBits;
    if (posSlot < kEndPosModelIndex) {
      dist = (dist + bitTreeReverseDecode(this.posDecoders, dist - posSlot, numDirectBits, this.rangeDec)) | 0;
    } else
    {
      dist = (dist + (this.rangeDec.decodeDirectBits(numDirectBits - kNumAlignBits) << kNumAlignBits)) | 0;
      dist = (dist + this.alignDecoder.reverseDecode(this.rangeDec)) | 0;
    }
    return dist;
  },
  init: function () {
    this.litProbs = new Uint16Array(0x300 << (this.lc + this.lp));
    initProbs(this.litProbs);

    this.initDist();

    this.isMatch = new Uint16Array(kNumStates << kNumPosBitsMax);
    initProbs(this.isMatch);
    this.isRep = new Uint16Array(kNumStates);
    initProbs(this.isRep);
    this.isRepG0 = new Uint16Array(kNumStates);
    initProbs(this.isRepG0);
    this.isRepG1 = new Uint16Array(kNumStates);
    initProbs(this.isRepG1);
    this.isRepG2 = new Uint16Array(kNumStates);
    initProbs(this.isRepG2);
    this.isRep0Long = new Uint16Array(kNumStates << kNumPosBitsMax);
    initProbs(this.isRep0Long);

    this.lenDecoder = new LenDecoder();
    this.lenDecoder.init();
    this.repLenDecoder = new LenDecoder();
    this.repLenDecoder.init();
  },
  decode: function(unpackSize) {
    this.init();
    this.rangeDec.init();

    var rep0 = 0, rep1 = 0, rep2 = 0, rep3 = 0;
    var state = 0;

    while (true) {
      if (unpackSize === 0 && !this.markerIsMandatory) {
        if (this.rangeDec.isFinishedOK()) {
          return LZMA_RES_FINISHED_WITHOUT_MARKER;
        }
      }

      var posState = this.outWindow.totalPos & ((1 << this.pb) - 1);

      if (this.rangeDec.decodeBit(this.isMatch, (state << kNumPosBitsMax) + posState) === 0) {
        if (unpackSize === 0) {
          return LZMA_RES_ERROR;
        }
        this.decodeLiteral(state, rep0);
        state = updateState_Literal(state);
        unpackSize--;
        continue;
      }

      var len;
      if (this.rangeDec.decodeBit(this.isRep, state) !== 0) {
        if (unpackSize === 0) {
          return LZMA_RES_ERROR;
        }
        if (this.outWindow.isEmpty()) {
          return LZMA_RES_ERROR;
        }
        if (this.rangeDec.decodeBit(this.isRepG0, state) === 0) {
          if (this.rangeDec.decodeBit(this.isRep0Long, (state << kNumPosBitsMax) + posState) === 0) {
            state = updateState_ShortRep(state);
            this.outWindow.putByte(this.outWindow.getByte(rep0 + 1));
            unpackSize--;
            continue;
          }
        } else {
          var dist;
          if (this.rangeDec.decodeBit(this.isRepG1, state) === 0) {
            dist = rep1;
          } else {
            if (this.rangeDec.decodeBit(this.isRepG2, state) === 0) {
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
        len = this.repLenDecoder.decode(this.rangeDec, posState);
        state = updateState_Rep(state);
      } else {
        rep3 = rep2;
        rep2 = rep1;
        rep1 = rep0;
        len = this.lenDecoder.decode(this.rangeDec, posState);
        state = updateState_Match(state);
        rep0 = this.decodeDistance(len);
        if (rep0 === -1) {
          return this.rangeDec.isFinishedOK() ?
            LZMA_RES_FINISHED_WITH_MARKER :
            LZMA_RES_ERROR;
        }

        if (unpackSize === 0) {
          return LZMA_RES_ERROR;
        }
        if (rep0 >= this.dictSize || !this.outWindow.checkDistance(rep0)) {
          return LZMA_RES_ERROR;
        }
      }
      len += kMatchMinLen;
      var isError = false;
      if (unpackSize !== undefined && unpackSize < len) {
        len = unpackSize;
        isError = true;
      }
      this.outWindow.copyMatch(rep0 + 1, len);
      unpackSize -= len;
      if (isError) {
        return LZMA_RES_ERROR;
      }
    }
  }
};

var LZMA_RES_ERROR = 0;
var LZMA_RES_FINISHED_WITH_MARKER = 1;
var LZMA_RES_FINISHED_WITHOUT_MARKER = 2;

function main2(inFile, outFile) {
  console.log("LZMA Reference Decoder 9.31 : Igor Pavlov : Public domain : 2013-02-06");
  if (arguments.length === 0) {
    console.log("Use: lzmaSpec a.lzma outFile");
  }
  if (arguments.length !== 2) {
    throw new Error("you must specify two parameters");
  }

  var inStream = new InputStream();
  inStream.file = inFile;
  inStream.init();
  if (!inStream.file) {
    throw new Error("Can't open input file");
  }

  var lzmaDecoder = new LzmaDecoder();
  lzmaDecoder.outWindow.outStream.file = outFile;
  lzmaDecoder.outWindow.outStream.init();
  if (!lzmaDecoder.outWindow.outStream.file) {
    throw new Error("Can't open output file");
  }

  var header = new Uint8Array(13);
  var i;
  for (i = 0; i < 13; i++) {
    header[i] = inStream.readByte();
  }
  lzmaDecoder.decodeProperties(header);

  console.info("lc=%d, lp=%d, pb=%d", lzmaDecoder.lc, lzmaDecoder.lp, lzmaDecoder.pb);
  console.info("Dictionary Size in properties = %d", lzmaDecoder.dictSizeInProperties);
  console.info("Dictionary Size for decoding  = %d", lzmaDecoder.dictSize);

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
  if (!unpackSizeDefined) {
    unpackSize = undefined;
  }

  lzmaDecoder.markerIsMandatory = !unpackSizeDefined;

  if (unpackSizeDefined) {
    console.log("Uncompressed Size: " + unpackSize);
  } else {
    console.log("End marker is expected");
  }
  lzmaDecoder.rangeDec.inStream = inStream;

  lzmaDecoder.create();
  var res = lzmaDecoder.decode(unpackSize);

  console.log("Read    " + inStream.processed);
  console.log("Written " + lzmaDecoder.outWindow.outStream.processed);

  if (res === LZMA_RES_ERROR) {
    throw new Error("LZMA decoding error");
  } else if (res === LZMA_RES_FINISHED_WITHOUT_MARKER) {
    console.log("Finished without end marker");
  } else if (res === LZMA_RES_FINISHED_WITH_MARKER) {
    if (unpackSizeDefined) {
      if (lzmaDecoder.outWindow.outStream.processed != unpackSize) {
        throw new Error("Finished with end marker before than specified size");
      }
      console.log("Warning: ");
    }
    console.log("Finished with end marker");
  } else {
    throw new Error("Internal Error");
  }

  if (lzmaDecoder.rangeDec.corrupted) {
    console.log("Warning: LZMA stream is corrupted");
  }
}

function decodeLzma(bytes) {
  var inPos = 0;
  var inFile = {
    getc: function () {
      if (inPos >= bytes.length) {
        return -1;
      }
      return bytes[inPos++];
    }
  };
  var buffer = new Uint8Array(128);
  var outPos = 0;
  var outFile = {
    putc: function (b) {
      if (outPos >= buffer.length) {
        var newBuffer = new Uint8Array(buffer.length * 2);
        newBuffer.set(buffer);
        buffer = newBuffer;
      }
      buffer[outPos++] = b;
      return true;
    }
  };
  main2(inFile, outFile);
  return buffer.subarray(0, outPos);
}

if (typeof exports !== 'undefined') {
  exports.decodeLzma = decodeLzma;
}