"use strict";

(function(root) {
  const MAX_VALUE = 0x7fffffff;

  // Initialize SHA2-256 constants
  const K = new Uint32Array(320), H = new Uint32Array(64);
  let __i, __j, __iroot = (n, r) => Math.pow(n, 1 / r) * 4294967296;
  // Construct list of first 64 primes (less than 320)
  for (__i = 18; __i > 1; __i--) {
    for (__j = __i; __j < 320;) {
      K[__j += __i] = 1;
    }
  }

  // i is 1 from previous loop
  for (__j = 0; __j < 64;) {
    if (!K[++__i]) {
      H[__j] = __iroot(__i, 2);
      K[__j++] = __iroot(__i, 3);
    }
  }

  // Computes padded version of a message for use with SHA2
  // m (message): Uint8Array
  const SHA256_Pad = (m) => {
    let mLen = m.length, pLen = (mLen & ~63) + ((mLen & 63) < 56 ? 64 : 128);
    let bitLenHi = (mLen / 0x20000000) | 0, bitLenLo = mLen << 3;

    let r = new Uint8Array(pLen);
    r.set(m);

    r[mLen] = 0x80;  pLen -= 7;  r[pLen++] = bitLenHi >>> 16;
    r[pLen++] = bitLenHi >>>  8; r[pLen++] = bitLenHi >>>  0;
    r[pLen++] = bitLenLo >>> 24; r[pLen++] = bitLenLo >>> 16;
    r[pLen++] = bitLenLo >>>  8; r[pLen++] = bitLenLo >>>  0;

    return r;
  };

  // Computes SHA2-256 of a message
  // r (result):  DataView
  // m (message): Uint8Array
  // o (offset):  Number
  const SHA256_Raw = (r, m, o) => {
    let h0 = H[0], h1 = H[1], h2 = H[2], h3 = H[3], h4 = H[4], h5 = H[5], h6 = H[6], h7 = H[7];
    const w = new Uint32Array(64);

    let off = 0, len = m.length, i;
    while (len >= 64) {
      let a = h0, b = h1, c = h2, d = h3, e = h4, f = h5, g = h6, h = h7, u, j, t1, t2;

      for (i = 0; i < 16; i++) {
        j = off + i*4;
        w[i] = (m[j]<<24) | (m[j+1]<<16) | (m[j+2]<<8) | m[j+3];
      }

      // i is 16 from previous loop
      for (; i < 64; i++) {
        u = w[i-2];
        t1 = ((u>>>17) | (u<<(32-17))) ^ ((u>>>19) | (u<<(32-19))) ^ (u>>>10);

        u = w[i-15];
        t2 = ((u>>>7) | (u<<(32-7))) ^ ((u>>>18) | (u<<(32-18))) ^ (u>>>3);

        w[i] = (((t1 + w[i-7]) | 0) + ((t2 + w[i-16]) | 0)) | 0;
      }

      for (i = 0; i < 64; i++) {
        t1 = ((((((e>>>6) | (e<<(32-6))) ^ ((e>>>11) | (e<<(32-11))) ^
             ((e>>>25) | (e<<(32-25)))) + ((e & f) ^ (~e & g))) | 0) +
             ((h + ((K[i] + w[i]) | 0)) | 0)) | 0;

        t2 = ((((a>>>2) | (a<<(32-2))) ^ ((a>>>13) | (a<<(32-13))) ^
             ((a>>>22) | (a<<(32-22)))) + ((a & b) ^ (a & c) ^ (b & c))) | 0;

        h = g; g = f; f = e;
        e = (d + t1) | 0;
        d = c; c = b; b = a;
        a = (t1 + t2) | 0;
      }

      h0 = (h0 + a) | 0; h1 = (h1 + b) | 0;
      h2 = (h2 + c) | 0; h3 = (h3 + d) | 0;
      h4 = (h4 + e) | 0; h5 = (h5 + f) | 0;
      h6 = (h6 + g) | 0; h7 = (h7 + h) | 0;

      off += 64; len -= 64;
    }

    r.setUint32(o,      h0); r.setUint32(o += 4, h1);
    r.setUint32(o += 4, h2); r.setUint32(o += 4, h3);
    r.setUint32(o += 4, h4); r.setUint32(o += 4, h5);
    r.setUint32(o += 4, h6); r.setUint32(o += 4, h7);
  };

  const SHA256_U8 = m => {
    const dv = new DataView(new ArrayBuffer(32));
    SHA256_Raw(dv, SHA256_Pad(m), 0);
    return ensureUint8Array(dv);
  };

  const PBKDF2_HMAC_SHA256_OneIter = (password, salt, dkLen) => {
    // compress password if it's longer than hash block length
    password = (password.length <= 64) ? password : SHA256_U8(password);

    const passLength = password.length;
    const innerLen = 64 + 4 + salt.length;
    const inner = SHA256_Pad(new Uint8Array(innerLen));
    const outerKey = SHA256_Pad(new Uint8Array(96));
    const outerDv = new DataView(outerKey.buffer);
    const dk = new DataView((new Uint8Array((dkLen + 31) & ~31)).buffer);

    let i, offset;

    // inner = (password ^ ipad) || salt || counter
    inner.fill(0x36, 0, 64);
    for (i = 0; i < passLength; i++) { inner[i] ^= password[i]; }
    inner.set(salt, 64);

    outerKey.fill(0x5c, 0, 64);
    for (i = 0; i < passLength; i++) outerKey[i] ^= password[i];

    const incrementCounter = (i => {
      const dv = new DataView(inner.buffer, innerLen - 4);
      return () => dv.setUint32(0, ++i);
    })(0);

    // output blocks = SHA256(outerKey || SHA256(inner)) ...
    for (offset = 0; offset < dkLen; offset += 32) {
      incrementCounter();
      SHA256_Raw(outerDv, inner, 64);
      SHA256_Raw(dk, outerKey, offset);
    }

    return new Uint8Array(dk.buffer, 0, dkLen);
  };

  // The following is an adaptation of scryptsy
  // See: https://www.npmjs.com/package/scryptsy
  const blockmix_salsa8 = (BY, Yi, r, x, _X) => {
    let i;

    arraycopy(BY, (2 * r - 1) * 16, _X, 0, 16);
    for (i = 0; i < 2 * r; i++) {
      blockxor(BY, i * 16, _X, 16);
      salsa20_8(_X, x);
      arraycopy(_X, 0, BY, Yi + (i * 16), 16);
    }

    for (i = 0; i < r; i++) {
      arraycopy(BY, Yi + (i * 2) * 16, BY, (i * 16), 16);
    }

    for (i = 0; i < r; i++) {
      arraycopy(BY, Yi + (i * 2 + 1) * 16, BY, (i + r) * 16, 16);
    }
  };

  const R = (a, b) => (a << b) | (a >>> (32 - b));

  const salsa20_8 = (B, x) => {
    arraycopy(B, 0, x, 0, 16);

    for (let i = 8; i > 0; i -= 2) {
      x[ 4] ^= R(x[ 0] + x[12],  7); x[ 8] ^= R(x[ 4] + x[ 0],  9);
      x[12] ^= R(x[ 8] + x[ 4], 13); x[ 0] ^= R(x[12] + x[ 8], 18);
      x[ 9] ^= R(x[ 5] + x[ 1],  7); x[13] ^= R(x[ 9] + x[ 5],  9);
      x[ 1] ^= R(x[13] + x[ 9], 13); x[ 5] ^= R(x[ 1] + x[13], 18);
      x[14] ^= R(x[10] + x[ 6],  7); x[ 2] ^= R(x[14] + x[10],  9);
      x[ 6] ^= R(x[ 2] + x[14], 13); x[10] ^= R(x[ 6] + x[ 2], 18);
      x[ 3] ^= R(x[15] + x[11],  7); x[ 7] ^= R(x[ 3] + x[15],  9);
      x[11] ^= R(x[ 7] + x[ 3], 13); x[15] ^= R(x[11] + x[ 7], 18);
      x[ 1] ^= R(x[ 0] + x[ 3],  7); x[ 2] ^= R(x[ 1] + x[ 0],  9);
      x[ 3] ^= R(x[ 2] + x[ 1], 13); x[ 0] ^= R(x[ 3] + x[ 2], 18);
      x[ 6] ^= R(x[ 5] + x[ 4],  7); x[ 7] ^= R(x[ 6] + x[ 5],  9);
      x[ 4] ^= R(x[ 7] + x[ 6], 13); x[ 5] ^= R(x[ 4] + x[ 7], 18);
      x[11] ^= R(x[10] + x[ 9],  7); x[ 8] ^= R(x[11] + x[10],  9);
      x[ 9] ^= R(x[ 8] + x[11], 13); x[10] ^= R(x[ 9] + x[ 8], 18);
      x[12] ^= R(x[15] + x[14],  7); x[13] ^= R(x[12] + x[15],  9);
      x[14] ^= R(x[13] + x[12], 13); x[15] ^= R(x[14] + x[13], 18);
    }

    for (let i = 0; i < 16; ++i) { B[i] += x[i]; }
  };

  // naive approach... going back to loop unrolling may yield additional performance
  const blockxor = (S, Si, D, len) => {
    for (let i = 0; i < len; i++) {
      D[i] ^= S[Si + i]
    }
  };

  const arraycopy = (src, srcPos, dest, destPos, length) => {
    while (length--) {
      dest[destPos++] = src[srcPos++];
    }
  };

  const ensureUint8Array = (value, name) => {
    if (typeof value === 'object' && 'byteLength' in value) {
      return new Uint8Array(value);
    } else {
      throw new Error(name + ' must be an ArrayBuffer or ArrayBufferView');
    }
  };

  const ensureInteger = (value, name) => {
    if (typeof(value) !== 'number' || (value % 1)) { throw new Error('invalid ' + name); }
    return value;
  };

  // N = Cpu cost, r = Memory cost, p = parallelization cost
  // callback(error, progress, key)
  const _scrypt = (password, salt, N, r, p, dkLen, callback) => {

    N = ensureInteger(N, 'N');
    r = ensureInteger(r, 'r');
    p = ensureInteger(p, 'p');

    dkLen = ensureInteger(dkLen, 'dkLen');

    if (N === 0 || (N & (N - 1)) !== 0) { throw new Error('N must be power of 2'); }

    if (N > MAX_VALUE / 128 / r) { throw new Error('N too large'); }
    if (r > MAX_VALUE / 128 / p) { throw new Error('r too large'); }

    password = ensureUint8Array(password, 'password');
    salt = ensureUint8Array(salt, 'salt');

    let b = PBKDF2_HMAC_SHA256_OneIter(password, salt, p * 128 * r);
    const B = new Uint32Array(p * 32 * r)
    for (let i = 0; i < B.length; i++) {
      const j = i * 4;
      B[i] = (b[j + 3] << 24) |(b[j + 2] << 16) | (b[j + 1] << 8) |b[j + 0];
    }

    const XY = new Uint32Array(64 * r);
    const V = new Uint32Array(32 * r * N);

    const Yi = 32 * r;

    // scratch space
    const x = new Uint32Array(16);       // salsa20_8
    const _X = new Uint32Array(16);      // blockmix_salsa8

    const totalOps = p * N * 2;
    let currentOp = 0;
    let lastPercent = null;

    // Set this to true to abandon the scrypt on the next step
    let stop = false;

    // State information
    let state = 0;
    let i0 = 0, i1;
    let Bi;

    // How many blockmix_salsa8 can we do per step?
    const limit = callback ? parseInt(1000 / r) : 0xffffffff;

    // Trick from scrypt-async; if there is a setImmediate shim in place, use it
    const nextTick = (typeof(setImmediate) !== 'undefined') ? setImmediate : setTimeout;

    // This is really all I changed; making scryptsy a state machine so we occasionally
    // stop and give other evnts on the evnt loop a chance to run. ~RicMoo
    const incrementalSMix = () => {
      if (stop) {
        return callback(new Error('cancelled'), currentOp / totalOps);
      }

      let maxProgressSteps = 100, steps;

      switch (state) {
        case 0:
          // for (var i = 0; i < p; i++)...
          Bi = i0 * 32 * r;

          arraycopy(B, Bi, XY, 0, Yi);                       // ROMix - 1

          state = 1;                                         // Move to ROMix 2
          i1 = 0;

          // Fall through

        case 1:

          // Run up to 1000 steps of the first inner smix loop
          steps = N - i1;
          if (steps > limit) { steps = limit; }
          for (let i = 0; i < steps; i++) {                  // ROMix - 2
            arraycopy(XY, 0, V, (i1 + i) * Yi, Yi)         // ROMix - 3
            blockmix_salsa8(XY, Yi, r, x, _X);             // ROMix - 4
          }

          // for (var i = 0; i < N; i++)
          i1 += steps;
          currentOp += steps;

          if (callback) {
            // Call the callback with the progress (optionally stopping us)
            let percent = parseInt(maxProgressSteps * currentOp / totalOps);
            if (percent !== lastPercent) {
              stop = callback(null, currentOp / totalOps);
              if (stop) { break; }
              lastPercent = percent;
            }
          }

          if (i1 < N) { break; }

          i1 = 0;                                          // Move to ROMix 6
          state = 2;

          // Fall through

        case 2:

          // Run up to 1000 steps of the second inner smix loop
          steps = N - i1;
          if (steps > limit) { steps = limit; }
          for (let i = 0; i < steps; i++) {                // ROMix - 6
            const offset = (2 * r - 1) * 16;             // ROMix - 7
            const j = XY[offset] & (N - 1);
            blockxor(V, j * Yi, XY, Yi);                 // ROMix - 8 (inner)
            blockmix_salsa8(XY, Yi, r, x, _X);           // ROMix - 9 (outer)
          }

          // for (var i = 0; i < N; i++)...
          i1 += steps;
          currentOp += steps;

          // Call the callback with the progress (optionally stopping us)
          if (callback) {
            let percent = parseInt(maxProgressSteps * currentOp / totalOps);
            if (percent !== lastPercent) {
              stop = callback(null, currentOp / totalOps);
              if (stop) { break; }
              lastPercent = percent;
            }
          }

          if (i1 < N) { break; }

          arraycopy(XY, 0, B, Bi, Yi);                     // ROMix - 10

          // for (var i = 0; i < p; i++)...
          i0++;
          if (i0 < p) {
            state = 0;
            break;
          }

          b = [];
          for (let i = 0; i < B.length; i++) {
            b.push((B[i] >>  0) & 0xff);
            b.push((B[i] >>  8) & 0xff);
            b.push((B[i] >> 16) & 0xff);
            b.push((B[i] >> 24) & 0xff);
          }

          const derivedKey = PBKDF2_HMAC_SHA256_OneIter(password, b, dkLen);

          // Send the result to the callback
          if (callback) { callback(null, 1.0, derivedKey); }

          // Done; don't break (which would reschedule)
          return derivedKey;
      }

      // Schedule the next steps
      if (callback) { nextTick(incrementalSMix); }
    }

    // Run the smix state machine until completion
    if (!callback) {
      while (true) {
        const derivedKey = incrementalSMix();
        if (derivedKey != undefined) { return derivedKey; }
      }
    }

    // Bootstrap the async incremental smix
    incrementalSMix();
  };

  const lib = {
    scrypt: (password, salt, N, r, p, dkLen, progressCallback) => {
      return new Promise((resolve, reject) => {
        let lastProgress = 0;
        if (progressCallback) { progressCallback(0); }
        _scrypt(password, salt, N, r, p, dkLen, (error, progress, key) => {
          if (error) {
            reject(error);
          } else if (key) {
            if (progressCallback && lastProgress !== 1) {
              progressCallback(1);
            }
            resolve(new Uint8Array(key));
          } else if (progressCallback && progress !== lastProgress) {
            lastProgress = progress;
            return progressCallback(progress);
          }
        });
      });
    },
    syncScrypt: (password, salt, N, r, p, dkLen) => new Uint8Array(
      _scrypt(password, salt, N, r, p, dkLen)
    )
  };

  // node.js
  if (typeof(exports) !== 'undefined') {
    module.exports = lib;

    // Web Browsers
  } else if (root) {

    root.scrypt = lib;
  }

})(this);
