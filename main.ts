// Tiny stack VM: runs each bytecode program in the input directory and
// writes its output bytes and exit code. Node 22, stdlib only, deterministic.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Per-opcode facts from the ISA: [immediate bytes, values popped, pushed].
const IMM = new Uint8Array(256), POP = new Uint8Array(256);
const PSH = new Uint8Array(256), KNOWN = new Uint8Array(256);
for (const [op, im, po, pu] of [
  [0, 0, 0, 0], [1, 1, 0, 1], [2, 4, 0, 1], [3, 0, 1, 0],
  [4, 0, 1, 2], [5, 0, 2, 2], [6, 0, 2, 3], [7, 0, 3, 3],
  [16, 0, 2, 1], [17, 0, 2, 1], [18, 0, 2, 1], [19, 0, 2, 1],
  [20, 0, 2, 1], [21, 0, 2, 1], [22, 0, 2, 1], [23, 0, 1, 1],
  [24, 0, 2, 1], [25, 0, 2, 1], [26, 0, 2, 1], [27, 0, 1, 1],
  [28, 0, 2, 1], [29, 0, 2, 1], [30, 0, 2, 1], [32, 0, 2, 1],
  [33, 0, 2, 1], [34, 0, 2, 1], [48, 2, 0, 0], [49, 2, 1, 0],
  [50, 2, 1, 0], [51, 2, 0, 0], [52, 0, 0, 0], [64, 0, 1, 1],
  [65, 0, 2, 0], [80, 0, 1, 0], [81, 0, 1, 0], [82, 0, 0, 1],
  [83, 0, 1, 0],
]) { IMM[op] = im; POP[op] = po; PSH[op] = pu; KNOWN[op] = 1; }

// Runs one program on its input bytes; returns [output bytes, exit code].
// A trap ends the run at once with the trap's code, keeping what was printed.
function run(p: Uint8Array, input: Uint8Array): [Uint8Array, number] {
  const S = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let cp = 0;
  const M = new Int32Array(256);
  const O = new Uint8Array(65536);
  let ol = 0, ip = 0, pc = 0, st = 0;
  const n = p.length;
  const done = (c: number): [Uint8Array, number] => [O.slice(0, ol), c];
  for (;;) {
    if (st === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = p[pc];
    if (!KNOWN[op]) return done(5);
    const im = IMM[op];
    if (pc + im >= n) return done(9);
    st++;
    const nx = pc + 1 + im, po = POP[op];
    if (sp < po) return done(2);
    if (sp - po + PSH[op] > 256) return done(3);
    pc = nx;
    switch (op) {
      case 0: return done(0); // HALT
      case 1: S[sp++] = (p[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 2: S[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break; // PUSH32
      case 3: sp--; break; // POP
      case 4: S[sp] = S[sp - 1]; sp++; break; // DUP
      case 5: { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; break; } // SWAP
      case 6: S[sp] = S[sp - 2]; sp++; break; // OVER
      case 7: { const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; break; } // ROT
      case 23: S[sp - 1] = -S[sp - 1] | 0; break; // NEG wraps
      case 27: S[sp - 1] = ~S[sp - 1]; break; // NOT
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30: case 32:
      case 33: case 34: {
        const b = S[sp - 1], a = S[sp - 2];
        let r: number;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b);
        else if (op === 19) {
          if (b === 0) return done(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 20) {
          if (b === 0) return done(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 21) {
          if (b === 0) return done(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 22) {
          if (b === 0) return done(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31);
        else if (op === 30) r = (a >>> (b & 31)) | 0;
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2; S[sp++] = r;
        break;
      }
      case 48: case 49: case 50: { // JMP / JZ / JNZ
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 48) { const v = S[--sp]; take = op === 49 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 51: // CALL: absolute address, unsigned immediate
        if (cp === 64) return done(7);
        C[cp++] = nx; pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52: // RET
        if (cp === 0) return done(8);
        pc = C[--cp];
        break;
      case 64: { // LOAD
        const ad = S[sp - 1];
        if (ad < 0 || ad >= 256) return done(6);
        S[sp - 1] = M[ad];
        break;
      }
      case 65: { // STORE: (value address --), address on top
        const ad = S[sp - 1], v = S[sp - 2];
        if (ad < 0 || ad >= 256) return done(6);
        sp -= 2; M[ad] = v;
        break;
      }
      case 80: { // PRINT: decimal ASCII, '-' only for negatives
        const t = String(S[sp - 1]);
        if (ol + t.length > 65536) return done(11);
        sp--;
        for (let i = 0; i < t.length; i++) O[ol++] = t.charCodeAt(i);
        break;
      }
      case 81: // PUTC: one byte, low 8 bits
        if (ol + 1 > 65536) return done(11);
        O[ol++] = S[--sp] & 255;
        break;
      case 82: // IN: -1 once the input is used up
        S[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      case 83: // EXIT: code is the low byte
        return done(S[--sp] & 255);
    }
  }
}

// Each instance directory holds program.bin and input.bin; answer it with
// stdout.bin and exit.txt.
for (const e of readdirSync(IN, { withFileTypes: true }).sort((a, b) => (a.name < b.name ? -1 : 1))) {
  if (!e.isDirectory()) continue;
  const d = join(IN, e.name);
  const prog = readFileSync(join(d, 'program.bin'));
  let input: Buffer;
  try { input = readFileSync(join(d, 'input.bin')); } catch { input = Buffer.alloc(0); }
  const [stdout, code] = run(prog, input);
  const od = join(OUT, e.name);
  mkdirSync(od, { recursive: true });
  writeFileSync(join(od, 'stdout.bin'), stdout);
  writeFileSync(join(od, 'exit.txt'), String(code) + '\n');
}
