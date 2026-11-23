// A tiny stack virtual machine for make.fun's tiny stack ISA (the kit's
// generator/subject/ISA.md): one run answers every instance of a set,
// writing each program's exact output bytes to /output/<id>/stdout.bin and
// the code it ended with (a trap's code included) to /output/<id>/exit.txt.
// Exact ISA.md semantics, traps and limits included; deterministic.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// One char per opcode byte 0x00..0x53: charCode - 35 packs its immediate
// length (high nibble), pops and pushes (two bits each); '!' is no opcode.
// Decoded once into lookup arrays.
const T = "#4d')-.2!!!!!!!!,,,,,,,(,,,(,,,!,,,!!!!!!!!!!!!!CGGC#!!!!!!!!!!!(+!!!!!!!!!!!!!!''$'";
const IM = new Int8Array(256).fill(-1);
const PO = new Int8Array(256);
const PU = new Int8Array(256);
for (let i = 0; i < 84; i++) {
  const v = T.charCodeAt(i) - 35;
  if (v >= 0) {
    IM[i] = v >> 4;
    PO[i] = (v >> 2) & 3;
    PU[i] = v & 3;
  }
}

// Runs one program to its end: [bytes written, exit code].
function run(P: Uint8Array, N: Uint8Array): [Uint8Array, number] {
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0;
  let cp = 0;
  let ol = 0;
  let ip = 0;
  let pc = 0;
  let st = 0;
  const n = P.length;
  const fin = (e: number): [Uint8Array, number] => [out.slice(0, ol), e];
  for (;;) {
    if (st >= 1e6) return fin(10); // the step order is ISA.md's
    if (pc < 0 || pc >= n) return fin(9);
    const op = P[pc];
    const imm = IM[op];
    if (imm < 0) return fin(5);
    if (pc + imm >= n) return fin(9);
    st++;
    if (sp < PO[op]) return fin(2);
    if (sp - PO[op] + PU[op] > 256) return fin(3);
    const nx = pc + 1 + imm;
    pc = nx;
    switch (op) {
      case 0x00: // HALT
        return fin(0);
      case 0x01: // PUSH8: sign-extended byte
        D[sp++] = (P[nx - 1] << 24) >> 24;
        break;
      case 0x02: // PUSH32: signed 32-bit little-endian
        D[sp++] = P[nx - 4] | (P[nx - 3] << 8) | (P[nx - 2] << 16) | (P[nx - 1] << 24);
        break;
      case 0x03: // POP
        sp--;
        break;
      case 0x04: // DUP
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 0x05: { // SWAP
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 0x06: // OVER
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 0x07: { // ROT
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 0x17: // NEG: wraps
        D[sp - 1] = (-D[sp - 1]) | 0;
        break;
      case 0x1b: // NOT
        D[sp - 1] = ~D[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break; // low 32 bits of the exact product
          case 0x13: // DIV: truncated toward zero
            if (b === 0) return fin(4);
            r = (a / b) | 0;
            break;
          case 0x14: // MOD: the sign of a
            if (b === 0) return fin(4);
            r = (a % b) | 0;
            break;
          case 0x15: // DIVU: unsigned
            if (b === 0) return fin(4);
            r = ((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16: // MODU
            if (b === 0) return fin(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break; // shift counts: low 5 bits only
          case 0x1d: r = a >> (b & 31); break; // arithmetic
          case 0x1e: r = (a >>> (b & 31)) | 0; break; // logical
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // 0x22 LTU
        }
        D[sp - 2] = r;
        sp--;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP, JZ, JNZ
        const rel = ((P[nx - 2] | (P[nx - 1] << 8)) << 16) >> 16;
        if (op === 0x30 || (op === 0x31) === (D[--sp] === 0)) pc = nx + rel;
        break;
      }
      case 0x33: // CALL
        if (cp === 64) return fin(7);
        C[cp++] = nx;
        pc = P[nx - 2] | (P[nx - 1] << 8);
        break;
      case 0x34: // RET
        if (cp === 0) return fin(8);
        pc = C[--cp];
        break;
      case 0x40: { // LOAD
        const a = D[sp - 1];
        if (a < 0 || a > 255) return fin(6);
        D[sp - 1] = M[a];
        break;
      }
      case 0x41: { // STORE
        const a = D[sp - 1];
        if (a < 0 || a > 255) return fin(6);
        M[a] = D[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT: decimal; past the limit writes nothing
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return fin(11);
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        sp--;
        break;
      }
      case 0x51: // PUTC: v AND 255
        if (ol >= 65536) return fin(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 0x52: // IN
        D[sp++] = ip < N.length ? N[ip++] : -1;
        break;
      default: // 0x53 EXIT: the low byte
        return fin(D[sp - 1] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const [bytes, code] = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), bytes);
  writeFileSync(join(O, id, 'exit.txt'), code + '\n');
}
