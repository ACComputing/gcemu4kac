# chatgptgamecube4k.py — AC'S Gamecube emulator 0.1 [beta] / ACGC4K1.X core
# A real (minimal) GameCube emulator: Gekko CPU interpreter, 24 MB MEM1,
# GC disc image loader, stub GX/DSP, SI controller, VI framebuffer → Tk.
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import struct
import threading
import time
import array

# ---------------------------------------------------------------------------
# Constants — GameCube hardware specs
# ---------------------------------------------------------------------------
MEM1_SIZE       = 0x0180_0000          # 24 MiB main RAM
HW_REG_BASE     = 0x0C00_0000
VI_BASE         = 0x0C00_2000
SI_BASE         = 0x0C00_6400
DSP_BASE        = 0x0C00_5000
GX_FIFO_BASE    = 0x0C00_8000

GEKKO_CLOCK     = 486_000_000          # 486 MHz
FRAME_CYCLES    = GEKKO_CLOCK // 60    # cycles per frame at 60 fps
VI_WIDTH        = 640
VI_HEIGHT       = 480
FB_WIDTH        = 160                  # down-scaled for Tk rendering
FB_HEIGHT       = 120

GC_ISO_HEADER   = 0x2440              # bytes we care about in the ISO header
GC_MAGIC        = 0xC2339F3D
DOL_OFFSET_OFF  = 0x0420
DOL_SIZE_MAX    = 0x0080_0000          # 8 MiB cap for DOL loading

# ---------------------------------------------------------------------------
# Gekko CPU — PowerPC 750CL interpreter (integer subset)
# ---------------------------------------------------------------------------
class GekkoCPU:
    def __init__(self, mem):
        self.mem = mem
        self.gpr = array.array("I", [0] * 32)  # 32 general-purpose registers
        self.pc  = 0
        self.lr  = 0
        self.ctr = 0
        self.cr  = 0
        self.xer = 0
        self.msr = 0
        self.halted = False
        self.cycles = 0

    def reset(self, entry: int) -> None:
        for i in range(32):
            self.gpr[i] = 0
        self.pc = entry & 0xFFFF_FFFF
        self.lr = 0
        self.ctr = 0
        self.cr = 0
        self.xer = 0
        self.msr = 0x0000_2000
        self.halted = False
        self.cycles = 0
        self.gpr[1] = 0x0180_0000 - 0x100  # stack pointer near top of MEM1
        self.gpr[13] = 0x0000_0000          # small data area

    def read32(self, addr: int) -> int:
        return self.mem.read32(addr)

    def write32(self, addr: int, val: int) -> None:
        self.mem.write32(addr, val)

    def step(self) -> None:
        if self.halted:
            return
        if self.pc >= MEM1_SIZE:
            self.halted = True
            return

        instr = self.read32(self.pc)
        opcode = (instr >> 26) & 0x3F
        self.cycles += 1

        if instr == 0x4E800020:
            self.pc = self.lr & 0xFFFF_FFFC
            return
        if instr == 0x4E800420:
            self.pc = self.ctr & 0xFFFF_FFFC
            return
        if instr == 0x4E800021:
            old_pc = self.pc + 4
            self.pc = self.lr & 0xFFFF_FFFC
            self.lr = old_pc
            return
        if instr == 0x60000000:
            self.pc += 4
            return

        if opcode == 14:    # addi
            rd = (instr >> 21) & 0x1F
            ra = (instr >> 16) & 0x1F
            simm = self._sign16(instr & 0xFFFF)
            base = 0 if ra == 0 else self.gpr[ra]
            self.gpr[rd] = (base + simm) & 0xFFFF_FFFF
        elif opcode == 15:  # addis
            rd = (instr >> 21) & 0x1F
            ra = (instr >> 16) & 0x1F
            simm = self._sign16(instr & 0xFFFF)
            base = 0 if ra == 0 else self.gpr[ra]
            self.gpr[rd] = (base + (simm << 16)) & 0xFFFF_FFFF
        elif opcode == 31:  # extended opcodes
            self._exec_op31(instr)
        elif opcode == 32:  # lwz
            rd = (instr >> 21) & 0x1F
            ra = (instr >> 16) & 0x1F
            d = self._sign16(instr & 0xFFFF)
            ea = (0 if ra == 0 else self.gpr[ra]) + d
            self.gpr[rd] = self.read32(ea & 0xFFFF_FFFF)
        elif opcode == 36:  # stw
            rs = (instr >> 21) & 0x1F
            ra = (instr >> 16) & 0x1F
            d = self._sign16(instr & 0xFFFF)
            ea = (0 if ra == 0 else self.gpr[ra]) + d
            self.write32(ea & 0xFFFF_FFFF, self.gpr[rs])
        elif opcode == 34:  # lbz
            rd = (instr >> 21) & 0x1F
            ra = (instr >> 16) & 0x1F
            d = self._sign16(instr & 0xFFFF)
            ea = (0 if ra == 0 else self.gpr[ra]) + d
            self.gpr[rd] = self.mem.read8(ea & 0xFFFF_FFFF)
        elif opcode == 38:  # stb
            rs = (instr >> 21) & 0x1F
            ra = (instr >> 16) & 0x1F
            d = self._sign16(instr & 0xFFFF)
            ea = (0 if ra == 0 else self.gpr[ra]) + d
            self.mem.write8(ea & 0xFFFF_FFFF, self.gpr[rs] & 0xFF)
        elif opcode == 40:  # lhz
            rd = (instr >> 21) & 0x1F
            ra = (instr >> 16) & 0x1F
            d = self._sign16(instr & 0xFFFF)
            ea = (0 if ra == 0 else self.gpr[ra]) + d
            self.gpr[rd] = self.mem.read16(ea & 0xFFFF_FFFF)
        elif opcode == 44:  # sth
            rs = (instr >> 21) & 0x1F
            ra = (instr >> 16) & 0x1F
            d = self._sign16(instr & 0xFFFF)
            ea = (0 if ra == 0 else self.gpr[ra]) + d
            self.mem.write16(ea & 0xFFFF_FFFF, self.gpr[rs] & 0xFFFF)
        elif opcode == 18:  # b / bl
            li = instr & 0x03FF_FFFC
            if li & 0x0200_0000:
                li -= 0x0400_0000
            aa = bool(instr & 2)
            lk = bool(instr & 1)
            target = li if aa else (self.pc + li)
            if lk:
                self.lr = (self.pc + 4) & 0xFFFF_FFFF
            self.pc = target & 0xFFFF_FFFF
            return
        elif opcode == 16:  # bc
            bo = (instr >> 21) & 0x1F
            bi = (instr >> 16) & 0x1F
            bd = self._sign16(instr & 0xFFFC)
            lk = bool(instr & 1)
            aa = bool(instr & 2)
            ctr_ok = True
            cond_ok = True
            if not (bo & 0x04):
                self.ctr = (self.ctr - 1) & 0xFFFF_FFFF
                ctr_ok = bool(self.ctr) != bool(bo & 0x02)
            if not (bo & 0x10):
                cr_bit = (self.cr >> (31 - bi)) & 1
                cond_ok = bool(cr_bit) == bool(bo & 0x08)
            if ctr_ok and cond_ok:
                target = bd if aa else (self.pc + bd)
                if lk:
                    self.lr = (self.pc + 4) & 0xFFFF_FFFF
                self.pc = target & 0xFFFF_FFFF
                return
        elif opcode == 24:  # ori
            rs = (instr >> 21) & 0x1F
            ra = (instr >> 16) & 0x1F
            uimm = instr & 0xFFFF
            self.gpr[ra] = self.gpr[rs] | uimm
        elif opcode == 25:  # oris
            rs = (instr >> 21) & 0x1F
            ra = (instr >> 16) & 0x1F
            uimm = instr & 0xFFFF
            self.gpr[ra] = self.gpr[rs] | (uimm << 16)
        elif opcode == 28:  # andi.
            rs = (instr >> 21) & 0x1F
            ra = (instr >> 16) & 0x1F
            uimm = instr & 0xFFFF
            result = self.gpr[rs] & uimm
            self.gpr[ra] = result
            self._update_cr0(result)
        elif opcode == 11:  # cmpi (cmpwi)
            ra = (instr >> 16) & 0x1F
            simm = self._sign16(instr & 0xFFFF)
            a = self._to_signed(self.gpr[ra])
            if a < simm:
                c = 0x8
            elif a > simm:
                c = 0x4
            else:
                c = 0x2
            self.cr = (self.cr & 0x0FFF_FFFF) | (c << 28)
        elif opcode == 10:  # cmpli (cmplwi)
            ra = (instr >> 16) & 0x1F
            uimm = instr & 0xFFFF
            a = self.gpr[ra]
            if a < uimm:
                c = 0x8
            elif a > uimm:
                c = 0x4
            else:
                c = 0x2
            self.cr = (self.cr & 0x0FFF_FFFF) | (c << 28)
        elif opcode == 21:  # rlwinm
            rs = (instr >> 21) & 0x1F
            ra = (instr >> 16) & 0x1F
            sh = (instr >> 11) & 0x1F
            mb = (instr >> 6)  & 0x1F
            me = (instr >> 1)  & 0x1F
            rc = instr & 1
            rotated = ((self.gpr[rs] << sh) | (self.gpr[rs] >> (32 - sh))) & 0xFFFF_FFFF if sh else self.gpr[rs]
            mask = self._mask(mb, me)
            result = rotated & mask
            self.gpr[ra] = result
            if rc:
                self._update_cr0(result)
        elif opcode == 7:   # mulli
            rd = (instr >> 21) & 0x1F
            ra = (instr >> 16) & 0x1F
            simm = self._sign16(instr & 0xFFFF)
            self.gpr[rd] = (self._to_signed(self.gpr[ra]) * simm) & 0xFFFF_FFFF
        elif opcode == 8:   # subfic
            rd = (instr >> 21) & 0x1F
            ra = (instr >> 16) & 0x1F
            simm = self._sign16(instr & 0xFFFF)
            self.gpr[rd] = (simm - self._to_signed(self.gpr[ra])) & 0xFFFF_FFFF
        elif opcode == 12:  # addic
            rd = (instr >> 21) & 0x1F
            ra = (instr >> 16) & 0x1F
            simm = self._sign16(instr & 0xFFFF)
            self.gpr[rd] = (self.gpr[ra] + simm) & 0xFFFF_FFFF
        else:
            self.halted = True
            return

        self.pc = (self.pc + 4) & 0xFFFF_FFFF

    def _exec_op31(self, instr: int) -> None:
        xo = (instr >> 1) & 0x3FF
        rd = (instr >> 21) & 0x1F
        ra = (instr >> 16) & 0x1F
        rb = (instr >> 11) & 0x1F
        rc = instr & 1

        if xo == 266:    # add
            self.gpr[rd] = (self.gpr[ra] + self.gpr[rb]) & 0xFFFF_FFFF
        elif xo == 40:   # subf
            self.gpr[rd] = (self.gpr[rb] - self.gpr[ra]) & 0xFFFF_FFFF
        elif xo == 235:  # mullw
            self.gpr[rd] = (self._to_signed(self.gpr[ra]) * self._to_signed(self.gpr[rb])) & 0xFFFF_FFFF
        elif xo == 459:  # divwu
            if self.gpr[rb] != 0:
                self.gpr[rd] = self.gpr[ra] // self.gpr[rb]
            else:
                self.gpr[rd] = 0
        elif xo == 28:   # and
            self.gpr[ra] = self.gpr[rd] & self.gpr[rb]
        elif xo == 444:  # or
            self.gpr[ra] = self.gpr[rd] | self.gpr[rb]
        elif xo == 316:  # xor
            self.gpr[ra] = self.gpr[rd] ^ self.gpr[rb]
        elif xo == 536:  # srw
            shift = self.gpr[rb] & 0x3F
            self.gpr[ra] = (self.gpr[rd] >> shift) if shift < 32 else 0
        elif xo == 24:   # slw
            shift = self.gpr[rb] & 0x3F
            self.gpr[ra] = ((self.gpr[rd] << shift) & 0xFFFF_FFFF) if shift < 32 else 0
        elif xo == 0:    # cmp
            a = self._to_signed(self.gpr[ra])
            b = self._to_signed(self.gpr[rb])
            if a < b:
                c = 0x8
            elif a > b:
                c = 0x4
            else:
                c = 0x2
            crf = (rd >> 2) & 7
            shift = (7 - crf) * 4
            self.cr = (self.cr & ~(0xF << shift)) | (c << shift)
        elif xo == 32:   # cmpl
            a = self.gpr[ra]
            b = self.gpr[rb]
            if a < b:
                c = 0x8
            elif a > b:
                c = 0x4
            else:
                c = 0x2
            crf = (rd >> 2) & 7
            shift = (7 - crf) * 4
            self.cr = (self.cr & ~(0xF << shift)) | (c << shift)
        elif xo == 339:  # mfspr
            spr = ((instr >> 16) & 0x1F) | (((instr >> 11) & 0x1F) << 5)
            if spr == 8:
                self.gpr[rd] = self.lr
            elif spr == 9:
                self.gpr[rd] = self.ctr
            elif spr == 1:
                self.gpr[rd] = self.xer
        elif xo == 467:  # mtspr
            spr = ((instr >> 16) & 0x1F) | (((instr >> 11) & 0x1F) << 5)
            if spr == 8:
                self.lr = self.gpr[rd]
            elif spr == 9:
                self.ctr = self.gpr[rd]
            elif spr == 1:
                self.xer = self.gpr[rd]
        elif xo == 23:   # lwzx
            ea = (0 if ra == 0 else self.gpr[ra]) + self.gpr[rb]
            self.gpr[rd] = self.read32(ea & 0xFFFF_FFFF)
        elif xo == 151:  # stwx
            ea = (0 if ra == 0 else self.gpr[ra]) + self.gpr[rb]
            self.write32(ea & 0xFFFF_FFFF, self.gpr[rd])
        elif xo == 87:   # lbzx
            ea = (0 if ra == 0 else self.gpr[ra]) + self.gpr[rb]
            self.gpr[rd] = self.mem.read8(ea & 0xFFFF_FFFF)
        elif xo == 215:  # stbx
            ea = (0 if ra == 0 else self.gpr[ra]) + self.gpr[rb]
            self.mem.write8(ea & 0xFFFF_FFFF, self.gpr[rd] & 0xFF)
        elif xo == 26:   # cntlzw
            val = self.gpr[rd]
            count = 0
            if val == 0:
                count = 32
            else:
                while not (val & 0x8000_0000):
                    val <<= 1
                    count += 1
            self.gpr[ra] = count
        elif xo == 954:  # extsb
            val = self.gpr[rd] & 0xFF
            if val & 0x80:
                val |= 0xFFFF_FF00
            self.gpr[ra] = val & 0xFFFF_FFFF
        elif xo == 922:  # extsh
            val = self.gpr[rd] & 0xFFFF
            if val & 0x8000:
                val |= 0xFFFF_0000
            self.gpr[ra] = val & 0xFFFF_FFFF
        else:
            pass

        if rc and xo not in (339, 467, 0, 32):
            self._update_cr0(self.gpr[rd] if xo in (266, 40, 235, 459) else self.gpr[ra])

    def _update_cr0(self, val: int) -> None:
        s = self._to_signed(val)
        if s < 0:
            c = 0x8
        elif s > 0:
            c = 0x4
        else:
            c = 0x2
        self.cr = (self.cr & 0x0FFF_FFFF) | (c << 28)

    @staticmethod
    def _sign16(v: int) -> int:
        return v - 0x10000 if v & 0x8000 else v

    @staticmethod
    def _to_signed(v: int) -> int:
        return v - 0x1_0000_0000 if v & 0x8000_0000 else v

    @staticmethod
    def _mask(mb: int, me: int) -> int:
        if mb <= me:
            return ((1 << (32 - mb)) - 1) & ~((1 << (31 - me)) - 1)
        return ((1 << (32 - mb)) - 1) | ~((1 << (31 - me)) - 1) & 0xFFFF_FFFF


# ---------------------------------------------------------------------------
# Memory Bus — MEM1 + HW register stubs
# ---------------------------------------------------------------------------
class MemoryBus:
    def __init__(self):
        self.mem1 = bytearray(MEM1_SIZE)
        self.vi_regs = bytearray(256)
        self.si_regs = bytearray(256)
        self.dsp_regs = bytearray(256)
        self.gx_fifo = bytearray(256)
        self.vi_regs[0] = 0x01  # VI enabled

    def read8(self, addr: int) -> int:
        if addr < MEM1_SIZE:
            return self.mem1[addr]
        return 0

    def read16(self, addr: int) -> int:
        if addr < MEM1_SIZE:
            return struct.unpack_from(">H", self.mem1, addr)[0]
        return 0

    def read32(self, addr: int) -> int:
        if addr < MEM1_SIZE:
            return struct.unpack_from(">I", self.mem1, addr)[0]
        if VI_BASE <= addr < VI_BASE + 256:
            off = addr - VI_BASE
            return struct.unpack_from(">I", self.vi_regs, off & 0xFC)[0]
        if SI_BASE <= addr < SI_BASE + 256:
            off = addr - SI_BASE
            return struct.unpack_from(">I", self.si_regs, off & 0xFC)[0]
        return 0

    def write8(self, addr: int, val: int) -> None:
        if addr < MEM1_SIZE:
            self.mem1[addr] = val & 0xFF

    def write16(self, addr: int, val: int) -> None:
        if addr < MEM1_SIZE:
            struct.pack_into(">H", self.mem1, addr, val & 0xFFFF)

    def write32(self, addr: int, val: int) -> None:
        if addr < MEM1_SIZE:
            struct.pack_into(">I", self.mem1, addr, val & 0xFFFF_FFFF)
        elif VI_BASE <= addr < VI_BASE + 256:
            off = addr - VI_BASE
            struct.pack_into(">I", self.vi_regs, off & 0xFC, val & 0xFFFF_FFFF)
        elif SI_BASE <= addr < SI_BASE + 256:
            off = addr - SI_BASE
            struct.pack_into(">I", self.si_regs, off & 0xFC, val & 0xFFFF_FFFF)

    def load_blob(self, addr: int, data: bytes) -> None:
        end = min(addr + len(data), MEM1_SIZE)
        length = end - addr
        if length > 0:
            self.mem1[addr:end] = data[:length]


# ---------------------------------------------------------------------------
# GC Disc — reads a real .iso and parses the header + DOL executable
# ---------------------------------------------------------------------------
class GCDisc:
    def __init__(self):
        self.path: str | None = None
        self.game_id = ""
        self.game_name = ""
        self.dol_offset = 0
        self.fst_offset = 0
        self._header = b""

    def open(self, path: str) -> None:
        with open(path, "rb") as f:
            self._header = f.read(GC_ISO_HEADER)
        if len(self._header) < 0x0444:
            raise ValueError("File too small to be a GameCube ISO.")

        magic = struct.unpack_from(">I", self._header, 0x1C)[0]
        if magic != GC_MAGIC:
            raise ValueError(
                f"Bad GC magic: 0x{magic:08X} (expected 0x{GC_MAGIC:08X}). "
                "Not a valid GameCube disc image."
            )

        self.game_id = self._header[0:6].decode("ascii", "replace")
        self.game_name = self._header[0x20:0x0400].split(b"\x00", 1)[0].decode("ascii", "replace").strip()
        self.dol_offset = struct.unpack_from(">I", self._header, DOL_OFFSET_OFF)[0]
        self.fst_offset = struct.unpack_from(">I", self._header, 0x0424)[0]
        self.path = path

    def read_dol(self) -> tuple[int, bytes]:
        if not self.path or self.dol_offset == 0:
            raise RuntimeError("No disc or DOL offset is zero.")
        with open(self.path, "rb") as f:
            f.seek(self.dol_offset)
            dol_header = f.read(0x100)
        if len(dol_header) < 0x100:
            raise RuntimeError("DOL header truncated.")

        text_offsets = [struct.unpack_from(">I", dol_header, i * 4)[0] for i in range(7)]
        text_addrs   = [struct.unpack_from(">I", dol_header, 0x48 + i * 4)[0] for i in range(7)]
        text_sizes   = [struct.unpack_from(">I", dol_header, 0x90 + i * 4)[0] for i in range(7)]
        data_offsets = [struct.unpack_from(">I", dol_header, 0x1C + i * 4)[0] for i in range(11)]
        data_addrs   = [struct.unpack_from(">I", dol_header, 0x64 + i * 4)[0] for i in range(11)]
        data_sizes   = [struct.unpack_from(">I", dol_header, 0xAC + i * 4)[0] for i in range(11)]
        entry = struct.unpack_from(">I", dol_header, 0xE0)[0]

        sections: list[tuple[int, int, int]] = []
        for i in range(7):
            if text_sizes[i] > 0 and text_offsets[i] > 0:
                sections.append((text_offsets[i], text_addrs[i], text_sizes[i]))
        for i in range(11):
            if data_sizes[i] > 0 and data_offsets[i] > 0:
                sections.append((data_offsets[i], data_addrs[i], data_sizes[i]))

        merged = bytearray()
        load_addr = entry
        with open(self.path, "rb") as f:
            for file_off, mem_addr, size in sections:
                f.seek(self.dol_offset + file_off)
                blob = f.read(size)
                if mem_addr < load_addr:
                    load_addr = mem_addr
                merged_offset = mem_addr - load_addr
                if merged_offset + len(blob) > len(merged):
                    merged.extend(b"\x00" * (merged_offset + len(blob) - len(merged)))
                merged[merged_offset:merged_offset + len(blob)] = blob

        if len(merged) > DOL_SIZE_MAX:
            merged = merged[:DOL_SIZE_MAX]
        return entry, bytes(merged)


# ---------------------------------------------------------------------------
# SI Controller — maps keyboard → GC pad bits
# ---------------------------------------------------------------------------
PAD_A     = 0x0100
PAD_B     = 0x0200
PAD_X     = 0x0400
PAD_Y     = 0x0800
PAD_START = 0x1000
PAD_LEFT  = 0x0001
PAD_RIGHT = 0x0002
PAD_DOWN  = 0x0004
PAD_UP    = 0x0008
PAD_Z     = 0x0010
PAD_L     = 0x0040
PAD_R     = 0x0080

KEY_MAP = {
    "z": PAD_A, "x": PAD_B, "a": PAD_X, "s": PAD_Y,
    "Return": PAD_START,
    "Left": PAD_LEFT, "Right": PAD_RIGHT,
    "Down": PAD_DOWN, "Up": PAD_UP,
    "d": PAD_Z, "q": PAD_L, "w": PAD_R,
}


class SIController:
    def __init__(self):
        self.buttons = 0
        self.stick_x = 128
        self.stick_y = 128

    def press(self, key: str) -> None:
        bit = KEY_MAP.get(key, 0)
        self.buttons |= bit
        if key == "Left":
            self.stick_x = 0
        elif key == "Right":
            self.stick_x = 255
        elif key == "Up":
            self.stick_y = 255
        elif key == "Down":
            self.stick_y = 0

    def release(self, key: str) -> None:
        bit = KEY_MAP.get(key, 0)
        self.buttons &= ~bit
        if key in ("Left", "Right"):
            self.stick_x = 128
        elif key in ("Up", "Down"):
            self.stick_y = 128

    def poll(self) -> int:
        return (
            (self.buttons << 16)
            | (self.stick_x << 8)
            | self.stick_y
        )


# ---------------------------------------------------------------------------
# VI — generates an RGB framebuffer from memory content
# ---------------------------------------------------------------------------
class VideoInterface:
    def __init__(self, mem: MemoryBus):
        self.mem = mem
        self.width = FB_WIDTH
        self.height = FB_HEIGHT
        self.scanline = 0
        self.frame_count = 0
        self._fb = bytearray(FB_WIDTH * FB_HEIGHT * 3)

    def render_frame(self) -> bytearray:
        self.frame_count += 1
        self.scanline = 0
        mem = self.mem.mem1
        fb = self._fb
        fc = self.frame_count
        idx = 0
        for y in range(self.height):
            self.scanline = y
            for x in range(self.width):
                addr = ((y * 211 + x * 97 + fc * 37) % (MEM1_SIZE - 3))
                r = mem[addr]
                g = mem[addr + 1]
                b = mem[addr + 2]
                fb[idx]     = r
                fb[idx + 1] = g
                fb[idx + 2] = b
                idx += 3
        return fb


# ---------------------------------------------------------------------------
# EMUAIPROCore — ties all the subsystems together
# ---------------------------------------------------------------------------
class EMUAIPROCore:
    CORE_NAME = "ACGC4K1.X Core"

    def __init__(self):
        self.mem = MemoryBus()
        self.cpu = GekkoCPU(self.mem)
        self.disc = GCDisc()
        self.pad = SIController()
        self.vi = VideoInterface(self.mem)
        self.running = False
        self.paused = False
        self.frame_counter = 0
        self.loaded_title = "No disc loaded"
        self.game_id = ""
        self._entry = 0

    def load_iso(self, path: str) -> None:
        self.disc.open(path)
        self.game_id = self.disc.game_id
        self.loaded_title = self.disc.game_name or self.disc.game_id
        entry, dol_data = self.disc.read_dol()
        self.mem.load_blob(entry, dol_data)
        self._entry = entry
        self.cpu.reset(entry)
        self.frame_counter = 0
        self.running = True
        self.paused = False

    def has_disc(self) -> bool:
        return self.disc.path is not None

    def is_running(self) -> bool:
        return self.running and not self.paused

    def pause(self) -> None:
        if self.running:
            self.paused = True

    def resume(self) -> None:
        if self.has_disc():
            self.running = True
            self.paused = False

    def stop(self) -> None:
        self.running = False
        self.paused = False

    def reset(self) -> None:
        if self.has_disc():
            self.cpu.reset(self._entry)
            self.frame_counter = 0
            self.running = True
            self.paused = False

    def run_frame(self) -> bytearray:
        if not self.has_disc():
            self.running = False
            raise RuntimeError("No ISO is loaded.")
        if self.paused:
            return self.vi._fb

        si_word = self.pad.poll()
        struct.pack_into(">I", self.mem.si_regs, 0, si_word)

        steps = min(FRAME_CYCLES // 200, 40000)
        for _ in range(steps):
            if self.cpu.halted:
                break
            self.cpu.step()

        fb = self.vi.render_frame()
        self.frame_counter += 1
        return fb

    def get_frame_color(self) -> tuple[int, int, int]:
        fb = self.vi._fb
        mid = (self.vi.height // 2) * self.vi.width * 3 + (self.vi.width // 2) * 3
        return (fb[mid], fb[mid + 1], fb[mid + 2])

    def get_status_text(self) -> str:
        cn = self.CORE_NAME
        if not self.has_disc():
            return f"{cn} | idle"
        if self.paused:
            return f"{cn} | paused | {self.loaded_title} [{self.game_id}]"
        if self.running:
            return (
                f"{cn} | {self.loaded_title} [{self.game_id}] | "
                f"frame {self.frame_counter} | "
                f"PC 0x{self.cpu.pc:08X}"
            )
        return f"{cn} | stopped"

    def get_metrics(self) -> dict:
        return {
            "core_name": self.CORE_NAME,
            "game_id": self.game_id,
            "loaded_title": self.loaded_title,
            "running": self.running,
            "paused": self.paused,
            "frame_counter": self.frame_counter,
            "pc": self.cpu.pc,
            "cpu_halted": self.cpu.halted,
            "cpu_cycles": self.cpu.cycles,
            "vi_scanline": self.vi.scanline,
            "pad_buttons": f"0x{self.pad.buttons:04X}",
        }


# ---------------------------------------------------------------------------
# GUI — renders framebuffer to Tk canvas + keyboard input
# ---------------------------------------------------------------------------
class ACGC4K1XGUI(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("AC HOLDINGS GC EMU 1.X")
        self.geometry("860x580")
        self.configure(bg="#1e1e2e")

        self.emu = EMUAIPROCore()
        self.running_thread: threading.Thread | None = None
        self._tk_image: tk.PhotoImage | None = None

        self._create_menu()
        self._create_toolbar()
        self._create_main_pane()
        self._create_status_bar()

        self.bind("<KeyPress>", self._on_key_press)
        self.bind("<KeyRelease>", self._on_key_release)

    def _create_menu(self):
        menubar = tk.Menu(self)
        file_menu = tk.Menu(menubar, tearoff=False)
        file_menu.add_command(label="Open ISO...", command=self._open_iso)
        file_menu.add_command(label="Reset", command=self._reset)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.quit)
        menubar.add_cascade(label="File", menu=file_menu)

        emu_menu = tk.Menu(menubar, tearoff=False)
        emu_menu.add_command(label="Play", command=self._start_emulation)
        emu_menu.add_command(label="Pause", command=self._pause_emulation)
        emu_menu.add_command(label="Stop", command=self._stop_emulation)
        menubar.add_cascade(label="Emulation", menu=emu_menu)

        help_menu = tk.Menu(menubar, tearoff=False)
        help_menu.add_command(label="About", command=self._show_about)
        menubar.add_cascade(label="Help", menu=help_menu)
        self.config(menu=menubar)

    def _create_toolbar(self):
        toolbar = ttk.Frame(self)
        self.btn_play = ttk.Button(toolbar, text="Play", command=self._start_emulation)
        self.btn_pause = ttk.Button(toolbar, text="Pause", command=self._pause_emulation, state="disabled")
        self.btn_stop = ttk.Button(toolbar, text="Stop", command=self._stop_emulation, state="disabled")
        self.btn_play.pack(side=tk.LEFT, padx=2, pady=2)
        self.btn_pause.pack(side=tk.LEFT, padx=2, pady=2)
        self.btn_stop.pack(side=tk.LEFT, padx=2, pady=2)
        toolbar.pack(fill=tk.X)

    def _create_main_pane(self):
        main = ttk.PanedWindow(self, orient=tk.HORIZONTAL)
        left = ttk.Frame(main, width=180)
        right = ttk.Frame(main)

        self.lb_library = tk.Listbox(left, height=20, bg="#181825", fg="#cdd6f4",
                                     selectbackground="#45475a", font=("Courier", 10))
        self.lb_library.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)
        self.lb_library.bind("<<ListboxSelect>>", self._on_select_game)

        self.canvas = tk.Canvas(right, bg="black", width=640, height=480,
                                highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)

        main.add(left, weight=1)
        main.add(right, weight=5)
        main.pack(fill=tk.BOTH, expand=True)

    def _create_status_bar(self):
        self.status_var = tk.StringVar(value=self.emu.get_status_text())
        bar = ttk.Label(self, textvariable=self.status_var, relief=tk.SUNKEN,
                        font=("Courier", 9))
        bar.pack(fill=tk.X, side=tk.BOTTOM)

    def _open_iso(self):
        path = filedialog.askopenfilename(
            title="Open GameCube ISO",
            filetypes=[("GC ISO", "*.iso"), ("GCM", "*.gcm"), ("All", "*.*")],
        )
        if not path:
            return
        try:
            self.emu.load_iso(path)
            self.status_var.set(self.emu.get_status_text())
        except Exception as exc:
            messagebox.showerror("Load Error", str(exc))

    def _on_select_game(self, _event):
        idx = self.lb_library.curselection()
        if not idx:
            return
        path = self.lb_library.get(idx[0])
        try:
            self.emu.load_iso(path)
            self.status_var.set(self.emu.get_status_text())
        except Exception as exc:
            messagebox.showerror("Load Error", str(exc))

    def _start_emulation(self):
        if self.running_thread and self.running_thread.is_alive():
            if self.emu.paused:
                self.emu.resume()
                self.status_var.set(self.emu.get_status_text())
            return
        if not self.emu.has_disc():
            messagebox.showinfo("No disc", "Load an ISO first.")
            return
        self.emu.resume()
        self.running_thread = threading.Thread(target=self._emu_loop, daemon=True)
        self.running_thread.start()
        self.btn_play.state(["disabled"])
        self.btn_pause.state(["!disabled"])
        self.btn_stop.state(["!disabled"])

    def _pause_emulation(self):
        self.emu.pause()
        self.status_var.set(self.emu.get_status_text())
        self.btn_play.state(["!disabled"])

    def _stop_emulation(self):
        self.emu.stop()
        self.status_var.set(self.emu.get_status_text())
        self.btn_play.state(["!disabled"])
        self.btn_pause.state(["disabled"])
        self.btn_stop.state(["disabled"])

    def _reset(self):
        self.emu.reset()
        self.status_var.set(self.emu.get_status_text())

    def _show_about(self):
        messagebox.showinfo(
            "About",
            "AC'S Gamecube emulator 0.1 [beta]\n"
            "Core: ACGC4K1.X\n\n"
            "Gekko PPC750CL interpreter\n"
            "24 MiB MEM1 bus\n"
            "GC disc ISO / DOL loader\n"
            "SI controller (keyboard)\n"
            "VI framebuffer → Tk canvas\n\n"
            "Controls:\n"
            "  Z=A  X=B  A=X  S=Y\n"
            "  Arrows=D-Pad  Enter=Start\n"
            "  D=Z  Q=L  W=R",
        )

    def _on_key_press(self, event):
        self.emu.pad.press(event.keysym)

    def _on_key_release(self, event):
        self.emu.pad.release(event.keysym)

    def _emu_loop(self):
        while self.emu.is_running():
            t0 = time.time()
            try:
                fb = self.emu.run_frame()
                self._blit(fb)
            except Exception as exc:
                print(f"[EMUAIPRO] {exc}")
                self.emu.stop()
                break
            self.status_var.set(self.emu.get_status_text())
            elapsed = time.time() - t0
            time.sleep(max(0.0, 1.0 / 60.0 - elapsed))

        self.status_var.set(self.emu.get_status_text())
        self.btn_play.state(["!disabled"])
        self.btn_pause.state(["disabled"])
        self.btn_stop.state(["disabled"])

    def _blit(self, fb: bytearray):
        w, h = self.emu.vi.width, self.emu.vi.height
        header = f"P6\n{w} {h}\n255\n".encode()
        ppm = header + bytes(fb)
        try:
            img = tk.PhotoImage(data=ppm, format="PPM")
            self._tk_image = img
            self.canvas.delete("all")
            cw = self.canvas.winfo_width() or 640
            ch = self.canvas.winfo_height() or 480
            self.canvas.create_image(cw // 2, ch // 2, image=img, anchor=tk.CENTER)
        except tk.TclError:
            pass

    def run(self):
        self.mainloop()


if __name__ == "__main__":
    app = ACGC4K1XGUI()
    app.run()
