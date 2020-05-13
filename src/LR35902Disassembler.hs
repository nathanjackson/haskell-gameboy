module LR35092Disassembler where

import qualified Data.Bits as Bit
import qualified Data.Word as Word
import qualified Data.ByteString as ByteString

data Register = A | F | AF | B | C | BC | D | E | DE | H | L | HL | SP | PC
    deriving (Show)

data DerefMod = None | Increment | Decrement deriving (Show)

data Operand = Imm8 Word.Word8 | Imm16 Word.Word16 | Reg Register | Deref Register DerefMod
    deriving (Show)

data Instruction = Instruction {
    operands :: [Operand],
    code :: ByteString.ByteString
} deriving (Show)

disasLdImm16 buf = Instruction [dest, imm16] code
    where hi = ByteString.head buf `Bit.shiftR` 4
          code = ByteString.take 3 buf
          imm16 = Imm16 $ ((fromIntegral (ByteString.index buf 2)) `Bit.shiftL` 8) Bit..|. (fromIntegral (ByteString.index buf 1))
          dest = case hi of
              0 -> Reg BC
              1 -> Reg DE
              2 -> Reg HL
              3 -> Reg SP

disasIncDec16 hi lo = insn [reg]
    where 
          insn op code = Instruction op code
          reg = case hi of
              0 -> Reg BC
              1 -> Reg DE
              2 -> Reg HL
              3 -> Reg SP

disasLd hi lo buf = insn [destOperand, srcOperand]
    where
        insn op code = Instruction op code
        destOperand
            | 0x0 == hi && 0x2 == lo = Deref BC None
            | 0x1 == hi && 0x2 == lo = Deref DE None
            | 0x2 == hi && 0x2 == lo = Deref HL Increment
            | 0x3 == hi && 0x2 == lo = Deref HL Decrement
            | 0x0 == hi && 0x6 == lo = Reg B
            | 0x1 == hi && 0x6 == lo = Reg D
            | 0x2 == hi && 0x6 == lo = Reg H
            | 0x3 == hi && 0x6 == lo = Deref HL None
            | 0x3 >= hi && 0xA == lo = Reg A
            | 0x0 == hi && 0xE == lo = Reg C
            | 0x1 == hi && 0xE == lo = Reg E
            | 0x2 == hi && 0xE == lo = Reg L
            | 0x3 == hi && 0xE == lo = Reg A
            | (0x4 == hi) && (0x0 <= lo) && (lo <= 0x7) = Reg B
            | (0x4 == hi) && (0x8 <= lo) && (lo <= 0xF) = Reg C
            | (0x5 == hi) && (0x0 <= lo) && (lo <= 0x7) = Reg D
            | (0x5 == hi) && (0x8 <= lo) && (lo <= 0xF) = Reg E
            | (0x6 == hi) && (0x0 <= lo) && (lo <= 0x7) = Reg H
            | (0x6 == hi) && (0x8 <= lo) && (lo <= 0xF) = Reg L
            | (0x7 == hi) && (0x0 <= lo) && (lo <= 0x7) = Deref HL None
            | (0x7 == hi) && (0x8 <= lo) && (lo <= 0xF) = Reg A
            | otherwise = error "unknown destination operand"
        srcOperand
            | (0x4 > hi) && 0x2 == lo = Reg A
            | 0x4 > hi && 0x6 == lo = Imm8 (ByteString.head (ByteString.tail buf))
            | 0x0 == hi && 0xA == lo = Deref BC None
            | 0x1 == hi && 0xA == lo = Deref DE None
            | 0x2 == hi && 0xA == lo = Deref HL Increment
            | 0x3 == hi && 0xA == lo = Deref HL Decrement
            | 0x4 > hi && 0xE == lo = Imm8 (ByteString.head (ByteString.tail buf))
            | 0x0 == lo || 0x8 == lo = Reg B
            | 0x1 == lo || 0x9 == lo = Reg C
            | 0x2 == lo || 0xA == lo = Reg D
            | 0x3 == lo || 0xB == lo = Reg E
            | 0x4 == lo || 0xC == lo = Reg H
            | 0x5 == lo || 0xD == lo = Reg L
            | 0x6 == lo || 0xE == lo = Deref HL None
            | 0x7 == lo || 0xF == lo = Reg A
            | otherwise = error "unknown source operand"

-- disas ldReg hi lo = insn [reg]

disas1 buf
    | 0x00 == opcode = Instruction [] $ ByteString.take 1 buf
    | (4 > hi) && (1 == lo) = disasLdImm16 buf
    | (4 > hi) && (3 == lo || 8 == lo) = disasIncDec16 hi lo $ ByteString.singleton opcode
    | (0x76 /= opcode) && ((8 > hi && 3 < hi) || (hi <= 0x3 && (0x2 == lo || 0x6 == lo || 0xA == lo || 0xE == lo))) = disasLd hi lo buf $ ByteString.singleton opcode
    | otherwise = error "Unrecognized Instruction"
    where opcode = ByteString.head buf
          lo = 0xF Bit..&. opcode
          hi = opcode `Bit.shiftR` 4