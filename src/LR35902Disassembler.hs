module LR35092Disassembler where

import qualified Data.Bits as Bit
import qualified Data.List as List
import qualified Data.Word as Word
import qualified Data.ByteString as ByteString

import qualified Numeric as Numeric

data Register = A | F | AF | B | C | BC | D | E | DE | H | L | HL | SP | PC
    deriving (Show)

data DerefMod = None | Increment | Decrement deriving (Show)

data Operand = Imm8 Word.Word8 | Imm16 Word.Word16 | Reg Register | Deref Operand DerefMod
    deriving (Show)

data Mnemonic = LD deriving (Show)

data Instruction = Instruction {
    mnemonic :: Mnemonic,
    operands :: [Operand],
    code :: ByteString.ByteString
} deriving (Show)

takeWord16 buf = ((fromIntegral (ByteString.index buf 1)) `Bit.shiftL` 8) Bit..|. (fromIntegral (ByteString.index buf 0))

--disasLdImm16 buf = Instruction [dest, imm16] code
--    where hi = ByteString.head buf `Bit.shiftR` 4
--          code = ByteString.take 3 buf
--          imm16 = Imm16 $ ((fromIntegral (ByteString.index buf 2)) `Bit.shiftL` 8) Bit..|. (fromIntegral (ByteString.index buf 1))
--          dest = case hi of
--              0 -> Reg BC
--              1 -> Reg DE
--              2 -> Reg HL
--              3 -> Reg SP
--
--disasIncDec16 hi lo = insn [reg]
--    where 
--          insn op code = Instruction op code
--          reg = case hi of
--              0 -> Reg BC
--              1 -> Reg DE
--              2 -> Reg HL
--              3 -> Reg SP

disasLd hi lo buf = insn [destOperand, srcOperand]
    where
        insn ops code = Instruction LD ops code
        destOperand
            | 0x0 == hi && 0x2 == lo = Deref (Reg BC) None
            | 0x1 == hi && 0x2 == lo = Deref (Reg DE) None
            | 0x2 == hi && 0x2 == lo = Deref (Reg HL) Increment
            | 0x3 == hi && 0x2 == lo = Deref (Reg HL) Decrement
            | 0x0 == hi && 0x1 == lo = Reg BC
            | 0x1 == hi && 0x1 == lo = Reg DE
            | 0x2 == hi && 0x1 == lo = Reg HL
            | 0x3 == hi && 0x1 == lo = Reg SP
            | 0x0 == hi && 0x6 == lo = Reg B
            | 0x1 == hi && 0x6 == lo = Reg D
            | 0x2 == hi && 0x6 == lo = Reg H
            | 0x3 == hi && 0x6 == lo = Deref (Reg HL) None
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
            | (0x7 == hi) && (0x0 <= lo) && (lo <= 0x7) = Deref (Reg HL) None
            | (0x7 == hi) && (0x8 <= lo) && (lo <= 0xF) = Reg A
            | (0x0 == hi) && (0x8 == lo) = Deref (Imm16 (takeWord16 (ByteString.tail buf))) None
            | otherwise = error "unknown destination operand"
        srcOperand
            | (0x4 > hi) && 0x2 == lo = Reg A
            | 0x4 > hi && 0x6 == lo = Imm8 (ByteString.head (ByteString.tail buf))
            | 0x0 == hi && 0xA == lo = Deref (Reg BC) None
            | 0x1 == hi && 0xA == lo = Deref (Reg DE) None
            | 0x2 == hi && 0xA == lo = Deref (Reg HL) Increment
            | 0x3 == hi && 0xA == lo = Deref (Reg HL) Decrement
            | 0x4 > hi && 0x1 == lo = Imm16 (takeWord16 (ByteString.tail buf))
            | 0x4 > hi && 0xE == lo = Imm8 (ByteString.head (ByteString.tail buf))
            | 0x8 == lo && 0x0 == hi = Reg SP
            | 0x0 == lo || 0x8 == lo = Reg B
            | 0x1 == lo || 0x9 == lo = Reg C
            | 0x2 == lo || 0xA == lo = Reg D
            | 0x3 == lo || 0xB == lo = Reg E
            | 0x4 == lo || 0xC == lo = Reg H
            | 0x5 == lo || 0xD == lo = Reg L
            | 0x6 == lo || 0xE == lo = Deref (Reg HL) None
            | 0x7 == lo || 0xF == lo = Reg A
            | otherwise = error "unknown source operand"

operandPretty (Reg reg) = show reg
operandPretty (Imm8 imm) = Numeric.showHex imm "" ++ "h"
operandPretty (Imm16 imm) = Numeric.showHex imm "" ++ "h"
operandPretty (Deref op mod) = "(" ++ operandPretty op ++ modstr mod ++ ")"
    where
        modstr None = ""
        modstr Increment = "+"
        modstr Decrement = "-"

insnToStr insn = (show (mnemonic insn)) ++ " " ++ opstr
    where
        opstr = List.intercalate ", " (map operandPretty (operands insn))

-- disas ldReg hi lo = insn [reg]

disas1 buf
    --- | 0x00 == opcode = Instruction [] $ ByteString.take 1 buf
    -- | (4 > hi) && (3 == lo || 8 == lo) = disasIncDec16 hi lo $ ByteString.singleton opcode
    | (0x76 /= opcode) && ((8 > hi && 3 < hi) || (hi <= 0x3 && (0x1 == lo || 0x2 == lo || 0x6 == lo || 0xA == lo || 0xE == lo)) || (opcode == 0x08)) = disasLd hi lo buf $ ByteString.singleton opcode
    | otherwise = error "Unrecognized Instruction"
    where opcode = ByteString.head buf
          lo = 0xF Bit..&. opcode
          hi = opcode `Bit.shiftR` 4