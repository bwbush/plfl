
namespace Part1.Naturals


/--
Natural numbers
-/
inductive ℤ  where
| zero : ℤ
| suc : ℤ → ℤ
deriving Repr
open ℤ (zero suc)


def toNat : ℤ → Nat
| zero => 0
| suc i => toNat i + 1

def fromNat : Nat → ℤ
| Nat.zero => zero
| Nat.succ i => suc $ fromNat i


def seven : ℤ :=
  suc $ suc $ suc $ suc $ suc $ suc $ suc zero
#guard toNat seven = 7


/--
Addition
-/
def add : ℤ → ℤ → ℤ
| zero, j => j
| suc i, j => suc $ add i j
infixl:100 " +' " => add

#guard toNat (fromNat 3 +' fromNat 4) = 7


example : fromNat 3 +' fromNat 4 = fromNat 7 := by
  simp [fromNat]
  rw [add, add]
  rfl

example : fromNat 3 +' fromNat 4 = fromNat 7 := rfl


/--
Multiplication
-/
def mul : ℤ → ℤ → ℤ
| zero, _ => zero
| suc i, j => add j (mul i j)
infixl:200 " *' " => mul

#guard toNat (fromNat 2 *' fromNat 3) = 6


example : fromNat 2 *' fromNat 3 = fromNat 6 := by
  simp [fromNat]
  rw [mul, mul, mul, add, add, add, add, add, add, add, add]

example : fromNat 2 *' fromNat 3 = fromNat 6 := rfl


/--
Powers
-/
def pow : ℤ → ℤ → ℤ
  | _, zero => suc zero
  | i, suc j => mul i (pow i j)
infixl:300 " ^' " => pow

#guard toNat (fromNat 2 ^' fromNat 3) = 8


example : fromNat 3 ^' fromNat 4 = fromNat 81 := by
  simp [fromNat]
  simp [pow, mul, add]

example : fromNat 3 ^' fromNat 4 = fromNat 81 := rfl


/--
Monus
-/
def monus : ℤ → ℤ → ℤ
| i, zero => i
| zero, suc _ => zero
| suc i, suc j => monus i j
infixl:100 " ∸' " => monus

#guard toNat (fromNat 3 ∸' fromNat 1) = 2
#guard toNat (fromNat 3 ∸' fromNat 4) = 0


example : fromNat 5 ∸' fromNat 3 = fromNat 2 := by
  simp [fromNat]
  rw [monus, monus, monus, monus]

example : fromNat 5 ∸' fromNat 3 = fromNat 2 := rfl

example : fromNat 3 ∸' fromNat 3 = fromNat 0 := by
  simp [fromNat]
  rw [monus, monus, monus, monus]

example : fromNat 3 ∸' fromNat 5 = fromNat 0 := rfl


/--
Bit strings
-/
inductive Bin where
| bits : Bin
| bit0 : Bin → Bin
| bit1 : Bin → Bin
deriving Repr, DecidableEq
open Bin (bits bit0 bit1)
postfix:500 " O" => bit0
postfix:500 " I" => bit1


/--
Increment a bit string.
-/
def inc : Bin → Bin
| bits => bit1 bits
| bit0 x => bit1 x
| bit1 x => bit0 (inc x)

#guard inc (bits O) = bits I
#guard inc (bits I) = bits I O
#guard inc (bits O O) = bits O I
#guard inc (bits O I) = bits I O
#guard inc (bits I O) = bits I I
#guard inc (bits I O I I) = bits I I O O


/--
Interpret a natural number as a bit string.
-/
def natToBin : Nat → Bin
  | Nat.zero => bit0 bits
  | Nat.succ x => inc (natToBin x)

#guard bits O = natToBin 0
#guard bits I = natToBin 1
#guard bits I O = natToBin 2
#guard bits I O I = natToBin 5
#guard bits I O I O I = natToBin 21


/--
Interpret a bit string as a natural number.
-/
def binToNat : Bin → Nat
| bits => 0
| bit0 x => 2 * binToNat x
| bit1 x => 2 * binToNat x + 1

#guard binToNat bits = 0
#guard binToNat (bits O) = 0
#guard binToNat (bits I) = 1
#guard binToNat (bits I O) = 2
#guard binToNat (bits O I) = 1
#guard binToNat (bits O I O I) = 5
#guard binToNat (bits I O I O I) = 21


end Part1.Naturals
