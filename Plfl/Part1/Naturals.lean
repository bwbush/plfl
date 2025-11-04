
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
Binary numbers
-/
inductive Bin where
| nobit : Bin
| bit0 : Bin → Bin
| bit1 : Bin → Bin
deriving Repr
open Bin (nobit bit0 bit1)
postfix:500 " O" => Bin.bit0
postfix:500 " I" => Bin.bit1


def binToNat : Bin → Nat :=
  let rec f : Nat → Bin → Nat
  | n, nobit => n
  | n, bit0 nobit => 2 * n
  | n, bit1 nobit => 2 * n + 1
  | n, bit0 i => 2 * f n i
  | n, bit1 i => 2 * f n i + 1
  f 0

#guard binToNat nobit = 0
#guard binToNat (nobit O) = 0
#guard binToNat (nobit I) = 1
#guard binToNat (nobit I O) = 2
#guard binToNat (nobit O I) = 1
#guard binToNat (nobit O I O I) = 5
#guard binToNat (nobit I O I O I) = 21


/-
def natToBin : Nat → Bin
  | Nat.zero => bit0 nobit
  | Nat.succ i
-/


end Part1.Naturals
