
namespace Plfl.Part1.Naturals


/--
Natural numbers
-/
inductive ℕ where
| zero : ℕ
| suc : ℕ → ℕ
deriving Repr
open ℕ (zero suc)


def toNat : ℕ → Nat
| zero => 0
| suc i => toNat i + 1

def fromNat : Nat → ℕ
| Nat.zero => zero
| Nat.succ i => suc $ fromNat i


def seven : ℕ :=
  suc $ suc $ suc $ suc $ suc $ suc $ suc zero
#guard toNat seven = 7


/--
Addition
-/
def add : ℕ → ℕ → ℕ
| zero, j => j
| suc i, j => suc $ add i j
infixl:100 " +' " => add

#guard toNat (fromNat 3 +' fromNat 4) = 7


example : zero.suc +' zero.suc = zero.suc.suc :=
  trans
    (
      Eq.mpr
        (id (congrArg (fun _a => _a = (zero +' zero.suc).suc) (add.eq_2 zero.suc zero)))
        (Eq.refl (zero +' zero.suc).suc)
    )
  (
    Eq.mpr
      (id (congrArg (fun _a => _a.suc = zero.suc.suc) (add.eq_1 zero.suc)))
      (Eq.refl zero.suc.suc)
  )

example : zero.suc.suc.suc +' zero.suc.suc.suc.suc = zero.suc.suc.suc.suc.suc.suc.suc :=
  calc
    zero.suc.suc.suc +' zero.suc.suc.suc.suc = (zero.suc.suc +' zero.suc.suc.suc.suc).suc := add.eq_2 zero.suc.suc zero.suc.suc.suc.suc
    _                                        = (zero.suc +' zero.suc.suc.suc.suc).suc.suc := congrArg suc (add.eq_2 zero.suc zero.suc.suc.suc.suc)
    _                                        = (zero +' zero.suc.suc.suc.suc).suc.suc.suc := congrArg (suc ∘ suc) (add.eq_2 zero zero.suc.suc.suc.suc)
    _                                        = zero.suc.suc.suc.suc.suc.suc.suc           := congrArg suc (add.eq_1 zero.suc.suc.suc.suc.suc.suc)

example : fromNat 3 +' fromNat 4 = fromNat 7 := by
  simp [fromNat]
  rw [add, add]
  rfl

example : fromNat 3 +' fromNat 4 = fromNat 7 := rfl


/--
Multiplication
-/
def mul : ℕ → ℕ → ℕ
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
def pow : ℕ → ℕ → ℕ
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
def monus : ℕ → ℕ → ℕ
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
def binFromNat : Bin → Nat
| bits => 0
| bit0 x => 2 * binFromNat x
| bit1 x => 2 * binFromNat x + 1

#guard binFromNat bits = 0
#guard binFromNat (bits O) = 0
#guard binFromNat (bits I) = 1
#guard binFromNat (bits I O) = 2
#guard binFromNat (bits O I) = 1
#guard binFromNat (bits O I O I) = 5
#guard binFromNat (bits I O I O I) = 21


end Plfl.Part1.Naturals
