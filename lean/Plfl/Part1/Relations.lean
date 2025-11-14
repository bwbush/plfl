
-- Preorder that is not a partial order.

inductive B where
| T : B
| F : B

#check B

inductive implies (m n : Bool) : Prop where
| timpt : m = n → implies m n
| fimpx : m = F → implies m n

#check implies


-- Partial order that is not a total order.

inductive divides (m n : Nat) : Prop where
| divs : Nat.mod n m = Nat.zero → divides m n


-- Strict inequality is transitive.

/--
Less than.
-/
inductive lt : Nat → Nat → Prop where
| zlt {n : Nat} : lt Nat.zero n
| slts {m n : Nat} : lt m n → lt m.succ n.succ
open lt

/--
Strict inequality is transitive.
-/
theorem lt_trans₁ {m n p : Nat} : lt m n → lt n p → lt m p
| zlt, _ => zlt
| slts mltn, slts nltp => slts (lt_trans₁ mltn nltp)

#print lt_trans₁

theorem lt_trans₂ (m n p : Nat) (hmn : lt m n) (hnp : lt n p) : lt m p :=
  match m, n, p, hmn, hnp with
  | Nat.zero, _, _, _, _ => zlt
  | Nat.succ m', Nat.succ n', Nat.succ p', slts h1, slts h2 => slts (lt_trans₂ m' n' p' h1 h2)

theorem lt_trans₃ {m n p : Nat} : lt m n → lt n p → lt m p := by
  intros hmn hnp
  match hmn with
  | zlt => exact zlt
  | slts hmn' => cases hnp with
                 | slts hnp' => exact slts (lt_trans₃ hmn' hnp')

theorem lt_trans₄ {m n p : Nat} : lt m n → lt n p → lt m p := by
  intros hmn hnp
  induction hmn generalizing p with
  | zlt => exact zlt
  | slts hmn' ih => cases hnp with
                    | slts hnp' => exact slts (ih hnp')

#print lt_trans₄


-- Trichotomy for strict inequality

/--
Greater than.
-/
inductive gt : Nat → Nat → Prop where
| zgt {n : Nat} : gt n Nat.zero
| sgts {m n : Nat} : gt m n → gt m.succ n.succ
open gt

/--
Helper type for trichotomy of strict inequality.
-/
inductive LtTrichotomy : Nat → Nat → Prop where
| tlt {m n : Nat} : lt m n → LtTrichotomy m n
| teq {m n : Nat} : m = n → LtTrichotomy m n
| tgt {m n : Nat} : gt m n → LtTrichotomy m n
open LtTrichotomy

/--
Strict inequality is trichotomous.
-/
theorem lt_trichotomy (m n : Nat) : @LtTrichotomy m n :=
  match m, n with
  | Nat.zero   , Nat.zero    => teq rfl
  | Nat.zero   , _           => tlt zlt
  | _          , Nat.zero    => tgt zgt
  | Nat.succ m', Nat.succ n' => match lt_trichotomy m' n' with
                                | tlt z => tlt (slts z)
                                | teq z => have h : m'.succ = n'.succ := by rw [z]
                                           teq h
                                | tgt z => tgt (sgts z)
