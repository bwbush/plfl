
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
Strict inequality.
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
  induction hmn with
  | zlt => exact zlt
  | slts hmn' ih => match p with
                    | Nat.zero => contradiction
                    | Nat.succ p' => sorry
