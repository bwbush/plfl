
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
| zlt {n : Nat} : lt Nat.zero n.succ
| slts {m n : Nat} : lt m n → lt m.succ n.succ
open lt

/--
Strict inequality is transitive.
-/
theorem lt_trans₁ {m n p : Nat} : lt m n → lt n p → lt m p
| zlt, slts _ => zlt
| slts mltn, slts nltp => slts (lt_trans₁ mltn nltp)

#print lt_trans₁

theorem lt_trans₂ (m n p : Nat) (hmn : lt m n) (hnp : lt n p) : lt m p :=
  match m, n, p, hmn, hnp with
  | Nat.zero, _, Nat.succ _, _, _ => zlt
  | Nat.succ m', Nat.succ n', Nat.succ p', slts h1, slts h2 => slts (lt_trans₂ m' n' p' h1 h2)

theorem lt_trans₃ {m n p : Nat} : lt m n → lt n p → lt m p := by
  intros hmn hnp
  match hmn with
  | zlt => cases hnp with
           | slts _ => exact zlt
  | slts hmn' => cases hnp with
                 | slts hnp' => exact slts (lt_trans₃ hmn' hnp')

theorem lt_trans₄ {m n p : Nat} : lt m n → lt n p → lt m p := by
  intros hmn hnp
  induction hmn generalizing p with
  | zlt => cases hnp with
           | slts _ => exact zlt
  | slts hmn' ih => cases hnp with
                    | slts hnp' => exact slts (ih hnp')

#print lt_trans₄


-- Trichotomy for strict inequality.

/--
Greater than.
-/
inductive gt : Nat → Nat → Prop where
| zgt {n : Nat} : gt n.succ Nat.zero
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
  | Nat.zero   , Nat.succ _  => tlt zlt
  | Nat.succ _ , Nat.zero    => tgt zgt
  | Nat.succ m', Nat.succ n' => match lt_trichotomy m' n' with
                                | tlt z => tlt (slts z)
                                | teq z => have h : m'.succ = n'.succ := by rw [z]
                                           teq h
                                | tgt z => tgt (sgts z)


-- Monotonocity for strict inequality.

theorem add_monor_lt : ∀ (n p q : Nat), lt p q → lt (n + p) (n + q) := by
  intros n p q hpq
  match n with
  | Nat.zero => rw [Nat.zero_add p, Nat.zero_add q]
                exact hpq
  | Nat.succ n' => have h : lt (n' + p).succ (n' + q).succ := slts (add_monor_lt n' p q hpq)
                   rw [Nat.succ_add n' p, Nat.succ_add n' q]
                   exact h

theorem add_monol_lt : ∀ (m n p : Nat), lt m n → lt (m + p) (n + p) := by
  intros m n p hmn
  rw [Nat.add_comm m p, Nat.add_comm n p]
  exact add_monor_lt p m n hmn

theorem add_mono_lt : ∀ (m n p q : Nat), lt m n → lt p q → lt (m + p) (n + q) := by
  intros m n p q hmn hpq
  exact lt_trans₁ (add_monol_lt m n p hmn) (add_monor_lt n p q hpq)


-- Strict implies non-strict inequality.

/--
Less than or equal to.
-/
inductive le : Nat → Nat → Prop where
| zle {n : Nat} : le Nat.zero n
| sles {m n : Nat} : le m n → le m.succ n.succ
open le

/--
Strict inequality implies non-strict inequality.
-/
theorem le_implies_lt : ∀ (m n : Nat), le m.succ n → lt m n := by
  intros m n hmn
  match m, hmn with
  | Nat.zero, sles _ => exact zlt
  | Nat.succ m', sles h => exact slts (le_implies_lt _ _ h)

/--
Non-strict inequality implies strict inequality.
-/
theorem lt_implies_le : ∀ (m n : Nat), lt m n → le m.succ n := by
  intros m n hmn
  match m, hmn with
  | Nat.zero, zlt => exact sles zle
  | Nat.succ m', slts h => exact sles (lt_implies_le _ _ h)


-- Proof of transitivity of non-strict equality.

private theorem le_trans {m n p : Nat} : le m n → le n p → le m p
| zle, _ => zle
| sles mlen, sles nlep => sles (le_trans mlen nlep)

private theorem le_succ (n : Nat) : le n n.succ := by
  induction n with
  | zero => exact zle
  | succ m ih => exact sles ih

/--
Strict equality is transitive.
-/
theorem lt_trans₅ (m n p : Nat) : lt m n → lt n p → lt m p := by
  intros hmn hnp
  apply le_implies_lt
  have lenns : le n n.succ := le_succ n
  exact le_trans (le_trans (lt_implies_le m n hmn) lenns) (lt_implies_le n p hnp)

theorem lt_trans₆ (m n p : Nat) (hmn : lt m n) (hnp : lt n p) : lt m p := by
  apply le_implies_lt
  have h1 : le m.succ n := lt_implies_le m n hmn
  have h2 : le n.succ p := lt_implies_le n p hnp
  have h_bridge : le n n.succ := le_succ n
  have h3 : le m.succ n.succ := le_trans h1 h_bridge
  have h4 : le m.succ p := le_trans h3 h2
  exact h4
