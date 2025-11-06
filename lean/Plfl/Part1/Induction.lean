
namespace Part1.Induction


open Nat (zero succ)


theorem add_swap (m n p : Nat) : m + (n + p) = n + (m + p) :=
  calc
    m + (n + p) = (n + p) + m := Nat.add_comm m (n + p)
    _           = n + (p + m) := Nat.add_assoc n p m
    _           = n + (m + p) := congrArg (fun x ↦ n + x) (Nat.add_comm p m)


theorem mul_add_dist : ∀ (m n p : Nat), (m + n) * p = m * p + n * p
| zero, n, p => calc
                  (zero + n) * p = n * p            := congrArg (fun x ↦ x * p) (Nat.zero_add n)
                  _              = zero + n * p     := Eq.symm $ Nat.zero_add (n * p)
                  _              = zero * p + n * p := congrArg (fun x ↦ x + n * p) (Eq.symm $ Nat.zero_mul p)
| succ m, n, p => calc
                    (succ m + n) * p = succ (m + n) * p      := congrArg (fun x ↦ x * p) (Nat.succ_add m n)
                    _                = (m + n) * p + p       := Nat.succ_mul (m + n) p
                    _                = m * p + n * p + p     := congrArg (fun x ↦ x + p) (mul_add_dist m n p)
                    _                = p + (m * p + n * p)   := Nat.add_comm (m * p + n * p) p
                    _                = p + m * p + n * p     := Eq.symm $ Nat.add_assoc p (m * p) (n * p)
                    _                = m * p + p + n * p     := congrArg (fun x ↦ x + n * p) (Nat.add_comm p (m * p))
                    _                = m.succ * p + n * p    := congrArg (fun x ↦ x + n * p) (Eq.symm $ Nat.succ_mul m p)

theorem mul_add_dist' : ∀ (m n p : Nat), (m + n) * p = m * p + n * p
| zero, n, p => by rw [Nat.zero_add, Nat.zero_mul, Nat.zero_add]
| succ m, n, p => by
    rw [Nat.succ_add, Nat.succ_mul, mul_add_dist', Nat.add_comm, ←Nat.add_assoc]
    conv =>
      lhs
      conv =>
        lhs
        rw [Nat.add_comm, ←Nat.succ_mul]

theorem mul_add_dist'' : ∀ (m n p : Nat), (m + n) * p = m * p + n * p
| zero, n, p => by rw [Nat.zero_add, Nat.zero_mul, Nat.zero_add]
| succ m, n, p => by
    rw [Nat.succ_add, Nat.succ_mul, mul_add_dist'', Nat.add_comm, ←Nat.add_assoc]
    rw [Nat.add_comm p (m * p)]
    rw [←Nat.succ_mul]


theorem mul_assoc : ∀ (m n p : Nat), (m * n) * p = m * (n * p)
| zero, n, p => by
    rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_mul]
| succ m, n, p => by
    rw [Nat.succ_mul, mul_add_dist, mul_assoc, Nat.succ_mul]


end Part1.Induction
