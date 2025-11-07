
import Plfl.Part1.Naturals

namespace Plfl.Part1.Induction


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


theorem mul_succ : ∀ (m n : Nat), m * succ n = m * n + m
| zero, n => calc
               zero * succ n = zero            := Nat.zero_mul (succ n)
               _             = zero + zero     := Nat.zero_add zero
               _             = zero * n + zero := congrArg (fun x ↦ x + zero) (Eq.symm $ Nat.zero_mul n)
| succ m, n => calc
                 succ m * succ n = m * succ n + succ n    := Nat.succ_mul m (succ n)
                 _               = m * n + m + succ n     := congrArg (fun x ↦ x + succ n) (mul_succ m n)
                 _               = (m * n) + (m + succ n) := Nat.add_assoc (m * n) m (succ n)
                 _               = m * n + succ (m + n)   := congrArg (fun x ↦ m * n + x) (Nat.add_succ m n)
                 _               = m * n + succ (n + m)   := congrArg (fun x ↦ m * n + succ x) (Nat.add_comm m n)
                 _               = m * n + (n + succ m)   := congrArg (fun x ↦ m * n + x) (Nat.add_succ n m)
                 _               = m * n + n + succ m     := Eq.symm $ Nat.add_assoc (m * n) n (succ m)
                 _               = succ m * n  + succ m   := congrArg (fun x ↦ x + succ m) (Eq.symm $ Nat.succ_mul m n)

theorem mul_comm : ∀ (m n : Nat), m * n = n * m
| zero, n => calc
               zero * n = zero     := Nat.zero_mul n
               _        = n * zero := Nat.mul_zero n
| succ m, n => calc
                 succ m * n = m * n + n  := Nat.succ_mul m n
                 _          = n * m + n  := congrArg (fun x ↦ x + n) (mul_comm m n)
                 _          = n * succ m := mul_succ n m


open Plfl.Part1.Naturals


theorem zero_monus : ∀ (m : ℕ), ℕ.zero ∸' m = ℕ.zero
| ℕ.zero => monus.eq_1 ℕ.zero
| ℕ.suc m => monus.eq_2 m


theorem monus_add_assoc : ∀ (m n p : ℕ), m ∸' n ∸' p = m ∸' (n +' p)
| ℕ.zero, n, p => calc
                    ℕ.zero ∸' n ∸' p = ℕ.zero ∸' p        := congrArg (fun x ↦ x ∸' p) (zero_monus n)
                  _                  = ℕ.zero             := zero_monus p
                  _                  = ℕ.zero ∸' (n +' p) := Eq.symm $ zero_monus (n +' p)
| ℕ.suc m, ℕ.zero, p => calc
                          ℕ.suc m ∸' ℕ.zero ∸' p = ℕ.suc m ∸' p             := congrArg (fun x ↦ x ∸' p) (monus.eq_1 m.suc)
                          _                      = ℕ.suc m ∸' (ℕ.zero +' p) := congrArg (fun x ↦ ℕ.suc m ∸' x) (add.eq_1 p)
| ℕ.suc m, ℕ.suc n, p => calc
                           ℕ.suc m ∸' ℕ.suc n ∸' p = m ∸' n ∸' p               := congrArg (fun x ↦ x ∸' p) (monus.eq_3 m n)
                           _                       = m ∸' (n +' p)             := monus_add_assoc m n p
                           _                       = ℕ.suc m ∸' ℕ.suc (n +' p) := Eq.symm $ monus.eq_3 m (n +' p)
                           _                       = ℕ.suc m ∸' (ℕ.suc n +' p) := congrArg (fun x ↦ ℕ.suc m ∸' x) (Eq.symm $ add.eq_2 p n)


end Plfl.Part1.Induction
