namespace Problem14

axiom A : Type
axiom st : A → A → A
axiom ι : A
infixl:60 " ⋆ " => st

axiom st_assoc : ∀ a b c, a ⋆ (b ⋆ c) = a ⋆ b ⋆ c
axiom st_identity_r : ∀ y, y ⋆ ι = y
axiom st_identity_l : ∀ y, ι ⋆ y = y

noncomputable def st_exp (n : A) : Nat → A
| .zero => ι
| .succ k => n ⋆ (st_exp n k)
infixl:60 " ⋆⋆ " => st_exp

def fromBits : List Bool → Nat
| [] => 0
| (false :: bs) => 2 * fromBits bs
| (true :: bs) => 1 + 2 * fromBits bs

noncomputable def expBySquare (y x : A) : List Bool → A
| [] => y
| (false :: n) => expBySquare y (x ⋆ x) n
| (true :: n)  => expBySquare (y ⋆ x) (x ⋆ x) n

noncomputable def st_exp' (x : A) (n : List Bool) : A := expBySquare ι x n
infixl:60 " ⋆⋆ᵇ " => st_exp'

theorem st_square : a ⋆⋆ 2 = a ⋆ a := by
  simp [st_exp]
  rw [st_assoc]
  simp [st_identity_r]

theorem st_one : a ⋆⋆ 1 = a := by
  simp [st_exp]
  rw [st_identity_r]

theorem st_exp_mul_comm : a ⋆⋆ b ⋆ a = a ⋆ (a ⋆⋆ b) := by
  induction b with
  | zero => simp [st_exp, st_identity_l, st_identity_r]
  | succ b ih =>
    simp [st_exp]
    rw [← st_assoc, ih]

theorem st_exp_add_one : a ⋆⋆ (b + 1) = (a ⋆⋆ b) ⋆ a := by
  induction b with
  | zero => simp [st_exp, st_identity_l, st_identity_r]
  | succ b ih =>
    rw [ih]
    simp [st_exp, st_assoc]
    rw [st_exp_mul_comm, ← st_assoc a (a ⋆⋆ b) a, st_exp_mul_comm]
    repeat rw [st_assoc]

theorem st_exp_add : a ⋆⋆ (b + c) = (a ⋆⋆ b) ⋆ (a ⋆⋆ c) := by
  induction c generalizing b with
  | zero => simp [st_exp, st_identity_r]
  | succ c ih =>
    rw [← Nat.add_assoc]
    have ih₁ := ih (b := b + 1)
    rw [st_exp_add_one, st_exp_add_one, ih, st_assoc]

theorem st_exp_mul : a ⋆⋆ (b * c) = (a ⋆⋆ b) ⋆⋆ c := by
  induction c generalizing a b with
  | zero => simp [st_exp]
  | succ c ih => rw [Nat.mul_succ, st_exp_add, st_exp_add, ih, st_one]

theorem base_expBySquare: expBySquare (ι ⋆ m) (n ⋆ n) k  = m ⋆ expBySquare ι (n ⋆ n) k := by
  induction k generalizing n m with
  | nil =>
    simp [expBySquare];
    rw [st_identity_r, st_identity_l]
  | cons b k ih =>
    cases b with
    | true =>
      simp [expBySquare]
      have ih₁ := ih (m := m ⋆ (n ⋆ n)) (n := n ⋆ n)
      rw [st_assoc] at ih₁
      rw [ih₁]
      have ih₂ := ih (m := n ⋆ n) (n := n ⋆ n)
      rw [ih₂]
      repeat rw [st_assoc]
    | false => exact ih

theorem proof : ∀ n k, n ⋆⋆ᵇ k = n ⋆⋆ (fromBits k) := by
  intro n k
  induction k generalizing n with
  | nil => simp [st_exp', expBySquare, fromBits, st_exp]
  | cons b k ih => cases b with
    | false =>
      simp [st_exp', expBySquare, fromBits]
      specialize ih (n ⋆ n)
      simp [st_exp'] at ih; rw [ih]
      rw [st_exp_mul, st_square]
    | true =>
      simp [st_exp', expBySquare, fromBits]
      rw [base_expBySquare, st_exp_add, st_one]
      suffices expBySquare ι (n ⋆ n) k = n ⋆⋆ 2 * fromBits k by
        rw [this]
      specialize ih (n ⋆ n)
      simp [st_exp'] at ih; rw [ih]
      rw [st_exp_mul, st_square]

end Problem14
