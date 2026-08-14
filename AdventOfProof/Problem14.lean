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

noncomputable def st_exp' (x : A)(n : List Bool) : A := expBySquare ι x n
infixl:60 " ⋆⋆ᵇ " => st_exp'

theorem proof : ∀ n k, n ⋆⋆ᵇ k = n ⋆⋆ (fromBits k) :=
by sorry

end Problem14
