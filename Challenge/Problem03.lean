-- Trusted Comparator challenge for Advent of Proof 2023, Q3.
-- Adapted from templates/Problem03.lean for Lean 4.30.

namespace Problem3

inductive subseq {A : Type} : List A → List A → Prop where 
| subseq_nil : subseq [] []
| subseq_cons : ∀{xs ys}{x}, subseq xs ys → subseq (x :: xs) (x :: ys)
| subseq_skip : ∀{x}{xs ys}, subseq xs ys → subseq xs (x :: ys)
infix:50 " ⊑ " => subseq

theorem subseq_refl : ∀{A : Type} (xs : List A), xs ⊑ xs := by 
sorry

theorem subseq_trans : ∀{A : Type}{xs ys zs : List A}, xs ⊑ ys → ys ⊑ zs → xs ⊑ zs := by
sorry

theorem subseq_len : ∀{A : Type}{xs ys : List A}, xs ⊑ ys → List.length xs ≤ List.length ys := by
sorry

theorem subseq_antisym : ∀{A : Type}{xs ys : List A}, xs ⊑ ys → ys ⊑ xs → xs = ys := by
sorry

end Problem3
