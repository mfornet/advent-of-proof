import Mathlib.Tactic

namespace Problem3

inductive subseq {A : Type} : List A → List A → Prop where
| subseq_nil : subseq [] []
| subseq_cons : ∀{xs ys}{x}, subseq xs ys → subseq (x :: xs) (x :: ys)
| subseq_skip : ∀{x}{xs ys}, subseq xs ys → subseq xs (x :: ys)
infix:50 " ⊑ " => subseq

theorem subseq_refl : ∀{A : Type} (xs : List A), xs ⊑ xs := by
  intro A xs
  induction' xs
  case nil => exact subseq.subseq_nil
  case cons x xs ih => exact subseq.subseq_cons ih

lemma subseq_cons_spec {A : Type} {xs ys : List A} {x}:  xs ⊑ ys → x::xs ⊑ x::ys := by
  exact subseq.subseq_cons

lemma subseq_skip_rev {A : Type} {xs ys : List A} {x}:  x::xs ⊑ ys → xs ⊑ ys := by
  intro h
  cases h
  case subseq_cons ys h => exact subseq.subseq_skip h
  case subseq_skip x' ys h =>
    suffices xs ⊑ ys by exact subseq.subseq_skip this
    exact subseq_skip_rev h

lemma empty_subseq {A : Type} {xs : List A}: [] ⊑ xs := by
  induction' xs
  case nil => exact subseq.subseq_nil
  case cons x xs ih => exact subseq.subseq_skip ih

lemma subseq_cons_rev {A : Type} {xs ys : List A} {x}:  x::xs ⊑ x::ys → xs ⊑ ys := by
  intro h
  cases h
  case subseq_cons h => exact h
  case subseq_skip h => exact subseq_skip_rev h

lemma subseq_empty : ∀{A : Type}{xs : List A}, [] ⊑ xs := by
  intro A xs
  induction' xs
  case nil => exact subseq.subseq_nil
  case cons x xs ih => exact subseq.subseq_skip ih

lemma subseq_remove_second {A : Type} {xs ys : List A} {x y} : x :: y :: xs ⊑ ys → x :: xs ⊑ ys := by
  intro h
  induction' ys generalizing x xs
  case nil => contradiction
  case cons y' ys ih =>
    cases h
    case subseq_cons h =>
      apply subseq.subseq_cons
      exact subseq_skip_rev h
    case subseq_skip h =>
      specialize ih h
      apply subseq.subseq_skip
      exact ih

lemma not_subseq_of_cons_self {A : Type} {xs : List A} {x} : ¬x::xs ⊑ xs := by
  intro h
  cases h
  case subseq_cons xs h => exact not_subseq_of_cons_self h
  case subseq_skip x' xs h => exact not_subseq_of_cons_self (subseq_remove_second h)

theorem subseq_trans : ∀{A : Type}{xs ys zs : List A}, xs ⊑ ys → ys ⊑ zs → xs ⊑ zs := by
  intro A xs ys zs hxy hyz
  induction' hyz generalizing xs
  case subseq_nil => exact hxy
  case subseq_cons xs' ys' x' h ih =>
    cases hxy
    case subseq_cons xs₂ h' =>
      suffices xs₂ ⊑ ys' by exact subseq.subseq_cons this
      exact ih h'
    case subseq_skip h' =>
      suffices xs ⊑ ys' by exact subseq.subseq_skip this
      exact ih h'
  case subseq_skip x xs' ys' h ih =>
    suffices xs ⊑ ys' by exact subseq.subseq_skip this
    exact ih hxy

theorem subseq_len : ∀{A : Type}{xs ys : List A}, xs ⊑ ys → List.length xs ≤ List.length ys := by
  intro A xs ys h
  induction' h
  case subseq_nil => simp
  case subseq_cons xs' ys' x' h ih => simp [ih]
  case subseq_skip x xs' ys' h ih => exact Nat.le_trans ih (Nat.le_succ_of_le (Nat.le_refl _))

theorem subseq_antisym : ∀{A : Type} {xs ys : List A}, xs ⊑ ys → ys ⊑ xs → xs = ys := by
  intro A xs ys hxy hyx
  induction' xs generalizing ys
  case nil =>
    cases hyx
    case subseq_nil => rfl
  case cons x xs ih =>
    cases hxy
    case subseq_cons ys hxy =>
      suffices xs = ys by rw [this]
      suffices ys ⊑ xs by exact ih hxy this
      exact subseq_cons_rev hyx
    case subseq_skip x' ys h =>
      exfalso
      exact not_subseq_of_cons_self (subseq_trans hyx h)

end Problem3
