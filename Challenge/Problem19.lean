-- Trusted Comparator challenge for Advent of Proof 2023, Q19.
-- The fixed definitions from the original template are in Spec.Problem19.
import Spec.Problem19

namespace Problem19

theorem nullable_correct₁ : Nullable R → Matches R [] := by sorry
theorem nullable_correct₂ : Matches R [] → Nullable R := by sorry

theorem step_correct₁ : Matches (step R c) s → Matches R (c :: s) := by sorry
theorem step_correct₂ : Matches R (c :: s) → Matches (step R c) s := by sorry

theorem steps_correct₁ : Matches (steps R s) [] → Matches R s := by sorry
theorem steps_correct₂ : Matches R s → Matches (steps R s) [] := by sorry

lemma check_lemma₁ (n : Nullable (steps R s)) : Matches R s := by sorry
lemma check_lemma₂ (m : Matches R s) : Nullable (steps R s) := by sorry

instance check (R : Regex) (s : List Char) : Decidable (Matches R s) :=
  if p : Nullable (steps R s)
  then isTrue (check_lemma₁ p)
  else isFalse (fun x => p (check_lemma₂ x))

end Problem19
