import Mathlib

namespace Problem19

inductive Regex : Type where
| fail    : Regex
| ε       : Regex
| char    : Char → Regex
| comp    : Regex → Regex → Regex
| union   : Regex → Regex → Regex
| star    : Regex → Regex


infixl:62 " ▹ " => Regex.comp
infixl:65 " ⊎ " => Regex.union
postfix:70 "⋆" => Regex.star
notation "∅"=> Regex.fail
notation "[" x "]" => Regex.char x

inductive Matches : Regex → List Char → Prop where
| empty : Matches .ε []
| char  : Matches [c] [c]
| comp  : Matches R s → Matches S t → Matches (R ▹ S) (s ++ t)
| un₁   : Matches R s → Matches (R ⊎ S) s
| un₂   : Matches S s → Matches (R ⊎ S) s
| starₑ : Matches (R⋆) []
| starₛ : Matches R s → Matches (R⋆) t → Matches (R⋆) (s ++ t)

@[simp]
def Nullable : Regex → Prop
| .fail => False
| .ε    => True
| [ _ ] => False
| r ▹ s => Nullable r ∧ Nullable s
| r ⊎ s => Nullable r ∨ Nullable s
| _ ⋆   => True

instance nullable : (r : Regex) → Decidable (Nullable r)
| .fail => isFalse (by simp)
| .ε    => isTrue (by simp)
| [ _ ] => isFalse (by simp)
| r ⋆   => isTrue (by simp)
| r ⊎ s => by have x := nullable r; have y := nullable s; apply instDecidableOr;
| r ▹ s => by have x := nullable r; have y := nullable s; apply instDecidableAnd;

theorem nullable_correct₁ : Nullable R → Matches R []
  := by sorry
theorem nullable_correct₂ : Matches R [] → Nullable R
  := by sorry

@[simp]
def step : Regex → Char → Regex
| .fail , _ => ∅
| .ε    , _ => ∅
| [ d ] , c => if c = d then .ε else ∅
| r ▹ s , c => if Nullable r then (step r c ▹ s) ⊎ (step s c) else step r c ▹ s
| r ⊎ s , c => step r c ⊎ step s c
| r ⋆   , c => step r c ▹ (r ⋆)
@[simp]
def steps (R : Regex) : List Char → Regex
| x :: xs => steps (step R x) xs
| [] => R

theorem step_correct₁ : Matches (step R c) s → Matches R (c :: s)
  := by sorry

theorem step_correct₂ : Matches R (c :: s) → Matches (step R c) s
  := by sorry

theorem steps_correct₁ : Matches (steps R s) [] → Matches R s
  := by sorry

theorem steps_correct₂ : Matches R s → Matches (steps R s) []
  := by sorry

lemma check_lemma₁ (n : Nullable (steps R s)) : Matches R s
  := by sorry
lemma check_lemma₂ (m : Matches R s) : Nullable (steps R s)
  := by sorry

instance check (R : Regex) (s : List Char) : Decidable (Matches R s) :=
  if p : Nullable (steps R s)
  then isTrue (check_lemma₁ p)
  else isFalse (fun x => p (check_lemma₂ x))

end Problem19
