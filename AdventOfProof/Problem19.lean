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

lemma starₛ_nempty (h : Matches (R⋆) (c :: s)) :
  ∃ a b, Matches R (c :: a) ∧ Matches (R⋆) b ∧ (c :: s = c :: a ++ b) := by
  generalize hx : c :: s = xs at h
  generalize hR : R⋆ = R' at h
  induction h generalizing s R with
  | empty => contradiction
  | char => contradiction
  | comp => contradiction
  | un₁ => contradiction
  | un₂ => contradiction
  | starₑ => contradiction
  | @starₛ R'' u v hu hv hiu hiv =>
    cases u with
    | nil => grind
    | cons => grind

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

theorem nullable_correct₁ : Nullable R → Matches R [] := by
  intro null
  induction R with
  | fail => simp at null
  | ε => exact Matches.empty
  | char a => simp at null
  | comp a b ah bh =>
    obtain ⟨na, nb⟩ := null
    exact Matches.comp (ah na) (bh nb)
  | union a b ah bh =>
    cases null with
    | inl null => exact Matches.un₁ (ah null)
    | inr null => exact Matches.un₂ (bh null)
  | star => exact Matches.starₑ

theorem nullable_correct₂ : Matches R [] → Nullable R := by
  intro m
  induction R with
  | fail => cases m
  | ε => simp
  | char c => cases m
  | comp a b ah bh =>
    generalize hs : ([] : List Char) = xs at m
    symm at hs
    cases m with
    | @comp _ sa _ sb ma mb =>
      rw [List.append_eq_nil_iff] at hs
      rw [hs.1] at ma
      rw [hs.2] at mb
      exact ⟨ah ma, bh mb⟩
  | union a b ah bh =>
    simp
    cases m with
    | un₁ h => grind
    | un₂ h => grind
  | star a ah =>
    trivial

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

theorem step_correct₁ : Matches (step R c) s → Matches R (c :: s) := by
  intro h
  cases R with
  | fail => cases h
  | ε => cases h
  | char c₁ =>
    simp at h
    by_cases h₁ : c = c₁
    · simp [h₁] at *
      cases h with
      | empty => exact Matches.char
    · simp [h₁] at *
      cases h
  | comp x y =>
    simp at h
    by_cases h₁ : Nullable x
    · simp [h₁] at h
      cases h with
      | un₁ h =>
        cases h with
        | @comp _ s _ t hs ht =>
          have tmp : c :: (s ++ t) = (c :: s) ++ t := by grind
          rw [tmp]
          exact Matches.comp (step_correct₁ hs) ht
      | un₂ h =>
        have tmp : c :: s = [] ++ (c :: s) := by simp
        rw [tmp]
        exact Matches.comp (nullable_correct₁ h₁) (step_correct₁ h)
    · simp [h₁] at *
      cases h with
      | @comp _ s _ t hs ht =>
        have tmp : c :: (s ++ t) = (c :: s) ++ t := by grind
        rw [tmp]
        exact Matches.comp (step_correct₁ hs) ht
  | union x y =>
    cases h with
    | un₁ h => exact Matches.un₁ (step_correct₁ h)
    | un₂ h => exact Matches.un₂ (step_correct₁ h)
  | star x =>
    cases h with
    | @comp _ s _ t hs ht =>
      have tmp : c :: (s ++ t) = (c :: s) ++ t := by grind
      rw [tmp]
      exact Matches.starₛ (step_correct₁ hs) ht

theorem step_correct₂ : Matches R (c :: s) → Matches (step R c) s := by
  intro h
  cases R with
  | fail => cases h
  | ε => cases h
  | char c₁ =>
    by_cases h₁ : c = c₁
    · simp [h₁] at *
      cases h
      exact Matches.empty
    · cases h
      contradiction
  | comp hs ht =>
    generalize hi : c :: s = xs at h
    cases h with
    | @comp _ s' _ t' hs' ht' =>
      cases s' with
      | nil =>
        simp at hi
        have tmp := nullable_correct₂ hs'
        simp [tmp]
        apply Matches.un₂
        rw [← hi] at ht'
        exact step_correct₂ ht'
      | cons c' s' =>
        have tmp : c' :: s' ++ t' = c' :: (s' ++ t') := by grind
        rw [tmp] at hi; clear tmp
        have cc' : c' = c := by grind
        rw [cc'] at hi hs'; clear cc'
        simp
        suffices Matches (step hs c ▹ ht) s by
          by_cases h1 : Nullable hs
          · simp [h1]
            exact Matches.un₁ this
          · simp [h1]
            exact this
        have hsst : s = s' ++ t' := by grind
        rw [hsst]; clear hsst
        apply Matches.comp
        · exact step_correct₂ hs'
        · exact ht'
  | union P Q =>
    cases h with
    | un₁ h => exact Matches.un₁ (step_correct₂ h)
    | un₂ h => exact Matches.un₂ (step_correct₂ h)
  | star R =>
    obtain ⟨s', t', hs', ht', _⟩ := starₛ_nempty h
    have hsst : s = s' ++ t' := by grind
    rw [hsst]; clear hsst
    exact Matches.comp (step_correct₂ hs') ht'

theorem steps_correct₁ : Matches (steps R s) [] → Matches R s := by
  induction s generalizing R with
  | nil => simp
  | cons head t ht => exact fun h => step_correct₁ (ht h)

theorem steps_correct₂ : Matches R s → Matches (steps R s) [] := by
  induction s generalizing R with
  | nil => simp
  | cons head t ht => exact fun h => ht (step_correct₂ h)

lemma check_lemma₁ (n : Nullable (steps R s)) : Matches R s := by
  exact steps_correct₁ (nullable_correct₁ n)

lemma check_lemma₂ (m : Matches R s) : Nullable (steps R s) := by
  exact nullable_correct₂ (steps_correct₂ m)

instance check (R : Regex) (s : List Char) : Decidable (Matches R s) :=
  if p : Nullable (steps R s)
  then isTrue (check_lemma₁ p)
  else isFalse (fun x => p (check_lemma₂ x))

end Problem19
