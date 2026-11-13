import Mathlib

namespace Problem19

inductive Regex : Type where
  | fail : Regex
  | ε : Regex
  | char : Char → Regex
  | comp : Regex → Regex → Regex
  | union : Regex → Regex → Regex
  | star : Regex → Regex

infixl:62 " ▹ " => Regex.comp
infixl:65 " ⊎ " => Regex.union
postfix:70 "⋆" => Regex.star
notation "∅"=> Regex.fail
notation "[" x "]" => Regex.char x

inductive Matches : Regex → List Char → Prop where
  | empty : Matches .ε []
  | char : Matches [c] [c]
  | comp : Matches R s → Matches S t → Matches (R ▹ S) (s ++ t)
  | un₁ : Matches R s → Matches (R ⊎ S) s
  | un₂ : Matches S s → Matches (R ⊎ S) s
  | starₑ : Matches (R⋆) []
  | starₛ : Matches R s → Matches (R⋆) t → Matches (R⋆) (s ++ t)

variable {R S : Regex} {c d : Char} {s t : List Char}

/-! ### Inversion

`cases` on `Matches R s` is easy when `s` is a variable and painful when it is a pattern such
as `[]` or `c :: s`. These lemmas pay that cost once, with `s` a variable, and feed the simp set. -/

@[simp] lemma not_fail : ¬ Matches ∅ s := by rintro ⟨⟩

@[simp]
lemma eps_iff : Matches .ε s ↔ s = [] :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .empty⟩

@[simp]
lemma char_iff : Matches [c] s ↔ s = ([c] : List Char) :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .char⟩

@[simp]
lemma union_iff : Matches (R ⊎ S) s ↔ Matches R s ∨ Matches S s :=
  ⟨
    fun h => by
      cases h with
      | un₁ h => exact .inl h
      | un₂ h => exact .inr h,
    fun h => h.elim .un₁ .un₂
  ⟩

@[simp]
lemma comp_iff : Matches (R ▹ S) s ↔ ∃ a b, Matches R a ∧ Matches S b ∧ s = a ++ b :=
  ⟨
    fun h => by
      cases h with
      | comp ha hb => exact ⟨_, _, ha, hb, rfl⟩,
    fun ⟨_, _, ha, hb, h⟩ => h ▸ .comp ha hb
  ⟩

/-- Inversion for `⋆`, with the first chunk forced to be non-empty. Not a `simp` lemma: the
right-hand side mentions `Matches (R⋆) b`, so simp would loop. -/
lemma starₛ_nempty (h : Matches (R⋆) (c :: s))
    : ∃ a b, Matches R (c :: a) ∧ Matches (R⋆) b ∧ (s = a ++ b) := by
  generalize hx : c :: s = xs at h
  generalize hR : R⋆ = R' at h
  induction h generalizing s R with
  | @starₛ R'' u v hu hv hiu hiv =>
      obtain _ | ⟨d, u⟩ := u <;> grind
  | _ => contradiction

/-! ### Nullability -/

@[simp]
def Nullable : Regex → Prop
  | .fail => False
  | .ε => True
  | [_] => False
  | r ▹ s => Nullable r ∧ Nullable s
  | r ⊎ s => Nullable r ∨ Nullable s
  | _ ⋆ => True

instance nullable : (r : Regex) → Decidable (Nullable r)
  | .fail => .isFalse id
  | .ε => .isTrue trivial
  | [_] => .isFalse id
  | _ ⋆ => .isTrue trivial
  | r ▹ s => @instDecidableAnd _ _ (nullable r) (nullable s)
  | r ⊎ s => @instDecidableOr _ _ (nullable r) (nullable s)

theorem nullable_iff : Nullable R ↔ Matches R [] := by
  induction R <;> simp_all [Matches.starₑ]

/-! ### Brzozowski derivatives -/

@[simp]
def step : Regex → Char → Regex
  | .fail, _ => ∅
  | .ε, _ => ∅
  | [d], c => if c = d then .ε else ∅
  | r ▹ s, c => if Nullable r then (step r c ▹ s) ⊎ (step s c) else step r c ▹ s
  | r ⊎ s, c => step r c ⊎ step s c
  | r ⋆, c => step r c ▹ (r ⋆)

theorem step_iff : Matches (step R c) s ↔ Matches R (c :: s) := by
  induction R generalizing s with
  | fail | ε => simp
  | char d => by_cases h : c = d <;> simp_all
  | union x y ihx ihy => simp_all
  | star x ihx =>
      simp only [step, comp_iff, ihx]
      constructor
      · rintro ⟨a, b, ha, hb, rfl⟩
        exact .starₛ ha hb
      · exact starₛ_nempty
  | comp x y ihx ihy =>
      by_cases h : Nullable x <;> simp [h, List.cons_eq_append_iff, ihx, ihy]
      · constructor
        · rintro (⟨a, ha, b, hb, rfl⟩ | hy)
          · exact ⟨c :: a, ha, b, hb, .inr ⟨a, rfl, rfl⟩⟩
          · exact ⟨[], nullable_iff.mp h, c :: s, hy, .inl ⟨rfl, rfl⟩⟩
        · rintro ⟨a, ha, b, hb, ⟨rfl, rfl⟩ | ⟨a', rfl, rfl⟩⟩
          · exact .inr hb
          · exact .inl ⟨a', ha, b, hb, rfl⟩
      · constructor
        · rintro ⟨a, ha, b, hb, rfl⟩
          exact ⟨c :: a, ha, b, hb, .inr ⟨a, rfl, rfl⟩⟩
        · rintro ⟨a, ha, b, hb, ⟨rfl, rfl⟩ | ⟨a', rfl, rfl⟩⟩
          · exact absurd (nullable_iff.mpr ha) h
          · exact ⟨a', ha, b, hb, rfl⟩

@[simp]
def steps (R : Regex) : List Char → Regex
  | x :: xs => steps (step R x) xs
  | [] => R

theorem steps_iff : Matches (steps R s) [] ↔ Matches R s := by
  induction s generalizing R <;> simp_all [step_iff]

instance check (R : Regex) (s : List Char) : Decidable (Matches R s) :=
  decidable_of_iff _ (nullable_iff.trans steps_iff)

example : Matches (['a']⋆ ▹ ['b']) ['a', 'a', 'b'] := by decide
example : ¬ Matches (['a']⋆ ▹ ['b']) ['a', 'b', 'b'] := by decide

end Problem19
