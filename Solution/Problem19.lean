import Spec.Problem19

namespace Problem19

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

theorem nullable_iff : Nullable R ↔ Matches R [] := by
  induction R <;> simp_all [Matches.starₑ]

/-! ### Brzozowski derivatives -/

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

theorem steps_iff : Matches (steps R s) [] ↔ Matches R s := by
  induction s generalizing R <;> simp_all [step_iff]

theorem nullable_correct₁ : Nullable R → Matches R [] := nullable_iff.mp
theorem nullable_correct₂ : Matches R [] → Nullable R := nullable_iff.mpr

theorem step_correct₁ : Matches (step R c) s → Matches R (c :: s) := step_iff.mp
theorem step_correct₂ : Matches R (c :: s) → Matches (step R c) s := step_iff.mpr

theorem steps_correct₁ : Matches (steps R s) [] → Matches R s := steps_iff.mp
theorem steps_correct₂ : Matches R s → Matches (steps R s) [] := steps_iff.mpr

lemma check_lemma₁ (n : Nullable (steps R s)) : Matches R s :=
  steps_correct₁ (nullable_correct₁ n)

lemma check_lemma₂ (m : Matches R s) : Nullable (steps R s) :=
  nullable_correct₂ (steps_correct₂ m)

instance check (R : Regex) (s : List Char) : Decidable (Matches R s) :=
  decidable_of_iff _ (nullable_iff.trans steps_iff)

example : Matches (['a']⋆ ▹ ['b']) ['a', 'a', 'b'] := by decide
example : ¬ Matches (['a']⋆ ▹ ['b']) ['a', 'b', 'b'] := by decide

end Problem19
