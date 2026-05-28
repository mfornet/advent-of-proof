axiom C : Type
axiom st : C → C → C
axiom op : C → C

infixl:65 " ⋆ " => st
postfix:max "ᵒ" => op

axiom assoc : ∀ a b c, a ⋆ (b ⋆ c) = (a ⋆ b) ⋆ c
axiom op_prop : ∀ a, a ⋆ aᵒ ⋆ a = a

noncomputable def co (x : C) : C := xᵒ ⋆ x ⋆ xᵒ
postfix:max "ᶜ" => co

theorem prop₁ : ∀ a, a ⋆ aᶜ ⋆ a = a
  := by simp [co, assoc, op_prop]

theorem prop₂ : ∀ a, aᶜ ⋆ a ⋆ aᶜ = aᶜ
  := by
  intro a
  simp [co, assoc]
  conv =>
    lhs
    arg 1; arg 1; arg 1
    rw [← assoc, ← assoc]
    arg 2
    rw [assoc, op_prop]
  conv =>
    lhs
    arg 1
    rw [← assoc, ← assoc]
    arg 2
    rw [assoc, op_prop]

axiom commute : ∀ a b, a ⋆ a = a → b ⋆ b = b → a ⋆ b = b ⋆ a

-- a ⋆ aᵒ commutes
-- a ⋆ aᶜ commutes
-- aᵒ ⋆ a commutes
-- aᶜ ⋆ a commutes

theorem t (n : Nat) : 0 + n = n + 0 :=
  of_eq_true
    (Eq.trans
      (congrFun' (congrArg Eq (Nat.zero_add n)) n)
      (eq_self n)
    )

def myadd (a : Nat) : Nat -> Nat -> Nat
  | 0, _ => a
  | Nat.succ n, _ => Nat.succ (myadd a n 0)


theorem uniqueness (p1 : a ⋆ z ⋆ a = a) (p2 : z ⋆ a ⋆ z = z) : z = aᶜ := by


  sorry
