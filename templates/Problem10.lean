axiom C : Type
axiom st : C → C → C
axiom op : C → C

infixl:65 " ⋆ " => st
postfix:max "ᵒ" => op

axiom assoc : ∀ a b c, a ⋆ (b ⋆ c) = (a ⋆ b) ⋆ c 
axiom op_prop : ∀ a, a ⋆ aᵒ ⋆ a = a

noncomputable def co (x : C) : C := sorry
postfix:max "ᶜ" => co

theorem prop₁ : ∀ a, a ⋆ aᶜ ⋆ a = a 
  := by sorry
theorem prop₂ : ∀ a, aᶜ ⋆ a ⋆ aᶜ = aᶜ   
  := by sorry

axiom commute : ∀ a b, a ⋆ a = a → b ⋆ b = b → a ⋆ b = b ⋆ a

theorem uniqueness (p1 : a ⋆ z ⋆ a = a) (p2 : z ⋆ a ⋆ z = z) : z = aᶜ :=
  by sorry