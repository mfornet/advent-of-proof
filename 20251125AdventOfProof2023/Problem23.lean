import Mathlib
def Assertion (State : Type) : Type := State → Prop

def conjₐ (φ ψ : Assertion State) : Assertion State := fun σ => φ σ ∧ ψ σ
infixl:60 " ∧' " => conjₐ
def negₐ (φ : Assertion State) : Assertion State := fun σ => ¬ φ σ
prefix:90 " ¬' " => negₐ
def implₐ (φ ψ : Assertion State) : Prop := ∀ σ, φ σ → ψ σ
infixr:80 " ⇒ " => implₐ

inductive Program (State : Type) : Type where
| SKIP : Program State
| ITE  : Assertion State → Program State → Program State → Program State
| LOOP : Assertion State → Program State → Program State
| SEQ  : Program State → Program State → Program State
| UPD  : (State → State) → Program State
open Program
notation "IF" a "THEN" b "ELSE" c "FI" => ITE a b c
notation "WHILE" a "DO" b "OD" => LOOP a b
infixl:40 " ∶ " => SEQ

inductive Triple : Assertion State → Program State → Assertion State → Prop where
| skipₕ : Triple φ SKIP φ
| ifₕ : Triple (φ ∧' g) P ψ → Triple (φ ∧' (¬' g)) Q ψ → Triple φ (IF g THEN P ELSE Q FI) ψ
| whileₕ : Triple (φ ∧' g) P φ → Triple φ (WHILE g DO P OD) (φ ∧' (¬' g))
| seqₕ : Triple π Q ψ → Triple φ P π → Triple φ (P ∶ Q) ψ
| updₕ : Triple (φ ∘ f) (Program.UPD f) φ
| conseqₕ : φ ⇒ φ' → ψ' ⇒ ψ → Triple φ' P ψ' → Triple φ P ψ

def Triple.upd_pre (t : Triple φ' (Program.UPD f) ψ) (h : φ ⇒ φ'): Triple φ (Program.UPD f) ψ := Triple.conseqₕ h (fun _ x => x) t

structure ListSum : Type where
  A : List Nat
  s : Nat
  i : Nat

def prog : Program ListSum :=
    UPD (fun σ => { σ with i := 0 })
  ∶ UPD (fun σ => { σ with s := 0 })
  ∶ WHILE (fun σ => σ.i ≠ σ.A.length) DO
      UPD (fun σ => { σ with s := σ.s + σ.A.getD σ.i 0 })
    ∶ UPD (fun σ => { σ with i := σ.i.succ})
    OD

variable (A₀ : List Nat)

@[reducible] def a0 : Assertion ListSum := fun σ => σ.A = A₀
@[reducible] def u1 : ListSum → ListSum := fun σ => { σ with i := 0 }
@[reducible] def a1 : Assertion ListSum := fun σ => σ.i = 0 ∧ σ.A = A₀

lemma h1 : Triple (a0 A₀) (UPD u1) (a1 A₀) := by
  apply Triple.updₕ.upd_pre
  intro σ h₁
  grind

@[reducible] def u2 : ListSum → ListSum := fun σ => { σ with s := 0 }
@[reducible] def a2 : Assertion ListSum := fun σ => (σ.s = 0 ∧ σ.i = 0 ∧ σ.A = A₀)

lemma h2 : Triple (a1 A₀) (UPD u2) (a2 A₀) := by
  apply Triple.updₕ.upd_pre
  intro σ h₁;
  grind

@[reducible] def a3 (d : Nat := 0) : Assertion ListSum := fun σ => σ.s = (σ.A.take (σ.i + d) |>.sum) ∧ σ.A = A₀

lemma loop_body₂ : Triple (a3 A₀ ∧' fun σ => σ.i ≠ σ.A.length) (UPD fun σ => { A := σ.A, s := σ.s + σ.A.getD σ.i 0, i := σ.i }) (a3 A₀ 1) := by
  apply Triple.updₕ.upd_pre
  intro σ; simp [conjₐ, a3]
  intro h₁ h₂ _
  constructor
  · rw [h₁, List.take_add_one]; simp; grind
  · exact h₂

lemma loop : Triple (a3 A₀)
  WHILE fun σ => σ.i ≠ σ.A.length DO
    (UPD fun σ => { A := σ.A, s := σ.s + σ.A.getD σ.i 0, i := σ.i })
    ∶ UPD fun σ => { A := σ.A, s := σ.s, i := σ.i.succ }
  OD
  fun σ => σ.s = A₀.sum :=
    Triple.conseqₕ
      (fun _ x => x)
      (by intro s h; simp [conjₐ, negₐ] at h; replace ⟨⟨h, h₁⟩, h₂⟩ := h; rw [h, h₂, h₁]; grind)
      (Triple.whileₕ (Triple.seqₕ (Triple.updₕ.upd_pre (by intro σ; simp)) (loop_body₂ A₀)))

theorem goal : Triple (fun σ => σ.A = A₀) prog (fun σ => σ.s = A₀.sum)
  := Triple.seqₕ (loop A₀) (Triple.seqₕ (Triple.conseqₕ (fun _ x => x) (by unfold a2 a3; intro s h; grind) (h2 A₀)) (h1 A₀))
