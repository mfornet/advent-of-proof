namespace Problem11

inductive Term : Type where
| Ref : Term
| Sop : Term
| Kop : Term
| App : Term → Term → Term

inductive reduces : Term → Term → Prop where
| red_S : ∀ {M N P}, reduces (.App (.App (.App .Sop M) N) P) (.App (.App M P) (.App N P))
| red_K : ∀ {M N}, reduces (.App (.App .Kop M) N) M
| red_left : ∀ {M1 M2 N}, reduces M1 M2 → reduces (.App M1 N) (.App M2 N)
| red_right : ∀ {M N1 N2}, reduces N1 N2 → reduces (.App M N1) (.App M N2)
| red_trans : ∀ {M N P}, reduces M N → reduces N P → reduces M P
-- Added this variant to make it easier.
| red_rfl : ∀ {M}, reduces M M

infixl:60 " ↦ " => reduces

def ident : Term :=
  .App (.App .Sop .Kop) .Kop

@[simp]
theorem red_S (h : (.App (.App M P) (.App N P)) ↦ R) :
  (.App (.App (.App .Sop M) N) P) ↦ R := .red_trans .red_S h

@[simp]
theorem red_K (h : M ↦ R) :
  (.App (.App .Kop M) N) ↦ R := .red_trans .red_K h

theorem red_left (h_le : M1 ↦ M2) (h_ri : N1 ↦ N2) :
  (.App M1 N1) ↦ (.App M2 N2) := reduces.red_trans (.red_right h_ri) (.red_left h_le)

theorem ident_red : .App ident M ↦ M := by
  exact red_S (red_K .red_rfl)

def const_sop : Term := .App .Kop .Sop
theorem const_sop_red : .App const_sop M ↦ .Sop := red_K .red_rfl

def const_kop : Term := .App .Kop .Kop
theorem const_kop_red : .App const_kop M ↦ .Kop := red_K .red_rfl

def app_app (M₁ : Term) (M₂ : Term) : Term := .App (.App .Sop M₁) M₂
theorem app_app_red : .App (app_app M₁ M₂) M₃ ↦ .App (.App M₁ M₃) (.App M₂ M₃) := red_S .red_rfl

def substitution : Term → Term → Term
| .Ref, N => N
| .Sop, _ => .Sop
| .Kop, _ => .Kop
| .App M₁ M₂, N => .App (substitution M₁ N) (substitution M₂ N)

def lambda : Term → Term
| .Ref => ident
| .Sop => const_sop
| .Kop => const_kop
| .App M₁ M₂ => app_app (lambda M₁) (lambda M₂)

theorem beta : .App (lambda M) N ↦ substitution M N := by
  induction M with
  | Ref => exact red_S (red_K .red_rfl)
  | Sop => exact red_K .red_rfl
  | Kop => exact red_K .red_rfl
  | App M₁ M₂ ih₁ ih₂ => exact red_S (red_left ih₁ ih₂)

end Problem11
