import Mathlib

namespace Problem16

def Inj (f : Fin n → Fin n) : Prop := ∀ i j, f i = f j → i = j
def Sur (f : Fin n → Fin n) : Prop := ∀ x, ∃ y, f y = x

def g (f : Fin n → Fin n) (x : Fin n) : Nat → Fin n
| 0 => x
| k + 1 => f (g f x k)

lemma nat_fin_repeat (f : Nat → Fin n) : ∃ (a d : Nat), f a = f (d + 1 + a) := by
  induction n
  case zero => exact Fin.elim0 (f 0)
  case succ n ih =>
    if ha : ∃ a, f a = n then
      obtain ⟨a, ha⟩ := ha
      if hd : ∃ d, f (d + 1 + a) = n then
        grind
      else
        push Not at hd
        let f' : Nat → Fin n := fun k =>
          ⟨(f (k + 1 + a)).toNat, by replace hd := hd k; simp; grind⟩
        replace ih := ih f'
        obtain ⟨x, dx, ih⟩ := ih
        simp [f'] at ih
        use x + 1 + a
        use dx
        grind
    else
      let f' : Nat → Fin n := fun k =>
        ⟨(f k).toNat,
          by push Not at ha; replace ha := ha k; simp; grind⟩
      replace ih := ih f'
      obtain ⟨a, d, ih⟩ := ih
      use a; use d
      simp [f'] at ih
      grind

lemma g_inf_cancel {a b d : Nat} (f : Fin n → Fin n) (hi : Inj f) : g f x (a + d) = g f x (b + d) → g f x a = g f x b := by
  intro he
  induction d
  case zero => simpa [he]
  case succ d ih =>
    apply ih
    simp [g] at he
    grind [Inj]

lemma g_cycle (f : Fin n → Fin n) (x : Fin n) (h : Inj f): ∃ k, x = g f x (k + 1) := by
  let ⟨a, d, he⟩ := nat_fin_repeat (g f x)
  have ht := @g_inf_cancel _ x 0 (d + 1) a f h
  simp only [zero_add] at ht
  apply ht at he
  use d
  simp [g] at he
  simp [g]
  assumption

theorem goal (n : Nat) (f : Fin n → Fin n) : Inj f → Sur f := by
  intro h x
  let ⟨k, hk⟩ := g_cycle f x h
  simp [g] at hk
  grind

end Problem16
