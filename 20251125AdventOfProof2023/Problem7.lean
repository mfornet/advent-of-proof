import Mathlib.Tactic

namespace Problem7

axiom T : Type
axiom f : T → T

-- marked noncomputable as f may be noncomputable
@[simp]
noncomputable def tortoise (p : T × T) : T × T := (f p.1, p.2)
@[simp]
noncomputable def hare (p : T × T) : T × T := (p.1, f p.2)

inductive Run : T × T → Nat → Prop where
| empty : Run (c, c) 0
| step  : Run (tortoise p) n → Run p (Nat.succ n)

@[simp]
def Loop (n : Nat) : Prop := ∃ c : T, Run (c, c) n

noncomputable def race (p : T × T) : T × T := hare (hare (tortoise p))

def race_spec (p : T × T) : race p = (f p.1, f (f p.2)) := by rfl

lemma nat_repeat_f : Nat.repeat g n (g x) = Nat.repeat g (Nat.succ n) x := by
  induction' n
  case zero => simp [Nat.repeat]
  case succ n ih =>
    simp [Nat.repeat]
    rw [ih]
    simp [Nat.repeat]

lemma race_repeat_spec {p : T × T} {n : Nat} : Nat.repeat race n p = (Nat.repeat f n p.1, Nat.repeat f n <| Nat.repeat f n p.2) := by
  induction' n
  case zero => simp [Nat.repeat]
  case succ n ih =>
    simp [Nat.repeat]
    rw [ih]
    simp [race]
    rw [nat_repeat_f]
    simp [Nat.repeat]

lemma race_repeat_spec_inst {x : T} {n : Nat} : Nat.repeat race n (x, x) = (Nat.repeat f n x, Nat.repeat f n <| Nat.repeat f n x) := by exact race_repeat_spec

lemma run_repeat_tort : Run (Nat.repeat tortoise n p) m → Run p (m + n) := by
  induction' n generalizing p m
  case zero => simp [Nat.repeat]
  case succ n ih =>
    rw [Nat.repeat, ← Nat.add_assoc]
    intro h
    apply Run.step at h
    specialize ih h
    simp at ih
    suffices m + n + 1 = m + 1 + n by rw [this]; exact ih
    simp [Nat.add_assoc, Nat.add_comm]

lemma repeat_tort : (Nat.repeat tortoise n (x, y)) = (Nat.repeat f n x, y) := by
  induction' n
  case zero => simp [Nat.repeat]
  case succ n ih =>
    simp [Nat.repeat]
    rw [ih]
    simp

lemma run_from_repeat : Nat.repeat f n x = x → Run (x, x) n := by
  intro h
  suffices Run (x, x) (0 + n) by simp at this; exact this
  apply @run_repeat_tort n (x, x) 0
  rw [repeat_tort, h]
  exact Run.empty

theorem goal : Nat.repeat race n (x, x) = (c, c) → Loop n := by
  intro h
  use c
  rw [race_repeat_spec_inst, Prod.eq_iff_fst_eq_snd_eq] at h
  simp at h
  have hxc : Nat.repeat f n x = c := by exact h.1
  have hcc : Nat.repeat f n c = c := by rw [hxc] at h; exact h.2
  exact run_from_repeat hcc

end Problem7
