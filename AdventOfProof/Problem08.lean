import Mathlib.Data.Vector.Basic

namespace Problem8

inductive CompressedString : Nat → Type where
| empty : CompressedString 0
| one   : Bool → (n : Nat) → CompressedString (Nat.succ n)
| cons  : (n : Nat) → CompressedString (Nat.succ m) → CompressedString (Nat.succ (Nat.succ (m + n)))

def head_c : CompressedString (Nat.succ n) → Bool
| .one x _ => x
| .cons _ str => !head_c str

def tail_c : CompressedString (Nat.succ n) → CompressedString n
| .one x c => match c with
              | .zero => .empty
              | .succ n => .one x n
| .cons c str => match c with
                 | .zero => str
                 | .succ n => .cons n str

@[simp]
lemma tail_cons_0 (str : CompressedString (n + 1)) : tail_c (.cons 0 str) = str := by rfl

@[simp]
lemma tail_cons (str : CompressedString (n + 1)) : tail_c (.cons (m + 1) str) = .cons m str := by rfl

def cons_c : Bool → CompressedString n → CompressedString (Nat.succ n)
| b, .empty => .one b 0
| b, .one x n => if b = x
               then .one x (Nat.succ n)
               else .cons 0 (.one x n)
| b, .cons n str => if b = head_c (.cons n str)
                  then .cons (Nat.succ n) str
                  else .cons 0 (.cons n str)

@[simp]
lemma cons_c_exists_zero (str : CompressedString (n + 1)) : cons_c (!head_c str) str = CompressedString.cons 0 str := by
  cases str with
  | one b => simp [cons_c, head_c]
  | @cons n n' str => simp [cons_c]

@[simp]
lemma cons_c_exists_succ (str : CompressedString (n + 1)) :
    cons_c (!head_c str) (.cons m str) = .cons (m + 1) str := by
  cases str with
  | one b => simp [cons_c, head_c]
  | @cons n n' str => simp [cons_c, head_c]

@[simp]
lemma head_cons_c (str : CompressedString n) : head_c (cons_c x str) = x := by
  cases x <;> cases str <;> simp only [cons_c] <;> (try split) <;> simp_all [head_c]

@[simp]
lemma tail_cons_c (str : CompressedString n) : tail_c (cons_c x str) = str := by
  cases str with
  | empty => simp [tail_c, cons_c]
  | one y n' =>
    by_cases h : x = y
    · simp [tail_c, cons_c, h]
    · simp [cons_c, h]
  | cons n' str =>
    cases n' with
    | zero =>
      simp [cons_c, head_c]
      split
      · simp [tail_c]
      · simp [tail_cons_0]
    | succ n' =>
      rw [← cons_c_exists_succ str]
      simp [cons_c, head_c]
      grind [tail_cons, tail_cons_0]

def compress : {n : Nat} → List.Vector Bool n → CompressedString n
| .zero , _ => .empty
| .succ _ , v => cons_c (List.Vector.head v) (compress (List.Vector.tail v))

lemma compress_cons (t : List.Vector Bool n): compress (x ::ᵥ t) = cons_c x (compress t) := by
  rfl

def decompress : ∀ {n}, CompressedString n → List.Vector Bool n
| .zero, .empty => .nil
| .succ _, str => (head_c str) ::ᵥ decompress (tail_c str)

@[simp]
lemma decompress_cons (v : CompressedString (n + 1)): decompress v = head_c v ::ᵥ decompress (tail_c v) := by
  rfl

/-- Rebuilding a non-empty string from its head and tail recovers it.
This is the dual of `head_cons_c`/`tail_cons_c`, and the key to `prf₁`. -/
lemma cons_head_tail : ∀ {n} (str : CompressedString (n + 1)),
    cons_c (head_c str) (tail_c str) = str
  | _, .one x n     => by cases n <;> simp [head_c, tail_c, cons_c]
  | _, .cons c rest => by cases c <;> simp [head_c]

theorem prf₁ : ∀ {n} (xs : CompressedString n), compress (decompress xs) = xs := by
  intro n
  induction n with
  | zero => intro xs; cases xs; rfl
  | succ n ih => intro xs; rw [decompress_cons, compress_cons, ih, cons_head_tail]

theorem prf₂ : ∀{n} (xs : List.Vector Bool n), decompress (compress xs) = xs := by
  intro n xs
  induction xs with
  | nil => rfl
  | @cons n' x xs h =>
    rw [compress_cons, decompress_cons, head_cons_c, tail_cons_c, h]

end Problem8
