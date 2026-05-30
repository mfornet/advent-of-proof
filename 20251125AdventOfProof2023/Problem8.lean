import Mathlib.Data.Vector.Basic

namespace Problem8

inductive CompressedString : Nat → Type where
| empty : CompressedString 0
| one   : Bool → (n : Nat) → CompressedString (Nat.succ n)
| cons  : (n : Nat) → CompressedString (Nat.succ m) → CompressedString (Nat.succ (Nat.succ (m + n)))

def head_c : CompressedString (Nat.succ n) → Bool
| .one x n => x
| .cons _ str => not (head_c str)


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
lemma cons_c_exists_succ (str : CompressedString (n + 1)) : cons_c (!head_c str) (.cons m str) = .cons (m + 1) str := by
  cases str with
  | one b => simp [cons_c, head_c]
  | @cons n n' str => simp [cons_c, head_c]

@[simp]
lemma head_cons_c (str : CompressedString n) : head_c (cons_c x str) = x := by
  simp [cons_c]
  split
  case h_1 n x' str => grind [head_c]
  case h_2 str x' n =>
    split
    case isTrue => grind [head_c];
    case isFalse _ _ h => simp [head_c]; exact Bool.eq_not.mpr fun a => h (id (Eq.symm a))
  case h_3 n _ str₁ n₁ n₂ str₂ =>
    split
    case isTrue _ h =>
      rw [h]
      simp [head_c]
    case isFalse _ h =>
      simp [head_c] at *
      grind

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


@[simp]
def compress : {n : Nat} → List.Vector Bool n → CompressedString n
| .zero , _ => .empty
| .succ _ , v => cons_c (List.Vector.head v) (compress (List.Vector.tail v))

lemma compress_cons (t : List.Vector Bool n): compress (x ::ᵥ t) = cons_c x (compress t) := by
  rfl

@[simp]
def decompress : ∀ {n}, CompressedString n → List.Vector Bool n
| .zero, .empty => .nil
| .succ _, str => (head_c str) ::ᵥ decompress (tail_c str)

@[simp]
lemma decompress_cons (v : CompressedString (n + 1)): decompress v = head_c v ::ᵥ decompress (tail_c v) := by
  rfl

theorem prf₁ : ∀{n} (xs : CompressedString n), compress (decompress xs) = xs  := by
  intro n xs
  induction xs with
  | empty => simp
  | one a n₁ =>
    induction n₁ with
    | zero => simp [head_c, cons_c]
    | succ n₁ h =>
      rw [decompress_cons]
      simp only [head_c]
      rw [compress_cons]
      simp only [tail_c]
      rw [h]
      simp [cons_c]
  | @cons n' m' str ih =>
    induction m' with
    | zero => rw [← cons_c_exists_zero str, decompress_cons, head_cons_c, compress_cons, tail_cons_c str, ih]
    | succ m' ih' => rw [← cons_c_exists_succ str, decompress_cons, head_cons_c, tail_cons_c, compress_cons, ih']

theorem prf₂ : ∀{n} (xs : List.Vector Bool n), decompress (compress xs) = xs := by
  intro n xs
  induction xs with
  | nil => simp
  | @cons n' x xs h =>
    rw [compress_cons, decompress_cons, head_cons_c, tail_cons_c, h]

end Problem8
