import Mathlib.Tactic

namespace Problem5

inductive Symbol : Type where
| O : Symbol
| C : Symbol

inductive M : List Symbol → Type where
| empty : M []
| juxt  : M a → M b → M (a ++ b)
| nest  : M a → M (Symbol.O :: a ++ [ Symbol.C ])

inductive ListOf (P : List Symbol → Type) : List Symbol → Type where
| empty : ListOf P []
| cons  : P a → ListOf P b → ListOf P (a ++ b)

inductive N : List Symbol → Type where
| nest : ListOf N a → N (Symbol.O :: a ++ [ Symbol.C ])

def L := ListOf N

-- Data-carrying (`Type`-valued) version of `M_unique`.
-- `∃`/`Exists` lives in `Prop` and cannot be eliminated to build data (a `Type`),
-- so to use the witnesses inside `goal` (which produces `L s : Type`) we must
-- return them as actual data via `Σ'`/`×'` rather than hide them in an `Exists`.
def M_split (s : List Symbol) (h : s.length ≠ 0) (x : M s) :
    Σ' a b, M a ×' M b ×' (s = [.O] ++ a ++ [.C] ++ b) := by
  cases ht : x with
  | empty => simp at h
  | juxt x₁ y =>
    expose_names
    cases ha : a with
    | nil =>
      rw [ha] at h
      simp only [List.nil_append] at h
      exact M_split b h y
    | cons head tail =>
      have ⟨a, b₁, x, y₁, hi⟩ := M_split a (by grind) x₁
      exact ⟨a, b₁ ++ b, x, y₁.juxt y, by grind⟩
  | nest x =>
    expose_names
    exact ⟨a, [], x_1, M.empty, by grind⟩

def goal  : M s → L s := by
  intro seq
  by_cases h : s.length = 0
  · -- empty word
    have hnil : s = [] := by grind
    rw [hnil]
    exact ListOf.empty
  · -- nonempty: split off the first balanced block `[O] a [C]` and the rest `b`
    have ⟨a, b, ma, mb, heq⟩ := M_split s h seq
    rw [heq]
    exact ListOf.cons (N.nest (goal ma)) (goal mb)
termination_by s.length
decreasing_by
  · subst heq; simp [List.length_append]
  · subst heq; simp [List.length_append]; omega

def goal₂ : {s : List Symbol} → L s → M s
  | _, ListOf.empty => M.empty
  | _, ListOf.cons (N.nest inner) rest => M.juxt (M.nest (goal₂ inner)) (goal₂ rest)
termination_by s _ => s.length
decreasing_by
  all_goals simp_wf
  all_goals omega

end Problem5
