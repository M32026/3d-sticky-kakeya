import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

/-!
# Intersection-reverse cyclic sequences

The combinatorial language used by Marcus--Tardos, *Intersection reverse
sequences and geometric applications*. A cyclic sequence is represented by a
nodup list, modulo cyclic rotation.
-/

namespace MarcusTardos

variable {α : Type*} [DecidableEq α]

/-- Index of the first occurrence of a symbol, or zero if it is absent. -/
def posOf (a : α) : List α → ℕ
  | [] => 0
  | x :: xs => if x = a then 0 else 1 + posOf a xs

/--
Two linear sequences induce opposite orders on their common symbols.
The nodup hypotheses needed in applications are kept at the theorem boundary.
-/
def IsIntersectionReverse (A B : List α) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → a ∈ B → b ∈ B →
    (posOf a A < posOf b A ↔ posOf b B < posOf a B)

/-- `B` is obtained from `A` by cutting and cyclically rotating it. -/
def IsRotation (A B : List α) : Prop :=
  ∃ n : ℕ, B = A.drop n ++ A.take n

/--
Two cyclic sequences are intersection reverse if suitable linearizations
induce opposite orders on all common symbols.
-/
def IsCyclicIntersectionReverse (A B : List α) : Prop :=
  ∃ A' B' : List α,
    IsRotation A A' ∧
      IsRotation B B' ∧
        IsIntersectionReverse A' B'

end MarcusTardos
