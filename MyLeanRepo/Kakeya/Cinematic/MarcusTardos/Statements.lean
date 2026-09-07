import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Frozen Marcus--Tardos sequence bounds

These statements isolate the pure combinatorial input used to count
non-overlapping lenses. They contain no PYZ geometry.
-/

namespace MarcusTardos

/--
Marcus--Tardos Theorem 1 for equal-length cyclic sequences.

The hypothesis `0 < m` is explicit: without it the common length `d` is
unconstrained by the empty family.
-/
def EqualLengthSequenceBoundStatement : Prop :=
  ∀ (α : Type) [DecidableEq α],
    ∃ C : ℝ, 0 < C ∧
      ∀ m d n : ℕ, 0 < m →
        ∀ alphabet : Finset α, alphabet.card = n →
          ∀ A : Fin m → List α,
            (∀ i, (A i).Nodup ∧ (A i).length = d) →
            (∀ i, ∀ x ∈ A i, x ∈ alphabet) →
            (∀ i j, i ≠ j →
              IsCyclicIntersectionReverse (A i) (A j)) →
            (d : ℝ) ≤
              C * (Real.sqrt n * Real.log (n + 1) +
                n / Real.sqrt m)

/--
Marcus--Tardos Corollary 6 for varying sequence lengths.
-/
def TotalLengthSequenceBoundStatement : Prop :=
  ∀ (α : Type) [DecidableEq α],
    ∃ C : ℝ, 0 < C ∧
      ∀ m n : ℕ,
        ∀ alphabet : Finset α, alphabet.card = n →
          ∀ A : Fin m → List α,
            (∀ i, (A i).Nodup) →
            (∀ i, ∀ x ∈ A i, x ∈ alphabet) →
            (∀ i j, i ≠ j →
              IsCyclicIntersectionReverse (A i) (A j)) →
            (∑ i, (A i).length : ℕ) ≤
              C * (m * Real.sqrt n * Real.log (n + 1) +
                n * Real.sqrt m)

/--
The dyadic pruning argument deriving Corollary 6 from Theorem 1.
-/
def TotalLengthFromEqualLengthStatement : Prop :=
  EqualLengthSequenceBoundStatement →
    TotalLengthSequenceBoundStatement

end MarcusTardos
