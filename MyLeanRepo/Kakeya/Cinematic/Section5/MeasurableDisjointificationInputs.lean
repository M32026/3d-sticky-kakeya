import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Finite measurable cover disjointification

A finite measurable cover can be assigned in index order to pairwise-disjoint
measurable pieces without losing any covered mass.
-/

open MeasureTheory

namespace Kakeya.Cinematic

def FiniteMeasurableDisjointificationStatement : Prop :=
  ∀ {α : Type*} [MeasurableSpace α] {N : ℕ}
    (E : Set α) (cover : Fin N → Set α),
    MeasurableSet E →
    (∀ i, MeasurableSet (cover i)) →
    E ⊆ ⋃ i, cover i →
    ∃ piece : Fin N → Set α,
      (∀ i, MeasurableSet (piece i)) ∧
      Set.PairwiseDisjoint (Set.univ : Set (Fin N)) piece ∧
      (∀ i, piece i ⊆ E ∩ cover i) ∧
      E = ⋃ i, piece i ∧
      ∀ μ : Measure α,
        μ E = ∑ i, μ (piece i)

end Kakeya.Cinematic
