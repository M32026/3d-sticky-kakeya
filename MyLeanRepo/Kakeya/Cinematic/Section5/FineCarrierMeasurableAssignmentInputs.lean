import MyLeanRepo.Kakeya.Cinematic.Section5.MeasurableDisjointificationInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.ShadingVolume

/-!
# Measurable assignment to enlarged fine carriers

The fine-shading assembly exposes a finite measurable real-carrier cover of
`E₂`.  This leaf assigns every point to one covering carrier without overlap,
preserves the exact total mass for every measure, and records the uniform
Lebesgue-volume bound inherited from the corresponding carrier.
-/

open MeasureTheory

namespace Kakeya.Cinematic

def FineCarrierMeasurableAssignmentStatement : Prop :=
  FiniteMeasurableDisjointificationStatement.{0} →
    ∀ {N : ℕ} {delta t : ℝ}
      (E : Set (ℝ × ℝ))
      (carrier : Fin N → CurvilinearRectangle delta t),
      0 ≤ delta →
      MeasurableSet E →
      E ⊆ ⋃ i, (carrier i).realCarrier →
      ∃ piece : Fin N → Set (ℝ × ℝ),
        (∀ i, MeasurableSet (piece i)) ∧
        Set.PairwiseDisjoint (Set.univ : Set (Fin N)) piece ∧
        (∀ i, piece i ⊆ E ∩ (carrier i).realCarrier) ∧
        E = ⋃ i, piece i ∧
        (∀ μ : Measure (ℝ × ℝ),
          μ E = ∑ i, μ (piece i)) ∧
        ∀ i,
          volume (piece i) ≤
            ENNReal.ofReal
              (2 * delta * (carrier i).interval.length)

end Kakeya.Cinematic
