import MyLeanRepo.Kakeya.Cinematic.Section5.FineCarrierMeasurableAssignmentInputs

/-!
# Assign a measurable fine-carrier cover without overlap
-/

open MeasureTheory

namespace Kakeya.Cinematic

theorem fine_carrier_measurable_assignment :
    FineCarrierMeasurableAssignmentStatement := by
  intro hdisj N delta t E carrier hdelta hE hcover
  let cover' : Fin N → Set (ℝ × ℝ) := fun i => (carrier i).realCarrier
  have hcover_mble : ∀ i, MeasurableSet (cover' i) := by
    intro i
    exact (carrier i).measurableSet_realCarrier
  have hmain : ∃ (piece : Fin N → Set (ℝ × ℝ)),
      (∀ i, MeasurableSet (piece i)) ∧
      Set.PairwiseDisjoint (Set.univ : Set (Fin N)) piece ∧
      (∀ i, piece i ⊆ E ∩ cover' i) ∧
      E = ⋃ i, piece i ∧
      (∀ μ : Measure (ℝ × ℝ), μ E = ∑ i, μ (piece i)) :=
    hdisj (α := ℝ × ℝ) (N := N) E cover' hE hcover_mble hcover
  rcases hmain with ⟨piece, hpiece_mble, hdisj', hpiece_sub, hE_eq, hmeasure⟩
  have hvolume : ∀ i, volume (piece i) ≤
      ENNReal.ofReal (2 * delta * (carrier i).interval.length) := by
    intro i
    have h1 : piece i ⊆ (carrier i).realCarrier := by
      have h2 : piece i ⊆ E ∩ (carrier i).realCarrier := hpiece_sub i
      have h3 : E ∩ (carrier i).realCarrier ⊆ (carrier i).realCarrier :=
        Set.inter_subset_right
      exact h2.trans h3
    have hvol1 : volume (piece i) ≤ volume ((carrier i).realCarrier) :=
      measure_mono h1
    have hvol2 : volume ((carrier i).realCarrier) =
        ENNReal.ofReal (2 * delta * (carrier i).interval.length) :=
      (carrier i).volume_realCarrier hdelta
    rw [hvol2] at hvol1
    exact hvol1
  exact ⟨piece, hpiece_mble, hdisj', hpiece_sub, hE_eq, hmeasure, hvolume⟩

end Kakeya.Cinematic
