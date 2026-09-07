import MyLeanRepo.Kakeya.CV.GeometricMeasure.GraphPullbackMeasureDensity
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

/-- Weighted graph area formula for a globally C¹ function. -/
theorem graph_area_formula_weighted
    (g : R2 → ℝ) (hg : ContDiff ℝ 1 g)
    {A : Set R2} (hA : MeasurableSet A)
    {f : R3 → ENNReal} (hf : Measurable f) :
    ∫⁻ z in graphMap g '' A, f z ∂μH[2] =
      ∫⁻ y in A, f (graphMap g y) * areaFactor g y ∂volume := by
  let ρ : Measure R2 := graphPullbackMeasure g
  haveI : IsLocallyFiniteMeasure ρ :=
    graphPullbackMeasure_isLocallyFinite g hg
  have h_ac : ρ ≪ volume := graphPullbackMeasure_absolutelyContinuous g hg
  have h_rn :
      ρ.rnDeriv volume =ᵐ[volume] areaFactor g :=
    graphPullbackMeasure_rnDeriv g hg
  have hρ_density : ρ = volume.withDensity (areaFactor g) := by
    calc
      ρ = volume.withDensity (ρ.rnDeriv volume) :=
        (Measure.withDensity_rnDeriv_eq ρ volume h_ac).symm
      _ = volume.withDensity (areaFactor g) :=
        withDensity_congr_ae h_rn
  have h_emb : MeasurableEmbedding (graphMap g) :=
    graphMap_measurableEmbedding hg.continuous
  have h_image_meas : MeasurableSet (graphMap g '' A) :=
    h_emb.measurableSet_image.mpr hA
  have h_image_sub : graphMap g '' A ⊆ Set.range (graphMap g) :=
    Set.image_subset_range _ _
  have h_preimage : graphMap g ⁻¹' (graphMap g '' A) = A :=
    (graphMap_injective g).preimage_image A
  have h_map : Measure.map (graphMap g) ρ =
      μH[2].restrict (Set.range (graphMap g)) :=
    h_emb.map_comap μH[2]
  have h_map_restrict :
      Measure.map (graphMap g) (ρ.restrict A) =
        μH[2].restrict (graphMap g '' A) := by
    calc
      Measure.map (graphMap g) (ρ.restrict A) =
          (Measure.map (graphMap g) ρ).restrict (graphMap g '' A) := by
        rw [h_emb.restrict_map ρ (graphMap g '' A), h_preimage]
      _ = (μH[2].restrict (Set.range (graphMap g))).restrict
          (graphMap g '' A) := by rw [h_map]
      _ = μH[2].restrict (graphMap g '' A) := by
        rw [Measure.restrict_restrict h_image_meas,
          inter_eq_left.mpr h_image_sub]
  have h_area_meas : Measurable (areaFactor g) :=
    (continuousOn_univ.mp
      (areaFactor_continuousOn isOpen_univ hg.contDiffOn)).measurable
  calc
    (∫⁻ z in graphMap g '' A, f z ∂μH[2]) =
        ∫⁻ z, f z ∂Measure.map (graphMap g) (ρ.restrict A) := by
      rw [h_map_restrict]
    _ = ∫⁻ y in A, f (graphMap g y) ∂ρ := by
      exact h_emb.lintegral_map f
    _ = ∫⁻ y in A, f (graphMap g y) ∂volume.withDensity (areaFactor g) := by
      rw [hρ_density]
    _ = ∫⁻ y in A, areaFactor g y * f (graphMap g y) ∂volume := by
      exact setLIntegral_withDensity_eq_setLIntegral_mul volume
        h_area_meas (hf.comp h_emb.measurable) hA
    _ = ∫⁻ y in A, f (graphMap g y) * areaFactor g y ∂volume := by
      apply lintegral_congr
      intro y
      exact mul_comm _ _

end Kakeya.CV
