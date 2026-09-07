import MyLeanRepo.Kakeya.CV.PolynomialCylinder.RegularCover
import MyLeanRepo.Kakeya.CV.GeometricMeasure.GraphAreaWeightedOnOpen
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Weighted graph area in every coordinate direction

Coordinate permutations preserve Hausdorff measure. This transfers the
weighted graph-area formula from standard z-graphs to the x- and y-graph
conventions used by the simultaneous regular cover.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

/-- A linear isometry transports set integrals against two-dimensional
Hausdorff measure without a Jacobian factor. -/
lemma setLIntegral_image_linearIsometryEquiv
    (σ : Point 3 ≃ₗᵢ[ℝ] Point 3)
    (f : Point 3 → ENNReal) (S : Set (Point 3)) :
    ∫⁻ z in σ '' S, f z ∂μH[2] =
      ∫⁻ z in S, f (σ z) ∂μH[2] := by
  have hmp : MeasurePreserving σ μH[2] μH[2] :=
    IsometryEquiv.measurePreserving_hausdorffMeasure
      σ.toIsometryEquiv 2
  have hemb : MeasurableEmbedding σ :=
    σ.toMeasurableEquiv.measurableEmbedding
  exact (hmp.setLIntegral_comp_emb hemb f S).symm

/-- Weighted graph-area formula for any of the three coordinate graph
directions. -/
lemma dir_graph_area_formula_weighted_on_open
    (dir : Fin 3) (g : R2 → ℝ)
    {A : Set R2} (hA : IsOpen A)
    (hg : ContDiffOn ℝ 1 g A)
    {B : Set R2} (hB : MeasurableSet B)
    (hB_sub : B ⊆ A)
    {f : R3 → ENNReal} (hf : Measurable f) :
    ∫⁻ z in dirGraphMap dir g '' B, f z ∂μH[2] =
      ∫⁻ y in B,
        f (dirGraphMap dir g y) * areaFactor g y ∂volume := by
  fin_cases dir
  · let σ : Point 3 ≃ₗᵢ[ℝ] Point 3 :=
      swapCoordsIsometry 0 2
    have hσ_graph :
        ∀ y, σ (graphMap g y) = xGraphMap g y :=
      fun y => rfl
    have hσ_image :
        σ '' (graphMap g '' B) = xGraphMap g '' B := by
      ext z
      constructor
      · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, hσ_graph y⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨graphMap g y, ⟨y, hy, rfl⟩, hσ_graph y⟩
    have hchange :
        ∫⁻ z in xGraphMap g '' B, f z ∂μH[2] =
          ∫⁻ z in graphMap g '' B, f (σ z) ∂μH[2] := by
      have h :=
        setLIntegral_image_linearIsometryEquiv
          σ f (graphMap g '' B)
      rw [hσ_image] at h
      exact h
    have harea :
        ∫⁻ z in graphMap g '' B, f (σ z) ∂μH[2] =
          ∫⁻ y in B,
            f (σ (graphMap g y)) * areaFactor g y ∂volume := by
      simpa only [Function.comp_apply] using
        graph_area_formula_weighted_on_open
          hA hg hB hB_sub
            (hf.comp σ.continuous.measurable)
    change
      (∫⁻ z in xGraphMap g '' B, f z ∂μH[2]) =
        ∫⁻ y in B,
          f (xGraphMap g y) * areaFactor g y ∂volume
    calc
      (∫⁻ z in xGraphMap g '' B, f z ∂μH[2])
          = ∫⁻ z in graphMap g '' B,
              f (σ z) ∂μH[2] := hchange
      _ = ∫⁻ y in B,
            f (σ (graphMap g y)) *
              areaFactor g y ∂volume := harea
      _ = ∫⁻ y in B,
            f (xGraphMap g y) *
              areaFactor g y ∂volume := by
          apply setLIntegral_congr_fun hB
          intro y _
          change
            f (σ (graphMap g y)) * areaFactor g y =
              f (xGraphMap g y) * areaFactor g y
          rw [hσ_graph y]
  · let σ : Point 3 ≃ₗᵢ[ℝ] Point 3 :=
      swapCoordsIsometry 1 2
    have hσ_graph :
        ∀ y, σ (graphMap g y) = yGraphMap g y :=
      fun y => rfl
    have hσ_image :
        σ '' (graphMap g '' B) = yGraphMap g '' B := by
      ext z
      constructor
      · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, hσ_graph y⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨graphMap g y, ⟨y, hy, rfl⟩, hσ_graph y⟩
    have hchange :
        ∫⁻ z in yGraphMap g '' B, f z ∂μH[2] =
          ∫⁻ z in graphMap g '' B, f (σ z) ∂μH[2] := by
      have h :=
        setLIntegral_image_linearIsometryEquiv
          σ f (graphMap g '' B)
      rw [hσ_image] at h
      exact h
    have harea :
        ∫⁻ z in graphMap g '' B, f (σ z) ∂μH[2] =
          ∫⁻ y in B,
            f (σ (graphMap g y)) * areaFactor g y ∂volume := by
      simpa only [Function.comp_apply] using
        graph_area_formula_weighted_on_open
          hA hg hB hB_sub
            (hf.comp σ.continuous.measurable)
    change
      (∫⁻ z in yGraphMap g '' B, f z ∂μH[2]) =
        ∫⁻ y in B,
          f (yGraphMap g y) * areaFactor g y ∂volume
    calc
      (∫⁻ z in yGraphMap g '' B, f z ∂μH[2])
          = ∫⁻ z in graphMap g '' B,
              f (σ z) ∂μH[2] := hchange
      _ = ∫⁻ y in B,
            f (σ (graphMap g y)) *
              areaFactor g y ∂volume := harea
      _ = ∫⁻ y in B,
            f (yGraphMap g y) *
              areaFactor g y ∂volume := by
          apply setLIntegral_congr_fun hB
          intro y _
          change
            f (σ (graphMap g y)) * areaFactor g y =
              f (yGraphMap g y) * areaFactor g y
          rw [hσ_graph y]
  · simpa [dirGraphMap] using
      graph_area_formula_weighted_on_open
        hA hg hB hB_sub hf

end Kakeya.CV
