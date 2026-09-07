import MyLeanRepo.Kakeya.CV.PolynomialCylinder.GraphAreaBasics
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Hausdorff-measure pullback along a global C¹ graph

The graph embedding pulls ambient two-dimensional Hausdorff measure back to a
measure on the parameter plane. For a globally C¹ graph this pullback is finite
on compact sets, hence locally finite.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

/-- Projection from the graph ambient space to its first two coordinates. -/
def graphProjection : R3 → R2 := fun p =>
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![p 0, p 1]

lemma graphProjection_continuous : Continuous graphProjection := by
  have h₀ : Continuous (fun p : R3 => p 0) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0
  have h₁ : Continuous (fun p : R3 => p 1) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1
  have hpi :
      Continuous (fun p : R3 => (![p 0, p 1] : Fin 2 → ℝ)) :=
    continuous_pi fun i => by
      fin_cases i
      · exact h₀
      · exact h₁
  exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp hpi

lemma graphProjection_leftInverse (g : R2 → ℝ) :
    Function.LeftInverse graphProjection (graphMap g) := by
  intro y
  ext i
  fin_cases i <;> simp [graphProjection, graphMap]

lemma graphMap_injective (g : R2 → ℝ) :
    Function.Injective (graphMap g) :=
  (graphProjection_leftInverse g).injective

lemma graphMap_continuous {g : R2 → ℝ} (hg : Continuous g) :
    Continuous (graphMap g) := by
  have h₀ : Continuous (fun x : R2 => x 0) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  have h₁ : Continuous (fun x : R2 => x 1) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
  have hpi :
      Continuous (fun x : R2 => (![x 0, x 1, g x] : Fin 3 → ℝ)) :=
    continuous_pi fun i => by
      fin_cases i
      · exact h₀
      · exact h₁
      · exact hg
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp hpi

/-- A continuous graph map is a measurable embedding. -/
def graphMap_measurableEmbedding {g : R2 → ℝ} (hg : Continuous g) :
    MeasurableEmbedding (graphMap g) :=
  (graphMap_continuous hg).measurable.measurableEmbedding
    (graphMap_injective g)

/-- Pullback of ambient `μH[2]` along a graph embedding. -/
def graphPullbackMeasure (g : R2 → ℝ) : Measure R2 :=
  (μH[2] : Measure R3).comap (graphMap g)

lemma graphPullbackMeasure_apply {g : R2 → ℝ} (hg : Continuous g)
    {E : Set R2} (hE : MeasurableSet E) :
    graphPullbackMeasure g E = μH[2] (graphMap g '' E) :=
  (graphMap_measurableEmbedding hg).comap_apply μH[2] E

lemma graphMap_contDiff {g : R2 → ℝ} (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (graphMap g) := by
  apply contDiff_piLp' 2
  intro i
  fin_cases i
  · simpa [graphMap] using
      (contDiff_piLp_apply (𝕜 := ℝ) (n := 1)
        (p := (2 : ENNReal)) (E := fun _ : Fin 2 => ℝ) (i := 0))
  · simpa [graphMap] using
      (contDiff_piLp_apply (𝕜 := ℝ) (n := 1)
        (p := (2 : ENNReal)) (E := fun _ : Fin 2 => ℝ) (i := 1))
  · simpa [graphMap] using hg

/-- The graph pullback of a globally C¹ function is finite on compact sets. -/
theorem graphPullbackMeasure_isFiniteMeasureOnCompacts
    (g : R2 → ℝ) (hg : ContDiff ℝ 1 g) :
    IsFiniteMeasureOnCompacts (graphPullbackMeasure g) := by
  refine ⟨?_⟩
  intro K hK
  have hgraph : ContDiff ℝ 1 (graphMap g) := graphMap_contDiff hg
  have hlocal : LocallyLipschitz (graphMap g) :=
    hgraph.locallyLipschitz
  obtain ⟨C, hC⟩ :=
    hlocal.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  rw [graphPullbackMeasure_apply hg.continuous hK.measurableSet]
  have hbound :
      μH[2] (graphMap g '' K) ≤
        (C : ENNReal) ^ (2 : ℝ) * μH[2] K :=
    hC.hausdorffMeasure_image_le (d := (2 : ℝ)) (by norm_num)
  have hK_volume : volume K ≠ ⊤ := hK.measure_ne_top
  have hK_hausdorff : μH[2] K ≠ ⊤ := by
    rw [μH2_eq K]
    exact ENNReal.mul_ne_top planeConstant_ne_top hK_volume
  have hC_finite : (C : ENNReal) ^ (2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.coe_ne_top
  exact hbound.trans_lt
    (ENNReal.mul_lt_top hC_finite.lt_top hK_hausdorff.lt_top)

/-- The graph pullback of a globally C¹ function is locally finite. -/
theorem graphPullbackMeasure_isLocallyFinite
    (g : R2 → ℝ) (hg : ContDiff ℝ 1 g) :
    IsLocallyFiniteMeasure (graphPullbackMeasure g) := by
  letI : IsFiniteMeasureOnCompacts (graphPullbackMeasure g) :=
    graphPullbackMeasure_isFiniteMeasureOnCompacts g hg
  infer_instance

end Kakeya.CV
