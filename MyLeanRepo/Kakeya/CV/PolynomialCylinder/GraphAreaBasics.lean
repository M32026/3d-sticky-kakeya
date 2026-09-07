import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Graph area inequality: basic definitions and helper lemmas
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

abbrev R2 := EuclideanSpace ℝ (Fin 2)
abbrev R3 := EuclideanSpace ℝ (Fin 3)

def e02 : R2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![1, 0]
def e12 : R2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 1]

def graphMap (f : R2 → ℝ) : R2 → R3 :=
  fun x => (EuclideanSpace.equiv (Fin 3) ℝ).symm ![x 0, x 1, f x]

def graphG (f : R2 → ℝ) : R2 → R2 :=
  fun y => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![y 1, f y]

def graphG' (f : R2 → ℝ) : R2 → R2 :=
  fun y => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![y 0, f y]

-- ============================================================================
-- planeConstant
-- ============================================================================

local instance : (μH[2] : Measure R2).IsAddHaarMeasure := by
  have hfin : Module.finrank ℝ R2 = 2 := finrank_euclideanSpace_fin
  have h_eq : (μH[2] : Measure R2) = μH[Module.finrank ℝ R2] := by
    congr 1 <;> exact_mod_cast hfin.symm
  exact h_eq ▸ (inferInstance : (μH[Module.finrank ℝ R2] : Measure R2).IsAddHaarMeasure)

def planeConstant : ENNReal :=
  (MeasureTheory.Measure.addHaarScalarFactor (volume : Measure R2) (μH[2] : Measure R2) : ENNReal)⁻¹

lemma μH2_eq : ∀ (S : Set R2), μH[2] S = planeConstant * volume S := by
  intro S
  have h1 : (μHE[2] : Measure R2) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2
  let hf : NNReal := MeasureTheory.Measure.addHaarScalarFactor (volume : Measure R2) (μH[2] : Measure R2)
  have h2 : (μHE[2] : Measure R2) = (hf : ENNReal) • μH[2] := by
    rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def] <;> rfl
  rw [h2] at h1
  have h3 : (hf : ENNReal) * μH[2] S = volume S := by
    have h4 : ((hf : ENNReal) • μH[2]) S = (hf : ENNReal) * μH[2] S := by rfl
    have h5 : ((hf : ENNReal) • μH[2]) S = volume S := by rw [h1]
    rw [h4] at h5; exact h5
  have h5 : (hf : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero 2)
  have h6 : (hf : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h7 : (hf : ENNReal)⁻¹ * ((hf : ENNReal) * μH[2] S) = μH[2] S := by
    rw [←mul_assoc, ENNReal.inv_mul_cancel h5 h6] <;> simp
  have h8 : μH[2] S = (hf : ENNReal)⁻¹ * volume S := by
    rw [←h3]; exact h7.symm
  simpa [planeConstant] using h8

lemma planeConstant_ne_top : planeConstant ≠ ⊤ := by
  dsimp only [planeConstant]
  have h5 : (MeasureTheory.Measure.addHaarScalarFactor (volume : Measure R2) (μH[2] : Measure R2) : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero 2)
  exact ENNReal.inv_ne_top.mpr h5

lemma planeConstant_pos : 0 < planeConstant := by
  dsimp only [planeConstant]
  have h6 : (MeasureTheory.Measure.addHaarScalarFactor (volume : Measure R2) (μH[2] : Measure R2) : ENNReal) ≠ ⊤ :=
    ENNReal.coe_ne_top
  exact ENNReal.inv_pos.mpr h6

-- ============================================================================
-- Weight function
-- ============================================================================

def graphAreaW (p : MvPolynomial (Fin 3) ℝ) : R3 → ENNReal :=
  fun x => ENNReal.ofReal ‖inner ℝ e3 (polynomialUnitNormal p x)‖

-- ============================================================================
-- Helper lemmas (proved)
-- ============================================================================

lemma hasDerivAt_smulVec (v : R2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => s • v) v t := by
  have h_id : HasDerivAt (id : ℝ → ℝ) 1 t := hasDerivAt_id t
  simpa [one_smul] using h_id.smul_const v

lemma algebraic_ineq_C (a b c d : ℝ) (h1 : c^2 ≥ 81 / 100 * d^2) (h2 : c^2 ≥ 9025 / 10000) :
    a^2 ≤ 3 * b^2 + 3 * (c*a + d*b)^2 := by
  have h_pos1 : 0 < 3 * c^2 - 1 := by nlinarith
  have h_det : 0 ≤ 3 * c^2 - d^2 - 1 := by
    by_cases h : d^2 ≤ 3 * (9025 / 10000 : ℝ) - 1
    · nlinarith
    · nlinarith [h1]
  have h_main : 0 ≤ (3 * c^2 - 1) * a^2 + 6 * c * d * a * b + (3 * d^2 + 3) * b^2 := by
    have h9 : (3 * c^2 - 1) * a^2 + 6 * c * d * a * b + (3 * d^2 + 3) * b^2 =
        (3 * c^2 - 1) * (a + (3 * c * d) / (3 * c^2 - 1) * b)^2 +
        (3 * (3 * c^2 - d^2 - 1)) / (3 * c^2 - 1) * b^2 := by
      field_simp [h_pos1.ne'] <;> ring
    rw [h9]
    have h10 : 0 ≤ (3 * c^2 - 1) * (a + (3 * c * d) / (3 * c^2 - 1) * b)^2 := by positivity
    have h11 : 0 ≤ (3 * (3 * c^2 - d^2 - 1)) / (3 * c^2 - 1) * b^2 := by
      have h12 : 0 ≤ 3 * c^2 - d^2 - 1 := h_det
      positivity
    linarith
  have h_expand : 3 * b^2 + 3 * (c*a + d*b)^2 - a^2 =
      (3 * c^2 - 1) * a^2 + 6 * c * d * a * b + (3 * d^2 + 3) * b^2 := by ring
  have h_goal : 0 ≤ 3 * b^2 + 3 * (c*a + d*b)^2 - a^2 := by
    rw [h_expand]; exact h_main
  linarith

lemma fderiv_decomp (f : R2 → ℝ) (y : R2) (v : R2) :
    fderiv ℝ f y v = (fderiv ℝ f y e02) * (v 0) + (fderiv ℝ f y e12) * (v 1) := by
  have h : v = (v 0) • e02 + (v 1) • e12 := by
    ext i; fin_cases i <;> simp [e02, e12] <;> ring
  have h_main : fderiv ℝ f y v = fderiv ℝ f y ((v 0) • e02 + (v 1) • e12) :=
    congr_arg (fderiv ℝ f y) h
  rw [h_main]
  have h2 : fderiv ℝ f y ((v 0) • e02 + (v 1) • e12) =
      fderiv ℝ f y ((v 0) • e02) + fderiv ℝ f y ((v 1) • e12) := by
    exact (fderiv ℝ f y).map_add ((v 0) • e02) ((v 1) • e12)
  rw [h2]
  have h3 : fderiv ℝ f y ((v 0) • e02) = (v 0) * fderiv ℝ f y e02 := by
    exact (fderiv ℝ f y).map_smul (v 0) e02
  have h4 : fderiv ℝ f y ((v 1) • e12) = (v 1) * fderiv ℝ f y e12 := by
    exact (fderiv ℝ f y).map_smul (v 1) e12
  rw [h3, h4] <;> simp [mul_comm] <;> ring

/-- Norm squared of a 3D vector equals sum of squared components. -/
lemma norm_sq_R3 (v : R3) : ‖v‖^2 = (v 0)^2 + (v 1)^2 + (v 2)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] <;> rfl

/-- Norm squared of a 2D vector equals sum of squared components. -/
lemma norm_sq_R2 (v : R2) : ‖v‖^2 = (v 0)^2 + (v 1)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> rfl

lemma mvt_on_segment {U : Set R2} {f : R2 → ℝ} (hU : IsOpen U)
    (hf : DifferentiableOn ℝ f U) (V : Set R2) (hV : Convex ℝ V) (hV_sub : V ⊆ U)
    (x y : R2) (hx : x ∈ V) (hy : y ∈ V) :
    ∃ (ξ : R2), ξ ∈ V ∧ f x - f y = fderiv ℝ f ξ (x - y) := by
  let g : ℝ → ℝ := fun t => f (y + t • (x - y))
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → y + t • (x - y) ∈ V := by
    intro t ht0 ht1
    have h_eq2 : y + t • (x - y) = (1 - t) • y + t • x := by
      simp [add_smul, sub_smul, smul_sub] <;> abel
    rw [h_eq2]
    have ha : 0 ≤ (1 - t : ℝ) := by linarith
    have hb : 0 ≤ (t : ℝ) := by linarith
    have hab : (1 - t : ℝ) + t = 1 := by ring
    exact hV hy hx ha hb hab
  have h_cont1 : Continuous (fun t : ℝ => y + t • (x - y)) := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have h_maps : MapsTo (fun t : ℝ => y + t • (x - y)) (Icc (0 : ℝ) 1) U := by
    intro t ht; exact hV_sub (hseg t ht.1 ht.2)
  have hg_cont : ContinuousOn g (Icc (0 : ℝ) 1) :=
    hf.continuousOn.comp h_cont1.continuousOn h_maps
  let g' : ℝ → ℝ := fun t => fderiv ℝ f (y + t • (x - y)) (x - y)
  have hg_diff : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g (g' t) t := by
    intro t ht
    set pt : R2 := y + t • (x - y) with hpt_def
    have hptV : pt ∈ V := hseg t (by linarith [ht.1]) (by linarith [ht.2])
    have hfd : HasFDerivAt f (fderiv ℝ f pt) pt :=
      (hf.differentiableAt (hU.mem_nhds (hV_sub hptV))).hasFDerivAt
    have hlin : HasDerivAt (fun t : ℝ => y + t • (x - y)) (x - y) t := by
      have h : HasDerivAt (fun t : ℝ => t • (x - y)) (x - y) t := hasDerivAt_smulVec (x - y) t
      simpa using h.const_add y
    have hlin' : HasFDerivAt (fun t : ℝ => y + t • (x - y))
        (ContinuousLinearMap.toSpanSingleton ℝ (x - y)) t :=
      hlin.hasFDerivAt
    have hcomp : HasFDerivAt g _ t := hfd.comp t hlin'
    simpa [g'] using hcomp.hasDerivAt
  have h_mvt : ∃ t ∈ Ioo (0 : ℝ) 1, g' t = g 1 - g 0 := by
    have h : ∃ t ∈ Ioo (0 : ℝ) 1, g' t = (g 1 - g 0) / (1 - 0) :=
      exists_hasDerivAt_eq_slope (f := g) (f' := g') (a := 0) (b := 1)
        (by norm_num) hg_cont hg_diff
    rcases h with ⟨t, ht, h_eq2⟩
    have h_final : g' t = g 1 - g 0 := by rw [h_eq2] <;> ring
    exact ⟨t, ht, h_final⟩
  rcases h_mvt with ⟨t, ht, h_eq2⟩
  set ξ : R2 := y + t • (x - y) with hξ_def
  have hξV : ξ ∈ V := hseg t (by linarith [ht.1]) (by linarith [ht.2])
  have h5 : g' t = fderiv ℝ f ξ (x - y) := by simp [g', hξ_def]
  have h6 : g 1 - g 0 = f x - f y := by simp [g]
  have h7 : g' t = f x - f y := by rw [h_eq2, h6]
  exact ⟨ξ, hξV, by rw [←h5, h7]⟩


end Kakeya.CV
