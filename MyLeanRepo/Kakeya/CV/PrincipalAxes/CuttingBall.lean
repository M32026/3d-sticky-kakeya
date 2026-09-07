import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.GeometricMeasure.FrontierSumBound
import MyLeanRepo.Kakeya.CV.GeometricMeasure.SphereFiniteness
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.AffinePullback
import MyLeanRepo.Kakeya.CV.Targets.ManyBisections.AffineTools
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# 40/40 cuts ball lemma

Generalization of `bisectingBallLemma` to `PolynomialCutsAtLeast`.

If both strict sign regions of a polynomial occupy at least 2/5 of the unit
ball, then the zero set inside the ball has at least a fixed positive fraction
of the unit sphere's 2D Hausdorff measure.

The constant is `cutsBallConstant := (2 * (2/5)^(2/3) - 1) / 2 > 0`.
-/

noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal Real BigOperators

namespace Kakeya.CV

section CuttingBall

/-- Positive constant for the 40/40 cuts ball lemma. -/
def cutsBallConstant : ℝ := (2 * (2 / 5 : ℝ) ^ (2 / 3 : ℝ) - 1) / 2

/-- `cutsBallConstant > 0`. -/
lemma cutsBallConstant_pos : 0 < cutsBallConstant := by
  have h13 : (4 / 25 : ℝ) > (1 / 8 : ℝ) := by norm_num
  have h14 : (4 / 25 : ℝ) ^ (1 / 3 : ℝ) > (1 / 8 : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_lt_rpow (by norm_num) h13 (by norm_num)
  have h15 : (1 / 8 : ℝ) ^ (1 / 3 : ℝ) = 1 / 2 := by norm_num
  have h16 : (2 / 5 : ℝ) ^ (2 / 3 : ℝ) = (4 / 25 : ℝ) ^ (1 / 3 : ℝ) := by
    have h_nonneg : 0 ≤ (2 / 5 : ℝ) := by norm_num
    have h_eq1 : (2 / 3 : ℝ) = (2 : ℝ) * (1 / 3 : ℝ) := by norm_num
    rw [h_eq1]
    have h17 : (2 / 5 : ℝ) ^ ((2 : ℝ) * (1 / 3 : ℝ)) =
        ((2 / 5 : ℝ) ^ (2 : ℝ)) ^ (1 / 3 : ℝ) := by
      rw [Real.rpow_mul h_nonneg]
    rw [h17]
    have h18 : (2 / 5 : ℝ) ^ (2 : ℝ) = (4 / 25 : ℝ) := by norm_num
    rw [h18]
  have h12 : (2 / 5 : ℝ) ^ (2 / 3 : ℝ) > 1 / 2 := by
    rw [h16]
    linarith [h14, h15]
  have h11 : 2 * (2 / 5 : ℝ) ^ (2 / 3 : ℝ) > 1 := by linarith
  dsimp only [cutsBallConstant]
  linarith

/-- Helper: `(2/5)^(2/3) > 1/2`. -/
private lemma two_fifths_rpow_gt_half :
    (2 / 5 : ℝ) ^ (2 / 3 : ℝ) > 1 / 2 := by
  have h13 : (4 / 25 : ℝ) > (1 / 8 : ℝ) := by norm_num
  have h14 : (4 / 25 : ℝ) ^ (1 / 3 : ℝ) > (1 / 8 : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_lt_rpow (by norm_num) h13 (by norm_num)
  have h15 : (1 / 8 : ℝ) ^ (1 / 3 : ℝ) = 1 / 2 := by norm_num
  have h16 : (2 / 5 : ℝ) ^ (2 / 3 : ℝ) = (4 / 25 : ℝ) ^ (1 / 3 : ℝ) := by
    have h_nonneg : 0 ≤ (2 / 5 : ℝ) := by norm_num
    have h_eq1 : (2 / 3 : ℝ) = (2 : ℝ) * (1 / 3 : ℝ) := by norm_num
    rw [h_eq1]
    have h17 : (2 / 5 : ℝ) ^ ((2 : ℝ) * (1 / 3 : ℝ)) =
        ((2 / 5 : ℝ) ^ (2 : ℝ)) ^ (1 / 3 : ℝ) := by
      rw [Real.rpow_mul h_nonneg]
    rw [h17]
    have h18 : (2 / 5 : ℝ) ^ (2 : ℝ) = (4 / 25 : ℝ) := by norm_num
    rw [h18]
  rw [h16]
  linarith [h14, h15]

/-- Core ENNReal arithmetic: cancel μS and divide by 2. -/
lemma bisecting_arithmetic_main (c d μS μZ : ENNReal)
    (hS_ne_top : μS ≠ ⊤)
    (h11 : 1 ≤ 2 * c)
    (_h2c_lt_top : 2 * c < ⊤)
    (h9 : 2 * c * μS ≤ μS + 2 * μZ)
    (h_2d_le : 2 * d ≤ 2 * c - 1) :
    d * μS ≤ μZ := by
  let b := 2 * c - 1
  have h_eq1 : b + 1 = 2 * c := by
    exact tsub_add_cancel_of_le h11
  have h20 : b * μS + μS = 2 * c * μS := by
    have h21 : b * μS + μS = b * μS + 1 * μS := by rw [one_mul]
    rw [h21]
    have h22 : b * μS + 1 * μS = (b + 1) * μS := by rw [add_mul]
    rw [h22, h_eq1]
  have h21 : b * μS + μS ≤ μS + 2 * μZ := by
    rw [h20]; exact h9
  have h22 : b * μS + μS ≤ 2 * μZ + μS := by
    rw [add_comm (2 * μZ) μS]; exact h21
  have h10 : b * μS ≤ 2 * μZ :=
    ENNReal.le_of_add_le_add_right hS_ne_top h22
  have h11' : 2 * d * μS ≤ b * μS := by gcongr
  have h12 : 2 * d * μS ≤ 2 * μZ := le_trans h11' h10
  have h13 : 2 * (d * μS) ≤ 2 * μZ := by
    have h14 : 2 * d * μS = 2 * (d * μS) := by ring
    rw [h14] at h12
    exact h12
  by_contra h
  have h15 : μZ < d * μS := by exact lt_of_not_ge h
  have h16 : (2 : ENNReal) * μZ < (2 : ENNReal) * (d * μS) :=
    ENNReal.mul_lt_mul_right (show (2 : ENNReal) ≠ 0 from by norm_num)
      (show (2 : ENNReal) ≠ ⊤ from by norm_num) h15
  exact not_le.mpr h16 h13

/-- From a 40/40 cut of the unit ball, both the sublevel and superlevel
volume fractions lie in `[2/5, 3/5]`. -/
lemma cutsAtLeast_fractionBounds (p : MvPolynomial (Fin 3) ℝ)
    (hCut : PolynomialCutsAtLeast p (unitBall 3) (2 / 5 : ℝ≥0∞)) :
    ∃ (a b : ℝ),
      a ∈ Set.Icc (2 / 5 : ℝ) (3 / 5 : ℝ) ∧
      b ∈ Set.Icc (2 / 5 : ℝ) (3 / 5 : ℝ) ∧
      volume (unitBall 3 ∩ {x | polynomialValue p x ≤ 0}) =
        ENNReal.ofReal a * volume (unitBall 3) ∧
      volume (unitBall 3 ∩ {x | polynomialValue p x ≥ 0}) =
        ENNReal.ofReal b * volume (unitBall 3) := by
  let B := unitBall 3
  let E := B ∩ {x | polynomialValue p x ≤ 0}
  let F := B ∩ {x | polynomialValue p x ≥ 0}
  let N := B ∩ {x | polynomialValue p x < 0}
  let P := B ∩ {x | 0 < polynomialValue p x}
  have hfinB : volume B < ⊤ := IsCompact.measure_lt_top (isCompact_closedBall 0 1)
  have hposB : 0 < volume B := Metric.measure_closedBall_pos volume 0 (by norm_num)
  have hN_lower : (2 / 5 : ENNReal) * volume B ≤ volume N := hCut.1
  have hP_lower : (2 / 5 : ENNReal) * volume B ≤ volume P := hCut.2
  have hN_sub_E : N ⊆ E := by
    intro x hx
    have h1 : x ∈ B := hx.1
    have h2 : polynomialValue p x < 0 := by simpa [N] using hx.2
    have h3 : polynomialValue p x ≤ 0 := le_of_lt h2
    simpa [E] using ⟨h1, h3⟩
  have hP_sub_F : P ⊆ F := by
    intro x hx
    have h1 : x ∈ B := hx.1
    have h2 : 0 < polynomialValue p x := by simpa [P] using hx.2
    have h3 : 0 ≤ polynomialValue p x := le_of_lt h2
    simpa [F] using ⟨h1, h3⟩
  have hE_lower : (2 / 5 : ENNReal) * volume B ≤ volume E :=
    le_trans hN_lower (measure_mono hN_sub_E)
  have hF_lower : (2 / 5 : ENNReal) * volume B ≤ volume F :=
    le_trans hP_lower (measure_mono hP_sub_F)
  have h_cont : Continuous (fun x : Point 3 => polynomialValue p x) := by
    have h1 : Continuous (EuclideanSpace.equiv (Fin 3) ℝ) :=
      (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap.continuous_of_finiteDimensional
    have h2 : Continuous (fun f : Fin 3 → ℝ => MvPolynomial.eval f p) :=
      MvPolynomial.continuous_eval p
    exact h2.comp h1
  have hE_meas : MeasurableSet E :=
    Metric.isClosed_closedBall.measurableSet.inter (isClosed_le h_cont continuous_const).measurableSet
  have hP_meas : MeasurableSet P :=
    Metric.isClosed_closedBall.measurableSet.inter (isOpen_lt continuous_const h_cont).measurableSet
  have hF_meas : MeasurableSet F :=
    Metric.isClosed_closedBall.measurableSet.inter (isClosed_le continuous_const h_cont).measurableSet
  have hN_meas : MeasurableSet N :=
    Metric.isClosed_closedBall.measurableSet.inter (isOpen_lt h_cont continuous_const).measurableSet
  have hEP_disj : Disjoint E P := by
    rw [disjoint_left]
    intro x hxE hxP
    have hle : polynomialValue p x ≤ 0 := by simpa [E] using hxE.2
    have hgt : 0 < polynomialValue p x := by simpa [P] using hxP.2
    linarith
  have hFN_disj : Disjoint F N := by
    rw [disjoint_left]
    intro x hxF hxN
    have hge : 0 ≤ polynomialValue p x := by simpa [F] using hxF.2
    have hlt : polynomialValue p x < 0 := by simpa [N] using hxN.2
    linarith
  have hEP_union : E ∪ P = B := by
    ext x
    simp only [E, P, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hB
      by_cases h : polynomialValue p x ≤ 0
      · exact Or.inl ⟨hB, h⟩
      · have h' : 0 < polynomialValue p x := by linarith
        exact Or.inr ⟨hB, h'⟩
  have hFN_union : F ∪ N = B := by
    ext x
    simp only [F, N, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hB
      by_cases h : 0 ≤ polynomialValue p x
      · exact Or.inl ⟨hB, h⟩
      · have h' : polynomialValue p x < 0 := by linarith
        exact Or.inr ⟨hB, h'⟩
  have hEP_sum : volume E + volume P = volume B := by
    have h : volume (E ∪ P) = volume E + volume P :=
      measure_union hEP_disj hP_meas
    have h' : volume (E ∪ P) = volume B := by rw [hEP_union]
    rw [h'] at h
    exact h.symm
  have hFN_sum : volume F + volume N = volume B := by
    have h : volume (F ∪ N) = volume F + volume N :=
      measure_union hFN_disj hN_meas
    have h' : volume (F ∪ N) = volume B := by rw [hFN_union]
    rw [h'] at h
    exact h.symm
  have hfinE : volume E ≠ ⊤ := by
    have h : volume E ≤ volume B := measure_mono (fun x hx => hx.1)
    exact ne_of_lt (lt_of_le_of_lt h hfinB)
  have hfinF : volume F ≠ ⊤ := by
    have h : volume F ≤ volume B := measure_mono (fun x hx => hx.1)
    exact ne_of_lt (lt_of_le_of_lt h hfinB)
  have hfinP : volume P ≠ ⊤ := by
    have h : volume P ≤ volume B := measure_mono (fun x hx => hx.1)
    exact ne_of_lt (lt_of_le_of_lt h hfinB)
  have hfinN : volume N ≠ ⊤ := by
    have h : volume N ≤ volume B := measure_mono (fun x hx => hx.1)
    exact ne_of_lt (lt_of_le_of_lt h hfinB)
  have hEP_sum_real : (volume E).toReal + (volume P).toReal = (volume B).toReal := by
    rw [← ENNReal.toReal_add hfinE hfinP, hEP_sum]
  have hFN_sum_real : (volume F).toReal + (volume N).toReal = (volume B).toReal := by
    rw [← ENNReal.toReal_add hfinF hfinN, hFN_sum]
  have hP_lower_real : (2 / 5 : ℝ) * (volume B).toReal ≤ (volume P).toReal := by
    have h : ((2 / 5 : ENNReal) * volume B).toReal ≤ (volume P).toReal :=
      ENNReal.toReal_mono hfinP hP_lower
    have h2 : ((2 / 5 : ENNReal) * volume B).toReal =
        (2 / 5 : ℝ) * (volume B).toReal := by
      simp [ENNReal.toReal_mul]
    rw [h2] at h
    exact h
  have hN_lower_real : (2 / 5 : ℝ) * (volume B).toReal ≤ (volume N).toReal := by
    have h : ((2 / 5 : ENNReal) * volume B).toReal ≤ (volume N).toReal :=
      ENNReal.toReal_mono hfinN hN_lower
    have h2 : ((2 / 5 : ENNReal) * volume B).toReal =
        (2 / 5 : ℝ) * (volume B).toReal := by
      simp [ENNReal.toReal_mul]
    rw [h2] at h
    exact h
  let a : ℝ := (volume E).toReal / (volume B).toReal
  let b : ℝ := (volume F).toReal / (volume B).toReal
  have hBtoReal_pos : 0 < (volume B).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hposB, hfinB⟩
  have hBtoReal_ne_zero : (volume B).toReal ≠ 0 := hBtoReal_pos.ne'
  have ha_nonneg : 0 ≤ a := by positivity
  have hb_nonneg : 0 ≤ b := by positivity
  have h_toRealE : (volume E).toReal = a * (volume B).toReal := by
    dsimp only [a]; field_simp [hBtoReal_ne_zero]
  have h_toRealF : (volume F).toReal = b * (volume B).toReal := by
    dsimp only [b]; field_simp [hBtoReal_ne_zero]
  have hrealE : volume E = ENNReal.ofReal a * volume B := by
    have h' : volume E = ENNReal.ofReal (volume E).toReal := by
      rw [ENNReal.ofReal_toReal hfinE]
    rw [h', h_toRealE]
    have h_mul : ENNReal.ofReal (a * (volume B).toReal) =
        ENNReal.ofReal a * ENNReal.ofReal (volume B).toReal := by
      rw [ENNReal.ofReal_mul ha_nonneg]
    rw [h_mul]
    have hB_eq : volume B = ENNReal.ofReal (volume B).toReal := by
      rw [ENNReal.ofReal_toReal hfinB.ne]
    exact congr_arg (fun x => ENNReal.ofReal a * x) hB_eq.symm
  have hrealF : volume F = ENNReal.ofReal b * volume B := by
    have h' : volume F = ENNReal.ofReal (volume F).toReal := by
      rw [ENNReal.ofReal_toReal hfinF]
    rw [h', h_toRealF]
    have h_mul : ENNReal.ofReal (b * (volume B).toReal) =
        ENNReal.ofReal b * ENNReal.ofReal (volume B).toReal := by
      rw [ENNReal.ofReal_mul hb_nonneg]
    rw [h_mul]
    have hB_eq : volume B = ENNReal.ofReal (volume B).toReal := by
      rw [ENNReal.ofReal_toReal hfinB.ne]
    exact congr_arg (fun x => ENNReal.ofReal b * x) hB_eq.symm
  have ha_lower : (2 / 5 : ℝ) ≤ a := by
    have h : (volume E).toReal ≥ ((2 / 5 : ENNReal) * volume B).toReal :=
      ENNReal.toReal_mono hfinE hE_lower
    have h2 : ((2 / 5 : ENNReal) * volume B).toReal =
        (2 / 5 : ℝ) * (volume B).toReal := by
      simp [ENNReal.toReal_mul]
    rw [h2] at h
    dsimp only [a]
    have h_div : (2 / 5 : ℝ) =
        ((2 / 5 : ℝ) * (volume B).toReal) / (volume B).toReal := by
      field_simp [hBtoReal_ne_zero]
    calc (2 / 5 : ℝ)
      = ((2 / 5 : ℝ) * (volume B).toReal) / (volume B).toReal := h_div
    _ ≤ (volume E).toReal / (volume B).toReal := by gcongr
  have hb_lower : (2 / 5 : ℝ) ≤ b := by
    have h : (volume F).toReal ≥ ((2 / 5 : ENNReal) * volume B).toReal :=
      ENNReal.toReal_mono hfinF hF_lower
    have h2 : ((2 / 5 : ENNReal) * volume B).toReal =
        (2 / 5 : ℝ) * (volume B).toReal := by
      simp [ENNReal.toReal_mul]
    rw [h2] at h
    dsimp only [b]
    have h_div : (2 / 5 : ℝ) =
        ((2 / 5 : ℝ) * (volume B).toReal) / (volume B).toReal := by
      field_simp [hBtoReal_ne_zero]
    calc (2 / 5 : ℝ)
      = ((2 / 5 : ℝ) * (volume B).toReal) / (volume B).toReal := h_div
    _ ≤ (volume F).toReal / (volume B).toReal := by gcongr
  have ha_upper : a ≤ (3 / 5 : ℝ) := by
    have h : (volume E).toReal ≤ (3 / 5 : ℝ) * (volume B).toReal := by
      linarith [hEP_sum_real, hP_lower_real]
    dsimp only [a]
    have h_div : (3 / 5 : ℝ) =
        ((3 / 5 : ℝ) * (volume B).toReal) / (volume B).toReal := by
      field_simp [hBtoReal_ne_zero]
    rw [h_div]
    gcongr
  have hb_upper : b ≤ (3 / 5 : ℝ) := by
    have h : (volume F).toReal ≤ (3 / 5 : ℝ) * (volume B).toReal := by
      linarith [hFN_sum_real, hN_lower_real]
    dsimp only [b]
    have h_div : (3 / 5 : ℝ) =
        ((3 / 5 : ℝ) * (volume B).toReal) / (volume B).toReal := by
      field_simp [hBtoReal_ne_zero]
    rw [h_div]
    gcongr
  exact ⟨a, b, ⟨ha_lower, ha_upper⟩, ⟨hb_lower, hb_upper⟩, hrealE, hrealF⟩

/-- Cuts-at-least ball lemma: if both strict sign regions occupy at least
2/5 of the unit ball, the polynomial zero set inside the ball has at least
`cutsBallConstant` times the sphere area. -/
lemma cutsAtLeastBallLemma (hIso : PolynomialRegionIsoperimetricStatement)
    (p : MvPolynomial (Fin 3) ℝ)
    (hCut : PolynomialCutsAtLeast p (unitBall 3) (2 / 5 : ℝ≥0∞)) :
    codimensionOneMeasure 3 (polynomialZeroSet p ∩ unitBall 3) ≥
      ENNReal.ofReal cutsBallConstant *
        codimensionOneMeasure 3 (unitSphere 3) := by
  let B := unitBall 3
  let S := unitSphere 3
  let Z := polynomialZeroSet p ∩ B
  let E := B ∩ {x | polynomialValue p x ≤ 0}
  let F := B ∩ {x | polynomialValue p x ≥ 0}
  let N := B ∩ {x | polynomialValue p x < 0}
  let P := B ∩ {x | 0 < polynomialValue p x}
  let μ := codimensionOneMeasure 3

  have hSfin : μ S < ⊤ := sphere_finite
  have hfinB : volume B < ⊤ := IsCompact.measure_lt_top (isCompact_closedBall 0 1)
  have hposB : 0 < volume B := Metric.measure_closedBall_pos volume 0 (by norm_num)

  have hN_lower : (2 / 5 : ENNReal) * volume B ≤ volume N := hCut.1
  have hP_lower : (2 / 5 : ENNReal) * volume B ≤ volume P := hCut.2

  have hN_sub_E : N ⊆ E := by
    intro x hx
    have h1 : x ∈ B := hx.1
    have h2 : polynomialValue p x < 0 := by simpa [N] using hx.2
    have h3 : polynomialValue p x ≤ 0 := le_of_lt h2
    simpa [E] using ⟨h1, h3⟩
  have hP_sub_F : P ⊆ F := by
    intro x hx
    have h1 : x ∈ B := hx.1
    have h2 : 0 < polynomialValue p x := by simpa [P] using hx.2
    have h3 : 0 ≤ polynomialValue p x := le_of_lt h2
    simpa [F] using ⟨h1, h3⟩

  have hE_lower : (2 / 5 : ENNReal) * volume B ≤ volume E :=
    le_trans hN_lower (measure_mono hN_sub_E)
  have hF_lower : (2 / 5 : ENNReal) * volume B ≤ volume F :=
    le_trans hP_lower (measure_mono hP_sub_F)

  have hE_sub_B : E ⊆ B := fun x hx => hx.1
  have hF_sub_B : F ⊆ B := fun x hx => hx.1

  have hfinE : volume E ≠ ⊤ := by
    have h : volume E ≤ volume B := measure_mono hE_sub_B
    exact ne_of_lt (lt_of_le_of_lt h hfinB)
  have hfinF : volume F ≠ ⊤ := by
    have h : volume F ≤ volume B := measure_mono hF_sub_B
    exact ne_of_lt (lt_of_le_of_lt h hfinB)

  let a : ℝ := (volume E).toReal / (volume B).toReal
  let b : ℝ := (volume F).toReal / (volume B).toReal

  have hBtoReal_pos : 0 < (volume B).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hposB, hfinB⟩
  have hBtoReal_ne_zero : (volume B).toReal ≠ 0 := hBtoReal_pos.ne'

  have ha_nonneg : 0 ≤ a := by positivity
  have hb_nonneg : 0 ≤ b := by positivity

  have ha_le_one : a ≤ 1 := by
    have h_le : (volume E).toReal ≤ (volume B).toReal :=
      ENNReal.toReal_mono hfinB.ne (measure_mono hE_sub_B)
    exact (div_le_one hBtoReal_pos).mpr h_le
  have hb_le_one : b ≤ 1 := by
    have h_le : (volume F).toReal ≤ (volume B).toReal :=
      ENNReal.toReal_mono hfinB.ne (measure_mono hF_sub_B)
    exact (div_le_one hBtoReal_pos).mpr h_le

  have ha1 : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha_nonneg, ha_le_one⟩
  have hb1 : b ∈ Set.Icc (0 : ℝ) 1 := ⟨hb_nonneg, hb_le_one⟩

  have ha_lower : (2 / 5 : ℝ) ≤ a := by
    have h : (volume E).toReal ≥ ((2 / 5 : ENNReal) * volume B).toReal :=
      ENNReal.toReal_mono hfinE hE_lower
    have h2 : ((2 / 5 : ENNReal) * volume B).toReal =
        (2 / 5 : ℝ) * (volume B).toReal := by
      simp [ENNReal.toReal_mul]
    rw [h2] at h
    dsimp only [a]
    have h_div : (2 / 5 : ℝ) =
        ((2 / 5 : ℝ) * (volume B).toReal) / (volume B).toReal := by
      field_simp [hBtoReal_ne_zero]
    calc (2 / 5 : ℝ)
      = ((2 / 5 : ℝ) * (volume B).toReal) / (volume B).toReal := h_div
    _ ≤ (volume E).toReal / (volume B).toReal := by gcongr

  have hb_lower : (2 / 5 : ℝ) ≤ b := by
    have h : (volume F).toReal ≥ ((2 / 5 : ENNReal) * volume B).toReal :=
      ENNReal.toReal_mono hfinF hF_lower
    have h2 : ((2 / 5 : ENNReal) * volume B).toReal =
        (2 / 5 : ℝ) * (volume B).toReal := by
      simp [ENNReal.toReal_mul]
    rw [h2] at h
    dsimp only [b]
    have h_div : (2 / 5 : ℝ) =
        ((2 / 5 : ℝ) * (volume B).toReal) / (volume B).toReal := by
      field_simp [hBtoReal_ne_zero]
    calc (2 / 5 : ℝ)
      = ((2 / 5 : ℝ) * (volume B).toReal) / (volume B).toReal := h_div
    _ ≤ (volume F).toReal / (volume B).toReal := by gcongr

  have h_toRealE : (volume E).toReal = a * (volume B).toReal := by
    dsimp only [a]; field_simp [hBtoReal_ne_zero]
  have h_toRealF : (volume F).toReal = b * (volume B).toReal := by
    dsimp only [b]; field_simp [hBtoReal_ne_zero]

  have hrealE : volume E = ENNReal.ofReal a * volume B := by
    have h' : volume E = ENNReal.ofReal (volume E).toReal := by
      rw [ENNReal.ofReal_toReal hfinE]
    rw [h', h_toRealE]
    have h_mul : ENNReal.ofReal (a * (volume B).toReal) =
        ENNReal.ofReal a * ENNReal.ofReal (volume B).toReal := by
      rw [ENNReal.ofReal_mul ha_nonneg]
    rw [h_mul]
    have hB_eq : volume B = ENNReal.ofReal (volume B).toReal := by
      rw [ENNReal.ofReal_toReal hfinB.ne]
    exact congr_arg (fun x => ENNReal.ofReal a * x) hB_eq.symm

  have hrealF : volume F = ENNReal.ofReal b * volume B := by
    have h' : volume F = ENNReal.ofReal (volume F).toReal := by
      rw [ENNReal.ofReal_toReal hfinF]
    rw [h', h_toRealF]
    have h_mul : ENNReal.ofReal (b * (volume B).toReal) =
        ENNReal.ofReal b * ENNReal.ofReal (volume B).toReal := by
      rw [ENNReal.ofReal_mul hb_nonneg]
    rw [h_mul]
    have hB_eq : volume B = ENNReal.ofReal (volume B).toReal := by
      rw [ENNReal.ofReal_toReal hfinB.ne]
    exact congr_arg (fun x => ENNReal.ofReal b * x) hB_eq.symm

  let cE : ℝ := a ^ (2 / 3 : ℝ)
  let cF : ℝ := b ^ (2 / 3 : ℝ)

  have hcE_lower : (2 / 5 : ℝ) ^ (2 / 3 : ℝ) ≤ cE := by
    dsimp only [cE]
    exact Real.rpow_le_rpow (by linarith) ha_lower (by norm_num)
  have hcF_lower : (2 / 5 : ℝ) ^ (2 / 3 : ℝ) ≤ cF := by
    dsimp only [cF]
    exact Real.rpow_le_rpow (by linarith) hb_lower (by norm_num)

  have hE_eq : E = polynomialSublevelInUnitBall p := by rfl
  have h_isoE : μ (frontier E) ≥ ENNReal.ofReal cE * μ S := by
    have h : ENNReal.ofReal a ^ (2 / 3 : ℝ) * μ S ≤ μ (frontier E) := by
      rw [hE_eq]
      exact hIso p a ha1 hrealE
    have h9 : ENNReal.ofReal a ^ (2 / 3 : ℝ) = ENNReal.ofReal cE := by
      rw [ENNReal.ofReal_rpow_of_nonneg ha_nonneg]
      norm_num
    rw [h9] at h
    exact h

  have hF_eq : F = polynomialSublevelInUnitBall (-p) := by
    ext x
    simp only [F, polynomialSublevelInUnitBall, Set.mem_inter_iff, Set.mem_setOf_eq]
    have h_neg : polynomialValue (-p) x = -polynomialValue p x := by
      simp [polynomialValue]
    constructor
    · rintro ⟨hB, hge⟩
      exact ⟨hB, by rw [h_neg]; linarith⟩
    · rintro ⟨hB, hle⟩
      exact ⟨hB, by rw [h_neg] at hle; linarith⟩

  have hrealF' : volume (polynomialSublevelInUnitBall (-p)) =
      ENNReal.ofReal b * volume (unitBall 3) := by
    rw [← hF_eq]
    exact hrealF

  have h_isoF : μ (frontier F) ≥ ENNReal.ofReal cF * μ S := by
    have h : ENNReal.ofReal b ^ (2 / 3 : ℝ) * μ S ≤ μ (frontier F) := by
      rw [hF_eq]
      exact hIso (-p) b hb1 hrealF'
    have h9 : ENNReal.ofReal b ^ (2 / 3 : ℝ) = ENNReal.ofReal cF := by
      rw [ENNReal.ofReal_rpow_of_nonneg hb_nonneg]
      norm_num
    rw [h9] at h
    exact h

  have h_cont : Continuous (fun x : Point 3 => polynomialValue p x) := by
    have h1 : Continuous (EuclideanSpace.equiv (Fin 3) ℝ) := by
      exact (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap.continuous_of_finiteDimensional
    have h2 : Continuous (fun f : Fin 3 → ℝ => MvPolynomial.eval f p) :=
      MvPolynomial.continuous_eval p
    exact h2.comp h1

  have h_sum_bound : μ (frontier E) + μ (frontier F) ≤ μ S + 2 * μ Z :=
    measure_frontier_sum_bound h_cont

  let c_sum : ℝ := cE + cF
  have hc_sum_lower : c_sum ≥ 2 * (2 / 5 : ℝ) ^ (2 / 3 : ℝ) := by
    dsimp only [c_sum]
    linarith [hcE_lower, hcF_lower]

  have h_iso_sum : ENNReal.ofReal c_sum * μ S ≤ μ (frontier E) + μ (frontier F) := by
    have h1 : ENNReal.ofReal cE * μ S + ENNReal.ofReal cF * μ S ≤
        μ (frontier E) + μ (frontier F) := by gcongr
    have h3 : ENNReal.ofReal cE + ENNReal.ofReal cF = ENNReal.ofReal c_sum := by
      rw [← ENNReal.ofReal_add] <;> positivity
    have h2 : ENNReal.ofReal cE * μ S + ENNReal.ofReal cF * μ S =
        ENNReal.ofReal c_sum * μ S := by
      rw [← add_mul, h3]
    rw [h2] at h1
    exact h1

  have h9 : ENNReal.ofReal c_sum * μ S ≤ μ S + 2 * μ Z :=
    le_trans h_iso_sum h_sum_bound

  have h_csum_gt_one : (1 : ℝ) < c_sum := by
    have h10 : c_sum ≥ 2 * (2 / 5 : ℝ) ^ (2 / 3 : ℝ) := hc_sum_lower
    have h11 : 2 * (2 / 5 : ℝ) ^ (2 / 3 : ℝ) > 1 := by
      linarith [two_fifths_rpow_gt_half]
    linarith

  let c_half : ℝ := c_sum / 2
  have h2chalf : 2 * c_half = c_sum := by ring

  have h_one_le : 1 ≤ 2 * ENNReal.ofReal c_half := by
    have h13 : (1 : ℝ) ≤ 2 * c_half := by
      dsimp only [c_half]
      linarith
    have h14 : (1 : ENNReal) ≤ ENNReal.ofReal (2 * c_half) :=
      ENNReal.one_le_ofReal.mpr h13
    have h15 : ENNReal.ofReal (2 * c_half) = 2 * ENNReal.ofReal c_half := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    rw [h15] at h14
    exact h14

  have h2c_lt_top : 2 * ENNReal.ofReal c_half < ⊤ :=
    ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top

  let d : ENNReal := ENNReal.ofReal cutsBallConstant

  have h_2d_le : 2 * d ≤ 2 * ENNReal.ofReal c_half - 1 := by
    have h_main : 2 * cutsBallConstant ≤ c_sum - 1 := by
      dsimp only [cutsBallConstant]
      linarith [hc_sum_lower]
    have h_sub : ENNReal.ofReal c_sum - 1 = ENNReal.ofReal (c_sum - 1) := by
      have h3 : ENNReal.ofReal (c_sum - 1) =
          ENNReal.ofReal c_sum - ENNReal.ofReal (1 : ℝ) :=
        ENNReal.ofReal_sub c_sum (q := 1) (by linarith)
      have h4 : ENNReal.ofReal (1 : ℝ) = (1 : ENNReal) := by simp
      rw [h4] at h3
      exact h3.symm
    have h_2c_half_sub : 2 * ENNReal.ofReal c_half - 1 = ENNReal.ofReal c_sum - 1 := by
      have h_eq : 2 * ENNReal.ofReal c_half = ENNReal.ofReal c_sum := by
        have h : ENNReal.ofReal (2 * c_half) = 2 * ENNReal.ofReal c_half := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          norm_num
        rw [← h, h2chalf]
      rw [h_eq]
    rw [h_2c_half_sub, h_sub]
    have h2d : 2 * d = ENNReal.ofReal (2 * cutsBallConstant) := by
      simp only [d]
      have h5 : ENNReal.ofReal (2 * cutsBallConstant) =
          (2 : ENNReal) * ENNReal.ofReal cutsBallConstant := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
      exact h5.symm
    rw [h2d]
    exact ENNReal.ofReal_le_ofReal h_main

  have h_eq_c : 2 * ENNReal.ofReal c_half = ENNReal.ofReal c_sum := by
    have h : ENNReal.ofReal (2 * c_half) = 2 * ENNReal.ofReal c_half := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    rw [← h, h2chalf]
  have h9' : 2 * ENNReal.ofReal c_half * μ S ≤ μ S + 2 * μ Z := by
    rw [h_eq_c]
    exact h9
  have h_final : d * μ S ≤ μ Z :=
    bisecting_arithmetic_main (ENNReal.ofReal c_half) d (μ S) (μ Z)
      hSfin.ne h_one_le h2c_lt_top h9' h_2d_le

  simpa [Z, d] using h_final

end CuttingBall

section CutsPullback

/-- The `PolynomialCutsAtLeast` condition is preserved under affine pullback
from a scaled ellipsoid to the unit ball. -/
lemma cutsAtLeast_pullback (p : MvPolynomial (Fin 3) ℝ) (z : Point 3) (η : ℝ) (hη : 0 < η)
    (A : Point 3 ≃ₗ[ℝ] Point 3) (τ : ℝ≥0∞)
    (hCut : PolynomialCutsAtLeast p (scaledEllipsoid A η z) τ) :
    PolynomialCutsAtLeast (pullbackPolynomial p z η A) (unitBall 3) τ := by
  let q := pullbackPolynomial p z η A
  let g : Point 3 → Point 3 := fun y => η • A y
  let f : Point 3 → Point 3 := fun y => z + g y
  let g' : Point 3 ≃L[ℝ] Point 3 :=
    { toFun := g
      invFun := fun x => η⁻¹ • A.symm x
      left_inv := by intro x; simp [g, hη.ne']
      right_inv := by intro x; simp [g, hη.ne']
      map_add' := by intro x y; simp [g]
      map_smul' := by
        intro c x
        dsimp only [g]
        rw [map_smul]
        exact smul_comm η c (A x)
      continuous_toFun := by
        have hA_cont : Continuous A := A.toLinearMap.continuous_of_finiteDimensional
        exact hA_cont.const_smul _
      continuous_invFun := by
        have hA_symm_cont : Continuous A.symm := A.symm.toLinearMap.continuous_of_finiteDimensional
        exact hA_symm_cont.const_smul _ }
  let detFactor := ENNReal.ofReal (η ^ 3 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|)
  have hdet_A_ne_zero : LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3) ≠ 0 := by
    have h : IsUnit (LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)) :=
      LinearEquiv.isUnit_det' A
    exact h.ne_zero
  have hdet_abs_pos : 0 < |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| := abs_pos.mpr hdet_A_ne_zero
  have hdet_pos : 0 < detFactor := by
    apply ENNReal.ofReal_pos.mpr
    exact mul_pos (pow_pos hη 3) hdet_abs_pos
  have hdet_finite : detFactor ≠ ⊤ := ENNReal.ofReal_lt_top.ne
  let S_neg := unitBall 3 ∩ {y | polynomialValue q y < 0}
  let S_pos := unitBall 3 ∩ {y | 0 < polynomialValue q y}
  have h_eval : ∀ y, polynomialValue q y = polynomialValue p (f y) := by
    intro y
    exact pullbackPolynomial_eval p z η A y
  have h_scaled_mem : ∀ (y : Point 3), y ∈ unitBall 3 → f y ∈ scaledEllipsoid A η z := by
    intro y hy
    have h_ball : ‖y‖ ≤ 1 := by simpa [unitBall, Metric.mem_closedBall] using hy
    let v := η • y
    have hv1 : ‖v‖ ≤ η := by
      rw [show v = η • y from rfl, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
      calc η * ‖y‖ ≤ η * 1 := by gcongr
        _ = η := by ring
    have hv2 : v ∈ Metric.closedBall (0 : Point 3) η := by
      simpa [Metric.mem_closedBall] using hv1
    have h3 : A v = g y := by
      simp [v, g, map_smul]
    have h4 : g y ∈ A '' Metric.closedBall (0 : Point 3) η := ⟨v, hv2, h3⟩
    have h5 : f y ∈ scaledEllipsoid A η z := by
      have h6 : f y = z +ᵥ g y := by simp [f]
      rw [h6]
      exact ⟨g y, h4, rfl⟩
    exact h5
  have h_scaled_inv : ∀ (x : Point 3), x ∈ scaledEllipsoid A η z →
      ∃ (y : Point 3), y ∈ unitBall 3 ∧ f y = x := by
    intro x hx
    simp only [scaledEllipsoid, Set.mem_vadd_set] at hx
    rcases hx with ⟨w, hw, h_eq1⟩
    rcases hw with ⟨v, hv, h_eq2⟩
    have h_ball : ‖v‖ ≤ η := by simpa [Metric.mem_closedBall] using hv
    let y := η⁻¹ • v
    have h_inv_pos : 0 < η⁻¹ := by positivity
    have hy1 : ‖y‖ ≤ 1 := by
      rw [show y = η⁻¹ • v from rfl, norm_smul, Real.norm_eq_abs, abs_of_pos h_inv_pos]
      calc η⁻¹ * ‖v‖ ≤ η⁻¹ * η := by gcongr
        _ = 1 := by field_simp [hη.ne']
    have hy2 : y ∈ unitBall 3 := by simpa [unitBall, Metric.mem_closedBall] using hy1
    have h2 : g y = A v := by
      have h : g y = η • A (η⁻¹ • v) := by simp [g, y]
      rw [h]
      have h' : A (η⁻¹ • v) = η⁻¹ • A v := by rw [map_smul]
      rw [h']
      have h'' : η • (η⁻¹ • A v) = A v := by
        simp [smul_smul, hη.ne']
      exact h''
    have hfy : f y = x := by
      have h1 : f y = z + g y := by simp [f]
      rw [h1, h2]
      have h4 : z + A v = z +ᵥ A v := by rfl
      rw [h4, h_eq2, h_eq1]
    exact ⟨y, hy2, hfy⟩
  have hcont_q : Continuous (fun y => polynomialValue q y) := by
    have h1 : Continuous (fun y : Point 3 => (fun i : Fin 3 => y i)) :=
      PiLp.continuous_ofLp 2 fun x => ℝ
    have h2 : Continuous (fun x : Fin 3 → ℝ => MvPolynomial.eval x q) := MvPolynomial.continuous_eval q
    exact h2.comp h1
  have h_ball_closed : IsClosed (unitBall 3) := Metric.isClosed_closedBall
  have hS_neg_meas : MeasurableSet S_neg :=
    h_ball_closed.measurableSet.inter (measurableSet_lt hcont_q.measurable measurable_const)
  have hS_pos_meas : MeasurableSet S_pos :=
    h_ball_closed.measurableSet.inter (measurableSet_lt measurable_const hcont_q.measurable)
  have h_image_preimage : ∀ (s : Set (Point 3)), g '' s = g'.symm ⁻¹' s := by
    intro s
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h_eq1 : g' x = g x := by rfl
      have h : g'.symm (g x) = x := by
        rw [← h_eq1]
        exact g'.left_inv x
      rw [h]
      exact hx
    · intro hy
      refine ⟨g'.symm y, hy, ?_⟩
      have h_eq : g (g'.symm y) = g' (g'.symm y) := by rfl
      rw [h_eq]
      exact g'.right_inv y
  have hgS_neg_meas : MeasurableSet (g '' S_neg) := by
    rw [h_image_preimage S_neg]
    exact hS_neg_meas.preimage g'.symm.continuous.measurable
  have hgS_pos_meas : MeasurableSet (g '' S_pos) := by
    rw [h_image_preimage S_pos]
    exact hS_pos_meas.preimage g'.symm.continuous.measurable
  have h_image_neg : f '' S_neg = scaledEllipsoid A η z ∩ {x | polynomialValue p x < 0} := by
    ext x
    simp only [S_neg, Set.mem_image, Set.mem_inter_iff]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have hfy : f y ∈ scaledEllipsoid A η z := h_scaled_mem y hy1
      have hsign : polynomialValue p (f y) < 0 := by
        rw [← h_eval y]
        exact hy2
      exact ⟨hfy, hsign⟩
    · rintro ⟨h1, h2⟩
      rcases h_scaled_inv x h1 with ⟨y, hy1, rfl⟩
      have h4 : polynomialValue q y < 0 := by
        rw [h_eval y]
        exact h2
      exact ⟨y, ⟨hy1, h4⟩, rfl⟩
  have h_image_pos : f '' S_pos = scaledEllipsoid A η z ∩ {x | 0 < polynomialValue p x} := by
    ext x
    simp only [S_pos, Set.mem_image, Set.mem_inter_iff]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have hfy : f y ∈ scaledEllipsoid A η z := h_scaled_mem y hy1
      have hsign : 0 < polynomialValue p (f y) := by
        rw [← h_eval y]
        exact hy2
      exact ⟨hfy, hsign⟩
    · rintro ⟨h1, h2⟩
      rcases h_scaled_inv x h1 with ⟨y, hy1, rfl⟩
      have h4 : 0 < polynomialValue q y := by
        rw [h_eval y]
        exact h2
      exact ⟨y, ⟨hy1, h4⟩, rfl⟩
  have h_translate : ∀ (s : Set (Point 3)), MeasurableSet s → volume ((fun x => z + x) '' s) = volume s := by
    intro s hs
    let t : Point 3 → Point 3 := fun x => z + x
    let t_inv : Point 3 → Point 3 := fun x => -z + x
    have hmp : MeasurePreserving t_inv := measurePreserving_add_left volume (-z)
    have h2 : t '' s = t_inv ⁻¹' s := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have h4 : t_inv (t x) = x := by
          simp [t, t_inv]
        rw [h4]
        exact hx
      · intro hy
        have h3 : t (t_inv y) = y := by
          simp [t, t_inv]
        exact ⟨t_inv y, hy, h3⟩
    rw [h2]
    exact hmp.measure_preimage hs.nullMeasurableSet
  have h_f_image : ∀ (s : Set (Point 3)), f '' s = (fun x => z + x) '' (g '' s) := by
    intro s
    ext x
    simp only [f, Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  have hdet_g : LinearMap.det (g' : Point 3 →ₗ[ℝ] Point 3) =
      η ^ 3 * LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3) := by
    let smulMap2 : Point 3 ≃L[ℝ] Point 3 := ContinuousLinearEquiv.smulLeft (Units.mk0 η hη.ne')
    have hsmul : ∀ (x : Point 3), (smulMap2 : Point 3 → Point 3) x = η • x := by
      intro x
      change (Units.mk0 η hη.ne' : ℝ) • x = η • x
      rfl
    have hdet_smul2 : LinearMap.det (smulMap2 : Point 3 →ₗ[ℝ] Point 3) = η ^ 3 := by
      have h : (smulMap2 : Point 3 →ₗ[ℝ] Point 3) = η • LinearMap.id := by
        apply LinearMap.ext; intro x
        exact hsmul x
      rw [h, LinearMap.det_smul, LinearMap.det_id]
      simp
    have h_comp : (g' : Point 3 →ₗ[ℝ] Point 3) = (smulMap2 : Point 3 →ₗ[ℝ] Point 3).comp (A : Point 3 →ₗ[ℝ] Point 3) := by
      apply LinearMap.ext
      intro x
      have h1 : (g' : Point 3 → Point 3) x = η • A x := by
        change g x = η • A x; simp [g]
      have h2 : ((smulMap2 : Point 3 →ₗ[ℝ] Point 3).comp (A : Point 3 →ₗ[ℝ] Point 3)) x = η • A x := by
        simp [hsmul]
      exact h1.trans h2.symm
    rw [h_comp, LinearMap.det_comp, hdet_smul2]
  have h_abs : |η ^ 3 * LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| =
      η ^ 3 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| := by
    rw [abs_mul, abs_pow, abs_of_pos hη]
  have hvol_g_neg : volume (g '' S_neg) = detFactor * volume S_neg := by
    have h : volume (g '' S_neg) =
        ENNReal.ofReal |LinearMap.det (g' : Point 3 →ₗ[ℝ] Point 3)| * volume S_neg :=
      MeasureTheory.Measure.addHaar_image_continuousLinearEquiv volume g' S_neg
    rw [h, hdet_g, h_abs]
  have hvol_g_pos : volume (g '' S_pos) = detFactor * volume S_pos := by
    have h : volume (g '' S_pos) =
        ENNReal.ofReal |LinearMap.det (g' : Point 3 →ₗ[ℝ] Point 3)| * volume S_pos :=
      MeasureTheory.Measure.addHaar_image_continuousLinearEquiv volume g' S_pos
    rw [h, hdet_g, h_abs]
  have hvol_neg : volume (f '' S_neg) = detFactor * volume S_neg := by
    rw [h_f_image S_neg, h_translate (g '' S_neg) hgS_neg_meas, hvol_g_neg]
  have hvol_pos : volume (f '' S_pos) = detFactor * volume S_pos := by
    rw [h_f_image S_pos, h_translate (g '' S_pos) hgS_pos_meas, hvol_g_pos]
  have h_ellipsoid_vol : volume (scaledEllipsoid A η z) = detFactor * volume (unitBall 3) :=
    volume_affine_ball A η hη z
  have h1 : volume (scaledEllipsoid A η z ∩ {x | polynomialValue p x < 0}) = detFactor * volume S_neg := by
    rw [← h_image_neg, hvol_neg]
  have h2 : volume (scaledEllipsoid A η z ∩ {x | 0 < polynomialValue p x}) = detFactor * volume S_pos := by
    rw [← h_image_pos, hvol_pos]
  have hCut1 : τ * volume (scaledEllipsoid A η z) ≤
      volume (scaledEllipsoid A η z ∩ {x | polynomialValue p x < 0}) := hCut.1
  have hCut2 : τ * volume (scaledEllipsoid A η z) ≤
      volume (scaledEllipsoid A η z ∩ {x | 0 < polynomialValue p x}) := hCut.2
  rw [h_ellipsoid_vol, h1] at hCut1
  rw [h_ellipsoid_vol, h2] at hCut2
  have h_mul_assoc1 : τ * (detFactor * volume (unitBall 3)) =
      detFactor * (τ * volume (unitBall 3)) := by
    calc τ * (detFactor * volume (unitBall 3))
      = (τ * detFactor) * volume (unitBall 3) := by rw [mul_assoc]
    _ = (detFactor * τ) * volume (unitBall 3) := by rw [mul_comm τ detFactor]
    _ = detFactor * (τ * volume (unitBall 3)) := by rw [mul_assoc]
  rw [h_mul_assoc1] at hCut1
  rw [h_mul_assoc1] at hCut2
  have h_cancel1 : τ * volume (unitBall 3) ≤ volume S_neg := by
    have h : detFactor * (τ * volume (unitBall 3)) ≤ detFactor * volume S_neg := hCut1
    have hdiv : detFactor⁻¹ * (detFactor * (τ * volume (unitBall 3))) ≤
        detFactor⁻¹ * (detFactor * volume S_neg) := by gcongr
    have hc1 : detFactor⁻¹ * (detFactor * (τ * volume (unitBall 3))) =
        τ * volume (unitBall 3) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hdet_pos.ne' hdet_finite, one_mul]
    have hc2 : detFactor⁻¹ * (detFactor * volume S_neg) = volume S_neg := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hdet_pos.ne' hdet_finite, one_mul]
    rw [hc1, hc2] at hdiv
    exact hdiv
  have h_cancel2 : τ * volume (unitBall 3) ≤ volume S_pos := by
    have h : detFactor * (τ * volume (unitBall 3)) ≤ detFactor * volume S_pos := hCut2
    have hdiv : detFactor⁻¹ * (detFactor * (τ * volume (unitBall 3))) ≤
        detFactor⁻¹ * (detFactor * volume S_pos) := by gcongr
    have hc1 : detFactor⁻¹ * (detFactor * (τ * volume (unitBall 3))) =
        τ * volume (unitBall 3) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hdet_pos.ne' hdet_finite, one_mul]
    have hc2 : detFactor⁻¹ * (detFactor * volume S_pos) = volume S_pos := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hdet_pos.ne' hdet_finite, one_mul]
    rw [hc1, hc2] at hdiv
    exact hdiv
  exact ⟨h_cancel1, h_cancel2⟩

end CutsPullback

section DisjointPieces

/-- Zero-set pieces inside pairwise-disjoint ellipsoids are pairwise disjoint. -/
lemma zeroSetPieces_disjoint {ι : Type*} (p : MvPolynomial (Fin 3) ℝ)
    (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (z : ι → Point 3)
    (h_disj : Pairwise (fun i j =>
      Disjoint (scaledEllipsoid A η (z i)) (scaledEllipsoid A η (z j)))) :
    Pairwise (fun i j =>
      Disjoint (polynomialZeroSet p ∩ scaledEllipsoid A η (z i))
        (polynomialZeroSet p ∩ scaledEllipsoid A η (z j))) := by
  intro i j hne
  have h : Disjoint (scaledEllipsoid A η (z i)) (scaledEllipsoid A η (z j)) :=
    h_disj hne
  have h1 : (polynomialZeroSet p ∩ scaledEllipsoid A η (z i)) ⊆
      scaledEllipsoid A η (z i) := fun x hx => hx.2
  have h2 : (polynomialZeroSet p ∩ scaledEllipsoid A η (z j)) ⊆
      scaledEllipsoid A η (z j) := fun x hx => hx.2
  exact h.mono h1 h2

end DisjointPieces

end Kakeya.CV
