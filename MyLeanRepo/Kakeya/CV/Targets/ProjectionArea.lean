import MyLeanRepo.Kakeya.CV.Isoperimetric.Statements
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Convex.Measure

/-!
# Projection area computation

Computes the area of the intersection of two ellipses:
`ellipseSet = {(y,z) | 2y² + z² ≤ 1 ∧ y² + 2z² ≤ 1}`

The area is `2 * √2 * arcsin(1/√3)`.
-/

noncomputable section

open Real Set MeasureTheory Metric intervalIntegral

open scoped Real Interval ENNReal

namespace Geometry.ProjectionArea

/-! ### Helper: integral of sqrt(1 - x²) -/

/-- Antiderivative of `√(1 - x²)`: `(arcsin x + x * √(1 - x²)) / 2`. -/
noncomputable def antiderivSqrt (x : ℝ) : ℝ :=
  (Real.arcsin x + x * Real.sqrt (1 - x ^ 2)) / 2

lemma hasDerivAt_antiderivSqrt {x : ℝ} (hx1 : -1 < x) (hx2 : x < 1) :
    HasDerivAt antiderivSqrt (Real.sqrt (1 - x ^ 2)) x := by
  have h_pos : 0 < 1 - x ^ 2 := by nlinarith
  have h_ne0 : (1 - x ^ 2) ≠ 0 := ne_of_gt h_pos
  have h_ne1 : x ≠ -1 := by linarith
  have h_ne2 : x ≠ 1 := by linarith
  have h_arcsin : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
    Real.hasDerivAt_arcsin h_ne1 h_ne2
  have h_id : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have h_pow2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    have h : HasDerivAt (fun y : ℝ => y * y) (1 * x + x * 1) x := h_id.mul h_id
    have h_eq : (1 * x + x * 1) = 2 * x := by ring
    rw [h_eq] at h
    simpa [pow_two] using h
  have h_neg_pow2 : HasDerivAt (fun y : ℝ => -y ^ 2) (-(2 * x)) x := h_pow2.neg
  have h_inner : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := h_neg_pow2.const_add 1
  have h_sqrt_deriv0 : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      ((-(2 * x)) / (2 * Real.sqrt (1 - x ^ 2))) x :=
    HasDerivAt.sqrt h_inner h_ne0
  have h_sqrt_eq : (-(2 * x)) / (2 * Real.sqrt (1 - x ^ 2)) = (-x) / Real.sqrt (1 - x ^ 2) := by ring
  have h_sqrt_deriv : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      ((-x) / Real.sqrt (1 - x ^ 2)) x := by
    rw [h_sqrt_eq] at h_sqrt_deriv0
    exact h_sqrt_deriv0
  have h_mul : HasDerivAt (fun y : ℝ => y * Real.sqrt (1 - y ^ 2))
      (1 * Real.sqrt (1 - x ^ 2) + x * ((-x) / Real.sqrt (1 - x ^ 2))) x :=
    h_id.mul h_sqrt_deriv
  have h_mul_eq : 1 * Real.sqrt (1 - x ^ 2) + x * ((-x) / Real.sqrt (1 - x ^ 2)) =
      Real.sqrt (1 - x ^ 2) - x ^ 2 / Real.sqrt (1 - x ^ 2) := by ring
  have h_mul' : HasDerivAt (fun y : ℝ => y * Real.sqrt (1 - y ^ 2))
      (Real.sqrt (1 - x ^ 2) - x ^ 2 / Real.sqrt (1 - x ^ 2)) x := by
    rw [h_mul_eq] at h_mul
    exact h_mul
  have h_add : HasDerivAt (fun y : ℝ => Real.arcsin y + y * Real.sqrt (1 - y ^ 2))
      (1 / Real.sqrt (1 - x ^ 2) + (Real.sqrt (1 - x ^ 2) - x ^ 2 / Real.sqrt (1 - x ^ 2))) x :=
    h_arcsin.add h_mul'
  have h_final : 1 / Real.sqrt (1 - x ^ 2) + (Real.sqrt (1 - x ^ 2) - x ^ 2 / Real.sqrt (1 - x ^ 2)) =
      2 * Real.sqrt (1 - x ^ 2) := by
    have h_spos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr h_pos
    field_simp [h_spos.ne']
    <;> nlinarith [Real.sq_sqrt (show 0 ≤ 1 - x ^ 2 by linarith)]
  rw [h_final] at h_add
  have h_div : HasDerivAt (fun y : ℝ => (Real.arcsin y + y * Real.sqrt (1 - y ^ 2)) / 2)
      ((2 * Real.sqrt (1 - x ^ 2)) / 2) x :=
    h_add.div_const 2
  have h2 : (2 * Real.sqrt (1 - x ^ 2)) / 2 = Real.sqrt (1 - x ^ 2) := by ring
  rw [h2] at h_div
  have h_eq_fun : (fun y : ℝ => (Real.arcsin y + y * Real.sqrt (1 - y ^ 2)) / 2) = antiderivSqrt := by
    funext y
    simp [antiderivSqrt]
  rw [h_eq_fun] at h_div
  exact h_div

lemma antiderivSqrt_continuous : Continuous antiderivSqrt := by
  have h1 : Continuous Real.arcsin := by fun_prop
  have h2 : Continuous (fun y : ℝ => y * Real.sqrt (1 - y ^ 2)) := by fun_prop
  have h3 : Continuous (fun y : ℝ => Real.arcsin y + y * Real.sqrt (1 - y ^ 2)) := h1.add h2
  exact h3.div_const 2

lemma integral_sqrt_one_sub_sq_interval {a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    ∫ t in a..b, Real.sqrt (1 - t ^ 2) = antiderivSqrt b - antiderivSqrt a := by
  have h_cont : ContinuousOn antiderivSqrt (Set.Icc a b) :=
    antiderivSqrt_continuous.continuousOn
  have h_deriv : ∀ t ∈ Set.Ioo a b, HasDerivAt antiderivSqrt (Real.sqrt (1 - t ^ 2)) t := by
    intro t ht
    have h_t1 : -1 < t := by linarith [ha, ht.1]
    have h_t2 : t < 1 := by linarith [hb, ht.2]
    exact hasDerivAt_antiderivSqrt h_t1 h_t2
  have h_int : IntervalIntegrable (fun t : ℝ => Real.sqrt (1 - t ^ 2)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  exact integral_eq_sub_of_hasDerivAt_of_le hab h_cont h_deriv h_int

lemma integral_sqrt_one_sub_sq_from_zero {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    ∫ t in (0 : ℝ)..x, Real.sqrt (1 - t ^ 2) = antiderivSqrt x := by
  by_cases hx0 : x = 0
  · rw [hx0]
    simp [antiderivSqrt]
  · have hpos : 0 < x := by
      exact lt_of_le_of_ne hx (Ne.symm hx0)
    have h : ∫ t in (0 : ℝ)..x, Real.sqrt (1 - t ^ 2) = antiderivSqrt x - antiderivSqrt 0 :=
      integral_sqrt_one_sub_sq_interval (a := 0) (b := x) (by linarith) hx' (by linarith)
    have h0 : antiderivSqrt 0 = 0 := by simp [antiderivSqrt]
    have h' : antiderivSqrt x - antiderivSqrt 0 = antiderivSqrt x := by
      rw [h0] <;> ring
    exact h.trans h'

/-! ### Area computation -/

/-- The projected set viewed as a subset of `ℝ × ℝ`. -/
def ellipseSet : Set (ℝ × ℝ) :=
  {p | 2 * p.1 ^ 2 + p.2 ^ 2 ≤ 1 ∧ p.1 ^ 2 + 2 * p.2 ^ 2 ≤ 1}

/-- Open projected set. -/
def ellipseSetOpen : Set (ℝ × ℝ) :=
  {p | 2 * p.1 ^ 2 + p.2 ^ 2 < 1 ∧ p.1 ^ 2 + 2 * p.2 ^ 2 < 1}

/-- Upper bound of the vertical slice. -/
def upperBound (y : ℝ) : ℝ :=
  min (Real.sqrt (1 - 2 * y ^ 2)) (Real.sqrt ((1 - y ^ 2) / 2))

/-- Lower bound of the vertical slice. -/
def lowerBound (y : ℝ) : ℝ := -upperBound y

/-- y-range of the ellipse set. -/
def yRange : Set ℝ := Icc (-(1 / Real.sqrt 2)) (1 / Real.sqrt 2)

lemma yRange_measurable : MeasurableSet yRange := measurableSet_Icc

lemma upperBound_continuous : Continuous upperBound := by
  have h1 : Continuous (fun y : ℝ => Real.sqrt (1 - 2 * y ^ 2)) := by fun_prop
  have h2 : Continuous (fun y : ℝ => Real.sqrt ((1 - y ^ 2) / 2)) := by fun_prop
  exact h1.min h2

lemma upperBound_integrable : IntegrableOn upperBound yRange :=
  upperBound_continuous.continuousOn.integrableOn_compact isCompact_Icc

lemma lowerBound_integrable : IntegrableOn lowerBound yRange :=
  upperBound_integrable.neg

/-- Helper: for `a ≥ 0`, `z² < a ↔ |z| < Real.sqrt a`. -/
lemma sq_lt_iff (z a : ℝ) (ha : 0 ≤ a) : z ^ 2 < a ↔ |z| < Real.sqrt a := by
  have hsq : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
  constructor
  · intro h
    have hpos1 : 0 ≤ |z| := by positivity
    have hpos2 : 0 ≤ Real.sqrt a := by positivity
    have h1 : |z| ^ 2 = z ^ 2 := by simp [pow_two]
    have h2 : |z| ^ 2 < (Real.sqrt a) ^ 2 := by
      rw [h1, hsq] <;> exact h
    have h3 : |z| < Real.sqrt a := by
      by_contra h4
      have h5 : Real.sqrt a ≤ |z| := by linarith
      have h6 : (Real.sqrt a) ^ 2 ≤ |z| ^ 2 := by gcongr
      linarith
    exact h3
  · intro h
    have hpos1 : 0 ≤ |z| := by positivity
    have hpos2 : 0 ≤ Real.sqrt a := by positivity
    have h2 : |z| ^ 2 < (Real.sqrt a) ^ 2 := by gcongr
    have h1 : z ^ 2 = |z| ^ 2 := by simp [pow_two]
    rw [h1]
    rw [hsq] at h2
    exact h2

/-- The slice of `ellipseSetOpen` at coordinate `y`. -/
lemma slice_eq (y : ℝ) :
    {z : ℝ | (y, z) ∈ ellipseSetOpen} =
    if y ^ 2 < 1 / 2 then Ioo (-(upperBound y)) (upperBound y) else (∅ : Set ℝ) := by
  by_cases h : y ^ 2 < 1 / 2
  · rw [if_pos h]
    ext z
    simp only [ellipseSetOpen, mem_setOf_eq, mem_Ioo]
    have h_a1 : 0 ≤ 1 - 2 * y ^ 2 := by nlinarith
    have h_a2 : 0 ≤ (1 - y ^ 2) / 2 := by nlinarith
    have h1 : 2 * y ^ 2 + z ^ 2 < 1 ↔ z ^ 2 < 1 - 2 * y ^ 2 := by
      constructor <;> intro h <;> linarith
    have h2 : y ^ 2 + 2 * z ^ 2 < 1 ↔ z ^ 2 < (1 - y ^ 2) / 2 := by
      constructor <;> intro h <;> linarith
    have h3 : z ^ 2 < 1 - 2 * y ^ 2 ↔ |z| < Real.sqrt (1 - 2 * y ^ 2) := sq_lt_iff z (1 - 2 * y ^ 2) h_a1
    have h4 : z ^ 2 < (1 - y ^ 2) / 2 ↔ |z| < Real.sqrt ((1 - y ^ 2) / 2) := sq_lt_iff z ((1 - y ^ 2) / 2) h_a2
    have h_def : upperBound y = min (Real.sqrt (1 - 2 * y ^ 2)) (Real.sqrt ((1 - y ^ 2) / 2)) := by
      simp [upperBound]
    have h5 : (|z| < Real.sqrt (1 - 2 * y ^ 2) ∧ |z| < Real.sqrt ((1 - y ^ 2) / 2)) ↔
        |z| < upperBound y := by
      rw [h_def]
      simp [lt_min_iff]
      <;> tauto
    rw [h1, h2, h3, h4]
    rw [h5]
    rw [abs_lt]
    <;> ring
  · rw [if_neg h]
    ext z
    simp only [ellipseSetOpen, mem_setOf_eq, mem_empty_iff_false, iff_false]
    intro h_contra
    have h6 : 2 * y ^ 2 + z ^ 2 < 1 := h_contra.1
    have h7 : z ^ 2 ≥ 0 := by positivity
    nlinarith

lemma ellipseSetOpen_measurable : MeasurableSet ellipseSetOpen := by
  have hf1 : Measurable fun (p : ℝ × ℝ) => 2 * p.1 ^ 2 + p.2 ^ 2 := by fun_prop
  have hf2 : Measurable fun (p : ℝ × ℝ) => p.1 ^ 2 + 2 * p.2 ^ 2 := by fun_prop
  have h1 : MeasurableSet {p : ℝ × ℝ | 2 * p.1 ^ 2 + p.2 ^ 2 < 1} :=
    measurableSet_lt hf1 measurable_const
  have h2 : MeasurableSet {p : ℝ × ℝ | p.1 ^ 2 + 2 * p.2 ^ 2 < 1} :=
    measurableSet_lt hf2 measurable_const
  exact h1.inter h2

lemma yRange_iff {y : ℝ} : y ∈ yRange ↔ y ^ 2 ≤ 1 / 2 := by
  have h_sqrt2_sq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    field_simp [show (Real.sqrt 2 : ℝ) ≠ 0 by positivity]
    <;> rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] <;> ring
  simp only [yRange, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : |y| ≤ 1 / Real.sqrt 2 := by
      rw [abs_le] <;> exact ⟨by linarith, by linarith⟩
    have h4 : |y| ^ 2 ≤ (1 / Real.sqrt 2) ^ 2 := by gcongr
    have h5 : |y| ^ 2 = y ^ 2 := by simp [pow_two]
    nlinarith
  · intro h
    have h3 : |y| ≤ 1 / Real.sqrt 2 := by
      have h4 : |y| ^ 2 ≤ (1 / Real.sqrt 2) ^ 2 := by
        have h5 : |y| ^ 2 = y ^ 2 := by simp [pow_two]
        rw [h5]
        nlinarith
      have h6 : 0 ≤ |y| := by positivity
      have h7 : 0 ≤ 1 / Real.sqrt 2 := by positivity
      nlinarith [sq_nonneg (|y| - (1 / Real.sqrt 2))]
    rw [abs_le] at h3
    exact ⟨by linarith, by linarith⟩

lemma upperBound_nonneg (y : ℝ) (h : y ∈ yRange) : 0 ≤ upperBound y := by
  have h1 : y ^ 2 ≤ 1 / 2 := yRange_iff.mp h
  have h2 : 0 ≤ 1 - 2 * y ^ 2 := by nlinarith
  have h3 : 0 ≤ (1 - y ^ 2) / 2 := by nlinarith
  have h4 : 0 ≤ Real.sqrt (1 - 2 * y ^ 2) := Real.sqrt_nonneg _
  have h5 : 0 ≤ Real.sqrt ((1 - y ^ 2) / 2) := Real.sqrt_nonneg _
  have h6 : 0 ≤ upperBound y := by
    rw [upperBound]
    exact le_min_iff.mpr ⟨h4, h5⟩
  exact h6

lemma upperBound_even (y : ℝ) : upperBound (-y) = upperBound y := by
  simp [upperBound, pow_two]
  <;> ring

lemma upperBound_eq_first {y : ℝ} (h : y ^ 2 ≤ 1 / 3) :
    upperBound y = Real.sqrt ((1 - y ^ 2) / 2) := by
  have h1 : (1 - y ^ 2) / 2 ≤ 1 - 2 * y ^ 2 := by nlinarith
  have h2 : 0 ≤ (1 - y ^ 2) / 2 := by nlinarith
  have h3 : 0 ≤ 1 - 2 * y ^ 2 := by nlinarith
  have h4 : Real.sqrt ((1 - y ^ 2) / 2) ≤ Real.sqrt (1 - 2 * y ^ 2) :=
    Real.sqrt_le_sqrt h1
  rw [upperBound, min_eq_right h4]

lemma upperBound_eq_second {y : ℝ} (h1 : 1 / 3 ≤ y ^ 2) (h2 : y ^ 2 ≤ 1 / 2) :
    upperBound y = Real.sqrt (1 - 2 * y ^ 2) := by
  have h3 : 1 - 2 * y ^ 2 ≤ (1 - y ^ 2) / 2 := by nlinarith
  have h4 : 0 ≤ 1 - 2 * y ^ 2 := by nlinarith
  have h5 : Real.sqrt (1 - 2 * y ^ 2) ≤ Real.sqrt ((1 - y ^ 2) / 2) :=
    Real.sqrt_le_sqrt h3
  rw [upperBound, min_eq_left h5]

lemma upperBound_at_boundary : upperBound (1 / Real.sqrt 2) = 0 := by
  have h1 : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    field_simp [show (Real.sqrt 2 : ℝ) ≠ 0 by positivity]
    <;> rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] <;> ring
  have h2 : 1 - 2 * (1 / Real.sqrt 2) ^ 2 = 0 := by rw [h1] <;> ring
  have h3 : Real.sqrt (1 - 2 * (1 / Real.sqrt 2) ^ 2) = 0 := by rw [h2] <;> simp
  have h4 : 0 ≤ Real.sqrt ((1 - (1 / Real.sqrt 2) ^ 2) / 2) := Real.sqrt_nonneg _
  have h5 : upperBound (1 / Real.sqrt 2) = min (Real.sqrt (1 - 2 * (1 / Real.sqrt 2) ^ 2)) (Real.sqrt ((1 - (1 / Real.sqrt 2) ^ 2) / 2)) := by
    simp [upperBound]
  rw [h5, h3]
  exact min_eq_left h4

lemma ellipseSetOpen_eq_regionBetween :
    ellipseSetOpen = regionBetween lowerBound upperBound yRange := by
  ext ⟨y, z⟩
  simp only [ellipseSetOpen, regionBetween, mem_setOf_eq, mem_Ioo, lowerBound]
  constructor
  · rintro ⟨h1, h2⟩
    have hy2 : y ^ 2 < 1 / 2 := by nlinarith
    have hy : y ∈ yRange := yRange_iff.mpr (by linarith)
    have h_a1 : 0 ≤ 1 - 2 * y ^ 2 := by nlinarith
    have h_a2 : 0 ≤ (1 - y ^ 2) / 2 := by nlinarith
    have h3 : z ^ 2 < 1 - 2 * y ^ 2 := by nlinarith
    have h4 : z ^ 2 < (1 - y ^ 2) / 2 := by nlinarith
    have h5 : |z| < Real.sqrt (1 - 2 * y ^ 2) := (sq_lt_iff z (1 - 2 * y ^ 2) h_a1).mp h3
    have h6 : |z| < Real.sqrt ((1 - y ^ 2) / 2) := (sq_lt_iff z ((1 - y ^ 2) / 2) h_a2).mp h4
    have h7 : |z| < upperBound y := by
      have h_def : upperBound y = min (Real.sqrt (1 - 2 * y ^ 2)) (Real.sqrt ((1 - y ^ 2) / 2)) := by
        simp [upperBound]
      rw [h_def]
      exact lt_min h5 h6
    have h8 : -upperBound y < z ∧ z < upperBound y := abs_lt.mp h7
    exact ⟨hy, h8.1, h8.2⟩
  · rintro ⟨hy, h8, h9⟩
    have h10 : |z| < upperBound y := by
      rw [abs_lt] <;> exact ⟨by linarith, by linarith⟩
    have h11 : upperBound y ≤ Real.sqrt (1 - 2 * y ^ 2) := by
      have h_def : upperBound y = min (Real.sqrt (1 - 2 * y ^ 2)) (Real.sqrt ((1 - y ^ 2) / 2)) := by
        simp [upperBound]
      rw [h_def]
      <;> simp
    have h12 : upperBound y ≤ Real.sqrt ((1 - y ^ 2) / 2) := by
      have h_def : upperBound y = min (Real.sqrt (1 - 2 * y ^ 2)) (Real.sqrt ((1 - y ^ 2) / 2)) := by
        simp [upperBound]
      rw [h_def]
      <;> simp
    have h13 : |z| < Real.sqrt (1 - 2 * y ^ 2) := lt_of_lt_of_le h10 h11
    have h14 : |z| < Real.sqrt ((1 - y ^ 2) / 2) := lt_of_lt_of_le h10 h12
    have h_y2_lt : y ^ 2 < 1 / 2 := by
      by_contra h
      have h' : y ^ 2 ≥ 1 / 2 := by linarith
      have h_y2_eq : y ^ 2 = 1 / 2 := by linarith [yRange_iff.mp hy]
      have h1 : 1 - 2 * y ^ 2 = 0 := by linarith
      have h2 : Real.sqrt (1 - 2 * y ^ 2) = 0 := by rw [h1] <;> simp
      have h_ub : upperBound y = 0 := by
        have h3 : upperBound y = min (Real.sqrt (1 - 2 * y ^ 2)) (Real.sqrt ((1 - y ^ 2) / 2)) := by simp [upperBound]
        have h4 : 0 ≤ Real.sqrt ((1 - y ^ 2) / 2) := Real.sqrt_nonneg _
        rw [h3, h2]
        exact min_eq_left h4
      rw [h_ub] at h10
      exact not_lt.mpr (abs_nonneg z) h10
    have h_a1 : 0 ≤ 1 - 2 * y ^ 2 := by nlinarith
    have h_a2 : 0 ≤ (1 - y ^ 2) / 2 := by nlinarith
    have h15 : z ^ 2 < 1 - 2 * y ^ 2 := (sq_lt_iff z (1 - 2 * y ^ 2) h_a1).mpr h13
    have h16 : z ^ 2 < (1 - y ^ 2) / 2 := (sq_lt_iff z ((1 - y ^ 2) / 2) h_a2).mpr h14
    exact ⟨by nlinarith, by nlinarith⟩

/-- Helper: `√((1-t²)/2) = (1/√2) * √(1-t²)`. -/
lemma sqrt_div_two (t : ℝ) :
    Real.sqrt ((1 - t ^ 2) / 2) = (1 / Real.sqrt 2) * Real.sqrt (1 - t ^ 2) := by
  by_cases h : 0 ≤ 1 - t ^ 2
  · rw [Real.sqrt_div (by linarith)] <;> ring
  · have h' : 1 - t ^ 2 < 0 := by linarith
    have h1 : Real.sqrt (1 - t ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    have h2 : (1 - t ^ 2) / 2 < 0 := by linarith
    have h3 : Real.sqrt ((1 - t ^ 2) / 2) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    rw [h1, h3] <;> ring

/-- First part of the integral: `0` to `1/√3`. -/
lemma integral_first_part :
    ∫ y in (0 : ℝ)..(1 / Real.sqrt 3), upperBound y =
    (1 / Real.sqrt 2) * antiderivSqrt (1 / Real.sqrt 3) := by
  have h_b1 : 0 ≤ 1 / Real.sqrt 3 := by positivity
  have h_b2 : 1 / Real.sqrt 3 ≤ 1 := by
    have h_sqrt3_ge1 : 1 ≤ Real.sqrt 3 := Real.le_sqrt_of_sq_le (by norm_num)
    have h_pos : 0 < Real.sqrt 3 := by positivity
    exact (div_le_one h_pos).mpr h_sqrt3_ge1
  have h_y2_le : ∀ y ∈ Set.uIcc (0 : ℝ) (1 / Real.sqrt 3), y ^ 2 ≤ 1 / 3 := by
    intro y hy
    have h0 : 0 ≤ 1 / Real.sqrt 3 := by positivity
    have h1 : Set.uIcc (0 : ℝ) (1 / Real.sqrt 3) = Set.Icc (0 : ℝ) (1 / Real.sqrt 3) := by
      rw [uIcc_of_le (by linarith)]
    rw [h1] at hy
    have h2 : 0 ≤ y := hy.1
    have h3 : y ≤ 1 / Real.sqrt 3 := hy.2
    have h4 : y ^ 2 ≤ (1 / Real.sqrt 3) ^ 2 := by gcongr
    have h5 : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
      field_simp [show (Real.sqrt 3 : ℝ) ≠ 0 by positivity]
      <;> rw [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] <;> ring
    nlinarith
  have h_eq : ∀ y ∈ Set.uIcc (0 : ℝ) (1 / Real.sqrt 3), upperBound y = Real.sqrt ((1 - y ^ 2) / 2) := by
    intro y hy
    exact upperBound_eq_first (h_y2_le y hy)
  rw [intervalIntegral.integral_congr h_eq]
  have h_int : ∫ y in (0 : ℝ)..(1 / Real.sqrt 3), Real.sqrt ((1 - y ^ 2) / 2) =
      (1 / Real.sqrt 2) * ∫ y in (0 : ℝ)..(1 / Real.sqrt 3), Real.sqrt (1 - y ^ 2) := by
    have h : ∫ y in (0 : ℝ)..(1 / Real.sqrt 3), Real.sqrt ((1 - y ^ 2) / 2) =
        ∫ y in (0 : ℝ)..(1 / Real.sqrt 3), (1 / Real.sqrt 2) * Real.sqrt (1 - y ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact sqrt_div_two x
    rw [h, intervalIntegral.integral_const_mul]
  rw [h_int, integral_sqrt_one_sub_sq_from_zero h_b1 h_b2] <;> ring

/-- Second part of the integral: `1/√3` to `1/√2`. -/
lemma integral_second_part :
    ∫ y in (1 / Real.sqrt 3)..(1 / Real.sqrt 2), upperBound y =
    (1 / Real.sqrt 2) * (antiderivSqrt 1 - antiderivSqrt (Real.sqrt (2 / 3))) := by
  have h_order : 1 / Real.sqrt 3 ≤ 1 / Real.sqrt 2 := by
    have h1 : Real.sqrt 2 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
    have h2 : 0 < Real.sqrt 2 := by positivity
    have h3 : 0 < Real.sqrt 3 := by positivity
    exact one_div_le_one_div_of_le h2 h1
  have h_y2 : ∀ y ∈ Set.uIcc (1 / Real.sqrt 3) (1 / Real.sqrt 2),
      1 / 3 ≤ y ^ 2 ∧ y ^ 2 ≤ 1 / 2 := by
    intro y hy
    have h1 : Set.uIcc (1 / Real.sqrt 3) (1 / Real.sqrt 2) = Set.Icc (1 / Real.sqrt 3) (1 / Real.sqrt 2) := by
      rw [uIcc_of_le h_order]
    rw [h1] at hy
    have h2 : 1 / Real.sqrt 3 ≤ y := hy.1
    have h3 : y ≤ 1 / Real.sqrt 2 := hy.2
    have h4_pos : 0 < 1 / Real.sqrt 3 := by positivity
    have h4 : 0 ≤ y := by linarith
    have h5 : (1 / Real.sqrt 3) ^ 2 ≤ y ^ 2 := by gcongr
    have h6 : y ^ 2 ≤ (1 / Real.sqrt 2) ^ 2 := by gcongr
    have h7 : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
      field_simp [show (Real.sqrt 3 : ℝ) ≠ 0 by positivity]
      <;> rw [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] <;> ring
    have h8 : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
      field_simp [show (Real.sqrt 2 : ℝ) ≠ 0 by positivity]
      <;> rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] <;> ring
    exact ⟨by nlinarith, by nlinarith⟩
  have h_eq : ∀ y ∈ Set.uIcc (1 / Real.sqrt 3) (1 / Real.sqrt 2),
      upperBound y = Real.sqrt (1 - 2 * y ^ 2) := by
    intro y hy
    have h9 := h_y2 y hy
    exact upperBound_eq_second h9.1 h9.2
  rw [intervalIntegral.integral_congr h_eq]
  have hc : Real.sqrt 2 ≠ 0 := by positivity
  have h_subst : ∫ y in (1 / Real.sqrt 3)..(1 / Real.sqrt 2), Real.sqrt (1 - 2 * y ^ 2) =
      (1 / Real.sqrt 2) * ∫ t in (Real.sqrt 2 * (1 / Real.sqrt 3))..(Real.sqrt 2 * (1 / Real.sqrt 2)), Real.sqrt (1 - t ^ 2) := by
    have h_eq2 : ∫ y in (1 / Real.sqrt 3)..(1 / Real.sqrt 2), Real.sqrt (1 - 2 * y ^ 2) =
        ∫ y in (1 / Real.sqrt 3)..(1 / Real.sqrt 2), Real.sqrt (1 - (Real.sqrt 2 * y) ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x _
      have hsq : (Real.sqrt 2 * x) ^ 2 = 2 * x ^ 2 := by
        calc
          (Real.sqrt 2 * x) ^ 2 = (Real.sqrt 2) ^ 2 * x ^ 2 := by ring
          _ = 2 * x ^ 2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] <;> ring
      simpa [hsq] using rfl
    rw [h_eq2]
    have h := intervalIntegral.integral_comp_mul_left
      (f := fun t : ℝ => Real.sqrt (1 - t ^ 2))
      (a := 1 / Real.sqrt 3) (b := 1 / Real.sqrt 2) (c := Real.sqrt 2) hc
    simpa [smul_eq_mul] using h
  rw [h_subst]
  have h_lim1 : Real.sqrt 2 * (1 / Real.sqrt 3) = Real.sqrt (2 / 3) := by
    have h : Real.sqrt 2 / Real.sqrt 3 = Real.sqrt (2 / 3) := by
      rw [← Real.sqrt_div (by norm_num)] <;> ring
    have h2 : Real.sqrt 2 * (1 / Real.sqrt 3) = Real.sqrt 2 / Real.sqrt 3 := by ring
    rw [h2, h]
  have h_lim2 : Real.sqrt 2 * (1 / Real.sqrt 2) = 1 := by
    field_simp [hc] <;> ring
  rw [h_lim1, h_lim2]
  have h_int : ∫ t in (Real.sqrt (2 / 3))..(1 : ℝ), Real.sqrt (1 - t ^ 2) =
      antiderivSqrt 1 - antiderivSqrt (Real.sqrt (2 / 3)) := by
    have h1 : -1 ≤ Real.sqrt (2 / 3) := by
      have h_pos : 0 ≤ Real.sqrt (2 / 3) := by positivity
      linarith
    have h3 : Real.sqrt (2 / 3) ≤ (1 : ℝ) := by
      have h4 : (Real.sqrt (2 / 3)) ^ 2 ≤ 1 := by
        rw [Real.sq_sqrt (by norm_num)] <;> norm_num
      have h5 : 0 ≤ Real.sqrt (2 / 3) := by positivity
      nlinarith [sq_nonneg (Real.sqrt (2 / 3) - 1)]
    exact integral_sqrt_one_sub_sq_interval h1 (by norm_num) h3
  rw [h_int] <;> ring

/-- Total integral from `0` to `1/√2`. -/
lemma integral_total :
    ∫ y in (0 : ℝ)..(1 / Real.sqrt 2), upperBound y =
    (1 / Real.sqrt 2) * Real.arcsin (1 / Real.sqrt 3) := by
  set a := (1 / Real.sqrt 3) with ha_def
  set b := (1 / Real.sqrt 2) with hb_def
  have h_ab : a ≤ b := by
    simp only [ha_def, hb_def]
    have h1 : Real.sqrt 2 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
    have h2 : 0 < Real.sqrt 2 := by positivity
    have h3 : 0 < Real.sqrt 3 := by positivity
    exact one_div_le_one_div_of_le h2 h1
  have h_int1 : IntervalIntegrable upperBound volume 0 a :=
    Continuous.intervalIntegrable (μ := volume) upperBound_continuous 0 a
  have h_int2 : IntervalIntegrable upperBound volume a b :=
    Continuous.intervalIntegrable (μ := volume) upperBound_continuous a b
  have h_split : ∫ y in (0 : ℝ)..b, upperBound y =
      (∫ y in (0 : ℝ)..a, upperBound y) + ∫ y in a..b, upperBound y := by
    exact (intervalIntegral.integral_add_adjacent_intervals h_int1 h_int2).symm
  rw [h_split, integral_first_part, integral_second_part]
  have h_pos1 : 0 ≤ 1 / Real.sqrt 3 := by positivity
  have h_sqrt_eq : Real.sqrt (1 - (1 / Real.sqrt 3) ^ 2) = Real.sqrt (2 / 3) := by
    have h2 : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
      field_simp [show (Real.sqrt 3 : ℝ) ≠ 0 by positivity]
      <;> rw [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] <;> ring
    rw [h2] <;> ring_nf
  have h_eq1 : Real.arcsin (1 / Real.sqrt 3) = Real.arccos (Real.sqrt (2 / 3)) := by
    rw [Real.arcsin_eq_arccos h_pos1, h_sqrt_eq]
  have h_eq2 : Real.arccos (Real.sqrt (2 / 3)) = Real.pi / 2 - Real.arcsin (Real.sqrt (2 / 3)) :=
    Real.arccos_eq_pi_div_two_sub_arcsin (Real.sqrt (2 / 3))
  have h_arcsin_comp : Real.arcsin (Real.sqrt (2 / 3)) = Real.pi / 2 - Real.arcsin (1 / Real.sqrt 3) := by
    linarith [h_eq1, h_eq2]
  have h_sqrt2 : Real.sqrt (1 - (Real.sqrt (2 / 3)) ^ 2) = 1 / Real.sqrt 3 := by
    have h2 : (Real.sqrt (2 / 3)) ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
    rw [h2]
    have h3 : Real.sqrt (1 - (2 / 3 : ℝ)) = Real.sqrt (1 / 3) := by ring_nf
    rw [h3]
    have h4 : Real.sqrt (1 / 3) = 1 / Real.sqrt 3 := by
      have h5 : Real.sqrt (1 / 3) = Real.sqrt 1 / Real.sqrt 3 := by
        exact Real.sqrt_div (show (0 : ℝ) ≤ 1 by norm_num) (3 : ℝ)
      rw [h5]
      have h6 : Real.sqrt 1 = 1 := by simp
      rw [h6] <;> ring
    exact h4
  have h_antideriv1_val : antiderivSqrt 1 = Real.pi / 4 := by
    simp [antiderivSqrt, Real.arcsin_one] <;> ring
  have h_prod_eq : (1 / Real.sqrt 3) * Real.sqrt (2 / 3) = Real.sqrt (2 / 3) * (1 / Real.sqrt 3) := by ring
  have h_antideriv_sum : antiderivSqrt (1 / Real.sqrt 3) + antiderivSqrt 1 - antiderivSqrt (Real.sqrt (2 / 3)) =
      Real.arcsin (1 / Real.sqrt 3) := by
    have h_expand1 : antiderivSqrt (1 / Real.sqrt 3) =
        (Real.arcsin (1 / Real.sqrt 3) + (1 / Real.sqrt 3) * Real.sqrt (2 / 3)) / 2 := by
      rw [antiderivSqrt]
      have h : Real.sqrt (1 - (1 / Real.sqrt 3) ^ 2) = Real.sqrt (2 / 3) := h_sqrt_eq
      rw [h] <;> ring
    have h_expand2 : antiderivSqrt (Real.sqrt (2 / 3)) =
        (Real.arcsin (Real.sqrt (2 / 3)) + Real.sqrt (2 / 3) * (1 / Real.sqrt 3)) / 2 := by
      rw [antiderivSqrt]
      have h : Real.sqrt (1 - (Real.sqrt (2 / 3)) ^ 2) = 1 / Real.sqrt 3 := h_sqrt2
      rw [h] <;> ring
    rw [h_expand1, h_antideriv1_val, h_expand2, h_arcsin_comp]
    <;> ring
  have h_main : (1 / Real.sqrt 2) * (antiderivSqrt (1 / Real.sqrt 3) + antiderivSqrt 1 - antiderivSqrt (Real.sqrt (2 / 3))) =
      (1 / Real.sqrt 2) * Real.arcsin (1 / Real.sqrt 3) := by
    rw [h_antideriv_sum]
  have h_factor : (1 / Real.sqrt 2) * antiderivSqrt (1 / Real.sqrt 3) + (1 / Real.sqrt 2) * (antiderivSqrt 1 - antiderivSqrt (Real.sqrt (2 / 3))) =
      (1 / Real.sqrt 2) * (antiderivSqrt (1 / Real.sqrt 3) + antiderivSqrt 1 - antiderivSqrt (Real.sqrt (2 / 3))) := by ring
  rw [h_factor]
  exact h_main

/-- Volume of the open ellipse set. -/
lemma ellipseSetOpen_volume :
    volume ellipseSetOpen = ENNReal.ofReal (2 * Real.sqrt 2 * Real.arcsin (1 / Real.sqrt 3)) := by
  rw [ellipseSetOpen_eq_regionBetween]
  have hfg : ∀ y ∈ yRange, lowerBound y ≤ upperBound y := by
    intro y hy
    have h : 0 ≤ upperBound y := upperBound_nonneg y hy
    simp [lowerBound] <;> linarith
  have h_vol : volume (regionBetween lowerBound upperBound yRange) =
      ENNReal.ofReal (∫ y in yRange, (upperBound - lowerBound) y) :=
    volume_regionBetween_eq_integral lowerBound_integrable upperBound_integrable yRange_measurable hfg
  rw [h_vol]
  have h_sub : (upperBound - lowerBound) = fun y : ℝ => 2 * upperBound y := by
    funext y
    simp [lowerBound] <;> ring
  rw [h_sub]
  set a := (1 / Real.sqrt 2) with ha_def
  have ha_pos : 0 < a := by positivity
  have h_set_int : ∫ y in yRange, (2 * upperBound y) =
      ∫ y in (-a)..a, (2 * upperBound y) := by
    have h1 : ∫ y in yRange, (2 * upperBound y) = ∫ y in Set.Ioc (-a) a, (2 * upperBound y) :=
      MeasureTheory.integral_Icc_eq_integral_Ioc
    rw [h1]
    rw [← intervalIntegral.integral_of_le (by linarith)]
  rw [h_set_int]
  have h_even_int : ∫ y in (-a)..(0 : ℝ), upperBound y =
      ∫ y in (0 : ℝ)..a, upperBound y := by
    have hc : (-1 : ℝ) ≠ 0 := by norm_num
    have h1 : ∫ y in (-a)..(0 : ℝ), upperBound y =
        ∫ y in (-a)..(0 : ℝ), upperBound (-y) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact (upperBound_even x).symm
    rw [h1]
    have h2 : ∫ y in (-a)..(0 : ℝ), upperBound (-y) =
        (-1 : ℝ) * ∫ t in a..(0 : ℝ), upperBound t := by
      have h3 := intervalIntegral.integral_comp_mul_left (f := upperBound) (a := -a) (b := 0) (c := -1) hc
      simpa [smul_eq_mul] using h3
    rw [h2]
    have h4 : (-1 : ℝ) * ∫ t in a..(0 : ℝ), upperBound t = ∫ t in (0 : ℝ)..a, upperBound t := by
      rw [intervalIntegral.integral_symm]
      <;> ring
    exact h4
  have h3 : ∫ y in (-a)..a, (2 * upperBound y) =
      4 * ∫ y in (0 : ℝ)..a, upperBound y := by
    have h4 : ∫ y in (-a)..a, (2 * upperBound y) =
        2 * ∫ y in (-a)..a, upperBound y := by
      rw [intervalIntegral.integral_const_mul]
    rw [h4]
    have h5 : ∫ y in (-a)..a, upperBound y =
        (∫ y in (-a)..(0 : ℝ), upperBound y) + ∫ y in (0 : ℝ)..a, upperBound y := by
      have h_i1 : IntervalIntegrable upperBound volume (-a) 0 :=
        Continuous.intervalIntegrable (μ := volume) upperBound_continuous (-a) 0
      have h_i2 : IntervalIntegrable upperBound volume 0 a :=
        Continuous.intervalIntegrable (μ := volume) upperBound_continuous 0 a
      exact (intervalIntegral.integral_add_adjacent_intervals h_i1 h_i2).symm
    rw [h5, h_even_int] <;> ring
  rw [h3, integral_total]
  have h_final : 4 * ((1 / Real.sqrt 2) * Real.arcsin (1 / Real.sqrt 3)) =
      2 * Real.sqrt 2 * Real.arcsin (1 / Real.sqrt 3) := by
    have h_sqrt2_pos : 0 < Real.sqrt 2 := by positivity
    field_simp [h_sqrt2_pos.ne']
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [h_final]

/-! ### Closed set and boundary -/

lemma isOpen_ellipseSetOpen : IsOpen ellipseSetOpen := by
  have hf1 : Continuous (fun (p : ℝ × ℝ) => 2 * p.1 ^ 2 + p.2 ^ 2) := by continuity
  have hf2 : Continuous (fun (p : ℝ × ℝ) => p.1 ^ 2 + 2 * p.2 ^ 2) := by continuity
  have h1 : IsOpen {p : ℝ × ℝ | 2 * p.1 ^ 2 + p.2 ^ 2 < 1} := isOpen_lt hf1 continuous_const
  have h2 : IsOpen {p : ℝ × ℝ | p.1 ^ 2 + 2 * p.2 ^ 2 < 1} := isOpen_lt hf2 continuous_const
  exact h1.inter h2

lemma convex_ellipseSetOpen : Convex ℝ ellipseSetOpen := by
  intro p hp q hq a b ha hb hab
  by_cases h_a0 : a = 0
  · have h_b1 : b = 1 := by linarith [hab]
    have hr_eq : a • p + b • q = q := by
      rw [h_a0, h_b1] <;> simp
    rw [hr_eq] <;> exact hq
  · by_cases h_b0 : b = 0
    · have h_a1 : a = 1 := by linarith [hab]
      have hr_eq : a • p + b • q = p := by
        rw [h_a1, h_b0] <;> simp
      rw [hr_eq] <;> exact hp
    · have h_pos1 : 0 < a := by
        by_contra h
        have h' : a = 0 := by linarith [ha]
        exact h_a0 h'
      have h_pos2 : 0 < b := by
        by_contra h
        have h' : b = 0 := by linarith [hb]
        exact h_b0 h'
      set r : ℝ × ℝ := a • p + b • q with hr
      have hr1 : r.1 = a * p.1 + b * q.1 := by simp [hr, smul_eq_mul] <;> ring
      have hr2 : r.2 = a * p.2 + b * q.2 := by simp [hr, smul_eq_mul] <;> ring
      have h1 : (a * p.1 + b * q.1)^2 ≤ a * p.1^2 + b * q.1^2 := by
        have h_eq : a * p.1^2 + b * q.1^2 - (a * p.1 + b * q.1)^2 = a * b * (p.1 - q.1)^2 := by
          have hb' : b = 1 - a := by linarith
          rw [hb'] <;> ring
        have h_nonneg : 0 ≤ a * b * (p.1 - q.1)^2 := by
          exact mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
        have h : 0 ≤ a * p.1^2 + b * q.1^2 - (a * p.1 + b * q.1)^2 := by
          rw [h_eq] <;> exact h_nonneg
        linarith
      have h2 : (a * p.2 + b * q.2)^2 ≤ a * p.2^2 + b * q.2^2 := by
        have h_eq : a * p.2^2 + b * q.2^2 - (a * p.2 + b * q.2)^2 = a * b * (p.2 - q.2)^2 := by
          have hb' : b = 1 - a := by linarith
          rw [hb'] <;> ring
        have h_nonneg : 0 ≤ a * b * (p.2 - q.2)^2 := by
          exact mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
        have h : 0 ≤ a * p.2^2 + b * q.2^2 - (a * p.2 + b * q.2)^2 := by
          rw [h_eq] <;> exact h_nonneg
        linarith
      have h4 : 2 * r.1^2 + r.2^2 ≤ a * (2 * p.1^2 + p.2^2) + b * (2 * q.1^2 + q.2^2) := by
        rw [hr1, hr2]; nlinarith [h1, h2]
      have h4' : a * (2 * p.1^2 + p.2^2) + b * (2 * q.1^2 + q.2^2) < 1 := by
        have hpa : 2 * p.1^2 + p.2^2 < 1 := hp.1
        have hqb : 2 * q.1^2 + q.2^2 < 1 := hq.1
        nlinarith [h_pos1, h_pos2, hab]
      have h3 : 2 * r.1^2 + r.2^2 < 1 := by
        calc 2 * r.1^2 + r.2^2 ≤ a * (2 * p.1^2 + p.2^2) + b * (2 * q.1^2 + q.2^2) := h4
             _ < 1 := h4'
      have h6 : r.1^2 + 2 * r.2^2 ≤ a * (p.1^2 + 2 * p.2^2) + b * (q.1^2 + 2 * q.2^2) := by
        rw [hr1, hr2]; nlinarith [h1, h2]
      have h6' : a * (p.1^2 + 2 * p.2^2) + b * (q.1^2 + 2 * q.2^2) < 1 := by
        have hpa : p.1^2 + 2 * p.2^2 < 1 := hp.2
        have hqb : q.1^2 + 2 * q.2^2 < 1 := hq.2
        nlinarith [h_pos1, h_pos2, hab]
      have h5 : r.1^2 + 2 * r.2^2 < 1 := by
        calc r.1^2 + 2 * r.2^2 ≤ a * (p.1^2 + 2 * p.2^2) + b * (q.1^2 + 2 * q.2^2) := h6
             _ < 1 := h6'
      exact ⟨h3, h5⟩

lemma frontier_ellipseSetOpen_null : volume (frontier ellipseSetOpen) = 0 := by
  have h_main : ∀ (s : Set (ℝ × ℝ)), Convex ℝ s → volume (frontier s) = 0 := by
    intro s hs
    exact Convex.addHaar_frontier volume hs
  exact h_main ellipseSetOpen convex_ellipseSetOpen

lemma ellipseSetOpen_subset : ellipseSetOpen ⊆ ellipseSet := by
  intro p hp
  simp only [ellipseSetOpen, ellipseSet, mem_setOf_eq] at hp ⊢
  exact ⟨by linarith, by linarith⟩

lemma ellipseSet_measurable : MeasurableSet ellipseSet := by
  have hf1 : Measurable fun (p : ℝ × ℝ) => 2 * p.1 ^ 2 + p.2 ^ 2 := by fun_prop
  have hf2 : Measurable fun (p : ℝ × ℝ) => p.1 ^ 2 + 2 * p.2 ^ 2 := by fun_prop
  have h1 : MeasurableSet {p : ℝ × ℝ | 2 * p.1 ^ 2 + p.2 ^ 2 ≤ 1} :=
    measurableSet_le hf1 measurable_const
  have h2 : MeasurableSet {p : ℝ × ℝ | p.1 ^ 2 + 2 * p.2 ^ 2 ≤ 1} :=
    measurableSet_le hf2 measurable_const
  exact h1.inter h2

/-- For `p ∈ ellipseSet` and `0 < t < 1`, `t • p ∈ ellipseSetOpen`. -/
lemma scaling_in_open {p : ℝ × ℝ} (hp : p ∈ ellipseSet) {t : ℝ} (ht1 : 0 < t) (ht2 : t < 1) :
    t • p ∈ ellipseSetOpen := by
  simp only [ellipseSetOpen, mem_setOf_eq]
  have h1 : 2 * (t * p.1) ^ 2 + (t * p.2) ^ 2 < 1 := by
    have h11 : 2 * (t * p.1) ^ 2 + (t * p.2) ^ 2 = t ^ 2 * (2 * p.1 ^ 2 + p.2 ^ 2) := by ring
    rw [h11]
    have h12 : 2 * p.1 ^ 2 + p.2 ^ 2 ≤ 1 := hp.1
    have h13 : t ^ 2 < 1 := by nlinarith
    nlinarith
  have h2 : (t * p.1) ^ 2 + 2 * (t * p.2) ^ 2 < 1 := by
    have h21 : (t * p.1) ^ 2 + 2 * (t * p.2) ^ 2 = t ^ 2 * (p.1 ^ 2 + 2 * p.2 ^ 2) := by ring
    rw [h21]
    have h22 : p.1 ^ 2 + 2 * p.2 ^ 2 ≤ 1 := hp.2
    have h23 : t ^ 2 < 1 := by nlinarith
    nlinarith
  exact ⟨h1, h2⟩

lemma ellipseSet_subset_closure_open : ellipseSet ⊆ closure ellipseSetOpen := by
  intro p hp
  let f : ℕ → ℝ × ℝ := fun n => (((n : ℝ) + 1) / ((n : ℝ) + 2)) • p
  have h : ∀ n : ℕ, f n ∈ ellipseSetOpen := by
    intro n
    have ht1 : 0 < (((n : ℝ) + 1) / ((n : ℝ) + 2)) := by positivity
    have ht2 : (((n : ℝ) + 1) / ((n : ℝ) + 2)) < 1 := by
      have h1 : (n : ℝ) + 1 < (n : ℝ) + 2 := by linarith
      have h2 : 0 < (n : ℝ) + 2 := by linarith
      exact (div_lt_one h2).mpr h1
    exact scaling_in_open hp ht1 ht2
  have h_tend : Filter.Tendsto f Filter.atTop (nhds p) := by
    have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) Filter.atTop (nhds 1) := by
      have h2 : (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) = fun n : ℕ => 1 - 1 / ((n : ℝ) + 2) := by
        funext n
        field_simp
        <;> ring
      rw [h2]
      have h3 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) Filter.atTop (nhds 0) := by
        have h4 : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2) Filter.atTop Filter.atTop := by
          apply Filter.tendsto_atTop_atTop.mpr
          intro b
          refine ⟨Nat.ceil b + 1, fun n hn => ?_⟩
          have h5 : (n : ℝ) ≥ Nat.ceil b + 1 := by exact_mod_cast hn
          have h6 : (n : ℝ) + 2 ≥ b := by
            have h7 : (n : ℝ) ≥ Nat.ceil b := by linarith
            have h8 : (Nat.ceil b : ℝ) ≥ b := Nat.le_ceil b
            linarith
          exact h6
        have h_eq : (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) = fun n : ℕ => ((n : ℝ) + 2)⁻¹ := by
          funext n
          field_simp
        rw [h_eq]
        exact tendsto_inv_atTop_zero.comp h4
      have h_const : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
      have h_sub : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - (1 : ℝ) / ((n : ℝ) + 2)) Filter.atTop (nhds ((1 : ℝ) - 0)) := h_const.sub h3
      have h_simp : (1 : ℝ) - 0 = (1 : ℝ) := by simp
      rw [h_simp] at h_sub
      exact h_sub
    have h_tmp : Filter.Tendsto f Filter.atTop (nhds ((1 : ℝ) • p)) := h1.smul_const p
    have h_one : (1 : ℝ) • p = p := by simp
    rw [h_one] at h_tmp
    exact h_tmp
  have h_event : ∀ᶠ n in Filter.atTop, f n ∈ ellipseSetOpen := by
    filter_upwards with n
    exact h n
  exact mem_closure_of_tendsto h_tend h_event

lemma ellipseSet_volume :
    volume ellipseSet = volume ellipseSetOpen := by
  have h1 : volume ellipseSetOpen ≤ volume ellipseSet := measure_mono ellipseSetOpen_subset
  have h2 : ellipseSet ⊆ closure ellipseSetOpen := ellipseSet_subset_closure_open
  have h3 : volume ellipseSet ≤ volume (closure ellipseSetOpen) := measure_mono h2
  have h5 : closure ellipseSetOpen = ellipseSetOpen ∪ frontier ellipseSetOpen := by
    have h_int : interior ellipseSetOpen = ellipseSetOpen := by
      rw [interior_eq_iff_isOpen] <;> exact isOpen_ellipseSetOpen
    have h : closure ellipseSetOpen = interior ellipseSetOpen ∪ frontier ellipseSetOpen := by
      exact closure_eq_interior_union_frontier ellipseSetOpen
    rw [h, h_int]
  have h_disj : Disjoint ellipseSetOpen (frontier ellipseSetOpen) := by
    have h_int : interior ellipseSetOpen = ellipseSetOpen := by
      rw [interior_eq_iff_isOpen] <;> exact isOpen_ellipseSetOpen
    have h_front : frontier ellipseSetOpen = closure ellipseSetOpen \ interior ellipseSetOpen := by
      exact Eq.symm (closure_sdiff_interior ellipseSetOpen)
    rw [h_front, h_int]
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact hx2.2 hx1
  have h_front_meas : MeasurableSet (frontier ellipseSetOpen) := by
    have h1 : IsClosed (closure ellipseSetOpen) := isClosed_closure
    have h2 : IsClosed (closure (ellipseSetOpenᶜ)) := isClosed_closure
    have h3 : frontier ellipseSetOpen = closure ellipseSetOpen ∩ closure (ellipseSetOpenᶜ) := by
      rw [frontier_eq_closure_inter_closure]
    rw [h3]
    exact (h1.inter h2).measurableSet
  have h4 : volume (closure ellipseSetOpen) = volume ellipseSetOpen := by
    rw [h5]
    have h_union : volume (ellipseSetOpen ∪ frontier ellipseSetOpen) = volume ellipseSetOpen + volume (frontier ellipseSetOpen) := by
      exact measure_union h_disj h_front_meas
    rw [h_union, frontier_ellipseSetOpen_null] <;> simp
  rw [h4] at h3
  exact le_antisymm h3 h1

end Geometry.ProjectionArea
