import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRescalingBasics
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLongitudinalCompressionEnvelopeHelpers
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Angle helpers for longitudinal-compression line distance
-/

noncomputable section

namespace Kakeya.Assouad

open InnerProductGeometry

lemma sq_ge_sq_imp_ge
    {first second : ℝ}
    (hfirst : 0 ≤ first)
    (hsecond : 0 ≤ second)
    (hsquares : first ^ 2 ≥ second ^ 2) :
    first ≥ second := by
  by_contra hlt
  have hstrict : first < second := by linarith
  have hsecond_pos : 0 < second := by
    by_contra hnonpos
    have hzero : second = 0 := by linarith
    rw [hzero] at hstrict
    linarith
  have hsquare_strict : first ^ 2 < second ^ 2 := by
    calc
      first ^ 2 ≤ first * second := by nlinarith
      _ < second ^ 2 := by nlinarith
  linarith

/--
The real-algebra core of the projective-angle comparison.
-/
lemma longitudinalCompression_algebraicCore
    (A B C : ℝ)
    (hA_nonneg : 0 ≤ A)
    (hB_nonneg : 0 ≤ B)
    (hC2_le : C ^ 2 ≤ A * B)
    (hA : A ≤ 3 / 10000)
    (hB : B ≤ 3 / 10000)
    (h_diff_nonneg : 0 ≤ A + B - 2 * C) :
    (C + 1) ^ 2 * ((10000 * A + 1) * (10000 * B + 1)) ≥
      (10000 * C + 1) ^ 2 * ((A + 1) * (B + 1)) := by
  have hAB_small : 10000 * A * B < 1 := by
    have h1 : 10000 * A ≤ 3 := by nlinarith
    have h2 : 10000 * B ≤ 3 := by nlinarith
    nlinarith
  set coefficient : ℝ :=
    10000 * (A + B) + 10001 with hcoefficient
  have hcoefficient_pos : 0 < coefficient := by positivity
  have hstep :
      C ^ 2 * coefficient ≤ A * B * coefficient :=
    mul_le_mul_of_nonneg_right hC2_le
      (le_of_lt hcoefficient_pos)
  have hbracket_le :
      C ^ 2 * coefficient +
            2 * C * (1 - 10000 * A * B) -
            (10001 * A * B + A + B) ≤
        (10000 * A * B - 1) * (A + B - 2 * C) := by
    have hrewrite :
        A * B * coefficient =
          10000 * A * B * (A + B) + 10001 * A * B := by
      simp [hcoefficient]
      ring
    linarith
  have hrhs_nonpos :
      (10000 * A * B - 1) * (A + B - 2 * C) ≤ 0 := by
    have hnegative : 10000 * A * B - 1 < 0 := by
      linarith
    nlinarith
  have hbracket_nonpos :
      C ^ 2 * coefficient +
            2 * C * (1 - 10000 * A * B) -
            (10001 * A * B + A + B) ≤
        0 := by
    linarith [hbracket_le, hrhs_nonpos]
  have hidentity :
      (C + 1) ^ 2 *
            ((10000 * A + 1) * (10000 * B + 1)) -
          (10000 * C + 1) ^ 2 * ((A + 1) * (B + 1)) =
        (1 - 10000 : ℝ) *
          (C ^ 2 * coefficient +
            2 * C * (1 - 10000 * A * B) -
            (10001 * A * B + A + B)) := by
    simp [hcoefficient]
    ring
  have hproduct :
      0 ≤
        (1 - 10000 : ℝ) *
          (C ^ 2 * coefficient +
            2 * C * (1 - 10000 * A * B) -
            (10001 * A * B + A + B)) :=
    mul_nonneg_of_nonpos_of_nonpos (by norm_num) hbracket_nonpos
  linarith [hidentity, hproduct]

/--
For sufficiently small transverse projective slopes, multiplying both slopes
by `100` does not decrease their spherical angle.
-/
lemma longitudinalCompression_coreAngleInequality
    {first second : Point3}
    (hfirst_two : first 2 = 0)
    (hsecond_two : second 2 = 0)
    (hfirst_bound : ‖first‖ ^ 2 ≤ 3 / 10000)
    (hsecond_bound : ‖second‖ ^ 2 ≤ 3 / 10000) :
    InnerProductGeometry.angle (first + e3) (second + e3) ≤
      InnerProductGeometry.angle
        ((100 : ℝ) • first + e3)
        ((100 : ℝ) • second + e3) := by
  set A : ℝ := ‖first‖ ^ 2 with hA
  set B : ℝ := ‖second‖ ^ 2 with hB
  set C : ℝ := inner ℝ first second with hC
  have hA_nonneg : 0 ≤ A := by positivity
  have hB_nonneg : 0 ≤ B := by positivity
  have hC2_le : C ^ 2 ≤ A * B := by
    have hinner :
        |inner ℝ first second| ≤ ‖first‖ * ‖second‖ :=
      abs_real_inner_le_norm first second
    have hsquares :
        C ^ 2 ≤ (‖first‖ * ‖second‖) ^ 2 := by
      have habs : |C| ≤ ‖first‖ * ‖second‖ := hinner
      have hsq_abs : C ^ 2 = |C| ^ 2 := by simp [sq_abs]
      rw [hsq_abs]
      gcongr
    have hproduct :
        (‖first‖ * ‖second‖) ^ 2 = A * B := by
      simp [hA, hB]
      ring
    linarith
  have hdiff_nonneg : 0 ≤ A + B - 2 * C := by
    have hnorm :
        ‖first - second‖ ^ 2 = A + B - 2 * C := by
      rw [norm_sub_sq_real first second, hA, hB, hC] <;> ring
    have hnonneg : 0 ≤ ‖first - second‖ ^ 2 := by positivity
    linarith
  have hC_lower : C ≥ -Real.sqrt (A * B) := by
    by_cases hC_nonneg : 0 ≤ C
    · have hsqrt_nonneg : 0 ≤ Real.sqrt (A * B) := by positivity
      linarith
    · have hC_neg : C < 0 := by linarith
      have hsquare : (-C) ^ 2 ≤ A * B := by nlinarith
      have hle : -C ≤ Real.sqrt (A * B) := by
        have hnonneg : 0 ≤ -C := by linarith
        have hsqrt_square :
            (Real.sqrt (A * B)) ^ 2 = A * B := by
          rw [Real.sq_sqrt]
          positivity
        nlinarith [Real.sqrt_nonneg (A * B)]
      linarith
  have hsqrt_le : Real.sqrt (A * B) ≤ 3 / 10000 := by
    have hproduct :
        A * B ≤ (3 / 10000 : ℝ) ^ 2 := by
      nlinarith
    have hsqrt :=
      Real.sqrt_le_sqrt hproduct
    have heval :
        Real.sqrt ((3 / 10000 : ℝ) ^ 2) = 3 / 10000 := by
      rw [Real.sqrt_sq_eq_abs]
      norm_num
    linarith
  have hC_one_pos : 0 < C + 1 := by
    have hC_small : C ≥ -3 / 10000 := by
      linarith
    linarith
  have hfirst_e3 : inner ℝ first e3 = 0 := by
    have h : first 2 = inner ℝ first e3 :=
      coord2_eq_inner_e3 first
    rw [← h, hfirst_two]
  have hsecond_e3 : inner ℝ second e3 = 0 := by
    have h : second 2 = inner ℝ second e3 :=
      coord2_eq_inner_e3 second
    rw [← h, hsecond_two]
  have he3_first : inner ℝ e3 first = 0 := by
    rw [real_inner_comm]
    exact hfirst_e3
  have he3_second : inner ℝ e3 second = 0 := by
    rw [real_inner_comm]
    exact hsecond_e3
  have hinner1 :
      inner ℝ (first + e3) (second + e3) = C + 1 := by
    simp [hC, inner_add_left, inner_add_right, hfirst_e3,
      he3_second, he3_first, e3_norm] <;> ring
  have hnorm11 : ‖first + e3‖ ^ 2 = A + 1 := by
    rw [norm_add_sq_real, hA, e3_norm, hfirst_e3] <;> ring
  have hnorm12 : ‖second + e3‖ ^ 2 = B + 1 := by
    rw [norm_add_sq_real, hB, e3_norm, hsecond_e3] <;> ring
  have hinner2 :
      inner ℝ ((100 : ℝ) • first + e3)
          ((100 : ℝ) • second + e3) =
        10000 * C + 1 := by
    have hexpand :
        inner ℝ ((100 : ℝ) • first + e3)
            ((100 : ℝ) • second + e3) =
          inner ℝ ((100 : ℝ) • first) ((100 : ℝ) • second) +
            inner ℝ ((100 : ℝ) • first) e3 +
            inner ℝ e3 ((100 : ℝ) • second) +
            inner ℝ e3 e3 := by
      simp [inner_add_left, inner_add_right]
      abel
    rw [hexpand]
    have h1 :
        inner ℝ ((100 : ℝ) • first) ((100 : ℝ) • second) =
          10000 * C := by
      simp [inner_smul_left, inner_smul_right, hC] <;> ring
    have h2 : inner ℝ ((100 : ℝ) • first) e3 = 0 := by
      rw [inner_smul_left, hfirst_e3] <;> ring
    have h3 : inner ℝ e3 ((100 : ℝ) • second) = 0 := by
      rw [inner_smul_right, he3_second] <;> ring
    have h4 : inner ℝ e3 e3 = 1 := by
      simp [e3_norm, inner_self_eq_norm_sq_to_K] <;> norm_num
    rw [h1, h2, h3, h4] <;> ring
  have hnorm21 :
      ‖(100 : ℝ) • first + e3‖ ^ 2 = 10000 * A + 1 := by
    have hscaled :
        ‖(100 : ℝ) • first‖ = 100 * ‖first‖ := by
      rw [norm_smul]
      simp [abs_of_pos]
    have hinner :
        inner ℝ ((100 : ℝ) • first) e3 = 0 := by
      rw [inner_smul_left, hfirst_e3] <;> ring
    rw [norm_add_sq_real, hscaled, hinner, e3_norm, hA] <;> ring
  have hnorm22 :
      ‖(100 : ℝ) • second + e3‖ ^ 2 = 10000 * B + 1 := by
    have hscaled :
        ‖(100 : ℝ) • second‖ = 100 * ‖second‖ := by
      rw [norm_smul]
      simp [abs_of_pos]
    have hinner :
        inner ℝ ((100 : ℝ) • second) e3 = 0 := by
      rw [inner_smul_left, hsecond_e3] <;> ring
    rw [norm_add_sq_real, hscaled, hinner, e3_norm, hB] <;> ring
  set firstAngle :=
    angle (first + e3) (second + e3) with hfirstAngle
  set secondAngle :=
    angle ((100 : ℝ) • first + e3)
      ((100 : ℝ) • second + e3) with hsecondAngle
  have hfirstAngle_nonneg : 0 ≤ firstAngle :=
    angle_nonneg _ _
  have hsecondAngle_nonneg : 0 ≤ secondAngle :=
    angle_nonneg _ _
  have hfirstAngle_le_pi : firstAngle ≤ Real.pi :=
    angle_le_pi _ _
  have hsecondAngle_le_pi : secondAngle ≤ Real.pi :=
    angle_le_pi _ _
  have hfirst_coord : (first + e3) 2 = 1 := by
    simp [hfirst_two, e3]
  have hsecond_coord : (second + e3) 2 = 1 := by
    simp [hsecond_two, e3]
  have hscaled_first_coord :
      ((100 : ℝ) • first + e3) 2 = 1 := by
    simp [hfirst_two, e3]
  have hscaled_second_coord :
      ((100 : ℝ) • second + e3) 2 = 1 := by
    simp [hsecond_two, e3]
  have hnorm1_pos : 0 < ‖first + e3‖ := by
    apply norm_pos_iff.mpr
    intro hzero
    rw [hzero] at hfirst_coord
    simp at hfirst_coord
  have hnorm2_pos : 0 < ‖second + e3‖ := by
    apply norm_pos_iff.mpr
    intro hzero
    rw [hzero] at hsecond_coord
    simp at hsecond_coord
  have hnorm3_pos : 0 < ‖(100 : ℝ) • first + e3‖ := by
    apply norm_pos_iff.mpr
    intro hzero
    rw [hzero] at hscaled_first_coord
    simp at hscaled_first_coord
  have hnorm4_pos : 0 < ‖(100 : ℝ) • second + e3‖ := by
    apply norm_pos_iff.mpr
    intro hzero
    rw [hzero] at hscaled_second_coord
    simp at hscaled_second_coord
  have hcos1 :
      Real.cos firstAngle =
        (C + 1) / (‖first + e3‖ * ‖second + e3‖) := by
    have hcos :=
      cos_angle_mul_norm_mul_norm (first + e3) (second + e3)
    rw [hinner1] at hcos
    field_simp [(mul_pos hnorm1_pos hnorm2_pos).ne'] at hcos ⊢
    linarith
  have hcos2 :
      Real.cos secondAngle =
        (10000 * C + 1) /
          (‖(100 : ℝ) • first + e3‖ *
            ‖(100 : ℝ) • second + e3‖) := by
    have hcos :=
      cos_angle_mul_norm_mul_norm
        ((100 : ℝ) • first + e3)
        ((100 : ℝ) • second + e3)
    rw [hinner2] at hcos
    field_simp [(mul_pos hnorm3_pos hnorm4_pos).ne'] at hcos ⊢
    linarith
  by_cases hcase : 10000 * C + 1 ≤ 0
  · have hcos2_nonpos : Real.cos secondAngle ≤ 0 := by
      rw [hcos2]
      exact
        div_nonpos_of_nonpos_of_nonneg hcase
          (by positivity)
    have hsecond_ge : Real.pi / 2 ≤ secondAngle := by
      by_contra h
      have hlt : secondAngle < Real.pi / 2 := by linarith
      have hcos_pos :
          0 < Real.cos secondAngle :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith, hlt⟩
      linarith
    have hcos1_pos : 0 < Real.cos firstAngle := by
      rw [hcos1]
      positivity
    have hfirst_lt : firstAngle < Real.pi / 2 := by
      by_contra h
      have hge : Real.pi / 2 ≤ firstAngle := by linarith
      have hcos_nonpos : Real.cos firstAngle ≤ 0 := by
        have hcos_le :
            Real.cos firstAngle ≤ Real.cos (Real.pi / 2) :=
          Real.cos_le_cos_of_nonneg_of_le_pi
            (by linarith [Real.pi_pos]) hfirstAngle_le_pi hge
        rw [Real.cos_pi_div_two] at hcos_le
        exact hcos_le
      linarith
    linarith
  · have hpositive : 0 < 10000 * C + 1 := by linarith
    have halgebra :=
      longitudinalCompression_algebraicCore A B C
        hA_nonneg hB_nonneg hC2_le hfirst_bound
        hsecond_bound hdiff_nonneg
    have hsqrt1 :
        ‖first + e3‖ * ‖second + e3‖ =
          Real.sqrt ((A + 1) * (B + 1)) := by
      have hsquare :
          (‖first + e3‖ * ‖second + e3‖) ^ 2 =
            (A + 1) * (B + 1) := by
        calc
          (‖first + e3‖ * ‖second + e3‖) ^ 2 =
              ‖first + e3‖ ^ 2 * ‖second + e3‖ ^ 2 := by
            ring
          _ = (A + 1) * (B + 1) := by
            rw [hnorm11, hnorm12]
      have hnonneg : 0 ≤ (A + 1) * (B + 1) := by
        positivity
      have hsqrt_square :
          Real.sqrt ((A + 1) * (B + 1)) ^ 2 =
            (A + 1) * (B + 1) :=
        Real.sq_sqrt hnonneg
      apply sq_eq_sq₀ (by positivity) (by positivity) |>.mp
      rw [hsquare, hsqrt_square]
    have hsqrt2 :
        ‖(100 : ℝ) • first + e3‖ *
            ‖(100 : ℝ) • second + e3‖ =
          Real.sqrt
            ((10000 * A + 1) * (10000 * B + 1)) := by
      have hsquare :
          (‖(100 : ℝ) • first + e3‖ *
              ‖(100 : ℝ) • second + e3‖) ^ 2 =
            (10000 * A + 1) * (10000 * B + 1) := by
        calc
          (‖(100 : ℝ) • first + e3‖ *
              ‖(100 : ℝ) • second + e3‖) ^ 2 =
              ‖(100 : ℝ) • first + e3‖ ^ 2 *
                ‖(100 : ℝ) • second + e3‖ ^ 2 := by
            ring
          _ =
              (10000 * A + 1) * (10000 * B + 1) := by
            rw [hnorm21, hnorm22]
      have hnonneg :
          0 ≤ (10000 * A + 1) * (10000 * B + 1) := by
        positivity
      have hsqrt_square :
          Real.sqrt
              ((10000 * A + 1) * (10000 * B + 1)) ^ 2 =
            (10000 * A + 1) * (10000 * B + 1) :=
        Real.sq_sqrt hnonneg
      apply sq_eq_sq₀ (by positivity) (by positivity) |>.mp
      rw [hsquare, hsqrt_square]
    have hcosine : Real.cos firstAngle ≥ Real.cos secondAngle := by
      rw [hcos1, hcos2, hsqrt1, hsqrt2]
      let leftNumerator :=
        (C + 1) *
          Real.sqrt
            ((10000 * A + 1) * (10000 * B + 1))
      let rightNumerator :=
        (10000 * C + 1) *
          Real.sqrt ((A + 1) * (B + 1))
      have hleft_nonneg : 0 ≤ leftNumerator := by positivity
      have hright_nonneg : 0 ≤ rightNumerator := by positivity
      have hscaled_nonneg :
          0 ≤ (10000 * A + 1) * (10000 * B + 1) := by
        positivity
      have hplain_nonneg :
          0 ≤ (A + 1) * (B + 1) := by positivity
      have hscaled_square :
          Real.sqrt
              ((10000 * A + 1) * (10000 * B + 1)) ^ 2 =
            (10000 * A + 1) * (10000 * B + 1) :=
        Real.sq_sqrt hscaled_nonneg
      have hplain_square :
          Real.sqrt ((A + 1) * (B + 1)) ^ 2 =
            (A + 1) * (B + 1) :=
        Real.sq_sqrt hplain_nonneg
      have hnumerator_squares :
          leftNumerator ^ 2 ≥ rightNumerator ^ 2 := by
        simp only [leftNumerator, rightNumerator, mul_pow]
        rw [hscaled_square, hplain_square]
        exact halgebra
      have hnumerator :
          leftNumerator ≥ rightNumerator :=
        sq_ge_sq_imp_ge hleft_nonneg hright_nonneg
          hnumerator_squares
      have hplain_pos :
          0 < Real.sqrt ((A + 1) * (B + 1)) :=
        Real.sqrt_pos.mpr (by positivity)
      have hscaled_pos :
          0 <
            Real.sqrt
              ((10000 * A + 1) * (10000 * B + 1)) :=
        Real.sqrt_pos.mpr (by positivity)
      have hleft_rewrite :
          (C + 1) / Real.sqrt ((A + 1) * (B + 1)) =
            leftNumerator /
              (Real.sqrt ((A + 1) * (B + 1)) *
                Real.sqrt
                  ((10000 * A + 1) * (10000 * B + 1))) := by
        simp only [leftNumerator]
        field_simp [hplain_pos.ne', hscaled_pos.ne'] <;> ring
      have hright_rewrite :
          (10000 * C + 1) /
              Real.sqrt
                ((10000 * A + 1) * (10000 * B + 1)) =
            rightNumerator /
              (Real.sqrt ((A + 1) * (B + 1)) *
                Real.sqrt
                  ((10000 * A + 1) * (10000 * B + 1))) := by
        simp only [rightNumerator]
        field_simp [hplain_pos.ne', hscaled_pos.ne'] <;> ring
      rw [hleft_rewrite, hright_rewrite]
      gcongr
    by_contra hangle
    have hstrict : secondAngle < firstAngle :=
      lt_of_not_ge hangle
    have hcos_strict :
        Real.cos firstAngle < Real.cos secondAngle :=
      Real.cos_lt_cos_of_nonneg_of_le_pi
        hsecondAngle_nonneg hfirstAngle_le_pi hstrict
    linarith

/--
Transport the core projective-angle inequality back to unit directions.
-/
lemma longitudinalCompression_angleChain
    {historicalFirst historicalSecond literalFirst literalSecond : Point3}
    (hhistoricalFirst_norm : ‖historicalFirst‖ = 1)
    (hhistoricalSecond_norm : ‖historicalSecond‖ = 1)
    (hhistoricalFirst_two : 0 < historicalFirst 2)
    (hhistoricalSecond_two : 0 < historicalSecond 2)
    (hliteralFirst_two : 0 < literalFirst 2)
    (hliteralSecond_two : 0 < literalSecond 2)
    (hliteralFirst_eq :
      literalFirst =
        NormedSpace.normalize
          (wz2PaperLongitudinalCompression historicalFirst))
    (hliteralSecond_eq :
      literalSecond =
        NormedSpace.normalize
          (wz2PaperLongitudinalCompression historicalSecond))
    (hfirst_bound :
      ‖transversePart
        (wz1PaperProjectiveDirection historicalFirst)‖ ^ 2 ≤
          3 / 10000)
    (hsecond_bound :
      ‖transversePart
        (wz1PaperProjectiveDirection historicalSecond)‖ ^ 2 ≤
          3 / 10000) :
    InnerProductGeometry.angle historicalFirst historicalSecond ≤
      InnerProductGeometry.angle literalFirst literalSecond := by
  let compression := wz2PaperLongitudinalCompression
  let projectiveFirst :=
    wz1PaperProjectiveDirection historicalFirst
  let projectiveSecond :=
    wz1PaperProjectiveDirection historicalSecond
  let transverseFirst := transversePart projectiveFirst
  let transverseSecond := transversePart projectiveSecond
  have htransverseFirst_two : transverseFirst 2 = 0 :=
    transversePart_coord2 projectiveFirst
  have htransverseSecond_two : transverseSecond 2 = 0 :=
    transversePart_coord2 projectiveSecond
  have hprojectiveFirst :
      projectiveFirst = transverseFirst + e3 := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [projectiveFirst, transverseFirst, transversePart_coord0,
        transversePart_coord1, transversePart_coord2,
        wz1PaperProjectiveDirection_coord_two
          hhistoricalFirst_two.ne',
        e3, PiLp.add_apply] <;>
      ring
  have hprojectiveSecond :
      projectiveSecond = transverseSecond + e3 := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [projectiveSecond, transverseSecond, transversePart_coord0,
        transversePart_coord1, transversePart_coord2,
        wz1PaperProjectiveDirection_coord_two
          hhistoricalSecond_two.ne',
        e3, PiLp.add_apply] <;>
      ring
  have hcompressionFirst_ne :
      compression historicalFirst ≠ 0 := by
    intro hzero
    have hcoordinate :
        (compression historicalFirst) 2 = 0 := by
      rw [hzero]
      simp
    have hdiv : historicalFirst 2 / 100 = 0 := by
      simpa [compression, wz2PaperLongitudinalCompression] using
        hcoordinate
    linarith
  have hcompressionSecond_ne :
      compression historicalSecond ≠ 0 := by
    intro hzero
    have hcoordinate :
        (compression historicalSecond) 2 = 0 := by
      rw [hzero]
      simp
    have hdiv : historicalSecond 2 / 100 = 0 := by
      simpa [compression, wz2PaperLongitudinalCompression] using
        hcoordinate
    linarith
  have hcompressionFirst_two :
      0 < (compression historicalFirst) 2 := by
    simp [compression, wz2PaperLongitudinalCompression,
      hhistoricalFirst_two] <;> linarith
  have hcompressionSecond_two :
      0 < (compression historicalSecond) 2 := by
    simp [compression, wz2PaperLongitudinalCompression,
      hhistoricalSecond_two] <;> linarith
  have hscale_angle :
      ∀ (first second : Point3) (firstScale secondScale : ℝ),
        0 < firstScale → 0 < secondScale →
          angle (firstScale • first) (secondScale • second) =
            angle first second := by
    intro first second firstScale secondScale
      hfirstScale hsecondScale
    rw [angle_smul_left_of_pos first (secondScale • second)
      hfirstScale]
    exact angle_smul_right_of_pos first second hsecondScale
  have hsource_angle :
      angle historicalFirst historicalSecond =
        angle projectiveFirst projectiveSecond := by
    have hfirstScale : 0 < (historicalFirst 2)⁻¹ :=
      inv_pos.mpr hhistoricalFirst_two
    have hsecondScale : 0 < (historicalSecond 2)⁻¹ :=
      inv_pos.mpr hhistoricalSecond_two
    have hscaled :=
      hscale_angle historicalFirst historicalSecond
        (historicalFirst 2)⁻¹ (historicalSecond 2)⁻¹
        hfirstScale hsecondScale
    exact hscaled.symm
  have hprojective_angle :
      angle projectiveFirst projectiveSecond =
        angle (transverseFirst + e3)
          (transverseSecond + e3) := by
    rw [hprojectiveFirst, hprojectiveSecond]
  have hcore :
      angle (transverseFirst + e3) (transverseSecond + e3) ≤
        angle ((100 : ℝ) • transverseFirst + e3)
          ((100 : ℝ) • transverseSecond + e3) :=
    longitudinalCompression_coreAngleInequality
      htransverseFirst_two htransverseSecond_two
      hfirst_bound hsecond_bound
  have hcompressedProjectiveFirst :
      wz1PaperProjectiveDirection
          (compression historicalFirst) =
        (100 : ℝ) • transverseFirst + e3 := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [projectiveFirst, transverseFirst, transversePart_coord0,
        transversePart_coord1, transversePart_coord2,
        wz1PaperProjectiveDirection, compression,
        wz2PaperLongitudinalCompression, e3, PiLp.add_apply,
        PiLp.smul_apply, smul_eq_mul] <;>
      field_simp [hhistoricalFirst_two.ne'] <;>
      ring
  have hcompressedProjectiveSecond :
      wz1PaperProjectiveDirection
          (compression historicalSecond) =
        (100 : ℝ) • transverseSecond + e3 := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [projectiveSecond, transverseSecond, transversePart_coord0,
        transversePart_coord1, transversePart_coord2,
        wz1PaperProjectiveDirection, compression,
        wz2PaperLongitudinalCompression, e3, PiLp.add_apply,
        PiLp.smul_apply, smul_eq_mul] <;>
      field_simp [hhistoricalSecond_two.ne'] <;>
      ring
  have hcompressedProjective_angle :
      angle ((100 : ℝ) • transverseFirst + e3)
          ((100 : ℝ) • transverseSecond + e3) =
        angle
          (wz1PaperProjectiveDirection
            (compression historicalFirst))
          (wz1PaperProjectiveDirection
            (compression historicalSecond)) := by
    rw [hcompressedProjectiveFirst, hcompressedProjectiveSecond]
  have hcompression_angle :
      angle
          (wz1PaperProjectiveDirection
            (compression historicalFirst))
          (wz1PaperProjectiveDirection
            (compression historicalSecond)) =
        angle (compression historicalFirst)
          (compression historicalSecond) := by
    exact
      hscale_angle
        (compression historicalFirst)
        (compression historicalSecond)
        ((compression historicalFirst) 2)⁻¹
        ((compression historicalSecond) 2)⁻¹
        (inv_pos.mpr hcompressionFirst_two)
        (inv_pos.mpr hcompressionSecond_two)
  have hliteral_angle :
      angle (compression historicalFirst)
          (compression historicalSecond) =
        angle literalFirst literalSecond := by
    rw [hliteralFirst_eq, hliteralSecond_eq]
    have hfirst_norm_pos :
        0 < ‖compression historicalFirst‖ :=
      norm_pos_iff.mpr hcompressionFirst_ne
    have hsecond_norm_pos :
        0 < ‖compression historicalSecond‖ :=
      norm_pos_iff.mpr hcompressionSecond_ne
    have hnormalizeFirst :
        NormedSpace.normalize
            (compression historicalFirst) =
          (‖compression historicalFirst‖)⁻¹ •
            compression historicalFirst := by
      have hnorm :
          ‖compression historicalFirst‖ •
              NormedSpace.normalize (compression historicalFirst) =
            compression historicalFirst :=
        NormedSpace.norm_smul_normalize
          (compression historicalFirst)
      have hscaled :
          (‖compression historicalFirst‖)⁻¹ •
              (‖compression historicalFirst‖ •
                NormedSpace.normalize
                  (compression historicalFirst)) =
            (‖compression historicalFirst‖)⁻¹ •
              compression historicalFirst := by
        rw [hnorm]
      have hcancel :
          (‖compression historicalFirst‖)⁻¹ •
              (‖compression historicalFirst‖ •
                NormedSpace.normalize
                  (compression historicalFirst)) =
            NormedSpace.normalize
              (compression historicalFirst) := by
        rw [smul_smul]
        have hcoefficient :
            (‖compression historicalFirst‖)⁻¹ *
                ‖compression historicalFirst‖ =
              1 := by
          field_simp [hfirst_norm_pos.ne'] <;> ring
        rw [hcoefficient, one_smul]
      rw [hcancel] at hscaled
      exact hscaled.symm
    have hnormalizeSecond :
        NormedSpace.normalize
            (compression historicalSecond) =
          (‖compression historicalSecond‖)⁻¹ •
            compression historicalSecond := by
      have hnorm :
          ‖compression historicalSecond‖ •
              NormedSpace.normalize (compression historicalSecond) =
            compression historicalSecond :=
        NormedSpace.norm_smul_normalize
          (compression historicalSecond)
      have hscaled :
          (‖compression historicalSecond‖)⁻¹ •
              (‖compression historicalSecond‖ •
                NormedSpace.normalize
                  (compression historicalSecond)) =
            (‖compression historicalSecond‖)⁻¹ •
              compression historicalSecond := by
        rw [hnorm]
      have hcancel :
          (‖compression historicalSecond‖)⁻¹ •
              (‖compression historicalSecond‖ •
                NormedSpace.normalize
                  (compression historicalSecond)) =
            NormedSpace.normalize
              (compression historicalSecond) := by
        rw [smul_smul]
        have hcoefficient :
            (‖compression historicalSecond‖)⁻¹ *
                ‖compression historicalSecond‖ =
              1 := by
          field_simp [hsecond_norm_pos.ne'] <;> ring
        rw [hcoefficient, one_smul]
      rw [hcancel] at hscaled
      exact hscaled.symm
    rw [hnormalizeFirst, hnormalizeSecond]
    exact
      (hscale_angle
        (compression historicalFirst)
        (compression historicalSecond)
        (‖compression historicalFirst‖)⁻¹
        (‖compression historicalSecond‖)⁻¹
        (inv_pos.mpr hfirst_norm_pos)
        (inv_pos.mpr hsecond_norm_pos)).symm
  calc
    angle historicalFirst historicalSecond =
        angle projectiveFirst projectiveSecond :=
      hsource_angle
    _ =
        angle (transverseFirst + e3)
          (transverseSecond + e3) :=
      hprojective_angle
    _ ≤
        angle ((100 : ℝ) • transverseFirst + e3)
          ((100 : ℝ) • transverseSecond + e3) :=
      hcore
    _ =
        angle
          (wz1PaperProjectiveDirection
            (compression historicalFirst))
          (wz1PaperProjectiveDirection
            (compression historicalSecond)) :=
      hcompressedProjective_angle
    _ =
        angle (compression historicalFirst)
          (compression historicalSecond) :=
      hcompression_angle
    _ = angle literalFirst literalSecond := hliteral_angle

end Kakeya.Assouad

end
