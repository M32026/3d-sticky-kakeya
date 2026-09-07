module

/-
  WideCenterLine — Center-line geometry for carrier transfer (Kcarrier=9).

  Provides:
  1. `wideCenterLine j T`: AffineLine at center of canonicalWideCarrier
  2. `wide_incidence_to_9δ`: wide incidence at δ → center-line incidence at 9δ
  3. `offset_bound_from_incidence`: incidence to B(0,1) gives offset norm ≤ 1+4δ
  4. `ncover_image_le`: Ncover(9δ, center image) ≤ Ncover(δ, dyadic family)

  Mathematical route:
  - canonicalWideCarrier is a 3δ strip translated by (-1/2,-1/2)
  - Center line has slope T.slope, intercept T.intercept + T.slope/2 - 1/2
  - Any point in carrier is within 3δ of center line (vertical residual)
  - cthickening δ of carrier ⊆ cthickening 4δ of center line ⊆ cthickening 9δ
  - Lipschitz via affine offset norm: exact offsetVec distance formula cancels
    the √(1+m²) factor, giving constant C+3/2 where C bounds ‖offset‖
  - Incidence to p ∈ B(0,1) gives ‖offset‖ = dist(0,centerLine) ≤ 1+4δ
  - For δ ≤ 1/2, C ≤ 3, Lipschitz constant ≤ 9/2
  - Internal 2δ-cover maps to 9δ-cover of image; coveringNumber(2δ) ≤ externalCoveringNumber(δ)

  Whiteprint: combining_theorem_rework / wide_center_line
  Dependencies: DyadicCardToNcover, DyadicToAffineAdapters, UniformIncidenceData
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicToAffineAdapters
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformIncidenceData
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace WideCenterLine

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheoremRework
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence
open DyadicCardToNcover
open DyadicToAffineAdapters

abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- ============================================================================
-- Exact offsetVec distance formula
-- ============================================================================

/-- Exact formula for the distance between offsetVec at two slopes. -/
lemma offsetVec_diff_exact (m1 m2 : ℝ) :
    ‖offsetVec m1 - offsetVec m2‖ =
      |m1 - m2| / Real.sqrt ((1 + m1^2) * (1 + m2^2)) := by
  have h1 : ‖offsetVec m1 - offsetVec m2‖ ^ 2 =
      (m1 - m2)^2 / ((1 + m1^2) * (1 + m2^2)) := by
    simp [offsetVec, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
         TubesAndSlopes.mkPlane_apply0, TubesAndSlopes.mkPlane_apply1]
    <;> field_simp <;> ring
  have h2 : 0 ≤ ‖offsetVec m1 - offsetVec m2‖ := by positivity
  have h3 : 0 ≤ (1 + m1^2) * (1 + m2^2) := by positivity
  have h41 : 0 ≤ ‖offsetVec m1 - offsetVec m2‖ := by positivity
  have h4 : Real.sqrt (‖offsetVec m1 - offsetVec m2‖ ^ 2) = ‖offsetVec m1 - offsetVec m2‖ := by
    rw [Real.sqrt_sq h41]
  have h51 : Real.sqrt ((m1 - m2)^2 / ((1 + m1^2) * (1 + m2^2))) =
      Real.sqrt ((m1 - m2)^2) / Real.sqrt ((1 + m1^2) * (1 + m2^2)) := by
    rw [Real.sqrt_div (by positivity)]
  have h52 : Real.sqrt ((m1 - m2)^2) = |m1 - m2| := by
    rw [Real.sqrt_sq_eq_abs]
  have h5 : Real.sqrt ((m1 - m2)^2 / ((1 + m1^2) * (1 + m2^2))) =
      |m1 - m2| / Real.sqrt ((1 + m1^2) * (1 + m2^2)) := by
    rw [h51, h52] <;> rfl
  have h7 : Real.sqrt (‖offsetVec m1 - offsetVec m2‖ ^ 2) =
      Real.sqrt ((m1 - m2)^2 / ((1 + m1^2) * (1 + m2^2))) := by
    rw [h1]
  rw [h4] at h7
  rw [h5] at h7
  exact h7

-- ============================================================================
-- Offset difference bound using affine offset norm
-- ============================================================================

/-- Offset difference bound using the affine offset norm instead of raw intercept.

    If `‖b2 • offsetVec m2‖ ≤ C`, then the offset difference is bounded by
    `|b1 - b2| + C * |m1 - m2|`. -/
lemma offset_diff_with_bound (m1 m2 b1 b2 C : ℝ)
    (h_off2 : ‖b2 • offsetVec m2‖ ≤ C) :
    ‖b1 • offsetVec m1 - b2 • offsetVec m2‖ ≤
      |b1 - b2| + C * |m1 - m2| := by
  have hC_nonneg : 0 ≤ C := by
    have h : 0 ≤ ‖b2 • offsetVec m2‖ := by positivity
    linarith
  have h_alg : b1 • offsetVec m1 - b2 • offsetVec m2 =
      (b1 - b2) • offsetVec m1 + b2 • (offsetVec m1 - offsetVec m2) := by
    simp [sub_smul, smul_sub] <;> abel
  rw [h_alg]
  have h1 : ‖offsetVec m1‖ ≤ 1 := by
    rw [offsetVec_norm m1]
    have h2 : 1 ≤ Real.sqrt (1 + m1^2) := by
      have h3 : 1 ≤ 1 + m1^2 := by nlinarith
      have h4 : Real.sqrt 1 ≤ Real.sqrt (1 + m1^2) := Real.sqrt_le_sqrt h3
      simpa using h4
    have h5 : 0 < Real.sqrt (1 + m1^2) := by positivity
    exact (div_le_one h5).mpr h2
  have h_exact : ‖offsetVec m1 - offsetVec m2‖ =
      |m1 - m2| / Real.sqrt ((1 + m1^2) * (1 + m2^2)) :=
    offsetVec_diff_exact m1 m2
  have h_b2_norm : ‖b2 • offsetVec m2‖ = |b2| / Real.sqrt (1 + m2^2) := by
    rw [norm_smul, offsetVec_norm m2]
    have h : ‖b2‖ = |b2| := by exact Real.norm_eq_abs b2
    rw [h] <;> ring
  have h_b2 : |b2| / Real.sqrt (1 + m2^2) ≤ C := by
    rw [←h_b2_norm]; exact h_off2
  have h_sqrt_mul : Real.sqrt ((1 + m1^2) * (1 + m2^2)) =
      Real.sqrt (1 + m1^2) * Real.sqrt (1 + m2^2) := by
    rw [Real.sqrt_mul] <;> positivity
  have h5 : |b2| * ‖offsetVec m1 - offsetVec m2‖ ≤ C * |m1 - m2| := by
    rw [h_exact, h_sqrt_mul]
    have h6 : |b2| * (|m1 - m2| / (Real.sqrt (1 + m1^2) * Real.sqrt (1 + m2^2))) =
        (|b2| / Real.sqrt (1 + m2^2)) * (|m1 - m2| / Real.sqrt (1 + m1^2)) := by ring
    rw [h6]
    have h71 : 0 ≤ |m1 - m2| / Real.sqrt (1 + m1^2) := by positivity
    have h7 : (|b2| / Real.sqrt (1 + m2^2)) * (|m1 - m2| / Real.sqrt (1 + m1^2)) ≤
        C * (|m1 - m2| / Real.sqrt (1 + m1^2)) := by
      exact mul_le_mul_of_nonneg_right h_b2 h71
    have h8 : 1 ≤ Real.sqrt (1 + m1^2) := by
      have h9 : 1 ≤ 1 + m1^2 := by nlinarith
      have h10 := Real.sqrt_le_sqrt h9
      simpa using h10
    have h9 : |m1 - m2| / Real.sqrt (1 + m1^2) ≤ |m1 - m2| := by
      have h10 : 0 ≤ |m1 - m2| := by positivity
      exact div_le_self h10 h8
    have h11 : C * (|m1 - m2| / Real.sqrt (1 + m1^2)) ≤ C * |m1 - m2| := by
      gcongr <;> exact h9
    exact le_trans h7 h11
  calc
    ‖(b1 - b2) • offsetVec m1 + b2 • (offsetVec m1 - offsetVec m2)‖
      ≤ ‖(b1 - b2) • offsetVec m1‖ + ‖b2 • (offsetVec m1 - offsetVec m2)‖ := norm_add_le _ _
    _ = |b1 - b2| * ‖offsetVec m1‖ + |b2| * ‖offsetVec m1 - offsetVec m2‖ := by
        rw [norm_smul, norm_smul] <;> rfl
    _ ≤ |b1 - b2| * 1 + C * |m1 - m2| := by gcongr <;> linarith
    _ = |b1 - b2| + C * |m1 - m2| := by ring

-- ============================================================================
-- wideCenterLine definition and Lipschitz
-- ============================================================================

/-- Center line of the canonical wide carrier for DyadicTube T.

    The canonicalWideCarrier is the strip |y - mx - b| ≤ 3δ translated by (-1/2,-1/2).
    Its center line has slope m and intercept b + m/2 - 1/2. -/
noncomputable def wideCenterLine (j : ℕ) (T : DyadicTube j) : AffineLine :=
  lineOfSlopeIntercept T.slope (T.intercept + T.slope / 2 - 1 / 2)

/-- wideCenterLine is Lipschitz on families with bounded affine offset norm.

    If every tube in the family has `‖(wideCenterLine j T).offset‖ ≤ C`,
    then the map is `(C + 3/2)`-Lipschitz from DyadicTube L1 metric to AffineLine. -/
lemma wideCenterLine_lipschitz_on_offset {j : ℕ} {T1 T2 : DyadicTube j}
    (C : ℝ) (hC1 : ‖(wideCenterLine j T1).offset‖ ≤ C)
    (hC2 : ‖(wideCenterLine j T2).offset‖ ≤ C) :
    dist (wideCenterLine j T1) (wideCenterLine j T2) ≤ (C + 3 / 2) * dist T1 T2 := by
  set m1 := T1.slope with hm1_def
  set m2 := T2.slope with hm2_def
  set b1 := T1.intercept + T1.slope / 2 - 1 / 2 with hb1_def
  set b2 := T2.intercept + T2.slope / 2 - 1 / 2 with hb2_def
  set ℓ1 := wideCenterLine j T1 with hℓ1
  set ℓ2 := wideCenterLine j T2 with hℓ2

  have h_dir_eq1 : ℓ1.1.direction = Submodule.span ℝ {tubeDirV m1} := by
    rw [hℓ1, wideCenterLine]; exact lineOfSlopeIntercept_direction m1 b1
  have h_dir_eq2 : ℓ2.1.direction = Submodule.span ℝ {tubeDirV m2} := by
    rw [hℓ2, wideCenterLine]; exact lineOfSlopeIntercept_direction m2 b2

  have h_proj_le : ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ ≤ |m1 - m2| := by
    rw [h_dir_eq1, h_dir_eq2]
    exact proj_op_norm_bound m1 m2

  have h_off1 : ℓ1.offset = b1 • offsetVec m1 := by
    rw [hℓ1, wideCenterLine]; exact offset_formula m1 b1
  have h_off2 : ℓ2.offset = b2 • offsetVec m2 := by
    rw [hℓ2, wideCenterLine]; exact offset_formula m2 b2

  have hC2' : ‖b2 • offsetVec m2‖ ≤ C := by
    rw [←h_off2]
    exact hC2
  have h_off_le : ‖ℓ1.offset - ℓ2.offset‖ ≤ |b1 - b2| + C * |m1 - m2| := by
    rw [h_off1, h_off2]
    exact offset_diff_with_bound m1 m2 b1 b2 C hC2'

  have h_def : dist ℓ1 ℓ2 =
      ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ +
      ‖ℓ1.offset - ℓ2.offset‖ := by rfl

  have h_b_diff : |b1 - b2| ≤ |T1.intercept - T2.intercept| + |T1.slope - T2.slope| / 2 := by
    have h_eq : b1 - b2 = (T1.intercept - T2.intercept) + (T1.slope - T2.slope) / 2 := by
      simp [hb1_def, hb2_def] <;> ring
    rw [h_eq]
    have h2 : |(T1.intercept - T2.intercept) + (T1.slope - T2.slope) / 2| ≤
        |T1.intercept - T2.intercept| + |(T1.slope - T2.slope) / 2| := abs_add_le _ _
    have h3 : |(T1.slope - T2.slope) / 2| = |T1.slope - T2.slope| / 2 := by
      rw [abs_div] <;> norm_num
    rw [h3] at h2
    exact h2

  rw [h_def]
  calc
    ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ + ‖ℓ1.offset - ℓ2.offset‖
      ≤ |m1 - m2| + (|b1 - b2| + C * |m1 - m2|) := by linarith
    _ = (C + 1) * |m1 - m2| + |b1 - b2| := by ring
    _ ≤ (C + 1) * |T1.slope - T2.slope| +
        (|T1.intercept - T2.intercept| + |T1.slope - T2.slope| / 2) := by
          have h10 : |m1 - m2| = |T1.slope - T2.slope| := by simp [hm1_def, hm2_def]
          rw [h10]
          linarith [h_b_diff]
    _ = (C + 3 / 2) * |T1.slope - T2.slope| + |T1.intercept - T2.intercept| := by ring
    _ ≤ (C + 3 / 2) * (|T1.slope - T2.slope| + |T1.intercept - T2.intercept|) := by
      have h5 : (1 : ℝ) ≤ C + 3 / 2 := by linarith [norm_nonneg (ℓ2.offset)]
      have h6 : 0 ≤ |T1.intercept - T2.intercept| := by positivity
      have h7 : |T1.intercept - T2.intercept| ≤ (C + 3 / 2) * |T1.intercept - T2.intercept| := by
        calc
          |T1.intercept - T2.intercept|
            = 1 * |T1.intercept - T2.intercept| := by ring
          _ ≤ (C + 3 / 2) * |T1.intercept - T2.intercept| := by
            exact mul_le_mul_of_nonneg_right h5 h6
      linarith
    _ = (C + 3 / 2) * dist T1 T2 := by rfl

-- ============================================================================
-- Carrier to center-line incidence
-- ============================================================================

/-- Every point in canonicalWideCarrier is within 3δ of wideCenterLine. -/
lemma carrier_subset_cthickening_center {j : ℕ} {T : DyadicTube j} :
    canonicalWideCarrier j T ⊆
      Metric.cthickening (3 * dyadicDelta j) ((wideCenterLine j T).1 : Set Plane) := by
  intro q hq
  rcases hq with ⟨p, hp_strip, rfl⟩
  set δ := dyadicDelta j with hδ
  set m := T.slope with hm
  set b' := T.intercept + T.slope / 2 - 1 / 2 with hb'
  set v : Plane := WithLp.toLp (2 : ENNReal) fun _ : Fin 2 => -1 / 2 with hv
  set q' : Plane := p + v with hq'
  set q_line : Plane := TubesAndSlopes.mkPlane (q' 0) (m * q' 0 + b') with hq_line
  set ℓ : AffineLine := wideCenterLine j T with hℓ

  have h1 : |p 1 - m * p 0 - T.intercept| ≤ 3 * δ := hp_strip

  have hq0 : q' 0 = p 0 - 1 / 2 := by
    simp [hq', v] <;> ring
  have hq1 : q' 1 = p 1 - 1 / 2 := by
    simp [hq', v] <;> ring

  have h_res : q' 1 - m * q' 0 - b' = p 1 - m * p 0 - T.intercept := by
    simp [hq0, hq1, hb'] <;> ring

  have h_dist_eq : dist q' q_line = |q' 1 - m * q' 0 - b'| := by
    have h2 : q_line 0 = q' 0 := by
      simp [hq_line, TubesAndSlopes.mkPlane_apply0]
    have h3 : q_line 1 = m * q' 0 + b' := by
      simp [hq_line, TubesAndSlopes.mkPlane_apply1]
    have h4 : dist q' q_line = ‖q' - q_line‖ := by rfl
    rw [h4]
    have h5 : (q' - q_line) 0 = 0 := by simp [h2]
    have h6 : (q' - q_line) 1 = q' 1 - q_line 1 := by simp
    have h7 : ‖q' - q_line‖ ^ 2 = ((q' - q_line) 0)^2 + ((q' - q_line) 1)^2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
    have h8 : ‖q' - q_line‖ ^ 2 = (q' 1 - q_line 1)^2 := by
      rw [h7, h5, h6] <;> ring
    have h9 : 0 ≤ ‖q' - q_line‖ := by positivity
    have h9' : ‖q' - q_line‖ ^ 2 = |q' 1 - q_line 1| ^ 2 := by
      rw [h8, sq_abs]
    have h10 : ‖q' - q_line‖ = |q' 1 - q_line 1| := by
      have h11 : 0 ≤ ‖q' - q_line‖ := by positivity
      have h12 : 0 ≤ |q' 1 - q_line 1| := by positivity
      nlinarith
    have h_abs : |q' 1 - q_line 1| = |q' 1 - m * q' 0 - b'| := by
      rw [h3]
      have h_alg : q' 1 - (m * q' 0 + b') = q' 1 - m * q' 0 - b' := by ring
      rw [h_alg]
    rw [h10, h_abs]

  have h_dist_le : dist q' q_line ≤ 3 * δ := by
    rw [h_dist_eq, h_res]
    exact h1

  have h_on_line : q_line ∈ (ℓ.1 : Set Plane) := by
    have h : q_line - TubesAndSlopes.mkPlane 0 b' ∈
        Submodule.span ℝ {tubeDirV m} := by
      have h2 : q_line - TubesAndSlopes.mkPlane 0 b' = (q' 0) • tubeDirV m := by
        ext i
        fin_cases i
        · simp [hq_line, TubesAndSlopes.mkPlane_apply0, TubesAndSlopes.mkPlane_apply1,
                tubeDirV, smul_eq_mul] <;> ring
        · simp [hq_line, TubesAndSlopes.mkPlane_apply0, TubesAndSlopes.mkPlane_apply1,
                tubeDirV, smul_eq_mul] <;> ring
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have h_b' : b' = T.intercept + T.slope / 2 - 1 / 2 := by simp [hb']
    have h' : q_line - TubesAndSlopes.mkPlane 0 (T.intercept + T.slope / 2 - 1 / 2) ∈
        Submodule.span ℝ {tubeDirV m} := by
      have h_eq : TubesAndSlopes.mkPlane 0 (T.intercept + T.slope / 2 - 1 / 2) =
          TubesAndSlopes.mkPlane 0 b' := by rw [h_b']
      rw [h_eq]
      exact h
    have h_goal : q_line ∈ (ℓ.1 : Set Plane) := by
      simp only [hℓ, wideCenterLine, lineOfSlopeIntercept, AffineSubspace.mem_mk']
      exact h'
    exact h_goal

  have h_edist : edist q' q_line ≤ ENNReal.ofReal (3 * δ) := by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal h_dist_le
  have h_inf : Metric.infEDist q' (ℓ.1 : Set Plane) ≤ edist q' q_line :=
    Metric.infEDist_le_edist_of_mem h_on_line
  exact Metric.mem_cthickening_iff.mpr (le_trans h_inf h_edist)

/-- Wide incidence at δ → center-line incidence at 9δ.

    If p is within δ of the canonical wide carrier (3δ strip), then p is
    within 9δ of the center line. (Actual bound is 4δ; padded to 9δ.) -/
lemma wide_incidence_to_9δ {j : ℕ} {T : DyadicTube j} {p : Plane}
    (h : p ∈ Metric.cthickening (dyadicDelta j) (canonicalWideCarrier j T)) :
    p ∈ Metric.cthickening (9 * dyadicDelta j) ((wideCenterLine j T).1 : Set Plane) := by
  set δ := dyadicDelta j with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos j
  let ℓ : AffineLine := wideCenterLine j T
  have h1 : canonicalWideCarrier j T ⊆ Metric.cthickening (3 * δ) ((ℓ.1 : Set Plane)) :=
    carrier_subset_cthickening_center
  have h2 : Metric.cthickening δ (canonicalWideCarrier j T) ⊆
      Metric.cthickening δ (Metric.cthickening (3 * δ) ((ℓ.1 : Set Plane))) :=
    Metric.cthickening_subset_of_subset δ h1
  have h3 : Metric.cthickening δ (Metric.cthickening (3 * δ) ((ℓ.1 : Set Plane))) ⊆
      Metric.cthickening (δ + 3 * δ) ((ℓ.1 : Set Plane)) :=
    Metric.cthickening_cthickening_subset (by linarith [hδ_pos]) (by linarith [hδ_pos]) _
  have h4 : δ + 3 * δ = 4 * δ := by ring
  have h3' : p ∈ Metric.cthickening (4 * δ) ((ℓ.1 : Set Plane)) := by
    rw [←h4]
    exact h3 (h2 h)
  have h5 : Metric.cthickening (4 * δ) ((ℓ.1 : Set Plane)) ⊆
      Metric.cthickening (9 * δ) ((ℓ.1 : Set Plane)) := by
    intro x hx
    have h6 : Metric.infEDist x ((ℓ.1 : Set Plane)) ≤ ENNReal.ofReal (4 * δ) :=
      Metric.mem_cthickening_iff.mp hx
    have h7 : ENNReal.ofReal (4 * δ) ≤ ENNReal.ofReal (9 * δ) := by
      exact ENNReal.ofReal_le_ofReal (by linarith [hδ_pos])
    exact Metric.mem_cthickening_iff.mpr (le_trans h6 h7)
  exact h5 h3'

-- ============================================================================
-- Offset bound from incidence
-- ============================================================================

/-- Bound on affine offset norm from incidence to a bounded point.

    If `‖p‖ ≤ 1` and `p` is within δ of the canonical wide carrier, then the
    orthogonal distance from 0 to the center line is at most `1 + 4δ`.

    Proof: dist(0, centerLine) ≤ ‖p‖ + dist(p, carrier) + dist(carrier, centerLine)
    ≤ 1 + δ + 3δ = 1 + 4δ. -/
lemma offset_bound_from_incidence {j : ℕ} {T : DyadicTube j} {p : Plane}
    (hp : ‖p‖ ≤ 1)
    (h_inc : p ∈ Metric.cthickening (dyadicDelta j) (canonicalWideCarrier j T)) :
    ‖(wideCenterLine j T).offset‖ ≤ 1 + 4 * dyadicDelta j := by
  set δ := dyadicDelta j with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos j
  set ℓ := wideCenterLine j T with hℓ
  set S : Set Plane := (ℓ.1 : Set Plane) with hS

  have h1 : p ∈ Metric.cthickening (4 * δ) S := by
    have h_carrier : canonicalWideCarrier j T ⊆ Metric.cthickening (3 * δ) S :=
      carrier_subset_cthickening_center
    have h2 : Metric.cthickening δ (canonicalWideCarrier j T) ⊆
        Metric.cthickening (4 * δ) S := by
      calc Metric.cthickening δ (canonicalWideCarrier j T)
        ⊆ Metric.cthickening δ (Metric.cthickening (3 * δ) S) :=
          Metric.cthickening_subset_of_subset δ h_carrier
      _ ⊆ Metric.cthickening (δ + 3 * δ) S :=
          Metric.cthickening_cthickening_subset (by linarith [hδ_pos]) (by linarith [hδ_pos]) _
      _ = Metric.cthickening (4 * δ) S := by ring_nf
    exact h2 h_inc

  have h_p_nonneg : 0 ≤ ‖p‖ := by positivity
  have h3 : (0 : Plane) ∈ Metric.cthickening (‖p‖ + 4 * δ) S := by
    have h4 : (0 : Plane) ∈ Metric.cthickening ‖p‖ ({p} : Set Plane) := by
      simp [Metric.mem_cthickening_iff, edist_dist, h_p_nonneg]
      <;> norm_num
    have h5 : ({p} : Set Plane) ⊆ Metric.cthickening (4 * δ) S := by
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      rw [hx]
      exact h1
    have h6 : Metric.cthickening ‖p‖ ({p} : Set Plane) ⊆
        Metric.cthickening ‖p‖ (Metric.cthickening (4 * δ) S) :=
      Metric.cthickening_subset_of_subset ‖p‖ h5
    have h7 : Metric.cthickening ‖p‖ (Metric.cthickening (4 * δ) S) ⊆
        Metric.cthickening (‖p‖ + 4 * δ) S :=
      Metric.cthickening_cthickening_subset h_p_nonneg (by linarith [hδ_pos]) _
    exact h7 (h6 h4)

  have h_sum_nonneg : 0 ≤ ‖p‖ + 4 * δ := by positivity

  have h_offset_mem : ℓ.offset ∈ S := ℓ.offset_mem

  have h14 : ∀ y ∈ S, ‖ℓ.offset‖ ≤ dist (0 : Plane) y := by
    intro y hy
    have h_inf : dist (0 : Plane) ℓ.offset = Metric.infDist (0 : Plane) S :=
      EuclideanGeometry.dist_orthogonalProjection_eq_infDist ℓ.1 (0 : Plane)
    have h : dist (0 : Plane) ℓ.offset ≤ dist (0 : Plane) y := by
      rw [h_inf]
      exact Metric.infDist_le_dist_of_mem hy
    simpa [dist_eq_norm] using h

  have h15 : ENNReal.ofReal ‖ℓ.offset‖ ≤ Metric.infEDist (0 : Plane) S := by
    have h_nonempty : (edist (0 : Plane) '' S).Nonempty := by
      refine' ⟨edist (0 : Plane) ℓ.offset, _⟩
      exact ⟨ℓ.offset, h_offset_mem, rfl⟩
    have h_lower : ∀ z ∈ (edist (0 : Plane) '' S), ENNReal.ofReal ‖ℓ.offset‖ ≤ z := by
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (h14 y hy)
    have h : ENNReal.ofReal ‖ℓ.offset‖ ≤ sInf (edist (0 : Plane) '' S) := le_csInf h_nonempty h_lower
    simpa [Metric.infEDist] using h

  have h16 : Metric.infEDist (0 : Plane) S ≤ ENNReal.ofReal ‖ℓ.offset‖ := by
    have h161 : Metric.infEDist (0 : Plane) S ≤ edist (0 : Plane) ℓ.offset :=
      Metric.infEDist_le_edist_of_mem h_offset_mem
    have h162 : edist (0 : Plane) ℓ.offset = ENNReal.ofReal ‖ℓ.offset‖ := by
      have h_dist : dist (0 : Plane) ℓ.offset = ‖ℓ.offset‖ := by
        simp [dist_eq_norm]
      rw [edist_dist, h_dist]
    rw [h162] at h161
    exact h161

  have h17 : Metric.infEDist (0 : Plane) S = ENNReal.ofReal ‖ℓ.offset‖ :=
    le_antisymm h16 h15

  have h10 : Metric.infEDist (0 : Plane) S ≤ ENNReal.ofReal (‖p‖ + 4 * δ) :=
    Metric.mem_cthickening_iff.mp h3

  rw [h17] at h10
  have h18 : ‖ℓ.offset‖ ≤ ‖p‖ + 4 * δ :=
    (ENNReal.ofReal_le_ofReal_iff h_sum_nonneg).mp h10
  linarith [hp]

/-- Offset bound ≤ 3 when δ ≤ 1/2. -/
lemma offset_bound_le_3 {j : ℕ} {T : DyadicTube j} {p : Plane}
    (hp : ‖p‖ ≤ 1) (hδ : dyadicDelta j ≤ 1 / 2)
    (h_inc : p ∈ Metric.cthickening (dyadicDelta j) (canonicalWideCarrier j T)) :
    ‖(wideCenterLine j T).offset‖ ≤ 3 := by
  have h := offset_bound_from_incidence hp h_inc
  linarith [hδ]

-- ============================================================================
-- Ncover comparison
-- ============================================================================

/-- Ncover comparison: Ncover(9δ, wideCenterLine image) ≤ Ncover(δ, original family).

    Requires uniform offset norm bound ≤ 3 on the family. This follows from
    incidence to P ⊆ B(0,1) when δ ≤ 1/2 (see `ncover_image_le_of_incidence`).

    Uses wideCenterLine Lipschitz constant 9/2 on offset-bounded families:
    an internal 2δ-cover maps to a 9δ-cover of the image. -/
lemma ncover_image_le {j : ℕ} {F : Set (DyadicTube j)}
    (h_offset : ∀ T ∈ F, ‖(wideCenterLine j T).offset‖ ≤ 3) :
    Ncover (9 * dyadicDelta j) (wideCenterLine j '' F) ≤
      Ncover (dyadicDelta j) F := by
  set δ := dyadicDelta j with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos j
  set δnn : NNReal := δ.toNNReal with hδnn

  have h_lip_on : ∀ (T1 T2 : DyadicTube j), T1 ∈ F → T2 ∈ F →
      dist (wideCenterLine j T1) (wideCenterLine j T2) ≤ (9 / 2 : ℝ) * dist T1 T2 := by
    intro T1 T2 hT1 hT2
    have h := wideCenterLine_lipschitz_on_offset 3 (h_offset T1 hT1) (h_offset T2 hT2)
    have h9 : (3 + 3 / 2 : ℝ) = (9 / 2 : ℝ) := by norm_num
    rw [h9] at h
    exact h

  have h_main : ∀ (C : Set (DyadicTube j)), C ⊆ F →
      Metric.IsCover (2 * δnn) F C →
      Metric.externalCoveringNumber (9 * δnn) (wideCenterLine j '' F) ≤ C.encard := by
    intro C hC_sub hcover
    have h_image_cover : Metric.IsCover (9 * δnn) (wideCenterLine j '' F) (wideCenterLine j '' C) := by
      intro y hy
      rcases hy with ⟨T, hT, rfl⟩
      have hT_in_C : ∃ c ∈ C, dist T c ≤ 2 * δ := by
        have h := hcover hT
        rcases h with ⟨c, hc, hedist⟩
        have h_coe : (↑(2 * δnn) : ENNReal) = ENNReal.ofReal (2 * δ) := by
          simp [hδnn, NNReal.coe_mk] <;> norm_cast
        have h_edist_eq : edist T c = ENNReal.ofReal (dist T c) := by
          rw [edist_dist]
        have h1 : edist T c ≤ ENNReal.ofReal (2 * δ) := by
          exact le_trans hedist (le_of_eq h_coe)
        have h2 : 0 ≤ 2 * δ := by positivity
        have h3 : dist T c ≤ 2 * δ := by
          have h4 : ENNReal.ofReal (dist T c) ≤ ENNReal.ofReal (2 * δ) := by
            rw [h_edist_eq] at h1
            exact h1
          exact (ENNReal.ofReal_le_ofReal_iff h2).mp h4
        exact ⟨c, hc, h3⟩
      rcases hT_in_C with ⟨c, hc, hdist⟩
      have hc_in_F : c ∈ F := hC_sub hc
      have hdist' : dist (wideCenterLine j T) (wideCenterLine j c) ≤ (9 / 2 : ℝ) * (2 * δ) :=
        h_lip_on T c hT hc_in_F |>.trans (by gcongr)
      have h9 : (9 / 2 : ℝ) * (2 * δ) = 9 * δ := by ring
      rw [h9] at hdist'
      have h_edist : edist (wideCenterLine j T) (wideCenterLine j c) ≤ (9 * δnn : ENNReal) := by
        have h_eq : (9 * δnn : ENNReal) = ENNReal.ofReal (9 * δ) := by
          simp [hδnn, NNReal.coe_mk] <;> norm_cast
        rw [h_eq]
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal hdist'
      exact ⟨wideCenterLine j c, ⟨c, hc, rfl⟩, h_edist⟩
    have h1 : Metric.externalCoveringNumber (9 * δnn) (wideCenterLine j '' F) ≤
        (wideCenterLine j '' C).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard h_image_cover
    have h2 : (wideCenterLine j '' C).encard ≤ C.encard := by
      exact Set.encard_image_le (wideCenterLine j) C
    exact le_trans h1 h2

  have h_cover2 : Metric.coveringNumber (2 * δnn) F ≤
      Metric.externalCoveringNumber δnn F :=
    Metric.coveringNumber_two_mul_le_externalCoveringNumber δnn F

  have h_final : Metric.externalCoveringNumber (9 * δnn) (wideCenterLine j '' F) ≤
      Metric.coveringNumber (2 * δnn) F := by
    dsimp only [Metric.coveringNumber]
    apply le_iInf
    intro C
    apply le_iInf
    intro hC_sub
    apply le_iInf
    intro hcover
    exact h_main C hC_sub hcover

  have h_goal : Metric.externalCoveringNumber (9 * δnn) (wideCenterLine j '' F) ≤
      Metric.externalCoveringNumber δnn F :=
    le_trans h_final h_cover2

  have h9δ : (9 * δ).toNNReal = 9 * δnn := by
    apply NNReal.coe_injective
    have h1 : ((9 * δ).toNNReal : ℝ) = 9 * δ := by
      have hpos : 0 ≤ 9 * δ := by linarith [hδ_pos]
      exact Real.coe_toNNReal (9 * δ) hpos
    have h2 : ((9 * δnn : NNReal) : ℝ) = 9 * δ := by
      simp [hδnn] <;> norm_cast <;> linarith
    rw [h1, h2]
  simpa [Ncover, h9δ] using h_goal

/-- Ncover comparison from incidence to a bounded point set.

    If every tube in F is incident to some point in P ⊆ B(0,1) and δ ≤ 1/2,
    then Ncover(9δ, wideCenterLine image) ≤ Ncover(δ, F). -/
lemma ncover_image_le_of_incidence {j : ℕ} {F : Set (DyadicTube j)}
    {P : Set Plane} (hP : P ⊆ Metric.closedBall 0 1)
    (hδ : dyadicDelta j ≤ 1 / 2)
    (h_inc : ∀ T ∈ F, ∃ p ∈ P,
      p ∈ Metric.cthickening (dyadicDelta j) (canonicalWideCarrier j T)) :
    Ncover (9 * dyadicDelta j) (wideCenterLine j '' F) ≤
      Ncover (dyadicDelta j) F := by
  have h_offset : ∀ T ∈ F, ‖(wideCenterLine j T).offset‖ ≤ 3 := by
    intro T hT
    rcases h_inc T hT with ⟨p, hpP, hp_inc⟩
    have hp_ball : ‖p‖ ≤ 1 := by
      have h : p ∈ Metric.closedBall (0 : Plane) 1 := hP hpP
      simpa [Metric.mem_closedBall] using h
    exact offset_bound_le_3 hp_ball hδ hp_inc
  exact ncover_image_le h_offset

end WideCenterLine

end
