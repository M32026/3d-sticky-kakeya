module

/-
  Adapter: transfer IsDeltaSSet from DyadicTube family to wideToAffineLine image
  at scale 9*δ.

  Direct proof at 9δ (avoids needing AffineLine doubling property).

  Key insight: wideToAffineLine differs from toAffineLine by an intercept shift
  b' = m/2 + b - 1/2. We relate dist(wide) to dist(orig):
    dist(orig) ≤ 4 * dist(wide)
  Then use existing toAffineLine_co_lipschitz (constant 22):
    paramDistLinf ≤ 22 * dist(orig) ≤ 88 * dist(wide)

  Proof chain:
    IsDeltaSSet δ s C F
    → DiscreteFrostmanL1 s (5C) F
    → IsFiniteTubeSSet s (max 1 (10C)) F
    → IsDeltaSSet (9δ) s (K_out) (wideToAffineLine '' F)

  Whiteprint node: carrier_transfer / tube_sset_adapter
  Dependencies: Bridge_SSetTransfer, DyadicCardToNcover, DyadicToAffineAdapters
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicToAffineAdapters
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge_SSetTransfer
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate

open DirecretisedFurstenbergEstimate
open DyadicCardToNcover
open DyadicToAffineAdapters
open DiscretisedFurstenbergEstimate.InductionOnScales

variable {n : ℕ}

/-- Map a DyadicTube to the affine line at the center of canonicalWideCarrier. -/
noncomputable def wideToAffineLine {n : ℕ} (T : DyadicTube n) : AffineLine :=
  lineOfSlopeIntercept T.slope (T.slope / 2 + T.intercept - 1 / 2)

/-- The wide intercept: b' = m/2 + b - 1/2. -/
def wideIntercept (m b : ℝ) : ℝ := m / 2 + b - 1 / 2

lemma wideIntercept_bound {m b : ℝ} (hm : |m| ≤ 1) (hb : |b| ≤ 3) :
    |wideIntercept m b| ≤ 4 := by
  dsimp only [wideIntercept]
  have h1 : |m / 2 + b - 1 / 2| ≤ |m / 2| + |b| + 1 / 2 := by
    have h2 : |m / 2 + b - 1 / 2| ≤ |m / 2 + b| + 1 / 2 := by
      have h3 : |m / 2 + b - 1 / 2| = |(m / 2 + b) + (-1 / 2 : ℝ)| := by ring_nf
      rw [h3]
      have h4 : |(m / 2 + b) + (-1 / 2 : ℝ)| ≤ |m / 2 + b| + |(-1 / 2 : ℝ)| := abs_add_le _ _
      have h5 : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num
      rw [h5] at h4
      exact h4
    have h5 : |m / 2 + b| ≤ |m / 2| + |b| := abs_add_le _ _
    linarith
  have h6 : |m / 2| = |m| / 2 := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  rw [h6] at h1
  linarith [hm, hb]

/-- Offset formula for wideToAffineLine. -/
lemma wideToAffineLine_offset (T : DyadicTube n) :
    (wideToAffineLine T).offset =
      (wideIntercept T.slope T.intercept) • offsetVec T.slope := by
  have h : wideToAffineLine T = lineOfSlopeIntercept T.slope (wideIntercept T.slope T.intercept) := by
    rfl
  rw [h]
  exact offset_formula T.slope (wideIntercept T.slope T.intercept)

-- ============================================================================
-- Co-Lipschitz bound for wideToAffineLine (constant 88)
--
-- Strategy: relate dist(wide) to dist(orig), then use toAffineLine_co_lipschitz.
-- dist(orig) ≤ 4 * dist(wide), so paramDistLinf ≤ 22 * 4 * dist(wide) = 88.
-- ============================================================================

lemma wideToAffineLine_co_lipschitz (T1 T2 : DyadicTube n)
    (hm1 : |T1.slope| ≤ 1) (hm2 : |T2.slope| ≤ 1)
    (hb2 : |T2.intercept| ≤ 3) :
    paramDistLinf T1 T2 ≤ 88 * dist (wideToAffineLine T1) (wideToAffineLine T2) := by
  set m1 := T1.slope with hm1_def
  set m2 := T2.slope with hm2_def
  set b1 := T1.intercept with hb1_def
  set b2 := T2.intercept with hb2_def
  set b1' := wideIntercept m1 b1 with hb1'_def
  set b2' := wideIntercept m2 b2 with hb2'_def
  set ℓ1 := wideToAffineLine T1 with hℓ1
  set ℓ2 := wideToAffineLine T2 with hℓ2
  set o1 := toAffineLine T1 with ho1
  set o2 := toAffineLine T2 with ho2

  -- Direction projections are the same (same slopes)
  have h_dir_same : ℓ1.1.direction.starProjection = o1.1.direction.starProjection := by
    have h1 : ℓ1.1.direction = Submodule.span ℝ {tubeDirV m1} := by
      rw [hℓ1]; exact lineOfSlopeIntercept_direction m1 b1'
    have h2 : o1.1.direction = Submodule.span ℝ {tubeDirV m1} := by
      rw [ho1]; exact lineOfSlopeIntercept_direction m1 b1
    rw [h1, h2]
  have h_dir_same2 : ℓ2.1.direction.starProjection = o2.1.direction.starProjection := by
    have h1 : ℓ2.1.direction = Submodule.span ℝ {tubeDirV m2} := by
      rw [hℓ2]; exact lineOfSlopeIntercept_direction m2 b2'
    have h2 : o2.1.direction = Submodule.span ℝ {tubeDirV m2} := by
      rw [ho2]; exact lineOfSlopeIntercept_direction m2 b2
    rw [h1, h2]

  have h_proj_lower : ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ ≥ |m1 - m2| / 2 := by
    have h_dir_eq1 : ℓ1.1.direction = Submodule.span ℝ {tubeDirV m1} := by
      rw [hℓ1]; exact lineOfSlopeIntercept_direction m1 b1'
    have h_dir_eq2 : ℓ2.1.direction = Submodule.span ℝ {tubeDirV m2} := by
      rw [hℓ2]; exact lineOfSlopeIntercept_direction m2 b2'
    have h : ‖(Submodule.span ℝ {tubeDirV m1}).starProjection - (Submodule.span ℝ {tubeDirV m2}).starProjection‖ ≥ |m1 - m2| / 2 :=
      proj_lower_bound_simple m1 m2 hm1 hm2
    simpa [h_dir_eq1, h_dir_eq2] using h

  -- Offset difference relation
  have h_off1_wide : ℓ1.offset = b1' • offsetVec m1 := wideToAffineLine_offset T1
  have h_off2_wide : ℓ2.offset = b2' • offsetVec m2 := wideToAffineLine_offset T2
  have h_off1_orig : o1.offset = b1 • offsetVec m1 := by
    rw [ho1]; exact offset_formula m1 b1
  have h_off2_orig : o2.offset = b2 • offsetVec m2 := by
    rw [ho2]; exact offset_formula m2 b2

  have h_db' : b1' - b2' = (b1 - b2) + (m1 - m2) / 2 := by
    dsimp only [b1', b2', wideIntercept] <;> ring
  have h_b2'_diff : b2' - b2 = m2 / 2 - 1 / 2 := by
    dsimp only [b2', wideIntercept] <;> ring
  have h_b2'_diff_bound : |b2' - b2| ≤ 1 := by
    rw [h_b2'_diff]
    have h : |m2 / 2 - 1 / 2| ≤ |m2| / 2 + 1 / 2 := by
      have h2 : |m2 / 2 - 1 / 2| ≤ |m2 / 2| + 1 / 2 := by
        have h3 : |m2 / 2 - 1 / 2| = |m2 / 2 + (-1 / 2 : ℝ)| := by ring_nf
        rw [h3]
        have h4 := abs_add_le (m2 / 2) (-1 / 2 : ℝ)
        have h5 : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num
        rw [h5] at h4
        exact h4
      have h6 : |m2 / 2| = |m2| / 2 := by
        rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      rw [h6] at h2
      exact h2
    linarith [hm2]

  let proj := ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection
  let wide_off := ℓ1.offset - ℓ2.offset
  let orig_off := o1.offset - o2.offset
  let extra := ((m1 - m2) / 2) • offsetVec m1 + (b2' - b2) • (offsetVec m1 - offsetVec m2)

  have h_extra_bound : ‖extra‖ ≤ (3 / 2 : ℝ) * |m1 - m2| := by
    have h1 : ‖extra‖ ≤ |m1 - m2| / 2 * ‖offsetVec m1‖ + |b2' - b2| * ‖offsetVec m1 - offsetVec m2‖ := by
      calc
        _ ≤ ‖((m1 - m2) / 2) • offsetVec m1‖ + ‖(b2' - b2) • (offsetVec m1 - offsetVec m2)‖ := norm_add_le _ _
        _ = |m1 - m2| / 2 * ‖offsetVec m1‖ + |b2' - b2| * ‖offsetVec m1 - offsetVec m2‖ := by
          simp [norm_smul, mul_comm, mul_left_comm] <;> ring
    have h2 : ‖offsetVec m1‖ ≤ 1 := by
      rw [offsetVec_norm m1]
      have h21 : 0 < Real.sqrt (1 + m1^2) := by positivity
      have h22 : (1 : ℝ) ≤ Real.sqrt (1 + m1^2) := by
        have h23 : (1 : ℝ) ≤ 1 + m1^2 := by nlinarith
        have h24 : Real.sqrt 1 ≤ Real.sqrt (1 + m1^2) := Real.sqrt_le_sqrt h23
        have h25 : Real.sqrt 1 = (1 : ℝ) := by norm_num
        rw [h25] at h24
        exact h24
      have h26 : 1 / Real.sqrt (1 + m1^2) ≤ 1 := by
        apply (div_le_one h21).mpr
        exact h22
      exact h26
    have h3 : ‖offsetVec m1 - offsetVec m2‖ ≤ |m1 - m2| := offsetVec_lipschitz m1 m2
    have h4 : |b2' - b2| ≤ 1 := h_b2'_diff_bound
    calc
      _ ≤ |m1 - m2| / 2 * ‖offsetVec m1‖ + |b2' - b2| * ‖offsetVec m1 - offsetVec m2‖ := h1
      _ ≤ |m1 - m2| / 2 * 1 + 1 * |m1 - m2| := by gcongr <;> linarith
      _ = (3 / 2 : ℝ) * |m1 - m2| := by ring

  have h_b1'_diff : b1' - b1 = m1 / 2 - 1 / 2 := by
    dsimp only [b1', wideIntercept] <;> ring

  have h_wide_def : wide_off = b1' • offsetVec m1 - b2' • offsetVec m2 := by
    have h : wide_off = ℓ1.offset - ℓ2.offset := by rfl
    rw [h, h_off1_wide, h_off2_wide]
  have h_orig_def : orig_off = b1 • offsetVec m1 - b2 • offsetVec m2 := by
    have h : orig_off = o1.offset - o2.offset := by rfl
    rw [h, h_off1_orig, h_off2_orig]

  have h_extra_expand : extra =
      (m1 / 2 - 1 / 2) • offsetVec m1 - (m2 / 2 - 1 / 2) • offsetVec m2 := by
    dsimp only [extra]
    rw [h_b2'_diff]
    set a := (m1 - m2) / 2 with ha_def
    set b := m2 / 2 - 1 / 2 with hb_def
    set v1 := offsetVec m1 with hv1_def
    set v2 := offsetVec m2 with hv2_def
    have h1 : b • (v1 - v2) = b • v1 - b • v2 := by rw [smul_sub]
    have h_main : a • v1 + b • (v1 - v2) = (a + b) • v1 - b • v2 := by
      calc
        a • v1 + b • (v1 - v2)
          = a • v1 + (b • v1 - b • v2) := by rw [h1]
        _ = (a • v1 + b • v1) - b • v2 := by abel
        _ = (a + b) • v1 - b • v2 := by rw [←add_smul] <;> rfl
    rw [h_main]
    have h5 : a + b = m1 / 2 - 1 / 2 := by
      simp [a, b] <;> ring
    rw [h5] <;> rfl

  have h_off_relation : ‖orig_off‖ ≤ ‖wide_off‖ + 3 * ‖proj‖ := by
    have h1 : wide_off - orig_off = extra := by
      rw [h_wide_def, h_orig_def]
      have h_lhs : (b1' • offsetVec m1 - b2' • offsetVec m2) -
          (b1 • offsetVec m1 - b2 • offsetVec m2) =
          (b1' - b1) • offsetVec m1 - (b2' - b2) • offsetVec m2 := by
        have h_sub1 : b1' • offsetVec m1 - b1 • offsetVec m1 =
            (b1' - b1) • offsetVec m1 := by rw [←sub_smul] <;> rfl
        have h_sub2 : b2' • offsetVec m2 - b2 • offsetVec m2 =
            (b2' - b2) • offsetVec m2 := by rw [←sub_smul] <;> rfl
        calc
          (b1' • offsetVec m1 - b2' • offsetVec m2) -
              (b1 • offsetVec m1 - b2 • offsetVec m2)
            = (b1' • offsetVec m1 - b1 • offsetVec m1) -
                (b2' • offsetVec m2 - b2 • offsetVec m2) := by abel
          _ = (b1' - b1) • offsetVec m1 - (b2' - b2) • offsetVec m2 := by
            rw [h_sub1, h_sub2] <;> rfl
      rw [h_lhs, h_b1'_diff, h_b2'_diff]
      exact h_extra_expand.symm
    have h2 : orig_off = wide_off - extra := by
      rw [←h1] <;> abel
    rw [h2]
    have h3 : ‖wide_off - extra‖ ≤ ‖wide_off‖ + ‖extra‖ := norm_sub_le _ _
    have h4 : |m1 - m2| ≤ 2 * ‖proj‖ := by linarith [h_proj_lower]
    calc
      _ ≤ ‖wide_off‖ + ‖extra‖ := h3
      _ ≤ ‖wide_off‖ + (3 / 2 : ℝ) * |m1 - m2| := by gcongr <;> exact h_extra_bound
      _ ≤ ‖wide_off‖ + 3 * ‖proj‖ := by linarith

  have h_dist_orig_le : dist o1 o2 ≤ 4 * dist ℓ1 ℓ2 := by
    have h_proj_eq : ‖o1.1.direction.starProjection - o2.1.direction.starProjection‖ = ‖proj‖ := by
      have h_eq1 : o1.1.direction.starProjection = ℓ1.1.direction.starProjection := h_dir_same.symm
      have h_eq2 : o2.1.direction.starProjection = ℓ2.1.direction.starProjection := h_dir_same2.symm
      rw [h_eq1, h_eq2] <;> rfl
    have h1 : dist o1 o2 = ‖proj‖ + ‖orig_off‖ := by
      simp [dist, AffineLine.dist, h_proj_eq] <;> ring
    have h2 : dist ℓ1 ℓ2 = ‖proj‖ + ‖wide_off‖ := by
      simp [dist, AffineLine.dist] <;> ring
    rw [h1, h2]
    have hwnn : 0 ≤ ‖wide_off‖ := by positivity
    have h_step1 : ‖proj‖ + ‖orig_off‖ ≤ 4 * ‖proj‖ + ‖wide_off‖ := by
      have h : ‖orig_off‖ ≤ ‖wide_off‖ + 3 * ‖proj‖ := h_off_relation
      linarith
    have h_step2 : 4 * ‖proj‖ + ‖wide_off‖ ≤ 4 * (‖proj‖ + ‖wide_off‖) := by
      linarith [hwnn]
    exact le_trans h_step1 h_step2

  have h_main : paramDistLinf T1 T2 ≤ 22 * dist o1 o2 :=
    toAffineLine_co_lipschitz T1 T2 hm1 hm2 hb2

  calc
    paramDistLinf T1 T2 ≤ 22 * dist o1 o2 := h_main
    _ ≤ 22 * (4 * dist ℓ1 ℓ2) := by gcongr
    _ = 88 * dist ℓ1 ℓ2 := by ring

-- ============================================================================
-- Pair parameter bound at distance 18*δ (for 9δ packing)
-- ============================================================================

/-- If dist(wideToAffineLine T1, wideToAffineLine T2) ≤ 18*δ, then
    |T1.a - T2.a| ≤ 36 and |T1.b - T2.b| ≤ 247. -/
lemma wideToAffineLine_pair_bound_18δ (T1 T2 : DyadicTube n)
    (hm1 : |T1.slope| ≤ 1) (hm2 : |T2.slope| ≤ 1)
    (hb2 : |T2.intercept| ≤ 3)
    (h_dist : dist (wideToAffineLine T1) (wideToAffineLine T2) ≤ 18 * dyadicDelta n) :
    |T1.a - T2.a| ≤ 36 ∧ |T1.b - T2.b| ≤ 261 := by
  set δ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  set m1 := T1.slope with hm1_def
  set m2 := T2.slope with hm2_def
  set b1 := T1.intercept with hb1_def
  set b2 := T2.intercept with hb2_def
  set b1' := wideIntercept m1 b1 with hb1'_def
  set b2' := wideIntercept m2 b2 with hb2'_def
  set ℓ1 := wideToAffineLine T1 with hℓ1
  set ℓ2 := wideToAffineLine T2 with hℓ2

  have h_dir_eq1 : ℓ1.1.direction = Submodule.span ℝ {tubeDirV m1} := by
    rw [hℓ1]; exact lineOfSlopeIntercept_direction m1 b1'
  have h_dir_eq2 : ℓ2.1.direction = Submodule.span ℝ {tubeDirV m2} := by
    rw [hℓ2]; exact lineOfSlopeIntercept_direction m2 b2'

  have h_proj_lower : ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ ≥ |m1 - m2| / 2 := by
    rw [h_dir_eq1, h_dir_eq2]; exact proj_lower_bound_simple m1 m2 hm1 hm2

  have h2 : ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ ≤ dist ℓ1 ℓ2 := by
    have h_def : dist ℓ1 ℓ2 = ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ + ‖ℓ1.offset - ℓ2.offset‖ := by rfl
    rw [h_def]
    have h3 : 0 ≤ ‖ℓ1.offset - ℓ2.offset‖ := norm_nonneg _
    linarith

  have h3 : |m1 - m2| / 2 ≤ 18 * δ := by linarith [h_dist, h_proj_lower]
  have h4 : |m1 - m2| ≤ 36 * δ := by linarith

  have ha : |(T1.a : ℝ) - (T2.a : ℝ)| ≤ 36 := by
    have h5 : m1 - m2 = δ * ((T1.a : ℝ) - (T2.a : ℝ)) := by
      simp [m1, m2, DyadicTube.slope, hδ] <;> ring
    have h6 : |m1 - m2| = δ * |(T1.a : ℝ) - (T2.a : ℝ)| := by
      rw [h5, abs_mul, abs_of_pos hδ_pos]
    rw [h6] at h4
    have h7 : δ * |(T1.a : ℝ) - (T2.a : ℝ)| ≤ 36 * δ := h4
    have h8 : |(T1.a : ℝ) - (T2.a : ℝ)| ≤ 36 := by nlinarith [hδ_pos]
    exact_mod_cast h8

  have h_off_bound : ‖ℓ1.offset - ℓ2.offset‖ ≤ 18 * δ := by
    have h_def : dist ℓ1 ℓ2 = ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ + ‖ℓ1.offset - ℓ2.offset‖ := by rfl
    rw [h_def] at h_dist
    have h3 : 0 ≤ ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ := norm_nonneg _
    linarith

  have h_off1 : ℓ1.offset = b1' • offsetVec m1 := wideToAffineLine_offset T1
  have h_off2 : ℓ2.offset = b2' • offsetVec m2 := wideToAffineLine_offset T2
  rw [h_off1, h_off2] at h_off_bound

  set x := (b1' - b2') • offsetVec m1 with hx
  set y := b2' • (offsetVec m1 - offsetVec m2) with hy
  have h_alg : b1' • offsetVec m1 - b2' • offsetVec m2 = x + y := by
    dsimp only [x, y]
    rw [sub_smul, smul_sub] <;> abel
  have h_rev : ‖x + y‖ ≤ 18 * δ := by
    rw [h_alg] at h_off_bound
    exact h_off_bound
  have h_tri : ‖(x + y) - y‖ ≤ ‖(x + y)‖ + ‖y‖ := norm_sub_le (x + y) y
  have h_eq : (x + y) - y = x := by abel
  rw [h_eq] at h_tri
  have h_lower : ‖x‖ - ‖y‖ ≤ ‖x + y‖ := by linarith

  have h9 : ‖x‖ = |b1' - b2'| * ‖offsetVec m1‖ := by rw [norm_smul] <;> rfl
  have h10 : ‖y‖ = |b2'| * ‖offsetVec m1 - offsetVec m2‖ := by rw [norm_smul] <;> rfl
  have h11 : ‖offsetVec m1‖ ≥ 1 / Real.sqrt 2 := by
    rw [offsetVec_norm m1]
    have h12 : Real.sqrt (1 + m1^2) ≤ Real.sqrt 2 := by
      have h13 : 1 + m1^2 ≤ 2 := by nlinarith [abs_le.mp hm1]
      exact Real.sqrt_le_sqrt h13
    have h14 : 0 < Real.sqrt (1 + m1^2) := by positivity
    exact one_div_le_one_div_of_le h14 h12
  have h15 : ‖offsetVec m1 - offsetVec m2‖ ≤ |m1 - m2| := offsetVec_lipschitz m1 m2
  have hb2'_bound : |b2'| ≤ 4 := wideIntercept_bound hm2 hb2

  have h_goal : ‖x + y‖ ≥ |b1' - b2'| * ‖offsetVec m1‖ - |b2'| * ‖offsetVec m1 - offsetVec m2‖ := by
    rw [h9, h10] at h_tri
    linarith
  have h_alg2 : |b1' - b2'| * ‖offsetVec m1‖ - |b2'| * ‖offsetVec m1 - offsetVec m2‖ ≥
      |b1' - b2'| / Real.sqrt 2 - 4 * |m1 - m2| := by
    set A := |b1' - b2'| * ‖offsetVec m1‖ with hA
    set B := |b2'| * ‖offsetVec m1 - offsetVec m2‖ with hB
    set C := |b1' - b2'| / Real.sqrt 2 with hC
    set D := 4 * |m1 - m2| with hD
    have h1 : C ≤ A := by
      have h_nonneg : 0 ≤ |b1' - b2'| := by positivity
      calc C
        = |b1' - b2'| / Real.sqrt 2 := by rfl
      _ = |b1' - b2'| * (1 / Real.sqrt 2) := by ring
      _ ≤ |b1' - b2'| * ‖offsetVec m1‖ := by gcongr
      _ = A := by rfl
    have h2 : B ≤ D := by
      calc B
        ≤ 4 * ‖offsetVec m1 - offsetVec m2‖ := by exact mul_le_mul_of_nonneg_right hb2'_bound (by positivity)
      _ ≤ D := by exact mul_le_mul_of_nonneg_left h15 (by positivity)
    have h3 : C - B ≤ A - B := by exact sub_le_sub_right h1 B
    have h4 : C - D ≤ C - B := by exact sub_le_sub_left h2 C
    exact le_trans h4 h3
  have h_final : |b1' - b2'| / Real.sqrt 2 - 4 * |m1 - m2| ≤ ‖x + y‖ := by
    exact ge_trans h_goal h_alg2
  have h_eq : |b1' - b2'| * (1 / Real.sqrt 2) = |b1' - b2'| / Real.sqrt 2 := by ring
  have h17 : |b1' - b2'| * (1 / Real.sqrt 2) - 4 * |m1 - m2| ≤ 18 * δ := by
    rw [h_eq]
    exact le_trans h_final h_rev

  have h18 : |b1' - b2'| * (1 / Real.sqrt 2) ≤ 162 * δ := by linarith [h17, h4]
  have h_sqrt2_pos : 0 < Real.sqrt 2 := by positivity
  have h19_real : |b1' - b2'| ≤ 162 * Real.sqrt 2 * δ := by
    have h_alg : |b1' - b2'| * (1 / Real.sqrt 2) = |b1' - b2'| / Real.sqrt 2 := by ring
    rw [h_alg] at h18
    have h : |b1' - b2'| / Real.sqrt 2 ≤ 162 * δ := h18
    have h2 : |b1' - b2'| ≤ 162 * Real.sqrt 2 * δ := by
      have h_eq : (|b1' - b2'| / Real.sqrt 2) * Real.sqrt 2 = |b1' - b2'| := by
        field_simp [h_sqrt2_pos.ne'] <;> ring
      calc |b1' - b2'|
        = (|b1' - b2'| / Real.sqrt 2) * Real.sqrt 2 := h_eq.symm
      _ ≤ (162 * δ) * Real.sqrt 2 := by gcongr
      _ = 162 * Real.sqrt 2 * δ := by ring
    exact h2

  have h_sqrt2_lt : Real.sqrt 2 < 3 / 2 := by
    have h_pos : (0 : ℝ) < 3 / 2 := by norm_num
    have h2 : (2 : ℝ) < (3 / 2 : ℝ) ^ 2 := by norm_num
    exact (Real.sqrt_lt' h_pos).mpr h2

  have h20 : 162 * Real.sqrt 2 < 243 := by
    have h21 : Real.sqrt 2 < 3 / 2 := h_sqrt2_lt
    nlinarith

  have h_db'_def : b1' - b2' = (m1 - m2) / 2 + (b1 - b2) := by
    dsimp only [b1', b2', wideIntercept] <;> ring
  have h_b_rel : |b1 - b2| ≤ |b1' - b2'| + |m1 - m2| / 2 := by
    have h : b1 - b2 = (b1' - b2') - (m1 - m2) / 2 := by rw [h_db'_def] <;> ring
    rw [h]
    have h2 : |(b1' - b2') - (m1 - m2) / 2| ≤ |b1' - b2'| + |(m1 - m2) / 2| := by
      exact abs_sub _ _
    have h3 : |(m1 - m2) / 2| = |m1 - m2| / 2 := by
      rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    rw [h3] at h2
    exact h2

  have h22 : |b1' - b2'| ≤ 243 * δ := by
    calc |b1' - b2'| ≤ 162 * Real.sqrt 2 * δ := h19_real
         _ ≤ 243 * δ := by
           have h : 162 * Real.sqrt 2 ≤ 243 := by linarith [h20]
           gcongr
  have h23 : |m1 - m2| / 2 ≤ 18 * δ := by linarith [h4]
  have h21 : |b1 - b2| ≤ 261 * δ := by
    calc |b1 - b2| ≤ |b1' - b2'| + |m1 - m2| / 2 := h_b_rel
         _ ≤ 243 * δ + 18 * δ := by gcongr
         _ = 261 * δ := by ring

  have hb : |(T1.b : ℝ) - (T2.b : ℝ)| ≤ 261 := by
    have h5 : b1 - b2 = δ * ((T1.b : ℝ) - (T2.b : ℝ)) := by
      simp [b1, b2, DyadicTube.intercept, hδ] <;> ring
    have h6 : |b1 - b2| = δ * |(T1.b : ℝ) - (T2.b : ℝ)| := by
      rw [h5, abs_mul, abs_of_pos hδ_pos]
    rw [h6] at h21
    have h7 : δ * |(T1.b : ℝ) - (T2.b : ℝ)| ≤ 261 * δ := h21
    have h8 : |(T1.b : ℝ) - (T2.b : ℝ)| ≤ 261 := by
      by_contra h
      have h9 : 261 < |(T1.b : ℝ) - (T2.b : ℝ)| := by linarith
      have h10 : δ * 261 < δ * |(T1.b : ℝ) - (T2.b : ℝ)| := mul_lt_mul_of_pos_left h9 hδ_pos
      linarith
    exact_mod_cast h8

  have ha' : |T1.a - T2.a| ≤ 36 := by exact_mod_cast ha
  have hb' : |T1.b - T2.b| ≤ 261 := by exact_mod_cast hb
  exact ⟨ha', hb'⟩

-- ============================================================================
-- Packing bound at 9δ: each 9δ-ball contains at most 38179 tubes
-- ============================================================================

/-- Wide image packing: at most 38179 tubes map into a 9δ-ball. -/
lemma wide_packing_9δ {n : ℕ} {S : Finset (DyadicTube n)}
    (hm : ∀ T ∈ S, |T.slope| ≤ 1)
    (hb : ∀ T ∈ S, |T.intercept| ≤ 3)
    (c : AffineLine) :
    (S.filter (fun T => wideToAffineLine T ∈ Metric.closedBall c ((9 * dyadicDelta n).toNNReal))).card ≤ 38179 := by
  set δ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  set δ9 := 9 * δ with hδ9
  have hδ9_pos : 0 < δ9 := by positivity
  have hδ9_nn_coe : ((δ9.toNNReal) : ℝ) = δ9 := by
    simp [hδ9_pos.le]
  let S_c := S.filter (fun T => wideToAffineLine T ∈ Metric.closedBall c δ9.toNNReal)
  by_cases h_empty : S_c.Nonempty
  · -- Nonempty case
    rcases h_empty with ⟨T0, hT0⟩
    have hT0_in_S : T0 ∈ S := (Finset.mem_filter.mp hT0).1
    have hT0_ball : wideToAffineLine T0 ∈ Metric.closedBall c δ9.toNNReal :=
      (Finset.mem_filter.mp hT0).2
    have h_bound : ∀ T ∈ S_c, |T.a - T0.a| ≤ 36 ∧ |T.b - T0.b| ≤ 261 := by
      intro T hT
      have hT_in_S : T ∈ S := (Finset.mem_filter.mp hT).1
      have hT_ball : wideToAffineLine T ∈ Metric.closedBall c δ9.toNNReal :=
        (Finset.mem_filter.mp hT).2
      have h_dist1 : dist (wideToAffineLine T) c ≤ δ9 := by
        simpa [Metric.mem_closedBall, hδ9_nn_coe] using hT_ball
      have h_dist2 : dist (wideToAffineLine T0) c ≤ δ9 := by
        simpa [Metric.mem_closedBall, hδ9_nn_coe] using hT0_ball
      have h_dist : dist (wideToAffineLine T) (wideToAffineLine T0) ≤ 2 * δ9 := by
        calc
          dist (wideToAffineLine T) (wideToAffineLine T0)
            ≤ dist (wideToAffineLine T) c + dist c (wideToAffineLine T0) := dist_triangle _ _ _
          _ = dist (wideToAffineLine T) c + dist (wideToAffineLine T0) c := by rw [dist_comm c (wideToAffineLine T0)]
          _ ≤ δ9 + δ9 := by gcongr
          _ = 2 * δ9 := by ring
      have h18δ : 2 * δ9 = 18 * δ := by ring
      rw [h18δ] at h_dist
      exact wideToAffineLine_pair_bound_18δ T T0 (hm T hT_in_S) (hm T0 hT0_in_S)
        (hb T0 hT0_in_S) h_dist
    let R_a := Finset.Icc (T0.a - 36) (T0.a + 36)
    let R_b := Finset.Icc (T0.b - 261) (T0.b + 261)
    have h1 : ∀ T ∈ S_c, T.a ∈ R_a ∧ T.b ∈ R_b := by
      intro T hT
      have h2 := h_bound T hT
      have h2a : |T.a - T0.a| ≤ 36 := h2.1
      have h2b : |T.b - T0.b| ≤ 261 := h2.2
      have ha_icc : T0.a - 36 ≤ T.a ∧ T.a ≤ T0.a + 36 := by
        have h : -36 ≤ T.a - T0.a ∧ T.a - T0.a ≤ 36 := by exact abs_le.mp h2a
        exact ⟨by linarith, by linarith⟩
      have hb_icc : T0.b - 261 ≤ T.b ∧ T.b ≤ T0.b + 261 := by
        have h : -261 ≤ T.b - T0.b ∧ T.b - T0.b ≤ 261 := by exact abs_le.mp h2b
        exact ⟨by linarith, by linarith⟩
      constructor
      · simp only [R_a, Finset.mem_Icc]; exact ha_icc
      · simp only [R_b, Finset.mem_Icc]; exact hb_icc
    let g : DyadicTube n → ℤ × ℤ := fun T => (T.a, T.b)
    have h_image : S_c.image g ⊆ R_a ×ˢ R_b := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨T, hT, rfl⟩
      have h4 := h1 T hT
      simp only [Finset.mem_product]; exact ⟨h4.1, h4.2⟩
    have h_inj : Set.InjOn g (S_c : Set _) := by
      intro T1 _ T2 _ h
      have h' : T1.a = T2.a ∧ T1.b = T2.b := by simpa [g, Prod.ext_iff] using h
      cases T1 <;> cases T2 <;> simp_all (config := {decide := true}) <;> aesop
    have h_card_img : (S_c.image g).card = S_c.card := Finset.card_image_of_injOn h_inj
    have h3 : S_c.card ≤ (R_a ×ˢ R_b).card := by rw [←h_card_img]; exact Finset.card_le_card h_image
    have hRa : R_a.card = 73 := by
      rw [Int.card_Icc]
      have h' : (T0.a + 36) + 1 - (T0.a - 36) = 73 := by omega
      rw [h'] <;> decide
    have hRb : R_b.card = 523 := by
      rw [Int.card_Icc]
      have h' : (T0.b + 261) + 1 - (T0.b - 261) = 523 := by omega
      rw [h'] <;> decide
    have h4 : (R_a ×ˢ R_b).card = 73 * 523 := by
      rw [Finset.card_product, hRa, hRb] <;> norm_num
    have h5 : S_c.card ≤ 73 * 523 := by rw [h4] at h3; exact h3
    have h6 : S_c.card ≤ 38179 := by
      rw [show (73 * 523 : ℕ) = 38179 by norm_num] at h5
      exact h5
    exact h6
  · -- Empty case
    have h_empty' : S_c = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using h_empty
    have h_goal : S_c.card ≤ 38179 := by
      rw [h_empty'] <;> norm_num
    exact h_goal

-- ============================================================================
-- Wide card-to-ncover at 9δ
-- ============================================================================

/-- `|S| / 38179 ≤ Ncover(9δ, wideToAffineLine '' S)`. -/
lemma wide_dyadic_card_to_ncover_9δ {n : ℕ} (S : Finset (DyadicTube n))
    (hm : ∀ T ∈ S, |T.slope| ≤ 1)
    (hb : ∀ T ∈ S, |T.intercept| ≤ 3) :
    ENNReal.ofReal ((S.card : ℝ) / 38179) ≤
      Metric.externalCoveringNumber (9 * dyadicDelta n).toNNReal (wideToAffineLine '' (S : Set (DyadicTube n))) := by
  classical
  set δ := dyadicDelta n with hδ
  set δ9 := 9 * δ with hδ9
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ9_pos : 0 < δ9 := by positivity
  set δ9_nn := δ9.toNNReal with hδ9_nn
  have hδ9_nn_coe : (δ9_nn : ℝ) = δ9 := by simp [hδ9_nn, hδ9_pos.le]
  set A : Set AffineLine := wideToAffineLine '' (S : Set (DyadicTube n)) with hA_def
  have hA_fin : A.Finite := Set.Finite.image _ (S.finite_toSet)
  have hcover_A : Metric.IsCover δ9_nn A A := by
    intro x hx; exact ⟨x, hx, by simp [Metric.IsCover, edist_dist]⟩
  let ι := {C : Set AffineLine // Metric.IsCover δ9_nn A C}
  have hι_nonempty : Nonempty ι := ⟨⟨A, hcover_A⟩⟩
  let f : ι → ℕ∞ := fun C => (C.val).encard
  have h_exists : ∃ (C : ι), f C = ⨅ (x : ι), f x := ENat.exists_eq_iInf f
  rcases h_exists with ⟨C_min, hC_min_eq⟩
  have h_ext_def : Metric.externalCoveringNumber δ9_nn A = ⨅ (C : ι), f C := by
    have h : Metric.externalCoveringNumber δ9_nn A =
        ⨅ (C : Set AffineLine) (_ : Metric.IsCover δ9_nn A C), C.encard := by rfl
    rw [h]
    have h2 : (⨅ (C : Set AffineLine) (_ : Metric.IsCover δ9_nn A C), C.encard) = ⨅ (C : ι), f C := by
      rw [iInf_subtype] <;> rfl
    rw [h2]
  have h_encard_eq : (C_min.val).encard = Metric.externalCoveringNumber δ9_nn A := by
    have h10 : f C_min = Metric.externalCoveringNumber δ9_nn A := by rw [hC_min_eq, h_ext_def]
    simpa [f] using h10
  have h_fin : (C_min.val).Finite := by
    have h1 : Metric.externalCoveringNumber δ9_nn A ≤ A.encard := Metric.externalCoveringNumber_le_encard_self A
    rw [←h_encard_eq] at h1
    exact Set.encard_lt_top_iff.mp (h1.trans_lt (hA_fin.encard_lt_top))
  let C_finset : Finset AffineLine := h_fin.toFinset
  have hC_coe : (C_finset : Set AffineLine) = C_min.val := by exact Set.Finite.coe_toFinset h_fin
  have h_edist_dist : ∀ (x c : AffineLine), edist x c ≤ (δ9_nn : ENNReal) ↔ dist x c ≤ δ9 := by
    intro x c
    simp [edist_dist, hδ9_nn_coe]
  have h_cover : ∀ (x : AffineLine), x ∈ A → ∃ (c : AffineLine), c ∈ C_finset ∧ x ∈ Metric.closedBall c δ9_nn := by
    intro x hx
    have h2 := C_min.property hx
    rcases h2 with ⟨c, hc, hball⟩
    have hball' : x ∈ Metric.closedBall c δ9_nn := by
      simpa [Metric.mem_closedBall, (h_edist_dist x c)] using hball
    have hc' : c ∈ C_finset := by
      have h1 : c ∈ (C_finset : Set AffineLine) := by rw [hC_coe] <;> exact hc
      simpa using h1
    exact ⟨c, hc', hball'⟩
  let S_c : AffineLine → Finset (DyadicTube n) := fun c =>
    S.filter (fun T => wideToAffineLine T ∈ Metric.closedBall c δ9_nn)
  have h_union : S ⊆ Finset.biUnion C_finset S_c := by
    intro T hT
    have hT_in_A : wideToAffineLine T ∈ A := by exact ⟨T, hT, rfl⟩
    rcases h_cover (wideToAffineLine T) hT_in_A with ⟨c, hc, hball⟩
    have h3 : T ∈ S_c c := by
      simp only [S_c, Finset.mem_filter]; exact ⟨hT, hball⟩
    exact Finset.mem_biUnion.mpr ⟨c, hc, h3⟩
  have h_ball_bound : ∀ (c : AffineLine), (S_c c).card ≤ 38179 := wide_packing_9δ hm hb
  have h_card : S.card ≤ 38179 * C_finset.card := by
    calc
      S.card ≤ (Finset.biUnion C_finset S_c).card := Finset.card_le_card h_union
      _ ≤ ∑ c ∈ C_finset, (S_c c).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ C_finset, 38179 := by gcongr <;> exact h_ball_bound c
      _ = 38179 * C_finset.card := by simp [Finset.sum_const] <;> ring
  have h_ncard_eq : (C_finset.card : ℕ∞) = Metric.externalCoveringNumber δ9_nn A := by
    have h5 : (C_finset.card : ℕ∞) = (C_min.val).encard := by
      have h6 : C_finset.card = (C_min.val).ncard := by
        exact Eq.symm (Set.ncard_eq_toFinset_card (C_min.val) h_fin)
      have h7 : ((C_min.val).ncard : ℕ∞) = (C_min.val).encard := by
        letI : Fintype (C_min.val) := Set.Finite.fintype h_fin
        simp
      rw [h6, h7]
    rw [h5, h_encard_eq]
  have h_main : (S.card : ENNReal) ≤ (38179 : ENNReal) * Metric.externalCoveringNumber δ9_nn A := by
    have h_card' : (S.card : ℝ) ≤ 38179 * (C_finset.card : ℝ) := by exact_mod_cast h_card
    have h : (S.card : ENNReal) ≤ (38179 : ENNReal) * (C_finset.card : ENNReal) := by
      exact_mod_cast h_card'
    have h9 : (C_finset.card : ENNReal) = Metric.externalCoveringNumber δ9_nn A := by
      exact_mod_cast h_ncard_eq
    rw [h9] at h
    exact h
  have h_final : ENNReal.ofReal ((S.card : ℝ) / 38179) ≤ Metric.externalCoveringNumber δ9_nn A := by
    have h_pos : (0 : ℝ) < 38179 := by norm_num
    have h_eq : ENNReal.ofReal ((S.card : ℝ) / 38179) = (S.card : ENNReal) / 38179 := by
      have h : (S.card : ℝ) / 38179 = (S.card : ℝ) * (1 / 38179 : ℝ) := by ring
      rw [h]
      have h_mul : ENNReal.ofReal ((S.card : ℝ) * (1 / 38179 : ℝ)) =
          ENNReal.ofReal (S.card : ℝ) * ENNReal.ofReal (1 / 38179 : ℝ) :=
        ENNReal.ofReal_mul (by positivity)
      rw [h_mul]
      have h_inv : ENNReal.ofReal (1 / 38179 : ℝ) = (38179 : ENNReal)⁻¹ := by simp
      rw [h_inv] <;> simp [div_eq_mul_inv]
    rw [h_eq]
    have h_comm : (S.card : ENNReal) ≤ Metric.externalCoveringNumber δ9_nn A * (38179 : ENNReal) := by
      have h' : (S.card : ENNReal) ≤ (38179 : ENNReal) * Metric.externalCoveringNumber δ9_nn A := h_main
      rw [mul_comm] at h'
      exact h'
    simpa [ENNReal.div_le_iff_le_mul] using h_comm
  exact h_final

-- ============================================================================
-- Wide S-set transfer: IsFiniteTubeSSet → IsDeltaSSet(9δ) on wide image
-- ============================================================================

/-- Transfer IsFiniteTubeSSet to IsDeltaSSet at scale 9δ on wideToAffineLine image.
    Output constant: `C * 38179 * 176^s`. -/
lemma wide_finiteTubeSSet_to_affineSSet_9δ {n : ℕ} {s C : ℝ} {F : Finset (DyadicTube n)}
    (hs : 0 ≤ s) (hC_one : 1 ≤ C)
    (hm : ∀ T ∈ F, |T.slope| ≤ 1)
    (hb : ∀ T ∈ F, |T.intercept| ≤ 3)
    (h : InductionOnScales.IsFiniteTubeSSet s C F) :
    IsDeltaSSet (9 * dyadicDelta n) s (C * 38179 * 176^s)
      (wideToAffineLine '' (F : Set (DyadicTube n))) := by
  set δ := dyadicDelta n with hδ
  set δ9 := 9 * δ with hδ9
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ9_pos : 0 < δ9 := by positivity
  have hC_pos : 0 < C := by linarith
  set S' : Set AffineLine := wideToAffineLine '' (F : Set (DyadicTube n)) with hS'_def
  have hF_nonempty : F.Nonempty := h.1
  have hS'_nonempty : S'.Nonempty := by
    rcases hF_nonempty with ⟨T, hT⟩
    exact ⟨wideToAffineLine T, ⟨T, hT, rfl⟩⟩
  have h_inj : Set.InjOn wideToAffineLine (F : Set (DyadicTube n)) := by
    intro T1 hT1 T2 hT2 h
    by_cases hne : T1 = T2
    · exact hne
    · exfalso
      have h_coLip : paramDistLinf T1 T2 ≤ 88 * dist (wideToAffineLine T1) (wideToAffineLine T2) :=
        wideToAffineLine_co_lipschitz T1 T2 (hm T1 hT1) (hm T2 hT2) (hb T2 hT2)
      rw [h] at h_coLip
      have h_and : T1.slope - T2.slope = 0 ∧ T1.intercept - T2.intercept = 0 := by simpa using h_coLip
      have h_slope : T1.slope = T2.slope := by linarith [h_and.1]
      have h_int : T1.intercept = T2.intercept := by linarith [h_and.2]
      have ha_eq : (T1.a : ℝ) = (T2.a : ℝ) := by
        have hδ : 0 < δ := dyadicDelta_pos n
        have h_eq : (T1.a : ℝ) * δ = (T2.a : ℝ) * δ := by
          simpa [DyadicTube.slope] using h_slope
        have h_eq' : δ * (T1.a : ℝ) = δ * (T2.a : ℝ) := by
          rw [mul_comm δ (T1.a : ℝ), mul_comm δ (T2.a : ℝ)] <;> exact h_eq
        exact (mul_right_inj' hδ.ne').mp h_eq'
      have hb_eq : (T1.b : ℝ) = (T2.b : ℝ) := by
        have hδ : 0 < δ := dyadicDelta_pos n
        have h_eq : (T1.b : ℝ) * δ = (T2.b : ℝ) * δ := by
          simpa [DyadicTube.intercept] using h_int
        have h_eq' : δ * (T1.b : ℝ) = δ * (T2.b : ℝ) := by
          rw [mul_comm δ (T1.b : ℝ), mul_comm δ (T2.b : ℝ)] <;> exact h_eq
        exact (mul_right_inj' hδ.ne').mp h_eq'
      have h_final : T1 = T2 := by
        have ha : T1.a = T2.a := by exact_mod_cast ha_eq
        have hb : T1.b = T2.b := by exact_mod_cast hb_eq
        cases T1 <;> cases T2 <;> simp_all <;> tauto
      exact hne h_final
  refine' ⟨hS'_nonempty, hδ9_pos, by positivity, hs, _⟩
  intro y r hr
  set G : Finset (DyadicTube n) := F.filter (fun T => dist (wideToAffineLine T) y ≤ r) with hG_def
  set B : Finset AffineLine := G.image wideToAffineLine with hB_def
  have hB_eq : (B : Set AffineLine) = S' ∩ Metric.closedBall y r := by
    ext ℓ
    simp only [hB_def, hS'_def, Finset.mem_coe, Finset.mem_image, Set.mem_inter_iff,
      Metric.mem_closedBall, Set.mem_image]
    constructor
    · rintro ⟨T, hT, rfl⟩
      have hT_in_F : T ∈ F := (Finset.mem_filter.mp hT).1
      have h_dist : dist (wideToAffineLine T) y ≤ r := (Finset.mem_filter.mp hT).2
      exact ⟨⟨T, hT_in_F, rfl⟩, h_dist⟩
    · rintro ⟨⟨T, hT, rfl⟩, h_dist⟩
      exact ⟨T, Finset.mem_filter.mpr ⟨hT, h_dist⟩, rfl⟩
  by_cases hG_empty : G.Nonempty
  · rcases hG_empty with ⟨T0, hT0⟩
    have hT0_in_F : T0 ∈ F := (Finset.mem_filter.mp hT0).1
    have h_dist0 : dist (wideToAffineLine T0) y ≤ r := (Finset.mem_filter.mp hT0).2
    have h_ball : G ⊆ F.filter (fun T => paramDistLinf T T0 ≤ 176 * r) := by
      intro T hT
      have hT_in_F : T ∈ F := (Finset.mem_filter.mp hT).1
      have h_distT : dist (wideToAffineLine T) y ≤ r := (Finset.mem_filter.mp hT).2
      have h_coLip : paramDistLinf T T0 ≤ 88 * dist (wideToAffineLine T) (wideToAffineLine T0) :=
        wideToAffineLine_co_lipschitz T T0 (hm T hT_in_F) (hm T0 hT0_in_F) (hb T0 hT0_in_F)
      have h_tri : dist (wideToAffineLine T) (wideToAffineLine T0) ≤ 2 * r := by
        calc
          dist (wideToAffineLine T) (wideToAffineLine T0)
            ≤ dist (wideToAffineLine T) y + dist y (wideToAffineLine T0) := dist_triangle _ _ _
          _ = dist (wideToAffineLine T) y + dist (wideToAffineLine T0) y := by rw [dist_comm y (wideToAffineLine T0)]
          _ ≤ r + r := by gcongr
          _ = 2 * r := by ring
      have h_final : paramDistLinf T T0 ≤ 176 * r := by
        calc
          paramDistLinf T T0 ≤ 88 * dist (wideToAffineLine T) (wideToAffineLine T0) := h_coLip
          _ ≤ 88 * (2 * r) := by gcongr
          _ = 176 * r := by ring
      exact Finset.mem_filter.mpr ⟨hT_in_F, h_final⟩
    have hG_card_le : (G.card : ℝ) ≤ ((F.filter (fun T => paramDistLinf T T0 ≤ 176 * r)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card h_ball
    have h176r_ge_delta : δ ≤ 176 * r := by
      have h1 : δ9 ≤ r := hr
      have h2 : δ ≤ δ9 := by linarith [hδ_pos]
      linarith
    have h_frost := h.2.2.2.2 T0 (176 * r) h176r_ge_delta
    have h_card_le : (G.card : ℝ) ≤ C * (176 * r)^s * (F.card : ℝ) := by
      calc
        (G.card : ℝ) ≤ (F.filter (fun T => paramDistLinf T T0 ≤ 176 * r)).card := hG_card_le
        _ ≤ C * (176 * r)^s * (F.card : ℝ) := h_frost
    let A : Set AffineLine := S' ∩ Metric.closedBall y r
    have h_ncover_le : (Metric.externalCoveringNumber δ9.toNNReal A : ENNReal) ≤ (B.card : ENNReal) := by
      have h : Metric.externalCoveringNumber δ9.toNNReal A ≤ A.encard :=
        Metric.externalCoveringNumber_le_encard_self A
      have hA : A = S' ∩ Metric.closedBall y r := by rfl
      have h2 : A.encard = (B.card : ℕ∞) := by
        rw [hA, ←hB_eq] <;> simp
      rw [h2] at h
      exact_mod_cast h
    have h_card_image : B.card = G.card := by
      rw [hB_def, Finset.card_image_of_injOn]
      intro T1 _ T2 _ h
      exact h_inj (Finset.mem_filter.mp ‹_›).1 (Finset.mem_filter.mp ‹_›).1 h
    have h_lower : (F.card : ENNReal) ≤ (38179 : ENNReal) *
        Metric.externalCoveringNumber δ9.toNNReal S' := by
      have h_ncov : ENNReal.ofReal ((F.card : ℝ) / 38179) ≤
          Metric.externalCoveringNumber δ9.toNNReal S' :=
        wide_dyadic_card_to_ncover_9δ F hm hb
      have h_eq : ENNReal.ofReal ((F.card : ℝ) / 38179) = (F.card : ENNReal) / 38179 := by
        have h : (F.card : ℝ) / 38179 = (F.card : ℝ) * (1 / 38179 : ℝ) := by ring
        rw [h]
        have h_mul : ENNReal.ofReal ((F.card : ℝ) * (1 / 38179 : ℝ)) =
            ENNReal.ofReal (F.card : ℝ) * ENNReal.ofReal (1 / 38179 : ℝ) :=
          ENNReal.ofReal_mul (by positivity)
        rw [h_mul]
        have h_inv : ENNReal.ofReal (1 / 38179 : ℝ) = (38179 : ENNReal)⁻¹ := by simp
        rw [h_inv] <;> simp [div_eq_mul_inv]
      rw [h_eq] at h_ncov
      have h : (F.card : ENNReal) ≤ Metric.externalCoveringNumber δ9.toNNReal S' * (38179 : ENNReal) := by
        simpa [ENNReal.div_le_iff_le_mul] using h_ncov
      have h' : Metric.externalCoveringNumber δ9.toNNReal S' * (38179 : ENNReal) =
          (38179 : ENNReal) * Metric.externalCoveringNumber δ9.toNNReal S' := by rw [mul_comm]
      rw [h'] at h
      exact h
    have h_r_nonneg : 0 ≤ r := by linarith [hδ9_pos, hr]
    have h176_pos : 0 < (176 : ℝ) := by norm_num
    have h_B_card_real : (B.card : ℝ) = (G.card : ℝ) := by exact_mod_cast h_card_image
    have h_card_le_B : (B.card : ℝ) ≤ C * (176 * r)^s * (F.card : ℝ) := by
      rw [h_B_card_real]; exact h_card_le
    have h_main : (B.card : ENNReal) ≤
        ENNReal.ofReal (C * 38179 * 176^s) * (ENNReal.ofReal r)^s *
          Metric.externalCoveringNumber δ9.toNNReal S' := by
      have h1 : (B.card : ENNReal) = ENNReal.ofReal (B.card : ℝ) := by simp
      rw [h1]
      have h2 : ENNReal.ofReal (B.card : ℝ) ≤
          ENNReal.ofReal (C * (176 * r)^s * (F.card : ℝ)) :=
        ENNReal.ofReal_le_ofReal h_card_le_B
      have h3 : C * (176 * r)^s * (F.card : ℝ) =
          (C * 38179 * 176^s) * r^s * ((F.card : ℝ) / 38179) := by
        have h4 : (176 * r)^s = 176^s * r^s :=
          Real.mul_rpow (x := (176 : ℝ)) (y := r) (z := s) (by norm_num) h_r_nonneg
        rw [h4] <;> ring
      have h5 : ENNReal.ofReal (C * (176 * r)^s * (F.card : ℝ)) =
          ENNReal.ofReal ((C * 38179 * 176^s) * r^s * ((F.card : ℝ) / 38179)) := by rw [h3]
      rw [h5] at h2
      have h_pos1 : 0 ≤ C * 38179 * 176^s := by positivity
      have h_pos2 : 0 ≤ r^s := by positivity
      have h_pos3 : 0 ≤ (F.card : ℝ) / 38179 := by positivity
      have h6 : ENNReal.ofReal ((C * 38179 * 176^s) * r^s * ((F.card : ℝ) / 38179)) =
          ENNReal.ofReal (C * 38179 * 176^s) * ENNReal.ofReal (r^s) *
            ENNReal.ofReal ((F.card : ℝ) / 38179) := by
        have h_step1 : ENNReal.ofReal (((C * 38179 * 176^s) * r^s) * ((F.card : ℝ) / 38179)) =
            ENNReal.ofReal ((C * 38179 * 176^s) * r^s) * ENNReal.ofReal ((F.card : ℝ) / 38179) :=
          ENNReal.ofReal_mul (by positivity)
        rw [h_step1]
        have h_step2 : ENNReal.ofReal ((C * 38179 * 176^s) * r^s) =
            ENNReal.ofReal (C * 38179 * 176^s) * ENNReal.ofReal (r^s) :=
          ENNReal.ofReal_mul h_pos1
        rw [h_step2] <;> ring
      rw [h6] at h2
      have h7 : ENNReal.ofReal (r^s) = (ENNReal.ofReal r)^s := by exact Eq.symm (ENNReal.ofReal_rpow_of_nonneg h_r_nonneg hs)
      rw [h7] at h2
      have h8 : ENNReal.ofReal ((F.card : ℝ) / 38179) ≤ Metric.externalCoveringNumber δ9.toNNReal S' :=
        wide_dyadic_card_to_ncover_9δ F hm hb
      have h9 : ENNReal.ofReal (C * 38179 * 176^s) * (ENNReal.ofReal r)^s *
            ENNReal.ofReal ((F.card : ℝ) / 38179) ≤
          ENNReal.ofReal (C * 38179 * 176^s) * (ENNReal.ofReal r)^s *
            Metric.externalCoveringNumber δ9.toNNReal S' := by gcongr <;> ring
      exact le_trans h2 h9
    calc
      (Metric.externalCoveringNumber δ9.toNNReal A : ENNReal)
        ≤ (B.card : ENNReal) := h_ncover_le
      _ ≤ ENNReal.ofReal (C * 38179 * 176^s) * (ENNReal.ofReal r)^s *
            Metric.externalCoveringNumber δ9.toNNReal S' := h_main
  · have hB_empty : B = ∅ := by
      rw [hB_def]
      simpa [hG_def] using hG_empty
    have h_cover : Metric.externalCoveringNumber δ9.toNNReal (S' ∩ Metric.closedBall y r) = 0 := by
      rw [←hB_eq, hB_empty] <;> simp
    rw [h_cover] <;> simp

-- ============================================================================
-- Full S-set transfer chain at 9δ
-- ============================================================================

/-- Full S-set transfer from DyadicTube to wideToAffineLine image at scale 9δ.

    Chain: IsDeltaSSet(δ) → DiscreteFrostmanL1(5C) → IsFiniteTubeSSet(max 1 (10C))
           → IsDeltaSSet(9δ) on wide image.
    Output constant: `max 1 (10 * C_fine) * 38179 * 176^s`. -/
lemma wide_tubeSSet_transfer_9δ {n : ℕ} {s C_fine : ℝ} {F : Finset (DyadicTube n)}
    (hs : 0 ≤ s) (hs_lt_one : s < 1) (hC_one : 1 ≤ C_fine)
    (hm : ∀ T ∈ F, |T.slope| ≤ 1)
    (hb : ∀ T ∈ F, |T.intercept| ≤ 3)
    (h : IsDeltaSSet (dyadicDelta n) s C_fine (F : Set (DyadicTube n))) :
    IsDeltaSSet (9 * dyadicDelta n) s
      (max 1 (10 * C_fine) * 38179 * 176^s)
      (wideToAffineLine '' (F : Set (DyadicTube n))) := by
  have h1 : DiscreteFrostmanL1 s (5 * C_fine) F :=
    isDeltaSSet_to_discreteFrostmanL1 h
  have h2 : IsFiniteTubeSSet s (max 1 (2 * (5 * C_fine))) F :=
    discreteFrostmanL1_to_isFiniteTubeSSet hs_lt_one.le hs h1
  have h3 : max 1 (2 * (5 * C_fine)) = max 1 (10 * C_fine) := by ring_nf
  rw [h3] at h2
  exact wide_finiteTubeSSet_to_affineSSet_9δ hs (by exact le_max_left _ _) hm hb h2

end DiscretisedFurstenbergEstimate

end
