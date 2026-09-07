module

/-
  S-set transfer from AffineLine to DyadicTube via snapToTubeThroughPoint.

  Main result: snap_sset_transfer
  Given a (δ, s, C)-set S of AffineLines near a point p, with bounded slopes,
  the snapped dyadic tubes form a (δ_n, s, C')-set with δ-independent C'.

  Dependencies: DyadicTubes, ConstructNiceConfiguration, DyadicCardToNcover,
                DyadicToAffineAdapters, SnappingSSetTransfer, PackingBound
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ConstructNiceConfiguration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicToAffineAdapters
public import MyLeanRepo.DiscretisedFurstenbergEstimate.SnappingSSetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable


noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MainAppendix
open DirecretisedFurstenbergEstimate.Snapping
open DyadicCardToNcover
open DiscretisedFurstenbergEstimate.CoveringUtils

/-- Triangle inequality for three real terms. -/
lemma abs_add_three (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  calc |a + b + c| ≤ |a + b| + |c| := abs_add_le (a + b) c
  _ ≤ |a| + |b| + |c| := by
    have h : |a + b| ≤ |a| + |b| := abs_add_le a b
    linarith

/-- Real absolute value of integer coercion equals Int.natAbs coercion. -/
lemma int_natAbs_cast_abs (z : ℤ) : |(z : ℝ)| = (Int.natAbs z : ℝ) := by
  have h_sq1 : |(z : ℝ)| ^ 2 = (z : ℝ) ^ 2 := by rw [sq_abs]
  have h_sq2 : (Int.natAbs z : ℝ) ^ 2 = (z : ℝ) ^ 2 := by
    have h : (Int.natAbs z : ℤ) ^ 2 = z ^ 2 := by exact Int.natAbs_pow_two z
    have h' : ((Int.natAbs z : ℝ) ^ 2) = ↑((Int.natAbs z : ℤ) ^ 2) := by norm_cast
    rw [h', h]
    <;> norm_cast
  have h_nonneg1 : 0 ≤ |(z : ℝ)| := by positivity
  have h_nonneg2 : 0 ≤ (Int.natAbs z : ℝ) := by positivity
  nlinarith

/-- Coordinate absolute value bounded by norm. -/
lemma coord_abs_le_norm (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  have h2 : ‖x‖ ^ 2 = (x 0)^2 + (x 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
  have h1 : (x i)^2 ≤ ‖x‖ ^ 2 := by
    rw [h2]
    fin_cases i <;> simp [add_assoc] <;> ring_nf <;> positivity
  have h3 : 0 ≤ ‖x‖ := norm_nonneg x
  have h4 : 0 ≤ |x i| := abs_nonneg (x i)
  have h5 : (x i)^2 = |x i| ^ 2 := by
    simp [sq_abs]
  rw [h5] at h1
  have h6 : |x i| ≤ ‖x‖ := by
    nlinarith [abs_nonneg (x i), norm_nonneg x]
  exact h6

/-- Rounding error helper: if y = δ_n * roundInt(x / δ_n), then |y - x| ≤ δ_n / 2. -/
lemma rounding_error_bound (x δ_n : ℝ) (hδn_pos : 0 < δ_n) (y : ℝ)
    (hy : y = δ_n * (roundInt (x / δ_n) : ℝ)) : |y - x| ≤ δ_n / 2 := by
  have h1 : y - x = δ_n * ((roundInt (x / δ_n) : ℝ) - x / δ_n) := by
    rw [hy]
    have h2 : δ_n * (roundInt (x / δ_n) : ℝ) - x =
        δ_n * ((roundInt (x / δ_n) : ℝ) - x / δ_n) := by
      have h3 : δ_n * (x / δ_n) = x := by
        field_simp [hδn_pos.ne'] <;> ring
      rw [mul_sub, h3] <;> ring
    exact h2
  rw [h1]
  have h4 : |δ_n * ((roundInt (x / δ_n) : ℝ) - x / δ_n)| =
      δ_n * |(roundInt (x / δ_n) : ℝ) - x / δ_n| := by
    rw [abs_mul, abs_of_pos hδn_pos]
  rw [h4]
  have h5 : |(roundInt (x / δ_n) : ℝ) - x / δ_n| ≤ 1 / 2 := roundInt_abs_error (x / δ_n)
  have h6 : δ_n * |(roundInt (x / δ_n) : ℝ) - x / δ_n| ≤ δ_n * (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left h5 hδn_pos.le
  have h7 : δ_n * (1 / 2 : ℝ) = δ_n / 2 := by ring
  rw [h7] at h6
  exact h6

/-- Floor error helper: if y = δ_n * Int.floor(x / δ_n), then |y - x| < δ_n. -/
lemma floor_error_bound (x δ_n : ℝ) (hδn_pos : 0 < δ_n) (y : ℝ)
    (hy : y = δ_n * (Int.floor (x / δ_n) : ℝ)) : |y - x| < δ_n := by
  let z : ℝ := x / δ_n
  have h1 : (Int.floor z : ℝ) ≤ z := Int.floor_le z
  have h2 : z < (Int.floor z : ℝ) + 1 := Int.lt_floor_add_one z
  have h3 : y ≤ x := by
    have h4 : y = δ_n * (Int.floor z : ℝ) := by simpa [z, hy] using rfl
    rw [h4]
    have h5 : δ_n * (Int.floor z : ℝ) ≤ δ_n * z := by gcongr
    have h6 : δ_n * z = x := by
      simp [z] <;> field_simp [hδn_pos.ne'] <;> ring
    rw [h6] at h5; exact h5
  have h4 : x < y + δ_n := by
    have h5 : y = δ_n * (Int.floor z : ℝ) := by simpa [z, hy] using rfl
    rw [h5]
    have h6 : δ_n * z < δ_n * ((Int.floor z : ℝ) + 1) := by gcongr
    have h7 : δ_n * z = x := by
      simp [z] <;> field_simp [hδn_pos.ne'] <;> ring
    rw [h7] at h6; linarith
  have h5 : 0 ≤ x - y := by linarith
  have h6 : x - y < δ_n := by linarith
  have h7 : |y - x| = x - y := by
    rw [abs_of_nonpos] <;> linarith
  rw [h7] <;> linarith

/-! ============================================================================
   line_eq_lineOfSlopeIntercept
   ============================================================================ -/

/-- For a non-vertical line ℓ with slope-intercept (m,c),
    ℓ = lineOfSlopeIntercept m c. -/
lemma line_eq_lineOfSlopeIntercept (ℓ : AffineLine)
    (hv0 : (LemmaE.getDirV ℓ) 0 ≠ 0) :
    ℓ = lineOfSlopeIntercept (affineLineSlopeIntercept ℓ).1
        (affineLineSlopeIntercept ℓ).2 := by
  set m := (affineLineSlopeIntercept ℓ).1 with hm_def
  set c := (affineLineSlopeIntercept ℓ).2 with hc_def
  let v := LemmaE.getDirV ℓ
  have hvm : m = v 1 / v 0 := by
    simp [affineLineSlopeIntercept, hv0, hm_def] <;> aesop
  have hvc : c = ℓ.offset 1 - m * ℓ.offset 0 := by
    simp [affineLineSlopeIntercept, hv0, hc_def] <;> aesop
  have h_v_in_dir : v ∈ ℓ.1.direction := (LemmaE.getDirV_spec ℓ).1
  have h_v_ne_zero : v ≠ 0 := (LemmaE.getDirV_spec ℓ).2

  have h1 : Submodule.span ℝ {v} ≤ ℓ.1.direction := by
    apply Submodule.span_le.mpr; intro x hx
    rw [Set.mem_singleton_iff] at hx; rw [hx]; exact h_v_in_dir
  have h2 : Module.finrank ℝ (Submodule.span ℝ {v}) = 1 :=
    finrank_span_singleton h_v_ne_zero
  have h_dir_span_v : ℓ.1.direction = Submodule.span ℝ {v} :=
    (Submodule.eq_of_le_of_finrank_eq h1 (by rw [h2, ℓ.2])).symm

  have h_v_eq : v = (v 0) • tubeDirV m := by
    apply PiLp.ext
    intro i
    fin_cases i
    · simp [tubeDirV, TubesAndSlopes.mkPlane_apply0] <;> ring
    · have h : v 1 = v 0 * m := by
        have h' : m = v 1 / v 0 := hvm
        have h'' : v 0 * m = v 1 := by
          rw [h']
          have h_div : v 0 * (v 1 / v 0) = v 1 := by exact mul_div_cancel₀ (v.ofLp 1) hv0
          exact h_div
        exact h''.symm
      simpa [tubeDirV, TubesAndSlopes.mkPlane_apply1] using h

  have h_isunit : IsUnit (v 0) := by
    exact Ne.isUnit hv0
  have h_span_eq : Submodule.span ℝ {v} = Submodule.span ℝ {tubeDirV m} := by
    rw [h_v_eq]
    rw [Submodule.span_singleton_smul_eq] <;> exact h_isunit

  have h_dir_eq : ℓ.1.direction = (lineOfSlopeIntercept m c).1.direction := by
    rw [h_dir_span_v, h_span_eq, lineOfSlopeIntercept_direction m c]

  have h_off_on_line : ℓ.offset 1 = m * ℓ.offset 0 + c := by
    rw [hvc] <;> ring

  have h_offset_in : ℓ.offset ∈ (lineOfSlopeIntercept m c).1 := by
    have h : ℓ.offset - TubesAndSlopes.mkPlane 0 c = (ℓ.offset 0) • tubeDirV m := by
      apply PiLp.ext
      intro i
      fin_cases i
      · simp [TubesAndSlopes.mkPlane_apply0, tubeDirV] <;> ring
      · simp [TubesAndSlopes.mkPlane_apply1, tubeDirV, h_off_on_line] <;> ring
    have h' : ℓ.offset - TubesAndSlopes.mkPlane 0 c ∈ (lineOfSlopeIntercept m c).1.direction := by
      rw [lineOfSlopeIntercept_direction m c, h]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have h_base : TubesAndSlopes.mkPlane 0 c ∈ (lineOfSlopeIntercept m c).1 := by
      simp [lineOfSlopeIntercept, AffineSubspace.mem_mk']
      <;> exact Submodule.zero_mem _
    have h_add : ℓ.offset = TubesAndSlopes.mkPlane 0 c + (ℓ.offset - TubesAndSlopes.mkPlane 0 c) := by
      ext i; fin_cases i <;> simp [TubesAndSlopes.mkPlane_apply0, TubesAndSlopes.mkPlane_apply1] <;> ring
    rw [h_add]
    simpa [vadd_eq_add] using (AffineSubspace.vadd_mem_iff_mem_of_mem_direction h').mpr h_base
  have h_main : ℓ.1 = (lineOfSlopeIntercept m c).1 := by
    apply AffineSubspace.eq_iff_direction_eq_of_mem ℓ.offset_mem h_offset_in |>.mpr
    exact h_dir_eq
  apply Subtype.ext
  exact h_main

/-! ============================================================================
   Movement bound
   ============================================================================ -/

/-- Clamp-aware slope error: |m - snapped_slope| ≤ δ_n.
    Without clamp: rounding error ≤ δ_n/2.
    With clamp (m near 1): snapped_slope = 1 - δ_n, and m ≥ 1 - δ_n/2, so error ≤ δ_n. -/
lemma snap_slope_err_clamp {n : ℕ} {m : ℝ} (hm : |m| ≤ 1)
    (T : DyadicTube n) (hT_a : T.a = min (roundInt (m / dyadicDelta n)) ((2 ^ n : ℤ) - 1)) :
    |m - T.slope| ≤ dyadicDelta n := by
  set δ_n := dyadicDelta n with hδn_def
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  let a_raw := roundInt (m / δ_n)
  have h_slope_eq : T.slope = (T.a : ℝ) * δ_n := by
    simp [DyadicTube.slope, hδn_def] <;> ring
  rw [h_slope_eq, hT_a]
  by_cases h : a_raw ≤ (2 ^ n : ℤ) - 1
  · rw [min_eq_left h]
    have h_eq : (a_raw : ℝ) * δ_n = δ_n * (roundInt (m / δ_n) : ℝ) := by
      simp [a_raw, mul_comm] <;> ring
    have h_err : |(a_raw : ℝ) * δ_n - m| ≤ δ_n / 2 :=
      rounding_error_bound m δ_n hδn_pos ((a_raw : ℝ) * δ_n) h_eq
    have h2 : |m - (a_raw : ℝ) * δ_n| = |(a_raw : ℝ) * δ_n - m| := by rw [abs_sub_comm]
    rw [h2]
    linarith
  · -- a_raw > 2^n - 1, so a_raw ≥ 2^n
    have h_ge : a_raw ≥ (2 ^ n : ℤ) := by omega
    have h_m_le_one : m ≤ 1 := by linarith [abs_le.mp hm]
    have h1 : |(a_raw : ℝ) - m / δ_n| ≤ 1 / 2 := roundInt_abs_error (m / δ_n)
    have h1b := abs_le.mp h1
    have h2 : m / δ_n ≤ (2 ^ n : ℝ) := by
      have h3 : m ≤ 1 := h_m_le_one
      have h4 : 0 < δ_n := hδn_pos
      have h5 : m / δ_n ≤ 1 / δ_n := by
        exact div_le_div_of_nonneg_right h3 h4.le
      have h6 : 1 / δ_n = (2 ^ n : ℝ) := by
        have h7 : δ_n = 1 / (2 ^ n : ℝ) := by simp [δ_n, dyadicDelta] <;> field_simp <;> ring
        rw [h7] <;> field_simp <;> ring
      rw [h6] at h5; exact h5
    have h_a_raw_upper : (a_raw : ℝ) ≤ (2 ^ n : ℝ) + 1 / 2 := by linarith [h1b.2, h2]
    have h_a_raw_le : a_raw ≤ (2 ^ n : ℤ) := by
      by_contra h6
      have h7 : a_raw ≥ (2 ^ n : ℤ) + 1 := by omega
      have h8 : (a_raw : ℝ) ≥ (2 ^ n : ℝ) + 1 := by exact_mod_cast h7
      linarith
    have h_a_raw_eq : a_raw = (2 ^ n : ℤ) := by omega
    have h9 : (a_raw : ℝ) = (2 ^ n : ℝ) := by exact_mod_cast h_a_raw_eq
    have h10 : m / δ_n ≥ (2 ^ n : ℝ) - 1 / 2 := by linarith [h1b.1, h9]
    have h11 : m ≥ 1 - δ_n / 2 := by
      have h12 : δ_n = 1 / (2 ^ n : ℝ) := by simp [δ_n, dyadicDelta] <;> field_simp <;> ring
      rw [h12] at h10 ⊢; field_simp at h10 ⊢ <;> linarith
    have h_round_eq : roundInt (m / δ_n) = a_raw := by rfl
    rw [h_round_eq]
    have h_goal : (2 ^ n : ℤ) - 1 ≤ a_raw := by omega
    rw [min_eq_right h_goal]
    have h14 : (↑((2 ^ n : ℤ) - 1) : ℝ) * δ_n = 1 - δ_n := by
      have h15 : (2 ^ n : ℝ) * δ_n = 1 := by
        have h16 : δ_n = 1 / (2 ^ n : ℝ) := by
          simp [δ_n, dyadicDelta] <;> field_simp <;> ring
        rw [h16]; field_simp <;> ring
      have h17 : (↑((2 ^ n : ℤ) - 1) : ℝ) = (2 ^ n : ℝ) - 1 := by
        have h18 : (1 : ℤ) ≤ (2 ^ n : ℤ) := by
          have h : (2 ^ n : ℕ) ≥ 1 := by apply Nat.one_le_pow <;> norm_num
          exact_mod_cast h
        have h19 : (↑((2 ^ n : ℤ) - 1) : ℝ) = (↑(2 ^ n : ℤ) : ℝ) - 1 := by
          rw [Int.cast_sub (2 ^ n : ℤ) 1] <;> norm_cast
        rw [h19]
        have h20 : (↑(2 ^ n : ℤ) : ℝ) = (2 ^ n : ℝ) := by norm_cast
        rw [h20]
      rw [h17]; linarith [h15]
    rw [h14]
    have h15 : |m - (1 - δ_n)| ≤ δ_n := by
      rw [abs_le]; constructor <;> linarith [h11, h_m_le_one]
    exact h15

/-- Clamp-aware slope bound: |snapped_slope| ≤ 3/2.
    Without clamp: |m'| ≤ |m| + δ_n/2 ≤ 3/2.
    With clamp: m' = 1 - δ_n ≤ 1. -/
lemma snap_slope_bound_3_2 {n : ℕ} {m : ℝ} (hm : |m| ≤ 1)
    (T : DyadicTube n) (hT_a : T.a = min (roundInt (m / dyadicDelta n)) ((2 ^ n : ℤ) - 1)) :
    |T.slope| ≤ 3 / 2 := by
  set δ_n := dyadicDelta n with hδn_def
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  let a_raw := roundInt (m / δ_n)
  have h_slope_eq : T.slope = (T.a : ℝ) * δ_n := by
    simp [DyadicTube.slope, hδn_def] <;> ring
  rw [h_slope_eq, hT_a]
  by_cases h : a_raw ≤ (2 ^ n : ℤ) - 1
  · rw [min_eq_left h]
    have h_eq : (a_raw : ℝ) * δ_n = δ_n * (roundInt (m / δ_n) : ℝ) := by
      simp [a_raw, mul_comm] <;> ring
    have h_err : |(a_raw : ℝ) * δ_n - m| ≤ δ_n / 2 :=
      rounding_error_bound m δ_n hδn_pos ((a_raw : ℝ) * δ_n) h_eq
    have h2 : |(a_raw : ℝ) * δ_n| ≤ |m| + |(a_raw : ℝ) * δ_n - m| := by
      calc |(a_raw : ℝ) * δ_n| = |m + ((a_raw : ℝ) * δ_n - m)| := by ring_nf
        _ ≤ |m| + |(a_raw : ℝ) * δ_n - m| := by exact real_abs_add m (↑a_raw * δ_n - m)
    linarith [dyadicDelta_le_one n]
  · -- Clamp activates
    have h_ge : (2 ^ n : ℤ) - 1 ≤ a_raw := by omega
    have h_round_eq : roundInt (m / δ_n) = a_raw := by rfl
    rw [h_round_eq, min_eq_right h_ge]
    have h14 : (↑((2 ^ n : ℤ) - 1) : ℝ) * δ_n = 1 - δ_n := by
      have h15 : (2 ^ n : ℝ) * δ_n = 1 := by
        have h16 : δ_n = 1 / (2 ^ n : ℝ) := by
          simp [δ_n, dyadicDelta] <;> field_simp <;> ring
        rw [h16]; field_simp <;> ring
      have h17 : (↑((2 ^ n : ℤ) - 1) : ℝ) = (↑(2 ^ n : ℤ) : ℝ) - 1 := by
        have h171 : ((2 ^ n : ℤ) - 1 : ℤ) = (2 ^ n : ℤ) - (1 : ℤ) := by rfl
        rw [h171]
        have h172 : ((↑((2 ^ n : ℤ) - (1 : ℤ)) : ℝ)) = (↑(2 ^ n : ℤ) : ℝ) - (↑(1 : ℤ) : ℝ) := by
          exact Int.cast_sub (2 ^ n) 1
        rw [h172]
        <;> norm_cast
      have h18 : (↑(2 ^ n : ℤ) : ℝ) = (2 ^ n : ℝ) := by norm_cast
      rw [h17, h18]
      rw [sub_mul, h15] <;> ring
    rw [h14]
    have hδn_le_one : δ_n ≤ 1 := dyadicDelta_le_one n
    have h_nonneg : 0 ≤ (1 : ℝ) - δ_n := by linarith
    rw [abs_of_nonneg h_nonneg] <;> linarith

/-! ============================================================================
   Intercept bound
   ============================================================================ -/

/-- Intercept bound for snapped tube: |intercept| ≤ 3. -/
lemma snap_intercept_bound {n : ℕ} {δ : ℝ} (hδn_leδ : dyadicDelta n ≤ δ)
    (ℓ : AffineLine) (p : EuclideanSpace ℝ (Fin 2))
    (hv0 : (LemmaE.getDirV ℓ) 0 ≠ 0)
    (hm_slope : |(affineLineSlopeIntercept ℓ).1| ≤ 1)
    (hp_ball : p ∈ Metric.closedBall 0 1) :
    |(snapToTubeThroughPoint n ℓ p).intercept| ≤ 3 := by
  set m := (affineLineSlopeIntercept ℓ).1 with hm_def
  set T := snapToTubeThroughPoint n ℓ p with hT_def
  set m' := T.slope with hm'_def
  set c' := T.intercept with hc'_def
  set δ_n := dyadicDelta n with hδn_def
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  have h1 : T.a = min (roundInt (m / δ_n)) ((2 ^ n : ℤ) - 1) := by
    simp [hT_def, snapToTubeThroughPoint] <;> rfl
  have h_m'_bound : |m'| ≤ 3 / 2 := by
    have h2 : m' = T.slope := by simp [hm'_def]
    rw [h2]
    exact snap_slope_bound_3_2 hm_slope T h1
  have h_Tb : T.b = Int.floor ((p 1 - m' * p 0) / δ_n) := by
    have h_def : T.b = Int.floor ((p 1 - (T.a : ℝ) * δ_n * p 0) / δ_n) := by
      simpa [hT_def, snapToTubeThroughPoint, hδn_def] using rfl
    have h_slope_eq : m' = (T.a : ℝ) * δ_n := by
      simp [hm'_def, DyadicTube.slope, hδn_def] <;> ring
    rw [h_def, h_slope_eq]
  have h_c'_eq : c' = δ_n * (Int.floor ((p 1 - m' * p 0) / δ_n) : ℝ) := by
    have h2 : c' = (T.b : ℝ) * δ_n := by
      simp [hc'_def, DyadicTube.intercept, hδn_def] <;> ring
    rw [h2, h_Tb] <;> ring
  have h_floor_err : |c' - (p 1 - m' * p 0)| ≤ δ_n := by
    let x : ℝ := (p 1 - m' * p 0) / δ_n
    have h1 : (Int.floor x : ℝ) ≤ x := Int.floor_le x
    have h2 : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
    have h3 : c' ≤ p 1 - m' * p 0 := by
      have h4 : c' = δ_n * (Int.floor x : ℝ) := by simpa [x, h_c'_eq] using rfl
      rw [h4]
      have h5 : δ_n * (Int.floor x : ℝ) ≤ δ_n * x := by gcongr
      have h6 : δ_n * x = p 1 - m' * p 0 := by
        simp [x] <;> field_simp [hδn_pos.ne'] <;> ring
      rw [h6] at h5; exact h5
    have h4 : p 1 - m' * p 0 < c' + δ_n := by
      have h5 : c' = δ_n * (Int.floor x : ℝ) := by simpa [x, h_c'_eq] using rfl
      rw [h5]
      have h6 : δ_n * x < δ_n * ((Int.floor x : ℝ) + 1) := by gcongr
      have h7 : δ_n * x = p 1 - m' * p 0 := by
        simp [x] <;> field_simp [hδn_pos.ne'] <;> ring
      rw [h7] at h6; linarith
    have h5 : 0 ≤ (p 1 - m' * p 0) - c' := by linarith
    have h6 : (p 1 - m' * p 0) - c' < δ_n := by linarith
    have h7 : |c' - (p 1 - m' * p 0)| = (p 1 - m' * p 0) - c' := by
      rw [abs_of_nonpos] <;> linarith
    rw [h7] <;> linarith
  have h_p0 : |p 0| ≤ 1 := by
    have h : |p 0| ≤ ‖p‖ := coord_abs_le_norm p 0
    have h2 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp_ball
    linarith
  have h_p1 : |p 1| ≤ 1 := by
    have h : |p 1| ≤ ‖p‖ := coord_abs_le_norm p 1
    have h2 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp_ball
    linarith
  by_cases hn : n = 0
  · -- Case n = 0: δ_n = 1, prove |m'| ≤ 1, then |c'| ≤ 1 + 1 + 1 = 3
    subst hn
    have hδn_eq_one : δ_n = 1 := by simp [hδn_def, dyadicDelta] <;> norm_num
    have h_round_bounds : -1 ≤ roundInt m ∧ roundInt m ≤ 1 := by
      have hme1 : -1 ≤ m := by linarith [abs_le.mp hm_slope]
      have hm1 : m ≤ 1 := by linarith [abs_le.mp hm_slope]
      have h_eq : roundInt m = Int.floor (m + 1 / 2) := by
        simp [roundInt]
      have h_le : (roundInt m : ℝ) ≤ m + 1 / 2 := by
        rw [h_eq]; exact_mod_cast Int.floor_le (m + 1 / 2)
      have h_gt : (m + 1 / 2 : ℝ) < (roundInt m : ℝ) + 1 := by
        rw [h_eq]; exact_mod_cast Int.lt_floor_add_one (m + 1 / 2)
      have h_lower : (-3 / 2 : ℝ) < (roundInt m : ℝ) := by linarith
      have h_upper : (roundInt m : ℝ) ≤ (3 / 2 : ℝ) := by linarith
      constructor
      · by_contra h; have h' : roundInt m ≤ -2 := by omega
        have : (roundInt m : ℝ) ≤ -2 := by exact_mod_cast h'
        linarith
      · by_contra h; have h' : roundInt m ≥ 2 := by omega
        have : (roundInt m : ℝ) ≥ 2 := by exact_mod_cast h'
        linarith
    have hdiv : m / δ_n = m := by
      rw [hδn_eq_one] <;> ring
    have h1' : T.a = min (roundInt m) 0 := by
      rw [h1, hdiv] <;> simp <;> norm_num
    have ha_bounds : -1 ≤ T.a ∧ T.a ≤ 0 := by
      rw [h1']
      have h21 : -1 ≤ roundInt m := h_round_bounds.1
      have h22 : roundInt m ≤ 1 := h_round_bounds.2
      constructor
      · have hmin1 : -1 ≤ min (roundInt m) (0 : ℤ) := le_min h21 (by norm_num)
        exact hmin1
      · exact min_le_right _ _
    have hm'_eq_one : m' = (T.a : ℝ) := by
      have h : m' = (T.a : ℝ) * δ_n := by
        simp [hm'_def, DyadicTube.slope, hδn_def] <;> ring
      rw [h, hδn_eq_one] <;> ring
    have h_m'_le_one : |m'| ≤ 1 := by
      rw [hm'_eq_one]
      have h1 : -1 ≤ (T.a : ℝ) := by exact_mod_cast ha_bounds.1
      have h2 : (T.a : ℝ) ≤ 0 := by exact_mod_cast ha_bounds.2
      rw [abs_le]; constructor <;> linarith
    have h_tri : |c'| ≤ |p 1| + |m'| * |p 0| + |c' - (p 1 - m' * p 0)| := by
      have h_eq : c' = (p 1 - m' * p 0) + (c' - (p 1 - m' * p 0)) := by ring
      have h2 : |(p 1 - m' * p 0) + (c' - (p 1 - m' * p 0))| ≤ |p 1 - m' * p 0| + |c' - (p 1 - m' * p 0)| :=
        abs_add_le _ _
      have h3 : |p 1 - m' * p 0| ≤ |p 1| + |m' * p 0| := by
        simpa [sub_eq_add_neg] using abs_add_le (p 1) (-(m' * p 0))
      have h4 : |m' * p 0| = |m'| * |p 0| := abs_mul _ _
      have h5 : |p 1 - m' * p 0| ≤ |p 1| + |m'| * |p 0| := by
        calc |p 1 - m' * p 0| ≤ |p 1| + |m' * p 0| := h3
          _ = |p 1| + |m'| * |p 0| := by rw [h4]
      have h6 : |(p 1 - m' * p 0) + (c' - (p 1 - m' * p 0))| ≤ (|p 1| + |m'| * |p 0|) + |c' - (p 1 - m' * p 0)| := by
        calc |(p 1 - m' * p 0) + (c' - (p 1 - m' * p 0))|
          ≤ |p 1 - m' * p 0| + |c' - (p 1 - m' * p 0)| := h2
        _ ≤ (|p 1| + |m'| * |p 0|) + |c' - (p 1 - m' * p 0)| := by exact add_le_add h5 (le_refl _)
      have h7 : |c'| = |(p 1 - m' * p 0) + (c' - (p 1 - m' * p 0))| := congr_arg abs h_eq
      rw [h7]; exact h6
    have hδn_one : δ_n = 1 := by simp [hδn_def, dyadicDelta] <;> norm_num
    have h_floor_err' : |c' - (p 1 - m' * p 0)| ≤ 1 := by
      rw [hδn_one] at h_floor_err; exact h_floor_err
    have h_goal : |c'| ≤ 3 := by
      calc |c'|
        ≤ |p 1| + |m'| * |p 0| + |c' - (p 1 - m' * p 0)| := h_tri
      _ ≤ 1 + 1 * 1 + 1 := by
        gcongr <;> linarith [abs_le.mp h_p0, abs_le.mp h_p1, abs_le.mp h_m'_le_one, abs_le.mp h_floor_err']
      _ = 3 := by norm_num
    exact h_goal
  · -- Case n ≥ 1: δ_n ≤ 1/2, use general bound 1 + 3/2 + 1/2 = 3
    have hn' : n ≥ 1 := by omega
    have hδn_le_half : δ_n ≤ 1 / 2 := dyadicDelta_le_half n hn'
    have h_tri : |c'| ≤ |p 1| + |m'| * |p 0| + |c' - (p 1 - m' * p 0)| := by
      have h_eq : c' = (p 1 - m' * p 0) + (c' - (p 1 - m' * p 0)) := by ring
      have h2 : |(p 1 - m' * p 0) + (c' - (p 1 - m' * p 0))| ≤ |p 1 - m' * p 0| + |c' - (p 1 - m' * p 0)| :=
        abs_add_le _ _
      have h3 : |p 1 - m' * p 0| ≤ |p 1| + |m' * p 0| := by
        simpa [sub_eq_add_neg] using abs_add_le (p 1) (-(m' * p 0))
      have h4 : |m' * p 0| = |m'| * |p 0| := abs_mul _ _
      have h5 : |p 1 - m' * p 0| ≤ |p 1| + |m'| * |p 0| := by
        calc |p 1 - m' * p 0| ≤ |p 1| + |m' * p 0| := h3
          _ = |p 1| + |m'| * |p 0| := by rw [h4]
      have h6 : |(p 1 - m' * p 0) + (c' - (p 1 - m' * p 0))| ≤ (|p 1| + |m'| * |p 0|) + |c' - (p 1 - m' * p 0)| := by
        calc |(p 1 - m' * p 0) + (c' - (p 1 - m' * p 0))|
          ≤ |p 1 - m' * p 0| + |c' - (p 1 - m' * p 0)| := h2
        _ ≤ (|p 1| + |m'| * |p 0|) + |c' - (p 1 - m' * p 0)| := by exact add_le_add h5 (le_refl _)
      have h7 : |c'| = |(p 1 - m' * p 0) + (c' - (p 1 - m' * p 0))| := congr_arg abs h_eq
      rw [h7]; exact h6
    have h_mul : |m'| * |p 0| ≤ 3 / 2 := by
      calc |m'| * |p 0| ≤ (3 / 2 : ℝ) * 1 := by gcongr <;> linarith
        _ = 3 / 2 := by ring
    linarith [h_tri, h_p0, h_p1, h_floor_err, h_mul, hδn_le_half]

/-- Movement bound: the center line of the snapped tube is within 15/2 δ of ℓ.
    Requires |slope| ≤ 1, p in unit ball, p within δ of ℓ, δ ≤ 1.
    With floor-based b, intercept error is δ_n (not δ_n/2), giving 15/2 δ. -/
lemma snap_movement_bound {n : ℕ} {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hδn_leδ : dyadicDelta n ≤ δ)
    (ℓ : AffineLine) (p : EuclideanSpace ℝ (Fin 2))
    (hv0 : (LemmaE.getDirV ℓ) 0 ≠ 0)
    (hm_slope : |(affineLineSlopeIntercept ℓ).1| ≤ 1)
    (hp_ball : p ∈ Metric.closedBall 0 1)
    (hp_near : p ∈ Metric.cthickening δ ℓ.1) :
    AffineLine.dist ℓ (toAffineLine (snapToTubeThroughPoint n ℓ p)) ≤ (15 / 2 : ℝ) * δ := by
  set m := (affineLineSlopeIntercept ℓ).1 with hm_def
  set c := (affineLineSlopeIntercept ℓ).2 with hc_def
  set T := snapToTubeThroughPoint n ℓ p with hT_def
  set m' := T.slope with hm'_def
  set c' := T.intercept with hc'_def
  set ℓ' := toAffineLine T with hℓ'_def
  set δ_n := dyadicDelta n with hδn_def

  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  have hℓ_eq : ℓ = lineOfSlopeIntercept m c := line_eq_lineOfSlopeIntercept ℓ hv0

  have h1 : T.a = min (roundInt (m / δ_n)) ((2 ^ n : ℤ) - 1) := by
    simp [hT_def, snapToTubeThroughPoint] <;> rfl
  have h_slope_err : |m - m'| ≤ δ_n := by
    have h2 : m' = T.slope := by simp [hm'_def]
    rw [h2]
    exact snap_slope_err_clamp hm_slope T h1
  have h_m'_bound : |m'| ≤ 3 / 2 := by
    have h2 : m' = T.slope := by simp [hm'_def]
    rw [h2]
    exact snap_slope_bound_3_2 hm_slope T h1

  have h_Tb : T.b = Int.floor ((p 1 - m' * p 0) / δ_n) := by
    have h_def : T.b = Int.floor ((p 1 - (T.a : ℝ) * δ_n * p 0) / δ_n) := by
      simpa [hT_def, snapToTubeThroughPoint, hδn_def] using rfl
    have h_slope_eq : m' = (T.a : ℝ) * δ_n := by
      simp [hm'_def, DyadicTube.slope, hδn_def] <;> ring
    rw [h_def, h_slope_eq]
  have h_c'_eq : c' = δ_n * (Int.floor ((p 1 - m' * p 0) / δ_n) : ℝ) := by
    have h2 : c' = (T.b : ℝ) * δ_n := by
      simp [hc'_def, DyadicTube.intercept, hδn_def] <;> ring
    rw [h2, h_Tb] <;> ring
  have h_floor_err : |c' - (p 1 - m' * p 0)| ≤ δ_n := by
    let x : ℝ := (p 1 - m' * p 0) / δ_n
    have h1 : (Int.floor x : ℝ) ≤ x := Int.floor_le x
    have h2 : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
    have h3 : c' ≤ p 1 - m' * p 0 := by
      have h4 : c' = δ_n * (Int.floor x : ℝ) := by simpa [x, h_c'_eq] using rfl
      rw [h4]
      have h5 : δ_n * (Int.floor x : ℝ) ≤ δ_n * x := by gcongr
      have h6 : δ_n * x = p 1 - m' * p 0 := by
        simp [x] <;> field_simp [hδn_pos.ne'] <;> ring
      rw [h6] at h5; exact h5
    have h4 : p 1 - m' * p 0 < c' + δ_n := by
      have h5 : c' = δ_n * (Int.floor x : ℝ) := by simpa [x, h_c'_eq] using rfl
      rw [h5]
      have h6 : δ_n * x < δ_n * ((Int.floor x : ℝ) + 1) := by gcongr
      have h7 : δ_n * x = p 1 - m' * p 0 := by
        simp [x] <;> field_simp [hδn_pos.ne'] <;> ring
      rw [h7] at h6; linarith
    have h5 : 0 ≤ (p 1 - m' * p 0) - c' := by linarith
    have h6 : (p 1 - m' * p 0) - c' < δ_n := by linarith
    have h7 : |c' - (p 1 - m' * p 0)| = (p 1 - m' * p 0) - c' := by
      rw [abs_of_nonpos] <;> linarith
    rw [h7] <;> linarith

  have h_p0 : |p 0| ≤ 1 := by
    have h : |p 0| ≤ ‖p‖ := coord_abs_le_norm p 0
    have h2 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp_ball
    linarith
  have h_p1 : |p 1| ≤ 1 := by
    have h : |p 1| ≤ ‖p‖ := coord_abs_le_norm p 1
    have h2 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp_ball
    linarith

  -- Vertical distance from p to ℓ
  have h_inf : Metric.infDist p ℓ.1 ≤ δ := by
    have h_edist : Metric.infEDist p ℓ.1 ≤ ENNReal.ofReal δ := by
      simpa [Metric.cthickening] using hp_near
    have h_eq : Metric.infDist p ℓ.1 = ENNReal.toReal (Metric.infEDist p ℓ.1) := by rfl
    have h_ne_top : (ENNReal.ofReal δ) ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [h_eq]
    have h : ENNReal.toReal (Metric.infEDist p ℓ.1) ≤ ENNReal.toReal (ENNReal.ofReal δ) :=
      ENNReal.toReal_mono h_ne_top h_edist
    have h_ofReal : ENNReal.toReal (ENNReal.ofReal δ) = δ :=
      ENNReal.toReal_ofReal hδ_pos.le
    rw [h_ofReal] at h
    exact h
  rw [hℓ_eq] at h_inf
  let n_vec : EuclideanSpace ℝ (Fin 2) := TubesAndSlopes.mkPlane (-m) 1
  have hn_norm : ‖n_vec‖ = Real.sqrt (1 + m^2) := by
    simp [n_vec, EuclideanSpace.norm_eq, Fin.sum_univ_two,
      TubesAndSlopes.mkPlane_apply0, TubesAndSlopes.mkPlane_apply1] <;> ring_nf
  have h_main : ∀ (q : EuclideanSpace ℝ (Fin 2)), q ∈ (lineOfSlopeIntercept m c).1 →
      |p 1 - m * p 0 - c| ≤ ‖n_vec‖ * ‖p - q‖ := by
    intro q hq
    have hq_line : q 1 = m * q 0 + c := by
      have hq' : q - TubesAndSlopes.mkPlane 0 c ∈ Submodule.span ℝ {tubeDirV m} := hq
      have h_exists : ∃ (t : ℝ), q - TubesAndSlopes.mkPlane 0 c = t • tubeDirV m := by
        have h : ∃ (a : ℝ), a • tubeDirV m = q - TubesAndSlopes.mkPlane 0 c := by
          simpa [Submodule.mem_span_singleton] using hq'
        rcases h with ⟨a, ha⟩
        exact ⟨a, ha.symm⟩
      rcases h_exists with ⟨t, ht⟩
      have hq0 : q 0 = t := by
        have h : (q - TubesAndSlopes.mkPlane 0 c) 0 = t := by
          rw [ht]; simp [tubeDirV, TubesAndSlopes.mkPlane_apply0] <;> ring
        simpa [TubesAndSlopes.mkPlane_apply0] using h
      have hq1 : q 1 = c + t * m := by
        have h : (q - TubesAndSlopes.mkPlane 0 c) 1 = t * m := by
          rw [ht]; simp [tubeDirV, TubesAndSlopes.mkPlane_apply1] <;> ring
        have h' : q 1 - c = t * m := by simpa [TubesAndSlopes.mkPlane_apply1] using h
        linarith
      rw [hq1, hq0] <;> ring
    have h_dot : (p 1 - m * p 0 - c) = (-m) * (p 0 - q 0) + (p 1 - q 1) := by linarith
    rw [h_dot]
    have h2 : ((-m) * (p 0 - q 0) + (p 1 - q 1)) ^ 2 ≤ ‖n_vec‖ ^ 2 * ‖p - q‖ ^ 2 := by
      have h3 : ‖n_vec‖ ^ 2 = m^2 + 1 := by
        rw [hn_norm]
        have h4 : Real.sqrt (1 + m^2) ^ 2 = 1 + m^2 := Real.sq_sqrt (by nlinarith)
        linarith
      have h4 : ‖p - q‖ ^ 2 = (p 0 - q 0)^2 + (p 1 - q 1)^2 := by
        have h41 : ‖p - q‖ ^ 2 = ((p - q) 0)^2 + ((p - q) 1)^2 := by
          rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
        rw [h41]
        have h42 : (p - q) 0 = p 0 - q 0 := by rfl
        have h43 : (p - q) 1 = p 1 - q 1 := by rfl
        rw [h42, h43] <;> ring
      rw [h3, h4]
      have h_cs : ((-m) * (p 0 - q 0) + (p 1 - q 1)) ^ 2 ≤ (m^2 + 1) * ((p 0 - q 0)^2 + (p 1 - q 1)^2) := by
        have h_id : (m^2 + 1) * ((p 0 - q 0)^2 + (p 1 - q 1)^2) - ((-m) * (p 0 - q 0) + (p 1 - q 1)) ^ 2 =
            ((-m) * (p 1 - q 1) - (p 0 - q 0)) ^ 2 := by ring
        have h_nonneg : 0 ≤ ((-m) * (p 1 - q 1) - (p 0 - q 0)) ^ 2 := by positivity
        linarith
      exact h_cs
    have h5 : 0 ≤ ‖n_vec‖ * ‖p - q‖ := by positivity
    have h6 : ((-m) * (p 0 - q 0) + (p 1 - q 1)) ^ 2 ≤ (‖n_vec‖ * ‖p - q‖) ^ 2 := by
      have h7 : (‖n_vec‖ * ‖p - q‖) ^ 2 = ‖n_vec‖ ^ 2 * ‖p - q‖ ^ 2 := by ring
      rw [h7]; exact h2
    have h8 : |(-m) * (p 0 - q 0) + (p 1 - q 1)| ≤ ‖n_vec‖ * ‖p - q‖ := by
      have h_pos : 0 ≤ ‖n_vec‖ * ‖p - q‖ := by positivity
      nlinarith [sq_abs ((-m) * (p 0 - q 0) + (p 1 - q 1))]
    exact h8
  have h_nonempty : ((lineOfSlopeIntercept m c).1 : Set (EuclideanSpace ℝ (Fin 2))).Nonempty :=
    (lineOfSlopeIntercept m c).nonempty
  have hn_pos : 0 < ‖n_vec‖ := by
    rw [hn_norm] <;> positivity
  have h_vert : |p 1 - m * p 0 - c| ≤ ‖n_vec‖ * Metric.infDist p (lineOfSlopeIntercept m c).1 := by
    have h9 : ∀ q ∈ (lineOfSlopeIntercept m c).1, |p 1 - m * p 0 - c| / ‖n_vec‖ ≤ ‖p - q‖ := by
      intro q hq
      have h10 := h_main q hq
      calc |p 1 - m * p 0 - c| / ‖n_vec‖
        ≤ (‖n_vec‖ * ‖p - q‖) / ‖n_vec‖ := by gcongr
      _ = ‖p - q‖ := by field_simp [hn_pos.ne'] <;> ring
    have h12 : |p 1 - m * p 0 - c| / ‖n_vec‖ ≤ Metric.infDist p (lineOfSlopeIntercept m c).1 := by
      have h_lower : ∀ y ∈ Set.image (dist p) (lineOfSlopeIntercept m c).1,
          |p 1 - m * p 0 - c| / ‖n_vec‖ ≤ y := by
        intro y hy
        rcases hy with ⟨q, hq, rfl⟩
        exact h9 q hq
      have h_glb : IsGLB (Set.image (dist p) (lineOfSlopeIntercept m c).1) (Metric.infDist p (lineOfSlopeIntercept m c).1) :=
        Metric.isGLB_infDist h_nonempty
      have h_in_lower : |p 1 - m * p 0 - c| / ‖n_vec‖ ∈ lowerBounds (Set.image (dist p) (lineOfSlopeIntercept m c).1) :=
        h_lower
      exact (Metric.le_infDist h_nonempty).mpr h9
    calc |p 1 - m * p 0 - c|
      = ‖n_vec‖ * (|p 1 - m * p 0 - c| / ‖n_vec‖) := by field_simp [hn_pos.ne'] <;> ring
    _ ≤ ‖n_vec‖ * Metric.infDist p (lineOfSlopeIntercept m c).1 := by gcongr
  have h_vert_dist : |p 1 - m * p 0 - c| ≤ δ * Real.sqrt 2 := by
    rw [hn_norm] at h_vert
    have h13 : Metric.infDist p (lineOfSlopeIntercept m c).1 ≤ δ := h_inf
    have h14 : Real.sqrt (1 + m^2) ≤ Real.sqrt 2 := by
      have h15 : 1 + m^2 ≤ 2 := by nlinarith [abs_le.mp hm_slope]
      exact Real.sqrt_le_sqrt h15
    nlinarith
  have h_int_err : |c - c'| ≤ δ * (Real.sqrt 2 + 2) := by
    have h_decomp : c - c' = (c - (p 1 - m * p 0)) + (m' - m) * p 0 + ((p 1 - m' * p 0) - c') := by ring
    rw [h_decomp]
    have h_tri := abs_add_three (c - (p 1 - m * p 0)) ((m' - m) * p 0) ((p 1 - m' * p 0) - c')
    have h_abs_mul : |(m' - m) * p 0| ≤ δ_n := by
      calc |(m' - m) * p 0| = |m' - m| * |p 0| := by rw [abs_mul]
        _ = |m - m'| * |p 0| := by rw [abs_sub_comm]
        _ ≤ δ_n * 1 := by gcongr <;> linarith [h_slope_err, h_p0]
        _ = δ_n := by ring
    have h1 : |c - (p 1 - m * p 0)| = |p 1 - m * p 0 - c| := by rw [show c - (p 1 - m * p 0) = -(p 1 - m * p 0 - c) by ring, abs_neg]
    have h2 : |(p 1 - m' * p 0) - c'| = |c' - (p 1 - m' * p 0)| := by rw [abs_sub_comm]
    linarith [h_tri, h_vert_dist, h_abs_mul, h_floor_err, hδn_leδ, h1, h2]
  have h_c'_bound : |c'| ≤ 3 :=
    snap_intercept_bound hδn_leδ ℓ p hv0 hm_slope hp_ball
  have h_proj : ‖ℓ.1.direction.starProjection - ℓ'.1.direction.starProjection‖ ≤ |m - m'| := by
    rw [hℓ_eq]
    have h_dir1 : (lineOfSlopeIntercept m c).1.direction = Submodule.span ℝ {tubeDirV m} :=
      lineOfSlopeIntercept_direction m c
    have h_dir2 : ℓ'.1.direction = Submodule.span ℝ {tubeDirV m'} := by
      simp [hℓ'_def, toAffineLine, lineOfSlopeIntercept_direction] <;> rfl
    rw [h_dir1, h_dir2]
    exact DyadicToAffineAdapters.proj_op_norm_bound m m'
  have h_off1 : ℓ.offset = c • offsetVec m := by
    have h : ℓ = lineOfSlopeIntercept m c := hℓ_eq
    rw [h]
    simp [toAffineLine, offset_formula]
    <;> exact offset_formula m c
  have h_off2 : ℓ'.offset = c' • offsetVec m' := by
    simp [hℓ'_def, toAffineLine] <;> exact offset_formula m' c'
  have h_offset : ‖ℓ.offset - ℓ'.offset‖ ≤ |c - c'| + 3 * |m - m'| := by
    rw [h_off1, h_off2]
    exact DyadicToAffineAdapters.offset_diff_upper m m' c c' h_c'_bound
  have h_dist : AffineLine.dist ℓ ℓ' =
      ‖ℓ.1.direction.starProjection - ℓ'.1.direction.starProjection‖ + ‖ℓ.offset - ℓ'.offset‖ := by rfl
  rw [h_dist]
  have h9 : |m - m'| ≤ δ := by
    calc |m - m'| ≤ δ_n := h_slope_err
      _ ≤ δ := by linarith [hδn_leδ]
  calc
    ‖ℓ.1.direction.starProjection - ℓ'.1.direction.starProjection‖ + ‖ℓ.offset - ℓ'.offset‖
      ≤ |m - m'| + (|c - c'| + 3 * |m - m'|) := by linarith
    _ = 4 * |m - m'| + |c - c'| := by ring
    _ ≤ 4 * δ + δ * (Real.sqrt 2 + 2) := by gcongr <;> linarith
    _ ≤ (15 / 2 : ℝ) * δ := by
      have h10 : Real.sqrt 2 ≤ 3 / 2 := by
        have h11 : (2 : ℝ) ≤ (3 / 2 : ℝ) ^ 2 := by norm_num
        have h12 : Real.sqrt 2 ≤ Real.sqrt ((3 / 2 : ℝ) ^ 2) := Real.sqrt_le_sqrt h11
        have h13 : Real.sqrt ((3 / 2 : ℝ) ^ 2) = 3 / 2 := by
          rw [Real.sqrt_sq_eq_abs] <;> norm_num
        rw [h13] at h12
        exact h12
      have h11 : 4 * δ + δ * (Real.sqrt 2 + 2) = δ * (6 + Real.sqrt 2) := by ring
      rw [h11]
      have h12 : δ * (6 + Real.sqrt 2) ≤ (15 / 2 : ℝ) * δ := by
        have h_sqrt2_le : Real.sqrt 2 ≤ 3 / 2 := by
          have h : (2 : ℝ) ≤ (3 / 2 : ℝ) ^ 2 := by norm_num
          have h2 : Real.sqrt 2 ≤ Real.sqrt ((3 / 2 : ℝ) ^ 2) := Real.sqrt_le_sqrt h
          have h3 : Real.sqrt ((3 / 2 : ℝ) ^ 2) = 3 / 2 := by
            rw [Real.sqrt_sq_eq_abs] <;> norm_num
          rw [h3] at h2
          exact h2
        have h13 : 6 + Real.sqrt 2 ≤ 15 / 2 := by
          calc 6 + Real.sqrt 2 ≤ 6 + 3 / 2 := by gcongr
            _ = 15 / 2 := by norm_num
        have h14 : 0 ≤ δ := by linarith
        have h15 : δ * (6 + Real.sqrt 2) ≤ δ * (15 / 2 : ℝ) := mul_le_mul_of_nonneg_left h13 h14
        have h16 : δ * (15 / 2 : ℝ) = (15 / 2 : ℝ) * δ := by ring
        rw [h16] at h15
        exact h15
      exact h12

/-- toAffineLine is 5-Lipschitz from L∞ parameter distance to AffineLine distance. -/
lemma toAffineLine_lipschitz_gen {n : ℕ} (T1 T2 : DyadicTube n)
    (hb2 : |T2.intercept| ≤ 3) :
    dist (toAffineLine T1) (toAffineLine T2) ≤ 5 * DyadicToAffineAdapters.paramDistLinf T1 T2 := by
  set m1 := T1.slope with hm1_def
  set m2 := T2.slope with hm2_def
  set b1 := T1.intercept with hb1_def
  set b2 := T2.intercept with hb2_def
  set ℓ1 := toAffineLine T1 with hℓ1
  set ℓ2 := toAffineLine T2 with hℓ2
  set d_inf := DyadicToAffineAdapters.paramDistLinf T1 T2 with hd_inf_def
  have hdm : |m1 - m2| ≤ d_inf := by
    dsimp only [d_inf, DyadicToAffineAdapters.paramDistLinf]; exact le_max_left _ _
  have hdb : |b1 - b2| ≤ d_inf := by
    dsimp only [d_inf, DyadicToAffineAdapters.paramDistLinf]; exact le_max_right _ _
  have h_proj_le : ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ ≤ |m1 - m2| := by
    have h_dir_eq1 : ℓ1.1.direction = Submodule.span ℝ {tubeDirV m1} := by
      rw [hℓ1]; exact lineOfSlopeIntercept_direction m1 b1
    have h_dir_eq2 : ℓ2.1.direction = Submodule.span ℝ {tubeDirV m2} := by
      rw [hℓ2]; exact lineOfSlopeIntercept_direction m2 b2
    rw [h_dir_eq1, h_dir_eq2]; exact DyadicToAffineAdapters.proj_op_norm_bound m1 m2
  have h_off1 : ℓ1.offset = b1 • offsetVec m1 := by
    rw [hℓ1]
    exact offset_formula m1 b1
  have h_off2 : ℓ2.offset = b2 • offsetVec m2 := by
    rw [hℓ2]
    exact offset_formula m2 b2
  have h_off_le : ‖ℓ1.offset - ℓ2.offset‖ ≤ |b1 - b2| + 3 * |m1 - m2| := by
    rw [h_off1, h_off2]; exact DyadicToAffineAdapters.offset_diff_upper m1 m2 b1 b2 hb2
  have h_def : dist ℓ1 ℓ2 =
      ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ +
      ‖ℓ1.offset - ℓ2.offset‖ := by rfl
  rw [h_def]
  calc
    ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ + ‖ℓ1.offset - ℓ2.offset‖
      ≤ |m1 - m2| + (|b1 - b2| + 3 * |m1 - m2|) := by linarith
    _ = 4 * |m1 - m2| + |b1 - b2| := by ring
    _ ≤ 4 * d_inf + d_inf := by gcongr
    _ = 5 * d_inf := by ring

/-! ============================================================================
   Diameter bound for snap image
   ============================================================================ -/

/-- Diameter bound: if dist_AL(ℓ1, ℓ2) ≤ 2δ, then dist_DT(snap(ℓ1), snap(ℓ2)) ≤ 11δ. -/
lemma snap_image_diameter {n : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδn_leδ : dyadicDelta n ≤ δ)
    (p : EuclideanSpace ℝ (Fin 2)) (hp_ball : p ∈ Metric.closedBall 0 1)
    {ℓ1 ℓ2 : AffineLine}
    (hv01 : (LemmaE.getDirV ℓ1) 0 ≠ 0) (hv02 : (LemmaE.getDirV ℓ2) 0 ≠ 0)
    (hm1 : |(affineLineSlopeIntercept ℓ1).1| ≤ 1)
    (hm2 : |(affineLineSlopeIntercept ℓ2).1| ≤ 1)
    (h_near1 : p ∈ Metric.cthickening δ ℓ1.1)
    (h_near2 : p ∈ Metric.cthickening δ ℓ2.1)
    (h_dist : AffineLine.dist ℓ1 ℓ2 ≤ 2 * δ) :
    dist (snapToTubeThroughPoint n ℓ1 p) (snapToTubeThroughPoint n ℓ2 p) ≤ 6 * dyadicDelta n + 8 * δ := by
  set δ_n := dyadicDelta n with hδn_def
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  set T1 := snapToTubeThroughPoint n ℓ1 p with hT1
  set T2 := snapToTubeThroughPoint n ℓ2 p with hT2
  set m1 := (affineLineSlopeIntercept ℓ1).1 with hm1_def
  set m2 := (affineLineSlopeIntercept ℓ2).1 with hm2_def
  set m1' := T1.slope with hm1'_def
  set m2' := T2.slope with hm2'_def
  set c1' := T1.intercept with hc1'_def
  set c2' := T2.intercept with hc2'_def

  have h_p0 : |p 0| ≤ 1 := by
    have h : |p 0| ≤ ‖p‖ := coord_abs_le_norm p 0
    have h2 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp_ball
    linarith

  have hℓ1_eq : ℓ1 = lineOfSlopeIntercept m1 (affineLineSlopeIntercept ℓ1).2 :=
    line_eq_lineOfSlopeIntercept ℓ1 hv01
  have hℓ2_eq : ℓ2 = lineOfSlopeIntercept m2 (affineLineSlopeIntercept ℓ2).2 :=
    line_eq_lineOfSlopeIntercept ℓ2 hv02
  have h_dir1 : ℓ1.1.direction = Submodule.span ℝ {tubeDirV m1} := by
    rw [hℓ1_eq]; exact lineOfSlopeIntercept_direction m1 _
  have h_dir2 : ℓ2.1.direction = Submodule.span ℝ {tubeDirV m2} := by
    rw [hℓ2_eq]; exact lineOfSlopeIntercept_direction m2 _
  have h_proj_lower : |m1 - m2| / 2 ≤
      ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ := by
    rw [h_dir1, h_dir2]; exact proj_lower_bound_simple m1 m2 hm1 hm2
  have h_proj_le_dist : ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ ≤
      AffineLine.dist ℓ1 ℓ2 := by
    have h : AffineLine.dist ℓ1 ℓ2 =
        ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ +
        ‖ℓ1.offset - ℓ2.offset‖ := by rfl
    rw [h]; linarith [norm_nonneg (ℓ1.offset - ℓ2.offset)]
  have h_slope_diff : |m1 - m2| ≤ 4 * δ := by
    calc |m1 - m2|
      = 2 * (|m1 - m2| / 2) := by ring
    _ ≤ 2 * ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ := by gcongr
    _ ≤ 2 * (AffineLine.dist ℓ1 ℓ2) := by gcongr
    _ ≤ 2 * (2 * δ) := by gcongr
    _ = 4 * δ := by ring

  have hT1_a : T1.a = min (roundInt (m1 / δ_n)) ((2 ^ n : ℤ) - 1) := by
    simp [hT1, snapToTubeThroughPoint] <;> rfl
  have hT2_a : T2.a = min (roundInt (m2 / δ_n)) ((2 ^ n : ℤ) - 1) := by
    simp [hT2, snapToTubeThroughPoint] <;> rfl
  have h_round1 : |m1 - m1'| ≤ δ_n := by
    have h2 : m1' = T1.slope := by simp [hm1'_def]
    rw [h2]
    exact snap_slope_err_clamp hm1 T1 hT1_a
  have h_round2 : |m2 - m2'| ≤ δ_n := by
    have h2 : m2' = T2.slope := by simp [hm2'_def]
    rw [h2]
    exact snap_slope_err_clamp hm2 T2 hT2_a

  have h_slope'_diff : |m1' - m2'| ≤ 2 * δ_n + |m1 - m2| := by
    have h1 : |m1' - m2'| ≤ |m1' - m1| + |m1 - m2| + |m2 - m2'| := by
      calc |m1' - m2'|
        = |(m1' - m1) + (m1 - m2) + (m2 - m2')| := by ring_nf
      _ ≤ |(m1' - m1) + (m1 - m2)| + |m2 - m2'| := abs_add_le ((m1' - m1) + (m1 - m2)) (m2 - m2')
      _ ≤ |m1' - m1| + |m1 - m2| + |m2 - m2'| := by
        have h2 : |(m1' - m1) + (m1 - m2)| ≤ |m1' - m1| + |m1 - m2| := abs_add_le (m1' - m1) (m1 - m2)
        linarith
    have h3 : |m1' - m1| = |m1 - m1'| := by rw [abs_sub_comm]
    linarith [h_round1, h_round2]

  have h_T1b : T1.b = Int.floor ((p 1 - m1' * p 0) / δ_n) := by
    have h_def : T1.b = Int.floor ((p 1 - (T1.a : ℝ) * δ_n * p 0) / δ_n) := by
      simpa [hT1, snapToTubeThroughPoint, hδn_def] using rfl
    have h_slope_eq : m1' = (T1.a : ℝ) * δ_n := by
      simp [hm1'_def, DyadicTube.slope, hδn_def] <;> ring
    rw [h_def, h_slope_eq]
  have h_c1'_eq : c1' = δ_n * (Int.floor ((p 1 - m1' * p 0) / δ_n) : ℝ) := by
    have h2 : c1' = (T1.b : ℝ) * δ_n := by
      simp [hc1'_def, DyadicTube.intercept, hδn_def] <;> ring
    rw [h2, h_T1b] <;> ring
  have h_cround1 : |c1' - (p 1 - m1' * p 0)| ≤ δ_n :=
    le_of_lt (floor_error_bound (p 1 - m1' * p 0) δ_n hδn_pos c1' h_c1'_eq)

  have h_T2b : T2.b = Int.floor ((p 1 - m2' * p 0) / δ_n) := by
    have h_def : T2.b = Int.floor ((p 1 - (T2.a : ℝ) * δ_n * p 0) / δ_n) := by
      simpa [hT2, snapToTubeThroughPoint, hδn_def] using rfl
    have h_slope_eq : m2' = (T2.a : ℝ) * δ_n := by
      simp [hm2'_def, DyadicTube.slope, hδn_def] <;> ring
    rw [h_def, h_slope_eq]
  have h_c2'_eq : c2' = δ_n * (Int.floor ((p 1 - m2' * p 0) / δ_n) : ℝ) := by
    have h2 : c2' = (T2.b : ℝ) * δ_n := by
      simp [hc2'_def, DyadicTube.intercept, hδn_def] <;> ring
    rw [h2, h_T2b] <;> ring
  have h_cround2 : |c2' - (p 1 - m2' * p 0)| ≤ δ_n :=
    le_of_lt (floor_error_bound (p 1 - m2' * p 0) δ_n hδn_pos c2' h_c2'_eq)

  have h_int'_diff : |c1' - c2'| ≤ 2 * δ_n + |m1' - m2'| := by
    have h1 : c1' - c2' = (c1' - (p 1 - m1' * p 0)) + ((p 1 - m1' * p 0) - (p 1 - m2' * p 0)) + ((p 1 - m2' * p 0) - c2') := by ring
    have h2 : |c1' - c2'| ≤ |c1' - (p 1 - m1' * p 0)| + |(p 1 - m1' * p 0) - (p 1 - m2' * p 0)| + |(p 1 - m2' * p 0) - c2'| := by
      rw [h1]
      exact abs_add_three _ _ _
    have h4 : |(p 1 - m1' * p 0) - (p 1 - m2' * p 0)| = |m1' - m2'| * |p 0| := by
      have h_eq : (p 1 - m1' * p 0) - (p 1 - m2' * p 0) = (m2' - m1') * p 0 := by ring
      rw [h_eq, abs_mul, abs_sub_comm] <;> rfl
    rw [h4] at h2
    have h_mul : |m1' - m2'| * |p 0| ≤ |m1' - m2'| := by
      have h_pos : 0 ≤ |m1' - m2'| := by positivity
      nlinarith
    have h_cround2' : |(p 1 - m2' * p 0) - c2'| ≤ δ_n := by
      rw [abs_sub_comm]
      exact h_cround2
    linarith [h2, h_cround1, h_cround2', h_mul]

  have h_dist_dt : dist T1 T2 = |m1' - m2'| + |c1' - c2'| := by
    simp [T1, T2, DyadicTube.dist, hm1'_def, hm2'_def, hc1'_def, hc2'_def] <;> rfl
  rw [h_dist_dt]
  have h_main : |m1' - m2'| + |c1' - c2'| ≤ 6 * δ_n + 8 * δ := by
    calc |m1' - m2'| + |c1' - c2'|
      ≤ |m1' - m2'| + (2 * δ_n + |m1' - m2'|) := by gcongr
    _ = 2 * |m1' - m2'| + 2 * δ_n := by ring
    _ ≤ 2 * (2 * δ_n + |m1 - m2|) + 2 * δ_n := by gcongr
    _ = 6 * δ_n + 2 * |m1 - m2| := by ring
    _ ≤ 6 * δ_n + 2 * (4 * δ) := by gcongr
    _ = 6 * δ_n + 8 * δ := by ring
  exact h_main

/-! ============================================================================
   Cardinality bound for bounded DyadicTube sets
   ============================================================================ -/

/-- A set of DyadicTubes within distance 30δ_n of T0 has at most 3721 elements. -/
lemma dyadicTube_ball30_card {n : ℕ} {A : Set (DyadicTube n)} {T0 : DyadicTube n}
    (hA : A ⊆ Metric.closedBall T0 (30 * dyadicDelta n)) :
    A.encard ≤ 3721 := by
  set δ_n := dyadicDelta n with hδn
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  have h1 : ∀ T ∈ A, (Int.natAbs (T.a - T0.a) : ℝ) + (Int.natAbs (T.b - T0.b) : ℝ) ≤ 30 := by
    intro T hT
    have h2 : dist T T0 ≤ 30 * δ_n := hA hT
    have h3 : dist T T0 = T.dist T0 := by rfl
    rw [h3] at h2
    have h4 : T.dist T0 = δ_n * ((Int.natAbs (T.a - T0.a) : ℝ) + (Int.natAbs (T.b - T0.b) : ℝ)) := by
      have h5 := DyadicTube.dist_eq T T0
      have h_abs : ∀ (z : ℤ), (|(z : ℝ)|) = (Int.natAbs z : ℝ) := by
        intro z
        exact int_natAbs_cast_abs z
      have h6 : (|(T.a - T0.a : ℤ)| : ℝ) = (Int.natAbs (T.a - T0.a) : ℝ) := h_abs (T.a - T0.a)
      have h7 : (|(T.b - T0.b : ℤ)| : ℝ) = (Int.natAbs (T.b - T0.b) : ℝ) := h_abs (T.b - T0.b)
      rw [h5, h6, h7, ←hδn]
    rw [h4] at h2
    nlinarith
  have h2 : ∀ T ∈ A, Int.natAbs (T.a - T0.a) ≤ 30 := by
    intro T hT
    have h3 : (Int.natAbs (T.a - T0.a) : ℝ) + (Int.natAbs (T.b - T0.b) : ℝ) ≤ 30 := h1 T hT
    have h4 : 0 ≤ (Int.natAbs (T.b - T0.b) : ℝ) := by positivity
    have h5 : (Int.natAbs (T.a - T0.a) : ℝ) ≤ 30 := by linarith
    by_contra h6
    have h7 : 31 ≤ Int.natAbs (T.a - T0.a) := by omega
    have h8 : (31 : ℝ) ≤ (Int.natAbs (T.a - T0.a) : ℝ) := by exact_mod_cast h7
    linarith
  have h3 : ∀ T ∈ A, Int.natAbs (T.b - T0.b) ≤ 30 := by
    intro T hT
    have h4 : (Int.natAbs (T.a - T0.a) : ℝ) + (Int.natAbs (T.b - T0.b) : ℝ) ≤ 30 := h1 T hT
    have h5 : 0 ≤ (Int.natAbs (T.a - T0.a) : ℝ) := by positivity
    have h6 : (Int.natAbs (T.b - T0.b) : ℝ) ≤ 30 := by linarith
    by_contra h7
    have h8 : 31 ≤ Int.natAbs (T.b - T0.b) := by omega
    have h9 : (31 : ℝ) ≤ (Int.natAbs (T.b - T0.b) : ℝ) := by exact_mod_cast h8
    linarith
  let f : DyadicTube n → ℤ × ℤ := fun T => (T.a, T.b)
  have h_inj : Set.InjOn f A := by
    intro T1 hT1 T2 hT2 h
    have ha : T1.a = T2.a := by simp [f] at h <;> exact h.1
    have hb : T1.b = T2.b := by simp [f] at h <;> exact h.2
    have h_slope : T1.slope = T2.slope := by simp [DyadicTube.slope, ha] <;> ring
    have h_intercept : T1.intercept = T2.intercept := by simp [DyadicTube.intercept, hb] <;> ring
    have h_dist : T1.dist T2 = 0 := by
      have h := DyadicTube.dist_eq T1 T2
      rw [h]
      have h1 : (|(T1.a - T2.a : ℤ)| : ℝ) = 0 := by
        have h2 : T1.a = T2.a := ha
        rw [h2] <;> norm_num
      have h2 : (|(T1.b - T2.b : ℤ)| : ℝ) = 0 := by
        have h3 : T1.b = T2.b := hb
        rw [h3] <;> norm_num
      rw [h1, h2] <;> ring
    exact DyadicTube.eq_of_dist_eq_zero T1 T2 h_dist
  let I : Finset ℤ := Finset.Icc (T0.a - 30) (T0.a + 30)
  let J : Finset ℤ := Finset.Icc (T0.b - 30) (T0.b + 30)
  have h4 : f '' A ⊆ (I ×ˢ J : Set (ℤ × ℤ)) := by
    intro z hz
    rcases hz with ⟨T, hT, rfl⟩
    have h5 : Int.natAbs (T.a - T0.a) ≤ 30 := h2 T hT
    have h6 : Int.natAbs (T.b - T0.b) ≤ 30 := h3 T hT
    have h7 : T0.a - 30 ≤ T.a := by omega
    have h9 : T.a ≤ T0.a + 30 := by omega
    have h11 : T0.b - 30 ≤ T.b := by omega
    have h13 : T.b ≤ T0.b + 30 := by omega
    have h15 : T.a ∈ I := by
      simp only [I, Finset.mem_Icc]; exact ⟨h7, h9⟩
    have h16 : T.b ∈ J := by
      simp only [J, Finset.mem_Icc]; exact ⟨h11, h13⟩
    exact ⟨h15, h16⟩
  have h_fin : (f '' A).Finite := by
    apply Set.Finite.subset (Finset.finite_toSet (I ×ˢ J))
    simpa [Finset.coe_product] using h4
  have h5 : (f '' A).encard ≤ (I ×ˢ J : Set (ℤ × ℤ)).encard := Set.encard_mono h4
  have h6 : (I ×ˢ J : Set (ℤ × ℤ)).encard = ↑(I ×ˢ J).card := by simp
  have h7 : (I ×ˢ J).card = I.card * J.card := Finset.card_product _ _
  have h8 : I.card = 61 := by
    rw [Int.card_Icc]
    have h_eq : (T0.a + 30) + 1 - (T0.a - 30) = (61 : ℤ) := by ring
    rw [h_eq]
    <;> simp
  have h9 : J.card = 61 := by
    rw [Int.card_Icc]
    have h_eq : (T0.b + 30) + 1 - (T0.b - 30) = (61 : ℤ) := by ring
    rw [h_eq]
    <;> simp
  have h10 : (I ×ˢ J).card = 3721 := by
    rw [h7, h8, h9] <;> norm_num
  rw [h6, h10] at h5
  have h11 : (f '' A).encard = A.encard := h_inj.encard_image
  rw [h11] at h5
  exact h5

/-- Any set of dyadic tubes within distance 52·δ_n of a fixed tube has at most
    (2·52+1)² = 105² = 11025 elements. Factor-4 version of `dyadicTube_ball30_card`. -/
lemma dyadicTube_ball52_card {n : ℕ} {A : Set (DyadicTube n)} {T0 : DyadicTube n}
    (hA : A ⊆ Metric.closedBall T0 (52 * dyadicDelta n)) :
    A.encard ≤ 11025 := by
  set δ_n := dyadicDelta n with hδn
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  have h1 : ∀ T ∈ A, (Int.natAbs (T.a - T0.a) : ℝ) + (Int.natAbs (T.b - T0.b) : ℝ) ≤ 52 := by
    intro T hT
    have h2 : dist T T0 ≤ 52 * δ_n := hA hT
    have h3 : dist T T0 = T.dist T0 := by rfl
    rw [h3] at h2
    have h4 : T.dist T0 = δ_n * ((Int.natAbs (T.a - T0.a) : ℝ) + (Int.natAbs (T.b - T0.b) : ℝ)) := by
      have h5 := DyadicTube.dist_eq T T0
      have h_abs : ∀ (z : ℤ), (|(z : ℝ)|) = (Int.natAbs z : ℝ) := by
        intro z
        exact int_natAbs_cast_abs z
      have h6 : (|(T.a - T0.a : ℤ)| : ℝ) = (Int.natAbs (T.a - T0.a) : ℝ) := h_abs (T.a - T0.a)
      have h7 : (|(T.b - T0.b : ℤ)| : ℝ) = (Int.natAbs (T.b - T0.b) : ℝ) := h_abs (T.b - T0.b)
      rw [h5, h6, h7, ←hδn]
    rw [h4] at h2
    nlinarith
  have h2 : ∀ T ∈ A, Int.natAbs (T.a - T0.a) ≤ 52 := by
    intro T hT
    have h3 : (Int.natAbs (T.a - T0.a) : ℝ) + (Int.natAbs (T.b - T0.b) : ℝ) ≤ 52 := h1 T hT
    have h4 : 0 ≤ (Int.natAbs (T.b - T0.b) : ℝ) := by positivity
    have h5 : (Int.natAbs (T.a - T0.a) : ℝ) ≤ 52 := by linarith
    by_contra h6
    have h7 : 53 ≤ Int.natAbs (T.a - T0.a) := by omega
    have h8 : (53 : ℝ) ≤ (Int.natAbs (T.a - T0.a) : ℝ) := by exact_mod_cast h7
    linarith
  have h3 : ∀ T ∈ A, Int.natAbs (T.b - T0.b) ≤ 52 := by
    intro T hT
    have h4 : (Int.natAbs (T.a - T0.a) : ℝ) + (Int.natAbs (T.b - T0.b) : ℝ) ≤ 52 := h1 T hT
    have h5 : 0 ≤ (Int.natAbs (T.a - T0.a) : ℝ) := by positivity
    have h6 : (Int.natAbs (T.b - T0.b) : ℝ) ≤ 52 := by linarith
    by_contra h7
    have h8 : 53 ≤ Int.natAbs (T.b - T0.b) := by omega
    have h9 : (53 : ℝ) ≤ (Int.natAbs (T.b - T0.b) : ℝ) := by exact_mod_cast h8
    linarith
  let f : DyadicTube n → ℤ × ℤ := fun T => (T.a, T.b)
  have h_inj : Set.InjOn f A := by
    intro T1 hT1 T2 hT2 h
    have ha : T1.a = T2.a := by simp [f] at h <;> exact h.1
    have hb : T1.b = T2.b := by simp [f] at h <;> exact h.2
    have h_slope : T1.slope = T2.slope := by simp [DyadicTube.slope, ha] <;> ring
    have h_intercept : T1.intercept = T2.intercept := by simp [DyadicTube.intercept, hb] <;> ring
    have h_dist : T1.dist T2 = 0 := by
      have h := DyadicTube.dist_eq T1 T2
      rw [h]
      have h1 : (|(T1.a - T2.a : ℤ)| : ℝ) = 0 := by
        have h2 : T1.a = T2.a := ha
        rw [h2] <;> norm_num
      have h2 : (|(T1.b - T2.b : ℤ)| : ℝ) = 0 := by
        have h3 : T1.b = T2.b := hb
        rw [h3] <;> norm_num
      rw [h1, h2] <;> ring
    exact DyadicTube.eq_of_dist_eq_zero T1 T2 h_dist
  let I : Finset ℤ := Finset.Icc (T0.a - 52) (T0.a + 52)
  let J : Finset ℤ := Finset.Icc (T0.b - 52) (T0.b + 52)
  have h4 : f '' A ⊆ (I ×ˢ J : Set (ℤ × ℤ)) := by
    intro z hz
    rcases hz with ⟨T, hT, rfl⟩
    have h5 : Int.natAbs (T.a - T0.a) ≤ 52 := h2 T hT
    have h6 : Int.natAbs (T.b - T0.b) ≤ 52 := h3 T hT
    have h7 : T0.a - 52 ≤ T.a := by omega
    have h9 : T.a ≤ T0.a + 52 := by omega
    have h11 : T0.b - 52 ≤ T.b := by omega
    have h13 : T.b ≤ T0.b + 52 := by omega
    have h15 : T.a ∈ I := by
      simp only [I, Finset.mem_Icc]; exact ⟨h7, h9⟩
    have h16 : T.b ∈ J := by
      simp only [J, Finset.mem_Icc]; exact ⟨h11, h13⟩
    exact ⟨h15, h16⟩
  have h_fin : (f '' A).Finite := by
    apply Set.Finite.subset (Finset.finite_toSet (I ×ˢ J))
    simpa [Finset.coe_product] using h4
  have h5 : (f '' A).encard ≤ (I ×ˢ J : Set (ℤ × ℤ)).encard := Set.encard_mono h4
  have h6 : (I ×ˢ J : Set (ℤ × ℤ)).encard = ↑(I ×ˢ J).card := by simp
  have h7 : (I ×ˢ J).card = I.card * J.card := Finset.card_product _ _
  have h8 : I.card = 105 := by
    rw [Int.card_Icc]
    have h_eq : (T0.a + 52) + 1 - (T0.a - 52) = (105 : ℤ) := by ring
    rw [h_eq] <;> simp
  have h9 : J.card = 105 := by
    rw [Int.card_Icc]
    have h_eq : (T0.b + 52) + 1 - (T0.b - 52) = (105 : ℤ) := by ring
    rw [h_eq] <;> simp
  have h10 : (I ×ˢ J).card = 11025 := by
    rw [h7, h8, h9] <;> norm_num
  rw [h6, h10] at h5
  have h11 : (f '' A).encard = A.encard := h_inj.encard_image
  rw [h11] at h5
  exact h5

/-! ============================================================================
   Preimage distance bound
   ============================================================================ -/

/-- Preimage bound: if dist_DT(snap(ℓ1), snap(ℓ2)) ≤ r, then dist_AL(ℓ1, ℓ2) ≤ 15δ + 5r. -/
lemma snap_preimage_bound {n : ℕ} {δ r : ℝ} (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hδn_leδ : dyadicDelta n ≤ δ)
    (p : EuclideanSpace ℝ (Fin 2)) (hp_ball : p ∈ Metric.closedBall 0 1)
    {ℓ1 ℓ2 : AffineLine}
    (hv01 : (LemmaE.getDirV ℓ1) 0 ≠ 0) (hv02 : (LemmaE.getDirV ℓ2) 0 ≠ 0)
    (hm1 : |(affineLineSlopeIntercept ℓ1).1| ≤ 1)
    (hm2 : |(affineLineSlopeIntercept ℓ2).1| ≤ 1)
    (h_near1 : p ∈ Metric.cthickening δ ℓ1.1)
    (h_near2 : p ∈ Metric.cthickening δ ℓ2.1)
    (hr_nonneg : 0 ≤ r)
    (h_dist : dist (snapToTubeThroughPoint n ℓ1 p) (snapToTubeThroughPoint n ℓ2 p) ≤ r) :
    AffineLine.dist ℓ1 ℓ2 ≤ 15 * δ + 5 * r := by
  set T1 := snapToTubeThroughPoint n ℓ1 p with hT1
  set T2 := snapToTubeThroughPoint n ℓ2 p with hT2
  set δ_n := dyadicDelta n with hδn_def
  set ℓ1' := toAffineLine T1 with hℓ1'
  set ℓ2' := toAffineLine T2 with hℓ2'
  have h_move1 : AffineLine.dist ℓ1 ℓ1' ≤ (15 / 2 : ℝ) * δ :=
    snap_movement_bound hδ_pos hδ_le_one hδn_leδ ℓ1 p hv01 hm1 hp_ball h_near1
  have h_move2 : AffineLine.dist ℓ2 ℓ2' ≤ (15 / 2 : ℝ) * δ :=
    snap_movement_bound hδ_pos hδ_le_one hδn_leδ ℓ2 p hv02 hm2 hp_ball h_near2
  have hb2 : |T2.intercept| ≤ 3 :=
    snap_intercept_bound hδn_leδ ℓ2 p hv02 hm2 hp_ball
  have h_lip : AffineLine.dist ℓ1' ℓ2' ≤ 5 * DyadicToAffineAdapters.paramDistLinf T1 T2 :=
    toAffineLine_lipschitz_gen T1 T2 hb2
  have h_inf_le : DyadicToAffineAdapters.paramDistLinf T1 T2 ≤ dist T1 T2 := by
    have hδn_pos : 0 < δ_n := dyadicDelta_pos n
    have h_a : |T1.slope - T2.slope| = δ_n * (Int.natAbs (T1.a - T2.a) : ℝ) := by
      have h_slope1 : T1.slope = (T1.a : ℝ) * dyadicDelta n := by simp [DyadicTube.slope]
      have h_slope2 : T2.slope = (T2.a : ℝ) * dyadicDelta n := by simp [DyadicTube.slope]
      rw [h_slope1, h_slope2]
      have h2 : (T1.a : ℝ) * dyadicDelta n - (T2.a : ℝ) * dyadicDelta n =
          ((T1.a : ℝ) - (T2.a : ℝ)) * dyadicDelta n := by ring
      rw [h2, abs_mul]
      have h3 : |dyadicDelta n| = dyadicDelta n := abs_of_pos (dyadicDelta_pos n)
      rw [h3]
      have h4 : dyadicDelta n = δ_n := hδn_def.symm
      have h_cast : (T1.a : ℝ) - (T2.a : ℝ) = ↑(T1.a - T2.a) := by norm_cast
      rw [h4, h_cast, int_natAbs_cast_abs (T1.a - T2.a)] <;> ring
    have h_b : |T1.intercept - T2.intercept| = δ_n * (Int.natAbs (T1.b - T2.b) : ℝ) := by
      have h_int1 : T1.intercept = (T1.b : ℝ) * dyadicDelta n := by simp [DyadicTube.intercept]
      have h_int2 : T2.intercept = (T2.b : ℝ) * dyadicDelta n := by simp [DyadicTube.intercept]
      rw [h_int1, h_int2]
      have h2 : (T1.b : ℝ) * dyadicDelta n - (T2.b : ℝ) * dyadicDelta n =
          ((T1.b : ℝ) - (T2.b : ℝ)) * dyadicDelta n := by ring
      rw [h2, abs_mul]
      have h3 : |dyadicDelta n| = dyadicDelta n := abs_of_pos (dyadicDelta_pos n)
      rw [h3]
      have h4 : dyadicDelta n = δ_n := hδn_def.symm
      have h_cast : (T1.b : ℝ) - (T2.b : ℝ) = ↑(T1.b - T2.b) := by norm_cast
      rw [h4, h_cast, int_natAbs_cast_abs (T1.b - T2.b)] <;> ring
    have h_dist : dist T1 T2 = δ_n * ((Int.natAbs (T1.a - T2.a) : ℝ) + (Int.natAbs (T1.b - T2.b) : ℝ)) := by
      have h1 : dist T1 T2 = T1.dist T2 := by rfl
      have h2 : T1.dist T2 = dyadicDelta n * ((Int.natAbs (T1.a - T2.a) : ℝ) + (Int.natAbs (T1.b - T2.b) : ℝ)) := by
        have h_dist_eq := DyadicTube.dist_eq T1 T2
        have h_abs : ∀ (z : ℤ), (|(z : ℝ)|) = (Int.natAbs z : ℝ) := by
          intro z
          exact int_natAbs_cast_abs z
        have h6 : (|(T1.a - T2.a : ℤ)| : ℝ) = (Int.natAbs (T1.a - T2.a) : ℝ) := h_abs (T1.a - T2.a)
        have h7 : (|(T1.b - T2.b : ℤ)| : ℝ) = (Int.natAbs (T1.b - T2.b) : ℝ) := h_abs (T1.b - T2.b)
        rw [h_dist_eq, h6, h7]
      have h3 : dyadicDelta n = δ_n := hδn_def.symm
      calc dist T1 T2
        = T1.dist T2 := h1
      _ = dyadicDelta n * ((Int.natAbs (T1.a - T2.a) : ℝ) + (Int.natAbs (T1.b - T2.b) : ℝ)) := h2
      _ = δ_n * ((Int.natAbs (T1.a - T2.a) : ℝ) + (Int.natAbs (T1.b - T2.b) : ℝ)) := by
        apply congr_arg (fun x : ℝ => x * _) h3
    rw [h_dist]
    dsimp only [DyadicToAffineAdapters.paramDistLinf]
    rw [h_a, h_b]
    have h_nonneg1 : 0 ≤ δ_n * (Int.natAbs (T1.a - T2.a) : ℝ) := by positivity
    have h_nonneg2 : 0 ≤ δ_n * (Int.natAbs (T1.b - T2.b) : ℝ) := by positivity
    exact max_le (by linarith [h_nonneg2]) (by linarith [h_nonneg1])
  have h_tri1 : AffineLine.dist ℓ1 ℓ2 ≤ AffineLine.dist ℓ1 ℓ1' + AffineLine.dist ℓ1' ℓ2 := dist_triangle ℓ1 ℓ1' ℓ2
  have h_tri2 : AffineLine.dist ℓ1' ℓ2 ≤ AffineLine.dist ℓ1' ℓ2' + AffineLine.dist ℓ2' ℓ2 := dist_triangle ℓ1' ℓ2' ℓ2
  calc AffineLine.dist ℓ1 ℓ2
    ≤ AffineLine.dist ℓ1 ℓ1' + AffineLine.dist ℓ1' ℓ2 := h_tri1
  _ ≤ AffineLine.dist ℓ1 ℓ1' + (AffineLine.dist ℓ1' ℓ2' + AffineLine.dist ℓ2' ℓ2) := add_le_add_right h_tri2 _
  _ = AffineLine.dist ℓ1 ℓ1' + AffineLine.dist ℓ1' ℓ2' + AffineLine.dist ℓ2' ℓ2 := by ring
  _ ≤ (15 / 2 : ℝ) * δ + (5 * DyadicToAffineAdapters.paramDistLinf T1 T2) + (15 / 2 : ℝ) * δ := by
    have h3 : AffineLine.dist ℓ2' ℓ2 ≤ (15 / 2 : ℝ) * δ := by
      have h4 : AffineLine.dist ℓ2' ℓ2 = AffineLine.dist ℓ2 ℓ2' := by
        simp [AffineLine.dist, norm_sub_rev] <;> abel
      rw [h4]
      exact h_move2
    gcongr
  _ ≤ (15 / 2 : ℝ) * δ + 5 * dist T1 T2 + (15 / 2 : ℝ) * δ := by linarith [h_inf_le]
  _ ≤ (15 / 2 : ℝ) * δ + 5 * r + (15 / 2 : ℝ) * δ := by gcongr <;> linarith
  _ = 15 * δ + 5 * r := by ring

/-! ============================================================================
   Covering bounds
   ============================================================================ -/

/-- Forward covering: Ncover_{δ_n}(f '' B) ≤ 11025 * Ncover_δ(B). -/
lemma snap_forward_cover {n : ℕ} {δ : ℝ}
    (hδ_pos : 0 < δ) (hδn_leδ : dyadicDelta n ≤ δ) (hδ_le4δn : δ ≤ 4 * dyadicDelta n)
    (p : EuclideanSpace ℝ (Fin 2)) (hp_ball : p ∈ Metric.closedBall 0 1)
    {S : Set AffineLine}
    (h_v0 : ∀ ℓ ∈ S, (LemmaE.getDirV ℓ) 0 ≠ 0)
    (h_slope : ∀ ℓ ∈ S, |(affineLineSlopeIntercept ℓ).1| ≤ 1)
    (h_near : ∀ ℓ ∈ S, p ∈ Metric.cthickening δ ℓ.1)
    {B : Set AffineLine} (hB : B ⊆ S) :
    Metric.externalCoveringNumber (dyadicDelta n).toNNReal
      ((fun ℓ => snapToTubeThroughPoint n ℓ p) '' B) ≤
    (11025 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal B := by
  let f : AffineLine → DyadicTube n := fun ℓ => snapToTubeThroughPoint n ℓ p
  let δ_n := dyadicDelta n
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n

  have h_main : ∀ (C : Set AffineLine), Metric.IsCover δ.toNNReal B C →
      (Metric.externalCoveringNumber δ_n.toNNReal (f '' B) : ENNReal) ≤
      (11025 : ENNReal) * (C.encard : ENNReal) := by
    intro C hC
    by_cases h_fin : C.Finite
    · let Cf := h_fin.toFinset
      have hCf : (Cf : Set AffineLine) = C := h_fin.coe_toFinset
      let C' : Set (DyadicTube n) := ⋃ c ∈ Cf, f '' (B ∩ Metric.closedBall c δ)
      have h_cover : Metric.IsCover δ_n.toNNReal (f '' B) C' := by
        intro y hy
        rcases hy with ⟨ℓ, hℓ, rfl⟩
        rcases hC hℓ with ⟨c, hc_in, hdist⟩
        have hdist' : dist ℓ c ≤ δ := by
          have h : edist ℓ c ≤ ↑δ.toNNReal := hdist
          rw [edist_dist] at h
          have h2 : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by
            simp [ENNReal.ofReal, hδ_pos.le] <;> rfl
          rw [h2] at h
          exact (ENNReal.ofReal_le_ofReal_iff hδ_pos.le).mp h
        have hℓ_in : ℓ ∈ B ∩ Metric.closedBall c δ := ⟨hℓ, Metric.mem_closedBall.mpr hdist'⟩
        have h_y_in : f ℓ ∈ f '' (B ∩ Metric.closedBall c δ) := ⟨ℓ, hℓ_in, rfl⟩
        have hc_in_Cf : c ∈ Cf := by
          simpa [←hCf] using hc_in
        have h_y_in_C' : f ℓ ∈ C' := Set.mem_iUnion₂.mpr ⟨c, hc_in_Cf, h_y_in⟩
        exact ⟨f ℓ, h_y_in_C', by simp [edist_dist, hδn_pos.le]⟩
      have h_each : ∀ c ∈ Cf, (f '' (B ∩ Metric.closedBall c δ)).encard ≤ 11025 := by
        intro c _
        by_cases h_empty : (f '' (B ∩ Metric.closedBall c δ)).Nonempty
        · rcases h_empty with ⟨T0, hT0⟩
          have h_sub : f '' (B ∩ Metric.closedBall c δ) ⊆ Metric.closedBall T0 (52 * δ_n) := by
            intro T hT
            rcases hT with ⟨ℓ, hℓ, rfl⟩
            rcases hT0 with ⟨ℓ0, hℓ0, rfl⟩
            have h_dist1 : dist ℓ c ≤ δ := Metric.mem_closedBall.mp hℓ.2
            have h_dist2 : dist ℓ0 c ≤ δ := Metric.mem_closedBall.mp hℓ0.2
            have h_dist3 : AffineLine.dist ℓ ℓ0 ≤ 2 * δ := by
              calc AffineLine.dist ℓ ℓ0
                ≤ AffineLine.dist ℓ c + AffineLine.dist c ℓ0 := dist_triangle ℓ c ℓ0
              _ = AffineLine.dist ℓ c + AffineLine.dist ℓ0 c := by
                apply congr_arg (fun x => AffineLine.dist ℓ c + x)
                exact dist_comm c ℓ0
              _ ≤ δ + δ := by
                have h1 : AffineLine.dist ℓ c ≤ δ := h_dist1
                have h2 : AffineLine.dist ℓ0 c ≤ δ := h_dist2
                exact add_le_add h1 h2
              _ = 2 * δ := by ring
            have h4_raw : dist (f ℓ) (f ℓ0) ≤ 6 * dyadicDelta n + 8 * δ :=
              snap_image_diameter hδ_pos hδn_leδ p hp_ball
                (h_v0 ℓ (hB hℓ.1)) (h_v0 ℓ0 (hB hℓ0.1))
                (h_slope ℓ (hB hℓ.1)) (h_slope ℓ0 (hB hℓ0.1))
                (h_near ℓ (hB hℓ.1)) (h_near ℓ0 (hB hℓ0.1))
                h_dist3
            have h5 : dist (f ℓ) (f ℓ0) ≤ 52 * δ_n := by
              have h6 : 6 * dyadicDelta n + 8 * δ ≤ 52 * δ_n := by
                have h7 : δ ≤ 4 * δ_n := hδ_le4δn
                linarith
              linarith [h4_raw, h6]
            exact Metric.mem_closedBall.mpr h5
          exact dyadicTube_ball52_card h_sub
        · have h_empty' : f '' (B ∩ Metric.closedBall c δ) = ∅ := by
            simpa [Set.not_nonempty_iff_eq_empty] using h_empty
          rw [h_empty'] <;> simp
      have h_card1 : C'.encard ≤ ∑ c ∈ Cf, (f '' (B ∩ Metric.closedBall c δ)).encard :=
        Finset.set_encard_biUnion_le Cf _
      have h_card2 : ∑ c ∈ Cf, (f '' (B ∩ Metric.closedBall c δ)).encard ≤ ∑ c ∈ Cf, (11025 : ENat) := by
        apply Finset.sum_le_sum; intro c hc; exact h_each c hc
      have h_card3 : ∑ c ∈ Cf, (11025 : ENat) = (11025 : ENat) * ↑Cf.card := by
        rw [Finset.sum_const] <;> ring
      have h_le : (Metric.externalCoveringNumber δ_n.toNNReal (f '' B) : ENNReal) ≤ (C'.encard : ENNReal) := by
        exact_mod_cast Metric.IsCover.externalCoveringNumber_le_encard h_cover
      have h_final : (C'.encard : ENNReal) ≤ (11025 : ENNReal) * (C.encard : ENNReal) := by
        have hCenc : (C.encard : ENNReal) = ↑Cf.card := by
          rw [← hCf] <;> simp
        rw [hCenc]
        exact_mod_cast le_trans h_card1 (le_trans h_card2 (by rw [h_card3] <;> simp))
      exact le_trans h_le h_final
    · have h : C.encard = ⊤ := Set.encard_eq_top_iff.mpr h_fin
      rw [h] <;> simp

  have h1 : ∀ (C : Set AffineLine), (Metric.externalCoveringNumber δ_n.toNNReal (f '' B) : ENNReal) ≤
      (11025 : ENNReal) * (iInf (fun hC : Metric.IsCover δ.toNNReal B C => (C.encard : ENNReal))) := by
    intro C
    by_cases hC : Metric.IsCover δ.toNNReal B C
    · have h2 : (iInf (fun hC : Metric.IsCover δ.toNNReal B C => (C.encard : ENNReal))) = (C.encard : ENNReal) := by
        simp [hC]
      rw [h2]
      exact h_main C hC
    · have h3 : (iInf (fun hC : Metric.IsCover δ.toNNReal B C => (C.encard : ENNReal))) = ⊤ := by
        simp [hC]
      rw [h3] <;> simp
  have h4 : (Metric.externalCoveringNumber δ_n.toNNReal (f '' B) : ENNReal) ≤
      iInf (fun C : Set AffineLine => (11025 : ENNReal) *
        iInf (fun hC : Metric.IsCover δ.toNNReal B C => (C.encard : ENNReal))) :=
    le_iInf h1
  have h5 : iInf (fun C : Set AffineLine => (11025 : ENNReal) *
        iInf (fun hC : Metric.IsCover δ.toNNReal B C => (C.encard : ENNReal))) =
      (11025 : ENNReal) * iInf (fun C : Set AffineLine =>
        iInf (fun hC : Metric.IsCover δ.toNNReal B C => (C.encard : ENNReal))) := by
    let g : Set AffineLine → ENNReal := fun C => iInf (fun hC : Metric.IsCover δ.toNNReal B C => (C.encard : ENNReal))
    have h_mul : (iInf g) * (11025 : ENNReal) = iInf (fun C => g C * (11025 : ENNReal)) :=
      ENNReal.iInf_mul_of_ne (by simp) (by simp)
    have h_comm : (iInf g) * (11025 : ENNReal) = (11025 : ENNReal) * iInf g := by ring
    have h_comm2 : iInf (fun C : Set AffineLine => g C * (11025 : ENNReal)) = iInf (fun C : Set AffineLine => (11025 : ENNReal) * g C) := by
      congr with C
      <;> ring
    rw [h_comm, h_comm2] at h_mul
    exact h_mul.symm
  rw [h5] at h4
  simpa [Metric.externalCoveringNumber] using h4

/-- Backward covering: Ncover_{25δ}(S) ≤ Ncover_{δ_n}(A). -/
lemma snap_backward_cover {n : ℕ} {δ : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) (hδn_leδ : dyadicDelta n ≤ δ)
    (p : EuclideanSpace ℝ (Fin 2)) (hp_ball : p ∈ Metric.closedBall 0 1)
    {S : Set AffineLine} (hS_nonempty : S.Nonempty)
    (h_v0 : ∀ ℓ ∈ S, (LemmaE.getDirV ℓ) 0 ≠ 0)
    (h_slope : ∀ ℓ ∈ S, |(affineLineSlopeIntercept ℓ).1| ≤ 1)
    (h_near : ∀ ℓ ∈ S, p ∈ Metric.cthickening δ ℓ.1) :
    Metric.externalCoveringNumber (25 * δ).toNNReal S ≤
    Metric.externalCoveringNumber (dyadicDelta n).toNNReal
      ((fun ℓ => snapToTubeThroughPoint n ℓ p) '' S) := by
  let f : AffineLine → DyadicTube n := fun ℓ => snapToTubeThroughPoint n ℓ p
  let δ_n := dyadicDelta n
  let A : Set (DyadicTube n) := f '' S
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  let ℓ0 : AffineLine := Classical.choose hS_nonempty
  have hℓ0_in_S : ℓ0 ∈ S := Classical.choose_spec hS_nonempty
  let g : DyadicTube n → AffineLine := fun T =>
    if h : ∃ ℓ ∈ S, dist (f ℓ) T ≤ δ_n then
      Classical.choose h
    else ℓ0
  apply le_iInf
  intro C
  apply le_iInf
  intro hC
  let C' : Set AffineLine := g '' C
  have hC'_card : C'.encard ≤ C.encard := Set.encard_image_le g C
  have h_cover : Metric.IsCover (25 * δ).toNNReal S C' := by
    intro ℓ hℓ
    have h_fℓ_in_A : f ℓ ∈ A := ⟨ℓ, hℓ, rfl⟩
    rcases hC h_fℓ_in_A with ⟨T, hT_in_C, hdist⟩
    have hdist' : dist (f ℓ) T ≤ δ_n := by
      have h : edist (f ℓ) T ≤ ↑δ_n.toNNReal := hdist
      have h2 : (↑δ_n.toNNReal : ENNReal) = ENNReal.ofReal δ_n := by
        have h3 : 0 ≤ δ_n := hδn_pos.le
        exact ENNReal.ofNNReal_toNNReal δ_n
      rw [edist_dist, h2] at h
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
    have hP : ∃ ℓ' ∈ S, dist (f ℓ') T ≤ δ_n := ⟨ℓ, hℓ, hdist'⟩
    have hgT : g T = Classical.choose hP := by
      dsimp only [g]; rw [dif_pos hP]
    have h_gT_in_S : (g T) ∈ S := by
      rw [hgT]; exact (Classical.choose_spec hP).1
    have h_gT_dist : dist (f (g T)) T ≤ δ_n := by
      rw [hgT]; exact (Classical.choose_spec hP).2
    have h_main : AffineLine.dist ℓ (g T) ≤ 25 * δ := by
      have h_pre : AffineLine.dist ℓ (g T) ≤ 15 * δ + 5 * dist (f ℓ) (f (g T)) :=
        snap_preimage_bound hδ_pos hδ_le_one hδn_leδ p hp_ball
          (h_v0 ℓ hℓ) (h_v0 (g T) h_gT_in_S)
          (h_slope ℓ hℓ) (h_slope (g T) h_gT_in_S)
          (h_near ℓ hℓ) (h_near (g T) h_gT_in_S)
          (by positivity) (by rfl)
      have h_tri : dist (f ℓ) (f (g T)) ≤ dist (f ℓ) T + dist T (f (g T)) := dist_triangle _ _ _
      have h6 : dist T (f (g T)) = dist (f (g T)) T := dist_comm _ _
      calc AffineLine.dist ℓ (g T)
        ≤ 15 * δ + 5 * dist (f ℓ) (f (g T)) := h_pre
      _ ≤ 15 * δ + 5 * (dist (f ℓ) T + dist T (f (g T))) := by gcongr
      _ = 15 * δ + 5 * (dist (f ℓ) T + dist (f (g T)) T) := by rw [h6]
      _ ≤ 15 * δ + 5 * (δ_n + δ_n) := by gcongr <;> linarith
      _ = 15 * δ + 10 * δ_n := by ring
      _ ≤ 25 * δ := by have h7 : δ_n ≤ δ := hδn_leδ; linarith
    have h_gT_in_C' : g T ∈ C' := ⟨T, hT_in_C, rfl⟩
    have h_edist : edist ℓ (g T) ≤ ↑(25 * δ).toNNReal := by
      rw [edist_dist]
      have h_pos : 0 ≤ 25 * δ := by positivity
      have h_eq : (↑(25 * δ).toNNReal : ENNReal) = ENNReal.ofReal (25 * δ) := by
        have h3 : 0 ≤ 25 * δ := h_pos
        exact ENNReal.ofNNReal_toNNReal (25 * δ)
      rw [h_eq]
      exact ENNReal.ofReal_le_ofReal h_main
    exact ⟨g T, h_gT_in_C', h_edist⟩
  have h10 : Metric.externalCoveringNumber (25 * δ).toNNReal S ≤ C'.encard :=
    Metric.IsCover.externalCoveringNumber_le_encard h_cover
  have h11 : C'.encard ≤ C.encard := hC'_card
  exact le_trans h10 h11

/-! ============================================================================
   Main S-set transfer
   ============================================================================ -/

/-- Main S-set transfer from AffineLine to DyadicTube via snapToTubeThroughPoint.

    Given a (δ, s, C)-set S of AffineLines near p, with |slope| ≤ 1,
    the snapped dyadic tubes form a (δ_n, s, C')-set with δ-independent C'.
    Constant: C' = 11025 * K_pack^5 * C * 70^s. -/
lemma snap_sset_transfer
    {n : ℕ} {δ δ_n s C : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hδn_pos : 0 < δ_n) (hδn_eq : δ_n = dyadicDelta n)
    (hδn_leδ : δ_n ≤ δ) (hδ_le4δn : δ ≤ 4 * δ_n)
    (hs_nonneg : 0 ≤ s) (hC_pos : 0 < C)
    {S : Set AffineLine} (hS : IsDeltaSSet δ s C S)
    (p : EuclideanSpace ℝ (Fin 2)) (hp_ball : p ∈ Metric.closedBall 0 1)
    (h_v0 : ∀ ℓ ∈ S, (LemmaE.getDirV ℓ) 0 ≠ 0)
    (h_slope : ∀ ℓ ∈ S, |(affineLineSlopeIntercept ℓ).1| ≤ 1)
    (h_near : ∀ ℓ ∈ S, p ∈ Metric.cthickening δ ℓ.1) :
    IsDeltaSSet δ_n s (11025 * (affineLine_packing_constant : ℝ)^5 * (70 : ℝ)^s * C)
      ((fun ℓ => snapToTubeThroughPoint n ℓ p) '' S) := by
  let f : AffineLine → DyadicTube n := fun ℓ => snapToTubeThroughPoint n ℓ p
  let A : Set (DyadicTube n) := f '' S
  have hS_nonempty : S.Nonempty := hS.1
  have hA_nonempty : A.Nonempty := hS_nonempty.image f
  have hδn_leδ' : dyadicDelta n ≤ δ := by rw [←hδn_eq] <;> exact hδn_leδ
  have hδ_le4δn' : δ ≤ 4 * dyadicDelta n := by rw [←hδn_eq] <;> exact hδ_le4δn

  have h_backward22 : Metric.externalCoveringNumber (25 * δ).toNNReal S ≤
      Metric.externalCoveringNumber δ_n.toNNReal A := by
    simpa [hδn_eq] using snap_backward_cover hδ_pos hδ_le_one hδn_leδ' p hp_ball
      hS_nonempty h_v0 h_slope h_near

  have h_doubling : Metric.externalCoveringNumber δ.toNNReal S ≤
      (affineLine_packing_constant : ENNReal)^5 *
      Metric.externalCoveringNumber (25 * δ).toNNReal S := by
    have h1 := affineLine_doubling_iter δ hδ_pos 5 (S := S)
    have h22_le32 : (25 * δ).toNNReal ≤ (((2^5 : ℕ) : ℝ) * δ).toNNReal := by
      have h : 25 * δ ≤ ((2^5 : ℕ) : ℝ) * δ := by
        have h5 : ((2^5 : ℕ) : ℝ) = 32 := by norm_num
        nlinarith
      have h' : (25 * δ).toNNReal ≤ (((2^5 : ℕ) : ℝ) * δ).toNNReal := by exact Real.toNNReal_mono h
      exact h'
    have h2 : Metric.externalCoveringNumber (((2^5 : ℕ) : ℝ) * δ).toNNReal S ≤
        Metric.externalCoveringNumber (25 * δ).toNNReal S :=
      Metric.externalCoveringNumber_anti (h := h22_le32)
    calc Metric.externalCoveringNumber δ.toNNReal S
      ≤ (affineLine_packing_constant : ENNReal)^5 *
          Metric.externalCoveringNumber (((2^5 : ℕ) : ℝ) * δ).toNNReal S := h1
    _ ≤ (affineLine_packing_constant : ENNReal)^5 *
          Metric.externalCoveringNumber (25 * δ).toNNReal S := by
      have h2' : (Metric.externalCoveringNumber (((2^5 : ℕ) : ℝ) * δ).toNNReal S : ENNReal) ≤
          (Metric.externalCoveringNumber (25 * δ).toNNReal S : ENNReal) := by exact_mod_cast h2
      exact mul_le_mul' (le_refl _) h2'

  have h_backward : Metric.externalCoveringNumber δ.toNNReal S ≤
      (affineLine_packing_constant : ENNReal)^5 *
      Metric.externalCoveringNumber δ_n.toNNReal A := by
    calc Metric.externalCoveringNumber δ.toNNReal S
      ≤ (affineLine_packing_constant : ENNReal)^5 *
          Metric.externalCoveringNumber (25 * δ).toNNReal S := h_doubling
    _ ≤ (affineLine_packing_constant : ENNReal)^5 *
          Metric.externalCoveringNumber δ_n.toNNReal A := by gcongr

  let K : ENNReal := (11025 : ENNReal) * (affineLine_packing_constant : ENNReal)^5 * (70 : ENNReal)^s
  let C'_real : ℝ := 11025 * (affineLine_packing_constant : ℝ)^5 * (70 : ℝ)^s * C
  have h_pack_pos : 0 < (affineLine_packing_constant : ℝ) := by
    exact_mod_cast affineLine_packing_constant_pos'
  have hC'_pos : 0 < C'_real := by
    dsimp only [C'_real]
    positivity
  refine' ⟨hA_nonempty, by simpa [hδn_eq] using hδn_pos, hC'_pos, hs_nonneg, _⟩
  intro T0 r hr
  have hr_pos : 0 ≤ r := by linarith [hδn_pos, hr]
  by_cases h_empty : (A ∩ Metric.closedBall T0 r).Nonempty
  · rcases h_empty with ⟨T1, hT1_in⟩
    have hT1_in_A : T1 ∈ A := hT1_in.1
    have h_dist_T1_T0 : dist T1 T0 ≤ r := Metric.mem_closedBall.mp hT1_in.2
    rcases hT1_in_A with ⟨ℓ0, hℓ0_in_S, hT1_eq⟩
    let R : ℝ := 15 * δ + 5 * (2 * r)
    have hR_geδ : δ ≤ R := by linarith
    have h_ball2 : A ∩ Metric.closedBall T0 r ⊆ A ∩ Metric.closedBall T1 (2 * r) := by
      intro T hT
      have h1 : T ∈ A := hT.1
      have h2 : dist T T0 ≤ r := Metric.mem_closedBall.mp hT.2
      have h4 : dist T T1 ≤ 2 * r := by
        calc dist T T1
          ≤ dist T T0 + dist T0 T1 := dist_triangle _ _ _
        _ = dist T T0 + dist T1 T0 := by rw [dist_comm T0 T1]
        _ ≤ r + r := by gcongr
        _ = 2 * r := by ring
      exact ⟨h1, Metric.mem_closedBall.mpr h4⟩
    have h_preimage : A ∩ Metric.closedBall T1 (2 * r) ⊆ f '' (S ∩ Metric.closedBall ℓ0 R) := by
      intro T hT
      rcases hT.1 with ⟨ℓ, hℓ_in_S, rfl⟩
      have h_dist : dist (f ℓ) T1 ≤ 2 * r := Metric.mem_closedBall.mp hT.2
      have h_dist' : dist (f ℓ) (f ℓ0) ≤ 2 * r := by
        simpa [hT1_eq] using h_dist
      have h_pre : AffineLine.dist ℓ ℓ0 ≤ R :=
        snap_preimage_bound hδ_pos hδ_le_one hδn_leδ' p hp_ball
          (h_v0 ℓ hℓ_in_S) (h_v0 ℓ0 hℓ0_in_S)
          (h_slope ℓ hℓ_in_S) (h_slope ℓ0 hℓ0_in_S)
          (h_near ℓ hℓ_in_S) (h_near ℓ0 hℓ0_in_S)
          (by positivity) h_dist'
      exact ⟨ℓ, ⟨hℓ_in_S, Metric.mem_closedBall.mpr h_pre⟩, rfl⟩
    have h_forward : (Metric.externalCoveringNumber δ_n.toNNReal (f '' (S ∩ Metric.closedBall ℓ0 R)) : ENNReal) ≤
        (11025 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall ℓ0 R) : ENNReal) := by
      have h := snap_forward_cover hδ_pos hδn_leδ' hδ_le4δn' p hp_ball
        h_v0 h_slope h_near (B := S ∩ Metric.closedBall ℓ0 R) (by exact Set.inter_subset_left)
      simpa [hδn_eq] using h
    have h_sset : (Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall ℓ0 R) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal R) ^ s * (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) :=
      hS.2.2.2.2 ℓ0 R hR_geδ
    have hR_le70r : R ≤ 70 * r := by
      dsimp only [R]
      have h4 : δ ≤ 4 * r := by
        have h5 : δ_n ≤ r := hr
        linarith [hδ_le4δn]
      linarith
    have h7 : (ENNReal.ofReal R) ^ s ≤ (ENNReal.ofReal (70 * r)) ^ s := by gcongr <;> linarith
    have h8 : (ENNReal.ofReal (70 * r)) ^ s = (70 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s := by
      have h_pos70 : 0 ≤ (70 : ℝ) := by norm_num
      have h10 : ENNReal.ofReal ((70 : ℝ) * r) = (70 : ENNReal) * ENNReal.ofReal r := by
        rw [ENNReal.ofReal_mul h_pos70]
        <;> simp
      rw [h10]
      have h11 : ((70 : ENNReal) * ENNReal.ofReal r) ^ s = (70 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s := by
        exact ENNReal.mul_rpow_of_nonneg (70 : ENNReal) (ENNReal.ofReal r) hs_nonneg
      exact h11
    have h_mono1 : Metric.externalCoveringNumber δ_n.toNNReal (A ∩ Metric.closedBall T0 r) ≤
        Metric.externalCoveringNumber δ_n.toNNReal (A ∩ Metric.closedBall T1 (2 * r)) :=
      Metric.externalCoveringNumber_mono_set h_ball2
    have h_mono2 : Metric.externalCoveringNumber δ_n.toNNReal (A ∩ Metric.closedBall T1 (2 * r)) ≤
        Metric.externalCoveringNumber δ_n.toNNReal (f '' (S ∩ Metric.closedBall ℓ0 R)) :=
      Metric.externalCoveringNumber_mono_set h_preimage
    calc (Metric.externalCoveringNumber δ_n.toNNReal (A ∩ Metric.closedBall T0 r) : ENNReal)
      ≤ (Metric.externalCoveringNumber δ_n.toNNReal (A ∩ Metric.closedBall T1 (2 * r)) : ENNReal) := by exact_mod_cast h_mono1
    _ ≤ (Metric.externalCoveringNumber δ_n.toNNReal (f '' (S ∩ Metric.closedBall ℓ0 R)) : ENNReal) := by exact_mod_cast h_mono2
    _ ≤ (11025 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall ℓ0 R) : ENNReal) := h_forward
    _ ≤ (11025 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal R) ^ s * (Metric.externalCoveringNumber δ.toNNReal S : ENNReal)) := by gcongr
    _ ≤ K * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ_n.toNNReal A : ENNReal) := by
      have h9 : (11025 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal R) ^ s * (Metric.externalCoveringNumber δ.toNNReal S : ENNReal)) ≤
          (11025 : ENNReal) * (ENNReal.ofReal C * ((70 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s) * (Metric.externalCoveringNumber δ.toNNReal S : ENNReal)) := by
        have h7' : (ENNReal.ofReal R) ^ s ≤ (70 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s := by
          calc (ENNReal.ofReal R) ^ s
            ≤ (ENNReal.ofReal (70 * r)) ^ s := h7
          _ = (70 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s := h8
        gcongr
        <;> exact h7'
      have h10 : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤
          (affineLine_packing_constant : ENNReal)^5 * (Metric.externalCoveringNumber δ_n.toNNReal A : ENNReal) := h_backward
      simp only [K]
      calc (11025 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal R) ^ s * (Metric.externalCoveringNumber δ.toNNReal S : ENNReal))
        ≤ (11025 : ENNReal) * (ENNReal.ofReal C * ((70 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s) * (Metric.externalCoveringNumber δ.toNNReal S : ENNReal)) := h9
      _ ≤ (11025 : ENNReal) * (ENNReal.ofReal C * ((70 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s) * ((affineLine_packing_constant : ENNReal)^5 * (Metric.externalCoveringNumber δ_n.toNNReal A : ENNReal))) := by gcongr
      _ = (11025 : ENNReal) * (affineLine_packing_constant : ENNReal)^5 * (70 : ENNReal)^s * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ_n.toNNReal A := by
        simp only [mul_assoc] <;> ac_rfl
    _ = ENNReal.ofReal C'_real * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ_n.toNNReal A : ENNReal) := by
      simp only [C'_real]
      have h_pos2 : 0 ≤ (affineLine_packing_constant : ℝ) := by positivity
      have h_pos3 : 0 ≤ (70 : ℝ)^s := by positivity
      have h_pos4 : 0 ≤ (affineLine_packing_constant : ℝ)^5 := by positivity
      have h11 : ENNReal.ofReal (11025 * (affineLine_packing_constant : ℝ)^5 * (70 : ℝ)^s * C) =
          (11025 : ENNReal) * ENNReal.ofReal ((affineLine_packing_constant : ℝ)^5) * ENNReal.ofReal ((70 : ℝ)^s) * ENNReal.ofReal C := by
        have h12 : ENNReal.ofReal (11025 * (affineLine_packing_constant : ℝ)^5 * (70 : ℝ)^s * C) =
            ENNReal.ofReal (11025 * ((affineLine_packing_constant : ℝ)^5 * ((70 : ℝ)^s * C))) := by ring_nf
        rw [h12]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 11025)]
        rw [ENNReal.ofReal_mul h_pos4]
        rw [ENNReal.ofReal_mul h_pos3]
        <;> simp [mul_assoc] <;> ac_rfl
      have h13 : ENNReal.ofReal ((affineLine_packing_constant : ℝ)^5) = (affineLine_packing_constant : ENNReal)^5 := by
        simp [ENNReal.ofReal_pow] <;> rfl
      have h14 : ENNReal.ofReal ((70 : ℝ)^s) = (70 : ENNReal)^s := by
        have h15 : (ENNReal.ofReal (70 : ℝ)) ^ s = ENNReal.ofReal ((70 : ℝ)^s) :=
          ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 70)
        have h16 : (70 : ENNReal) = ENNReal.ofReal (70 : ℝ) := by simp
        rw [h16]
        exact h15.symm
      rw [h11, h13, h14] <;> simp [mul_assoc] <;> ac_rfl
  · have h_empty' : A ∩ Metric.closedBall T0 r = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h_empty
    rw [h_empty']
    simp

/-- Existential version of `snap_sset_transfer`. -/
lemma snap_sset_transfer_exists
    {n : ℕ} {δ δ_n s C : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hδn_pos : 0 < δ_n) (hδn_eq : δ_n = dyadicDelta n)
    (hδn_leδ : δ_n ≤ δ) (hδ_le4δn : δ ≤ 4 * δ_n)
    (hs_nonneg : 0 ≤ s) (hC_pos : 0 < C)
    {S : Set AffineLine} (hS : IsDeltaSSet δ s C S)
    (p : EuclideanSpace ℝ (Fin 2)) (hp_ball : p ∈ Metric.closedBall 0 1)
    (h_v0 : ∀ ℓ ∈ S, (LemmaE.getDirV ℓ) 0 ≠ 0)
    (h_slope : ∀ ℓ ∈ S, |(affineLineSlopeIntercept ℓ).1| ≤ 1)
    (h_near : ∀ ℓ ∈ S, p ∈ Metric.cthickening δ ℓ.1) :
    ∃ (C' : ℝ), 0 < C' ∧
      IsDeltaSSet δ_n s C' ((fun ℓ => snapToTubeThroughPoint n ℓ p) '' S) := by
  let C'_real : ℝ := 11025 * (affineLine_packing_constant : ℝ)^5 * (70 : ℝ)^s * C
  have hC'_pos : 0 < C'_real := by
    dsimp only [C'_real]
    have h_pack_pos : 0 < (affineLine_packing_constant : ℝ) := by
      exact_mod_cast affineLine_packing_constant_pos'
    positivity
  exact ⟨C'_real, hC'_pos, snap_sset_transfer hδ_pos hδ_le_one hδn_pos hδn_eq hδn_leδ hδ_le4δn hs_nonneg hC_pos hS p hp_ball h_v0 h_slope h_near⟩

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

end
