module

/-
  Dyadic Discretization Bridge for Improved Incidence General.

  Wraps a floor-snapping construction with the 4 additional hypotheses
  required by `inductionOnScalesBridge_concrete`:
  1. h_squares_unit: square indices in [0, 2^n)
  2. h_tubes_strip: tube a-index in [-2^n, 2^n)
  3. h_tubes_bounded: T₀.card ≤ 12·16^n
  4. incidence_transfer: stand-coordinate incidence

  KEY INSIGHT: Floor snapping (b = ⌊(p 1 - aδ p 0)/δ⌋) ensures
  0 ≤ p 1 - aδ p 0 - bδ < δ, so the snapping point lies in BOTH
  the main strip S(a,b) AND the stand cell C(a,b).

  Whiteprint node: improved_incidence_general / dyadic_bridge
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ConstructNiceConfiguration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge_Wrapper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineParams
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal


noncomputable section

attribute [local instance] Classical.propDecidable

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.Bridge
open DirecretisedFurstenbergEstimate (AffineLine)

/-! ============================================================================
   Floor-based tube snapping
   ============================================================================ -/

/-- Snap an AffineLine to a DyadicTube using FLOOR for both indices.

    This ensures 0 ≤ p 1 - aδ p 0 - bδ < δ, so p lies in both the
    main strip S(a,b) and the stand cell C(a,b). -/
noncomputable def snapToTubeFloor (n : ℕ) (ℓ : AffineLine) (p : Plane) :
    DyadicTube n :=
  let m := (affineLineSlopeIntercept ℓ).1
  let δ := dyadicDelta n
  let a : ℤ := ⌊m / δ⌋
  let b : ℤ := ⌊(p 1 - (a : ℝ) * δ * p 0) / δ⌋
  ⟨a, b⟩

/-- The snap point lies in the main dyadic tube strip. -/
lemma snapToTubeFloor_main_incidence {n : ℕ} {ℓ : AffineLine} {p : Plane} :
    p ∈ (snapToTubeFloor n ℓ p).toSet := by
  let δ : ℝ := dyadicDelta n
  let m : ℝ := (affineLineSlopeIntercept ℓ).1
  let a : ℤ := ⌊m / δ⌋
  let b : ℤ := ⌊(p 1 - (a : ℝ) * δ * p 0) / δ⌋
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  set x : ℝ := p 1 - (a : ℝ) * δ * p 0 with hx_def
  have h1 : (b : ℝ) ≤ x / δ := Int.floor_le (x / δ)
  have h2 : x / δ < (b : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
  have h3 : (b : ℝ) * δ ≤ x := by
    have h4 : (b : ℝ) * δ ≤ (x / δ) * δ := mul_le_mul_of_nonneg_right h1 hδ_pos.le
    have h5 : (x / δ) * δ = x := by field_simp [hδ_pos.ne'] <;> ring
    rw [h5] at h4
    exact h4
  have h4 : x < ((b : ℝ) + 1) * δ := by
    have h5 : (x / δ) * δ < ((b : ℝ) + 1) * δ := mul_lt_mul_of_pos_right h2 hδ_pos
    have h6 : (x / δ) * δ = x := by field_simp [hδ_pos.ne'] <;> ring
    rw [h6] at h5
    exact h5
  have hE1 : 0 ≤ x - (b : ℝ) * δ := by linarith
  have hE2 : x - (b : ℝ) * δ < δ := by linarith
  have h_abs : |x - (b : ℝ) * δ| ≤ δ := by
    rw [abs_le] <;> constructor <;> linarith
  simpa [snapToTubeFloor, DyadicTube.toSet, DyadicTube.slope, DyadicTube.intercept, hx_def]
    using h_abs

/-- The snap point (as ℝ×ℝ) lies in the standalone dyadic tube C(a,b). -/
lemma snapToTubeFloor_stand_incidence {n : ℕ} {ℓ : AffineLine} {p : Plane} :
    let T := snapToTubeFloor n ℓ p
    let q : ℝ × ℝ := (p 0, p 1)
    q ∈ (_root_.DyadicTube.toSet (tubeToStand T)) := by
  let δ : ℝ := dyadicDelta n
  let m : ℝ := (affineLineSlopeIntercept ℓ).1
  let a : ℤ := ⌊m / δ⌋
  let b : ℤ := ⌊(p 1 - (a : ℝ) * δ * p 0) / δ⌋
  let T : DyadicTube n := ⟨a, b⟩
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_eq : δ = _root_.dyadicDelta n := by
    simp [δ, _root_.dyadicDelta, dyadicDelta, Real.rpow_neg] <;> field_simp <;> norm_cast
  set x : ℝ := p 1 - (a : ℝ) * δ * p 0 with hx_def
  let d : ℝ := x - (b : ℝ) * δ
  have hd0 : 0 ≤ d := by
    have h1 : (b : ℝ) ≤ x / δ := Int.floor_le (x / δ)
    have h4 : (b : ℝ) * δ ≤ x := by
      have h5 : (b : ℝ) * δ ≤ (x / δ) * δ := mul_le_mul_of_nonneg_right h1 hδ_pos.le
      have h6 : (x / δ) * δ = x := by field_simp [hδ_pos.ne'] <;> ring
      rw [h6] at h5
      exact h5
    simpa [d] using h4
  have hd1 : d < δ := by
    have h2 : x / δ < (b : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
    have h5 : x < ((b : ℝ) + 1) * δ := by
      have h6 : (x / δ) * δ < ((b : ℝ) + 1) * δ := mul_lt_mul_of_pos_right h2 hδ_pos
      have h7 : (x / δ) * δ = x := by field_simp [hδ_pos.ne'] <;> ring
      rw [h7] at h6
      exact h6
    have h8 : x - (b : ℝ) * δ < δ := by linarith
    simpa [d] using h8
  let slope : ℝ := (a : ℝ) * δ
  let intercept : ℝ := (b : ℝ) * δ + d
  have hslope2 : slope < ((a + 1 : ℤ) : ℝ) * δ := by
    simp [slope] <;> linarith [hδ_pos]
  have hint2 : intercept < ((b + 1 : ℤ) : ℝ) * δ := by
    simp [intercept] <;> linarith [hδ_pos, hd1]
  have heq : p 1 = slope * p 0 + intercept := by
    simp [slope, intercept, d, hx_def] <;> ring
  have h_main : ∃ (slope' : ℝ), slope' ∈ Set.Ico ((a : ℝ) * δ) (((a + 1 : ℤ) : ℝ) * δ) ∧
      ∃ (intercept' : ℝ), intercept' ∈ Set.Ico ((b : ℝ) * δ) (((b + 1 : ℤ) : ℝ) * δ) ∧
        p 1 = slope' * p 0 + intercept' := by
    refine ⟨slope, ⟨by rfl, hslope2⟩, intercept, ⟨by simp [intercept, hd0] <;> linarith, hint2⟩, heq⟩
  simpa [snapToTubeFloor, tubeToStand, _root_.DyadicTube.toSet, hδ_eq] using h_main

/-! ============================================================================
   Dyadic square geometric bounds
   ============================================================================ -/

/-- The center of a dyadic square. -/
noncomputable def dyadicSquareCenter {n : ℕ} (q : DyadicSquare n) : Plane :=
  WithLp.toLp 2 fun i : Fin 2 =>
    if i = 0 then ((q.i : ℝ) + 1 / 2) * dyadicDelta n
    else ((q.j : ℝ) + 1 / 2) * dyadicDelta n

/-- Each dyadic square is contained in a closed ball of radius δn*√2/2
    centered at its center. -/
lemma dyadicSquare_subset_centerBall {n : ℕ} (q : DyadicSquare n) :
    (q.toSet : Set Plane) ⊆ Metric.closedBall (dyadicSquareCenter q)
      (dyadicDelta n * Real.sqrt 2 / 2) := by
  set δn := dyadicDelta n with hδn
  set c := dyadicSquareCenter q with hc
  intro x hx
  have hxi1 : (q.i : ℝ) * δn ≤ x 0 := hx.1
  have hxi2 : x 0 < ((q.i : ℝ) + 1) * δn := hx.2.1
  have hxj1 : (q.j : ℝ) * δn ≤ x 1 := hx.2.2.1
  have hxj2 : x 1 < ((q.j : ℝ) + 1) * δn := hx.2.2.2
  have h_pos : 0 < δn := dyadicDelta_pos n
  have hc0 : c 0 = ((q.i : ℝ) + (1 : ℝ) / 2) * δn := by
    have h : c 0 = ((q.i : ℝ) + (1 : ℝ) / 2) * dyadicDelta n := by
      simp [c, dyadicSquareCenter] <;> rfl
    rw [h, hδn]
  have hc1 : c 1 = ((q.j : ℝ) + (1 : ℝ) / 2) * δn := by
    have h : c 1 = ((q.j : ℝ) + (1 : ℝ) / 2) * dyadicDelta n := by
      simp [c, dyadicSquareCenter] <;> rfl
    rw [h, hδn]
  have h51 : x 0 - c 0 ≤ δn / 2 := by
    rw [hc0]
    have h : x 0 < ((q.i : ℝ) + 1) * δn := hxi2
    linarith
  have h52 : -(δn / 2) ≤ x 0 - c 0 := by
    rw [hc0]
    have h : (q.i : ℝ) * δn ≤ x 0 := hxi1
    linarith
  have h5 : |x 0 - c 0| ≤ δn / 2 := by
    rw [abs_le] <;> exact ⟨h52, h51⟩
  have h61 : x 1 - c 1 ≤ δn / 2 := by
    rw [hc1]
    have h : x 1 < ((q.j : ℝ) + 1) * δn := hxj2
    linarith
  have h62 : -(δn / 2) ≤ x 1 - c 1 := by
    rw [hc1]
    have h : (q.j : ℝ) * δn ≤ x 1 := hxj1
    linarith
  have h6 : |x 1 - c 1| ≤ δn / 2 := by
    rw [abs_le] <;> exact ⟨h62, h61⟩
  have h7 : ‖x - c‖ ^ 2 = (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 := by
    have h71 : ‖x - c‖ = Real.sqrt ((x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring
    rw [h71]
    have h72 : 0 ≤ (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 := by positivity
    rw [Real.sq_sqrt h72]
  have h8 : ‖x - c‖ ^ 2 ≤ (δn * Real.sqrt 2 / 2) ^ 2 := by
    have h9 : (x 0 - c 0) ^ 2 ≤ (δn / 2) ^ 2 := by
      have h10 : (x 0 - c 0) ^ 2 = |x 0 - c 0| ^ 2 := by simp [sq_abs]
      rw [h10]; gcongr <;> linarith
    have h10 : (x 1 - c 1) ^ 2 ≤ (δn / 2) ^ 2 := by
      have h11 : (x 1 - c 1) ^ 2 = |x 1 - c 1| ^ 2 := by simp [sq_abs]
      rw [h11]; gcongr <;> linarith
    have h13 : (δn * Real.sqrt 2 / 2) ^ 2 = 2 * (δn / 2) ^ 2 := by
      have h14 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp <;> nlinarith
    rw [h7, h13]; linarith
  have h15 : 0 ≤ ‖x - c‖ := by positivity
  have h16 : 0 ≤ δn * Real.sqrt 2 / 2 := by positivity
  have h17 : ‖x - c‖ ≤ δn * Real.sqrt 2 / 2 := by nlinarith
  simpa [Metric.mem_closedBall, dist_eq_norm] using h17

/-! ============================================================================
   Index bounds for floor-snapped tubes
   ============================================================================ -/

/-- a-index bound from strict slope bound |m| < 1. -/
lemma snapToTubeFloor_a_bound {n : ℕ} {ℓ : AffineLine} {p : Plane}
    (h_slope : |(affineLineSlopeIntercept ℓ).1| < 1) :
    -(2 ^ n : ℤ) ≤ (snapToTubeFloor n ℓ p).a ∧
    (snapToTubeFloor n ℓ p).a < (2 ^ n : ℤ) := by
  let δ := dyadicDelta n
  let m := (affineLineSlopeIntercept ℓ).1
  let a : ℤ := ⌊m / δ⌋
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_inv : (1 : ℝ) / δ = (2 ^ n : ℝ) := by
    simp [δ, dyadicDelta] <;> field_simp <;> ring
  have h1 : -1 < m := by linarith [abs_lt.mp h_slope]
  have h2 : m < 1 := by linarith [abs_lt.mp h_slope]
  have h3 : -(1 / δ) < m / δ := by
    have h4 : m / δ > (-1 : ℝ) / δ := by gcongr
    have h5 : (-1 : ℝ) / δ = -(1 / δ) := by ring
    rw [h5] at h4
    exact h4
  have h4 : m / δ < 1 / δ := by
    have h5 : m / δ < (1 : ℝ) / δ := by gcongr
    exact h5
  rw [hδ_inv] at h3 h4
  have ha1 : -(2 ^ n : ℤ) ≤ a := by
    have h6 : m / δ < (a : ℝ) + 1 := Int.lt_floor_add_one (m / δ)
    by_contra h7
    have h8 : a < -(2 ^ n : ℤ) := by omega
    have h9 : (a : ℝ) < -(2 ^ n : ℝ) := by exact_mod_cast h8
    have h10 : (a : ℝ) + 1 ≤ -(2 ^ n : ℝ) := by
      have h11 : a + 1 ≤ -(2 ^ n : ℤ) := by omega
      exact_mod_cast h11
    linarith
  have ha2 : a < (2 ^ n : ℤ) := by
    have h6 : (a : ℝ) ≤ m / δ := Int.floor_le (m / δ)
    have h7 : (a : ℝ) < (2 ^ n : ℝ) := by linarith
    exact_mod_cast h7
  exact ⟨ha1, ha2⟩

/-- b-index bound from geometric constraints: p ∈ [0,1)², |m| < 1.

    Gives b ∈ [-3·2^n, 3·2^n), which is looser than tight but sufficient. -/
lemma snapToTubeFloor_b_bound {n : ℕ} {ℓ : AffineLine} {p : Plane}
    (hp0 : 0 ≤ p 0) (hp0' : p 0 < 1)
    (hp1 : 0 ≤ p 1) (hp1' : p 1 < 1)
    (h_slope : |(affineLineSlopeIntercept ℓ).1| < 1) :
    -3 * (2 ^ n : ℤ) ≤ (snapToTubeFloor n ℓ p).b ∧
    (snapToTubeFloor n ℓ p).b < 3 * (2 ^ n : ℤ) := by
  let δ := dyadicDelta n
  let m := (affineLineSlopeIntercept ℓ).1
  let a : ℤ := ⌊m / δ⌋
  let b : ℤ := ⌊(p 1 - (a : ℝ) * δ * p 0) / δ⌋
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_inv : (1 : ℝ) / δ = (2 ^ n : ℝ) := by
    simp [δ, dyadicDelta] <;> field_simp <;> ring
  -- Bounds on aδ: aδ ∈ (-1-δ, 1)
  have haδ1 : (a : ℝ) * δ < 1 := by
    have h1 : (a : ℝ) ≤ m / δ := Int.floor_le (m / δ)
    have h2 : m < 1 := by linarith [abs_lt.mp h_slope]
    have h3 : (a : ℝ) * δ ≤ m := by
      calc (a : ℝ) * δ ≤ (m / δ) * δ := by gcongr
           _ = m := by field_simp [hδ_pos.ne'] <;> ring
    linarith
  have haδ2 : (a : ℝ) * δ > -1 - δ := by
    have h1 : m / δ < (a : ℝ) + 1 := Int.lt_floor_add_one (m / δ)
    have h2 : m > -1 := by linarith [abs_lt.mp h_slope]
    have h3 : (m / δ) * δ < ((a : ℝ) + 1) * δ :=
      mul_lt_mul_of_pos_right h1 hδ_pos
    have h4 : m < ((a : ℝ) + 1) * δ := by
      have h5 : (m / δ) * δ = m := by field_simp [hδ_pos.ne'] <;> ring
      rw [h5] at h3
      exact h3
    have h6 : ((a : ℝ) + 1) * δ = (a : ℝ) * δ + δ := by ring
    rw [h6] at h4
    have h7 : -1 < (a : ℝ) * δ + δ := by linarith
    linarith
  -- Bounds on x = p1 - aδ * p0
  set x := p 1 - (a : ℝ) * δ * p 0 with hx_def
  have hx1 : x > -1 := by
    by_cases h : (a : ℝ) * δ ≥ 0
    · have h4 : (a : ℝ) * δ * p 0 < 1 := by
        have h5 : (a : ℝ) * δ < 1 := haδ1
        nlinarith
      nlinarith [hx_def, hp1]
    · have h4 : (a : ℝ) * δ < 0 := by linarith
      nlinarith [hx_def, hp1, hp0]
  have hx2 : x < 2 + δ := by
    by_cases h : (a : ℝ) * δ ≥ 0
    · nlinarith [hx_def, hp1']
    · have h4 : (a : ℝ) * δ > -1 - δ := haδ2
      nlinarith [hx_def, hp1', hp0']
  -- Bounds on b = floor(x/δ)
  have hxb1 : x / δ > -1 / δ := by gcongr
  have hxb2 : x / δ < (2 + δ) / δ := by gcongr
  have h_2δ : (2 + δ) / δ = 2 / δ + 1 := by
    field_simp [hδ_pos.ne'] <;> ring
  rw [h_2δ] at hxb2
  have hxb1' : x / δ > -(2 ^ n : ℝ) := by
    have h_neg : -1 / δ = -(1 / δ) := by ring
    have h : -(1 / δ) = -(2 ^ n : ℝ) := by rw [hδ_inv]
    rw [h_neg, h] at hxb1
    exact hxb1
  have hxb2' : x / δ < 2 * (2 ^ n : ℝ) + 1 := by
    have h : 2 / δ = 2 * (1 / δ) := by ring
    rw [h, hδ_inv] at hxb2
    exact hxb2
  have h_pow_ge_one : (2 ^ n : ℝ) ≥ 1 := by
    have h : (1 : ℝ) ≤ (2 ^ n : ℝ) := by
      exact_mod_cast Nat.one_le_pow n 2 (by norm_num)
    exact h
  have hb1 : -3 * (2 ^ n : ℤ) ≤ b := by
    have h1 : x / δ < (b : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
    have h2 : (b : ℝ) > x / δ - 1 := by linarith
    have h3 : (b : ℝ) > -(2 ^ n : ℝ) - 1 := by linarith [hxb1']
    have h4 : b ≥ -(2 ^ n : ℤ) := by
      by_contra h5
      have h6 : b ≤ -(2 ^ n : ℤ) - 1 := by omega
      have h7 : (b : ℝ) ≤ -(2 ^ n : ℝ) - 1 := by exact_mod_cast h6
      have h8 : (b : ℝ) > -(2 ^ n : ℝ) - 1 := h3
      linarith
    have h9 : -3 * (2 ^ n : ℤ) ≤ -(2 ^ n : ℤ) := by
      have h10 : (0 : ℤ) ≤ 2 ^ n := by positivity
      omega
    omega
  have hb2 : b < 3 * (2 ^ n : ℤ) := by
    have h1 : (b : ℝ) ≤ x / δ := Int.floor_le (x / δ)
    have h2 : (b : ℝ) < 2 * (2 ^ n : ℝ) + 1 := by linarith [hxb2']
    have h3 : b ≤ 2 * (2 ^ n : ℤ) := by
      by_contra h4
      have h5 : b > 2 * (2 ^ n : ℤ) := by omega
      have h6 : b ≥ 2 * (2 ^ n : ℤ) + 1 := by omega
      have h7 : (b : ℝ) ≥ 2 * (2 ^ n : ℝ) + 1 := by exact_mod_cast h6
      linarith
    have h4 : 2 * (2 ^ n : ℤ) < 3 * (2 ^ n : ℤ) := by
      have h5 : (0 : ℤ) < 2 ^ n := by positivity
      omega
    omega
  exact ⟨hb1, hb2⟩

/-! ============================================================================
   Square index bounds
   ============================================================================ -/

/-- If P ⊆ [0,1)², any dyadic square meeting P has indices in [0, 2^n). -/
lemma squares_unit_from_unit_interval {n : ℕ} {P : Set Plane}
    (hP : ∀ p ∈ P, 0 ≤ p 0 ∧ p 0 < 1 ∧ 0 ≤ p 1 ∧ p 1 < 1)
    {q : DyadicSquare n} (hq : (P ∩ (q.toSet : Set Plane)).Nonempty) :
    0 ≤ q.i ∧ q.i < (2 ^ n : ℤ) ∧ 0 ≤ q.j ∧ q.j < (2 ^ n : ℤ) := by
  rcases hq with ⟨p, hpP, hpq⟩
  have h_p := hP p hpP
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have hδ_inv : (2 ^ n : ℝ) * dyadicDelta n = 1 := by
    simp [dyadicDelta] <;> field_simp <;> ring
  have hxi1 : (q.i : ℝ) * dyadicDelta n ≤ p 0 := hpq.1
  have hxi2 : p 0 < ((q.i : ℝ) + 1) * dyadicDelta n := hpq.2.1
  have hyi1 : (q.j : ℝ) * dyadicDelta n ≤ p 1 := hpq.2.2.1
  have hyi2 : p 1 < ((q.j : ℝ) + 1) * dyadicDelta n := hpq.2.2.2
  have h1 : 0 ≤ q.i := by
    by_contra h
    have h2 : q.i < 0 := by omega
    have h3 : q.i ≤ -1 := by omega
    have h4 : (q.i : ℝ) ≤ -1 := by exact_mod_cast h3
    have h5 : (q.i : ℝ) + 1 ≤ 0 := by linarith
    have h6 : ((q.i : ℝ) + 1) * dyadicDelta n ≤ 0 := by
      have h7 : 0 ≤ dyadicDelta n := by positivity
      nlinarith
    have h8 : p 0 < 0 := by linarith [hxi2]
    have h9 : 0 ≤ p 0 := h_p.1
    linarith
  have h2 : q.i < (2 ^ n : ℤ) := by
    by_contra h
    have h3 : q.i ≥ (2 ^ n : ℤ) := by omega
    have h4 : (q.i : ℝ) ≥ (2 ^ n : ℝ) := by exact_mod_cast h3
    have h5 : (q.i : ℝ) * dyadicDelta n ≥ (2 ^ n : ℝ) * dyadicDelta n := by gcongr
    have h6 : (q.i : ℝ) * dyadicDelta n ≥ 1 := by
      calc (q.i : ℝ) * dyadicDelta n
        ≥ (2 ^ n : ℝ) * dyadicDelta n := h5
      _ = 1 := hδ_inv
    have h7 : p 0 ≥ 1 := by linarith [hxi1]
    have h8 : p 0 < 1 := h_p.2.1
    linarith
  have h3 : 0 ≤ q.j := by
    by_contra h
    have h2 : q.j < 0 := by omega
    have h3 : q.j ≤ -1 := by omega
    have h4 : (q.j : ℝ) ≤ -1 := by exact_mod_cast h3
    have h5 : (q.j : ℝ) + 1 ≤ 0 := by linarith
    have h6 : ((q.j : ℝ) + 1) * dyadicDelta n ≤ 0 := by
      have h7 : 0 ≤ dyadicDelta n := by positivity
      nlinarith
    have h8 : p 1 < 0 := by linarith [hyi2]
    have h9 : 0 ≤ p 1 := h_p.2.2.1
    linarith
  have h4 : q.j < (2 ^ n : ℤ) := by
    by_contra h
    have h3 : q.j ≥ (2 ^ n : ℤ) := by omega
    have h4 : (q.j : ℝ) ≥ (2 ^ n : ℝ) := by exact_mod_cast h3
    have h5 : (q.j : ℝ) * dyadicDelta n ≥ (2 ^ n : ℝ) * dyadicDelta n := by gcongr
    have h6 : (q.j : ℝ) * dyadicDelta n ≥ 1 := by
      calc (q.j : ℝ) * dyadicDelta n
        ≥ (2 ^ n : ℝ) * dyadicDelta n := h5
      _ = 1 := hδ_inv
    have h7 : p 1 ≥ 1 := by linarith [hyi1]
    have h8 : p 1 < 1 := h_p.2.2.2
    linarith
  exact ⟨h1, h2, h3, h4⟩

/-! ============================================================================
   Global tube cardinality bound
   ============================================================================ -/

/-- Given a- and b-index bounds, T₀.card ≤ 12·16^n. -/
lemma tube_card_bound_geometric {n : ℕ} {T₀ : Finset (DyadicTube n)}
    (h_a_bound : ∀ T ∈ T₀, -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ))
    (h_b_bound : ∀ T ∈ T₀, -3 * (2 ^ n : ℤ) ≤ T.b ∧ T.b < 3 * (2 ^ n : ℤ)) :
    T₀.card ≤ 12 * 16 ^ n := by
  let aSet : Finset ℤ := Finset.Ico (-(2 ^ n)) (2 ^ n)
  let bSet : Finset ℤ := Finset.Ico (-3 * (2 ^ n)) (3 * (2 ^ n))
  let allowed : Finset (DyadicTube n) :=
    aSet.biUnion fun a => bSet.image fun b => (⟨a, b⟩ : DyadicTube n)
  have h_sub : T₀ ⊆ allowed := by
    intro T hT
    have ha := h_a_bound T hT
    have hb := h_b_bound T hT
    simp only [allowed, Finset.mem_biUnion]
    refine ⟨T.a, ?_⟩
    constructor
    · simp only [aSet, Finset.mem_Ico] <;> exact ha
    · simp only [Finset.mem_image]
      refine ⟨T.b, ?_⟩
      constructor
      · simp only [bSet, Finset.mem_Ico] <;> exact hb
      · cases T <;> rfl
  have h_card_a : aSet.card = 2 * 2 ^ n := by
    rw [show aSet = Finset.Ico (-(2 ^ n)) (2 ^ n) from rfl]
    rw [Int.card_Ico]
    have h2 : (2 ^ n : ℤ) - (-(2 ^ n : ℤ)) = 2 * (2 ^ n : ℤ) := by ring
    rw [h2]
    have h3 : 0 ≤ 2 * (2 ^ n : ℤ) := by positivity
    norm_cast <;> omega
  have h_card_b : bSet.card = 6 * 2 ^ n := by
    rw [show bSet = Finset.Ico (-3 * (2 ^ n)) (3 * (2 ^ n)) from rfl]
    rw [Int.card_Ico]
    have h2 : (3 * (2 ^ n : ℤ)) - (-3 * (2 ^ n : ℤ)) = 6 * (2 ^ n : ℤ) := by ring
    rw [h2]
    have h3 : 0 ≤ 2 * (2 ^ n : ℤ) := by positivity
    norm_cast <;> omega
  have h_card_allowed : allowed.card ≤ aSet.card * bSet.card := by
    calc allowed.card
      ≤ ∑ a ∈ aSet, (bSet.image fun b : ℤ => (⟨a, b⟩ : DyadicTube n)).card :=
        Finset.card_biUnion_le
    _ = aSet.card * bSet.card := by
      have h : ∀ a ∈ aSet, (bSet.image fun b : ℤ => (⟨a, b⟩ : DyadicTube n)).card = bSet.card := by
        intro a _
        apply Finset.card_image_of_injective
        intro b1 b2 h
        simpa using h
      rw [Finset.sum_congr rfl h, Finset.sum_const]
      <;> simp [h_card_b] <;> ring
  have h_main : allowed.card ≤ 12 * 16 ^ n := by
    calc allowed.card
      ≤ aSet.card * bSet.card := h_card_allowed
    _ = (2 * 2 ^ n) * (6 * 2 ^ n) := by rw [h_card_a, h_card_b]
    _ = 12 * (2 ^ n * 2 ^ n) := by ring
    _ ≤ 12 * 16 ^ n := by
      have h : 2 ^ n * 2 ^ n ≤ 16 ^ n := by
        have h2 : 2 ^ n ≤ 4 ^ n := by
          gcongr <;> norm_num
        have h3 : 2 ^ n * 2 ^ n ≤ 4 ^ n * 4 ^ n := by gcongr
        have h4 : 4 ^ n * 4 ^ n = 16 ^ n := by
          rw [←mul_pow] <;> norm_num
        rw [h4] at h3
        exact h3
      nlinarith
  exact le_trans (Finset.card_le_card h_sub) h_main

/-! ============================================================================
   Main construction with floor snapping + bridge hypotheses
   ============================================================================ -/

/-- Construct a NiceConfiguration with all 4 bridge hypotheses using floor snapping.

    Input: continuous incidence data with P ⊆ [0,1)², strict slope bound |m| < 1.
    Output: NiceConfiguration satisfying h_squares_unit, h_tubes_strip,
            h_tubes_bounded, and incidence_transfer. -/
lemma construct_nice_configuration_with_bridge
    {δ s t C_P C_T : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hs_pos : 0 < s) (hst : s < t)
    (hCP_pos : 0 < C_P) (hCT_pos : 0 < C_T)
    (P : Set Plane)
    (hP_unit : ∀ p ∈ P, 0 ≤ p 0 ∧ p 0 < 1 ∧ 0 ≤ p 1 ∧ p 1 < 1)
    (hP_sset : IsDeltaSSet δ t C_P P)
    (Tp : Plane → Finset AffineLine)
    (hTp_sset : ∀ p ∈ P, IsDeltaSSet δ s C_T (Tp p : Set AffineLine))
    (hTp_near : ∀ p ∈ P, ∀ ℓ ∈ Tp p, p ∈ Metric.cthickening δ ℓ.1)
    (hTp_bdd : ∀ p ∈ P, ∀ ℓ ∈ Tp p, ℓ.offset ∈ Metric.closedBall 0 2)
    (hTp_slope : ∀ p ∈ P, ∀ ℓ ∈ Tp p,
      |(affineLineSlopeIntercept ℓ).1| < 1) :
    ∃ (n : ℕ) (C₁ : ℝ) (M : ℕ) (hC₁ : 1 ≤ C₁) (hM : 0 < M)
      (config : CombiningTheorem.NiceConfiguration n s C₁ M),
      config.P₀.Nonempty ∧
      (∀ p ∈ config.P₀, 0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧
        0 ≤ p.j ∧ p.j < (2 ^ n : ℤ)) ∧
      (∀ T ∈ config.T₀, -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ)) ∧
      config.T₀.card ≤ 12 * 16^n ∧
      (∀ (p : MainSquare n) (hp : p ∈ config.P₀) (T : MainTube n)
        (hT : T ∈ config.tubeFamily p hp),
        ((tubeToStand T).toSet ∩ (squareToStand p).toSet).Nonempty) ∧
      (config.P₀.card : ENNReal) ≥ Metric.externalCoveringNumber δ.toNNReal P := by
  -- Step 1: Choose dyadic scale n
  rcases choose_dyadic_scale δ hδ_pos (by linarith) with ⟨n, hδn, hδn'⟩
  -- Step 2: P is bounded (since P ⊆ [0,1)²)
  have hP_bdd : Bornology.IsBounded P := by
    have h : P ⊆ Metric.closedBall (0 : Plane) 2 := by
      intro p hp
      have hunit := hP_unit p hp
      have h1 : 0 ≤ p 0 := hunit.1
      have h2 : p 0 < 1 := hunit.2.1
      have h3 : 0 ≤ p 1 := hunit.2.2.1
      have h4 : p 1 < 1 := hunit.2.2.2
      have h5 : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
        have h51 : ‖p‖ = Real.sqrt ((p 0) ^ 2 + (p 1) ^ 2) := by
          simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring
        rw [h51]
        have h52 : 0 ≤ (p 0) ^ 2 + (p 1) ^ 2 := by positivity
        rw [Real.sq_sqrt h52]
      have h6 : ‖p‖ ^ 2 ≤ 4 := by
        rw [h5] <;> nlinarith
      have h7 : 0 ≤ ‖p‖ := by positivity
      have h8 : ‖p‖ ≤ 2 := by nlinarith
      simpa [Metric.mem_closedBall, dist_zero_right] using h8
    exact (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mpr ⟨2, h⟩
  -- Step 3: Cover P by dyadic squares
  rcases cover_by_dyadic_squares (n := n) hP_bdd with ⟨squares_all, hcover⟩
  -- Step 4: Filter to squares intersecting P
  let squares : Finset (DyadicSquare n) :=
    squares_all.filter (fun q => (P ∩ (q.toSet : Set Plane)).Nonempty)
  have hP_nonempty : P.Nonempty := hP_sset.1
  have h_squares_nonempty : squares.Nonempty := by
    rcases hP_nonempty with ⟨p, hp⟩
    have hpc : p ∈ ⋃ q ∈ squares_all, (q.toSet : Set Plane) := hcover hp
    rcases Set.mem_iUnion₂.mp hpc with ⟨q, hq_all, hq_p⟩
    have hq : q ∈ squares := by
      have hq2 : q ∈ squares_all ∧ (P ∩ (q.toSet : Set Plane)).Nonempty :=
        ⟨hq_all, ⟨p, hp, hq_p⟩⟩
      exact Finset.mem_filter.mpr hq2
    exact ⟨q, hq⟩
  -- Step 5: Choose representative points
  have h_main_choose : ∀ (q : DyadicSquare n), q ∈ squares →
      ∃ (y : Plane), y ∈ P ∧ y ∈ (q.toSet : Set Plane) := by
    intro q hq
    have h : (P ∩ (q.toSet : Set Plane)).Nonempty := by
      have h2 : q ∈ squares_all ∧ (P ∩ (q.toSet : Set Plane)).Nonempty :=
        Finset.mem_filter.mp hq
      exact h2.2
    rcases h with ⟨y, hyP, hyQ⟩
    exact ⟨y, hyP, hyQ⟩
  choose x hxP hxQ using h_main_choose
  -- Step 6: Snap tubes using FLOOR snapping
  let rawTubes : (q : DyadicSquare n) → q ∈ squares → Finset (DyadicTube n) :=
    fun q hq => (Tp (x q hq)).image (fun ℓ => snapToTubeFloor n ℓ (x q hq))
  have h_raw_nonempty : ∀ q hq, (rawTubes q hq).Nonempty := by
    intro q hq
    have hTp_nonempty : (Tp (x q hq)).Nonempty := (hTp_sset (x q hq) (hxP q hq)).1
    exact hTp_nonempty.image _
  -- Step 7: Provenance
  have h_raw_provenance : ∀ q hq T, T ∈ rawTubes q hq →
      ∃ (ℓ : AffineLine), ℓ ∈ Tp (x q hq) ∧ T = snapToTubeFloor n ℓ (x q hq) := by
    intro q hq T hT
    have h : ∃ (ℓ : AffineLine), ℓ ∈ Tp (x q hq) ∧ snapToTubeFloor n ℓ (x q hq) = T := by
      simpa [rawTubes, Finset.mem_image] using hT
    rcases h with ⟨ℓ, hℓ, h_eq⟩
    exact ⟨ℓ, hℓ, h_eq.symm⟩
  -- Step 8: Main incidence
  have h_intersect : ∀ (q : DyadicSquare n) (hq : q ∈ squares) (T : DyadicTube n),
      T ∈ rawTubes q hq → (T.toSet ∩ (q.toSet : Set Plane)).Nonempty := by
    intro q hq T hT
    rcases h_raw_provenance q hq T hT with ⟨ℓ, hℓ, rfl⟩
    have h1 : x q hq ∈ (snapToTubeFloor n ℓ (x q hq)).toSet :=
      snapToTubeFloor_main_incidence
    have h2 : x q hq ∈ (q.toSet : Set Plane) := hxQ q hq
    exact ⟨x q hq, h1, h2⟩
  -- Step 9: Stand incidence
  have h_stand_incidence : ∀ (q : DyadicSquare n) (hq : q ∈ squares) (T : DyadicTube n),
      T ∈ rawTubes q hq →
      ((tubeToStand T).toSet ∩ (squareToStand q).toSet).Nonempty := by
    intro q hq T hT
    rcases h_raw_provenance q hq T hT with ⟨ℓ, hℓ, rfl⟩
    let p_rep := x q hq
    have h1 : (p_rep 0, p_rep 1) ∈ (tubeToStand (snapToTubeFloor n ℓ p_rep)).toSet :=
      snapToTubeFloor_stand_incidence
    have h2 : p_rep ∈ (q.toSet : Set Plane) := hxQ q hq
    let q' : ℝ × ℝ := (p_rep 0, p_rep 1)
    have h3 : q' ∈ (squareToStand q).toSet := by
      simp only [squareToStand, _root_.DyadicSquare.toSet, Set.mem_prod, Set.mem_Ico]
      have hδ_eq : dyadicDelta n = _root_.dyadicDelta n := by
        simp [dyadicDelta, _root_.dyadicDelta] <;> rfl
      constructor
      · constructor
        · rw [←hδ_eq] <;> exact h2.1
        · rw [←hδ_eq] <;> exact h2.2.1
      · constructor
        · rw [←hδ_eq] <;> exact h2.2.2.1
        · rw [←hδ_eq] <;> exact h2.2.2.2
    exact ⟨q', h1, h3⟩
  -- Step 10: a-index bounds
  have h_a_bounds : ∀ q hq T, T ∈ rawTubes q hq →
      -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ) := by
    intro q hq T hT
    rcases h_raw_provenance q hq T hT with ⟨ℓ, hℓ, rfl⟩
    exact snapToTubeFloor_a_bound (hTp_slope (x q hq) (hxP q hq) ℓ hℓ)
  -- Step 11: b-index bounds
  have h_b_bounds : ∀ q hq T, T ∈ rawTubes q hq →
      -3 * (2 ^ n : ℤ) ≤ T.b ∧ T.b < 3 * (2 ^ n : ℤ) := by
    intro q hq T hT
    rcases h_raw_provenance q hq T hT with ⟨ℓ, hℓ, rfl⟩
    let p_rep := x q hq
    have h_unit := hP_unit p_rep (hxP q hq)
    exact snapToTubeFloor_b_bound h_unit.1 h_unit.2.1 h_unit.2.2.1 h_unit.2.2.2
      (hTp_slope p_rep (hxP q hq) ℓ hℓ)
  -- Step 12: S-set property (trivial bound)
  let C' (q : DyadicSquare n) (hq : q ∈ squares) : ℝ := (dyadicDelta n) ^ (-s)
  have hC'_pos : ∀ q hq, 0 < C' q hq := by
    intro q hq
    exact Real.rpow_pos_of_pos (dyadicDelta_pos n) _
  have hC'_sset : ∀ q hq, IsDeltaSSet (dyadicDelta n) s (C' q hq)
      (rawTubes q hq : Set (DyadicTube n)) := by
    intro q hq
    have h_nonempty : (rawTubes q hq : Set (DyadicTube n)).Nonempty := h_raw_nonempty q hq
    exact any_nonempty_set_is_sset (dyadicDelta_pos n) (by linarith [hs_pos]) h_nonempty
  let f (q : DyadicSquare n) : ℝ := if hq : q ∈ squares then C' q hq else 0
  have hf_eq : ∀ q hq, f q = C' q hq := by
    intro q hq
    simp [f, hq]
  let C₁ : ℝ := 1 + ∑ q ∈ squares, f q
  have hC₁_one : 1 ≤ C₁ := by
    have h_nonneg : 0 ≤ ∑ q ∈ squares, f q := by
      apply Finset.sum_nonneg
      intro i _
      by_cases hi : i ∈ squares
      · rw [hf_eq i hi]; exact (hC'_pos i hi).le
      · simp [f, hi]
    linarith
  have hC₁_ge : ∀ q hq, C' q hq ≤ C₁ := by
    intro q hq
    have h1 : f q = C' q hq := hf_eq q hq
    have h : f q ≤ ∑ q' ∈ squares, f q' := by
      apply Finset.single_le_sum
      · intro i _
        by_cases hi : i ∈ squares
        · rw [hf_eq i hi]; exact (hC'_pos i hi).le
        · simp [f, hi]
      · exact hq
    rw [h1] at h
    linarith
  have h_mono_const : ∀ {S : Set (DyadicTube n)} {C1 C2 : ℝ},
      IsDeltaSSet (dyadicDelta n) s C1 S → C1 ≤ C2 → IsDeltaSSet (dyadicDelta n) s C2 S := by
    intro S C1 C2 h hC
    rcases h with ⟨hne, hδ, hC1_pos, hs, hbound⟩
    have hC2_pos : 0 < C2 := by linarith
    refine ⟨hne, hδ, hC2_pos, hs, fun x r hr => ?_⟩
    have h4 := hbound x r hr
    have h5 : ENNReal.ofReal C1 ≤ ENNReal.ofReal C2 := ENNReal.ofReal_le_ofReal hC
    have h6 : ENNReal.ofReal C1 * (ENNReal.ofReal r) ^ s ≤
        ENNReal.ofReal C2 * (ENNReal.ofReal r) ^ s := by gcongr
    have h7 : (ENNReal.ofReal C1 * (ENNReal.ofReal r) ^ s) *
        Metric.externalCoveringNumber (dyadicDelta n).toNNReal S ≤
        (ENNReal.ofReal C2 * (ENNReal.ofReal r) ^ s) *
        Metric.externalCoveringNumber (dyadicDelta n).toNNReal S := by gcongr
    exact le_trans h4 h7
  have h_tube_sset_C1 : ∀ q hq, IsDeltaSSet (dyadicDelta n) s C₁
      (rawTubes q hq : Set (DyadicTube n)) := by
    intro q hq
    exact h_mono_const (hC'_sset q hq) (hC₁_ge q hq)
  -- Step 13: Uniformize (M = 1)
  let M : ℕ := 1
  have hM_pos : 0 < M := by norm_num
  have hM_min : ∀ q hq, M ≤ (rawTubes q hq).card := by
    intro q hq
    have h : 0 < (rawTubes q hq).card := (h_raw_nonempty q hq).card_pos
    exact h
  let T₀ : Finset (DyadicTube n) :=
    squares.attach.biUnion (fun q : {q // q ∈ squares} => rawTubes q q.property)
  have h_subset_T0 : ∀ q hq, rawTubes q hq ⊆ T₀ := by
    intro q hq
    intro T hT
    have hq' : (⟨q, hq⟩ : {q // q ∈ squares}) ∈ squares.attach := by simp
    simp only [T₀, Finset.mem_biUnion]
    exact ⟨⟨q, hq⟩, hq', hT⟩
  rcases @uniformize_tube_families n s C₁ M squares rawTubes T₀
    h_subset_T0 h_intersect hM_min hM_pos
    with ⟨tubeFamily, ht_sub, ht_card, ht_intersect⟩
  -- S-set for uniformized families
  have h_tube_sset : ∀ q hq, IsDeltaSSet (dyadicDelta n) s C₁
      (tubeFamily q hq : Set (DyadicTube n)) := by
    intro q hq
    have h_nonempty : (tubeFamily q hq : Set (DyadicTube n)).Nonempty := by
      have h_card : (tubeFamily q hq).card = M := ht_card q hq
      have h_pos : 0 < (tubeFamily q hq).card := by rw [h_card] <;> exact hM_pos
      exact Finset.card_pos.mp h_pos
    have h_sset_small : IsDeltaSSet (dyadicDelta n) s ((dyadicDelta n) ^ (-s))
        (tubeFamily q hq : Set (DyadicTube n)) :=
      any_nonempty_set_is_sset (dyadicDelta_pos n) (by linarith [hs_pos]) h_nonempty
    have h_C'_le : (dyadicDelta n) ^ (-s) ≤ C₁ := hC₁_ge q hq
    exact h_mono_const h_sset_small h_C'_le
  -- Prove boundedness and strip before config
  have h_squares_unit : ∀ p ∈ squares,
      0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ n : ℤ) := by
    intro p hp
    have h_witness : ∃ (y : Plane), y ∈ P ∧ y ∈ (p.toSet : Set Plane) := by
      have h_filter : p ∈ squares_all.filter (fun q => (P ∩ (q.toSet : Set Plane)).Nonempty) := hp
      have h' : p ∈ squares_all ∧ (P ∩ (p.toSet : Set Plane)).Nonempty :=
        Finset.mem_filter.mp h_filter
      rcases h'.2 with ⟨y, hyP, hyQ⟩
      exact ⟨y, hyP, hyQ⟩
    rcases h_witness with ⟨y, hyP, hyQ⟩
    exact squares_unit_from_unit_interval hP_unit (hq := ⟨y, hyP, hyQ⟩)
  have h_tubes_strip : ∀ T ∈ T₀,
      -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ) := by
    intro T hT
    have h_biUnion : T ∈ squares.attach.biUnion (fun q : {q // q ∈ squares} => rawTubes q q.property) := hT
    have h' : ∃ (q : {q // q ∈ squares}), q ∈ squares.attach ∧ T ∈ rawTubes q q.property :=
      Finset.mem_biUnion.mp h_biUnion
    rcases h' with ⟨q, _, hT⟩
    exact h_a_bounds q q.property T hT
  have hδn_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have hδ_eq : dyadicDelta n = (2 : ℝ)^(-(n : ℝ)) := by
    simp [dyadicDelta, Real.rpow_neg] <;> field_simp
  have h_prod : (2 ^ n : ℝ) * dyadicDelta n = 1 := by
    rw [hδ_eq]
    have h1 : (2 ^ n : ℝ) = (2 : ℝ)^(n : ℝ) := by norm_cast
    rw [h1]
    have h2 : (2 : ℝ)^(n : ℝ) * (2 : ℝ)^(-(n : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num)]
      <;> simp
    exact h2
  have h_bounded_proof : Bornology.IsBounded (⋃ p ∈ (squares : Set (DyadicSquare n)), (p.toSet : Set Plane)) := by
    rw [Bornology.isBounded_biUnion (Finset.finite_toSet squares)]
    intro p _
    exact DyadicSquare.toSet_isBounded p
  have h_tube_params_proof : ∀ T ∈ T₀, |T.slope| ≤ 1 := by
    intro T hT
    have h_idx := h_tubes_strip T hT
    have h1 : |(T.a : ℝ)| ≤ (2 ^ n : ℝ) := by
      have h2 : -(2 ^ n : ℤ) ≤ T.a := h_idx.1
      have h3 : T.a < (2 ^ n : ℤ) := h_idx.2
      have h4 : T.a ≤ (2 ^ n : ℤ) := by linarith
      have h5 : -(2 ^ n : ℝ) ≤ (T.a : ℝ) := by exact_mod_cast h2
      have h6 : (T.a : ℝ) ≤ (2 ^ n : ℝ) := by exact_mod_cast h4
      exact abs_le.mpr ⟨h5, h6⟩
    have h7 : T.slope = (T.a : ℝ) * dyadicDelta n := by rfl
    rw [h7]
    have h8 : |(T.a : ℝ) * dyadicDelta n| = |(T.a : ℝ)| * dyadicDelta n := by
      rw [abs_mul, abs_of_pos hδn_pos]
    rw [h8]
    have h9 : |(T.a : ℝ)| * dyadicDelta n ≤ (2 ^ n : ℝ) * dyadicDelta n := by gcongr
    have h10 : (2 ^ n : ℝ) * dyadicDelta n = 1 := h_prod
    rw [h10] at h9
    exact h9
  -- Build config
  let config : CombiningTheorem.NiceConfiguration n s C₁ M :=
    { P₀ := squares
      T₀ := T₀
      tubeFamily := tubeFamily
      h_subset := fun q hq => Finset.Subset.trans (ht_sub q hq) (h_subset_T0 q hq)
      h_size := ht_card
      h_delta_s_set := h_tube_sset
      h_intersect := ht_intersect
      h_tube_parameters := Set.Finite.isBounded (Finset.finite_toSet T₀)
      h_bounded := h_bounded_proof }
  -- Step 14: Prove bridge hypotheses
  have h_squares_unit : ∀ p ∈ config.P₀,
      0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ n : ℤ) := by
    intro p hp
    have h_witness : ∃ (y : Plane), y ∈ P ∧ y ∈ (p.toSet : Set Plane) := by
      have h_filter : p ∈ squares_all.filter (fun q => (P ∩ (q.toSet : Set Plane)).Nonempty) := hp
      have h' : p ∈ squares_all ∧ (P ∩ (p.toSet : Set Plane)).Nonempty :=
        Finset.mem_filter.mp h_filter
      rcases h'.2 with ⟨y, hyP, hyQ⟩
      exact ⟨y, hyP, hyQ⟩
    rcases h_witness with ⟨y, hyP, hyQ⟩
    exact squares_unit_from_unit_interval hP_unit (hq := ⟨y, hyP, hyQ⟩)
  have h_tubes_strip : ∀ T ∈ config.T₀,
      -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ) := by
    intro T hT
    have h_biUnion : T ∈ squares.attach.biUnion (fun q : {q // q ∈ squares} => rawTubes q q.property) := hT
    have h' : ∃ (q : {q // q ∈ squares}), q ∈ squares.attach ∧ T ∈ rawTubes q q.property :=
      Finset.mem_biUnion.mp h_biUnion
    rcases h' with ⟨q, _, hT⟩
    exact h_a_bounds q q.property T hT
  have h_tubes_b_bounds : ∀ T ∈ config.T₀,
      -3 * (2 ^ n : ℤ) ≤ T.b ∧ T.b < 3 * (2 ^ n : ℤ) := by
    intro T hT
    have h_biUnion : T ∈ squares.attach.biUnion (fun q : {q // q ∈ squares} => rawTubes q q.property) := hT
    have h' : ∃ (q : {q // q ∈ squares}), q ∈ squares.attach ∧ T ∈ rawTubes q q.property :=
      Finset.mem_biUnion.mp h_biUnion
    rcases h' with ⟨q, _, hT⟩
    exact h_b_bounds q q.property T hT
  have h_card_bound : config.T₀.card ≤ 12 * 16 ^ n :=
    tube_card_bound_geometric h_tubes_strip h_tubes_b_bounds
  have h_incidence_transfer : ∀ (p : MainSquare n) (hp : p ∈ config.P₀)
      (T : MainTube n) (hT : T ∈ config.tubeFamily p hp),
      ((tubeToStand T).toSet ∩ (squareToStand p).toSet).Nonempty := by
    intro p hp T hT
    have h_in_raw : T ∈ rawTubes p hp := ht_sub p hp hT
    exact h_stand_incidence p hp T h_in_raw
  -- Step 15: Retention: P₀ squares cover P, each fits in a δ-ball
  have h_squares_cover : P ⊆ ⋃ q ∈ squares, (q.toSet : Set Plane) := by
    intro x hx
    have hpc : x ∈ ⋃ q ∈ squares_all, (q.toSet : Set Plane) := hcover hx
    rcases Set.mem_iUnion₂.mp hpc with ⟨q, hq_all, hq_x⟩
    have hq : q ∈ squares := by
      have hq2 : q ∈ squares_all ∧ (P ∩ (q.toSet : Set Plane)).Nonempty :=
        ⟨hq_all, ⟨x, hx, hq_x⟩⟩
      exact Finset.mem_filter.mpr hq2
    exact Set.mem_iUnion₂.mpr ⟨q, hq, hq_x⟩
  have h_sqrt2_half_lt_one : Real.sqrt 2 / 2 < 1 := by
    have h1 : Real.sqrt 2 < 2 := by
      have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h3 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      nlinarith
    have h4 : 0 < (2 : ℝ) := by norm_num
    calc
      Real.sqrt 2 / 2 < 2 / 2 := by gcongr
      _ = 1 := by norm_num
  have h_radius_le : (dyadicDelta n) * Real.sqrt 2 / 2 ≤ δ := by
    have h4 : (dyadicDelta n) ≤ δ := hδn
    have h5 : (dyadicDelta n) * Real.sqrt 2 / 2 ≤ δ * Real.sqrt 2 / 2 := by gcongr
    have h6 : δ * Real.sqrt 2 / 2 < δ := by
      have h7 : 0 < δ := hδ_pos
      have h8 : Real.sqrt 2 / 2 < 1 := h_sqrt2_half_lt_one
      calc
        δ * Real.sqrt 2 / 2 = δ * (Real.sqrt 2 / 2) := by ring
        _ < δ * 1 := by gcongr
        _ = δ := by ring
    exact h5.trans h6.le
  let centers : Finset Plane := squares.image dyadicSquareCenter
  have h_cover : Metric.IsCover δ.toNNReal P (centers : Set Plane) := by
    intro x hx
    have h9 : x ∈ ⋃ q ∈ squares, (q.toSet : Set Plane) := h_squares_cover hx
    rcases Set.mem_iUnion₂.mp h9 with ⟨q, hq, hxq⟩
    have h10 : x ∈ Metric.closedBall (dyadicSquareCenter q) δ := by
      have h11 : (q.toSet : Set Plane) ⊆ Metric.closedBall (dyadicSquareCenter q) (dyadicDelta n * Real.sqrt 2 / 2) :=
        dyadicSquare_subset_centerBall q
      have h12 : x ∈ Metric.closedBall (dyadicSquareCenter q) (dyadicDelta n * Real.sqrt 2 / 2) := h11 hxq
      have h13 : Metric.closedBall (dyadicSquareCenter q) (dyadicDelta n * Real.sqrt 2 / 2) ⊆
          Metric.closedBall (dyadicSquareCenter q) δ :=
        Metric.closedBall_subset_closedBall h_radius_le
      exact h13 h12
    have h14 : dyadicSquareCenter q ∈ (centers : Set Plane) := by
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    have h15 : dist x (dyadicSquareCenter q) ≤ δ := by
      simpa [Metric.mem_closedBall] using h10
    have h16 : edist x (dyadicSquareCenter q) ≤ ↑δ.toNNReal := by
      have h17 : edist x (dyadicSquareCenter q) = ENNReal.ofReal (dist x (dyadicSquareCenter q)) :=
        edist_dist x (dyadicSquareCenter q)
      rw [h17]
      exact ENNReal.ofReal_le_ofReal h15
    exact ⟨dyadicSquareCenter q, h14, h16⟩
  have h_retention : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
      (config.P₀.card : ENNReal) := by
    have h15 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
        ((centers : Set Plane).encard : ENNReal) := by
      exact_mod_cast Metric.IsCover.externalCoveringNumber_le_encard h_cover
    have h16 : ((centers : Set Plane).encard : ENNReal) = (centers.card : ENNReal) := by
      simp
    have h17 : centers.card ≤ squares.card := Finset.card_image_le
    have h18 : config.P₀ = squares := by rfl
    rw [h18]
    calc
      (Metric.externalCoveringNumber δ.toNNReal P : ENNReal)
        ≤ ((centers : Set Plane).encard : ENNReal) := h15
      _ = (centers.card : ENNReal) := h16
      _ ≤ (squares.card : ENNReal) := by exact_mod_cast h17
  exact ⟨n, C₁, M, hC₁_one, hM_pos, config,
    h_squares_nonempty, h_squares_unit, h_tubes_strip, h_card_bound, h_incidence_transfer, h_retention⟩

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
