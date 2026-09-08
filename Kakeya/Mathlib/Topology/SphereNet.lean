/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Topology.CoveringNumber

/-!
# Nets of the unit sphere

A `θ`-separated subset of the unit sphere has at most `sphereSeparatedCount.C n * θ ^ (-(n-1))`
elements, and a maximal such subset is a `θ`-net of the sphere. Ported from the
`Kakeya/Mathlib/Topology/CoveringNumber.lean` of an earlier development, from which these
declarations were later dropped; they are the direction-counting input of the bush bound
`Kakeya.bushCount_exists`.
-/

@[expose] public section

open Metric MeasureTheory

namespace Metric

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem one_add_pow_sub_one_sub_pow_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 + u) ^ n - (1 - u) ^ n ≤ n * 2 ^ n * u := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have h_nonneg_1pu : 0 ≤ 1 + u := by linarith
    have h_nonneg_1mu : 0 ≤ 1 - u := by linarith
    have h_1pu_le_2 : 1 + u ≤ 2 := by linarith
    have h_1mu_le_1 : 1 - u ≤ 1 := by linarith
    have h_diff_nonneg : 0 ≤ (1 + u) ^ n - (1 - u) ^ n := by
      have h : (1 - u) ^ n ≤ (1 + u) ^ n :=
        pow_le_pow_left₀ (by linarith) (by linarith) n
      linarith
    have h_1mu_pow_le_1 : (1 - u) ^ n ≤ 1 :=
      pow_le_one₀ h_nonneg_1mu h_1mu_le_1
    have h_two_pow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ n :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
    have h_2u_nonneg : 0 ≤ 2 * u := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hu
    have htemp : 2 * u * (1 - u) ^ n ≤ 2 * u := by
      calc
        2 * u * (1 - u) ^ n ≤ 2 * u * 1 :=
          mul_le_mul_of_nonneg_left h_1mu_pow_le_1 h_2u_nonneg
        _ = 2 * u := by ring
    have htemp2 : (1 + u) * ((1 + u) ^ n - (1 - u) ^ n) ≤ 2 * ((1 + u) ^ n - (1 - u) ^ n) :=
      mul_le_mul_of_nonneg_right h_1pu_le_2 h_diff_nonneg
    have htemp3 : 2 * ((1 + u) ^ n - (1 - u) ^ n) ≤ 2 * (n * 2 ^ n * u) :=
      mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 2)
    have h_factor : 2 * (n : ℝ) * ((2 : ℝ) ^ n) + 2 ≤
        2 * (n : ℝ) * ((2 : ℝ) ^ n) + 2 * ((2 : ℝ) ^ n) := by
      nlinarith
    simpa [Nat.cast_succ] using
      calc
        (1 + u) ^ (n + 1) - (1 - u) ^ (n + 1)
            = (1 + u) * ((1 + u) ^ n - (1 - u) ^ n) + 2 * u * (1 - u) ^ n := by
          ring
        _ ≤ (1 + u) * ((1 + u) ^ n - (1 - u) ^ n) + 2 * u := by
          nlinarith
        _ ≤ 2 * ((1 + u) ^ n - (1 - u) ^ n) + 2 * u := by
          nlinarith
        _ ≤ 2 * (n * 2 ^ n * u) + 2 * u := by
          nlinarith
        _ = (2 * (n : ℝ) * ((2 : ℝ) ^ n) + 2) * u := by
          ring
        _ ≤ (2 * (n : ℝ) * ((2 : ℝ) ^ n) + 2 * ((2 : ℝ) ^ n)) * u :=
          mul_le_mul_of_nonneg_right h_factor hu
        _ = (n + 1) * 2 ^ (n + 1) * u := by
          ring

/-- The constant in `Metric.card_mul_pow_le_of_sphere_separated`, depending only on the
ambient dimension: `C n = n * 2 ^ (2 * n)`. For `n = 3` it equals `192`. -/
noncomputable abbrev sphereSeparatedCount.C (n : ℕ) : ℝ := n * 2 ^ (2 * n)

/-- The closed `θ`-thickening of the unit sphere is contained in the annulus
`1 - θ ≤ ‖y‖ ≤ 1 + θ`, and its volume is therefore *linear* in `θ`: at most
`n * 2 ^ n * θ` times the volume of the unit ball, `n = finrank ℝ E`.

This is the measure-theoretic half of `card_mul_pow_le_of_sphere_separated`. Bounding the
thickening by the ball of radius `1 + θ` instead would give a bound of order `1`, which is
what would degrade the sphere count by one power of `θ`. -/
theorem volume_cthickening_sphere_le (_hn : 1 ≤ Module.finrank ℝ E)
    {θ : ℝ} (hθ_pos : 0 < θ) (hθ_le : θ ≤ 1) :
    volume (Metric.cthickening θ (Metric.sphere (0 : E) 1)) ≤
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * 2 ^ (Module.finrank ℝ E) * θ) *
        volume (Metric.closedBall (0 : E) 1) := by
  set n := Module.finrank ℝ E
  have hsphere_nonempty : (Metric.sphere (0 : E) 1).Nonempty := by
    rw [NormedSpace.sphere_nonempty]
    norm_num
  have h_nonneg_one_plus : 0 ≤ 1 + θ := by linarith
  have h_nonneg_one_minus : 0 ≤ 1 - θ := by nlinarith
  have h_ball_subset : Metric.ball (0 : E) (1 - θ) ⊆ Metric.closedBall (0 : E) (1 + θ) := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm_sub, sub_zero] at hx
    rw [Metric.mem_closedBall, dist_eq_norm_sub, sub_zero]
    linarith
  have h_vol_ball_fin : volume (Metric.ball (0 : E) (1 - θ)) ≠ ⊤ := by
    rw [InnerProductSpace.volume_ball (0 : E) (1 - θ)]
    apply ENNReal.mul_ne_top
    · apply ENNReal.pow_ne_top; simp
    · simp
  have h_vol_unitBall_fin : volume (Metric.closedBall (0 : E) (1 : ℝ)) ≠ ⊤ := by
    rw [InnerProductSpace.volume_closedBall (0 : E) (1 : ℝ)]
    apply ENNReal.mul_ne_top
    · apply ENNReal.pow_ne_top; simp
    · simp
  -- Step 1: containment of the cthickening in the annulus
  have h_cont : Metric.cthickening θ (Metric.sphere (0 : E) 1) ⊆
      Metric.closedBall (0 : E) (1 + θ) \ Metric.ball (0 : E) (1 - θ) := by
    intro y hy
    rw [Metric.mem_cthickening_iff] at hy
    have h_infDist : Metric.infDist y (Metric.sphere (0 : E) 1) ≤ θ := by
      rw [Metric.infDist]
      have h_fin : Metric.infEDist y (Metric.sphere (0 : E) 1) ≠ ⊤ :=
        Metric.infEDist_ne_top hsphere_nonempty
      have h_toReal : ENNReal.toReal (Metric.infEDist y (Metric.sphere (0 : E) 1)) ≤
          ENNReal.toReal (ENNReal.ofReal θ) :=
        ENNReal.toReal_mono (by
        have htop : ENNReal.ofReal θ ≠ ⊤ := ENNReal.ofReal_ne_top (r := θ)
        exact htop) hy
      rw [ENNReal.toReal_ofReal hθ_pos.le] at h_toReal
      exact h_toReal
    have h_abs : |‖y‖ - 1| ≤ θ := by
      have h_bound : |‖y‖ - 1| ≤ Metric.infDist y (Metric.sphere (0 : E) 1) :=
        ((Metric.le_infDist hsphere_nonempty (r := |‖y‖ - 1|)).2 fun z hz => by
          rw [Metric.mem_sphere, dist_eq_norm_sub] at hz
          rw [sub_zero] at hz
          calc
            |‖y‖ - 1| = |‖y‖ - ‖z‖| := by rw [hz]
            _ ≤ ‖y - z‖ := abs_norm_sub_norm_le _ _
            _ = dist y z := by rw [dist_eq_norm_sub])
      exact h_bound.trans h_infDist
    have h_norm_le : ‖y‖ ≤ 1 + θ := by
      have h := abs_le.mp h_abs
      linarith
    have h_norm_ge : ‖y‖ ≥ 1 - θ := by
      have h := abs_le.mp h_abs
      linarith
    have h_mem_closedBall : y ∈ Metric.closedBall (0 : E) (1 + θ) := by
      rw [Metric.mem_closedBall, dist_eq_norm_sub, sub_zero]
      exact h_norm_le
    have h_not_mem_ball : y ∉ Metric.ball (0 : E) (1 - θ) := by
      rw [Metric.mem_ball, dist_eq_norm_sub, sub_zero]
      exact not_lt.mpr h_norm_ge
    exact ⟨h_mem_closedBall, h_not_mem_ball⟩
  -- Step 2: volume of the annulus
  have h_vol_annulus : volume (Metric.closedBall (0 : E) (1 + θ) \ Metric.ball (0 : E) (1 - θ)) =
      volume (Metric.closedBall (0 : E) (1 + θ)) - volume (Metric.ball (0 : E) (1 - θ)) :=
    measure_sdiff h_ball_subset (measurableSet_ball.nullMeasurableSet) h_vol_ball_fin
  have h_vol_closedBall : volume (Metric.closedBall (0 : E) (1 + θ)) =
      (ENNReal.ofReal (1 + θ)) ^ n * volume (Metric.closedBall (0 : E) (1 : ℝ)) := by
    rw [InnerProductSpace.volume_closedBall (0 : E) (1 + θ)]
    congr 1
    rw [InnerProductSpace.volume_closedBall (0 : E) (1 : ℝ)]
    simp [ENNReal.ofReal_one]
  have h_vol_ball : volume (Metric.ball (0 : E) (1 - θ)) =
      (ENNReal.ofReal (1 - θ)) ^ n * volume (Metric.closedBall (0 : E) (1 : ℝ)) := by
    rw [InnerProductSpace.volume_ball (0 : E) (1 - θ)]
    congr 1
    rw [InnerProductSpace.volume_closedBall (0 : E) (1 : ℝ)]
    simp [ENNReal.ofReal_one]
  -- Step 3: compute the difference
  have h_diff : volume (Metric.closedBall (0 : E) (1 + θ)) - volume (Metric.ball (0 : E) (1 - θ)) =
      ENNReal.ofReal ((1 + θ) ^ n - (1 - θ) ^ n) * volume (Metric.closedBall (0 : E) (1 : ℝ)) := by
    rw [h_vol_closedBall, h_vol_ball]
    set a := (ENNReal.ofReal (1 + θ)) ^ n
    set b := (ENNReal.ofReal (1 - θ)) ^ n
    set c := volume (Metric.closedBall (0 : E) (1 : ℝ))
    have h_c_fin : c ≠ ⊤ := h_vol_unitBall_fin
    have h_sub_cond : 0 < b → b < a → c ≠ ⊤ := fun _ _ => h_c_fin
    rw [← ENNReal.sub_mul h_sub_cond]
    congr 1
    calc
      a - b = (ENNReal.ofReal ((1 + θ) ^ n)) - (ENNReal.ofReal ((1 - θ) ^ n)) := by
        simp [a, b, ENNReal.ofReal_pow h_nonneg_one_plus, ENNReal.ofReal_pow h_nonneg_one_minus]
      _ = ENNReal.ofReal ((1 + θ) ^ n - (1 - θ) ^ n) := by
        rw [ENNReal.ofReal_sub ((1 + θ) ^ n) (by positivity : 0 ≤ (1 - θ) ^ n)]
  -- Step 4: combine
  apply le_trans (measure_mono h_cont)
  rw [h_vol_annulus, h_diff]
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal
    (one_add_pow_sub_one_sub_pow_le n hθ_pos.le hθ_le)) (volume (Metric.closedBall (0 : E) 1))

/-- **Separated sets on the unit sphere.** A `θ`-separated finite subset of the unit sphere
of `E` has at most `sphereSeparatedCount.C n * θ ^ (-(n - 1))` elements, where
`n = finrank ℝ E`. The bound is stated multiplicatively to avoid negative exponents.

The proof is the packing bound `packingNumber_mul_pow_le_volume_cthickening` applied to the
unit sphere, together with the fact that its closed `θ`-thickening is contained in the
annulus `1 - θ ≤ ‖y‖ ≤ 1 + θ`, whose volume is linear in `θ` by
`one_add_pow_sub_one_sub_pow_le`. -/
theorem card_mul_pow_le_of_sphere_separated (hn : 2 ≤ Module.finrank ℝ E)
    {θ : ℝ} (hθ_pos : 0 < θ) (hθ_le : θ ≤ 1) {V : Finset E}
    (hV_sphere : ∀ v ∈ V, ‖v‖ = 1)
    (hV_sep : (V : Set E).Pairwise fun v w => θ ≤ dist v w) :
    (V.card : ℝ) * θ ^ (Module.finrank ℝ E - 1) ≤
      sphereSeparatedCount.C (Module.finrank ℝ E) := by
  set n := Module.finrank ℝ E with hn_def
  have hn_pos : 1 ≤ n := by omega
  have hθ_nonneg : 0 ≤ θ := le_of_lt hθ_pos
  -- `V` is a subset of the unit sphere
  have hVsphere_set : (V : Set E) ⊆ Metric.sphere (0 : E) 1 := by
    intro v hv
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact hV_sphere v hv
  -- Open balls of radius θ/2 around points of V are pairwise disjoint
  have hball_disj : (V : Set E).PairwiseDisjoint (fun v => Metric.ball v (θ/2)) := by
    intro v hv w hw hne
    have hθle : θ ≤ dist v w := hV_sep hv hw hne
    exact Metric.ball_disjoint_ball (by nlinarith)
  -- Each such ball is contained in the cthickening
  have hball_sub : ∀ v ∈ V,
      Metric.ball v (θ/2) ⊆ Metric.cthickening θ (Metric.sphere (0 : E) 1) := by
    intro v hv
    have hv_sphere : v ∈ Metric.sphere (0 : E) 1 := hVsphere_set hv
    calc
      Metric.ball v (θ/2) ⊆ Metric.closedBall v (θ/2) := Metric.ball_subset_closedBall
      _ ⊆ Metric.closedBall v θ := by
        intro y hy
        rw [Metric.mem_closedBall] at hy ⊢
        linarith
      _ ⊆ Metric.cthickening θ (Metric.sphere (0 : E) 1) :=
        Metric.closedBall_subset_cthickening hv_sphere θ
  have hmeas : ∀ v ∈ V, MeasurableSet (Metric.ball v (θ/2)) := fun v _ => measurableSet_ball
  set ω := volume (Metric.closedBall (0 : E) 1) with hω_def
  have hω_fin : ω ≠ ⊤ := by
    exact ne_of_lt MeasureTheory.measure_closedBall_lt_top
  have hω_pos : 0 < ω := Metric.measure_closedBall_pos volume (0 : E) (by norm_num : (0 : ℝ) < 1)
  have hω_ne_zero : ω ≠ 0 := by exact ne_of_gt hω_pos
  -- Volume of the ball of radius θ/2, expressed using the volume of the unit ball
  have hvol_ball_eq : volume (Metric.ball (0 : E) (θ/2)) = ENNReal.ofReal ((θ/2) ^ n) * ω := by
    calc
      volume (Metric.ball (0 : E) (θ/2))
          = volume (Metric.closedBall (0 : E) (θ/2)) := by
        rw [MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball]
      _ = (ENNReal.ofReal (θ/2)) ^ n * ENNReal.ofReal
          (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)) := by
        rw [InnerProductSpace.volume_closedBall (0 : E) (θ/2)]
      _ = ENNReal.ofReal ((θ/2) ^ n) * ENNReal.ofReal
          (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)) := by
        rw [ENNReal.ofReal_pow (by positivity : 0 ≤ θ/2)]
      _ = ENNReal.ofReal ((θ/2) ^ n) * volume (Metric.closedBall (0 : E) 1) := by
        rw [InnerProductSpace.volume_closedBall (0 : E) (1 : ℝ), hn_def]
        simp
      _ = ENNReal.ofReal ((θ/2) ^ n) * ω := rfl
  -- Measure inequality in ENNReal
  have hvol_balls_ennreal : (V.card : ENNReal) * volume (Metric.ball (0 : E) (θ/2)) ≤
      volume (Metric.cthickening θ (Metric.sphere (0 : E) 1)) := by
    calc
      (V.card : ENNReal) * volume (Metric.ball (0 : E) (θ/2))
          = (V.card : ℕ) • volume (Metric.ball (0 : E) (θ/2)) := by
        simp [nsmul_eq_mul]
      _ = (∑ v ∈ V, volume (Metric.ball (0 : E) (θ/2))) := by
        simp
      _ = (∑ v ∈ V, volume (Metric.ball v (θ/2))) := by
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [MeasureTheory.Measure.addHaar_ball_center volume v (θ/2)]
      _ = volume (⋃ v ∈ V, Metric.ball v (θ/2)) := by
        rw [MeasureTheory.measure_biUnion_finset hball_disj hmeas]
      _ ≤ volume (Metric.cthickening θ (Metric.sphere (0 : E) 1)) :=
        measure_mono (Set.iUnion₂_subset hball_sub)
  -- The measure-theoretic half: volume of the cthickening is bounded by n * 2^n * θ times ω
  have hvol_cthick_bound : volume (Metric.cthickening θ (Metric.sphere (0 : E) 1)) ≤
      ENNReal.ofReal ((n : ℝ) * 2 ^ n * θ) * ω := by
    -- use the separate lemma, which bounds the volume of the cthickening of the sphere
    have h := volume_cthickening_sphere_le hn_pos hθ_pos hθ_le
    simpa [hω_def] using h
  -- Chain the inequalities and cancel ω
  have h_ineq_ennreal : ((V.card : ENNReal) * ENNReal.ofReal ((θ/2) ^ n)) * ω ≤
      (ENNReal.ofReal ((n : ℝ) * 2 ^ n * θ)) * ω := by
    calc
      ((V.card : ENNReal) * ENNReal.ofReal ((θ/2) ^ n)) * ω
          = (V.card : ENNReal) * (ENNReal.ofReal ((θ/2) ^ n) * ω) := by ring
      _ = (V.card : ENNReal) * volume (Metric.ball (0 : E) (θ/2)) := by rw [hvol_ball_eq]
      _ ≤ volume (Metric.cthickening θ (Metric.sphere (0 : E) 1)) := hvol_balls_ennreal
      _ ≤ ENNReal.ofReal ((n : ℝ) * 2 ^ n * θ) * ω := hvol_cthick_bound
      _ = (ENNReal.ofReal ((n : ℝ) * 2 ^ n * θ)) * ω := by ring
  have h_cancel : (V.card : ENNReal) * ENNReal.ofReal ((θ/2) ^ n) ≤
      ENNReal.ofReal ((n : ℝ) * 2 ^ n * θ) := by
    -- h_ineq_ennreal: ((V.card) * ENNReal.ofReal ((θ/2)^n)) * ω ≤ (ENNReal.ofReal (n*2^n*θ)) * ω
    -- rewrite as ω *... ≤ ω *... and use ENNReal.mul_le_mul_iff_right
    have h_ineq' : ω * ((V.card : ENNReal) * ENNReal.ofReal ((θ/2) ^ n)) ≤
        ω * (ENNReal.ofReal ((n : ℝ) * 2 ^ n * θ)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h_ineq_ennreal
    exact ((ENNReal.mul_le_mul_iff_right hω_ne_zero hω_fin).mp h_ineq')
  -- Convert to ℝ
  have h_real : (V.card : ℝ) * ((θ/2) ^ n) ≤ (n : ℝ) * 2 ^ n * θ := by
    have h_card_fin : (V.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top V.card
    have h_rhs_fin : ENNReal.ofReal ((n : ℝ) * 2 ^ n * θ) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h_cancel_real : ((V.card : ENNReal) * ENNReal.ofReal ((θ/2) ^ n)).toReal ≤
        (ENNReal.ofReal ((n : ℝ) * 2 ^ n * θ)).toReal :=
      ENNReal.toReal_mono h_rhs_fin h_cancel
    have h_pos : 0 ≤ (θ/2) ^ n := by positivity
    have h_pos' : 0 ≤ (n : ℝ) * 2 ^ n * θ := by positivity
    simpa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal h_pos,
      ENNReal.toReal_ofReal h_pos'] using h_cancel_real
  -- Algebra: from (V.card : ℝ) * ((θ/2) ^ n) ≤ (n : ℝ) * 2 ^ n * θ
  -- derive (V.card : ℝ) * θ ^ (n - 1) ≤ n * 2 ^ (2 * n) = sphereSeparatedCount.C n
  have h_theta_pow : (θ/2) ^ n * (2 : ℝ) ^ n = θ ^ n := by
    calc
      (θ/2) ^ n * (2 : ℝ) ^ n = ((θ/2) * (2 : ℝ)) ^ n := by rw [mul_pow]
      _ = θ ^ n := by ring
  have h_two_pow_sq : (2 : ℝ) ^ n * (2 : ℝ) ^ n = (2 : ℝ) ^ (2 * n) := by
    calc
      (2 : ℝ) ^ n * (2 : ℝ) ^ n = (2 : ℝ) ^ (n + n) := by rw [pow_add]
      _ = (2 : ℝ) ^ (2 * n) := by ring
  have h_mul : (V.card : ℝ) * θ ^ n ≤ (n : ℝ) * (2 : ℝ) ^ (2 * n) * θ := by
    calc
      (V.card : ℝ) * θ ^ n = (V.card : ℝ) * ((θ/2) ^ n * (2 : ℝ) ^ n) := by
        rw [h_theta_pow]
      _ = ((V.card : ℝ) * (θ/2) ^ n) * (2 : ℝ) ^ n := by ring
      _ ≤ ((n : ℝ) * 2 ^ n * θ) * (2 : ℝ) ^ n := by
        have h_nonneg : 0 ≤ (2 : ℝ) ^ n := by positivity
        nlinarith
      _ = (n : ℝ) * ((2 : ℝ) ^ n * (2 : ℝ) ^ n) * θ := by ring
      _ = (n : ℝ) * (2 : ℝ) ^ (2 * n) * θ := by rw [h_two_pow_sq]
      _ = ((n : ℝ) * (2 : ℝ) ^ (2 * n)) * θ := by ring
  have h_pow_eq : θ ^ n = θ * θ ^ (n - 1) := by
    calc
      θ ^ n = θ ^ ((n - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      _ = θ ^ (n - 1) * θ := by rw [pow_succ]
      _ = θ * θ ^ (n - 1) := mul_comm _ _
  have h_ineq : (V.card : ℝ) * (θ * θ ^ (n - 1)) ≤ ((n : ℝ) * (2 : ℝ) ^ (2 * n)) * θ := by
    rw [← h_pow_eq]
    exact h_mul
  have h_final : (V.card : ℝ) * θ ^ (n - 1) ≤ (n : ℝ) * (2 : ℝ) ^ (2 * n) := by
    have h_LHS : (V.card : ℝ) * (θ * θ ^ (n - 1)) = (V.card : ℝ) * θ ^ (n - 1) * θ := by ring
    rw [h_LHS] at h_ineq
    -- h_ineq: (V.card : ℝ) * θ ^ (n - 1) * θ ≤ ((n : ℝ) * (2 : ℝ) ^ (2 * n)) * θ
    -- cancel θ > 0
    have h_nonneg : 0 ≤ (V.card : ℝ) * θ ^ (n - 1) := by positivity
    have h_nonneg' : 0 ≤ (n : ℝ) * (2 : ℝ) ^ (2 * n) := by positivity
    nlinarith
  -- match the conclusion
  have h_C : sphereSeparatedCount.C n = (n : ℝ) * (2 : ℝ) ^ (2 * n) := rfl
  rw [h_C]
  exact h_final

/-- **Counting direction classes.** For `0 < ρ ≤ 1` the unit sphere of `E` admits a finite
`ρ`-net whose cardinality obeys the bound of `card_mul_pow_le_of_sphere_separated`.

This is the form in which the sphere count is consumed: it partitions a family of tubes by
the direction class of each tube, with `ρ` of order `δ`, so that in dimension `3` the number
of classes is `O(δ ^ (-2))`. A maximal `ρ`-separated subset of the sphere is such a net,
since maximality forces every unit vector to lie within `ρ` of the net. -/
theorem exists_finset_sphere_net (hn : 2 ≤ Module.finrank ℝ E)
    {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_le : ρ ≤ 1) :
    ∃ Θ : Finset E, (∀ w ∈ Θ, ‖w‖ = 1) ∧
      (Θ.card : ℝ) * ρ ^ (Module.finrank ℝ E - 1) ≤
        sphereSeparatedCount.C (Module.finrank ℝ E) ∧
      ∀ v : E, ‖v‖ = 1 → ∃ w ∈ Θ, dist v w ≤ ρ := by
  let s := Metric.sphere (0 : E) 1
  have hs_bounded : Bornology.IsBounded s := Metric.isBounded_sphere
  let ρ' : NNReal := ⟨ρ, hρ_pos.le⟩
  -- packing number of the sphere is finite
  have hpack : packingNumber ρ' s ≠ ⊤ := by
    by_contra! htop
    have htop' : (packingNumber ρ' s : ENNReal) = ⊤ := by
      simp [htop]
    have hineq := packingNumber_mul_pow_le_volume_cthickening ρ' s
    set C := coveringNumber_mul_pow_le_volume_cthickening.C (Module.finrank ℝ E)
    have hC_ne_zero : (C : ENNReal) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr (coveringNumber_mul_pow_le_volume_cthickening.C_pos _).ne'
    have hρ'_ne_zero : (ρ' : ENNReal) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr (by
        intro hzero_nn
        apply hρ_pos.ne'
        calc
          ρ = (ρ' : ℝ) := rfl
          _ = (0 : ℝ) := congrArg Subtype.val hzero_nn)
    have hLHS : (C : ENNReal) * (packingNumber ρ' s : ENNReal) * (ρ' : ENNReal) ^
        (Module.finrank ℝ E) = ⊤ := by
      rw [htop']
      calc
        (C : ENNReal) * (⊤ : ENNReal) * (ρ' : ENNReal) ^ (Module.finrank ℝ E)
            = (C : ENNReal) * ((⊤ : ENNReal) * (ρ' : ENNReal) ^ (Module.finrank ℝ E)) := by ring
        _ = (C : ENNReal) * ⊤ := by
          rw [ENNReal.top_mul (pow_ne_zero (Module.finrank ℝ E) hρ'_ne_zero)]
        _ = ⊤ := ENNReal.mul_top hC_ne_zero
    have hbounded_cthick : Bornology.IsBounded (cthickening (ρ' : ℝ) s) :=
      hs_bounded.cthickening
    have hvol_fin : volume (cthickening (ρ' : ℝ) s) < ⊤ := hbounded_cthick.measure_lt_top
    rw [hLHS] at hineq
    exact (not_lt.mpr hineq) hvol_fin
  have hcard : (maximalSeparatedSet ρ' s).encard = packingNumber ρ' s :=
    encard_maximalSeparatedSet hpack
  have hfin : (maximalSeparatedSet ρ' s).Finite := by
    rw [← Set.encard_ne_top_iff, hcard]
    exact hpack
  let Θ : Finset E := hfin.toFinset
  have hΘ_mem (x : E) : x ∈ Θ ↔ x ∈ maximalSeparatedSet ρ' s := hfin.mem_toFinset
  have hΘ_sphere : ∀ w ∈ Θ, ‖w‖ = 1 := by
    intro w hw
    have hw' : w ∈ maximalSeparatedSet ρ' s := (hΘ_mem w).mp hw
    have hw_mem_s : w ∈ s := maximalSeparatedSet_subset hw'
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hw_mem_s
    exact hw_mem_s
  have hcover : IsCover ρ' s (maximalSeparatedSet ρ' s) :=
    isCover_maximalSeparatedSet hpack
  have hcover_balls : s ⊆ ⋃ y ∈ maximalSeparatedSet ρ' s, closedBall y ρ' :=
    (isCover_iff_subset_iUnion_closedBall.mp hcover)
  have hcover' : ∀ v : E, ‖v‖ = 1 → ∃ w ∈ Θ, dist v w ≤ ρ := by
    intro v hv
    have hv_mem_s : v ∈ s := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero, hv]
    have hv_union : v ∈ ⋃ y ∈ maximalSeparatedSet ρ' s, closedBall y ρ' :=
      hcover_balls hv_mem_s
    rcases Set.mem_iUnion₂.mp hv_union with ⟨w, hw_mem, hw_ball⟩
    have hw_Θ : w ∈ Θ := (hΘ_mem w).mpr hw_mem
    have hdist_le : dist v w ≤ ρ := by
      have hmem : dist v w ≤ (ρ' : ℝ) := by
        rw [Metric.mem_closedBall] at hw_ball
        simpa [dist_comm] using hw_ball
      calc
        dist v w ≤ (ρ' : ℝ) := hmem
        _ = ρ := rfl
    exact ⟨w, hw_Θ, hdist_le⟩
  have hcard_bound : (Θ.card : ℝ) * ρ ^ (Module.finrank ℝ E - 1) ≤
      sphereSeparatedCount.C (Module.finrank ℝ E) := by
    have hΘ_sep : (Θ : Set E).Pairwise fun v w => ρ ≤ dist v w := by
      intro v hv w hw hne
      have hsep : IsSeparated (ρ' : ENNReal) (maximalSeparatedSet ρ' s : Set E) :=
        isSeparated_maximalSeparatedSet (ε := ρ') (A := s)
      have hv' : v ∈ maximalSeparatedSet ρ' s := (hΘ_mem v).mp hv
      have hw' : w ∈ maximalSeparatedSet ρ' s := (hΘ_mem w).mp hw
      have h_lt : (ρ' : ENNReal) < edist v w := hsep hv' hw' hne
      rw [edist_dist] at h_lt
      -- h_lt : (ρ' : ENNReal) < ENNReal.ofReal (dist v w)
      have hpos_dist : 0 < dist v w := dist_pos.mpr hne
      have h_eq : (ρ' : ENNReal) = ENNReal.ofReal ρ := by
        calc
          (ρ' : ENNReal) = ENNReal.ofReal (ρ' : ℝ) :=
            (ENNReal.ofReal_coe_nnreal (p := ρ')).symm
          _ = ENNReal.ofReal ρ := by
            have : (ρ' : ℝ) = ρ := rfl
            rw [this]
      rw [h_eq] at h_lt
      -- h_lt : ENNReal.ofReal ρ < ENNReal.ofReal (dist v w)
      have h_lt_real : ρ < dist v w :=
        (ENNReal.ofReal_lt_ofReal_iff hpos_dist).mp h_lt
      exact le_of_lt h_lt_real
    have hΘ_sphere' : ∀ v ∈ Θ, ‖v‖ = 1 := hΘ_sphere
    exact card_mul_pow_le_of_sphere_separated hn hρ_pos hρ_le hΘ_sphere' hΘ_sep
  exact ⟨Θ, hΘ_sphere, hcard_bound, hcover'⟩


end Metric
