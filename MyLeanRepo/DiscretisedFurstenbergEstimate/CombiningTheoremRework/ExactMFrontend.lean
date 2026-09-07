module

/-
  Exact-M Quantitative Frontend — THRESHOLD INTERFACE

  Converts metric RegularIncidenceBody input into a dyadic NiceConfiguration
  with exact common cardinality M and even scale n=2m.

  THRESHOLD: ∃ δ_exact > 0, ∀ δ ≤ δ_exact, inputs → output.
  This is necessary because fixed factors (packing constants, fiber bounds,
  common-M losses) must be absorbed into positive powers of δ_n.

  Whiteprint node: exact_m_frontend
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ConstructNiceConfiguration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.Gap1Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.SnapTubeSSetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.GlobalOrientationPartition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.S0RegularityTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.B1_Sublemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DirectionsCoveringBounds
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FiniteSeparationBridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.FrontendHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.FrontendQuantBounds
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.PolynomialAbsorptionThreshold
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.RetainedRegularityClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CleanSquareLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.LocalRegularityTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.SnapFiberBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BallGrowth
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
open DyadicCardToNcover (toAffineLine)

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 500000

noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.SSetBridges (packing_cover_generic)
open DirecretisedFurstenbergEstimate.RegularIncidence hiding Ncover
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.CombiningTheoremRework
open DiscretisedFurstenbergEstimate.Bridge
open DiscretisedFurstenbergEstimate.InductionOnScales
open DyadicCardToNcover

/-- S-set transfer constant for snapping. -/
def K_snap (s : ℝ) : ℝ :=
  11025 * (MainAppendix.affineLine_packing_constant : ℝ)^5 * (70 : ℝ)^s

/-- For a line in standard chart, the chosen direction vector has nonzero x-component. -/
lemma inChart_v0_ne_zero {ℓ : AffineLine} (h : InStandardChart.inChart ℓ) :
    (LemmaE.getDirV ℓ) 0 ≠ 0 := by
  rcases h with ⟨m, b, hm, h_eq⟩
  have h_dir : ℓ.1.direction = Submodule.span ℝ {WithLp.toLp (2 : ENNReal) ![1, m]} := by
    have h1 : (AffineLine.mkSlopeIntercept m b).1.direction =
        Submodule.span ℝ {WithLp.toLp (2 : ENNReal) ![1, m]} := by
      unfold AffineLine.mkSlopeIntercept
      <;> simp [AffineSubspace.direction_mk'] <;> rfl
    rw [←h_eq] <;> exact h1
  have h_v_in : (LemmaE.getDirV ℓ) ∈ ℓ.1.direction := (LemmaE.getDirV_spec ℓ).1
  have h_v_ne : (LemmaE.getDirV ℓ) ≠ 0 := (LemmaE.getDirV_spec ℓ).2
  rw [h_dir] at h_v_in
  have h_exists : ∃ (c : ℝ), (LemmaE.getDirV ℓ) = c • (WithLp.toLp (2 : ENNReal) ![1, m]) := by
    have h' : ∃ (a : ℝ), a • (WithLp.toLp (2 : ENNReal) ![1, m]) = (LemmaE.getDirV ℓ) := by
      simpa [Submodule.mem_span_singleton] using h_v_in
    rcases h' with ⟨a, ha⟩
    exact ⟨a, ha.symm⟩
  rcases h_exists with ⟨c, hc⟩
  have hc_ne : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    exact h_v_ne hc
  have h_comp : (LemmaE.getDirV ℓ) 0 = c := by
    rw [hc] <;> simp <;> ring
  rw [h_comp] <;> exact hc_ne

/-- If ℓ = mkSlopeIntercept m b, then (affineLineSlopeIntercept ℓ).1 = m. -/
lemma slopeIntercept_of_mkSlopeIntercept {m b : ℝ} :
    (affineLineSlopeIntercept (AffineLine.mkSlopeIntercept m b)).1 = m := by
  have hdir : (AffineLine.mkSlopeIntercept m b).1.direction =
      Submodule.span ℝ {WithLp.toLp (2 : ENNReal) ![1, m]} := by
    simp [AffineLine.mkSlopeIntercept, AffineSubspace.direction_mk'] <;> rfl
  have h_v_in : (LemmaE.getDirV (AffineLine.mkSlopeIntercept m b)) ∈
      (AffineLine.mkSlopeIntercept m b).1.direction :=
    (LemmaE.getDirV_spec (AffineLine.mkSlopeIntercept m b)).1
  have h_v_ne : (LemmaE.getDirV (AffineLine.mkSlopeIntercept m b)) ≠ 0 :=
    (LemmaE.getDirV_spec (AffineLine.mkSlopeIntercept m b)).2
  rw [hdir] at h_v_in
  have h_exists : ∃ (c : ℝ),
      (LemmaE.getDirV (AffineLine.mkSlopeIntercept m b)) =
      c • (WithLp.toLp (2 : ENNReal) ![1, m]) := by
    have h' : ∃ (a : ℝ), a • (WithLp.toLp (2 : ENNReal) ![1, m]) =
        (LemmaE.getDirV (AffineLine.mkSlopeIntercept m b)) := by
      simpa [Submodule.mem_span_singleton] using h_v_in
    rcases h' with ⟨a, ha⟩
    exact ⟨a, ha.symm⟩
  rcases h_exists with ⟨c, hc⟩
  have hc_ne : c ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hc; exact h_v_ne hc
  have h_v0 : (LemmaE.getDirV (AffineLine.mkSlopeIntercept m b)) 0 ≠ 0 := by
    have h_comp : (LemmaE.getDirV (AffineLine.mkSlopeIntercept m b)) 0 = c := by
      rw [hc] <;> simp <;> ring
    rw [h_comp] <;> exact hc_ne
  have h_main : (affineLineSlopeIntercept (AffineLine.mkSlopeIntercept m b)).1 = m := by
    rw [affineLineSlopeIntercept_slope h_v0]
    have h1 : (LemmaE.getDirV (AffineLine.mkSlopeIntercept m b)) 1 = c * m := by
      rw [hc] <;> simp <;> ring
    have h2 : (LemmaE.getDirV (AffineLine.mkSlopeIntercept m b)) 0 = c := by
      rw [hc] <;> simp <;> ring
    rw [h1, h2] <;> field_simp [hc_ne] <;> ring
  exact h_main

/-- inChart implies affineLineSlopeIntercept slope bound. -/
lemma inChart_slope_bound {ℓ : AffineLine} (h : InStandardChart.inChart ℓ) :
    |(affineLineSlopeIntercept ℓ).1| ≤ 1 := by
  rcases h with ⟨m, b, hm, h_eq⟩
  have h1 : (affineLineSlopeIntercept ℓ).1 = m := by
    rw [←h_eq]
    exact slopeIntercept_of_mkSlopeIntercept
  rw [h1]
  exact hm

/-- If p is in the unit ball, then ‖S0 p‖ ≤ 3/4. -/
lemma S0_norm_le_three_quarters {p : Plane} (hp : p ∈ Metric.closedBall (0 : Plane) 1) :
    ‖S0 p‖ ≤ 3 / 4 := by
  have h1 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp
  have h2 : S0 p = (1 / 4 : ℝ) • p + quarterVec := S0_apply p
  rw [h2]
  have h3 : ‖(1 / 4 : ℝ) • p + quarterVec‖ ≤ ‖(1 / 4 : ℝ) • p‖ + ‖quarterVec‖ := by exact norm_add_le ((1 / 4) • p) quarterVec
  have h4 : ‖(1 / 4 : ℝ) • p‖ = (1 / 4 : ℝ) * ‖p‖ := by
    rw [norm_smul] <;> norm_num
  have h5 : ‖quarterVec‖ = Real.sqrt 2 / 4 := by
    have h6 : ‖quarterVec‖ = Real.sqrt ((1 / 4 : ℝ)^2 + (1 / 4 : ℝ)^2) := by
      simp [quarterVec, EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring_nf
    rw [h6]
    have h7 : Real.sqrt ((1 / 4 : ℝ)^2 + (1 / 4 : ℝ)^2) = Real.sqrt 2 / 4 := by
      have h8 : (1 / 4 : ℝ)^2 + (1 / 4 : ℝ)^2 = 2 / 16 := by norm_num
      rw [h8]
      have h9 : Real.sqrt (2 / 16) = Real.sqrt 2 / 4 := by
        have h_pos1 : 0 ≤ Real.sqrt (2 / 16) := by positivity
        have h_pos2 : 0 ≤ Real.sqrt 2 / 4 := by positivity
        have h_sq : (Real.sqrt (2 / 16)) ^ 2 = (Real.sqrt 2 / 4) ^ 2 := by
          have h1 : (Real.sqrt (2 / 16)) ^ 2 = 2 / 16 := Real.sq_sqrt (by norm_num)
          have h2 : (Real.sqrt 2 / 4) ^ 2 = 2 / 16 := by
            calc (Real.sqrt 2 / 4) ^ 2
              = (Real.sqrt 2) ^ 2 / 16 := by ring
            _ = 2 / 16 := by rw [Real.sq_sqrt (by norm_num)] <;> ring
          rw [h1, h2]
        nlinarith
      exact h9
    exact h7
  rw [h4, h5] at h3
  have h9 : (1 / 4 : ℝ) * ‖p‖ + Real.sqrt 2 / 4 ≤ 3 / 4 := by
    have h10 : ‖p‖ ≤ 1 := h1
    have h11 : Real.sqrt 2 ≤ 2 := by
      have h12 : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      have h13 : Real.sqrt 4 = 2 := by rw [Real.sqrt_eq_cases] <;> norm_num
      linarith
    linarith
  exact h3.trans h9

/-- If p is in the unit ball, then ‖S0 p‖ ≤ (1+√2)/4. -/
lemma S0_norm_tight {p : Plane} (hp : p ∈ Metric.closedBall (0 : Plane) 1) :
    ‖S0 p‖ ≤ (1 + Real.sqrt 2) / 4 := by
  have h1 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp
  have h2 : S0 p = (1 / 4 : ℝ) • p + quarterVec := S0_apply p
  rw [h2]
  have h3 : ‖(1 / 4 : ℝ) • p + quarterVec‖ ≤ ‖(1 / 4 : ℝ) • p‖ + ‖quarterVec‖ := by exact norm_add_le ((1 / 4) • p) quarterVec
  have h4 : ‖(1 / 4 : ℝ) • p‖ = (1 / 4 : ℝ) * ‖p‖ := by rw [norm_smul] <;> norm_num
  have h5 : ‖quarterVec‖ = Real.sqrt 2 / 4 := by
    have h6 : ‖quarterVec‖ = Real.sqrt ((1 / 4 : ℝ)^2 + (1 / 4 : ℝ)^2) := by
      simp [quarterVec, EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring_nf
    rw [h6]
    have h7 : Real.sqrt ((1 / 4 : ℝ)^2 + (1 / 4 : ℝ)^2) = Real.sqrt 2 / 4 := by
      have h8 : (1 / 4 : ℝ)^2 + (1 / 4 : ℝ)^2 = 2 / 16 := by norm_num
      rw [h8]
      have h9 : Real.sqrt (2 / 16) = Real.sqrt 2 / 4 := by
        have h_pos1 : 0 ≤ Real.sqrt (2 / 16) := by positivity
        have h_pos2 : 0 ≤ Real.sqrt 2 / 4 := by positivity
        have h_sq : (Real.sqrt (2 / 16)) ^ 2 = (Real.sqrt 2 / 4) ^ 2 := by
          have h1 : (Real.sqrt (2 / 16)) ^ 2 = 2 / 16 := Real.sq_sqrt (by norm_num)
          have h2 : (Real.sqrt 2 / 4) ^ 2 = 2 / 16 := by
            calc (Real.sqrt 2 / 4) ^ 2
              = (Real.sqrt 2) ^ 2 / 16 := by ring
            _ = 2 / 16 := by rw [Real.sq_sqrt (by norm_num)] <;> ring
          rw [h1, h2]
        nlinarith
      exact h9
    exact h7
  rw [h4, h5] at h3
  linarith

/-- Diameter of a dyadic square: any two points are at most √2 * δ_n apart. -/
lemma dyadic_square_diam {n : ℕ} {q : DyadicSquare n} {x y : Plane}
    (hx : x ∈ q.toSet) (hy : y ∈ q.toSet) :
    dist x y ≤ Real.sqrt 2 * dyadicDelta n := by
  set δ : ℝ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hx0 : (q.i : ℝ) * δ ≤ x 0 := hx.1
  have hx1 : x 0 < ((q.i : ℝ) + 1) * δ := hx.2.1
  have hx2 : (q.j : ℝ) * δ ≤ x 1 := hx.2.2.1
  have hx3 : x 1 < ((q.j : ℝ) + 1) * δ := hx.2.2.2
  have hy0 : (q.i : ℝ) * δ ≤ y 0 := hy.1
  have hy1 : y 0 < ((q.i : ℝ) + 1) * δ := hy.2.1
  have hy2 : (q.j : ℝ) * δ ≤ y 1 := hy.2.2.1
  have hy3 : y 1 < ((q.j : ℝ) + 1) * δ := hy.2.2.2
  have hdx : |x 0 - y 0| < δ := by
    have h1 : x 0 - y 0 < δ := by linarith
    have h2 : -(δ) < x 0 - y 0 := by linarith
    exact abs_lt.mpr ⟨h2, h1⟩
  have hdy : |x 1 - y 1| < δ := by
    have h1 : x 1 - y 1 < δ := by linarith
    have h2 : -(δ) < x 1 - y 1 := by linarith
    exact abs_lt.mpr ⟨h2, h1⟩
  have h1sq : (x 0 - y 0)^2 < δ^2 := by
    have h3 : |x 0 - y 0| < δ := hdx
    have h4 : (x 0 - y 0)^2 = |x 0 - y 0|^2 := by rw [sq_abs]
    rw [h4]
    have h5 : |x 0 - y 0|^2 < δ^2 := by nlinarith [abs_nonneg (x 0 - y 0)]
    exact h5
  have h2sq : (x 1 - y 1)^2 < δ^2 := by
    have h3 : |x 1 - y 1| < δ := hdy
    have h4 : (x 1 - y 1)^2 = |x 1 - y 1|^2 := by rw [sq_abs]
    rw [h4]
    have h5 : |x 1 - y 1|^2 < δ^2 := by nlinarith [abs_nonneg (x 1 - y 1)]
    exact h5
  have h3sq : (x 0 - y 0)^2 + (x 1 - y 1)^2 < 2 * δ^2 := by linarith
  have h_dist_eq : dist x y = ‖x - y‖ := by rfl
  have h_norm2 : ‖x - y‖ ^ 2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
    have h_pos : 0 ≤ (x 0 - y 0)^2 + (x 1 - y 1)^2 := by positivity
    have h : ‖x - y‖ = Real.sqrt ((x 0 - y 0)^2 + (x 1 - y 1)^2) := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
      <;> simp [sq_abs] <;> ring
    rw [h]
    rw [Real.sq_sqrt h_pos] <;> ring
  have h4 : dist x y ^ 2 < (Real.sqrt 2 * δ)^2 := by
    rw [h_dist_eq, h_norm2]
    have h5 : (Real.sqrt 2 * δ)^2 = 2 * δ^2 := by
      calc (Real.sqrt 2 * δ)^2
        = (Real.sqrt 2)^2 * δ^2 := by ring
      _ = 2 * δ^2 := by rw [Real.sq_sqrt (by norm_num)] <;> ring
    rw [h5]
    exact h3sq
  have h6 : 0 ≤ dist x y := by positivity
  have h7 : 0 ≤ Real.sqrt 2 * δ := by positivity
  nlinarith

/-- Helper: if x, S0 p are in the same dyadic square and ‖p‖ ≤ 1, then ‖x‖ < 1. -/
lemma point_in_square_in_unit_ball {n : ℕ} {q : DyadicSquare n} {x p : Plane}
    (hx : x ∈ q.toSet) (hSp : S0 p ∈ q.toSet) (hp : p ∈ Metric.closedBall (0 : Plane) 1)
    (hδn_le_quart : dyadicDelta n ≤ 1 / 4) : ‖x‖ < 1 := by
  have h1 : ‖S0 p‖ ≤ (1 + Real.sqrt 2) / 4 := S0_norm_tight hp
  have h2 : dist x (S0 p) ≤ Real.sqrt 2 * dyadicDelta n := dyadic_square_diam hx hSp
  have h3 : ‖x‖ ≤ ‖S0 p‖ + ‖x - S0 p‖ := by
    calc ‖x‖ = ‖S0 p + (x - S0 p)‖ := by abel_nf
    _ ≤ ‖S0 p‖ + ‖x - S0 p‖ := norm_add_le _ _
  have h4 : ‖x - S0 p‖ = dist x (S0 p) := by rfl
  have h5 : ‖x‖ ≤ ‖S0 p‖ + dist x (S0 p) := by
    rw [h4] at h3
    exact h3
  have h6 : Real.sqrt 2 * dyadicDelta n ≤ Real.sqrt 2 * (1 / 4 : ℝ) := by
    have h7 : 0 ≤ Real.sqrt 2 := by positivity
    exact mul_le_mul_of_nonneg_left hδn_le_quart h7
  have h8 : ‖x‖ ≤ (1 + Real.sqrt 2) / 4 + Real.sqrt 2 * (1 / 4 : ℝ) := by linarith
  have h9 : (1 + Real.sqrt 2) / 4 + Real.sqrt 2 * (1 / 4 : ℝ) < 1 := by
    have h10 : Real.sqrt 2 < 2 := by
      have h11 : Real.sqrt 2 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h12 : Real.sqrt 4 = 2 := by rw [Real.sqrt_eq_cases] <;> norm_num
      linarith
    have h13 : (1 + Real.sqrt 2) / 4 + Real.sqrt 2 * (1 / 4 : ℝ) = (1 + 2 * Real.sqrt 2) / 4 := by ring
    rw [h13]
    have h14 : Real.sqrt 2 < 3 / 2 := by
      have h15 : (Real.sqrt 2)^2 < (3 / 2 : ℝ)^2 := by
        rw [Real.sq_sqrt (by norm_num)] <;> norm_num
      have h16 : 0 ≤ Real.sqrt 2 := by positivity
      nlinarith
    linarith
  linarith

/-- Helper: square index bounds from point in unit square. -/
lemma square_index_bounds {n : ℕ} {q : DyadicSquare n} {x : Plane}
    (hx : x ∈ q.toSet) (hunit : 0 ≤ x 0 ∧ x 0 < 1 ∧ 0 ≤ x 1 ∧ x 1 < 1) :
    0 ≤ q.i ∧ q.i < (2 ^ n : ℤ) ∧ 0 ≤ q.j ∧ q.j < (2 ^ n : ℤ) := by
  set δ : ℝ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_mul : δ * (2 ^ n : ℝ) = 1 := by
    simp [hδ, dyadicDelta, Real.rpow_neg] <;> field_simp <;> norm_cast
  have h_i1 : (q.i : ℝ) * δ ≤ x 0 := hx.1
  have h_i2 : x 0 < ((q.i : ℝ) + 1) * δ := hx.2.1
  have h_j1 : (q.j : ℝ) * δ ≤ x 1 := hx.2.2.1
  have h_j2 : x 1 < ((q.j : ℝ) + 1) * δ := hx.2.2.2
  have h_qi_nonneg : 0 ≤ q.i := by
    by_contra h
    have h' : q.i < 0 := by linarith
    have h'' : q.i ≤ -1 := by linarith
    have h3 : (q.i : ℝ) + 1 ≤ 0 := by
      have h4 : (q.i : ℝ) ≤ -1 := by exact_mod_cast h''
      linarith
    have h5 : ((q.i : ℝ) + 1) * δ ≤ 0 := by nlinarith
    have h6 : x 0 < 0 := by linarith
    have h7 : 0 ≤ x 0 := hunit.1
    linarith
  have h_qi_lt : q.i < (2 ^ n : ℤ) := by
    have h1 : (q.i : ℝ) * δ < 1 := by linarith [h_i1, hunit.2.1]
    have h2 : (q.i : ℝ) < (2 ^ n : ℝ) := by
      have h3 : (q.i : ℝ) * (δ * (2 ^ n : ℝ)) = (q.i : ℝ) := by
        rw [hδ_mul] <;> ring
      have h4 : (q.i : ℝ) * δ * (2 ^ n : ℝ) = (q.i : ℝ) := by
        ring_nf at h3 ⊢ <;> exact h3
      calc (q.i : ℝ)
        = (q.i : ℝ) * δ * (2 ^ n : ℝ) := h4.symm
      _ < 1 * (2 ^ n : ℝ) := by gcongr
      _ = (2 ^ n : ℝ) := by ring
    exact_mod_cast h2
  have h_qj_nonneg : 0 ≤ q.j := by
    by_contra h
    have h' : q.j < 0 := by linarith
    have h'' : q.j ≤ -1 := by linarith
    have h3 : (q.j : ℝ) + 1 ≤ 0 := by
      have h4 : (q.j : ℝ) ≤ -1 := by exact_mod_cast h''
      linarith
    have h5 : ((q.j : ℝ) + 1) * δ ≤ 0 := by nlinarith
    have h6 : x 1 < 0 := by linarith
    have h7 : 0 ≤ x 1 := hunit.2.2.1
    linarith
  have h_qj_lt : q.j < (2 ^ n : ℤ) := by
    have h1 : (q.j : ℝ) * δ < 1 := by linarith [h_j1, hunit.2.2.2]
    have h2 : (q.j : ℝ) < (2 ^ n : ℝ) := by
      have h3 : (q.j : ℝ) * (δ * (2 ^ n : ℝ)) = (q.j : ℝ) := by
        rw [hδ_mul] <;> ring
      have h4 : (q.j : ℝ) * δ * (2 ^ n : ℝ) = (q.j : ℝ) := by
        ring_nf at h3 ⊢ <;> exact h3
      calc (q.j : ℝ)
        = (q.j : ℝ) * δ * (2 ^ n : ℝ) := h4.symm
      _ < 1 * (2 ^ n : ℝ) := by gcongr
      _ = (2 ^ n : ℝ) := by ring
    exact_mod_cast h2
  exact ⟨h_qi_nonneg, h_qi_lt, h_qj_nonneg, h_qj_lt⟩

/-- Subset S-set transfer for DyadicTubes: if B ⊆ A, |A| < 2|B|, and A is a
    (δ_n, s, C)-S-set, then B is a (δ_n, s, 18*C)-S-set.

    Key: distinct DyadicTubes are δ_n-separated, so |B| ≤ 9 * Ncover(δ_n, B).
    Then Ncover(δ_n, A) ≤ |A| < 2|B| ≤ 18 * Ncover(δ_n, B). -/
lemma dyadic_subset_sset_transfer {n : ℕ} {s C : ℝ}
    {A B : Finset (DyadicTube n)}
    (hB_sub : B ⊆ A)
    (h_card : A.card < 2 * B.card)
    (hA_sset : IsDeltaSSet (dyadicDelta n) s C (A : Set (DyadicTube n))) :
    IsDeltaSSet (dyadicDelta n) s (18 * C) (B : Set (DyadicTube n)) := by
  set δ_n := dyadicDelta n with hδn_def
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  have hB_pos : 0 < B.card := by
    by_contra h
    have h0 : B.card = 0 := by omega
    have h1 : B = ∅ := by simpa [Finset.card_eq_zero] using h0
    rw [h1] at h_card
    exact False.elim (not_lt.mpr (Nat.zero_le A.card) h_card)
  have hB_nonempty : (B : Set (DyadicTube n)).Nonempty := by
    simpa [Finset.nonempty_iff_ne_empty] using hB_pos
  have h_sep : SeparatedAt δ_n (B : Set (DyadicTube n)) := by
    intro T1 hT1 T2 hT2 hne
    have h_dist_eq : dist T1 T2 = T1.dist T2 := by rfl
    rw [h_dist_eq, DyadicTube.dist_eq T1 T2]
    have h_ne_coord : T1.a ≠ T2.a ∨ T1.b ≠ T2.b := by
      by_contra h
      push Not at h
      have h' : T1 = T2 := by exact InductionOnScales.DyadicTube.eq_iff.mpr h
      exact hne h'
    have h_pos : 0 < (|(T1.a - T2.a : ℤ)| : ℝ) + (|(T1.b - T2.b : ℤ)| : ℝ) := by
      rcases h_ne_coord with (h | h)
      · have h' : (T1.a - T2.a : ℤ) ≠ 0 := by omega
        have h'' : 0 < |(T1.a - T2.a : ℤ)| := abs_pos.mpr h'
        have h3 : 0 ≤ (|(T1.b - T2.b : ℤ)| : ℝ) := by positivity
        have h4 : (0 : ℝ) < (|(T1.a - T2.a : ℤ)| : ℝ) := by exact_mod_cast h''
        exact add_pos_of_pos_of_nonneg h4 h3
      · have h' : (T1.b - T2.b : ℤ) ≠ 0 := by omega
        have h'' : 0 < |(T1.b - T2.b : ℤ)| := abs_pos.mpr h'
        have h3 : 0 ≤ (|(T1.a - T2.a : ℤ)| : ℝ) := by positivity
        have h4 : (0 : ℝ) < (|(T1.b - T2.b : ℤ)| : ℝ) := by exact_mod_cast h''
        exact add_pos_of_nonneg_of_pos h3 h4
    have h9 : (1 : ℝ) ≤ (|(T1.a - T2.a : ℤ)| : ℝ) + (|(T1.b - T2.b : ℤ)| : ℝ) := by
      exact_mod_cast h_pos
    have h_ge : δ_n * ((|(T1.a - T2.a : ℤ)| : ℝ) + (|(T1.b - T2.b : ℤ)| : ℝ)) ≥ δ_n := by
      nlinarith
    exact h_ge
  have h_pack : (B.card : ENNReal) ≤ (9 : ENNReal) * Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n)) :=
      DirecretisedFurstenbergEstimate.SSetBridges.packing_cover_generic
      (hδ_pos := hδn_pos) (hsep := h_sep) (hK_pos := by norm_num)
      (fun x => max_points_in_delta_ball_DyadicTube hδn_pos B h_sep x)
  have h1 : (Metric.externalCoveringNumber δ_n.toNNReal (A : Set (DyadicTube n)) : ENNReal) ≤
      (A.card : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_le_encard_self (A : Set (DyadicTube n))
  have h2 : (A.card : ENNReal) < 2 * (B.card : ENNReal) := by
    exact_mod_cast h_card
  have h3 : (Metric.externalCoveringNumber δ_n.toNNReal (A : Set (DyadicTube n)) : ENNReal) ≤
      (18 : ENNReal) * Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n)) := by
    calc (Metric.externalCoveringNumber δ_n.toNNReal (A : Set (DyadicTube n)) : ENNReal)
      ≤ (A.card : ENNReal) := h1
    _ ≤ 2 * (B.card : ENNReal) := le_of_lt h2
    _ ≤ 2 * ((9 : ENNReal) * Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n))) := by gcongr
    _ = (18 : ENNReal) * Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n)) := by ring
  rcases hA_sset with ⟨hne_A, hδ, hC_pos, hs, hmain⟩
  have hC18_pos : 0 < 18 * C := by positivity
  refine ⟨hB_nonempty, hδ, hC18_pos, hs, fun x r hr => ?_⟩
  have h4 : (Metric.externalCoveringNumber δ_n.toNNReal ((B : Set (DyadicTube n)) ∩ Metric.closedBall x r) : ENNReal) ≤
      Metric.externalCoveringNumber δ_n.toNNReal ((A : Set (DyadicTube n)) ∩ Metric.closedBall x r) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set (show (B : Set (DyadicTube n)) ∩ Metric.closedBall x r ⊆ (A : Set (DyadicTube n)) ∩ Metric.closedBall x r from by gcongr)
  have h5 := hmain x r hr
  calc (Metric.externalCoveringNumber δ_n.toNNReal ((B : Set (DyadicTube n)) ∩ Metric.closedBall x r) : ENNReal)
    ≤ Metric.externalCoveringNumber δ_n.toNNReal ((A : Set (DyadicTube n)) ∩ Metric.closedBall x r) := h4
  _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        Metric.externalCoveringNumber δ_n.toNNReal (A : Set (DyadicTube n)) := h5
  _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        ((18 : ENNReal) * Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n))) := by gcongr
  _ = ENNReal.ofReal (18 * C) * (ENNReal.ofReal r) ^ s *
        Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n)) := by
    let a : ENNReal := ENNReal.ofReal C
    let b : ENNReal := (ENNReal.ofReal r) ^ s
    let c_enc := Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n))
    let c : ENNReal := ↑c_enc
    have h_mul : a * b * ((18 : ENNReal) * c) = (18 : ENNReal) * a * b * c := by
      have h1 : a * b * ((18 : ENNReal) * c) = (18 : ENNReal) * (a * b * c) := by
        calc a * b * ((18 : ENNReal) * c)
          = (a * b) * ((18 : ENNReal) * c) := by rfl
        _ = ((18 : ENNReal) * c) * (a * b) := by exact mul_comm (a * b) ((18 : ENNReal) * c)
        _ = (18 : ENNReal) * (c * (a * b)) := by rw [mul_assoc]
        _ = (18 : ENNReal) * ((a * b) * c) := by rw [mul_comm c (a * b)]
        _ = (18 : ENNReal) * (a * b * c) := by rw [mul_assoc a b]
      rw [h1] <;> simp only [mul_assoc]
    have h6 : (18 : ENNReal) * a = ENNReal.ofReal (18 * C) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18)] <;> norm_cast
    have h_final : a * b * ((18 : ENNReal) * c) = ENNReal.ofReal (18 * C) * b * c := by
      rw [h_mul, h6] <;> simp only [mul_assoc]
    exact h_final

/-- Fiber bound constant for snapToTubeThroughPoint. -/
def snapThroughFiberM : ℕ := 260000

/-- Slope closeness: if |m| ≤ 1, then |m - T.slope| ≤ δ_n. -/
lemma snapToTubeThroughPoint_slope_closeness {n : ℕ} {ℓ : AffineLine} {p : Plane}
    (h_m : |(affineLineSlopeIntercept ℓ).1| ≤ 1) :
    |(affineLineSlopeIntercept ℓ).1 - (snapToTubeThroughPoint n ℓ p).slope| ≤ dyadicDelta n := by
  set δ : ℝ := dyadicDelta n with hδ
  let m : ℝ := (affineLineSlopeIntercept ℓ).1
  let a_raw : ℤ := roundInt (m / δ)
  let a : ℤ := min a_raw ((2 ^ n : ℤ) - 1)
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_def : δ = 1 / (2 ^ n : ℝ) := by exact Eq.symm (Real.ext_cauchy rfl)
  have hδ_eq : (2 ^ n : ℝ) * δ = 1 := by
    rw [mul_comm, hδ_def]
    field_simp <;> ring
  have hT_a : (snapToTubeThroughPoint n ℓ p).a = a := by rfl
  have hT_slope : (snapToTubeThroughPoint n ℓ p).slope = (a : ℝ) * δ := by
    have h2 : (snapToTubeThroughPoint n ℓ p).slope =
        ((snapToTubeThroughPoint n ℓ p).a : ℝ) * dyadicDelta n := by
      simp [DyadicTube.slope]
    rw [h2, hT_a, hδ] <;> ring
  rw [hT_slope]
  by_cases h_clamp : a_raw ≥ (2 ^ n : ℤ) - 1
  · have ha : a = (2 ^ n : ℤ) - 1 := by
      simp [a, h_clamp] <;> omega
    rw [ha]
    have h1 : m / δ ≥ (2 ^ n : ℝ) - 3 / 2 := by
      have h2 : (a_raw : ℝ) ≥ ((2 ^ n : ℝ) - 1) := by exact_mod_cast h_clamp
      have h3 : (roundInt (m / δ) : ℝ) - 1 / 2 ≤ m / δ := by
        have h4 := roundInt_abs_error (m / δ)
        rw [abs_le] at h4 <;> linarith
      linarith
    have h4 : m ≥ 1 - 3 / 2 * δ := by
      have h5 : m ≥ δ * ((2 ^ n : ℝ) - 3 / 2) := by
        calc m = δ * (m / δ) := by field_simp [hδ_pos.ne'] <;> ring
             _ ≥ δ * ((2 ^ n : ℝ) - 3 / 2) := by gcongr
      have h6 : δ * ((2 ^ n : ℝ) - 3 / 2) = (2 ^ n : ℝ) * δ - δ * (3 / 2) := by ring
      rw [h6] at h5
      rw [hδ_eq] at h5
      linarith
    have h7 : m ≤ 1 := by linarith [abs_le.mp h_m]
    have h8 : (((2 ^ n : ℤ) - 1 : ℝ)) * δ = 1 - δ := by
      have h81 : ((2 ^ n : ℤ) - 1 : ℝ) = (2 ^ n : ℝ) - 1 := by
        simp <;> norm_cast <;> omega
      rw [h81]
      linarith [hδ_eq]
    have h_goal : |m - (((2 ^ n : ℤ) - 1 : ℝ)) * δ| ≤ δ := by
      rw [h8]
      rw [abs_le] <;> constructor <;> linarith
    simpa using h_goal
  · have h_raw : a_raw < (2 ^ n : ℤ) - 1 := by omega
    have ha : a = a_raw := by
      simp [a, h_raw] <;> omega
    rw [ha]
    have h1 : |(a_raw : ℝ) - m / δ| ≤ 1 / 2 := roundInt_abs_error (m / δ)
    have h2 : |(a_raw : ℝ) * δ - m| ≤ δ / 2 := by
      have h3 : (a_raw : ℝ) * δ - m = δ * ((a_raw : ℝ) - m / δ) := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [h3]
      have h4 : |δ * ((a_raw : ℝ) - m / δ)| = δ * |(a_raw : ℝ) - m / δ| := by
        rw [abs_mul, abs_of_pos hδ_pos]
      rw [h4]
      have h5 : δ * |(a_raw : ℝ) - m / δ| ≤ δ * (1 / 2) :=
        mul_le_mul_of_nonneg_left h1 hδ_pos.le
      have h6 : δ * (1 / 2) = δ / 2 := by ring
      rw [h6] at h5
      exact h5
    have h7 : |m - (a_raw : ℝ) * δ| = |(a_raw : ℝ) * δ - m| := by rw [abs_sub_comm]
    rw [h7]
    have h8 : δ / 2 ≤ δ := by linarith
    exact h2.trans h8

/-- Intercept bound for lines near p with |m| ≤ 1 and ‖p‖ ≤ 1. -/
lemma snapToTubeThroughPoint_c_bound {n : ℕ} {δ : ℝ} {ℓ : AffineLine} {p : Plane}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (h_v0 : (LemmaE.getDirV ℓ) 0 ≠ 0)
    (h_slope : |(affineLineSlopeIntercept ℓ).1| ≤ 1)
    (h_near : p ∈ Metric.cthickening δ ℓ.1)
    (hp_ball : p ∈ Metric.closedBall (0 : Plane) 1) :
    |(affineLineSlopeIntercept ℓ).2| ≤ 6 := by
  have hp_norm : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp_ball
  have hp_norm2 : ‖p‖ ≤ 2 := by linarith
  exact regular_slope_c_bound hδ_pos hδ_le_one h_v0 h_slope h_near hp_norm2

/-- Slope diameter: two lines in the same snap fiber have |m1-m2| ≤ 2*δ_n. -/
lemma snapToTubeThroughPoint_slope_diam {n : ℕ} {ℓ1 ℓ2 : AffineLine} {p : Plane} {T : DyadicTube n}
    (h_slope1 : |(affineLineSlopeIntercept ℓ1).1| ≤ 1)
    (h_slope2 : |(affineLineSlopeIntercept ℓ2).1| ≤ 1)
    (h_same1 : snapToTubeThroughPoint n ℓ1 p = T)
    (h_same2 : snapToTubeThroughPoint n ℓ2 p = T) :
    |(affineLineSlopeIntercept ℓ1).1 - (affineLineSlopeIntercept ℓ2).1| ≤ 2 * dyadicDelta n := by
  set δ_n := dyadicDelta n with hδn
  have h1 : |(affineLineSlopeIntercept ℓ1).1 - (snapToTubeThroughPoint n ℓ1 p).slope| ≤ δ_n :=
    snapToTubeThroughPoint_slope_closeness (n := n) (ℓ := ℓ1) (p := p) h_slope1
  have h2 : |(affineLineSlopeIntercept ℓ2).1 - (snapToTubeThroughPoint n ℓ2 p).slope| ≤ δ_n :=
    snapToTubeThroughPoint_slope_closeness (n := n) (ℓ := ℓ2) (p := p) h_slope2
  rw [h_same1] at h1
  rw [h_same2] at h2
  have h3 : |T.slope - (affineLineSlopeIntercept ℓ2).1| = |(affineLineSlopeIntercept ℓ2).1 - T.slope| := by
    rw [abs_sub_comm]
  calc |(affineLineSlopeIntercept ℓ1).1 - (affineLineSlopeIntercept ℓ2).1|
    = |((affineLineSlopeIntercept ℓ1).1 - T.slope) + (T.slope - (affineLineSlopeIntercept ℓ2).1)| := by ring_nf
  _ ≤ |(affineLineSlopeIntercept ℓ1).1 - T.slope| + |T.slope - (affineLineSlopeIntercept ℓ2).1| := by exact real_abs_add ((affineLineSlopeIntercept ℓ1).1 - T.slope) (T.slope - (affineLineSlopeIntercept ℓ2).1)
  _ = |(affineLineSlopeIntercept ℓ1).1 - T.slope| + |(affineLineSlopeIntercept ℓ2).1 - T.slope| := by rw [h3]
  _ ≤ 2 * δ_n := by linarith

/-- Intercept diameter: two lines in same snap fiber near p have |c1-c2| ≤ 4δ + 2δ_n. -/
lemma snapToTubeThroughPoint_intercept_diam {n : ℕ} {δ : ℝ} {ℓ1 ℓ2 : AffineLine} {p : Plane} {T : DyadicTube n}
    (hδ_pos : 0 < δ)
    (h_v01 : (LemmaE.getDirV ℓ1) 0 ≠ 0)
    (h_v02 : (LemmaE.getDirV ℓ2) 0 ≠ 0)
    (h_slope1 : |(affineLineSlopeIntercept ℓ1).1| ≤ 1)
    (h_slope2 : |(affineLineSlopeIntercept ℓ2).1| ≤ 1)
    (h_near1 : p ∈ Metric.cthickening δ ℓ1.1)
    (h_near2 : p ∈ Metric.cthickening δ ℓ2.1)
    (hp_ball : p ∈ Metric.closedBall (0 : Plane) 1)
    (h_same1 : snapToTubeThroughPoint n ℓ1 p = T)
    (h_same2 : snapToTubeThroughPoint n ℓ2 p = T) :
    |(affineLineSlopeIntercept ℓ1).2 - (affineLineSlopeIntercept ℓ2).2| ≤ 4 * δ + 2 * dyadicDelta n := by
  set m1 := (affineLineSlopeIntercept ℓ1).1 with hm1
  set m2 := (affineLineSlopeIntercept ℓ2).1 with hm2
  set δ_n := dyadicDelta n with hδn
  have hp_norm : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp_ball
  have hp_norm2 : ‖p‖ ≤ 2 := by linarith
  have h_m_diff : |m1 - m2| ≤ 2 * δ_n := by
    have h := snapToTubeThroughPoint_slope_diam h_slope1 h_slope2 h_same1 h_same2
    simpa [hm1, hm2, hδn] using h
  have h : |(affineLineSlopeIntercept ℓ1).2 - (affineLineSlopeIntercept ℓ2).2| ≤
      4 * δ + |m1 - m2| * ‖p‖ :=
    regular_slope_intercept_diff_bound hδ_pos h_v01 h_v02 h_slope1 h_slope2 h_near1 h_near2 hp_norm2
  have h9 : |m1 - m2| * ‖p‖ ≤ 2 * δ_n := by
    have h10 : |m1 - m2| ≤ 2 * δ_n := h_m_diff
    have h11 : ‖p‖ ≤ 1 := hp_norm
    have h12 : 0 ≤ 2 * δ_n := by
      have h13 : 0 < δ_n := by simpa [hδn] using dyadicDelta_pos n
      linarith
    calc |m1 - m2| * ‖p‖ ≤ (2 * δ_n) * ‖p‖ := by gcongr
         _ ≤ (2 * δ_n) * 1 := by gcongr
         _ = 2 * δ_n := by ring
  linarith

/-- Fiber bound for snapToTubeThroughPoint: a δ'-separated family near p at scale δ
    has fibers of size at most snapThroughFiberM. -/
lemma snapToTubeThroughPoint_fiber_bound {n : ℕ} {δ δ' : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hδ'_pos : 0 < δ') (hδ'_eq : δ' = δ / 4)
    (hδn_leδ' : dyadicDelta n ≤ δ')
    (p : Plane) (hp_ball : p ∈ Metric.closedBall (0 : Plane) 1)
    (S : Finset AffineLine)
    (h_sep : SeparatedAt δ' (S : Set AffineLine))
    (h_slope : ∀ ℓ ∈ S, |(affineLineSlopeIntercept ℓ).1| ≤ 1)
    (h_v0 : ∀ ℓ ∈ S, (LemmaE.getDirV ℓ) 0 ≠ 0)
    (h_near : ∀ ℓ ∈ S, p ∈ Metric.cthickening δ ℓ.1) :
    ∀ (T : DyadicTube n),
      (S.filter (fun ℓ => snapToTubeThroughPoint n ℓ p = T)).card ≤ snapThroughFiberM := by
  let δ_n : ℝ := dyadicDelta n
  let cell_size : ℝ := δ' / 65
  have h_cell_pos : 0 < cell_size := by positivity
  have hδ : δ = 4 * δ' := by linarith [hδ'_eq]
  intro T
  let F : Finset AffineLine := S.filter (fun ℓ => snapToTubeThroughPoint n ℓ p = T)
  have hF_sub : F ⊆ S := Finset.filter_subset _ _
  have h_sep_F : SeparatedAt δ' (F : Set AffineLine) :=
    h_sep.mono (Finset.coe_subset.mpr hF_sub)
  have h_slope_F : ∀ ℓ ∈ F, |(affineLineSlopeIntercept ℓ).1| ≤ 1 :=
    fun ℓ hℓ => h_slope ℓ (hF_sub hℓ)
  have h_v0_F : ∀ ℓ ∈ F, (LemmaE.getDirV ℓ) 0 ≠ 0 :=
    fun ℓ hℓ => h_v0 ℓ (hF_sub hℓ)
  have h_near_F : ∀ ℓ ∈ F, p ∈ Metric.cthickening δ ℓ.1 :=
    fun ℓ hℓ => h_near ℓ (hF_sub hℓ)
  have h_c_bound : ∀ ℓ ∈ F, |(affineLineSlopeIntercept ℓ).2| ≤ 6 := by
    intro ℓ hℓ
    exact snapToTubeThroughPoint_c_bound (n := n) hδ_pos hδ_le_one
      (h_v0_F ℓ hℓ) (h_slope_F ℓ hℓ) (h_near_F ℓ hℓ) hp_ball
  let M_set : Finset ℝ := F.image (fun ℓ => (affineLineSlopeIntercept ℓ).1)
  let C_set : Finset ℝ := F.image (fun ℓ => (affineLineSlopeIntercept ℓ).2)
  have h_m_diam : ∀ m1 ∈ M_set, ∀ m2 ∈ M_set, |m1 - m2| ≤ (130 : ℝ) * cell_size := by
    intro m1 hm1 m2 hm2
    rcases Finset.mem_image.mp hm1 with ⟨ℓ1, hℓ1, rfl⟩
    rcases Finset.mem_image.mp hm2 with ⟨ℓ2, hℓ2, rfl⟩
    have h_same1 : snapToTubeThroughPoint n ℓ1 p = T := by
      simp only [F, Finset.mem_filter] at hℓ1; exact hℓ1.2
    have h_same2 : snapToTubeThroughPoint n ℓ2 p = T := by
      simp only [F, Finset.mem_filter] at hℓ2; exact hℓ2.2
    have h3 : |(affineLineSlopeIntercept ℓ1).1 - (affineLineSlopeIntercept ℓ2).1| ≤ 2 * δ_n :=
      snapToTubeThroughPoint_slope_diam (h_slope_F ℓ1 hℓ1) (h_slope_F ℓ2 hℓ2) h_same1 h_same2
    have h4 : 2 * δ_n ≤ (130 : ℝ) * cell_size := by
      have h5 : δ_n ≤ δ' := hδn_leδ'
      have h6 : (130 : ℝ) * cell_size = 2 * δ' := by
        simp [cell_size] <;> ring
      rw [h6]; linarith
    linarith
  have h_c_diam : ∀ c1 ∈ C_set, ∀ c2 ∈ C_set, |c1 - c2| ≤ (1170 : ℝ) * cell_size := by
    intro c1 hc1 c2 hc2
    rcases Finset.mem_image.mp hc1 with ⟨ℓ1, hℓ1, rfl⟩
    rcases Finset.mem_image.mp hc2 with ⟨ℓ2, hℓ2, rfl⟩
    have h_same1 : snapToTubeThroughPoint n ℓ1 p = T := by
      simp only [F, Finset.mem_filter] at hℓ1; exact hℓ1.2
    have h_same2 : snapToTubeThroughPoint n ℓ2 p = T := by
      simp only [F, Finset.mem_filter] at hℓ2; exact hℓ2.2
    have h6 : |(affineLineSlopeIntercept ℓ1).2 - (affineLineSlopeIntercept ℓ2).2| ≤ 4 * δ + 2 * δ_n :=
      snapToTubeThroughPoint_intercept_diam hδ_pos
        (h_v0_F ℓ1 hℓ1) (h_v0_F ℓ2 hℓ2)
        (h_slope_F ℓ1 hℓ1) (h_slope_F ℓ2 hℓ2)
        (h_near_F ℓ1 hℓ1) (h_near_F ℓ2 hℓ2) hp_ball h_same1 h_same2
    have h7 : 4 * δ + 2 * δ_n ≤ (1170 : ℝ) * cell_size := by
      have h8 : δ = 4 * δ' := hδ
      have h9 : δ_n ≤ δ' := hδn_leδ'
      have h10 : (1170 : ℝ) * cell_size = 18 * δ' := by
        simp [cell_size] <;> ring
      rw [h10, h8] <;> linarith
    linarith
  by_cases hF_empty : F = ∅
  · have h_goal : (S.filter (fun ℓ => snapToTubeThroughPoint n ℓ p = T)).card ≤ snapThroughFiberM := by
      have hF_eq : S.filter (fun ℓ => snapToTubeThroughPoint n ℓ p = T) = ∅ := by
        exact hF_empty
      rw [hF_eq]
      <;> simp [snapThroughFiberM] <;> decide
    exact h_goal
  · have hF_ne : F.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty] <;> exact hF_empty
    let gridM_img := M_set.image (fun m => Int.floor (m / cell_size))
    let gridC_img := C_set.image (fun c => Int.floor (c / cell_size))
    have h_gridM_card : gridM_img.card ≤ 130 + 2 :=
      floor_image_card_of_diam h_cell_pos (by norm_num) (Finset.Nonempty.image hF_ne _) h_m_diam
    have h_gridC_card : gridC_img.card ≤ 1170 + 2 :=
      floor_image_card_of_diam h_cell_pos (by norm_num) (Finset.Nonempty.image hF_ne _) h_c_diam
    have h_inj : Set.InjOn (fun ℓ : AffineLine =>
        (Int.floor ((affineLineSlopeIntercept ℓ).1 / cell_size),
         Int.floor ((affineLineSlopeIntercept ℓ).2 / cell_size))) (F : Set AffineLine) := by
      intro ℓ1 hℓ1 ℓ2 hℓ2 h_eq
      by_cases hne : ℓ1 ≠ ℓ2
      · set m1 := (affineLineSlopeIntercept ℓ1).1 with hm1
        set c1 := (affineLineSlopeIntercept ℓ1).2 with hc1
        set m2 := (affineLineSlopeIntercept ℓ2).1 with hm2
        set c2 := (affineLineSlopeIntercept ℓ2).2 with hc2
        have hgm : Int.floor (m1 / cell_size) = Int.floor (m2 / cell_size) := by exact congr_arg Prod.fst h_eq
        have hgc : Int.floor (c1 / cell_size) = Int.floor (c2 / cell_size) := by exact congr_arg Prod.snd h_eq
        have hdm : |m1 - m2| < cell_size := same_cell_abs_lt_gen h_cell_pos hgm
        have hdc : |c1 - c2| < cell_size := same_cell_abs_lt_gen h_cell_pos hgc
        have h_dist : AffineLine.dist ℓ1 ℓ2 ≤ 32 * (|m1 - m2| + |c1 - c2|) :=
          regular_slope_dist_lipschitz ℓ1 ℓ2
            (h_v0_F ℓ1 hℓ1) (h_v0_F ℓ2 hℓ2)
            (h_slope_F ℓ1 hℓ1) (h_slope_F ℓ2 hℓ2)
            (h_c_bound ℓ1 hℓ1) (h_c_bound ℓ2 hℓ2)
        have h_sum : |m1 - m2| + |c1 - c2| < 2 * cell_size := by
          have h1 : |m1 - m2| < cell_size := hdm
          have h2 : |c1 - c2| < cell_size := hdc
          linarith
        have h9 : 32 * (|m1 - m2| + |c1 - c2|) < 64 * cell_size := by
          have h10 : 32 * (|m1 - m2| + |c1 - c2|) < 32 * (2 * cell_size) := by
            exact mul_lt_mul_of_pos_left h_sum (by norm_num)
          have h11 : 32 * (2 * cell_size) = 64 * cell_size := by ring
          rw [h11] at h10
          exact h10
        have h10 : 64 * cell_size < δ' := by
          simp [cell_size] <;> linarith
        have h11 : AffineLine.dist ℓ1 ℓ2 < δ' := by linarith
        have h12 : δ' ≤ AffineLine.dist ℓ1 ℓ2 := h_sep_F hℓ1 hℓ2 hne
        linarith
      · simpa using hne
    let Im : Finset (ℤ × ℤ) := F.image (fun ℓ =>
        (Int.floor ((affineLineSlopeIntercept ℓ).1 / cell_size),
         Int.floor ((affineLineSlopeIntercept ℓ).2 / cell_size)))
    have h_card_F : F.card = Im.card := by
      rw [Finset.card_image_of_injOn h_inj]
    have h_Im_product : Im ⊆ gridM_img ×ˢ gridC_img := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨ℓ, hℓ, rfl⟩
      have hm : (affineLineSlopeIntercept ℓ).1 ∈ M_set := Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩
      have hc : (affineLineSlopeIntercept ℓ).2 ∈ C_set := Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩
      exact Finset.mem_product.mpr ⟨
        Finset.mem_image.mpr ⟨_, hm, rfl⟩,
        Finset.mem_image.mpr ⟨_, hc, rfl⟩⟩
    have h_final : F.card ≤ gridM_img.card * gridC_img.card := by
      calc F.card = Im.card := h_card_F
           _ ≤ (gridM_img ×ˢ gridC_img).card := Finset.card_le_card h_Im_product
           _ = gridM_img.card * gridC_img.card := Finset.card_product _ _
    have h_goal : F.card ≤ snapThroughFiberM := by
      calc F.card ≤ gridM_img.card * gridC_img.card := h_final
           _ ≤ (130 + 2) * (1170 + 2) := by gcongr <;> linarith
           _ ≤ snapThroughFiberM := by norm_num [snapThroughFiberM]
    exact h_goal

/-- Helper: for K > 0 and α > 0, ∃ δ₀ > 0 such that ∀ 0 < δ ≤ δ₀, K ≤ δ^{-α}. -/
lemma exists_delta_power_bound (K : ℝ) (hK_pos : 0 < K) (α : ℝ) (hα_pos : 0 < α) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ → K ≤ δ^(-α) := by
  let δ₀ : ℝ := K^(-1/α)
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_le => ?_⟩
  have h1 : δ ≤ K^(-1/α) := hδ_le
  have h2 : δ^(-α) ≥ (K^(-1/α))^(-α) := by
    have h3 : -α < 0 := by linarith
    have h4 : 0 < δ := hδ_pos
    have h5 : 0 < K^(-1/α) := by positivity
    have h6 : δ ≤ K^(-1/α) := h1
    have h7 : (K^(-1/α))^(-α) ≤ δ^(-α) := by
      exact (Real.rpow_le_rpow_iff_of_neg hδ₀_pos hδ_pos h3).mpr hδ_le
    exact h7
  have h8 : (K^(-1/α))^(-α) = K := by
    have h9 : ((-1/α) * (-α)) = 1 := by field_simp [hα_pos.ne']
    rw [← Real.rpow_mul (by positivity)]
    <;> rw [h9] <;> simp
  rw [h8] at h2
  exact h2

/-- Local common-M pigeonhole: dyadic band selection with retention 1/(K+1). -/
lemma common_m_pigeonhole_local
    {Y α : Type*} [DecidableEq Y] [DecidableEq α]
    (P_fin : Finset Y) (F : Y → Finset α) (m_min K : ℕ)
    (hP_nonempty : P_fin.Nonempty)
    (h_lower : ∀ p ∈ P_fin, m_min ≤ (F p).card)
    (h_upper : ∀ p ∈ P_fin, (F p).card ≤ 2^K)
    (h_nonempty : ∀ p ∈ P_fin, (F p).Nonempty) :
    ∃ (P'' : Finset Y) (M : ℕ) (F' : Y → Finset α),
      P'' ⊆ P_fin ∧
      (P''.card : ℝ) ≥ (P_fin.card : ℝ) / (K + 1 : ℝ) ∧
      P''.Nonempty ∧ 0 < M ∧
      (∀ p ∈ P'', (F' p).card = M) ∧
      (∀ p ∈ P'', F' p ⊆ F p) ∧
      (∀ p ∈ P'', (F p).card < 2 * M) ∧
      (M : ℝ) ≥ (m_min : ℝ) / 2 := by
  let w : Y → ℝ := fun _ => 1
  have hw_nonneg : ∀ p ∈ P_fin, 0 ≤ w p := by intro _ _; norm_num
  have h_main := DiscretisedFurstenbergEstimate.InductionOnScales.weighted_uniformize_cardinalities
    P_fin F w K h_upper h_nonempty hw_nonneg
  rcases h_main with ⟨k, P'', M, F', hk_le, hM_eq, hP''sub, h_weight, h_trim⟩
  have hM_pos : 0 < M := by rw [hM_eq] <;> positivity
  have h_card_retention : (P''.card : ℝ) ≥ (P_fin.card : ℝ) / (K + 1 : ℝ) := by
    simpa [w, Finset.sum_const] using h_weight
  have hP''nonempty : P''.Nonempty := by
    have h1 : 0 < (P_fin.card : ℝ) := by exact_mod_cast hP_nonempty.card_pos
    have h2 : 0 < (P_fin.card : ℝ) / (K + 1 : ℝ) := by positivity
    have h3 : 0 < (P''.card : ℝ) := by linarith
    exact Finset.card_pos.mp (by exact_mod_cast h3)
  have h_size : ∀ p ∈ P'', (F' p).card = M := by
    intro p hp; exact (h_trim p hp).2.1
  have h_subset : ∀ p ∈ P'', F' p ⊆ F p := by
    intro p hp; exact (h_trim p hp).1
  have h_upper_band : ∀ p ∈ P'', (F p).card < 2 * M := by
    intro p hp
    exact (h_trim p hp).2.2.2
  have hM_lower : (M : ℝ) ≥ (m_min : ℝ) / 2 := by
    rcases hP''nonempty with ⟨p, hp⟩
    have h1 : M ≤ (F p).card := (h_trim p hp).2.2.1
    have h2 : (F p).card < 2 * M := h_upper_band p hp
    have h3 : m_min ≤ (F p).card := h_lower p (hP''sub hp)
    have h4 : (m_min : ℝ) ≤ ((F p).card : ℝ) := by exact_mod_cast h3
    have h5 : ((F p).card : ℝ) < 2 * (M : ℝ) := by exact_mod_cast h2
    linarith
  exact ⟨P'', M, F', hP''sub, h_card_retention, hP''nonempty, hM_pos, h_size, h_subset, h_upper_band, hM_lower⟩

/-! ========================================================================
   Frontend helper lemmas (fiber bound, threshold absorption, log bound)
   ======================================================================== -/

/-- General fiber cardinality bound: if f has fibers of size ≤ K, then |f '' A| ≥ |A| / K. -/
lemma card_image_fiber_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (A : Finset α) (K : ℕ) (hK_pos : 0 < K)
    (h_fiber : ∀ y ∈ A.image f, (A.filter (fun x => f x = y)).card ≤ K) :
    (A.card : ℝ) ≤ (K : ℝ) * (A.image f).card := by
  have h_disj : Set.PairwiseDisjoint (A.image f : Set β) (fun y => A.filter (fun x => f x = y)) := by
    intro y1 _ y2 _ hne
    simp only [Finset.disjoint_left, Finset.mem_coe, Finset.mem_filter]
    intro x hx1 hx2
    have h1 : f x = y1 := hx1.2
    have h2 : f x = y2 := hx2.2
    exact hne (h1.symm.trans h2)
  have h_union : (A.image f).biUnion (fun y => A.filter (fun x => f x = y)) = A := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨y, _, hx, _⟩; exact hx
    · intro hx
      exact ⟨f x, ⟨x, hx, rfl⟩, hx, rfl⟩
  have h_sum : ∑ y ∈ A.image f, (A.filter (fun x => f x = y)).card = A.card := by
    have h := Finset.card_biUnion h_disj
    rw [h_union] at h; exact h.symm
  have h_le : ∑ y ∈ A.image f, (A.filter (fun x => f x = y)).card ≤
      ∑ y ∈ A.image f, K := by
    apply Finset.sum_le_sum; intro y hy; exact h_fiber y hy
  have h_const : ∑ y ∈ A.image f, K = (A.image f).card * K := by
    rw [Finset.sum_const] <;> ring
  rw [h_const] at h_le
  rw [h_sum] at h_le
  exact_mod_cast (by linarith)

/-- Log-polynomial bound: 2n+5 ≤ C_α * 2^{α*n} for all n : ℕ, α > 0. -/
lemma log_poly_bound {α : ℝ} (hα_pos : 0 < α) (n : ℕ) :
    (2 * (n : ℝ) + 5) ≤
      (28 / (α^2 * (Real.log 2)^2) + 5) * (2 : ℝ)^(α * (n : ℝ)) := by
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C : ℝ := 28 / (α^2 * (Real.log 2)^2) + 5 with hC
  have hC_pos : 0 < C := by positivity
  have h_exp_quad : ∀ (x : ℝ), 0 ≤ x → Real.exp x ≥ x^2 / 4 := by
    intro x hx
    have h3 : Real.exp x = (Real.exp (x / 2)) * (Real.exp (x / 2)) := by
      rw [← Real.exp_add] <;> ring_nf
    rw [h3]
    have h4 : Real.exp (x / 2) ≥ 1 + x / 2 := by
      linarith [Real.add_one_le_exp (x / 2)]
    have h5 : 0 ≤ 1 + x / 2 := by linarith
    nlinarith
  by_cases hn : n = 0
  · rw [hn]
    simpa using show (5 : ℝ) ≤ C by
      dsimp only [C] <;> linarith [show (0 : ℝ) ≤ 28 / (α^2 * (Real.log 2)^2) by positivity]
  · have h_n_pos : 0 < n := Nat.pos_of_ne_zero hn
    set x : ℝ := α * (n : ℝ) * Real.log 2 with hx
    have hx_nonneg : 0 ≤ x := by positivity
    have h1 : (2 : ℝ)^(α * (n : ℝ)) ≥ x^2 / 4 := by
      have h3 : (2 : ℝ)^(α * (n : ℝ)) = Real.exp x := by
        rw [Real.rpow_def_of_pos (by norm_num), hx] <;> ring_nf
      rw [h3]
      exact h_exp_quad x hx_nonneg
    have h4 : C * (2 : ℝ)^(α * (n : ℝ)) ≥ C * (x^2 / 4) := by gcongr
    have h5 : C * (x^2 / 4) ≥ 7 * (n : ℝ)^2 := by
      have h6 : C ≥ 28 / (α^2 * (Real.log 2)^2) := by
        dsimp only [C] <;> linarith
      have h7 : (28 / (α^2 * (Real.log 2)^2)) * (x^2 / 4) = 7 * (n : ℝ)^2 := by
        simp only [hx]
        field_simp [hα_pos.ne', h_log2_pos.ne'] <;> ring
      calc C * (x^2 / 4)
        ≥ (28 / (α^2 * (Real.log 2)^2)) * (x^2 / 4) := by gcongr
      _ = 7 * (n : ℝ)^2 := h7
    have h8 : 7 * (n : ℝ)^2 ≥ 2 * (n : ℝ) + 5 := by
      have h9 : (n : ℝ) ≥ 1 := by exact_mod_cast h_n_pos
      nlinarith
    linarith

/-- Threshold lemma: for small enough δ_n, L/K_fiber ≥ 2 * δ_n^{-s+εReg+fixedLoss}. -/
lemma m_min_threshold_condition
    (s εReg fixedLoss K_fiber : ℝ)
    (hs_gt_εReg : εReg < s)
    (hfixedLoss_pos : 0 < fixedLoss)
    (hK_fiber_pos : 0 < K_fiber)
    (δ_n δ : ℝ)
    (hδn_pos : 0 < δ_n)
    (hδ_lt_16δn : δ < 16 * δ_n)
    (hδ_pos : 0 < δ)
    (L_real : ℝ)
    (hL : L_real ≥ δ^(-s + εReg))
    (h_threshold : δ_n^fixedLoss ≤ (16 : ℝ)^(-s + εReg) / (2 * K_fiber)) :
    L_real / K_fiber ≥ 2 * δ_n^(-s + εReg + fixedLoss) := by
  have h_exp_neg : -s + εReg < 0 := by linarith
  have h1 : δ^(-s + εReg) ≥ (16 * δ_n)^(-s + εReg) := by
    have h2 : δ ≤ 16 * δ_n := by linarith
    have h3 : 0 < δ := hδ_pos
    have h4 : 0 < 16 * δ_n := by positivity
    by_cases h7 : -s + εReg = 0
    · rw [h7] <;> simp
    · have h8 : -s + εReg < 0 := by linarith
      have h9 : Real.log δ ≤ Real.log (16 * δ_n) := Real.log_le_log (by linarith) (by linarith)
      have h10 : (-s + εReg) * Real.log δ ≥ (-s + εReg) * Real.log (16 * δ_n) := by nlinarith
      have h11 : δ^(-s + εReg) = Real.exp ((-s + εReg) * Real.log δ) := by
        rw [Real.rpow_def_of_pos h3] <;> ring_nf
      have h12 : (16 * δ_n)^(-s + εReg) = Real.exp ((-s + εReg) * Real.log (16 * δ_n)) := by
        rw [Real.rpow_def_of_pos h4] <;> ring_nf
      rw [h11, h12]; exact Real.exp_le_exp.mpr h10
  have h5 : (16 * δ_n)^(-s + εReg) = (16 : ℝ)^(-s + εReg) * δ_n^(-s + εReg) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)] <;> ring
  have h6 : L_real / K_fiber ≥ δ^(-s + εReg) / K_fiber := by gcongr
  have h7 : δ^(-s + εReg) / K_fiber ≥
      (16 : ℝ)^(-s + εReg) * δ_n^(-s + εReg) / K_fiber := by gcongr <;> linarith
  have h8 : (16 : ℝ)^(-s + εReg) * δ_n^(-s + εReg) / K_fiber ≥
      2 * δ_n^(-s + εReg + fixedLoss) := by
    have h9 : δ_n^(-s + εReg + fixedLoss) = δ_n^(-s + εReg) * δ_n^fixedLoss := by
      rw [← Real.rpow_add hδn_pos] <;> ring
    rw [h9]
    have h10 : (16 : ℝ)^(-s + εReg) / K_fiber ≥ 2 * δ_n^fixedLoss := by
      calc (16 : ℝ)^(-s + εReg) / K_fiber
        = 2 * ((16 : ℝ)^(-s + εReg) / (2 * K_fiber)) := by ring
      _ ≥ 2 * δ_n^fixedLoss := by gcongr
    have h11 : 0 < δ_n^(-s + εReg) := by positivity
    have h12 : (16 : ℝ)^(-s + εReg) * δ_n^(-s + εReg) / K_fiber =
        δ_n^(-s + εReg) * ((16 : ℝ)^(-s + εReg) / K_fiber) := by ring
    rw [h12]
    have h13 : δ_n^(-s + εReg) * ((16 : ℝ)^(-s + εReg) / K_fiber) ≥
        δ_n^(-s + εReg) * (2 * δ_n^fixedLoss) := by gcongr
    have h14 : δ_n^(-s + εReg) * (2 * δ_n^fixedLoss) =
        2 * (δ_n^(-s + εReg) * δ_n^fixedLoss) := by ring
    calc δ_n^(-s + εReg) * ((16 : ℝ)^(-s + εReg) / K_fiber)
      ≥ δ_n^(-s + εReg) * (2 * δ_n^fixedLoss) := h13
    _ = 2 * (δ_n^(-s + εReg) * δ_n^fixedLoss) := h14
  linarith

/-- Existence of threshold δ_front for the m_min condition. -/
lemma exists_m_min_threshold
    (s εReg fixedLoss K_fiber : ℝ)
    (hs_gt_εReg : εReg < s)
    (hfixedLoss_pos : 0 < fixedLoss)
    (hK_fiber_pos : 0 < K_fiber) :
    ∃ (δ_front : ℝ), 0 < δ_front ∧ ∀ (δ_n : ℝ), 0 < δ_n → δ_n ≤ δ_front →
      δ_n^fixedLoss ≤ (16 : ℝ)^(-s + εReg) / (2 * K_fiber) := by
  let C : ℝ := (16 : ℝ)^(-s + εReg) / (2 * K_fiber)
  have hC_pos : 0 < C := by positivity
  let δ_front : ℝ := C^(1 / fixedLoss)
  have hδ_front_pos : 0 < δ_front := by positivity
  refine ⟨δ_front, hδ_front_pos, fun δ_n hδn_pos hδn_le => ?_⟩
  have h1 : δ_n^fixedLoss ≤ δ_front^fixedLoss := by gcongr <;> linarith
  have h2 : δ_front^fixedLoss = C := by
    have h3 : δ_front = C^(1 / fixedLoss) := by rfl
    rw [h3]
    have h4 : (1 / fixedLoss) * fixedLoss = 1 := by field_simp [hfixedLoss_pos.ne'] <;> ring
    rw [← Real.rpow_mul (by positivity)] <;> rw [h4] <;> simp
  rw [h2] at h1; exact h1

/-- Complete quantitative image bound: if |A| ≥ δ^{-s+εReg} and the map f has fibers
    of size ≤ K_fiber, and the threshold condition holds, then
    |f '' A| ≥ 2 * δ_n^{-s+εReg+fixedLoss}. -/
lemma quantitative_image_bound
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (A : Finset α) (K_fiber : ℕ) (hK_pos : 0 < K_fiber)
    (s εReg fixedLoss δ_n δ : ℝ)
    (hs_gt_εReg : εReg < s)
    (hfixedLoss_pos : 0 < fixedLoss)
    (hδn_pos : 0 < δ_n)
    (hδ_pos : 0 < δ)
    (hδ_lt_16δn : δ < 16 * δ_n)
    (h_fiber : ∀ y ∈ A.image f, (A.filter (fun x => f x = y)).card ≤ K_fiber)
    (hA_lower : (A.card : ℝ) ≥ δ^(-s + εReg))
    (h_threshold : δ_n^fixedLoss ≤ (16 : ℝ)^(-s + εReg) / (2 * (K_fiber : ℝ))) :
    ((A.image f).card : ℝ) ≥ 2 * δ_n^(-s + εReg + fixedLoss) := by
  have h1 : (A.card : ℝ) ≤ (K_fiber : ℝ) * (A.image f).card :=
    card_image_fiber_bound f A K_fiber hK_pos h_fiber
  have hK_real_pos : (0 : ℝ) < (K_fiber : ℝ) := by exact_mod_cast hK_pos
  have h2 : ((A.image f).card : ℝ) ≥ (A.card : ℝ) / (K_fiber : ℝ) := by
    have h21 : (A.card : ℝ) ≤ (K_fiber : ℝ) * (A.image f).card := h1
    have h : (A.card : ℝ) / (K_fiber : ℝ) ≤ ((A.image f).card : ℝ) := by
      calc (A.card : ℝ) / (K_fiber : ℝ)
        ≤ ((K_fiber : ℝ) * (A.image f).card) / (K_fiber : ℝ) := by gcongr
      _ = ((A.image f).card : ℝ) := by
        field_simp [hK_real_pos.ne'] <;> ring
    exact h
  let L_real := δ^(-s + εReg)
  have hL : L_real ≥ δ^(-s + εReg) := by simp [L_real]
  have hA_ge_L : (A.card : ℝ) ≥ L_real := by
    simpa [L_real] using hA_lower
  have h3 : ((A.image f).card : ℝ) ≥ L_real / (K_fiber : ℝ) := by
    calc ((A.image f).card : ℝ)
      ≥ (A.card : ℝ) / (K_fiber : ℝ) := h2
    _ ≥ L_real / (K_fiber : ℝ) := by gcongr
  have h4 := m_min_threshold_condition s εReg fixedLoss (K_fiber : ℝ)
    hs_gt_εReg hfixedLoss_pos hK_real_pos δ_n δ hδn_pos hδ_lt_16δn hδ_pos L_real hL h_threshold
  linarith

/-- At most 4 points whose images under f are δ_n-separated in a δ_n-square. -/
lemma four_point_packing_bound {α : Type*} {E : Finset α} {n : ℕ} {q : DyadicSquare n} (f : α → EuclideanPlane)
    (hδn_pos : 0 < dyadicDelta n)
    (h_sep : ∀ (x y : α), x ∈ E → y ∈ E → x ≠ y → dyadicDelta n ≤ dist (f x) (f y))
    (h_in : ∀ x ∈ E, f x ∈ q.toSet) :
    E.card ≤ 4 := by
  let δ_n := dyadicDelta n
  let half : ℝ := δ_n / 2
  let i0 : ℝ := (q.i : ℝ) * δ_n
  let j0 : ℝ := (q.j : ℝ) * δ_n
  have h_half2 : half + half = δ_n := by dsimp only [half] <;> ring
  have h_i_end : ((q.i + 1 : ℤ) : ℝ) * δ_n = i0 + δ_n := by
    have h_cast : ((q.i + 1 : ℤ) : ℝ) = (q.i : ℝ) + 1 := by
      simp [Int.cast_add] <;> ring
    rw [h_cast]
    dsimp only [i0] <;> ring
  have h_j_end : ((q.j + 1 : ℤ) : ℝ) * δ_n = j0 + δ_n := by
    have h_cast : ((q.j + 1 : ℤ) : ℝ) = (q.j : ℝ) + 1 := by
      simp [Int.cast_add] <;> ring
    rw [h_cast]
    dsimp only [j0] <;> ring
  let quadrant : α → Bool × Bool := fun x =>
    (f x 0 < i0 + half, f x 1 < j0 + half)
  by_contra h
  have h5 : 5 ≤ E.card := by omega
  let Q : Finset (Bool × Bool) := E.image quadrant
  have hQ_le4 : Q.card ≤ 4 := by
    have h1 : Q ⊆ Finset.univ := Finset.subset_univ _
    have h2 := Finset.card_le_card h1
    simpa using h2
  have h_inj : ¬ Set.InjOn quadrant (E : Set α) := by
    intro h_inj_on
    have h_eq : Q.card = E.card := Finset.card_image_of_injOn h_inj_on
    rw [h_eq] at hQ_le4
    omega
  have h_exists : ∃ (x : α), x ∈ E ∧ ∃ (y : α), y ∈ E ∧ x ≠ y ∧ quadrant x = quadrant y := by
    have h' : ¬ Set.InjOn quadrant (E : Set α) := h_inj
    have h'' : ∃ (x : α), x ∈ E ∧ ∃ (y : α), y ∈ E ∧ quadrant x = quadrant y ∧ x ≠ y := by
      simpa [Set.InjOn] using h'
    rcases h'' with ⟨x, hx, y, hy, hq_eq, hne⟩
    exact ⟨x, hx, y, hy, hne, hq_eq⟩
  rcases h_exists with ⟨x, hx, y, hy, hne, hq_eq⟩
  set fx : EuclideanPlane := f x with hfx_def
  set fy : EuclideanPlane := f y with hfy_def
  have hx' : fx ∈ q.toSet := h_in x hx
  have hy' : fy ∈ q.toSet := h_in y hy
  have hqx : (fx 0 < i0 + half) = (fy 0 < i0 + half) := by
    have h : (quadrant x).1 = (quadrant y).1 := by rw [hq_eq]
    simpa [quadrant] using h
  have hqy : (fx 1 < j0 + half) = (fy 1 < j0 + half) := by
    have h : (quadrant x).2 = (quadrant y).2 := by rw [hq_eq]
    simpa [quadrant] using h
  have hdx : |fx 0 - fy 0| < half := by
    by_cases h : fx 0 < i0 + half
    · have h' : fy 0 < i0 + half := by rw [hqx] at h; exact h
      have h1 : i0 ≤ fx 0 := hx'.1
      have h2 : i0 ≤ fy 0 := hy'.1
      have h_lo : -half < fx 0 - fy 0 := by linarith
      have h_hi : fx 0 - fy 0 < half := by linarith
      exact abs_lt.mpr ⟨h_lo, h_hi⟩
    · have h' : ¬(fy 0 < i0 + half) := by rw [hqx] at h; exact h
      have h1 : i0 + half ≤ fx 0 := by linarith
      have h2 : i0 + half ≤ fy 0 := by linarith
      have h3 : fx 0 < ((q.i + 1 : ℤ) : ℝ) * δ_n := by simpa [δ_n] using hx'.2.1
      have h4 : fy 0 < ((q.i + 1 : ℤ) : ℝ) * δ_n := by simpa [δ_n] using hy'.2.1
      rw [h_i_end] at h3 h4
      have h_lo : -half < fx 0 - fy 0 := by linarith
      have h_hi : fx 0 - fy 0 < half := by linarith
      exact abs_lt.mpr ⟨h_lo, h_hi⟩
  have hdy : |fx 1 - fy 1| < half := by
    by_cases h : fx 1 < j0 + half
    · have h' : fy 1 < j0 + half := by rw [hqy] at h; exact h
      have h1 : j0 ≤ fx 1 := hx'.2.2.1
      have h2 : j0 ≤ fy 1 := hy'.2.2.1
      have h_lo : -half < fx 1 - fy 1 := by linarith
      have h_hi : fx 1 - fy 1 < half := by linarith
      exact abs_lt.mpr ⟨h_lo, h_hi⟩
    · have h' : ¬(fy 1 < j0 + half) := by rw [hqy] at h; exact h
      have h1 : j0 + half ≤ fx 1 := by linarith
      have h2 : j0 + half ≤ fy 1 := by linarith
      have h3 : fx 1 < ((q.j + 1 : ℤ) : ℝ) * δ_n := by simpa [δ_n] using hx'.2.2.2
      have h4 : fy 1 < ((q.j + 1 : ℤ) : ℝ) * δ_n := by simpa [δ_n] using hy'.2.2.2
      rw [h_j_end] at h3 h4
      have h_lo : -half < fx 1 - fy 1 := by linarith
      have h_hi : fx 1 - fy 1 < half := by linarith
      exact abs_lt.mpr ⟨h_lo, h_hi⟩
  have hdist_lt : dist fx fy < δ_n := by
    have h_sq : dist fx fy ^ 2 ≤ (|fx 0 - fy 0| + |fx 1 - fy 1|) ^ 2 := by
      have h_cs : (fx 0 - fy 0)^2 + (fx 1 - fy 1)^2 ≤ (|fx 0 - fy 0| + |fx 1 - fy 1|)^2 := by
        have h1 : (fx 0 - fy 0)^2 ≤ |fx 0 - fy 0|^2 := by
          rw [sq_abs]
        have h2 : (fx 1 - fy 1)^2 ≤ |fx 1 - fy 1|^2 := by rw [sq_abs]
        nlinarith [abs_nonneg (fx 0 - fy 0), abs_nonneg (fx 1 - fy 1)]
      have h_dist2 : dist fx fy ^ 2 = (fx 0 - fy 0)^2 + (fx 1 - fy 1)^2 := by
        have h1 : dist fx fy = ‖fx - fy‖ := by exact dist_eq_norm fx fy
        rw [h1]
        have h2 : ‖fx - fy‖ = Real.sqrt (((fx - fy) 0)^2 + ((fx - fy) 1)^2) := by
          simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring
        rw [h2]
        have h3 : 0 ≤ (fx - fy) 0 ^ 2 + (fx - fy) 1 ^ 2 := by positivity
        rw [Real.sq_sqrt h3] <;> simp [sub_eq_add_neg] <;> ring
      rw [h_dist2]
      exact h_cs
    have h_sum : |fx 0 - fy 0| + |fx 1 - fy 1| < δ_n := by
      have h1 : |fx 0 - fy 0| < half := hdx
      have h2 : |fx 1 - fy 1| < half := hdy
      linarith [h_half2]
    have h_pos : 0 ≤ dist fx fy := by positivity
    have h_pos2 : 0 ≤ |fx 0 - fy 0| + |fx 1 - fy 1| := by positivity
    nlinarith
  have hsep : δ_n ≤ dist fx fy := h_sep x y hx hy hne
  linarith


-- Note: snapToTubeThroughPoint now uses Int.floor for the b-index,
-- which guarantees both Main tube strip incidence (0 ≤ d < δ) and
-- Stand exact-cell incidence (d ∈ [0,δ)). No separate floorB variant needed.


/-- Local copy of dyadic_subset_sset_transfer: transfer S-set from larger to smaller tube family. -/
lemma dyadic_subset_sset_transfer_local {n : ℕ} {s C : ℝ}
    {A B : Finset (DyadicTube n)}
    (hB_sub : B ⊆ A)
    (h_card : A.card < 2 * B.card)
    (hA_sset : IsDeltaSSet (dyadicDelta n) s C (A : Set (DyadicTube n))) :
    IsDeltaSSet (dyadicDelta n) s (18 * C) (B : Set (DyadicTube n)) := by
  set δ_n := dyadicDelta n with hδn_def
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  have hB_pos : 0 < B.card := by
    by_contra h
    have h0 : B.card = 0 := by omega
    have h1 : B = ∅ := by simpa [Finset.card_eq_zero] using h0
    rw [h1] at h_card
    exact False.elim (not_lt.mpr (Nat.zero_le A.card) h_card)
  have hB_nonempty : (B : Set (DyadicTube n)).Nonempty := by
    simpa [Finset.nonempty_iff_ne_empty] using hB_pos
  have h_sep : SeparatedAt δ_n (B : Set (DyadicTube n)) := by
    intro T1 hT1 T2 hT2 hne
    have h_dist_eq : dist T1 T2 = T1.dist T2 := by rfl
    rw [h_dist_eq, DyadicTube.dist_eq T1 T2]
    have h_ne_coord : T1.a ≠ T2.a ∨ T1.b ≠ T2.b := by
      by_contra h
      push Not at h
      have h' : T1 = T2 := by exact InductionOnScales.DyadicTube.eq_iff.mpr h
      exact hne h'
    have h_pos : 0 < (|(T1.a - T2.a : ℤ)| : ℝ) + (|(T1.b - T2.b : ℤ)| : ℝ) := by
      rcases h_ne_coord with (h | h)
      · have h' : (T1.a - T2.a : ℤ) ≠ 0 := by omega
        have h'' : 0 < |(T1.a - T2.a : ℤ)| := abs_pos.mpr h'
        have h3 : 0 ≤ (|(T1.b - T2.b : ℤ)| : ℝ) := by positivity
        have h4 : (0 : ℝ) < (|(T1.a - T2.a : ℤ)| : ℝ) := by exact_mod_cast h''
        exact add_pos_of_pos_of_nonneg h4 h3
      · have h' : (T1.b - T2.b : ℤ) ≠ 0 := by omega
        have h'' : 0 < |(T1.b - T2.b : ℤ)| := abs_pos.mpr h'
        have h3 : 0 ≤ (|(T1.a - T2.a : ℤ)| : ℝ) := by positivity
        have h4 : (0 : ℝ) < (|(T1.b - T2.b : ℤ)| : ℝ) := by exact_mod_cast h''
        exact add_pos_of_nonneg_of_pos h3 h4
    have h9 : (1 : ℝ) ≤ (|(T1.a - T2.a : ℤ)| : ℝ) + (|(T1.b - T2.b : ℤ)| : ℝ) := by
      exact_mod_cast h_pos
    have h_ge : δ_n * ((|(T1.a - T2.a : ℤ)| : ℝ) + (|(T1.b - T2.b : ℤ)| : ℝ)) ≥ δ_n := by
      nlinarith
    exact h_ge
  have h_pack : (B.card : ENNReal) ≤ (9 : ENNReal) * Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n)) :=
    DirecretisedFurstenbergEstimate.SSetBridges.packing_cover_generic
      (hδ_pos := hδn_pos) (hsep := h_sep) (hK_pos := by norm_num)
      (fun x => max_points_in_delta_ball_DyadicTube hδn_pos B h_sep x)
  have h1 : (Metric.externalCoveringNumber δ_n.toNNReal (A : Set (DyadicTube n)) : ENNReal) ≤ (A.card : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_le_encard_self (A : Set (DyadicTube n))
  have h2 : (A.card : ENNReal) < 2 * (B.card : ENNReal) := by exact_mod_cast h_card
  have h3 : (Metric.externalCoveringNumber δ_n.toNNReal (A : Set (DyadicTube n)) : ENNReal) ≤
      (18 : ENNReal) * Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n)) := by
    calc (Metric.externalCoveringNumber δ_n.toNNReal (A : Set (DyadicTube n)) : ENNReal)
      ≤ (A.card : ENNReal) := h1
    _ ≤ 2 * (B.card : ENNReal) := le_of_lt h2
    _ ≤ 2 * ((9 : ENNReal) * Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n))) := by gcongr
    _ = (18 : ENNReal) * Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n)) := by ring
  rcases hA_sset with ⟨hne_A, hδ, hC_pos, hs, hmain⟩
  have hC18_pos : 0 < 18 * C := by positivity
  refine ⟨hB_nonempty, hδ, hC18_pos, hs, fun x r hr => ?_⟩
  have h4 : (Metric.externalCoveringNumber δ_n.toNNReal ((B : Set (DyadicTube n)) ∩ Metric.closedBall x r) : ENNReal) ≤
      Metric.externalCoveringNumber δ_n.toNNReal ((A : Set (DyadicTube n)) ∩ Metric.closedBall x r) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set (show (B : Set (DyadicTube n)) ∩ Metric.closedBall x r ⊆ (A : Set (DyadicTube n)) ∩ Metric.closedBall x r from by gcongr)
  have h5 := hmain x r hr
  calc (Metric.externalCoveringNumber δ_n.toNNReal ((B : Set (DyadicTube n)) ∩ Metric.closedBall x r) : ENNReal)
    ≤ Metric.externalCoveringNumber δ_n.toNNReal ((A : Set (DyadicTube n)) ∩ Metric.closedBall x r) := h4
  _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ_n.toNNReal (A : Set (DyadicTube n)) := h5
  _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * ((18 : ENNReal) * Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n))) := by gcongr
  _ = ENNReal.ofReal (18 * C) * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n)) := by
    let a : ENNReal := ENNReal.ofReal C
    let b : ENNReal := (ENNReal.ofReal r) ^ s
    let c : ENNReal := Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n))
    have h_mul : a * b * ((18 : ENNReal) * c) = (18 : ENNReal) * a * b * c := by
      have h1 : a * b * ((18 : ENNReal) * c) = (18 : ENNReal) * (a * b * c) := by
        calc a * b * ((18 : ENNReal) * c)
          = (a * b) * ((18 : ENNReal) * c) := by rfl
        _ = ((18 : ENNReal) * c) * (a * b) := by exact mul_comm (a * b) ((18 : ENNReal) * c)
        _ = (18 : ENNReal) * (c * (a * b)) := by rw [mul_assoc]
        _ = (18 : ENNReal) * ((a * b) * c) := by rw [mul_comm c (a * b)]
        _ = (18 : ENNReal) * (a * b * c) := by rw [mul_assoc a b]
      rw [h1] <;> simp only [mul_assoc]
    have h6 : (18 : ENNReal) * a = ENNReal.ofReal (18 * C) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18)] <;> norm_cast
    have h_final : a * b * ((18 : ENNReal) * c) = ENNReal.ofReal (18 * C) * b * c := by
      rw [h_mul, h6] <;> simp only [mul_assoc]
    exact h_final

/-- Standalone bound on the cardinality of the universal dyadic tube set. -/
lemma exact_m_frontend_allTubes_bound (n : ℕ) :
    ((Finset.Ico (-(2^n : ℤ)) (2^n : ℤ)).biUnion
      (fun a : ℤ => (Finset.Ico (-(3 * 2^n : ℤ)) (3 * 2^n : ℤ)).image
        (fun b : ℤ => (⟨a, b⟩ : DyadicTube n)))).card ≤ 12 * 16^n := by
  let aSet := Finset.Ico (-(2^n : ℤ)) (2^n : ℤ)
  let bSet := Finset.Ico (-(3 * 2^n : ℤ)) (3 * 2^n : ℤ)
  let f : ℤ × ℤ → DyadicTube n := fun p => ⟨p.1, p.2⟩
  let allTubes := aSet.biUnion (fun a => bSet.image (fun b => f (a, b)))
  have h_inj : Function.Injective f := by
    intro p q h
    injection h with h1 h2
    exact Prod.ext h1 h2
  have h_sub : allTubes ⊆ (aSet ×ˢ bSet).image f := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hb⟩
    rcases Finset.mem_image.mp hb with ⟨b, hb', rfl⟩
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb'⟩, rfl⟩
  have h_card : allTubes.card ≤ aSet.card * bSet.card := by
    calc allTubes.card
      ≤ ((aSet ×ˢ bSet).image f).card := Finset.card_le_card h_sub
    _ = (aSet ×ˢ bSet).card := Finset.card_image_of_injective _ h_inj
    _ = aSet.card * bSet.card := Finset.card_product _ _
  have ha : aSet.card = 2 * 2^n := by
    rw [Int.card_Ico]
    have h : (2^n : ℤ) - (-(2^n : ℤ)) = 2 * (2^n : ℤ) := by ring
    rw [h]
    have h2 : 0 ≤ 2 * (2^n : ℤ) := by positivity
    have h3 : ((2 * (2^n : ℤ)).toNat : ℤ) = 2 * (2^n : ℤ) := Int.toNat_of_nonneg h2
    exact_mod_cast h3
  have hb : bSet.card = 6 * 2^n := by
    rw [Int.card_Ico]
    have h : (3 * (2^n : ℤ)) - (-(3 * (2^n : ℤ))) = 6 * (2^n : ℤ) := by ring
    rw [h]
    have h2 : 0 ≤ 6 * (2^n : ℤ) := by positivity
    have h3 : ((6 * (2^n : ℤ)).toNat : ℤ) = 6 * (2^n : ℤ) := Int.toNat_of_nonneg h2
    exact_mod_cast h3
  have h4 : 2^n * 2^n = 4^n := by
    have h41 : 2^n * 2^n = 2^(n + n) := by rw [← pow_add]
    rw [h41]
    have h42 : n + n = 2 * n := by omega
    rw [h42]
    have h43 : 2^(2 * n) = (2^2)^n := by
      rw [pow_mul] <;> omega
    rw [h43] <;> norm_num
  have h5 : allTubes.card ≤ 12 * 4^n := by
    calc allTubes.card
      ≤ aSet.card * bSet.card := h_card
    _ = (2 * 2^n) * (6 * 2^n) := by rw [ha, hb]
    _ = 12 * (2^n * 2^n) := by ring
    _ = 12 * 4^n := by rw [h4]
  have h6 : (4 : ℕ)^n ≤ (16 : ℕ)^n := by
    have h7 : (16 : ℕ)^n = (4 : ℕ)^n * (4 : ℕ)^n := by
      have h8 : (16 : ℕ) = 4 * 4 := by decide
      rw [h8, mul_pow] <;> rfl
    rw [h7]
    have h9 : 0 < (4 : ℕ)^n := by positivity
    exact le_mul_of_one_le_right (by positivity) h9
  calc allTubes.card
    ≤ 12 * 4^n := h5
  _ ≤ 12 * 16^n := mul_le_mul_of_nonneg_left h6 (by positivity)

set_option maxHeartbeats 1000000

/-- Exact-M quantitative frontend with small-scale threshold. -/
theorem exact_m_frontend
    {s εReg εA fixedLoss pointLoss tubeLoss : ℝ}
    (hs_pos : 0 < s)
    (hεReg_pos : 0 < εReg)
    (hεReg_lt_s : εReg < s)
    (hεA_pos : 0 < εA)
    (hfixedLoss_pos : 0 < fixedLoss)
    (hpointLoss_pos : 0 < pointLoss)
    (htubeLoss_pos : 0 < tubeLoss)
    (h_budget : εReg + pointLoss + tubeLoss + fixedLoss ≤ εA) :
    ∃ (δ_exact : ℝ), 0 < δ_exact ∧
      ∀ (u : ℝ), s < u → u ≤ 2 →
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ_exact → δ ≤ 1 →
      ∀ (P : Set Plane)
        (hP_subset : P ⊆ Metric.closedBall (0 : Plane) 1)
        (hReg : IsSquareRootRegular δ u
          (Real.rpow δ (-εReg)) (Real.rpow δ (-εReg)) P)
        (tubeFamily : (p : Plane) → p ∈ P → Set AffineLine)
        (hTubes : ∀ p hp, IsDeltaSSet δ s (Real.rpow δ (-εReg)) (tubeFamily p hp))
        (hIncidence : ∀ p hp, ∀ ℓ ∈ tubeFamily p hp,
          p ∈ Metric.cthickening δ ℓ.1)
        (hChart : ∀ p hp, ∀ ℓ ∈ tubeFamily p hp, InStandardChart.inChart ℓ)
        (hOffset : ∀ p hp, ∀ ℓ ∈ tubeFamily p hp, ‖ℓ.offset‖ ≤ 2),
        ∃ (n m : ℕ) (C₁ M : ℕ) (C_P_reg K_P_reg : ℝ),
          n = 2 * m ∧
          dyadicDelta n ≤ δ / 4 ∧ δ / 4 < 4 * dyadicDelta n ∧
          0 < M ∧
          (M : ℝ) ≥ (dyadicDelta n)^(-s + εReg + fixedLoss) ∧
          (C₁ : ℝ) ≤ (dyadicDelta n)^(-(εReg + tubeLoss)) ∧
          1 ≤ C₁ ∧
          0 ≤ C_P_reg ∧ C_P_reg ≤ (dyadicDelta n)^(-(εReg + pointLoss)) ∧
          0 < K_P_reg ∧ K_P_reg ≤ (dyadicDelta n)^(-(εReg + pointLoss)) ∧
          ∃ (config : CombiningTheorem.NiceConfiguration n s (C₁ : ℝ) M),
            config.P₀.Nonempty ∧
            (∀ (p : DyadicSquare n), p ∈ config.P₀ →
              0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧
              0 ≤ p.j ∧ p.j < (2 ^ n : ℤ)) ∧
            (∀ (T : DyadicTube n), T ∈ config.T₀ →
              -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ)) ∧
            config.T₀.card ≤ 12 * 16^n ∧
            (∀ (p : DyadicSquare n) (hp : p ∈ config.P₀)
              (T : DyadicTube n) (hT : T ∈ config.tubeFamily p hp),
              ((tubeToStand T).toSet ∩ (squareToStand p).toSet).Nonempty) ∧
            (config.P₀.card : ENNReal) ≥
              ENNReal.ofReal ((dyadicDelta n)^(-u + εReg + pointLoss)) ∧
            IsSquareRootRegular (dyadicDelta n) u C_P_reg K_P_reg config.pointSet ∧
            (config.P₀.card : ENNReal) ≥
              Ncover (dyadicDelta n) config.pointSet ∧
            (∀ (p : DyadicSquare n) (hp : p ∈ config.P₀)
              (T : DyadicTube n) (hT : T ∈ config.tubeFamily p hp),
              ∃ (p_orig : Plane) (hp_orig : p_orig ∈ P)
                (ℓ : AffineLine) (hℓ : ℓ ∈ tubeFamily p_orig hp_orig),
              T = snapToTubeThroughPoint n (S0_line ℓ) (S0 p_orig)) ∧
            (∀ (q : DyadicSquare n), q ∈ config.P₀ →
              ∃ (p_orig : Plane) (hp_orig : p_orig ∈ P),
                S0 p_orig ∈ q.toSet) ∧
            config.pointSet ⊆ Metric.closedBall (0 : Plane) 1 ∧
            (∀ (T : DyadicTube n), T ∈ config.T₀ → |T.slope| ≤ 1) ∧
            (∀ (T : DyadicTube n), T ∈ config.T₀ →
              ∃ (p_orig : Plane) (hp_orig : p_orig ∈ P)
                (ℓ : AffineLine) (hℓ : ℓ ∈ tubeFamily p_orig hp_orig),
              dist (DyadicCardToNcover.toAffineLine T) (S0_line ℓ) ≤ (15 / 2 : ℝ) * (δ / 4)) := by
  -- ======================================================================
  -- Threshold selection
  -- We need δ small enough to absorb all fixed factors.
  -- Use SEPARATE thresholds for each loss exponent, then take the minimum.
  -- ======================================================================

  have hK_pack_pos : 0 < (K_pack : ℝ) := by exact_mod_cast K_pack_pos

  -- FixedLoss: absorbs snapping fiber (260000) and common-M loss (2)
  let K_fixed : ℝ := (260000 : ℝ) * 2 * (16 : ℝ)^εReg
  have hK_fixed_pos : 0 < K_fixed := by dsimp only [K_fixed]; positivity

  -- C₁ constant factor (without δ^{-εReg})
  let K_C1_const : ℝ := 18 * K_snap s * (K_pack : ℝ) * (8 : ℝ)^s * (262144 : ℝ)^4
  -- TubeLoss: absorbs C₁ constant factor for Nat.ceil
  let K_tube : ℝ := K_C1_const + 1
  have hK_C1_const_pos : 0 < K_C1_const := by
    dsimp only [K_C1_const, K_snap]
    have h1 : 0 < (K_pack : ℝ) := by exact_mod_cast K_pack_pos
    positivity
  have hK_tube_pos : 0 < K_tube := by
    dsimp only [K_tube]
    exact add_pos_of_pos_of_nonneg hK_C1_const_pos (by norm_num)

  -- PointLoss: absorbs scale transfer (16 = worst-case 4^u for u≤2),
  -- scale comparison (16^εReg), and point-to-square packing (4)
  let K_point : ℝ := (16 : ℝ) * (16 : ℝ)^εReg * 4
  have hK_point_pos : 0 < K_point := by dsimp only [K_point]; positivity

  -- Geometry constants from local regularity transfer
  let C_geom : ℝ := (2 * (Real.sqrt 2 + 1) + 4) ^ 2
  let K_geom_C : ℝ := 81 * (16 : ℝ)^2 * C_geom^2 * (1 + Real.sqrt 2)^2
  let K_geom_K : ℝ := 9 * C_geom
  have hK_geom_C_pos : 0 < K_geom_C := by dsimp only [K_geom_C, C_geom] <;> positivity
  have hK_geom_K_pos : 0 < K_geom_K := by dsimp only [K_geom_K, C_geom] <;> positivity

  rcases exists_delta_power_bound K_fixed hK_fixed_pos fixedLoss hfixedLoss_pos with
    ⟨δ_fixed, hδ_fixed_pos, h_absorb_fixed⟩
  rcases exists_delta_power_bound K_tube hK_tube_pos tubeLoss htubeLoss_pos with
    ⟨δ_tube, hδ_tube_pos, h_absorb_tube⟩
  rcases exists_delta_power_bound K_point hK_point_pos pointLoss hpointLoss_pos with
    ⟨δ_point, hδ_point_pos, h_absorb_point⟩

  -- Geometry constant absorption thresholds
  rcases exists_delta_power_bound K_geom_C hK_geom_C_pos (pointLoss / 2) (by linarith) with
    ⟨δ_geomC, hδ_geomC_pos, h_absorb_geomC⟩
  rcases exists_delta_power_bound K_geom_K hK_geom_K_pos pointLoss hpointLoss_pos with
    ⟨δ_geomK, hδ_geomK_pos, h_absorb_geomK⟩

  -- Polynomial absorption threshold: 1024 * (2n+5) ≤ δ_n^{-pointLoss/2}
  rcases FrontendQuantBounds.exists_delta_poly_absorption 1024 (pointLoss / 2) (by norm_num) (by linarith) with
    ⟨δ_poly, hδ_poly_pos, h_absorb_poly⟩

  -- M-Min threshold: ensures δ_n^fixedLoss ≤ 16^{-s+εReg} / (2 * 260000)
  rcases exists_m_min_threshold s εReg fixedLoss (260000 : ℝ)
      hεReg_lt_s hfixedLoss_pos (by norm_num) with
    ⟨δ_mmin, hδ_mmin_pos, h_absorb_mmin⟩

  let δ_front : ℝ := min δ_fixed (min δ_tube (min δ_point (min δ_geomC (min δ_geomK (min (δ_poly / 4) (δ_mmin / 4))))))
  have hδ_poly4_pos : 0 < δ_poly / 4 := by positivity
  have hδ_mmin4_pos : 0 < δ_mmin / 4 := by positivity
  have hδ_front_pos : 0 < δ_front := by
    dsimp only [δ_front]
    exact lt_min_iff.mpr ⟨hδ_fixed_pos, lt_min_iff.mpr ⟨hδ_tube_pos, lt_min_iff.mpr ⟨hδ_point_pos, lt_min_iff.mpr ⟨hδ_geomC_pos, lt_min_iff.mpr ⟨hδ_geomK_pos, lt_min_iff.mpr ⟨hδ_poly4_pos, hδ_mmin4_pos⟩⟩⟩⟩⟩⟩

  have h_absorb_fixed' : ∀ δ, 0 < δ → δ ≤ δ_front → K_fixed ≤ δ^(-fixedLoss) := by
    intro δ hδ_pos hδ_le
    have h : δ ≤ δ_fixed := by
      dsimp only [δ_front] at hδ_le
      exact le_trans hδ_le (min_le_left _ _)
    exact h_absorb_fixed δ hδ_pos h
  have h_absorb_tube' : ∀ δ, 0 < δ → δ ≤ δ_front → K_tube ≤ δ^(-tubeLoss) := by
    intro δ hδ_pos hδ_le
    dsimp only [δ_front] at hδ_le
    have h : δ ≤ δ_tube := by
      exact le_trans hδ_le (le_trans (min_le_right _ _) (min_le_left _ _))
    exact h_absorb_tube δ hδ_pos h
  have h_absorb_point' : ∀ δ, 0 < δ → δ ≤ δ_front → K_point ≤ δ^(-pointLoss) := by
    intro δ hδ_pos hδ_le
    dsimp only [δ_front] at hδ_le
    have h : δ ≤ δ_point := by
      exact le_trans hδ_le (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    exact h_absorb_point δ hδ_pos h
  have h_absorb_geomC' : ∀ δ, 0 < δ → δ ≤ δ_front → K_geom_C ≤ δ^(-(pointLoss / 2)) := by
    intro δ hδ_pos hδ_le
    dsimp only [δ_front] at hδ_le
    have h : δ ≤ δ_geomC := by
      exact le_trans hδ_le (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
    exact h_absorb_geomC δ hδ_pos h
  have h_absorb_geomK' : ∀ δ, 0 < δ → δ ≤ δ_front → K_geom_K ≤ δ^(-pointLoss) := by
    intro δ hδ_pos hδ_le
    dsimp only [δ_front] at hδ_le
    have h : δ ≤ δ_geomK := by
      exact le_trans hδ_le (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))))
    exact h_absorb_geomK δ hδ_pos h
  have h_absorb_mmin' : ∀ (δ : ℝ), 0 < δ → δ ≤ δ_front → ∀ (δ_n : ℝ), 0 < δ_n → δ_n ≤ δ / 4 →
      δ_n^fixedLoss ≤ (16 : ℝ)^(-s + εReg) / (2 * (260000 : ℝ)) := by
    intro δ hδ_pos hδ_le δ_n hδn_pos hδn_leδ4
    dsimp only [δ_front] at hδ_le
    have h1 : δ_front ≤ min δ_geomK (min (δ_poly / 4) (δ_mmin / 4)) := by
      dsimp only [δ_front]
      have h_a : δ_front ≤ min δ_tube (min δ_point (min δ_geomC (min δ_geomK (min (δ_poly / 4) (δ_mmin / 4))))) := min_le_right _ _
      have h_b : min δ_tube (min δ_point (min δ_geomC (min δ_geomK (min (δ_poly / 4) (δ_mmin / 4))))) ≤ min δ_point (min δ_geomC (min δ_geomK (min (δ_poly / 4) (δ_mmin / 4)))) := min_le_right _ _
      have h_c : min δ_point (min δ_geomC (min δ_geomK (min (δ_poly / 4) (δ_mmin / 4)))) ≤ min δ_geomC (min δ_geomK (min (δ_poly / 4) (δ_mmin / 4))) := min_le_right _ _
      have h_d : min δ_geomC (min δ_geomK (min (δ_poly / 4) (δ_mmin / 4))) ≤ min δ_geomK (min (δ_poly / 4) (δ_mmin / 4)) := min_le_right _ _
      exact le_trans h_a (le_trans h_b (le_trans h_c h_d))
    have h2 : min δ_geomK (min (δ_poly / 4) (δ_mmin / 4)) ≤ δ_mmin / 4 := by
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have h3 : δ ≤ δ_mmin / 4 := le_trans hδ_le (le_trans h1 h2)
    have h4 : δ_n ≤ δ_mmin := by linarith
    exact h_absorb_mmin δ_n hδn_pos h4

  refine ⟨δ_front, hδ_front_pos, fun u hst hu_le2 δ hδ_pos hδ_le hδ_le_one P hP_subset hReg tubeFamily hTubes hIncidence hChart hOffset => ?_⟩

  -- ======================================================================
  -- Step 1: Even scale selection
  -- ======================================================================
  let δ' := δ / 4
  have hδ'_pos : 0 < δ' := by positivity
  have hδ'_le_one : δ' ≤ 1 := by
    have h : δ' ≤ 1 / 4 := by dsimp only [δ']; linarith
    linarith
  rcases choose_even_dyadic_scale δ' hδ'_pos hδ'_le_one with ⟨m, hδn_le, hδn_lt⟩
  let n := 2 * m
  have hn : n = 2 * m := by rfl
  have hδn_le' : dyadicDelta n ≤ δ' := hδn_le
  have hδn_lt' : δ' < 4 * dyadicDelta n := hδn_lt
  have hδn_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have hδn_le_one : dyadicDelta n ≤ 1 := dyadicDelta_le_one n
  let δ_n : ℝ := dyadicDelta n

  -- n ≥ 2 since δ_n ≤ δ/4 ≤ 1/4
  have hn_ge2 : n ≥ 2 := by
    have h1 : dyadicDelta n ≤ 1 / 4 := by
      have h2 : dyadicDelta n ≤ δ / 4 := hδn_le'
      have h3 : δ ≤ 1 := hδ_le_one
      linarith
    have h4 : (1 / 2 : ℝ)^n ≤ 1 / 4 := by
      simpa [dyadicDelta, Real.rpow_neg] using h1
    by_contra h
    have h5 : n < 2 := by omega
    interval_cases n <;> norm_num at h4 <;> linarith

  -- Polynomial absorption: 1024*(2n+5) ≤ δ_n^{-pointLoss/2}
  have hδn_leδpoly : dyadicDelta n ≤ δ_poly := by
    have h1 : δ_front ≤ min δ_point (min (δ_poly / 4) (δ_mmin / 4)) := by
      dsimp only [δ_front]
      let Y := min (δ_poly / 4) (δ_mmin / 4)
      let X := min δ_geomC (min δ_geomK Y)
      have hX : X ≤ Y := by
        dsimp only [X, Y]
        exact le_trans (min_le_right _ _) (min_le_right _ _)
      have h_inner : min δ_point X ≤ min δ_point Y := by
        exact min_le_min le_rfl hX
      exact le_trans (min_le_right δ_fixed _) (le_trans (min_le_right δ_tube _) h_inner)
    have h2 : min δ_point (min (δ_poly / 4) (δ_mmin / 4)) ≤ δ_poly / 4 := by
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have h3 : δ ≤ δ_poly / 4 := le_trans hδ_le (le_trans h1 h2)
    have h4 : dyadicDelta n ≤ δ / 4 := hδn_le'
    have h5 : dyadicDelta n ≤ δ_poly / 16 := by
      calc dyadicDelta n
        ≤ δ / 4 := h4
      _ ≤ (δ_poly / 4) / 4 := by gcongr
      _ = δ_poly / 16 := by ring
    have h6 : δ_poly / 16 ≤ δ_poly := by
      have h7 : 0 < δ_poly := hδ_poly_pos
      linarith
    exact le_trans h5 h6
  have h_poly_absorb_half : (1024 : ℝ) * (2 * (n : ℝ) + 5) ≤ (dyadicDelta n)^(-pointLoss / 2) := by
    have h5 : (dyadicDelta n) = (1 / 2 : ℝ)^n := by
      simp [dyadicDelta, Real.rpow_neg] <;> field_simp <;> norm_cast
    have h6 : (1 / 2 : ℝ)^n ≤ δ_poly := by
      rw [h5] at hδn_leδpoly <;> exact hδn_leδpoly
    have h7 := h_absorb_poly n h6
    have h8 : (2 : ℝ)^((pointLoss / 2) * (n : ℝ)) = (dyadicDelta n)^(-pointLoss / 2) := by
      rw [h5]
      have h9 : (1 / 2 : ℝ)^n = (2 : ℝ)^(-(n : ℝ)) := by
        simp [Real.rpow_neg] <;> field_simp <;> norm_cast
      rw [h9]
      rw [← Real.rpow_mul (by norm_num)] <;> ring_nf
    rw [h8] at h7
    exact h7

  -- Derive full-pointLoss absorption from half-pointLoss
  have h_poly_absorb : (1024 : ℝ) * (2 * (n : ℝ) + 5) ≤ (dyadicDelta n)^(-pointLoss) := by
    have h_half_le_full : (dyadicDelta n)^(-pointLoss / 2) ≤ (dyadicDelta n)^(-pointLoss) :=
      Real.rpow_le_rpow_of_exponent_ge hδn_pos hδn_le_one (by linarith)
    exact le_trans h_poly_absorb_half h_half_le_full

  -- Geometry constant absorption: K_geom_C ≤ δ_n^{-pointLoss/2}, K_geom_K ≤ δ_n^{-pointLoss}
  have hδ_le_geomC : δ ≤ δ_geomC := by
    dsimp only [δ_front] at hδ_le
    have h1 : δ_front ≤ min δ_geomC (min δ_geomK (min (δ_poly / 4) (δ_mmin / 4))) := by
      dsimp only [δ_front]
      exact le_trans (min_le_right δ_fixed _)
        (le_trans (min_le_right δ_tube _) (min_le_right δ_point _))
    have h2 : min δ_geomC (min δ_geomK (min (δ_poly / 4) (δ_mmin / 4))) ≤ δ_geomC := min_le_left _ _
    exact le_trans hδ_le (le_trans h1 h2)
  have hδ_le_geomK : δ ≤ δ_geomK := by
    dsimp only [δ_front] at hδ_le
    have h1 : δ_front ≤ min δ_geomK (min (δ_poly / 4) (δ_mmin / 4)) := by
      dsimp only [δ_front]
      exact le_trans (min_le_right δ_fixed _)
        (le_trans (min_le_right δ_tube _)
          (le_trans (min_le_right δ_point _) (min_le_right δ_geomC _)))
    have h2 : min δ_geomK (min (δ_poly / 4) (δ_mmin / 4)) ≤ δ_geomK := min_le_left _ _
    exact le_trans hδ_le (le_trans h1 h2)
  have h_geomC_absorb : K_geom_C ≤ (dyadicDelta n)^(-pointLoss / 2) := by
    have h1 : K_geom_C ≤ δ^(-(pointLoss / 2)) := h_absorb_geomC δ hδ_pos hδ_le_geomC
    have h_exp : (-(pointLoss / 2)) = -pointLoss / 2 := by ring
    rw [h_exp] at h1
    have hδn_leδ : dyadicDelta n ≤ δ := by
      have h : dyadicDelta n ≤ δ / 4 := hδn_le'
      linarith
    have h2 : δ^(-pointLoss / 2) ≤ (dyadicDelta n)^(-pointLoss / 2) :=
      Real.rpow_le_rpow_of_nonpos hδn_pos hδn_leδ (by linarith)
    exact le_trans h1 h2
  have h_geomK_absorb : K_geom_K ≤ (dyadicDelta n)^(-pointLoss) := by
    have h1 : K_geom_K ≤ δ^(-pointLoss) := h_absorb_geomK δ hδ_pos hδ_le_geomK
    have hδn_leδ : dyadicDelta n ≤ δ := by
      have h : dyadicDelta n ≤ δ / 4 := hδn_le'
      linarith
    have h2 : δ^(-pointLoss) ≤ (dyadicDelta n)^(-pointLoss) :=
      Real.rpow_le_rpow_of_nonpos hδn_pos hδn_leδ (by linarith)
    exact le_trans h1 h2

  -- Key scale comparison: δ ≤ 16 * δ_n
  have hδ_le_16δn : δ ≤ 16 * dyadicDelta n := by
    have h : δ / 4 < 4 * dyadicDelta n := hδn_lt'
    linarith

  -- δ_n ≤ δ (since δ_n ≤ δ/4 < δ)
  have hδn_leδ : dyadicDelta n ≤ δ := by
    have h : dyadicDelta n ≤ δ / 4 := hδn_le'
    linarith

  -- ======================================================================
  -- Step 2: S0 normalization of points
  -- ======================================================================
  let P' := S0 '' P
  have hP'_ball : P' ⊆ Metric.closedBall (0 : Plane) 1 := S0_image_ball hP_subset
  have hP'_unit : ∀ p ∈ P', 0 ≤ p 0 ∧ p 0 < 1 ∧ 0 ≤ p 1 ∧ p 1 < 1 := by
    intro p hp
    have h := S0_image_unitSquare hP_subset p hp
    exact ⟨h.1, by linarith [h.2.1], h.2.2.1, by linarith [h.2.2.2]⟩
  have hP'_sset : IsDeltaSSet δ' u ((Real.rpow δ (-εReg)) * (4 : ℝ)^u) P' :=
    S0_sset hReg.1
  have hP'_regular : IsSquareRootRegular δ' u
      ((Real.rpow δ (-εReg)) * (4 : ℝ)^u) (Real.rpow δ (-εReg)) P' :=
    scale_squareRootRegular hδ_pos hδ_le_one (le_of_lt (lt_trans hs_pos hst)) (Real.rpow_nonneg hδ_pos.le (-εReg))
      (fun {t C} h => S0_sset h)
      (fun r hr => by
        have h := S0_ncover (δ := 4 * r) (hδ_pos := by positivity) (P := P)
        have h4 : (4 * r) / 4 = r := by ring
        rw [h4] at h; exact h)
      hReg

  -- ======================================================================
  -- Step 3: Lower bound derivation from IsDeltaSSet
  --
  -- For C = δ^{-εReg}:
  --   Ncover(δ, E) ≥ 1/(C·δ^d) = δ^{-d+εReg}
  -- Since δ_n ≤ δ: Ncover(δ_n, E) ≥ Ncover(δ, E)
  -- Since δ ≤ 16·δ_n and exponent -d+εReg < 0:
  --   δ^{-d+εReg} ≥ (16·δ_n)^{-d+εReg} = 16^{-d+εReg} · δ_n^{-d+εReg}
  -- ======================================================================

  -- General helper: Ncover(δ_n, E) ≥ 16^{-d+εReg} · δ_n^{-d+εReg}
  let lower_bound_at_deltan (d : ℝ) (hd_pos : 0 < d) (hεReg_lt_d : εReg < d)
      {E : Set AffineLine} (hE : IsDeltaSSet δ d (Real.rpow δ (-εReg)) E) :
      ENNReal.ofReal ((16 : ℝ)^(-d + εReg) * (dyadicDelta n)^(-d + εReg)) ≤
      Ncover (dyadicDelta n) E := by
    have h_exp_neg : -d + εReg < 0 := by linarith
    have hC_pos : 0 < Real.rpow δ (-εReg) := Real.rpow_pos_of_pos hδ_pos _
    have h1 : ENNReal.ofReal (1 / (Real.rpow δ (-εReg) * δ^d)) ≤
        Ncover δ E :=
      DirecretisedFurstenbergEstimate.Phase2.sset_lower_cover_bound
        hδ_pos (le_of_lt hd_pos) hC_pos hE
    have h2 : (1 / (Real.rpow δ (-εReg) * δ^d)) = δ^(-d + εReg) := by
      have h_eq1 : Real.rpow δ (-εReg) * δ^d = δ^(-εReg + d) := by
        have h : δ^(-εReg + d) = δ^(-εReg) * δ^d := Real.rpow_add hδ_pos _ _
        exact h.symm
      rw [h_eq1]
      have h_eq2 : 1 / δ^(-εReg + d) = δ^(-(-εReg + d)) := by
        have h_neg : δ^(-(-εReg + d)) = (δ^(-εReg + d))⁻¹ :=
          Real.rpow_neg hδ_pos.le (-εReg + d)
        simpa [one_div] using h_neg.symm
      rw [h_eq2]
      have h_eq3 : -(-εReg + d) = -d + εReg := by ring
      rw [h_eq3]
    rw [h2] at h1
    have h5 : δ^(-d + εReg) ≥ (16 * dyadicDelta n)^(-d + εReg) := by
      have h6 : 0 < δ := hδ_pos
      have h7 : 0 < 16 * dyadicDelta n := by positivity
      have h8 : δ ≤ 16 * dyadicDelta n := hδ_le_16δn
      have h9 : (16 * dyadicDelta n)^(-d + εReg) ≤ δ^(-d + εReg) :=
        (Real.rpow_le_rpow_iff_of_neg h7 h6 h_exp_neg).mpr h8
      exact h9
    have h10 : (16 * dyadicDelta n)^(-d + εReg) =
        (16 : ℝ)^(-d + εReg) * (dyadicDelta n)^(-d + εReg) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    have h11 : ENNReal.ofReal ((16 : ℝ)^(-d + εReg) * (dyadicDelta n)^(-d + εReg)) ≤
        ENNReal.ofReal (δ^(-d + εReg)) := by
      have h5' : (16 : ℝ)^(-d + εReg) * (dyadicDelta n)^(-d + εReg) ≤ δ^(-d + εReg) := by
        rw [← h10]
        exact h5
      exact ENNReal.ofReal_le_ofReal h5'
    have hδnn : (dyadicDelta n).toNNReal ≤ δ.toNNReal :=
      (Real.toNNReal_le_toNNReal_iff_of_pos hδn_pos).mpr hδn_leδ
    have h12 : Ncover δ E ≤ Ncover (dyadicDelta n) E := by
      simpa [Ncover] using Metric.externalCoveringNumber_anti hδnn
    exact le_trans h11 (le_trans h1 h12)

  -- Tube family Ncover lower bound (per point)
  have h_tube_ncover_lower : ∀ (p : Plane) (hp : p ∈ P),
      ENNReal.ofReal ((16 : ℝ)^(-s + εReg) * (dyadicDelta n)^(-s + εReg)) ≤
      Ncover (dyadicDelta n) (tubeFamily p hp) := by
    intro p hp
    exact lower_bound_at_deltan s hs_pos hεReg_lt_s (hTubes p hp)

  -- Point set Ncover lower bound (same pattern for dimension u)
  have hεReg_lt_u : εReg < u := lt_trans hεReg_lt_s hst
  have h_point_ncover_lower :
      ENNReal.ofReal ((16 : ℝ)^(-u + εReg) * (dyadicDelta n)^(-u + εReg)) ≤
      Ncover (dyadicDelta n) P := by
    have h_exp_neg : -u + εReg < 0 := by
      have h_eps : εReg < u := hεReg_lt_u
      have h2 : -u + εReg < -u + u := by gcongr
      have h3 : -u + u = (0 : ℝ) := by ring
      rw [h3] at h2
      exact h2
    have hC_pos2 : 0 < Real.rpow δ (-εReg) := Real.rpow_pos_of_pos hδ_pos _
    have h1 : ENNReal.ofReal (1 / (Real.rpow δ (-εReg) * δ^u)) ≤
        Ncover δ P :=
      DirecretisedFurstenbergEstimate.Phase2.sset_lower_cover_bound
        hδ_pos (le_of_lt (lt_trans hs_pos hst)) hC_pos2 hReg.1
    have h2 : (1 / (Real.rpow δ (-εReg) * δ^u)) = δ^(-u + εReg) := by
      have h_eq1 : Real.rpow δ (-εReg) * δ^u = δ^(-εReg + u) := by
        have h : δ^(-εReg + u) = δ^(-εReg) * δ^u := Real.rpow_add hδ_pos _ _
        exact h.symm
      rw [h_eq1]
      have h_eq2 : 1 / δ^(-εReg + u) = δ^(-(-εReg + u)) := by
        have h_neg : δ^(-(-εReg + u)) = (δ^(-εReg + u))⁻¹ :=
          Real.rpow_neg hδ_pos.le (-εReg + u)
        simpa [one_div] using h_neg.symm
      rw [h_eq2]
      have h_eq3 : -(-εReg + u) = -u + εReg := by ring
      rw [h_eq3]
    rw [h2] at h1
    have h5 : δ^(-u + εReg) ≥ (16 * dyadicDelta n)^(-u + εReg) := by
      have h6 : 0 < δ := hδ_pos
      have h7 : 0 < 16 * dyadicDelta n := by positivity
      have h8 : δ ≤ 16 * dyadicDelta n := hδ_le_16δn
      have h_exp_neg2 : -u + εReg < 0 := by
        have h_eps : εReg < u := hεReg_lt_u
        have h2 : -u + εReg < -u + u := by gcongr
        have h3 : -u + u = (0 : ℝ) := by ring
        rw [h3] at h2
        exact h2
      have h9 : (16 * dyadicDelta n)^(-u + εReg) ≤ δ^(-u + εReg) :=
        (Real.rpow_le_rpow_iff_of_neg h7 h6 h_exp_neg2).mpr h8
      exact h9
    have h10 : (16 * dyadicDelta n)^(-u + εReg) =
        (16 : ℝ)^(-u + εReg) * (dyadicDelta n)^(-u + εReg) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    have h11 : ENNReal.ofReal ((16 : ℝ)^(-u + εReg) * (dyadicDelta n)^(-u + εReg)) ≤
        ENNReal.ofReal (δ^(-u + εReg)) := by
      have h5' : (16 : ℝ)^(-u + εReg) * (dyadicDelta n)^(-u + εReg) ≤ δ^(-u + εReg) := by
        rw [← h10]
        exact h5
      exact ENNReal.ofReal_le_ofReal h5'
    have hδnn2 : (dyadicDelta n).toNNReal ≤ δ.toNNReal :=
      (Real.toNNReal_le_toNNReal_iff_of_pos hδn_pos).mpr hδn_leδ
    have h12 : Ncover δ P ≤ Ncover (dyadicDelta n) P := by
      simpa [Ncover] using Metric.externalCoveringNumber_anti hδnn2
    exact le_trans h11 (le_trans h1 h12)

  -- ======================================================================
  -- Step 4: Point extraction at scale 4*δ_n
  --
  -- Extract P_fin ⊆ P that is 4δ_n-separated and 4δ_n-covers P.
  -- S0 scales by 1/4, so S0(P_fin) is δ_n-separated and δ_n-covers S0(P).
  -- ======================================================================

  let r_point : ℝ := 4 * dyadicDelta n
  have hr_point_pos : 0 < r_point := by positivity
  have hr_point_leδ : r_point ≤ δ := by
    have h : dyadicDelta n ≤ δ / 4 := hδn_le'
    linarith
  have hP_tb : TotallyBounded P := by
    have h_ball_compact : IsCompact (Metric.closedBall (0 : Plane) 1) := by exact isCompact_closedBall 0 1
    have h_ball_tb : TotallyBounded (Metric.closedBall (0 : Plane) 1) :=
      h_ball_compact.totallyBounded
    intro d hd
    rcases h_ball_tb d hd with ⟨t, ht_fin, hcover⟩
    exact ⟨t, ht_fin, subset_trans hP_subset hcover⟩
  have hP_nonempty : P.Nonempty := hReg.1.1

  have hr_point_nn_pos : 0 < r_point.toNNReal := by
    simp [r_point, NNReal.coe_pos] <;> positivity
  rcases finite_separated_subset_of_totallyBounded
    (δ := r_point.toNNReal) hr_point_nn_pos hP_tb hP_nonempty
    with ⟨P_fin_set, hP_fin_finite, hP_fin_sub, hP_fin_sep, hP_fin_cover, hP_fin_card_ge⟩

  let P_fin : Finset Plane := Set.Finite.toFinset hP_fin_finite
  have hP_fin_coe : (P_fin : Set Plane) = P_fin_set := by
    exact Set.Finite.coe_toFinset hP_fin_finite
  have hP_mem : ∀ p ∈ P_fin, p ∈ P := by
    intro p hp
    have hp' : p ∈ P_fin_set := by
      rw [←hP_fin_coe] <;> exact hp
    exact hP_fin_sub hp'
  have hP_fin_nonempty : P_fin.Nonempty := by
    have h : P_fin_set.Nonempty := hP_fin_cover.nonempty hP_nonempty
    simpa [P_fin, hP_fin_coe] using h

  -- S0(P_fin) is δ_n-separated (since P_fin is 4δ_n-separated, S0 scales by 1/4)
  have hS0_sep : Set.Pairwise (S0 '' (P_fin : Set Plane))
      (fun x y => dyadicDelta n ≤ dist x y) := by
    intro x hx y hy hne
    rcases hx with ⟨p, hp, rfl⟩
    rcases hy with ⟨q, hq, rfl⟩
    have hpq : p ≠ q := by
      intro h; rw [h] at hne; exact hne rfl
    have h_sep : r_point ≤ dist p q := by
      have h_lt : (r_point.toNNReal : ENNReal) < edist p q := hP_fin_sep
        (by rw [←hP_fin_coe] <;> exact hp)
        (by rw [←hP_fin_coe] <;> exact hq) hpq
      have h_eq1 : (r_point.toNNReal : ENNReal) = ENNReal.ofReal r_point := by
        have h_nonneg : 0 ≤ r_point := by positivity
        simp [ENNReal.ofReal, h_nonneg]
        <;> rfl
      have h_eq2 : edist p q = ENNReal.ofReal (dist p q) := edist_dist p q
      rw [h_eq1, h_eq2] at h_lt
      have h_real_lt : r_point < dist p q := by
        by_contra h
        have h' : dist p q ≤ r_point := by linarith
        have h'' : ENNReal.ofReal (dist p q) ≤ ENNReal.ofReal r_point :=
          ENNReal.ofReal_le_ofReal h'
        exact not_lt.mpr h'' h_lt
      linarith
    have h_dist : dist (S0 p) (S0 q) = (1 / 4 : ℝ) * dist p q := S0_dist p q
    rw [h_dist]
    have h4 : (1 / 4 : ℝ) * dist p q ≥ (1 / 4 : ℝ) * r_point := by gcongr
    have h5 : (1 / 4 : ℝ) * r_point = dyadicDelta n := by
      dsimp only [r_point] <;> ring
    linarith

  -- S0(P_fin) δ_n-covers S0(P) (since P_fin 4δ_n-covers P, S0 scales by 1/4)
  have hS0_cover : Metric.IsCover (dyadicDelta n).toNNReal P' (S0 '' (P_fin : Set Plane)) := by
    intro x hx
    rcases hx with ⟨p, hp, rfl⟩
    have hcover1 : P ⊆ ⋃ q ∈ P_fin_set, Metric.closedBall q (↑r_point.toNNReal : ℝ) :=
      hP_fin_cover.subset_iUnion_closedBall
    have h_rpoint_coe : (↑r_point.toNNReal : ℝ) = r_point := by
      simp [NNReal.coe_mk] <;> linarith
    have hcover2 : P ⊆ ⋃ q ∈ P_fin_set, Metric.closedBall q r_point := by
      rw [h_rpoint_coe] at hcover1 <;> exact hcover1
    have hp_in : p ∈ P := hp
    have h2 : p ∈ ⋃ q ∈ P_fin_set, Metric.closedBall q r_point := hcover2 hp_in
    rcases Set.mem_iUnion₂.mp h2 with ⟨q, hq, hball⟩
    have hq' : q ∈ (P_fin : Set Plane) := by
      rw [hP_fin_coe] <;> exact hq
    have h4 : dist p q ≤ r_point := by
      simpa [Metric.mem_closedBall] using hball
    have h5 : dist (S0 p) (S0 q) ≤ dyadicDelta n := by
      have h6 : dist (S0 p) (S0 q) = (1 / 4 : ℝ) * dist p q := S0_dist p q
      rw [h6]
      have h7 : (1 / 4 : ℝ) * dist p q ≤ (1 / 4 : ℝ) * r_point := by gcongr
      have h8 : (1 / 4 : ℝ) * r_point = dyadicDelta n := by
        dsimp only [r_point] <;> ring
      rw [h8] at h7 <;> linarith
    have h9 : edist (S0 p) (S0 q) ≤ (dyadicDelta n).toNNReal := by
      have h10 : edist (S0 p) (S0 q) = ENNReal.ofReal (dist (S0 p) (S0 q)) := edist_dist _ _
      rw [h10]
      exact ENNReal.ofReal_le_ofReal h5
    exact ⟨S0 q, Set.mem_image_of_mem S0 hq', h9⟩

  -- Cardinality lower bound: |P_fin| ≥ Ncover(4δ_n, P) ≥ Ncover(δ, P) ≥ δ^{-u+εReg}
  -- Then δ ≤ 16δ_n and negative exponent gives ≥ 16^{-u+εReg} * δ_n^{-u+εReg}
  have hP_fin_card_lower : (P_fin.card : ENNReal) ≥
      ENNReal.ofReal ((16 : ℝ)^(-u + εReg) * (dyadicDelta n)^(-u + εReg)) := by
    have h1 : Ncover r_point P ≤ (P_fin.card : ENNReal) := by
      have h2 : P_fin_set.encard = (P_fin.card : ENat) := by
        have h3 : P_fin_set = (P_fin : Set Plane) := hP_fin_coe.symm
        rw [h3] <;> simp
      have h4 : (Ncover r_point P : ENNReal) ≤ (P_fin_set.encard : ENNReal) := by
        exact_mod_cast hP_fin_card_ge
      rw [h2] at h4
      exact h4
    have h2 : Ncover δ P ≤ Ncover r_point P := by
      have h3 : r_point ≤ δ := hr_point_leδ
      exact ncover_antitone h3 (by positivity)
    have hC_pos2 : 0 < Real.rpow δ (-εReg) := Real.rpow_pos_of_pos hδ_pos _
    have h3 : ENNReal.ofReal (δ^(-u + εReg)) ≤ Ncover δ P := by
      have h_raw := DirecretisedFurstenbergEstimate.Phase2.sset_lower_cover_bound
        hδ_pos (le_of_lt (lt_trans hs_pos hst)) hC_pos2 hReg.1
      have h_eq : (1 / (Real.rpow δ (-εReg) * δ^u)) = δ^(-u + εReg) := by
        have h1 : Real.rpow δ (-εReg) * δ^u = Real.rpow δ (-εReg + u) :=
          (Real.rpow_add hδ_pos (-εReg) u).symm
        rw [h1]
        have h2 : 1 / Real.rpow δ (-εReg + u) = (Real.rpow δ (-εReg + u))⁻¹ := by
          simp [one_div]
        rw [h2]
        have h3 : (Real.rpow δ (-εReg + u))⁻¹ = Real.rpow δ (-(-εReg + u)) :=
          (Real.rpow_neg hδ_pos.le (-εReg + u)).symm
        rw [h3]
        have h4 : -(-εReg + u) = -u + εReg := by ring
        rw [h4]
        <;> rfl
      rw [h_eq] at h_raw
      exact h_raw
    have h4 : δ^(-u + εReg) ≥ (16 : ℝ)^(-u + εReg) * (dyadicDelta n)^(-u + εReg) := by
      have h_exp_neg : -u + εReg < 0 := by
        have h_eps : εReg < u := hεReg_lt_u
        have h2 : -u + εReg < -u + u := by gcongr
        have h3 : -u + u = (0 : ℝ) := by ring
        rw [h3] at h2
        exact h2
      have h5 : δ ≤ 16 * dyadicDelta n := hδ_le_16δn
      have h6 : 0 < 16 * dyadicDelta n := by positivity
      have h7 : (16 * dyadicDelta n)^(-u + εReg) ≤ δ^(-u + εReg) :=
        (Real.rpow_le_rpow_iff_of_neg h6 hδ_pos h_exp_neg).mpr h5
      have h8 : (16 * dyadicDelta n)^(-u + εReg) =
          (16 : ℝ)^(-u + εReg) * (dyadicDelta n)^(-u + εReg) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
      rw [h8] at h7
      exact h7
    have h9 : ENNReal.ofReal ((16 : ℝ)^(-u + εReg) * (dyadicDelta n)^(-u + εReg)) ≤
        ENNReal.ofReal (δ^(-u + εReg)) := ENNReal.ofReal_le_ofReal h4
    exact le_trans h9 (le_trans h3 (le_trans h2 h1))

  -- ======================================================================
  -- Step 5: Tube extraction at scale δ
  -- For each p ∈ P_fin, extract finite δ-separated G(p) ⊆ tubeFamily(p)
  -- with S-set retention and cardinality lower bound.
  -- ======================================================================

  -- Boundedness: all lines have |slope|≤1, |intercept|≤3, so the set is bounded
  have h_chart3 : ∀ (p : Plane) (hp : p ∈ P) (ℓ : AffineLine),
      ℓ ∈ tubeFamily p hp →
      ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ := by
    intro p hp ℓ hℓ
    exact boundedChart_of_inChart_offset (hChart p hp ℓ hℓ) (hOffset p hp ℓ hℓ)

  have hTubes_bdd : ∀ (p : Plane) (hp : p ∈ P),
      Bornology.IsBounded (tubeFamily p hp) := by
    intro p hp
    exact FrontendHelpers.affineLine_family_bounded (h_chart3 p hp)

  -- Extract finite separated tube family with S-set retention
  have h_extract_main : ∀ (p : Plane) (hp : p ∈ P_fin),
      ∃ (G : Finset AffineLine),
        (G : Set AffineLine) ⊆ tubeFamily p (hP_mem p hp) ∧
        (∀ x ∈ G, ∀ y ∈ G, x ≠ y → δ ≤ dist x y) ∧
        Metric.IsCover δ.toNNReal (tubeFamily p (hP_mem p hp)) (G : Set AffineLine) ∧
        IsDeltaSSet δ s ((Real.rpow δ (-εReg)) * K_pack) (G : Set AffineLine) ∧
        (G.card : ENNReal) ≥ ENNReal.ofReal (δ ^ (-s + εReg)) := by
    intro p hp
    let F := tubeFamily p (hP_mem p hp)
    have hF_sset : IsDeltaSSet δ s (Real.rpow δ (-εReg)) F := hTubes p (hP_mem p hp)
    have hF_bdd : Bornology.IsBounded F := hTubes_bdd p (hP_mem p hp)
    rcases finite_separated_tube_sset hδ_pos hF_sset hF_bdd with
      ⟨T', hT'_fin, hT'_sub, hT'_sep, hT'_cover, hT'_sset⟩
    let G : Finset AffineLine := hT'_fin.toFinset
    have hG_coe : (G : Set AffineLine) = T' := Set.Finite.coe_toFinset hT'_fin
    have h_sub : (G : Set AffineLine) ⊆ F := by rw [hG_coe]; exact hT'_sub
    have h_sep : ∀ x ∈ G, ∀ y ∈ G, x ≠ y → δ ≤ dist x y := by
      intro x hx y hy hxy
      have hx' : x ∈ T' := by rw [←hG_coe]; exact hx
      have hy' : y ∈ T' := by rw [←hG_coe]; exact hy
      exact hT'_sep x hx' y hy' hxy
    have h_cover : Metric.IsCover δ.toNNReal F (G : Set AffineLine) := by
      rw [hG_coe]; exact hT'_cover
    have h_sset : IsDeltaSSet δ s ((Real.rpow δ (-εReg)) * K_pack) (G : Set AffineLine) := by
      rw [hG_coe]; exact hT'_sset
    have h_lower_raw : ENNReal.ofReal (1 / (Real.rpow δ (-εReg) * δ^s)) ≤
        Ncover δ F :=
      DirecretisedFurstenbergEstimate.Phase2.sset_lower_cover_bound
        hδ_pos (le_of_lt hs_pos) (Real.rpow_pos_of_pos hδ_pos _) hF_sset
    have h_eq : (1 / (Real.rpow δ (-εReg) * δ^s)) = δ^(-s + εReg) := by
      have h1 : Real.rpow δ (-εReg) * δ^s = δ^(-εReg + s) :=
        (Real.rpow_add hδ_pos (-εReg) s).symm
      rw [h1]
      have h2 : 1 / δ^(-εReg + s) = δ^(-(-εReg + s)) := by
        have h_neg : δ^(-(-εReg + s)) = (δ^(-εReg + s))⁻¹ :=
          Real.rpow_neg hδ_pos.le (-εReg + s)
        simpa [one_div] using h_neg.symm
      rw [h2]
      have h3 : -(-εReg + s) = -s + εReg := by ring
      rw [h3] <;> rfl
    have h_lower : ENNReal.ofReal (δ ^ (-s + εReg)) ≤ Ncover δ F := by
      rw [←h_eq] <;> exact h_lower_raw
    have h_ge : Ncover δ F ≤ (G.card : ENNReal) := by
      have h1 : Metric.externalCoveringNumber δ.toNNReal F ≤ T'.encard :=
        Metric.IsCover.externalCoveringNumber_le_encard hT'_cover
      have h2 : (T'.encard : ENNReal) = (G.card : ENNReal) := by
        rw [←hG_coe]; simp
      have h3 : (Metric.externalCoveringNumber δ.toNNReal F : ENNReal) ≤ (T'.encard : ENNReal) := by exact_mod_cast h1
      rw [h2] at h3; exact h3
    have h_card : (G.card : ENNReal) ≥ ENNReal.ofReal (δ ^ (-s + εReg)) :=
      le_trans h_lower h_ge
    exact ⟨G, h_sub, h_sep, h_cover, h_sset, h_card⟩

  let G (p : Plane) (hp : p ∈ P_fin) : Finset AffineLine :=
    Classical.choose (h_extract_main p hp)

  have hG_spec : ∀ (p : Plane) (hp : p ∈ P_fin),
      (G p hp : Set AffineLine) ⊆ tubeFamily p (hP_mem p hp) ∧
      (∀ x ∈ G p hp, ∀ y ∈ G p hp, x ≠ y → δ ≤ dist x y) ∧
      Metric.IsCover δ.toNNReal (tubeFamily p (hP_mem p hp)) (G p hp : Set AffineLine) ∧
      IsDeltaSSet δ s ((Real.rpow δ (-εReg)) * K_pack) (G p hp : Set AffineLine) ∧
      (G p hp).card ≥ ENNReal.ofReal (δ ^ (-s + εReg)) := by
    intro p hp
    exact Classical.choose_spec (h_extract_main p hp)

  -- ======================================================================
  -- Step 6: S0_line transfer + snapping through S0(p)
  -- Scale δ' = δ/4 satisfies δ_n ≤ δ' < 4δ_n.
  -- ======================================================================

  let δ' := δ / 4
  have hδ'_pos : 0 < δ' := by positivity
  have hδ'_le_one : δ' ≤ 1 := by linarith
  have hδn_leδ' : dyadicDelta n ≤ δ' := hδn_le'
  have hδ'_lt4δn : δ' < 4 * dyadicDelta n := hδn_lt'
  have hδ'_le4δn : δ' ≤ 4 * dyadicDelta n := by linarith

  let S0G (p : Plane) (hp : p ∈ P_fin) : Finset AffineLine :=
    (G p hp).image S0_line

  -- S0_line is injective
  have hS0_line_inj : Function.Injective S0_line :=
    S0_line_antilipschitz.injective

  -- S0G separation at δ' (S0_line is 4-antilipschitz: dist ≥ 1/4 * original)
  have hS0G_sep : ∀ (p : Plane) (hp : p ∈ P_fin),
      ∀ ℓ1 ∈ S0G p hp, ∀ ℓ2 ∈ S0G p hp, ℓ1 ≠ ℓ2 → δ' ≤ dist ℓ1 ℓ2 := by
    intro p hp ℓ1 hℓ1 ℓ2 hℓ2 hne
    rcases Finset.mem_image.mp hℓ1 with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hℓ2 with ⟨y, hy, rfl⟩
    have hxy : x ≠ y := by
      intro h; rw [h] at hne; exact hne rfl
    have h_sep : δ ≤ dist x y := (hG_spec p hp).2.1 x hx y hy hxy
    have h1 : (1 / 4 : ℝ) * dist x y ≤ dist (S0_line x) (S0_line y) :=
      S0_line_bilipschitz.1
    have h2 : δ' = (1 / 4 : ℝ) * δ := by dsimp only [δ']; ring
    rw [h2]
    have h3 : (1 / 4 : ℝ) * δ ≤ (1 / 4 : ℝ) * dist x y :=
      mul_le_mul_of_nonneg_left h_sep (by norm_num)
    exact le_trans h3 h1

  -- S0G S-set at scale δ'
  have hS0G_sset : ∀ (p : Plane) (hp : p ∈ P_fin),
      IsDeltaSSet δ' s
        ((Real.rpow δ (-εReg)) * K_pack * (8 : ℝ)^s * (262144 : ℝ)^4)
        (S0G p hp : Set AffineLine) := by
    intro p hp
    have h_chart : ∀ ℓ ∈ (G p hp : Set AffineLine),
        ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ := by
      intro ℓ hℓ
      have hℓ' : ℓ ∈ tubeFamily p (hP_mem p hp) := (hG_spec p hp).1 hℓ
      exact h_chart3 p (hP_mem p hp) ℓ hℓ'
    have h_set_eq : (S0G p hp : Set AffineLine) = S0_line '' (G p hp : Set AffineLine) := by
      ext x; simp [S0G] <;> aesop
    rw [h_set_eq]
    exact S0_line_ncover_forward hδ_pos (by linarith)
      (mul_pos (Real.rpow_pos_of_pos hδ_pos _) (by exact_mod_cast K_pack_pos))
      (hG_spec p hp).2.2.2.1 h_chart

  -- S0G near condition at δ'
  have hS0G_near : ∀ (p : Plane) (hp : p ∈ P_fin) (ℓ : AffineLine),
      ℓ ∈ S0G p hp → S0 p ∈ Metric.cthickening δ' ℓ.1 := by
    intro p hp ℓ hℓ
    rcases Finset.mem_image.mp hℓ with ⟨x, hx, rfl⟩
    have hx' : x ∈ tubeFamily p (hP_mem p hp) := (hG_spec p hp).1 hx
    have h_near_orig : p ∈ Metric.cthickening δ x.1 := hIncidence p (hP_mem p hp) x hx'
    exact (S0_incidence hδ_pos.le).mp h_near_orig

  -- S0G slope and v0 conditions
  have hS0G_slope : ∀ (p : Plane) (hp : p ∈ P_fin) (ℓ : AffineLine),
      ℓ ∈ S0G p hp → |(affineLineSlopeIntercept ℓ).1| ≤ 1 := by
    intro p hp ℓ hℓ
    rcases Finset.mem_image.mp hℓ with ⟨x, hx, rfl⟩
    have hx' : x ∈ tubeFamily p (hP_mem p hp) := (hG_spec p hp).1 hx
    have hchart : InStandardChart.inChart x := hChart p (hP_mem p hp) x hx'
    have h'S0chart : InStandardChart.inChart (S0_line x) := S0_line_inChart hchart
    exact inChart_slope_bound h'S0chart

  have hS0G_v0 : ∀ (p : Plane) (hp : p ∈ P_fin) (ℓ : AffineLine),
      ℓ ∈ S0G p hp → (LemmaE.getDirV ℓ) 0 ≠ 0 := by
    intro p hp ℓ hℓ
    rcases Finset.mem_image.mp hℓ with ⟨x, hx, rfl⟩
    have hchart : InStandardChart.inChart x := hChart p (hP_mem p hp) x
      ((hG_spec p hp).1 hx)
    have h'S0chart : InStandardChart.inChart (S0_line x) := S0_line_inChart hchart
    exact inChart_v0_ne_zero h'S0chart

  -- Snapped tube families
  let snapped (p : Plane) (hp : p ∈ P_fin) : Finset (DyadicTube n) :=
    (S0G p hp).image (fun ℓ => snapToTubeThroughPoint n ℓ (S0 p))

  -- Snapped S-set at δ_n
  have hSnapped_sset : ∀ (p : Plane) (hp : p ∈ P_fin),
      IsDeltaSSet (dyadicDelta n) s
        (K_snap s *
          ((Real.rpow δ (-εReg)) * K_pack * (8 : ℝ)^s * (262144 : ℝ)^4))
        (snapped p hp : Set (DyadicTube n)) := by
    intro p hp
    have h_set_eq : (snapped p hp : Set (DyadicTube n)) =
        (fun ℓ => snapToTubeThroughPoint n ℓ (S0 p)) '' (S0G p hp : Set AffineLine) := by
      ext x; simp [snapped] <;> aesop
    rw [h_set_eq]
    let C_input : ℝ := (Real.rpow δ (-εReg)) * K_pack * (8 : ℝ)^s * (262144 : ℝ)^4
    have hC_input_pos : 0 < C_input := by
      dsimp only [C_input]
      have h1 : 0 < Real.rpow δ (-εReg) := Real.rpow_pos_of_pos hδ_pos _
      have h2 : (0 : ℝ) < (K_pack : ℝ) := by exact_mod_cast K_pack_pos
      have h3 : (0 : ℝ) < (8 : ℝ)^s := by positivity
      have h4 : (0 : ℝ) < (262144 : ℝ)^4 := by positivity
      exact mul_pos (mul_pos (mul_pos h1 h2) h3) h4
    exact snap_sset_transfer (n := n) (δ := δ') (δ_n := dyadicDelta n) (s := s) (C := C_input)
      hδ'_pos hδ'_le_one hδn_pos rfl
      hδn_leδ' hδ'_le4δn (show 0 ≤ s from le_of_lt hs_pos)
      hC_input_pos
      (hS0G_sset p hp) (S0 p)
      (S0_image_ball hP_subset (Set.mem_image_of_mem S0 (hP_mem p hp)))
      (fun ℓ hℓ => hS0G_v0 p hp ℓ hℓ)
      (fun ℓ hℓ => hS0G_slope p hp ℓ hℓ)
      (fun ℓ hℓ => hS0G_near p hp ℓ hℓ)

  -- Snapped incidence, strip, slope, provenance
  have hSnapped_inc : ∀ (p : Plane) (hp : p ∈ P_fin) (T : DyadicTube n),
      T ∈ snapped p hp → S0 p ∈ T.toSet := by
    intro p hp T hT
    rcases Finset.mem_image.mp hT with ⟨ℓ, hℓ, rfl⟩
    exact snapToTubeThroughPoint_incidence

  have hSnapped_strip : ∀ (p : Plane) (hp : p ∈ P_fin) (T : DyadicTube n),
      T ∈ snapped p hp → -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ) := by
    intro p hp T hT
    rcases Finset.mem_image.mp hT with ⟨ℓ, hℓ, rfl⟩
    exact snapToTubeThroughPoint_a_strip (hS0G_slope p hp ℓ hℓ)

  have hSnapped_slope : ∀ (p : Plane) (hp : p ∈ P_fin) (T : DyadicTube n),
      T ∈ snapped p hp → |T.slope| ≤ 1 := by
    intro p hp T hT
    rcases Finset.mem_image.mp hT with ⟨ℓ, hℓ, rfl⟩
    exact snapToTubeThroughPoint_slope_bound (hS0G_slope p hp ℓ hℓ)

  have hSnapped_provenance : ∀ (p : Plane) (hp : p ∈ P_fin) (T : DyadicTube n),
      T ∈ snapped p hp →
      ∃ (p_orig : Plane) (hp_orig : p_orig ∈ P)
        (ℓ : AffineLine) (hℓ : ℓ ∈ tubeFamily p_orig hp_orig),
        T = snapToTubeThroughPoint n (S0_line ℓ) (S0 p_orig) := by
    intro p hp T hT
    rcases Finset.mem_image.mp hT with ⟨ℓ, hℓ, rfl⟩
    rcases Finset.mem_image.mp hℓ with ⟨x, hx, rfl⟩
    have hx' : x ∈ tubeFamily p (hP_mem p hp) := (hG_spec p hp).1 hx
    exact ⟨p, hP_mem p hp, x, hx', rfl⟩

  -- ======================================================================
  -- Step 7: Common exact M via dyadic pigeonhole
  -- ======================================================================

  -- Bound each snapped family cardinality by 2^K_pigeon
  let K_pigeon : ℕ := 2 * n + 4
  let aSet : Finset ℤ := Finset.Ico (-(2^n : ℤ)) (2^n : ℤ)
  let bSet : Finset ℤ := Finset.Ico (-(3*2^n : ℤ)) (3*2^n : ℤ)
  let allTubes : Finset (DyadicTube n) :=
    aSet.biUnion (fun a => bSet.image (fun b => (⟨a, b⟩ : DyadicTube n)))

  have h_snapped_sub_all : ∀ (p : Plane) (hp : p ∈ P_fin),
      snapped p hp ⊆ allTubes := by
    intro p hp T hT
    rcases Finset.mem_image.mp hT with ⟨ℓ, hℓ, rfl⟩
    let T' := snapToTubeThroughPoint n ℓ (S0 p)
    have h_strip : -(2 ^ n : ℤ) ≤ T'.a ∧ T'.a < (2 ^ n : ℤ) :=
      snapToTubeThroughPoint_a_strip (hS0G_slope p hp ℓ hℓ)
    have h_inc : S0 p ∈ T'.toSet := snapToTubeThroughPoint_incidence
    have h_slope : |T'.slope| ≤ 1 :=
      snapToTubeThroughPoint_slope_bound (hS0G_slope p hp ℓ hℓ)
    have h_b_bound : |T'.intercept| < 3 := by
      have h1 : |(S0 p) 1 - T'.slope * (S0 p) 0 - T'.intercept| ≤ dyadicDelta n := h_inc
      have h2 : 0 ≤ (S0 p) 0 := (hP'_unit (S0 p) (Set.mem_image_of_mem S0 (hP_mem p hp))).1
      have h3 : (S0 p) 0 < 1 := (hP'_unit (S0 p) (Set.mem_image_of_mem S0 (hP_mem p hp))).2.1
      have h4 : 0 ≤ (S0 p) 1 := (hP'_unit (S0 p) (Set.mem_image_of_mem S0 (hP_mem p hp))).2.2.1
      have h5 : (S0 p) 1 < 1 := (hP'_unit (S0 p) (Set.mem_image_of_mem S0 (hP_mem p hp))).2.2.2
      have h6 : |T'.intercept| ≤ (S0 p) 1 + |T'.slope| * (S0 p) 0 + dyadicDelta n := by
        let x := (S0 p) 1 - T'.slope * (S0 p) 0
        let y := (S0 p) 1 - T'.slope * (S0 p) 0 - T'.intercept
        have h_eq : T'.intercept = x - y := by
          dsimp only [x, y] <;> ring
        have h_tri1 : |T'.intercept| ≤ |x| + |y| := by
          rw [h_eq]
          have h_abs : |x - y| ≤ |x| + |y| := by
            calc |x - y|
              = |x + (-y)| := by ring_nf
            _ ≤ |x| + |(-y)| := by exact real_abs_add x (-y)
            _ = |x| + |y| := by simp
          exact h_abs
        have h_tri2 : |x| ≤ (S0 p) 1 + |T'.slope * (S0 p) 0| := by
          have h : |x| ≤ |(S0 p) 1| + |T'.slope * (S0 p) 0| := by
            dsimp only [x] <;> exact real_abs_sub ((S0 p).ofLp 1) (T'.slope * (S0 p).ofLp 0)
          have h' : |(S0 p) 1| = (S0 p) 1 := by rw [abs_of_nonneg h4]
          rw [h'] at h
          exact h
        have h_abs_mul : |T'.slope * (S0 p) 0| = |T'.slope| * (S0 p) 0 := by
          rw [abs_mul, abs_of_nonneg h2]
        have h_y_bound : |y| ≤ dyadicDelta n := by
          dsimp only [y] <;> exact h1
        linarith [h_tri1, h_tri2, h_abs_mul, h_y_bound]
      have h7 : dyadicDelta n ≤ 1 / 4 := by
        have h : dyadicDelta n ≤ δ' := hδn_le'
        have h9 : δ' ≤ 1 / 4 := by dsimp only [δ']; linarith
        linarith
      have h_final : (S0 p) 1 + |T'.slope| * (S0 p) 0 + dyadicDelta n < 3 := by
        have h_s1 : (S0 p) 1 < 1 := h5
        have h_s0 : (S0 p) 0 ≤ 1 := by linarith [h3]
        have h_sl : |T'.slope| ≤ 1 := h_slope
        have h_d : dyadicDelta n ≤ 1 / 4 := h7
        have h : (S0 p) 1 + |T'.slope| * (S0 p) 0 + dyadicDelta n ≤ 1 + 1 * 1 + 1 / 4 := by
          gcongr <;> linarith
        linarith
      have h_goal : |T'.intercept| < 3 := by
        calc |T'.intercept|
          ≤ (S0 p) 1 + |T'.slope| * (S0 p) 0 + dyadicDelta n := h6
        _ < 3 := h_final
      exact h_goal
    have h_ib : |(T'.b : ℝ)| < (3 : ℝ) * (2 ^ n : ℝ) := by
      have h_eq : T'.intercept = (T'.b : ℝ) * dyadicDelta n := by
        simp [DyadicTube.intercept] <;> ring
      rw [h_eq] at h_b_bound
      have hδn_pos' : 0 < dyadicDelta n := hδn_pos
      have h9 : |(T'.b : ℝ) * dyadicDelta n| = |(T'.b : ℝ)| * dyadicDelta n := by
        rw [abs_mul, abs_of_pos hδn_pos]
      rw [h9] at h_b_bound
      have h10 : |(T'.b : ℝ)| * dyadicDelta n < 3 := h_b_bound
      have h11 : (3 : ℝ) / dyadicDelta n = (3 : ℝ) * (2 ^ n : ℝ) := by
        have h12 : dyadicDelta n * (2 ^ n : ℝ) = 1 := by
          simp [dyadicDelta] <;> field_simp <;> ring
        field_simp [hδn_pos.ne'] <;> linarith
      have h13 : |(T'.b : ℝ)| < (3 : ℝ) / dyadicDelta n := by
        calc |(T'.b : ℝ)|
          = (|(T'.b : ℝ)| * dyadicDelta n) / dyadicDelta n := by field_simp [hδn_pos.ne'] <;> ring
        _ < 3 / dyadicDelta n := by gcongr
      rw [h11] at h13
      exact h13
    have ha_in : T'.a ∈ aSet := by
      simpa [aSet, Finset.mem_Ico] using h_strip
    have hb_in : T'.b ∈ bSet := by
      have h10 : |(T'.b : ℝ)| < (3 : ℝ) * (2 ^ n : ℝ) := h_ib
      have h11 : -(3 * (2 ^ n : ℤ)) ≤ T'.b := by
        have h12 : -(3 : ℝ) * (2 ^ n : ℝ) ≤ (T'.b : ℝ) := by
          linarith [abs_lt.mp h10]
        exact_mod_cast h12
      have h13 : T'.b < 3 * (2 ^ n : ℤ) := by
        have h14 : (T'.b : ℝ) < (3 : ℝ) * (2 ^ n : ℝ) := by
          linarith [abs_lt.mp h10]
        exact_mod_cast h14
      simpa [bSet, Finset.mem_Ico] using ⟨h11, h13⟩
    exact Finset.mem_biUnion.mpr ⟨T'.a, ha_in, Finset.mem_image.mpr ⟨T'.b, hb_in, rfl⟩⟩

  have h_card_upper : ∀ (p : Plane) (hp : p ∈ P_fin),
      (snapped p hp).card ≤ 2 ^ K_pigeon := by
    intro p hp
    have h1 : (snapped p hp).card ≤ allTubes.card := Finset.card_le_card (h_snapped_sub_all p hp)
    have h2 : allTubes.card ≤ aSet.card * bSet.card := by
      have h_sub : allTubes ⊆ (aSet ×ˢ bSet).image (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : DyadicTube n)) := by
        intro x hx
        rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hb⟩
        rcases Finset.mem_image.mp hb with ⟨b, hb', rfl⟩
        exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb'⟩, rfl⟩
      have h_inj : Function.Injective (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : DyadicTube n)) := by
        intro p q h
        have h' : p.1 = q.1 ∧ p.2 = q.2 := by
          injection h with h1 h2
          exact ⟨h1, h2⟩
        exact Prod.ext h'.1 h'.2
      calc allTubes.card
        ≤ ((aSet ×ˢ bSet).image (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : DyadicTube n))).card := Finset.card_le_card h_sub
      _ = (aSet ×ˢ bSet).card := Finset.card_image_of_injective _ h_inj
      _ = aSet.card * bSet.card := Finset.card_product _ _
    have h3 : aSet.card = 2 * 2^n := by
      dsimp only [aSet]
      have h : aSet.card = ((2^n : ℤ) - (-(2^n : ℤ))).toNat := by
        rw [Int.card_Ico]
      rw [h]
      have h2 : ((2^n : ℤ) - (-(2^n : ℤ))) = 2 * (2^n : ℤ) := by ring
      rw [h2]
      have h3 : (2 * (2^n : ℤ)).toNat = 2 * 2^n := by
        norm_cast <;> omega
      exact h3
    have h4 : bSet.card = 6 * 2^n := by
      dsimp only [bSet]
      have h : bSet.card = ((3 * 2^n : ℤ) - (-(3 * 2^n : ℤ))).toNat := by
        rw [Int.card_Ico]
      rw [h]
      have h2 : ((3 * 2^n : ℤ) - (-(3 * 2^n : ℤ))) = 6 * (2^n : ℤ) := by ring
      rw [h2]
      have h3 : (6 * (2^n : ℤ)).toNat = 6 * 2^n := by
        norm_cast <;> omega
      exact h3
    have h5 : 2 * 2 ^ n * (6 * 2 ^ n) ≤ 2 ^ K_pigeon := by
      dsimp only [K_pigeon]
      have h10 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
        have h11 : ∀ n, (4 : ℕ) ^ n = 2 ^ (2 * n) := by
          intro n; induction n <;> simp [*, pow_succ, pow_add] <;> ring
        exact h11 n
      have h12 : 2 * 2 ^ n * (6 * 2 ^ n) = 12 * 2 ^ (2 * n) := by
        calc 2 * 2 ^ n * (6 * 2 ^ n)
          = 12 * (2 ^ n * 2 ^ n) := by ring
        _ = 12 * 2 ^ (n + n) := by rw [← pow_add]
        _ = 12 * 2 ^ (2 * n) := by ring_nf
      rw [h12]
      have h13 : 12 * 2 ^ (2 * n) ≤ 16 * 2 ^ (2 * n) := by
        apply mul_le_mul_of_nonneg_right
        · norm_num
        · positivity
      have h14 : 16 * 2 ^ (2 * n) = 2 ^ (2 * n + 4) := by
        have h15 : 16 * 2 ^ (2 * n) = 2 ^ 4 * 2 ^ (2 * n) := by norm_num
        rw [h15, ← pow_add] <;> ring
      rw [h14] at h13
      exact h13
    calc (snapped p hp).card
      ≤ allTubes.card := h1
    _ ≤ aSet.card * bSet.card := h2
    _ = (2 * 2 ^ n) * (6 * 2 ^ n) := by rw [h3, h4] <;> ring
    _ ≤ 2 ^ K_pigeon := h5

  have h_snapped_nonempty : ∀ (p : Plane) (hp : p ∈ P_fin),
      (snapped p hp).Nonempty := by
    intro p hp
    have h3 : (G p hp).card > 0 := by
      have h4 : (G p hp).card ≥ ENNReal.ofReal (δ ^ (-s + εReg)) :=
        (hG_spec p hp).2.2.2.2
      have h5 : 0 < δ ^ (-s + εReg) := by positivity
      have h6 : ENNReal.ofReal (δ ^ (-s + εReg)) > 0 := by positivity
      exact_mod_cast (lt_of_lt_of_le h6 h4)
    have h4 : (S0G p hp).card = (G p hp).card :=
      Finset.card_image_of_injective _ hS0_line_inj
    have h5 : 0 < (S0G p hp).card := by rw [h4] <;> exact h3
    exact Finset.Nonempty.image (Finset.card_pos.mp h5) _

  -- Quantitative m_min for pigeonhole
  let m_min : ℕ := Nat.ceil (2 * (dyadicDelta n)^(-s + εReg + fixedLoss))

  have hδ_lt_16δn : δ < 16 * dyadicDelta n := by
    have h : δ / 4 < 4 * dyadicDelta n := hδn_lt'
    linarith

  have h_threshold : (dyadicDelta n)^fixedLoss ≤
      (16 : ℝ)^(-s + εReg) / (2 * (260000 : ℝ)) :=
    h_absorb_mmin' δ hδ_pos hδ_le (dyadicDelta n) hδn_pos hδn_le'

  have h_m_min : ∀ (p : Plane) (hp : p ∈ P_fin),
      m_min ≤ (snapped p hp).card := by
    intro p hp
    have hG_lower_ENNReal : (G p hp).card ≥ ENNReal.ofReal (δ ^ (-s + εReg)) :=
      (hG_spec p hp).2.2.2.2
    have hG_pos : 0 ≤ δ ^ (-s + εReg) := by positivity
    have hG_lower : ((G p hp).card : ℝ) ≥ δ^(-s + εReg) := by
      have h : ENNReal.ofReal (δ ^ (-s + εReg)) ≤ ↑(G p hp).card := hG_lower_ENNReal
      have h2 : (δ ^ (-s + εReg) : ℝ) ≤ (G p hp).card := by
        exact ENNReal.ofReal_le_natCast.mp hG_lower_ENNReal
      exact h2
    have hS0G_card : ((S0G p hp).card : ℝ) = ((G p hp).card : ℝ) := by
      rw [Finset.card_image_of_injective _ hS0_line_inj] <;> norm_cast
    have hδ'_eq : δ' = δ / 4 := by simp [δ']
    have hS0G_near' : ∀ ℓ ∈ S0G p hp, S0 p ∈ Metric.cthickening δ ℓ.1 := by
      intro ℓ hℓ
      have h_le : δ' ≤ δ := by linarith [hδ'_eq]
      have h_near : S0 p ∈ Metric.cthickening δ' ℓ.1 := hS0G_near p hp ℓ hℓ
      have h_mono : ∀ (E : Set Plane), Metric.cthickening δ' E ⊆ Metric.cthickening δ E :=
        Metric.cthickening_mono h_le
      exact h_mono ℓ.1 h_near
    have h_fiber : ∀ (T : DyadicTube n),
        ((S0G p hp).filter (fun ℓ => snapToTubeThroughPoint n ℓ (S0 p) = T)).card ≤ 260000 :=
      snapToTubeThroughPoint_fiber_bound hδ_pos hδ_le_one hδ'_pos hδ'_eq
        hδn_leδ' (S0 p) (hP'_ball (Set.mem_image_of_mem S0 (hP_mem p hp)))
        (S0G p hp) (hS0G_sep p hp) (hS0G_slope p hp) (hS0G_v0 p hp) hS0G_near'
    have h_fiber' : ∀ y ∈ (S0G p hp).image (fun ℓ => snapToTubeThroughPoint n ℓ (S0 p)),
        ((S0G p hp).filter (fun ℓ => snapToTubeThroughPoint n ℓ (S0 p) = y)).card ≤ 260000 := by
      intro y _
      exact h_fiber y
    have h_snapped_lower : ((snapped p hp).card : ℝ) ≥
        2 * (dyadicDelta n)^(-s + εReg + fixedLoss) :=
      quantitative_image_bound
        (fun ℓ => snapToTubeThroughPoint n ℓ (S0 p))
        (S0G p hp) 260000 (by norm_num)
        s εReg fixedLoss (dyadicDelta n) δ
        hεReg_lt_s hfixedLoss_pos hδn_pos hδ_pos hδ_lt_16δn
        h_fiber'
        (by rw [hS0G_card] <;> exact hG_lower)
        h_threshold
    have h_m_min_real : (m_min : ℝ) ≤ ((snapped p hp).card : ℝ) := by
      have h1 : (m_min : ℝ) = ↑(Nat.ceil (2 * (dyadicDelta n)^(-s + εReg + fixedLoss))) := by
        simp [m_min] <;> norm_cast
      rw [h1]
      have h2 : Nat.ceil (2 * (dyadicDelta n)^(-s + εReg + fixedLoss)) ≤ (snapped p hp).card :=
        Nat.ceil_le.mpr h_snapped_lower
      exact_mod_cast h2
    exact Nat.cast_le.mp h_m_min_real

  -- Apply common-M pigeonhole
  let F_total : Plane → Finset (DyadicTube n) := fun p =>
    if hp : p ∈ P_fin then snapped p hp else ∅
  have hF_total_eq : ∀ (p : Plane) (hp : p ∈ P_fin), F_total p = snapped p hp := by
    intro p hp
    simp [F_total, hp]
  rcases common_m_pigeonhole_local P_fin F_total
      m_min K_pigeon hP_fin_nonempty
      (fun p hp => by rw [hF_total_eq p hp] <;> exact h_m_min p hp)
      (fun p hp => by rw [hF_total_eq p hp] <;> exact h_card_upper p hp)
      (fun p hp => by rw [hF_total_eq p hp] <;> exact h_snapped_nonempty p hp)
    with ⟨P'', M, F', hP''sub, hP''ret, hP''nonempty, hM_pos, hTF_size, hTF_sub, h_band, hM_lower⟩

  -- ======================================================================
  -- Step 8: Map P'' points to dyadic squares and assemble NiceConfiguration
  -- ======================================================================

  let pointToSquare (p : Plane) : DyadicSquare n :=
    { i := Int.floor ((S0 p) 0 / dyadicDelta n)
    , j := Int.floor ((S0 p) 1 / dyadicDelta n) }

  have hPointToSquare_mem : ∀ (p : Plane), S0 p ∈ (pointToSquare p).toSet := by
    intro p
    let x : Plane := S0 p
    let δ_n : ℝ := dyadicDelta n
    have hpos : 0 < δ_n := hδn_pos
    have h_floor_le : ∀ (i : Fin 2), (Int.floor (x i / δ_n) : ℝ) * δ_n ≤ x i := by
      intro i
      have h1 : (Int.floor (x i / δ_n) : ℝ) ≤ x i / δ_n := Int.floor_le _
      have h2 : (Int.floor (x i / δ_n) : ℝ) * δ_n ≤ x i := by
        have h2a : (Int.floor (x i / δ_n) : ℝ) * δ_n ≤ (x i / δ_n) * δ_n := mul_le_mul_of_nonneg_right h1 hpos.le
        have h2b : (x i / δ_n) * δ_n = x i := by field_simp [hpos.ne'] <;> ring
        rw [h2b] at h2a; exact h2a
      exact h2
    have h_floor_lt : ∀ (i : Fin 2), x i < ((Int.floor (x i / δ_n) : ℝ) + 1) * δ_n := by
      intro i
      have h1 : x i / δ_n < (Int.floor (x i / δ_n) : ℝ) + 1 := Int.lt_floor_add_one _
      have h2 : x i < ((Int.floor (x i / δ_n) : ℝ) + 1) * δ_n := by
        have h2a : (x i / δ_n) * δ_n < ((Int.floor (x i / δ_n) : ℝ) + 1) * δ_n := mul_lt_mul_of_pos_right h1 hpos
        have h2b : (x i / δ_n) * δ_n = x i := by field_simp [hpos.ne'] <;> ring
        rw [h2b] at h2a; exact h2a
      exact h2
    have h_main : (Int.floor (x 0 / δ_n) : ℝ) * δ_n ≤ x 0 ∧
        x 0 < ((Int.floor (x 0 / δ_n) : ℝ) + 1) * δ_n ∧
        (Int.floor (x 1 / δ_n) : ℝ) * δ_n ≤ x 1 ∧
        x 1 < ((Int.floor (x 1 / δ_n) : ℝ) + 1) * δ_n :=
      ⟨h_floor_le 0, h_floor_lt 0, h_floor_le 1, h_floor_lt 1⟩
    simpa [pointToSquare, DyadicSquare.toSet] using h_main

  -- Square uniqueness: dyadic squares partition the plane
  have h_square_unique : ∀ (q1 q2 : DyadicSquare n) (x : Plane),
      x ∈ q1.toSet → x ∈ q2.toSet → q1 = q2 := by
    let δ_n : ℝ := dyadicDelta n
    have hδ_pos : 0 < δ_n := dyadicDelta_pos n
    have h_interval_unique : ∀ (a b : ℤ) (y : ℝ),
        (a : ℝ) * δ_n ≤ y → y < (a + 1 : ℝ) * δ_n →
        (b : ℝ) * δ_n ≤ y → y < (b + 1 : ℝ) * δ_n → a = b := by
      intro a b y ha1 ha2 hb1 hb2
      by_cases h : a < b
      · have h5 : a + 1 ≤ b := by omega
        have h6 : ((a + 1 : ℝ) * δ_n) ≤ ((b : ℝ) * δ_n) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast h5) hδ_pos.le
        have h7 : ((a + 1 : ℝ) * δ_n) ≤ y := le_trans h6 hb1
        exact False.elim (not_le.mpr ha2 h7)
      · by_cases h2 : b < a
        · have h5 : b + 1 ≤ a := by omega
          have h6 : ((b + 1 : ℝ) * δ_n) ≤ ((a : ℝ) * δ_n) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast h5) hδ_pos.le
          have h7 : ((b + 1 : ℝ) * δ_n) ≤ y := le_trans h6 ha1
          exact False.elim (not_le.mpr hb2 h7)
        · omega
    intro q1 q2 x hx1 hx2
    have h_i_eq : q1.i = q2.i := by
      exact h_interval_unique q1.i q2.i (x 0) hx1.1 hx1.2.1 hx2.1 hx2.2.1
    have h_j_eq : q1.j = q2.j := by
      exact h_interval_unique q1.j q2.j (x 1) hx1.2.2.1 hx1.2.2.2 hx2.2.2.1 hx2.2.2.2
    have h_ext : ∀ (a b : DyadicSquare n), a.i = b.i → a.j = b.j → a = b := by
      intro a b hi hj
      cases a; cases b; congr <;> assumption
    have h_main : q1 = q2 := h_ext q1 q2 h_i_eq h_j_eq
    exact h_main

  let P0 : Finset (DyadicSquare n) := P''.image pointToSquare

  have hP0_nonempty : P0.Nonempty := hP''nonempty.image pointToSquare

  -- Internal provenance: q ∈ P0 → ∃ p ∈ P'', pointToSquare(p)=q ∧ S0(p) ∈ q.toSet
  have hPointSquare_internal : ∀ (q : DyadicSquare n), q ∈ P0 →
      ∃ (p : Plane) (hp : p ∈ P''), pointToSquare p = q ∧ S0 p ∈ q.toSet := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl, hPointToSquare_mem p⟩

  -- Public provenance: q ∈ P0 → ∃ p ∈ P, S0(p) ∈ q.toSet
  have hPointSquare_provenance : ∀ (q : DyadicSquare n), q ∈ P0 →
      ∃ (p_orig : Plane) (hp_orig : p_orig ∈ P), S0 p_orig ∈ q.toSet := by
    intro q hq
    rcases hPointSquare_internal q hq with ⟨p, hp, _, hSp⟩
    exact ⟨p, hP_mem p (hP''sub hp), hSp⟩

  -- Select representative from P'' for each square
  let rep (q : DyadicSquare n) (hq : q ∈ P0) : Plane :=
    Classical.choose (hPointSquare_internal q hq)
  have hrep_P'' : ∀ (q : DyadicSquare n) (hq : q ∈ P0), rep q hq ∈ P'' := by
    intro q hq
    exact (Classical.choose_spec (hPointSquare_internal q hq)).1
  have hrep_square : ∀ (q : DyadicSquare n) (hq : q ∈ P0),
      S0 (rep q hq) ∈ q.toSet := by
    intro q hq
    exact (Classical.choose_spec (hPointSquare_internal q hq)).2.2
  have hrep_pointToSquare : ∀ (q : DyadicSquare n) (hq : q ∈ P0),
      pointToSquare (rep q hq) = q := by
    intro q hq
    exact (Classical.choose_spec (hPointSquare_internal q hq)).2.1

  -- Tube family for each square (using representative from P'')
  let squareTubeFamily (q : DyadicSquare n) (hq : q ∈ P0) : Finset (DyadicTube n) :=
    F' (rep q hq)

  let T0 : Finset (DyadicTube n) :=
    P0.attach.biUnion (fun q => squareTubeFamily q.val q.property)

  -- S-set constant: snapped S-set constant * 18 (subset transfer factor)
  let C_snapped : ℝ := K_snap s *
      ((Real.rpow δ (-εReg)) * K_pack * (8 : ℝ)^s * (262144 : ℝ)^4)
  let C₁_real : ℝ := 18 * C_snapped
  let C₁_nat : ℕ := Nat.ceil C₁_real

  -- Assemble NiceConfiguration
  let config : CombiningTheorem.NiceConfiguration n s (C₁_nat : ℝ) M :=
    { P₀ := P0
      T₀ := T0
      tubeFamily := squareTubeFamily
      h_subset := by
        intro q hq T hT
        exact Finset.mem_biUnion.mpr ⟨⟨q, hq⟩, by simp, hT⟩
      h_size := by
        intro q hq
        exact hTF_size (rep q hq) (hrep_P'' q hq)
      h_delta_s_set := by
        intro q hq
        let p := rep q hq
        have hp : p ∈ P'' := hrep_P'' q hq
        have hp' : p ∈ P_fin := hP''sub hp
        have hF_eq : F_total p = snapped p hp' := hF_total_eq p hp'
        have h1 : IsDeltaSSet (dyadicDelta n) s C_snapped
            (snapped p hp' : Set (DyadicTube n)) :=
          hSnapped_sset p hp'
        have h2 : (squareTubeFamily q hq) ⊆ snapped p hp' := by
          have h21 : F' p ⊆ F_total p := hTF_sub p hp
          rw [hF_eq] at h21
          exact h21
        have h3 : (snapped p hp').card < 2 * (squareTubeFamily q hq).card := by
          have h4 : (squareTubeFamily q hq).card = M := hTF_size p hp
          rw [h4]
          have h5 : (F_total p).card < 2 * M := h_band p hp
          rw [hF_eq] at h5
          exact h5
        have h4 : IsDeltaSSet (dyadicDelta n) s C₁_real
            (squareTubeFamily q hq : Set (DyadicTube n)) :=
          dyadic_subset_sset_transfer_local h2 h3 h1
        have hC_le : C₁_real ≤ (C₁_nat : ℝ) := Nat.le_ceil C₁_real
        rcases h4 with ⟨hne, hδ, hC1_pos, hs, hbound⟩
        have hC2_pos : 0 < (C₁_nat : ℝ) := by linarith
        refine ⟨hne, hδ, hC2_pos, hs, fun x r hr => ?_⟩
        have h5 := hbound x r hr
        have h6 : ENNReal.ofReal C₁_real ≤ ENNReal.ofReal (C₁_nat : ℝ) :=
          ENNReal.ofReal_le_ofReal hC_le
        let B : ENNReal := Metric.externalCoveringNumber (dyadicDelta n).toNNReal (squareTubeFamily q hq : Set (DyadicTube n))
        have h7 : ENNReal.ofReal C₁_real * (ENNReal.ofReal r)^s * B ≤
            ENNReal.ofReal (C₁_nat : ℝ) * (ENNReal.ofReal r)^s * B := by
          gcongr
          <;> exact h6
        exact le_trans h5 h7
      h_intersect := by
        intro q hq T hT
        let rp := rep q hq
        have hrp : rp ∈ P'' := hrep_P'' q hq
        have hrp' : rp ∈ P_fin := hP''sub hrp
        have hT_snapped : T ∈ snapped rp hrp' := by
          have h1 : T ∈ squareTubeFamily q hq := hT
          have h2 : T ∈ F_total rp := hTF_sub rp hrp h1
          rw [hF_total_eq rp hrp'] at h2
          exact h2
        have h1 : S0 rp ∈ T.toSet := hSnapped_inc rp hrp' T hT_snapped
        have h2 : S0 rp ∈ q.toSet := hrep_square q hq
        exact ⟨S0 rp, h1, h2⟩
      h_tube_parameters := by
        exact Finset.finite_toSet T0 |>.isBounded
      h_bounded := by
        have h : Bornology.IsBounded (⋃ p ∈ (P0 : Set (DyadicSquare n)), (p.toSet : Set Plane)) :=
          (Bornology.isBounded_biUnion_finset P0).mpr (fun p _ => DyadicSquare.toSet_isBounded p)
        exact h
    }

  -- Point set ball bound using fjord's corrected estimate:
  -- ‖x‖ ≤ ‖S0(p)‖ + dist(x, S0(p)) ≤ (1+√2)/4 + √2·δ_n ≤ (1+2√2)/4 < 1
  have hδn_le_quart : dyadicDelta n ≤ 1 / 4 := by
    have h1 : dyadicDelta n ≤ δ / 4 := hδn_le'
    have h2 : δ ≤ 1 := hδ_le_one
    have h3 : δ / 4 ≤ 1 / 4 := by
      exact div_le_div_of_nonneg_right h2 (by norm_num)
    exact le_trans h1 h3
  have h_witness_ball : ∀ (q : DyadicSquare n), q ∈ P0 →
      ∃ (p : Plane), p ∈ Metric.closedBall (0 : Plane) 1 ∧ S0 p ∈ q.toSet := by
    intro q hq
    rcases hPointSquare_internal q hq with ⟨p, hp, _, hSp⟩
    exact ⟨p, hP_subset (hP_mem p (hP''sub hp)), hSp⟩
  have hPointSet_ball : config.pointSet ⊆ Metric.closedBall (0 : Plane) 1 := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨q, hq, hxq⟩
    rcases hPointSquare_internal q hq with ⟨p, _hp, _, hSp⟩
    have h_pball : p ∈ Metric.closedBall (0 : Plane) 1 := hP_subset (hP_mem p (hP''sub _hp))
    have h_norm_x : ‖x‖ < 1 := point_in_square_in_unit_ball hxq hSp h_pball hδn_le_quart
    have h_goal : dist x (0 : Plane) ≤ 1 := by
      have h_dist : dist x (0 : Plane) = ‖x‖ := by simp
      rw [h_dist]
      exact h_norm_x.le
    simpa [Metric.mem_closedBall] using h_goal

  -- Square cover: each dyadic square is covered by one δ_n-ball (diameter δ_n√2 < 2δ_n, center ball radius δ_n suffices)
  have h_card_cover : (P0.card : ENNReal) ≥ Ncover (dyadicDelta n) config.pointSet := by
    let Cfin : Finset Plane := P0.image DyadicSquare.center
    let C : Set Plane := (Cfin : Set Plane)
    have hC : Metric.IsCover (dyadicDelta n).toNNReal config.pointSet C := by
      intro x hx
      rcases Set.mem_iUnion₂.mp hx with ⟨q, hq, hxq⟩
      have h2 : dist x (DyadicSquare.center q) ≤ dyadicDelta n :=
        DyadicSquare.centered_ball hxq
      have h3 : edist x (DyadicSquare.center q) ≤ (dyadicDelta n).toNNReal := by
        have h4 : edist x (DyadicSquare.center q) = ENNReal.ofReal (dist x (DyadicSquare.center q)) := edist_dist _ _
        rw [h4]
        have h5 : ENNReal.ofReal (dist x (DyadicSquare.center q)) ≤ ENNReal.ofReal (dyadicDelta n) :=
          ENNReal.ofReal_le_ofReal h2
        have h6 : 0 ≤ dyadicDelta n := hδn_pos.le
        have h7 : ENNReal.ofReal (dyadicDelta n) = ↑(dyadicDelta n).toNNReal :=
          (ENNReal.ofNNReal_toNNReal (dyadicDelta n)).symm
        rw [h7] at h5
        exact h5
      exact ⟨DyadicSquare.center q, Finset.mem_image_of_mem _ hq, h3⟩
    have hfc : C.encard = ↑Cfin.card := by
      simp [C, Set.encard] <;> rfl
    have h1 : Ncover (dyadicDelta n) config.pointSet ≤ (Cfin.card : ENNReal) := by
      have h_le : Metric.externalCoveringNumber (dyadicDelta n).toNNReal config.pointSet ≤ C.encard :=
        Metric.IsCover.externalCoveringNumber_le_encard hC
      have h_le' : (Metric.externalCoveringNumber (dyadicDelta n).toNNReal config.pointSet : ENNReal) ≤ (Cfin.card : ENNReal) := by
        rw [hfc] at h_le
        exact_mod_cast h_le
      have h_eq : Ncover (dyadicDelta n) config.pointSet = (Metric.externalCoveringNumber (dyadicDelta n).toNNReal config.pointSet : ENNReal) := by
        simp [Ncover] <;> rfl
      rw [h_eq]
      exact h_le'
    have h2 : (Cfin.card : ENNReal) ≤ (P0.card : ENNReal) := by
      exact_mod_cast Finset.card_image_le (f := DyadicSquare.center)
    exact le_trans h1 h2

  -- Square bounds: pointToSquare maps points in [0,1)² to squares with indices in [0,2^n)
  have h_squares : ∀ (q : DyadicSquare n), q ∈ P0 →
      0 ≤ q.i ∧ q.i < (2 ^ n : ℤ) ∧ 0 ≤ q.j ∧ q.j < (2 ^ n : ℤ) := by
    intro q hq
    let p := rep q hq
    have hp : p ∈ P'' := hrep_P'' q hq
    have hSp : S0 p ∈ q.toSet := hrep_square q hq
    have h_unit := hP'_unit (S0 p) (Set.mem_image_of_mem S0 (hP_mem p (hP''sub hp)))
    exact square_index_bounds hSp h_unit

  -- Tube strip bound: inherited from snapped families
  have h_tubes : ∀ (T : DyadicTube n), T ∈ T0 →
      -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ) := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨q_sub, hq, hT'⟩
    let q : DyadicSquare n := q_sub.val
    have hq' : q ∈ P0 := q_sub.property
    let rp := rep q hq'
    have hrp : rp ∈ P'' := hrep_P'' q hq'
    have hrp' : rp ∈ P_fin := hP''sub hrp
    have hT_snapped : T ∈ snapped rp hrp' := by
      have h1 : T ∈ F_total rp := hTF_sub rp hrp hT'
      rw [hF_total_eq rp hrp'] at h1
      exact h1
    exact hSnapped_strip rp hrp' T hT_snapped

  -- Tube slope bound: inherited from snapped families
  have h_tube_slope : ∀ (T : DyadicTube n), T ∈ T0 → |T.slope| ≤ 1 := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨q_sub, hq, hT'⟩
    let q : DyadicSquare n := q_sub.val
    have hq' : q ∈ P0 := q_sub.property
    let rp := rep q hq'
    have hrp : rp ∈ P'' := hrep_P'' q hq'
    have hrp' : rp ∈ P_fin := hP''sub hrp
    have hT_snapped : T ∈ snapped rp hrp' := by
      have h1 : T ∈ F_total rp := hTF_sub rp hrp hT'
      rw [hF_total_eq rp hrp'] at h1
      exact h1
    exact hSnapped_slope rp hrp' T hT_snapped

  -- Incidence: floor remainder gives exact Stand tube membership
  have h_incidence : ∀ (p : DyadicSquare n) (hp : p ∈ P0)
      (T : DyadicTube n) (hT : T ∈ squareTubeFamily p hp),
      ((tubeToStand T).toSet ∩ (squareToStand p).toSet).Nonempty := by
    intro p hp T hT
    let rp := rep p hp
    have hrp : rp ∈ P'' := hrep_P'' p hp
    have hrp' : rp ∈ P_fin := hP''sub hrp
    have hT_total : T ∈ F_total rp := hTF_sub rp hrp hT
    have hT_snapped : T ∈ snapped rp hrp' := by
      rw [hF_total_eq rp hrp'] at hT_total
      exact hT_total
    rcases Finset.mem_image.mp hT_snapped with ⟨ℓ, _hℓ, rfl⟩
    set p_rep : Plane := S0 rp with hp_rep_def
    set T' : DyadicTube n := snapToTubeThroughPoint n ℓ p_rep with hT'_def
    have h_floor : 0 ≤ p_rep 1 - T'.slope * p_rep 0 - T'.intercept ∧
        p_rep 1 - T'.slope * p_rep 0 - T'.intercept < dyadicDelta n :=
      snapToTubeThroughPoint_floor_remainder (n := n) (ℓ := ℓ) (p := p_rep)
    have h_sq : p_rep ∈ (p.toSet : Set Plane) := hrep_square p hp
    set δ : ℝ := dyadicDelta n with hδ_def
    have hδ_pos : 0 < δ := dyadicDelta_pos n
    have hδ_eq : δ = _root_.dyadicDelta n := by
      simp [hδ_def, _root_.dyadicDelta, dyadicDelta, Real.rpow_neg] <;> field_simp <;> norm_cast
    let d : ℝ := p_rep 1 - T'.slope * p_rep 0 - T'.intercept
    have hd0 : 0 ≤ d := h_floor.1
    have hd1 : d < δ := h_floor.2
    let slope : ℝ := T'.slope
    let intercept : ℝ := T'.intercept + d
    have h_T_intercept : T'.intercept = (T'.b : ℝ) * δ := by
      simp [DyadicTube.intercept, hδ_def] <;> ring
    have hslope_left : (T'.a : ℝ) * δ ≤ slope := by
      simp [slope, DyadicTube.slope, hδ_def] <;> ring
    have hslope_right : slope < ((T'.a : ℝ) + 1) * δ := by
      have h : (T'.a : ℝ) < (T'.a : ℝ) + 1 := by linarith
      exact mul_lt_mul_of_pos_right h hδ_pos
    have hint_left : (T'.b : ℝ) * δ ≤ intercept := by
      have h : intercept = (T'.b : ℝ) * δ + d := by
        simp [intercept, h_T_intercept] <;> ring
      rw [h] <;> linarith [hd0]
    have hint_right : intercept < ((T'.b : ℝ) + 1) * δ := by
      have h : intercept = (T'.b : ℝ) * δ + d := by
        simp [intercept, h_T_intercept] <;> ring
      rw [h] <;> linarith [hd1, hδ_pos]
    have heq : p_rep 1 = slope * p_rep 0 + intercept := by
      simp [slope, intercept, d] <;> ring
    have h_p_in_stand_square : (p_rep 0, p_rep 1) ∈ (squareToStand p).toSet := by
      simp only [squareToStand, _root_.DyadicSquare.toSet, Set.mem_prod, Set.mem_Ico]
      constructor
      · constructor
        · rw [←hδ_eq] <;> exact h_sq.1
        · rw [←hδ_eq] <;> exact h_sq.2.1
      · constructor
        · rw [←hδ_eq] <;> exact h_sq.2.2.1
        · rw [←hδ_eq] <;> exact h_sq.2.2.2
    have h_p_in_stand_tube : (p_rep 0, p_rep 1) ∈ (tubeToStand T').toSet := by
      have hslope1' : (T'.a : ℝ) * _root_.dyadicDelta n ≤ slope ∧
                        slope < ((T'.a : ℝ) + 1) * _root_.dyadicDelta n := by
        rw [←hδ_eq] <;> exact ⟨hslope_left, hslope_right⟩
      have hint1' : (T'.b : ℝ) * _root_.dyadicDelta n ≤ intercept ∧
                        intercept < ((T'.b : ℝ) + 1) * _root_.dyadicDelta n := by
        rw [←hδ_eq] <;> exact ⟨hint_left, hint_right⟩
      have h_main : ∃ (slope' : ℝ), ((T'.a : ℝ) * _root_.dyadicDelta n ≤ slope' ∧
          slope' < ((T'.a : ℝ) + 1) * _root_.dyadicDelta n) ∧
          ∃ (intercept' : ℝ), ((T'.b : ℝ) * _root_.dyadicDelta n ≤ intercept' ∧
            intercept' < ((T'.b : ℝ) + 1) * _root_.dyadicDelta n) ∧
            p_rep 1 = slope' * p_rep 0 + intercept' := by
        exact ⟨slope, ⟨hslope1'.1, hslope1'.2⟩, intercept, ⟨hint1'.1, hint1'.2⟩, heq⟩
      simpa [tubeToStand, _root_.DyadicTube.toSet] using h_main
    exact ⟨(p_rep 0, p_rep 1), h_p_in_stand_tube, h_p_in_stand_square⟩

  -- Tube provenance
  have h_provenance : ∀ (p : DyadicSquare n) (hp : p ∈ P0)
      (T : DyadicTube n) (hT : T ∈ squareTubeFamily p hp),
      ∃ (p_orig : Plane) (hp_orig : p_orig ∈ P)
        (ℓ : AffineLine) (hℓ : ℓ ∈ tubeFamily p_orig hp_orig),
      T = snapToTubeThroughPoint n (S0_line ℓ) (S0 p_orig) := by
    intro p hp T hT
    let rp := rep p hp
    have hrp : rp ∈ P'' := hrep_P'' p hp
    have hrp' : rp ∈ P_fin := hP''sub hrp
    have hT_total : T ∈ F_total rp := hTF_sub rp hrp hT
    have hT_snapped : T ∈ snapped rp hrp' := by
      rw [hF_total_eq rp hrp'] at hT_total
      exact hT_total
    exact hSnapped_provenance rp hrp' T hT_snapped

  -- Regularity constants from local transfer output
  let C_P_reg : ℝ := 81 * (Real.rpow δ (-εReg)) * (4 : ℝ)^u * (4 : ℝ)^u * C_geom^2 * (1 + Real.sqrt 2)^u * (dyadicDelta n)^(-pointLoss / 2)
  let K_P_reg : ℝ := (Real.rpow δ (-εReg)) * 9 * C_geom

  -- Narrow sorrys for remaining quantitative bounds
  have hC₁_bound : (C₁_nat : ℝ) ≤ (dyadicDelta n)^(-(εReg + tubeLoss)) := by
    have hK_tube_absorbδn : K_tube ≤ (dyadicDelta n)^(-tubeLoss) := by
      have h1 : K_tube ≤ δ^(-tubeLoss) := h_absorb_tube' δ hδ_pos hδ_le
      have h2 : δ^(-tubeLoss) ≤ (dyadicDelta n)^(-tubeLoss) :=
        Real.rpow_le_rpow_of_nonpos hδn_pos hδn_leδ (by linarith)
      exact le_trans h1 h2
    have hC1_eq : C₁_real = K_C1_const * Real.rpow δ (-εReg) := by
      dsimp only [C₁_real, C_snapped, K_C1_const] <;> ring
    have hC1_nonneg : 0 ≤ C₁_real := by
      rw [hC1_eq]
      have h1 : 0 ≤ K_C1_const := hK_C1_const_pos.le
      have h2 : 0 ≤ Real.rpow δ (-εReg) := Real.rpow_nonneg (by linarith) _
      exact mul_nonneg h1 h2
    exact FrontendQuantBounds.C₁_nat_bound hδn_pos hδn_leδ hεReg_pos htubeLoss_pos hδn_le_one
      K_C1_const K_tube hK_C1_const_pos.le hK_tube_pos.le
      (by dsimp only [K_tube] <;> linarith)
      hK_tube_absorbδn C₁_real hC1_nonneg hC1_eq

  have hM_bound' : (M : ℝ) ≥ (dyadicDelta n)^(-s + εReg + fixedLoss) := by
    have h1 : (M : ℝ) ≥ (m_min : ℝ) / 2 := hM_lower
    have h2 : (m_min : ℝ) ≥ 2 * (dyadicDelta n)^(-s + εReg + fixedLoss) := by
      have h3 : (m_min : ℝ) = ↑(Nat.ceil (2 * (dyadicDelta n)^(-s + εReg + fixedLoss))) := by
        simp [m_min] <;> norm_cast
      rw [h3]
      exact Nat.le_ceil _
    linarith

  -- Shared helpers for h_abs_mass and h_point_reg
  have hS0_sep_shared : ∀ (x y : Plane), x ∈ P'' → y ∈ P'' → x ≠ y → dyadicDelta n ≤ dist (S0 x) (S0 y) := by
    intro x y hx hy hne
    have hx' : x ∈ P_fin := hP''sub hx
    have hy' : y ∈ P_fin := hP''sub hy
    have h1 : (r_point.toNNReal : ENNReal) < edist x y :=
      hP_fin_sep (by rw [←hP_fin_coe] <;> exact hx') (by rw [←hP_fin_coe] <;> exact hy') hne
    have h_rpoint_nonneg : 0 ≤ r_point := by
      simp [r_point] <;> positivity
    have h_eq1 : (r_point.toNNReal : ENNReal) = ENNReal.ofReal r_point := by
      simp [ENNReal.ofReal, h_rpoint_nonneg] <;> norm_cast
    have h_eq2 : edist x y = ENNReal.ofReal (dist x y) := edist_dist x y
    rw [h_eq1, h_eq2] at h1
    have h2 : r_point < dist x y := by
      by_contra h
      have h' : dist x y ≤ r_point := by linarith
      have h'' : ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal r_point :=
        ENNReal.ofReal_le_ofReal h'
      exact not_lt.mpr h'' h1
    have h3 : r_point = 4 * dyadicDelta n := by
      simp [r_point] <;> ring
    have h4 : 4 * dyadicDelta n < dist x y := by
      rw [h3] at h2
      exact h2
    have h5 : dist (S0 x) (S0 y) = (1 / 4 : ℝ) * dist x y := S0_dist x y
    rw [h5]
    linarith

  have h_fiber4_shared : ∀ (q : DyadicSquare n), q ∈ P0 →
      (P''.filter (fun p => pointToSquare p = q)).card ≤ 4 := by
    intro q hq
    let E := P''.filter (fun p => pointToSquare p = q)
    have hE1 : ∀ x ∈ E, S0 x ∈ q.toSet := by
      intro x hx
      have h_eq : pointToSquare x = q := (Finset.mem_filter.mp hx).2
      have h : S0 x ∈ (pointToSquare x).toSet := hPointToSquare_mem x
      rw [h_eq] at h
      exact h
    have hE_sep : ∀ (x y : Plane), x ∈ E → y ∈ E → x ≠ y → dyadicDelta n ≤ dist (S0 x) (S0 y) := by
      intro x y hx hy hne
      have hx' : x ∈ P'' := (Finset.mem_filter.mp hx).1
      have hy' : y ∈ P'' := (Finset.mem_filter.mp hy).1
      exact hS0_sep_shared x y hx' hy' hne
    exact four_point_packing_bound (f := S0) hδn_pos hE_sep hE1

  have hP0_ge_P''4_shared : (P0.card : ℝ) ≥ (P''.card : ℝ) / 4 := by
    have h1 : (P''.card : ℝ) ≤ 4 * (P0.card : ℝ) :=
      card_image_fiber_bound pointToSquare P'' 4 (by norm_num) h_fiber4_shared
    linarith

  have h_abs_mass : (P0.card : ENNReal) ≥
      ENNReal.ofReal ((dyadicDelta n)^(-u + εReg + pointLoss)) := by
    set δ_n : ℝ := dyadicDelta n with hδn_eq
    have hδn_pos' : 0 < δ_n := hδn_pos
    -- Use shared separation and fiber bounds
    have hS0_sep : ∀ (x y : Plane), x ∈ P'' → y ∈ P'' → x ≠ y → δ_n ≤ dist (S0 x) (S0 y) :=
      hS0_sep_shared
    have h_fiber4 : ∀ (q : DyadicSquare n), q ∈ P0 →
        (P''.filter (fun p => pointToSquare p = q)).card ≤ 4 := h_fiber4_shared
    have hP0_ge_P''4 : (P0.card : ℝ) ≥ (P''.card : ℝ) / 4 := hP0_ge_P''4_shared
    -- |P''| ≥ |P_fin| / (2n+5)
    have hP''_ge : (P''.card : ℝ) ≥ (P_fin.card : ℝ) / (2 * (n : ℝ) + 5) := by
      have h : (P''.card : ℝ) ≥ (P_fin.card : ℝ) / ((K_pigeon : ℝ) + 1) := hP''ret
      have hK : ((K_pigeon : ℝ) + 1) = 2 * (n : ℝ) + 5 := by
        simp [K_pigeon] <;> ring
      rw [hK] at h
      exact h
    -- |P_fin| ≥ 16^{-u+εReg} * δ_n^{-u+εReg}
    have hP_fin_ge : (P_fin.card : ℝ) ≥
        (16 : ℝ)^(-u + εReg) * δ_n^(-u + εReg) := by
      have h := hP_fin_card_lower
      exact_mod_cast h
    -- Combine: |P0| ≥ 16^{-u+εReg} * δ_n^{-u+εReg} / (4*(2n+5))
    have hP0_ge : (P0.card : ℝ) ≥
        (16 : ℝ)^(-u + εReg) * δ_n^(-u + εReg) / (4 * (2 * (n : ℝ) + 5)) := by
      calc (P0.card : ℝ)
        ≥ (P''.card : ℝ) / 4 := hP0_ge_P''4
      _ ≥ ((P_fin.card : ℝ) / (2 * (n : ℝ) + 5)) / 4 := by gcongr
      _ = (P_fin.card : ℝ) / (4 * (2 * (n : ℝ) + 5)) := by field_simp <;> ring
      _ ≥ ((16 : ℝ)^(-u + εReg) * δ_n^(-u + εReg)) / (4 * (2 * (n : ℝ) + 5)) := by
          gcongr
    -- 16^{-u+εReg} ≥ 1/256 since u-εReg ≤ 2
    have h16_lower : (16 : ℝ)^(-u + εReg) ≥ 1 / 256 := by
      have h_exp : -u + εReg ≥ -2 := by linarith [hu_le2]
      have h : (16 : ℝ)^(-u + εReg) ≥ (16 : ℝ)^(-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h_exp
      have h2 : (16 : ℝ)^(-2 : ℝ) = 1 / 256 := by norm_num
      rw [h2] at h
      exact h
    -- Polynomial absorption: 1024 * (2n+5) ≤ δ_n^{-pointLoss}
    have h_absorb : (1024 : ℝ) * (2 * (n : ℝ) + 5) ≤ δ_n^(-pointLoss) := h_poly_absorb
    -- Main inequality: 16^{-u+εReg} / (4*(2n+5)) ≥ δ_n^{pointLoss}
    have h_main : (16 : ℝ)^(-u + εReg) / (4 * (2 * (n : ℝ) + 5)) ≥ δ_n^(pointLoss) := by
      have h3 : (16 : ℝ)^(-u + εReg) / (4 * (2 * (n : ℝ) + 5)) ≥
          (1 / 256 : ℝ) / (4 * (2 * (n : ℝ) + 5)) := by gcongr
      have h4 : (1 / 256 : ℝ) / (4 * (2 * (n : ℝ) + 5)) =
          1 / ((1024 : ℝ) * (2 * (n : ℝ) + 5)) := by field_simp <;> ring
      rw [h4] at h3
      have h5 : 0 < (1024 : ℝ) * (2 * (n : ℝ) + 5) := by positivity
      have h6 : δ_n^(pointLoss) ≤ 1 / ((1024 : ℝ) * (2 * (n : ℝ) + 5)) := by
        have h7 : δ_n^(-pointLoss) ≥ (1024 : ℝ) * (2 * (n : ℝ) + 5) := h_absorb
        have h8 : δ_n^(pointLoss) = (δ_n^(-pointLoss))⁻¹ := by
          rw [← Real.rpow_neg hδn_pos'.le] <;> ring_nf
        rw [h8]
        have h9 : (δ_n^(-pointLoss))⁻¹ ≤ (((1024 : ℝ) * (2 * (n : ℝ) + 5))⁻¹) := by
          gcongr <;> linarith
        have h10 : (((1024 : ℝ) * (2 * (n : ℝ) + 5))⁻¹) = 1 / ((1024 : ℝ) * (2 * (n : ℝ) + 5)) := by
          field_simp
        rw [h10] at h9
        exact h9
      linarith
    -- Convert to target: δ_n^{-u+εReg} * δ_n^{pointLoss} = δ_n^{-u+εReg+pointLoss}
    have h_final : (P0.card : ℝ) ≥ δ_n^(-u + εReg + pointLoss) := by
      have h10 : (P0.card : ℝ) ≥
          (16 : ℝ)^(-u + εReg) * δ_n^(-u + εReg) / (4 * (2 * (n : ℝ) + 5)) := hP0_ge
      have h11 : (16 : ℝ)^(-u + εReg) * δ_n^(-u + εReg) / (4 * (2 * (n : ℝ) + 5)) ≥
          δ_n^(-u + εReg) * δ_n^(pointLoss) := by
        have h12 : (16 : ℝ)^(-u + εReg) / (4 * (2 * (n : ℝ) + 5)) ≥ δ_n^(pointLoss) := h_main
        have h13 : 0 ≤ δ_n^(-u + εReg) := by positivity
        have h14 : δ_n^(-u + εReg) * ((16 : ℝ)^(-u + εReg) / (4 * (2 * (n : ℝ) + 5))) ≥
            δ_n^(-u + εReg) * δ_n^(pointLoss) :=
          mul_le_mul_of_nonneg_left h12 h13
        have h15 : δ_n^(-u + εReg) * ((16 : ℝ)^(-u + εReg) / (4 * (2 * (n : ℝ) + 5))) =
            (16 : ℝ)^(-u + εReg) * δ_n^(-u + εReg) / (4 * (2 * (n : ℝ) + 5)) := by ring
        rw [h15] at h14
        exact h14
      have h14 : δ_n^(-u + εReg) * δ_n^(pointLoss) = δ_n^(-u + εReg + pointLoss) := by
        rw [← Real.rpow_add hδn_pos'] <;> ring
      have h16 : (16 : ℝ)^(-u + εReg) * δ_n^(-u + εReg) / (4 * (2 * (n : ℝ) + 5)) ≥
          δ_n^(-u + εReg + pointLoss) := by
        rw [h14] at h11
        exact h11
      linarith
    have h_nonneg : 0 ≤ δ_n^(-u + εReg + pointLoss) := by positivity
    have h_ennreal : ENNReal.ofReal (δ_n^(-u + εReg + pointLoss)) ≤ ENNReal.ofReal (P0.card : ℝ) :=
      ENNReal.ofReal_le_ofReal h_final
    have h_cast : ENNReal.ofReal (P0.card : ℝ) = (P0.card : ENNReal) := by
      simp
    rw [h_cast] at h_ennreal
    exact h_ennreal

  have h_point_reg : IsSquareRootRegular (dyadicDelta n) u C_P_reg K_P_reg config.pointSet := by
    set δ_n : ℝ := dyadicDelta n with hδn_eq
    set C_in : ℝ := (Real.rpow δ (-εReg)) * (4 : ℝ)^u with hC_in_def
    set K_in : ℝ := Real.rpow δ (-εReg) with hK_in_def
    let scale : Plane → Plane := fun x => (1 / 4 : ℝ) • x
    let transl : Plane → Plane := fun x => x + quarterVec

    -- Covering number equality: Ncover(ε, S0 '' P) = Ncover(4ε, P)
    have h_ncover_S0 : ∀ (ε : ℝ), 0 < ε →
        Ncover ε (S0 '' P) = Ncover (4 * ε) P := by
      intro ε hε
      have h_S0_eq : ∀ (x : Plane), S0 x = transl (scale x) := by
        intro x
        simp [S0_apply, scale, transl] <;> rfl
      have h21 : transl '' (scale '' P) = (transl ∘ scale) '' P := by
        simpa [Function.comp] using Set.image_image transl scale P
      have h22 : (transl ∘ scale) '' P = S0 '' P := by
        apply Set.image_congr
        intro x _
        exact (h_S0_eq x).symm
      have h2 : transl '' (scale '' P) = S0 '' P := by
        rw [h21, h22]
      have h_translate : Metric.externalCoveringNumber ε.toNNReal (transl '' (scale '' P)) =
          Metric.externalCoveringNumber ε.toNNReal (scale '' P) :=
        ncover_translate (ε := ε.toNNReal) (P := scale '' P) (v := quarterVec)
      have h1 : Ncover ε (transl '' (scale '' P)) = Ncover ε (scale '' P) := by
        unfold Ncover
        rw [h_translate]
      have h_scale_eq : scale '' P = (fun x : Plane => (1 / 4 : ℝ) • x) '' P := by rfl
      have h4ε_pos : 0 < 4 * ε := by positivity
      have h_ns : Ncover ((1 / 4 : ℝ) * (4 * ε)) ((fun x : Plane => (1 / 4 : ℝ) • x) '' P) = Ncover (4 * ε) P :=
        ncover_scale (P := P) (c := 1 / 4) (δ := 4 * ε)
          (show (0 : ℝ) < 1 / 4 by norm_num) (by norm_num) h4ε_pos
      have h_mul : (1 / 4 : ℝ) * (4 * ε) = ε := by ring
      have h3 : Ncover ε (scale '' P) = Ncover (4 * ε) P := by
        rw [h_scale_eq]
        rw [h_mul] at h_ns
        exact h_ns
      calc Ncover ε (S0 '' P)
        _ = Ncover ε (transl '' (scale '' P)) := by rw [h2]
        _ = Ncover ε (scale '' P) := h1
        _ = Ncover (4 * ε) P := h3

    -- Step 1: Ncover(δ_n, S0 '' P) ≤ card(P_fin)
    have h1 : Ncover δ_n (S0 '' P) ≤ (P_fin.card : ENNReal) := by
      have h_eq : Ncover δ_n (S0 '' P) = Ncover (4 * δ_n) P := h_ncover_S0 δ_n hδn_pos
      rw [h_eq]
      have h_rpoint : 4 * δ_n = r_point := by
        simp [r_point, hδn_eq] <;> ring
      rw [h_rpoint]
      have h_cover : Ncover r_point P = ↑(Metric.externalCoveringNumber r_point.toNNReal P) := by
        simp [Ncover] <;> rfl
      rw [h_cover]
      have h_encard : P_fin_set.encard = (P_fin.card : ENat) := by
        rw [hP_fin_finite.encard_eq_coe_toFinset_card] <;> rfl
      have h : Metric.externalCoveringNumber r_point.toNNReal P ≤ P_fin_set.encard := hP_fin_card_ge
      rw [h_encard] at h
      exact_mod_cast h

    -- Step 2: card(P_fin) ≤ (2n+5) * card(P'')
    let poly_enn : ENNReal := ↑(2 * n + 5)
    have h2 : (P_fin.card : ENNReal) ≤ poly_enn * (P''.card : ENNReal) := by
      have h_ret : (P''.card : ℝ) ≥ (P_fin.card : ℝ) / ((K_pigeon : ℝ) + 1) := hP''ret
      have hK : ((K_pigeon : ℝ) + 1) = 2 * (n : ℝ) + 5 := by
        simp [K_pigeon] <;> ring
      rw [hK] at h_ret
      have h : (P_fin.card : ℝ) ≤ (2 * (n : ℝ) + 5) * (P''.card : ℝ) := by
        have h' : (P_fin.card : ℝ) / (2 * (n : ℝ) + 5) ≤ (P''.card : ℝ) := h_ret
        have h_pos : 0 < (2 * (n : ℝ) + 5) := by positivity
        calc (P_fin.card : ℝ)
          = ((P_fin.card : ℝ) / (2 * (n : ℝ) + 5)) * (2 * (n : ℝ) + 5) := by field_simp [h_pos.ne'] <;> ring
        _ ≤ (P''.card : ℝ) * (2 * (n : ℝ) + 5) := mul_le_mul_of_nonneg_right h' h_pos.le
        _ = (2 * (n : ℝ) + 5) * (P''.card : ℝ) := by ring
      have h_nat : P_fin.card ≤ (2 * n + 5) * P''.card := by
        have h' : (P_fin.card : ℝ) ≤ ↑((2 * n + 5) * P''.card) := by
          simpa [Nat.cast_mul] using h
        exact Nat.cast_le.mp h'
      have h_enn : (P_fin.card : ENNReal) ≤ ↑((2 * n + 5) * P''.card) := by exact_mod_cast h_nat
      have h_mul : ↑((2 * n + 5) * P''.card) = poly_enn * (P''.card : ENNReal) := by
        simp [poly_enn, Nat.cast_mul] <;> ring
      rw [h_mul] at h_enn
      exact h_enn

    -- Step 3: card(P'') ≤ 4 * card(P0)
    have h3 : (P''.card : ENNReal) ≤ 4 * (P0.card : ENNReal) := by
      have h1 : (P''.card : ℝ) ≤ 4 * (P0.card : ℝ) :=
        card_image_fiber_bound pointToSquare P'' 4 (by norm_num) h_fiber4_shared
      have h : (P''.card : ℝ) ≤ 4 * (P0.card : ℝ) := h1
      exact_mod_cast h

    -- Step 4: card(P0) ≤ 9 * Ncover(δ_n, config.pointSet)
    have h4 : (P0.card : ENNReal) ≤ 9 * Ncover δ_n config.pointSet := by
      exact finset_squares_ncover_lower_clean P0

    -- Combined density chain
    have h_density : Ncover δ_n (S0 '' P) ≤
        (36 : ENNReal) * poly_enn * Ncover δ_n config.pointSet := by
      calc Ncover δ_n (S0 '' P)
        ≤ (P_fin.card : ENNReal) := h1
      _ ≤ poly_enn * (P''.card : ENNReal) := h2
      _ ≤ poly_enn * (4 * (P0.card : ENNReal)) := by gcongr
      _ = (4 : ENNReal) * poly_enn * (P0.card : ENNReal) := by ring
      _ ≤ (4 : ENNReal) * poly_enn * (9 * Ncover δ_n config.pointSet) := by gcongr
      _ = (36 : ENNReal) * poly_enn * Ncover δ_n config.pointSet := by ring

    -- Convert to h_mass using polynomial absorption
    have h_poly36 : (36 : ℝ) * (2 * (n : ℝ) + 5) ≤ δ_n^(-pointLoss / 2) := by
      have h : (36 : ℝ) * (2 * (n : ℝ) + 5) ≤ (1024 : ℝ) * (2 * (n : ℝ) + 5) := by
        gcongr <;> norm_num
      exact le_trans h h_poly_absorb_half
    have h_mass : Ncover δ_n config.pointSet ≥
        ENNReal.ofReal (δ_n^(pointLoss / 2)) * Ncover δ_n (S0 '' P) := by
      have h5 : Ncover δ_n (S0 '' P) ≤
          ENNReal.ofReal (δ_n^(-pointLoss / 2)) * Ncover δ_n config.pointSet := by
        have h6 : (36 : ENNReal) * poly_enn ≤
            ENNReal.ofReal (δ_n^(-pointLoss / 2)) := by
          have h61 : (36 : ENNReal) * poly_enn = ENNReal.ofReal ((36 : ℝ) * (2 * (n : ℝ) + 5)) := by
            simp [poly_enn, ENNReal.ofReal_mul]
            <;> norm_cast
          rw [h61]
          exact ENNReal.ofReal_le_ofReal h_poly36
        calc Ncover δ_n (S0 '' P)
          ≤ (36 : ENNReal) * poly_enn * Ncover δ_n config.pointSet := h_density
        _ ≤ ENNReal.ofReal (δ_n^(-pointLoss / 2)) * Ncover δ_n config.pointSet := by gcongr
      have h7 : ENNReal.ofReal (δ_n^(pointLoss / 2)) * Ncover δ_n (S0 '' P) ≤
          ENNReal.ofReal (δ_n^(pointLoss / 2)) *
          (ENNReal.ofReal (δ_n^(-pointLoss / 2)) * Ncover δ_n config.pointSet) := by gcongr
      have h8 : ENNReal.ofReal (δ_n^(pointLoss / 2)) * ENNReal.ofReal (δ_n^(-pointLoss / 2)) = 1 := by
        have h9 : δ_n^(pointLoss / 2) * δ_n^(-pointLoss / 2) = 1 := by
          have h10 : δ_n^(pointLoss / 2) * δ_n^(-pointLoss / 2) = δ_n^((pointLoss / 2) + (-pointLoss / 2)) := by
            rw [← Real.rpow_add hδn_pos]
          rw [h10]
          have h11 : (pointLoss / 2) + (-pointLoss / 2) = 0 := by ring
          rw [h11]
          simp
        rw [← ENNReal.ofReal_mul (by positivity), h9]
        <;> simp
      have h_final : ENNReal.ofReal (δ_n^(pointLoss / 2)) * Ncover δ_n (S0 '' P) ≤
          Ncover δ_n config.pointSet := by
        calc ENNReal.ofReal (δ_n^(pointLoss / 2)) * Ncover δ_n (S0 '' P)
          ≤ ENNReal.ofReal (δ_n^(pointLoss / 2)) *
              (ENNReal.ofReal (δ_n^(-pointLoss / 2)) * Ncover δ_n config.pointSet) := h7
        _ = (ENNReal.ofReal (δ_n^(pointLoss / 2)) * ENNReal.ofReal (δ_n^(-pointLoss / 2))) *
              Ncover δ_n config.pointSet := by rw [← mul_assoc]
        _ = (1 : ENNReal) * Ncover δ_n config.pointSet := by rw [h8]
        _ = Ncover δ_n config.pointSet := by rw [one_mul]
      exact h_final

    -- Step 5: Transfer regularity from P to S0 '' P at scale δ/4
    let hS0_sset_general : ∀ {t C : ℝ}, IsDeltaSSet δ t C P →
        IsDeltaSSet (δ / 4) t (C * (4 : ℝ)^t) (S0 '' P) := by
      intro t C h
      have h1_raw : IsDeltaSSet ((1 / 4 : ℝ) * δ) t (C * (1 / 4 : ℝ)^(-t)) (scale '' P) :=
        rescale_sset_euclidean (show (0 : ℝ) < 1 / 4 by norm_num) h
      have h_scale_eq : (1 / 4 : ℝ) * δ = δ / 4 := by ring
      have h_pow : (1 / 4 : ℝ)^(-t) = (4 : ℝ)^t := by
        have h_pos4 : 0 < (4 : ℝ) := by norm_num
        have h1 : (1 / 4 : ℝ) = (4 : ℝ)^(-1 : ℝ) := by norm_num
        rw [h1]
        have h2 : ((4 : ℝ)^(-1 : ℝ))^(-t) = (4 : ℝ)^((-1 : ℝ) * (-t)) := by
          rw [← Real.rpow_mul h_pos4.le]
        rw [h2]
        congr 1 <;> ring
      have h_C_eq : C * (1 / 4 : ℝ)^(-t) = C * (4 : ℝ)^t := by rw [h_pow]
      have h1 : IsDeltaSSet (δ / 4) t (C * (4 : ℝ)^t) (scale '' P) := by
        rw [h_scale_eq, h_C_eq] at h1_raw
        exact h1_raw
      have h2 : IsDeltaSSet (δ / 4) t (C * (4 : ℝ)^t) (transl '' (scale '' P)) :=
        translate_sset_euclidean h1
      have h3 : transl '' (scale '' P) = S0 '' P := by
        ext z; simp only [Set.mem_image]
        constructor
        · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, by simp [S0_apply, transl, scale]⟩
        · rintro ⟨x, hx, rfl⟩; exact ⟨scale x, ⟨x, hx, rfl⟩, by simp [S0_apply, transl, scale]⟩
      rw [h3] at h2
      exact h2
    have hK_in_nonneg : 0 ≤ K_in := by
      dsimp only [K_in]
      exact Real.rpow_nonneg hδ_pos.le (-εReg)
    let hS0_regular : IsSquareRootRegular (δ / 4) u C_in K_in (S0 '' P) :=
      scale_squareRootRegular (hK_nonneg := hK_in_nonneg)
        hδ_pos hδ_le_one (by linarith) hS0_sset_general h_ncover_S0 hReg

    -- Step 6: Define P_oriented and prove properties
    let P_oriented : Set Plane := S0 '' (P'' : Set Plane)
    have hP_oriented_sub : P_oriented ⊆ config.pointSet := by
      intro y hy
      rcases hy with ⟨p, hp, rfl⟩
      have h_q : pointToSquare p ∈ P0 := Finset.mem_image_of_mem _ hp
      have h_in : S0 p ∈ (pointToSquare p).toSet := hPointToSquare_mem p
      exact Set.mem_iUnion₂.mpr ⟨pointToSquare p, h_q, h_in⟩
    have h_occupied : ∀ q ∈ config.P₀, (q.toSet ∩ P_oriented).Nonempty := by
      intro q hq
      have hq' : q ∈ P0 := by
        have h_eq : config.P₀ = P0 := by rfl
        rw [h_eq] at hq
        exact hq
      rcases hPointSquare_internal q hq' with ⟨p, hp, h_eq, hSp⟩
      exact ⟨S0 p, hSp, ⟨p, hp, rfl⟩⟩
    have hP_oriented_sub_P : P_oriented ⊆ S0 '' P := by
      intro y hy
      rcases hy with ⟨p, hp, rfl⟩
      have h_p_in_P : p ∈ P := hP_mem p (hP''sub hp)
      exact ⟨p, h_p_in_P, rfl⟩
    have hP_oriented_nonempty : P_oriented.Nonempty := by
      rcases hP''nonempty with ⟨p, hp⟩
      exact ⟨S0 p, ⟨p, hp, rfl⟩⟩

    -- Step 7: Call local regularity transfer
    have hC_in_pos : 0 < C_in := by
      dsimp only [C_in]
      exact mul_pos (Real.rpow_pos_of_pos hδ_pos _) (by positivity)
    have hK_in_pos : 0 < K_in := by
      dsimp only [K_in]
      exact Real.rpow_pos_of_pos hδ_pos _
    have h_transfer := local_config_pointSet_regular_transfer
      (δ := δ')
      (δ_n := dyadicDelta n)
      (u := u)
      (C := C_in)
      (K := K_in)
      (P := S0 '' P)
      (P_oriented := P_oriented)
      (swapped := false)
      (rho_mass := pointLoss / 2)
      (hδn_pos := hδn_pos)
      (hδ_pos := hδ'_pos)
      (hδn_leδ := hδn_le')
      (hδ_lt4δn := hδn_lt')
      (hu_pos := lt_trans hs_pos hst)
      (hC_pos := hC_in_pos)
      (hK_pos := hK_in_pos)
      (hrho_mass_nonneg := by linarith)
      (hδn_le_one := hδn_le_one)
      (hδn_eq := by rfl)
      (hP_regular := hS0_regular)
      (hP_oriented_sub := hP_oriented_sub)
      (h_occupied := h_occupied)
      (h_swapped_false := fun (_ : false = false) => hP_oriented_sub_P)
      (h_swapped_true := fun (h : false = true) => False.elim (by contradiction))
      (h_mass := h_mass)
      (hP_oriented_nonempty := hP_oriented_nonempty)

    -- Output constants match C_P_reg, K_P_reg by definition
    have hC_out : (81 * (Real.rpow δ (-εReg) * (4 : ℝ)^u) * (4 : ℝ)^u * C_geom^2 * (1 + Real.sqrt 2)^u * (dyadicDelta n)^(-(pointLoss / 2))) = C_P_reg := by
      dsimp only [C_P_reg, C_geom]
      have h_exp : (-(pointLoss / 2) : ℝ) = -pointLoss / 2 := by ring
      rw [h_exp]
      <;> ring
    have hK_out : (Real.rpow δ (-εReg) * 9 * C_geom) = K_P_reg := by
      dsimp only [K_P_reg, C_geom] <;> rfl
    have h1_sset : IsDeltaSSet (dyadicDelta n) u C_P_reg config.pointSet := by
      have h_orig := h_transfer.1
      exact h_orig.weaken_C (le_of_eq hC_out)
    have h2_sqrt : Ncover (Real.sqrt (dyadicDelta n)) config.pointSet ≤
        ENNReal.ofReal (K_P_reg * Real.rpow (dyadicDelta n) (-u / 2)) := by
      have h_orig := h_transfer.2
      have h_eq : ENNReal.ofReal ((Real.rpow δ (-εReg) * 9 * C_geom) * Real.rpow (dyadicDelta n) (-u / 2)) =
          ENNReal.ofReal (K_P_reg * Real.rpow (dyadicDelta n) (-u / 2)) := by
        rw [hK_out]
      rw [h_eq] at h_orig
      exact h_orig
    exact ⟨h1_sset, h2_sqrt⟩

  have h_T0_card : T0.card ≤ 12 * 16^n := by
    have h1 : T0 ⊆ allTubes := by
      intro T hT
      rcases Finset.mem_biUnion.mp hT with ⟨q_sub, hq, hT'⟩
      let q : DyadicSquare n := q_sub.val
      have hq' : q ∈ P0 := q_sub.property
      let rp := rep q hq'
      have hrp : rp ∈ P'' := hrep_P'' q hq'
      have hrp' : rp ∈ P_fin := hP''sub hrp
      have hT_snapped : T ∈ snapped rp hrp' := by
        have h2 : T ∈ F_total rp := hTF_sub rp hrp hT'
        rw [hF_total_eq rp hrp'] at h2
        exact h2
      exact h_snapped_sub_all rp hrp' hT_snapped
    have h2 : T0.card ≤ allTubes.card := Finset.card_le_card h1
    have h3 : allTubes.card ≤ 12 * 16^n := exact_m_frontend_allTubes_bound n
    exact le_trans h2 h3

  have hCP_bound : 0 ≤ C_P_reg ∧ C_P_reg ≤ (dyadicDelta n)^(-(εReg + pointLoss)) := by
    have h_pos : 0 ≤ C_P_reg := by
      dsimp only [C_P_reg]
      have h1 : 0 < Real.rpow δ (-εReg) := Real.rpow_pos_of_pos hδ_pos _
      have h2 : 0 < (4 : ℝ)^u := Real.rpow_pos_of_pos (by norm_num) _
      have h3 : 0 < C_geom := by dsimp only [C_geom] <;> positivity
      have h4 : 0 < (1 + Real.sqrt 2)^u := Real.rpow_pos_of_pos (by positivity) _
      have h5 : 0 < (dyadicDelta n)^(-pointLoss / 2) := Real.rpow_pos_of_pos hδn_pos _
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1.le) h2.le) h2.le) (sq_nonneg _)) h4.le) h5.le
    have hδ_ge : δ_n ≤ δ := hδn_leδ
    have h1 : Real.rpow δ (-εReg) ≤ Real.rpow δ_n (-εReg) :=
      Real.rpow_le_rpow_of_nonpos hδn_pos hδ_ge (by linarith)
    have h2 : (4 : ℝ)^u * (4 : ℝ)^u ≤ (16 : ℝ)^2 := by
      have h21 : (4 : ℝ)^u * (4 : ℝ)^u = (16 : ℝ)^u := by
        have h : (4 : ℝ)^u * (4 : ℝ)^u = (4 : ℝ)^(u + u) := by rw [← Real.rpow_add] <;> linarith
        rw [h]
        have h22 : u + u = 2 * u := by ring
        rw [h22]
        have h23 : (4 : ℝ)^(2 * u) = ((4 : ℝ)^(2 : ℝ))^u := by
          rw [Real.rpow_mul] <;> norm_num
        rw [h23] <;> norm_num
      rw [h21]
      have h3 : (16 : ℝ)^u ≤ (16 : ℝ)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      norm_num at h3 ⊢ <;> exact h3
    have h3 : (1 + Real.sqrt 2)^u ≤ (1 + Real.sqrt 2)^(2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h4 : C_P_reg ≤ K_geom_C * δ_n^(-εReg) * δ_n^(-pointLoss / 2) := by
      dsimp only [C_P_reg, K_geom_C]
      let a1 := Real.rpow δ (-εReg)
      let b1 := δ_n^(-εReg)
      let a2 := (4 : ℝ)^u * (4 : ℝ)^u
      let b2 := (16 : ℝ)^2
      let a3 := (1 + Real.sqrt 2)^u
      let b3 := (1 + Real.sqrt 2)^2
      let c := (81 : ℝ) * C_geom^2 * δ_n^(-pointLoss / 2)
      have h3_nat : a3 ≤ b3 := by
        have h3_real : (1 + Real.sqrt 2)^u ≤ (1 + Real.sqrt 2)^(2 : ℝ) := h3
        have h_eq : (1 + Real.sqrt 2)^(2 : ℝ) = (1 + Real.sqrt 2)^2 := by norm_cast
        rw [h_eq] at h3_real
        exact h3_real
      have ha1 : 0 ≤ a1 := Real.rpow_nonneg hδ_pos.le _
      have ha2 : 0 ≤ a2 := by positivity
      have ha3 : 0 ≤ a3 := by positivity
      have hc : 0 ≤ c := by positivity
      have hb1 : 0 ≤ b1 := Real.rpow_nonneg hδn_pos.le _
      have hb2 : 0 ≤ b2 := by positivity
      have h_step1 : a1 * a2 ≤ b1 * b2 := by
        have h1a : a1 * a2 ≤ b1 * a2 := mul_le_mul_of_nonneg_right h1 ha2
        have h2a : b1 * a2 ≤ b1 * b2 := mul_le_mul_of_nonneg_left h2 hb1
        exact le_trans h1a h2a
      have h_step2 : (a1 * a2) * a3 ≤ (b1 * b2) * b3 := by
        have h1a : (a1 * a2) * a3 ≤ (b1 * b2) * a3 := mul_le_mul_of_nonneg_right h_step1 ha3
        have h2a : (b1 * b2) * a3 ≤ (b1 * b2) * b3 := mul_le_mul_of_nonneg_left h3_nat (mul_nonneg hb1 hb2)
        exact le_trans h1a h2a
      have h_final : c * ((a1 * a2) * a3) ≤ c * ((b1 * b2) * b3) :=
        mul_le_mul_of_nonneg_left h_step2 hc
      have h_lhs : (81 : ℝ) * Real.rpow δ (-εReg) * (4 : ℝ)^u * (4 : ℝ)^u * C_geom^2 * (1 + Real.sqrt 2)^u * δ_n^(-pointLoss / 2) = c * ((a1 * a2) * a3) := by
        dsimp only [a1, a2, a3, c] <;> ring
      have h_rhs : (81 : ℝ) * (16 : ℝ)^2 * C_geom^2 * (1 + Real.sqrt 2)^2 * δ_n^(-εReg) * δ_n^(-pointLoss / 2) = c * ((b1 * b2) * b3) := by
        dsimp only [b1, b2, b3, c] <;> ring
      rw [h_lhs, h_rhs]
      exact h_final
    have h5 : K_geom_C * δ_n^(-εReg) * δ_n^(-pointLoss / 2) ≤
        δ_n^(-pointLoss / 2) * δ_n^(-εReg) * δ_n^(-pointLoss / 2) := by
      have h6 : K_geom_C ≤ δ_n^(-pointLoss / 2) := h_geomC_absorb
      gcongr <;> positivity
    have h7 : δ_n^(-pointLoss / 2) * δ_n^(-εReg) * δ_n^(-pointLoss / 2) = δ_n^(-(εReg + pointLoss)) := by
      dsimp only [δ_n]
      rw [← Real.rpow_add hδn_pos, ← Real.rpow_add hδn_pos] <;> ring_nf
    rw [h7] at h5
    exact ⟨h_pos, le_trans h4 h5⟩

  have hKP_bound : 0 < K_P_reg ∧ K_P_reg ≤ (dyadicDelta n)^(-(εReg + pointLoss)) := by
    have h_pos : 0 < K_P_reg := by
      dsimp only [K_P_reg]
      have h1 : 0 < Real.rpow δ (-εReg) := Real.rpow_pos_of_pos hδ_pos _
      have h2 : 0 < C_geom := by dsimp only [C_geom] <;> positivity
      exact mul_pos (mul_pos h1 (by norm_num)) h2
    have hδ_ge : δ_n ≤ δ := hδn_leδ
    have h1 : Real.rpow δ (-εReg) ≤ Real.rpow δ_n (-εReg) :=
      Real.rpow_le_rpow_of_nonpos hδn_pos hδ_ge (by linarith)
    have h2 : K_P_reg ≤ K_geom_K * δ_n^(-εReg) := by
      dsimp only [K_P_reg, K_geom_K, C_geom]
      have h_pos1 : 0 ≤ Real.rpow δ (-εReg) := Real.rpow_nonneg hδ_pos.le _
      have h_pos2 : 0 ≤ C_geom := by dsimp only [C_geom] <;> positivity
      calc Real.rpow δ (-εReg) * 9 * C_geom
        = 9 * C_geom * Real.rpow δ (-εReg) := by ring
      _ ≤ 9 * C_geom * δ_n^(-εReg) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = K_geom_K * δ_n^(-εReg) := by dsimp only [K_geom_K, C_geom] <;> ring
    have h3 : K_geom_K * δ_n^(-εReg) ≤ δ_n^(-pointLoss) * δ_n^(-εReg) := by
      have h4 : K_geom_K ≤ δ_n^(-pointLoss) := h_geomK_absorb
      gcongr <;> positivity
    have h5 : δ_n^(-pointLoss) * δ_n^(-εReg) = δ_n^(-(εReg + pointLoss)) := by
      dsimp only [δ_n]
      rw [← Real.rpow_add hδn_pos] <;> ring_nf
    rw [h5] at h3
    exact ⟨h_pos, le_trans h2 h3⟩

  -- Global T0 provenance: every T ∈ T0 is close to some S0_line ℓ
  have h_T0_global_provenance : ∀ (T : DyadicTube n), T ∈ config.T₀ →
      ∃ (p_orig : Plane) (hp_orig : p_orig ∈ P)
        (ℓ : AffineLine) (hℓ : ℓ ∈ tubeFamily p_orig hp_orig),
      dist (DyadicCardToNcover.toAffineLine T) (S0_line ℓ) ≤ (15 / 2 : ℝ) * (δ / 4) := by
    intro T hT
    have hT_in_T0 : T ∈ T0 := by
      have h_eq : config.T₀ = T0 := by rfl
      rw [h_eq] at hT
      exact hT
    rcases Finset.mem_biUnion.mp hT_in_T0 with ⟨q_sub, hq, hT_sq⟩
    let q : DyadicSquare n := q_sub.val
    have hq' : q ∈ P0 := q_sub.property
    let rp := rep q hq'
    have hrp : rp ∈ P'' := hrep_P'' q hq'
    have hrp' : rp ∈ P_fin := hP''sub hrp
    have hT_snapped : T ∈ snapped rp hrp' := by
      have h1 : T ∈ squareTubeFamily q hq' := hT_sq
      have h2 : T ∈ F_total rp := hTF_sub rp hrp h1
      rw [hF_total_eq rp hrp'] at h2
      exact h2
    rcases Finset.mem_image.mp hT_snapped with ⟨ℓ', hℓ'_in_S0G, hT_eq⟩
    rcases Finset.mem_image.mp hℓ'_in_S0G with ⟨ℓ, hℓ_in_G, h_S0_eq⟩
    have hℓ_in_tube : ℓ ∈ tubeFamily rp (hP_mem rp hrp') := (hG_spec rp hrp').1 hℓ_in_G
    have hv0 : (LemmaE.getDirV ℓ') 0 ≠ 0 := hS0G_v0 rp hrp' ℓ' hℓ'_in_S0G
    have hm_slope : |(affineLineSlopeIntercept ℓ').1| ≤ 1 := hS0G_slope rp hrp' ℓ' hℓ'_in_S0G
    have hp_ball : S0 rp ∈ Metric.closedBall (0 : Plane) 1 :=
      hP'_ball (Set.mem_image_of_mem S0 (hP_mem rp hrp'))
    have hp_near : S0 rp ∈ Metric.cthickening (δ / 4) ℓ'.1 := hS0G_near rp hrp' ℓ' hℓ'_in_S0G
    have h_dist : dist ℓ' (DyadicCardToNcover.toAffineLine T) ≤ (15 / 2 : ℝ) * (δ / 4) := by
      rw [←hT_eq]
      exact snap_movement_bound hδ'_pos hδ'_le_one hδn_le' ℓ' (S0 rp) hv0 hm_slope hp_ball hp_near
    have h_symm : dist (DyadicCardToNcover.toAffineLine T) ℓ' ≤ (15 / 2 : ℝ) * (δ / 4) := by
      rw [dist_comm]
      exact h_dist
    have h_final : dist (DyadicCardToNcover.toAffineLine T) (S0_line ℓ) ≤ (15 / 2 : ℝ) * (δ / 4) := by
      rw [h_S0_eq]
      exact h_symm
    exact ⟨rp, hP_mem rp hrp', ℓ, hℓ_in_tube, h_final⟩

  have hC1_pos : 1 ≤ C₁_nat := by
    have h_pos_real : 0 < C₁_real := by
      dsimp only [C₁_real, C_snapped, K_snap]
      have h1 : 0 < (K_pack : ℝ) := by exact_mod_cast K_pack_pos
      have h2 : 0 < Real.rpow δ (-εReg) := Real.rpow_pos_of_pos hδ_pos _
      have h3 : 0 < (8 : ℝ)^s := Real.rpow_pos_of_pos (by norm_num) _
      have h4 : 0 < (70 : ℝ)^s := Real.rpow_pos_of_pos (by norm_num) _
      have h5 : 0 < (MainAppendix.affineLine_packing_constant : ℝ) := by positivity
      have h6 : 0 < (262144 : ℝ)^4 := by positivity
      have h7 : 0 < (MainAppendix.affineLine_packing_constant : ℝ)^5 := by positivity
      positivity
    have h : 0 < (C₁_nat : ℝ) := by
      have h_le : C₁_real ≤ (C₁_nat : ℝ) := Nat.le_ceil C₁_real
      linarith
    exact_mod_cast h

  exact ⟨n, m, C₁_nat, M, C_P_reg, K_P_reg,
    by rfl, hδn_le', hδn_lt', hM_pos, hM_bound', hC₁_bound, hC1_pos,
    hCP_bound.1, hCP_bound.2, hKP_bound.1, hKP_bound.2,
    config, hP0_nonempty, h_squares, h_tubes, h_T0_card, h_incidence,
    h_abs_mass, h_point_reg, h_card_cover, h_provenance,
    hPointSquare_provenance, hPointSet_ball, h_tube_slope,
    h_T0_global_provenance⟩


end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

end
