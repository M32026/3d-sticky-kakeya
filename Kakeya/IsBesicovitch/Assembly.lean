/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Kakeya.IsBesicovitch.HausdorffDim
public import Kakeya.MaximalSeparatedSubset
public import Kakeya.IsBesicovitch.PartsAB
public import Kakeya.IsBesicovitch.B75Tubes
public import Kakeya.IsBesicovitch.VolumesAndFrostman
public import Kakeya.IsBesicovitch.ConstructTubesV3
public import Kakeya.IsBesicovitch.GeometricChain

/-!
# Assembly: polynomial-vs-exponential contradiction

Combines the geometric estimates (B7)–(B10) with a real-analysis
polynomial-vs-exponential argument to produce the contradiction that drives
the Katz–Tao reduction.
-/

@[expose] public section

open scoped ENNReal NNReal MeasureTheory Topology Pointwise

namespace Kakeya.IsBesicovitch

/-- (B11a.) Polynomial growth `(m+1)^P` is eventually dominated by any positive
exponential `2^(m·s)` with `s > 0`; the ratio is bounded over `ℕ`.

This is the pure real-analysis kernel of (B11) — exposed as a free-standing
helper so that (B11) reduces to a few lines of bookkeeping. -/
theorem exists_poly_dominated_by_exp
    {P s : ℝ} (_hP : 0 < P) (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, ((m : ℝ) + 1) ^ P ≤ K * (2 : ℝ) ^ ((m : ℝ) * s) := by
  set b : ℝ := s * Real.log 2 with hb_def
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 < b := mul_pos hs hlog2
  have hzero : Filter.Tendsto (fun x : ℝ => x ^ P * Real.exp (-b * x)) Filter.atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero P b hb
  have hatTop : Filter.Tendsto (fun m : ℕ => ((m : ℝ) + 1)) Filter.atTop Filter.atTop := by
    have : Filter.Tendsto (fun m : ℕ => (m : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    simpa using this.atTop_add tendsto_const_nhds
  have hcomp : Filter.Tendsto
      (fun m : ℕ => ((m : ℝ) + 1) ^ P * Real.exp (-b * ((m : ℝ) + 1)))
      Filter.atTop (nhds 0) :=
    hzero.comp hatTop
  set f : ℕ → ℝ := fun m => ((m : ℝ) + 1) ^ P / (2 : ℝ) ^ ((m : ℝ) * s) with hf_def
  have hrewrite : ∀ m : ℕ,
      f m = Real.exp b * (((m : ℝ) + 1) ^ P * Real.exp (-b * ((m : ℝ) + 1))) := by
    intro m
    have h2 : (0 : ℝ) < 2 := by norm_num
    have hpow : (2 : ℝ) ^ ((m : ℝ) * s) = Real.exp (b * (m : ℝ)) := by
      rw [Real.rpow_def_of_pos h2]
      congr 1
      simp [hb_def]; ring
    simp only [hf_def, hpow]
    rw [div_eq_mul_inv, ← Real.exp_neg]
    rw [show -(b * (m : ℝ)) = -b * (m : ℝ) from by ring]
    rw [show Real.exp (-b * (m : ℝ)) = Real.exp b * Real.exp (-b * ((m : ℝ) + 1)) from by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  have hf_tendsto : Filter.Tendsto f Filter.atTop (nhds 0) := by
    have hmul : Filter.Tendsto
        (fun m : ℕ => Real.exp b * (((m : ℝ) + 1) ^ P * Real.exp (-b * ((m : ℝ) + 1))))
        Filter.atTop (nhds (Real.exp b * 0)) := hcomp.const_mul _
    rw [mul_zero] at hmul
    exact (Filter.Tendsto.congr (fun m => (hrewrite m).symm) hmul)
  have hbdd : BddAbove (Set.range f) := hf_tendsto.bddAbove_range
  obtain ⟨M, hM⟩ := hbdd
  refine ⟨max M 1 + 1, ?_, ?_⟩
  · linarith [le_max_right M 1]
  · intro m
    have hpos2 : (0 : ℝ) < (2 : ℝ) ^ ((m : ℝ) * s) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hfm : f m ≤ M := hM ⟨m, rfl⟩
    have hKge : f m ≤ max M 1 + 1 := by
      have : M ≤ max M 1 + 1 := by linarith [le_max_left M 1]
      linarith
    have hfm_eq : ((m : ℝ) + 1) ^ P = f m * (2 : ℝ) ^ ((m : ℝ) * s) := by
      rw [hf_def]
      field_simp
    rw [hfm_eq]
    have := mul_le_mul_of_nonneg_right hKge (le_of_lt hpos2)
    linarith

/-- (B11.) Polynomial-vs-exponential clash.  If for every `K₀` some `k ≥ K₀` satisfies
`(c₀ / (k - K₀ + 1)²)^B ≤ C · (2^{-k})^{γ/2}`, then `False`: the left-hand side is only
polynomially small in `k - K₀`, while the right-hand side is exponentially small in `k`. -/
theorem polynomial_vs_exponential_contradiction
    {q B γ c₀ C : ℝ} (_hq_pos : 0 < q) (_hq_lt : q < 3) (hB_pos : 0 < B)
    (hγ_pos : 0 < γ) (hc₀ : 0 < c₀) (hC : 0 < C)
    (h : ∀ K₀ : ℕ, ∃ k : ℕ, K₀ ≤ k ∧
        (c₀ / ((k - K₀ : ℕ) + 1 : ℝ) ^ 2) ^ B ≤
          C * ((1 / 2 : ℝ) ^ k) ^ (γ / 2)) : False := by
  have hP : (0 : ℝ) < 2 * B := by linarith
  have hs : (0 : ℝ) < γ / 2 := by linarith
  obtain ⟨K, hK_pos, hKbound⟩ := exists_poly_dominated_by_exp hP hs
  have hc₀B_pos : (0 : ℝ) < c₀ ^ B := Real.rpow_pos_of_pos hc₀ B
  set c : ℝ := (1 / 2 : ℝ) ^ (γ / 2) with hc_def
  have hc_pos : 0 < c :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) _
  have hc_lt_one : c < 1 := by
    rw [hc_def]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hs
  have hc_tendsto :
      Filter.Tendsto (fun N : ℕ => c ^ N) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hc_pos.le hc_lt_one
  have hCK_tendsto :
      Filter.Tendsto (fun N : ℕ => C * K * c ^ N) Filter.atTop (nhds (C * K * 0)) :=
    hc_tendsto.const_mul _
  rw [mul_zero] at hCK_tendsto
  have hev :
      ∀ᶠ N : ℕ in Filter.atTop, C * K * c ^ N < c₀ ^ B :=
    hCK_tendsto.eventually_lt_const hc₀B_pos
  obtain ⟨N, hN⟩ := hev.exists
  obtain ⟨k, hkN, hk_ineq⟩ := h N
  set m : ℕ := k - N with hm_def
  have hkN_eq : (k : ℕ) = N + m := by
    rw [hm_def]; omega
  have hpow_split : ((1 / 2 : ℝ) ^ k) = ((1 / 2 : ℝ) ^ N) * ((1 / 2 : ℝ) ^ m) := by
    rw [hkN_eq, pow_add]
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hm1sq_pos : (0 : ℝ) < ((m : ℝ) + 1) ^ 2 := by positivity
  have hm1sqB_pos : (0 : ℝ) < (((m : ℝ) + 1) ^ 2) ^ B :=
    Real.rpow_pos_of_pos hm1sq_pos _
  have hLHS_eq :
      (c₀ / ((m : ℝ) + 1) ^ 2) ^ B = c₀ ^ B / (((m : ℝ) + 1) ^ 2) ^ B := by
    rw [Real.div_rpow (le_of_lt hc₀) (le_of_lt hm1sq_pos)]
  have hpow_mul :
      (((m : ℝ) + 1) ^ 2) ^ B = ((m : ℝ) + 1) ^ (2 * B) := by
    rw [show (((m : ℝ) + 1) ^ 2 : ℝ) = ((m : ℝ) + 1) ^ ((2 : ℕ) : ℝ) from by
          rw [Real.rpow_natCast],
        ← Real.rpow_mul (le_of_lt hm1_pos)]
    ring_nf
  have hkmN : ((k - N : ℕ) : ℝ) = (m : ℝ) := by
    rw [hm_def]
  rw [hkmN] at hk_ineq
  have hLHS_simp :
      (c₀ / ((m : ℝ) + 1) ^ 2) ^ B * (((m : ℝ) + 1) ^ 2) ^ B = c₀ ^ B := by
    rw [hLHS_eq]
    field_simp
  have hineq2 :
      c₀ ^ B ≤ C * ((1 / 2 : ℝ) ^ k) ^ (γ / 2) * (((m : ℝ) + 1) ^ 2) ^ B := by
    have := mul_le_mul_of_nonneg_right hk_ineq (le_of_lt hm1sqB_pos)
    rw [hLHS_simp] at this
    exact this
  have h12N_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ N := by positivity
  have h12m_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ m := by positivity
  have hsplit_rpow :
      ((1 / 2 : ℝ) ^ k) ^ (γ / 2) =
        ((1 / 2 : ℝ) ^ N) ^ (γ / 2) * ((1 / 2 : ℝ) ^ m) ^ (γ / 2) := by
    rw [hpow_split,
        Real.mul_rpow (le_of_lt h12N_pos) (le_of_lt h12m_pos)]
  have hcN_eq : ((1 / 2 : ℝ) ^ N) ^ (γ / 2) = c ^ N := by
    rw [hc_def]
    rw [show ((1 / 2 : ℝ) ^ N : ℝ) = ((1 / 2 : ℝ)) ^ ((N : ℕ) : ℝ) from by
          rw [Real.rpow_natCast]]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ (γ / 2)) N]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    ring_nf
  rw [hsplit_rpow, hcN_eq] at hineq2
  have hKbound_m := hKbound m
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h12mγ_eq :
      ((1 / 2 : ℝ) ^ m) ^ (γ / 2) = (2 : ℝ) ^ (-((m : ℝ) * (γ / 2))) := by
    rw [show ((1 / 2 : ℝ) ^ m : ℝ) = ((1 / 2 : ℝ)) ^ ((m : ℕ) : ℝ) from by
          rw [Real.rpow_natCast]]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [show ((1 / 2 : ℝ) : ℝ) = (2 : ℝ)⁻¹ from by norm_num]
    rw [Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have hbound_factor :
      ((1 / 2 : ℝ) ^ m) ^ (γ / 2) * (((m : ℝ) + 1) ^ 2) ^ B ≤ K := by
    rw [h12mγ_eq, hpow_mul]
    have h2pow_neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-((m : ℝ) * (γ / 2))) :=
      Real.rpow_pos_of_pos h2_pos _
    have := mul_le_mul_of_nonneg_left hKbound_m (le_of_lt h2pow_neg_pos)
    have hsimplify :
        (2 : ℝ) ^ (-((m : ℝ) * (γ / 2))) * (K * (2 : ℝ) ^ ((m : ℝ) * (γ / 2))) = K := by
      rw [show (2 : ℝ) ^ (-((m : ℝ) * (γ / 2))) * (K * (2 : ℝ) ^ ((m : ℝ) * (γ / 2)))
            = K * ((2 : ℝ) ^ (-((m : ℝ) * (γ / 2))) * (2 : ℝ) ^ ((m : ℝ) * (γ / 2))) from by ring]
      rw [← Real.rpow_add h2_pos]
      simp
    linarith [this, hsimplify ▸ this]
  have hCcN_pos : (0 : ℝ) < C * c ^ N := by
    have : (0 : ℝ) < c ^ N := pow_pos hc_pos N
    exact mul_pos hC this
  have hcombine : c₀ ^ B ≤ C * c ^ N * K := by
    have hineq3 :
        c₀ ^ B ≤ (C * c ^ N) *
            (((1 / 2 : ℝ) ^ m) ^ (γ / 2) * (((m : ℝ) + 1) ^ 2) ^ B) := by
      have := hineq2
      linarith [this, (by ring :
        C * c ^ N * (((1 / 2 : ℝ) ^ m) ^ (γ / 2)) * (((m : ℝ) + 1) ^ 2) ^ B
          = (C * c ^ N) * (((1 / 2 : ℝ) ^ m) ^ (γ / 2) * (((m : ℝ) + 1) ^ 2) ^ B))]
    have := mul_le_mul_of_nonneg_left hbound_factor (le_of_lt hCcN_pos)
    linarith
  have hcombine2 : c₀ ^ B ≤ C * K * c ^ N := by
    have : C * c ^ N * K = C * K * c ^ N := by ring
    linarith
  linarith

/-! ### Auxiliary measure-theoretic prerequisites for the assembly tail.

These two declarations supply the assembly proof of
`false_of_qcover_kakeyaEstimate`, alongside the geometric core
`geometric_bound_at_scale`. They isolate the two clearly named pieces of classical
Hausdorff-measure data that the Katz–Tao reduction needs.
-/

/-- The 1-dimensional Hausdorff measure of a unit affine segment in `EuclideanSpace ℝ (Fin 3)`
equals `1`. -/
theorem hausdorff_one_unitSegment
    {a v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1) :
    (μH[(1 : ℝ)] : MeasureTheory.Measure _) (affineSegment ℝ a (a + v)) = 1 := by
  rw [MeasureTheory.hausdorffMeasure_affineSegment]
  rw [edist_dist, dist_self_add_right, hv]
  simp


/-- Shift identity for `ℝ≥0∞`-valued series: if `f` vanishes below `K₀`, the full series equals the
tail starting at `K₀`. -/
theorem tsum_shift_of_zero_below
    {f : ℕ → ℝ≥0∞} (K₀ : ℕ) (hzero : ∀ k, k < K₀ → f k = 0) :
    (∑' k : ℕ, f k) = ∑' j : ℕ, f (K₀ + j) := by
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun x : Function.support (fun j : ℕ => f (K₀ + j)) => K₀ + x.val)
    ?_ ?_ ?_
  · intro a b hab
    have : K₀ + a.val = K₀ + b.val := hab
    exact Subtype.ext (Nat.add_left_cancel this)
  · intro k hk
    have hk_ne : f k ≠ 0 := hk
    have hk_ge : K₀ ≤ k := by
      by_contra h
      push Not at h
      exact hk_ne (hzero k h)
    have hkeq : K₀ + (k - K₀) = k := by omega
    refine ⟨⟨k - K₀, ?_⟩, ?_⟩
    · change f (K₀ + (k - K₀)) ≠ 0
      rw [hkeq]; exact hk_ne
    · simpa using hkeq
  · intro x
    rfl

set_option maxHeartbeats 1600000 in
-- Raised heartbeat budget: the proof below combines a `tsum` reindexing
-- with an `ENNReal` summability argument that elaborates slowly.
/-- Per-direction pigeonhole step (B3+B4 for a single line `L`).  Given a line `L` with
`μH[1] L = 1` covered by `⋃ k ≥ K₀, E k`, where `E k = ∅` for `k < K₀`, and an inverse-square
weight family `w` satisfying the relevant summability and sum bound, produces a level `k ≥ K₀`
with `ofReal (w k) ≤ μH[1] (L ∩ E k)`. -/
theorem per_direction_pigeonhole
    {n : ℕ} {K₀ : ℕ} {c₀ : ℝ}
    {L : Set (EuclideanSpace ℝ (Fin n))}
    {E : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    {w : ℕ → ℝ}
    (hL_meas : (μH[(1 : ℝ)] : MeasureTheory.Measure _) L = 1)
    (hL_cover : L ⊆ ⋃ (k : ℕ) (_ : K₀ ≤ k), E k)
    (hE_empty_below : ∀ k, k < K₀ → E k = ∅)
    (hw_nn : ∀ k, 0 ≤ w k)
    (hwshift_summable : Summable (fun j : ℕ => w (K₀ + j)))
    (hshift_eq : ∀ j : ℕ, w (K₀ + j) = c₀ / ((j : ℝ) + 1) ^ 2)
    (hwlt : ∑' j : ℕ, c₀ / ((j : ℝ) + 1) ^ 2 < (1 / 2 : ℝ)) :
    ∃ k : ℕ, K₀ ≤ k ∧
      ENNReal.ofReal (w k) ≤
        (μH[(1 : ℝ)] : MeasureTheory.Measure _) (L ∩ E k) := by
  have hsum_ge : (1 : ℝ≥0∞) ≤
      ∑' k : ℕ, (μH[(1 : ℝ)] : MeasureTheory.Measure _) (L ∩ E k) :=
    line_covered_by_Ek hL_meas hL_cover
  have h_a_zero : ∀ k, k < K₀ →
      (μH[(1 : ℝ)] : MeasureTheory.Measure _) (L ∩ E k) = 0 := by
    intro k hk
    rw [hE_empty_below k hk, Set.inter_empty]
    simp
  have h_a_split :
      (∑' k : ℕ, (μH[(1 : ℝ)] : MeasureTheory.Measure _) (L ∩ E k)) =
        ∑' j : ℕ, (μH[(1 : ℝ)] : MeasureTheory.Measure _) (L ∩ E (K₀ + j)) :=
    tsum_shift_of_zero_below (f := fun k =>
      (μH[(1 : ℝ)] : MeasureTheory.Measure _) (L ∩ E k)) K₀ h_a_zero
  have hash_sum_ge : (1 : ℝ≥0∞) ≤
      ∑' j : ℕ, (μH[(1 : ℝ)] : MeasureTheory.Measure _) (L ∩ E (K₀ + j)) := by
    rw [← h_a_split]; exact hsum_ge
  have hwsh_sum_lt : (∑' j : ℕ, w (K₀ + j)) < (1 / 2 : ℝ) := by
    have htsum_eq :
        ∑' j : ℕ, w (K₀ + j) = ∑' j : ℕ, c₀ / ((j : ℝ) + 1) ^ 2 :=
      tsum_congr hshift_eq
    rw [htsum_eq]; exact hwlt
  have hwsh_nn : ∀ j, 0 ≤ w (K₀ + j) := fun j => hw_nn (K₀ + j)
  obtain ⟨j, hj⟩ :=
    weighted_pigeonhole_direction
      (a := fun j => (μH[(1 : ℝ)] : MeasureTheory.Measure _) (L ∩ E (K₀ + j)))
      (w := fun j => w (K₀ + j))
      hwsh_nn hwshift_summable hwsh_sum_lt hash_sum_ge
  exact ⟨K₀ + j, Nat.le_add_right K₀ j, hj⟩

set_option maxHeartbeats 1600000 in
-- Raised heartbeat budget: the Katz-Tao reduction body composes many
-- ENNReal/Real coercions and weight pigeonhole steps in one declaration.
/-- Core of the reduction: a Besicovitch set `S ⊂ ℝ³`, exponents `0 < q < 3`, the shaded Kakeya
estimate `KakeyaEstimate 3 ((3 - q) / 2) η` and a `q`-Hausdorff cover of `S` at every threshold
`K₀` together yield a contradiction.  The proof body chains the sub-lemmas (B1)–(B11) above. -/
theorem false_of_qcover_kakeyaEstimate
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : IsBesicovitch S)
    {q : ℝ} (hq_pos : 0 < q) (hq_lt_three : q < 3)
    {η : ℝ} (hη_pos : 0 < η) (hKE : KakeyaEstimate.{0} 3 ((3 - q) / 2) η)
    (h_cover : ∀ K₀ : ℕ,
        ∃ (ι : Type) (x : ι → EuclideanSpace ℝ (Fin 3)) (r : ι → ℝ),
          (∀ i, 0 < r i ∧ r i ≤ (1 / 2 : ℝ) ^ K₀) ∧
          S ⊆ ⋃ i, Metric.closedBall (x i) (r i) ∧
          ∑' i, (r i) ^ q ≤ 1 ∧
          Summable (fun i => (r i) ^ q)) : False := by
  classical
  obtain ⟨c₀, hc₀_pos, hwsum, hwlt⟩ := exists_inverseSquare_weights
  obtain ⟨c_n, hc_n_pos, hSphere_meas⟩ :=
    Kakeya.IsBesicovitch.HausdorffTwoUnitSphere.hausdorff_two_unitSphere
  obtain ⟨C_geo, hC_geo_pos, k_min, hC_geo⟩ :=
    geometric_bound_at_scale S hS hq_pos hq_lt_three hη_pos hKE hc_n_pos
  obtain ⟨K_dom, hK_dom_pos, hK_dom⟩ :=
    exists_poly_dominated_by_exp (P := (2 : ℝ)) (s := η) (by norm_num) hη_pos
  have h400K_pos : (0 : ℝ) < 400 * K_dom / c₀ := by
    have hh : (0 : ℝ) < 400 * K_dom := by positivity
    exact div_pos hh hc₀_pos
  have h2η_pos : (0 : ℝ) < (2 : ℝ) ^ η :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h2η_one : (1 : ℝ) < (2 : ℝ) ^ η := by
    have : (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := by simp
    rw [this]
    exact Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2) |>.mpr hη_pos
  obtain ⟨K_floor, hK_floor⟩ :
      ∃ N : ℕ, 400 * K_dom / c₀ ≤ ((2 : ℝ) ^ η) ^ N := by
    have htend : Filter.Tendsto (fun N : ℕ => ((2 : ℝ) ^ η) ^ N)
        Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt h2η_one
    exact (htend.eventually_ge_atTop (400 * K_dom / c₀)).exists
  refine polynomial_vs_exponential_contradiction
    (q := q) (B := 1) (γ := 3 - q) (c₀ := c₀) (C := C_geo)
    hq_pos hq_lt_three (by norm_num) (by linarith)
    hc₀_pos hC_geo_pos ?_
  intro K₀'
  set K₀ := max (max K₀' k_min) K_floor with hK₀_def
  obtain ⟨ι, x, r, hr, h_cov_subset, h_rq_sum, h_rq_summable⟩ := h_cover K₀
  obtain ⟨J, hJ_lt, hJ_mem, _hJ_disj, hJ_radii_full, hJ_card⟩ :=
    dyadic_partition_of_cover (r := r) hq_pos hr h_rq_sum h_rq_summable
  have hJ_radii_le : ∀ k i, i ∈ J k → r i ≤ (1 / 2 : ℝ) ^ k :=
    fun k i hi => (hJ_radii_full k i hi).2
  set E : ℕ → Set (EuclideanSpace ℝ (Fin 3)) :=
    fun k => ⋃ i ∈ J k, Metric.closedBall (x i) ((2 : ℝ) * (1 / 2 : ℝ) ^ k)
      with hE_def
  have hS_subE : S ⊆ ⋃ (k : ℕ) (_ : K₀ ≤ k), E k :=
    cover_subset_union_Ek (C := 2) (by norm_num)
      hr h_cov_subset hJ_mem hJ_radii_le
  set w : ℕ → ℝ := fun k =>
    if K₀ ≤ k then c₀ / ((k - K₀ : ℕ) + 1 : ℝ) ^ 2 else 0 with hw_def
  have hw_nn : ∀ k, 0 ≤ w k := by
    intro k
    by_cases hk : K₀ ≤ k
    · have hpos : (0 : ℝ) < ((k - K₀ : ℕ) + 1 : ℝ) ^ 2 := by positivity
      simp only [hw_def, if_pos hk]
      exact div_nonneg hc₀_pos.le hpos.le
    · simp [hw_def, hk]
  have hw_zero_below : ∀ k, k < K₀ → w k = 0 := by
    intro k hk
    have : ¬ K₀ ≤ k := not_le.mpr hk
    simp [hw_def, this]
  have hw_eq_above : ∀ k, K₀ ≤ k →
      w k = c₀ / ((k - K₀ : ℕ) + 1 : ℝ) ^ 2 := by
    intro k hk
    simp [hw_def, hk]
  have hshift_eq : ∀ j : ℕ, w (K₀ + j) = c₀ / ((j : ℝ) + 1) ^ 2 := by
    intro j
    have hk : K₀ ≤ K₀ + j := Nat.le_add_right K₀ j
    rw [hw_eq_above _ hk]
    have hsub : K₀ + j - K₀ = j := by omega
    rw [hsub]
  have hwshift_summable : Summable (fun j : ℕ => w (K₀ + j)) := by
    have : Summable (fun j : ℕ => c₀ / ((j : ℝ) + 1) ^ 2) := hwsum
    exact this.congr (fun j => (hshift_eq j).symm)
  have hw_summable : Summable w := by
    have hcomm : ∀ j : ℕ, w (K₀ + j) = w (j + K₀) := by
      intro j; congr 1; omega
    have hshift' : Summable (fun j : ℕ => w (j + K₀)) :=
      hwshift_summable.congr hcomm
    exact (summable_nat_add_iff K₀).mp hshift'
  have htsum_shift :
      ∑' j : ℕ, w (K₀ + j) = ∑' j : ℕ, c₀ / ((j : ℝ) + 1) ^ 2 :=
    tsum_congr hshift_eq
  have hsum_partial_zero : ∑ k ∈ Finset.range K₀, w k = 0 :=
    Finset.sum_eq_zero (fun k hk => hw_zero_below k (Finset.mem_range.mp hk))
  have htsum_w_eq :
      ∑' k : ℕ, w k = ∑' j : ℕ, c₀ / ((j : ℝ) + 1) ^ 2 := by
    have hsplit := hw_summable.sum_add_tsum_nat_add K₀
    rw [hsum_partial_zero, zero_add] at hsplit
    have hcommute : ∀ j, w (j + K₀) = w (K₀ + j) := by
      intro j; congr 1; omega
    have hshift2 :
        ∑' j : ℕ, w (j + K₀) = ∑' j : ℕ, w (K₀ + j) :=
      tsum_congr hcommute
    rw [hshift2] at hsplit
    rw [← hsplit, htsum_shift]
  have hw_sum_lt : ∑' k : ℕ, w k < (1 / 2 : ℝ) := by
    rw [htsum_w_eq]; exact hwlt
  set Sphere : Set (EuclideanSpace ℝ (Fin 3)) := {v | ‖v‖ = 1} with hSphere_def
  have hbesi : ∀ v ∈ Sphere, ∃ a, affineSegment ℝ a (a + v) ⊆ S :=
    fun v hv => hS.2 v hv
  let a_of : ∀ ω ∈ Sphere, EuclideanSpace ℝ (Fin 3) :=
    fun ω hω => Classical.choose (hbesi ω hω)
  have a_of_spec : ∀ ω (hω : ω ∈ Sphere),
      affineSegment ℝ (a_of ω hω) (a_of ω hω + ω) ⊆ S :=
    fun ω hω => Classical.choose_spec (hbesi ω hω)
  set F : ℕ → Set (EuclideanSpace ℝ (Fin 3)) := fun k =>
    {ω | ∃ hω : ω ∈ Sphere,
      ENNReal.ofReal (w k) ≤ (μH[(1 : ℝ)] : MeasureTheory.Measure _)
        (affineSegment ℝ (a_of ω hω) (a_of ω hω + ω) ∩ E k)} with hF_def
  have hE_empty_below : ∀ k, k < K₀ → E k = ∅ := by
    intro k hk
    change (⋃ i ∈ J k, Metric.closedBall (x i) ((2 : ℝ) * (1 / 2 : ℝ) ^ k)) = ∅
    rw [hJ_lt k hk]
    simp
  have hF_per : ∀ ω ∈ Sphere, ∃ k, K₀ ≤ k ∧ ω ∈ F k := by
    intro ω hω
    have hLsub : affineSegment ℝ (a_of ω hω) (a_of ω hω + ω) ⊆ S :=
      a_of_spec ω hω
    have hLsubE :
        affineSegment ℝ (a_of ω hω) (a_of ω hω + ω) ⊆
          ⋃ (k : ℕ) (_ : K₀ ≤ k), E k :=
      hLsub.trans hS_subE
    have hL_meas : (μH[(1 : ℝ)] : MeasureTheory.Measure _)
        (affineSegment ℝ (a_of ω hω) (a_of ω hω + ω)) = 1 :=
      hausdorff_one_unitSegment hω
    obtain ⟨k, hKk, hk_bound⟩ :=
      per_direction_pigeonhole (n := 3) (K₀ := K₀) (c₀ := c₀)
        (L := affineSegment ℝ (a_of ω hω) (a_of ω hω + ω))
        (E := E) (w := w)
        hL_meas hLsubE hE_empty_below
        hw_nn hwshift_summable hshift_eq hwlt
    exact ⟨k, hKk, hω, hk_bound⟩
  have hcover_sphere : Sphere ⊆ ⋃ (k : ℕ) (_ : K₀ ≤ k), F k :=
    Fk_covers_sphere hF_per
  set σ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)) := μH[(2 : ℝ)] with hσ_def
  obtain ⟨k₀, hKk₀, hσFk₀⟩ :=
    spherical_pigeonhole (σ := σ) (Sphere := Sphere) (F := F) (w := w)
      (K₀ := K₀) (c_n := c_n) hc_n_pos hw_nn hw_summable hw_sum_lt
      hSphere_meas hcover_sphere
  obtain ⟨hfin_k₀, hcard_k₀⟩ := hJ_card k₀
  have hwk₀_eq : w k₀ = c₀ / ((k₀ - K₀ : ℕ) + 1 : ℝ) ^ 2 :=
    hw_eq_above k₀ hKk₀
  have hk₀sub_pos : (0 : ℝ) < ((k₀ - K₀ : ℕ) + 1 : ℝ) ^ 2 := by positivity
  have hwk₀_pos : 0 < w k₀ := by
    rw [hwk₀_eq]; exact div_pos hc₀_pos hk₀sub_pos
  have hwk₀_le_one : w k₀ ≤ 1 := by
    have h1 : w k₀ ≤ ∑' k : ℕ, w k :=
      hw_summable.le_tsum k₀ (fun k _ => hw_nn k)
    linarith
  have hδ_le_one : (1 / 2 : ℝ) ^ k₀ ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hσFk₀_le : ENNReal.ofReal (c_n * w k₀) ≤
      (μH[(2 : ℝ)] : MeasureTheory.Measure _) (F k₀) := hσFk₀
  have hF_sub_sphere : F k₀ ⊆ Sphere := by
    intro ω hω
    exact hω.choose
  have hper_dir : ∀ ω ∈ F k₀, ∃ a : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (w k₀) ≤
        (μH[(1 : ℝ)] : MeasureTheory.Measure _)
          (affineSegment ℝ a (a + ω) ∩ E k₀) := by
    intro ω hω
    obtain ⟨hωS, hωshade⟩ := hω
    exact ⟨a_of ω hωS, hωshade⟩
  have hk_min_le_k₀ : k_min ≤ k₀ :=
    le_trans (le_max_right K₀' k_min) (le_trans (le_max_left _ K_floor) hKk₀)
  have hK_floor_le_k₀ : K_floor ≤ k₀ :=
    le_trans (le_max_right (max K₀' k_min) K_floor) hKk₀
  have hρ_floor : 400 * ((1 / 2 : ℝ) ^ k₀) ^ η ≤ w k₀ := by
    set m : ℕ := k₀ - K₀ with hm_def
    have hkeq : k₀ = K₀ + m := by rw [hm_def]; omega
    have hw_eq : w k₀ = c₀ / ((m : ℝ) + 1) ^ 2 := hwk₀_eq
    have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hm1sq_pos : (0 : ℝ) < ((m : ℝ) + 1) ^ 2 := by positivity
    have hpow_split : ((1 / 2 : ℝ) ^ k₀) = ((1 / 2 : ℝ) ^ K₀) * ((1 / 2 : ℝ) ^ m) := by
      rw [hkeq, pow_add]
    have h12K₀_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ K₀ := by positivity
    have h12m_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ m := by positivity
    have hsplit_rpow :
        ((1 / 2 : ℝ) ^ k₀) ^ η =
          ((1 / 2 : ℝ) ^ K₀) ^ η * ((1 / 2 : ℝ) ^ m) ^ η := by
      rw [hpow_split, Real.mul_rpow h12K₀_pos.le h12m_pos.le]
    have h12pow_neg : ∀ N : ℕ,
        ((1 / 2 : ℝ) ^ N) ^ η = (2 : ℝ) ^ (-((N : ℝ) * η)) := by
      intro N
      have : ((1 / 2 : ℝ) ^ N : ℝ) = ((1 / 2 : ℝ)) ^ ((N : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
      rw [this, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [show ((1 / 2 : ℝ) : ℝ) = (2 : ℝ)⁻¹ from by norm_num]
      rw [Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    have h2_pos : (0 : ℝ) < (2 : ℝ) := by norm_num
    have hK₀η : ((2 : ℝ) ^ η) ^ K₀ = (2 : ℝ) ^ ((K₀ : ℝ) * η) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ η) K₀,
          ← Real.rpow_mul h2_pos.le]
      ring_nf
    have hKK₀ : ((2 : ℝ) ^ η) ^ K_floor ≤ ((2 : ℝ) ^ η) ^ K₀ := by
      have h_le : K_floor ≤ K₀ := le_max_right _ _
      exact pow_le_pow_right₀ h2η_one.le h_le
    have hK₀_lower : 400 * K_dom / c₀ ≤ ((2 : ℝ) ^ η) ^ K₀ :=
      le_trans hK_floor hKK₀
    have hK₀_lower' : 400 * K_dom / c₀ ≤ (2 : ℝ) ^ ((K₀ : ℝ) * η) := by
      rw [← hK₀η]; exact hK₀_lower
    have h400K_le : 400 * K_dom ≤ c₀ * (2 : ℝ) ^ ((K₀ : ℝ) * η) := by
      have h2K₀_pos : (0 : ℝ) < (2 : ℝ) ^ ((K₀ : ℝ) * η) :=
        Real.rpow_pos_of_pos h2_pos _
      have := (div_le_iff₀ hc₀_pos).mp hK₀_lower'
      linarith
    have hpoly_m_nat : ((m : ℝ) + 1) ^ 2 ≤ K_dom * (2 : ℝ) ^ ((m : ℝ) * η) := by
      have hpm : ((m : ℝ) + 1) ^ (2 : ℝ) ≤ K_dom * (2 : ℝ) ^ ((m : ℝ) * η) :=
        hK_dom m
      have heq : ((m : ℝ) + 1) ^ (2 : ℝ) = ((m : ℝ) + 1) ^ 2 := by
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
      rw [← heq]; exact hpm
    have h2mη_pos : (0 : ℝ) < (2 : ℝ) ^ ((m : ℝ) * η) :=
      Real.rpow_pos_of_pos h2_pos _
    have h2pow_add : (2 : ℝ) ^ ((K₀ : ℝ) * η) * (2 : ℝ) ^ ((m : ℝ) * η) =
        (2 : ℝ) ^ ((k₀ : ℝ) * η) := by
      rw [← Real.rpow_add h2_pos]
      congr 1
      have hk₀_cast : (k₀ : ℝ) = (K₀ : ℝ) + (m : ℝ) := by
        rw [hkeq]; push_cast; ring
      rw [hk₀_cast]; ring
    have hclean : 400 * ((m : ℝ) + 1) ^ 2 ≤ c₀ * (2 : ℝ) ^ ((k₀ : ℝ) * η) := by
      have h400nn : (0 : ℝ) ≤ 400 := by norm_num
      have hp_scaled : 400 * ((m : ℝ) + 1) ^ 2 ≤
          400 * (K_dom * (2 : ℝ) ^ ((m : ℝ) * η)) :=
        mul_le_mul_of_nonneg_left hpoly_m_nat h400nn
      have hbridge2 : 400 * (K_dom * (2 : ℝ) ^ ((m : ℝ) * η)) =
          (400 * K_dom) * (2 : ℝ) ^ ((m : ℝ) * η) := by ring
      rw [hbridge2] at hp_scaled
      have h2 := mul_le_mul_of_nonneg_right h400K_le h2mη_pos.le
      calc 400 * ((m : ℝ) + 1) ^ 2
          ≤ (400 * K_dom) * (2 : ℝ) ^ ((m : ℝ) * η) := hp_scaled
        _ ≤ c₀ * (2 : ℝ) ^ ((K₀ : ℝ) * η) * (2 : ℝ) ^ ((m : ℝ) * η) := h2
        _ = c₀ * ((2 : ℝ) ^ ((K₀ : ℝ) * η) * (2 : ℝ) ^ ((m : ℝ) * η)) := by ring
        _ = c₀ * (2 : ℝ) ^ ((k₀ : ℝ) * η) := by rw [h2pow_add]
    have h12k₀_eq : ((1 / 2 : ℝ) ^ k₀) ^ η = (2 : ℝ) ^ (-((k₀ : ℝ) * η)) :=
      h12pow_neg k₀
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((k₀ : ℝ) * η) :=
      Real.rpow_pos_of_pos h2_pos _
    have h2recip : (2 : ℝ) ^ (-((k₀ : ℝ) * η)) = ((2 : ℝ) ^ ((k₀ : ℝ) * η))⁻¹ := by
      rw [Real.rpow_neg h2_pos.le]
    rw [hw_eq, h12k₀_eq, h2recip]
    rw [show 400 * ((2 : ℝ) ^ ((k₀ : ℝ) * η))⁻¹
          = 400 / (2 : ℝ) ^ ((k₀ : ℝ) * η) from by rw [div_eq_mul_inv]]
    rw [div_le_div_iff₀ h2pos hm1sq_pos]
    linarith
  have hδ_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k₀ := pow_nonneg (by norm_num) _
  have hδ_k₀_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ k₀ := by positivity
  have hE_thick_vol_k₀ :
      MeasureTheory.volume.real
          (Metric.thickening ((1 / 2 : ℝ) ^ k₀) (E k₀)) ≤
        400 * (hfin_k₀.toFinset.card : ℝ) * ((1 / 2 : ℝ) ^ k₀) ^ 3 :=
    volume_thickening_union_two_radius_balls_eucl (J k₀) hfin_k₀ x
      ((1 / 2 : ℝ) ^ k₀) hδ_k₀_pos
  have hE_thick_finite_k₀ :
      MeasureTheory.volume
          (Metric.thickening ((1 / 2 : ℝ) ^ k₀) (E k₀)) ≠ ⊤ :=
    volume_thickening_union_two_radius_balls_finite_eucl (J k₀) hfin_k₀ x
      ((1 / 2 : ℝ) ^ k₀) hδ_k₀_pos
  have hgeom : w k₀ ≤ C_geo * ((1 / 2 : ℝ) ^ k₀) ^ ((3 - q) / 2) :=
    hC_geo hk_min_le_k₀ hwk₀_pos hwk₀_le_one hδ_le_one hρ_floor hcard_k₀
      hE_thick_vol_k₀ hE_thick_finite_k₀ hF_sub_sphere hσFk₀_le hper_dir
  have hK₀'_le_k₀ : K₀' ≤ k₀ :=
    le_trans (le_max_left K₀' k_min)
      (le_trans (le_max_left _ K_floor) hKk₀)
  refine ⟨k₀, hK₀'_le_k₀, ?_⟩
  rw [Real.rpow_one]
  have hsub_mono : (k₀ - K₀ : ℕ) ≤ k₀ - K₀' := by
    have hle : K₀' ≤ K₀ :=
      le_trans (le_max_left K₀' k_min) (le_max_left _ K_floor)
    omega
  have hcast : ((k₀ - K₀ : ℕ) : ℝ) ≤ ((k₀ - K₀' : ℕ) : ℝ) :=
    Nat.cast_le.mpr hsub_mono
  have hdenom_le :
      (((k₀ - K₀ : ℕ) : ℝ) + 1) ^ 2 ≤ (((k₀ - K₀' : ℕ) : ℝ) + 1) ^ 2 := by
    have hbase_nn : (0 : ℝ) ≤ ((k₀ - K₀ : ℕ) : ℝ) + 1 := by positivity
    have hbase_le : ((k₀ - K₀ : ℕ) : ℝ) + 1 ≤ ((k₀ - K₀' : ℕ) : ℝ) + 1 := by
      linarith
    exact pow_le_pow_left₀ hbase_nn hbase_le 2
  have hdenom_pos : (0 : ℝ) < (((k₀ - K₀ : ℕ) : ℝ) + 1) ^ 2 := by positivity
  calc c₀ / (((k₀ - K₀' : ℕ) : ℝ) + 1) ^ 2
      ≤ c₀ / (((k₀ - K₀ : ℕ) : ℝ) + 1) ^ 2 :=
        div_le_div_of_nonneg_left hc₀_pos.le hdenom_pos hdenom_le
    _ = w k₀ := hwk₀_eq.symm
    _ ≤ C_geo * ((1 / 2 : ℝ) ^ k₀) ^ ((3 - q) / 2) := hgeom

end Kakeya.IsBesicovitch
