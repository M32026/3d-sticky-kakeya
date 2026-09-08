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
public import Mathlib

/-! ### Covering and pigeonholing for the Katz–Tao reduction

This file formalises the Hausdorff-covering and weighted-pigeonholing parts of
the Katz–Tao reduction from a shaded Kakeya estimate to the three-dimensional
Hausdorff-dimension bound.

The blueprint argument is split into named lemmas for the Hausdorff covering,
spherical, and tube machinery. The main theorem
`dimH_ge_three_of_kakeyaEstimate` glues these components together.
-/

@[expose] public section

open scoped ENNReal NNReal MeasureTheory Topology Pointwise

namespace Kakeya.IsBesicovitch

/-- From `dimH S < (3 : ℝ≥0∞)` extract a real number
`q ∈ (dimH S, 3)` with `0 < q`. Used to set up the exponent `γ := 3 - q` in
the Katz–Tao reduction. -/
theorem exists_real_between_dimH_and_three
    (S : Set (EuclideanSpace ℝ (Fin 3))) (h : dimH S < (3 : ℝ≥0∞)) :
    ∃ q : ℝ, 0 < q ∧ q < 3 ∧ dimH S < ENNReal.ofReal q := by
  have h_ne_top : dimH S ≠ ⊤ := ne_top_of_lt h
  have h_three : (3 : ℝ≥0∞) = ENNReal.ofReal 3 := by
    simp [ENNReal.ofReal_ofNat]
  have h_lt_real : (dimH S).toReal < 3 := by
    have := h
    rw [h_three] at this
    have h3 : ENNReal.ofReal 3 ≠ ⊤ := ENNReal.ofReal_ne_top
    have := (ENNReal.toReal_lt_toReal h_ne_top h3).mpr this
    rwa [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 3)] at this
  have h_nn : 0 ≤ (dimH S).toReal := ENNReal.toReal_nonneg
  refine ⟨((dimH S).toReal + 3) / 2, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · calc dimH S
        = ENNReal.ofReal (dimH S).toReal :=
          (ENNReal.ofReal_toReal h_ne_top).symm
      _ < ENNReal.ofReal (((dimH S).toReal + 3) / 2) := by
          rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg h_nn]
          linarith

/-! ### Part A: ball covering (`exists_qcover_of_dimH_lt`)

The opening "ball covering" step of the blueprint is split into three sub-lemmas:

* `hausdorffMeasure_zero_of_dimH_lt` (A1): if `dimH S < q` then `μH[q] S = 0`.
* `exists_cover_of_hausdorffMeasure_zero` (A2): if `μH[q] S = 0` then for every
  `ε > 0` and threshold `K₀`, there is a countable cover by closed balls of
  radii `≤ 2^{-K₀}` with `∑ rⱼ^q ≤ ε`.
* `exists_qcover_of_dimH_lt` (A3): assemble (A1) and (A2) at `ε = 1`.
-/

/-- (A1.) Hausdorff measure vanishes above the Hausdorff dimension.
If `dimH S < ENNReal.ofReal q` and `0 < q`, then `μH[q] S = 0`.

Proof strategy: convert the bound `dimH S < ENNReal.ofReal q` to the
`ℝ≥0`-version expected by `MeasureTheory.hausdorffMeasure_of_dimH_lt`. -/
theorem hausdorffMeasure_zero_of_dimH_lt
    {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    {q : ℝ} (hq_pos : 0 < q) (h : dimH S < ENNReal.ofReal q) :
    (μH[q] : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) S = 0 := by
  have hq_le : 0 ≤ q := le_of_lt hq_pos
  have h_eq : ENNReal.ofReal q = (q.toNNReal : ℝ≥0∞) := rfl
  have h' : dimH S < (q.toNNReal : ℝ≥0∞) := h_eq ▸ h
  have key := hausdorffMeasure_of_dimH_lt (X := EuclideanSpace ℝ (Fin n))
    (s := S) (d := q.toNNReal) h'
  have hq_eq : (q.toNNReal : ℝ) = q := Real.coe_toNNReal q hq_le
  rw [show (q : ℝ) = ((q.toNNReal : ℝ≥0) : ℝ) from hq_eq.symm]
  exact key

/-- (A2.) Existence of a fine countable ball-cover with small `q`-sum: if `μH[q] S = 0` then for
every `ε > 0` and every threshold `K₀ : ℕ` the set `S` is contained in a countable union of closed
balls `closedBall xⱼ rⱼ` with `0 < rⱼ ≤ 2^{-K₀}` and `∑ⱼ rⱼ^q ≤ ε`. -/
theorem exists_cover_of_hausdorffMeasure_zero
    {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    {q : ℝ} (hq_pos : 0 < q)
    (hH : (μH[q] : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) S = 0)
    {ε : ℝ} (hε : 0 < ε) (K₀ : ℕ) :
    ∃ (ι : Type) (x : ι → EuclideanSpace ℝ (Fin n)) (r : ι → ℝ),
      (∀ i, 0 < r i ∧ r i ≤ (1 / 2 : ℝ) ^ K₀) ∧
      S ⊆ ⋃ i, Metric.closedBall (x i) (r i) ∧
      ∑' i, (r i) ^ q ≤ ε ∧
      Summable (fun i => (r i) ^ q) := by
  classical
  set δ : ℝ := (1 / 2 : ℝ) ^ K₀ with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have h_apply :=
    MeasureTheory.Measure.hausdorffMeasure_apply (X := EuclideanSpace ℝ (Fin n)) q S
  rw [hH] at h_apply
  have hsup_zero : (⨆ (r : ℝ≥0∞) (_ : 0 < r),
      ⨅ (t : ℕ → Set (EuclideanSpace ℝ (Fin n))) (_ : S ⊆ ⋃ k, t k)
        (_ : ∀ k, Metric.ediam (t k) ≤ r),
        ∑' k, ⨆ _ : (t k).Nonempty, Metric.ediam (t k) ^ q) = 0 :=
    h_apply.symm
  have h_inner_zero : ∀ (r : ℝ≥0∞), 0 < r →
      (⨅ (t : ℕ → Set (EuclideanSpace ℝ (Fin n))) (_ : S ⊆ ⋃ k, t k)
        (_ : ∀ k, Metric.ediam (t k) ≤ r),
        ∑' k, ⨆ _ : (t k).Nonempty, Metric.ediam (t k) ^ q) = 0 := by
    intro r hr
    have h1 : (⨆ (_ : 0 < r),
        ⨅ (t : ℕ → Set (EuclideanSpace ℝ (Fin n))) (_ : S ⊆ ⋃ k, t k)
          (_ : ∀ k, Metric.ediam (t k) ≤ r),
          ∑' k, ⨆ _ : (t k).Nonempty, Metric.ediam (t k) ^ q) = 0 :=
      (ENNReal.iSup_eq_zero.mp hsup_zero) r
    rw [iSup_pos hr] at h1
    exact h1
  have hr_pos : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ_pos
  have h_inf := h_inner_zero (ENNReal.ofReal δ) hr_pos
  have hε2_pos : (0 : ℝ) < ε / 2 := by linarith
  have h_target_pos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) :=
    ENNReal.ofReal_pos.mpr hε2_pos
  have h_lt : (⨅ (t : ℕ → Set (EuclideanSpace ℝ (Fin n))) (_ : S ⊆ ⋃ k, t k)
        (_ : ∀ k, Metric.ediam (t k) ≤ ENNReal.ofReal δ),
        ∑' k, ⨆ _ : (t k).Nonempty, Metric.ediam (t k) ^ q)
      < ENNReal.ofReal (ε / 2) := by
    rw [h_inf]; exact h_target_pos
  obtain ⟨t, ht_lt⟩ := iInf_lt_iff.mp h_lt
  obtain ⟨ht_cover, ht_lt'⟩ := iInf_lt_iff.mp ht_lt
  obtain ⟨ht_diam, ht_sum_lt⟩ := iInf_lt_iff.mp ht_lt'
  have ht_sum_le : (∑' k : ℕ, ⨆ _ : (t k).Nonempty, Metric.ediam (t k) ^ q)
      ≤ ENNReal.ofReal (ε / 2) := le_of_lt ht_sum_lt
  let xn : ℕ → EuclideanSpace ℝ (Fin n) :=
    fun k => if h : (t k).Nonempty then h.choose else 0
  let bn : ℕ → ℝ :=
    fun k => min ((ε / 2 * (1/2)^(k+1)) ^ (1/q)) (δ / 2)
  have hbn_pos : ∀ k, 0 < bn k := by
    intro k
    refine lt_min ?_ (by linarith)
    apply Real.rpow_pos_of_pos
    positivity
  have hbn_le_half_delta : ∀ k, bn k ≤ δ / 2 := fun k => min_le_right _ _
  let dn : ℕ → ℝ := fun k => (Metric.ediam (t k)).toReal
  have hdn_nonneg : ∀ k, 0 ≤ dn k := fun _ => ENNReal.toReal_nonneg
  have hdn_le_delta : ∀ k, dn k ≤ δ := by
    intro k
    have hdiam_le : Metric.ediam (t k) ≤ ENNReal.ofReal δ := ht_diam k
    have h1 : (Metric.ediam (t k)).toReal ≤ (ENNReal.ofReal δ).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hdiam_le
    rw [ENNReal.toReal_ofReal hδ_nonneg] at h1
    exact h1
  let rn : ℕ → ℝ := fun k => max (dn k) (bn k)
  have hrn_pos : ∀ k, 0 < rn k :=
    fun k => lt_of_lt_of_le (hbn_pos k) (le_max_right _ _)
  have hrn_le_delta : ∀ k, rn k ≤ δ := by
    intro k
    refine max_le (hdn_le_delta k) ?_
    linarith [hbn_le_half_delta k, hδ_pos]
  refine ⟨ℕ, xn, rn, ?_, ?_, ?_⟩
  · intro k; exact ⟨hrn_pos k, hrn_le_delta k⟩
  · intro p hp
    have hp' : p ∈ ⋃ k, t k := ht_cover hp
    rcases Set.mem_iUnion.mp hp' with ⟨k, hp_k⟩
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    have ht_nonempty : (t k).Nonempty := ⟨p, hp_k⟩
    have hxn_eq : xn k = ht_nonempty.choose := by
      simp only [xn, ht_nonempty, dif_pos]
    have hxn_mem : xn k ∈ t k := by
      rw [hxn_eq]; exact ht_nonempty.choose_spec
    have hedist : edist p (xn k) ≤ Metric.ediam (t k) :=
      Metric.edist_le_ediam_of_mem hp_k hxn_mem
    have hdiam_ne_top : Metric.ediam (t k) ≠ ⊤ := by
      intro hne
      have hk := ht_diam k
      rw [hne] at hk
      exact ENNReal.ofReal_ne_top (top_le_iff.mp hk)
    have hedist_real : dist p (xn k) ≤ dn k := by
      have h1 : edist p (xn k) ≤ Metric.ediam (t k) := hedist
      have h_edist_top : edist p (xn k) ≠ ⊤ := by
        intro hne
        rw [hne] at h1
        exact hdiam_ne_top (top_le_iff.mp h1)
      have : (edist p (xn k)).toReal ≤ (Metric.ediam (t k)).toReal :=
        ENNReal.toReal_mono hdiam_ne_top h1
      rwa [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at this
    rw [Metric.mem_closedBall]
    exact le_trans hedist_real (le_max_left _ _)
  · have hbn_q_sum : ∑' k : ℕ, (bn k) ^ q ≤ ε / 2 := by
      have hbn_q_le : ∀ k, (bn k) ^ q ≤ ε / 2 * (1/2)^(k+1) := by
        intro k
        have hbn_le_arg : bn k ≤ (ε / 2 * (1/2)^(k+1)) ^ (1/q) := min_le_left _ _
        have hbn_pos_k : 0 < bn k := hbn_pos k
        calc (bn k) ^ q
            ≤ ((ε / 2 * (1/2)^(k+1)) ^ (1/q)) ^ q := by
              apply Real.rpow_le_rpow (le_of_lt hbn_pos_k) hbn_le_arg (le_of_lt hq_pos)
          _ = (ε / 2 * (1/2)^(k+1)) ^ ((1/q) * q) := by
              have h_arg_nn : (0 : ℝ) ≤ ε / 2 * (1/2)^(k+1) := by positivity
              rw [← Real.rpow_mul h_arg_nn]
          _ = ε / 2 * (1/2)^(k+1) := by
              rw [div_mul_cancel₀ _ (ne_of_gt hq_pos)]
              rw [Real.rpow_one]
      have h_geom_shift : Summable (fun k : ℕ => ((1/2 : ℝ))^(k+1)) := by
        have h_geom : Summable (fun k : ℕ => ((1/2 : ℝ))^k) :=
          summable_geometric_of_lt_one (by norm_num) (by norm_num)
        exact (summable_nat_add_iff 1).mpr h_geom
      have h_geom_sum : Summable (fun k : ℕ => ε / 2 * (1/2)^(k+1)) :=
        h_geom_shift.mul_left _
      have hbn_q_nonneg : ∀ k, 0 ≤ (bn k) ^ q := fun k =>
        Real.rpow_nonneg (le_of_lt (hbn_pos k)) _
      have hbn_q_summable : Summable (fun k : ℕ => (bn k) ^ q) :=
        Summable.of_nonneg_of_le hbn_q_nonneg hbn_q_le h_geom_sum
      calc ∑' k : ℕ, (bn k) ^ q
          ≤ ∑' k : ℕ, ε / 2 * (1/2)^(k+1) :=
            hbn_q_summable.tsum_le_tsum hbn_q_le h_geom_sum
        _ = ε / 2 * ∑' k : ℕ, ((1/2 : ℝ))^(k+1) := by rw [tsum_mul_left]
        _ = ε / 2 * 1 := by
            congr 1
            have h_geom_sum : ∑' k : ℕ, ((1/2 : ℝ))^k = 2 := tsum_geometric_two
            have h_geom_sum_shift :
                ∑' k : ℕ, ((1/2 : ℝ))^(k+1) = (1/2) * ∑' k : ℕ, ((1/2 : ℝ))^k := by
              rw [← tsum_mul_left]
              congr 1
              ext k; ring
            rw [h_geom_sum_shift, h_geom_sum]; norm_num
        _ = ε / 2 := by ring
    set Dn : ℕ → ℝ≥0∞ :=
      fun k => ⨆ _ : (t k).Nonempty, Metric.ediam (t k) ^ q with hDn_def
    have hdiam_ne_top : ∀ k, Metric.ediam (t k) ≠ ⊤ := by
      intro k hne
      have hk := ht_diam k
      rw [hne] at hk
      exact ENNReal.ofReal_ne_top (top_le_iff.mp hk)
    have hDn_ne_top : ∀ k, Dn k ≠ ⊤ := by
      intro k
      simp only [hDn_def]
      by_cases h : (t k).Nonempty
      · rw [iSup_pos h]
        exact ENNReal.rpow_ne_top_of_nonneg (le_of_lt hq_pos) (hdiam_ne_top k)
      · rw [iSup_neg h]
        exact ENNReal.zero_ne_top
    have hDn_toReal : ∀ k, (Dn k).toReal = (dn k)^q := by
      intro k
      simp only [hDn_def]
      by_cases h : (t k).Nonempty
      · rw [iSup_pos h, ← ENNReal.toReal_rpow]
      · rw [iSup_neg h]
        have hempty : t k = ∅ := Set.not_nonempty_iff_eq_empty.mp h
        change (⊥ : ℝ≥0∞).toReal = (dn k)^q
        rw [show (⊥ : ℝ≥0∞) = (0 : ℝ≥0∞) from rfl, ENNReal.toReal_zero]
        simp only [dn, hempty, Metric.ediam_empty, ENNReal.toReal_zero]
        exact (Real.zero_rpow (ne_of_gt hq_pos)).symm
    have hDn_sum : ∑' k : ℕ, Dn k ≤ ENNReal.ofReal (ε/2) := ht_sum_le
    have hdn_q_sum_le : ∑' k : ℕ, (dn k)^q ≤ ε/2 := by
      have h1 : ∑' k : ℕ, (dn k)^q = ∑' k : ℕ, (Dn k).toReal := by
        congr 1
        ext k; exact (hDn_toReal k).symm
      rw [h1]
      have h2 : (∑' k : ℕ, Dn k).toReal = ∑' k : ℕ, (Dn k).toReal :=
        ENNReal.tsum_toReal_eq hDn_ne_top
      rw [← h2]
      have h3 : (∑' k : ℕ, Dn k).toReal ≤ (ENNReal.ofReal (ε/2)).toReal := by
        apply ENNReal.toReal_mono _ hDn_sum
        exact ENNReal.ofReal_ne_top
      rwa [ENNReal.toReal_ofReal (le_of_lt hε2_pos)] at h3
    have hdn_q_nonneg : ∀ k, 0 ≤ (dn k)^q := fun k =>
      Real.rpow_nonneg (hdn_nonneg k) _
    have hdn_q_summable : Summable (fun k : ℕ => (dn k)^q) := by
      have h_eq : (fun k : ℕ => (dn k)^q) = (fun k : ℕ => (Dn k).toReal) := by
        ext k; exact (hDn_toReal k).symm
      rw [h_eq]
      have h_sum_ne_top : ∑' k : ℕ, Dn k ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt hDn_sum ENNReal.ofReal_lt_top)
      exact ENNReal.summable_toReal h_sum_ne_top
    have hbn_q_nonneg : ∀ k, 0 ≤ (bn k)^q := fun k =>
      Real.rpow_nonneg (le_of_lt (hbn_pos k)) _
    have h_geom_shift' : Summable (fun k : ℕ => ((1/2 : ℝ))^(k+1)) := by
      have h_geom : Summable (fun k : ℕ => ((1/2 : ℝ))^k) :=
        summable_geometric_of_lt_one (by norm_num) (by norm_num)
      exact (summable_nat_add_iff 1).mpr h_geom
    have h_geom_sum' : Summable (fun k : ℕ => ε / 2 * (1/2)^(k+1)) :=
      h_geom_shift'.mul_left _
    have hbn_q_le' : ∀ k, (bn k)^q ≤ ε / 2 * (1/2)^(k+1) := by
      intro k
      have hbn_le_arg : bn k ≤ (ε / 2 * (1/2)^(k+1)) ^ (1/q) := min_le_left _ _
      have h_arg_nn : (0 : ℝ) ≤ ε / 2 * (1/2)^(k+1) := by positivity
      calc (bn k) ^ q
          ≤ ((ε / 2 * (1/2)^(k+1)) ^ (1/q)) ^ q := by
            apply Real.rpow_le_rpow (le_of_lt (hbn_pos k)) hbn_le_arg (le_of_lt hq_pos)
        _ = (ε / 2 * (1/2)^(k+1)) ^ ((1/q) * q) := by
            rw [← Real.rpow_mul h_arg_nn]
        _ = ε / 2 * (1/2)^(k+1) := by
            rw [div_mul_cancel₀ _ (ne_of_gt hq_pos), Real.rpow_one]
    have hbn_q_summable : Summable (fun k : ℕ => (bn k)^q) :=
      Summable.of_nonneg_of_le hbn_q_nonneg hbn_q_le' h_geom_sum'
    have hrn_q_le : ∀ k, (rn k)^q ≤ (dn k)^q + (bn k)^q := by
      intro k
      rcases le_total (dn k) (bn k) with hle | hle
      · have hmax : rn k = bn k := by simp only [rn, max_eq_right hle]
        rw [hmax]; linarith [hdn_q_nonneg k]
      · have hmax : rn k = dn k := by simp only [rn, max_eq_left hle]
        rw [hmax]; linarith [hbn_q_nonneg k]
    have hrn_q_nonneg : ∀ k, 0 ≤ (rn k)^q := fun k =>
      Real.rpow_nonneg (le_of_lt (hrn_pos k)) _
    have h_sum_summable : Summable (fun k : ℕ => (dn k)^q + (bn k)^q) :=
      hdn_q_summable.add hbn_q_summable
    have hrn_q_summable : Summable (fun k : ℕ => (rn k)^q) :=
      Summable.of_nonneg_of_le hrn_q_nonneg hrn_q_le h_sum_summable
    refine ⟨?_, hrn_q_summable⟩
    calc ∑' k : ℕ, (rn k)^q
        ≤ ∑' k : ℕ, ((dn k)^q + (bn k)^q) :=
          hrn_q_summable.tsum_le_tsum hrn_q_le h_sum_summable
      _ = ∑' k : ℕ, (dn k)^q + ∑' k : ℕ, (bn k)^q :=
          hdn_q_summable.tsum_add hbn_q_summable
      _ ≤ ε/2 + ε/2 := add_le_add hdn_q_sum_le hbn_q_sum
      _ = ε := by ring

/-- (A3, blueprint "ball covering".) Hausdorff cover at exponent `q`: if `dimH S < q`, then for every
threshold `K₀ : ℕ` the set `S` admits a countable cover by closed balls with radii bounded by
`(1/2)^K₀` whose `q`-th power radii sum to at most `1`. -/
theorem exists_qcover_of_dimH_lt
    {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    {q : ℝ} (hq_pos : 0 < q) (h : dimH S < ENNReal.ofReal q) (K₀ : ℕ) :
    ∃ (ι : Type) (x : ι → EuclideanSpace ℝ (Fin n)) (r : ι → ℝ),
      (∀ i, 0 < r i ∧ r i ≤ (1 / 2 : ℝ) ^ K₀) ∧
      S ⊆ ⋃ i, Metric.closedBall (x i) (r i) ∧
      ∑' i, (r i) ^ q ≤ 1 ∧
      Summable (fun i => (r i) ^ q) := by
  have h_zero := hausdorffMeasure_zero_of_dimH_lt S hq_pos h
  exact exists_cover_of_hausdorffMeasure_zero S hq_pos h_zero
    (by norm_num : (0 : ℝ) < 1) K₀

/-- The inverse-square pigeonhole weights
`w_k = c₀ / (k + 1)²`, with `c₀ > 0` chosen so that the total mass is
strictly less than `1/2`. This is the "weighted pigeonhole principle" weight construction from
the blueprint. -/
theorem exists_inverseSquare_weights :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      Summable (fun k : ℕ ↦ c₀ / ((k : ℝ) + 1) ^ 2) ∧
      ∑' k : ℕ, c₀ / ((k : ℝ) + 1) ^ 2 < (1 / 2 : ℝ) := by
  have hsum_base : Summable (fun k : ℕ ↦ 1 / ((k : ℝ) + 1) ^ 2) := by
    have h : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h2 : Summable (fun k : ℕ ↦ 1 / ((k + 1 : ℕ) : ℝ) ^ 2) :=
      (summable_nat_add_iff 1).mpr h
    refine h2.congr ?_
    intro k
    push_cast
    ring
  set S : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 with hS_def
  have hS_nonneg : 0 ≤ S := by
    refine tsum_nonneg ?_
    intro k
    have hk : 0 ≤ ((k : ℝ) + 1) ^ 2 := by positivity
    positivity
  refine ⟨1 / (4 * S + 1), ?_, ?_, ?_⟩
  · have : 0 < 4 * S + 1 := by linarith
    positivity
  · have := hsum_base.mul_left (1 / (4 * S + 1))
    refine (this).congr ?_
    intro k
    ring
  · have hpos : 0 < 4 * S + 1 := by linarith
    have h_eq :
        ∑' k : ℕ, (1 / (4 * S + 1)) / ((k : ℝ) + 1) ^ 2 =
          (1 / (4 * S + 1)) * S := by
      rw [hS_def]
      rw [show (fun k : ℕ ↦ (1 / (4 * S + 1)) / ((k : ℝ) + 1) ^ 2)
            = fun k : ℕ ↦ (1 / (4 * S + 1)) * (1 / ((k : ℝ) + 1) ^ 2) from
          funext (fun k ↦ by ring)]
      exact tsum_mul_left
    have h_tsum_eq :
        ∑' k : ℕ, (1 / (4 * S + 1)) / ((k : ℝ) + 1) ^ 2 = S / (4 * S + 1) := by
      rw [h_eq]; ring
    rw [h_tsum_eq]
    rw [div_lt_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
    linarith

/-! ### Part B: dyadic and spherical pigeonholing

This file contains steps B1–B6 of the contradiction argument. Throughout this
block we use the dyadic notation `δ_k := (1/2)^k` and the inverse-square weights
`w_k := c₀ / (k - K₀ + 1)²`. The geometric and measure-theoretic objects attached
to a cover `B(xⱼ, rⱼ)` are:

* dyadic indexing `J_k := {j : 2^{-(k+1)} < rⱼ ≤ 2^{-k}}`;
* inflated balls `E_k := ⋃_{j ∈ J_k} closedBall xⱼ (C·δ_k)` and a slightly
  larger version `E'_k` used as the "shading container";
* per-direction line `L_ω` from the Besicovitch property;
* good-direction set `F_k := {ω : H¹(L_ω ∩ E_k) ≥ w_k}`;
The later geometric steps are in `GeometricChain`, and `Assembly` combines them
with these pigeonholing results.
-/

/-- (B1.) Dyadic decomposition of a `q`-cover: for a cover with radii `r i ∈ (0, 2^{-K₀}]` whose
`q`-sum is at most `1`, the index set partitions into the sets
`J_k := {i | 2^{-(k+1)} < r i ≤ 2^{-k}}` (`k ≥ K₀`), each of cardinality at most `2^{(k+1)q}`. -/
theorem dyadic_partition_of_cover
    {ι : Type} {r : ι → ℝ} {q : ℝ} (hq_pos : 0 < q) {K₀ : ℕ}
    (hr : ∀ i, 0 < r i ∧ r i ≤ (1 / 2 : ℝ) ^ K₀)
    (hsum : ∑' i, (r i) ^ q ≤ 1)
    (hsummable : Summable (fun i => (r i) ^ q)) :
    ∃ J : ℕ → Set ι,
      (∀ k, k < K₀ → J k = ∅) ∧
      (∀ i, ∃ k, K₀ ≤ k ∧ i ∈ J k) ∧
      Pairwise (fun a b => Disjoint (J a) (J b)) ∧
      (∀ k i, i ∈ J k →
          (1 / 2 : ℝ) ^ (k + 1) < r i ∧ r i ≤ (1 / 2 : ℝ) ^ k) ∧
      (∀ k, ∃ hfin : (J k).Finite,
          (hfin.toFinset.card : ℝ) * ((1 / 2 : ℝ) ^ k) ^ q ≤ (2 : ℝ) ^ q) := by
  classical
  have h12_pos : (0 : ℝ) < 1 / 2 := by norm_num
  have h12_le_one : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have h12_lt_one : (1 / 2 : ℝ) < 1 := by norm_num
  have hpow_anti : ∀ {a b : ℕ}, a ≤ b → (1 / 2 : ℝ) ^ b ≤ (1 / 2 : ℝ) ^ a := by
    intro a b hab
    exact pow_le_pow_of_le_one h12_pos.le h12_le_one hab
  have hpow_pos : ∀ k : ℕ, 0 < (1 / 2 : ℝ) ^ k := fun k => pow_pos h12_pos k
  let J : ℕ → Set ι := fun k =>
    {i | (1 / 2 : ℝ) ^ (k + 1) < r i ∧ r i ≤ (1 / 2 : ℝ) ^ k}
  refine ⟨J, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    ext i
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, _⟩
    have h2 : r i ≤ (1 / 2 : ℝ) ^ K₀ := (hr i).2
    have hKle : k + 1 ≤ K₀ := hk
    have h3 : (1 / 2 : ℝ) ^ K₀ ≤ (1 / 2 : ℝ) ^ (k + 1) := hpow_anti hKle
    linarith
  · intro i
    have hri_pos : 0 < r i := (hr i).1
    have hri_le : r i ≤ (1 / 2 : ℝ) ^ K₀ := (hr i).2
    let Q : ℕ → Prop := fun k => (1 / 2 : ℝ) ^ (k + 1) < r i
    have hex : ∃ k, Q k := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / r i) (by norm_num : (1 : ℝ) < 2)
      refine ⟨n, ?_⟩
      simp only [Q]
      have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
      have h_inv : (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n := by
        rw [one_div, inv_pow, one_div]
      have : (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ n := hpow_anti (Nat.le_succ n)
      have hh1 : (1 / 2 : ℝ) ^ n < r i := by
        rw [h_inv]
        rw [div_lt_iff₀ h2n_pos]
        rw [div_lt_iff₀ hri_pos] at hn
        linarith
      linarith
    let k := Nat.find hex
    have hQk : Q k := Nat.find_spec hex
    have hk_min : ∀ m, m < k → ¬ Q m := fun m hm => Nat.find_min hex hm
    have hKle : K₀ ≤ k := by
      by_contra hneg
      push Not at hneg
      have hk1 : k + 1 ≤ K₀ := hneg
      have hh2 : r i ≤ (1 / 2 : ℝ) ^ (k + 1) := le_trans hri_le (hpow_anti hk1)
      have hQk' : (1 / 2 : ℝ) ^ (k + 1) < r i := hQk
      linarith
    refine ⟨k, hKle, hQk, ?_⟩
    by_cases hk0 : k = 0
    · rw [hk0]
      rw [hk0] at hKle
      have hKzero : K₀ = 0 := Nat.le_zero.mp hKle
      rw [hKzero] at hri_le
      simpa using hri_le
    · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
      have hsub : k - 1 < k := Nat.sub_lt hk_pos Nat.one_pos
      have hnQ : ¬ Q (k - 1) := hk_min (k - 1) hsub
      have hkeq : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
      simp only [Q, hkeq] at hnQ
      push Not at hnQ
      exact hnQ
  · intro a b hab
    rw [Set.disjoint_iff_inter_eq_empty]
    ext i
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩
    rcases lt_or_gt_of_ne hab with h | h
    · have : (1 / 2 : ℝ) ^ b ≤ (1 / 2 : ℝ) ^ (a + 1) := hpow_anti h
      linarith
    · have : (1 / 2 : ℝ) ^ a ≤ (1 / 2 : ℝ) ^ (b + 1) := hpow_anti h
      linarith
  · intro k i hi; exact hi
  · intro k
    set c : ℝ := ((1 / 2 : ℝ) ^ (k + 1)) ^ q with hc_def
    have hpow_kp1_pos : 0 < (1 / 2 : ℝ) ^ (k + 1) := hpow_pos (k + 1)
    have hc_pos : 0 < c := Real.rpow_pos_of_pos hpow_kp1_pos q
    have h_rq_nn : ∀ i, 0 ≤ (r i) ^ q := fun i =>
      Real.rpow_nonneg (hr i).1.le q
    have h_rq_gt : ∀ i ∈ J k, c < (r i) ^ q := by
      intro i hi
      have h1 : (1 / 2 : ℝ) ^ (k + 1) < r i := hi.1
      exact Real.rpow_lt_rpow hpow_kp1_pos.le h1 hq_pos
    have h_threshold_finite : {i | c ≤ (r i) ^ q}.Finite := by
      by_contra h_not_finite
      rw [Set.not_finite] at h_not_finite
      have h_partial : ∀ n : ℕ, ∃ s : Finset ι, (n : ℝ) * c ≤ ∑ i ∈ s, (r i) ^ q := by
        intro n
        obtain ⟨s, hs_sub, hs_card⟩ := h_not_finite.exists_subset_card_eq n
        refine ⟨s, ?_⟩
        have h1 : ∀ i ∈ s, c ≤ (r i) ^ q := fun i hi => hs_sub hi
        calc (n : ℝ) * c
            = (s.card : ℝ) * c := by rw [hs_card]
          _ = ∑ _ ∈ s, c := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ i ∈ s, (r i) ^ q := Finset.sum_le_sum h1
      have h_bound : ∀ s : Finset ι, ∑ i ∈ s, (r i) ^ q ≤ ∑' i, (r i) ^ q :=
        fun s => hsummable.sum_le_tsum s (fun i _ => h_rq_nn i)
      have h_n_bound : ∀ n : ℕ, (n : ℝ) * c ≤ 1 := by
        intro n
        obtain ⟨s, hs⟩ := h_partial n
        exact hs.trans ((h_bound s).trans hsum)
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / c)
      have hn_pos : (0 : ℝ) < n := by
        have h1c : 0 < 1 / c := by positivity
        linarith
      have : (n : ℝ) * c > 1 := by
        have := (div_lt_iff₀ hc_pos).mp hn
        linarith
      linarith [h_n_bound n]
    have hJk_sub : J k ⊆ {i | c ≤ (r i) ^ q} := by
      intro i hi
      exact (h_rq_gt i hi).le
    have hfin : (J k).Finite := h_threshold_finite.subset hJk_sub
    refine ⟨hfin, ?_⟩
    set F := hfin.toFinset
    have hF_mem : ∀ i ∈ F, c < (r i) ^ q := by
      intro i hi
      apply h_rq_gt i
      exact (Set.Finite.mem_toFinset hfin).mp hi
    have h_card_c_le_sum : (F.card : ℝ) * c ≤ ∑ i ∈ F, (r i) ^ q := by
      calc (F.card : ℝ) * c
          = ∑ _ ∈ F, c := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ i ∈ F, (r i) ^ q := Finset.sum_le_sum (fun i hi => (hF_mem i hi).le)
    have h_sum_le_tsum : ∑ i ∈ F, (r i) ^ q ≤ ∑' i, (r i) ^ q :=
      hsummable.sum_le_tsum F (fun i _ => h_rq_nn i)
    have h_card_c_le_one : (F.card : ℝ) * c ≤ 1 :=
      (h_card_c_le_sum.trans h_sum_le_tsum).trans hsum
    have hpow_k_pos : 0 < (1 / 2 : ℝ) ^ k := hpow_pos k
    have h_two_pos : (0 : ℝ) < 2 := by norm_num
    have h_2q_pos : 0 < (2 : ℝ) ^ q := Real.rpow_pos_of_pos h_two_pos q
    have hk_eq : ((1 / 2 : ℝ) ^ k) ^ q = (2 : ℝ) ^ q * c := by
      have h_split : (1 / 2 : ℝ) ^ k = 2 * (1 / 2 : ℝ) ^ (k + 1) := by
        rw [pow_succ]; ring
      rw [h_split]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hpow_kp1_pos.le]
    rw [hk_eq]
    have hF_card_nn : (0 : ℝ) ≤ F.card := by exact_mod_cast Nat.zero_le _
    calc (F.card : ℝ) * ((2 : ℝ) ^ q * c)
        = (2 : ℝ) ^ q * ((F.card : ℝ) * c) := by ring
      _ ≤ (2 : ℝ) ^ q * 1 := by
          apply mul_le_mul_of_nonneg_left h_card_c_le_one h_2q_pos.le
      _ = (2 : ℝ) ^ q := by ring

/-- (B2.) The cover is contained in `⋃_k E_k`: given a cover `B(xⱼ, rⱼ)` of `S` and the dyadic
partition `J_k` from (B1), the inflated dyadic unions
`E_k := ⋃_{j ∈ J_k} closedBall xⱼ (C·2^{-k})` (any `C ≥ 1`) satisfy `S ⊆ ⋃_{k ≥ K₀} E_k`. -/
theorem cover_subset_union_Ek
    {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {ι : Type} {x : ι → EuclideanSpace ℝ (Fin n)} {r : ι → ℝ}
    {K₀ : ℕ} {C : ℝ} (hC : 1 ≤ C)
    (_hr : ∀ i, 0 < r i ∧ r i ≤ (1 / 2 : ℝ) ^ K₀)
    (hcover : S ⊆ ⋃ i, Metric.closedBall (x i) (r i))
    {J : ℕ → Set ι}
    (hJ_part : ∀ i, ∃ k, K₀ ≤ k ∧ i ∈ J k)
    (hJ_radii : ∀ k i, i ∈ J k → r i ≤ (1 / 2 : ℝ) ^ k) :
    S ⊆ ⋃ (k : ℕ) (_ : K₀ ≤ k), ⋃ i ∈ J k,
      Metric.closedBall (x i) (C * (1 / 2 : ℝ) ^ k) := by
  intro p hp
  have hpc := hcover hp
  rw [Set.mem_iUnion] at hpc
  obtain ⟨i, hi⟩ := hpc
  obtain ⟨k, hKk, hiJk⟩ := hJ_part i
  have hri_le : r i ≤ (1 / 2 : ℝ) ^ k := hJ_radii k i hiJk
  have hpow_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
  have hpow_le : (1 / 2 : ℝ) ^ k ≤ C * (1 / 2 : ℝ) ^ k := by
    have : 1 * (1 / 2 : ℝ) ^ k ≤ C * (1 / 2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right hC hpow_nn
    simpa using this
  have hp_in : p ∈ Metric.closedBall (x i) (C * (1 / 2 : ℝ) ^ k) := by
    rw [Metric.mem_closedBall] at hi ⊢
    exact hi.trans (hri_le.trans hpow_le)
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  refine Set.mem_iUnion.mpr ⟨hKk, ?_⟩
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  exact Set.mem_iUnion.mpr ⟨hiJk, hp_in⟩

/-- (B3.) Each Besicovitch line is covered by `⋃ E_k` in one-dimensional Hausdorff measure: for a
set `L` of unit `μH[1]`-measure contained in `⋃_{k ≥ K₀} E_k`, sub-additivity gives
`1 = H¹(L) ≤ ∑_{k ≥ K₀} H¹(L ∩ E_k)`. -/
theorem line_covered_by_Ek
    {n : ℕ} {L : Set (EuclideanSpace ℝ (Fin n))}
    (hL_meas_one : (μH[(1 : ℝ)] : MeasureTheory.Measure _) L = 1)
    {E : ℕ → Set (EuclideanSpace ℝ (Fin n))} {K₀ : ℕ}
    (hL_subset : L ⊆ ⋃ (k : ℕ) (_ : K₀ ≤ k), E k) :
    (1 : ℝ≥0∞) ≤ ∑' k : ℕ,
      (μH[(1 : ℝ)] : MeasureTheory.Measure _) (L ∩ E k) := by
  set μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)) := μH[(1 : ℝ)] with hμ
  have hL_sub_union : L ⊆ ⋃ k : ℕ, L ∩ E k := by
    intro p hp
    have hp' : p ∈ ⋃ (k : ℕ) (_ : K₀ ≤ k), E k := hL_subset hp
    rcases hp' with ⟨_, ⟨k, rfl⟩, hpk⟩
    rcases hpk with ⟨_, ⟨_hk, rfl⟩, hpEk⟩
    exact Set.mem_iUnion.mpr ⟨k, hp, hpEk⟩
  have h1 : μ L ≤ μ (⋃ k : ℕ, L ∩ E k) := MeasureTheory.measure_mono hL_sub_union
  have h2 : μ (⋃ k : ℕ, L ∩ E k) ≤ ∑' k : ℕ, μ (L ∩ E k) :=
    MeasureTheory.measure_iUnion_le _
  have h3 : μ L ≤ ∑' k : ℕ, μ (L ∩ E k) := h1.trans h2
  rw [hL_meas_one] at h3
  exact h3

/-- (B4.) Per-direction weighted pigeonhole on `[K₀, ∞)`: if `1 ≤ ∑_k aₖ` in `ℝ≥0∞` and `w` is
summable with `∑_k wₖ < 1/2`, then `wₖ ≤ aₖ` for some `k`.  The `Summable w` hypothesis is needed:
without it `∑' k, w k` is `0` by Mathlib convention, so `hw_sum` carries no information. -/
theorem weighted_pigeonhole_direction
    {a : ℕ → ℝ≥0∞} {w : ℕ → ℝ}
    (hw_nn : ∀ k, 0 ≤ w k) (hw_summable : Summable w)
    (hw_sum : ∑' k : ℕ, w k < (1 / 2 : ℝ))
    (ha_sum : (1 : ℝ≥0∞) ≤ ∑' k : ℕ, a k) :
    ∃ k : ℕ, ENNReal.ofReal (w k) ≤ a k := by
  by_contra h
  push Not at h
  have step1 : (∑' k, a k) ≤ ∑' k, ENNReal.ofReal (w k) :=
    ENNReal.tsum_le_tsum (fun k => (h k).le)
  have step2 : (∑' k, ENNReal.ofReal (w k)) = ENNReal.ofReal (∑' k, w k) :=
    (ENNReal.ofReal_tsum_of_nonneg hw_nn hw_summable).symm
  have hhalf : ENNReal.ofReal (∑' k, w k) < ENNReal.ofReal (1/2 : ℝ) :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1/2)).mpr hw_sum
  have hhalf_lt_one : ENNReal.ofReal (1/2 : ℝ) < 1 := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr (by norm_num)
  have hcontr : (1 : ℝ≥0∞) < 1 :=
    lt_of_le_of_lt ha_sum
      (lt_of_le_of_lt (step1.trans step2.le) (hhalf.trans hhalf_lt_one))
  exact lt_irrefl _ hcontr

/-- (B5.) The "good-direction" sets `F_k` cover the sphere: if every `ω ∈ Ω` lies in some `F k`
with `k ≥ K₀`, then `Ω ⊆ ⋃_{k ≥ K₀} F_k`. -/
theorem Fk_covers_sphere
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {F : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    {K₀ : ℕ}
    (hF : ∀ ω ∈ Ω, ∃ k, K₀ ≤ k ∧ ω ∈ F k) :
    Ω ⊆ ⋃ (k : ℕ) (_ : K₀ ≤ k), F k := by
  intro ω hω
  obtain ⟨k, hk, hωk⟩ := hF ω hω
  simp only [Set.mem_iUnion]
  exact ⟨k, hk, hωk⟩

-- The case-split `simp [hk]` in this proof rewrites both branches of an `if`
-- together with closing one of them; splitting into `simp only` per branch
-- is awkward, so we scope-disable `linter.flexible` for this declaration.
set_option linter.flexible false in
/-- (B6.) Spherical pigeonhole: if a sphere of surface measure `c_n > 0` is covered by
`⋃_{k ≥ K₀} F_k` and the weights satisfy `∑ w_k < 1/2`, then some `k ≥ K₀` has `σ(F_k)` bounded
below by an absolute multiple of `w_k`. -/
theorem spherical_pigeonhole
    {n : ℕ} {σ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))}
    {Sphere : Set (EuclideanSpace ℝ (Fin n))} {F : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    {w : ℕ → ℝ} {K₀ : ℕ} {c_n : ℝ} (hc_n : 0 < c_n)
    (hw_nn : ∀ k, 0 ≤ w k) (hw_summable : Summable w)
    (hw_sum : ∑' k : ℕ, w k < (1 / 2 : ℝ))
    (hSphere_meas : σ Sphere = ENNReal.ofReal c_n)
    (hcover : Sphere ⊆ ⋃ (k : ℕ) (_ : K₀ ≤ k), F k) :
    ∃ k : ℕ, K₀ ≤ k ∧ σ (F k) ≥ ENNReal.ofReal (c_n * w k) := by
  by_contra h
  push Not at h
  set G : ℕ → Set (EuclideanSpace ℝ (Fin n)) :=
    fun k => if K₀ ≤ k then F k else ∅ with hG_def
  have hG_union : (⋃ (k : ℕ) (_ : K₀ ≤ k), F k) = ⋃ k, G k := by
    ext x
    simp only [Set.mem_iUnion, hG_def]
    constructor
    · rintro ⟨k, hk, hxk⟩
      refine ⟨k, ?_⟩
      simp [hk, hxk]
    · rintro ⟨k, hxk⟩
      by_cases hk : K₀ ≤ k
      · exact ⟨k, hk, by simpa [hk] using hxk⟩
      · simp [hk] at hxk
  have h_sphere_le : σ Sphere ≤ σ (⋃ k, G k) := by
    rw [← hG_union]
    exact MeasureTheory.measure_mono hcover
  have h_union_le : σ (⋃ k, G k) ≤ ∑' k, σ (G k) :=
    MeasureTheory.measure_iUnion_le G
  have h_pt : ∀ k, σ (G k) ≤ ENNReal.ofReal (c_n * (if K₀ ≤ k then w k else 0)) := by
    intro k
    by_cases hk : K₀ ≤ k
    · simp only [hG_def, if_pos hk]
      exact (h k hk).le
    · simp [hG_def, hk]
  have h_tsum_le : (∑' k, σ (G k)) ≤
      ∑' k, ENNReal.ofReal (c_n * (if K₀ ≤ k then w k else 0)) :=
    ENNReal.tsum_le_tsum h_pt
  set f : ℕ → ℝ := fun k => c_n * (if K₀ ≤ k then w k else 0) with hf_def
  have hf_nn : ∀ k, 0 ≤ f k := by
    intro k
    by_cases hk : K₀ ≤ k
    · simp only [hf_def, if_pos hk]
      exact mul_nonneg hc_n.le (hw_nn k)
    · simp [hf_def, hk]
  have hw_indic_nn : ∀ k, 0 ≤ (if K₀ ≤ k then w k else 0 : ℝ) := by
    intro k
    by_cases hk : K₀ ≤ k
    · simp [hk, hw_nn k]
    · simp [hk]
  have hw_indic_le : ∀ k, (if K₀ ≤ k then w k else 0 : ℝ) ≤ w k := by
    intro k
    by_cases hk : K₀ ≤ k
    · simp [hk]
    · simp [hk]; exact hw_nn k
  have hw_indic_summable : Summable (fun k => (if K₀ ≤ k then w k else 0 : ℝ)) :=
    Summable.of_nonneg_of_le hw_indic_nn hw_indic_le hw_summable
  have hf_summable : Summable f := by
    simp only [hf_def]
    exact hw_indic_summable.mul_left c_n
  have h_convert : (∑' k, ENNReal.ofReal (f k)) = ENNReal.ofReal (∑' k, f k) :=
    (ENNReal.ofReal_tsum_of_nonneg hf_nn hf_summable).symm
  have hf_tsum_eq : (∑' k, f k) = c_n * ∑' k, (if K₀ ≤ k then w k else 0 : ℝ) := by
    simp only [hf_def]
    exact tsum_mul_left
  have h_indic_tsum_le : (∑' k, (if K₀ ≤ k then w k else 0 : ℝ)) ≤ ∑' k, w k :=
    hw_indic_summable.tsum_le_tsum hw_indic_le hw_summable
  have hf_tsum_lt : (∑' k, f k) < c_n * (1 / 2 : ℝ) := by
    rw [hf_tsum_eq]
    have h1 : c_n * (∑' k, (if K₀ ≤ k then w k else 0 : ℝ)) ≤ c_n * ∑' k, w k :=
      mul_le_mul_of_nonneg_left h_indic_tsum_le hc_n.le
    exact lt_of_le_of_lt h1 (mul_lt_mul_of_pos_left hw_sum hc_n)
  have h_half_lt : c_n * (1 / 2 : ℝ) < c_n := by
    have : c_n * (1 / 2 : ℝ) < c_n * 1 :=
      mul_lt_mul_of_pos_left (by norm_num) hc_n
    simpa using this
  have hf_tsum_lt_cn : (∑' k, f k) < c_n := lt_trans hf_tsum_lt h_half_lt
  have h_chain : ENNReal.ofReal c_n ≤ ENNReal.ofReal (∑' k, f k) := by
    calc ENNReal.ofReal c_n
        = σ Sphere := hSphere_meas.symm
      _ ≤ σ (⋃ k, G k) := h_sphere_le
      _ ≤ ∑' k, σ (G k) := h_union_le
      _ ≤ ∑' k, ENNReal.ofReal (f k) := h_tsum_le
      _ = ENNReal.ofReal (∑' k, f k) := h_convert
  have h_strict : ENNReal.ofReal (∑' k, f k) < ENNReal.ofReal c_n :=
    (ENNReal.ofReal_lt_ofReal_iff hc_n).mpr hf_tsum_lt_cn
  exact lt_irrefl _ (lt_of_le_of_lt h_chain h_strict)

end Kakeya.IsBesicovitch
