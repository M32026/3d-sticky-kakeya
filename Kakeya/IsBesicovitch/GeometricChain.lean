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
public import Kakeya.IsBesicovitch.B75Tubes
public import Kakeya.IsBesicovitch.VolumesAndFrostman
public import Kakeya.IsBesicovitch.ConstructTubesV3

/-!
# Geometric chain: algebraic helpers for the Katz–Tao reduction

Algebraic and cardinality lemmas that connect the geometric estimates
(B7)–(B10) into the chained inequality used in the Katz–Tao reduction.
-/

@[expose] public section

open scoped ENNReal NNReal MeasureTheory Topology Pointwise

namespace Kakeya.IsBesicovitch

/-- Algebraic helper for `_gba_geometric_chain`: convert the zpow form
`δ^(1-3) = (δ^2)⁻¹` and turn the cardinality lower bound
`c_n·ρ/C_F · δ^(1-3) ≤ |Ω|` into the linear form
`c_n·ρ ≤ C_F · |Ω| · δ^2`. -/
private lemma _gba_card_lb_alg
    {c_n ρ C_F δ N : ℝ}
    (hc_n : 0 < c_n) (hρ_pos : 0 < ρ) (hC_F_pos : 0 < C_F) (hδ_pos : 0 < δ)
    (hge : c_n * ρ / C_F * δ ^ (1 - (3 : ℤ)) ≤ N) :
    c_n * ρ ≤ C_F * N * δ ^ 2 := by
  have hδ_zpow : δ ^ (1 - (3 : ℤ)) = (δ ^ 2)⁻¹ := by
    have hsimp : (1 - (3 : ℤ)) = -((2 : ℕ) : ℤ) := by ring
    rw [hsimp, zpow_neg, zpow_natCast]
  rw [hδ_zpow] at hge
  have h_step :
      (c_n * ρ / C_F) * (δ ^ 2)⁻¹ * (C_F * δ ^ 2) ≤ N * (C_F * δ ^ 2) := by
    apply mul_le_mul_of_nonneg_right hge
    positivity
  have hC_F_ne : C_F ≠ 0 := ne_of_gt hC_F_pos
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
  have hδ2_ne : (δ ^ 2 : ℝ) ≠ 0 := pow_ne_zero _ hδ_ne
  have h_lhs :
      (c_n * ρ / C_F) * (δ ^ 2)⁻¹ * (C_F * δ ^ 2) = c_n * ρ := by
    field_simp
  linarith [h_step]

/-- Algebraic tail of `_gba_geometric_chain`: given the lower/upper-bound
mismatch `δ^((3-q)/2) · N · δ^2 ≤ 400 · Jcard · δ^3` and the cardinality
hypothesis `Jcard · δ^q ≤ 2^q`, conclude
`N · δ^2 ≤ 2 · 400 · 2^q · δ^((3-q)/2)`. -/
private lemma _gba_final_algebra
    {δ q Jcard N : ℝ} (hδ_pos : 0 < δ)
    (hJ : Jcard * δ ^ q ≤ (2 : ℝ) ^ q)
    (h_lower_upper :
      δ ^ ((3 - q) / 2) * N * δ ^ 2 ≤ 400 * Jcard * δ ^ 3) :
    N * δ ^ 2 ≤ 2 * 400 * (2 : ℝ) ^ q * δ ^ ((3 - q) / 2) := by
  have hδ_β_pos : (0 : ℝ) < δ ^ ((3 - q) / 2) := Real.rpow_pos_of_pos hδ_pos _
  have h_inv_nn : (0 : ℝ) ≤ (δ ^ ((3 - q) / 2))⁻¹ := by positivity
  have h_step1 :
      N * δ ^ 2 ≤ 400 * Jcard * δ ^ 3 * (δ ^ ((3 - q) / 2))⁻¹ := by
    have h_β_ne : δ ^ ((3 - q) / 2) ≠ 0 := ne_of_gt hδ_β_pos
    calc N * δ ^ 2
        = (δ ^ ((3 - q) / 2))⁻¹ * (δ ^ ((3 - q) / 2) * N * δ ^ 2) := by
          rw [show (δ ^ ((3 - q) / 2))⁻¹ * (δ ^ ((3 - q) / 2) * N * δ ^ 2)
                = (δ ^ ((3 - q) / 2))⁻¹ * δ ^ ((3 - q) / 2) * N * δ ^ 2 from by ring,
              inv_mul_cancel₀ h_β_ne, one_mul]
      _ ≤ (δ ^ ((3 - q) / 2))⁻¹ * (400 * Jcard * δ ^ 3) :=
          mul_le_mul_of_nonneg_left h_lower_upper h_inv_nn
      _ = 400 * Jcard * δ ^ 3 * (δ ^ ((3 - q) / 2))⁻¹ := by ring
  have hδ_three : (δ : ℝ) ^ 3 = δ ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_cast, Real.rpow_natCast]
  have hδ_three_β_inv :
      (δ : ℝ) ^ 3 * (δ ^ ((3 - q) / 2))⁻¹ = δ ^ ((3 + q) / 2) := by
    rw [hδ_three, ← Real.rpow_neg hδ_pos.le, ← Real.rpow_add hδ_pos]
    congr 1; ring
  have hcombo :
      400 * Jcard * δ ^ 3 * (δ ^ ((3 - q) / 2))⁻¹
        = 400 * Jcard * δ ^ ((3 + q) / 2) := by
    rw [show 400 * Jcard * δ ^ 3 * (δ ^ ((3 - q) / 2))⁻¹
          = (400 * Jcard) * (δ ^ 3 * (δ ^ ((3 - q) / 2))⁻¹) from by ring,
        hδ_three_β_inv]
  have h_step2 :
      N * δ ^ 2 ≤ 400 * Jcard * δ ^ ((3 + q) / 2) := by
    rw [← hcombo]; exact h_step1
  have hδ_split : δ ^ ((3 + q) / 2) = δ ^ q * δ ^ ((3 - q) / 2) := by
    rw [← Real.rpow_add hδ_pos]; congr 1; ring
  have hδ_β_nn : (0 : ℝ) ≤ δ ^ ((3 - q) / 2) := hδ_β_pos.le
  have h_step3 :
      400 * Jcard * δ ^ ((3 + q) / 2)
        ≤ 400 * (2 : ℝ) ^ q * δ ^ ((3 - q) / 2) := by
    rw [hδ_split]
    have h400 : (0 : ℝ) ≤ 400 := by norm_num
    calc 400 * Jcard * (δ ^ q * δ ^ ((3 - q) / 2))
        = 400 * (Jcard * δ ^ q) * δ ^ ((3 - q) / 2) := by ring
      _ ≤ 400 * (2 : ℝ) ^ q * δ ^ ((3 - q) / 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hJ h400) hδ_β_nn
  have h_pre :
      N * δ ^ 2 ≤ 400 * (2 : ℝ) ^ q * δ ^ ((3 - q) / 2) :=
    h_step2.trans h_step3
  have h_2pow_nn : (0 : ℝ) ≤ (2 : ℝ) ^ q * δ ^ ((3 - q) / 2) := by positivity
  have h_400_le : (400 : ℝ) ≤ 2 * 400 := by norm_num
  calc N * δ ^ 2
      ≤ 400 * (2 : ℝ) ^ q * δ ^ ((3 - q) / 2) := h_pre
    _ = 400 * ((2 : ℝ) ^ q * δ ^ ((3 - q) / 2)) := by ring
    _ ≤ 2 * 400 * ((2 : ℝ) ^ q * δ ^ ((3 - q) / 2)) :=
        mul_le_mul_of_nonneg_right h_400_le h_2pow_nn
    _ = 2 * 400 * (2 : ℝ) ^ q * δ ^ ((3 - q) / 2) := by ring

/-- Calibration helper for `_gba_geometric_chain`: given the threshold bound
`δ ≤ (1 / 1000) ^ (1 / η)` (with `η > 0`), conclude `1000 ≤ δ ^ (-η)`. -/
private lemma _gba_thousand_le_delta_pow_neg_eta
    {δ η : ℝ} (hδ_pos : 0 < δ) (hη_pos : 0 < η)
    (hδ_le_bound : δ ≤ (1 / 1000 : ℝ) ^ (1 / η)) :
    (1000 : ℝ) ≤ δ ^ (-η) := by
  have hδη_le : δ ^ η ≤ ((1 / 1000 : ℝ) ^ (1 / η)) ^ η :=
    Real.rpow_le_rpow hδ_pos.le hδ_le_bound hη_pos.le
  have h_simp : ((1 / 1000 : ℝ) ^ (1 / η)) ^ η = (1 / 1000 : ℝ) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 1000)]
    rw [show (1 / η) * η = 1 from by field_simp]
    rw [Real.rpow_one]
  rw [h_simp] at hδη_le
  rw [Real.rpow_neg hδ_pos.le]
  have hδη_pos : (0 : ℝ) < δ ^ η := Real.rpow_pos_of_pos hδ_pos _
  have h_inv : (1 / 1000 : ℝ)⁻¹ ≤ (δ ^ η)⁻¹ := inv_anti₀ hδη_pos hδη_le
  have h_inv_val : (1 / 1000 : ℝ)⁻¹ = 1000 := by norm_num
  linarith

/-- Fullness lower bound helper for `_gba_geometric_chain`: given the per-tube
shade ≥ `(1/2)·ρ·δ²` and carrier ≤ `200·δ²` data, plus the ρ-floor
`400·δ^η ≤ ρ`, the fullness ratio `(∑shade)/(∑carrier)` is at least `δ^η`. -/
private lemma _gba_full_lb
    {δ ρ η : ℝ} (hδ_pos : 0 < δ)
    (hρ_lower : 400 * δ ^ η ≤ ρ)
    {Scard : ℝ}
    {S_shade S_carrier : ℝ}
    (h_shade_sum_lower : Scard * ((1 / 2 : ℝ) * ρ * δ ^ 2) ≤ S_shade)
    (h_carrier_sum_upper : S_carrier ≤ Scard * (200 * δ ^ 2))
    (h_carrier_sum_pos : 0 < S_carrier) :
    δ ^ η ≤ S_shade / S_carrier := by
  rw [le_div_iff₀ h_carrier_sum_pos]
  have hδη_pos : (0 : ℝ) < δ ^ η := Real.rpow_pos_of_pos hδ_pos _
  have hδη_le : δ ^ η ≤ ρ / 400 := by
    have h400 : (0 : ℝ) < 400 := by norm_num
    rw [le_div_iff₀ h400]
    linarith
  calc δ ^ η * S_carrier
      ≤ δ ^ η * (Scard * (200 * δ ^ 2)) :=
        mul_le_mul_of_nonneg_left h_carrier_sum_upper hδη_pos.le
    _ ≤ (ρ / 400) * (Scard * (200 * δ ^ 2)) := by
        apply mul_le_mul_of_nonneg_right hδη_le
        exact h_carrier_sum_pos.le.trans h_carrier_sum_upper
    _ = Scard * ((1 / 2 : ℝ) * ρ * δ ^ 2) := by
        rw [show (ρ / 400) * (Scard * (200 * δ ^ 2))
              = Scard * (ρ * (200 / 400) * δ ^ 2) from by ring,
            show (200 / 400 : ℝ) = 1 / 2 from by norm_num]
        ring
    _ ≤ S_shade := h_shade_sum_lower

theorem _gba_geometric_chain
    (S : Set (EuclideanSpace ℝ (Fin 3))) (_hS : IsBesicovitch S)
    {q : ℝ} (hq_pos : 0 < q) (hq_lt_three : q < 3)
    {η : ℝ} (hη_pos : 0 < η)
    (hKE : KakeyaEstimate.{0} 3 ((3 - q) / 2) η)
    {c_n : ℝ} (hc_n : 0 < c_n) :
    ∃ B : ℝ, 0 < B ∧
    ∃ k_min : ℕ,
      ∀ ⦃k : ℕ⦄, k_min ≤ k →
        ∀ ⦃ρ Jcard : ℝ⦄
          ⦃E F : Set (EuclideanSpace ℝ (Fin 3))⦄,
          0 < ρ → ρ ≤ 1 → (1 / 2 : ℝ) ^ k ≤ 1 →
          400 * ((1 / 2 : ℝ) ^ k) ^ η ≤ ρ →
          Jcard * ((1 / 2 : ℝ) ^ k) ^ q ≤ (2 : ℝ) ^ q →
          MeasureTheory.volume.real
              (Metric.thickening ((1 / 2 : ℝ) ^ k) E) ≤
              400 * Jcard * ((1 / 2 : ℝ) ^ k) ^ 3 →
          MeasureTheory.volume
              (Metric.thickening ((1 / 2 : ℝ) ^ k) E) ≠ ⊤ →
          F ⊆ {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1} →
          ENNReal.ofReal (c_n * ρ) ≤
              (μH[(2 : ℝ)] : MeasureTheory.Measure _) F →
          (∀ ω ∈ F, ∃ a : EuclideanSpace ℝ (Fin 3),
              ENNReal.ofReal ρ ≤
                (μH[(1 : ℝ)] : MeasureTheory.Measure _)
                  (affineSegment ℝ a (a + ω) ∩ E)) →
          c_n * ρ ≤ B * ((1 / 2 : ℝ) ^ k) ^ ((3 - q) / 2) := by
  classical
  obtain ⟨C_F, hC_F_pos, hFrost⟩ := spherical_frostman_two
  obtain ⟨k_KE, hKE_apply⟩ :=
    _aux_apply_kakeya_estimate.{0} hq_pos hq_lt_three hKE
  obtain ⟨k_thresh, hk_thresh⟩ :
      ∃ N : ℕ, ((1/2 : ℝ)) ^ N ≤ (1/1000 : ℝ) ^ (1 / η) := by
    have h_bound_pos : (0 : ℝ) < (1/1000 : ℝ) ^ (1 / η) :=
      Real.rpow_pos_of_pos (by norm_num) _
    obtain ⟨N, hN⟩ : ∃ n : ℕ, ((1/2 : ℝ)) ^ n < (1/1000 : ℝ) ^ (1 / η) :=
      exists_pow_lt_of_lt_one h_bound_pos (by norm_num)
    exact ⟨N, hN.le⟩
  set B : ℝ := kakeyaLocalizationConstant * 2 * 400 * C_F * (2 : ℝ) ^ q with hB_def
  have hB_pos : 0 < B := by
    rw [hB_def, kakeyaLocalizationConstant]
    positivity
  refine ⟨B, hB_pos, max k_KE k_thresh, ?_⟩
  intro k hk_min ρ Jcard E F hρ_pos hρ_le hδ_le hρ_lower hJ hE_vol hE_finite hF_sub hF_mass hseg
  have hk_min_KE : k_KE ≤ k := le_of_max_le_left hk_min
  have hk_min_thresh : k_thresh ≤ k := le_of_max_le_right hk_min
  set δ : ℝ := (1/2 : ℝ) ^ k with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have hδ_le_one : δ ≤ 1 := hδ_le
  set σ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)) :=
    (μH[(2 : ℝ)] : MeasureTheory.Measure _).restrict
      {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1} with hσ_def
  have hσ_F : σ F = (μH[(2 : ℝ)] : MeasureTheory.Measure _) F :=
    MeasureTheory.Measure.restrict_eq_self _ hF_sub
  have hσ_F_lower : ENNReal.ofReal (c_n * ρ) ≤ σ F := by rw [hσ_F]; exact hF_mass
  have hc_n_ρ_pos : 0 < c_n * ρ := mul_pos hc_n hρ_pos
  have hFrost_σ : ∀ (x : EuclideanSpace ℝ (Fin 3)) (r : ℝ), 0 ≤ r →
      σ (Metric.closedBall x r) ≤ ENNReal.ofReal (C_F * r ^ (3 - 1)) := hFrost
  obtain ⟨Ω, hΩ_sub, hΩ_sep, hΩ_card_lb⟩ :=
    Tube.maximal_separated_subset (n := 3) (by norm_num)
      (σ := σ) hC_F_pos hFrost_σ hc_n_ρ_pos hσ_F_lower hδ_pos
  have hCard_alg : c_n * ρ ≤ C_F * (Ω.card : ℝ) * δ ^ 2 :=
    _gba_card_lb_alg hc_n hρ_pos hC_F_pos hδ_pos hΩ_card_lb
  have h_card_delta_sq :
      (Ω.card : ℝ) * δ ^ 2 ≤
        kakeyaLocalizationConstant * 2 * 400 * (2 : ℝ) ^ q * δ ^ ((3 - q) / 2) := by
    have hΩ_unit : ∀ ω ∈ Ω, ‖ω‖ = 1 := fun ω hω => hF_sub (hΩ_sub hω)
    have hΩ_seg : ∀ ω ∈ Ω, ∃ a : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal ρ ≤
          (μH[(1 : ℝ)] : MeasureTheory.Measure _)
            (affineSegment ℝ a (a + ω) ∩ E) :=
      fun ω hω => hseg ω (hΩ_sub hω)
    obtain ⟨T, h_shade_vol, h_align, h_shade_thick⟩ :=
      B7_5_construct_tubes_v3 hδ_pos hρ_pos Ω hΩ_unit hΩ_seg
    have h_carrier_vol : ∀ ω (hω : ω ∈ Ω),
        MeasureTheory.volume.real (T ω hω).carrier ≤ 200 * δ ^ 2 := by
      intro ω hω
      set Tω := T ω hω
      have h_seg_eq_image : segment ℝ Tω.x Tω.y =
          (fun θ : ℝ => (1 - θ) • Tω.x + θ • Tω.y) '' Set.Icc (0 : ℝ) 1 :=
        segment_eq_image ℝ Tω.x Tω.y
      have h_seg_compact : IsCompact (segment ℝ Tω.x Tω.y) := by
        rw [h_seg_eq_image]
        refine IsCompact.image isCompact_Icc ?_
        exact (continuous_const.sub continuous_id).smul continuous_const
          |>.add (continuous_id.smul continuous_const)
      have h_seg_closed : IsClosed (segment ℝ Tω.x Tω.y) := h_seg_compact.isClosed
      have h_eq : Tω.carrier = Metric.cthickening δ (segment ℝ Tω.x Tω.y) := by
        have h := Tω.toTube.carrier_eq
        rw [h]
        rw [show (δ.toNNReal : ℝ) = δ from Real.coe_toNNReal δ hδ_pos.le]
        rw [← h_seg_closed.cthickening_eq_biUnion_closedBall hδ_pos.le]
      rw [h_eq]
      exact volume_cthickening_unit_dist_segment_le_eucl hδ_pos hδ_le_one _ _
        Tω.toTube.dist_eq_one
    have hKT_1000 : ConvexSpaceBody.IsKatzTao (Ω.attach)
        (fun i => (T i.val i.property).toConvexSpaceBody) (1000 : ℝ≥0∞) :=
      B7_5_isKatzTao_v2 (δ_sep := δ) Ω hΩ_unit hδ_pos hδ_le_one hΩ_sep
        (Real.toNNReal_pos.mpr hδ_pos) (by rw [Real.coe_toNNReal δ hδ_pos.le]) T h_align
    have hδη_inv_pos : 0 < δ ^ (-η) := Real.rpow_pos_of_pos hδ_pos _
    have hC₀_le_δη : (1000 : ℝ) ≤ δ ^ (-η) := by
      have hδ_le_thresh : δ ≤ (1/2 : ℝ) ^ k_thresh := by
        rw [hδ_def]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hk_min_thresh
      exact _gba_thousand_le_delta_pow_neg_eta hδ_pos hη_pos
        (hδ_le_thresh.trans hk_thresh)
    have hδ_nn_eq : δ.toNNReal = (1/2 : NNReal) ^ k := by
      apply NNReal.eq
      rw [Real.coe_toNNReal δ hδ_pos.le, hδ_def, NNReal.coe_pow]
      push_cast; rfl
    have hKT_Cmax : ConvexSpaceBody.IsKatzTao (Ω.attach)
        (fun i => (T i.val i.property).toConvexSpaceBody) (ENNReal.ofReal (δ ^ (-η))) := by
      have h1 : Kakeya.maxDensity Ω.attach
          (fun i => (T i.val i.property).toConvexSpaceBody) ≤ (1000 : ℝ≥0∞) :=
        (ConvexSpaceBody.IsKatzTao_def Ω.attach
          (fun i => (T i.val i.property).toConvexSpaceBody)).mp hKT_1000
      have h2 : (1000 : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-η)) := by
        have h1000_e : (1000 : ℝ≥0∞) = ENNReal.ofReal 1000 := by
          rw [show (1000 : ℝ) = ((1000 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
          norm_num
        rw [h1000_e]
        exact ENNReal.ofReal_le_ofReal hC₀_le_δη
      exact (ConvexSpaceBody.IsKatzTao_def Ω.attach
        (fun i => (T i.val i.property).toConvexSpaceBody)).mpr (h1.trans h2)
    have h_full : ∀ s' ⊆ Ω.attach, s'.Nonempty →
        ShadedBody.fullness s'
          (fun i => (T i.val i.property).toShadedBody) ≥ δ ^ η := by
      intro s' hs' hs'_ne
      have hs'_card_pos : 0 < (s'.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr hs'_ne
      have h_shade_sum_lower :
          (s'.card : ℝ) * ((1/2 : ℝ) * ρ * δ ^ 2) ≤
            ∑ i ∈ s', MeasureTheory.volume.real (T i.val i.property).shade := by
        have h1 : (s'.card) • ((1/2 : ℝ) * ρ * δ ^ 2) ≤
            ∑ i ∈ s', MeasureTheory.volume.real (T i.val i.property).shade := by
          apply Finset.card_nsmul_le_sum
          intro i hi
          exact h_shade_vol i.val i.property
        simpa [nsmul_eq_mul] using h1
      have h_carrier_sum_upper :
          ∑ i ∈ s', MeasureTheory.volume.real (T i.val i.property).carrier ≤
            (s'.card : ℝ) * (200 * δ ^ 2) := by
        have h1 : ∑ i ∈ s', MeasureTheory.volume.real (T i.val i.property).carrier ≤
            (s'.card) • (200 * δ ^ 2 : ℝ) := by
          apply Finset.sum_le_card_nsmul
          intro i hi
          exact h_carrier_vol i.val i.property
        simpa [nsmul_eq_mul] using h1
      have h_carrier_sum_pos :
          0 < ∑ i ∈ s', MeasureTheory.volume.real (T i.val i.property).carrier := by
        have h_shade_le_carrier : ∀ i ∈ s',
            MeasureTheory.volume.real (T i.val i.property).shade ≤
            MeasureTheory.volume.real (T i.val i.property).carrier := by
          intro i _
          exact MeasureTheory.measureReal_mono (T i.val i.property).shade_subset
            (T i.val i.property).isCompact'.measure_lt_top.ne
        have h_lower :
            (s'.card : ℝ) * ((1/2 : ℝ) * ρ * δ ^ 2) ≤
              ∑ i ∈ s', MeasureTheory.volume.real (T i.val i.property).carrier := by
          apply h_shade_sum_lower.trans
          exact Finset.sum_le_sum h_shade_le_carrier
        have hp : 0 < (s'.card : ℝ) * ((1/2 : ℝ) * ρ * δ ^ 2) := by positivity
        exact hp.trans_le h_lower
      have h_full_real :
          δ ^ η ≤
            (∑ i ∈ s', MeasureTheory.volume.real (T i.val i.property).shade) /
            (∑ i ∈ s', MeasureTheory.volume.real (T i.val i.property).carrier) :=
        _gba_full_lb hδ_pos hρ_lower
          h_shade_sum_lower h_carrier_sum_upper h_carrier_sum_pos
      have hδη_pos : (0 : ℝ) < δ ^ η := Real.rpow_pos_of_pos hδ_pos _
      have h_carrier_top : ∀ i ∈ s',
          MeasureTheory.volume (T i.val i.property).carrier ≠ ⊤ := fun i _ =>
        (T i.val i.property).isCompact'.measure_ne_top
      have h_shade_top : ∀ i ∈ s',
          MeasureTheory.volume (T i.val i.property).shade ≠ ⊤ := fun i hi =>
        ne_top_of_le_ne_top (h_carrier_top i hi)
          (MeasureTheory.measure_mono (T i.val i.property).shade_subset)
      have h_sum_carrier_top :
          (∑ i ∈ s', MeasureTheory.volume (T i.val i.property).carrier) ≠ ⊤ := by
        exact (ENNReal.sum_lt_top.mpr
          (fun i hi => (h_carrier_top i hi).lt_top)).ne
      have h_sum_shade_top :
          (∑ i ∈ s', MeasureTheory.volume (T i.val i.property).shade) ≠ ⊤ := by
        exact (ENNReal.sum_lt_top.mpr
          (fun i hi => (h_shade_top i hi).lt_top)).ne
      have h_sum_carrier_pos_e :
          0 < ∑ i ∈ s', MeasureTheory.volume (T i.val i.property).carrier := by
        have : (0 : ℝ) <
            (∑ i ∈ s',
                MeasureTheory.volume (T i.val i.property).carrier).toReal := by
          rw [ENNReal.toReal_sum (fun i hi => h_carrier_top i hi)]
          simpa [MeasureTheory.measureReal_def] using h_carrier_sum_pos
        exact (ENNReal.toReal_pos_iff.mp this).1
      have h_full_ne_top : ShadedBody.fullness' s'
          (fun i => (T i.val i.property).toShadedBody) ≠ ⊤ :=
        ShadedBody.fullness'_ne_top _ _
      have h_full_toReal :
          ((ShadedBody.fullness s'
            (fun i => (T i.val i.property).toShadedBody) : NNReal) : ℝ) =
          (ShadedBody.fullness' s'
            (fun i => (T i.val i.property).toShadedBody)).toReal := by
        rw [show ((ShadedBody.fullness s'
            (fun i => (T i.val i.property).toShadedBody) : NNReal) : ℝ) =
            ((ShadedBody.fullness s'
              (fun i => (T i.val i.property).toShadedBody) : NNReal) : ℝ≥0∞).toReal
          from by rw [ENNReal.coe_toReal]]
        rw [ShadedBody.coe_fullness]
      have h_fullness'_eq :
          (ShadedBody.fullness' s'
            (fun i => (T i.val i.property).toShadedBody)).toReal =
          (∑ i ∈ s', MeasureTheory.volume.real (T i.val i.property).shade) /
          (∑ i ∈ s', MeasureTheory.volume.real (T i.val i.property).carrier) := by
        unfold ShadedBody.fullness'
        rw [ENNReal.toReal_div, ENNReal.toReal_sum (fun i hi => h_shade_top i hi),
          ENNReal.toReal_sum (fun i hi => h_carrier_top i hi)]
        simp [MeasureTheory.measureReal_def]
      change (δ ^ η : ℝ) ≤ ((ShadedBody.fullness s'
        (fun i => (T i.val i.property).toShadedBody) : NNReal) : ℝ)
      rw [h_full_toReal, h_fullness'_eq]
      exact h_full_real
    have hKE_apply_at_k := hKE_apply hk_min_KE
    rw [← hδ_nn_eq] at hKE_apply_at_k
    have h_const_eq :
        ((δ.toNNReal : ℝ≥0∞)) ^ (-η) = ENNReal.ofReal (δ ^ (-η)) := by
      have : (δ.toNNReal : ℝ≥0∞) = ENNReal.ofReal δ := rfl
      rw [this, ← ENNReal.ofReal_rpow_of_pos hδ_pos]
    have hKT_Cmax' : ConvexSpaceBody.IsKatzTao Ω.attach
        (fun i => (T i.val i.property).toConvexSpaceBody)
        ((((1/2 : NNReal) ^ k : NNReal) : ℝ≥0∞) ^ (-η)) := by
      rw [show (((1/2 : NNReal) ^ k : NNReal) : ℝ≥0∞) = ((δ.toNNReal : NNReal) : ℝ≥0∞)
            from by rw [hδ_nn_eq], h_const_eq]
      exact hKT_Cmax
    have h_pow_real :
        ((δ.toNNReal ^ η : NNReal) : ℝ) = δ ^ η := by
      rw [NNReal.coe_rpow, Real.coe_toNNReal δ hδ_pos.le]
    have h_full' : ∀ s' ⊆ Ω.attach, s'.Nonempty →
        ShadedBody.fullness s' (fun i => (T i.val i.property).toShadedBody) ≥
          δ.toNNReal ^ η := by
      intro s' hs' hs'_ne
      rw [ge_iff_le, ← NNReal.coe_le_coe, h_pow_real]
      exact h_full s' hs' hs'_ne
    have h_KE : MeasureTheory.volume.real
          (⋃ i ∈ Ω.attach, (T i.val i.property).shade) ≥
        (δ ^ ((3 - q) / 2) * (Ω.attach.card : ℝ) * δ ^ 2) /
          kakeyaLocalizationConstant := by
      have h_KE' := hKE_apply_at_k (↥Ω) Ω.attach
        (fun i => T i.val i.property) hKT_Cmax' h_full'
      have hδ_real : ((1/2 : ℝ) ^ k) = δ := hδ_def.symm
      rw [hδ_real] at h_KE'
      exact h_KE'
    set E' : Set (EuclideanSpace ℝ (Fin 3)) := Metric.thickening δ E with hE'_def
    have hE'_vol : MeasureTheory.volume.real E' ≤ 400 * Jcard * δ ^ 3 := hE_vol
    have hE'_finite' : MeasureTheory.volume E' ≠ ∞ := hE_finite
    have h_shade_sub : ∀ ω (hω : ω ∈ Ω), (T ω hω).shade ⊆ E' :=
      fun ω hω => h_shade_thick ω hω
    have hE'_vol_400 : MeasureTheory.volume.real E' ≤ (400 * Jcard) * δ ^ 3 := by
      have := hE'_vol; linarith
    have hB10 :=
      B10_containment (Jcard := 400 * Jcard) hδ_pos T hE'_finite' h_shade_sub
        hE'_vol_400
    have h_iUnion_eq :
        (⋃ i ∈ Ω.attach, (T i.val i.property).shade) =
        (⋃ ω : Ω.attach, (T ω.val.val ω.val.property).shade) := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi, hx⟩; exact ⟨⟨i, hi⟩, hx⟩
      · rintro ⟨ω, hx⟩; exact ⟨ω.val, ω.property, hx⟩
    have h_KE' :
        (δ ^ ((3 - q) / 2) * (Ω.attach.card : ℝ) * δ ^ 2) /
            kakeyaLocalizationConstant ≤
        MeasureTheory.volume.real
          (⋃ ω : Ω.attach, (T ω.val.val ω.val.property).shade) := by
      have := h_KE
      rw [h_iUnion_eq] at this
      exact this
    have h_lower_upper :
        δ ^ ((3 - q) / 2) * ((Ω.attach.card : ℝ) / 729) * δ ^ 2 ≤
          400 * Jcard * δ ^ 3 := by
      calc
        δ ^ ((3 - q) / 2) * ((Ω.attach.card : ℝ) / 729) * δ ^ 2 =
            (δ ^ ((3 - q) / 2) * (Ω.attach.card : ℝ) * δ ^ 2) /
              kakeyaLocalizationConstant := by
          rw [kakeyaLocalizationConstant]
          ring
        _ ≤ 400 * Jcard * δ ^ 3 := h_KE'.trans hB10
    have hdiv := _gba_final_algebra hδ_pos hJ h_lower_upper
    rw [Finset.card_attach] at hdiv
    rw [kakeyaLocalizationConstant]
    nlinarith
  calc c_n * ρ
      ≤ C_F * (Ω.card : ℝ) * δ ^ 2 := hCard_alg
    _ = C_F * ((Ω.card : ℝ) * δ ^ 2) := by ring
    _ ≤ C_F * (kakeyaLocalizationConstant * 2 * 400 * (2 : ℝ) ^ q *
          δ ^ ((3 - q) / 2)) :=
        mul_le_mul_of_nonneg_left h_card_delta_sq hC_F_pos.le
    _ = B * δ ^ ((3 - q) / 2) := by rw [hB_def]; ring

/-- (B7–B10, combined geometric core.)  Given a Besicovitch set `S ⊂ ℝ³`, the Kakeya estimate at
exponent `(3 - q) / 2` and the spherical-measure constant `c_n > 0`, there is an absolute `C > 0`
such that every scale `k` carrying the (B1) cardinality bound together with a set `F` of
directions with `μH² F ≥ c_n · ρ` whose segments meet `E` in measure `≥ ρ` obeys
`ρ ≤ C · δ_k^{(3 - q) / 2}`. -/
theorem geometric_bound_at_scale
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : IsBesicovitch S)
    {q : ℝ} (hq_pos : 0 < q) (hq_lt_three : q < 3)
    {η : ℝ} (hη_pos : 0 < η) (hKE : KakeyaEstimate.{0} 3 ((3 - q) / 2) η)
    {c_n : ℝ} (hc_n : 0 < c_n) :
    ∃ C : ℝ, 0 < C ∧
    ∃ k_min : ℕ,
      ∀ ⦃k : ℕ⦄, k_min ≤ k →
        ∀ ⦃ρ Jcard : ℝ⦄
          ⦃E F : Set (EuclideanSpace ℝ (Fin 3))⦄,
          0 < ρ → ρ ≤ 1 → (1 / 2 : ℝ) ^ k ≤ 1 →
          400 * ((1 / 2 : ℝ) ^ k) ^ η ≤ ρ →
          Jcard * ((1 / 2 : ℝ) ^ k) ^ q ≤ (2 : ℝ) ^ q →
          MeasureTheory.volume.real
              (Metric.thickening ((1 / 2 : ℝ) ^ k) E) ≤
              400 * Jcard * ((1 / 2 : ℝ) ^ k) ^ 3 →
          MeasureTheory.volume
              (Metric.thickening ((1 / 2 : ℝ) ^ k) E) ≠ ⊤ →
          F ⊆ {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1} →
          ENNReal.ofReal (c_n * ρ) ≤
              (μH[(2 : ℝ)] : MeasureTheory.Measure _) F →
          (∀ ω ∈ F, ∃ a : EuclideanSpace ℝ (Fin 3),
              ENNReal.ofReal ρ ≤
                (μH[(1 : ℝ)] : MeasureTheory.Measure _)
                  (affineSegment ℝ a (a + ω) ∩ E)) →
          ρ ≤ C * ((1 / 2 : ℝ) ^ k) ^ ((3 - q) / 2) := by
  obtain ⟨B, hB_pos, k_min, hB⟩ :=
    _gba_geometric_chain S hS hq_pos hq_lt_three hη_pos hKE hc_n
  refine ⟨B / c_n, div_pos hB_pos hc_n, k_min, ?_⟩
  intro k hk_min ρ Jcard E F hρ_pos hρ_le hδ_le hρ_lower hJ hE_vol hE_finite hF_sub hF_mass hseg
  have hchain :
      c_n * ρ ≤ B * ((1 / 2 : ℝ) ^ k) ^ ((3 - q) / 2) :=
    hB hk_min (k := k) (ρ := ρ) (Jcard := Jcard) (E := E) (F := F)
      hρ_pos hρ_le hδ_le hρ_lower hJ hE_vol hE_finite hF_sub hF_mass hseg
  have hkey :
      c_n * ρ ≤ B / c_n * ((1 / 2 : ℝ) ^ k) ^ ((3 - q) / 2) * c_n := by
    have hreorg : B / c_n * ((1 / 2 : ℝ) ^ k) ^ ((3 - q) / 2) * c_n =
        B * ((1 / 2 : ℝ) ^ k) ^ ((3 - q) / 2) := by
      field_simp
    rw [hreorg]; exact hchain
  have hmul :
      ρ * c_n ≤ B / c_n * ((1 / 2 : ℝ) ^ k) ^ ((3 - q) / 2) * c_n := by
    have hcomm : c_n * ρ = ρ * c_n := by ring
    linarith [hkey]
  exact le_of_mul_le_mul_right hmul hc_n

end Kakeya.IsBesicovitch
