/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Basic

/-!
# Counting essentially distinct δ-tubes

This file collects the less elementary facts about δ-tubes that build on
`Kakeya.Tube.Basic`.  Its main result is `Tube.card_le_of_EssDistinct`: a crude
real-valued upper bound on the number of pairwise essentially distinct `δ`-tubes
contained in a ball of radius `r` centred at the origin, of the form
`C n · (r / δ) ^ (2 n)` with `n = dim E` and the explicit constant
`C n = (8 n² + 6) ^ (2 n) + 1`.
-/

open MeasureTheory ENNReal Metric

@[expose] public section

namespace Tube

private lemma homothety_subset_inter
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : NNReal} {σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (T1 T2 : Tube δ E)
    (hx : ‖T1.x - T2.x‖ ≤ σ * (δ : ℝ)) (hy : ‖T1.y - T2.y‖ ≤ σ * (δ : ℝ)) :
    (fun p : E => T2.x + (1 - σ) • (p - T2.x)) '' T2.carrier
      ⊆ T1.carrier ∩ T2.carrier := by
  have hδr : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  rintro q ⟨p, hp, rfl⟩
  change T2.x + (1 - σ) • (p - T2.x) ∈ T1.carrier ∩ T2.carrier
  refine ⟨?_, ?_⟩
  · rw [T2.carrier_eq] at hp
    rw [Set.mem_iUnion₂] at hp
    obtain ⟨z2, hz2_seg, hpz2⟩ := hp
    obtain ⟨a, b, ha, hb, hab, hz2_eq⟩ := hz2_seg
    set tt : ℝ := (1 - σ) * b with htt_def
    have htt_nn : 0 ≤ tt := mul_nonneg (by linarith) hb
    have htt_le : tt ≤ 1 := by
      have hb_le : b ≤ 1 := by linarith
      have h1 : (1 - σ) ≤ 1 := by linarith
      calc tt = (1 - σ) * b := rfl
        _ ≤ 1 * 1 := by
            apply mul_le_mul h1 hb_le hb
            linarith
        _ = 1 := by ring
    set z1 : E := T1.x + tt • (T1.y - T1.x) with hz1_def
    have hz1_seg : z1 ∈ segment ℝ T1.x T1.y := by
      refine ⟨1 - tt, tt, by linarith, htt_nn, by ring, ?_⟩
      simp only [hz1_def, smul_sub]
      match_scalars <;> ring
    have ha_eq : a = 1 - b := by linarith
    set fp : E := T2.x + (1 - σ) • (p - T2.x) with hfp_def
    set fz2 : E := T2.x + tt • (T2.y - T2.x) with hfz2_def
    have hfz2_alt : fz2 = T2.x + (1 - σ) • (z2 - T2.x) := by
      simp only [hfz2_def, htt_def]
      rw [← hz2_eq, ha_eq]
      simp only [smul_sub, sub_smul, one_smul]
      module
    have hz1_sub_fz2 : z1 - fz2 =
        (1 - tt) • (T1.x - T2.x) + tt • (T1.y - T2.y) := by
      simp only [hz1_def, hfz2_def, smul_sub, sub_smul, one_smul]
      module
    have h_z1_fz2_norm : ‖z1 - fz2‖ ≤ σ * (δ : ℝ) := by
      rw [hz1_sub_fz2]
      have h1 : ‖(1 - tt) • (T1.x - T2.x) + tt • (T1.y - T2.y)‖
          ≤ ‖(1 - tt) • (T1.x - T2.x)‖ + ‖tt • (T1.y - T2.y)‖ := norm_add_le _ _
      have h2 : ‖(1 - tt) • (T1.x - T2.x)‖ = (1 - tt) * ‖T1.x - T2.x‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by linarith)]
      have h3 : ‖tt • (T1.y - T2.y)‖ = tt * ‖T1.y - T2.y‖ := by
        rw [norm_smul, Real.norm_of_nonneg htt_nn]
      have h4 : (1 - tt) * ‖T1.x - T2.x‖ ≤ (1 - tt) * (σ * (δ : ℝ)) :=
        mul_le_mul_of_nonneg_left hx (by linarith)
      have h5 : tt * ‖T1.y - T2.y‖ ≤ tt * (σ * (δ : ℝ)) :=
        mul_le_mul_of_nonneg_left hy htt_nn
      calc ‖(1 - tt) • (T1.x - T2.x) + tt • (T1.y - T2.y)‖
          ≤ ‖(1 - tt) • (T1.x - T2.x)‖ + ‖tt • (T1.y - T2.y)‖ := h1
        _ = (1 - tt) * ‖T1.x - T2.x‖ + tt * ‖T1.y - T2.y‖ := by rw [h2, h3]
        _ ≤ (1 - tt) * (σ * (δ : ℝ)) + tt * (σ * (δ : ℝ)) := add_le_add h4 h5
        _ = σ * (δ : ℝ) := by ring
    have h_fp_fz2 : fp - fz2 = (1 - σ) • (p - z2) := by
      rw [hfz2_alt, hfp_def]
      simp only [smul_sub]
      module
    have h_fp_fz2_norm : ‖fp - fz2‖ ≤ (1 - σ) * (δ : ℝ) := by
      rw [h_fp_fz2, norm_smul, Real.norm_of_nonneg (by linarith)]
      have hpz2' : ‖p - z2‖ ≤ (δ : ℝ) := by
        rw [← dist_eq_norm]; exact hpz2
      exact mul_le_mul_of_nonneg_left hpz2' (by linarith)
    rw [T1.carrier_eq]
    refine Set.mem_iUnion₂.mpr ⟨z1, hz1_seg, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : fp - z1 = (fp - fz2) - (z1 - fz2) := by abel
    calc ‖fp - z1‖ = ‖(fp - fz2) - (z1 - fz2)‖ := by rw [this]
      _ ≤ ‖fp - fz2‖ + ‖z1 - fz2‖ := norm_sub_le _ _
      _ ≤ (1 - σ) * (δ : ℝ) + σ * (δ : ℝ) := add_le_add h_fp_fz2_norm h_z1_fz2_norm
      _ = (δ : ℝ) := by ring
  · have hconv : Convex ℝ T2.carrier := (T2.toConvexSpaceBody).convex
    have hx_mem : T2.x ∈ T2.carrier := by
      rw [T2.carrier_eq]
      refine Set.mem_iUnion₂.mpr ⟨T2.x, left_mem_segment ℝ T2.x T2.y, ?_⟩
      exact Metric.mem_closedBall_self hδr.le
    have h_combo : T2.x + (1 - σ) • (p - T2.x) = σ • T2.x + (1 - σ) • p := by
      simp only [smul_sub]; module
    rw [h_combo]
    exact hconv hx_mem hp hσ (by linarith) (by ring)

/-- **Volume scaling corollary.** Under the hypotheses of `homothety_subset_inter`
and assuming an inner-product structure on `E`, we obtain a lower bound on the
volume of `T1.carrier ∩ T2.carrier` in terms of `(1-σ)^n · volume T2.carrier`. -/
private lemma volume_inter_ge_of_homothety
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    {δ : NNReal} {σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (T1 T2 : Tube δ E)
    (hx : ‖T1.x - T2.x‖ ≤ σ * (δ : ℝ)) (hy : ‖T1.y - T2.y‖ ≤ σ * (δ : ℝ)) :
    ENNReal.ofReal ((1 - σ) ^ Module.finrank ℝ E) * volume T2.carrier
      ≤ volume (T1.carrier ∩ T2.carrier) := by
  set n := Module.finrank ℝ E
  have h_eq : (fun p : E => T2.x + (1 - σ) • (p - T2.x))
      = AffineMap.homothety T2.x (1 - σ) := by
    ext p
    rw [AffineMap.homothety_apply]
    rw [vsub_eq_sub, vadd_eq_add, add_comm]
  have h_subset := homothety_subset_inter hδ hσ hσ1 T1 T2 hx hy
  rw [h_eq] at h_subset
  have h_vol_eq : volume (AffineMap.homothety T2.x (1 - σ) '' T2.carrier)
      = ENNReal.ofReal (|((1 - σ) ^ n)|) * volume T2.carrier :=
    MeasureTheory.Measure.addHaar_image_homothety (μ := (volume : Measure E))
      T2.x (1 - σ) T2.carrier
  have h_abs : |((1 - σ) ^ n)| = (1 - σ) ^ n :=
    abs_of_nonneg (pow_nonneg (by linarith) _)
  rw [h_abs] at h_vol_eq
  calc ENNReal.ofReal ((1 - σ) ^ n) * volume T2.carrier
      = volume (AffineMap.homothety T2.x (1 - σ) '' T2.carrier) := h_vol_eq.symm
    _ ≤ volume (T1.carrier ∩ T2.carrier) := measure_mono h_subset

/-- Symmetric version: also bound by `(1-σ)^n · volume T1.carrier`. -/
private lemma volume_inter_ge_of_homothety_sym
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    {δ : NNReal} {σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (T1 T2 : Tube δ E)
    (hx : ‖T1.x - T2.x‖ ≤ σ * (δ : ℝ)) (hy : ‖T1.y - T2.y‖ ≤ σ * (δ : ℝ)) :
    ENNReal.ofReal ((1 - σ) ^ Module.finrank ℝ E) * volume T1.carrier
      ≤ volume (T1.carrier ∩ T2.carrier) := by
  have hx' : ‖T2.x - T1.x‖ ≤ σ * (δ : ℝ) := by rw [norm_sub_rev]; exact hx
  have hy' : ‖T2.y - T1.y‖ ≤ σ * (δ : ℝ) := by rw [norm_sub_rev]; exact hy
  have h := volume_inter_ge_of_homothety hδ hσ hσ1 T2 T1 hx' hy'
  rw [Set.inter_comm] at h
  exact h

/-- **ED endpoint separation (qualitative).**
If two `δ`-tubes are essentially distinct, then for any `0 ≤ σ ≤ 1` with
`(1 - σ)^n > 1/2`, we cannot have **both** endpoints close
(`‖T1.x - T2.x‖ ≤ σδ` and `‖T1.y - T2.y‖ ≤ σδ`). -/
lemma endpoint_separated_of_ed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    {δ : NNReal} {σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hσ_strong : (1 / 2 : ℝ) < (1 - σ) ^ Module.finrank ℝ E)
    (T1 T2 : Tube δ E)
    (h_ed : IsEssentiallyDistinct T1.carrier T2.carrier) :
    σ * (δ : ℝ) < ‖T1.x - T2.x‖ ∨ σ * (δ : ℝ) < ‖T1.y - T2.y‖ := by
  by_contra h
  rw [not_or, not_lt, not_lt] at h
  obtain ⟨hx, hy⟩ := h
  set n := Module.finrank ℝ E with hn_def
  set c : ℝ := (le_volume.c n : ℝ) with hc_def
  have hc_pos : 0 < c := by exact_mod_cast le_volume.c_pos n
  have hc : ∀ T : Tube δ E, c * (δ : ℝ) ^ (n - 1) ≤ volume.real T.carrier := by
    intro T
    have h := Tube.le_volume (δ := δ) T
    have hRHS_fin : (le_volume.c n : ENNReal) * (δ : ENNReal) ^ (n - 1) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    have hreal := ENNReal.toReal_mono T.isCompact.measure_lt_top.ne h
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, ENNReal.coe_toReal] at hreal
    exact hreal
  have hT1_pos : (0 : ℝ) < volume.real T1.carrier :=
    lt_of_lt_of_le (by positivity) (hc T1)
  have hT2_pos : (0 : ℝ) < volume.real T2.carrier :=
    lt_of_lt_of_le (by positivity) (hc T2)
  have hT1_fin : volume T1.carrier < ⊤ := T1.isCompact.measure_lt_top
  have hT2_fin : volume T2.carrier < ⊤ := T2.isCompact.measure_lt_top
  have hT1_pos' : (0 : ℝ≥0∞) < volume T1.carrier := by
    rw [pos_iff_ne_zero]
    intro h
    rw [measureReal_def, h, ENNReal.toReal_zero] at hT1_pos
    exact lt_irrefl _ hT1_pos
  have hT2_pos' : (0 : ℝ≥0∞) < volume T2.carrier := by
    rw [pos_iff_ne_zero]
    intro h
    rw [measureReal_def, h, ENNReal.toReal_zero] at hT2_pos
    exact lt_irrefl _ hT2_pos
  have h_vol_T2 := volume_inter_ge_of_homothety hδ hσ hσ1 T1 T2 hx hy
  have h_vol_T1 := volume_inter_ge_of_homothety_sym hδ hσ hσ1 T1 T2 hx hy
  have h_inter_fin : volume (T1.carrier ∩ T2.carrier) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_left) hT1_fin
  have h_factor_pos : 0 < (1 - σ) ^ n := lt_of_le_of_lt (by norm_num) hσ_strong
  have h_vol_T2_real : (1 - σ) ^ n * volume.real T2.carrier
      ≤ volume.real (T1.carrier ∩ T2.carrier) := by
    have := ENNReal.toReal_mono h_inter_fin.ne h_vol_T2
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h_factor_pos.le] at this
    exact this
  have h_vol_T1_real : (1 - σ) ^ n * volume.real T1.carrier
      ≤ volume.real (T1.carrier ∩ T2.carrier) := by
    have := ENNReal.toReal_mono h_inter_fin.ne h_vol_T1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h_factor_pos.le] at this
    exact this
  have h_max : (1 - σ) ^ n * max (volume.real T1.carrier) (volume.real T2.carrier)
      ≤ volume.real (T1.carrier ∩ T2.carrier) := by
    rcases le_total (volume.real T1.carrier) (volume.real T2.carrier) with hle | hle
    · rw [max_eq_right hle]; exact h_vol_T2_real
    · rw [max_eq_left hle]; exact h_vol_T1_real
  have h_ed_real : volume.real (T1.carrier ∩ T2.carrier)
      ≤ (1/2 : ℝ) * max (volume.real T1.carrier) (volume.real T2.carrier) := by
    have hmax_ne : max (volume T1.carrier) (volume T2.carrier) ≠ ⊤ := by
      rw [ne_eq, max_eq_top, not_or]; exact ⟨hT1_fin.ne, hT2_fin.ne⟩
    have hRHS_ne : (1 / 2 : ℝ≥0∞) * max (volume T1.carrier) (volume T2.carrier) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤) hmax_ne
    have h := ENNReal.toReal_mono hRHS_ne h_ed
    rw [ENNReal.toReal_mul, show ((1 / 2 : ℝ≥0∞).toReal : ℝ) = 1 / 2 by simp] at h
    have hmax_to : (max (volume T1.carrier) (volume T2.carrier)).toReal =
        max (volume T1.carrier).toReal (volume T2.carrier).toReal := by
      rcases le_total (volume T1.carrier) (volume T2.carrier) with hle | hle
      · rw [max_eq_right hle, max_eq_right (ENNReal.toReal_mono hT2_fin.ne hle)]
      · rw [max_eq_left hle, max_eq_left (ENNReal.toReal_mono hT1_fin.ne hle)]
    rw [hmax_to] at h
    exact h
  have h_max_pos : 0 < max (volume.real T1.carrier) (volume.real T2.carrier) :=
    lt_max_of_lt_left hT1_pos
  have h_chain : (1 - σ) ^ n * max (volume.real T1.carrier) (volume.real T2.carrier)
      ≤ (1/2 : ℝ) * max (volume.real T1.carrier) (volume.real T2.carrier) :=
    le_trans h_max h_ed_real
  have h_factor_le : (1 - σ) ^ n ≤ 1 / 2 :=
    le_of_mul_le_mul_right (by linarith [h_chain]) h_max_pos
  linarith

/-- The explicit (dimension-dependent) constant in `Tube.card_le_of_EssDistinct`. -/
@[nolint defsWithUnderscore]
noncomputable abbrev card_le_of_EssDistinct.C (n : ℕ) : ℝ :=
  ((8 * n ^ 2 + 6) ^ (2 * n)) + 1

theorem card_le_of_EssDistinct.C_pos {n} : 0 < C n := by positivity

/-- If `T : ι → Tube δ E` is a family of `δ`-tubes whose carriers are pairwise
essentially distinct and all contained in the ball of radius `r` about the
origin, then the number of tubes is at most
`card_le_of_EssDistinct.C n · (r / δ) ^ (2 n)`, where `n = dim E` and
`card_le_of_EssDistinct.C n = (8 n² + 6) ^ (2 n) + 1`.

The constant `C n` is exposed deliberately, but the bound is far from being
sharp: the geometrically expected count grows like `(r / δ) ^ n`, whereas this
estimate gives the much larger exponent `2 n` and a polynomial-in-`n` base.
Both come from a crude lattice-point counting of tube endpoints and make no
attempt at the optimal constant. -/
theorem card_le_of_EssDistinct
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    {ι : Type*} {δ : NNReal} (hδ : 0 < δ)
    (r : ℝ) (s : Finset ι) (T : ι → Tube δ E)
    (hT_ball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) r)
    (hT_ed : (s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)) :
    (s.card : ℝ) ≤ card_le_of_EssDistinct.C (Module.finrank ℝ E)
      * (r / (δ : ℝ)) ^ (2 * Module.finrank ℝ E) := by
  classical
  have hn : 0 < Module.finrank ℝ E := Module.finrank_pos
  set n := Module.finrank ℝ E
  change (s.card : ℝ) ≤ ((8 * (n : ℝ) ^ 2 + 6) ^ (2 * n) + 1) * (r / (δ : ℝ)) ^ (2 * n)
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  haveI : NeZero n := ⟨by omega⟩
  set e := stdOrthonormalBasis ℝ E
  set σ₀ : ℝ := 1 / (4 * n) with hσ₀_def
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hσ₀_le_one : σ₀ ≤ 1 := by
    rw [hσ₀_def]; exact div_le_one_of_le₀ (by linarith) (by positivity)
  have hnσ₀ : (n : ℝ) * σ₀ = 1 / 4 := by rw [hσ₀_def]; field_simp
  have hδr : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  set ε := σ₀ * (δ : ℝ) / n with hε_def
  have hεpos : 0 < ε := by
    rw [hε_def]; exact div_pos (mul_pos (by positivity) hδr) (by positivity)
  have hep : ∀ i, (T i).x ∈ (T i).carrier ∧ (T i).y ∈ (T i).carrier := fun i =>
    ⟨(T i).carrier_eq ▸ Set.mem_iUnion₂.mpr
      ⟨_, left_mem_segment ℝ _ _, Metric.mem_closedBall_self hδr.le⟩,
     (T i).carrier_eq ▸ Set.mem_iUnion₂.mpr
      ⟨_, right_mem_segment ℝ _ _, Metric.mem_closedBall_self hδr.le⟩⟩
  have h2n_even : Even (2 * n) := ⟨n, by ring⟩
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp only [Finset.card_empty, CharP.cast_eq_zero, ge_iff_le]
    exact mul_nonneg (by positivity) (h2n_even.pow_nonneg _)
  · have hrd : 1 / 2 ≤ r / (δ : ℝ) := by
      rw [le_div_iff₀ hδr]
      have h1 : ‖(T i₀).x‖ ≤ r := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hT_ball i₀ hi₀ (hep i₀).1
      have h2 : ‖(T i₀).x + (δ : ℝ) • (T i₀).direction‖ ≤ r := by
        have hmem : (T i₀).x + (δ : ℝ) • (T i₀).direction ∈ (T i₀).carrier :=
          (T i₀).carrier_eq ▸ Set.mem_iUnion₂.mpr ⟨_, left_mem_segment ℝ _ _, by
            simp [Metric.mem_closedBall, dist_eq_norm, norm_smul,
                  Real.norm_of_nonneg hδr.le, norm_direction]⟩
        have := hT_ball i₀ hi₀ hmem
        simp only [Metric.mem_closedBall, dist_zero_right] at this; exact this
      linarith [norm_sub_le ((T i₀).x + (δ : ℝ) • (T i₀).direction) (T i₀).x,
        show ‖(T i₀).x + (δ : ℝ) • (T i₀).direction - (T i₀).x‖ = (δ : ℝ) from by
          simp [norm_smul, Real.norm_of_nonneg hδr.le, norm_direction]]
    have h_onb : ∀ v : E, ‖v‖ ≤ ∑ k : Fin n, |inner ℝ (e k) v| := fun v => by
      conv_lhs => rw [← e.sum_repr v]
      exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => by
        simp [norm_smul, Real.norm_eq_abs, e.norm_eq_one, e.repr_apply_apply]))
    have hfl : ∀ a b : ℝ, ⌊a / ε⌋ = ⌊b / ε⌋ → |a - b| < ε := fun a b h => by
      have : |a / ε - b / ε| < 1 := by
        rw [abs_sub_lt_iff]; constructor <;>
        linarith [Int.floor_le (a / ε), Int.lt_floor_add_one (a / ε),
                     Int.floor_le (b / ε), Int.lt_floor_add_one (b / ε),
                     show (⌊a / ε⌋ : ℝ) = (⌊b / ε⌋ : ℝ) from by exact_mod_cast h]
      rwa [show a / ε - b / ε = (a - b) / ε from by ring,
           abs_div, abs_of_pos hεpos, div_lt_one hεpos] at this
    let Ψ : ι → (Fin n → ℤ) × (Fin n → ℤ) := fun i =>
      (fun k => ⌊inner ℝ (e k) (T i).x / ε⌋, fun k => ⌊inner ℝ (e k) (T i).y / ε⌋)
    have hΨ_inj : Set.InjOn Ψ s := by
      intro i hi j hj heq; by_contra hne
      have norm_lt : ∀ f g : E, (∀ k, ⌊inner ℝ (e k) f / ε⌋ = ⌊inner ℝ (e k) g / ε⌋) →
          ‖f - g‖ < σ₀ * (δ : ℝ) := fun f g hk => calc
        ‖f - g‖ ≤ ∑ k, |inner ℝ (e k) (f - g)| := h_onb _
        _ < ∑ _k : Fin n, ε := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
            fun k _ => by rw [inner_sub_right]; exact hfl _ _ (hk k)
        _ = σ₀ * (δ : ℝ) := by rw [Finset.sum_const, Finset.card_univ,
                                   Fintype.card_fin, nsmul_eq_mul, hε_def]
                               field_simp
      exact absurd (endpoint_separated_of_ed hδ (by positivity) hσ₀_le_one
        (by have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -σ₀ from by linarith) n
            rw [show (1 : ℝ) + -σ₀ = 1 - σ₀ from by ring,
                show (1 : ℝ) + n * -σ₀ = 1 - ↑n * σ₀ from by ring] at this
            linarith)
            _ _ (hT_ed hi hj hne)) (not_or.mpr
                  ⟨not_lt.mpr (norm_lt _ _ fun k => congr_fun (Prod.ext_iff.mp heq).1 k).le,
                   not_lt.mpr (norm_lt _ _ fun k => congr_fun (Prod.ext_iff.mp heq).2 k).le⟩)
    set K := ⌈r / ε⌉₊
    set B := Finset.Icc (-(K : ℤ)) (K : ℤ)
    have hK_ge : r / ε ≤ (K : ℝ) := Nat.le_ceil _
    have h_in_B : ∀ a : ℝ, |a| ≤ r → ⌊a / ε⌋ ∈ B := fun a ha => by
      have hd : |a / ε| ≤ (K : ℝ) := by
        rw [abs_div, abs_of_pos hεpos]
        exact (div_le_div_of_nonneg_right ha hεpos.le).trans hK_ge
      obtain ⟨h1, h2⟩ := abs_le.mp hd
      exact Finset.mem_Icc.mpr
        ⟨Int.le_floor.mpr (by push_cast; exact h1),
         by exact_mod_cast (Int.floor_le (a / ε)).trans h2⟩
    set CodB := Fintype.piFinset (fun _ : Fin n => B)
    set Cod := CodB ×ˢ CodB
    have h_coord : ∀ i ∈ s, ∀ v ∈ (T i).carrier, ∀ k, ⌊inner ℝ (e k) v / ε⌋ ∈ B :=
      fun i hi v hv _ => h_in_B _ ((abs_real_inner_le_norm _ _).trans (by
        rw [e.norm_eq_one, one_mul]
        simpa [Metric.mem_closedBall, dist_zero_right] using hT_ball i hi hv))
    have h_maps_to : Set.MapsTo Ψ ↑s ↑Cod := fun i hi =>
      Finset.mem_product.mpr
        ⟨Fintype.mem_piFinset.mpr (h_coord i hi _ (hep i).1),
         Fintype.mem_piFinset.mpr (h_coord i hi _ (hep i).2)⟩
    have h2K1 : ((2 * K + 1 : ℕ) : ℝ) ≤ (8 * (n : ℝ) ^ 2 + 6) * (r / (δ : ℝ)) := by
      have hKr : (K : ℝ) ≤ 4 * (n : ℝ) ^ 2 * (r / (δ : ℝ)) + 1 := by
        calc (K : ℝ) ≤ r / ε + 1 := (Nat.ceil_lt_add_one
                (div_nonneg (by linarith [(le_div_iff₀ hδr).mp hrd]) hεpos.le)).le
          _ = 4 * (n : ℝ) ^ 2 * (r / (δ : ℝ)) + 1 := by rw [hε_def, hσ₀_def]; field_simp
      push_cast; linarith [hrd, hKr]
    calc (s.card : ℝ)
        ≤ ((2 * K + 1 : ℕ) : ℝ) ^ (2 * n) := by
          exact_mod_cast Finset.card_le_card_of_injOn Ψ h_maps_to hΨ_inj |>.trans (by
            simp only [Cod, CodB, Finset.card_product, Fintype.card_piFinset,
              show B.card = 2 * K + 1 from by simp [B, Int.card_Icc]; omega,
              Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            rw [show 2 * n = n + n from by ring, pow_add])
      _ ≤ ((8 * (n : ℝ) ^ 2 + 6) * (r / (δ : ℝ))) ^ (2 * n) :=
          pow_le_pow_left₀ (by positivity) h2K1 _
      _ = (8 * (n : ℝ) ^ 2 + 6) ^ (2 * n) * (r / (δ : ℝ)) ^ (2 * n) := mul_pow _ _ _
      _ ≤ ((8 * (n : ℝ) ^ 2 + 6) ^ (2 * n) + 1) * (r / (δ : ℝ)) ^ (2 * n) :=
          mul_le_mul_of_nonneg_right (by linarith) (h2n_even.pow_nonneg _)

end Tube
end
