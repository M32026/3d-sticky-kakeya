/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Kakeya.Tube.Basic

/-!
# Anchor-scale density from a discrete chain of scales

A multiscale construction produces density lower bounds only at the discrete
scales `ρ 0 > ρ 1 > … > ρ M` of a chain. Downstream arguments, however, need the
bound at an arbitrary *anchor* radius `ρ_anchor ∈ [δ, 1]`.

This file bridges that gap: `anchor_densityIn_ge_of_discrete` upgrades the
per-scale discrete lower bounds to every anchor radius, at the cost of a
constant factor controlled by

* `max_ratio`, an upper bound for the consecutive-scale ratios
  `(ρ k.castSucc / ρ k.succ) ^ (n - 1)`, and
* the inflation factor `C` by which the discrete bounds are stated at
  `C · ρ k.succ` rather than at `ρ k.succ` itself.

The statement is purely deterministic; it involves no random translations.
-/

@[expose] public section

open MeasureTheory Metric

namespace Kakeya

set_option maxHeartbeats 800000 in
-- The two range branches each carry a long ENNReal↔ℝ bridging chain over the
-- volume band, and the chain-scale localization adds a `Finset.min'` argument on
-- `Fin (M + 1)`; together they push elaboration past the default budget.
/-- **Anchor density from the per-scale discrete bound.**  The discrete lower bound is taken at the
*inflated* chain scale `C · ρ k.succ` instead of `ρ k.succ`, and the conclusion's density constant
absorbs a `C^(n-1)` factor in its denominator: `(le_c/vol_C)^2 / (max_ratio · C^(n-1))`.  The
inflation factor `C` is independent of the chain scale. -/
theorem StickyKakeya.anchor_densityIn_ge_of_discrete
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    {ι : Type*}
    (M : ℕ) (hM : 1 ≤ M) (δ : NNReal) (hδ_pos : 0 < δ)
    (ρ : Fin (M + 1) → NNReal)
    (h_anti : StrictAnti ρ)
    (h_ρ_top : ρ 0 = 1)
    (h_ρ_bot : ρ (Fin.last M) = δ)
    (T' : ι × E → Tube δ E)
    (s : Finset (ι × E))
    (C : NNReal) (hC : 1 ≤ C)
    (max_ratio : ℝ) (h_max_ratio_pos : 0 < max_ratio)
    (h_max_ratio_bound :
      ∀ k : Fin M,
        ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
            ((Module.finrank ℝ E : ℝ) - 1) ≤ max_ratio)
    (inSlack : ℝ) (h_inSlack_pos : 0 < inSlack) (h_inSlack_le_one : inSlack ≤ 1)
    (h_disc :
      ∀ k : Fin M, ∀ p₀ ∈ s,
        ENNReal.ofReal
            (((Tube.le_volume.c (Module.finrank ℝ E) : ℝ) /
              (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)) * inSlack /
              (C : ℝ) ^ (Module.finrank ℝ E - 1))
          ≤ Kakeya.densityIn
              (s.filter (fun p : ι × E =>
                (T' p).toConvexSpaceBody ≤
                  (Tube.rescale (T' p₀) (C * ρ k.succ)).toConvexSpaceBody))
              (fun p : ι × E => (T' p).toConvexSpaceBody)
              (Tube.rescale (T' p₀) (C * ρ k.succ)).toConvexSpaceBody) :
    ∀ ρ_anchor : NNReal, δ ≤ ρ_anchor → ρ_anchor ≤ 1 →
      ∀ p₀ ∈ s,
        ENNReal.ofReal
          (((Tube.le_volume.c (Module.finrank ℝ E) : ℝ) /
              (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)) ^ 2 * inSlack /
            (max_ratio * (C : ℝ) ^ (2 * (Module.finrank ℝ E - 1))))
          ≤ Kakeya.densityIn
              (s.filter (fun p : ι × E =>
                (T' p).toConvexSpaceBody ≤
                  (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody))
              (fun p : ι × E => (T' p).toConvexSpaceBody)
              (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn_pos : 0 < n := Module.finrank_pos
  have hC_pos : 0 < C := lt_of_lt_of_le one_pos hC
  have hC_r_pos : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC_pos
  have hC_r_ge_one : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hδ_le_one_NN : δ ≤ (1 : NNReal) := by
    have h := h_anti.antitone (Fin.zero_le (Fin.last M))
    rw [h_ρ_top, h_ρ_bot] at h
    exact h
  have h_ρ_pos : ∀ i, 0 < ρ i := by
    intro i
    have h := h_anti.antitone (Fin.le_last i)
    rw [h_ρ_bot] at h
    exact lt_of_lt_of_le hδ_pos h
  have h_C_const_pos : (0 : ℝ) < (Tube.volume_le.C n : ℝ) := by
    refine NNReal.coe_pos.mpr ?_
    unfold Tube.volume_le.C
    positivity
  have h_c_const_pos : (0 : ℝ) < (Tube.le_volume.c n : ℝ) := by
    exact_mod_cast Tube.le_volume.c_pos n
  set K_inv_const : ℝ := (Tube.le_volume.c n : ℝ) / (Tube.volume_le.C n : ℝ)
    with hK_inv_def
  have h_K_inv_pos : 0 < K_inv_const :=
    div_pos h_c_const_pos h_C_const_pos
  set K_const : ℝ := (Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ) with hK_def
  have h_K_pos : 0 < K_const := div_pos h_C_const_pos h_c_const_pos
  have h_K_K_inv : K_const * K_inv_const = 1 := by
    rw [hK_def, hK_inv_def]; field_simp
  have h_C_pow_pos : (0 : ℝ) < (C : ℝ) ^ (n - 1) := pow_pos hC_r_pos _
  have h_C_pow_ge_one : (1 : ℝ) ≤ (C : ℝ) ^ (n - 1) :=
    one_le_pow₀ hC_r_ge_one
  have h_C_pow2_pos : (0 : ℝ) < (C : ℝ) ^ (2 * (n - 1)) := pow_pos hC_r_pos _
  have h_C_pow2_ge_one : (1 : ℝ) ≤ (C : ℝ) ^ (2 * (n - 1)) :=
    one_le_pow₀ hC_r_ge_one
  have h_C_pow_le_pow2 : (C : ℝ) ^ (n - 1) ≤ (C : ℝ) ^ (2 * (n - 1)) := by
    apply pow_le_pow_right₀ hC_r_ge_one
    omega
  set target_real : ℝ := K_inv_const ^ 2 * inSlack / (max_ratio * (C : ℝ) ^ (2 * (n - 1)))
    with htarget_def
  have h_target_pos : 0 < target_real := by
    rw [htarget_def]
    exact div_pos (mul_pos (pow_pos h_K_inv_pos 2) h_inSlack_pos)
      (mul_pos h_max_ratio_pos h_C_pow2_pos)
  intro ρ_anchor hδ_le_anchor hanchor_le_one p₀ hp₀
  have h_anchor_pos_NN : 0 < ρ_anchor := lt_of_lt_of_le hδ_pos hδ_le_anchor
  have h_anchor_pos : (0 : ℝ) < (ρ_anchor : ℝ) := by exact_mod_cast h_anchor_pos_NN
  have hδr_pos : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  have h_δ_le_anchor_r : (δ : ℝ) ≤ (ρ_anchor : ℝ) := by exact_mod_cast hδ_le_anchor
  have h_anchor_le_one_r : (ρ_anchor : ℝ) ≤ 1 := by exact_mod_cast hanchor_le_one
  have h_max_ratio_ge_one : (1 : ℝ) ≤ max_ratio := by
    have h_k_lt : 0 < M := hM
    set k₀ : Fin M := ⟨0, h_k_lt⟩
    have hsucc_pos : (0 : ℝ) < (ρ k₀.succ : ℝ) := by exact_mod_cast h_ρ_pos _
    have h_cs_ge_succ : (ρ k₀.succ : ℝ) ≤ (ρ k₀.castSucc : ℝ) := by
      have : k₀.castSucc < k₀.succ := by simp [Fin.castSucc_lt_succ_iff]
      exact_mod_cast (h_anti this).le
    have h_ratio_ge_one : (1 : ℝ) ≤ (ρ k₀.castSucc : ℝ) / (ρ k₀.succ : ℝ) :=
      (one_le_div hsucc_pos).mpr h_cs_ge_succ
    have h_pow_ge_one :
        (1 : ℝ) ≤ ((ρ k₀.castSucc : ℝ) / (ρ k₀.succ : ℝ)) ^ ((n : ℝ) - 1) := by
      have hn_r : (0 : ℝ) ≤ (n : ℝ) - 1 := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
        linarith
      exact Real.one_le_rpow h_ratio_ge_one hn_r
    exact h_pow_ge_one.trans (h_max_ratio_bound k₀)
  have hδ_pow_r_pos : (0 : ℝ) < (δ : ℝ) ^ (n - 1) := pow_pos hδr_pos _
  have h_le_c_le_vol_C : (Tube.le_volume.c n : ℝ) ≤ (Tube.volume_le.C n : ℝ) := by
    have h_lo := Tube.le_volume (T' p₀)
    have h_hi := Tube.volume_le hδ_le_one_NN (T' p₀)
    have h_chain_ENN :
        (Tube.le_volume.c n : ENNReal) * (δ : ENNReal) ^ (n - 1) ≤
          (Tube.volume_le.C n : ENNReal) * (δ : ENNReal) ^ (n - 1) := by
      change (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
          ((δ : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1) ≤ _
      exact h_lo.trans h_hi
    have h_finite : (Tube.le_volume.c n : ENNReal) * (δ : ENNReal) ^ (n - 1) ≠ ⊤ := by
      apply ENNReal.mul_ne_top ENNReal.coe_ne_top
      exact ENNReal.pow_ne_top ENNReal.coe_ne_top
    have h_finite' : (Tube.volume_le.C n : ENNReal) * (δ : ENNReal) ^ (n - 1) ≠ ⊤ := by
      apply ENNReal.mul_ne_top ENNReal.coe_ne_top
      exact ENNReal.pow_ne_top ENNReal.coe_ne_top
    have h_chain_r : (Tube.le_volume.c n : ℝ) * (δ : ℝ) ^ (n - 1) ≤
        (Tube.volume_le.C n : ℝ) * (δ : ℝ) ^ (n - 1) := by
      have h_lhs_toReal : ((Tube.le_volume.c n : ENNReal) *
          (δ : ENNReal) ^ (n - 1)).toReal =
            (Tube.le_volume.c n : ℝ) * (δ : ℝ) ^ (n - 1) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
            ENNReal.coe_toReal]
      have h_rhs_toReal : ((Tube.volume_le.C n : ENNReal) *
          (δ : ENNReal) ^ (n - 1)).toReal =
            (Tube.volume_le.C n : ℝ) * (δ : ℝ) ^ (n - 1) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
            ENNReal.coe_toReal]
      rw [← h_lhs_toReal, ← h_rhs_toReal]
      exact ENNReal.toReal_mono h_finite' h_chain_ENN
    exact le_of_mul_le_mul_right (by linarith [h_chain_r]) hδ_pow_r_pos
  have h_K_inv_le_one : K_inv_const ≤ 1 := by
    rw [hK_inv_def]
    exact (div_le_one h_C_const_pos).mpr h_le_c_le_vol_C
  have h_K_inv_le_max_ratio : K_inv_const ≤ max_ratio :=
    h_K_inv_le_one.trans h_max_ratio_ge_one
  by_cases h_main : (C : ℝ) * (δ : ℝ) ≤ (ρ_anchor : ℝ)
  · set ρa_r : ℝ := (ρ_anchor : ℝ) / (C : ℝ) with hρa_def
    have hρa_pos : 0 < ρa_r := div_pos h_anchor_pos hC_r_pos
    have hρa_ge_δ : (δ : ℝ) ≤ ρa_r := by
      rw [hρa_def, le_div_iff₀ hC_r_pos, mul_comm]
      exact h_main
    have hρa_le_one : ρa_r ≤ 1 := by
      rw [hρa_def, div_le_one hC_r_pos]
      exact h_anchor_le_one_r.trans hC_r_ge_one
    have h_loc :
        ∃ k : Fin M, (ρ k.succ : ℝ) ≤ ρa_r ∧ ρa_r ≤ (ρ k.castSucc : ℝ) := by
      let S : Finset (Fin (M + 1)) :=
        (Finset.univ).filter (fun i => (ρ i : ℝ) ≤ ρa_r)
      have hS_ne : S.Nonempty := by
        refine ⟨Fin.last M, ?_⟩
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [h_ρ_bot]; exact hρa_ge_δ
      let i_min : Fin (M + 1) := S.min' hS_ne
      have h_min_mem : i_min ∈ S := S.min'_mem hS_ne
      have h_min_le : (ρ i_min : ℝ) ≤ ρa_r := by
        have := h_min_mem
        simp only [S, Finset.mem_filter] at this
        exact this.2
      have h_min_minimal : ∀ j ∈ S, i_min ≤ j := fun j hj => S.min'_le _ hj
      by_cases h_i_min_zero : i_min = 0
      · have h_anchor_eq_one : ρa_r = 1 := by
          rw [h_i_min_zero] at h_min_le
          rw [h_ρ_top] at h_min_le
          have h1 : ((1 : NNReal) : ℝ) = 1 := NNReal.coe_one
          rw [h1] at h_min_le
          linarith [hρa_le_one]
        refine ⟨⟨0, hM⟩, ?_, ?_⟩
        · have h_succ_lt : ρ (⟨0, hM⟩ : Fin M).succ < ρ (⟨0, hM⟩ : Fin M).castSucc := h_anti (by
            rw [Fin.castSucc_lt_succ_iff])
          have h_cs_eq : (⟨0, hM⟩ : Fin M).castSucc = (0 : Fin (M + 1)) := by
            ext; simp
          rw [h_cs_eq, h_ρ_top] at h_succ_lt
          rw [h_anchor_eq_one]
          have : ((ρ (⟨0, hM⟩ : Fin M).succ : NNReal) : ℝ) < 1 := by
            have h1 : ((1 : NNReal) : ℝ) = 1 := NNReal.coe_one
            rw [← h1]; exact_mod_cast h_succ_lt
          linarith
        · have h_cs_eq : (⟨0, hM⟩ : Fin M).castSucc = (0 : Fin (M + 1)) := by
            ext; simp
          rw [h_cs_eq, h_ρ_top, h_anchor_eq_one]
          exact le_refl _
      · have h_i_min_pos : 0 < i_min.val :=
          Nat.pos_of_ne_zero (fun h => h_i_min_zero (Fin.eq_of_val_eq h))
        have h_k_lt : i_min.val - 1 < M := by omega
        refine ⟨⟨i_min.val - 1, h_k_lt⟩, ?_, ?_⟩
        · have h_succ_eq : (⟨i_min.val - 1, h_k_lt⟩ : Fin M).succ = i_min := by
            apply Fin.ext
            change i_min.val - 1 + 1 = i_min.val
            omega
          rw [h_succ_eq]; exact h_min_le
        · have h_cs_eq : (⟨i_min.val - 1, h_k_lt⟩ : Fin M).castSucc =
              (⟨i_min.val - 1, by omega⟩ : Fin (M + 1)) := by
            apply Fin.ext
            change i_min.val - 1 = i_min.val - 1
            rfl
          rw [h_cs_eq]
          have h_lt_imin : (⟨i_min.val - 1, by omega⟩ : Fin (M + 1)) < i_min := by
            rw [Fin.lt_def]
            change i_min.val - 1 < i_min.val
            omega
          have h_not_in_S : (⟨i_min.val - 1, by omega⟩ : Fin (M + 1)) ∉ S := by
            intro h
            exact absurd (h_min_minimal _ h) (not_le.mpr h_lt_imin)
          have h_gt : ρa_r < (ρ (⟨i_min.val - 1, by omega⟩ : Fin (M + 1)) : ℝ) := by
            by_contra h
            push Not at h
            apply h_not_in_S
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            exact h
          exact h_gt.le
    obtain ⟨k, h_succ_le_ρa, h_ρa_le_cs⟩ := h_loc
    have h_succ_C_le_anchor : (C : ℝ) * (ρ k.succ : ℝ) ≤ (ρ_anchor : ℝ) := by
      rw [hρa_def, le_div_iff₀ hC_r_pos, mul_comm] at h_succ_le_ρa
      linarith
    have h_anchor_le_C_cs : (ρ_anchor : ℝ) ≤ (C : ℝ) * (ρ k.castSucc : ℝ) := by
      rw [hρa_def, div_le_iff₀ hC_r_pos] at h_ρa_le_cs
      linarith
    set ρ_s : NNReal := ρ k.succ
    set ρ_cs : NNReal := ρ k.castSucc
    have h_ρ_s_pos : 0 < ρ_s := h_ρ_pos _
    have h_ρ_cs_pos : 0 < ρ_cs := h_ρ_pos _
    have h_ρ_s_r_pos : (0 : ℝ) < (ρ_s : ℝ) := by exact_mod_cast h_ρ_s_pos
    have h_ρ_cs_r_pos : (0 : ℝ) < (ρ_cs : ℝ) := by exact_mod_cast h_ρ_cs_pos
    have h_ρ_s_le_cs : ρ_s ≤ ρ_cs := by
      have : k.castSucc < k.succ := by simp [Fin.castSucc_lt_succ_iff]
      exact (h_anti this).le
    have h_C_ρ_s_le_anchor_NN : C * ρ_s ≤ ρ_anchor := by
      have : ((C * ρ_s : NNReal) : ℝ) ≤ ((ρ_anchor : NNReal) : ℝ) := by
        push_cast
        exact h_succ_C_le_anchor
      exact_mod_cast this
    have h_δ_le_ρ_s : δ ≤ ρ_s := by
      have := h_anti.antitone (Fin.le_last k.succ)
      rw [h_ρ_bot] at this
      exact this
    have h_δ_le_C_ρ_s : δ ≤ C * ρ_s := h_δ_le_ρ_s.trans (by
      have : (1 : NNReal) * ρ_s ≤ C * ρ_s := mul_le_mul_left hC ρ_s
      simpa using this)
    have h_C_ρ_s_le_one : C * ρ_s ≤ 1 := by
      have : (C : ℝ) * (ρ_s : ℝ) ≤ (ρ_anchor : ℝ) := h_succ_C_le_anchor
      have h1 : (C * ρ_s : NNReal) ≤ ρ_anchor := by
        have : ((C * ρ_s : NNReal) : ℝ) ≤ ((ρ_anchor : NNReal) : ℝ) := by
          push_cast; linarith
        exact_mod_cast this
      exact h1.trans hanchor_le_one
    have h_disc_inst := h_disc k p₀ hp₀
    have h_rescale_mono :
        (Tube.rescale (T' p₀) (C * ρ_s)).toConvexSpaceBody ≤
          (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody :=
      Tube.rescale_le_rescale_of_radius_le (T' p₀) h_C_ρ_s_le_anchor_NN
    have h_filter_subset :
        (s.filter (fun p : ι × E =>
          (T' p).toConvexSpaceBody ≤
            (Tube.rescale (T' p₀) (C * ρ_s)).toConvexSpaceBody)) ⊆
        (s.filter (fun p : ι × E =>
          (T' p).toConvexSpaceBody ≤
            (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody)) := by
      intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, hp.2.trans h_rescale_mono⟩
    set numer_anchor : ENNReal :=
      ∑ p ∈ s.filter (fun p : ι × E =>
        (T' p).toConvexSpaceBody ≤ (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody),
        volume (T' p).carrier with hnumer_anchor_def
    set numer_s : ENNReal :=
      ∑ p ∈ s.filter (fun p : ι × E =>
        (T' p).toConvexSpaceBody ≤
          (Tube.rescale (T' p₀) (C * ρ_s)).toConvexSpaceBody),
        volume (T' p).carrier with hnumer_s_def
    have h_numer_le : numer_s ≤ numer_anchor :=
      Finset.sum_le_sum_of_subset h_filter_subset
    set denom_anchor : ENNReal :=
      volume (Tube.rescale (T' p₀) ρ_anchor).carrier with hdenom_anchor_def
    set denom_s : ENNReal :=
      volume (Tube.rescale (T' p₀) (C * ρ_s)).carrier with hdenom_s_def
    have h_denom_anchor_ne_top : denom_anchor ≠ ⊤ :=
      (Tube.rescale (T' p₀) ρ_anchor).isCompact.measure_lt_top.ne
    have h_denom_s_ne_top : denom_s ≠ ⊤ :=
      (Tube.rescale (T' p₀) (C * ρ_s)).isCompact.measure_lt_top.ne
    have h_denom_anchor_le :
        denom_anchor ≤
          ((Tube.volume_le.C n : ENNReal) *
            ((ρ_anchor : NNReal) : ENNReal) ^ (n - 1)) :=
      Tube.volume_le hanchor_le_one _
    have h_denom_s_ge :
        ((Tube.le_volume.c n : ENNReal) * ((C * ρ_s : NNReal) : ENNReal) ^ (n - 1)) ≤
          denom_s :=
      Tube.le_volume _
    set slack_real : ℝ :=
      K_const * ((ρ_anchor : ℝ) / ((C : ℝ) * (ρ_s : ℝ))) ^ (n - 1) with hslack_def
    have h_anchor_C_ρ_s_pos : (0 : ℝ) < (C : ℝ) * (ρ_s : ℝ) :=
      mul_pos hC_r_pos h_ρ_s_r_pos
    have h_ratio_inner_pos :
        (0 : ℝ) < (ρ_anchor : ℝ) / ((C : ℝ) * (ρ_s : ℝ)) :=
      div_pos h_anchor_pos h_anchor_C_ρ_s_pos
    have h_slack_pos : 0 < slack_real := by
      rw [hslack_def]
      exact mul_pos h_K_pos (pow_pos h_ratio_inner_pos _)
    have h_C_ρ_s_NN_eq : ((C * ρ_s : NNReal) : ℝ) = (C : ℝ) * (ρ_s : ℝ) := by
      push_cast; rfl
    have h_anchor_pow_eq :
        ((ρ_anchor : NNReal) : ENNReal) ^ (n - 1) =
          ENNReal.ofReal (((ρ_anchor : ℝ) / ((C : ℝ) * (ρ_s : ℝ))) ^ (n - 1)) *
            ((C * ρ_s : NNReal) : ENNReal) ^ (n - 1) := by
      rw [show ((ρ_anchor : NNReal) : ENNReal) =
            ENNReal.ofReal ((ρ_anchor : ℝ)) from (ENNReal.ofReal_coe_nnreal).symm]
      rw [show ((C * ρ_s : NNReal) : ENNReal) =
            ENNReal.ofReal (((C * ρ_s : NNReal) : ℝ)) from
              (ENNReal.ofReal_coe_nnreal).symm]
      rw [h_C_ρ_s_NN_eq]
      rw [← ENNReal.ofReal_pow h_anchor_pos.le,
          ← ENNReal.ofReal_pow h_anchor_C_ρ_s_pos.le,
          ← ENNReal.ofReal_mul (pow_nonneg h_ratio_inner_pos.le _),
          ← mul_pow]
      congr 2
      field_simp
    have h_C_eq_K_times_c : (Tube.volume_le.C n : ENNReal) =
        ENNReal.ofReal K_const * (Tube.le_volume.c n : ENNReal) := by
      rw [hK_def]
      rw [show ((Tube.volume_le.C n : NNReal) : ENNReal) =
            ENNReal.ofReal (Tube.volume_le.C n : ℝ) from
              (ENNReal.ofReal_coe_nnreal).symm,
          show ((Tube.le_volume.c n : NNReal) : ENNReal) =
            ENNReal.ofReal (Tube.le_volume.c n : ℝ) from
              (ENNReal.ofReal_coe_nnreal).symm]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    have h_slack_ENN_eq :
        ENNReal.ofReal slack_real =
          ENNReal.ofReal K_const *
            ENNReal.ofReal (((ρ_anchor : ℝ) / ((C : ℝ) * (ρ_s : ℝ))) ^ (n - 1)) := by
      rw [hslack_def]
      exact ENNReal.ofReal_mul h_K_pos.le
    have h_chain :
        denom_anchor ≤ ENNReal.ofReal slack_real * denom_s := by
      calc denom_anchor
          ≤ (Tube.volume_le.C n : ENNReal) * (ρ_anchor : ENNReal) ^ (n - 1) :=
            h_denom_anchor_le
        _ = (ENNReal.ofReal K_const * (Tube.le_volume.c n : ENNReal)) *
              (ENNReal.ofReal (((ρ_anchor : ℝ) / ((C : ℝ) * (ρ_s : ℝ))) ^ (n - 1))
                * ((C * ρ_s : NNReal) : ENNReal) ^ (n - 1)) := by
              rw [h_C_eq_K_times_c, h_anchor_pow_eq]
        _ = (ENNReal.ofReal K_const *
                ENNReal.ofReal (((ρ_anchor : ℝ) / ((C : ℝ) * (ρ_s : ℝ))) ^ (n - 1))) *
              ((Tube.le_volume.c n : ENNReal) *
                ((C * ρ_s : NNReal) : ENNReal) ^ (n - 1)) := by
              ring
        _ = ENNReal.ofReal slack_real *
              ((Tube.le_volume.c n : ENNReal) *
                ((C * ρ_s : NNReal) : ENNReal) ^ (n - 1)) := by
              rw [h_slack_ENN_eq]
        _ ≤ ENNReal.ofReal slack_real * denom_s := by
              gcongr
    have h_denom_s_pos : 0 < denom_s := by
      have h_pow_pos : (0 : ENNReal) < ((C * ρ_s : NNReal) : ENNReal) ^ (n - 1) := by
        apply ENNReal.pow_pos
        have h_NN_pos : (0 : NNReal) < C * ρ_s := mul_pos hC_pos h_ρ_s_pos
        exact_mod_cast h_NN_pos
      have h_mul_pos : (0 : ENNReal) <
          (Tube.le_volume.c n : ENNReal) * ((C * ρ_s : NNReal) : ENNReal) ^ (n - 1) :=
        ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos n).ne')
          h_pow_pos.ne'
      exact lt_of_lt_of_le h_mul_pos h_denom_s_ge
    have h_denom_s_ne_zero : denom_s ≠ 0 := ne_of_gt h_denom_s_pos
    have h_disc' : ENNReal.ofReal (K_inv_const * inSlack / (C : ℝ) ^ (n - 1)) ≤
        Kakeya.densityIn
          (s.filter (fun p : ι × E =>
            (T' p).toConvexSpaceBody ≤
              (Tube.rescale (T' p₀) (C * ρ_s)).toConvexSpaceBody))
          (fun p : ι × E => (T' p).toConvexSpaceBody)
          (Tube.rescale (T' p₀) (C * ρ_s)).toConvexSpaceBody := by
      convert h_disc_inst using 2
    have h_numer_s_ge :
        ENNReal.ofReal (K_inv_const * inSlack / (C : ℝ) ^ (n - 1)) * denom_s ≤ numer_s := by
      have h_div_le := h_disc'
      have h_eq : Kakeya.densityIn
          (s.filter (fun p : ι × E =>
            (T' p).toConvexSpaceBody ≤
              (Tube.rescale (T' p₀) (C * ρ_s)).toConvexSpaceBody))
          (fun p : ι × E => (T' p).toConvexSpaceBody)
          (Tube.rescale (T' p₀) (C * ρ_s)).toConvexSpaceBody
          = numer_s / denom_s := by
        change (∑ p ∈ s.filter _ with _, _) / denom_s = numer_s / denom_s
        simp only [hnumer_s_def]
        congr 1
        apply Finset.sum_congr
        · ext p
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨⟨hp, h1⟩, h2⟩; exact ⟨hp, h1⟩
          · rintro ⟨hp, h1⟩; exact ⟨⟨hp, h1⟩, h1⟩
        · intros; rfl
      rw [h_eq] at h_div_le
      rwa [ENNReal.le_div_iff_mul_le (Or.inl h_denom_s_ne_zero) (Or.inl h_denom_s_ne_top)]
        at h_div_le
    have h_ratio_inner_eq :
        (ρ_anchor : ℝ) / ((C : ℝ) * (ρ_s : ℝ)) =
          ((ρ_anchor : ℝ) / (ρ_s : ℝ)) / (C : ℝ) := by
      field_simp
    have h_anchor_div_ρ_s_le :
        (ρ_anchor : ℝ) / (ρ_s : ℝ) ≤ (C : ℝ) * ((ρ_cs : ℝ) / (ρ_s : ℝ)) := by
      rw [div_le_iff₀ h_ρ_s_r_pos]
      rw [show (C : ℝ) * ((ρ_cs : ℝ) / (ρ_s : ℝ)) * (ρ_s : ℝ) = (C : ℝ) * (ρ_cs : ℝ) from by
        field_simp]
      exact h_anchor_le_C_cs
    have h_anchor_div_ρ_s_pos : 0 < (ρ_anchor : ℝ) / (ρ_s : ℝ) :=
      div_pos h_anchor_pos h_ρ_s_r_pos
    have h_C_ratio_pos : 0 < (C : ℝ) * ((ρ_cs : ℝ) / (ρ_s : ℝ)) :=
      mul_pos hC_r_pos (div_pos h_ρ_cs_r_pos h_ρ_s_r_pos)
    have h_anchor_div_pow_le :
        ((ρ_anchor : ℝ) / (ρ_s : ℝ)) ^ (n - 1) ≤
          ((C : ℝ) * ((ρ_cs : ℝ) / (ρ_s : ℝ))) ^ (n - 1) :=
      pow_le_pow_left₀ h_anchor_div_ρ_s_pos.le h_anchor_div_ρ_s_le _
    have h_ratio_pow_le_max :
        ((ρ_cs : ℝ) / (ρ_s : ℝ)) ^ (n - 1) ≤ max_ratio := by
      have hr_pos : 0 < (ρ_cs : ℝ) / (ρ_s : ℝ) :=
        div_pos h_ρ_cs_r_pos h_ρ_s_r_pos
      have h_real_pow_eq :
          ((ρ_cs : ℝ) / (ρ_s : ℝ)) ^ ((n : ℝ) - 1)
            = ((ρ_cs : ℝ) / (ρ_s : ℝ)) ^ (n - 1) := by
        rw [show ((n : ℝ) - 1 : ℝ) = ((n - 1 : ℕ) : ℝ) by
          rw [Nat.cast_sub hn_pos]; push_cast; ring]
        exact Real.rpow_natCast _ (n - 1)
      have hk := h_max_ratio_bound k
      change ((ρ_cs : ℝ) / (ρ_s : ℝ)) ^ ((n : ℝ) - 1) ≤ max_ratio at hk
      rw [h_real_pow_eq] at hk
      exact hk
    have h_anchor_div_ρ_s_pow_le :
        ((ρ_anchor : ℝ) / (ρ_s : ℝ)) ^ (n - 1) ≤ (C : ℝ) ^ (n - 1) * max_ratio := by
      calc ((ρ_anchor : ℝ) / (ρ_s : ℝ)) ^ (n - 1)
          ≤ ((C : ℝ) * ((ρ_cs : ℝ) / (ρ_s : ℝ))) ^ (n - 1) := h_anchor_div_pow_le
        _ = (C : ℝ) ^ (n - 1) * ((ρ_cs : ℝ) / (ρ_s : ℝ)) ^ (n - 1) := by
            rw [mul_pow]
        _ ≤ (C : ℝ) ^ (n - 1) * max_ratio := by
            gcongr
    have h_pow_div_eq :
        ((ρ_anchor : ℝ) / ((C : ℝ) * (ρ_s : ℝ))) ^ (n - 1) =
          ((ρ_anchor : ℝ) / (ρ_s : ℝ)) ^ (n - 1) / (C : ℝ) ^ (n - 1) := by
      rw [h_ratio_inner_eq, div_pow]
    have h_inner_pow_le_max :
        ((ρ_anchor : ℝ) / ((C : ℝ) * (ρ_s : ℝ))) ^ (n - 1) ≤ max_ratio := by
      rw [h_pow_div_eq]
      rw [div_le_iff₀ h_C_pow_pos]
      calc ((ρ_anchor : ℝ) / (ρ_s : ℝ)) ^ (n - 1)
          ≤ (C : ℝ) ^ (n - 1) * max_ratio := h_anchor_div_ρ_s_pow_le
        _ = max_ratio * (C : ℝ) ^ (n - 1) := by ring
    have h_target_slack_le :
        target_real * slack_real ≤ K_inv_const * inSlack / (C : ℝ) ^ (n - 1) := by
      rw [htarget_def, hslack_def]
      have h_step :
          K_inv_const ^ 2 * inSlack / (max_ratio * (C : ℝ) ^ (2 * (n - 1))) *
              (K_const * ((ρ_anchor : ℝ) / ((C : ℝ) * (ρ_s : ℝ))) ^ (n - 1))
            = (K_inv_const * inSlack) * (K_const * K_inv_const) *
                (((ρ_anchor : ℝ) / ((C : ℝ) * (ρ_s : ℝ))) ^ (n - 1) /
                  (max_ratio * (C : ℝ) ^ (2 * (n - 1)))) := by
        ring
      rw [h_step, h_K_K_inv, mul_one]
      have h_div_le :
          ((ρ_anchor : ℝ) / ((C : ℝ) * (ρ_s : ℝ))) ^ (n - 1) /
              (max_ratio * (C : ℝ) ^ (2 * (n - 1))) ≤ 1 / (C : ℝ) ^ (n - 1) := by
        have h_pow_split : (C : ℝ) ^ (2 * (n - 1)) =
            (C : ℝ) ^ (n - 1) * (C : ℝ) ^ (n - 1) := by
          rw [← pow_add]; congr 1; omega
        rw [h_pow_split]
        rw [show max_ratio * ((C : ℝ) ^ (n - 1) * (C : ℝ) ^ (n - 1))
              = (max_ratio * (C : ℝ) ^ (n - 1)) * (C : ℝ) ^ (n - 1) from by ring]
        rw [div_mul_eq_div_div]
        apply div_le_div_of_nonneg_right _ h_C_pow_pos.le
        · rw [div_le_one (mul_pos h_max_ratio_pos h_C_pow_pos)]
          calc ((ρ_anchor : ℝ) / ((C : ℝ) * (ρ_s : ℝ))) ^ (n - 1)
              ≤ max_ratio := h_inner_pow_le_max
            _ = max_ratio * 1 := (mul_one _).symm
            _ ≤ max_ratio * (C : ℝ) ^ (n - 1) := by
                gcongr
      calc (K_inv_const * inSlack) *
            (((ρ_anchor : ℝ) / ((C : ℝ) * (ρ_s : ℝ))) ^ (n - 1) /
              (max_ratio * (C : ℝ) ^ (2 * (n - 1))))
          ≤ (K_inv_const * inSlack) * (1 / (C : ℝ) ^ (n - 1)) :=
            mul_le_mul_of_nonneg_left h_div_le
              (mul_nonneg h_K_inv_pos.le h_inSlack_pos.le)
        _ = K_inv_const * inSlack / (C : ℝ) ^ (n - 1) := by rw [mul_one_div]
    have h_target_denom_le_numer :
        ENNReal.ofReal target_real * denom_anchor ≤ numer_anchor := by
      calc ENNReal.ofReal target_real * denom_anchor
          ≤ ENNReal.ofReal target_real * (ENNReal.ofReal slack_real * denom_s) := by
            gcongr
        _ = ENNReal.ofReal target_real * ENNReal.ofReal slack_real * denom_s := by
            rw [mul_assoc]
        _ = ENNReal.ofReal (target_real * slack_real) * denom_s := by
            rw [← ENNReal.ofReal_mul h_target_pos.le]
        _ ≤ ENNReal.ofReal (K_inv_const * inSlack / (C : ℝ) ^ (n - 1)) * denom_s :=
            mul_le_mul_left (ENNReal.ofReal_le_ofReal h_target_slack_le) _
        _ ≤ numer_s := h_numer_s_ge
        _ ≤ numer_anchor := h_numer_le
    have h_denom_anchor_pos : 0 < denom_anchor := by
      have h_anchor_pow_pos : (0 : ENNReal) < (ρ_anchor : ENNReal) ^ (n - 1) := by
        apply ENNReal.pow_pos
        exact_mod_cast h_anchor_pos_NN
      have h_le : (Tube.le_volume.c n : ENNReal) * (ρ_anchor : ENNReal) ^ (n - 1) ≤
          denom_anchor :=
        Tube.le_volume (Tube.rescale (T' p₀) ρ_anchor)
      have h_lhs_pos : (0 : ENNReal) < (Tube.le_volume.c n : ENNReal) *
          (ρ_anchor : ENNReal) ^ (n - 1) :=
        ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos n).ne')
          h_anchor_pow_pos.ne'
      exact lt_of_lt_of_le h_lhs_pos h_le
    have h_eq_anchor : Kakeya.densityIn
          (s.filter (fun p : ι × E =>
            (T' p).toConvexSpaceBody ≤
              (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody))
          (fun p : ι × E => (T' p).toConvexSpaceBody)
          (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody
          = numer_anchor / denom_anchor := by
      change (∑ p ∈ s.filter _ with _, _) / denom_anchor = numer_anchor / denom_anchor
      simp only [hnumer_anchor_def]
      congr 1
      apply Finset.sum_congr
      · ext p
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hp, h1⟩, h2⟩; exact ⟨hp, h1⟩
        · rintro ⟨hp, h1⟩; exact ⟨⟨hp, h1⟩, h1⟩
      · intros; rfl
    rw [h_eq_anchor]
    rw [ENNReal.le_div_iff_mul_le (Or.inl h_denom_anchor_pos.ne')
      (Or.inl h_denom_anchor_ne_top)]
    exact h_target_denom_le_numer
  · push Not at h_main
    have h_self_le_rescale :
        (T' p₀).toConvexSpaceBody ≤ (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody := by
      rw [← (T' p₀).toConvexBody_cthickening_sub hδ_le_anchor]
      intro x hx
      exact Metric.self_subset_cthickening _ hx
    have h_p₀_in_filter :
        p₀ ∈ s.filter (fun p : ι × E =>
          (T' p).toConvexSpaceBody ≤
            (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody) :=
      Finset.mem_filter.mpr ⟨hp₀, h_self_le_rescale⟩
    set filter_set : Finset (ι × E) :=
      s.filter (fun p : ι × E =>
        (T' p).toConvexSpaceBody ≤
          (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody) with hfilter_def
    set numer_anchor : ENNReal :=
      ∑ p ∈ filter_set, volume (T' p).carrier with hnumer_anchor_def
    set denom_anchor : ENNReal :=
      volume (Tube.rescale (T' p₀) ρ_anchor).carrier with hdenom_anchor_def
    have h_denom_anchor_ne_top : denom_anchor ≠ ⊤ :=
      (Tube.rescale (T' p₀) ρ_anchor).isCompact.measure_lt_top.ne
    have h_singleton_subset : ({p₀} : Finset (ι × E)) ⊆ filter_set := by
      intro q hq
      rw [Finset.mem_singleton] at hq
      rw [hq]
      exact h_p₀_in_filter
    have h_p₀_volume_le_numer :
        volume (T' p₀).carrier ≤ numer_anchor := by
      have := Finset.sum_le_sum_of_subset (s := ({p₀} : Finset (ι × E)))
        (t := filter_set) (f := fun p => volume (T' p).carrier) h_singleton_subset
      simpa using this
    have h_p₀_ge : (Tube.le_volume.c n : ENNReal) * (δ : ENNReal) ^ (n - 1) ≤
        volume (T' p₀).carrier := by
      have := Tube.le_volume (T' p₀)
      change (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
          ((δ : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1) ≤ _ at this
      exact this
    have h_numer_ge : (Tube.le_volume.c n : ENNReal) * (δ : ENNReal) ^ (n - 1) ≤
        numer_anchor :=
      h_p₀_ge.trans h_p₀_volume_le_numer
    have h_denom_le : denom_anchor ≤ (Tube.volume_le.C n : ENNReal) *
        (ρ_anchor : ENNReal) ^ (n - 1) :=
      Tube.volume_le hanchor_le_one _
    set δr : ℝ := (δ : ℝ) with hδr_def
    set ρar : ℝ := (ρ_anchor : ℝ) with hρar_def
    have hδr_pos' : 0 < δr := hδr_pos
    have hρar_pos : 0 < ρar := h_anchor_pos
    set lb_real : ℝ := K_inv_const * (δr / ρar) ^ (n - 1) with hlb_def
    have h_δ_div_ρar_pos : 0 < δr / ρar := div_pos hδr_pos' hρar_pos
    have h_lb_pos : 0 < lb_real := by
      rw [hlb_def]; exact mul_pos h_K_inv_pos (pow_pos h_δ_div_ρar_pos _)
    have h_ρar_div_δr_pos : 0 < ρar / δr := div_pos hρar_pos hδr_pos'
    have h_ρar_div_δr_lt_C : ρar / δr ≤ (C : ℝ) := by
      rw [div_le_iff₀ hδr_pos']
      linarith [h_main.le]
    have h_ρar_div_δr_pow_le : (ρar / δr) ^ (n - 1) ≤ (C : ℝ) ^ (n - 1) :=
      pow_le_pow_left₀ h_ρar_div_δr_pos.le h_ρar_div_δr_lt_C _
    set old_target_real : ℝ :=
      K_inv_const ^ 2 / (max_ratio * (C : ℝ) ^ (2 * (n - 1))) with hold_target_def
    have h_old_target_pos : 0 < old_target_real :=
      div_pos (pow_pos h_K_inv_pos 2) (mul_pos h_max_ratio_pos h_C_pow2_pos)
    have h_target_le_old : target_real ≤ old_target_real := by
      rw [htarget_def, hold_target_def, mul_div_assoc]
      calc K_inv_const ^ 2 * (inSlack / (max_ratio * (C : ℝ) ^ (2 * (n - 1))))
          ≤ K_inv_const ^ 2 * (1 / (max_ratio * (C : ℝ) ^ (2 * (n - 1)))) := by
            gcongr
        _ = K_inv_const ^ 2 / (max_ratio * (C : ℝ) ^ (2 * (n - 1))) := by
            rw [mul_one_div]
    have h_target_le_lb : target_real ≤ lb_real := by
      refine h_target_le_old.trans ?_
      rw [hold_target_def, hlb_def]
      have h_δ_ρ_pow_eq : (δr / ρar) ^ (n - 1) = 1 / (ρar / δr) ^ (n - 1) := by
        rw [one_div, ← inv_pow]
        congr 1
        rw [inv_div]
      rw [h_δ_ρ_pow_eq, one_div]
      rw [show K_inv_const ^ 2 / (max_ratio * (C : ℝ) ^ (2 * (n - 1))) =
            K_inv_const * (K_inv_const / (max_ratio * (C : ℝ) ^ (2 * (n - 1))))
              from by ring]
      apply mul_le_mul_of_nonneg_left _ h_K_inv_pos.le
      rw [div_le_iff₀ (mul_pos h_max_ratio_pos h_C_pow2_pos)]
      have h_pow_ρ_div_pos : 0 < (ρar / δr) ^ (n - 1) :=
        pow_pos h_ρar_div_δr_pos _
      rw [show ((ρar / δr) ^ (n - 1))⁻¹ * (max_ratio * (C : ℝ) ^ (2 * (n - 1)))
            = (max_ratio * (C : ℝ) ^ (2 * (n - 1))) / (ρar / δr) ^ (n - 1) from by
              field_simp]
      rw [le_div_iff₀ h_pow_ρ_div_pos]
      calc K_inv_const * (ρar / δr) ^ (n - 1)
          ≤ K_inv_const * (C : ℝ) ^ (n - 1) := by
            gcongr
        _ ≤ max_ratio * (C : ℝ) ^ (n - 1) := by
            gcongr
        _ ≤ max_ratio * (C : ℝ) ^ (2 * (n - 1)) := by
            gcongr
    have h_K_inv_mul_vol_C_eq :
        ENNReal.ofReal K_inv_const * (Tube.volume_le.C n : ENNReal) =
          (Tube.le_volume.c n : ENNReal) := by
      rw [hK_inv_def]
      rw [show ((Tube.volume_le.C n : NNReal) : ENNReal) =
            ENNReal.ofReal (Tube.volume_le.C n : ℝ) from
              (ENNReal.ofReal_coe_nnreal).symm,
          show ((Tube.le_volume.c n : NNReal) : ENNReal) =
            ENNReal.ofReal (Tube.le_volume.c n : ℝ) from
              (ENNReal.ofReal_coe_nnreal).symm]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    have h_lb_real_form :
        ENNReal.ofReal lb_real * (Tube.volume_le.C n : ENNReal) *
            (ρ_anchor : ENNReal) ^ (n - 1) =
          (Tube.le_volume.c n : ENNReal) * (δ : ENNReal) ^ (n - 1) := by
      have h1 : ENNReal.ofReal lb_real =
          ENNReal.ofReal K_inv_const *
            ENNReal.ofReal ((δr / ρar) ^ (n - 1)) := by
        rw [hlb_def]
        exact ENNReal.ofReal_mul h_K_inv_pos.le
      rw [h1]
      have h_inner_pow_eq :
          ENNReal.ofReal ((δr / ρar) ^ (n - 1)) * (ρ_anchor : ENNReal) ^ (n - 1)
            = (δ : ENNReal) ^ (n - 1) := by
        have h_anchor_pow_eq : ((ρ_anchor : NNReal) : ENNReal) ^ (n - 1) =
            ENNReal.ofReal ((ρar : ℝ) ^ (n - 1)) := by
          rw [show ((ρ_anchor : NNReal) : ENNReal) =
                ENNReal.ofReal ((ρ_anchor : ℝ)) from
                  (ENNReal.ofReal_coe_nnreal).symm]
          rw [← ENNReal.ofReal_pow h_anchor_pos.le]
        have h_δ_pow_eq : ((δ : NNReal) : ENNReal) ^ (n - 1) =
            ENNReal.ofReal ((δr : ℝ) ^ (n - 1)) := by
          rw [show ((δ : NNReal) : ENNReal) = ENNReal.ofReal ((δ : ℝ)) from
                (ENNReal.ofReal_coe_nnreal).symm]
          rw [← ENNReal.ofReal_pow hδr_pos.le]
        rw [h_anchor_pow_eq, h_δ_pow_eq]
        rw [← ENNReal.ofReal_mul (pow_nonneg h_δ_div_ρar_pos.le _)]
        congr 1
        rw [div_pow]
        rw [hδr_def, hρar_def]
        field_simp
      calc ENNReal.ofReal K_inv_const *
              ENNReal.ofReal ((δr / ρar) ^ (n - 1)) *
              (Tube.volume_le.C n : ENNReal) * (ρ_anchor : ENNReal) ^ (n - 1)
          = (ENNReal.ofReal K_inv_const * (Tube.volume_le.C n : ENNReal)) *
              (ENNReal.ofReal ((δr / ρar) ^ (n - 1)) *
                (ρ_anchor : ENNReal) ^ (n - 1)) := by ring
        _ = (Tube.le_volume.c n : ENNReal) * (δ : ENNReal) ^ (n - 1) := by
              rw [h_K_inv_mul_vol_C_eq, h_inner_pow_eq]
    have h_lb_denom_le_numer :
        ENNReal.ofReal lb_real * denom_anchor ≤ numer_anchor := by
      calc ENNReal.ofReal lb_real * denom_anchor
          ≤ ENNReal.ofReal lb_real *
              ((Tube.volume_le.C n : ENNReal) * (ρ_anchor : ENNReal) ^ (n - 1)) := by
            gcongr
        _ = ENNReal.ofReal lb_real * (Tube.volume_le.C n : ENNReal) *
              (ρ_anchor : ENNReal) ^ (n - 1) := by ring
        _ = (Tube.le_volume.c n : ENNReal) * (δ : ENNReal) ^ (n - 1) :=
            h_lb_real_form
        _ ≤ numer_anchor := h_numer_ge
    have h_target_denom_le_numer :
        ENNReal.ofReal target_real * denom_anchor ≤ numer_anchor := by
      calc ENNReal.ofReal target_real * denom_anchor
          ≤ ENNReal.ofReal lb_real * denom_anchor := by
            exact mul_le_mul_left (ENNReal.ofReal_le_ofReal h_target_le_lb) _
        _ ≤ numer_anchor := h_lb_denom_le_numer
    have h_denom_anchor_pos : 0 < denom_anchor := by
      have h_anchor_pow_pos : (0 : ENNReal) < (ρ_anchor : ENNReal) ^ (n - 1) := by
        apply ENNReal.pow_pos
        exact_mod_cast h_anchor_pos_NN
      have h_le : (Tube.le_volume.c n : ENNReal) * (ρ_anchor : ENNReal) ^ (n - 1) ≤
          denom_anchor :=
        Tube.le_volume (Tube.rescale (T' p₀) ρ_anchor)
      have h_lhs_pos : (0 : ENNReal) < (Tube.le_volume.c n : ENNReal) *
          (ρ_anchor : ENNReal) ^ (n - 1) :=
        ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos n).ne')
          h_anchor_pow_pos.ne'
      exact lt_of_lt_of_le h_lhs_pos h_le
    have h_eq_anchor : Kakeya.densityIn
          (s.filter (fun p : ι × E =>
            (T' p).toConvexSpaceBody ≤
              (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody))
          (fun p : ι × E => (T' p).toConvexSpaceBody)
          (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody
          = numer_anchor / denom_anchor := by
      change (∑ p ∈ s.filter _ with _, _) / denom_anchor = numer_anchor / denom_anchor
      simp only [hnumer_anchor_def, hfilter_def]
      congr 1
      apply Finset.sum_congr
      · ext p
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hp, h1⟩, h2⟩; exact ⟨hp, h1⟩
        · rintro ⟨hp, h1⟩; exact ⟨⟨hp, h1⟩, h1⟩
      · intros; rfl
    rw [h_eq_anchor]
    rw [ENNReal.le_div_iff_mul_le (Or.inl h_denom_anchor_pos.ne')
      (Or.inl h_denom_anchor_ne_top)]
    exact h_target_denom_le_numer

end Kakeya
