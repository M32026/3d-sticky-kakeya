/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Compatibility additions for convex space bodies

This module preserves the historical import path and the extra homothety inclusion used by the
Section 7 development.
-/

open MeasureTheory ENNReal

@[expose] public section

/-- **Steiner-type inclusion.** If a compact convex set `H` contains the closed
`δ`-ball about `p`, then its closed `δ`-thickening is contained in the image of
`H` under the homothety centered at `p` with ratio `2` (the map `x ↦ 2 • x - p`). -/
lemma cthickening_subset_homothety_two
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : Set F) (hH_conv : Convex ℝ H) (hH_compact : IsCompact H)
    (p : F) {δ : ℝ} (hδ_pos : 0 ≤ δ)
    (hp_ball : Metric.closedBall p δ ⊆ H) :
    Metric.cthickening δ H ⊆ (AffineMap.homothety p (2 : ℝ)) '' H := by
  have hH_ne : H.Nonempty := (Metric.nonempty_closedBall.mpr hδ_pos).mono hp_ball
  intro x hx
  obtain ⟨h₀, hh₀_mem, hh₀_dist⟩ := hH_compact.exists_infDist_eq_dist hH_ne x
  rw [Metric.mem_cthickening_iff] at hx
  have h_inf_le : Metric.infDist x H ≤ δ := by
    have hed_eq : Metric.infEDist x H = ENNReal.ofReal (Metric.infDist x H) := by
      rw [Metric.infDist, ENNReal.ofReal_toReal]
      exact Metric.infEDist_ne_top hH_ne
    rw [hed_eq] at hx
    rwa [ENNReal.ofReal_le_ofReal_iff hδ_pos] at hx
  have hdist_le : dist x h₀ ≤ δ := hh₀_dist ▸ h_inf_le
  set g : F := x - h₀ + p with hg_def
  have hdist_eq : dist g p = dist x h₀ := by
    simp only [hg_def, dist_eq_norm]
    congr 1
    abel
  have hg_mem : g ∈ H := by
    apply hp_ball
    rw [Metric.mem_closedBall, hdist_eq]
    exact hdist_le
  set h := (1 / 2 : ℝ) • h₀ + (1 / 2 : ℝ) • g with hh_def
  have hh_mem : h ∈ H :=
    hH_conv hh₀_mem hg_mem (by norm_num) (by norm_num) (by norm_num)
  refine ⟨h, hh_mem, ?_⟩
  rw [AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add, hh_def, hg_def]
  match_scalars <;> ring
