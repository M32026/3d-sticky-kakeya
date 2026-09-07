module

/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Induction on Scales Team
-/
public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# SSet properties for finite tube families

This module establishes properties of `IsFiniteTubeSSet`, the finite cardinal
Frostman condition on dyadic tube-parameter sets.

## Critical note

The "subset preserves constant" lemma `IsFiniteTubeSSet.subset` (same C) is
**false**. The Frostman bound is normalized by `F.card`, so passing to a
smaller subset weakens the right-hand side. A counterexample:
- n=1, δ=1/2, s=1, C=1
- F = {T1=(0,0), T2=(100,0)}, G = {T1}
- F satisfies the condition; G fails at center=T1, r=1/2 since 1 > 1/2.

The correct subset lemma `subset_scaled` scales the constant by `|F|/|G|`.

## Whiteprint node
`sset_properties` under `InductionOnScales/`.
-/

open scoped BigOperators

noncomputable section

namespace InductionOnScales

/-- `tubeParamDist` is symmetric. -/
lemma tubeParamDist_symm {n : ℕ} (T U : DyadicTube n) :
    tubeParamDist T U = tubeParamDist U T := by
  have h1 : |T.slope - U.slope| = |U.slope - T.slope| := by
    have h : T.slope - U.slope = -(U.slope - T.slope) := by ring
    rw [h, abs_neg]
  have h2 : |T.intercept - U.intercept| = |U.intercept - T.intercept| := by
    have h : T.intercept - U.intercept = -(U.intercept - T.intercept) := by ring
    rw [h, abs_neg]
  simp [tubeParamDist, h1, h2]

/-- `tubeParamDist` satisfies the triangle inequality. -/
lemma tubeParamDist_triangle {n : ℕ} (T U V : DyadicTube n) :
    tubeParamDist T U ≤ tubeParamDist T V + tubeParamDist V U := by
  have h_abs : ∀ (a b : ℝ), |a + b| ≤ |a| + |b| := by
    intro a b
    exact abs_add_le a b
  have h1 : |T.slope - U.slope| ≤ |T.slope - V.slope| + |V.slope - U.slope| := by
    have h_eq : T.slope - U.slope = (T.slope - V.slope) + (V.slope - U.slope) := by ring
    rw [h_eq]; exact h_abs _ _
  have h2 : |T.intercept - U.intercept| ≤ |T.intercept - V.intercept| + |V.intercept - U.intercept| := by
    have h_eq : T.intercept - U.intercept = (T.intercept - V.intercept) + (V.intercept - U.intercept) := by ring
    rw [h_eq]; exact h_abs _ _
  have h3 : |T.slope - V.slope| ≤ tubeParamDist T V := le_max_left _ _
  have h4 : |T.intercept - V.intercept| ≤ tubeParamDist T V := le_max_right _ _
  have h5 : |V.slope - U.slope| ≤ tubeParamDist V U := le_max_left _ _
  have h6 : |V.intercept - U.intercept| ≤ tubeParamDist V U := le_max_right _ _
  have h7 : |T.slope - U.slope| ≤ tubeParamDist T V + tubeParamDist V U := by linarith
  have h8 : |T.intercept - U.intercept| ≤ tubeParamDist T V + tubeParamDist V U := by linarith
  exact max_le h7 h8

namespace IsFiniteTubeSSet

variable {n : ℕ} {s C : ℝ} {F : Finset (DyadicTube n)}

/-- Extract separation condition. -/
lemma separation (h : IsFiniteTubeSSet s C F) :
    ∀ T ∈ F, ∀ U ∈ F, T ≠ U → dyadicDelta n ≤ tubeParamDist T U := by
  rcases h with ⟨_, _, _, h_sep, _⟩
  exact h_sep

/-- Extract Frostman condition. -/
lemma frostman (h : IsFiniteTubeSSet s C F) :
    ∀ (center : DyadicTube n) (r : ℝ), dyadicDelta n ≤ r →
      ((F.filter fun T => tubeParamDist T center ≤ r).card : ℝ) ≤
      C * Real.rpow r s * (F.card : ℝ) := by
  rcases h with ⟨_, _, _, _, h_frost⟩
  exact h_frost

/-- Monotonicity in the constant C. -/
lemma monotone_const {C' : ℝ} (hC : C ≤ C') (h : IsFiniteTubeSSet s C F) :
    IsFiniteTubeSSet s C' F := by
  rcases h with ⟨h_nonempty, h_C, h_s, h_sep, h_frost⟩
  refine ⟨h_nonempty, le_trans h_C hC, h_s, h_sep, ?_⟩
  intro center r hr
  have h1 := h_frost center r hr
  have hr_pos : 0 ≤ r := by
    have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
    linarith
  have h_rpow_nonneg : 0 ≤ Real.rpow r s := Real.rpow_nonneg hr_pos s
  have h_card_nonneg : 0 ≤ (F.card : ℝ) := by positivity
  have h2 : C * Real.rpow r s * (F.card : ℝ) ≤ C' * Real.rpow r s * (F.card : ℝ) := by
    nlinarith
  exact h1.trans h2

/-- Corrected subset lemma: the constant must scale by `|F|/|G|`.

The Frostman condition is normalized by the total cardinal, so a subset
with the same constant is generally **not** an SSet. The correct bound
uses `C' = C * |F| / |G|`. -/
lemma subset_scaled {G : Finset (DyadicTube n)} (hGne : G.Nonempty)
    (hsub : G ⊆ F) (h : IsFiniteTubeSSet s C F) :
    IsFiniteTubeSSet s (C * (F.card : ℝ) / (G.card : ℝ)) G := by
  rcases h with ⟨hFne, hC, h_s, h_sep, h_frost⟩
  have hGpos : (G.card : ℝ) > 0 := by exact_mod_cast hGne.card_pos
  have h_card_le : (G.card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
  set C' := C * (F.card : ℝ) / (G.card : ℝ) with hC'def
  have hC'_one : 1 ≤ C' := by
    rw [hC'def]
    have h1 : C ≥ 1 := hC
    have h3 : (F.card : ℝ) / (G.card : ℝ) ≥ 1 := by
      have h32 : (G.card : ℝ) > 0 := hGpos
      calc (F.card : ℝ) / (G.card : ℝ)
        ≥ (G.card : ℝ) / (G.card : ℝ) := by gcongr
        _ = 1 := by field_simp [h32.ne'] <;> ring
    have h4 : 1 ≤ C * (F.card : ℝ) / (G.card : ℝ) := by
      have h43 : C * (F.card : ℝ) / (G.card : ℝ) = C * ((F.card : ℝ) / (G.card : ℝ)) := by
        field_simp [hGpos.ne'] <;> ring
      rw [h43]
      calc 1
        = 1 * 1 := by ring
        _ ≤ C * ((F.card : ℝ) / (G.card : ℝ)) := by gcongr
    exact h4
  refine ⟨hGne, hC'_one, h_s, ?_, ?_⟩
  · intro T hT U hU hne
    exact h_sep T (hsub hT) U (hsub hU) hne
  · intro center r hr
    set filtG := G.filter fun T => tubeParamDist T center ≤ r with hfiltG
    set filtF := F.filter fun T => tubeParamDist T center ≤ r with hfiltF
    have h_filter : filtG ⊆ filtF := by
      intro x hx
      simp only [hfiltG, hfiltF, Finset.mem_filter] at hx ⊢
      exact ⟨hsub hx.1, hx.2⟩
    have h3 : (filtG.card : ℝ) ≤ (filtF.card : ℝ) := by
      exact_mod_cast Finset.card_le_card h_filter
    have h4 : (filtF.card : ℝ) ≤ C * Real.rpow r s * (F.card : ℝ) := h_frost center r hr
    have h5 : C * Real.rpow r s * (F.card : ℝ) = C' * Real.rpow r s * (G.card : ℝ) := by
      rw [hC'def]; field_simp [hGpos.ne'] <;> ring
    have h6 : (filtG.card : ℝ) ≤ C' * Real.rpow r s * (G.card : ℝ) := by
      calc (filtG.card : ℝ)
        ≤ (filtF.card : ℝ) := h3
        _ ≤ C * Real.rpow r s * (F.card : ℝ) := h4
        _ = C' * Real.rpow r s * (G.card : ℝ) := h5
    simpa [hfiltG] using h6

end IsFiniteTubeSSet

end InductionOnScales
