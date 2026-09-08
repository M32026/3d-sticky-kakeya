/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Tactic

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard

open MeasureTheory
open scoped ContDiff

variable {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → ℝ}

/-- Simple Taylor estimate: if `fderiv ℝ f x = 0` and `f` is `C²`, then
`|f y - f x| ≤ C * ‖y - x‖ ^ 2` for `y` in a convex compact set containing `x`. -/
lemma taylor_estimate_second_order
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : Convex ℝ K) (hK' : IsCompact K)
    (hf : ContDiff ℝ (1 + 1) f) {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ K)
    (hderiv : fderiv ℝ f x = 0) :
    ∃ C : ℝ, ∀ y ∈ K, |f y - f x| ≤ C * ‖y - x‖ ^ 2 := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := by
    have h12 := (contDiff_succ_iff_fderiv.mp hf)
    exact h12.2.2
  have h1' : ContDiffOn ℝ 1 (fderiv ℝ f) K := h1.contDiffOn
  have h_lip : ∃ (C₁ : NNReal), LipschitzOnWith C₁ (fderiv ℝ f) K :=
    h1'.exists_lipschitzOnWith (by norm_num) hK hK'
  rcases h_lip with ⟨C₁, hC₁⟩
  have h_dist_le : ∀ (x : _), x ∈ K → ∀ (y : _), y ∈ K → dist (fderiv ℝ f x) (fderiv ℝ f y) ≤ (C₁ : ℝ) * dist x y :=
    lipschitzOnWith_iff_dist_le_mul.mp hC₁
  have h3 : ∀ z ∈ K, ‖fderiv ℝ f z‖ ≤ (C₁ : ℝ) * ‖z - x‖ := by
    intro z hz
    have h4 : dist (fderiv ℝ f z) (fderiv ℝ f x) ≤ (C₁ : ℝ) * dist z x := h_dist_le z hz x hx
    have h6 : ‖fderiv ℝ f z - fderiv ℝ f x‖ = dist (fderiv ℝ f z) (fderiv ℝ f x) := by rw [dist_eq_norm]
    have h7 : ‖z - x‖ = dist z x := by rw [dist_eq_norm]
    have h8 : ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ (C₁ : ℝ) * ‖z - x‖ := by
      rw [h6, h7]; exact h4
    rw [hderiv, sub_zero] at h8
    exact h8
  have h_diff : Differentiable ℝ f := hf.differentiable (by simp)
  use (C₁ : ℝ)
  intro y hy
  let S := segment ℝ x y
  have hS_sub : S ⊆ K := hK.segment_subset hx hy
  have h4 : ∀ z ∈ S, ‖fderiv ℝ f z‖ ≤ (C₁ : ℝ) * ‖y - x‖ := by
    intro z hz
    have hzK : z ∈ K := hS_sub hz
    have h5 : ‖z - x‖ ≤ ‖y - x‖ := norm_sub_le_of_mem_segment hz
    have h6 : ‖fderiv ℝ f z‖ ≤ (C₁ : ℝ) * ‖z - x‖ := h3 z hzK
    calc
      ‖fderiv ℝ f z‖ ≤ (C₁ : ℝ) * ‖z - x‖ := h6
      _ ≤ (C₁ : ℝ) * ‖y - x‖ := by
        gcongr
  have h_main : ‖f y - f x‖ ≤ (C₁ : ℝ) * ‖y - x‖ * ‖y - x‖ := by
    have h_conv : Convex ℝ S := convex_segment _ _
    exact h_conv.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => h_diff.differentiableAt) h4 (by exact left_mem_segment ℝ x y) (by exact right_mem_segment ℝ x y)
  have h_final : |f y - f x| ≤ (C₁ : ℝ) * ‖y - x‖ ^ 2 := by
    have h9 : |f y - f x| = ‖f y - f x‖ := by simp
    rw [h9]
    have h10 : (C₁ : ℝ) * ‖y - x‖ * ‖y - x‖ = (C₁ : ℝ) * ‖y - x‖ ^ 2 := by ring
    rw [h10] at h_main
    exact h_main
  exact h_final


end ForMathlib.Analysis.Calculus.Sard
