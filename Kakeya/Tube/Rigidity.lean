/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Equal-radius tube rigidity

For two `δ`-tubes of the same radius (unit core length), `A.carrier ⊆ B.carrier` forces
`A.carrier = B.carrier`. The `δ`-thickening on both sides cancels (a separation/support-function
argument), reducing to nested equal-length core segments, which must coincide.

Used to bound the leaf-scale (`ρ = δ`) bounded-overlap count by `≤ 1` without essential
distinctness: any two leaf tubes comparable (via a shared `δ`-tube) with a fixed `V` have
`carrier = V.carrier`, so distinct-carrier leaf tubes give at most one such comparable tube.
-/

open Metric Set
open scoped NNReal

@[expose] public section

namespace Tube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- If a point `a` of `A`'s core segment lies in `A.carrier ⊆ B.carrier`, then `a` lies on `B`'s
core segment: the `δ`-thickening on both sides cancels. -/
theorem mem_segment_of_carrier_subset {δ : NNReal} (A B : Tube δ E)
    (h : A.carrier ⊆ B.carrier) {a : E} (ha : a ∈ segment ℝ A.x A.y) :
    a ∈ segment ℝ B.x B.y := by
  by_contra haB
  obtain ⟨f, u, hfa, hfb⟩ := geometric_hahn_banach_point_closed
    (convex_segment (𝕜 := ℝ) B.x B.y) isClosed_segment haB
  have hBx : B.x ∈ segment ℝ B.x B.y := left_mem_segment ℝ _ _
  have hf_ne : f ≠ 0 := by
    rintro rfl
    have h1 := hfb B.x hBx
    simp only [zero_apply] at hfa h1
    linarith
  set y : E := (InnerProductSpace.toDual ℝ E).symm f with hy
  have hfy : ∀ x, f x = inner ℝ y x := fun x => InnerProductSpace.toDual_symm_apply.symm
  have hyne : y ≠ 0 := by
    intro hy0
    apply hf_ne
    refine ContinuousLinearMap.ext (fun x => ?_)
    rw [hfy x, hy0, inner_zero_left, zero_apply]
  have hynorm : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hyne
  have hnormf : ‖f‖ = ‖y‖ := ((InnerProductSpace.toDual ℝ E).symm.norm_map f).symm
  set w : E := ‖y‖⁻¹ • y with hw
  have hwnorm : ‖w‖ = 1 := by
    rw [hw, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hynorm)]
  have hfw : f w = ‖y‖ := by
    rw [hfy w, hw, inner_smul_right, real_inner_self_eq_norm_mul_norm]
    field_simp
  set p : E := a - (δ : ℝ) • w with hp
  have hdist_pa : dist p a = (δ : ℝ) := by
    rw [hp, dist_eq_norm, show a - (δ : ℝ) • w - a = -((δ : ℝ) • w) from by abel,
      norm_neg, norm_smul, hwnorm, mul_one, Real.norm_eq_abs, abs_of_nonneg δ.coe_nonneg]
  have hpA : p ∈ A.carrier := by
    rw [A.carrier_eq]
    exact Set.mem_biUnion ha (Metric.mem_closedBall.mpr (le_of_eq hdist_pa))
  have hpB : p ∈ B.carrier := h hpA
  rw [B.carrier_eq] at hpB
  obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.mp hpB
  rw [Metric.mem_closedBall] at hpz
  have hfp : f p = f a - (δ : ℝ) * ‖y‖ := by
    rw [hp, map_sub, map_smul, hfw, smul_eq_mul]
  have hfz_le : f z ≤ f a := by
    have hzp : ‖z - p‖ ≤ (δ : ℝ) := by rw [← dist_eq_norm, dist_comm]; exact hpz
    have h1 : f z - f p ≤ ‖f‖ * (δ : ℝ) := by
      calc f z - f p = f (z - p) := (map_sub f z p).symm
        _ ≤ |f (z - p)| := le_abs_self _
        _ = ‖f (z - p)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖f‖ * ‖z - p‖ := f.le_opNorm _
        _ ≤ ‖f‖ * (δ : ℝ) := mul_le_mul_of_nonneg_left hzp (norm_nonneg _)
    rw [hfp, hnormf] at h1
    linarith
  have := hfb z hz
  linarith [hfa]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Equal-radius rigidity.** If two `δ`-tubes satisfy `A.carrier ⊆ B.carrier`, their carriers are
equal: the core segments are nested and of equal (unit) length, hence equal. -/
theorem carrier_eq_of_subset {δ : NNReal} (A B : Tube δ E)
    (h : A.carrier ⊆ B.carrier) : A.carrier = B.carrier := by
  have hsub : segment ℝ A.x A.y ⊆ segment ℝ B.x B.y :=
    fun a ha => mem_segment_of_carrier_subset A B h ha
  obtain ⟨s, hs, hsx⟩ :=
    (segment_eq_image' ℝ B.x B.y) ▸ hsub (left_mem_segment ℝ A.x A.y)
  obtain ⟨t, ht, hty⟩ :=
    (segment_eq_image' ℝ B.x B.y) ▸ hsub (right_mem_segment ℝ A.x A.y)
  simp only [Set.mem_Icc] at hs ht
  have hdir : A.y - A.x = (t - s) • (B.y - B.x) := by rw [← hty, ← hsx]; module
  have hnorm1 : ‖B.y - B.x‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact B.dist_eq_one
  have hnormA : ‖A.y - A.x‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact A.dist_eq_one
  have hts : |t - s| = 1 := by
    have h2 : ‖(t - s) • (B.y - B.x)‖ = 1 := by rw [← hdir]; exact hnormA
    rwa [norm_smul, hnorm1, mul_one, Real.norm_eq_abs] at h2
  have hseg : segment ℝ A.x A.y = segment ℝ B.x B.y := by
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp hts with htt | htt
    · have hs0 : s = 0 := by linarith [hs.1, hs.2, ht.1, ht.2]
      have ht1 : t = 1 := by linarith [hs.1, hs.2, ht.1, ht.2]
      have hAx : A.x = B.x := by have := hsx.symm; rw [hs0] at this; simpa using this
      have hAy : A.y = B.y := by have := hty.symm; rw [ht1] at this; simpa using this
      rw [hAx, hAy]
    · have hs1 : s = 1 := by linarith [hs.1, hs.2, ht.1, ht.2]
      have ht0 : t = 0 := by linarith [hs.1, hs.2, ht.1, ht.2]
      have hAx : A.x = B.y := by have := hsx.symm; rw [hs1] at this; simpa using this
      have hAy : A.y = B.x := by have := hty.symm; rw [ht0] at this; simpa using this
      rw [hAx, hAy, segment_symm]
  rw [A.carrier_eq_cthickening, B.carrier_eq_cthickening, hseg]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Rigidity across a radius equality `δ₁ = δ₂` (the radii need not be defeq). -/
theorem carrier_eq_of_subset' {δ₁ δ₂ : NNReal} (hδ : δ₁ = δ₂)
    (A : Tube δ₁ E) (B : Tube δ₂ E) (h : A.carrier ⊆ B.carrier) : A.carrier = B.carrier := by
  subst hδ; exact carrier_eq_of_subset A B h

end Tube
