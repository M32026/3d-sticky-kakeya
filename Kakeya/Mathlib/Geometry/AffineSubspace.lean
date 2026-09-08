/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Distance to an affine subspace under thickening

A geometric lemma relating the infimal distance from a point to an affine subspace `A`
with the closed thickenings of `A`: if the closed `ρ`-ball around `x` is contained in the
closed `r'`-thickening of `A`, then `infDist x A + ρ ≤ r'`. This is the geometric core of
`Metric.le_ethickness_cthickening`.
-/

@[expose] public section

open Metric EuclideanGeometry

variable {V E : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace E] [NormedAddTorsor V E]

/-- Pushing `x` by `ρ` along a unit vector orthogonal to `A.direction` (which exists since
`A` is a strict subspace, `A.directionᗮ ≠ ⊥`) shows that if the closed `ρ`-ball around `x`
lies in the closed `r'`-thickening of `A`, then `infDist x A + ρ ≤ r'`. -/
lemma infDist_add_le_of_closedBall_subset_cthickening
    {A : AffineSubspace ℝ E} [Nonempty A] [A.direction.HasOrthogonalProjection]
    (hAne : (A : Set E).Nonempty) (hperp : A.directionᗮ ≠ ⊥) {x : E} {ρ : ℝ} (hρ : 0 < ρ)
    {r' : NNReal} (hballsub : closedBall x ρ ⊆ cthickening (r' : ℝ) (A : Set E)) :
    Metric.infDist x (A : Set E) + ρ ≤ (r' : ℝ) := by
  set proj : E := (orthogonalProjection A x : E)
  have hres : x -ᵥ proj ∈ A.directionᗮ := vsub_orthogonalProjection_mem_direction_orthogonal A x
  have hd : Metric.infDist x (A : Set E) = ‖x -ᵥ proj‖ := by
    rw [← dist_orthogonalProjection_eq_infDist A x, dist_eq_norm_vsub V]
  -- a unit vector `u ⊥ A.direction` with `⟪x -ᵥ proj, u⟫ = infDist x A`
  obtain ⟨u, hu_mem, hu_norm, hu_inner⟩ :
      ∃ u : V, u ∈ A.directionᗮ ∧ ‖u‖ = 1 ∧
        (inner ℝ (x -ᵥ proj) u) = Metric.infDist x (A : Set E) := by
    rcases eq_or_ne (x -ᵥ proj) 0 with h0 | h0
    · obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.ne_bot_iff _ |>.1 hperp
      refine ⟨‖v‖⁻¹ • v, Submodule.smul_mem _ _ hv_mem, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv_ne)]
      · rw [h0, inner_zero_left, hd, h0, norm_zero]
    · refine ⟨‖x -ᵥ proj‖⁻¹ • (x -ᵥ proj), Submodule.smul_mem _ _ hres, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
      · rw [real_inner_smul_right, real_inner_self_eq_norm_mul_norm, hd, ← mul_assoc,
          inv_mul_cancel₀ (norm_ne_zero_iff.2 h0), one_mul]
  -- the pushed point `y = ρ • u +ᵥ x`
  set y : E := (ρ • u) +ᵥ x with hydef
  have hy_ball : y ∈ closedBall x ρ := by
    rw [mem_closedBall, dist_eq_norm_vsub V, hydef, vadd_vsub, norm_smul,
      Real.norm_eq_abs, abs_of_pos hρ, hu_norm, mul_one]
  have hy_infDist : Metric.infDist y (A : Set E) ≤ (r' : ℝ) :=
    ENNReal.toReal_le_of_le_ofReal (NNReal.coe_nonneg r')
      (Metric.mem_cthickening_iff.1 (hballsub hy_ball))
  have hlb : Metric.infDist x (A : Set E) + ρ ≤ Metric.infDist y (A : Set E) := by
    rw [Metric.le_infDist hAne]
    intro a ha
    have hpa : proj -ᵥ a ∈ A.direction :=
      AffineSubspace.vsub_mem_direction (orthogonalProjection A x).2 ha
    have hinner : (inner ℝ (y -ᵥ a) u) = Metric.infDist x (A : Set E) + ρ := by
      have e1 : y -ᵥ a = ρ • u + (x -ᵥ a) := by rw [hydef, vadd_vsub_assoc]
      have e2 : (x -ᵥ a : V) = (x -ᵥ proj) + (proj -ᵥ a) := (vsub_add_vsub_cancel _ _ _).symm
      rw [e1, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_mul_norm, hu_norm,
        e2, inner_add_left, hu_inner, Submodule.inner_right_of_mem_orthogonal hpa hu_mem]
      ring
    calc Metric.infDist x (A : Set E) + ρ = inner ℝ (y -ᵥ a) u := hinner.symm
      _ ≤ |inner ℝ (y -ᵥ a) u| := le_abs_self _
      _ ≤ ‖y -ᵥ a‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ = ‖y -ᵥ a‖ := by rw [hu_norm, mul_one]
      _ = dist y a := (dist_eq_norm_vsub V y a).symm
  linarith [hlb, hy_infDist]
