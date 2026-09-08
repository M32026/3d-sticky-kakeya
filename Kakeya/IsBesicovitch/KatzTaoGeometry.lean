/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.CylinderApprox

/-!
# Elementary geometry for the separated Katz--Tao inequality

This file collects the low-dimensional tube and difference-body estimates used
in the geometric proof of the separated Katz--Tao inequality.
-/

@[expose] public section

open MeasureTheory
open scoped Pointwise

namespace Kakeya.IsBesicovitch

/-- A `1 x delta` tube in Euclidean three-space has volume at most
`3 * pi * delta^2` when `delta <= 1`. -/
lemma tube_volume_real_le_three_pi
    {δ : NNReal} (hδ_le : (δ : ℝ) ≤ 1)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) :
    volume.real T.carrier ≤ 3 * Real.pi * (δ : ℝ) ^ 2 := by
  let cyl := cylinder T.midpoint T.direction
    (-(1 / 2) - (δ : ℝ)) (1 / 2 + (δ : ℝ)) (δ : ℝ)
  have hsub : T.carrier ⊆ cyl := Tube.carrier_subset_cylinder_self T (by positivity)
  have hdir : ‖T.direction‖ = 1 := T.norm_direction
  have hdir_ne : T.direction ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdir
    norm_num at hdir
  have hfinrank : Module.finrank ℝ
      (((ℝ ∙ T.direction)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))) = 2 := by
    apply Submodule.finrank_add_finrank_orthogonal'
    rw [finrank_span_singleton hdir_ne]
    norm_num
  letI : Nontrivial
      (((ℝ ∙ T.direction)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfinrank]; norm_num)
  have hcross :
      volume (Metric.closedBall
        (0 : ((ℝ ∙ T.direction)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))) (δ : ℝ)) =
        ENNReal.ofReal (δ : ℝ) ^ 2 * ENNReal.ofReal Real.pi := by
    rw [InnerProductSpace.volume_closedBall_of_dim_even (k := 1) hfinrank]
    rw [hfinrank]
    norm_num
  have hcyl : volume cyl =
      ENNReal.ofReal ((1 / 2 + (δ : ℝ)) - (-(1 / 2) - (δ : ℝ))) *
        (ENNReal.ofReal (δ : ℝ) ^ 2 * ENNReal.ofReal Real.pi) := by
    rw [show cyl = cylinder T.midpoint T.direction
      (-(1 / 2) - (δ : ℝ)) (1 / 2 + (δ : ℝ)) (δ : ℝ) from rfl,
      volume_cylinder hdir, hcross]
  have hcyl_fin : volume cyl ≠ ⊤ := by
    rw [hcyl]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
  have hmono : volume.real T.carrier ≤ volume.real cyl :=
    measureReal_mono hsub hcyl_fin
  have hcyl_real : volume.real cyl =
      (1 + 2 * (δ : ℝ)) * (δ : ℝ) ^ 2 * Real.pi := by
    rw [measureReal_def, hcyl, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (δ : ℝ)),
      ENNReal.toReal_ofReal Real.pi_pos.le,
      ENNReal.toReal_ofReal]
    · ring
    · have : (0 : ℝ) ≤ δ := by positivity
      linarith
  calc
    volume.real T.carrier ≤ volume.real cyl := hmono
    _ = (1 + 2 * (δ : ℝ)) * (δ : ℝ) ^ 2 * Real.pi := hcyl_real
    _ = ((1 + 2 * (δ : ℝ)) * Real.pi) * (δ : ℝ) ^ 2 := by ring
    _ ≤ (3 * Real.pi) * (δ : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg (δ : ℝ))
      exact mul_le_mul_of_nonneg_right (by linarith) Real.pi_pos.le

/-- Alignment with a unit vector by a scalar at least one forces the scalar to
be one, since a tube's direction already has norm one. -/
lemma tube_direction_eq_of_aligned
    {δ : NNReal} (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    {ω : EuclideanSpace ℝ (Fin 3)} (hω : ‖ω‖ = 1)
    (h_align : ∃ s : ℝ, 1 ≤ s ∧ s ≤ 2 ∧
      ∀ i : Fin 3, T.direction i = s * ω i) :
    T.direction = ω := by
  obtain ⟨s, hs_one, -, hs⟩ := h_align
  have hvec : T.direction = s • ω := by
    ext i
    simpa using hs i
  have hs_nonneg : 0 ≤ s := zero_le_one.trans hs_one
  have hs_eq : s = 1 := by
    have hnorm := congrArg norm hvec
    rw [T.norm_direction, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs_nonneg, hω,
      mul_one] at hnorm
    exact hnorm.symm
  simpa [hs_eq] using hvec

/-- If a tube carrier lies in `K`, then the difference body `K - K` contains
the closed ball of radius `2 * delta` around the tube direction. -/
lemma closedBall_direction_two_mul_subset_sub
    {δ : NNReal} (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (hTK : T.carrier ⊆ K.carrier) :
    Metric.closedBall T.direction (2 * (δ : ℝ)) ⊆ K.carrier - K.carrier := by
  intro z hz
  let v : EuclideanSpace ℝ (Fin 3) := (1 / 2 : ℝ) • (z - T.direction)
  have hv : ‖v‖ ≤ (δ : ℝ) := by
    have hz' : ‖z - T.direction‖ ≤ 2 * (δ : ℝ) := by
      simpa [dist_eq_norm] using hz
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith
  have hy : T.y + v ∈ K.carrier := by
    apply hTK
    apply T.closedBall_subset_carrier_of_mem_segment (right_mem_segment ℝ T.x T.y)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hv
  have hx : T.x - v ∈ K.carrier := by
    apply hTK
    apply T.closedBall_subset_carrier_of_mem_segment (left_mem_segment ℝ T.x T.y)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hv
  rw [Set.mem_sub]
  refine ⟨T.y + v, hy, T.x - v, hx, ?_⟩
  dsimp only [v, Tube.direction]
  module

/-- Aligned form of `closedBall_direction_two_mul_subset_sub`: the difference
body contains the radius-`2 * delta` ball around the prescribed unit direction. -/
lemma closedBall_aligned_two_mul_subset_sub
    {δ : NNReal} (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    {ω : EuclideanSpace ℝ (Fin 3)} (hω : ‖ω‖ = 1)
    (h_align : ∃ s : ℝ, 1 ≤ s ∧ s ≤ 2 ∧
      ∀ i : Fin 3, T.direction i = s * ω i)
    (hTK : T.carrier ⊆ K.carrier) :
    Metric.closedBall ω (2 * (δ : ℝ)) ⊆ K.carrier - K.carrier := by
  rw [← tube_direction_eq_of_aligned T hω h_align]
  exact closedBall_direction_two_mul_subset_sub T K hTK

end Kakeya.IsBesicovitch
