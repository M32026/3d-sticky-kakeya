/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Topology.Lipschitz
public import Kakeya.Mathlib.Geometry.Projection
public import Kakeya.Thickness.Basic
public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Thickness under affine map.
In this file we show how `ethickness` behaves under Lipschitz affine map
One consequence is : Orthogonal projections shrinks thickness.
-/

@[expose] public section

open EuclideanGeometry AffineSubspace Metric

section
variable
  {𝕜} [Ring 𝕜] [Nontrivial 𝕜]
  {V} [AddCommGroup V] [Module 𝕜 V]
  {P} [AddTorsor V P] [PseudoEMetricSpace P]
  {V'} [AddCommGroup V'] [Module 𝕜 V']
  {P'} [AddTorsor V' P'] [EMetricSpace P']

theorem LipschitzWith.ethickness_image_le {f : P →ᵃ[𝕜] P'} {C} (hf : LipschitzWith C f)
    (s : Set P) : ethickness 𝕜 (f '' s) ≤ C • ethickness 𝕜 s := by
  intro n
  by_cases hC : C = 0
  · subst hC
    rw [hf.subsingleton.ethickness_eq_zero n]
    simp
  rw [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul,
    le_mul_ethickness_iff _ _ _ (ENNReal.coe_ne_zero.mpr hC) ENNReal.coe_ne_top]
  intro r A hA hs
  refine sInf_le ⟨A.map f, ?_, ?_⟩
  · exact AffineSubspace.map_direction f A ▸ Cardinal.lift_le_nat_iff.mp
      ((lift_rank_map_le f.linear A.direction).trans (Cardinal.lift_le_nat_iff.mpr hA))
  rintro - ⟨x, hx, rfl⟩
  apply hs at hx
  have hxA : infEDist x (A : Set P) ≤ _ := Metric.mem_cthickening_iff.mp hx
  rw [AffineSubspace.coe_map, Metric.mem_cthickening_iff]
  apply (hf.infEDist_le_mul_of_ne_zero hC _ _).trans
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.zero_le_coe, ENNReal.ofReal_mul,
    ENNReal.ofReal_coe_nnreal] at hxA ⊢
  apply mul_le_mul_right hxA
end

section
variable
  {V E}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace E] [NormedAddTorsor V E]

/-- The orthogonal projection onto a nonempty affine subspace shrinks `ethickness`. -/
theorem ethickness_image_orthogonalProjection_le
    {A : AffineSubspace ℝ E} [Nonempty A] [A.direction.HasOrthogonalProjection] (s : Set E) :
    ethickness ℝ ((orthogonalProjection A : E →ᵃ[ℝ] ↥A) '' s) ≤ ethickness ℝ s := by
  simpa using orthogonalProjection_lipschitzWith_one A |>.ethickness_image_le s

/-- The orthogonal projection onto a nonempty affine subspace shrinks `thickness` of bounded
sets. -/
theorem thickness_image_orthogonalProjection_le
    (A : AffineSubspace ℝ E) [Nonempty A] [A.direction.HasOrthogonalProjection]
    {s : Set E} (hs : Bornology.IsBounded s) (n : ℕ) :
    Metric.thickness ℝ ((orthogonalProjection A : E →ᵃ[ℝ] ↥A) '' s) n
      ≤ Metric.thickness ℝ s n := by
  have ht : Bornology.IsBounded ((orthogonalProjection A : E →ᵃ[ℝ] ↥A) '' s) :=
    (orthogonalProjection_lipschitzWith_one A).isBounded_image hs
  rw [← ENNReal.ofReal_le_ofReal_iff (thickness_nonneg s n),
    ← ethickness_thickness' ht n, ← ethickness_thickness' hs n]
  exact ethickness_image_orthogonalProjection_le s n

end
