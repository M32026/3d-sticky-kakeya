/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Thickness.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Affine thickness of a cthickening and of a ball

Two facts about `Metric.thickness` that need no volume and no tube: thickening a set grows every
affine thickness by at most the radius, and a closed ball of radius `r` has every affine thickness
of rank below the ambient dimension at least `r`.

They were extracted from `Kakeya.Tube.Fubini`, whose remaining content is the tube volume ratio
proper.
Keeping them at the thickness layer is what lets
`Kakeya.volume_cthickening_four_le` live in `Kakeya.Thickness.ConvexSpaceBody` rather than above
`Kakeya.Tube.Fubini`.
-/

@[expose] public section


open MeasureTheory ENNReal Metric EuclideanGeometry

namespace Metric

section ThickeningGrowth

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [PseudoMetricSpace P] [NormedAddTorsor V P]

/-- **Thickening growth.**  For a bounded nonempty `s ⊆ P` and `R ≥ 0`,
`thickness ℝ (cthickening R s) j ≤ thickness ℝ s j + R`.  The proof reduces to: if
`s ⊆ cthickening r A` then `cthickening R s ⊆ cthickening (r + R) A`, via Mathlib's
`cthickening_cthickening`. -/
lemma thickness_cthickening_le
    {s : Set P} (hs_bdd : Bornology.IsBounded s) (hs_ne : s.Nonempty)
    {R : ℝ} (hR : 0 ≤ R) (j : ℕ) :
    Metric.thickness ℝ (Metric.cthickening R s) j
      ≤ Metric.thickness ℝ s j + R := by
  have hS_ne : ({ r : ℝ | 0 ≤ r ∧ ∃ A : AffineSubspace ℝ P,
      Module.rank ℝ A.direction ≤ (j : Cardinal) ∧ s ⊆ cthickening r A }).Nonempty := by
    obtain ⟨x, _⟩ := hs_ne
    obtain ⟨r, hr_pos, hsub⟩ := hs_bdd.subset_closedBall_lt 0 x
    refine ⟨r, le_of_lt hr_pos, affineSpan ℝ {x}, ?_, ?_⟩
    · rw [direction_affineSpan, vectorSpan_singleton]
      simp
    · exact hsub.trans (closedBall_subset_cthickening (by simp) r)
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨r, hr_mem, hr_lt⟩ := Real.lt_sInf_add_pos hS_ne hε
  obtain ⟨hr_nn, A, hA_rank, hs_sub⟩ := hr_mem
  have hCthick : cthickening R s ⊆ cthickening (R + r) (A : Set P) :=
    (cthickening_subset_of_subset R hs_sub).trans
      (cthickening_cthickening_subset hR hr_nn (A : Set P))
  have h_thick_le : thickness ℝ (cthickening R s) j ≤ R + r :=
    thickness_le_of_cthickening (add_nonneg hR hr_nn) hA_rank hCthick
  have hr_lt' : r < thickness ℝ s j + ε := hr_lt
  linarith

end ThickeningGrowth

section BallThickness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Helper: in a finite-dimensional inner-product space `E`, if an
affine subspace `A` has rank-of-direction at most `k < finrank E`,
then there exists a unit vector orthogonal to `A.direction`. -/
lemma exists_unit_orthogonal_of_rank_lt
    (A : AffineSubspace ℝ E) {k : ℕ}
    (hA : Module.rank ℝ A.direction ≤ k) (hk : k < Module.finrank ℝ E) :
    ∃ v : E, v ∈ A.directionᗮ ∧ ‖v‖ = 1 := by
  have h_rank_lt : Module.finrank ℝ A.direction < Module.finrank ℝ E := by
    have h1 : (Module.finrank ℝ A.direction : Cardinal) ≤ (k : Cardinal) := by
      rw [Module.finrank_eq_rank]
      exact hA
    have h1' : Module.finrank ℝ A.direction ≤ k := by exact_mod_cast h1
    omega
  have h_orth_pos : 0 < Module.finrank ℝ (A.directionᗮ) := by
    have h_sum := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) A.direction
    omega
  obtain ⟨w, hw_mem, hw_ne⟩ : ∃ w : E, w ∈ A.directionᗮ ∧ w ≠ 0 := by
    have h_ne_bot : (A.directionᗮ : Submodule ℝ E) ≠ ⊥ := by
      intro h_bot
      rw [h_bot] at h_orth_pos
      simp at h_orth_pos
    obtain ⟨w, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_ne_bot
    exact ⟨w, hw.1, hw.2⟩
  refine ⟨(‖w‖)⁻¹ • w, ?_, ?_⟩
  · exact Submodule.smul_mem _ _ hw_mem
  · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw_ne)]

/-- Helper: for a finite-dimensional inner-product space, a closed ball
of radius `r ≥ 0` has thickness at least `r` at any rank strictly below
`finrank E`. -/
lemma thickness_closedBall_ge
    {x : E} {r : ℝ} (hr : 0 ≤ r) {k : ℕ} (hk : k < Module.finrank ℝ E) :
    r ≤ Metric.thickness ℝ (Metric.closedBall x r) k := by
  refine le_csInf ?_ ?_
  · refine ⟨r, hr, affineSpan ℝ {x}, ?_, ?_⟩
    · rw [direction_affineSpan, vectorSpan_singleton]
      simp
    · apply closedBall_subset_cthickening
      simp
  · rintro ε ⟨hε, A, hA, hsub⟩
    by_contra h_lt
    push Not at h_lt
    have hA_ne : (A : Set E).Nonempty := by
      by_contra h_empty
      have h_empty' : (A : Set E) = ∅ := Set.not_nonempty_iff_eq_empty.mp h_empty
      have h_cth_empty : Metric.cthickening ε (A : Set E) = ∅ := by
        rw [h_empty']; exact Metric.cthickening_empty ε
      rw [h_cth_empty, Set.subset_empty_iff] at hsub
      have h_ball_ne : (Metric.closedBall x r).Nonempty := ⟨x, Metric.mem_closedBall_self hr⟩
      rw [hsub] at h_ball_ne
      exact Set.not_nonempty_empty h_ball_ne
    haveI : Nonempty A := hA_ne.to_subtype
    haveI hopA : A.direction.HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace _
    set x' : A := orthogonalProjection A x with hx'_def
    have h_diff_orth : x - (x' : E) ∈ A.directionᗮ := by
      have h := vsub_orthogonalProjection_mem_direction_orthogonal A x
      simpa [vsub_eq_sub] using h
    rcases eq_or_ne (x - (x' : E)) 0 with hdiff | hdiff
    · obtain ⟨v, hv_mem, hv_norm⟩ := exists_unit_orthogonal_of_rank_lt A hA hk
      have hpoint_mem : x + r • v ∈ Metric.closedBall x r := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hsubst : x + r • v - x = r • v := by abel
        rw [hsubst, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hv_norm, mul_one]
      have h_in_cth : x + r • v ∈ Metric.cthickening ε A := hsub hpoint_mem
      have h_infDist_le : Metric.infDist (x + r • v) (A : Set E) ≤ ε := by
        rw [Metric.mem_cthickening_iff] at h_in_cth
        rw [Metric.infDist]
        rw [← ENNReal.toReal_ofReal hε]
        exact (ENNReal.toReal_le_toReal (Metric.infEDist_ne_top hA_ne)
          ENNReal.ofReal_ne_top).mpr h_in_cth
      have h_proj_eq : orthogonalProjection A (x + r • v) = x' := by
        rw [orthogonalProjection_eq_iff_mem]
        change (x + r • v) -ᵥ (x' : E) ∈ A.directionᗮ
        rw [vsub_eq_sub]
        have h_eq : x + r • v - (x' : E) = (x - (x' : E)) + r • v := by abel
        rw [h_eq, hdiff, zero_add]
        exact Submodule.smul_mem _ _ hv_mem
      have h_infDist_eq : Metric.infDist (x + r • v) (A : Set E) = r := by
        rw [← dist_orthogonalProjection_eq_infDist A (x + r • v), h_proj_eq,
            dist_eq_norm]
        have h_eq : x + r • v - (x' : E) = (x - (x' : E)) + r • v := by abel
        rw [h_eq, hdiff, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr,
            hv_norm, mul_one]
      linarith
    · set v : E := (‖x - (x' : E)‖)⁻¹ • (x - (x' : E)) with hv_def
      have hv_norm : ‖v‖ = 1 := by
        rw [hv_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_norm,
            inv_mul_cancel₀ (norm_ne_zero_iff.mpr hdiff)]
      have hv_mem : v ∈ A.directionᗮ :=
        Submodule.smul_mem _ _ h_diff_orth
      have hpoint_mem : x + r • v ∈ Metric.closedBall x r := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hsubst : x + r • v - x = r • v := by abel
        rw [hsubst, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hv_norm, mul_one]
      have h_in_cth : x + r • v ∈ Metric.cthickening ε A := hsub hpoint_mem
      have h_infDist_le : Metric.infDist (x + r • v) (A : Set E) ≤ ε := by
        rw [Metric.mem_cthickening_iff] at h_in_cth
        rw [Metric.infDist]
        rw [← ENNReal.toReal_ofReal hε]
        exact (ENNReal.toReal_le_toReal (Metric.infEDist_ne_top hA_ne)
          ENNReal.ofReal_ne_top).mpr h_in_cth
      have h_sum_orth : (x - (x' : E)) + r • v ∈ A.directionᗮ :=
        Submodule.add_mem _ h_diff_orth (Submodule.smul_mem _ _ hv_mem)
      have h_proj_eq : orthogonalProjection A (x + r • v) = x' := by
        rw [orthogonalProjection_eq_iff_mem]
        change (x + r • v) -ᵥ (x' : E) ∈ A.directionᗮ
        rw [vsub_eq_sub]
        have h_eq : x + r • v - (x' : E) = (x - (x' : E)) + r • v := by abel
        rw [h_eq]
        exact h_sum_orth
      have h_v_eq : r • v = (r / ‖x - (x' : E)‖) • (x - (x' : E)) := by
        rw [hv_def, smul_smul, div_eq_mul_inv]
      have h_combine : (x - (x' : E)) + r • v
          = (1 + r / ‖x - (x' : E)‖) • (x - (x' : E)) := by
        rw [h_v_eq, add_smul, one_smul]
      have h_norm_pos : 0 < ‖x - (x' : E)‖ := norm_pos_iff.mpr hdiff
      have h_coeff_nn : 0 ≤ 1 + r / ‖x - (x' : E)‖ := by
        have : 0 ≤ r / ‖x - (x' : E)‖ := div_nonneg hr h_norm_pos.le
        linarith
      have h_norm_eq : ‖(x - (x' : E)) + r • v‖ = ‖x - (x' : E)‖ + r := by
        rw [h_combine, norm_smul, Real.norm_eq_abs, abs_of_nonneg h_coeff_nn]
        field_simp
      have h_infDist_eq : Metric.infDist (x + r • v) (A : Set E)
          = ‖x - (x' : E)‖ + r := by
        rw [← dist_orthogonalProjection_eq_infDist A (x + r • v), h_proj_eq,
            dist_eq_norm]
        have h_eq : x + r • v - (x' : E) = (x - (x' : E)) + r • v := by abel
        rw [h_eq, h_norm_eq]
      linarith

end BallThickness

end Metric
