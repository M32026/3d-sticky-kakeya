/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Geometry

/-!
# Bridge ingredients for GWZ Lemma 6.4

Two small, self-contained steps that the reduction bridge
`Kakeya.plankReductionForFrostmanEstimate` needs and that no existing lemma supplies.

* `Prism3D.abs_inner_basis_zero_le_of_angle_le` turns the *angle* bound recorded by
  `Plank.inSlabFamilyC` into the *coordinate* bound demanded by the `tangency` field of
  `Plank.SlabFibreGeometry`. Both express "the short normal of the prism is nearly parallel to the
  short normal of the slab", but the structure asks for it in the Parseval form
  `|⟪P.basis 0, S.basis j⟫| ≤ C·θ` for the two long slab directions `j ≠ 0`.

* `Plank.exists_slabAssignment_of_mem_inSlabFamilyC` repackages a bare slab map together with the
  controlled slab-membership clause — which is the shape in which
  `Kakeya.redPlankTube_finalAssembly` returns its slab data — as a genuine
  `Plank.SlabAssignment`. The used-slab set is then forced to be the image of the active ensemble,
  which is what makes every used slab carry a nonempty fibre.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal Real Classical

noncomputable section

namespace Prism3D

/-- **From a plane-angle bound to coordinate bounds.** `Prism3D.angle P S = arccos |⟪n_P, n_S⟫|`
records that the unit normals of `P` and `S` are within angle `c`. Since `S.basis` is an orthonormal
basis, Parseval turns this into a bound on the components of `n_P` along the two *long* directions
of `S`: each is at most `sin c ≤ c`. This is the `tangency` field of `Plank.SlabFibreGeometry`. -/
theorem abs_inner_basis_zero_le_of_angle_le {a₁ b₁ c₁ a₂ b₂ c₂ : ℝ≥0}
    {h₁ : a₁ ≤ b₁} {h₁' : b₁ ≤ c₁} {h₂ : a₂ ≤ b₂} {h₂' : b₂ ≤ c₂}
    (P : Prism3D a₁ b₁ c₁ h₁ h₁') (S : Prism3D a₂ b₂ c₂ h₂ h₂')
    {c : ℝ} (hc : 0 ≤ c) (hangle : Prism3D.angle P S ≤ c) {j : Fin 3} (hj : j ≠ 0) :
    |inner ℝ (P.basis 0) (S.basis j)| ≤ c := by
  by_cases hc1 : 1 ≤ c
  · exact (abs_inner_basis_le_one P S 0 j).trans hc1
  · have hc_lt_1 : c < 1 := lt_of_not_ge hc1
    set t : ℝ := |inner ℝ (P.basis 0) (S.basis 0)|
    set u : ℝ := inner ℝ (P.basis 0) (S.basis j)
    have ht_nonneg : 0 ≤ t := by simp [t]
    have ht_le_1 : t ≤ 1 := by
      simpa [t] using abs_inner_basis_le_one P S 0 0
    have ht_ge_neg_one : -1 ≤ t := by linarith
    have hc_le_pi : c ≤ Real.pi := by linarith [Real.two_le_pi, hc_lt_1]
    have hc_le_pi2 : c ≤ Real.pi / 2 := by linarith [Real.two_le_pi, hc_lt_1]
    have hparseval : ∑ k : Fin 3, (inner ℝ (P.basis 0) (S.basis k)) ^ 2 = 1 := by
      rw [OrthonormalBasis.sum_sq_inner_left S.basis (P.basis 0)]
      rw [P.basis.norm_eq_one 0, one_pow]
    have h2sum : (inner ℝ (P.basis 0) (S.basis 0)) ^ 2 + u ^ 2 ≤ 1 := by
      have hu2 : u ^ 2 = (inner ℝ (P.basis 0) (S.basis j)) ^ 2 := by dsimp [u]
      rw [hu2]
      fin_cases j <;> simp
      · exfalso
        exact hj rfl
      · have hfull : (inner ℝ (P.basis 0) (S.basis 0)) ^ 2 +
            (inner ℝ (P.basis 0) (S.basis 1)) ^ 2 + (inner ℝ (P.basis 0) (S.basis 2)) ^ 2 = 1 := by
          simpa [Fin.sum_univ_three] using hparseval
        nlinarith [sq_nonneg (inner ℝ (P.basis 0) (S.basis 2))]
      · have hfull : (inner ℝ (P.basis 0) (S.basis 0)) ^ 2 +
            (inner ℝ (P.basis 0) (S.basis 1)) ^ 2 + (inner ℝ (P.basis 0) (S.basis 2)) ^ 2 = 1 := by
          simpa [Fin.sum_univ_three] using hparseval
        nlinarith [sq_nonneg (inner ℝ (P.basis 0) (S.basis 1))]
    have hu_aux : u ^ 2 ≤ 1 - t ^ 2 := by
      have ht2 : t ^ 2 = (inner ℝ (P.basis 0) (S.basis 0)) ^ 2 := by
        dsimp [t]
        rw [sq_abs]
      have hu2 : u ^ 2 = (inner ℝ (P.basis 0) (S.basis j)) ^ 2 := by dsimp [u]
      nlinarith
    have harccos_le_c : Real.arccos t ≤ c := by
      dsimp [t]
      simpa [Prism3D.angle_def] using hangle
    have hcos_le_t : Real.cos c ≤ t := by
      have hmono : Real.cos c ≤ Real.cos (Real.arccos t) := by
        exact Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _) hc_le_pi harccos_le_c
      simpa [Real.cos_arccos ht_ge_neg_one ht_le_1] using hmono
    have hcosc_nonneg : 0 ≤ Real.cos c := by
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hc_le_pi2⟩
    have hcos2_le_t2 : (Real.cos c) ^ 2 ≤ t ^ 2 := by
      rw [sq_le_sq]
      rw [abs_of_nonneg hcosc_nonneg, abs_of_nonneg ht_nonneg]
      exact hcos_le_t
    have hu2_le_sin2 : u ^ 2 ≤ (Real.sin c) ^ 2 := by
      nlinarith [hu_aux, hcos2_le_t2, Real.sin_sq_add_cos_sq c]
    have hsinc_nonneg : 0 ≤ Real.sin c := by
      exact Real.sin_nonneg_of_nonneg_of_le_pi hc hc_le_pi
    have hu_le : |u| ≤ c := by
      have h1 : |u| ≤ |Real.sin c| := (sq_le_sq.mp hu2_le_sin2)
      have h2 : |Real.sin c| = Real.sin c := abs_of_nonneg hsinc_nonneg
      rw [h2] at h1
      exact h1.trans (Real.sin_le hc)
    simpa [u] using hu_le

/-- **From coordinate bounds back to a plane-angle bound.** The converse of
`Prism3D.abs_inner_basis_zero_le_of_angle_le`, and the direction the slab-to-tube normalisation
needs: `Plank.SlabFibreGeometry.tangency` records the two Parseval components
`|⟪P.basis 0, S.basis j⟫| ≤ c` for `j ≠ 0`, while `Plank.image_carrier_subset_slabTube` consumes the
plane angle `Prism3D.angle P S = arccos |⟪P.basis 0, S.basis 0⟫|`.

The loss is the fixed factor `3`. Parseval gives `⟪n_P, n_S⟫² ≥ 1 - 2c²`, so it suffices that
`cos (3c) ≤ √(1 - 2c²)`, i.e. that `2c² ≤ sin² (3c)`; Jordan's inequality `(2/π)·x ≤ sin x` on
`[0, π/2]` gives `sin (3c) ≥ (6/π)·c` and `(6/π)² > 2`. The angle is at most `π/2` outright
(it is an `arccos` of an absolute value), so the range `c ≥ π/6` is trivial. -/
theorem angle_le_of_abs_inner_basis_zero_le {a₁ b₁ c₁ a₂ b₂ c₂ : ℝ≥0}
    {h₁ : a₁ ≤ b₁} {h₁' : b₁ ≤ c₁} {h₂ : a₂ ≤ b₂} {h₂' : b₂ ≤ c₂}
    (P : Prism3D a₁ b₁ c₁ h₁ h₁') (S : Prism3D a₂ b₂ c₂ h₂ h₂')
    {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (P.basis 0) (S.basis j)| ≤ c) :
    Prism3D.angle P S ≤ 3 * c := by
  set t : ℝ := |inner ℝ (P.basis 0) (S.basis 0)| with ht_def
  have ht0 : 0 ≤ t := abs_nonneg _
  have ht1 : t ≤ 1 := Prism3D.abs_inner_basis_le_one P S 0 0
  have hangle : Prism3D.angle P S = Real.arccos t := by
    simpa [ht_def] using (Prism3D.angle_def ..)
  by_cases hbig : Real.pi / 6 ≤ c
  · -- trivial branch: the angle is an `arccos` of a nonnegative number, so ≤ π/2 ≤ 3c
    have : Real.arccos t ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr ht0
    rw [hangle]; linarith
  · -- main branch
    have hsmall : c < Real.pi / 6 := lt_of_not_ge hbig
    have h3c : 3 * c ≤ Real.pi / 2 := by linarith
    -- Parseval
    have hpars : (inner ℝ (P.basis 0) (S.basis 0)) ^ 2 + (inner ℝ (P.basis 0) (S.basis 1)) ^ 2
        + (inner ℝ (P.basis 0) (S.basis 2)) ^ 2 = 1 := by
      have := OrthonormalBasis.sum_sq_inner_left S.basis (P.basis 0)
      simpa [Fin.sum_univ_three, P.basis.norm_eq_one 0] using this
    have h1 := h 1 (by decide)
    have h2 := h 2 (by decide)
    have hts : 1 - 2 * c ^ 2 ≤ t ^ 2 := by
      have e1 : (inner ℝ (P.basis 0) (S.basis 1)) ^ 2 ≤ c ^ 2 := by
        nlinarith [abs_nonneg (inner ℝ (P.basis 0) (S.basis 1)),
          sq_abs (inner ℝ (P.basis 0) (S.basis 1))]
      have e2 : (inner ℝ (P.basis 0) (S.basis 2)) ^ 2 ≤ c ^ 2 := by
        nlinarith [abs_nonneg (inner ℝ (P.basis 0) (S.basis 2)),
          sq_abs (inner ℝ (P.basis 0) (S.basis 2))]
      have : t ^ 2 = (inner ℝ (P.basis 0) (S.basis 0)) ^ 2 := by rw [ht_def, sq_abs]
      nlinarith
    -- Jordan: 2/π * (3c) ≤ sin (3c)
    have hjordan : 2 / Real.pi * (3 * c) ≤ Real.sin (3 * c) :=
      Real.mul_le_sin (by linarith) h3c
    have hsin_nonneg : 0 ≤ Real.sin (3 * c) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
    have hcross : 6 * c ≤ Real.pi * Real.sin (3 * c) := by
      have h6p : 6 * c / Real.pi ≤ Real.sin (3 * c) := by
        rwa [show (2 / Real.pi) * (3 * c) = 6 * c / Real.pi by ring] at hjordan
      simpa [mul_comm] using (div_le_iff₀ Real.pi_pos).mp h6p
    have hpi_sin_le : Real.pi * Real.sin (3 * c) ≤ 4 * Real.sin (3 * c) := by
      exact mul_le_mul_of_nonneg_right Real.pi_le_four hsin_nonneg
    have hsin_ge : 3 * c ≤ 2 * Real.sin (3 * c) := by
      nlinarith [hcross, hpi_sin_le]
    have hsin2 : 2 * c ^ 2 ≤ Real.sin (3 * c) ^ 2 := by
      have hsq : (3 * c) ^ 2 ≤ (2 * Real.sin (3 * c)) ^ 2 := by
        rw [sq_le_sq]
        rw [abs_of_nonneg (mul_nonneg (by norm_num) hc),
          abs_of_nonneg (mul_nonneg (by norm_num) hsin_nonneg)]
        exact hsin_ge
      nlinarith [hsq, sq_nonneg c]
    have hcos_sq : Real.cos (3 * c) ^ 2 ≤ t ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq (3 * c)]
    have hcos_nonneg : 0 ≤ Real.cos (3 * c) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h3c⟩
    have hcos_le : Real.cos (3 * c) ≤ t := by nlinarith
    calc Prism3D.angle P S = Real.arccos t := hangle
      _ ≤ Real.arccos (Real.cos (3 * c)) := Real.arccos_le_arccos hcos_le
      _ = 3 * c := Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])

end Prism3D

namespace Plank

variable {ι : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}

/-- **A bare slab map plus controlled membership is a `Plank.SlabAssignment`.** This is the shape in
which `Kakeya.redPlankTube_finalAssembly` returns its slab data, and the shape the Section 6
interfaces (`Plank.frostmanThickenedSlabFibre`, `Plank.normaliseSlabFamilyToTubes`) consume. Taking
`used` to be the image of the family under `slabOf ∘ repr` is what forces every used slab to carry a
nonempty fibre of the active ensemble. -/
theorem exists_slabAssignment_of_mem_inSlabFamilyC {s : Finset ι} {V : ι → Plank a b hab hb1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} {repr : ι → ThickenedPlank θ b hθ1 hb1} (Cset Cang : ℝ≥0)
    (slabOf : ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1)
    (hmem : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V (slabOf (repr i))) :
    ∃ SA : SlabAssignment s V θ hθ1 repr Cset Cang,
      SA.slabOf = slabOf ∧ SA.used = s.image (fun i => slabOf (repr i)) := by
  refine ⟨{
    slabOf := slabOf
    used := s.image (fun i => slabOf (repr i))
    slabOf_mem := fun i hi => Finset.mem_image_of_mem _ hi
    mem_inSlabFamily := hmem }, rfl, rfl⟩

end Plank

end

end
