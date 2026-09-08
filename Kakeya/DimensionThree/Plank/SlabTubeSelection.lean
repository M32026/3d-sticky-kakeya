/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabFibreFrame

/-!
# The anisotropic ED-packing bridge for GWZ Section 6

The missing geometric input of `Plank.normaliseSlabFamilyToTubes`: the enclosing `b/8`-tube family
of one slab fibre is essentially distinct **up to a bounded multiplicity** `MED` depending only on
the slab-fibre loss constant `Cfib` (through the absolute constants of
`Kakeya.exists_notED_tube_axis_bound` and `Plank.fibreTubeConst`), and in particular *not* on `a`,
`b`, `θ`, the slab, the cardinality of the fibre, or the configuration.

## The chain

1. `Kakeya.exists_notED_tube_axis_bound`: two `δ`-tubes that are not essentially distinct have
   projective direction distance and transverse midpoint offset `≲ δ`. Here `δ = b / 8`.
2. `Plank.exists_axis_scalar` / `Plank.exists_center_scalar`: transport that control back through
   the normalising map `Slab.normalizeScaled S κ`, producing a comparison scalar `t` with
   `‖L (u₂ - t • u₂')‖ ≲ κ b` and a scalar `r` with `‖L (Δ - r • u₂')‖ ≲ b`.
3. `Plank.abs_inner_basis_le_of_norm_linear_le`: the linear part is diagonal in `S.basis` with
   entries `(κ/θ, κ, κ)`, so those bounds become the *anisotropic profile* `(≲ θ b, ≲ b, ≲ b)`.
4. `Plank.frame_confined_of_slab_profile` / `Plank.center_confined_of_slab_profile`: the profile
   plus tangency gives the symmetric anisotropic pose confinement at the weights `(θ b, b, 1)`.
5. `Plank.card_le_of_anisotropicConfined_pairwiseED`: pairwise essentially distinct prisms with a
   confined pose number at most `(768 R² + 2) ^ 12`.

Step 5 is where the *cores'* essential distinctness — the only thing the normalisation preserves —
is consumed. Tube-level pairwise essential distinctness is never assumed anywhere, so the argument
is not circular; see the module docstring of `Kakeya.DimensionThree.Plank.SlabTubeEssentialDistinctness`.
-/

@[expose] public section

open MeasureTheory Kakeya
open scoped NNReal Real Classical

noncomputable section

namespace Plank

variable {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1}
  {fibre : Finset (ThickenedPlank θ b hθ1 hb1)}
  {Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))}
  {S : Slab θ hθ1} {Cfib : ℝ≥0}

/-- The slab normal makes a small inner product with both long axes of a fibre prism: the plane
angle bound `Plank.SlabFibreGeometry.angle_le` fed into `Plank.abs_inner_slabNormal_basis_le`. -/
theorem SlabFibreGeometry.abs_inner_slabNormal_le (h : SlabFibreGeometry fibre Yθ S Cfib)
    {Q : ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ fibre) {j : Fin 3} (hj : j ≠ 0) :
    |inner ℝ (S.basis 0) (Q.basis j)| ≤ 3 * (Cfib : ℝ) * (θ : ℝ) := by
  simpa [NNReal.coe_mul] using abs_inner_slabNormal_basis_le Q S (h.angle_le hQ) hj

/-- Two-sided control of the normalised length of a fibre prism's long axis: it is between `κ` and
`κ (1 + 3 Cfib)`. The lower bound is universal (`Plank.le_norm_normalizeScaled_linear`); the upper
bound uses tangency through `Plank.norm_normalizeScaled_linear_le_of_inner_sq_le`. -/
theorem SlabFibreGeometry.norm_linear_longAxis_bounds (h : SlabFibreGeometry fibre Yθ S Cfib)
    (hθ0 : 0 < θ) {κ : ℝ≥0} (hκ : 0 < κ) {Q : ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ fibre) :
    (κ : ℝ) ≤ ‖(Slab.normalizeScaled S κ hθ0 hκ).linear (Q.basis 2)‖ ∧
      ‖(Slab.normalizeScaled S κ hθ0 hκ).linear (Q.basis 2)‖ ≤ (κ : ℝ) * (1 + 3 * (Cfib : ℝ)) := by
  have hu : ‖Q.basis 2‖ = 1 := Q.basis.norm_eq_one 2
  have hC : 0 ≤ 3 * (Cfib : ℝ) := by positivity
  have hinner : inner ℝ (S.basis 0) (Q.basis 2) ^ 2 ≤ (3 * (Cfib : ℝ)) ^ 2 * (θ : ℝ) ^ 2 := by
    have h : |inner ℝ (S.basis 0) (Q.basis 2)| ≤ 3 * (Cfib : ℝ) * (θ : ℝ) :=
      SlabFibreGeometry.abs_inner_slabNormal_le h hQ (by decide)
    have ht0 : 0 ≤ 3 * (Cfib : ℝ) * (θ : ℝ) := by positivity
    have hsq : inner ℝ (S.basis 0) (Q.basis 2) ^ 2 ≤ (3 * (Cfib : ℝ) * (θ : ℝ)) ^ 2 := by
      exact (sq_le_sq.mpr (by simpa [abs_of_nonneg ht0] using h))
    simpa [mul_pow] using hsq
  constructor
  · exact Plank.le_norm_normalizeScaled_linear S κ hθ0 hκ hu
  · exact Plank.norm_normalizeScaled_linear_le_of_inner_sq_le S κ hθ0 hκ hu hC hinner

/-- The centres of two fibre prisms are at distance at most `8 Cfib`, since each prism — hence its
centre — lies in the controlled ball of radius `4 Cfib`. -/
theorem SlabFibreGeometry.norm_center_sub_le (h : SlabFibreGeometry fibre Yθ S Cfib)
    (hCfib : 1 ≤ Cfib) {Q Q₀ : ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ fibre) (hQ₀ : Q₀ ∈ fibre) :
    ‖(Q.center -ᵥ Q₀.center : EuclideanSpace ℝ (Fin 3))‖ ≤ 8 * (Cfib : ℝ) := by
  have hQball : Q.center ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (4 * (Cfib : ℝ)) :=
    SlabFibreGeometry.prism_subset_controlledBall h hCfib hQ
      (PrismNDim.center_mem_carrier Q.toPrismNDim)
  have hQ₀ball : Q₀.center ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (4 * (Cfib : ℝ)) :=
    SlabFibreGeometry.prism_subset_controlledBall h hCfib hQ₀
      (PrismNDim.center_mem_carrier Q₀.toPrismNDim)
  rw [← dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 3))]
  calc
    dist Q.center Q₀.center ≤ dist Q.center 0 + dist 0 Q₀.center :=
      dist_triangle Q.center 0 Q₀.center
    _ ≤ 4 * (Cfib : ℝ) + 4 * (Cfib : ℝ) := by
      gcongr
      · exact hQball
      · rw [dist_comm]
        exact hQ₀ball
    _ = 8 * (Cfib : ℝ) := by ring

/-- **The axis profile.** If the enclosing tubes of two fibre prisms are not essentially distinct
then, for an absolute `A` depending only on `Cfib`, the long axis of `Q` differs from a nonzero
multiple `t` of the long axis of `Q₀` by a vector whose `S`-frame components are bounded by the
anisotropic profile `(A θ b, A b, A b)`, and `|t⁻¹| ≤ 1 + 3 Cfib`.

This is `Kakeya.exists_notED_tube_axis_bound` (direction half) transported through
`Plank.exists_axis_scalar` and read off in the `S` frame by
`Plank.abs_inner_basis_le_of_norm_linear_le`. The two-sided bound
`Plank.SlabFibreGeometry.norm_linear_longAxis_bounds` on `‖L u₂‖` is what makes `A` and the bound
on `|t⁻¹|` absolute. -/
theorem exists_axisProfile_of_notED_slabTube (Cfib : ℝ≥0) (hCfib : 1 ≤ Cfib) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1} (hθ0 : 0 < θ) (hb0 : 0 < b)
        (fibre : Finset (ThickenedPlank θ b hθ1 hb1))
        (Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (S : Slab θ hθ1),
        SlabFibreGeometry fibre Yθ S Cfib →
        ∀ {Q Q₀ : ThickenedPlank θ b hθ1 hb1}, Q ∈ fibre → Q₀ ∈ fibre →
        ¬ IsEssentiallyDistinct
            ((Q.slabTube S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib)).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))
            ((Q₀.slabTube S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib)).carrier :
              Set (EuclideanSpace ℝ (Fin 3))) →
        ∃ t : ℝ, t ≠ 0 ∧ |t⁻¹| ≤ 1 + 3 * (Cfib : ℝ) ∧
          |inner ℝ (S.basis 0) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (θ : ℝ) * (b : ℝ) ∧
          |inner ℝ (S.basis 1) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (b : ℝ) ∧
          |inner ℝ (S.basis 2) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (b : ℝ) := by
  obtain ⟨Ctub, hCtub0, hCtub⟩ := Kakeya.exists_notED_tube_axis_bound
  let A : ℝ := (1 + 3 * (Cfib : ℝ)) * Ctub / 8
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro θ b hθ1 hb1 hθ0 hb0 fibre Yθ S h Q Q₀ hQ hQ₀ hnotED
  let L : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (Slab.normalizeScaled S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib)).linear
  let u : EuclideanSpace ℝ (Fin 3) := Q.basis 2
  let u₀ : EuclideanSpace ℝ (Fin 3) := Q₀.basis 2
  have hκ : 0 < fibreTubeConst Cfib := fibreTubeConst_pos Cfib
  have hκR : 0 < (fibreTubeConst Cfib : ℝ) := NNReal.coe_pos.mpr hκ
  have hδ0 : (0 : ℝ≥0) < b / 8 := by positivity
  have hδ1 : (b / 8 : ℝ≥0) ≤ 1 := by
    exact (div_le_one (by norm_num : (0 : ℝ≥0) < 8)).mpr (le_trans hb1 (by norm_num))
  obtain ⟨hdir, _⟩ := hCtub hδ0 hδ1 (Q.slabTube S (fibreTubeConst Cfib) hθ0 hκ)
    (Q₀.slabTube S (fibreTubeConst Cfib) hθ0 hκ) hnotED
  rw [slabTube_direction, slabTube_direction] at hdir
  obtain ⟨t, ht_eq, ht_le⟩ := exists_axis_scalar Q Q₀ S (fibreTubeConst Cfib) hθ0 hκ hdir
  obtain ⟨hlow, hhigh⟩ := h.norm_linear_longAxis_bounds hθ0 hκ hQ
  obtain ⟨hlow₀, hhigh₀⟩ := h.norm_linear_longAxis_bounds hθ0 hκ hQ₀
  have hlow' : (fibreTubeConst Cfib : ℝ) ≤ ‖L u‖ := by
    simpa [L, u] using hlow
  have hhigh' : ‖L u‖ ≤ (fibreTubeConst Cfib : ℝ) * (1 + 3 * (Cfib : ℝ)) := by
    simpa [L, u] using hhigh
  have hlow₀' : (fibreTubeConst Cfib : ℝ) ≤ ‖L u₀‖ := by
    simpa [L, u₀] using hlow₀
  have hhigh₀' : ‖L u₀‖ ≤ (fibreTubeConst Cfib : ℝ) * (1 + 3 * (Cfib : ℝ)) := by
    simpa [L, u₀] using hhigh₀
  have hu_pos : 0 < ‖L u‖ := lt_of_lt_of_le hκR hlow'
  have hu₀_pos : 0 < ‖L u₀‖ := lt_of_lt_of_le hκR hlow₀'
  have ht_eq' : |t| * ‖L u₀‖ = ‖L u‖ := by
    simpa [L, u, u₀] using ht_eq
  have hu_ne : ‖L u‖ ≠ 0 := ne_of_gt hu_pos
  have hu₀_ne : ‖L u₀‖ ≠ 0 := ne_of_gt hu₀_pos
  have ht0 : t ≠ 0 := by
    intro ht_zero
    have hzero : (0 : ℝ) = ‖L u‖ := by
      calc
        0 = |t| * ‖L u₀‖ := by simp [ht_zero]
        _ = ‖L u‖ := ht_eq'
    linarith
  have ht_abs : |t| = ‖L u‖ / ‖L u₀‖ := by
    field_simp [hu₀_ne]
    exact ht_eq'
  have ht_inv : |t|⁻¹ = ‖L u₀‖ / ‖L u‖ := by
    rw [ht_abs]
    field_simp [hu_ne, hu₀_ne]
  have hprod : ‖L u₀‖ * (fibreTubeConst Cfib : ℝ)
      ≤ ((fibreTubeConst Cfib : ℝ) * (1 + 3 * (Cfib : ℝ))) * ‖L u‖ := by
    nlinarith [hhigh₀', hlow', hu₀_pos, hu_pos, hκR]
  have hdiv : ‖L u₀‖ / ‖L u‖
      ≤ ((fibreTubeConst Cfib : ℝ) * (1 + 3 * (Cfib : ℝ))) / (fibreTubeConst Cfib : ℝ) := by
    field_simp [hu_pos.ne', hκR.ne']
    nlinarith [hprod]
  have hsimpl : ((fibreTubeConst Cfib : ℝ) * (1 + 3 * (Cfib : ℝ))) / (fibreTubeConst Cfib : ℝ)
      = 1 + 3 * (Cfib : ℝ) := by
    field_simp [hκR.ne']
  have hinv : |t⁻¹| ≤ 1 + 3 * (Cfib : ℝ) := by
    rw [abs_inv, ht_inv]
    exact hdiv.trans_eq hsimpl
  let M : ℝ := ((fibreTubeConst Cfib : ℝ) * (1 + 3 * (Cfib : ℝ)))
    * (Ctub * ((b / 8 : ℝ≥0) : ℝ))
  have hM : ‖L (u - t • u₀)‖ ≤ M := by
    calc
      ‖L (u - t • u₀)‖ ≤ ‖L u‖ * (Ctub * ((b / 8 : ℝ≥0) : ℝ)) := by
          simpa [L, u, u₀] using ht_le
      _ ≤ M := by
        dsimp [M]
        gcongr
  obtain ⟨z0, z1, z2⟩ := abs_inner_basis_le_of_norm_linear_le S (fibreTubeConst Cfib) hθ0 hκ hM
  refine ⟨t, ht0, hinv, ?_, ?_, ?_⟩
  · calc
      |inner ℝ (S.basis 0) (Q.basis 2 - t • Q₀.basis 2)|
          ≤ M * (θ : ℝ) / (fibreTubeConst Cfib : ℝ) := by
            simpa [u, u₀] using z0
      _ = A * (θ : ℝ) * (b : ℝ) := by
        dsimp [M, A]
        field_simp [hκR.ne']
  · calc
      |inner ℝ (S.basis 1) (Q.basis 2 - t • Q₀.basis 2)|
          ≤ M / (fibreTubeConst Cfib : ℝ) := by
            simpa [u, u₀] using z1
      _ = A * (b : ℝ) := by
        dsimp [M, A]
        field_simp [hκR.ne']
  · calc
      |inner ℝ (S.basis 2) (Q.basis 2 - t • Q₀.basis 2)|
          ≤ M / (fibreTubeConst Cfib : ℝ) := by
            simpa [u, u₀] using z2
      _ = A * (b : ℝ) := by
        dsimp [M, A]
        field_simp [hκR.ne']

/-- **The centre profile.** The positional half of `Kakeya.exists_notED_tube_axis_bound`,
transported through `Plank.exists_center_scalar` and read off in the `S` frame: the centre offset
of the two prisms differs from a multiple of `Q₀`'s long axis by a vector with the anisotropic
profile `(B θ b, B b, B b)`, for an absolute `B` depending only on `Cfib`. -/
theorem exists_centerProfile_of_notED_slabTube (Cfib : ℝ≥0) (hCfib : 1 ≤ Cfib) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1} (hθ0 : 0 < θ) (hb0 : 0 < b)
        (fibre : Finset (ThickenedPlank θ b hθ1 hb1))
        (Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (S : Slab θ hθ1),
        SlabFibreGeometry fibre Yθ S Cfib →
        ∀ {Q Q₀ : ThickenedPlank θ b hθ1 hb1}, Q ∈ fibre → Q₀ ∈ fibre →
        ¬ IsEssentiallyDistinct
            ((Q.slabTube S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib)).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))
            ((Q₀.slabTube S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib)).carrier :
              Set (EuclideanSpace ℝ (Fin 3))) →
        ∃ r : ℝ,
          |inner ℝ (S.basis 0)
              ((Q.center -ᵥ Q₀.center : EuclideanSpace ℝ (Fin 3)) - r • Q₀.basis 2)|
            ≤ B * (θ : ℝ) * (b : ℝ) ∧
          |inner ℝ (S.basis 1)
              ((Q.center -ᵥ Q₀.center : EuclideanSpace ℝ (Fin 3)) - r • Q₀.basis 2)|
            ≤ B * (b : ℝ) ∧
          |inner ℝ (S.basis 2)
              ((Q.center -ᵥ Q₀.center : EuclideanSpace ℝ (Fin 3)) - r • Q₀.basis 2)|
            ≤ B * (b : ℝ) := by
  obtain ⟨Ctub, hCtub0, hCtub⟩ := Kakeya.exists_notED_tube_axis_bound
  refine ⟨Ctub / (8 * ((fibreTubeConst Cfib : ℝ≥0) : ℝ)), by positivity, ?_⟩
  intro θ b hθ1 hb1 hθ0 hb0 fibre Yθ S h Q Q₀ hQ hQ₀ hnotED
  have hκ : 0 < fibreTubeConst Cfib := fibreTubeConst_pos Cfib
  have hδ0 : (0 : ℝ≥0) < b / 8 := by positivity
  have hδ1 : b / 8 ≤ 1 := by
    exact (div_le_one (by norm_num : (0 : ℝ≥0) < 8)).mpr (le_trans hb1 (by norm_num))
  obtain ⟨_, hpos⟩ := hCtub hδ0 hδ1 (Q.slabTube S (fibreTubeConst Cfib) hθ0 hκ)
    (Q₀.slabTube S (fibreTubeConst Cfib) hθ0 hκ) hnotED
  obtain ⟨r, hr⟩ := exists_center_scalar Q Q₀ S (fibreTubeConst Cfib) hθ0 hκ hpos
  obtain ⟨z0, z1, z2⟩ := abs_inner_basis_le_of_norm_linear_le S (fibreTubeConst Cfib) hθ0 hκ hr
  refine ⟨r, ?_, ?_, ?_⟩
  · calc
      |inner ℝ (S.basis 0) ((Q.center -ᵥ Q₀.center : EuclideanSpace ℝ (Fin 3)) - r • Q₀.basis 2)|
          ≤ Ctub * ((b / 8 : ℝ≥0) : ℝ) * (θ : ℝ) / (fibreTubeConst Cfib : ℝ) := z0
      _ = Ctub / (8 * (fibreTubeConst Cfib : ℝ)) * (θ : ℝ) * (b : ℝ) := by
          rw [NNReal.coe_div]
          norm_num
          field_simp [show (fibreTubeConst Cfib : ℝ) ≠ 0 from ne_of_gt hκ]
  · calc
      |inner ℝ (S.basis 1) ((Q.center -ᵥ Q₀.center : EuclideanSpace ℝ (Fin 3)) - r • Q₀.basis 2)|
          ≤ Ctub * ((b / 8 : ℝ≥0) : ℝ) / (fibreTubeConst Cfib : ℝ) := z1
      _ = Ctub / (8 * (fibreTubeConst Cfib : ℝ)) * (b : ℝ) := by
          rw [NNReal.coe_div]
          norm_num
          field_simp [show (fibreTubeConst Cfib : ℝ) ≠ 0 from ne_of_gt hκ]
  · calc
      |inner ℝ (S.basis 2) ((Q.center -ᵥ Q₀.center : EuclideanSpace ℝ (Fin 3)) - r • Q₀.basis 2)|
          ≤ Ctub * ((b / 8 : ℝ≥0) : ℝ) / (fibreTubeConst Cfib : ℝ) := z2
      _ = Ctub / (8 * (fibreTubeConst Cfib : ℝ)) * (b : ℝ) := by
          rw [NNReal.coe_div]
          norm_num
          field_simp [show (fibreTubeConst Cfib : ℝ) ≠ 0 from ne_of_gt hκ]

/-- **Failure of tube essential distinctness confines the pose of the two prisms.**

For a fixed slab-fibre loss `Cfib ≥ 1` there is an absolute `R ≥ 1` such that, whenever two prisms
of a slab fibre have enclosing normalised tubes that are *not* essentially distinct, their frames
and centres are `R`-confined against each other in the symmetric anisotropic sense at the weights
`(θ b, b, 1)` — exactly the hypotheses of
`Plank.card_le_of_anisotropicConfined_pairwiseED`.

`R` depends only on `Cfib` (through `Plank.fibreTubeConst Cfib` and the dimensional constant of
`Kakeya.exists_notED_tube_axis_bound`); it does not depend on `a`, `b`, `θ`, the slab, the fibre or
its cardinality. -/
theorem exists_anisotropicConfined_of_notED_slabTube (Cfib : ℝ≥0) (hCfib : 1 ≤ Cfib) :
    ∃ R : ℝ, 1 ≤ R ∧
      ∀ {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1} (hθ0 : 0 < θ) (hb0 : 0 < b)
        (fibre : Finset (ThickenedPlank θ b hθ1 hb1))
        (Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (S : Slab θ hθ1),
        SlabFibreGeometry fibre Yθ S Cfib →
        ∀ {Q Q₀ : ThickenedPlank θ b hθ1 hb1}, Q ∈ fibre → Q₀ ∈ fibre →
        ¬ IsEssentiallyDistinct
            ((Q.slabTube S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib)).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))
            ((Q₀.slabTube S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib)).carrier :
              Set (EuclideanSpace ℝ (Fin 3))) →
        (∀ j k : Fin 3, j ≠ k →
            max ((![θ * b, b, 1] j : ℝ≥0) : ℝ) ((![θ * b, b, 1] k : ℝ≥0) : ℝ)
                * |inner ℝ (Q.basis j) (Q₀.basis k)|
              ≤ R * min ((![θ * b, b, 1] j : ℝ≥0) : ℝ) ((![θ * b, b, 1] k : ℝ≥0) : ℝ)) ∧
          (∀ k : Fin 3, |inner ℝ (Q₀.basis k) (Q.center -ᵥ Q₀.center)|
              ≤ R * ((![θ * b, b, 1] k : ℝ≥0) : ℝ)) := by
  obtain ⟨A, hA, hAprof⟩ := exists_axisProfile_of_notED_slabTube Cfib hCfib
  obtain ⟨B, hB, hBprof⟩ := exists_centerProfile_of_notED_slabTube Cfib hCfib
  have hCf : (0:ℝ) ≤ (Cfib : ℝ) := (Cfib : ℝ≥0).coe_nonneg
  set Ctan : ℝ := 3 * (Cfib : ℝ)
  set T : ℝ := 1 + 3 * (Cfib : ℝ)
  set D : ℝ := 8 * (Cfib : ℝ)
  have hCtan0 : 0 ≤ Ctan := by positivity
  have hT0 : 0 ≤ T := by positivity
  have hT1 : 1 ≤ T := by nlinarith [hCf]
  have hD0 : 0 ≤ D := by positivity
  refine ⟨1 + (3*Ctan + 4*T*A*(1+2*Ctan) + 4*T*A) + (D + 3*B*(1+2*Ctan)), ?_, ?_⟩
  · have h0 : 0 ≤ 3*Ctan + 4*T*A*(1+2*Ctan) + 4*T*A + D + 3*B*(1+2*Ctan) := by positivity
    linarith
  intro θ b hθ1 hb1 hθ0 hb0 fibre Yθ S h Q Q₀ hQ hQ₀ hnotED
  obtain ⟨t, ht0, htinv, hv0, hv1, hv2⟩ := hAprof hθ0 hb0 fibre Yθ S h hQ hQ₀ hnotED
  obtain ⟨r, hz0, hz1, hz2⟩ := hBprof hθ0 hb0 fibre Yθ S h hQ hQ₀ hnotED
  have htanQ : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (Q.basis 0) (S.basis j)| ≤ Ctan * (θ:ℝ) := by
    intro j hj
    have ht := h.tangency Q hQ j hj
    have hθ : (0:ℝ) ≤ (θ:ℝ) := (θ : ℝ≥0).coe_nonneg
    nlinarith
  have htanQ₀ : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (Q₀.basis 0) (S.basis j)| ≤ Ctan * (θ:ℝ) := by
    intro j hj
    have ht := h.tangency Q₀ hQ₀ j hj
    have hθ : (0:ℝ) ≤ (θ:ℝ) := (θ : ℝ≥0).coe_nonneg
    nlinarith
  have hnrmQ : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (S.basis 0) (Q.basis j)| ≤ Ctan * (θ:ℝ) :=
    fun j hj => by simpa [Ctan] using h.abs_inner_slabNormal_le hQ hj
  have hnrmQ₀ : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (S.basis 0) (Q₀.basis j)| ≤ Ctan * (θ:ℝ) :=
    fun j hj => by simpa [Ctan] using h.abs_inner_slabNormal_le hQ₀ hj
  have hΔ : ‖(Q.center -ᵥ Q₀.center : EuclideanSpace ℝ (Fin 3))‖ ≤ D := by
    simpa [D] using h.norm_center_sub_le hCfib hQ hQ₀
  refine ⟨?_, ?_⟩
  · intro j k hjk
    have hfr := frame_confined_of_slab_profile S Q Q₀ hb0 (by positivity) hA hT1
      htanQ htanQ₀ hnrmQ hnrmQ₀ ht0 htinv hv0 hv1 hv2 j k hjk
    have hmin : (0:ℝ) ≤ min ((![θ*b, b, 1] j : ℝ≥0) : ℝ) ((![θ*b, b, 1] k : ℝ≥0) : ℝ) := by
      positivity
    have hRge : 3*Ctan + 4*T*A*(1+2*Ctan) + 4*T*A ≤
        1 + (3*Ctan + 4*T*A*(1+2*Ctan) + 4*T*A) + (D + 3*B*(1+2*Ctan)) := by
      have h0 : 0 ≤ 1 + D + 3*B*(1+2*Ctan) := by positivity
      linarith
    exact le_trans hfr (mul_le_mul_of_nonneg_right hRge hmin)
  · intro k
    have hcen := center_confined_of_slab_profile S Q Q₀ hb0 (by positivity) hB htanQ₀ hΔ
      hz0 hz1 hz2 k
    have hw : (0:ℝ) ≤ ((![θ*b, b, 1] k : ℝ≥0) : ℝ) := (_ : ℝ≥0).coe_nonneg
    have hRge : D + 3*B*(1+2*Ctan) ≤
        1 + (3*Ctan + 4*T*A*(1+2*Ctan) + 4*T*A) + (D + 3*B*(1+2*Ctan)) := by
      have h0 : 0 ≤ 1 + (3*Ctan + 4*T*A*(1+2*Ctan) + 4*T*A) := by positivity
      linarith
    exact le_trans hcen (mul_le_mul_of_nonneg_right hRge hw)

/-- **The anisotropic ED-packing bridge** (the missing geometric input of
`Plank.normaliseSlabFamilyToTubes`).

For a fixed slab-fibre loss `Cfib ≥ 1` there is `MED : ℕ`, depending only on `Cfib`, such that the
enclosing `b/8`-tube family of any slab fibre with the geometry of `Plank.SlabFibreGeometry` is
essentially distinct up to multiplicity `MED`:

`Kakeya.IsEDUpToMult fibre (fun Q => (Q.slabTube S κ …).carrier) MED`.

Tube-level *pairwise* essential distinctness is false (the tube inflates the core by a fixed
factor, so two cores separated only at their own scale are swallowed); the bounded-multiplicity
statement is the honest replacement, and
`Kakeya.IsEDUpToMult.exists_pairwise_subset_with_weight` converts it into a genuinely pairwise
essentially distinct subfamily at the fixed cost `MED + 1` in shade mass.

The proof fixes `Q₀` and counts the members `Q` of the fibre whose tube fails to be essentially
distinct from `T Q₀`. Each such `Q` is pose-confined against `Q₀`
(`Plank.exists_anisotropicConfined_of_notED_slabTube`), and the fibre prisms are pairwise
essentially distinct, so `Plank.card_le_of_anisotropicConfined_pairwiseED` bounds that count by
`(768 R² + 2) ^ 12`. -/
theorem exists_isEDUpToMult_slabTube (Cfib : ℝ≥0) (hCfib : 1 ≤ Cfib) :
    ∃ MED : ℕ,
      ∀ {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1} (hθ0 : 0 < θ) (hb0 : 0 < b)
        (fibre : Finset (ThickenedPlank θ b hθ1 hb1))
        (Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (S : Slab θ hθ1),
        SlabFibreGeometry fibre Yθ S Cfib →
        Kakeya.IsEDUpToMult fibre
          (fun Q => ((Q.slabTube S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib)).carrier :
            Set (EuclideanSpace ℝ (Fin 3)))) MED := by
  obtain ⟨R, hR, hconf⟩ := exists_anisotropicConfined_of_notED_slabTube Cfib hCfib
  refine ⟨⌈(768 * R ^ 2 + 2) ^ 12⌉₊, ?_⟩
  intro θ b hθ1 hb1 hθ0 hb0 fibre Yθ S h Q₀ hQ₀
  classical
  set V : ThickenedPlank θ b hθ1 hb1 → Set (EuclideanSpace ℝ (Fin 3)) :=
    fun Q => (Q.slabTube S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib)).carrier with hV
  set F := Kakeya.notEssDistinctSet fibre V (V Q₀) with hF
  have hmem : ∀ Q, Q ∈ F ↔ (Q ∈ fibre ∧ ¬ IsEssentiallyDistinct (V Q) (V Q₀)) := by
    intro Q; simp [hF, Kakeya.notEssDistinctSet, Finset.mem_filter]
  have ha0 : 0 < θ * b := mul_pos hθ0 hb0
  have hcard : (F.card : ℝ) ≤ (768 * R ^ 2 + 2) ^ 12 := by
    refine card_le_of_anisotropicConfined_pairwiseED ha0 F (fun Q => Q) Q₀ hR ?_ ?_ ?_
    · intro Q hQF
      exact (hconf hθ0 hb0 fibre Yθ S h ((hmem Q).1 hQF).1 hQ₀ ((hmem Q).1 hQF).2).1
    · intro Q hQF
      exact (hconf hθ0 hb0 fibre Yθ S h ((hmem Q).1 hQF).1 hQ₀ ((hmem Q).1 hQF).2).2
    · intro Q hQF Q' hQ'F hne
      exact h.pairwise_essentiallyDistinct (Finset.mem_coe.mpr ((hmem Q).1 hQF).1)
        (Finset.mem_coe.mpr ((hmem Q').1 hQ'F).1) hne
  have : (F.card : ℝ) ≤ ((⌈(768 * R ^ 2 + 2) ^ 12⌉₊ : ℕ) : ℝ) := hcard.trans (Nat.le_ceil _)
  exact_mod_cast this

/-- **Extraction of a pairwise essentially distinct subfamily of tubes.**

The form in which `Plank.frostmanSlabUnionVolumeLowerBound` consumes the bridge: for a fixed
slab-fibre loss `Cfib ≥ 1` there is `MED : ℕ` such that every slab fibre with the geometry of
`Plank.SlabFibreGeometry` has a subfamily whose enclosing `b/8`-tubes are *genuinely* pairwise
essentially distinct — the hypothesis of `Kakeya.FrostmanEstimate` (GWZ Lemma 3.9) — and which
retains, for **any** nonnegative weight `w`, at least a `1 / (MED + 1)` fraction of the total
weight.

Taking `w Q = (volume (Yθ Q).shade).toReal` this is the shade-mass statement the per-slab volume
lower bound needs; taking `w = 1` it is the cardinality statement. Since the union over the
subfamily is contained in the union over the whole fibre, a union-volume lower bound proved for the
subfamily is one for the fibre, so the only loss is the absolute factor `MED + 1`.

This is `Kakeya.IsEDUpToMult.exists_pairwise_subset_with_weight` applied to
`Plank.exists_isEDUpToMult_slabTube`. -/
theorem exists_pairwiseED_subfibre_slabTube (Cfib : ℝ≥0) (hCfib : 1 ≤ Cfib) :
    ∃ MED : ℕ,
      ∀ {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1} (hθ0 : 0 < θ) (hb0 : 0 < b)
        (fibre : Finset (ThickenedPlank θ b hθ1 hb1))
        (Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (S : Slab θ hθ1),
        SlabFibreGeometry fibre Yθ S Cfib →
        ∀ w : ThickenedPlank θ b hθ1 hb1 → ℝ, (∀ Q ∈ fibre, 0 ≤ w Q) →
        ∃ sub : Finset (ThickenedPlank θ b hθ1 hb1), sub ⊆ fibre ∧
          (↑sub : Set (ThickenedPlank θ b hθ1 hb1)).Pairwise
            (fun Q Q' => IsEssentiallyDistinct
              ((Q.slabTube S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib)).carrier :
                Set (EuclideanSpace ℝ (Fin 3)))
              ((Q'.slabTube S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib)).carrier :
                Set (EuclideanSpace ℝ (Fin 3)))) ∧
          (∑ Q ∈ fibre, w Q) ≤ ((MED : ℝ) + 1) * ∑ Q ∈ sub, w Q := by
  obtain ⟨MED, hMED⟩ := exists_isEDUpToMult_slabTube Cfib hCfib
  refine ⟨MED, ?_⟩
  intro θ b hθ1 hb1 hθ0 hb0 fibre Yθ S h w hw
  exact (hMED hθ0 hb0 fibre Yθ S h).exists_pairwise_subset_with_weight w hw

end Plank

end
