/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallCoreEDCount

/-!
# GWZ §9.3 steps 6-8, assembled at the dilated carrier (S-4)

This file assembles the `BallDataCore` used by `Kakeya.VeryNotSticky.edFoldCore`
at a dilated carrier and proves the resulting estimate under explicit
hypothesis floors for the geometric constants.

## What is here

* `Kakeya.VeryNotSticky.CapsulePresentation` — the capsule presentation of a `BallDataCore`'s
  segments, as *data*: the parent tube of each segment, named. This is
  `Kakeya.VeryNotSticky.HasCapsuleSegments` with the existential skolemised, plus the two
  facts about the presentation the dilated re-presentation needs (the parent's shading meets
  the piece; the pieces sit in the shrunken balls).
* `Kakeya.VeryNotSticky.edDilateCore` — the **re-presentation of a capsule core at the
  `K′₀`-dilated carrier**, all forty-four `BallDataCore` fields. Nothing is folded here: the
  segments, the parent families, the fibre count and the shadings are the base core's; only
  the carriers grow, from `Kakeya.VeryNotSticky.segCarrierSet` to
  `Kakeya.VeryNotSticky.segCarrierSetAt edDilateConstant`.
* `Kakeya.VeryNotSticky.exists_core_edSegments_of_cover_floor` — the BP264 target with the
  three hypothesis floors of  §G-1  in
  place of `4 ≤ C₀`, `4 c₁ D ≤ 1` and `16 δ ≤ r₁`, and with the fibre budget kept as an
  explicit binder so that the explicit fibre budget is a substitution.

## Why the carrier is the *radius* dilate and not the homothety dilate

`Kakeya.VeryNotSticky.not_segCarrierSetHom_subset_closedBall_of_radiusFloor` (below) is the
compiled reason: the homothety dilate of a capsule of half-length `L = r₁/4` has half-length
`K′₀ L ≈ 25 r₁`, so it violates `BallDataCore.segs_subset_ball` for *every* configuration —
the field asks the carrier to sit inside the ball of radius `r₁` it was cut out of. The
radius-only dilate `Kakeya.VeryNotSticky.segCarrierSetAt` keeps the core window and only widens
the tube, and its margin `r₁/4 + r₁/16 + K′₀ δ ≤ r₁` is paid by the radius floor.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace Kakeya.VeryNotSticky

universe u

variable {cfg : VeryNotSticky.{u}}

/-! ### Preliminaries -/

/-- Weakening the constant of a thickness profile. -/
theorem hasThicknesses_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {A : Set E} {C C' : NNReal} {t : Fin n → ℝ} (hC : 0 < C) (hCC' : C ≤ C')
    (ht : ∀ k, 0 ≤ t k) (h : Kakeya.HasThicknesses A C t) : Kakeya.HasThicknesses A C' t := by
  intro k
  obtain ⟨h1, h2⟩ := h k
  have hCR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hCC'R : (C : ℝ) ≤ (C' : ℝ) := by exact_mod_cast hCC'
  exact ⟨le_trans (mul_le_mul_of_nonneg_right (inv_anti₀ hCR hCC'R) (ht k)) h1,
    le_trans h2 (mul_le_mul_of_nonneg_right hCC'R (ht k))⟩

/-- `Metric.ethickness.scale` is monotone under inclusion. -/
theorem ethickness_scale_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : Set E} (h : s ⊆ t) :
    Metric.ethickness.scale ℝ s ≤ Metric.ethickness.scale ℝ t :=
  Finset.inf_mono_fun (fun n _ => Metric.ethickness_monotone (𝕜 := ℝ) h n)

theorem one_lt_edDilateConstant : 1 < edDilateConstant := by
  rw [← NNReal.coe_lt_coe, coe_edDilateConstant, NNReal.coe_one]
  exact one_lt_edComparabilityConstant

theorem edDilateConstant_pos : 0 < edDilateConstant :=
  lt_of_lt_of_le zero_lt_one one_le_edDilateConstant

/-- The radius floor pays the dilate inside a quarter of the ball radius. -/
theorem edDilate_mul_delta_le_quarter
    (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) :
    ((edDilateConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 4 := by
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  have he : ((edRadiusConstant : NNReal) : ℝ) = 8 * ((edDilateConstant : NNReal) : ℝ) := by
    rw [edRadiusConstant]; push_cast; ring
  rw [he] at hrad
  have hK0 : (0 : ℝ) ≤ ((edDilateConstant : NNReal) : ℝ) := (edDilateConstant).coe_nonneg
  nlinarith

theorem edDilate_mul_delta_le_eighth
    (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) :
    ((edDilateConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 8 := by
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  have he : ((edRadiusConstant : NNReal) : ℝ) = 8 * ((edDilateConstant : NNReal) : ℝ) := by
    rw [edRadiusConstant]; push_cast; ring
  rw [he] at hrad
  linarith

theorem delta_le_quarter_of_radiusFloor
    (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) :
    (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 4 := by
  have h := deltaLeR₁_of_radiusFloor hrad
  linarith

theorem two_mul_quarter_le_one (cfg : VeryNotSticky.{u}) : 2 * ((cfg.r₁ : ℝ) / 4) ≤ 1 := by
  have := r₁_le_one cfg
  linarith

/-- The dilated capsule stays inside the ball it was cut out of, at the concrete margin. -/
theorem segCarrierSetAt_subset_closedBall_ctr {δ : NNReal} (K : NNReal)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) {L ρ R : ℝ}
    (hL : 0 ≤ L) (hmeet : (T.carrier ∩ ball c ρ).Nonempty)
    (hR : (K : ℝ) * (δ : ℝ) + (2 * L + 2 * (δ : ℝ) + ρ) ≤ R) :
    segCarrierSetAt K T c L ⊆ closedBall c R := by
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hρ : 0 < ρ := by
    obtain ⟨x, -, hx⟩ := hmeet
    exact lt_of_le_of_lt dist_nonneg (Metric.mem_ball.1 hx)
  have hR' : (0 : ℝ) ≤ 2 * L + 2 * (δ : ℝ) + ρ := by linarith
  have h1 : segment ℝ (corePt T (segStart T c L)) (corePt T (segStart T c L + 2 * L)) ⊆
      closedBall c (2 * L + 2 * (δ : ℝ) + ρ) :=
    subset_trans (Metric.self_subset_cthickening _)
      (segCarrierSet_subset_closedBall_ctr T c hL hmeet le_rfl)
  intro z hz
  have h2 := Metric.cthickening_subset_of_subset ((K : ℝ) * (δ : ℝ)) h1 hz
  rw [cthickening_closedBall (by positivity) hR'] at h2
  exact Metric.closedBall_subset_closedBall hR h2

/-! ### The dilated capsule is a capsule: R-a and the core-line clause at radius `K δ`

`Kakeya.VeryNotSticky.capsule_subset_hom_of_not_essDistinct` (R-a) is stated at the tube's own
radius `δ` and for two windows about a *common* reference point. Both restrictions are
inessential to its proof, and lifting them is what lets the fold's obligations be discharged at
the **dilated** carrier, where  §G-1 rules they have to live. -/

section DilatedRadiusGeometry

variable {δ : NNReal}

/-- The `K`-dilated capsule as a convex body. -/
noncomputable def capsuleBodyAt (K : NNReal) (T : Tube δ E3) (c : E3) {L : ℝ} (hL : 0 ≤ L) :
    ConvexSpaceBody E3 where
  carrier := segCarrierSetAt K T c L
  convex' := (convex_segCarrierSetAt K T c L).isConvexSet
  isCompact' := Metric.isCompact_of_isClosed_isBounded (isClosed_segCarrierSetAt K T c L)
    (isBounded_segCarrierSetAt K T c hL)
  nonempty' := ⟨corePt T (segStart T c L), Metric.self_subset_cthickening _
    (left_mem_segment ℝ _ _)⟩

@[simp] theorem capsuleBodyAt_carrier (K : NNReal) (T : Tube δ E3) (c : E3) {L : ℝ}
    (hL : 0 ≤ L) : (capsuleBodyAt K T c hL).carrier = segCarrierSetAt K T c L := rfl

/-- **The dilated capsule, rescaled to a unit tube.** -/
noncomputable def rescaledCapsuleTubeAt {δ' : NNReal} (K : NNReal) (T : Tube δ E3) (c m : E3)
    {L : ℝ} (hL : 0 < L) (hδ' : (δ' : ℝ) = (2 * L)⁻¹ * ((K : ℝ) * (δ : ℝ))) : Tube δ' E3 where
  toConvexSpaceBody :=
    ConvexSpaceBody.affineImage (AffineMap.homothety m (2 * L)⁻¹)
      (AffineMap.continuous_of_finiteDimensional _) (capsuleBodyAt K T c (le_of_lt hL))
  x := AffineMap.homothety m (2 * L)⁻¹ (corePt T (segStart T c L))
  y := AffineMap.homothety m (2 * L)⁻¹ (corePt T (segStart T c L + 2 * L))
  dist_eq_one := by
    have h2L : (0 : ℝ) < 2 * L := by linarith
    rw [dist_homothety, abs_of_pos (inv_pos.2 h2L), dist_corePt_window T c (le_of_lt hL),
      inv_mul_cancel₀ (ne_of_gt h2L)]
  carrier_eq := by
    have h2L : (0 : ℝ) < 2 * L := by linarith
    have hk : (0 : ℝ) < (2 * L)⁻¹ := inv_pos.2 h2L
    have hKδ : (0 : ℝ) ≤ (K : ℝ) * (δ : ℝ) := by positivity
    change (AffineMap.homothety m (2 * L)⁻¹) '' (segCarrierSetAt K T c L) = _
    rw [segCarrierSetAt, isClosed_segment.cthickening_eq_biUnion_closedBall hKδ,
      Set.image_iUnion₂]
    rw [← homothety_image_segment m (2 * L)⁻¹ _ _]
    rw [Set.biUnion_image]
    refine Set.iUnion₂_congr fun w _ => ?_
    rw [homothety_image_closedBall hk w ((K : ℝ) * (δ : ℝ)), hδ']

@[simp] theorem rescaledCapsuleTubeAt_carrier {δ' : NNReal} (K : NNReal) (T : Tube δ E3)
    (c m : E3) {L : ℝ} (hL : 0 < L) (hδ' : (δ' : ℝ) = (2 * L)⁻¹ * ((K : ℝ) * (δ : ℝ))) :
    (rescaledCapsuleTubeAt K T c m hL hδ').carrier =
      (AffineMap.homothety m (2 * L)⁻¹) '' (segCarrierSetAt K T c L) := rfl

theorem rescaledCapsuleTubeAt_center {δ' : NNReal} (K : NNReal) (T : Tube δ E3) (c m : E3)
    {L : ℝ} (hL : 0 < L) (hδ' : (δ' : ℝ) = (2 * L)⁻¹ * ((K : ℝ) * (δ : ℝ))) :
    (rescaledCapsuleTubeAt K T c m hL hδ').center =
      AffineMap.homothety m (2 * L)⁻¹ (capsuleCentre T c L) := by
  change midpoint ℝ _ _ = _
  rw [show (rescaledCapsuleTubeAt K T c m hL hδ').x =
      AffineMap.homothety m (2 * L)⁻¹ (corePt T (segStart T c L)) from rfl,
    show (rescaledCapsuleTubeAt K T c m hL hδ').y =
      AffineMap.homothety m (2 * L)⁻¹ (corePt T (segStart T c L + 2 * L)) from rfl,
    ← AffineMap.map_midpoint]
  congr 1
  change midpoint ℝ (corePt T (segStart T c L)) (corePt T (segStart T c L + 2 * L)) =
    corePt T (segStart T c L + L)
  simp only [corePt, midpoint_eq_smul_add, invOf_eq_inv]
  module

/-- **R-a at the dilated radius, with the two windows allowed to have different centres.**
Two `K`-dilated capsules of the same half-length `L` that are not essentially distinct: each
lies in the `K′₀`-homothety dilate of the other about the other's own centre. This is
`Kakeya.VeryNotSticky.capsule_subset_hom_of_not_essDistinct` at radius `K δ`, with `c` split —
the proof never needed the two windows to share a reference point. -/
theorem segCarrierSetAt_subset_hom_of_not_essDistinct {K : NNReal} (hδ0 : 0 < δ) (hK : 0 < K)
    (Ti Tj : Tube δ E3) (ci cj : E3) {L : ℝ} (hL : 0 < L)
    (hKδL : (K : ℝ) * (δ : ℝ) ≤ 2 * L)
    (hne : ¬ IsEssentiallyDistinct (segCarrierSetAt K Ti ci L) (segCarrierSetAt K Tj cj L)) :
    segCarrierSetAt K Tj cj L ⊆
      (AffineMap.homothety (capsuleCentre Ti ci L) edComparabilityConstant) ''
        (segCarrierSetAt K Ti ci L) := by
  have h2L : (0 : ℝ) < 2 * L := by linarith
  have hk0 : (0 : ℝ) < (2 * L)⁻¹ := inv_pos.2 h2L
  have hkne : ((2 * L)⁻¹ : ℝ) ≠ 0 := ne_of_gt hk0
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  set k : ℝ := (2 * L)⁻¹ with hkdef
  set m : E3 := ci with hmdef
  set σ : E3 →ᵃ[ℝ] E3 := AffineMap.homothety m k with hσdef
  set δ' : NNReal := (k * ((K : ℝ) * (δ : ℝ))).toNNReal with hδ'def
  have hδ' : (δ' : ℝ) = k * ((K : ℝ) * (δ : ℝ)) := Real.coe_toNNReal _ (by positivity)
  have hδ'0 : 0 < δ' := by
    have : (0 : ℝ) < (δ' : ℝ) := by rw [hδ']; positivity
    exact_mod_cast this
  have hδ'1 : δ' ≤ 1 := by
    have : (δ' : ℝ) ≤ 1 := by
      rw [hδ', hkdef, inv_mul_le_iff₀ h2L]
      linarith
    exact_mod_cast this
  set Ti' : Tube δ' E3 := rescaledCapsuleTubeAt K Ti ci m hL hδ' with hTi'
  set Tj' : Tube δ' E3 := rescaledCapsuleTubeAt K Tj cj m hL hδ' with hTj'
  set σe : E3 ≃ᵃ[ℝ] E3 := AffineEquiv.homothetyUnitsMulHom m (Units.mk0 k hkne) with hσedef
  have hcoe : ⇑σe = ⇑σ := by
    rw [hσedef, AffineEquiv.coe_homothetyUnitsMulHom_apply, hσdef]; rfl
  have hne' : ¬ IsEssentiallyDistinct Ti'.carrier Tj'.carrier := by
    intro hED
    refine hne ?_
    have h := hED.image_affineEquiv σe.symm
    rw [hTi', hTj', rescaledCapsuleTubeAt_carrier, rescaledCapsuleTubeAt_carrier, ← hcoe,
      ← Set.image_comp, ← Set.image_comp] at h
    simpa using h
  have hsub := tube_subset_dilate_of_not_essDistinct hδ'0 hδ'1 Ti' Tj' hne'
  rw [Tube.dilate_carrier, hTi', rescaledCapsuleTubeAt_carrier,
    rescaledCapsuleTubeAt_center] at hsub
  intro x hx
  have hσx : σ x ∈ Tj'.carrier := by
    rw [hTj', rescaledCapsuleTubeAt_carrier]
    exact ⟨x, hx, rfl⟩
  obtain ⟨u, ⟨v, hv, rfl⟩, huv⟩ := hsub hσx
  refine ⟨v, hv, ?_⟩
  have := congrArg (AffineMap.homothety m k⁻¹) huv
  rw [homothety_conj hkne (capsuleCentre Ti ci L) edComparabilityConstant v,
    homothety_inv_apply hkne x] at this
  exact this

/-- **The `K′`-homothety dilate of a `K`-dilated capsule still lies along the core line**, at
radius `K′ K δ`. -/
theorem segCarrierSetAtHom_subset_cthickening_line {K' : ℝ} (hK' : 0 ≤ K') (K : NNReal)
    (T : Tube δ E3) (c : E3) {L : ℝ} (hL : 0 ≤ L) {C : ℝ}
    (hC : K' * ((K : ℝ) * (δ : ℝ)) ≤ C) :
    (AffineMap.homothety (capsuleCentre T c L) K') '' (segCarrierSetAt K T c L) ⊆
      cthickening C (AffineSubspace.mk' (corePt T (segStart T c L))
        (Submodule.span ℝ {T.direction}) : Set E3) := by
  have hKδ : (0 : ℝ) ≤ (K : ℝ) * (δ : ℝ) := by positivity
  rintro _ ⟨x, hx, rfl⟩
  rw [segCarrierSetAt, isClosed_segment.cthickening_eq_biUnion_closedBall hKδ] at hx
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
  have hwline : w ∈ (AffineSubspace.mk' (corePt T (segStart T c L))
      (Submodule.span ℝ {T.direction}) : Set E3) := by
    obtain ⟨u, _, rfl⟩ := segment_subset_corePt_image T (by linarith) hw
    have : corePt T u = (u - segStart T c L) • T.direction +ᵥ corePt T (segStart T c L) := by
      simp only [corePt, vadd_eq_add]; module
    rw [this]
    exact AffineSubspace.vadd_mem_mk' _
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hcline : capsuleCentre T c L ∈ (AffineSubspace.mk' (corePt T (segStart T c L))
      (Submodule.span ℝ {T.direction}) : Set E3) := by
    have : capsuleCentre T c L = L • T.direction +ᵥ corePt T (segStart T c L) := by
      simp only [capsuleCentre, corePt, vadd_eq_add]; module
    rw [this]
    exact AffineSubspace.vadd_mem_mk' _
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hhw : AffineMap.homothety (capsuleCentre T c L) K' w ∈
      (AffineSubspace.mk' (corePt T (segStart T c L))
        (Submodule.span ℝ {T.direction}) : Set E3) := by
    have hdir : w -ᵥ capsuleCentre T c L ∈
        (AffineSubspace.mk' (corePt T (segStart T c L))
          (Submodule.span ℝ {T.direction})).direction :=
      AffineSubspace.vsub_mem_direction hwline hcline
    have := AffineSubspace.vadd_mem_of_mem_direction
      (Submodule.smul_mem _ K' hdir) hcline
    simpa [AffineMap.homothety_apply] using this
  refine Metric.closedBall_subset_cthickening hhw C ?_
  rw [Metric.mem_closedBall, dist_homothety, abs_of_nonneg hK']
  rw [Metric.mem_closedBall] at hxw
  calc K' * dist x w ≤ K' * ((K : ℝ) * (δ : ℝ)) := mul_le_mul_of_nonneg_left hxw hK'
    _ ≤ C := hC


/-- **R-b at the dilated radius.** If the `K`-dilated capsule of `Tj` lies in the `K′`-homothety
dilate of the `K`-dilated capsule of `Ti`, the two directions make a line angle at most
`(π/2)·(2 K′ K δ / L)`. This is
`Kakeya.VeryNotSticky.lineAngle_direction_le_of_capsule_subset_hom` at radius `K δ`, with the two
window reference points split. -/
theorem lineAngle_direction_le_of_segCarrierSetAt_subset_hom {K : NNReal} (hK : 1 ≤ K)
    (Ti Tj : Tube δ E3) (ci cj : E3) {L : ℝ} (hL : 0 < L) {K' : ℝ} (hK' : 0 ≤ K')
    (hsub : segCarrierSetAt K Tj cj L ⊆
      (AffineMap.homothety (capsuleCentre Ti ci L) K') '' (segCarrierSetAt K Ti ci L)) :
    NonSlab.lineAngle Tj.direction Ti.direction ≤
      Real.pi / 2 * (2 * K' * ((K : ℝ) * (δ : ℝ)) / L) := by
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hR0 : (0 : ℝ) ≤ (K : ℝ) * (δ : ℝ) := by positivity
  have h2L : (0 : ℝ) < 2 * L := by linarith
  set R : ℝ := (K : ℝ) * (δ : ℝ) with hRdef
  set aj := segStart Tj cj L with haj
  set ai := segStart Ti ci L with hai
  have hp : corePt Tj aj ∈ segCarrierSetAt K Tj cj L :=
    segCarrierSet_subset_segCarrierSetAt hK Tj cj L
      (corePt_window_mem_segCarrierSet Tj cj aj ⟨le_rfl, by linarith⟩)
  have hq : corePt Tj (aj + 2 * L) ∈ segCarrierSetAt K Tj cj L :=
    segCarrierSet_subset_segCarrierSetAt hK Tj cj L
      (corePt_window_mem_segCarrierSet Tj cj (aj + 2 * L) ⟨by linarith, le_rfl⟩)
  have hdecomp : ∀ t : ℝ, corePt Tj t ∈ segCarrierSetAt K Tj cj L →
      ∃ (r : ℝ) (e : E3), ‖e‖ ≤ R ∧
        corePt Tj t = r • Ti.direction + K' • e + capsuleCentre Ti ci L := by
    intro t ht
    obtain ⟨u, hu, hEq⟩ := hsub ht
    rw [segCarrierSetAt, isClosed_segment.cthickening_eq_biUnion_closedBall hR0] at hu
    obtain ⟨w, hw, huw⟩ := Set.mem_iUnion₂.mp hu
    obtain ⟨s, hs, rfl⟩ := segment_subset_corePt_image Ti (by linarith) hw
    refine ⟨K' * (s - (ai + L)), u - corePt Ti s, ?_, ?_⟩
    · rw [← dist_eq_norm]
      exact Metric.mem_closedBall.1 huw
    · rw [← hEq]
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, capsuleCentre, corePt]
      module
  obtain ⟨rp, ep, hep, hpEq⟩ := hdecomp aj hp
  obtain ⟨rq, eq', heq, hqEq⟩ := hdecomp (aj + 2 * L) hq
  have hchord : (2 * L) • Tj.direction = (rq - rp) • Ti.direction + K' • (eq' - ep) := by
    have h : corePt Tj (aj + 2 * L) - corePt Tj aj = (2 * L) • Tj.direction := by
      simp only [corePt]; module
    rw [← h, hpEq, hqEq]
    module
  have hjn : ‖Tj.direction‖ = 1 := Tj.norm_direction
  have hin : ‖Ti.direction‖ = 1 := Ti.norm_direction
  set lam : ℝ := (rq - rp) / (2 * L) with hlam
  have hr : ‖Tj.direction - lam • Ti.direction‖ ≤ K' * R / L := by
    have hscaled : Tj.direction - lam • Ti.direction = (2 * L)⁻¹ • (K' • (eq' - ep)) := by
      have h := congrArg (fun z => (2 * L)⁻¹ • z) hchord
      simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt h2L), one_smul, hlam] at h ⊢
      rw [smul_add, smul_smul, smul_smul] at h
      rw [show (2 * L)⁻¹ * (rq - rp) = (rq - rp) / (2 * L) by ring] at h
      rw [h]
      module
    rw [hscaled, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 h2L), abs_of_nonneg hK']
    have hee : ‖eq' - ep‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith)
    have hstep : K' * ‖eq' - ep‖ ≤ K' * (2 * R) := mul_le_mul_of_nonneg_left hee hK'
    calc (2 * L)⁻¹ * (K' * ‖eq' - ep‖) ≤ (2 * L)⁻¹ * (K' * (2 * R)) :=
          mul_le_mul_of_nonneg_left hstep (le_of_lt (inv_pos.2 h2L))
      _ = K' * R / L := by field_simp
  have hlam1 : |(|lam| - 1)| ≤ K' * R / L := by
    have h1 : ‖lam • Ti.direction‖ = |lam| := by
      rw [norm_smul, Real.norm_eq_abs, hin, mul_one]
    have h2 := abs_norm_sub_norm_le (Tj.direction) (lam • Ti.direction)
    rw [hjn, h1] at h2
    rw [abs_sub_comm]
    exact le_trans h2 hr
  refine lineAngle_le_of_min_norm hjn hin ?_
  rcases le_total 0 lam with hpos | hneg
  · left
    have hsgn : |lam| = lam := abs_of_nonneg hpos
    calc ‖Tj.direction - Ti.direction‖
        ≤ ‖Tj.direction - lam • Ti.direction‖ + ‖lam • Ti.direction - Ti.direction‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ K' * R / L + K' * R / L := by
          refine add_le_add hr ?_
          rw [show lam • Ti.direction - Ti.direction = (lam - 1) • Ti.direction by module,
            norm_smul, Real.norm_eq_abs, hin, mul_one]
          rw [← hsgn]; exact hlam1
      _ = 2 * K' * R / L := by ring
  · right
    have hsgn : |lam| = -lam := abs_of_nonpos hneg
    calc ‖Tj.direction + Ti.direction‖
        ≤ ‖Tj.direction - lam • Ti.direction‖ + ‖lam • Ti.direction + Ti.direction‖ := by
          have h : Tj.direction + Ti.direction
              = (Tj.direction - lam • Ti.direction) + (lam • Ti.direction + Ti.direction) := by
            module
          rw [h]; exact norm_add_le _ _
      _ ≤ K' * R / L + K' * R / L := by
          refine add_le_add hr ?_
          rw [show lam • Ti.direction + Ti.direction = (lam + 1) • Ti.direction by module,
            norm_smul, Real.norm_eq_abs, hin, mul_one]
          have habs : |lam + 1| = |(|lam| - 1)| := by
            rw [hsgn, show -lam - 1 = -(lam + 1) by ring, abs_neg]
          rw [habs]
          exact hlam1
      _ = 2 * K' * R / L := by ring

end DilatedRadiusGeometry

/-! ### The capsule presentation, skolemised -/

/-- The capsule presentation of a `BallDataCore`'s segments, as *data*. -/
structure CapsulePresentation (core : BallDataCore cfg) where
  /-- The parent tube of a segment. -/
  tub : core.σ → cfg.ι
  /-- The parent tube belongs to the family. -/
  tub_mem : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, tub p ∈ cfg.s
  /-- The carrier of a segment is the capsule of its parent tube. -/
  carrier_eq : ∀ B ∈ core.bs, ∀ p ∈ core.segs B,
    (core.Y p).carrier = segCarrierSet (cfg.T (tub p)).toTube (core.ctr B) ((cfg.r₁ : ℝ) / 4)
  /-- The parent family is the singleton of the parent tube. -/
  fam_eq : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, core.fam p = {tub p}
  /-- The parent tube's shading meets the piece. -/
  meets : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, ((cfg.T (tub p)).shade ∩ core.P B).Nonempty
  /-- The pieces sit in the shrunken balls. -/
  ball16 : ∀ B ∈ core.bs, core.P B ⊆ ball (core.ctr B) ((cfg.r₁ : ℝ) / 16)

/-! ### The dilated re-presentation -/

/-- The `K′₀`-dilated capsule of the segment `p.2` in the ball `p.1`. -/
noncomputable abbrev edDilateSet (core : BallDataCore cfg) (tub : core.σ → cfg.ι)
    (p : core.bι × core.σ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  segCarrierSetAt edDilateConstant (cfg.T (tub p.2)).toTube (core.ctr p.1) ((cfg.r₁ : ℝ) / 4)

/-- The segment body of the dilated re-presentation. -/
noncomputable def edDilateBody (core : BallDataCore cfg) (tub : core.σ → cfg.ι)
    (p : core.bι × core.σ) : ShadedBody (EuclideanSpace ℝ (Fin 3)) where
  carrier := edDilateSet core tub p
  convex' := (convex_segCarrierSetAt _ _ _ _).isConvexSet
  isCompact' := Metric.isCompact_of_isClosed_isBounded (isClosed_segCarrierSetAt _ _ _ _)
    (isBounded_segCarrierSetAt _ _ _ (by positivity))
  nonempty' := Set.Nonempty.mono
    (segCarrierSet_subset_segCarrierSetAt one_le_edDilateConstant _ _ _)
    (segCarrierSet_nonempty _ _ (by positivity))
  shade := (core.Y p.2).shade ∩ edDilateSet core tub p
  measurableSet_shade := (core.Y p.2).measurableSet_shade.inter
    (isClosed_segCarrierSetAt _ _ _ _).measurableSet
  shade_subset := fun _ hx => hx.2

@[simp] theorem edDilateBody_carrier (core : BallDataCore cfg) (tub : core.σ → cfg.ι)
    (p : core.bι × core.σ) :
    (edDilateBody core tub p).carrier = edDilateSet core tub p := rfl

@[simp] theorem edDilateBody_shade (core : BallDataCore cfg) (tub : core.σ → cfg.ι)
    (p : core.bι × core.σ) :
    (edDilateBody core tub p).shade = (core.Y p.2).shade ∩ edDilateSet core tub p := rfl

open scoped Classical in
/-- The segment index set of the dilated re-presentation: the base core's, tagged by the ball. -/
noncomputable def edDilateSegs (core : BallDataCore cfg) (B : core.bι) :
    Finset (core.bι × core.σ) :=
  (core.segs B).image (fun x => ((B, x) : core.bι × core.σ))

theorem mem_edDilateSegs {core : BallDataCore cfg} {B : core.bι} {p : core.bι × core.σ} :
    p ∈ edDilateSegs core B ↔ p.1 = B ∧ p.2 ∈ core.segs B := by
  classical
  constructor
  · intro hp
    obtain ⟨x, hx, hxp⟩ := Finset.mem_image.1 hp
    exact ⟨by rw [← hxp], by rw [← hxp]; exact hx⟩
  · rintro ⟨h1, h2⟩
    refine Finset.mem_image.2 ⟨p.2, h2, ?_⟩
    rw [← h1]

theorem mem_edDilateSegs' {core : BallDataCore cfg} {B : core.bι} {p : core.bι × core.σ}
    (hp : p ∈ edDilateSegs core B) : ∃ x ∈ core.segs B, p = (B, x) := by
  classical
  obtain ⟨x, hx, hxp⟩ := Finset.mem_image.1 hp
  exact ⟨x, hx, hxp.symm⟩

section DilateCore

variable {core : BallDataCore cfg} (pres : CapsulePresentation core)

theorem base_carrier_subset_edDilateSet {B : core.bι} (hB : B ∈ core.bs) {x : core.σ}
    (hx : x ∈ core.segs B) :
    (core.Y x).carrier ⊆ edDilateSet core pres.tub (B, x) := by
  rw [pres.carrier_eq B hB x hx]
  exact segCarrierSet_subset_segCarrierSetAt one_le_edDilateConstant _ _ _

theorem base_shade_subset_edDilateSet {B : core.bι} (hB : B ∈ core.bs) {x : core.σ}
    (hx : x ∈ core.segs B) :
    (core.Y x).shade ⊆ edDilateSet core pres.tub (B, x) :=
  subset_trans (core.Y x).shade_subset (base_carrier_subset_edDilateSet pres hB hx)

theorem edDilate_shade_eq {B : core.bι} (hB : B ∈ core.bs) {x : core.σ}
    (hx : x ∈ core.segs B) :
    (edDilateBody core pres.tub (B, x)).shade = (core.Y x).shade :=
  Set.inter_eq_self_of_subset_left (base_shade_subset_edDilateSet pres hB hx)

theorem edDilate_profile_nonneg (cfg : VeryNotSticky.{u}) :
    ∀ k : Fin 3, 0 ≤ (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] : Fin 3 → ℝ) k := by
  intro k
  fin_cases k <;> simp

theorem edDilate_hasThicknesses {B : core.bι} (_hB : B ∈ core.bs) {x : core.σ}
    (_hx : x ∈ core.segs B)
    (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hfloor : edSegmentsConstant ≤ core.C₀) :
    Kakeya.HasThicknesses (edDilateBody core pres.tub (B, x)).carrier core.C₀
      ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] := by
  have hδL : (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 4 := delta_le_quarter_of_radiusFloor hrad
  have h := hasThicknesses_segCarrierSetAt one_le_edDilateConstant
    (cfg.T (pres.tub x)).toTube (core.ctr B) (L := (cfg.r₁ : ℝ) / 4) (by positivity) hδL
  have hrw : (4 : ℝ) * ((cfg.r₁ : ℝ) / 4) = (cfg.r₁ : ℝ) := by ring
  rw [hrw] at h
  refine hasThicknesses_mono ?_ ?_ (edDilate_profile_nonneg cfg) h
  · have hK : (1 : NNReal) ≤ edDilateConstant := one_le_edDilateConstant
    calc (0 : NNReal) < 1 := zero_lt_one
      _ ≤ 4 * edDilateConstant := by
          nth_rewrite 1 [show (4 : NNReal) * edDilateConstant
            = 4 * edDilateConstant from rfl]
          calc (1 : NNReal) ≤ edDilateConstant := hK
            _ = 1 * edDilateConstant := (one_mul _).symm
            _ ≤ 4 * edDilateConstant := by gcongr; norm_num
  · exact hfloor

theorem edDilate_segs_core {B : core.bι} (hB : B ∈ core.bs) {x : core.σ}
    (hx : x ∈ core.segs B) (hfloor : edSegmentsConstant ≤ core.C₀) {i : cfg.ι}
    (hi : i ∈ core.fam x) :
    ∃ z : EuclideanSpace ℝ (Fin 3), edDilateSet core pres.tub (B, x) ⊆
      cthickening ((core.C₀ : ℝ) * (cfg.δ : ℝ))
        (AffineSubspace.mk' z (Submodule.span ℝ {(cfg.T i).direction}) :
          Set (EuclideanSpace ℝ (Fin 3))) := by
  rw [pres.fam_eq B hB x hx, Finset.mem_singleton] at hi
  subst hi
  refine ⟨corePt (cfg.T (pres.tub x)).toTube
    (segStart (cfg.T (pres.tub x)).toTube (core.ctr B) ((cfg.r₁ : ℝ) / 4)), ?_⟩
  refine segCarrierSetAt_subset_cthickening_line _ _ _ (by positivity) ?_
  have h : ((edDilateConstant : NNReal) : ℝ) ≤ ((core.C₀ : NNReal) : ℝ) := by
    exact_mod_cast edDilateConstant_le_of_floor hfloor
  exact mul_le_mul_of_nonneg_right h (cfg.δ).coe_nonneg

theorem edDilate_segs_subset_ball {B : core.bι} (hB : B ∈ core.bs) {x : core.σ}
    (hx : x ∈ core.segs B)
    (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) :
    edDilateSet core pres.tub (B, x) ⊆ closedBall (core.ctr B) (cfg.r₁ : ℝ) := by
  obtain ⟨y, hy1, hy2⟩ := pres.meets B hB x hx
  have hr₁0 : (0 : ℝ) ≤ (cfg.r₁ : ℝ) := (cfg.r₁).coe_nonneg
  refine segCarrierSetAt_subset_closedBall_ctr _ _ _ (ρ := (cfg.r₁ : ℝ) / 16)
    (by positivity) ⟨y, (cfg.T (pres.tub x)).shade_subset hy1, pres.ball16 B hB hy2⟩ ?_
  have h1 : ((edDilateConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 8 :=
    edDilate_mul_delta_le_eighth hrad
  have h2 : (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 16 := by
    have := deltaLeR₁_of_radiusFloor hrad; linarith
  linarith

theorem edDilate_segs_scale {B : core.bι} (_hB : B ∈ core.bs) {x : core.σ}
    (_hx : x ∈ core.segs B) :
    (cfg.δ : ENNReal) ≤ Metric.ethickness.scale ℝ (edDilateSet core pres.tub (B, x)) :=
  le_trans (le_ethickness_scale_segCarrierSet _ _ (by positivity))
    (ethickness_scale_mono (segCarrierSet_subset_segCarrierSetAt one_le_edDilateConstant _ _ _))

open scoped Classical in
/-- **The dilated re-presentation of a capsule core**, all forty-four `BallDataCore` fields.

Nothing is folded: the segments, parent families, fibre count, working shading and shadings are
the base core's. Only the carriers grow, from the capsule `segCarrierSet` to its `K′₀`-dilate
`Kakeya.VeryNotSticky.segCarrierSetAt edDilateConstant`, which is where  §G-1 rules
the comparability clause has to live. The three floors are what pay for the growth:
`edSegmentsConstant ≤ C₀` for `segs_thickness` and `segs_core`, and the radius floor for
`segs_dims`, `segs_subset_ball` and the `δ`-cover. -/
noncomputable def edDilateCore
    (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hfloor : edSegmentsConstant ≤ core.C₀)
    (hDfloor : ballCoverConstant ≤ core.D) : BallDataCore cfg where
  C₀ := core.C₀
  hC₀ := core.hC₀
  D := core.D
  Yg := core.Yg
  Yg_subset := core.Yg_subset
  Yg_measurable := core.Yg_measurable
  Cg := core.Cg
  hCg := core.hCg
  Yg_mass := core.Yg_mass
  bι := core.bι
  σ := core.bι × core.σ
  bs := core.bs
  bs_nonempty := core.bs_nonempty
  ctr := core.ctr
  P := core.P
  P_subset_ball := core.P_subset_ball
  P_disjoint := core.P_disjoint
  P_measurable := core.P_measurable
  P_cover := core.P_cover
  ballOverlap := core.ballOverlap
  segs := fun B => edDilateSegs core B
  Y := fun p => edDilateBody core pres.tub p
  fam := fun p => core.fam p.2
  segs_nonempty := by
    intro B hB
    obtain ⟨x, hx⟩ := core.segs_nonempty B hB
    exact ⟨(B, x), mem_edDilateSegs.2 ⟨rfl, hx⟩⟩
  fam_subset := by
    intro B hB p hp
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    exact core.fam_subset B hB x hx
  fam_disjoint := by
    intro B hB p hp q hq hpq
    rw [Finset.mem_coe] at hp hq
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    obtain ⟨y, hy, rfl⟩ := mem_edDilateSegs' hq
    have hne : x ≠ y := fun h => hpq (by rw [h])
    exact core.fam_disjoint B hB (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) hne
  Y_piece := by
    intro B hB p hp z hz
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    exact core.Y_piece B hB x hx hz.1
  segs_thickness := by
    intro B hB p hp
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    exact edDilate_hasThicknesses pres hB hx hrad hfloor
  segs_dims := by
    intro B hB p hp q hq
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    obtain ⟨y, hy, rfl⟩ := mem_edDilateSegs' hq
    exact thickness_segCarrierSetAt_le_two_nsmul one_le_edDilateConstant _ _ _ _
      (by positivity) (edDilate_mul_delta_le_quarter hrad)
  parent := by
    intro B hB i hi hne
    obtain ⟨x, hx, hix⟩ := core.parent B hB i hi hne
    exact ⟨(B, x), mem_edDilateSegs.2 ⟨rfl, hx⟩, hix⟩
  into := by
    intro B hB p hp i hi
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    intro z hz
    have hz' := core.into B hB x hx i hi hz
    exact ⟨hz', base_shade_subset_edDilateSet pres hB hx hz'⟩
  back := by
    intro B hB p hp
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    exact fun z hz => core.back B hB x hx hz.1
  segs_core := by
    intro B hB p hp i hi
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    exact edDilate_segs_core pres hB hx hfloor hi
  m := core.m
  Cm := core.Cm
  hCm := core.hCm
  fibre := by
    intro B hB p hp z hz
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    exact core.fibre B hB x hx z hz.1
  γ := (exists_deltaCovers cfg.hδ (edDilateBody core pres.tub)).choose
  cov := (exists_deltaCovers cfg.hδ (edDilateBody core pres.tub)).choose_spec.choose
  covCtr :=
    (exists_deltaCovers cfg.hδ (edDilateBody core pres.tub)).choose_spec.choose_spec.choose
  cov_isCover := fun _ _ p _ =>
    ⟨((exists_deltaCovers cfg.hδ
        (edDilateBody core pres.tub)).choose_spec.choose_spec.choose_spec.1 p).subset_iUnion,
      fun x => le_trans (((exists_deltaCovers cfg.hδ
        (edDilateBody core pres.tub)).choose_spec.choose_spec.choose_spec.1 p).card_filter_le
          x) hDfloor⟩
  cov_meets := fun _ _ p _ =>
    (exists_deltaCovers cfg.hδ
      (edDilateBody core pres.tub)).choose_spec.choose_spec.choose_spec.2 p
  segs_subset_ball := by
    intro B hB p hp
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    exact edDilate_segs_subset_ball pres hB hx hrad
  segs_scale := by
    intro B hB p hp
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    exact edDilate_segs_scale pres hB hx

end DilateCore

/-! ### The two quantitative clauses at the dilated carrier -/

/-- **`maxDensity` under a bounded enlargement of every member of the family.** If each body
grows to a body of at most `R` times its volume, the maximal density grows by at most `R`: the
numerator of every test density grows by `R` and the test set of the enlarged family is a subset
of that of the original. -/
theorem maxDensity_le_mul_of_volume_ratio {ι : Type*} (s : Finset ι)
    (W W' : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (R : ENNReal)
    (hsub : ∀ i ∈ s, W i ≤ W' i)
    (hvol : ∀ i ∈ s, volume (W' i).carrier ≤ R * volume (W i).carrier) :
    Kakeya.maxDensity s W' ≤ R * Kakeya.maxDensity s W := by
  classical
  rw [Kakeya.maxDensity_le_iff]
  intro K
  have hnum : ∑ i ∈ s.filter (fun i => W' i ≤ K), volume (W' i).carrier
      ≤ R * ∑ i ∈ s.filter (fun i => W i ≤ K), volume (W i).carrier := by
    calc ∑ i ∈ s.filter (fun i => W' i ≤ K), volume (W' i).carrier
        ≤ ∑ i ∈ s.filter (fun i => W' i ≤ K), R * volume (W i).carrier :=
          Finset.sum_le_sum (fun i hi => hvol i (Finset.mem_filter.1 hi).1)
      _ = R * ∑ i ∈ s.filter (fun i => W' i ≤ K), volume (W i).carrier := by
          rw [Finset.mul_sum]
      _ ≤ R * ∑ i ∈ s.filter (fun i => W i ≤ K), volume (W i).carrier := by
          have hsubset : s.filter (fun i => W' i ≤ K) ⊆ s.filter (fun i => W i ≤ K) := by
            intro i hi
            rw [Finset.mem_filter] at hi ⊢
            exact ⟨hi.1, le_trans (hsub i hi.1) hi.2⟩
          gcongr
  calc Kakeya.densityIn s W' K
      ≤ (R * ∑ i ∈ s.filter (fun i => W i ≤ K), volume (W i).carrier) / volume K.carrier := by
        rw [Kakeya.densityIn]
        gcongr
    _ = R * Kakeya.densityIn s W K := by rw [Kakeya.densityIn, mul_div_assoc]
    _ ≤ R * Kakeya.maxDensity s W := by gcongr; exact Kakeya.le_maxDensity s W K

section DilateClauses

variable {core : BallDataCore cfg} (pres : CapsulePresentation core)

/-- **`segs_density` at the dilated carrier.** The dilate multiplies the carrier's volume by at
most `16 K′₀² / c₃`, so a base density constant `c₀` with `16 K′₀² c₁ ≤ c₀ c₃` delivers the
caller's `c₁` at the dilated carrier. -/
theorem edDilate_segs_density {c₀ c₁ : NNReal}
    (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hrel : 16 * ((edDilateConstant : NNReal) : ENNReal) ^ 2 * (c₁ : ENNReal)
      ≤ (c₀ : ENNReal) * ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal))
    (hdens : ∀ B ∈ core.bs, ∀ p ∈ core.segs B,
      (c₀ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier ≤
        volume (core.Y p).shade)
    {B : core.bι} (hB : B ∈ core.bs) {x : core.σ} (hx : x ∈ core.segs B) :
    (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) *
        volume (edDilateBody core pres.tub (B, x)).carrier ≤
      volume (edDilateBody core pres.tub (B, x)).shade := by
  set θ : ENNReal := (cfg.δ : ENNReal) ^ (2 * cfg.η) with hθ
  set K : NNReal := edDilateConstant with hK
  have hbase := hdens B hB x hx
  rw [pres.carrier_eq B hB x hx] at hbase
  have hstep := segsDensity_of_segCarrierSetAt (K := K) (c₁ := c₀) (θ := θ)
    (cfg.T (pres.tub x)).toTube (core.ctr B) (L := (cfg.r₁ : ℝ) / 4)
    (by positivity) (two_mul_quarter_le_one cfg) (edDilate_mul_delta_le_quarter hrad) hbase
  have hfac0 : (16 : ENNReal) * ((K : NNReal) : ENNReal) ^ 2 ≠ 0 := by
    have : ((K : NNReal) : ENNReal) ≠ 0 := by
      simpa using (ne_of_gt (edDilateConstant_pos))
    positivity
  have hfactop : (16 : ENNReal) * ((K : NNReal) : ENNReal) ^ 2 ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (by simp))
  rw [edDilateBody_carrier, edDilate_shade_eq pres hB hx]
  refine (ENNReal.mul_le_mul_iff_left hfac0 hfactop).1 ?_
  calc (c₁ : ENNReal) * θ * volume (edDilateSet core pres.tub (B, x)) *
        ((16 : ENNReal) * ((K : NNReal) : ENNReal) ^ 2)
      = (16 * ((K : NNReal) : ENNReal) ^ 2 * (c₁ : ENNReal)) * θ *
          volume (edDilateSet core pres.tub (B, x)) := by ring
    _ ≤ ((c₀ : ENNReal) * ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal)) * θ *
          volume (edDilateSet core pres.tub (B, x)) := by gcongr
    _ = (c₀ : ENNReal) * ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal) * θ *
          volume (segCarrierSetAt K (cfg.T (pres.tub x)).toTube (core.ctr B)
            ((cfg.r₁ : ℝ) / 4)) := rfl
    _ ≤ 16 * ((K : NNReal) : ENNReal) ^ 2 * volume (core.Y x).shade := hstep
    _ = volume (core.Y x).shade * (16 * ((K : NNReal) : ENNReal) ^ 2) := by ring

/-- The volume price of the radius dilate, as a single `δ`-free ratio `16 K′₀² / c₃`. -/
noncomputable def edVolumeRatio : ENNReal :=
  16 * ((edDilateConstant : NNReal) : ENNReal) ^ 2 /
    ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal)

theorem c₃_ne_zero : ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal) ≠ 0 := by
  simpa using (Metric.lt_volume_convexHull.c_pos 3).ne'

theorem c₃_ne_top : ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal) ≠ ⊤ := by simp

/-- **`segs_dilation` at the dilated carrier.** The dilate costs the volume ratio
`edVolumeRatio = 16 K′₀² / c₃` and nothing else: the segment family and the ball are unchanged,
so the clause transfers with its constant multiplied by that ratio. -/
theorem edDilate_segs_dilation {Cdil : NNReal}
    (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hCdil : 16 * ((edDilateConstant : NNReal) : ENNReal) ^ 2 *
        (segsDilationConstant : ENNReal) ≤
      (Cdil : ENNReal) * ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal))
    (hdil : ∀ B ∈ core.bs, (cfg.r₁ : ENNReal) ^ 2 *
        Kakeya.maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) ≤
      (segsDilationConstant : ENNReal) *
        Kakeya.maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody))
    {B : core.bι} (hB : B ∈ core.bs) :
    (cfg.r₁ : ENNReal) ^ 2 *
        Kakeya.maxDensity (edDilateSegs core B)
          (fun p ↦ (edDilateBody core pres.tub p).toConvexSpaceBody) ≤
      (Cdil : ENNReal) * Kakeya.maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody) := by
  classical
  have hinj : ∀ x ∈ core.segs B, ∀ y ∈ core.segs B,
      ((B, x) : core.bι × core.σ) = (B, y) → x = y := by
    intro x _ y _ h
    exact (Prod.mk.injEq .. ▸ h).2
  have hre := maxDensity_image (core.segs B) (fun x => ((B, x) : core.bι × core.σ)) hinj
    (fun p => (edDilateBody core pres.tub p).toConvexSpaceBody)
  -- the ratio bound, member by member
  have hratio : Kakeya.maxDensity (core.segs B)
      (fun x => (edDilateBody core pres.tub (B, x)).toConvexSpaceBody) ≤
      edVolumeRatio * Kakeya.maxDensity (core.segs B)
        (fun x => (core.Y x).toConvexSpaceBody) := by
    refine maxDensity_le_mul_of_volume_ratio (core.segs B) _ _ edVolumeRatio ?_ ?_
    · intro x hx
      exact base_carrier_subset_edDilateSet pres hB hx
    · intro x hx
      have hvol := volume_segCarrierSetAt_le_mul_volume_segCarrierSet (K := edDilateConstant)
        (cfg.T (pres.tub x)).toTube (core.ctr B) (L := (cfg.r₁ : ℝ) / 4)
        (by positivity) (two_mul_quarter_le_one cfg) (edDilate_mul_delta_le_quarter hrad)
      have hcar : (core.Y x).carrier =
          segCarrierSet (cfg.T (pres.tub x)).toTube (core.ctr B) ((cfg.r₁ : ℝ) / 4) :=
        pres.carrier_eq B hB x hx
      rw [hcar]
      rw [edVolumeRatio, ENNReal.div_eq_inv_mul,
        show (((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal))⁻¹ *
            (16 * ((edDilateConstant : NNReal) : ENNReal) ^ 2) *
            volume (segCarrierSet (cfg.T (pres.tub x)).toTube (core.ctr B)
              ((cfg.r₁ : ℝ) / 4)) =
          (16 * ((edDilateConstant : NNReal) : ENNReal) ^ 2 *
            volume (segCarrierSet (cfg.T (pres.tub x)).toTube (core.ctr B)
              ((cfg.r₁ : ℝ) / 4))) /
            ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal) by
          rw [ENNReal.div_eq_inv_mul]; ring]
      exact (ENNReal.le_div_iff_mul_le (Or.inl c₃_ne_zero) (Or.inl c₃_ne_top)).2
        (by rw [mul_comm]; exact hvol)
  rw [edDilateSegs, hre]
  calc (cfg.r₁ : ENNReal) ^ 2 * Kakeya.maxDensity (core.segs B)
        (fun x => (edDilateBody core pres.tub (B, x)).toConvexSpaceBody)
      ≤ (cfg.r₁ : ENNReal) ^ 2 * (edVolumeRatio * Kakeya.maxDensity (core.segs B)
          (fun x => (core.Y x).toConvexSpaceBody)) := by gcongr
    _ = edVolumeRatio * ((cfg.r₁ : ENNReal) ^ 2 * Kakeya.maxDensity (core.segs B)
          (fun x => (core.Y x).toConvexSpaceBody)) := by ring
    _ ≤ edVolumeRatio * ((segsDilationConstant : ENNReal) *
          Kakeya.maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)) :=
        mul_le_mul_right (hdil B hB) _
    _ = (edVolumeRatio * (segsDilationConstant : ENNReal)) *
          Kakeya.maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody) := by ring
    _ ≤ (Cdil : ENNReal) *
          Kakeya.maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody) := by
        gcongr
        rw [edVolumeRatio, ENNReal.div_eq_inv_mul,
          show (((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal))⁻¹ *
              (16 * ((edDilateConstant : NNReal) : ENNReal) ^ 2) *
              (segsDilationConstant : ENNReal) =
            (16 * ((edDilateConstant : NNReal) : ENNReal) ^ 2 *
              (segsDilationConstant : ENNReal)) /
              ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal) by
            rw [ENNReal.div_eq_inv_mul]; ring]
        exact ENNReal.div_le_of_le_mul hCdil

end DilateClauses

/-! ### The capsule presentation of a capsule core -/

/-- A segment of a capsule core with a positive `segs_density` clause has non-empty shading;
this is what supplies `CapsulePresentation.meets`. -/
theorem shade_nonempty_of_capsule_density {core : BallDataCore cfg} {c₁ : NNReal} (hc₁ : 0 < c₁)
    (hdens : ∀ B ∈ core.bs, ∀ p ∈ core.segs B,
      (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier ≤
        volume (core.Y p).shade) :
    ∀ B ∈ core.bs, ∀ p ∈ core.segs B, ((core.Y p).shade).Nonempty := by
  intro B hB p hp
  refine shade_nonempty_of_segs_density core
    (c := (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) ?_ hB hp (hdens B hB p hp)
  have hc₁' : ((c₁ : NNReal) : ENNReal) ≠ 0 := by simpa using ne_of_gt hc₁
  have hθ : ((cfg.δ : ENNReal)) ^ (2 * cfg.η) ≠ 0 := by
    refine ne_of_gt (ENNReal.rpow_pos ?_ (by simp))
    exact_mod_cast cfg.hδ
  simp only [ne_eq, mul_eq_zero, not_or]
  exact ⟨hc₁', hθ⟩

/-- **The capsule presentation exists.** `Kakeya.VeryNotSticky.HasCapsuleSegments` is an
existential; the fold needs the witness as a function, so it is skolemised here. The parent
family being a singleton is what makes the choice canonical. -/
theorem nonempty_capsulePresentation (core : BallDataCore cfg) (hsne : cfg.s.Nonempty)
    (hcap : HasCapsuleSegments core)
    (hshade : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, ((core.Y p).shade).Nonempty)
    (hball16 : ∀ B ∈ core.bs, core.P B ⊆ ball (core.ctr B) ((cfg.r₁ : ℝ) / 16)) :
    Nonempty (CapsulePresentation core) := by
  classical
  obtain ⟨i₀, -⟩ := hsne
  have hkey : ∀ B ∈ core.bs, ∀ p ∈ core.segs B,
      (if h : (core.fam p).Nonempty then h.choose else i₀) ∈ cfg.s ∧
      (core.Y p).carrier = segCarrierSet
        (cfg.T (if h : (core.fam p).Nonempty then h.choose else i₀)).toTube
        (core.ctr B) ((cfg.r₁ : ℝ) / 4) ∧
      (core.Y p).shade ⊆
        (cfg.T (if h : (core.fam p).Nonempty then h.choose else i₀)).shade ∩ core.P B ∧
      core.fam p = {if h : (core.fam p).Nonempty then h.choose else i₀} := by
    intro B hB p hp
    obtain ⟨i, hi, hcar, hsh, hfam⟩ := hcap B hB p hp
    have hne : (core.fam p).Nonempty := ⟨i, by rw [hfam]; exact Finset.mem_singleton_self i⟩
    have hsing : ∀ j ∈ core.fam p, j = i := by
      intro j hj
      rw [hfam, Finset.mem_singleton] at hj
      exact hj
    have hval : (if h : (core.fam p).Nonempty then h.choose else i₀) = i := by
      rw [dif_pos hne]
      exact hsing _ hne.choose_spec
    rw [hval]
    exact ⟨hi, hcar, hsh, hfam⟩
  exact ⟨{ tub := fun p => if h : (core.fam p).Nonempty then h.choose else i₀
           tub_mem := fun B hB p hp => (hkey B hB p hp).1
           carrier_eq := fun B hB p hp => (hkey B hB p hp).2.1
           fam_eq := fun B hB p hp => (hkey B hB p hp).2.2.2
           meets := by
             intro B hB p hp
             obtain ⟨z, hz⟩ := hshade B hB p hp
             exact ⟨z, (hkey B hB p hp).2.2.1 hz⟩
           ball16 := hball16 }⟩

section DilateCoreSimp

variable {core : BallDataCore cfg} (pres : CapsulePresentation core)
  (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
  (hfloor : edSegmentsConstant ≤ core.C₀) (hDfloor : ballCoverConstant ≤ core.D)

@[simp] theorem edDilateCore_C₀ :
    (edDilateCore pres hrad hfloor hDfloor).C₀ = core.C₀ := rfl

@[simp] theorem edDilateCore_D :
    (edDilateCore pres hrad hfloor hDfloor).D = core.D := rfl

@[simp] theorem edDilateCore_bs :
    (edDilateCore pres hrad hfloor hDfloor).bs = core.bs := rfl

@[simp] theorem edDilateCore_segs (B : core.bι) :
    (edDilateCore pres hrad hfloor hDfloor).segs B = edDilateSegs core B := rfl

@[simp] theorem edDilateCore_Y (p : core.bι × core.σ) :
    (edDilateCore pres hrad hfloor hDfloor).Y p = edDilateBody core pres.tub p := rfl

end DilateCoreSimp

/-! ### The three floor constants -/

/-- The base density constant the dilated presentation needs: `16 K′₀² c₁ / c₃`. -/
noncomputable def edBaseDensityConstant (c₁ : NNReal) : NNReal :=
  16 * edDilateConstant ^ 2 * c₁ / (Metric.lt_volume_convexHull.c 3)

/-- **The `c₁` floor of  §G-1, at the value the *homothety-free* dilate costs**:
`64 K′₀² / c₃`. The constant `edDensityConstant = 4 K′²` prices only the `K′²` growth of the
carrier and not the inscribed-simplex constant `c₃` of the capsule's volume lower bound; the
compiled ratio is `Kakeya.VeryNotSticky.volume_segCarrierSetAt_le_mul_volume_segCarrierSet`,
`c₃ |At| ≤ 16 K′² |cap|`, so the floor is `4 · 16 K′²/c₃ = 64 K′²/c₃`. -/
noncomputable def edDensityFloorConstant : NNReal :=
  64 * edDilateConstant ^ 2 / (Metric.lt_volume_convexHull.c 3)

/-- **The `Cdil` floor**: the dilate multiplies every carrier volume by at most `16 K′₀²/c₃`, so
the existing `segsDilationConstant` of the capsule core becomes `16 K′₀²/c₃ · segsDilationConstant`
at the dilated carrier. This is a *fourth* amendment to §G-1's floor list, and unlike the other
three it is on the target's **conclusion**, so it is carried here as a binder with a floor. -/
noncomputable def edDilationFloorConstant : NNReal :=
  16 * edDilateConstant ^ 2 * segsDilationConstant / (Metric.lt_volume_convexHull.c 3)


/-! ### The two floors the dilated carrier's *geometry* forces -/

/-- **The `C₀` floor the dilated core-line clause forces**: `4 K′₀²`. The clause at the dilated
carrier asks the `K′₀`-dilated capsule of `i` to lie within `C₀ δ` of the core line of a
comparable `j`, and R-a at radius `K′₀ δ` gives it at `K′₀ · K′₀ δ`. This is a
**hypothesis-floor** move of exactly  §G-1's kind, on a caller-chosen constant that
already carries a floor; it implies `edSegmentsConstant ≤ C₀`. -/
noncomputable def edFoldSegmentsConstant : NNReal := 4 * edDilateConstant ^ 2

/-- **The radius floor the dilated class count forces**: `8 K′₀²`, because the cone radius of the
count at the dilated carrier is `ρ = 8 K′₀² δ / r₁` and `card_cone_le` needs `ρ ≤ 1`. It implies
`edRadiusConstant · δ ≤ r₁`. -/
noncomputable def edFoldRadiusConstant : NNReal := 8 * edDilateConstant ^ 2

theorem edSegmentsConstant_le_edFoldSegmentsConstant :
    edSegmentsConstant ≤ edFoldSegmentsConstant := by
  rw [edSegmentsConstant, edFoldSegmentsConstant, sq]
  have hK : (1 : NNReal) ≤ edDilateConstant := one_le_edDilateConstant
  calc 4 * edDilateConstant = 4 * (1 * edDilateConstant) := by ring
    _ ≤ 4 * (edDilateConstant * edDilateConstant) := by gcongr

theorem edDilateConstant_sq_le_edFoldSegmentsConstant :
    edDilateConstant ^ 2 ≤ edFoldSegmentsConstant := by
  rw [edFoldSegmentsConstant]
  calc edDilateConstant ^ 2 = 1 * edDilateConstant ^ 2 := (one_mul _).symm
    _ ≤ 4 * edDilateConstant ^ 2 := by gcongr; norm_num

theorem edRadiusConstant_le_edFoldRadiusConstant :
    edRadiusConstant ≤ edFoldRadiusConstant := by
  rw [edRadiusConstant, edFoldRadiusConstant, sq]
  have hK : (1 : NNReal) ≤ edDilateConstant := one_le_edDilateConstant
  calc 8 * edDilateConstant = 8 * (1 * edDilateConstant) := by ring
    _ ≤ 8 * (edDilateConstant * edDilateConstant) := by gcongr

theorem radiusFloor_of_foldRadiusFloor
    (h : ((edFoldRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) :
    ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) := by
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (cfg.δ).coe_nonneg) h
  exact_mod_cast edRadiusConstant_le_edFoldRadiusConstant

theorem segmentsFloor_of_foldSegmentsFloor {C₀ : NNReal} (h : edFoldSegmentsConstant ≤ C₀) :
    edSegmentsConstant ≤ C₀ :=
  le_trans edSegmentsConstant_le_edFoldSegmentsConstant h

theorem four_le_edFoldSegmentsConstant : 4 ≤ edFoldSegmentsConstant :=
  le_trans four_le_edSegmentsConstant edSegmentsConstant_le_edFoldSegmentsConstant

theorem c₃_ne_zero' : (Metric.lt_volume_convexHull.c 3 : NNReal) ≠ 0 :=
  (Metric.lt_volume_convexHull.c_pos 3).ne'

theorem edBaseDensityConstant_pos {c₁ : NNReal} (hc₁ : 0 < c₁) :
    0 < edBaseDensityConstant c₁ := by
  rw [edBaseDensityConstant]
  have hK : (0 : NNReal) < edDilateConstant := lt_of_lt_of_le zero_lt_one one_le_edDilateConstant
  have hc₃ : (0 : NNReal) < (Metric.lt_volume_convexHull.c 3 : NNReal) :=
    Metric.lt_volume_convexHull.c_pos 3
  positivity

theorem four_mul_edBaseDensityConstant {c₁ : NNReal} :
    4 * edBaseDensityConstant c₁ = edDensityFloorConstant * c₁ := by
  rw [edBaseDensityConstant, edDensityFloorConstant, div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem edBaseDensityConstant_mul_c₃ {c₁ : NNReal} :
    edBaseDensityConstant c₁ * (Metric.lt_volume_convexHull.c 3 : NNReal)
      = 16 * edDilateConstant ^ 2 * c₁ := by
  rw [edBaseDensityConstant, div_mul_cancel₀ _ c₃_ne_zero']

theorem edDilationFloorConstant_mul_c₃ :
    edDilationFloorConstant * (Metric.lt_volume_convexHull.c 3 : NNReal)
      = 16 * edDilateConstant ^ 2 * segsDilationConstant := by
  rw [edDilationFloorConstant, div_mul_cancel₀ _ c₃_ne_zero']


/-! ### The step-5/6 core, with the shrunken-ball localisation exported -/

open scoped Classical in
/-- `Kakeya.VeryNotSticky.exists_core_segsDensity_capsule_of_cover` with the **shrunken-ball
localisation of the pieces** added to the conclusion; the proof is that producer's, with one
extra `rfl`-chase. It is needed because the dilated re-presentation's `segs_subset_ball` margin
is `r₁/4 + r₁/16 + K′₀ δ ≤ r₁` and the `r₁/16` is not recoverable from a `BallDataCore`'s own
fields. The original's docstring: `restrictBalls` and `markovDyadicTierCore` leave `Y` and
`fam` untouched and only shrink `bs` and `segs`, so every segment of the tier is still one of
T3's capsules. -/
theorem exists_core_segsDensity_capsule_ball16_of_cover (cfg : VeryNotSticky.{u}) {bι : Type u}
    {C₀ : NNReal} (hC₀ : 4 ≤ C₀) {D : ℕ} (hD : ballCoverConstant ≤ D)
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (bs : Finset bι) (ctr : bι → EuclideanSpace ℝ (Fin 3))
    (P : bι → Set (EuclideanSpace ℝ (Fin 3)))
    (hbsne : bs.Nonempty)
    (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
    (hPball : ∀ B ∈ bs, P B ⊆ closedBall (ctr B) (cfg.r₁ : ℝ))
    (hPdisj : (bs : Set bι).PairwiseDisjoint P)
    (hPmeas : ∀ B, MeasurableSet (P B))
    (hPcov : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B)
    (hoverlap : ∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
      (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant)
    (hPne : ∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty)
    {c₁ : NNReal} (hc₁ : 0 < c₁)
    (hc₁' : 4 * c₁ * (ballCoverConstant : NNReal) ≤ 1) :
    ∃ core : BallDataCore cfg,
      core.C₀ = C₀ ∧ core.D = D ∧
      (∀ B ∈ core.bs, ∀ p ∈ core.segs B,
        (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier ≤
          volume (core.Y p).shade) ∧
      (∀ B ∈ core.bs, (cfg.r₁ : ENNReal) ^ 2 *
          Kakeya.maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) ≤
        (segsDilationConstant : ENNReal) *
          Kakeya.maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)) ∧
      (∀ B ∈ core.bs, ∀ p ∈ core.segs B, ∃ i ∈ cfg.s,
        (core.Y p).carrier =
            segCarrierSet (cfg.T i).toTube (core.ctr B) ((cfg.r₁ : ℝ) / 4) ∧
          (core.Y p).shade ⊆ (cfg.T i).shade ∩ core.P B ∧
          core.fam p = {i}) ∧
      (∀ B ∈ core.bs, core.P B ⊆ ball (core.ctr B) ((cfg.r₁ : ℝ) / 16)) := by
  classical
  set core₀ := ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj hPmeas
    hPcov hoverlap hPne with hcore₀
  have hbs₀ : core₀.bs = bs := rfl
  have hsegs₀ : core₀.segs = segsOfCover cfg P := rfl
  have hY₀ : core₀.Y = segBodyOfCover cfg ctr P hPmeas := rfl
  have hP₀ : core₀.P = P := rfl
  have hctr₀ : core₀.ctr = ctr := rfl
  have hsne : cfg.s.Nonempty := by
    obtain ⟨B, hB⟩ := hbsne
    obtain ⟨x, -, hxs⟩ := hPne B hB
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.mp hxs
    exact ⟨i, hi⟩
  have hSm : ∀ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).shade
      = ballYgMass core₀ B := fun B hB =>
    sum_segShade_eq_ballYgMass_aux cfg hPmeas hδr hPball16 hB
  have hCtop : ∑ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).carrier ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (sum_sum_segCarrier_le cfg hPmeas hδr hPball16 hoverlap)
    exact ENNReal.mul_ne_top (by simp) (sum_volume_carrier_ne_top cfg)
  have hS0eq : ∑ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).shade
      = ∑ i ∈ cfg.s, volume (cfg.T i).shade :=
    sum_sum_segShade_eq cfg hPmeas hδr hPball16 hPdisj hPcov
  have hS0 : ∑ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).shade ≠ 0 := by
    rw [hS0eq]
    exact ne_of_gt (sum_volume_shade_pos_of_nonempty cfg hsne)
  have hfull : 4 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
      ∑ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).carrier ≤
      ∑ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).shade := by
    rw [hbs₀, hsegs₀, hY₀]
    exact segs_fullness_of_cover cfg hPmeas hδr hPball16 hPdisj hPcov hoverlap hc₁'
  obtain ⟨bs', hsub, hne, hret, hheavy⟩ :=
    exists_heavyBalls_core core₀ hSm hCtop hS0 hfull
  set core₁ := core₀.restrictBalls bs' hsub hne (K := 2) (by norm_num) hret with hcore₁
  have hfull₁ : ∀ B ∈ core₁.bs, 2 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
      ∑ p ∈ core₁.segs B, volume (core₁.Y p).carrier ≤
      ∑ p ∈ core₁.segs B, volume (core₁.Y p).shade := hheavy
  obtain ⟨k, hkne, hkret⟩ := exists_markovDyadicTier_data core₁ hc₁ hfull₁
  refine ⟨markovDyadicTierCore core₁ c₁ k hkne hkret, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact markovDyadicTierCore_segs_density core₁ c₁ k hkne hkret
  · exact tierCore_segs_dilation core₁ _ _ _ _ _
      (restrictBalls_segs_dilation core₀ bs' hsub hne (by norm_num) hret
        (segs_dilation_ballDataCoreOfCover (cfg := cfg) (hC₀ := hC₀) (hD := hD) (hδr := hδr)
          (bs := bs) (ctr := ctr) (P := P) (hbsne := hbsne) (hPball16 := hPball16)
          (hPball := hPball) (hPdisj := hPdisj) (hPmeas := hPmeas) (hPcov := hPcov)
          (hoverlap := hoverlap) (hPne := hPne)))
  · intro B hB p hp
    have hp₀ : p ∈ core₀.segs B := markovDyadicTier_subset core₁ c₁ k B hp
    have hB₀ : B ∈ core₀.bs := hsub hB
    rw [hsegs₀] at hp₀
    obtain ⟨i, hi, -, rfl⟩ := (mem_segsOfCover cfg P B p).1 hp₀
    refine ⟨i, hi, rfl, ?_, rfl⟩
    intro z hz
    exact ⟨hz.1.1, hz.1.2⟩
  · intro B hB
    exact hPball16 B (hsub hB)


/-! ### Why the carrier is the radius dilate: the homothety dilate does not fit in its ball -/

theorem four_lt_edDilateConstant : 4 < edDilateConstant := by
  rw [← NNReal.coe_lt_coe, coe_edDilateConstant, edComparabilityConstant_eq]
  have hc : (0 : ℝ) < ((Tube.le_volume.c 3 : NNReal) : ℝ) := by
    exact_mod_cast Tube.le_volume.c_pos 3
  have hpos : (0 : ℝ) ≤ 2 * 4 ^ 3 / ((Tube.le_volume.c 3 : NNReal) : ℝ) := by positivity
  push_cast
  linarith

/-- **The homothety dilate of a capsule does not fit in a ball of radius `R < K L`.** Its core
window has half-length `K L`, so its diameter is at least `2 K L`. -/
theorem not_segCarrierSetHom_subset_closedBall {δ : NNReal} (T : Tube δ E3) (c : E3) {L : ℝ}
    (hL : 0 < L) {K : ℝ} (hK : 0 < K) {R : ℝ} (hR : R < K * L) :
    ¬ (segCarrierSetHom K T c L ⊆ closedBall c R) := by
  intro hsub
  rw [segCarrierSetHom_eq T c hK] at hsub
  have hmemA : corePt T (segStart T c L + L - K * L) ∈
      cthickening (K * (δ : ℝ)) (segment ℝ (corePt T (segStart T c L + L - K * L))
        (corePt T (segStart T c L + L + K * L))) :=
    Metric.self_subset_cthickening _ (left_mem_segment ℝ _ _)
  have hmemB : corePt T (segStart T c L + L + K * L) ∈
      cthickening (K * (δ : ℝ)) (segment ℝ (corePt T (segStart T c L + L - K * L))
        (corePt T (segStart T c L + L + K * L))) :=
    Metric.self_subset_cthickening _ (right_mem_segment ℝ _ _)
  have h1 := Metric.mem_closedBall.1 (hsub hmemA)
  have h2 := Metric.mem_closedBall.1 (hsub hmemB)
  have hd : dist (corePt T (segStart T c L + L - K * L))
      (corePt T (segStart T c L + L + K * L)) = 2 * (K * L) := by
    rw [dist_corePt,
      show segStart T c L + L - K * L - (segStart T c L + L + K * L) = -(2 * (K * L)) by ring,
      abs_neg, abs_of_nonneg (by positivity)]
  have htri := dist_triangle (corePt T (segStart T c L + L - K * L)) c
    (corePt T (segStart T c L + L + K * L))
  rw [hd, dist_comm c] at htri
  linarith

/-- **`BallDataCore.segs_subset_ball` refutes the homothety carrier.** At `L = r₁/4` and
`K = K′₀ > 4` the dilated capsule has half-length `K′₀ r₁/4 > r₁`, so it cannot lie in the ball
of radius `r₁` the field demands — for *every* configuration and every tube. This is the compiled
reason the S-4 carrier is the **radius** dilate `Kakeya.VeryNotSticky.segCarrierSetAt` and not
the homothety dilate `Kakeya.VeryNotSticky.segCarrierSetHom`, whatever the comparability clause
is stated at. -/
theorem not_segCarrierSetHom_subset_closedBall_ctr (cfg : VeryNotSticky.{u})
    (T : Tube cfg.δ E3) (c : E3) :
    ¬ (segCarrierSetHom ((edDilateConstant : NNReal) : ℝ) T c ((cfg.r₁ : ℝ) / 4) ⊆
      closedBall c (cfg.r₁ : ℝ)) := by
  have hr : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  have h4 : (4 : ℝ) < ((edDilateConstant : NNReal) : ℝ) := by
    exact_mod_cast four_lt_edDilateConstant
  refine not_segCarrierSetHom_subset_closedBall T c (by positivity) (by linarith) ?_
  nlinarith

/-- `c₃ = Metric.lt_volume_convexHull.c 3 = 1/6`, the inscribed-simplex constant in dimension
three. -/
theorem c₃_eq : (Metric.lt_volume_convexHull.c 3 : NNReal) = (6 : NNReal)⁻¹ := by
  rw [Metric.lt_volume_convexHull.c]
  norm_num [Nat.factorial]

/-- **The two floor amendments are forced, measured.**  §G-1's `edDensityConstant`
= `4 K′²` prices only the `K′²` growth of the carrier; the compiled ratio carries the
inscribed-simplex constant as well, and `edDensityFloorConstant = 64 K′²/c₃ = 384 K′²` strictly
exceeds it. -/
theorem edDensityConstant_lt_edDensityFloorConstant :
    edDensityConstant < edDensityFloorConstant := by
  have hK : (4 : NNReal) < edDilateConstant := four_lt_edDilateConstant
  rw [← NNReal.coe_lt_coe, edDensityConstant, edDensityFloorConstant, c₃_eq,
    div_eq_mul_inv, inv_inv]
  have hKR : (4 : ℝ) < ((edDilateConstant : NNReal) : ℝ) := by exact_mod_cast hK
  push_cast
  nlinarith [sq_nonneg (((edDilateConstant : NNReal) : ℝ) - 4)]

/-- **The `Cdil` amendment is forced, measured.** The floor strictly exceeds the existing
`segsDilationConstant`, so the target's dilation clause cannot be delivered at its own constant
from the dilated carrier — this is the fourth amendment, and it is on the conclusion. -/
theorem segsDilationConstant_lt_edDilationFloorConstant :
    segsDilationConstant < edDilationFloorConstant := by
  have hC : (0 : NNReal) < segsDilationConstant :=
    lt_of_lt_of_le zero_lt_one one_le_segsDilationConstant
  have hK : (4 : NNReal) < edDilateConstant := four_lt_edDilateConstant
  rw [← NNReal.coe_lt_coe, edDilationFloorConstant, c₃_eq, div_eq_mul_inv, inv_inv]
  have hCR : (0 : ℝ) < ((segsDilationConstant : NNReal) : ℝ) := by exact_mod_cast hC
  have hKR : (4 : ℝ) < ((edDilateConstant : NNReal) : ℝ) := by exact_mod_cast hK
  push_cast
  nlinarith [sq_nonneg (((edDilateConstant : NNReal) : ℝ) - 4)]

/-! ### Satisfiability controls for the three remaining obligations -/

/-- **Non-vacuity control for the two comparability obligations at the dilated carrier.** If the
dilated capsules of every ball are already pairwise essentially distinct, both hold: the existing
`Kakeya.VeryNotSticky.edClass_inputs_of_pairwise_essDistinct` applies verbatim to the dilated
re-presentation. So the two hypotheses are not self-contradictory. -/
theorem edDilateCore_inputs_of_pairwise_essDistinct {core : BallDataCore cfg}
    (pres : CapsulePresentation core)
    (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hfloor : edSegmentsConstant ≤ core.C₀) (hDfloor : ballCoverConstant ≤ core.D)
    (hED : ∀ B ∈ core.bs, (edDilateSegs core B : Set (core.bι × core.σ)).Pairwise
      fun p q => IsEssentiallyDistinct (edDilateSet core pres.tub p)
        (edDilateSet core pres.tub q)) :
    EDClassContainment (edDilateCore pres hrad hfloor hDfloor) ∧
      EDClassCore (edDilateCore pres hrad hfloor hDfloor) :=
  edClass_inputs_of_pairwise_essDistinct _ hED

open scoped Classical in
/-- **Satisfiability control for the multiplicity obligation**: it always holds at
`M = #𝕋`. This is a *control*, not a producer — the constant depends on `cfg`, which is exactly
what  §G-3 forbids for the `∀ᶠ δ` device — but it shows the clause is not vacuous. -/
theorem edClassMult_card (core : BallDataCore cfg) :
    EDClassMult core ((cfg.s.card : ℕ) : NNReal) := by
  classical
  intro B hB x _ z
  have hsub : (edFam core B x).filter (fun i => z ∈ core.Yg i) ⊆ cfg.s := by
    intro i hi
    obtain ⟨q, hq, hiq⟩ := mem_edFam.1 (Finset.mem_filter.1 hi).1
    exact core.fam_subset B hB q (mem_edClass.1 hq).1 hiq
  have hcard := Finset.card_le_card hsub
  calc ((((edFam core B x).filter (fun i => z ∈ core.Yg i)).card : ℕ) : ENNReal)
      ≤ ((cfg.s.card : ℕ) : ENNReal) := by exact_mod_cast hcard
    _ = ((((cfg.s.card : ℕ) : NNReal)) : ENNReal) := by simp

/-- **The compiled class count plugs into the exit binder.** With
`M = edClassCountConstant · δ^{-(η + 2 exscal)}` — the value
`Kakeya.VeryNotSticky.capsuleHomDilateCount_of_radiusFloor` produces from `cfg.maxDensity_le` —
the hypothesis `hMexit` of the target is exactly the explicit fibre budget. -/
theorem edClassCount_le_exit {Bfib : ENNReal}
    (hexit : (edClassCountConstant : ENNReal) *
      (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) ≤ Bfib) :
    ((edClassCountConstant * cfg.δ ^ (-(cfg.η + 2 * cfg.exscal)) : NNReal) : ENNReal) ≤ Bfib :=
  le_trans classCount_le_fibreBudget hexit

/-! ### The three obligations in capsule form at the dilated carrier

The existing reductions `Kakeya.VeryNotSticky.edClassContainment_of_capsule`,
`edClassCore_of_capsule`, `edClassMult_of_capsule` state (C1)/(C2)/(C3) for the **undilated**
capsule. These are their analogues for the dilated re-presentation: the exact
Euclidean-geometry statements about two `K′₀`-dilated capsules and a piece of the ball cover
that discharge the three hypotheses of
`Kakeya.VeryNotSticky.exists_core_edSegments_of_cover_floor`. -/

theorem volume_segCarrierSetAt_ne_zero {δ : NNReal} (hδ : 0 < δ) (K : NNReal) (hK : 1 ≤ K)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ}
    (hL : 0 ≤ L) : volume (segCarrierSetAt K T c L) ≠ 0 :=
  fun h => volume_segCarrierSet_ne_zero hδ T c hL
    (measure_mono_null (segCarrierSet_subset_segCarrierSetAt hK T c L) h)

theorem volume_segCarrierSetAt_ne_top {δ : NNReal} (K : NNReal)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ}
    (hL : 0 ≤ L) : volume (segCarrierSetAt K T c L) ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (measure_mono (segCarrierSetAt_subset_closedBall K T c hL))
    measure_closedBall_lt_top)

/-- A dilated capsule is never essentially distinct from itself. -/
theorem not_isEssentiallyDistinct_segCarrierSetAt_self {δ : NNReal} (hδ : 0 < δ) {K : NNReal}
    (hK : 1 ≤ K) (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3))
    {L : ℝ} (hL : 0 ≤ L) :
    ¬ IsEssentiallyDistinct (segCarrierSetAt K T c L) (segCarrierSetAt K T c L) :=
  not_isEssentiallyDistinct_self (volume_segCarrierSetAt_ne_zero hδ K hK T c hL)
    (volume_segCarrierSetAt_ne_top K T c hL)

section CapsuleFormDilate

variable {core : BallDataCore cfg} (pres : CapsulePresentation core)
  (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
  (hfloor : edSegmentsConstant ≤ core.C₀) (hDfloor : ballCoverConstant ≤ core.D)

/-- **(C1) at the dilated carrier ⇒ `EDClassContainment`.** The geometric statement is: the part
of a comparable tube's capsule inside the piece lies in the representative's `K′₀`-dilate, with
comparability *measured at the dilate*. -/
theorem edClassContainment_dilate_of_capsule
    (hgeom : ∀ B ∈ core.bs, ∀ i ∈ cfg.s, ∀ j ∈ cfg.s,
      ¬ IsEssentiallyDistinct (ballCapsuleAt core edDilateConstant B i)
          (ballCapsuleAt core edDilateConstant B j) →
        ballCapsule core B j ∩ core.P B ⊆ ballCapsuleAt core edDilateConstant B i) :
    EDClassContainment (edDilateCore pres hrad hfloor hDfloor) := by
  intro B hB p hp q hq hne
  obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
  obtain ⟨y, hy, rfl⟩ := mem_edDilateSegs' hq
  refine subset_trans ?_
    (hgeom B hB (pres.tub x) (pres.tub_mem B hB x hx) (pres.tub y) (pres.tub_mem B hB y hy) hne)
  intro z hz
  refine ⟨?_, core.Y_piece B hB y hy hz.1⟩
  have h1 : z ∈ (core.Y y).carrier := (core.Y y).shade_subset hz.1
  rw [pres.carrier_eq B hB y hy] at h1
  exact h1

/-- **(C2) at the dilated carrier ⇒ `EDClassCore`.** The geometric statement is: two dilated
capsules that are not essentially distinct are contained in each other's `2 K′₀`-dilate, which
the floor `edSegmentsConstant ≤ C₀` pays for through
`Kakeya.VeryNotSticky.two_mul_edDilateConstant_le_of_floor`. -/
theorem edClassCore_dilate_of_capsule
    (hgeom : ∀ B ∈ core.bs, ∀ i ∈ cfg.s, ∀ j ∈ cfg.s,
      ¬ IsEssentiallyDistinct (ballCapsuleAt core edDilateConstant B i)
          (ballCapsuleAt core edDilateConstant B j) →
        ballCapsuleAt core edDilateConstant B i ⊆
          ballCapsuleAt core (2 * edDilateConstant) B j) :
    EDClassCore (edDilateCore pres hrad hfloor hDfloor) := by
  intro B hB p hp q hq hne i hi
  obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
  obtain ⟨y, hy, rfl⟩ := mem_edDilateSegs' hq
  rw [show (edDilateCore pres hrad hfloor hDfloor).fam (B, y) = core.fam y from rfl,
    pres.fam_eq B hB y hy, Finset.mem_singleton] at hi
  subst hi
  refine ⟨corePt (cfg.T (pres.tub y)).toTube
    (segStart (cfg.T (pres.tub y)).toTube (core.ctr B) ((cfg.r₁ : ℝ) / 4)), ?_⟩
  refine subset_trans
    (hgeom B hB (pres.tub x) (pres.tub_mem B hB x hx) (pres.tub y) (pres.tub_mem B hB y hy) hne)
    ?_
  refine segCarrierSetAt_subset_cthickening_line _ _ _ (by positivity) ?_
  have h : ((2 * edDilateConstant : NNReal) : ℝ) ≤ ((core.C₀ : NNReal) : ℝ) := by
    exact_mod_cast two_mul_edDilateConstant_le_of_floor hfloor
  exact mul_le_mul_of_nonneg_right h (cfg.δ).coe_nonneg


/-! ### Obligation (C2) at the dilated carrier: **PROVED** -/

/-- **R-a at the dilated carrier**, in `ballCapsuleAt` form: two `K`-dilated capsules of one ball
that are not essentially distinct each lie in the `K′₀`-homothety dilate of the other. -/
theorem ballCapsuleAt_subset_hom_of_not_essDistinct (core : BallDataCore cfg) {K : NNReal}
    (hK : 0 < K) (hKδ : (K : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 2)
    (B : core.bι) (i j : cfg.ι)
    (hne : ¬ IsEssentiallyDistinct (ballCapsuleAt core K B i) (ballCapsuleAt core K B j)) :
    ballCapsuleAt core K B j ⊆
      (AffineMap.homothety
        (capsuleCentre (cfg.T i).toTube (core.ctr B) ((cfg.r₁ : ℝ) / 4))
        edComparabilityConstant) '' (ballCapsuleAt core K B i) := by
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  exact segCarrierSetAt_subset_hom_of_not_essDistinct cfg.hδ hK (cfg.T i).toTube
    (cfg.T j).toTube (core.ctr B) (core.ctr B) (by positivity) (by linarith) hne

/-- **The core-line clause at the dilated carrier, discharged**: a `K`-dilated capsule lies within
`K′₀ K δ` of the core line of every tube it is not essentially distinct from. -/
theorem ballCapsuleAt_subset_cthickening_ballCoreLine (core : BallDataCore cfg) {K : NNReal}
    (hK : 0 < K) (hKδ : (K : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 2)
    (B : core.bι) (i j : cfg.ι)
    (hne : ¬ IsEssentiallyDistinct (ballCapsuleAt core K B i) (ballCapsuleAt core K B j))
    {C : ℝ} (hC : edComparabilityConstant * ((K : ℝ) * (cfg.δ : ℝ)) ≤ C) :
    ballCapsuleAt core K B i ⊆ cthickening C (ballCoreLine core B j) := by
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  have hne' : ¬ IsEssentiallyDistinct (ballCapsuleAt core K B j) (ballCapsuleAt core K B i) :=
    fun h => hne (isEssentiallyDistinct_symm h)
  refine subset_trans (ballCapsuleAt_subset_hom_of_not_essDistinct core hK hKδ B j i hne') ?_
  exact segCarrierSetAtHom_subset_cthickening_line
    (le_of_lt edComparabilityConstant_pos) K (cfg.T j).toTube (core.ctr B) (by positivity) hC

/-- **`EDClassCore` at the dilated carrier — PROVED, from the two floors alone.** No hypothesis
beyond `edFoldSegmentsConstant ≤ C₀` and the radius floor; in particular no comparability
assumption. -/
theorem edClassCore_dilate {core : BallDataCore cfg} (pres : CapsulePresentation core)
    (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hfloor : edSegmentsConstant ≤ core.C₀) (hDfloor : ballCoverConstant ≤ core.D)
    (hfloor2 : edFoldSegmentsConstant ≤ core.C₀) :
    EDClassCore (edDilateCore pres hrad hfloor hDfloor) := by
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  have hKδ : ((edDilateConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 2 := by
    have := edDilate_mul_delta_le_eighth hrad
    linarith
  have hC : edComparabilityConstant *
      (((edDilateConstant : NNReal) : ℝ) * (cfg.δ : ℝ)) ≤ ((core.C₀ : NNReal) : ℝ) *
        (cfg.δ : ℝ) := by
    rw [← coe_edDilateConstant, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (cfg.δ).coe_nonneg
    have h : (edDilateConstant : NNReal) ^ 2 ≤ core.C₀ :=
      le_trans edDilateConstant_sq_le_edFoldSegmentsConstant hfloor2
    have := (NNReal.coe_le_coe.2 h)
    rw [NNReal.coe_pow, sq] at this
    exact this
  intro B hB p hp q hq hne i hi
  obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
  obtain ⟨y, hy, rfl⟩ := mem_edDilateSegs' hq
  rw [show (edDilateCore pres hrad hfloor hDfloor).fam (B, y) = core.fam y from rfl,
    pres.fam_eq B hB y hy, Finset.mem_singleton] at hi
  subst hi
  refine ⟨corePt (cfg.T (pres.tub y)).toTube
    (segStart (cfg.T (pres.tub y)).toTube (core.ctr B) ((cfg.r₁ : ℝ) / 4)), ?_⟩
  exact ballCapsuleAt_subset_cthickening_ballCoreLine core edDilateConstant_pos hKδ B
    (pres.tub x) (pres.tub y) hne hC


/-! ### Obligation (C3) at the dilated carrier: **PROVED** -/

/-- **The `δ`-free constant of the class count at the dilated carrier**: `64 · coneCardConstant ·
K′₀⁴`. It is `Kakeya.VeryNotSticky.edClassCountConstant` times `K′₀²`, the price of measuring
comparability at the dilate. -/
noncomputable def edFoldCountConstant : NNReal := 64 * coneCardConstant * edDilateConstant ^ 4

theorem edFoldCountConstant_pos : 0 < edFoldCountConstant := by
  rw [edFoldCountConstant]
  have h1 : 0 < coneCardConstant := coneCardConstant_pos
  have h2 : 0 < edDilateConstant := edDilateConstant_pos
  positivity

/-- **R-b at the dilated carrier**: a class member's direction is within
`(π/2)·(8 K′₀² δ / r₁)` of the representative's. -/
theorem lineAngle_le_of_ballCapsuleAt (core : BallDataCore cfg)
    (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (B : core.bι) (i j : cfg.ι)
    (hne : ¬ IsEssentiallyDistinct (ballCapsuleAt core edDilateConstant B i)
      (ballCapsuleAt core edDilateConstant B j)) :
    NonSlab.lineAngle (cfg.T j).direction (cfg.T i).direction ≤
      Real.pi / 2 * (8 * ((edDilateConstant : NNReal) : ℝ) ^ 2 * (cfg.δ : ℝ) / (cfg.r₁ : ℝ)) := by
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  have hKδ : ((edDilateConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 2 := by
    have := edDilate_mul_delta_le_eighth hrad
    linarith
  have hsub := ballCapsuleAt_subset_hom_of_not_essDistinct core edDilateConstant_pos hKδ B i j hne
  have h := lineAngle_direction_le_of_segCarrierSetAt_subset_hom one_le_edDilateConstant
    (cfg.T i).toTube (cfg.T j).toTube (core.ctr B) (core.ctr B) (by positivity)
    (le_of_lt edComparabilityConstant_pos) hsub
  refine h.trans_eq ?_
  congr 1
  rw [coe_edDilateConstant] at *
  field_simp
  ring

open scoped Classical in
/-- **The class count at the dilated carrier, from the density cap — PROVED.**

`Kakeya.VeryNotSticky.card_cone_le`, i.e. `cfg.maxDensity_le`, with no essential-distinctness
hypothesis on `cfg.s` ( §G-addendum (a)). The cone radius is `ρ = 8 K′₀² δ / r₁`,
admissible because of the raised radius floor, and `ρ · r₁ = 8 K′₀² δ` exactly, so the
`δ`-power bookkeeping is an identity. -/
theorem edFoldClassCount_of_radiusFloor (core : BallDataCore cfg)
    (hfloor : ((edFoldRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) :
    ∀ B ∈ core.bs, ∀ i ∈ cfg.s, ∀ z : E3,
      (((cfg.s.filter (fun j => z ∈ core.Yg j ∧
          ¬ IsEssentiallyDistinct (ballCapsuleAt core edDilateConstant B i)
            (ballCapsuleAt core edDilateConstant B j))).card : ℕ) : ENNReal) ≤
        ((edFoldCountConstant * cfg.δ ^ (-(cfg.η + 2 * cfg.exscal)) : NNReal) : ENNReal) := by
  classical
  have hrad0 := radiusFloor_of_foldRadiusFloor hfloor
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  have hr₁ne : cfg.r₁ ≠ 0 := by intro h; rw [h] at hr₁pos; simp at hr₁pos
  have hδpos : (0 : ℝ) < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
  have hKR : (1 : ℝ) ≤ ((edDilateConstant : NNReal) : ℝ) := by
    exact_mod_cast one_le_edDilateConstant
  have hK0 : (0 : ℝ) ≤ ((edDilateConstant : NNReal) : ℝ) := by linarith
  have hr₁1 : (cfg.r₁ : ℝ) ≤ 1 := r₁_le_one cfg
  have h8K : ((edFoldRadiusConstant : NNReal) : ℝ)
      = 8 * ((edDilateConstant : NNReal) : ℝ) ^ 2 := by
    rw [edFoldRadiusConstant]; push_cast; ring
  rw [h8K] at hfloor
  set K : ℝ := ((edDilateConstant : NNReal) : ℝ) ^ 2 with hKdef
  have hK1 : (1 : ℝ) ≤ K := by rw [hKdef]; nlinarith
  set ρ : NNReal := 8 * edDilateConstant ^ 2 * cfg.δ / cfg.r₁ with hρdef
  have hρR : (ρ : ℝ) = 8 * K * (cfg.δ : ℝ) / (cfg.r₁ : ℝ) := by
    rw [hρdef, hKdef]; push_cast; ring
  have hρ1 : ρ ≤ 1 := by
    rw [← NNReal.coe_le_coe, NNReal.coe_one, hρR, div_le_one hr₁pos]
    linarith
  set θ : ℝ := Real.pi / 2 * (8 * K * (cfg.δ : ℝ) / (cfg.r₁ : ℝ)) with hθdef
  have hrad : 2 * (cfg.δ : ℝ) + θ ≤ 4 * (ρ : ℝ) := by
    rw [hρR, hθdef]
    have hπ : Real.pi ≤ 4 := Real.pi_le_four
    have hstep1 : 2 * (cfg.δ : ℝ) ≤ 16 * K * (cfg.δ : ℝ) / (cfg.r₁ : ℝ) := by
      rw [le_div_iff₀ hr₁pos]
      nlinarith
    have hstep2 : Real.pi / 2 * (8 * K * (cfg.δ : ℝ) / (cfg.r₁ : ℝ))
        ≤ 16 * K * (cfg.δ : ℝ) / (cfg.r₁ : ℝ) := by
      have h1 : Real.pi / 2 * (8 * K * (cfg.δ : ℝ) / (cfg.r₁ : ℝ))
          = (Real.pi / 2 * (8 * K * (cfg.δ : ℝ))) / (cfg.r₁ : ℝ) := by ring
      have h2 : Real.pi / 2 * (8 * K * (cfg.δ : ℝ)) ≤ 16 * K * (cfg.δ : ℝ) := by
        nlinarith [mul_nonneg (le_trans zero_le_one hK1) (le_of_lt hδpos)]
      rw [h1]
      gcongr
    have h : 16 * K * (cfg.δ : ℝ) / (cfg.r₁ : ℝ) + 16 * K * (cfg.δ : ℝ) / (cfg.r₁ : ℝ)
        = 4 * (8 * K * (cfg.δ : ℝ) / (cfg.r₁ : ℝ)) := by ring
    linarith
  intro B hB i hi z
  set t : Finset cfg.ι := cfg.s.filter (fun j => z ∈ core.Yg j ∧
    ¬ IsEssentiallyDistinct (ballCapsuleAt core edDilateConstant B i)
      (ballCapsuleAt core edDilateConstant B j)) with htdef
  have hmem : ∀ j ∈ t, j ∈ cfg.s ∧ z ∈ core.Yg j ∧
      ¬ IsEssentiallyDistinct (ballCapsuleAt core edDilateConstant B i)
        (ballCapsuleAt core edDilateConstant B j) := by
    intro j hj
    rw [htdef, Finset.mem_filter] at hj
    exact ⟨hj.1, hj.2.1, hj.2.2⟩
  have hcone := cfg.card_cone_le hρ1 z ((cfg.T i).direction) (cfg.T i).norm_direction hrad
    (Finset.filter_subset _ _)
    (fun j hj => (cfg.T j).shade_subset (core.Yg_subset j (hmem j hj).1 (hmem j hj).2.1))
    (fun j hj => by
      have h := lineAngle_le_of_ballCapsuleAt core hrad0 B i j (hmem j hj).2.2
      rw [hθdef, hKdef]
      exact h)
  have hδE0 : (cfg.δ : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt cfg.hδ
  have hδEtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hr₁E0 : (cfg.r₁ : ENNReal) ≠ 0 := by exact_mod_cast hr₁ne
  have hr₁Etop : (cfg.r₁ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hc₃0 : ((Tube.le_volume.c 3 : NNReal) : ENNReal) ≠ 0 := by
    exact_mod_cast (Tube.le_volume.c_pos 3).ne'
  have hc₃top : ((Tube.le_volume.c 3 : NNReal) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsq0 : ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2 ≠ 0 :=
    mul_ne_zero hc₃0 (pow_ne_zero _ hδE0)
  have hsqtop : ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top hc₃top (ENNReal.pow_ne_top hδEtop)
  refine (ENNReal.mul_le_mul_iff_left hsq0 hsqtop).mp (le_trans hcone ?_)
  have hr₁sq0 : (cfg.r₁ : ENNReal) ^ 2 ≠ 0 := pow_ne_zero _ hr₁E0
  have hr₁sqtop : (cfg.r₁ : ENNReal) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hr₁Etop
  refine (ENNReal.mul_le_mul_iff_left hr₁sq0 hr₁sqtop).mp ?_
  have hρr : (ρ : ENNReal) * (cfg.r₁ : ENNReal) = 8 * (edDilateConstant : ENNReal) ^ 2 *
      (cfg.δ : ENNReal) := by
    have h : ρ * cfg.r₁ = 8 * edDilateConstant ^ 2 * cfg.δ := by
      rw [hρdef, div_mul_cancel₀ _ hr₁ne]
    calc (ρ : ENNReal) * (cfg.r₁ : ENNReal) = ((ρ * cfg.r₁ : NNReal) : ENNReal) := by
          push_cast; ring
      _ = ((8 * edDilateConstant ^ 2 * cfg.δ : NNReal) : ENNReal) := by rw [h]
      _ = 8 * (edDilateConstant : ENNReal) ^ 2 * (cfg.δ : ENNReal) := by push_cast; ring
  have hr₁pow : (cfg.r₁ : ENNReal) ^ 2 = (cfg.δ : ENNReal) ^ (2 * cfg.exscal) := by
    have h1 : ((cfg.r₁ : NNReal) : ENNReal) = (cfg.δ : ENNReal) ^ cfg.exscal := by
      rw [show cfg.r₁ = cfg.δ ^ cfg.exscal from rfl,
        ENNReal.coe_rpow_of_ne_zero (by exact_mod_cast ne_of_gt cfg.hδ)]
    rw [h1, ← ENNReal.rpow_natCast ((cfg.δ : ENNReal) ^ cfg.exscal) 2, ← ENNReal.rpow_mul]
    norm_num
    ring_nf
  have hδcancel : (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) *
      (cfg.δ : ENNReal) ^ (2 * cfg.exscal) = (cfg.δ : ENNReal) ^ (-cfg.η) := by
    rw [← ENNReal.rpow_add _ _ hδE0 hδEtop]
    ring_nf
  have hconst : ((edFoldCountConstant : NNReal) : ENNReal) *
      ((Tube.le_volume.c 3 : NNReal) : ENNReal)
      = 64 * (64 * ((Tube.volume_le.C 3 : NNReal) : ENNReal)) *
        ((edDilateConstant : ENNReal)) ^ 4 := by
    have hc : (Tube.le_volume.c 3) ≠ 0 := (Tube.le_volume.c_pos 3).ne'
    have hnn : edFoldCountConstant * Tube.le_volume.c 3
        = 64 * (64 * Tube.volume_le.C 3) * edDilateConstant ^ 4 := by
      rw [edFoldCountConstant, coneCardConstant]
      field_simp
    calc ((edFoldCountConstant : NNReal) : ENNReal) *
          ((Tube.le_volume.c 3 : NNReal) : ENNReal)
        = ((edFoldCountConstant * Tube.le_volume.c 3 : NNReal) : ENNReal) := by push_cast; ring
      _ = ((64 * (64 * Tube.volume_le.C 3) * edDilateConstant ^ 4 : NNReal) : ENNReal) := by
          rw [hnn]
      _ = _ := by push_cast; ring
  refine le_of_eq ?_
  calc (cfg.δ : ENNReal) ^ (-cfg.η) *
        (64 * (((Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2)) *
        (cfg.r₁ : ENNReal) ^ 2
      = (cfg.δ : ENNReal) ^ (-cfg.η) * (64 * ((Tube.volume_le.C 3 : NNReal) : ENNReal)) *
          ((ρ : ENNReal) * (cfg.r₁ : ENNReal)) ^ 2 := by ring
    _ = (cfg.δ : ENNReal) ^ (-cfg.η) * (64 * ((Tube.volume_le.C 3 : NNReal) : ENNReal)) *
          (8 * (edDilateConstant : ENNReal) ^ 2 * (cfg.δ : ENNReal)) ^ 2 := by rw [hρr]
    _ = 64 * (64 * ((Tube.volume_le.C 3 : NNReal) : ENNReal)) *
          ((edDilateConstant : ENNReal)) ^ 4 * ((cfg.δ : ENNReal) ^ (-cfg.η)) *
          (cfg.δ : ENNReal) ^ 2 := by ring
    _ = ((edFoldCountConstant : NNReal) : ENNReal) *
          ((Tube.le_volume.c 3 : NNReal) : ENNReal) * ((cfg.δ : ENNReal) ^ (-cfg.η)) *
          (cfg.δ : ENNReal) ^ 2 := by rw [hconst]
    _ = ((edFoldCountConstant : NNReal) : ENNReal) *
          ((cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) *
            (cfg.δ : ENNReal) ^ (2 * cfg.exscal)) *
          (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2) := by
        rw [hδcancel]; ring
    _ = ((edFoldCountConstant * cfg.δ ^ (-(cfg.η + 2 * cfg.exscal)) : NNReal) : ENNReal) *
          (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2) *
          (cfg.r₁ : ENNReal) ^ 2 := by
        have hcoe : ((edFoldCountConstant * cfg.δ ^ (-(cfg.η + 2 * cfg.exscal)) :
              NNReal) : ENNReal)
            = ((edFoldCountConstant : NNReal) : ENNReal) *
              (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) := by
          rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero (ne_of_gt cfg.hδ)]
        rw [hr₁pow, hcoe]
        ring

open scoped Classical in
/-- **(C3) at the dilated carrier ⇒ `EDClassMult`.** The geometric statement is the class count
at the dilate: at most `M` tubes of the family shade a point with a `K′₀`-dilated capsule not
essentially distinct from a fixed one. -/
theorem edClassMult_dilate_of_capsule {M : NNReal}
    (hgeom : ∀ B ∈ core.bs, ∀ i ∈ cfg.s, ∀ z : EuclideanSpace ℝ (Fin 3),
      (((cfg.s.filter (fun j => z ∈ core.Yg j ∧
          ¬ IsEssentiallyDistinct (ballCapsuleAt core edDilateConstant B i)
            (ballCapsuleAt core edDilateConstant B j))).card : ℕ) : ENNReal) ≤ (M : ENNReal)) :
    EDClassMult (edDilateCore pres hrad hfloor hDfloor) M := by
  classical
  intro B hB x hx z
  obtain ⟨x₂, hx₂, hxeq⟩ :=
    mem_edDilateSegs' (edSel_subset (edDilateCore pres hrad hfloor hDfloor) B hx)
  subst hxeq
  refine le_trans ?_ (hgeom B hB (pres.tub x₂) (pres.tub_mem B hB x₂ hx₂) z)
  refine Nat.cast_le.2 (Finset.card_le_card ?_)
  intro j hj
  obtain ⟨hjF, hjz⟩ := Finset.mem_filter.1 hj
  obtain ⟨q, hqc, hjq⟩ := mem_edFam.1 hjF
  obtain ⟨hqs, hrep⟩ := mem_edClass.1 hqc
  obtain ⟨y₂, hy₂, hyeq⟩ := mem_edDilateSegs' hqs
  subst hyeq
  rw [show (edDilateCore pres hrad hfloor hDfloor).fam (B, y₂) = core.fam y₂ from rfl,
    pres.fam_eq B hB y₂ hy₂, Finset.mem_singleton] at hjq
  subst hjq
  refine Finset.mem_filter.2 ⟨pres.tub_mem B hB y₂ hy₂, hjz, ?_⟩
  rcases edRep_ed (edDilateCore pres hrad hfloor hDfloor) B hqs with h | h
  · rw [h] at hrep
    have hxy : x₂ = y₂ := congrArg Prod.snd hrep.symm
    rw [hxy]
    exact not_isEssentiallyDistinct_segCarrierSetAt_self cfg.hδ one_le_edDilateConstant _ _
      (by positivity)
  · rw [hrep] at h
    exact h

theorem edClassMult_mono {core : BallDataCore cfg} {M M' : NNReal} (h : M ≤ M')
    (hm : EDClassMult core M) : EDClassMult core M' :=
  fun B hB x hx z => le_trans (hm B hB x hx z) (by exact_mod_cast h)

/-- **The fibre bound the dilated fold pays**: `max 1 (C_fib · δ^{-(η+2 exscal)})` with
`C_fib = edFoldCountConstant` a `δ`-free constant. The `max` supplies `BallDataCore.hCm`. -/
noncomputable def edFoldFibreBound (cfg : VeryNotSticky.{u}) : NNReal :=
  max 1 (edFoldCountConstant * cfg.δ ^ (-(cfg.η + 2 * cfg.exscal)))

theorem one_le_edFoldFibreBound (cfg : VeryNotSticky.{u}) : 1 ≤ edFoldFibreBound cfg :=
  le_max_left _ _

/-- **`EDClassMult` at the dilated carrier — PROVED, from the radius floor alone.** -/
theorem edClassMult_dilate {core : BallDataCore cfg} (pres : CapsulePresentation core)
    (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hfloor : edSegmentsConstant ≤ core.C₀) (hDfloor : ballCoverConstant ≤ core.D)
    (hfloorR : ((edFoldRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) :
    EDClassMult (edDilateCore pres hrad hfloor hDfloor) (edFoldFibreBound cfg) :=
  edClassMult_mono (le_max_right _ _)
    (edClassMult_dilate_of_capsule pres hrad hfloor hDfloor
      (edFoldClassCount_of_radiusFloor core hfloorR))

/-! ### Obligation (C1) at the dilated carrier: **the one that stays open, and why** -/

/-- **How strong `EDClassContainment` is at the dilated carrier: no slack.** It puts the shading
of a class member within `K′₀ δ` — the carrier's own radius — of the representative's **core
line**. This is `Kakeya.VeryNotSticky.capsuleComparability_forces_delta_alignment` one dilate up:
moving to the dilated carrier weakened the demand from `δ` to `K′₀ δ`, but it also weakened the
hypothesis by exactly the same factor, so the clause is no less sharp than before. -/
theorem edClassContainment_dilate_forces_alignment {core : BallDataCore cfg}
    (pres : CapsulePresentation core)
    (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hfloor : edSegmentsConstant ≤ core.C₀) (hDfloor : ballCoverConstant ≤ core.D)
    (h : EDClassContainment (edDilateCore pres hrad hfloor hDfloor)) :
    ∀ B ∈ core.bs, ∀ x ∈ core.segs B, ∀ y ∈ core.segs B,
      ¬ IsEssentiallyDistinct (ballCapsuleAt core edDilateConstant B (pres.tub x))
          (ballCapsuleAt core edDilateConstant B (pres.tub y)) →
        (core.Y y).shade ⊆ cthickening (((edDilateConstant : NNReal) : ℝ) * (cfg.δ : ℝ))
          (ballCoreLine core B (pres.tub x)) := by
  intro B hB x hx y hy hne
  have hp : ((B, x) : core.bι × core.σ) ∈ edDilateSegs core B := mem_edDilateSegs.2 ⟨rfl, hx⟩
  have hq : ((B, y) : core.bι × core.σ) ∈ edDilateSegs core B := mem_edDilateSegs.2 ⟨rfl, hy⟩
  have hsub := h B hB _ hp _ hq hne
  have hfirst : (core.Y y).shade ⊆
      ((edDilateCore pres hrad hfloor hDfloor).Y ((B, y) : core.bι × core.σ)).shade := by
    intro z hz
    exact ⟨hz, base_shade_subset_edDilateSet pres hB hy hz⟩
  refine subset_trans hfirst (subset_trans hsub ?_)
  exact segCarrierSetAt_subset_cthickening_line _ _ _ (by positivity) le_rfl

/-- **And this is all the compiled geometry delivers: a factor `K′₀` more.** R-a at the dilated
radius puts a class member's shading within `K′₀ · K′₀ δ` of the representative's core line, not
within `K′₀ δ`. The gap is exactly `K′₀ = Kakeya.Tube.tubeOverlapCoreClose.C 3`, the constant of
the only route in the tree from `¬ IsEssentiallyDistinct` to a geometric containment; closing
`EDClassContainment` needs a **sharp** line-distance lemma (constant `≤ 1`), which
`tubeOverlapCoreClose` is not and cannot be made to be by composition. -/
theorem shade_subset_cthickening_ballCoreLine_of_not_essDistinct (core : BallDataCore cfg)
    (pres : CapsulePresentation core)
    (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    {B : core.bι} (hB : B ∈ core.bs) {x : core.σ} (_hx : x ∈ core.segs B) {y : core.σ}
    (hy : y ∈ core.segs B)
    (hne : ¬ IsEssentiallyDistinct (ballCapsuleAt core edDilateConstant B (pres.tub x))
      (ballCapsuleAt core edDilateConstant B (pres.tub y))) :
    (core.Y y).shade ⊆ cthickening
      (((edDilateConstant : NNReal) : ℝ) * (((edDilateConstant : NNReal) : ℝ) * (cfg.δ : ℝ)))
      (ballCoreLine core B (pres.tub x)) := by
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  have hKδ : ((edDilateConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 2 := by
    have := edDilate_mul_delta_le_eighth hrad
    linarith
  have hne' : ¬ IsEssentiallyDistinct (ballCapsuleAt core edDilateConstant B (pres.tub y))
      (ballCapsuleAt core edDilateConstant B (pres.tub x)) :=
    fun hED => hne (isEssentiallyDistinct_symm hED)
  refine subset_trans (base_shade_subset_edDilateSet pres hB hy) ?_
  refine ballCapsuleAt_subset_cthickening_ballCoreLine core edDilateConstant_pos hKδ B
    (pres.tub y) (pres.tub x) hne' ?_
  rw [coe_edDilateConstant]

/-- **(C1)'s single Euclidean inequality, with the `r₁/16` localisation.** This is the whole of
what remains of G13: two `K`-dilated capsules of one ball whose overlap exceeds half their volume,
and the part of the *undilated* capsule of the second that lies in the shrunken ball, must sit in
the first. No fold machinery appears in it — it is a statement about two capsules and a ball. -/
abbrev SharpCapsuleAlignment (core : BallDataCore cfg) (K : NNReal) : Prop :=
  ∀ B ∈ core.bs, ∀ i ∈ cfg.s, ∀ j ∈ cfg.s,
    ¬ IsEssentiallyDistinct (ballCapsuleAt core K B i) (ballCapsuleAt core K B j) →
      ballCapsule core B j ∩ ball (core.ctr B) ((cfg.r₁ : ℝ) / 16) ⊆ ballCapsuleAt core K B i

/-- **`SharpCapsuleAlignment` ⇒ `EDClassContainment` at the dilated carrier**, hence ⇒ G13. -/
theorem edClassContainment_dilate_of_sharpAlignment {core : BallDataCore cfg}
    (pres : CapsulePresentation core)
    (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hfloor : edSegmentsConstant ≤ core.C₀) (hDfloor : ballCoverConstant ≤ core.D)
    (halign : SharpCapsuleAlignment core edDilateConstant) :
    EDClassContainment (edDilateCore pres hrad hfloor hDfloor) :=
  edClassContainment_dilate_of_capsule pres hrad hfloor hDfloor
    (fun B hB i hi j hj hne =>
      subset_trans (Set.inter_subset_inter_right _ (pres.ball16 B hB))
        (halign B hB i hi j hj hne))

/-- **How sharp `SharpCapsuleAlignment` is**: it demands alignment to the carrier's **own**
radius `K δ` — there is no slack in it, exactly as for the undilated
`Kakeya.VeryNotSticky.capsuleComparability_forces_delta_alignment`. -/
theorem sharpCapsuleAlignment_forces_line_alignment (core : BallDataCore cfg) {K : NNReal}
    (halign : SharpCapsuleAlignment core K) :
    ∀ B ∈ core.bs, ∀ i ∈ cfg.s, ∀ j ∈ cfg.s,
      ¬ IsEssentiallyDistinct (ballCapsuleAt core K B i) (ballCapsuleAt core K B j) →
        ballCapsule core B j ∩ ball (core.ctr B) ((cfg.r₁ : ℝ) / 16) ⊆
          cthickening ((K : ℝ) * (cfg.δ : ℝ)) (ballCoreLine core B i) := by
  intro B hB i hi j hj hne
  refine subset_trans (halign B hB i hi j hj hne) ?_
  exact segCarrierSetAt_subset_cthickening_line _ _ _ (by positivity) le_rfl

/-- **(C1) AT ITS OWN FACTOR IS A THEOREM.** The localised shading of a class member lies in the
`K′₀`-homothety dilate of the representative's `K`-dilated capsule — with **no** hypothesis beyond
`¬ IsEssentiallyDistinct` and the radius bound.

So what `SharpCapsuleAlignment` is missing is not the containment but its **scale**: it asks for
the containment at `K δ` and the compiled geometry delivers it at `K′₀ · K δ`. Since the fold's
essential-distinctness conclusion is measured at the *same* body as the containment
(`BallDataCore` has one carrier per segment), the factor cannot be absorbed by any choice of `K`:
raising `K` raises both sides. That is the whole of the residue, and it is a **target-text**
issue, not a missing lemma. -/
theorem capsuleShade_subset_ownFactor_of_not_essDistinct (core : BallDataCore cfg) {K : NNReal}
    (hK : 1 ≤ K) (hKδ : (K : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 2)
    (B : core.bι) (i j : cfg.ι)
    (hne : ¬ IsEssentiallyDistinct (ballCapsuleAt core K B i) (ballCapsuleAt core K B j)) :
    ballCapsule core B j ⊆
      (AffineMap.homothety
        (capsuleCentre (cfg.T i).toTube (core.ctr B) ((cfg.r₁ : ℝ) / 4))
        edComparabilityConstant) '' (ballCapsuleAt core K B i) :=
  subset_trans (segCarrierSet_subset_segCarrierSetAt hK _ _ _)
    (ballCapsuleAt_subset_hom_of_not_essDistinct core (lt_of_lt_of_le zero_lt_one hK) hKδ B i j
      hne)

end CapsuleFormDilate

/-! ### The cover level, over the floor text -/

theorem s_nonempty_of_cover {bι : Type u} (cfg : VeryNotSticky.{u}) {bs : Finset bι}
    {P : bι → Set (EuclideanSpace ℝ (Fin 3))} (hbsne : bs.Nonempty)
    (hPne : ∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty) : cfg.s.Nonempty := by
  obtain ⟨B, hB⟩ := hbsne
  obtain ⟨x, -, hxs⟩ := hPne B hB
  obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.mp hxs
  exact ⟨i, hi⟩

section CoverFloor

variable (cfg : VeryNotSticky.{u}) {bι : Type u}
  {C₀ : NNReal} (hC₀ : edFoldSegmentsConstant ≤ C₀) {D : ℕ} (hD : ballCoverConstant ≤ D)
  (hrad : ((edFoldRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
  (bs : Finset bι) (ctr : bι → EuclideanSpace ℝ (Fin 3))
  (P : bι → Set (EuclideanSpace ℝ (Fin 3)))
  (hbsne : bs.Nonempty)
  (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
  (hPball : ∀ B ∈ bs, P B ⊆ closedBall (ctr B) (cfg.r₁ : ℝ))
  (hPdisj : (bs : Set bι).PairwiseDisjoint P)
  (hPmeas : ∀ B, MeasurableSet (P B))
  (hPcov : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B)
  (hoverlap : ∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
    (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant)
  (hPne : ∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty)
  {c₁ : NNReal} (hc₁ : 0 < c₁)
  (hc₁' : edDensityFloorConstant * c₁ * (ballCoverConstant : NNReal) ≤ 1)

/-- **The named step-5/6 core over the floor text**, at the raised base density
`edBaseDensityConstant c₁` the dilated presentation needs. -/
noncomputable def edFloorBaseCore : BallDataCore cfg :=
  (exists_core_segsDensity_capsule_ball16_of_cover cfg
    (le_trans four_le_edFoldSegmentsConstant hC₀) hD
    (deltaLeR₁_of_radiusFloor (radiusFloor_of_foldRadiusFloor hrad))
    bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov hoverlap hPne
    (edBaseDensityConstant_pos hc₁)
    (by rw [four_mul_edBaseDensityConstant]; exact hc₁')).choose

local notation "𝔅₀" => edFloorBaseCore cfg hC₀ hD hrad bs ctr P hbsne hPball16 hPball hPdisj
  hPmeas hPcov hoverlap hPne hc₁ hc₁'

theorem edFloorBaseCore_spec :
    (𝔅₀).C₀ = C₀ ∧ (𝔅₀).D = D ∧
      (∀ B ∈ (𝔅₀).bs, ∀ p ∈ (𝔅₀).segs B,
        ((edBaseDensityConstant c₁ : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) *
            volume ((𝔅₀).Y p).carrier ≤ volume ((𝔅₀).Y p).shade) ∧
      (∀ B ∈ (𝔅₀).bs, (cfg.r₁ : ENNReal) ^ 2 *
          Kakeya.maxDensity ((𝔅₀).segs B) (fun p ↦ ((𝔅₀).Y p).toConvexSpaceBody) ≤
        (segsDilationConstant : ENNReal) *
          Kakeya.maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)) ∧
      HasCapsuleSegments (𝔅₀) ∧
      (∀ B ∈ (𝔅₀).bs, (𝔅₀).P B ⊆ ball ((𝔅₀).ctr B) ((cfg.r₁ : ℝ) / 16)) :=
  (exists_core_segsDensity_capsule_ball16_of_cover cfg
    (le_trans four_le_edFoldSegmentsConstant hC₀) hD
    (deltaLeR₁_of_radiusFloor (radiusFloor_of_foldRadiusFloor hrad))
    bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov hoverlap hPne
    (edBaseDensityConstant_pos hc₁)
    (by rw [four_mul_edBaseDensityConstant]; exact hc₁')).choose_spec

theorem edFloorBaseCore_C₀_foldfloor : edFoldSegmentsConstant ≤ (𝔅₀).C₀ := by
  rw [(edFloorBaseCore_spec cfg hC₀ hD hrad bs ctr P hbsne hPball16 hPball hPdisj hPmeas
    hPcov hoverlap hPne hc₁ hc₁').1]
  exact hC₀

theorem edFloorBaseCore_C₀_floor : edSegmentsConstant ≤ (𝔅₀).C₀ :=
  segmentsFloor_of_foldSegmentsFloor
    (edFloorBaseCore_C₀_foldfloor cfg hC₀ hD hrad bs ctr P hbsne hPball16 hPball hPdisj hPmeas
      hPcov hoverlap hPne hc₁ hc₁')

theorem edFloorBaseCore_D_floor : ballCoverConstant ≤ (𝔅₀).D := by
  rw [(edFloorBaseCore_spec cfg hC₀ hD hrad bs ctr P hbsne hPball16 hPball hPdisj hPmeas
    hPcov hoverlap hPne hc₁ hc₁').2.1]
  exact hD

/-- The capsule presentation of the named step-5/6 core, skolemised. -/
noncomputable def edFloorPres : CapsulePresentation (𝔅₀) :=
  (nonempty_capsulePresentation (𝔅₀) (s_nonempty_of_cover cfg hbsne hPne)
    (edFloorBaseCore_spec cfg hC₀ hD hrad bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
      hoverlap hPne hc₁ hc₁').2.2.2.2.1
    (shade_nonempty_of_capsule_density (edBaseDensityConstant_pos hc₁)
      (edFloorBaseCore_spec cfg hC₀ hD hrad bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
        hoverlap hPne hc₁ hc₁').2.2.1)
    (edFloorBaseCore_spec cfg hC₀ hD hrad bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
      hoverlap hPne hc₁ hc₁').2.2.2.2.2).some

/-- **The step-5/6 core, re-presented at the `K′₀`-dilated carrier.** This is the core the
repaired fold folds, and the core the one remaining geometric obligation is stated about. -/
noncomputable def edFloorDilateCore : BallDataCore cfg :=
  edDilateCore (edFloorPres cfg hC₀ hD hrad bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
      hoverlap hPne hc₁ hc₁')
    (radiusFloor_of_foldRadiusFloor hrad)
    (edFloorBaseCore_C₀_floor cfg hC₀ hD hrad bs ctr P hbsne hPball16 hPball hPdisj hPmeas
      hPcov hoverlap hPne hc₁ hc₁')
    (edFloorBaseCore_D_floor cfg hC₀ hD hrad bs ctr P hbsne hPball16 hPball hPdisj hPmeas
      hPcov hoverlap hPne hc₁ hc₁')

local notation "𝔅₁" => edFloorDilateCore cfg hC₀ hD hrad bs ctr P hbsne hPball16 hPball hPdisj
  hPmeas hPcov hoverlap hPne hc₁ hc₁'

/-- **`EDClassCore` for the cover-level dilated core — no hypothesis.** -/
theorem edFloorDilateCore_edClassCore : EDClassCore (𝔅₁) :=
  edClassCore_dilate _ _ _ _
    (edFloorBaseCore_C₀_foldfloor cfg hC₀ hD hrad bs ctr P hbsne hPball16 hPball hPdisj hPmeas
      hPcov hoverlap hPne hc₁ hc₁')

/-- **`EDClassMult` for the cover-level dilated core — no hypothesis.** -/
theorem edFloorDilateCore_edClassMult : EDClassMult (𝔅₁) (edFoldFibreBound cfg) :=
  edClassMult_dilate _ _ _ _ hrad

/-- **G13 / S-4 — the BP264 target over the floor text, with two of the three geometric
obligations discharged.**

The floors replace `4 ≤ C₀`, `4 c₁ D ≤ 1` and `16 δ ≤ r₁` by `edFoldSegmentsConstant ≤ C₀`,
`edDensityFloorConstant · c₁ · D ≤ 1` and `edFoldRadiusConstant · δ ≤ r₁`; the fibre budget is
the binder `Bfib` above the compiled bound `edFoldFibreBound`, so the explicit fibre budget is a
substitution; and the dilation constant is the binder `Cdil` with the floor
`edDilationFloorConstant ≤ Cdil`.

**`EDClassCore` and `EDClassMult` at the dilated carrier are theorems**
(`edFloorDilateCore_edClassCore`, `edFloorDilateCore_edClassMult`). The single remaining
hypothesis is `EDClassContainment` — the existing obligation (C1), whose sharpness at this carrier
is `edClassContainment_dilate_forces_alignment` and whose gap to the compiled geometry is
`shade_subset_cthickening_ballCoreLine_of_not_essDistinct`: exactly one factor of `K′₀`. -/
theorem exists_core_edSegments_of_cover_floor
    {Cdil : NNReal} (hCdil : edDilationFloorConstant ≤ Cdil)
    {Bfib : ENNReal} (hexit : ((edFoldFibreBound cfg : NNReal) : ENNReal) ≤ Bfib)
    (hclass : EDClassContainment (𝔅₁)) :
    ∃ core : BallDataCore cfg,
      core.C₀ = C₀ ∧ core.D = D ∧
      (∀ B ∈ core.bs, (core.segs B : Set core.σ).Pairwise
        fun p q => _root_.IsEssentiallyDistinct (core.Y p).carrier (core.Y q).carrier) ∧
      ((core.Cm : ENNReal) * (core.m : ENNReal) ≤ Bfib) ∧
      (∀ B ∈ core.bs, ∀ p ∈ core.segs B,
        (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier ≤
          volume (core.Y p).shade) ∧
      (∀ B ∈ core.bs, (cfg.r₁ : ENNReal) ^ 2 *
          Kakeya.maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) ≤
        (Cdil : ENNReal) * Kakeya.maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)) := by
  classical
  obtain ⟨hC₀eq, hDeq, hdens₀, hdil₀, -, -⟩ :=
    edFloorBaseCore_spec cfg hC₀ hD hrad bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
      hoverlap hPne hc₁ hc₁'
  have hrad0 := radiusFloor_of_foldRadiusFloor hrad
  have hrel : 16 * ((edDilateConstant : NNReal) : ENNReal) ^ 2 * (c₁ : ENNReal)
      ≤ ((edBaseDensityConstant c₁ : NNReal) : ENNReal) *
        ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal) := by
    rw [← ENNReal.coe_mul, edBaseDensityConstant_mul_c₃]
    push_cast
    exact le_rfl
  have hCdil' : 16 * ((edDilateConstant : NNReal) : ENNReal) ^ 2 *
      (segsDilationConstant : ENNReal) ≤
      (Cdil : ENNReal) * ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal) := by
    have h : (16 * edDilateConstant ^ 2 * segsDilationConstant : NNReal)
        ≤ Cdil * (Metric.lt_volume_convexHull.c 3 : NNReal) := by
      rw [← edDilationFloorConstant_mul_c₃]
      exact mul_le_mul_left hCdil _
    have h' := ENNReal.coe_le_coe.2 h
    push_cast at h' ⊢
    exact h'
  have hdens₁ : ∀ B ∈ (𝔅₁).bs, ∀ p ∈ (𝔅₁).segs B,
      (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume ((𝔅₁).Y p).carrier ≤
        volume ((𝔅₁).Y p).shade := by
    intro B hB p hp
    obtain ⟨x, hx, rfl⟩ := mem_edDilateSegs' hp
    exact edDilate_segs_density _ hrad0 hrel hdens₀ hB hx
  have hdil₁ : ∀ B ∈ (𝔅₁).bs, (cfg.r₁ : ENNReal) ^ 2 *
      Kakeya.maxDensity ((𝔅₁).segs B) (fun p ↦ ((𝔅₁).Y p).toConvexSpaceBody) ≤
      (Cdil : ENNReal) * Kakeya.maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody) := by
    intro B hB
    exact edDilate_segs_dilation _ hrad0 hCdil' hdil₀ hB
  refine ⟨edFoldCore (𝔅₁) hclass
      (edFloorDilateCore_edClassCore cfg hC₀ hD hrad bs ctr P hbsne hPball16 hPball hPdisj
        hPmeas hPcov hoverlap hPne hc₁ hc₁')
      (edFoldFibreBound cfg) (one_le_edFoldFibreBound cfg)
      (edFloorDilateCore_edClassMult cfg hC₀ hD hrad bs ctr P hbsne hPball16 hPball hPdisj
        hPmeas hPcov hoverlap hPne hc₁ hc₁'),
    hC₀eq, hDeq, ?_, ?_, ?_, ?_⟩
  · intro B _
    exact edFoldCore_essDistinct (𝔅₁) B
  · simpa using hexit
  · exact edFoldCore_segs_density (𝔅₁) hdens₁
  · exact edFoldCore_segs_dilation (𝔅₁) hdil₁


/-- **G13 over the floor text, with the residue reduced to the single Euclidean inequality.**
The only geometric input is `SharpCapsuleAlignment`, a statement about two capsules and a ball
with no fold machinery in it. -/
theorem exists_core_edSegments_of_cover_floor_of_alignment
    {Cdil : NNReal} (hCdil : edDilationFloorConstant ≤ Cdil)
    {Bfib : ENNReal} (hexit : ((edFoldFibreBound cfg : NNReal) : ENNReal) ≤ Bfib)
    (halign : SharpCapsuleAlignment (𝔅₀) edDilateConstant) :
    ∃ core : BallDataCore cfg,
      core.C₀ = C₀ ∧ core.D = D ∧
      (∀ B ∈ core.bs, (core.segs B : Set core.σ).Pairwise
        fun p q => _root_.IsEssentiallyDistinct (core.Y p).carrier (core.Y q).carrier) ∧
      ((core.Cm : ENNReal) * (core.m : ENNReal) ≤ Bfib) ∧
      (∀ B ∈ core.bs, ∀ p ∈ core.segs B,
        (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier ≤
          volume (core.Y p).shade) ∧
      (∀ B ∈ core.bs, (cfg.r₁ : ENNReal) ^ 2 *
          Kakeya.maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) ≤
        (Cdil : ENNReal) * Kakeya.maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)) :=
  exists_core_edSegments_of_cover_floor cfg hC₀ hD hrad bs ctr P hbsne hPball16 hPball hPdisj
    hPmeas hPcov hoverlap hPne hc₁ hc₁' hCdil hexit
    (edClassContainment_dilate_of_sharpAlignment _ _ _ _ halign)

end CoverFloor

end Kakeya.VeryNotSticky

/-! ### F28 — the BP264 target, re-cut to the hypothesis-floor text

It cannot be cut *in place* in
`Kakeya/DimensionThree/MainLemma2/BallCoreEDSegments.lean`, and the reason is mechanical rather
than editorial: the re-cut statement's geometric hypothesis is about the **dilated** capsule
`Kakeya.VeryNotSticky.segCarrierSetAt`, which is defined in `BallCoreEDCapsule.lean`, and its
proof is `Kakeya.VeryNotSticky.exists_core_edSegments_of_cover_floor_of_alignment`, which lives
here; both modules import `BallCoreEDSegments.lean`, so a `theorem` with this statement cannot be
elaborated there. **The re-cut target belongs in a leaf after `BallCoreEDFold.lean`.**

Licences:  §G-1 (the hypothesis-floor form of the (C1) dilate, and the `c₁` floor),
 §G-2 (SP-H: `bd.m = 1 ∧ bd.Cm = 1` → the fibre budget),  §C-iii (the exit),
and the four amendments  The four constants are
`Kakeya.VeryNotSticky.edFoldSegmentsConstant = 4 K′₀²`,
`Kakeya.VeryNotSticky.edDensityFloorConstant = 64 K′₀²/c₃`,
`Kakeya.VeryNotSticky.edFoldRadiusConstant = 8 K′₀²` and
`Kakeya.VeryNotSticky.edDilationFloorConstant`, all built from the single named
`Kakeya.VeryNotSticky.edDilateConstant = Kakeya.Tube.tubeOverlapCoreClose.C 3`. -/

namespace BP264

open Kakeya Kakeya.VeryNotSticky

/-- **G13 (R31's construction): GWZ §9.3 steps 6–8 at the core level — the re-cut target.**

The segment family of each ball is cut down to ESSENTIALLY DISTINCT representatives, the
comparable tubes are folded into `fam`, and the fibre count is pigeonholed. Against the
Blueprinter's original text (, statement source versions
`c5422c3c1f0abc1b86ef7794299f2249`) the changes are exactly:

* `hC₀ : 4 ≤ C₀` → `edFoldSegmentsConstant ≤ C₀`;
* `hc₁' : 4 * c₁ * ballCoverConstant ≤ 1` → `edDensityFloorConstant * c₁ * ballCoverConstant ≤ 1`;
* `hδr : 16 * δ ≤ r₁` → `edFoldRadiusConstant * δ ≤ r₁`;
* the fibre bound `δ^{-(η + 2 exscal)}` → the binder `Bfib` above the compiled
  `edFoldFibreBound cfg` (the explicit fibre budget is the choice of `Bfib`);
* the dilation constant `segsDilationConstant` → the binder `Cdil` with its floor;
* the three abstract geometric hypotheses → the single Euclidean statement
  `SharpCapsuleAlignment`, `EDClassCore` and `EDClassMult` having become theorems. -/
theorem exists_core_edSegments_of_cover (cfg : VeryNotSticky.{u}) {bι : Type u}
    {C₀ : NNReal} (hC₀ : edFoldSegmentsConstant ≤ C₀) {D : ℕ} (hD : ballCoverConstant ≤ D)
    (hδr : ((edFoldRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (bs : Finset bι) (ctr : bι → EuclideanSpace ℝ (Fin 3))
    (P : bι → Set (EuclideanSpace ℝ (Fin 3)))
    (hbsne : bs.Nonempty)
    (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
    (hPball : ∀ B ∈ bs, P B ⊆ closedBall (ctr B) (cfg.r₁ : ℝ))
    (hPdisj : (bs : Set bι).PairwiseDisjoint P)
    (hPmeas : ∀ B, MeasurableSet (P B))
    (hPcov : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B)
    (hoverlap : ∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
      (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant)
    (hPne : ∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty)
    {c₁ : NNReal} (hc₁ : 0 < c₁)
    (hc₁' : edDensityFloorConstant * c₁ * (ballCoverConstant : NNReal) ≤ 1)
    {Cdil : NNReal} (hCdil : edDilationFloorConstant ≤ Cdil)
    {Bfib : ENNReal} (hexit : ((edFoldFibreBound cfg : NNReal) : ENNReal) ≤ Bfib)
    (halign : SharpCapsuleAlignment
      (edFloorBaseCore cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
        hoverlap hPne hc₁ hc₁') edDilateConstant) :
    ∃ core : BallDataCore cfg,
      core.C₀ = C₀ ∧ core.D = D ∧
      -- (R31): the segments of each ball are pairwise essentially distinct
      (∀ B ∈ core.bs, (core.segs B : Set core.σ).Pairwise
        fun p q => _root_.IsEssentiallyDistinct (core.Y p).carrier (core.Y q).carrier) ∧
      -- (the price): `m = 1` is gone; the fibre count sits inside the budget binder
      ((core.Cm : ENNReal) * (core.m : ENNReal) ≤ Bfib) ∧
      (∀ B ∈ core.bs, ∀ p ∈ core.segs B,
        (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier ≤
          volume (core.Y p).shade) ∧
      (∀ B ∈ core.bs, (cfg.r₁ : ENNReal) ^ 2 *
          maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) ≤
        (Cdil : ENNReal) * maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)) :=
  exists_core_edSegments_of_cover_floor_of_alignment cfg hC₀ hD hδr bs ctr P hbsne hPball16
    hPball hPdisj hPmeas hPcov hoverlap hPne hc₁ hc₁' hCdil hexit halign

end BP264
