/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallCoreEDComparable
public import Kakeya.DimensionThree.MainLemma2.NonSlabAngle

/-!
# R-a and R-b: GWZ's "comparable" for capsules is a THEOREM, and the angular step

Fourth and last file of the G13 stack (`BallCoreEDSegments`, `BallCoreEDCapsule`,
`BallCoreEDComparable`, this). **Land it together with the previous two**: the third file
supersedes the second's radius-only reading of comparability, and this one discharges the
hypothesis the third left open.

## R-a — `CapsuleComparableHomAt` is proved

`Kakeya.VeryNotSticky.capsuleComparableHomAt_of_deltaLeR₁`: for every `BallDataCore` of a
configuration with `16 δ ≤ r₁` — the binder the BP264 target already carries — two capsules of one
ball that are **not essentially distinct** each lie in the `K′₀`-homothety dilate of the other,
at `K′₀ = Kakeya.VeryNotSticky.edDilateConstant`. **This was G13's single remaining geometric
obligation.**

The proof is a rescaling, and every step is existing geometry:

* `Kakeya.VeryNotSticky.rescaledCapsuleTube` — the homothety of ratio `(2L)⁻¹` carries a capsule
  of half-length `L` and radius `δ` to the carrier of a genuine `Kakeya.Tube` of scale
  `δ/(2L) ≤ 1` (the core window has length exactly `2L`, so its image has length exactly `1`);
* `IsEssentiallyDistinct.image_affineEquiv` transports the hypothesis;
* `Kakeya.VeryNotSticky.tube_subset_dilate_of_not_essDistinct` — i.e. the existing
  `Kakeya.Tube.tubeOverlapCoreClose` — applies there;
* its conclusion is a `Kakeya.Tube.dilate`, a homothety about `Tube.center = midpoint x y`, and
  `homothety_conj` + `rescaledCapsuleTube_center` pull it back to a homothety about the capsule's
  own centre.

Consequences, all now unconditional in `core`: `capsuleInputs_of_floor` and `capsuleShade_subset_hom_at_K₀` (the (C1) clause the repaired fold consumes).

## R-b — the angular step

`Kakeya.VeryNotSticky.lineAngle_le_of_ballCapsuleHom`: a class member's direction is within
`(π/2)·(8 K δ / r₁)` of the representative's. That is the `hang` hypothesis of
`Kakeya.VeryNotSticky.card_cone_le`, so the density-cap route of  §G-addendum (a) — no
essential-distinctness hypothesis on `cfg.s` — is fed. The proof is elementary: the two endpoints
of the class member's core window decompose along the representative's core line with an error
`K δ`, so the unit chord differs from `± dir i` by at most `2Kδ/L`, and
`NonSlab.lineAngle_le_pi_div_two_mul_norm_sub` converts that to an angle.

## R-c — left as a binder, as instructed

`Kakeya.VeryNotSticky.fibreClause_of_classCount` states the fold's fibre clause with the budget's
constant as an explicit named `C_fib`, so that the same estimate applies to any chosen budget.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace Kakeya.VeryNotSticky

universe u
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-! ### The homothety toolbox -/

theorem homothety_image_closedBall {p : E3} {k : ℝ} (hk : 0 < k) (z : E3) (r : ℝ) :
    (AffineMap.homothety p k) '' closedBall z r =
      closedBall (AffineMap.homothety p k z) (k * r) := by
  ext y
  simp only [Set.mem_image, Metric.mem_closedBall]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [dist_homothety, abs_of_pos hk]
    exact mul_le_mul_of_nonneg_left hx (le_of_lt hk)
  · intro hy
    refine ⟨AffineMap.homothety p k⁻¹ y, ?_, ?_⟩
    · have := dist_homothety p k⁻¹ y (AffineMap.homothety p k z)
      rw [abs_of_pos (inv_pos.2 hk)] at this
      have hz : AffineMap.homothety p k⁻¹ (AffineMap.homothety p k z) = z := by
        rw [← AffineMap.comp_apply, ← AffineMap.homothety_mul,
          inv_mul_cancel₀ (ne_of_gt hk), AffineMap.homothety_one]; rfl
      rw [hz] at this
      rw [this, inv_mul_le_iff₀ hk] at *
      calc dist y (AffineMap.homothety p k z) ≤ k * r := hy
        _ = k * r := rfl
    · rw [← AffineMap.comp_apply, ← AffineMap.homothety_mul,
        mul_inv_cancel₀ (ne_of_gt hk), AffineMap.homothety_one]; rfl

theorem homothety_image_segment (p : E3) (k : ℝ) (a b : E3) :
    (AffineMap.homothety p k) '' segment ℝ a b =
      segment ℝ (AffineMap.homothety p k a) (AffineMap.homothety p k b) := by
  ext y
  simp only [Set.mem_image, segment_eq_image' ℝ]
  constructor
  · rintro ⟨x, ⟨θ, hθ, rfl⟩, rfl⟩
    refine ⟨θ, hθ, ?_⟩
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    module
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨a + θ • (b - a), ⟨θ, hθ, rfl⟩, ?_⟩
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    module

/-- **Conjugating a homothety by a homothety** gives a homothety of the same ratio about the
image of the centre. -/
theorem homothety_conj {p : E3} {k : ℝ} (hk : k ≠ 0) (a : E3) (C : ℝ) (x : E3) :
    AffineMap.homothety p k⁻¹
        (AffineMap.homothety (AffineMap.homothety p k a) C (AffineMap.homothety p k x)) =
      AffineMap.homothety a C x := by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  rw [show k • (x - p) + p - (k • (a - p) + p) = k • (x - a) by module]
  rw [show C • k • (x - a) + (k • (a - p) + p) - p = k • (C • (x - a) + (a - p)) by module]
  rw [smul_smul, inv_mul_cancel₀ hk, one_smul]
  module


/-! ### The capsule as a convex body, and its rescaling to a unit tube -/

/-- The capsule `segCarrierSet T c L` packaged as a `ConvexSpaceBody`. -/
noncomputable def capsuleBody {δ : NNReal} (T : Tube δ E3) (c : E3) {L : ℝ} (hL : 0 ≤ L) :
    ConvexSpaceBody E3 where
  carrier := segCarrierSet T c L
  convex' := (convex_segCarrierSet' T c L).isConvexSet
  isCompact' :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_segCarrierSet T c L)
      (Metric.isBounded_closedBall.subset (segCarrierSet_subset_closedBall T c hL))
  nonempty' := segCarrierSet_nonempty T c hL

@[simp] theorem capsuleBody_carrier {δ : NNReal} (T : Tube δ E3) (c : E3) {L : ℝ} (hL : 0 ≤ L) :
    (capsuleBody T c hL).carrier = segCarrierSet T c L := rfl

theorem dist_corePt_window {δ : NNReal} (T : Tube δ E3) (c : E3) {L : ℝ} (hL : 0 ≤ L) :
    dist (corePt T (segStart T c L)) (corePt T (segStart T c L + 2 * L)) = 2 * L := by
  rw [dist_corePt, show segStart T c L - (segStart T c L + 2 * L) = -(2 * L) by ring, abs_neg,
    abs_of_nonneg (by linarith)]

/-- **The capsule, rescaled to a unit tube.** The homothety of ratio `(2L)⁻¹` about `m` takes the
core window (of length `2L`) to a segment of length `1` and the radius `δ` to `δ / (2L)`, so the
image of `segCarrierSet T c L` is literally the carrier of a `Kakeya.Tube` of that scale. This is
what lets the existing `Kakeya.Tube.tubeOverlapCoreClose` be applied to capsules. -/
noncomputable def rescaledCapsuleTube {δ δ' : NNReal} (T : Tube δ E3) (c m : E3) {L : ℝ}
    (hL : 0 < L) (hδ' : (δ' : ℝ) = (2 * L)⁻¹ * (δ : ℝ)) : Tube δ' E3 where
  toConvexSpaceBody :=
    ConvexSpaceBody.affineImage (AffineMap.homothety m (2 * L)⁻¹)
      (AffineMap.continuous_of_finiteDimensional _) (capsuleBody T c (le_of_lt hL))
  x := AffineMap.homothety m (2 * L)⁻¹ (corePt T (segStart T c L))
  y := AffineMap.homothety m (2 * L)⁻¹ (corePt T (segStart T c L + 2 * L))
  dist_eq_one := by
    have h2L : (0 : ℝ) < 2 * L := by linarith
    rw [dist_homothety, abs_of_pos (inv_pos.2 h2L), dist_corePt_window T c (le_of_lt hL),
      inv_mul_cancel₀ (ne_of_gt h2L)]
  carrier_eq := by
    have h2L : (0 : ℝ) < 2 * L := by linarith
    have hk : (0 : ℝ) < (2 * L)⁻¹ := inv_pos.2 h2L
    change (AffineMap.homothety m (2 * L)⁻¹) '' (segCarrierSet T c L) = _
    rw [segCarrierSet_eq_biUnion, Set.image_iUnion₂]
    rw [← homothety_image_segment m (2 * L)⁻¹ _ _]
    rw [Set.biUnion_image]
    refine Set.iUnion₂_congr fun w _ => ?_
    rw [homothety_image_closedBall hk w (δ : ℝ), hδ']

@[simp] theorem rescaledCapsuleTube_carrier {δ δ' : NNReal} (T : Tube δ E3) (c m : E3) {L : ℝ}
    (hL : 0 < L) (hδ' : (δ' : ℝ) = (2 * L)⁻¹ * (δ : ℝ)) :
    (rescaledCapsuleTube T c m hL hδ').carrier =
      (AffineMap.homothety m (2 * L)⁻¹) '' (segCarrierSet T c L) := rfl

@[simp] theorem rescaledCapsuleTube_x {δ δ' : NNReal} (T : Tube δ E3) (c m : E3) {L : ℝ}
    (hL : 0 < L) (hδ' : (δ' : ℝ) = (2 * L)⁻¹ * (δ : ℝ)) :
    (rescaledCapsuleTube T c m hL hδ').x =
      AffineMap.homothety m (2 * L)⁻¹ (corePt T (segStart T c L)) := rfl

@[simp] theorem rescaledCapsuleTube_y {δ δ' : NNReal} (T : Tube δ E3) (c m : E3) {L : ℝ}
    (hL : 0 < L) (hδ' : (δ' : ℝ) = (2 * L)⁻¹ * (δ : ℝ)) :
    (rescaledCapsuleTube T c m hL hδ').y =
      AffineMap.homothety m (2 * L)⁻¹ (corePt T (segStart T c L + 2 * L)) := rfl

theorem rescaledCapsuleTube_center {δ δ' : NNReal} (T : Tube δ E3) (c m : E3) {L : ℝ}
    (hL : 0 < L) (hδ' : (δ' : ℝ) = (2 * L)⁻¹ * (δ : ℝ)) :
    (rescaledCapsuleTube T c m hL hδ').center =
      AffineMap.homothety m (2 * L)⁻¹ (capsuleCentre T c L) := by
  change midpoint ℝ _ _ = _
  rw [rescaledCapsuleTube_x, rescaledCapsuleTube_y, ← AffineMap.map_midpoint]
  congr 1
  change midpoint ℝ (corePt T (segStart T c L)) (corePt T (segStart T c L + 2 * L)) =
    corePt T (segStart T c L + L)
  simp only [corePt, midpoint_eq_smul_add, invOf_eq_inv]
  module


theorem homothety_inv_apply {p : E3} {k : ℝ} (hk : k ≠ 0) (x : E3) :
    AffineMap.homothety p k⁻¹ (AffineMap.homothety p k x) = x := by
  rw [← AffineMap.comp_apply, ← AffineMap.homothety_mul, inv_mul_cancel₀ hk,
    AffineMap.homothety_one]
  rfl

/-! ### R-a: comparability of capsules at `K′₀`, from the existing tube geometry -/

/-- **R-a — GWZ's "comparable" for capsules, proved.** Two capsules of the same half-length `L`
about the same point that are **not essentially distinct** each lie in the `K′₀`-homothety dilate
of the other, at `K′₀ = Kakeya.VeryNotSticky.edComparabilityConstant`.

The proof is the rescaling: the homothety of ratio `(2L)⁻¹` carries the two capsules to two
genuine `Kakeya.Tube`s of scale `δ/(2L) ≤ 1` (`rescaledCapsuleTube`), essential distinctness is
invariant under an affine equivalence (`IsEssentiallyDistinct.image_affineEquiv`), the existing
`Kakeya.Tube.tubeOverlapCoreClose` applies there
(`Kakeya.VeryNotSticky.tube_subset_dilate_of_not_essDistinct`), and its conclusion — a homothety
dilate about the tube's centre — pulls back to a homothety dilate about the capsule's centre
(`homothety_conj`, `rescaledCapsuleTube_center`). -/
theorem capsule_subset_hom_of_not_essDistinct {δ : NNReal} (hδ0 : 0 < δ)
    (Ti Tj : Tube δ E3) (c m : E3) {L : ℝ} (hL : 0 < L) (hδL : (δ : ℝ) ≤ 2 * L)
    (hne : ¬ IsEssentiallyDistinct (segCarrierSet Ti c L) (segCarrierSet Tj c L)) :
    segCarrierSet Tj c L ⊆ segCarrierSetHom edComparabilityConstant Ti c L := by
  have h2L : (0 : ℝ) < 2 * L := by linarith
  have hk0 : (0 : ℝ) < (2 * L)⁻¹ := inv_pos.2 h2L
  have hkne : ((2 * L)⁻¹ : ℝ) ≠ 0 := ne_of_gt hk0
  set k : ℝ := (2 * L)⁻¹ with hkdef
  set σ : E3 →ᵃ[ℝ] E3 := AffineMap.homothety m k with hσdef
  -- the rescaled radius
  set δ' : NNReal := (k * (δ : ℝ)).toNNReal with hδ'def
  have hδ' : (δ' : ℝ) = k * (δ : ℝ) := Real.coe_toNNReal _ (by positivity)
  have hδ'0 : 0 < δ' := by
    have : (0 : ℝ) < (δ' : ℝ) := by rw [hδ']; have : (0:ℝ) < (δ:ℝ) := by exact_mod_cast hδ0
                                    positivity
    exact_mod_cast this
  have hδ'1 : δ' ≤ 1 := by
    have : (δ' : ℝ) ≤ 1 := by
      rw [hδ', hkdef, inv_mul_le_iff₀ h2L]
      linarith
    exact_mod_cast this
  set Ti' : Tube δ' E3 := rescaledCapsuleTube Ti c m hL hδ' with hTi'
  set Tj' : Tube δ' E3 := rescaledCapsuleTube Tj c m hL hδ' with hTj'
  -- essential distinctness transports
  have hσe : (AffineEquiv.homothetyUnitsMulHom m (Units.mk0 k hkne) :
      E3 ≃ᵃ[ℝ] E3) = (AffineEquiv.homothetyUnitsMulHom m (Units.mk0 k hkne)) := rfl
  set σe : E3 ≃ᵃ[ℝ] E3 := AffineEquiv.homothetyUnitsMulHom m (Units.mk0 k hkne) with hσedef
  have hcoe : ⇑σe = ⇑σ := by
    rw [hσedef, AffineEquiv.coe_homothetyUnitsMulHom_apply, hσdef]; rfl
  have hne' : ¬ IsEssentiallyDistinct Ti'.carrier Tj'.carrier := by
    intro hED
    refine hne ?_
    have h := hED.image_affineEquiv σe.symm
    rw [hTi', hTj', rescaledCapsuleTube_carrier, rescaledCapsuleTube_carrier, ← hcoe,
      ← Set.image_comp, ← Set.image_comp] at h
    simpa using h
  -- the existing tube geometry
  have hsub := tube_subset_dilate_of_not_essDistinct hδ'0 hδ'1 Ti' Tj' hne'
  rw [Tube.dilate_carrier, hTi', rescaledCapsuleTube_carrier,
    rescaledCapsuleTube_center] at hsub
  -- pull back
  intro x hx
  have hσx : σ x ∈ Tj'.carrier := by
    rw [hTj', rescaledCapsuleTube_carrier]
    exact ⟨x, hx, rfl⟩
  obtain ⟨u, ⟨v, hv, rfl⟩, huv⟩ := hsub hσx
  refine ⟨v, hv, ?_⟩
  have := congrArg (AffineMap.homothety m k⁻¹) huv
  rw [homothety_conj hkne (capsuleCentre Ti c L) edComparabilityConstant v,
    homothety_inv_apply hkne x] at this
  exact this


/-- **R-a at the core level: `CapsuleComparableHomAt` is a THEOREM, not a hypothesis.**

It needs nothing of `core` beyond the configuration's own `16 δ ≤ r₁` — the same binder the
BP264 target already carries — so the single geometric obligation R31 left open is discharged.
The constant is `K′₀ = Kakeya.VeryNotSticky.edDilateConstant`, the `def`  §G-1 asks
for. -/
theorem capsuleComparableHomAt_of_deltaLeR₁ {cfg : VeryNotSticky.{u}} (core : BallDataCore cfg)
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) :
    CapsuleComparableHomAt core ((edDilateConstant : NNReal) : ℝ) := by
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  have hL : (0 : ℝ) < (cfg.r₁ : ℝ) / 4 := by positivity
  have hδL : (cfg.δ : ℝ) ≤ 2 * ((cfg.r₁ : ℝ) / 4) := by linarith
  intro B hB i hi j hj hne
  have hswap : ¬ IsEssentiallyDistinct (ballCapsule core B j) (ballCapsule core B i) :=
    fun h => hne (isEssentiallyDistinct_symm h)
  rw [coe_edDilateConstant]
  exact ⟨capsule_subset_hom_of_not_essDistinct cfg.hδ (cfg.T i).toTube (cfg.T j).toTube
      (core.ctr B) (core.ctr B) hL hδL hne,
    capsule_subset_hom_of_not_essDistinct cfg.hδ (cfg.T j).toTube (cfg.T i).toTube
      (core.ctr B) (core.ctr B) hL hδL hswap⟩

/-- **The §G-1 plug, with comparability discharged.** Only the class count remains. -/
theorem capsuleInputs_of_floor {cfg : VeryNotSticky.{u}} (core : BallDataCore cfg) {M : NNReal}
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hfloor : edSegmentsConstant ≤ core.C₀)
    (hcount : CapsuleHomDilateCount core ((edDilateConstant : NNReal) : ℝ) M) :
    CapsuleCoreLine core ∧ CapsuleClassCount core M :=
  capsuleInputs_of_comparableHomAt_of_floor core hfloor
    (capsuleComparableHomAt_of_deltaLeR₁ core hδr) hcount

/-- **(C1) at `K′₀`, discharged**: the shading of a comparable tube inside a piece lies in the
`K′₀`-homothety dilate of the representative's capsule. This is the clause the repaired fold
consumes. -/
theorem capsuleShade_subset_hom_at_K₀ {cfg : VeryNotSticky.{u}} (core : BallDataCore cfg)
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hP16 : ∀ B ∈ core.bs, core.P B ⊆ ball (core.ctr B) ((cfg.r₁ : ℝ) / 16)) :
    ∀ B ∈ core.bs, ∀ i ∈ cfg.s, ∀ j ∈ cfg.s,
      ¬ IsEssentiallyDistinct (ballCapsule core B i) (ballCapsule core B j) →
        (cfg.T j).shade ∩ core.P B ⊆ ballCapsuleHom core ((edDilateConstant : NNReal) : ℝ) B i :=
  capsuleShade_subset_hom_of_comparableHomAt core hδr hP16
    (capsuleComparableHomAt_of_deltaLeR₁ core hδr)


/-! ### R-b: the angular step feeding `card_cone_le` -/

theorem lineAngle_neg_right {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) : NonSlab.lineAngle u (-v) = NonSlab.lineAngle u v := by
  rw [NonSlab.lineAngle, NonSlab.lineAngle, neg_neg, min_comm]

theorem lineAngle_le_of_min_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u w : E} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) {ρ : ℝ}
    (h : ‖u - w‖ ≤ ρ ∨ ‖u + w‖ ≤ ρ) :
    NonSlab.lineAngle u w ≤ Real.pi / 2 * ρ := by
  rcases h with h | h
  · exact (NonSlab.lineAngle_le_pi_div_two_mul_norm_sub hu hw).trans
      (mul_le_mul_of_nonneg_left h (by positivity))
  · have hnw : ‖(-w : E)‖ = 1 := by simpa using hw
    have := (NonSlab.lineAngle_le_pi_div_two_mul_norm_sub hu hnw).trans
      (mul_le_mul_of_nonneg_left (by simpa [sub_neg_eq_add] using h) (by positivity))
    rwa [lineAngle_neg_right] at this

/-- **A window endpoint is in the capsule.** -/
theorem corePt_window_mem_segCarrierSet {δ : NNReal} (T : Tube δ E3) (c : E3) {L : ℝ}
    (t : ℝ) (ht : t ∈ Set.Icc (segStart T c L) (segStart T c L + 2 * L)) :
    corePt T t ∈ segCarrierSet T c L := by
  refine Metric.self_subset_cthickening _ ?_
  rw [segment_eq_image' ℝ]
  refine ⟨(t - segStart T c L) / (2 * L), ⟨?_, ?_⟩, ?_⟩
  · rcases ht with ⟨h1, h2⟩
    rcases lt_or_ge (0 : ℝ) (2 * L) with hpos | hnp
    · positivity
    · have : t = segStart T c L := le_antisymm (by linarith) h1
      simp [this]
  · rcases ht with ⟨h1, h2⟩
    rcases lt_or_ge (0 : ℝ) (2 * L) with hpos | hnp
    · rw [div_le_one hpos]; linarith
    · have : t = segStart T c L := le_antisymm (by linarith) h1
      simp [this]
  · rcases lt_or_ge (0 : ℝ) (2 * L) with hpos | hnp
    · simp only [corePt]
      rw [show (T.x + (segStart T c L + 2 * L) • T.direction -
            (T.x + segStart T c L • T.direction)) = (2 * L) • T.direction from by module,
        smul_smul, div_mul_cancel₀ _ (ne_of_gt hpos)]
      module
    · have : t = segStart T c L := le_antisymm (by rcases ht with ⟨-, h2⟩; linarith)
        (ht.1)
      subst this
      simp

/-- **R-b — the angular step.** If the capsule of `Tj` lies in the `K`-homothety dilate of the
capsule of `Ti` (both of half-length `L` about the same point), then the two tube directions make
a line angle at most `(π/2) · 2Kδ/L`. With `L = r₁/4` that is `(π/2) · 8Kδ/r₁`, which is the `θ`
that `Kakeya.VeryNotSticky.card_cone_le` consumes, at `ρ = (2δ + θ)/4`. -/
theorem lineAngle_direction_le_of_capsule_subset_hom {δ : NNReal} (Ti Tj : Tube δ E3) (c : E3)
    {L : ℝ} (hL : 0 < L) {K : ℝ} (hK : 0 ≤ K)
    (hsub : segCarrierSet Tj c L ⊆ segCarrierSetHom K Ti c L) :
    NonSlab.lineAngle Tj.direction Ti.direction ≤
      Real.pi / 2 * (2 * K * (δ : ℝ) / L) := by
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have h2L : (0 : ℝ) < 2 * L := by linarith
  set aj := segStart Tj c L with haj
  set ai := segStart Ti c L with hai
  -- the two window endpoints of `Tj`
  have hp : corePt Tj aj ∈ segCarrierSet Tj c L :=
    corePt_window_mem_segCarrierSet Tj c aj ⟨le_rfl, by linarith⟩
  have hq : corePt Tj (aj + 2 * L) ∈ segCarrierSet Tj c L :=
    corePt_window_mem_segCarrierSet Tj c (aj + 2 * L) ⟨by linarith, le_rfl⟩
  -- decompose each along `Ti`'s core line
  have hdecomp : ∀ t : ℝ, corePt Tj t ∈ segCarrierSet Tj c L →
      ∃ (r : ℝ) (e : E3), ‖e‖ ≤ (δ : ℝ) ∧
        corePt Tj t = r • Ti.direction + K • e + capsuleCentre Ti c L := by
    intro t ht
    obtain ⟨u, hu, hEq⟩ := hsub ht
    rw [segCarrierSet_eq_biUnion] at hu
    obtain ⟨w, hw, huw⟩ := Set.mem_iUnion₂.mp hu
    obtain ⟨s, hs, rfl⟩ := segment_subset_corePt_image Ti (by linarith) hw
    refine ⟨K * (s - (ai + L)), u - corePt Ti s, ?_, ?_⟩
    · rw [← dist_eq_norm]
      exact Metric.mem_closedBall.1 huw
    · rw [← hEq]
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, capsuleCentre, corePt]
      module
  obtain ⟨rp, ep, hep, hpEq⟩ := hdecomp aj hp
  obtain ⟨rq, eq', heq, hqEq⟩ := hdecomp (aj + 2 * L) hq
  -- the chord
  have hchord : (2 * L) • Tj.direction = (rq - rp) • Ti.direction + K • (eq' - ep) := by
    have : corePt Tj (aj + 2 * L) - corePt Tj aj = (2 * L) • Tj.direction := by
      simp only [corePt]; module
    rw [← this, hpEq, hqEq]
    module
  -- normalise
  have hjn : ‖Tj.direction‖ = 1 := Tj.norm_direction
  have hin : ‖Ti.direction‖ = 1 := Ti.norm_direction
  set lam : ℝ := (rq - rp) / (2 * L) with hlam
  have hr : ‖Tj.direction - lam • Ti.direction‖ ≤ K * (δ : ℝ) / L := by
    have hscaled : Tj.direction - lam • Ti.direction =
        (2 * L)⁻¹ • (K • (eq' - ep)) := by
      have := congrArg (fun z => (2 * L)⁻¹ • z) hchord
      simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt h2L), one_smul, hlam] at this ⊢
      rw [smul_add, smul_smul, smul_smul] at this
      rw [show (2 * L)⁻¹ * (rq - rp) = (rq - rp) / (2 * L) by ring] at this
      rw [this]
      module
    rw [hscaled, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 h2L), abs_of_nonneg hK]
    have hee : ‖eq' - ep‖ ≤ 2 * (δ : ℝ) :=
      (norm_sub_le _ _).trans (by linarith)
    have hstep : K * ‖eq' - ep‖ ≤ K * (2 * (δ : ℝ)) := mul_le_mul_of_nonneg_left hee hK
    calc (2 * L)⁻¹ * (K * ‖eq' - ep‖) ≤ (2 * L)⁻¹ * (K * (2 * (δ : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep (le_of_lt (inv_pos.2 h2L))
      _ = K * (δ : ℝ) / L := by field_simp
  -- `|lam|` is close to `1`
  have hlam1 : |(|lam| - 1)| ≤ K * (δ : ℝ) / L := by
    have h1 : ‖lam • Ti.direction‖ = |lam| := by
      rw [norm_smul, Real.norm_eq_abs, hin, mul_one]
    have h2 := abs_norm_sub_norm_le (Tj.direction) (lam • Ti.direction)
    rw [hjn, h1] at h2
    rw [abs_sub_comm]
    exact le_trans h2 hr
  -- conclude
  refine lineAngle_le_of_min_norm hjn hin ?_
  rcases le_total 0 lam with hpos | hneg
  · left
    have hsgn : |lam| = lam := abs_of_nonneg hpos
    calc ‖Tj.direction - Ti.direction‖
        ≤ ‖Tj.direction - lam • Ti.direction‖ + ‖lam • Ti.direction - Ti.direction‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ K * (δ : ℝ) / L + K * (δ : ℝ) / L := by
          refine add_le_add hr ?_
          rw [show lam • Ti.direction - Ti.direction = (lam - 1) • Ti.direction by module,
            norm_smul, Real.norm_eq_abs, hin, mul_one]
          rw [← hsgn]; exact hlam1
      _ = 2 * K * (δ : ℝ) / L := by ring
  · right
    have hsgn : |lam| = -lam := abs_of_nonpos hneg
    calc ‖Tj.direction + Ti.direction‖
        ≤ ‖Tj.direction - lam • Ti.direction‖ + ‖lam • Ti.direction + Ti.direction‖ := by
          have : Tj.direction + Ti.direction
              = (Tj.direction - lam • Ti.direction) + (lam • Ti.direction + Ti.direction) := by
            module
          rw [this]; exact norm_add_le _ _
      _ ≤ K * (δ : ℝ) / L + K * (δ : ℝ) / L := by
          refine add_le_add hr ?_
          rw [show lam • Ti.direction + Ti.direction = (lam + 1) • Ti.direction by module,
            norm_smul, Real.norm_eq_abs, hin, mul_one]
          have habs : |lam + 1| = |(|lam| - 1)| := by
            rw [hsgn, show -lam - 1 = -(lam + 1) by ring, abs_neg]
          rw [habs]
          exact hlam1
      _ = 2 * K * (δ : ℝ) / L := by ring


/-- **R-b at the core level.** Every member of a comparability class of `i` in the ball `B` has
its direction within `θ = (π/2)·(8 K δ / r₁)` of `i`'s — the `hang` hypothesis of
`Kakeya.VeryNotSticky.card_cone_le`, at `ρ = (2δ + θ)/4`. -/
theorem lineAngle_le_of_ballCapsuleHom {cfg : VeryNotSticky.{u}} (core : BallDataCore cfg)
    {K : ℝ} (hK : 0 ≤ K) :
    ∀ B ∈ core.bs, ∀ i ∈ cfg.s, ∀ j ∈ cfg.s,
      ballCapsule core B j ⊆ ballCapsuleHom core K B i →
        NonSlab.lineAngle (cfg.T j).direction (cfg.T i).direction ≤
          Real.pi / 2 * (8 * K * (cfg.δ : ℝ) / (cfg.r₁ : ℝ)) := by
  intro B hB i hi j hj hsub
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  have hL : (0 : ℝ) < (cfg.r₁ : ℝ) / 4 := by positivity
  have h := lineAngle_direction_le_of_capsule_subset_hom (cfg.T i).toTube (cfg.T j).toTube
    (core.ctr B) hL hK hsub
  refine h.trans_eq ?_
  congr 1
  field_simp
  ring

/-- The fibre clause of the fold at an explicit budget.
The fold sets `Cm := M` and `m := 1`, so its fibre clause is `M ≤ B`.
The density-cap estimate gives `M ≤ C_fib · δ^{-(η + 2 exscal)}`, where
`C_fib = coneCardConstant · K′² · 16` is independent of `δ`. Taking
`B := C_fib · δ^{-(η + 2 exscal)}` preserves that constant. Taking
`B := δ^{-(η + 2 exscal)}` instead requires `C_fib ≤ 1`: at equal
exponents, smallness of `δ` cannot absorb a larger constant, as shown by
`Kakeya.VeryNotSticky.not_eventually_const_mul_rpow_le_self`. -/
theorem fibreClause_of_classCount {cfg : VeryNotSticky.{u}} {M C_fib : NNReal} {B : ENNReal}
    (hcount : (M : ENNReal) ≤
      (C_fib : ENNReal) * (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)))
    (hexit : (C_fib : ENNReal) * (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) ≤ B) :
    (M : ENNReal) * ((1 : NNReal) : ENNReal) ≤ B := by
  simpa using le_trans hcount hexit

end Kakeya.VeryNotSticky
