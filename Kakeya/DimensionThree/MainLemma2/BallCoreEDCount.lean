/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallCoreEDRescale
public import Kakeya.DimensionThree.MainLemma2.Conjunct6Refutation

/-!
# S-3: R31's class count from the density cap — and the geometry the dilated fold needs

Fifth file of the G13 stack (`BallCoreEDSegments`, `BallCoreEDCapsule`, `BallCoreEDComparable`,
`BallCoreEDRescale`, this). **Patches 2 and 3 of that stack must land together**; this one comes
last.

## S-3 — the class count, without an essential-distinctness hypothesis

 §G-addendum (a) rejects an `essDistinct` field on `cfg.s` and rules that the class
count must come from `cfg.maxDensity_le`. It does:
`Kakeya.VeryNotSticky.capsuleHomDilateCount_of_radiusFloor` derives
`CapsuleHomDilateCount core K′₀ (edClassCountConstant · δ^{-(η + 2 exscal)})` from the existing
`Kakeya.VeryNotSticky.card_cone_le` — i.e. from `Δmax(𝕋) ≤ δ^{-η}` — using
`Kakeya.VeryNotSticky.lineAngle_le_of_ballCapsuleHom` (R-b) for its `hang` and
`capsuleHomDilateCount_of_carrierCap` for its `hx`.

The cone radius is `ρ = 8 K′₀ δ / r₁`, for which `ρ · r₁ = 8 K′₀ δ` **exactly**, so the
`δ`-power bookkeeping is an identity, not an estimate: the two sides of the count agree after
multiplying by `r₁²`, and `r₁² = δ^{2 exscal}` is `cfg.r₁`'s definition.

`ρ ≤ 1` is what forces the third hypothesis floor,
`Kakeya.VeryNotSticky.edRadiusConstant · δ ≤ r₁` in place of the caller's `16 δ ≤ r₁`. Like
§G-1's floors on `C₀` and `c₁` this is a hypothesis-floor move on a caller-chosen constant, it
costs nothing (`r₁/δ = δ^{exscal−1} → ∞`), and `deltaLeR₁_of_radiusFloor` shows it implies the
old binder.

`capsuleInputs_of_floors` composes S-3 with R-a: **both existing obligations, from the two floors
alone.** `fibreClause_at_floors` is the R-c plug, with the budget `B` still a binder.

## S-4 prerequisites — the geometry of the dilated carrier

The repaired fold presents a segment as the `K′₀`-homothety dilate of its capsule. What that
costs is computed here:

* `Kakeya.VeryNotSticky.segCarrierSetHom_eq` / `segCarrierSetHom_eq_genCapsule` — the dilate **is
  a capsule**, of radius `K δ` and half-length `K L`, about the same centre;
* `Kakeya.VeryNotSticky.genCapsule` and its five thickness lemmas — the capsule API at an
  arbitrary radius and half-length, which the undilated `segCarrierSet` lemmas do not cover;
* `Kakeya.VeryNotSticky.hasThicknesses_segCarrierSetHom` — profile `![r₁, δ, δ]` at the constant
  `4 K`, i.e. **exactly  §G-1's `edSegmentsConstant`**, and the reason the floor belongs
  on the hypothesis `C₀` and not on the conclusion;
* `Kakeya.VeryNotSticky.thickness_segCarrierSetHom_le_two_nsmul` — `segs_dims` survives at the
  same constant `2`.

Together with `segsDensity_of_segCarrierSetAt` (`c₁`'s price) and `capsuleShade_subset_hom_at_K₀`
(the (C1) clause) this is every per-field price of the dilated fold; what remains is the
assembly.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace Kakeya.VeryNotSticky

universe u



open scoped Classical in
/-- **S-3 — the class count, from the density cap.** The comparability class of `i` at a point
`z`, counted on the tube carriers, has at most
`edClassCountConstant · δ^{-(η + 2 exscal)}` members.

No essential-distinctness hypothesis on `cfg.s` is used ( §G-addendum (a)); the bound
comes from `Kakeya.VeryNotSticky.card_cone_le`, i.e. from `cfg.maxDensity_le`. The cone radius is
`ρ = 8 K′₀ δ / r₁`, admissible because of the radius floor, and `ρ · r₁ = 8 K′₀ δ` exactly, so the
`δ`-power bookkeeping is an identity rather than an estimate. -/
theorem capsuleHomDilateCount_of_radiusFloor {cfg : VeryNotSticky.{u}} (core : BallDataCore cfg)
    (hfloor : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) :
    CapsuleHomDilateCount core ((edDilateConstant : NNReal) : ℝ)
      (edClassCountConstant * cfg.δ ^ (-(cfg.η + 2 * cfg.exscal))) := by
  classical
  -- numerics
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  have hr₁ne : cfg.r₁ ≠ 0 := by
    intro h; rw [h] at hr₁pos; simp at hr₁pos
  have hδpos : (0 : ℝ) < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
  have hKR : (1 : ℝ) ≤ ((edDilateConstant : NNReal) : ℝ) := by
    exact_mod_cast one_le_edDilateConstant
  have hK0 : (0 : ℝ) ≤ ((edDilateConstant : NNReal) : ℝ) := by linarith
  have hr₁1 : (cfg.r₁ : ℝ) ≤ 1 := r₁_le_one cfg
  have hδ1 : (cfg.δ : ℝ) ≤ 1 := by exact_mod_cast cfg.hδ1
  have h8K : ((edRadiusConstant : NNReal) : ℝ) = 8 * ((edDilateConstant : NNReal) : ℝ) := by
    rw [edRadiusConstant]; push_cast; ring
  rw [h8K] at hfloor
  -- the cone radius
  set K : ℝ := ((edDilateConstant : NNReal) : ℝ) with hKdef
  set ρ : NNReal := 8 * edDilateConstant * cfg.δ / cfg.r₁ with hρdef
  have hρR : (ρ : ℝ) = 8 * K * (cfg.δ : ℝ) / (cfg.r₁ : ℝ) := by
    rw [hρdef]; push_cast; ring
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
        nlinarith [mul_nonneg hK0 (le_of_lt hδpos)]
      rw [h1]
      gcongr
    have : 16 * K * (cfg.δ : ℝ) / (cfg.r₁ : ℝ) + 16 * K * (cfg.δ : ℝ) / (cfg.r₁ : ℝ)
        = 4 * (8 * K * (cfg.δ : ℝ) / (cfg.r₁ : ℝ)) := by ring
    linarith
  -- the count, on the carriers (the shape `card_cone_le`'s `hx` has)
  refine capsuleHomDilateCount_of_carrierCap core ?_
  intro B hB i hi z
  set t : Finset cfg.ι := cfg.s.filter (fun j => z ∈ (cfg.T j).carrier ∧
    ballCapsule core B j ⊆ ballCapsuleHom core K B i) with htdef
  have hmem : ∀ j ∈ t, j ∈ cfg.s ∧ z ∈ (cfg.T j).carrier ∧
      ballCapsule core B j ⊆ ballCapsuleHom core K B i := by
    intro j hj
    rw [htdef, Finset.mem_filter] at hj
    exact ⟨hj.1, hj.2.1, hj.2.2⟩
  have hcone := cfg.card_cone_le hρ1 z ((cfg.T i).direction) (cfg.T i).norm_direction hrad
    (Finset.filter_subset _ _)
    (fun j hj => (hmem j hj).2.1)
    (fun j hj => lineAngle_le_of_ballCapsuleHom core hK0 B hB i hi j
      (hmem j hj).1 (hmem j hj).2.2)
  -- arithmetic
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
  -- both sides become the same expression after multiplying by `r₁ ^ 2`
  have hr₁sq0 : (cfg.r₁ : ENNReal) ^ 2 ≠ 0 := pow_ne_zero _ hr₁E0
  have hr₁sqtop : (cfg.r₁ : ENNReal) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hr₁Etop
  refine (ENNReal.mul_le_mul_iff_left hr₁sq0 hr₁sqtop).mp ?_
  have hρr : (ρ : ENNReal) * (cfg.r₁ : ENNReal) = 8 * (edDilateConstant : ENNReal) *
      (cfg.δ : ENNReal) := by
    have : ρ * cfg.r₁ = 8 * edDilateConstant * cfg.δ := by
      rw [hρdef, div_mul_cancel₀ _ hr₁ne]
    calc (ρ : ENNReal) * (cfg.r₁ : ENNReal) = ((ρ * cfg.r₁ : NNReal) : ENNReal) := by
          push_cast; ring
      _ = ((8 * edDilateConstant * cfg.δ : NNReal) : ENNReal) := by rw [this]
      _ = 8 * (edDilateConstant : ENNReal) * (cfg.δ : ENNReal) := by push_cast; ring
  have hr₁pow : (cfg.r₁ : ENNReal) ^ 2 = (cfg.δ : ENNReal) ^ (2 * cfg.exscal) := by
    have h1 : ((cfg.r₁ : NNReal) : ENNReal) = (cfg.δ : ENNReal) ^ cfg.exscal := by
      rw [show cfg.r₁ = cfg.δ ^ cfg.exscal from rfl,
        ENNReal.coe_rpow_of_ne_zero (by exact_mod_cast ne_of_gt cfg.hδ)]
    rw [h1, ← ENNReal.rpow_natCast ((cfg.δ : ENNReal) ^ cfg.exscal) 2,
      ← ENNReal.rpow_mul]
    norm_num
    ring_nf
  have hδcancel : (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) *
      (cfg.δ : ENNReal) ^ (2 * cfg.exscal) = (cfg.δ : ENNReal) ^ (-cfg.η) := by
    rw [← ENNReal.rpow_add _ _ hδE0 hδEtop]
    ring_nf
  have hconst : ((edClassCountConstant : NNReal) : ENNReal) *
      ((Tube.le_volume.c 3 : NNReal) : ENNReal)
      = 64 * (64 * ((Tube.volume_le.C 3 : NNReal) : ENNReal)) *
        ((edDilateConstant : ENNReal)) ^ 2 := by
    have hc : (Tube.le_volume.c 3) ≠ 0 := (Tube.le_volume.c_pos 3).ne'
    have hnn : edClassCountConstant * Tube.le_volume.c 3
        = 64 * (64 * Tube.volume_le.C 3) * edDilateConstant ^ 2 := by
      rw [edClassCountConstant, coneCardConstant]
      field_simp
    calc ((edClassCountConstant : NNReal) : ENNReal) *
          ((Tube.le_volume.c 3 : NNReal) : ENNReal)
        = ((edClassCountConstant * Tube.le_volume.c 3 : NNReal) : ENNReal) := by push_cast; ring
      _ = ((64 * (64 * Tube.volume_le.C 3) * edDilateConstant ^ 2 : NNReal) : ENNReal) := by
          rw [hnn]
      _ = _ := by push_cast; ring
  refine le_of_eq ?_
  calc (cfg.δ : ENNReal) ^ (-cfg.η) *
        (64 * (((Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2)) *
        (cfg.r₁ : ENNReal) ^ 2
      = (cfg.δ : ENNReal) ^ (-cfg.η) * (64 * ((Tube.volume_le.C 3 : NNReal) : ENNReal)) *
          ((ρ : ENNReal) * (cfg.r₁ : ENNReal)) ^ 2 := by ring
    _ = (cfg.δ : ENNReal) ^ (-cfg.η) * (64 * ((Tube.volume_le.C 3 : NNReal) : ENNReal)) *
          (8 * (edDilateConstant : ENNReal) * (cfg.δ : ENNReal)) ^ 2 := by rw [hρr]
    _ = 64 * (64 * ((Tube.volume_le.C 3 : NNReal) : ENNReal)) *
          ((edDilateConstant : ENNReal)) ^ 2 * ((cfg.δ : ENNReal) ^ (-cfg.η)) *
          (cfg.δ : ENNReal) ^ 2 := by ring
    _ = ((edClassCountConstant : NNReal) : ENNReal) *
          ((Tube.le_volume.c 3 : NNReal) : ENNReal) * ((cfg.δ : ENNReal) ^ (-cfg.η)) *
          (cfg.δ : ENNReal) ^ 2 := by rw [hconst]
    _ = ((edClassCountConstant : NNReal) : ENNReal) *
          ((cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) *
            (cfg.δ : ENNReal) ^ (2 * cfg.exscal)) *
          (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2) := by
        rw [hδcancel]; ring
    _ = ((edClassCountConstant * cfg.δ ^ (-(cfg.η + 2 * cfg.exscal)) : NNReal) : ENNReal) *
          (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2) *
          (cfg.r₁ : ENNReal) ^ 2 := by
        have hcoe : ((edClassCountConstant * cfg.δ ^ (-(cfg.η + 2 * cfg.exscal)) :
              NNReal) : ENNReal)
            = ((edClassCountConstant : NNReal) : ENNReal) *
              (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) := by
          rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero (ne_of_gt cfg.hδ)]
        rw [hr₁pow, hcoe]
        ring


/-- The class count, in the `C_fib`-binder shape of `fibreClause_of_classCount` (R-c). -/
theorem classCount_le_fibreBudget {cfg : VeryNotSticky.{u}} :
    ((edClassCountConstant * cfg.δ ^ (-(cfg.η + 2 * cfg.exscal)) : NNReal) : ENNReal)
      ≤ (edClassCountConstant : ENNReal) *
        (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) := by
  refine le_of_eq ?_
  rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero (ne_of_gt cfg.hδ)]

/-- **S-3 composed with R-a: both existing obligations from the two floors alone.**

`CapsuleComparableHomAt` is `capsuleComparableHomAt_of_deltaLeR₁` (R-a) and the class count is
`capsuleHomDilateCount_of_radiusFloor` (S-3, from `card_cone_le`, i.e. from `cfg.maxDensity_le`);
neither takes an essential-distinctness hypothesis on `cfg.s`. -/
theorem capsuleInputs_of_floors {cfg : VeryNotSticky.{u}} (core : BallDataCore cfg)
    (hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hfloor : edSegmentsConstant ≤ core.C₀) :
    CapsuleCoreLine core ∧
      CapsuleClassCount core
        (edClassCountConstant * cfg.δ ^ (-(cfg.η + 2 * cfg.exscal))) :=
  capsuleInputs_of_floor core (deltaLeR₁_of_radiusFloor hrad) hfloor
    (capsuleHomDilateCount_of_radiusFloor core hrad)

/-- The fibre clause at the hypothesis floors, with an explicit budget `B`.
The fold uses `Cm · m = M · 1`, and
`M ≤ edClassCountConstant · δ^{-(η + 2 exscal)}`. -/
theorem fibreClause_at_floors {cfg : VeryNotSticky.{u}} {B : ENNReal}
    (hexit : (edClassCountConstant : ENNReal) *
      (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) ≤ B) :
    ((edClassCountConstant * cfg.δ ^ (-(cfg.η + 2 * cfg.exscal)) : NNReal) : ENNReal) *
        ((1 : NNReal) : ENNReal) ≤ B :=
  fibreClause_of_classCount classCount_le_fibreBudget hexit


/-! ### S-4 prerequisites: the homothety dilate is a capsule of radius `K δ`
and half-length `K L` -/

theorem homothety_corePt {δ : NNReal} (T : Tube δ E3) (c : E3) (L K t : ℝ) :
    AffineMap.homothety (capsuleCentre T c L) K (corePt T t) =
      corePt T (segStart T c L + L + K * (t - (segStart T c L + L))) := by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, capsuleCentre, corePt]
  module

/-- **The homothety dilate of a capsule is a capsule** — of radius `K δ` and half-length `K L`,
about the same centre. This is what a `BallDataCore` whose segments are the dilated bodies has to
be measured against. -/
theorem segCarrierSetHom_eq {δ : NNReal} (T : Tube δ E3) (c : E3) {L K : ℝ} (hK : 0 < K) :
    segCarrierSetHom K T c L =
      cthickening (K * (δ : ℝ))
        (segment ℝ (corePt T (segStart T c L + L - K * L))
          (corePt T (segStart T c L + L + K * L))) := by
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hKδ : (0 : ℝ) ≤ K * (δ : ℝ) := by positivity
  have hp : AffineMap.homothety (capsuleCentre T c L) K (corePt T (segStart T c L)) =
      corePt T (segStart T c L + L - K * L) := by
    rw [homothety_corePt]; ring_nf
  have hq : AffineMap.homothety (capsuleCentre T c L) K
      (corePt T (segStart T c L + 2 * L)) = corePt T (segStart T c L + L + K * L) := by
    rw [homothety_corePt]; ring_nf
  have hball : ∀ w : E3, (AffineMap.homothety (capsuleCentre T c L) K) '' closedBall w (δ : ℝ)
      = closedBall (AffineMap.homothety (capsuleCentre T c L) K w) (K * (δ : ℝ)) :=
    fun w => homothety_image_closedBall hK w (δ : ℝ)
  rw [segCarrierSetHom, segCarrierSet_eq_biUnion, Set.image_iUnion₂]
  simp only [hball]
  rw [isClosed_segment.cthickening_eq_biUnion_closedBall hKδ, ← hp, ← hq,
    ← homothety_image_segment, Set.biUnion_image]

/-! #### The thickness profile of a generalized capsule -/

/-- The capsule of radius `r` about the core sub-segment `[corePt T b, corePt T (b + 2 m)]`. -/
noncomputable def genCapsule {δ : NNReal} (T : Tube δ E3) (r b m : ℝ) : Set E3 :=
  cthickening r (segment ℝ (corePt T b) (corePt T (b + 2 * m)))

theorem genCapsule_subset_closedBall {δ : NNReal} (T : Tube δ E3) {r b m : ℝ}
    (hr : 0 ≤ r) (hm : 0 ≤ m) :
    genCapsule T r b m ⊆ closedBall (corePt T (b + m)) (r + m) := by
  refine subset_trans (cthickening_subset_of_subset _
    (segment_subset_closedBall_mid T b m hm)) ?_
  rw [cthickening_closedBall hr hm]

theorem isBounded_genCapsule {δ : NNReal} (T : Tube δ E3) {r b m : ℝ}
    (hr : 0 ≤ r) (hm : 0 ≤ m) : Bornology.IsBounded (genCapsule T r b m) :=
  Metric.isBounded_closedBall.subset (genCapsule_subset_closedBall T hr hm)

theorem genCapsule_subset_cthickening_line {δ : NNReal} (T : Tube δ E3) {r b m : ℝ}
    (hm : 0 ≤ m) {C : ℝ} (hC : r ≤ C) :
    genCapsule T r b m ⊆ cthickening C
      (AffineSubspace.mk' (corePt T b) (Submodule.span ℝ {T.direction}) : Set E3) := by
  have hline : segment ℝ (corePt T b) (corePt T (b + 2 * m)) ⊆
      (AffineSubspace.mk' (corePt T b) (Submodule.span ℝ {T.direction}) : Set E3) := by
    intro z hz
    obtain ⟨u, _, rfl⟩ := segment_subset_corePt_image T (by linarith) hz
    have : corePt T u = (u - b) • T.direction +ᵥ corePt T b := by
      simp only [corePt, vadd_eq_add]; module
    rw [this]
    exact AffineSubspace.vadd_mem_mk' _
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  exact subset_trans (Metric.cthickening_subset_of_subset r hline) (Metric.cthickening_mono hC _)

theorem le_thickness_genCapsule {δ : NNReal} (T : Tube δ E3) {r b m : ℝ}
    (hr : 0 ≤ r) (hm : 0 ≤ m) {n : ℕ} (hn : n < 3) :
    r ≤ Metric.thickness ℝ (genCapsule T r b m) n := by
  have hbdd := isBounded_genCapsule (b := b) T hr hm
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  have hsub : closedBall (corePt T b) r ⊆ genCapsule T r b m :=
    Metric.closedBall_subset_cthickening (left_mem_segment ℝ _ _) r
  have h1 : (r.toNNReal : ENNReal) ≤
      Metric.ethickness ℝ (closedBall (corePt T b) ((r.toNNReal : NNReal) : ℝ)) n :=
    le_ethickness_closedBall (V := E3) r.toNNReal (by rw [hfr]; exact hn)
  rw [Real.coe_toNNReal r hr] at h1
  have h2 := Metric.ethickness_monotone (𝕜 := ℝ) hsub n
  have h3 : ENNReal.ofReal r ≤ Metric.ethickness ℝ (genCapsule T r b m) n := by
    calc ENNReal.ofReal r = ((r.toNNReal : NNReal) : ENNReal) := rfl
      _ ≤ _ := h1.trans h2
  rw [Metric.ethickness_thickness' hbdd n] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (Metric.thickness_nonneg _ _)).1 h3

theorem thickness_genCapsule_le {δ : NNReal} (T : Tube δ E3) {r b m : ℝ}
    (hr : 0 ≤ r) (hm : 0 ≤ m) {n : ℕ} (hn : 1 ≤ n) :
    Metric.thickness ℝ (genCapsule T r b m) n ≤ r := by
  have hrank : Module.rank ℝ
      (AffineSubspace.mk' (corePt T b) (Submodule.span ℝ {T.direction})).direction ≤
        (n : Cardinal) := by
    rw [AffineSubspace.direction_mk']
    refine le_trans (rank_span_le _) ?_
    simp only [Cardinal.mk_fintype]
    exact_mod_cast Nat.one_le_cast.2 hn
  exact Metric.thickness_le_of_cthickening hr hrank
    (genCapsule_subset_cthickening_line T hm (le_refl r))

theorem le_thickness_genCapsule_zero {δ : NNReal} (T : Tube δ E3) {r b m : ℝ}
    (hr : 0 ≤ r) (hm : 0 ≤ m) : m ≤ Metric.thickness ℝ (genCapsule T r b m) 0 := by
  have hbdd := isBounded_genCapsule (b := b) T hr hm
  have hmemL : corePt T b ∈ genCapsule T r b m :=
    Metric.self_subset_cthickening _ (left_mem_segment ℝ _ _)
  have hmemR : corePt T (b + 2 * m) ∈ genCapsule T r b m :=
    Metric.self_subset_cthickening _ (right_mem_segment ℝ _ _)
  have hd : dist (corePt T b) (corePt T (b + 2 * m)) = 2 * m := by
    rw [dist_corePt, show b - (b + 2 * m) = -(2 * m) by ring, abs_neg,
      abs_of_nonneg (by linarith)]
  have h := Metric.half_dist_le_ethickness_zero (𝕜 := ℝ) hmemL hmemR
  rw [hd, Metric.ethickness_thickness' hbdd 0] at h
  have := (ENNReal.ofReal_le_ofReal_iff (Metric.thickness_nonneg _ _)).1 h
  linarith

theorem thickness_genCapsule_zero_le {δ : NNReal} (T : Tube δ E3) {r b m : ℝ}
    (hr : 0 ≤ r) (hm : 0 ≤ m) : Metric.thickness ℝ (genCapsule T r b m) 0 ≤ r + m :=
  Metric.thickness_le_of_subset_closedBall (genCapsule_subset_closedBall T hr hm)
    (by positivity) 0


theorem segCarrierSetHom_eq_genCapsule {δ : NNReal} (T : Tube δ E3) (c : E3) {L K : ℝ}
    (hK : 0 < K) :
    segCarrierSetHom K T c L =
      genCapsule T (K * (δ : ℝ)) (segStart T c L + L - K * L) (K * L) := by
  rw [segCarrierSetHom_eq T c hK, genCapsule]
  congr 3
  ring

/-- **The price of the homothety dilate, in the constant of `BallDataCore.segs_thickness`.**
The `K`-homothety dilate of a capsule of half-length `L = r₁/4` has the profile `![r₁, δ, δ]` at
the constant `4 K` — the thin thicknesses are exactly `K δ` and the long one is between `K L` and
`K δ + K L`. This is  §G-1's `edSegmentsConstant = 4 K′` and the reason the floor is on
the **hypothesis** `C₀`, not on the conclusion. -/
theorem hasThicknesses_segCarrierSetHom {δ K : NNReal} (hK : 1 ≤ K)
    (T : Tube δ E3) (c : E3) {L : ℝ} (hL : 0 ≤ L) (hδL : (δ : ℝ) ≤ L) :
    Kakeya.HasThicknesses (segCarrierSetHom ((K : NNReal) : ℝ) T c L) (4 * K)
      ![4 * L, (δ : ℝ), (δ : ℝ)] := by
  have hKR : (1 : ℝ) ≤ ((K : NNReal) : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < ((K : NNReal) : ℝ) := by linarith
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hr0 : (0 : ℝ) ≤ ((K : NNReal) : ℝ) * (δ : ℝ) := by positivity
  have hm0 : (0 : ℝ) ≤ ((K : NNReal) : ℝ) * L := by positivity
  rw [segCarrierSetHom_eq_genCapsule T c hKpos]
  have h0l := le_thickness_genCapsule_zero T (r := ((K : NNReal) : ℝ) * (δ : ℝ))
    (b := segStart T c L + L - ((K : NNReal) : ℝ) * L) (m := ((K : NNReal) : ℝ) * L) hr0 hm0
  have h0u := thickness_genCapsule_zero_le T (r := ((K : NNReal) : ℝ) * (δ : ℝ))
    (b := segStart T c L + L - ((K : NNReal) : ℝ) * L) (m := ((K : NNReal) : ℝ) * L) hr0 hm0
  have h1l := le_thickness_genCapsule T (r := ((K : NNReal) : ℝ) * (δ : ℝ))
    (b := segStart T c L + L - ((K : NNReal) : ℝ) * L) (m := ((K : NNReal) : ℝ) * L) hr0 hm0
    (n := 1) (by norm_num)
  have h1u := thickness_genCapsule_le T (r := ((K : NNReal) : ℝ) * (δ : ℝ))
    (b := segStart T c L + L - ((K : NNReal) : ℝ) * L) (m := ((K : NNReal) : ℝ) * L) hr0 hm0
    (n := 1) (by norm_num)
  have h2l := le_thickness_genCapsule T (r := ((K : NNReal) : ℝ) * (δ : ℝ))
    (b := segStart T c L + L - ((K : NNReal) : ℝ) * L) (m := ((K : NNReal) : ℝ) * L) hr0 hm0
    (n := 2) (by norm_num)
  have h2u := thickness_genCapsule_le T (r := ((K : NNReal) : ℝ) * (δ : ℝ))
    (b := segStart T c L + L - ((K : NNReal) : ℝ) * L) (m := ((K : NNReal) : ℝ) * L) hr0 hm0
    (n := 2) (by norm_num)
  have hc : ((4 * K : NNReal) : ℝ) = 4 * ((K : NNReal) : ℝ) := by push_cast; ring
  intro k
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  have hI : (4 * ((K : NNReal) : ℝ))⁻¹ * (4 * L) ≤ ((K : NNReal) : ℝ) * L := by
    rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hII : ((K : NNReal) : ℝ) * (δ : ℝ) + ((K : NNReal) : ℝ) * L
      ≤ 4 * ((K : NNReal) : ℝ) * (4 * L) := by nlinarith
  have hIII : (4 * ((K : NNReal) : ℝ))⁻¹ * (δ : ℝ) ≤ ((K : NNReal) : ℝ) * (δ : ℝ) := by
    have hinv : (4 * ((K : NNReal) : ℝ))⁻¹ ≤ ((K : NNReal) : ℝ) := by
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      nlinarith
    nlinarith
  have hIV : ((K : NNReal) : ℝ) * (δ : ℝ) ≤ 4 * ((K : NNReal) : ℝ) * (δ : ℝ) := by nlinarith
  rcases hk with rfl | rfl | rfl <;> refine ⟨?_, ?_⟩ <;>
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, hc] <;> linarith

/-- **`segs_dims` for homothety dilates**: any two of them, of the same `K` and `L`, have
`2`-comparable thickness profiles. -/
theorem thickness_segCarrierSetHom_le_two_nsmul {δ K : NNReal} (hK : 1 ≤ K)
    (T T' : Tube δ E3) (c c' : E3) {L : ℝ} (hL : 0 ≤ L) (hδL : (δ : ℝ) ≤ L) :
    Metric.thickness ℝ (segCarrierSetHom ((K : NNReal) : ℝ) T c L) ≤
      2 • Metric.thickness ℝ (segCarrierSetHom ((K : NNReal) : ℝ) T' c' L) := by
  have hKR : (1 : ℝ) ≤ ((K : NNReal) : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < ((K : NNReal) : ℝ) := by linarith
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hr0 : (0 : ℝ) ≤ ((K : NNReal) : ℝ) * (δ : ℝ) := by positivity
  have hm0 : (0 : ℝ) ≤ ((K : NNReal) : ℝ) * L := by positivity
  rw [segCarrierSetHom_eq_genCapsule T c hKpos, segCarrierSetHom_eq_genCapsule T' c' hKpos]
  intro n
  have hnn : ∀ p : ℕ, 0 ≤ Metric.thickness ℝ
      (genCapsule T' (((K : NNReal) : ℝ) * (δ : ℝ))
        (segStart T' c' L + L - ((K : NNReal) : ℝ) * L) (((K : NNReal) : ℝ) * L)) p :=
    fun p => Metric.thickness_nonneg _ _
  have hsm : (2 • Metric.thickness ℝ
      (genCapsule T' (((K : NNReal) : ℝ) * (δ : ℝ))
        (segStart T' c' L + L - ((K : NNReal) : ℝ) * L) (((K : NNReal) : ℝ) * L))) n
      = 2 * Metric.thickness ℝ
      (genCapsule T' (((K : NNReal) : ℝ) * (δ : ℝ))
        (segStart T' c' L + L - ((K : NNReal) : ℝ) * L) (((K : NNReal) : ℝ) * L)) n := by simp
  rw [hsm]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n
    · have h0u := thickness_genCapsule_zero_le T (r := ((K : NNReal) : ℝ) * (δ : ℝ))
        (b := segStart T c L + L - ((K : NNReal) : ℝ) * L)
        (m := ((K : NNReal) : ℝ) * L) hr0 hm0
      have h0l := le_thickness_genCapsule_zero T' (r := ((K : NNReal) : ℝ) * (δ : ℝ))
        (b := segStart T' c' L + L - ((K : NNReal) : ℝ) * L)
        (m := ((K : NNReal) : ℝ) * L) hr0 hm0
      have := hnn 0
      nlinarith
    · have h1u := thickness_genCapsule_le T (r := ((K : NNReal) : ℝ) * (δ : ℝ))
        (b := segStart T c L + L - ((K : NNReal) : ℝ) * L)
        (m := ((K : NNReal) : ℝ) * L) hr0 hm0 (n := 1) (by norm_num)
      have h1l := le_thickness_genCapsule T' (r := ((K : NNReal) : ℝ) * (δ : ℝ))
        (b := segStart T' c' L + L - ((K : NNReal) : ℝ) * L)
        (m := ((K : NNReal) : ℝ) * L) hr0 hm0 (n := 1) (by norm_num)
      have := hnn 1
      linarith
    · have h2u := thickness_genCapsule_le T (r := ((K : NNReal) : ℝ) * (δ : ℝ))
        (b := segStart T c L + L - ((K : NNReal) : ℝ) * L)
        (m := ((K : NNReal) : ℝ) * L) hr0 hm0 (n := 2) (by norm_num)
      have h2l := le_thickness_genCapsule T' (r := ((K : NNReal) : ℝ) * (δ : ℝ))
        (b := segStart T' c' L + L - ((K : NNReal) : ℝ) * L)
        (m := ((K : NNReal) : ℝ) * L) hr0 hm0 (n := 2) (by norm_num)
      have := hnn 2
      linarith
  · have hz : Metric.thickness ℝ
        (genCapsule T (((K : NNReal) : ℝ) * (δ : ℝ))
          (segStart T c L + L - ((K : NNReal) : ℝ) * L) (((K : NNReal) : ℝ) * L)) n = 0 := by
      refine Metric.thickness_eq_zero_of_finrank_le (𝕜 := ℝ) ?_
      have h3 : Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
        rw [← Module.finrank_eq_rank]; simp
      rw [h3]
      exact_mod_cast Nat.cast_le.2 hn
    rw [hz]
    have := hnn n
    linarith

end Kakeya.VeryNotSticky
