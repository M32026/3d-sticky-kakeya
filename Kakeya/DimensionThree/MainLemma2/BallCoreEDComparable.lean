/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallCoreEDCapsule
public import Kakeya.DimensionThree.MainLemma2.EDConstants
public import Kakeya.Tube.Dilate

/-!
# Capsule volume and homothety dilation

This file develops the volume and comparability estimates for capsule segments.

## (1) The capsule volume lower bound, and the `δ`-free dilate price

`Kakeya.VeryNotSticky.le_volumeReal_segCarrierSet`: `c₃ · L · δ² ≤ |segCarrierSet T c L|`, where
`c₃ = Metric.lt_volume_convexHull.c 3` is the inscribed-simplex constant. The capsule is convex
(`Convex.cthickening` of a segment) and its three thicknesses are already pinned
(`le_thickness_segCarrierSet_zero`, `le_thickness_segCarrierSet`), so this is one application of
`Convex.prod_thickness_le_volumeReal` — the same input `volume_ge_of_tubeProfile`
(`TangentialCase.lean:2428`) uses. The `δ³` bound
`volume_closedBall_le_volume_segCarrierSet` could not give a `δ`-free ratio; this one can:

* `Kakeya.VeryNotSticky.volume_segCarrierSetAt_le_mul_volume_segCarrierSet` —
  `c₃ · |K-dilate| ≤ 16 K² · |capsule|`, division-free, with **no `δ`**;
* `Kakeya.VeryNotSticky.segsDensity_of_segCarrierSetAt` — hence `segs_density` survives the
  dilate at the cost `c₁ ↦ c₁ · c₃ / (16 K²)`, which is  §G-1's `edDensityConstant`.

## (2) The dilate `K′`, and the shape it must have

`Kakeya.VeryNotSticky.not_subset_segCarrierSetAt_of_axial_offset` pins the mechanism that
**refutes** the radius-only reading of comparability used in `BallCoreEDCapsule.lean`: the
`segStart` clamp can put two windows of one ball at an *axial* offset of order `L = r₁/4` while
their capsules are still not essentially distinct, and no `δ`-free `K` has `K δ ≥ L`. The dilate
must therefore be a **homothety**, scaling the core window as well as the radius — which is the
shape of the existing `Kakeya.Tube.dilate` and of `Kakeya.Tube.tubeOverlapCoreClose`.

* `Kakeya.VeryNotSticky.segCarrierSetHom` — the homothety dilate of a capsule;
* `Kakeya.VeryNotSticky.CapsuleComparableHomAt` — comparability in GWZ's own shape;
* `capsuleShade_subset_hom_of_comparableHomAt`, `capsuleCoreLine_of_comparableHomAt`,
  `capsuleClassCount_of_homDilateCount` — (C1), (C2), (C3) from it, at general `K`;
* `comparableHomAt_of_comparableAt` — the radius-only form implies this one, so
  `BallCoreEDCapsule.lean`'s three reductions are subsumed;
* `Kakeya.VeryNotSticky.edComparabilityConstant = Kakeya.Tube.tubeOverlapCoreClose.C 3
  = 9 + 2·4³/c₃` — **the value `K′₀`**, read off the only route in the tree that can prove
  comparability from `¬ IsEssentiallyDistinct`, together with its unit-tube instance
  `tube_subset_dilate_of_not_essDistinct`.

##  §G-1's hypothesis floor

`edDilateConstant` (`= K′`), `edSegmentsConstant = 4 K′`, `edDensityConstant = 4 K′²` are the
three named constants of the licensed repair, which moves the **hypothesis floor**
(`4 ≤ C₀ ↦ edSegmentsConstant ≤ C₀`, `4 c₁ ballCoverConstant ≤ 1 ↦ edDensityConstant c₁ … ≤ 1`)
and leaves every conclusion verbatim. `edDilateConstant_le_of_floor` and
`two_mul_edDilateConstant_le_of_floor` discharge the addendum's side conditions from the one
floor, and `capsuleInputs_of_comparableHomAt_of_floor` is the plug.

## §G-3 and §G-addendum (a)

`Kakeya.VeryNotSticky.not_eventually_const_mul_rpow_le_self` records the boundary of the `∀ᶠ δ`
device: it absorbs a `δ`-free constant across a **strict** exponent gap and not at equal
exponents. `capsuleHomDilateCount_of_carrierCap` restates (C3)'s count on the tube **carriers**,
the shape `Kakeya.VeryNotSticky.card_cone_le`'s counting hypothesis has, so that the density-cap
estimate composes without an essential-distinctness hypothesis on `cfg.s`.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace Kakeya.VeryNotSticky

universe u
variable {δ : NNReal}

theorem convex_segCarrierSetAt (K : NNReal) (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) : Convex ℝ (segCarrierSetAt K T c L) :=
  (convex_segment _ _).cthickening _

theorem convex_segCarrierSet' (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) : Convex ℝ (segCarrierSet T c L) :=
  (convex_segment _ _).cthickening _

/-- **The volume lower bound for a capsule**, `c₃ · L · δ² ≤ |segCarrierSet T c L|`. -/
theorem le_volumeReal_segCarrierSet (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) (hL1 : 2 * L ≤ 1) :
    ((Metric.lt_volume_convexHull.c 3 : NNReal) : ℝ) * (L * (δ : ℝ) * (δ : ℝ)) ≤
      volume.real (segCarrierSet T c L) := by
  have hbdd : Bornology.IsBounded (segCarrierSet T c L) :=
    Metric.isBounded_closedBall.subset (segCarrierSet_subset_closedBall T c hL)
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  have hprod := (convex_segCarrierSet' T c L).prod_thickness_le_volumeReal hbdd
  rw [hfr] at hprod
  refine le_trans ?_ hprod
  have hexp : ∏ i ∈ Finset.range 3, Metric.thickness ℝ (segCarrierSet T c L) i =
      Metric.thickness ℝ (segCarrierSet T c L) 0 * Metric.thickness ℝ (segCarrierSet T c L) 1 *
        Metric.thickness ℝ (segCarrierSet T c L) 2 := by
    simp [Finset.prod_range_succ, mul_assoc]
  rw [hexp]
  have h0 := le_thickness_segCarrierSet_zero T c hL hL1
  have h1 := le_thickness_segCarrierSet T c hL (n := 1) (by norm_num)
  have h2 := le_thickness_segCarrierSet T c hL (n := 2) (by norm_num)
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hc0 : (0 : ℝ) ≤ ((Metric.lt_volume_convexHull.c 3 : NNReal) : ℝ) := NNReal.coe_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ hc0
  have ht0 : 0 ≤ Metric.thickness ℝ (segCarrierSet T c L) 0 := Metric.thickness_nonneg _ _
  have ht1 : 0 ≤ Metric.thickness ℝ (segCarrierSet T c L) 1 := Metric.thickness_nonneg _ _
  have hstep : L * (δ : ℝ) ≤
      Metric.thickness ℝ (segCarrierSet T c L) 0 * Metric.thickness ℝ (segCarrierSet T c L) 1 :=
    mul_le_mul h0 h1 hδ0 ht0
  exact mul_le_mul hstep h2 hδ0 (by positivity)


/-- `ENNReal` form of `Kakeya.VeryNotSticky.le_volumeReal_segCarrierSet`. -/
theorem ofReal_le_volume_segCarrierSet (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) (hL1 : 2 * L ≤ 1) :
    ENNReal.ofReal (((Metric.lt_volume_convexHull.c 3 : NNReal) : ℝ) * (L * (δ : ℝ) * (δ : ℝ))) ≤
      volume (segCarrierSet T c L) := by
  have htop : volume (segCarrierSet T c L) ≠ ⊤ := volume_segCarrierSet_ne_top T c hL
  have h := le_volumeReal_segCarrierSet T c hL hL1
  calc ENNReal.ofReal (((Metric.lt_volume_convexHull.c 3 : NNReal) : ℝ) * (L * (δ : ℝ) * (δ : ℝ)))
      ≤ ENNReal.ofReal (volume.real (segCarrierSet T c L)) := ENNReal.ofReal_le_ofReal h
    _ = volume (segCarrierSet T c L) := by
        rw [MeasureTheory.Measure.real, ENNReal.ofReal_toReal htop]

/-- **The dilate price is `δ`-free.** `c₃ · |K-dilated capsule| ≤ 16 K² · |capsule|`, with
`c₃ = Metric.lt_volume_convexHull.c 3` the inscribed-simplex constant. Both sides are finite and
the ratio `16 K² / c₃` depends on nothing but `K` and the ambient dimension — in particular not
on `δ`, `L` or the tube. This is what the `δ³` bound
`Kakeya.VeryNotSticky.volume_closedBall_le_volume_segCarrierSet` could not give. -/
theorem volume_segCarrierSetAt_le_mul_volume_segCarrierSet {K : NNReal}
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ}
    (hL : 0 ≤ L) (hL1 : 2 * L ≤ 1) (hKδL : (K : ℝ) * (δ : ℝ) ≤ L) :
    ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal) *
        volume (segCarrierSetAt K T c L) ≤
      16 * ((K : NNReal) : ENNReal) ^ 2 * volume (segCarrierSet T c L) := by
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hc3 : (0 : ℝ) ≤ ((Metric.lt_volume_convexHull.c 3 : NNReal) : ℝ) := NNReal.coe_nonneg _
  -- upper bound on the dilate
  have hup := volume_segCarrierSetAt_le K T c hL
  have hup2 : volume (segCarrierSetAt K T c L) ≤
      16 * ((K : NNReal) : ENNReal) ^ 2 *
        ENNReal.ofReal (L * (δ : ℝ) * (δ : ℝ)) := by
    refine hup.trans ?_
    have hlen : ENNReal.ofReal ((K : ℝ) * (δ : ℝ) + L) ≤ ENNReal.ofReal (2 * L) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    have hKd : ((K * δ : NNReal) : ENNReal) = ((K : NNReal) : ENNReal) * (δ : ENNReal) := by
      push_cast; ring
    calc 8 * (ENNReal.ofReal ((K : ℝ) * (δ : ℝ) + L) * ((K * δ : NNReal) : ENNReal) *
            ((K * δ : NNReal) : ENNReal))
        ≤ 8 * (ENNReal.ofReal (2 * L) * ((K * δ : NNReal) : ENNReal) *
            ((K * δ : NNReal) : ENNReal)) := by gcongr
      _ = 16 * ((K : NNReal) : ENNReal) ^ 2 *
            (ENNReal.ofReal L * (δ : ENNReal) * (δ : ENNReal)) := by
          rw [hKd, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
          simp only [ENNReal.ofReal_ofNat]
          ring
      _ = 16 * ((K : NNReal) : ENNReal) ^ 2 * ENNReal.ofReal (L * (δ : ℝ) * (δ : ℝ)) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hL,
            ENNReal.ofReal_coe_nnreal]
  -- lower bound on the capsule
  have hlow := ofReal_le_volume_segCarrierSet T c hL hL1
  rw [ENNReal.ofReal_mul hc3, ENNReal.ofReal_coe_nnreal] at hlow
  calc ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal) *
        volume (segCarrierSetAt K T c L)
      ≤ ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal) *
          (16 * ((K : NNReal) : ENNReal) ^ 2 * ENNReal.ofReal (L * (δ : ℝ) * (δ : ℝ))) := by
        gcongr
    _ = 16 * ((K : NNReal) : ENNReal) ^ 2 *
          (((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal) *
            ENNReal.ofReal (L * (δ : ℝ) * (δ : ℝ))) := by ring
    _ ≤ 16 * ((K : NNReal) : ENNReal) ^ 2 * volume (segCarrierSet T c L) := by gcongr

/-- **The `segs_density` clause survives the dilate, at a `δ`-free cost.** If the shading `S`
fills the capsule at the density `c₁ · θ`, it fills the `K`-dilated capsule at
`c₁ · c₃ / (16 K²) · θ` — written multiplicatively so that no division occurs in `ℝ≥0∞`. This is
the second half of the price of a dilated presentation; the first is `C₀ = 4 K`
(`Kakeya.VeryNotSticky.hasThicknesses_segCarrierSetAt`). -/
theorem segsDensity_of_segCarrierSetAt {K c₁ : NNReal} {θ : ENNReal}
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ}
    (hL : 0 ≤ L) (hL1 : 2 * L ≤ 1) (hKδL : (K : ℝ) * (δ : ℝ) ≤ L)
    {S : Set (EuclideanSpace ℝ (Fin 3))}
    (hdens : (c₁ : ENNReal) * θ * volume (segCarrierSet T c L) ≤ volume S) :
    (c₁ : ENNReal) * ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal) * θ *
        volume (segCarrierSetAt K T c L) ≤
      16 * ((K : NNReal) : ENNReal) ^ 2 * volume S := by
  have hratio := volume_segCarrierSetAt_le_mul_volume_segCarrierSet T c hL hL1 hKδL
  calc (c₁ : ENNReal) * ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal) * θ *
        volume (segCarrierSetAt K T c L)
      = (c₁ : ENNReal) * θ *
          (((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal) *
            volume (segCarrierSetAt K T c L)) := by ring
    _ ≤ (c₁ : ENNReal) * θ *
          (16 * ((K : NNReal) : ENNReal) ^ 2 * volume (segCarrierSet T c L)) := by gcongr
    _ = 16 * ((K : NNReal) : ENNReal) ^ 2 *
          ((c₁ : ENNReal) * θ * volume (segCarrierSet T c L)) := by ring
    _ ≤ 16 * ((K : NNReal) : ENNReal) ^ 2 * volume S := by gcongr


/-! ### The radius-only dilate is the wrong shape — the axial mechanism, pinned -/

/-- **A radius-only dilate cannot absorb an axial displacement.** If the left endpoint of one
capsule's core window is farther than `K δ + L` from the *midpoint* of another's, the first
capsule is not contained in the second's `K`-dilate.

This is the mechanism that refutes a radius-only reading of GWZ's "comparable": the `segStart`
clamp `min (max (coreParam − L) 0) (1 − 2L)` can place the two windows of a ball at an **axial**
offset of order `L = r₁/4` while their capsules are still not essentially distinct (the overlap
is then a capsule of core length `L`, of volume `π δ² L + (4/3) π δ³`, against the half-volume
`π δ² L + (2/3) π δ³`). No `δ`-free `K` satisfies `K δ ≥ L = r₁/4`, since `r₁/δ → ∞`. So
`Kakeya.VeryNotSticky.CapsuleComparableAt` must be read with a **homothety** dilate, scaling the
core window as well as the radius — which is exactly the shape of the existing
`Kakeya.Tube.dilate` and hence of `Kakeya.Tube.tubeOverlapCoreClose`. -/
theorem not_subset_segCarrierSetAt_of_axial_offset {K : NNReal}
    (T T' : Tube δ (EuclideanSpace ℝ (Fin 3))) (c c' : EuclideanSpace ℝ (Fin 3)) {L : ℝ}
    (hL : 0 ≤ L)
    (hfar : (K : ℝ) * (δ : ℝ) + L <
      dist (corePt T' (segStart T' c' L)) (corePt T (segStart T c L + L))) :
    ¬ (segCarrierSet T' c' L ⊆ segCarrierSetAt K T c L) := by
  intro hsub
  have hmem : corePt T' (segStart T' c' L) ∈ segCarrierSet T' c' L :=
    Metric.self_subset_cthickening _ (left_mem_segment ℝ _ _)
  have hball := segCarrierSetAt_subset_closedBall K T c hL (hsub hmem)
  rw [Metric.mem_closedBall] at hball
  linarith


/-- **The existing unit-tube comparability, in `IsEssentiallyDistinct` form.** Two `δ`-tubes that
are *not* essentially distinct are comparable at the dilation `K′₀`: this is
`Kakeya.Tube.tubeOverlapCoreClose` with its hypothesis rewritten, and it is where `K′₀` comes
from. Note the dilate is `Kakeya.Tube.dilate`, a **homothety about the tube's centre** — it
scales the core length as well as the radius. -/
theorem tube_subset_dilate_of_not_essDistinct {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (T T' : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (h : ¬ IsEssentiallyDistinct T.carrier T'.carrier) :
    T'.carrier ⊆ (Kakeya.Tube.dilate T edComparabilityConstant).carrier := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  have hov : 1 / 2 * volume T.carrier < volume (T.carrier ∩ T'.carrier) := by
    rw [IsEssentiallyDistinct, not_le] at h
    refine lt_of_le_of_lt ?_ h
    gcongr
    exact le_max_left _ _
  have := Kakeya.Tube.tubeOverlapCoreClose hδ hδ1 T T' hov
  rwa [hfr] at this



theorem four_le_edDensityConstant : 4 ≤ edDensityConstant := by
  rw [edDensityConstant]
  nth_rewrite 1 [show (4 : NNReal) = 4 * 1 by ring]
  gcongr
  exact one_le_pow₀ one_le_edDilateConstant

/-- The floor discharges (C2)'s side condition: `K′ ≤ C₀`. -/
theorem edDilateConstant_le_of_floor {C₀ : NNReal} (h : edSegmentsConstant ≤ C₀) :
    edDilateConstant ≤ C₀ := by
  refine le_trans ?_ h
  rw [edSegmentsConstant]
  nth_rewrite 1 [show edDilateConstant = 1 * edDilateConstant by ring]
  gcongr
  norm_num

/-- The floor discharges the addendum's `2 K′ ≤ C₀` as well. -/
theorem two_mul_edDilateConstant_le_of_floor {C₀ : NNReal} (h : edSegmentsConstant ≤ C₀) :
    2 * edDilateConstant ≤ C₀ := by
  refine le_trans ?_ h
  rw [edSegmentsConstant]
  gcongr
  norm_num


/-- **The `∀ᶠ δ` device cannot absorb a constant at the *same* exponent.**  §G-3 is
right that `∀ᶠ δ` needs no new hypothesis when the exponents differ strictly; it does not help
when they agree. This matters because the density-cap route of §G-addendum (a) produces
`M = M₀ · δ^{-(η + 2 exscal)}` — the budget's own exponent — so the `δ`-free `M₀` has nowhere to
go. -/
theorem not_eventually_const_mul_rpow_le_self {M₀ : ENNReal} (hM₀ : 1 < M₀) (p : ℝ) :
    ¬ (∀ᶠ d : NNReal in 𝓝[>] (0 : NNReal),
      M₀ * (d : ENNReal) ^ p ≤ (d : ENNReal) ^ p) := by
  intro h
  obtain ⟨d, hle, hd0⟩ := (h.and self_mem_nhdsWithin).exists
  have hdpos : (0 : NNReal) < d := hd0
  have hdne : (d : ENNReal) ≠ 0 := by
    simpa using ne_of_gt hdpos
  have hdtop : (d : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hx0 : (d : ENNReal) ^ p ≠ 0 := by
    intro hc
    rw [ENNReal.rpow_eq_zero_iff] at hc
    rcases hc with ⟨hc, -⟩ | ⟨hc, -⟩
    · exact hdne hc
    · exact hdtop hc
  have hxtop : (d : ENNReal) ^ p ≠ ⊤ := by
    intro hc
    rw [ENNReal.rpow_eq_top_iff] at hc
    rcases hc with ⟨hc, -⟩ | ⟨hc, -⟩
    · exact hdne hc
    · exact hdtop hc
  have h1 : M₀ ≤ 1 := by
    have := (ENNReal.mul_le_iff_le_inv hx0 hxtop).mp (by
      simpa [mul_comm] using hle)
    calc M₀ ≤ ((d : ENNReal) ^ p)⁻¹ * ((d : ENNReal) ^ p) := by
          rw [ENNReal.inv_mul_cancel hx0 hxtop] at *
          simpa using this
      _ = 1 := ENNReal.inv_mul_cancel hx0 hxtop
  exact absurd h1 (not_le.2 hM₀)


/-! ### The homothety dilate of a capsule, and comparability in GWZ's own shape -/

/-- The midpoint of a capsule's core window. -/
noncomputable def capsuleCentre (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  corePt T (segStart T c L + L)

/-- **The `K`-homothety dilate of a capsule**, about its own centre — the shape of
`Kakeya.Tube.dilate` and hence of `Kakeya.Tube.tubeOverlapCoreClose`'s conclusion. Unlike
`Kakeya.VeryNotSticky.segCarrierSetAt` it scales the **core window** as well as the radius, which
`Kakeya.VeryNotSticky.not_subset_segCarrierSetAt_of_axial_offset` shows is necessary. -/
noncomputable def segCarrierSetHom (K : ℝ) (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  (AffineMap.homothety (capsuleCentre T c L) K) '' (segCarrierSet T c L)

theorem dist_homothety (p : EuclideanSpace ℝ (Fin 3)) (K : ℝ)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    dist (AffineMap.homothety p K x) (AffineMap.homothety p K y) = |K| * dist x y := by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, dist_eq_norm]
  rw [show K • (x - p) + p - (K • (y - p) + p) = K • (x - y) by module, norm_smul,
    Real.norm_eq_abs]

theorem capsuleCentre_mem_segCarrierSet (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) :
    capsuleCentre T c L ∈ segCarrierSet T c L := by
  refine Metric.self_subset_cthickening _ ?_
  rw [segment_eq_image' ℝ]
  refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
  simp only [capsuleCentre, corePt]
  module

theorem segCarrierSet_subset_segCarrierSetHom {K : ℝ} (hK : 1 ≤ K)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) :
    segCarrierSet T c L ⊆ segCarrierSetHom K T c L := by
  intro x hx
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨AffineMap.homothety (capsuleCentre T c L) K⁻¹ x, ?_, ?_⟩
  · have hmid := capsuleCentre_mem_segCarrierSet T c L
    have hconv := convex_segCarrierSet' T c L
    have : AffineMap.homothety (capsuleCentre T c L) K⁻¹ x =
        (1 - K⁻¹) • capsuleCentre T c L + K⁻¹ • x := by
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
      module
    rw [this]
    exact hconv hmid hx (by
      have : K⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]; right; exact hK
      linarith [inv_pos.2 hK0]) (le_of_lt (inv_pos.2 hK0)) (by ring)
  · show AffineMap.homothety (capsuleCentre T c L) K
      (AffineMap.homothety (capsuleCentre T c L) K⁻¹ x) = x
    rw [← AffineMap.comp_apply, ← AffineMap.homothety_mul,
      mul_inv_cancel₀ (ne_of_gt hK0), AffineMap.homothety_one]
    rfl

/-- **The homothety dilate still lies along the core line**, at the dilated radius `K δ`. -/
theorem segCarrierSetHom_subset_cthickening_line {K : ℝ} (hK : 0 ≤ K)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ}
    (hL : 0 ≤ L) {C : ℝ} (hC : K * (δ : ℝ) ≤ C) :
    segCarrierSetHom K T c L ⊆ cthickening C
      (AffineSubspace.mk' (corePt T (segStart T c L)) (Submodule.span ℝ {T.direction}) :
        Set (EuclideanSpace ℝ (Fin 3))) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [segCarrierSet_eq_biUnion] at hx
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
  have hwline : w ∈ (AffineSubspace.mk' (corePt T (segStart T c L))
      (Submodule.span ℝ {T.direction}) : Set (EuclideanSpace ℝ (Fin 3))) := by
    obtain ⟨u, _, rfl⟩ := segment_subset_corePt_image T (by linarith) hw
    have : corePt T u = (u - segStart T c L) • T.direction +ᵥ corePt T (segStart T c L) := by
      simp only [corePt, vadd_eq_add]; module
    rw [this]
    exact AffineSubspace.vadd_mem_mk' _
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hcline : capsuleCentre T c L ∈ (AffineSubspace.mk' (corePt T (segStart T c L))
      (Submodule.span ℝ {T.direction}) : Set (EuclideanSpace ℝ (Fin 3))) := by
    have : capsuleCentre T c L = L • T.direction +ᵥ corePt T (segStart T c L) := by
      simp only [capsuleCentre, corePt, vadd_eq_add]; module
    rw [this]
    exact AffineSubspace.vadd_mem_mk' _
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hhw : AffineMap.homothety (capsuleCentre T c L) K w ∈
      (AffineSubspace.mk' (corePt T (segStart T c L))
        (Submodule.span ℝ {T.direction}) : Set (EuclideanSpace ℝ (Fin 3))) := by
    have hdir : w -ᵥ capsuleCentre T c L ∈
        (AffineSubspace.mk' (corePt T (segStart T c L))
          (Submodule.span ℝ {T.direction})).direction :=
      AffineSubspace.vsub_mem_direction hwline hcline
    have := AffineSubspace.vadd_mem_of_mem_direction
      (Submodule.smul_mem _ K hdir) hcline
    simpa [AffineMap.homothety_apply] using this
  refine Metric.closedBall_subset_cthickening hhw C ?_
  rw [Metric.mem_closedBall, dist_homothety, abs_of_nonneg hK]
  rw [Metric.mem_closedBall] at hxw
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  calc K * dist x w ≤ K * (δ : ℝ) := by
        exact mul_le_mul_of_nonneg_left hxw hK
    _ ≤ C := hC


theorem capsuleCentre_mem_window (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) :
    capsuleCentre T c L ∈
      segment ℝ (corePt T (segStart T c L)) (corePt T (segStart T c L + 2 * L)) := by
  rw [segment_eq_image' ℝ]
  refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
  simp only [capsuleCentre, corePt]
  module

/-- **The radius-only dilate is inside the homothety dilate of the same ratio.** -/
theorem segCarrierSetAt_subset_segCarrierSetHom {K : NNReal} (hK : 1 ≤ K)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (c : EuclideanSpace ℝ (Fin 3)) (L : ℝ) :
    segCarrierSetAt K T c L ⊆ segCarrierSetHom (K : ℝ) T c L := by
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le zero_lt_one hKR
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hKδ : (0 : ℝ) ≤ (K : ℝ) * (δ : ℝ) := by positivity
  intro y hy
  rw [segCarrierSetAt, isClosed_segment.cthickening_eq_biUnion_closedBall hKδ] at hy
  obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp hy
  rw [Metric.mem_closedBall] at hyw
  refine ⟨AffineMap.homothety (capsuleCentre T c L) (K : ℝ)⁻¹ y, ?_, ?_⟩
  · have hwin : AffineMap.homothety (capsuleCentre T c L) (K : ℝ)⁻¹ w ∈
        segment ℝ (corePt T (segStart T c L)) (corePt T (segStart T c L + 2 * L)) := by
      have hrw : AffineMap.homothety (capsuleCentre T c L) (K : ℝ)⁻¹ w =
          (1 - (K : ℝ)⁻¹) • capsuleCentre T c L + (K : ℝ)⁻¹ • w := by
        simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]; module
      rw [hrw]
      refine (convex_segment _ _) (capsuleCentre_mem_window T c L) hw ?_ ?_ (by ring)
      · have : (K : ℝ)⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; exact hKR
        linarith [inv_pos.2 hK0]
      · exact le_of_lt (inv_pos.2 hK0)
    refine Metric.closedBall_subset_cthickening hwin (δ : ℝ) ?_
    rw [Metric.mem_closedBall, dist_homothety, abs_of_nonneg (le_of_lt (inv_pos.2 hK0))]
    rw [inv_mul_le_iff₀ hK0]
    calc dist y w ≤ (K : ℝ) * (δ : ℝ) := hyw
      _ = (K : ℝ) * (δ : ℝ) := rfl
  · show AffineMap.homothety (capsuleCentre T c L) (K : ℝ)
      (AffineMap.homothety (capsuleCentre T c L) (K : ℝ)⁻¹ y) = y
    rw [← AffineMap.comp_apply, ← AffineMap.homothety_mul,
      mul_inv_cancel₀ (ne_of_gt hK0), AffineMap.homothety_one]
    rfl


/-! ### Comparability in GWZ's own shape, and the three obligations from it -/

section HomObligations

variable {cfg : VeryNotSticky.{u}} (core : BallDataCore cfg)

/-- The `K`-homothety dilate of the capsule of tube `i` in ball `B`. -/
noncomputable abbrev ballCapsuleHom (K : ℝ) (B : core.bι) (i : cfg.ι) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  segCarrierSetHom K (cfg.T i).toTube (core.ctr B) ((cfg.r₁ : ℝ) / 4)

/-- **Comparability at dilation `K`, in GWZ's own shape** (`gwz.txt` l.2021): two capsules of one
ball that are not essentially distinct each lie in the `K`-**homothety** dilate of the other.

This is the form `Kakeya.Tube.tubeOverlapCoreClose` delivers for whole tubes, and — unlike the
radius-only `Kakeya.VeryNotSticky.CapsuleComparableAt` — it is not refuted by the axial mechanism
of `Kakeya.VeryNotSticky.not_subset_segCarrierSetAt_of_axial_offset`, because the homothety
scales the core window too. The value the existing geometry fixes is
`Kakeya.VeryNotSticky.edComparabilityConstant`. -/
abbrev CapsuleComparableHomAt (K : ℝ) : Prop :=
  ∀ B ∈ core.bs, ∀ i ∈ cfg.s, ∀ j ∈ cfg.s,
    ¬ IsEssentiallyDistinct (ballCapsule core B i) (ballCapsule core B j) →
      ballCapsule core B j ⊆ ballCapsuleHom core K B i ∧
        ballCapsule core B i ⊆ ballCapsuleHom core K B j

/-- **(C1) from the homothety form.** -/
theorem capsuleShade_subset_hom_of_comparableHomAt {K : ℝ}
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hP16 : ∀ B ∈ core.bs, core.P B ⊆ ball (core.ctr B) ((cfg.r₁ : ℝ) / 16))
    (hcomp : CapsuleComparableHomAt core K) :
    ∀ B ∈ core.bs, ∀ i ∈ cfg.s, ∀ j ∈ cfg.s,
      ¬ IsEssentiallyDistinct (ballCapsule core B i) (ballCapsule core B j) →
        (cfg.T j).shade ∩ core.P B ⊆ ballCapsuleHom core K B i := by
  intro B hB i hi j hj hne
  refine subset_trans ?_ (hcomp B hB i hi j hj hne).1
  intro x hx
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  have hxT : x ∈ (cfg.T j).carrier ∩ ball (core.ctr B) ((cfg.r₁ : ℝ) / 16) :=
    ⟨(cfg.T j).shade_subset hx.1, hP16 B hB hx.2⟩
  exact tube_inter_ball_subset_segCarrierSet (cfg.T j).toTube (core.ctr B)
    (by positivity) (by linarith) hxT

/-- **(C2) from the homothety form, reaching the existing obligation.** `CapsuleCoreLine core`
follows as soon as the core's own constant pays for the dilate, `K ≤ core.C₀`. -/
theorem capsuleCoreLine_of_comparableHomAt {K : ℝ} (hK : 0 ≤ K) (hKC₀ : K ≤ (core.C₀ : ℝ))
    (hcomp : CapsuleComparableHomAt core K) : CapsuleCoreLine core := by
  intro B hB i hi j hj hne
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  refine ⟨corePt (cfg.T j).toTube
    (segStart (cfg.T j).toTube (core.ctr B) ((cfg.r₁ : ℝ) / 4)), ?_⟩
  refine subset_trans (hcomp B hB i hi j hj hne).2 ?_
  refine segCarrierSetHom_subset_cthickening_line hK (cfg.T j).toTube (core.ctr B)
    (by positivity) ?_
  exact mul_le_mul_of_nonneg_right hKC₀ hδ0

open scoped Classical in
/-- **(C3) from the homothety form**: the geometric class count, with `¬ ED` replaced by
containment in the `K`-homothety dilate. -/
abbrev CapsuleHomDilateCount (K : ℝ) (M : NNReal) : Prop :=
  ∀ B ∈ core.bs, ∀ i ∈ cfg.s, ∀ z : EuclideanSpace ℝ (Fin 3),
    (((cfg.s.filter (fun j => z ∈ (cfg.T j).shade ∧
        ballCapsule core B j ⊆ ballCapsuleHom core K B i)).card : ℕ) : ENNReal) ≤ (M : ENNReal)

open scoped Classical in
/-- **(C3) at `K` ⇒ the existing `CapsuleClassCount`.** -/
theorem capsuleClassCount_of_homDilateCount {K : ℝ} {M : NNReal}
    (hcomp : CapsuleComparableHomAt core K) (hcount : CapsuleHomDilateCount core K M) :
    CapsuleClassCount core M := by
  classical
  intro B hB i hi z
  refine le_trans ?_ (hcount B hB i hi z)
  refine Nat.cast_le.2 (Finset.card_le_card ?_)
  intro j hj
  rw [Finset.mem_filter] at hj
  exact Finset.mem_filter.2 ⟨hj.1, hj.2.1, (hcomp B hB i hi j hj.1 hj.2.2).1⟩

/-- **The radius-only form is strictly stronger.** So the three reductions of
`Kakeya/DimensionThree/MainLemma2/BallCoreEDCapsule.lean` are subsumed by the ones above; the
radius-only hypothesis, being refuted by the axial mechanism, is the one to discard. -/
theorem comparableHomAt_of_comparableAt {K : NNReal} (hK : 1 ≤ K)
    (hcomp : CapsuleComparableAt core K) : CapsuleComparableHomAt core (K : ℝ) := by
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  have hL : (0 : ℝ) ≤ (cfg.r₁ : ℝ) / 4 := by positivity
  intro B hB i hi j hj hne
  obtain ⟨h1, h2⟩ := hcomp B hB i hi j hj hne
  exact ⟨subset_trans h1 (segCarrierSetAt_subset_segCarrierSetHom hK _ _ _),
    subset_trans h2 (segCarrierSetAt_subset_segCarrierSetHom hK _ _ _)⟩

open scoped Classical in
/-- **(C3) from a cap stated on the tube CARRIERS.** `Kakeya.VeryNotSticky.card_cone_le`'s
counting hypothesis is `∀ i ∈ t, x ∈ (cfg.T i).carrier`, not `… .shade`; since
`ShadedTube.shade_subset` the carrier form is the weaker cap and it is what the density-cap
route of  §G-addendum (a) delivers. This lines the two up. -/
theorem capsuleHomDilateCount_of_carrierCap {K : ℝ} {M : NNReal}
    (hcap : ∀ B ∈ core.bs, ∀ i ∈ cfg.s, ∀ z : EuclideanSpace ℝ (Fin 3),
      (((cfg.s.filter (fun j => z ∈ (cfg.T j).carrier ∧
          ballCapsule core B j ⊆ ballCapsuleHom core K B i)).card : ℕ) : ENNReal)
        ≤ (M : ENNReal)) :
    CapsuleHomDilateCount core K M := by
  classical
  intro B hB i hi z
  refine le_trans ?_ (hcap B hB i hi z)
  refine Nat.cast_le.2 (Finset.card_le_card ?_)
  intro j hj
  rw [Finset.mem_filter] at hj
  exact Finset.mem_filter.2 ⟨hj.1, (cfg.T j).shade_subset hj.2.1, hj.2.2⟩

/-- **The §G-1 plug.** From the raised floor `edSegmentsConstant ≤ core.C₀` and comparability at `K′`, the two existing obligations follow. (C1) is
deliberately absent: it targets the **undilated** capsule and is the one clause that needs the
repaired fold at the dilated carrier — that is the whole content of the §G-1 finding. -/
theorem capsuleInputs_of_comparableHomAt_of_floor {M : NNReal}
    (hfloor : edSegmentsConstant ≤ core.C₀)
    (hcomp : CapsuleComparableHomAt core ((edDilateConstant : NNReal) : ℝ))
    (hcount : CapsuleHomDilateCount core ((edDilateConstant : NNReal) : ℝ) M) :
    CapsuleCoreLine core ∧ CapsuleClassCount core M :=
  ⟨capsuleCoreLine_of_comparableHomAt core (NNReal.coe_nonneg _)
      (by exact_mod_cast edDilateConstant_le_of_floor hfloor) hcomp,
    capsuleClassCount_of_homDilateCount core hcomp hcount⟩


end HomObligations

end Kakeya.VeryNotSticky
