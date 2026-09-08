/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.IntersectionVolume

/-!
# A tube's carrier determines its centre, and hence its dilates

A `Kakeya.Tube` carries more data than its carrier: the two endpoints `x`, `y` are fields of the
structure, and `Tube.reverse` exhibits two distinct tubes with the same carrier.  The
*unordered* pair `{x, y}` is however determined, and therefore so is the centre
`Tube.center = midpoint ℝ x y`.  This file proves that, and draws the consequence that
matters downstream:

`Kakeya.Tube.dilate T c` is the image of the carrier under the homothety of ratio `c` centred at
`T.center`, so it depends on exactly two data, both of which are determined by the carrier.  Hence
a fact about `Tube.dilate T c` transports along `T.toConvexSpaceBody = T'.toConvexSpaceBody`
(`Kakeya.Tube.dilate_congr`).

That transport is load-bearing.  Both `Kakeya.ml1Boot.IsParentFamily` and
`Kakeya.ml1Boot.IsParentFamilyDilate` ask for injectivity of `k ↦ (V k).toConvexSpaceBody` while
stating their containment clause in terms of `Tube.dilate`, and the deduplication
`Kakeya.ml1Boot.exists_dedupe` that supplies that injectivity can only return equality of
*bodies* — by `Tube.reverse` it cannot return equality of tubes.  Without `dilate_congr` the
containment clauses do not survive the deduplication.

## Blueprint correspondence

* `Kakeya.eq_zero_of_isBounded_of_vadd_subset` ↔ `lem:boundedTranslationInvariant`;
* `Kakeya.eq_of_image_pointReflection_eq` ↔ `lem:centreOfSymmetryUnique`;
* `Kakeya.image_pointReflection_midpoint_segment` ↔ `lem:tubePointReflectionSegment`;
* `Kakeya.Tube.image_pointReflection_center_carrier` ↔ `lem:tubeCarrierSymmetricAboutCentre`;
* `Kakeya.Tube.center_eq_of_toConvexSpaceBody_eq` ↔ `lem:ml1bootTubeCentreFromCarrier`;
* `Kakeya.Tube.dilate_congr` ↔ `cor:ml1bootDilateFromCarrier`.

The ambient must be a *normed* space and not merely a seminormed one, which is a genuine
strengthening of the ambient of `Kakeya.Tube`: if the null space `{v : ‖v‖ = 0}` is nonzero then
translating both endpoints by a null vector leaves the carrier unchanged and moves the centre.
-/

@[expose] public section

open Metric

namespace Kakeya

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A bounded nonempty set admits no nonzero translation** (blueprint
`lem:boundedTranslationInvariant`): if `S + v ⊆ S` with `S` nonempty and bounded, then `v = 0`.

Iterating the hypothesis puts `s + n • v` in `S` for every `n`, and boundedness caps `n ‖v‖`.
The final passage from `‖v‖ = 0` to `v = 0` is where the ambient must be normed. -/
theorem eq_zero_of_isBounded_of_vadd_subset {S : Set E} {v : E}
    (hne : S.Nonempty) (hbdd : Bornology.IsBounded S)
    (hsub : (fun z => z + v) '' S ⊆ S) : v = 0 := by
  rcases hne with ⟨s, hs⟩
  have hmem : ∀ n : ℕ, s + n • v ∈ S := by
    intro n
    induction n with
    | zero => simpa using hs
    | succ n ih =>
        have hstep : (s + n • v) + v ∈ S := hsub ⟨s + n • v, ih, rfl⟩
        simpa [Nat.succ_eq_add_one, succ_nsmul, add_assoc, add_comm, add_left_comm] using hstep
  rcases hbdd.subset_closedBall (0 : E) with ⟨R, hball⟩
  have hcap : ∀ n : ℕ, ‖s + n • v‖ ≤ R := by
    intro n
    simpa [mem_closedBall_zero_iff] using hball (hmem n)
  have hbound : ∀ n : ℕ, (n : ℝ) * ‖v‖ ≤ R + ‖s‖ := by
    intro n
    have hx : (s + n • v) - s = n • v := by abel
    have hnn : ‖n • v‖ = (n : ℝ) * ‖v‖ := by
      rw [← Nat.cast_smul_eq_nsmul (R := ℝ), norm_smul]
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
    calc
      (n : ℝ) * ‖v‖ = ‖n • v‖ := hnn.symm
      _ = ‖(s + n • v) - s‖ := by rw [hx]
      _ ≤ ‖s + n • v‖ + ‖s‖ := norm_sub_le _ _
      _ ≤ R + ‖s‖ := add_le_add_left (hcap n) ‖s‖
  by_contra hv
  have hv_nz : ‖v‖ ≠ 0 := by
    intro hvz
    exact hv (norm_eq_zero.mp hvz)
  have hv_pos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv_nz)
  rcases exists_nat_gt ((R + ‖s‖) / ‖v‖) with ⟨n₀, hn₀⟩
  have hlt : R + ‖s‖ < (n₀ : ℝ) * ‖v‖ := (div_lt_iff₀ hv_pos).mp hn₀
  exact (not_lt_of_ge (hbound n₀)) hlt

/-- **A centre of symmetry is unique** (blueprint `lem:centreOfSymmetryUnique`): a nonempty
bounded set is symmetric about at most one point.

The composite of the two point reflections is the translation by `2 • (c' - c)`, so
`Kakeya.eq_zero_of_isBounded_of_vadd_subset` applies.  Both hypotheses are essential: a line is
symmetric about each of its points, and the empty set about every point. -/
theorem eq_of_image_pointReflection_eq {S : Set E} {c c' : E}
    (hne : S.Nonempty) (hbdd : Bornology.IsBounded S)
    (hc : Equiv.pointReflection c '' S = S)
    (hc' : Equiv.pointReflection c' '' S = S) : c = c' := by
  let v : E := (2 : ℝ) • (c' - c)
  have hcomp : ∀ z : E, Equiv.pointReflection c' (Equiv.pointReflection c z) = z + v := by
    intro z
    simp only [Equiv.pointReflection_apply, vsub_eq_sub, vadd_eq_add, v]
    module
  have himg : (fun z => z + v) '' S = S := by
    have hstep : (fun z => z + v) '' S
        = Equiv.pointReflection c' '' (Equiv.pointReflection c '' S) := by
      rw [Set.image_image]
      exact Set.image_congr' (fun z => (hcomp z).symm)
    rw [hstep, hc, hc']
  have hv : v = 0 := eq_zero_of_isBounded_of_vadd_subset hne hbdd himg.subset
  have hsub : c' - c = 0 := by
    have hsmul : (2 : ℝ) • (c' - c) = 0 := by
      simpa [v] using hv
    exact (smul_right_injective E (hr := (two_ne_zero : (2 : ℝ) ≠ 0)))
      (by simpa [smul_zero] using hsmul)
  exact (sub_eq_zero.mp hsub).symm

/-- **The point reflection about the midpoint preserves the segment** (blueprint
`lem:tubePointReflectionSegment`): being affine it carries the segment to the segment of the
images, and it exchanges the two endpoints. -/
theorem image_pointReflection_midpoint_segment (x y : E) :
    Equiv.pointReflection (midpoint ℝ x y) '' segment ℝ x y = segment ℝ x y := by
  simpa [segment_symm] using
    image_segment (𝕜 := ℝ) (E := E) (F := E)
      (AffineEquiv.pointReflection ℝ (midpoint ℝ x y) : E →ᵃ[ℝ] E) x y

end Normed

namespace Tube

section Carrier

variable {δ : NNReal} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- **A tube's carrier is symmetric about its centre** (blueprint
`lem:tubeCarrierSymmetricAboutCentre`).

The carrier is the union of the closed `δ`-balls centred on the core segment
(`Tube.carrier_eq`); the reflection about the centre is an isometry, so it carries each
such ball to the ball of the same radius about the reflected point, and by
`Kakeya.image_pointReflection_midpoint_segment` it permutes the centres. -/
theorem image_pointReflection_center_carrier (T : Tube δ E) :
    Equiv.pointReflection T.center '' T.carrier = T.carrier := by
  let R : E ≃ᵃⁱ[ℝ] E := AffineIsometryEquiv.pointReflection ℝ T.center
  have hfun : (Equiv.pointReflection T.center : E → E) = (R : E → E) := by
    funext z
    rfl
  have hRseg : (R : E → E) '' segment ℝ T.x T.y = segment ℝ T.x T.y := by
    rw [← hfun]
    exact Kakeya.image_pointReflection_midpoint_segment T.x T.y
  rw [T.carrier_eq, Set.image_iUnion₂, hfun]
  calc
    (⋃ z ∈ segment ℝ T.x T.y, (R : E → E) '' Metric.closedBall z δ)
        = ⋃ z ∈ segment ℝ T.x T.y, Metric.closedBall ((R : E → E) z) δ := by
            exact Set.iUnion₂_congr (fun z _ => by
              simpa using (IsometryEquiv.image_closedBall R.toIsometryEquiv z (δ : ℝ)))
    _ = ⋃ w ∈ (R : E → E) '' segment ℝ T.x T.y, Metric.closedBall w δ := by
            rw [Set.biUnion_image]
    _ = ⋃ w ∈ segment ℝ T.x T.y, Metric.closedBall w δ := by
            rw [hRseg]

/-- **The carrier of a tube determines its centre** (blueprint
`lem:ml1bootTubeCentreFromCarrier`).

The two scales need not agree: `Kakeya.Tube.image_pointReflection_center_carrier` is applied to
each tube separately.  The analogous statement for the *endpoints* is false by
`Tube.reverse`; only the unordered pair, and hence its midpoint, is determined. -/
theorem center_eq_of_toConvexSpaceBody_eq {δ' : NNReal} (T : Tube δ E) (T' : Tube δ' E)
    (h : T.toConvexSpaceBody = T'.toConvexSpaceBody) : T.center = T'.center := by
  have hcarrier : T.carrier = T'.carrier := by
    simpa using congrArg ConvexSpaceBody.carrier h
  have hne : (T.carrier : Set E).Nonempty := T.toConvexSpaceBody.nonempty
  have hbdd : Bornology.IsBounded (T.carrier : Set E) :=
    T.toConvexSpaceBody.isCompact.isBounded
  have hc : Equiv.pointReflection T.center '' (T.carrier : Set E) = (T.carrier : Set E) :=
    Tube.image_pointReflection_center_carrier T
  have hc' : Equiv.pointReflection T'.center '' (T.carrier : Set E) = (T.carrier : Set E) := by
    simpa [hcarrier] using (Tube.image_pointReflection_center_carrier T')
  exact Kakeya.eq_of_image_pointReflection_eq (S := T.carrier) (c := T.center) (c' := T'.center)
    hne hbdd hc hc'

end Carrier

end Tube

section Dilate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **Dilates transport along equality of carriers** (blueprint `cor:ml1bootDilateFromCarrier`).

`Kakeya.Tube.dilate T c` is the image of `T.toConvexSpaceBody` under the homothety of ratio `c`
centred at `T.center`, so it depends on exactly the carrier and the centre; the first agrees by
hypothesis and the second by `Kakeya.Tube.center_eq_of_toConvexSpaceBody_eq`.

This is what lets a containment in `Tube.dilate _ c` survive the deduplication
`Kakeya.ml1Boot.exists_dedupe`, which returns equality of bodies and cannot return equality of
tubes. -/
theorem Tube.dilate_congr {δ δ' : NNReal} (T : Tube δ E) (T' : Tube δ' E)
    (h : T.toConvexSpaceBody = T'.toConvexSpaceBody) (c : ℝ) :
    Tube.dilate T c = Tube.dilate T' c := by
  apply ConvexSpaceBody.ext
  simp [Tube.dilate, center_eq_of_toConvexSpaceBody_eq T T' h, h]

end Dilate

end Kakeya
