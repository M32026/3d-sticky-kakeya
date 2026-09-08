/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.DimensionThree.Plank.RepresentativeFrostman
public import Kakeya.DimensionThree.Plank.SlabAssignmentGeometry
public import Kakeya.DimensionThree.Plank.DilatedSlabTube
public import Kakeya.FrostmanConstant
public import Kakeya.PartialEstimates
public import Kakeya.Thickening

/-!
# Geometry of one GWZ Section 6 slab fibre

`Plank.SlabFibreGeometry` is the data that the affine slab-to-tube normalisation of GWZ Lemma 6.4
consumes about the fibre of thickened representative prisms assigned to a single `θ × 1 × 1` slab,
together with the constant `Plank.fibreTubeConst` at which that fibre is normalised and the handful
of immediate consequences of the structure's fields.

This module sits *below* the anisotropic ED-packing bridge
(`Kakeya.DimensionThree.Plank.SlabTubeEssentialDistinctness` and its successors), which needs the structure, and
therefore below `Kakeya.DimensionThree.Plank.FrostmanPlankGeometry`, which needs the bridge. It was split
out of `FrostmanPlankGeometry` for exactly that reason; nothing else changed.
-/

@[expose] public section

open MeasureTheory Kakeya
open scoped NNReal Real Classical

noncomputable section

namespace Plank

/-- **Geometry of one slab fibre.** The data the affine slab-to-tube normalisation actually
consumes about the fibre `fibre` of thickened representatives assigned to a single `θ × 1 × 1` slab
`S`, at plank scale `b`, with a single loss constant `Cfib ≥ 1`.

Every field is used by the normalisation: the prisms must be essentially distinct (so their images
are), shaded by their own carriers and contained in a *controlled* ball (so the images are `b`-tubes
in a ball of fixed radius, which the normalisation then contracts), inside a fixed dilation of `S`
and of the right shape (so the anisotropic map sending `S` to a slab of unit long axes turns them
into `b`-tubes), tangential to `S` (so the short axis is the one that is *not* compressed), and of
positive total mass (so fullness and multiplicity are meaningful).

This replaces the earlier arbitrary-prism input, which had no hypothesis tying `Q` to `S` at all.

**Boundedness is controlled, not exact.** The earlier field demanded
`Q.carrier ⊆ Metric.closedBall 0 1` for every prism of the fibre. That is not something GWZ 6.13
supplies: `Kakeya.redPlankTube` bounds the *original planks* and then relates a plank to its
representative only through the `cThk`-dilation
(`(V i).carrier ⊆ ((Qθ (repr i)).dilation cThk).carrier` and `IsCComparable`), which does not put the
representative inside the same ball as the plank. The field is therefore
`subset_controlledBall`, with the fixed radius `4 · Cfib`. (Independently, radius `1` would be the wrong
window for a genuine `a × b × 1` plank; see `Kakeya.plankWindowRadius`.)

**The shading sits on a controlled dilation, not on the representative itself.** The earlier field
`shade_body : ∀ Q ∈ fibre, (Yθ Q).carrier = Q.carrier` was not something the reduction can supply,
and it must not be asserted. What GWZ 6.13 controls is
`(P i).carrier ⊆ ((Qθ (repr i)).dilation cThk).carrier`: a plank's shading is only known to lie in a
fixed *dilation* of its representative prism, so a shading body built from the fibre's planks has to
be carried by that dilation. The two roles are therefore kept apart:

* the **geometric** object is the undilated representative `Q`. It is the one that must stay
  undilated, because `pairwise_essentiallyDistinct` is *not* preserved by dilation — nothing here
  claims that the dilated representatives are pairwise essentially distinct;
* the **shading** object `Yθ Q` is carried by `Q.dilation Cfib` (field `shade_body`).

`subset_controlledBall` is correspondingly stated for the dilated body, which is what has to fit in a
ball of fixed radius for the affine normalisation; containment of the undilated `Q` follows
(`Plank.SlabFibreGeometry.prism_subset_controlledBall`). The fixed volume/fullness/normalisation loss
caused by replacing `Q` with `Q.dilation Cfib` is bounded by a function of `Cfib` alone, and `Cfib`
is quantified before `Closs` in `Plank.normaliseSlabFamilyToTubes` and before `K` in
`Plank.frostmanSlabUnionVolumeLowerBound`, so those constants absorb it. -/
structure SlabFibreGeometry {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1}
    (fibre : Finset (ThickenedPlank θ b hθ1 hb1))
    (Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))) (S : Slab θ hθ1)
    (Cfib : ℝ≥0) : Prop where
  /-- The prisms of the fibre are pairwise essentially distinct. This is asserted for the
  *undilated* representatives only. -/
  pairwise_essentiallyDistinct :
    (↑fibre : Set (ThickenedPlank θ b hθ1 hb1)).Pairwise
      (fun P P' => PrismNDim.IsEssentiallyDistinct P.toPrismNDim P'.toPrismNDim)
  /-- The shading body attached to `Q` is carried by the **controlled dilation** `Q.dilation Cfib`,
  not by `Q` itself; see the note in the structure's docstring. -/
  shade_body : ∀ Q ∈ fibre, (Yθ Q).carrier = (Q.toPrismNDim.dilation Cfib).carrier
  /-- The dilated shading bodies — hence, a fortiori, the prisms themselves — live in a ball of
  fixed radius `4 · Cfib`. Exact unit-ball containment is *not* available for thickened
  representatives; see the note in the structure's docstring. The radius is a fixed *multiple* of
  `Cfib` rather than `Cfib` itself, because the `Cfib`-dilation of a representative already has long
  half-width `Cfib`, so it reaches distance `Cfib` from its own centre and the centre itself only
  lies in the working window (`Plank.windowRadius = 4`): containment in `closedBall 0 Cfib` is
  unsatisfiable for a representative not centred at the origin. -/
  subset_controlledBall : ∀ Q ∈ fibre,
    ((Q.toPrismNDim.dilation Cfib).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      Metric.closedBall 0 (4 * (Cfib : ℝ))
  /-- The prisms live in a fixed dilation of the slab (controlled slab membership). -/
  subset_slab : ∀ Q ∈ fibre,
    (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ (S.toPrismNDim.dilation Cfib).carrier
  /-- The prisms have the thicknesses of a `θ`-thickened `b`-plank, up to the loss `Cfib`. -/
  thickness_comparable : ∀ Q ∈ fibre, ∀ i : Fin 3,
    Cfib⁻¹ * (![θ * b, b, 1] i) ≤ Q.thicknesses i ∧ Q.thicknesses i ≤ Cfib * (![θ * b, b, 1] i)
  /-- The prisms are tangential to the slab: the short normal of `Q` is nearly orthogonal to the two
  long directions of `S`. -/
  tangency : ∀ Q ∈ fibre, ∀ j : Fin 3, j ≠ 0 →
    |inner ℝ (Q.basis 0) (S.basis j)| ≤ (Cfib : ℝ) * (θ : ℝ)
  /-- The fibre carries positive shade mass. -/
  mass_pos : 0 < ∑ Q ∈ fibre, volume (Yθ Q).shade

/-- Nothing is lost by stating `subset_controlledBall` for the dilated shading body: since
`1 ≤ Cfib`, the undilated representative sits inside its own dilation
(`PrismNDim.self_subset_dilation`) and therefore in the same ball. -/
theorem SlabFibreGeometry.prism_subset_controlledBall {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1}
    {fibre : Finset (ThickenedPlank θ b hθ1 hb1)}
    {Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {S : Slab θ hθ1} {Cfib : ℝ≥0} (h : SlabFibreGeometry fibre Yθ S Cfib) (hCfib : 1 ≤ Cfib)
    {Q : ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ fibre) :
    (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 (4 * (Cfib : ℝ)) :=
  (PrismNDim.self_subset_dilation Q.toPrismNDim hCfib).trans (h.subset_controlledBall Q hQ)

/-- The shading body of a fibre element is contained in the same controlled ball, by
`SlabFibreGeometry.shade_body` and `SlabFibreGeometry.subset_controlledBall`. -/
theorem SlabFibreGeometry.shadeBody_subset_controlledBall {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1}
    {fibre : Finset (ThickenedPlank θ b hθ1 hb1)}
    {Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {S : Slab θ hθ1} {Cfib : ℝ≥0} (h : SlabFibreGeometry fibre Yθ S Cfib)
    {Q : ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ fibre) :
    ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 (4 * (Cfib : ℝ)) :=
  (h.shade_body Q hQ) ▸ h.subset_controlledBall Q hQ

/-- **A thickened plank is its own `θ`-thickening, after dilation.** A `Plank.ThickenedPlank θ b` is
by definition a `Plank (θ * b) b`, and thickening it again at the *same* scale `θ` rebuilds
`PrismNDim.mk'` from the same centre, the same frame and the same half-widths `![θ * b, b, 1]`. Both
dilations are therefore the same `mk'` application.

This is the plumbing that lets the slab-to-tube API of `Kakeya/DimensionThree/Plank/SlabTube`,
phrased in terms of `P.thickened θ` for a plank `P`, be applied to the representative prisms of a
slab fibre, which arrive already thickened. -/
theorem dilation_thickened_self_eq {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1}
    (Q : ThickenedPlank θ b hθ1 hb1) (r : ℝ≥0) :
    (Q.thickened θ hθ1).toPrismNDim.dilation r = Q.toPrismNDim.dilation r := by
  simp only [Plank.thickened, PrismNDim.dilation, PrismNDim.center_mk', PrismNDim.basis_mk',
    PrismNDim.thicknesses_mk']
  congr 1
  funext i
  rw [Q.thicknesses_eq]

/-- The conversion constant at which one slab fibre is normalised to `b/8`-tubes. It is
`Plank.slabTubeConst` at the slab-containment constant `Plank.dilatedSetConst Cfib Cfib` — the
enlargement that the `Cfib`-dilated shading forces — and at the angle constant `3 * Cfib`, which is
what `Plank.SlabFibreGeometry.tangency` yields through
`Prism3D.angle_le_of_abs_inner_basis_zero_le`. -/
def fibreTubeConst (Cfib : ℝ≥0) : ℝ≥0 :=
  slabTubeConst (dilatedSetConst Cfib Cfib) (3 * Cfib)

/-- `Plank.fibreTubeConst` is positive, being a `Plank.slabTubeConst`. -/
theorem fibreTubeConst_pos (Cfib : ℝ≥0) : 0 < fibreTubeConst Cfib :=
  slabTubeConst_pos _ _

/-- **Tangency as a plane-angle bound.** `Plank.SlabFibreGeometry.tangency` records the two Parseval
components of the fibre prism's short normal against the long directions of the slab; the plane
angle they control is at most `3 * Cfib * θ` by `Prism3D.angle_le_of_abs_inner_basis_zero_le`. -/
theorem SlabFibreGeometry.angle_le {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1}
    {fibre : Finset (ThickenedPlank θ b hθ1 hb1)}
    {Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {S : Slab θ hθ1} {Cfib : ℝ≥0} (h : SlabFibreGeometry fibre Yθ S Cfib)
    {Q : ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ fibre) :
    Prism3D.angle Q S ≤ ((3 * Cfib : ℝ≥0) : ℝ) * (θ : ℝ) := by
  calc
    Prism3D.angle Q S ≤ 3 * ((Cfib : ℝ) * (θ : ℝ)) :=
      Prism3D.angle_le_of_abs_inner_basis_zero_le Q S (by positivity) (h.tangency Q hQ)
    _ = ((3 * Cfib : ℝ≥0) : ℝ) * (θ : ℝ) := by push_cast; ring

/-- **A slab fibre is a controlled slab family, at the undilated set constant.** Every fibre prism
lies in the `Cfib`-dilate of `S` and makes plane angle at most `3 * Cfib * θ` with it: this is
membership in `Plank.inSlabFamilyC Cfib (3 * Cfib)`, which is the form the
`Kakeya/DimensionThree/Plank/DilatedSlabTube` interface consumes with `Cset := Cfib` and
`Cdil := Cfib`. -/
theorem SlabFibreGeometry.mem_slabFamilyC {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1}
    {fibre : Finset (ThickenedPlank θ b hθ1 hb1)}
    {Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {S : Slab θ hθ1} {Cfib : ℝ≥0} (h : SlabFibreGeometry fibre Yθ S Cfib)
    {Q : ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ fibre) :
    Q ∈ inSlabFamilyC Cfib (3 * Cfib) fibre (fun Q => Q) S := by
  rw [_root_.Plank.mem_inSlabFamilyC]
  exact ⟨hQ, h.subset_slab Q hQ, Plank.SlabFibreGeometry.angle_le h hQ⟩

/-- **A slab fibre is a controlled slab family.** Every fibre prism lies in the
`Plank.dilatedSetConst Cfib Cfib`-dilate of `S` and makes plane angle at most `3 * Cfib * θ` with
it, which is exactly membership in `Plank.inSlabFamilyC` at those two constants — the hypothesis
that the whole `Kakeya/DimensionThree/Plank/SlabTube` interface consumes. -/
theorem SlabFibreGeometry.mem_slabFamily {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1}
    {fibre : Finset (ThickenedPlank θ b hθ1 hb1)}
    {Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {S : Slab θ hθ1} {Cfib : ℝ≥0} (h : SlabFibreGeometry fibre Yθ S Cfib) (hCfib : 1 ≤ Cfib)
    {Q : ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ fibre) :
    Q ∈ inSlabFamilyC (dilatedSetConst Cfib Cfib) (3 * Cfib) fibre (fun Q => Q) S := by
  rw [_root_.Plank.mem_inSlabFamilyC]
  exact ⟨hQ, (h.subset_slab Q hQ).trans
    (PrismNDim.dilation_carrier_mono S.toPrismNDim (Plank.le_dilatedSetConst hCfib)),
    Plank.SlabFibreGeometry.angle_le h hQ⟩

/-- **Anything inside the `Cfib`-dilation of a fibre prism normalises into that prism's tube.** This
is `Plank.image_subset_slabTube_of_subset_dilatedThickened` transported through
`Plank.dilation_thickened_self_eq`, which identifies the `Cfib`-dilation of `Q.thickened θ` with
that of `Q` itself. It is applied twice: to the shading `(Yθ Q).shade`, which sits in
`(Q.dilation Cfib).carrier` by `Plank.SlabFibreGeometry.shade_body`, and to `Q.carrier` itself. -/
theorem SlabFibreGeometry.image_subset_slabTube {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1}
    {fibre : Finset (ThickenedPlank θ b hθ1 hb1)}
    {Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {S : Slab θ hθ1} {Cfib : ℝ≥0} (h : SlabFibreGeometry fibre Yθ S Cfib) (hCfib : 1 ≤ Cfib)
    (hθ0 : 0 < θ) {Q : ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ fibre)
    {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : A ⊆ ((Q.toPrismNDim.dilation Cfib).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    (Slab.normalizeScaled S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib)) '' A
      ⊆ (Q.slabTube S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib)).carrier := by
  have hMain :=
    image_subset_slabTube_of_subset_dilatedThickened (P := Q) (S := S)
      (hθ := hθ1) (hθ0 := hθ0) (Cset := Cfib) (Cang := 3 * Cfib) (Cdil := Cfib) (hCdil := hCfib)
      (hang := h.angle_le hQ)
      (hA := by simpa [← dilation_thickened_self_eq Q Cfib] using hA)
  simpa [fibreTubeConst, fibreTubeConst_pos] using hMain

end Plank

end
