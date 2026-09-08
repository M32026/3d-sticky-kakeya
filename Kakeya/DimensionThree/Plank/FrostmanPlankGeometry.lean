/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.DimensionThree.Plank.RepresentativeFrostman
public import Kakeya.DimensionThree.Plank.SlabAssignmentGeometry
public import Kakeya.DimensionThree.Plank.SlabTubeSelection
public import Kakeya.DimensionThree.Plank.SlabFibreFrostman
public import Kakeya.DimensionThree.Plank.SlabFibreTubes
public import Kakeya.DimensionThree.Plank.SlabFrostmanEstimate
public import Kakeya.DimensionThree.Plank.DilatedSlabTube
public import Kakeya.FrostmanConstant
public import Kakeya.PartialEstimates
public import Kakeya.Thickening

/-!
# GWZ Section 6 geometry: dependency lemmas for the Frostman plank estimate

This file states the geometry lemmas that the Frostman estimate for planks
(`Kakeya.FrostmanEstimate.plankEstimate`, GWZ Lemma 6.4) consumes.

The three lemmas consumed by GWZ Lemma 6.4 are stated here:
`thickenedRepresentativeFibreCardinality` (fibre concentration, `N ≲ Mθ`),
`frostmanThickenedSlabFibre` (local Frostman constant of an assigned slab fibre, S6G15, using the
scalar `Kakeya.frostmanConstant`), and `normaliseSlabFamilyToTubes` (the fixed-loss affine
slab-to-tube normalisation with comparable fullness/multiplicity/cardinality/Frostman).

All three carry their loss constants explicitly, and in the correct order: the representative
dilation `cThk`, the controlled slab-membership losses `Cset`, `Cang`, and the slab-fibre loss `Cfib`
are quantified *before* the constants that depend on them. Slab membership is the controlled
`Plank.inSlabFamilyC`, and the slab-fibre data is packaged as `Plank.SlabFibreGeometry`.

## Note on the normalisation window (repaired)

`PrismNDim.thicknesses` are *half*-widths, so for an `a × b × 1` plank with `a > 0` the constraint
`(V i).carrier ⊆ Metric.closedBall 0 1` is **unsatisfiable**: the long half-axis already has length
`1`, so its endpoint is at distance `1` from the centre, and any point displaced from it in a
transverse direction (possible because `a`, `b` are positive) is at distance `> 1` — concretely
`‖(a, 0, 1)‖ = √(1 + a²) > 1`.

Plank-level statements therefore use `Kakeya.plankWindowRadius` (an absolute constant, value `4`)
and the reference body `Kakeya.plankWindow`, with `Kakeya.plank_carrier_subset_plankWindow` and
`Kakeya.ShadedPlank.carrier_subset_plankWindow` as the producers' entry points. Tube-level
statements keep the unit ball, which a `δ`-tube of axis length `1` does fit; the one place where a
`b`-tube family is *produced* (`Plank.normaliseSlabFamilyToTubes` below) carries the explicit
small-scale hypothesis `b ≤ 1 / 4` that the containment needs.

No proof in Section 6 ever derived anything from the earlier vacuity, and none does now.

The boundedness field of `Plank.SlabFibreGeometry` avoids the problem locally: it asks only for
containment in `Metric.closedBall 0 (4 · Cfib)` with `1 ≤ Cfib`, which is what the 6.13 output can
actually supply for a thickened representative — the representative's centre lies in the working
window of radius `Plank.windowRadius = 4` and its `Cfib`-dilation adds at most `3 · Cfib`, so the
radius must be a fixed multiple of `Cfib`, not `Cfib` itself.

## Note on the shading carrier

`Plank.SlabFibreGeometry` deliberately separates the *geometric* representative prism `Q` (undilated,
and the only object asserted to be pairwise essentially distinct) from the *shading* body `Yθ Q`,
whose carrier is the controlled dilation `Q.dilation Cfib`. This is forced by the plank-to-tube
reduction, which only controls `(P i).carrier ⊆ ((Qθ (repr i)).dilation cThk).carrier`. Asserting
`(Yθ Q).carrier = Q.carrier` would be a claim the reduction cannot support.

## The one missing geometric input

`Plank.normaliseSlabFamilyToTubes` exports pairwise essential distinctness of the *cores*
`g '' Q.carrier` — an affine invariant of the fibre's own essential distinctness — but **not** of
the enclosing tubes, which inflate the cores by a fixed factor.
`Kakeya.FrostmanEstimate.multiplicity_bound` (GWZ Lemma 3.9) demands pairwise essential distinctness
of the tubes, and the gap between the two is exactly one anisotropic packing estimate, which the
repository does not contain:

> There is `MED : ℕ` depending only on the shape constants such that, for every finite family of
> prisms with thickness vector `(θb, b, 1)` that is pairwise essentially distinct and whose members
> all lie in a fixed dilation of a common `θ × 1 × 1` slab, the enclosing `b/8`-tube family
> satisfies `Kakeya.IsEDUpToMult u (fun k => (T k).carrier) MED`.

It is true — a tube sees only the direction and the transverse position of its core, and tangency
confines the fibre's roll angles to a range of size `≈ Cfib · θ`, so only boundedly many pairwise
essentially distinct cores can share one tube — and it is the prism analogue of GWZ Lemma 3.8
(`Kakeya.badAgainstSet_count_le_of_ED_thinBox`); but that lemma is stated for tubes and already
assumes the family is pairwise essentially distinct, so it cannot be reused as it stands.

Once it exists, `Kakeya.IsEDUpToMult.exists_pairwise_subset_with_weight` converts it into a
genuinely pairwise essentially distinct subfamily at the fixed cost `MED + 1` in shade mass, which
is all `Plank.frostmanSlabUnionVolumeLowerBound` needs: the union over a subfamily is contained in
the union over the whole family, so a lower bound for the subfamily is one for the family.

### The route to that estimate

The count has to be run at the *prism* level, where essential distinctness survives, and with the
anisotropic weights `w = (a, b, 1)`. Both halves already exist in the repository:

* `Plank.plank_not_essentiallyDistinct_of_pose_close`
  (`Kakeya/DimensionThree/Plank/ThickenedReprGeometry.lean`) is the anisotropic separation input —
  planks whose frame entries and centre offsets are small at the weights `w` are not essentially
  distinct;
* `Plank.card_le_of_pose_confined_separated` (`Kakeya/DimensionThree/Plank/SlabBoxAPI.lean`) is the
  metric packing engine in the twelve-dimensional pose space.

What is missing is the reduction of the first to a *single* pose map, so that the second applies.
The pose to use reads the frame entries of each prism against a fixed reference prism `P₀` with the
anisotropic normalisation `96 R · w p / w q`, and the centre coordinates with `48 R / w q`; the
confinement hypothesis must be the *symmetric* one,
`max (w j) (w k) · |⟪e j, e' k⟫| ≤ R · min (w j) (w k)`, since the one-sided form
`w j · |⟪e j, e' k⟫| ≤ R · w k` leaves the off-diagonal entry unconstrained when `w q ≫ w k` and the
cross terms of the frame expansion then fail to close. With those normalisations the three terms of
the expansion each contribute exactly `w k / 96` (resp. `w k / 48`), matching the `/32` and `/16`
demanded by `plank_not_essentiallyDistinct_of_pose_close`, and the packing engine returns
`(768 R² + 2) ^ 12`. Both directions of the symmetric confinement are available at the call site,
because the normalising map of `Plank.slabTube` is exactly the one that makes the fibre's anisotropy
isotropic. Contrast `Plank.ThickenedRepr.phi_packing_bound`, which uses the same engine but
normalises all twelve coordinates at the *shortest* half-width and so only reaches `a ^ (-12)`.
-/

@[expose] public section

open MeasureTheory Kakeya
open scoped NNReal Real Classical

noncomputable section

namespace Plank

/-- **Fibre concentration for thickened representatives** (`lem:geometryFibreConcentration`).
For every dilation constant `cThk ≥ 1` there is a constant `C_conc ≥ 1` with the following property.
Suppose the original plank family is non-concentrated in
`Plank.ThickenedRepr.fibreDilation cThk`-dilated thickenings (`Plank.IsThickeningNonconcentrated`).
Then, for any `cThk`-thickened representative ensemble `R`, every active fibre `repr⁻¹(Q)`
(`Q ∈ R.indexSet`) contains at most `C_conc · M · θ` planks.

This is the `N ≲ M θ` input to the proof of GWZ Lemma 6.4; the `N`-form is
`Plank.thickenedRepresentativeFibreScale` below. The proof is
`Plank.ThickenedRepr.card_fibre_le_of_nonconcentration`: the fibre sits inside a *fixed* dilation of
the standard `θ`-thickening of any one of its own members
(`Plank.ThickenedRepr.fibre_subset_dilated_thickening`, from `subset_repr` and
`repr_subset_thickened`), and the hypothesis is then applied at the single scale `φ = θ`. In
particular `C_conc = 1` works and no large-`θ` branch is needed.

**The hypothesis is the dilated one, and this is a correction.** This lemma previously assumed the
*aligned* count `|{j ∈ s : P_j ⊆ (P_i)_θ}| ≤ M θ`, and with that hypothesis it is **false**: take
`a = b`, `θ = 1` and `K` planks obtained from one plank `P` by translating along its long axis by
distinct `δ ∈ (0,1)`. Each is non-essentially-distinct from `Q := (P)_1 = P` and lies in
`Q.dilation 2`, so all `K` form one fibre of a legitimate `ThickenedRepr` at `cThk = 2`; but at
`a = b` the aligned thickening `(P_i)_1` is `P_i` itself, so the aligned count is `1 ≤ M · θ` with
`M = 1` while the fibre has `K` members. Geometrically: the representative geometry controls a plank
only through fixed *dilations*, and dilating an aligned `θb × b × 1` thickening also widens its `b`-
and `1`-axes, which no aligned thickening at any scale `φ ≤ 1` recovers. (The counterexample family
is not pairwise essentially distinct, so it refutes the general implication without settling the
essentially distinct case; recovering the aligned form there would need the sharp anisotropic
packing bound that `Plank.ThickenedRepr.phi_packing_bound` explicitly does not provide.)

The dilation constant `cThk` is an *input*, not an output: the dilation factor at which the
hypothesis must hold, hence `C_conc`, depends on `cThk`, so an absolute `C_conc` valid for every
`cThk` would be false, while returning `cThk` existentially would make the lemma uncomposable — a
caller already holds a `ThickenedRepr` at the `cThk` supplied by `Plank.exists_thickenedRepr` (or by
`Kakeya.redPlankTube_finalAssembly`) and needs the fibre bound at *that* constant. Compare
`Plank.frostmanThickenedSlabFibre` and `Plank.normaliseSlabFamilyToTubes`, which take their loss
constants the same way. -/
theorem thickenedRepresentativeFibreCardinality (cThk : ℝ≥0) (hcThk : 1 ≤ cThk) :
    ∃ Cconc : ℝ≥0, 1 ≤ Cconc ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1)
        (R : ThickenedRepr s V θ hθ1 cThk) (M : ℝ≥0),
        0 < θ → a / b ≤ θ → 1 ≤ M →
        IsThickeningNonconcentrated s V (ThickenedRepr.fibreDilation cThk) M →
        ∀ Q ∈ R.indexSet,
          ((s.filter (fun i => R.repr i = Q)).card : ℝ≥0) ≤ Cconc * M * θ := by
  refine ⟨1, le_rfl, ?_⟩
  intro a b hab hb1 ι s V θ hθ1 R M _ hθa _ hNonconc Q hQ
  simpa using ThickenedRepr.card_fibre_le_of_nonconcentration R hNonconc hθa hQ

/-- **`N ≲ M θ`** (the form GWZ Lemma 6.4 consumes). For every `cThk ≥ 1` and every pigeonhole
constant `cN > 0` there is `Cfib ≥ 1` such that a uniform fibre scale `N` supplied by GWZ Lemma 6.13
— i.e. one with `N / cN ≤ |repr⁻¹(Q)|` for every active `Q` — obeys `N ≤ Cfib · M · θ`.

`Cfib = cN` works: the fibre bound of `Plank.thickenedRepresentativeFibreCardinality` gives
`|repr⁻¹(Q)| ≤ M θ` at any active `Q`, and the pigeonhole lower bound converts it. No power of
`b / a` appears anywhere. -/
theorem thickenedRepresentativeFibreScale (cThk cN : ℝ≥0) (hcThk : 1 ≤ cThk) (hcN : 1 ≤ cN) :
    ∃ Cfib : ℝ≥0, 1 ≤ Cfib ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1)
        (R : ThickenedRepr s V θ hθ1 cThk) (M : ℝ≥0) (N : ℕ),
        0 < θ → a / b ≤ θ → 1 ≤ M →
        IsThickeningNonconcentrated s V (ThickenedRepr.fibreDilation cThk) M →
        R.indexSet.Nonempty →
        (∀ Q ∈ R.indexSet, (N : ℝ) / (cN : ℝ) ≤ ((s.filter (fun i => R.repr i = Q)).card : ℝ)) →
        (N : ℝ≥0) ≤ Cfib * M * θ := by
  refine ⟨cN, hcN, ?_⟩
  intro a b hab hb1 ι s V θ hθ1 R M N _ hθa _ hM hne hfib
  exact ThickenedRepr.fibreScale_le_of_nonconcentration R hM hθa
    (lt_of_lt_of_le zero_lt_one hcN) hne hfib

/-- **Local Frostman constant of an assigned slab fibre** (`lem:geometryLocalFrostmanThickened`,
S6G15). There are absolute constants `cThk ≥ 1` and `C_loc ≥ 1` with the following property. Let `R`
be a `cThk`-thickened representative ensemble with a `(Cset, Cang)`-controlled slab assignment `SA`;
write `𝒯 = R.indexSet` for all active representatives and, for a used slab `S`,
`𝒯_S = 𝒯.filter (SA.slabOf · = S)` for the representatives assigned to `S`. If the original plank
family is `C_F`-Frostman in the unit ball (`IsFrostmanIn … CF`), then, for every used slab `S` with a
nonempty fibre `𝒯_S`, the scalar Frostman constant of the fibre inside the slab obeys
`C_F(𝒯_S, S) ≤ C_loc · CF · (|𝒯| / |𝒯_S|) · |S|`.
The actual fibre quotient `|𝒯|/|𝒯_S|` is retained (it cancels after summing per-slab lower bounds),
so equal slab-fibre cardinalities are not needed.

Three honesty points about the quantifiers, two of which are corrections to the earlier interface.

* `cThk`, and the slab-assignment losses `Cset`, `Cang`, are quantified *before* `C_loc`: the
  transfer of a Frostman bound from the planks to their representatives costs a factor depending on
  all three, so a `C_loc` uniform in them would be false.
* The transfer also needs the representative fibres to have comparable sizes, which an arbitrary
  `ThickenedRepr` does not provide. That comparison (`hfibre`, the `N`/`cN` data produced by the
  dyadic pigeonhole `ThickenedRepr.pigeonholeThickenedMultiplicity_of_card_positive`) is therefore an
  explicit hypothesis rather than something silently assumed. **`cN` is now quantified before
  `C_loc`**: the transfer pays `cN` twice — once for the fibre lower bound and once for
  `|s| ≤ cN · N · |𝒯|` — so `C_loc` genuinely depends on it and a `cN`-uniform `C_loc` is false
  (make the fibres over `𝒯_S` minimal and the others maximal).
* **The plank family must be known to lie in the window.** `IsFrostmanIn s V plankWindow CF` on its
  own says nothing about a family sitting outside the window: with every plank outside, `CF = 0`
  satisfies the hypothesis while the left-hand side is positive. The containment hypothesis
  `∀ i ∈ s, (V i).toConvexSpaceBody ≤ plankWindow` is what turns the Frostman hypothesis into the
  usable `Δ_max(𝒫) · |B| ≤ CF · ∑ |P_i|`
  (`Kakeya.maxDensity_mul_volume_le_of_isFrostmanIn`); every producer has it.

The proof is `Plank.ThickenedRepr.frostmanConstant_slabFibre_le`, applied to the slab fibre as an
arbitrary subset of `R.indexSet` — the slab assignment `SA` plays no role beyond naming the fibre,
and no containment of the fibre in (a dilation of) `S` is used, because the `|S|` on the right is the
`|K|` of `Kakeya.frostmanConstant` rather than the result of a slab-versus-ball comparison. -/
theorem frostmanThickenedSlabFibre (cThk Cset Cang cN : ℝ≥0)
    (hcThk : 1 ≤ cThk) (hCset : 1 ≤ Cset) (hCang : 1 ≤ Cang) (hcN : 1 ≤ cN) :
    ∃ Cloc : ℝ≥0, 1 ≤ Cloc ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1)
        (R : ThickenedRepr s V θ hθ1 cThk)
        (SA : SlabAssignment s V θ hθ1 R.repr Cset Cang)
        (N : ℕ) (CF : ENNReal),
        0 < a → 0 < θ → 1 ≤ N →
        (∀ Q ∈ R.indexSet,
          (N : ℝ) / (cN : ℝ) ≤ ((s.filter (fun i => R.repr i = Q)).card : ℝ) ∧
            ((s.filter (fun i => R.repr i = Q)).card : ℝ) ≤ (cN : ℝ) * (N : ℝ)) →
        (∀ i ∈ s, (V i).toConvexSpaceBody ≤ plankWindow) →
        ConvexSpaceBody.IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) plankWindow CF →
        ∀ S ∈ SA.used, (R.indexSet.filter (fun Q => SA.slabOf Q = S)).Nonempty →
          Kakeya.frostmanConstant (R.indexSet.filter (fun Q => SA.slabOf Q = S))
              (fun Q => Q.toConvexSpaceBody) S.toConvexSpaceBody
            ≤ (Cloc : ENNReal) * CF *
                ((R.indexSet.card : ENNReal)
                  / ((R.indexSet.filter (fun Q => SA.slabOf Q = S)).card : ENNReal))
                * volume S.carrier := by
  classical
  refine ⟨1 + enlargementConst cThk * cN ^ 2, ?_, ?_⟩
  · exact le_self_add
  · intro a b hab hb1 ι s V θ hθ1 R SA N CF ha hθ hN hfibre hVwin hFrost S hSused hfibre_ne
    set T : Finset (ThickenedPlank θ b hθ1 hb1) := R.indexSet.filter (fun Q => SA.slabOf Q = S)
    have hT : T ⊆ R.indexSet := by
      dsimp [T]
      exact Finset.filter_subset _ _
    have hb : 0 < b := lt_of_lt_of_le ha hab
    have hlo : ∀ Q ∈ R.indexSet, (N : ℝ) / (cN : ℝ) ≤ ((s.filter fun i => R.repr i = Q).card : ℝ) :=
      fun Q hQ => (hfibre Q hQ).1
    have hhi : ∀ Q ∈ R.indexSet, ((s.filter fun i => R.repr i = Q).card : ℝ) ≤ (cN : ℝ) * (N : ℝ) :=
      fun Q hQ => (hfibre Q hQ).2
    have h_le := ThickenedRepr.frostmanConstant_slabFibre_le R hT hfibre_ne hN hcN ha hb hθ hlo hhi
      hVwin hFrost S
    have hconst : ((enlargementConst cThk * cN ^ 2 : ℝ≥0) : ENNReal) ≤
        ((1 + enlargementConst cThk * cN ^ 2 : ℝ≥0) : ENNReal) := by
      exact ENNReal.coe_le_coe.mpr (le_add_of_nonneg_left (zero_le (a := (1 : ℝ≥0))))
    calc
      Kakeya.frostmanConstant T (fun Q => Q.toConvexSpaceBody) S.toConvexSpaceBody
          ≤ ((enlargementConst cThk * cN ^ 2 : ℝ≥0) : ENNReal) * CF *
              ((R.indexSet.card : ENNReal) / (T.card : ENNReal)) * volume S.carrier := h_le
      _ ≤ ((1 + enlargementConst cThk * cN ^ 2 : ℝ≥0) : ENNReal) * CF *
              ((R.indexSet.card : ENNReal) / (T.card : ENNReal)) * volume S.carrier := by
        gcongr

/-! ## The slab-fibre interface, and where it now lives

`Plank.SlabFibreGeometry`, `Plank.fibreTubeConst` and their immediate consequences have moved to
`Kakeya.DimensionThree.Plank.SlabFibreGeometry`. That module sits *below* the anisotropic
ED-packing bridge (`Kakeya.DimensionThree.Plank.SlabTubeEssentialDistinctness`,
`…SlabFibreFrame`, `…SlabTubeSelection`), which needs the structure; this module imports the
bridge, so every one of those names is still in scope here and for all downstream consumers. -/

/-- **Normalise a slab fibre to tubes** (`lem:geometrySlabToTubeNormalisation`), in the form that is
actually true. Every fibre with the slab-fibre geometry of `Plank.SlabFibreGeometry` is carried by
the *explicit* affine equivalence `Plank.slabFibreNormalisation Cfib S hθ0` onto the *explicit*
family of `b/8`-tubes `Plank.slabFibreTubes Cfib fibre Yθ S hθ0`, indexed by the fibre itself, with:

* every tube inside `B₁` — for *every* index, not only those in the fibre, which is the form
  `Kakeya.FrostmanEstimate.multiplicity_bound` consumes;
* the shading transported exactly, `(T Q).shade = g '' (Yθ Q).shade`, hence an exact identity for
  the volume of the union of shades;
* the transported prism (the **core** `g '' Q.carrier`) inside its own tube;
* the cores **pairwise essentially distinct**;
* multiplicity preserved exactly, and fullness preserved up to the fixed `Plank.fibreTubeLoss Cfib`;
* cardinality preserved exactly (the index set *is* the fibre).

**Nothing here is existentially quantified.** The map, the tube family and the loss constant are
all given by name. That is what lets the anisotropic ED-packing bridge of
`Kakeya.DimensionThree.Plank.SlabTubeSelection` — which is stated for
`Q.slabTube S (fibreTubeConst Cfib) …`, the underlying tube of `Plank.slabFibreTubes` on the fibre
(`Plank.slabFibreTubes_toTube`) — be applied to the very same family, with no transport step.

## Three corrections to the earlier statement

**The tube radius is `b / 8`, not `b`.** `Plank.slabTube` produces a `Tube (b / 8)`, and the fixed
factor `8` is forced: the normalising map `Slab.normalizeScaled S κ` must contract by
`κ = Plank.slabTubeConst` in order to land the axial half-length inside `1 / 2` and the image centre
inside `closedBall 0 (3 / 16)`. Nothing downstream needs the radius to be `b` on the nose — the
per-slab bound of `Plank.frostmanSlabUnionVolumeLowerBound` is stated with explicit powers of `b`,
and replacing `b` by `b / 8` changes them by the fixed factor `8 ^ (-2β - β)`, absorbed by `K`. The
earlier `ShadedTube b` was therefore  unavailable from the existing
normalisation. The small-scale hypothesis `b ≤ 1 / 4` is correspondingly no longer needed:
`Plank.slabTube_carrier_subset_closedBall` closes the budget `3/16 + 1/2 + 1/8 ≤ 1` from `b ≤ 1`
alone.

**Pairwise essential distinctness of the *tubes* is false, and is not claimed.** `SlabFibreGeometry`
asserts essential distinctness of the undilated prisms `Q`, and essential distinctness is an affine
invariant (`IsEssentiallyDistinct.mapAffine`), so the cores `g '' Q.carrier` are pairwise
essentially distinct — that is what this lemma exports. But the tube strictly *inflates* the core:
the core is a box of half-widths `(κ b, κ b, κ)` while the enclosing tube has radius `b / 8` and
half-length `1 / 2`, i.e. it is larger by the fixed factor `1 / (8 κ) ≥ 2` transversally and
`1 / (2 κ) ≥ 8` axially. Two cores that are essentially distinct only because they are separated at
their own scale are swallowed by the common inflation, and their tubes then coincide up to a set of
small measure. So no bookkeeping recovers `Pairwise IsEssentiallyDistinct` for `T`; the honest
statement is `Kakeya.IsEDUpToMult` with a multiplicity depending on `Cfib`, which is exactly what
`Plank.exists_isEDUpToMult_slabTube` supplies, downstream, from the core essential distinctness
exported here plus the anisotropic prism-packing estimate
`Plank.card_le_of_anisotropicConfined_pairwiseED`. It is *not* asserted here, so that this lemma
stays pure normalisation geometry and the packing geometry stays in
`Kakeya.DimensionThree.Plank.SlabTubeSelection`.

**The Frostman clause is not part of the normalisation.** `ConvexSpaceBody.IsFrostmanIn.mapAffine`
transports a Frostman bound to the cores with the *same* constant, but passing from the cores to
the enclosing tubes changes both `maxDensity` and `densityIn`, and is governed by the same
inflation. The clause is therefore dropped rather than asserted with a fixed loss. -/
theorem normaliseSlabFamilyToTubes (Cfib : ℝ≥0) (hCfib : 1 ≤ Cfib) :
    ∀ {b : ℝ≥0} {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ1 : θ ≤ 1}
      (fibre : Finset (ThickenedPlank θ b hθ1 hb1))
      (Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (S : Slab θ hθ1) (hb0 : 0 < b) (hθ0 : 0 < θ),
      SlabFibreGeometry fibre Yθ S Cfib →
        (∀ Q, ((slabFibreTubes Cfib fibre Yθ S hθ0 Q).carrier :
            Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 1) ∧
        (∀ Q ∈ fibre, (slabFibreTubes Cfib fibre Yθ S hθ0 Q).shade
          = slabFibreNormalisation Cfib S hθ0 '' (Yθ Q).shade) ∧
        (∀ Q ∈ fibre,
          slabFibreNormalisation Cfib S hθ0 '' (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
            ((slabFibreTubes Cfib fibre Yθ S hθ0 Q).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))) ∧
        (↑fibre : Set (ThickenedPlank θ b hθ1 hb1)).Pairwise
          (fun Q Q' => _root_.IsEssentiallyDistinct
            (slabFibreNormalisation Cfib S hθ0 ''
              (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))))
            (slabFibreNormalisation Cfib S hθ0 ''
              (Q'.carrier : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        ShadedBody.multiplicity fibre
            (fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toShadedBody)
          = ShadedBody.multiplicity fibre Yθ ∧
        (fibreTubeLoss Cfib)⁻¹ * ShadedBody.fullness fibre Yθ
          ≤ ShadedBody.fullness fibre
              (fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toShadedBody) ∧
        volume (⋃ Q ∈ fibre, (slabFibreTubes Cfib fibre Yθ S hθ0 Q).shade)
          = Kakeya.affineJacobian (slabFibreNormalisation Cfib S hθ0)
              * volume (⋃ Q ∈ fibre, (Yθ Q).shade) := by
  intro b hb1 θ hθ1 fibre Yθ S hb0 hθ0 h
  exact ⟨slabFibreTubes_carrier_subset_closedBall h hCfib hθ0,
    fun Q hQ => slabFibreTubes_shade h hCfib hθ0 hQ,
    fun Q hQ => slabFibreTubes_core_subset h hCfib hθ0 hQ,
    slabFibreTubes_pairwise_core_ED h hθ0,
    slabFibreTubes_multiplicity h hCfib hθ0,
    slabFibreTubes_fullness h hCfib hθ0 hb0,
    slabFibreTubes_volume_iUnion_shade h hCfib hθ0⟩

/-- **Per-slab Frostman volume lower bound** (analysis leaf for GWZ Lemma 6.4).
For every `ε > 0`, every per-slab fullness constant `c2 > 0` and every slab-fibre loss `Cfib ≥ 1`
there are `η, b₀ > 0` and a constant `K > 0` with the following property. Consider one used slab `S`
at angle `θ` and the fibre `fibre ⊆ 𝒯` of thickened representative prisms assigned to it, shaded by
`Yθ`, with the slab-fibre geometry of `Plank.SlabFibreGeometry`, fullness `≥ c2·a^(4η)`, and with the
local Frostman constant of the fibre inside `S` controlled by `Cloc·CF·(|𝒯|/|fibre|)·|S|`. Applying the
affine slab-to-tube normalisation and the generalized (τ-flexible) Frostman tube estimate at scale
`b` gives the per-slab union-volume lower bound (up to the loss `K`)
`a^ε · CF^(β/2-1) · b^(2β) · (b²)^(β/2) · θ^(β/2) · |𝒯|^(β/2-1) · |fibre| ≤ K · |U(fibre, Yθ)|`.
This is the honest per-slab step of the proof of GWZ Lemma 6.4; the `θ^(β/2)` factor cancels
against `∑_S |fibre_S| = |𝒯|` when summing over slabs.

The prisms *are* the fibre elements, and `SlabFibreGeometry` is what connects them, their shadings
`Yθ`, and the slab `S`; the earlier signature carried an unrelated `Qθ` with no hypothesis linking it
to `S`. The loss `Cfib` is quantified before `K`, since the normalisation loss depends on it — and
`Cfib` is now also (i) the radius of the controlled ball containing the fibre
(`SlabFibreGeometry.subset_controlledBall`) and (ii) the dilation factor carrying the shading bodies
(`SlabFibreGeometry.shade_body`, `(Yθ Q).carrier = (Q.dilation Cfib).carrier`). So `K` absorbs both
the fixed contraction that `Plank.normaliseSlabFamilyToTubes` performs and the fixed
volume/fullness loss of passing from `Q` to `Q.dilation Cfib`. The shading bodies are *not* assumed
to be carried by the undilated representatives: that is not something the plank-to-tube reduction
can supply.

## The local Frostman loss `Cloc`

The Frostman constant governing a *fibre of thickened representatives* inside `S` is not the Frostman
constant `CF` of the original plank family: transferring the bound from the planks to their
representatives costs the fixed factor `Cloc` of `Plank.frostmanThickenedSlabFibre`. That is why the
Frostman hypothesis below is stated in the honest form

`C_F(fibre, S) ≤ Cloc · CF · (|𝒯| / |fibre|) · |S|`,

with `Cloc` an explicit parameter quantified **before** `η`, `b₀` and `K`, and *not* as the
`Cloc`-free bound that the consumer cannot supply.

Since `β / 2 - 1 ≤ 0`, running the tube estimate with the effective local constant `Cloc · CF`
produces `(Cloc · CF) ^ (β/2 - 1) = Cloc ^ (β/2 - 1) · CF ^ (β/2 - 1)`, i.e. it costs the fixed
factor `Cloc ^ (1 - β/2)` relative to the plain-`CF` form stated in the conclusion. That factor is
retained honestly: it is absorbed into this lemma's own fixed loss `K`, which is exactly why `K` is
quantified after `Cloc`. The `CF` in the conclusion is therefore the Frostman constant of the original
family, which is what `Kakeya.aggregateSlabVolume` and GWZ Lemma 6.4 consume — no step anywhere
rewrites `Cloc * CF` to `CF`.

The proof is `Plank.frostmanSlabUnionVolumeLowerBound_proof`
(`Kakeya.DimensionThree.Plank.SlabFrostmanEstimate`), where the analytic input — the two-scale,
free-Frostman-constant form of GWZ Lemma 3.9 — is isolated as the single explicit hypothesis of
`Plank.frostmanSlabUnionVolumeLowerBound_of_twoScaleKF`. -/
theorem frostmanSlabUnionVolumeLowerBound {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKF : Kakeya.FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β) :
    ∀ ε > (0 : ℝ), ∀ c2 > (0 : ℝ≥0), ∀ Cfib : ℝ≥0, 1 ≤ Cfib → ∀ Cloc : ℝ≥0, 1 ≤ Cloc →
      ∃ η > (0 : ℝ), ∃ b₀ > (0 : ℝ≥0), ∃ K : ℝ≥0, 0 < K ∧
      ∀ {a b : ℝ≥0} (ha : 0 < a) (hab : a ≤ b) (hb0 : b ≤ b₀) (hb1 : b ≤ 1)
        {θ : ℝ≥0} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθa : a / b ≤ θ)
        (Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (𝒯 fibre : Finset (ThickenedPlank θ b hθ1 hb1)) (S : Slab θ hθ1) (CF : ENNReal),
        fibre ⊆ 𝒯 → fibre.Nonempty → 1 ≤ CF → CF ≠ ⊤ →
        SlabFibreGeometry fibre Yθ S Cfib →
        (c2 : ℝ≥0) * a ^ (4 * η) ≤ ShadedBody.fullness fibre Yθ →
        Kakeya.frostmanConstant fibre (fun Q => Q.toConvexSpaceBody) S.toConvexSpaceBody
            ≤ (Cloc : ENNReal) * CF
              * ((𝒯.card : ENNReal) / (fibre.card : ENNReal)) * volume S.carrier →
        (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
              * ((b : ENNReal) ^ 2) ^ (β / 2) * (θ : ENNReal) ^ (β / 2)
              * (𝒯.card : ENNReal) ^ (β / 2 - 1) * (fibre.card : ENNReal)
            ≤ (K : ENNReal) * volume (⋃ Q ∈ fibre, (Yθ Q).shade) :=
  frostmanSlabUnionVolumeLowerBound_proof hβpos hβle hKF

/-- `f` **normalises** the plank `W` with contraction `κ > 0` and target frame `g`: it rotates `W`'s
ordered frame `W.basis` onto `g` and scales the `i`-th coordinate by `κ / W.thicknesses i`, i.e. by
`κ/a`, `κ/b`, `κ` respectively. This is exactly the map produced by
`Plank.factorNormalisingAffineEquiv` (translate the centre, rotate the frame to a standard basis,
compose with `diag (a⁻¹, b⁻¹, 1)` and one fixed contraction).

Carrying this structural description is *necessary* for S6G18, not cosmetic. Without it `f` is
constrained only by a volume identity, and then **no** lower bound on the least width of
`W ∩ f⁻¹(S)` can hold: take `f = id`, `θ = 1` and `S ⊇ W`, so that `W ∩ f⁻¹(S) = W`, whose least
width is exactly `a` by `Prism3D.a_le_ethickness_scale` and `Prism3D.ethickness_scale_le_a`, while
`a/b` may be arbitrarily small. -/
def IsPlankNormalisation {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (κ : ℝ)
    (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin 3), f x = f W.center
    + ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - W.center) (W.basis i)) • g i

/-- **The diagonal normalising linear map of a plank**: in the frame `W.basis` it scales the `i`-th
coordinate by `κ / W.thicknesses i`, and its determinant is `κ ^ 3 / (a * b)`. -/
private theorem exists_diagonalNormalisingLinearMap {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (ha : 0 < a) (W : Plank a b hab hb1) (κ : ℝ) :
    ∃ L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3),
      (∀ v, L v = ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ v (W.basis i)) • W.basis i) ∧
      LinearMap.det L = κ ^ 3 * ((a : ℝ) * (b : ℝ))⁻¹ := by
  set bsis := W.basis.toBasis
  have hsum : ∀ v, v = ∑ i, inner ℝ v (W.basis i) • W.basis i := by
    intro v
    calc
      v = ∑ i, inner ℝ (W.basis i) v • W.basis i := by
        rw [W.basis.sum_repr' v]
      _ = ∑ i, inner ℝ v (W.basis i) • W.basis i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [real_inner_comm]
  let L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    bsis.constr ℝ (fun i => (κ * ((W.thicknesses i : ℝ))⁻¹) • W.basis i)
  have hL_formula : ∀ v, L v = ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ v (W.basis i)) • W.basis i := by
    intro v
    calc
      L v = L (∑ i, inner ℝ v (W.basis i) • W.basis i) :=
        congrArg L (hsum v)
      _ = ∑ i, inner ℝ v (W.basis i) • L (W.basis i) := by
        simp [map_sum, LinearMap.map_smul]
      _ = ∑ i, inner ℝ v (W.basis i) • ((κ * ((W.thicknesses i : ℝ))⁻¹) • W.basis i) := by
        simp [L, bsis, Module.Basis.constr_basis]
      _ = ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ v (W.basis i)) • W.basis i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
  have h_diag : LinearMap.toMatrix bsis bsis L = Matrix.diagonal (fun i => κ * ((W.thicknesses i : ℝ))⁻¹) := by
    ext i j
    simp [LinearMap.toMatrix_apply, L, bsis, Module.Basis.constr_basis, Matrix.diagonal_apply,
      Module.Basis.repr_self]
    split_ifs with h
    · rw [h]
    · rfl
  have h_det : LinearMap.det L = κ ^ 3 * ((a : ℝ) * (b : ℝ))⁻¹ := by
    calc
      LinearMap.det L = Matrix.det (LinearMap.toMatrix bsis bsis L) := by
        rw [LinearMap.det_toMatrix]
      _ = Matrix.det (Matrix.diagonal (fun i => κ * ((W.thicknesses i : ℝ))⁻¹)) := by rw [h_diag]
      _ = ∏ i : Fin 3, (κ * ((W.thicknesses i : ℝ))⁻¹) := by rw [Matrix.det_diagonal]
      _ = (κ * ((W.thicknesses 0 : ℝ))⁻¹) * (κ * ((W.thicknesses 1 : ℝ))⁻¹) * (κ * ((W.thicknesses 2 : ℝ))⁻¹) := by
        rw [Fin.prod_univ_three]
      _ = κ ^ 3 * ((a : ℝ) * (b : ℝ))⁻¹ := by
        rw [W.thicknesses_eq]
        simp
        ring
  refine ⟨L, hL_formula, h_det⟩

/-- Volume of the image of an arbitrary set under `x ↦ L (x - c)`. -/
private theorem volume_image_sub_linearMap
    (L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))
    (c : EuclideanSpace ℝ (Fin 3)) (S : Set (EuclideanSpace ℝ (Fin 3))) :
    volume ((fun x => L (x - c)) '' S) = ENNReal.ofReal |LinearMap.det L| * volume S := by
  have h_image : (fun x => L (x - c)) '' S = (fun y => y - L c) '' (L '' S) :=
  calc
    (fun x => L (x - c)) '' S = ((fun y => y - L c) ∘ L) '' S := by
      refine congrArg (· '' S) ?_
      ext x; simp [map_sub L]
    _ = (fun y => y - L c) '' (L '' S) := (Set.image_image (fun y => y - L c) L S).symm
  calc
    volume ((fun x => L (x - c)) '' S)
        = volume ((fun y => y - L c) '' (L '' S)) := by rw [h_image]
    _ = volume (L '' S) := by
      simpa [sub_eq_add_neg, add_comm] using MeasureTheory.measure_image_add volume (-L c) (L '' S)
    _ = ENNReal.ofReal |LinearMap.det L| * volume S := by
      rw [MeasureTheory.Measure.addHaar_image_linearMap volume L S]

/-- **Affine map normalising a factor plank** (`lem:geometryFactorAffineMap`).

For an `a × b × 1` factor plank `W` there is an affine map `f` with linear part comparable to
`diag (a⁻¹, b⁻¹, 1)`, sending `W` into the unit ball, and with a constant Jacobian `J`: translate
the centre of `W` to the origin, rotate its ordered frame to the standard basis, compose with
`diag (a⁻¹, b⁻¹, 1)` and one fixed contraction. Since `|W| = 8ab`, the Jacobian obeys
`J · (a · b) ∼ 1`, which is how the comparability of the linear factors is recorded here.

Following `Plank.boxRescaleAffine`, the map is delivered as an `→ᵃ[ℝ]` together with the volume
identity `volume (f '' E) = J · volume E` rather than as a bundled `AffineEquiv`.

The contraction `κ` and the target frame `g` are exposed as well, via
`Plank.IsPlankNormalisation`: `κ` is absolute (it is the fixed contraction taking the normalised
cube into `B₁`), while `g` depends on `W`. S6G18 needs this structural description — a bare volume
identity does not determine `f` enough for any width bound to hold. The proof constructs the explicit
diagonal normalisation map. -/
theorem factorNormalisingAffineEquiv :
    ∃ (κ : ℝ) (cfac Cfac : ℝ≥0), 0 < κ ∧ 0 < cfac ∧ 1 ≤ Cfac ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (ha : 0 < a) (W : Plank a b hab hb1),
        ∃ (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (J : ℝ≥0)
          (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))),
          0 < J ∧
          IsPlankNormalisation W f κ g ∧
          (∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ENNReal) * volume E) ∧
          f '' W.carrier ⊆ Metric.closedBall 0 1 ∧
          (∀ x ∈ W.carrier, ‖f x - f W.center‖ ≤ 1) ∧
          cfac ≤ J * (a * b) ∧ J * (a * b) ≤ Cfac := by
  refine ⟨(1 : ℝ)/3, (27 : ℝ≥0)⁻¹, 1, by norm_num, by norm_num, le_rfl, ?_⟩
  intro a b hab hb1 ha W
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  have hane : ((a : ℝ)) ≠ 0 := by exact_mod_cast ha.ne.symm
  have hbne : ((b : ℝ)) ≠ 0 := by exact_mod_cast hbpos.ne.symm
  have hthick_pos : ∀ i : Fin 3, (0 : ℝ) < (W.thicknesses i : ℝ) := by
    intro i; rw [W.thicknesses_eq]; fin_cases i
    · exact_mod_cast ha
    · exact_mod_cast hbpos
    · norm_num
  obtain ⟨L, hL_formula, hL_det⟩ := exists_diagonalNormalisingLinearMap ha W ((1 : ℝ)/3)
  set f := AffineMap.mk' (fun x => L (x - W.center)) L W.center (by intro p'; simp) with hf_def
  have hfapp : ∀ x, f x = L (x - W.center) := by
    intro x
    rw [hf_def, AffineMap.coe_mk']
  have hfc : f W.center = 0 := by
    rw [hfapp, sub_self, map_zero]
  set J : ℝ≥0 := (27 : ℝ≥0)⁻¹ * (a * b)⁻¹ with hJ_def
  have hJpos : 0 < J := by
    dsimp [J]
    refine mul_pos (by norm_num) (inv_pos.mpr ?_)
    exact mul_pos ha hbpos
  -- IsPlankNormalisation
  have h_plank_norm : IsPlankNormalisation W f ((1 : ℝ)/3) W.basis := by
    intro x
    rw [hfapp, hfc, zero_add]
    exact hL_formula (x - W.center)
  -- Volume identity
  have hJreal : ((J : ℝ≥0) : ℝ) = |LinearMap.det L| := by
    dsimp [J]
    rw [hL_det]
    have hpos : 0 < ((1 : ℝ)/3) ^ 3 * ((a : ℝ) * (b : ℝ))⁻¹ := by
      refine mul_pos (by norm_num) (inv_pos.mpr ?_)
      exact mul_pos (by exact_mod_cast ha) (by exact_mod_cast hbpos)
    rw [abs_of_pos hpos]
    push_cast
    field_simp [hane, hbne]
    ring
  have hJcoe : (J : ENNReal) = ENNReal.ofReal |LinearMap.det L| := by
    rw [← hJreal, ENNReal.ofReal_coe_nnreal]
  have h_vol : ∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ENNReal) * volume E := by
    intro E
    calc
      volume (f '' E) = volume ((fun x => L (x - W.center)) '' E) := by
        simp [hfapp]
      _ = ENNReal.ofReal |LinearMap.det L| * volume E := volume_image_sub_linearMap L W.center E
      _ = (J : ENNReal) * volume E := by rw [hJcoe]
  -- Norm bound
  have h_norm : ∀ x ∈ W.carrier, ‖f x - f W.center‖ ≤ 1 := by
    intro x hx
    rw [hfapp, hfc, sub_zero]
    have hx_inner : ∀ i : Fin 3, |inner ℝ (x - W.center) (W.basis i)| ≤ (W.thicknesses i : ℝ) := by
      intro i
      have hmem := (W.mem_carrier_iff (x := x)).mp hx i
      rw [W.basis.repr_apply_apply, vsub_eq_sub] at hmem
      rw [real_inner_comm] at hmem
      exact hmem
    have hthick_ne_zero : ∀ i : Fin 3, (W.thicknesses i : ℝ) ≠ 0 := by
      intro i; exact ne_of_gt (hthick_pos i)
    have h_term_bound : ∀ i : Fin 3,
        |(1/3 : ℝ) * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - W.center) (W.basis i)| ≤ 1/3 := by
      intro i
      calc
        |(1/3 : ℝ) * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - W.center) (W.basis i)|
            = (1/3 : ℝ) * ((W.thicknesses i : ℝ))⁻¹ * |inner ℝ (x - W.center) (W.basis i)| := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1/3),
            abs_of_pos (inv_pos.mpr (hthick_pos i))]
        _ ≤ (1/3 : ℝ) * ((W.thicknesses i : ℝ))⁻¹ * (W.thicknesses i : ℝ) := by
          gcongr; exact hx_inner i
        _ = (1/3 : ℝ) := by
          field_simp [hthick_ne_zero i]
    calc
      ‖L (x - W.center)‖ = ‖∑ i : Fin 3, ((1/3 : ℝ) * ((W.thicknesses i : ℝ))⁻¹
          * inner ℝ (x - W.center) (W.basis i)) • W.basis i‖ := by
        rw [hL_formula (x - W.center)]
      _ ≤ ∑ i : Fin 3, ‖(((1/3 : ℝ) * ((W.thicknesses i : ℝ))⁻¹
          * inner ℝ (x - W.center) (W.basis i)) • W.basis i)‖ := norm_sum_le _ _
      _ = ∑ i : Fin 3, |(1/3 : ℝ) * ((W.thicknesses i : ℝ))⁻¹
          * inner ℝ (x - W.center) (W.basis i)| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, W.basis.norm_eq_one i, mul_one, Real.norm_eq_abs]
      _ ≤ ∑ i : Fin 3, (1/3 : ℝ) :=
        Finset.sum_le_sum fun i _ => h_term_bound i
      _ = 3 * (1/3 : ℝ) := by simp
      _ = 1 := by norm_num
  -- closedBall containment
  have h_closedBall : f '' W.carrier ⊆ Metric.closedBall 0 1 := by
    rintro y ⟨x, hx, rfl⟩
    have hx' : ‖f x - f W.center‖ ≤ 1 := h_norm x hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    calc
      ‖f x‖ = ‖f x - f W.center‖ := by simp [hfc]
      _ ≤ 1 := hx'
  -- Comparability goals
  have hJab_val : ((J * (a * b) : ℝ≥0) : ℝ) = ((27 : ℝ≥0)⁻¹ : ℝ) := by
    dsimp [J]
    push_cast
    field_simp [hane, hbne]
  have hJab : J * (a * b) = (27 : ℝ≥0)⁻¹ := by
    apply NNReal.coe_injective
    simpa using hJab_val
  refine ⟨f, J, W.basis, hJpos, h_plank_norm, h_vol, h_closedBall, h_norm, ?_, ?_⟩
  · -- cfac ≤ J * (a * b), i.e., (27 : ℝ≥0)⁻¹ ≤ (27 : ℝ≥0)⁻¹
    simpa [hJab]
  · -- J * (a * b) ≤ Cfac, i.e., (27 : ℝ≥0)⁻¹ ≤ 1
    rw [hJab]
    have h27inv : (27 : ℝ≥0)⁻¹ ≤ 1 := by
      have h' : ((27 : ℝ≥0)⁻¹ : ℝ) ≤ (1 : ℝ) := by
        calc
          ((27 : ℝ≥0)⁻¹ : ℝ) = (27 : ℝ)⁻¹ := by norm_num
          _ = (1/27 : ℝ) := by norm_num
          _ ≤ (1 : ℝ) := by norm_num
      exact_mod_cast h'
    exact h27inv

/-- **A `θ × 1 × 1` slab meets the unit ball in volume `≤ 8θ`.** In the slab's own orthonormal
frame the intersection is trapped in the `θ × 1 × 1` box whose thin centre coordinate is that of `S`
and whose two long centre coordinates are `0`, because `‖y‖ ≤ 1` forces `|⟪y, S.basis i⟫| ≤ 1`. -/
theorem volume_closedBall_inter_slab_le {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) :
    volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ∩ S.carrier)
      ≤ 8 * (θ : ENNReal) := by
  let c : EuclideanSpace ℝ (Fin 3) := (inner ℝ S.center (S.basis 0)) • S.basis 0
  let S' : Slab θ hθ1 :=
    { toPrismNDim := PrismNDim.mk' c S.basis ![θ, 1, 1], thicknesses_eq := rfl }
  have hsubset : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ∩ S.carrier ⊆ S'.carrier := by
    intro y hy
    rcases hy with ⟨hyB, hyS⟩
    rw [S'.mem_carrier_iff]
    intro i
    have h_inner : S'.basis.repr (y -ᵥ S'.center) i = inner ℝ (y -ᵥ S'.center) (S'.basis i) := by
      rw [S'.basis.repr_apply_apply, real_inner_comm]
    rw [h_inner, vsub_eq_sub]
    have hyB' : ‖y‖ ≤ 1 := by
      have hd := Metric.mem_closedBall.mp hyB
      rw [dist_eq_norm, sub_zero] at hd
      exact hd
    fin_cases i
    · -- i = 0
      dsimp [S', PrismNDim.mk']
      have hc0 : inner ℝ c (S.basis 0) = inner ℝ S.center (S.basis 0) := by
        dsimp [c]
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq, S.basis.norm_eq_one 0]
        norm_num
      have h_eq : inner ℝ (y - c) (S.basis 0) = inner ℝ (y - S.center) (S.basis 0) := by
        calc
          inner ℝ (y - c) (S.basis 0) = inner ℝ y (S.basis 0) - inner ℝ c (S.basis 0) := by
            rw [inner_sub_left]
          _ = inner ℝ y (S.basis 0) - inner ℝ S.center (S.basis 0) := by rw [hc0]
          _ = inner ℝ (y - S.center) (S.basis 0) := by rw [← inner_sub_left]
      have hyS0 : |inner ℝ (y - S.center) (S.basis 0)| ≤ (θ : ℝ) := by
        have hmem := (S.mem_carrier_iff (x := y)).mp hyS 0
        rw [S.basis.repr_apply_apply, real_inner_comm, vsub_eq_sub, S.thicknesses_eq] at hmem
        simpa using hmem
      rw [h_eq]
      simpa using hyS0
    · -- i = 1
      dsimp [S', PrismNDim.mk']
      have hc1 : inner ℝ c (S.basis 1) = 0 := by
        dsimp [c]
        rw [real_inner_smul_left]
        simp
      have hb : |inner ℝ (y - c) (S.basis 1)| ≤ 1 := by
        rw [inner_sub_left, hc1, sub_zero]
        calc
          |inner ℝ y (S.basis 1)| ≤ ‖y‖ * ‖S.basis 1‖ := abs_real_inner_le_norm _ _
          _ = ‖y‖ := by simp [S.basis.norm_eq_one 1]
          _ ≤ 1 := hyB'
      simpa using hb
    · -- i = 2
      dsimp [S', PrismNDim.mk']
      have hc2 : inner ℝ c (S.basis 2) = 0 := by
        dsimp [c]
        rw [real_inner_smul_left]
        simp
      have hb : |inner ℝ (y - c) (S.basis 2)| ≤ 1 := by
        rw [inner_sub_left, hc2, sub_zero]
        calc
          |inner ℝ y (S.basis 2)| ≤ ‖y‖ * ‖S.basis 2‖ := abs_real_inner_le_norm _ _
          _ = ‖y‖ := by simp [S.basis.norm_eq_one 2]
          _ ≤ 1 := hyB'
      simpa using hb
  have hvol : volume S'.carrier = 8 * (θ : ENNReal) := by
    rw [Prism3D.volume_carrier S']
    simp
  exact (measure_mono hsubset).trans hvol.le

/-- **Volume of a pulled-back normalised slab** (`lem:geometryPullbackSlabVolume`, S6G17).

For a `θ × 1 × 1` slab `S` in normalised coordinates, the pullback
`K_{W,S} = W ∩ f⁻¹(S)` is convex and `|K_{W,S}| ≤ C_pull · θ · |W|`.

Convexity is immediate (affine preimages of convex sets are convex, and intersecting with the
convex plank `W` preserves convexity). For the volume: `f(K_{W,S}) = f(W) ∩ S ⊆ B₁ ∩ S`, and in the
frame of `S` Fubini bounds `|B₁ ∩ S|` by the short width `≲ θ` times the area of a fixed
two-dimensional ball; the inverse Jacobian identity
(`MeasureTheory.Measure.addHaar_preimage_linearMap`) then converts this into the stated bound, using
that `J · (a · b)` is bounded above and below by absolute constants.

The lower bound `cfac ≤ J · (a · b)` is essential: with a contraction `f x = ε • (x - W.center)`
on the unit cube `a = b = 1`, `ε ≤ min θ (1 / 2)`, and `S` the `θ × 1 × 1` slab centred at `0`,
`W.carrier ∩ f ⁻¹' S.carrier = W.carrier` and the claimed bound collapses to `1 ≤ C_pull · θ`,
which is false for small `θ`. -/
theorem volumePullbackNormalisedSlab (cfac : ℝ≥0) (hcfac : 0 < cfac) :
    ∃ Cpull : ℝ≥0, 1 ≤ Cpull ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (ha : 0 < a) (W : Plank a b hab hb1)
        (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (J : ℝ≥0),
        0 < J →
        (∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ENNReal) * volume E) →
        f '' W.carrier ⊆ Metric.closedBall 0 1 →
        cfac ≤ J * (a * b) →
        ∀ (θ : ℝ≥0) (hθ1 : θ ≤ 1) (S : Slab θ hθ1),
          Convexity.IsConvexSet ℝ (W.carrier ∩ f ⁻¹' S.carrier) ∧
          volume (W.carrier ∩ f ⁻¹' S.carrier)
            ≤ (Cpull : ENNReal) * (θ : ENNReal) * volume W.carrier := by
  refine ⟨max 1 cfac⁻¹, ?_, ?_⟩
  · exact le_max_left (1 : ℝ≥0) cfac⁻¹
  · intro a b hab hb1 ha W f J hJ hvolf himg hJab θ hθ1 S
    have hWconv : Convexity.IsConvexSet ℝ (W.carrier : Set _) := by
      exact W.convex'
    have hSconv : Convexity.IsConvexSet ℝ (S.carrier : Set _) := by
      exact S.convex'
    have hpre : Convexity.IsConvexSet ℝ (f ⁻¹' S.carrier) :=
      Convexity.IsConvexSet.affineMap_preimage f hSconv
    have hconv : Convexity.IsConvexSet ℝ (W.carrier ∩ f ⁻¹' S.carrier) :=
      hWconv.inter hpre
    refine ⟨hconv, ?_⟩
    let K : Set (EuclideanSpace ℝ (Fin 3)) := W.carrier ∩ f ⁻¹' S.carrier
    have hK : f '' K = f '' W.carrier ∩ S.carrier := by
      dsimp [K]
      rw [Set.image_inter_preimage]
    have hvol : volume (f '' W.carrier ∩ S.carrier) = (J : ENNReal) * volume K := by
      rw [← hK, hvolf K]
    have hsub : f '' W.carrier ∩ S.carrier ⊆
        Metric.closedBall 0 1 ∩ S.carrier := by
      intro y hy
      rcases hy with ⟨hyf, hyS⟩
      constructor
      · rw [Set.mem_image] at hyf
        rcases hyf with ⟨x, hxW, rfl⟩
        exact himg ⟨x, hxW, rfl⟩
      · exact hyS
    have htm : (J : ENNReal) * volume K ≤ 8 * (θ : ENNReal) := by
      rw [← hvol]
      exact (measure_mono hsub).trans (volume_closedBall_inter_slab_le S)
    have hJne : (J : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hJ.ne'
    have hJnt : (J : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hVle : volume K ≤ (J : ENNReal)⁻¹ * (8 * (θ : ENNReal)) := by
      exact (ENNReal.mul_le_iff_le_inv hJne hJnt).mp htm
    have hbpos : 0 < b := lt_of_lt_of_le ha hab
    have hab_pos : 0 < a * b := mul_pos ha hbpos
    -- J⁻¹ ≤ cfac⁻¹ * (a * b), from cfac ≤ J * (a * b) by inverting (order-reversing) and
    -- multiplying back by the positive factor a * b.
    have hJinv_le : (J⁻¹ : ℝ≥0) ≤ cfac⁻¹ * (a * b) := by
      have h_invNN : (J * (a * b))⁻¹ ≤ cfac⁻¹ :=
        (inv_le_inv₀ (mul_pos hJ hab_pos) hcfac).mpr hJab
      have hfac_pos : (a * b) ≠ 0 := hab_pos.ne'
      calc
        (J⁻¹ : ℝ≥0) = (J⁻¹ * (a * b)⁻¹) * (a * b) := by
          rw [mul_assoc, inv_mul_cancel₀ hfac_pos, mul_one]
        _ = (J * (a * b))⁻¹ * (a * b) := by rw [← mul_inv]
        _ ≤ cfac⁻¹ * (a * b) := mul_le_mul_of_nonneg_right h_invNN (by positivity)
    -- cfac⁻¹ ≤ max 1 cfac⁻¹, so J⁻¹ ≤ max 1 cfac⁻¹ * (a * b).
    have hkey : (J⁻¹ : ℝ≥0) ≤ max 1 cfac⁻¹ * (a * b) := by
      calc
        (J⁻¹ : ℝ≥0) ≤ cfac⁻¹ * (a * b) := hJinv_le
        _ ≤ max 1 cfac⁻¹ * (a * b) := by
          exact mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ≥0) cfac⁻¹) (by positivity)
    have hJinv_cast : (J : ENNReal)⁻¹ = ((J⁻¹ : ℝ≥0) : ENNReal) := by
      rw [ENNReal.coe_inv hJ.ne']
    have hVle' : volume K ≤ ((J⁻¹ : ℝ≥0) : ENNReal) * (8 * (θ : ENNReal)) := by
      simpa [hJinv_cast] using hVle
    have hVle'' : volume K ≤ ((max 1 cfac⁻¹ * (a * b) : ℝ≥0) : ENNReal) * (8 * (θ : ENNReal)) :=
      hVle'.trans (mul_le_mul' (ENNReal.coe_le_coe.mpr hkey) le_rfl)
    have hWvol : volume W.carrier = 8 * ((a * b : ℝ≥0) : ENNReal) := by
      rw [Prism3D.volume_carrier W, mul_assoc, ENNReal.coe_mul]
      norm_num
      ring
    have hfinalEq : ((max 1 cfac⁻¹ * (a * b) : ℝ≥0) : ENNReal) * (8 * (θ : ENNReal))
        = ((max 1 cfac⁻¹ : ℝ≥0) : ENNReal) * (θ : ENNReal) * volume W.carrier := by
      rw [hWvol]
      exact_mod_cast (by
        ring : (max 1 cfac⁻¹ * (a * b) : ℝ≥0) * (8 * θ) = (max 1 cfac⁻¹) * θ * (8 * (a * b)))
    calc
      volume K ≤ ((max 1 cfac⁻¹ * (a * b) : ℝ≥0) : ENNReal) * (8 * (θ : ENNReal)) := hVle''
      _ = ((max 1 cfac⁻¹ : ℝ≥0) : ENNReal) * (θ : ENNReal) * volume W.carrier := hfinalEq

/-- The **pullback normal**: the vector `m` representing, in `W`'s own frame, the linear functional
that a slab's unit normal `n` induces on the source of a plank normalisation. Explicitly
`m = ∑ᵢ (κ / W.thicknesses i) · ⟪n, g i⟫ • W.basis i`, i.e. `m = Dᵀn` read in the frame `W.basis`,
where `D = diag (κ/a, κ/b, κ)` is the diagonal part of the normalisation.

Its defining property is `Plank.inner_pullbackNormal`: `⟪f x - f W.center, n⟫ = ⟪x - W.center, m⟫`.
So the preimage under `f` of the slab constraint `|⟪y - S.center, n⟫| ≤ θ` is the strip of normal `m`
and half-width `θ / ‖m‖`, which is why bounding `‖m‖` above bounds the strip's width below. -/
def pullbackNormal {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1) (κ : ℝ)
    (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (n : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ n (g i)) • W.basis i

/-- **Defining property of the pullback normal.** For a plank normalisation `f` of `W`, testing the
displacement `f x - f W.center` against `n` is the same as testing `x - W.center` against
`Plank.pullbackNormal W κ g n`. Pure algebra: expand `f` through `IsPlankNormalisation`, pull the
inner product through the finite sum, and use symmetry of the real inner product. -/
theorem inner_pullbackNormal {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : IsPlankNormalisation W f κ g) (n x : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (f x - f W.center) n = inner ℝ (x - W.center) (pullbackNormal W κ g n) := by
  have hfx : f x - f W.center
      = ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - W.center) (W.basis i)) • g i := by
    rw [hnorm x]
    abel
  rw [hfx, pullbackNormal]
  calc
    inner ℝ (∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - W.center) (W.basis i)) • g i) n
        = ∑ i, inner ℝ ((κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - W.center) (W.basis i)) • g i) n := by
      rw [sum_inner]
    _ = ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - W.center) (W.basis i)) * inner ℝ (g i) n := by
      simp_rw [real_inner_smul_left]
    _ = ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - W.center) (W.basis i)) * inner ℝ n (g i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_comm (g i) n]
    _ = inner ℝ (x - W.center) (∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ n (g i)) • W.basis i) := by
      rw [inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_right]
      ring

/-- **The wedge-product estimate of S6G18.** The pullback normal has norm `≲ κ · θ / a`.

`‖m‖ ≤ ∑ᵢ κ · |⟪n, g i⟫| / W.thicknesses i` by the triangle inequality and orthonormality of
`W.basis`, and the three terms are bounded separately, with `W.thicknesses = ![a, b, 1]`:
* `i = 0`: the tangency hypothesis gives `|⟪n, g 0⟫| ≤ C_tang · θ`, so the term is `≤ κ·C_tang·θ/a`;
* `i = 1`: `|⟪n, g 1⟫| ≤ 1`, so the term is `≤ κ/b ≤ κ·θ/a`, using `a/b ≤ θ`;
* `i = 2`: `|⟪n, g 2⟫| ≤ 1`, so the term is `≤ κ ≤ κ·θ/a`, using `a ≤ a/b ≤ θ` (as `b ≤ 1`).

This is the quantitative content of the blueprint's "`‖Dᵀn‖ ≤ C/b`" step — note that in the corrected
normalisation the relevant bound is `≲ κθ/a`, which is what yields a strip of width `≳ a/κ` and hence
the `c_tr · a` conclusion of S6G18 rather than the (impossible) `c_tr · θ · b`. -/
theorem norm_pullbackNormal_le {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    {κ : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1)
    {θ : ℝ≥0} (hθab : a / b ≤ θ) {Ctang : ℝ≥0}
    (htang : |inner ℝ n (g 0)| ≤ (Ctang : ℝ) * (θ : ℝ)) :
    ‖pullbackNormal W κ g n‖ ≤ κ * ((Ctang : ℝ) + 2) * (θ : ℝ) / (a : ℝ) := by
  set_option maxHeartbeats 1000000 in
  -- scalar facts
  have hap : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hbp : (0:ℝ) < (b:ℝ) := by exact_mod_cast (ha.trans_le hab)
  have hb1' : (b:ℝ) ≤ 1 := by exact_mod_cast hb1
  have hθmul : (a:ℝ) ≤ (θ:ℝ) * (b:ℝ) := by
    have h : (a:ℝ) / (b:ℝ) ≤ (θ:ℝ) := by exact_mod_cast hθab
    rwa [div_le_iff₀ hbp] at h
  have hθp : (0:ℝ) ≤ (θ:ℝ) := (θ : ℝ≥0).coe_nonneg
  -- 1/b ≤ θ/a  and  1 ≤ θ/a
  have key1 : ((b:ℝ))⁻¹ ≤ (θ:ℝ) / (a:ℝ) := by
    rw [inv_eq_one_div]
    refine (div_le_div_iff₀ hbp hap).mpr ?_
    calc
      (1:ℝ) * (a:ℝ) = (a:ℝ) := by ring
      _ ≤ (θ:ℝ) * (b:ℝ) := hθmul
  have key2 : (1:ℝ) ≤ (θ:ℝ) / (a:ℝ) := by
    rw [le_div_iff₀ hap]
    calc
      (1:ℝ) * (a:ℝ) = (a:ℝ) := by ring
      _ ≤ (θ:ℝ) * (b:ℝ) := hθmul
      _ ≤ (θ:ℝ) * 1 := mul_le_mul_of_nonneg_left hb1' (by positivity : 0 ≤ (θ:ℝ))
      _ = (θ:ℝ) := mul_one _
  -- for each i, |inner ℝ n (g i)| ≤ 1
  have hgi : ∀ i, |inner ℝ n (g i)| ≤ 1 := by
    intro i
    calc |inner ℝ n (g i)| ≤ ‖n‖ * ‖g i‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [hn, g.norm_eq_one i, mul_one]
  -- STEP 1 — triangle inequality plus orthonormality of W.basis
  rw [pullbackNormal]
  have hstep : ‖∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ n (g i)) • W.basis i‖
      ≤ ∑ i, |κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ n (g i)| := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro i _
    rw [norm_smul, Real.norm_eq_abs, W.basis.norm_eq_one i, mul_one]
  refine hstep.trans ?_
  -- STEP 2 — expand the three terms and evaluate the thicknesses
  have ht0 : ((W.thicknesses 0 : ℝ)) = (a:ℝ) := by
    rw [W.thicknesses_eq]
    simp
  have ht1 : ((W.thicknesses 1 : ℝ)) = (b:ℝ) := by
    rw [W.thicknesses_eq]
    simp
  have ht2 : ((W.thicknesses 2 : ℝ)) = (1:ℝ) := by
    rw [W.thicknesses_eq]
    simp
  rw [Fin.sum_univ_three, ht0, ht1, ht2]
  -- STEP 3 — bound the three absolute values
  have hb0 : |κ * ((a:ℝ))⁻¹ * inner ℝ n (g 0)| ≤ κ * ((a:ℝ))⁻¹ * ((Ctang : ℝ) * (θ : ℝ)) := by
    calc
      |κ * ((a:ℝ))⁻¹ * inner ℝ n (g 0)| = κ * ((a:ℝ))⁻¹ * |inner ℝ n (g 0)| := by
        rw [abs_mul, abs_mul, abs_of_pos hκ, abs_of_pos (inv_pos.mpr hap)]
      _ ≤ κ * ((a:ℝ))⁻¹ * ((Ctang : ℝ) * (θ : ℝ)) := by
        gcongr
  have hb1'val : |κ * ((b:ℝ))⁻¹ * inner ℝ n (g 1)| ≤ κ * ((b:ℝ))⁻¹ := by
    calc
      |κ * ((b:ℝ))⁻¹ * inner ℝ n (g 1)| = κ * ((b:ℝ))⁻¹ * |inner ℝ n (g 1)| := by
        rw [abs_mul, abs_mul, abs_of_pos hκ, abs_of_pos (inv_pos.mpr hbp)]
      _ ≤ κ * ((b:ℝ))⁻¹ * 1 := by
        gcongr; exact hgi 1
      _ = κ * ((b:ℝ))⁻¹ := by ring
  have hb2 : |κ * ((1:ℝ))⁻¹ * inner ℝ n (g 2)| ≤ κ := by
    calc
      |κ * ((1:ℝ))⁻¹ * inner ℝ n (g 2)| = κ * |inner ℝ n (g 2)| := by
        simp [abs_mul, abs_of_pos hκ, inv_one]
      _ ≤ κ * 1 := by
        gcongr; exact hgi 2
      _ = κ := by ring
  -- STEP 4 — finish
  have c1 : κ * ((b:ℝ))⁻¹ ≤ κ * ((θ:ℝ) / (a:ℝ)) :=
    mul_le_mul_of_nonneg_left key1 hκ.le
  have c2 : κ ≤ κ * ((θ:ℝ) / (a:ℝ)) := by
    calc κ = κ * 1 := (mul_one κ).symm
      _ ≤ κ * ((θ:ℝ) / (a:ℝ)) := mul_le_mul_of_nonneg_left key2 hκ.le
  have hrhs : κ * ((a:ℝ))⁻¹ * ((Ctang : ℝ) * (θ : ℝ)) + κ * ((θ:ℝ)/(a:ℝ)) + κ * ((θ:ℝ)/(a:ℝ))
      = κ * ((Ctang : ℝ) + 2) * (θ : ℝ) / (a : ℝ) := by
    field_simp
    ring
  calc
    |κ * ((a:ℝ))⁻¹ * inner ℝ n (g 0)| + |κ * ((b:ℝ))⁻¹ * inner ℝ n (g 1)| + |κ * ((1:ℝ))⁻¹ * inner ℝ n (g 2)|
        ≤ κ * ((a:ℝ))⁻¹ * ((Ctang : ℝ) * (θ : ℝ)) + κ * ((b:ℝ))⁻¹ + κ := by
      nlinarith
    _ ≤ κ * ((a:ℝ))⁻¹ * ((Ctang : ℝ) * (θ : ℝ)) + κ * ((θ:ℝ)/(a:ℝ)) + κ * ((θ:ℝ)/(a:ℝ)) := by
      nlinarith
    _ = κ * ((Ctang : ℝ) + 2) * (θ : ℝ) / (a : ℝ) := hrhs

/-- Crude bound on the pullback normal, valid for *any* unit direction (no tangency needed):
`‖m‖ ≤ 3κ/a`, since every thickness of an `a × b × 1` plank is at least `a`.

The sharp bound `Plank.norm_pullbackNormal_le` applies only to the slab's thin direction `S.basis 0`,
where tangency is available. For the slab's two *long* directions this crude bound is what controls
the corresponding coordinates, and it suffices because those thicknesses equal `1` rather than `θ`. -/
theorem norm_pullbackNormal_le_three {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (W : Plank a b hab hb1) {κ : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1) :
    ‖pullbackNormal W κ g n‖ ≤ 3 * κ / (a : ℝ) := by
  set_option maxHeartbeats 1000000 in
  have hap : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbp : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (ha.trans_le hab)
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hb1' : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  have ha1' : (a : ℝ) ≤ 1 := le_trans hab' hb1'
  -- for each i, |inner ℝ n (g i)| ≤ 1
  have hgi : ∀ i, |inner ℝ n (g i)| ≤ 1 := by
    intro i
    calc |inner ℝ n (g i)| ≤ ‖n‖ * ‖g i‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [hn, g.norm_eq_one i, mul_one]
  -- triangle inequality plus orthonormality of W.basis
  rw [pullbackNormal]
  have hstep : ‖∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ n (g i)) • W.basis i‖
      ≤ ∑ i, |κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ n (g i)| := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro i _
    rw [norm_smul, Real.norm_eq_abs, W.basis.norm_eq_one i, mul_one]
  refine hstep.trans ?_
  -- expand the three terms and evaluate the thicknesses
  have ht0 : ((W.thicknesses 0 : ℝ)) = (a : ℝ) := by
    rw [W.thicknesses_eq]
    simp
  have ht1 : ((W.thicknesses 1 : ℝ)) = (b : ℝ) := by
    rw [W.thicknesses_eq]
    simp
  have ht2 : ((W.thicknesses 2 : ℝ)) = (1 : ℝ) := by
    rw [W.thicknesses_eq]
    simp
  rw [Fin.sum_univ_three, ht0, ht1, ht2]
  -- each term ≤ κ * a⁻¹, so sum ≤ 3 * κ * a⁻¹ = 3 * κ / a
  have h_inv1_le_inva : ((1 : ℝ))⁻¹ ≤ ((a : ℝ))⁻¹ := by
    simpa [inv_one] using (inv_le_inv₀ (by norm_num : 0 < (1 : ℝ)) hap).mpr ha1'
  have h_invb_le_inva : ((b : ℝ))⁻¹ ≤ ((a : ℝ))⁻¹ :=
    (inv_le_inv₀ hbp hap).mpr hab'
  have hκ_nonneg : 0 ≤ κ := hκ.le
  have hb0 : |κ * ((a : ℝ))⁻¹ * inner ℝ n (g 0)| ≤ κ * ((a : ℝ))⁻¹ := by
    calc
      |κ * ((a : ℝ))⁻¹ * inner ℝ n (g 0)| = κ * ((a : ℝ))⁻¹ * |inner ℝ n (g 0)| := by
        rw [abs_mul, abs_mul, abs_of_pos hκ, abs_of_pos (inv_pos.mpr hap)]
      _ ≤ κ * ((a : ℝ))⁻¹ * 1 := by
        gcongr; exact hgi 0
      _ = κ * ((a : ℝ))⁻¹ := by ring
  have hb1_val : |κ * ((b : ℝ))⁻¹ * inner ℝ n (g 1)| ≤ κ * ((a : ℝ))⁻¹ := by
    calc
      |κ * ((b : ℝ))⁻¹ * inner ℝ n (g 1)| = κ * ((b : ℝ))⁻¹ * |inner ℝ n (g 1)| := by
        rw [abs_mul, abs_mul, abs_of_pos hκ, abs_of_pos (inv_pos.mpr hbp)]
      _ ≤ κ * ((b : ℝ))⁻¹ * 1 := by
        gcongr; exact hgi 1
      _ = κ * ((b : ℝ))⁻¹ := by ring
      _ ≤ κ * ((a : ℝ))⁻¹ := mul_le_mul_of_nonneg_left h_invb_le_inva hκ_nonneg
  have hb2 : |κ * ((1 : ℝ))⁻¹ * inner ℝ n (g 2)| ≤ κ * ((a : ℝ))⁻¹ := by
    calc
      |κ * ((1 : ℝ))⁻¹ * inner ℝ n (g 2)| = κ * |inner ℝ n (g 2)| := by
        simp [abs_mul, abs_of_pos hκ, inv_one, mul_assoc]
      _ ≤ κ * 1 := by
        gcongr; exact hgi 2
      _ = κ := by ring
      _ ≤ κ * ((a : ℝ))⁻¹ := by
        have : 1 ≤ (a : ℝ)⁻¹ := by
          simpa [inv_one] using (inv_le_inv₀ (by norm_num : 0 < (1 : ℝ)) hap).mpr ha1'
        nlinarith
  calc
    |κ * ((a : ℝ))⁻¹ * inner ℝ n (g 0)| + |κ * ((b : ℝ))⁻¹ * inner ℝ n (g 1)|
        + |κ * ((1 : ℝ))⁻¹ * inner ℝ n (g 2)|
      ≤ (κ * ((a : ℝ))⁻¹) + (κ * ((a : ℝ))⁻¹) + (κ * ((a : ℝ))⁻¹) := by
      nlinarith
    _ = 3 * κ * ((a : ℝ))⁻¹ := by ring
    _ = 3 * κ / (a : ℝ) := by ring

/-- The displacement form of `Plank.inner_pullbackNormal`: testing `f x - f y` against `n` is the
same as testing `x - y` against the pullback normal. Immediate by subtracting the identity at `x`
and at `y`. -/
theorem inner_pullbackNormal_sub {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : IsPlankNormalisation W f κ g) (n x y : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (f x - f y) n = inner ℝ (x - y) (pullbackNormal W κ g n) := by
  have hx := inner_pullbackNormal W hnorm n x
  have hy := inner_pullbackNormal W hnorm n y
  have hL : f x - f y = (f x - f W.center) - (f y - f W.center) := by abel
  have hR : x - y = (x - W.center) - (y - W.center) := by abel
  calc
    inner ℝ (f x - f y) n = inner ℝ ((f x - f W.center) - (f y - f W.center)) n := by rw [hL]
    _ = inner ℝ (f x - f W.center) n - inner ℝ (f y - f W.center) n := by rw [inner_sub_left]
    _ = inner ℝ (x - W.center) (pullbackNormal W κ g n) - inner ℝ (y - W.center) (pullbackNormal W κ g n) := by rw [hx, hy]
    _ = inner ℝ ((x - W.center) - (y - W.center)) (pullbackNormal W κ g n) := by rw [← inner_sub_left]
    _ = inner ℝ (x - y) (pullbackNormal W κ g n) := by rw [hR]

/-- **Strip containment.** If `f x₀` sits in the *middle half* of the slab `S` in every coordinate,
and the radius `r` is small enough that moving by `r` changes each coordinate of the image by at most
half the corresponding thickness, then the whole ball `closedBall x₀ r` is pulled back into `S`.

This is the quantitative form of "the pullback of `S` is a strip of half-width `θ / ‖m‖`": by
`Plank.inner_pullbackNormal_sub` the `i`-th coordinate of `f x - f x₀` is `⟪x - x₀, mᵢ⟫`, which
Cauchy--Schwarz bounds by `r · ‖mᵢ‖`. Together with the middle-half hypothesis this keeps every
coordinate of `f x - S.center` within `S.thicknesses i`. -/
theorem closedBall_subset_preimage_slab {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : IsPlankNormalisation W f κ g)
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    (x₀ : EuclideanSpace ℝ (Fin 3)) {r : ℝ} (hr : 0 ≤ r)
    (hmid : ∀ i, |inner ℝ (f x₀ - S.center) (S.basis i)| ≤ (S.thicknesses i : ℝ) / 2)
    (hrad : ∀ i, r * ‖pullbackNormal W κ g (S.basis i)‖ ≤ (S.thicknesses i : ℝ) / 2) :
    Metric.closedBall x₀ r ⊆ f ⁻¹' S.carrier := by
  set_option maxHeartbeats 1000000 in
  intro x hx
  have hdist : ‖x - x₀‖ ≤ r := by
    have hx' : dist x x₀ ≤ r := Metric.mem_closedBall.mp hx
    rw [dist_eq_norm] at hx'
    exact hx'
  have hmem : f x ∈ S.carrier := by
    rw [S.mem_carrier_iff]
    intro i
    have h_inner : S.basis.repr (f x -ᵥ S.center) i = inner ℝ (f x -ᵥ S.center) (S.basis i) := by
      rw [S.basis.repr_apply_apply, real_inner_comm]
    rw [h_inner, vsub_eq_sub]
    have hsplit : inner ℝ (f x - S.center) (S.basis i) =
        inner ℝ (f x - f x₀) (S.basis i) + inner ℝ (f x₀ - S.center) (S.basis i) := by
      rw [show f x - S.center = (f x - f x₀) + (f x₀ - S.center) by abel, inner_add_left]
    rw [hsplit]
    have hdisp : |inner ℝ (f x - f x₀) (S.basis i)| ≤ r * ‖pullbackNormal W κ g (S.basis i)‖ := by
      rw [W.inner_pullbackNormal_sub hnorm (S.basis i) x x₀]
      calc
        |inner ℝ (x - x₀) (pullbackNormal W κ g (S.basis i))|
            ≤ ‖x - x₀‖ * ‖pullbackNormal W κ g (S.basis i)‖ := abs_real_inner_le_norm _ _
        _ ≤ r * ‖pullbackNormal W κ g (S.basis i)‖ := by
          exact mul_le_mul_of_nonneg_right hdist (norm_nonneg _)
    have hcenter : |inner ℝ (f x₀ - S.center) (S.basis i)| ≤ (S.thicknesses i : ℝ) / 2 := hmid i
    have hrad' : r * ‖pullbackNormal W κ g (S.basis i)‖ ≤ (S.thicknesses i : ℝ) / 2 := hrad i
    have h_abs_add : |inner ℝ (f x - f x₀) (S.basis i) + inner ℝ (f x₀ - S.center) (S.basis i)|
        ≤ |inner ℝ (f x - f x₀) (S.basis i)| + |inner ℝ (f x₀ - S.center) (S.basis i)| :=
      abs_add_le _ _
    calc
      |inner ℝ (f x - f x₀) (S.basis i) + inner ℝ (f x₀ - S.center) (S.basis i)|
          ≤ |inner ℝ (f x - f x₀) (S.basis i)| + |inner ℝ (f x₀ - S.center) (S.basis i)| := h_abs_add
      _ ≤ r * ‖pullbackNormal W κ g (S.basis i)‖ + (S.thicknesses i : ℝ) / 2 := by
        nlinarith
      _ ≤ (S.thicknesses i : ℝ) / 2 + (S.thicknesses i : ℝ) / 2 := by
        nlinarith
      _ = (S.thicknesses i : ℝ) := by ring
  exact hmem

/-- **Strip containment, slack form.** The general version of
`Plank.closedBall_subset_preimage_slab`: it is enough that in each coordinate the distance of
`f x₀` from `S.center` plus the room `r · ‖mᵢ‖` needed by the ball fits inside the thickness. The
middle-half version is the special case where both summands are at most half the thickness. -/
theorem closedBall_subset_preimage_slab' {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : IsPlankNormalisation W f κ g)
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    (x₀ : EuclideanSpace ℝ (Fin 3)) {r : ℝ} (hr : 0 ≤ r)
    (hslack : ∀ i, |inner ℝ (f x₀ - S.center) (S.basis i)|
        + r * ‖pullbackNormal W κ g (S.basis i)‖ ≤ (S.thicknesses i : ℝ)) :
    Metric.closedBall x₀ r ⊆ f ⁻¹' S.carrier := by
  set_option maxHeartbeats 1000000 in
  intro x hx
  have hdist : ‖x - x₀‖ ≤ r := by
    have hx' : dist x x₀ ≤ r := Metric.mem_closedBall.mp hx
    rw [dist_eq_norm] at hx'
    exact hx'
  have hmem : f x ∈ S.carrier := by
    rw [S.mem_carrier_iff]
    intro i
    have h_inner : S.basis.repr (f x -ᵥ S.center) i = inner ℝ (f x -ᵥ S.center) (S.basis i) := by
      rw [S.basis.repr_apply_apply, real_inner_comm]
    rw [h_inner, vsub_eq_sub]
    have hsplit : inner ℝ (f x - S.center) (S.basis i) =
        inner ℝ (f x - f x₀) (S.basis i) + inner ℝ (f x₀ - S.center) (S.basis i) := by
      rw [show f x - S.center = (f x - f x₀) + (f x₀ - S.center) by abel, inner_add_left]
    rw [hsplit]
    have hdisp : |inner ℝ (f x - f x₀) (S.basis i)| ≤ r * ‖pullbackNormal W κ g (S.basis i)‖ := by
      rw [W.inner_pullbackNormal_sub hnorm (S.basis i) x x₀]
      calc
        |inner ℝ (x - x₀) (pullbackNormal W κ g (S.basis i))|
            ≤ ‖x - x₀‖ * ‖pullbackNormal W κ g (S.basis i)‖ := abs_real_inner_le_norm _ _
        _ ≤ r * ‖pullbackNormal W κ g (S.basis i)‖ :=
            mul_le_mul_of_nonneg_right hdist (norm_nonneg _)
    calc
      |inner ℝ (f x - f x₀) (S.basis i) + inner ℝ (f x₀ - S.center) (S.basis i)|
          ≤ |inner ℝ (f x - f x₀) (S.basis i)| + |inner ℝ (f x₀ - S.center) (S.basis i)| :=
            abs_add_le _ _
      _ ≤ r * ‖pullbackNormal W κ g (S.basis i)‖ + |inner ℝ (f x₀ - S.center) (S.basis i)| := by
        nlinarith
      _ ≤ (S.thicknesses i : ℝ) := by
        calc
          r * ‖pullbackNormal W κ g (S.basis i)‖ + |inner ℝ (f x₀ - S.center) (S.basis i)|
              = |inner ℝ (f x₀ - S.center) (S.basis i)| + r * ‖pullbackNormal W κ g (S.basis i)‖ := by ring
          _ ≤ (S.thicknesses i : ℝ) := hslack i
  exact hmem

/-- A `δ`-tube contains the closed `δ`-ball about its centre, since the centre lies on its axis and
the carrier is the union of the `δ`-balls about the points of that axis. Hence any set containing the
tube contains that ball. -/
theorem closedBall_center_subset_of_tube {δ : ℝ≥0}
    (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hT : T.carrier ⊆ K) :
    Metric.closedBall T.center (δ : ℝ) ⊆ K := by
  refine subset_trans ?_ hT
  rw [T.carrier_eq]
  have hmem : T.center ∈ segment ℝ T.x T.y := midpoint_mem_segment T.x T.y
  exact Set.subset_biUnion_of_mem (u := fun z : EuclideanSpace ℝ (Fin 3) => Metric.closedBall z (δ : ℝ)) hmem

/-- **The positional hypothesis, and what it actually yields.** If the pullback
`K_{W,S} = W ∩ f⁻¹(S)` contains a `δ`-tube of `W` — the formal content of the blueprint's "the long
directions of the tangent plank cross the interior of `W`" — then it contains a ball of radius `δ`,
namely the one about the tube's centre.

This is exactly the positional information that is available at the call site: in
`Plank.katzTaoTransverseFactorBound` the hypotheses `hcarrier` and `hlink` give
`(T i).carrier ⊆ W.carrier` and `(T i).carrier ⊆ f ⁻¹' S.carrier` for any `i` in the slab subfamily.

**The radius is `δ`, not `a`.** No hypothesis of this shape can give a ball of radius `≈ a`: see the
correction on `Plank.pullbackNormalisedSlabMinWidthOfTube` below. -/
theorem pullbackSlabInscribedBallOfTube {a b δ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hTW : T.carrier ⊆ W.carrier) (hTS : T.carrier ⊆ f ⁻¹' S.carrier) :
    ∃ x₀ : EuclideanSpace ℝ (Fin 3),
      Metric.closedBall x₀ (δ : ℝ) ⊆ W.carrier ∩ f ⁻¹' S.carrier :=
  ⟨T.center, closedBall_center_subset_of_tube T (Set.subset_inter hTW hTS)⟩

/-- **Transverse lower bound for the pullback width** (`lem:geometryPullbackSlabTransversality`,
S6G18), in the form the positional hypothesis actually supports: the least Euclidean width of
`K_{W,S} = W ∩ f⁻¹(S)` is at least `δ`, where `δ` is the width of a tube of `W` contained in the
pullback. **Proved** from `Plank.pullbackSlabInscribedBallOfTube` via
`Metric.le_ethickness_closedBall`.

**Correction to the blueprint, part 1.** The blueprint states `least width ≥ c_tr · θ · b`. That is
false: `K_{W,S} ⊆ W`, and the least width of an `a × b × 1` plank is *exactly* `a`
(`Prism3D.a_le_ethickness_scale` with `Prism3D.ethickness_scale_le_a`), so a subset can never have
least width above `a`, whereas `c_tr · θ · b` exceeds `a` as soon as `θ ≫ a/b`.

**Correction to the blueprint, part 2.** The weaker form `least width ≥ c_tr · a` — which the
blueprint also records, and which the volume half of S6G19 was written to consume — is *also false*,
even with the tangency bound and with the positional hypothesis that the pullback contains a
`δ`-tube. Counterexample: normalise so `f W.center = 0`, so `f '' W.carrier` is the cube `Q` of
half-side `κ`. Take `S.basis 0 = g 1` (tangency holds, `⟪S.basis 0, g 0⟫ = 0`), `S.basis 1 = g 0`,
`S.basis 2 = g 2`, and `S.center = (1 + κ - ε) • g 0`. The `i = 1` constraint of `S` has thickness
`1`, so inside `Q` it forces the `g 0`-coordinate into `[κ - ε, κ]`: the pullback is a slice of
`e₀`-thickness `ε · a / κ`, whose least width is `< a` as soon as `ε < κ`. Taking `ε ≈ 2δκ/a` leaves
just enough room for a `δ`-tube (whose axis may run along `e₂`), so the positional hypothesis holds
while the conclusion `≥ c_tr · a` fails by the factor `a/δ`.

So `δ` is the honest bound, and the least-width route to the volume half of S6G19 cannot work, since
there the thickening radius is `C_rad · ρ` with `δ ≤ ρ ≤ a`. The fix is to bypass least width
entirely: `N_r(K_{W,S})` is contained in the pullback of the slab `S` *dilated in its thin direction*
by the factor `1 + r‖m₀‖/θ`, and by `Plank.norm_pullbackNormal_le` that factor is at most
`1 + C_rad · κ(C_tang + 2)` — an absolute constant. Applying S6G17
(`Plank.volumePullbackNormalisedSlab`) to the dilated slab then bounds `|K⁺_{W,S}|` by
`const · C_pull · θ · |W|` directly. -/
theorem pullbackNormalisedSlabMinWidthOfTube {a b δ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hTW : T.carrier ⊆ W.carrier) (hTS : T.carrier ⊆ f ⁻¹' S.carrier) :
    (δ : ENNReal) ≤ Metric.ethickness.scale ℝ (W.carrier ∩ f ⁻¹' S.carrier) := by
  obtain ⟨x₀, hx₀⟩ := pullbackSlabInscribedBallOfTube W S T hTW hTS
  rw [Metric.ethickness.le_scale_iff (s := W.carrier ∩ f ⁻¹' S.carrier) (δ := δ)]
  intro n
  refine le_trans ?_ (Metric.ethickness_monotone hx₀ n.val)
  exact le_ethickness_closedBall (V := EuclideanSpace ℝ (Fin 3))
    (E := EuclideanSpace ℝ (Fin 3)) (x := x₀) δ n.isLt

/-- **A coarse-tube compatible outer body: the containment half of S6G19**
(`lem:geometryCoarseTubeContainer`).

If a fine tube `T i ⊆ K_{W,S}` is contained in a coarse `ρ`-tube `R (assign i) ⊆ W`, then already
`R (assign i) ⊆ K⁺_{W,S} = W ∩ N_{C_rad·ρ}(K_{W,S})`. This is the crux of the argument: fine-tube
containment in the *raw* pullback does **not** imply containment of the supporting coarse tube, so
the pullback has to be thickened by `≈ ρ`. The radius constant is `C_rad = 4`, coming from the
Hausdorff-distance bound `R (assign i) ⊆ N_{4·ρ}(T i)` for a fine tube inside its coarse parent.

The containment hypothesis `(T i).carrier ⊆ (R (assign i)).carrier` is essential: without it the
coarse tube may sit anywhere in `W`. Inside an `a × 1 × 1` plank `W`, take `S` a sliver whose
thin normal is `g 0`; then `K_{W,S}` is a slice of thickness `≈ a²/κ` hugging one short face of
`W`, while a unit-length `ρ`-tube along `W.basis 2` at the opposite face satisfies
`R (assign i) ⊆ W` yet lies `≈ 2a` away, so for `ρ` small enough it is outside
`N_{C·ρ}(K_{W,S})` for any fixed `C`.

**Note on the split.** The blueprint's S6G19 states this together with the volume bound
`|K⁺_{W,S}| ≤ C_ctr·θ·|W|`, using the *same* constant `C_ctr` for the thickening radius and for the
volume. That identification is not available formally: the volume of the thickening inflates by a
factor growing like `(C_rad / c_tr)^3`, so a single constant serving both roles would have to satisfy
`C ≥ const · C^3 / c_tr^3`, which fails for small `c_tr`. The two halves are therefore separated,
with the radius constant `C_rad` here and the volume constant produced by
`Plank.volumeCthickeningPullbackSlab` (which is proved). -/
theorem coarseTubeContainerOfPullbackSlab :
    ∃ Crad : ℝ≥0, 1 ≤ Crad ∧
      ∀ {a b δ ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (ha : 0 < a) (hδ0 : 0 < δ) (hρa : ρ ≤ a)
        (W : Plank a b hab hb1)
        (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (J : ℝ≥0),
        0 < J →
        (∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ENNReal) * volume E) →
        f '' W.carrier ⊆ Metric.closedBall 0 1 →
        ∀ (θ : ℝ≥0) (hθ1 : θ ≤ 1) (S : Slab θ hθ1), a / b ≤ θ →
          ∀ {ι κ : Type*} (qW : Finset ι)
            (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
            (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (assign : ι → κ),
            ∀ i ∈ qW, (T i).carrier ⊆ W.carrier ∩ f ⁻¹' S.carrier →
              (T i).carrier ⊆ (R (assign i)).carrier →
              (R (assign i)).carrier ⊆ W.carrier →
              (R (assign i)).carrier ⊆ W.carrier ∩ Metric.cthickening ((Crad * ρ : ℝ≥0) : ℝ)
                (W.carrier ∩ f ⁻¹' S.carrier) := by
  refine ⟨4, by norm_num, ?_⟩
  intro a b δ ρ hab hb1 ha hδ0 hρa W f J hJ hvolf himg θ hθ1 S hθge ι κ qW T R assign
  intro i hiq hTi_sub hTi_parent hRiW
  let Tf : Tube δ (EuclideanSpace ℝ (Fin 3)) := (T i).toTube
  let Rc : Tube ρ (EuclideanSpace ℝ (Fin 3)) := R (assign i)
  -- 1. every point of the fine segment is within `ρ` of the coarse segment,
  --    because it lies in `T i`'s carrier, hence in `R (assign i)`'s carrier.
  have hclose : ∀ p ∈ segment ℝ Tf.x Tf.y,
      ∃ q ∈ segment ℝ Rc.x Rc.y, dist p q ≤ (ρ : ℝ) := by
    intro p hp
    have hpTf : p ∈ (T i).carrier := by
      change p ∈ Tf.carrier
      rw [Tf.carrier_eq]
      exact Set.mem_iUnion₂.mpr ⟨p, hp, Metric.mem_closedBall_self (NNReal.coe_nonneg δ)⟩
    have hpR : p ∈ (R (assign i)).carrier := hTi_parent hpTf
    rw [Rc.carrier_eq] at hpR
    obtain ⟨q, hq, hpq⟩ := Set.mem_iUnion₂.mp hpR
    exact ⟨q, hq, Metric.mem_closedBall.mp hpq⟩
  -- 2. the Hausdorff-symmetry lemma transfers the bound to the coarse segment.
  have hsymm : ∀ z ∈ segment ℝ Rc.x Rc.y,
      ∃ w ∈ segment ℝ Tf.x Tf.y, dist z w ≤ 3 * (ρ : ℝ) :=
    Tube.symm_hausdorff_segment
      (a := Tf.x) (b := Tf.y) (c := Rc.x) (d := Rc.y)
      (hab := Tf.norm_direction) (hcd := Rc.norm_direction)
      (hρ := NNReal.coe_nonneg ρ) (hclose := hclose)
  -- 3. every point of the coarse carrier lies within `4ρ` of `W ∩ f⁻¹' S.carrier`.
  have hcthk : (R (assign i)).carrier ⊆
      Metric.cthickening ((4 * ρ : ℝ≥0) : ℝ) (W.carrier ∩ f ⁻¹' S.carrier) := by
    intro y hy
    rw [Rc.carrier_eq] at hy
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp hy
    obtain ⟨w, hw, hzw⟩ := hsymm z hz
    refine Metric.mem_cthickening_of_dist_le y w ((4 * ρ : ℝ≥0) : ℝ) _ ?_ ?_
    · have hwTf : w ∈ (T i).carrier := by
        change w ∈ Tf.carrier
        rw [Tf.carrier_eq]
        exact Set.mem_iUnion₂.mpr ⟨w, hw, Metric.mem_closedBall_self (NNReal.coe_nonneg δ)⟩
      exact hTi_sub hwTf
    · calc
        dist y w ≤ dist y z + dist z w := dist_triangle y z w
        _ ≤ (ρ : ℝ) + 3 * (ρ : ℝ) := add_le_add (Metric.mem_closedBall.mp hyz) hzw
        _ = (4 : ℝ) * (ρ : ℝ) := by ring
        _ = ((4 * ρ : ℝ≥0) : ℝ) := by norm_num [NNReal.coe_mul]
  exact Set.subset_inter hRiW hcthk

end Plank

end
