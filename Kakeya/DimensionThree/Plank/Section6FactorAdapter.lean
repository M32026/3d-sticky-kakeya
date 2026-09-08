/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Section6
public import Kakeya.DimensionThree.Plank

/-!
# The Section-6-facing adapter for GWZ Proposition 5.1

This file is the interface layer between the *generic* statement of GWZ Proposition 5.1
(`ShadedBody.factoringAndMultPropCore` in `Kakeya/Factoring/Multiplicity.lean`, whose hypotheses
are the three predicates of `Kakeya/FactorFamily/Predicates.lean`) and the *concrete* Section-6
consumers for Proposition 6.6(A) and `Kakeya.factoringAndMultPropGlobal`.

## What the check found

Reading GWZ Definition 4.2 ("`𝕎` factors `𝕍`") against the two existing Section-6 factorisation
data `Kakeya.ComparableBodyFactorization` and `Kakeya.GlobalComparableBodyFactorization`, the clauses that
are genuinely part of the definition are

1. **inner containment** — every fine body lies in the body of its cell;
2. **fibre Frostman in the outer body** — each fibre `𝕍_W` is `C`-Frostman *inside* `W`;
3. **outer Katz--Tao** — the outer family has bounded density;
4. **comparable outer dimensions** — every outer body has dimensions comparable to `a × b × 1`;
5. **comparable fibre mass** — the fibre densities `Δ(𝕍_W, W)` agree across `W` up to a constant.

Of these, `ComparableBodyFactorization` carries only (1) and (3) (plus the one-sided transverse
bound `wide`), and `GlobalComparableBodyFactorization` carries (1), (3) and the upper half of (4).  Neither
carries (2) or (5), and neither carries the representative-shape data needed to hand an
`a × b × 1` plank back to Section 6.  Those are exactly the gaps this file fills, in **new**
wrapper structures rather than by mutating the two widely used core structures.

Clause (2) is what generic Proposition 5.1 consumes as
`ShadedBody.FactorFamily.HasFrostmanFibers`; clause (5) is what GWZ Remark 3.3(A) consumes to
transfer Frostman control *upwards* to the selected outer family
(`ConvexSpaceBody.isFrostmanIn_parents_of_uniform_fibres` below); clause (4) is what repairs the
`cthickening` mismatch described next.

## The `cthickening`ed output, and how it is resolved

Generic Proposition 5.1 returns a fully shaded factor family `G` whose outer convex carrier is

`(F.outerBody j).cthickening (F.outerBody j).scale`,

not the original body, because the `shade_subset` field of a `ShadedBody` genuinely fails for the
original carrier: the induced shading of GWZ Definition 5.7 is
`N_{2r}(U(𝒱, Y)) ∩ N_r(W)`, which sticks out of `W`.  Section 6 wants an exact `a × b × 1`
`Kakeya.ShadedPlank`.

The resolution here does **not** touch generic Proposition 5.1 and does **not** use the false
lemma `cthickening r (Plank a b) ⊆ Plank (a + r) (b + r)` (metric thickening also enlarges the
long axis).  Instead:

* the adapter *carries* the representative plank and the containment
  `(body x).cthickening ((body x).scale) ≤ repr x` as **data** (field
  `Kakeya.Section6FactorData.cthickening_le_repr`).  This is satisfiable at every scale — it is
  the "approximately the same dimensions" clause of GWZ Definition 4.2, read with enough room for
  the `r`-collar, and it never asks a plank to equal a body;
* the Section-6 outer view is then obtained by `ShadedBody.reshape`: keep the shade produced by
  Proposition 5.1 verbatim and re-present it on the representative plank.  Because
  `ShadedBody.multiplicity`, `ShadedBody.pointwiseMultiplicity` and
  `ShadedBody.HasCConstantMultiplicity` depend on the *shades only*, all three transfer with **no
  loss at all**, and `ShadedBody.fullness` — the only quantity that sees the carrier — degrades by
  exactly the dimension-comparison constant `Cdim` of clause (4)
  (`ShadedBody.fullness'_le_mul_fullness'_reshape`).

So the clipping theorem the plan asked about is *true*, provided one clips the **carrier** upward
to the representative plank rather than clipping the **shade** downward into it.  Clipping the
shade is what fails: the shade may live almost entirely in the `r`-collar `N_r(W) \ W`, and no
constant-mass bound survives.  That obstruction is recorded in
`Kakeya.Section6FactorData.shade_not_in_body`'s docstring.

## Part B and GWZ Remark 5.3

For Proposition 6.6(B) the *fine* fibres need not be Frostman; what is Frostman is the coarse
(thickened) fibre.  `Kakeya.Section6CoarseFactorData` therefore packages a `Section6FactorData`
for the **coarse** family together with the fine-to-coarse projection, so that the family handed
to generic Proposition 5.1 is the coarse one — which is literally what GWZ Remark 5.3 licenses.
The fine-family multiplicity split is *not* claimed here; it is the Remark-5.3 upgrade of
Proposition 5.1 and is isolated as the explicit hypothesis
`Kakeya.Section6CoarseFactorData.Remark53Split`.
-/

@[expose] public section

open MeasureTheory Metric Convexity
open scoped NNReal

noncomputable section

/-! ## Reshaping a shaded body onto a larger convex carrier -/

namespace ShadedBody

section Reshape

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [ConvexSpace ℝ E]

/-- **Re-present a shaded body on a different convex carrier.**

The shade is kept verbatim; only the convex body carrying it changes.  This is the operation that
turns the `cthickening`ed outer body returned by GWZ Proposition 5.1 into a body Section 6 can
consume, and it is *lossless* for every quantity that depends on the shades alone. -/
def reshape (S : ShadedBody E) (K : ConvexSpaceBody E) (h : S.shade ⊆ K.carrier) :
    ShadedBody E where
  toConvexSpaceBody := K
  shade := S.shade
  measurableSet_shade := S.measurableSet_shade
  shade_subset := h

@[simp]
theorem shade_reshape (S : ShadedBody E) (K : ConvexSpaceBody E) (h : S.shade ⊆ K.carrier) :
    (S.reshape K h).shade = S.shade := rfl

@[simp]
theorem toConvexSpaceBody_reshape (S : ShadedBody E) (K : ConvexSpaceBody E)
    (h : S.shade ⊆ K.carrier) : (S.reshape K h).toConvexSpaceBody = K := rfl

end Reshape

section ReshapeFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **Multiplicity is blind to the carrier.**  Two shaded families with the same index set and
the same shades have the same multiplicity, whatever their carriers. -/
theorem multiplicity_congr_shade (s : Finset ι) (V V' : ι → ShadedBody E)
    (h : ∀ i ∈ s, (V i).shade = (V' i).shade) :
    multiplicity s V = multiplicity s V' := by
  have hU : (⋃ i ∈ s, (V i).shade) = ⋃ i ∈ s, (V' i).shade :=
    Set.iUnion₂_congr fun i hi => h i hi
  have hS : (∑ i ∈ s, volume (V i).shade) = ∑ i ∈ s, volume (V' i).shade :=
    Finset.sum_congr rfl fun i hi => by rw [h i hi]
  unfold multiplicity
  rw [hU, hS]

/-- **Pointwise multiplicity is blind to the carrier.** -/
theorem pointwiseMultiplicity_congr_shade (s : Finset ι) (V V' : ι → ShadedBody E)
    (h : ∀ i ∈ s, (V i).shade = (V' i).shade) (x : E) :
    pointwiseMultiplicity s V x = pointwiseMultiplicity s V' x := by
  classical
  unfold pointwiseMultiplicity
  congr 1
  refine Finset.filter_congr fun i hi => ?_
  rw [h i hi]

/-- **Constant multiplicity is blind to the carrier.** -/
theorem hasCConstantMultiplicity_congr_shade (s : Finset ι) (V V' : ι → ShadedBody E)
    (h : ∀ i ∈ s, (V i).shade = (V' i).shade) (C : NNReal) :
    HasCConstantMultiplicity s V C ↔ HasCConstantMultiplicity s V' C := by
  have hU : (⋃ i ∈ s, (V i).shade) = ⋃ i ∈ s, (V' i).shade :=
    Set.iUnion₂_congr fun i hi => h i hi
  unfold HasCConstantMultiplicity
  simp only [hU, pointwiseMultiplicity_congr_shade s V V' h]

/-- **The fullness cost of enlarging the carriers.**

If the new carriers have total volume at most `c` times the old total volume, then the fullness
drops by at most the factor `c`.  This is the only loss incurred by
`ShadedBody.reshape`, and in the application `c` is the dimension-comparison constant of GWZ
Definition 4.2. -/
theorem fullness'_le_mul_fullness'_reshape (s : Finset ι) (V V' : ι → ShadedBody E)
    (hshade : ∀ i ∈ s, (V i).shade = (V' i).shade) {c : ENNReal} (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hvol : ∑ i ∈ s, volume (V' i).carrier ≤ c * ∑ i ∈ s, volume (V i).carrier) :
    fullness' s V ≤ c * fullness' s V' := by
  classical
  unfold fullness'
  set A : ENNReal := (∑ i ∈ s, volume (V i).shade) with hA
  set Ap : ENNReal := (∑ i ∈ s, volume (V' i).shade) with hAp
  set B : ENNReal := (∑ i ∈ s, volume (V i).carrier) with hB
  set B' : ENNReal := (∑ i ∈ s, volume (V' i).carrier) with hB'
  have hApA : Ap = A := by
    calc
      Ap = ∑ i ∈ s, volume (V' i).shade := hAp.symm
      _ = ∑ i ∈ s, volume (V i).shade :=
        Finset.sum_congr rfl (fun i hi => by rw [hshade i hi])
      _ = A := hA
  rw [hApA]
  rw [show c * (A / B') = (c * A) / B' by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    rw [mul_assoc]]
  calc
    A / B = (c * A) / (c * B) := (ENNReal.mul_div_mul_left A B hc0 hctop).symm
    _ ≤ (c * A) / B' := ENNReal.div_le_div le_rfl hvol

end ReshapeFamily

end ShadedBody

/-! ## The Section-6 factorisation adapter -/

namespace Kakeya

open Classical in
/-- **The Section-6 factorisation adapter (GWZ Definition 4.2, complete form).**

A *new* wrapper carrying exactly the five clauses of "`𝕎` factors `𝕍`" identified in the module
docstring, together with the representative-shape data that lets the output of GWZ Proposition
5.1 be handed back to Section 6 as an exact `a × b × 1` `Kakeya.ShadedPlank`.

Relative to `Kakeya.ComparableBodyFactorization` the new fields are `fibre_nonempty`,
`fibre_frostman`, `fibre_mass_comparable`, `repr`, `cthickening_le_repr` and `volume_repr_le`;
relative to `Kakeya.GlobalComparableBodyFactorization` the new fields are the same minus the
representative plank, whose one-sided form is `le_plank` there.  Nothing here requires the actual
body to *equal* a plank, and nothing requires an exact plank to lie inside a `ρ`-tube: the actual
convex body `body x` and the representative plank `repr x` stay strictly separate.

`cthickening_le_repr` asks the representative to contain not just the body but its
`scale`-collar.  That collar is where the induced shading of GWZ Definition 5.7 lives, so this is
precisely the room needed to keep the Proposition-5.1 shade inside the representative; and since
`scale (body x) ≤ a`, it costs only a bounded enlargement of the representative, i.e. it is still
the Definition-4.2 clause "approximately the same dimensions".  `volume_repr_le` is the matching
lower half of that clause, in the single scalar form the fullness transfer consumes. -/
structure Section6CoreFactorData (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
    {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (CFib : ENNReal) (C₀ Cmass Cdim : ℝ≥0) where
  /-- Index type of the outer cells. -/
  Cell : Type
  /-- Decidable equality used by all finite outer-index constructions. -/
  [decEqCell : DecidableEq Cell]
  /-- The outer cells actually used. -/
  cells : Finset Cell
  /-- The *actual* outer body of a cell.  Never assumed to be a plank. -/
  body : Cell → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))
  /-- The cell collecting each fine body. -/
  cellOf : ι → Cell
  /-- Every fine index is collected by a cell in use. -/
  cellOf_mem : ∀ i ∈ q, cellOf i ∈ cells
  /-- Clause (1): every fine body lies in the body of its cell. -/
  le_body : ∀ i ∈ q, (T i).toConvexSpaceBody ≤ body (cellOf i)
  /-- The fibre, stored explicitly so dependent-sum adapters can fix their decidability data. -/
  fibre : Cell → Finset ι
  /-- Membership in the stored fibre is restriction along `cellOf`. -/
  fibre_mem : ∀ {i x}, i ∈ fibre x ↔ i ∈ q ∧ cellOf i = x
  /-- Every cell in use collects at least one fine body. -/
  fibre_nonempty : ∀ x ∈ cells, (fibre x).Nonempty
  /-- Clause (2): each fibre is `CFib`-Frostman inside the body of its cell. -/
  fibre_frostman : ∀ x ∈ cells,
    ConvexSpaceBody.IsFrostmanIn (fibre x)
      (fun i => (T i).toConvexSpaceBody) (body x) CFib
  /-- Clause (5): the fibre masses are comparable across cells. -/
  fibre_mass_comparable : ∀ x ∈ cells, ∀ y ∈ cells,
    Kakeya.densityIn (fibre x)
        (fun i => (T i).toConvexSpaceBody) (body x)
      ≤ (Cmass : ENNReal) * Kakeya.densityIn (fibre y)
        (fun i => (T i).toConvexSpaceBody) (body y)
  /-- Clause (4a): the `a × b × 1` representative plank of a cell. -/
  repr : Cell → Plank a b hab hb1
  /-- Clause (4b): the representative contains the `scale`-collar of the actual body, hence in
  particular the actual body itself. -/
  cthickening_le_repr : ∀ x ∈ cells,
    (body x).cthickening ((body x).scale) ≤ (repr x).toConvexSpaceBody
  /-- Clause (4c): the representative is not much bigger than the actual body. -/
  volume_repr_le : ∀ x ∈ cells,
    volume ((repr x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ (Cdim : ENNReal) * volume (body x).carrier

/-- The Part-(B) analytic package.  The global outer Katz--Tao clause is deliberately kept out of
`Section6CoreFactorData`: Proposition 5.1 does not consume it, and in Part (A) only the
parentwise representative families are Katz--Tao. -/
structure Section6FactorData (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
    {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (CFib : ENNReal) (C₀ Cmass Cdim : ℝ≥0)
    extends Section6CoreFactorData a b hab hb1 q T CFib C₀ Cmass Cdim where
  /-- Clause (3), used by the global Part-(B) adapter. -/
  isKatzTao : ConvexSpaceBody.IsKatzTao cells body (C₀ : ENNReal)

namespace Section6CoreFactorData

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {CFib : ENNReal} {C₀ Cmass Cdim : ℝ≥0}
  (F : Section6CoreFactorData a b hab hb1 q T CFib C₀ Cmass Cdim)

/-- **The factor family handed to generic GWZ Proposition 5.1.**

Inner bodies are the shaded fine tubes, outer bodies are the *actual* factor bodies, and the
parent map is the cell map.  The two proof fields of `ShadedBody.FactorFamily` are literally the
adapter's `cellOf_mem` and `le_body`. -/
def toFactorFamily : ShadedBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι F.Cell where
  innerSet := q
  innerBody := fun i => (T i).toShadedBody
  outerSet := F.cells
  outerBody := F.body
  parent := F.cellOf
  parent_mem := F.cellOf_mem
  inner_le_parent := F.le_body

@[simp] theorem toFactorFamily_innerSet : F.toFactorFamily.innerSet = q := rfl
@[simp] theorem toFactorFamily_outerSet : F.toFactorFamily.outerSet = F.cells := rfl
@[simp] theorem toFactorFamily_parent : F.toFactorFamily.parent = F.cellOf := rfl
@[simp] theorem toFactorFamily_outerBody : F.toFactorFamily.outerBody = F.body := rfl

open Classical in
theorem toFactorFamily_fiber (x : F.Cell) :
    F.toFactorFamily.fiber x = F.fibre x := by
  apply Finset.ext
  intro i
  rw [F.fibre_mem]
  simp [ShadedBody.FactorFamily.fiber]

/-- **Clause (2) is exactly the Proposition-5.1 Frostman hypothesis.** -/
theorem hasFrostmanFibers : F.toFactorFamily.HasFrostmanFibers CFib := by
  intro x hx
  rw [F.toFactorFamily_fiber]
  exact F.fibre_frostman x hx

/-- **The inner family has `2`-similar shape.**

All inner bodies are `δ`-tubes, so their thickness sequences agree up to the absolute factor `2`
once `δ ≤ 1/2` (`Kakeya.Tube.thickness_le_two_mul_thickness`).  This is the only hypothesis of
generic Proposition 5.1 that constrains the fine scale, and `δ ≤ 1/2` is harmless: Section 6
always works below a fixed threshold `δ₀`. -/
theorem innerHasSimilarShape (hδ : (δ : ℝ) ≤ 1 / 2) :
    F.toFactorFamily.InnerHasSimilarShape 2 := by
  intro i _ i' _
  intro n
  simpa [toFactorFamily] using
    Kakeya.Tube.thickness_le_two_mul_thickness hδ (T i).toTube (T i').toTube n

/-- **Outer Frostman transfer (steps E), specialised to the adapter.**

Clause (5) plus global Frostman control of the fine family gives Frostman control of the whole
outer family, with the loss `Cmass`.  This is the honest provenance of the outer Frostman
conclusion used by Proposition 6.6(A). -/
theorem outerFrostman [DecidableEq ι] {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {CF : ENNReal}
    (hFr : ConvexSpaceBody.IsFrostmanIn q (fun i => (T i).toConvexSpaceBody) K CF)
    (hVpos : ∀ i ∈ q, 0 < volume ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hbodyK : ∀ x ∈ F.cells, F.body x ≤ K) :
    ConvexSpaceBody.IsFrostmanIn F.cells F.body K ((Cmass : ENNReal) * CF) := by
  classical
  exact ConvexSpaceBody.isFrostmanIn_parents_of_uniform_fibres hFr hVpos F.cellOf_mem
    F.le_body hbodyK (fun x ↦ by
      apply Finset.ext
      intro i
      rw [F.fibre_mem]
      simp) F.fibre_nonempty F.fibre_mass_comparable

/-! ### The original-outer view -/

/-- **The Section-6 outer view of a Proposition-5.1 outer body.**

The shade produced by Proposition 5.1 is kept verbatim (clipped to the representative only so
that the definition is total; on the selected cells the clipping is vacuous, see
`Kakeya.Section6FactorData.shade_outerView`), and it is re-presented on the exact `a × b × 1`
representative plank.  The result is a `Kakeya.ShadedPlank`, which is precisely the type the two
Section-6 consumers demand. -/
def outerView (G : ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) ι F.Cell)
    (x : F.Cell) : ShadedPlank a b hab hb1 where
  toPrism3D := F.repr x
  shade := (G.outerBody x).shade ∩ ((F.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
  measurableSet_shade :=
    (G.outerBody x).measurableSet_shade.inter (F.repr x).isCompact.isClosed.measurableSet
  shade_subset := Set.inter_subset_right

@[simp] theorem outerView_toPrism3D
    (G : ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) ι F.Cell) (x : F.Cell) :
    (F.outerView G x).toPrism3D = F.repr x := rfl

/-- On a cell whose Proposition-5.1 outer carrier is the `scale`-collar of the actual body, the
clipping in `Kakeya.Section6FactorData.outerView` removes nothing. -/
theorem shade_outerView
    (G : ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) ι F.Cell) {x : F.Cell}
    (hx : x ∈ F.cells)
    (hcar : (G.outerBody x).toConvexSpaceBody = (F.body x).cthickening ((F.body x).scale)) :
    (F.outerView G x).shade = (G.outerBody x).shade := by
  rw [Section6CoreFactorData.outerView]
  rw [Set.inter_eq_left]
  exact (G.outerBody x).shade_subset.trans (by
    rw [hcar]
    exact SetLike.coe_subset_coe.mpr (F.cthickening_le_repr x hx))

/-- **The obstruction to clipping the shade.**

One might instead try to keep the exact plank as carrier and intersect the Proposition-5.1 shade
with the *actual body*, hoping for a constant-mass bound
`volume ((G.outerBody x).shade ∩ (F.body x).carrier) ≥ c * volume ((G.outerBody x).shade)`.
That bound is **false** in general: by `ShadedBody.shade_inducedShading` the shade is
`N_{2r}(U) ∩ N_r(W)` with `r = W.scale`, and `N_{2r}(U)` can carry almost all of its mass in the
collar `N_r(W) \ W` — take `U` a single point of `∂W`, or more relevantly a shaded union
concentrated near the boundary of a very eccentric `W`, where the collar has volume comparable to
`W` itself.  No constant depending only on the dimension survives.

Consequently the transfer here goes the other way: the carrier is enlarged to the representative
plank and the shade is untouched.  The only price is the fullness factor `Cdim`, and it is paid
by clause (4) of GWZ Definition 4.2 rather than by an unavailable clipping estimate. -/
theorem shade_outerView_of_mem
    (G : ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) ι F.Cell)
    (hsub : G.outerSet ⊆ F.cells)
    (hcar : ∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody =
      (F.body j).cthickening ((F.body j).scale)) :
    ∀ x ∈ G.outerSet, (F.outerView G x).shade = (G.outerBody x).shade :=
  fun x hx => F.shade_outerView G (hsub hx) (hcar x hx)

/-- **Multiplicity is transferred with no loss.** -/
theorem multiplicity_outerView
    (G : ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) ι F.Cell)
    (hsub : G.outerSet ⊆ F.cells)
    (hcar : ∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody =
      (F.body j).cthickening ((F.body j).scale)) :
    ShadedBody.multiplicity G.outerSet (fun x => (F.outerView G x).toShadedBody)
      = ShadedBody.multiplicity G.outerSet G.outerBody :=
  ShadedBody.multiplicity_congr_shade _ _ _ (F.shade_outerView_of_mem G hsub hcar)

/-- **Constant multiplicity is transferred with no loss.** -/
theorem hasCConstantMultiplicity_outerView
    (G : ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) ι F.Cell)
    (hsub : G.outerSet ⊆ F.cells)
    (hcar : ∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody =
      (F.body j).cthickening ((F.body j).scale)) (C : ℝ≥0) :
    ShadedBody.HasCConstantMultiplicity G.outerSet
        (fun x => (F.outerView G x).toShadedBody) C
      ↔ ShadedBody.HasCConstantMultiplicity G.outerSet G.outerBody C :=
  ShadedBody.hasCConstantMultiplicity_congr_shade _ _ _
    (F.shade_outerView_of_mem G hsub hcar) C

/-- **Volume comparison between a representative plank and the Proposition-5.1 outer carrier.**

The outer carrier is the `scale`-collar of the actual body, so it contains the actual body, and
clause (4c) bounds the representative by the actual body. -/
theorem volume_outerView_le
    (G : ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) ι F.Cell)
    {x : F.Cell} (hx : x ∈ F.cells)
    (hcar : (G.outerBody x).toConvexSpaceBody = (F.body x).cthickening ((F.body x).scale)) :
    volume ((F.outerView G x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ (Cdim : ENNReal) * volume ((G.outerBody x).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  calc
    volume ((F.outerView G x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = volume ((F.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3))) := rfl
    _ ≤ (Cdim : ENNReal) * volume ((F.body x).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
      F.volume_repr_le x hx
    _ ≤ (Cdim : ENNReal) * volume ((G.outerBody x).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
      gcongr
      calc
        (F.body x).carrier ⊆ ((F.body x).cthickening ((F.body x).scale)).carrier :=
          ConvexSpaceBody.self_le_cthickening (F.body x) ((F.body x).scale)
        _ = (G.outerBody x).carrier := by
          simpa using congrArg ConvexSpaceBody.carrier hcar.symm

/-- **Fullness is transferred at the cost of the dimension-comparison constant.** -/
theorem fullness'_outerView
    (G : ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) ι F.Cell)
    (hsub : G.outerSet ⊆ F.cells)
    (hcar : ∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody =
      (F.body j).cthickening ((F.body j).scale))
    (hCdim0 : Cdim ≠ 0) :
    ShadedBody.fullness' G.outerSet G.outerBody
      ≤ (Cdim : ENNReal) *
        ShadedBody.fullness' G.outerSet (fun x => (F.outerView G x).toShadedBody) := by
  refine ShadedBody.fullness'_le_mul_fullness'_reshape _ _ _
    (fun x hx => (F.shade_outerView_of_mem G hsub hcar x hx).symm)
    (by exact_mod_cast hCdim0) ENNReal.coe_ne_top ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x hx => F.volume_outerView_le G (hsub hx) (hcar x hx)

/-! ### Canonical Proposition 5.1 calls -/

/-- Apply the fixed-scale Section 6 interface of the corrected Proposition 5.1 to the actual
factor bodies packaged by `Section6FactorData`.

The representative planks do not enter this call: Proposition 5.1 factors through `F.body` and
returns the thick actual-body family.  Re-presentation on `F.repr` is a separate Section 6 step,
using `cthickening_le_repr`, `shade_outerView_of_mem`, and `fullness'_outerView` above. -/
theorem prop51CoreAtScale {δ₀ w₁ : NNReal}
    (input : ShadedBody.Section6FactoringAtScaleInput F.toFactorFamily δ₀ w₁) :
    @ShadedBody.FactoringAndMultPropCoreAtScale _ _ _ _ _ _ _ _ _ F.decEqCell
      F.toFactorFamily CFib δ₀ input.hδ
      input.hdisc input.volumeRatio w₁ input.hw₁ :=
  by
    letI := F.decEqCell
    exact ShadedBody.section6LocalFactorisation F.toFactorFamily input F.hasFrostmanFibers

/-- Apply the scale-selecting Section 6 interface when the actual factor bodies have only a
common upper scale bound.  The selected scale and the fixed-scale core are returned together;
in particular no shortest-scale information is inferred from `ContainsFlatDisc`. -/
theorem prop51CoreSelectScale {δ₀ B : NNReal}
    (input : @ShadedBody.Section6FactoringSelectScaleInput _ _ _ _ _ _ _ _ F.decEqCell
      F.toFactorFamily δ₀ B) :
    @ShadedBody.FactoringAndMultPropCoreSelectScaleResult _ _ _ _ _ _ _ _ _ F.decEqCell
      F.toFactorFamily CFib δ₀ B
      (@ShadedBody.Section6FactoringSelectScaleInput.hδ _ _ _ _ _ _ _ _ F.decEqCell
        F.toFactorFamily δ₀ B input)
      (@ShadedBody.Section6FactoringSelectScaleInput.hdisc _ _ _ _ _ _ _ _ F.decEqCell
        F.toFactorFamily δ₀ B input)
      (@ShadedBody.Section6FactoringSelectScaleInput.volumeRatio _ _ _ _ _ _ _ _
        F.decEqCell F.toFactorFamily δ₀ B input)
      (@ShadedBody.Section6FactoringSelectScaleInput.hδB _ _ _ _ _ _ _ _ F.decEqCell
        F.toFactorFamily δ₀ B input)
      (@ShadedBody.Section6FactoringSelectScaleInput.hupper _ _ _ _ _ _ _ _ F.decEqCell
        F.toFactorFamily δ₀ B input)
      (@ShadedBody.Section6FactoringSelectScaleInput.hmass _ _ _ _ _ _ _ _ F.decEqCell
        F.toFactorFamily δ₀ B input) :=
  by
    letI := F.decEqCell
    exact @ShadedBody.section6LocalFactorisationSelectScale _ _ _ _ _ _ _ _ _
      F.decEqCell F.toFactorFamily CFib δ₀ B input F.hasFrostmanFibers

end Section6CoreFactorData

end Kakeya

end

end
