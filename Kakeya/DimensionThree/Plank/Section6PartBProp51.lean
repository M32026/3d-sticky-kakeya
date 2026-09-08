/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Section6FactorAdapter
public import Kakeya.DimensionThree.Plank.Section6CoarseFactorisation

/-!
# The Part-(B) Remark-5.3 adapter for GWZ Proposition 6.6(B)

`Kakeya.Section6FactorData.section6LocalOutput` is the *fine* (Part-(A)) adapter: it applies GWZ
Proposition 5.1 to a factor family whose **own** fibres are Frostman, and re-presents the output on
the representative `a × b × 1` planks.  Part (B) cannot use it, and must not be made to: in GWZ
Proposition 6.6(B) the fine fibre `𝒯_W` is *not* Frostman in `W`.  What is Frostman is the coarse
fibre `𝒯_{ρ,W}`, and GWZ Remark 5.3 says that this is enough to run Proposition 5.1 on the fine
family.  This file is the parallel Part-(B) adapter implementing exactly that.

## The shape of the argument

`Kakeya.Section6PartBData` already carries, and this file uses, nothing but:

* `decomp` — the fine-to-coarse assignment *function* with two-sided comparable fibres
  (`assign`, `assign_mem`, `leaf_le_parent`, `le_card_fibre`, `card_fibre_le`);
* `factor` — the outer cells, the *actual* cell bodies, the cell map, the representative
  `a × b × 1` planks, the outer Katz--Tao property, and the **coarse-fibre Frostman** datum
  `coarse_fibre_frostman`.

No field is added to `Kakeya.Section6PartBData`.  The representative-plank presentation is already
part of `Kakeya.Section6PartBData.Remark53Prop51`, so downstream users consume its fields directly
rather than passing through a second conjunction-valued adapter.

`Kakeya.Section6PartBData.toFineFactorFamily` is the Proposition-5.1 input: inner bodies are the
**fine** shaded `δ`-tubes, outer bodies are the actual cell bodies, and the parent map is
`Kakeya.Section6PartBData.cellOfFine = cellOf ∘ assign`.  Of the two geometric hypotheses of
`ShadedBody.factoringAndMultPropCore`, this family satisfies

* `ShadedBody.FactorFamily.InnerHasSimilarShape 2` outright
  (`Kakeya.Section6PartBData.innerHasSimilarShape`, from `δ ≤ 1/2`), and
* `ShadedBody.FactorFamily.HasFrostmanFibers` **not at all** — that is the false statement, and it
  is deliberately never formed here.  Compare
  `Kakeya.Section6PartBFactorisation.hasFrostmanFibers`, which is the *coarse* family's Frostman
  datum and is genuinely available.

## Where Remark 5.3 enters

The canonical Proposition 5.1 core now has the precise Remark-5.3 variant needed here: it keeps
the fine tubes as inner indices and consumes Frostman control only after thickening them at the
outer body's shortest scale.  The theorem
`Kakeya.Section6PartBData.prop51CoreAtScaleOfRemark53` applies that variant to the actual cell
bodies.  Replacing those bodies by exact representative planks, and the accompanying cardinality
comparison, are separate Section 6 presentation data.

Those presentation clauses are isolated in
`Kakeya.Section6PartBData.Remark53Prop51`: a `Prop`-valued structure whose first nine fields are
*literally* the conjuncts of `ShadedBody.factoringAndMultPropCore` read for
`Kakeya.Section6PartBData.toFineFactorFamily`, with the Frostman constant replaced by the effective
Part-(B) constant `Kakeya.remark53Const Cfib CF = Cfib² · coarseTubeVolumeRatio · CF`, and whose
tenth records the fibre-cardinality pigeonholing performed inside the proof of Proposition 5.1 with
its absolute constant.

That constant is not invented.  It is the constant already *proved* to govern fine-family
non-concentration from the coarse datum alone, in
`Kakeya.Section6PartBData.remark53_card_fine_le`: `Cfib²` is the price of transporting a coarse
count to a fine count through comparable fibres, and `coarseTubeVolumeRatio · CF` is the coarse
Frostman count of `Kakeya.card_coarse_le_of_frostmanIn`.  Remark 5.3 asserts that this same
substitution is legitimate throughout the proof of Proposition 5.1, not merely in the one counting
step that is already proved here.

Everything downstream of the leaf **is** proved.  Consumers use the fields of
`Kakeya.Section6PartBData.Remark53Prop51` directly; the derived nonemptiness and cardinality facts
below contain no additional mathematical assumption.

## What the adapter exposes

Only what `Kakeya.factoringAndMultPropGlobal` consumes: the selected outer cells, their
representative shaded planks, the refined fine family with its containment and refinement data,
the outer fullness lower bound, constant outer multiplicity, the constant inner multiplicity that
yields the cardinality relation, the multiplicity split
`μ(𝒯, Y) ≤ Csplit · μ(𝒲, Y_𝒲) · μ(𝒯_W, Y')`, and the shading containment.  The irrelevant
Proposition-5.1 output (item 7, the ball-averaged multiplicity, together with its hypothesis
`ShadedBody.FactorFamily.OuterIsAtScale`) is not duplicated.

## What this file does not touch

`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`, `Kakeya.globalCoarsePlankFallback`,
Proposition 5.1 itself, and `Kakeya.Section6FactorData.section6LocalOutput` are all left exactly as
they are.  Part (B) is never converted into a `Kakeya.Section6FactorData`, and no fine-family
`ShadedBody.FactorFamily.HasFrostmanFibers` datum is ever constructed.
-/

@[expose] public section

open MeasureTheory Convexity
-- Every fibre in this file is a `Finset.filter` over an arbitrary index type.
set_option linter.style.openClassical false
open scoped NNReal ENNReal Classical

noncomputable section

namespace Kakeya

/-- **The effective Part-(B) Frostman constant of GWZ Remark 5.3.**

`Cfib² · coarseTubeVolumeRatio · CF`, where `CF` is the coarse-fibre Frostman constant of
`Kakeya.Section6PartBFactorisation.coarse_fibre_frostman` and `Cfib` the fibre-comparability
constant of `Kakeya.Section6CoarseTubeDecomposition`.

This is exactly the constant with which the coarse datum already *provably* controls the fine
family: it is the constant of `Kakeya.Section6PartBData.remark53_card_fine_le`, whose two factors
are the fibre-transport loss `Cfib²` (`Kakeya.card_le_of_comparable_fibres_of_selected_le`) and the
coarse Frostman count `coarseTubeVolumeRatio · CF` (`Kakeya.card_coarse_le_of_frostmanIn`).  It is
*not* `CF`: forcing the fine family to inherit the bare coarse constant would be a strictly
stronger — and unjustified — claim. -/
def remark53Const (Cfib CF : ℝ≥0) : ℝ≥0 := Cfib ^ 2 * coarseTubeVolumeRatio * CF

theorem one_le_remark53Const {Cfib CF : ℝ≥0} (hCfib : 1 ≤ Cfib) (hCF : 1 ≤ CF) :
    1 ≤ remark53Const Cfib CF := by
  rw [remark53Const]
  have h1 : (1 : ℝ≥0) ≤ Cfib ^ 2 := one_le_pow₀ hCfib
  calc
    (1 : ℝ≥0) = 1 * 1 * 1 := by norm_num
    _ ≤ Cfib ^ 2 * coarseTubeVolumeRatio * CF := by
      gcongr
      exact one_le_coarseTubeVolumeRatio

namespace Section6PartBData

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {m Cfib CF C₀ : ℝ≥0}
  (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)

/-! ## The fine factor family -/

/-- **The Proposition-5.1 input of Part (B): the *fine* factor family.**

Inner bodies are the fine shaded `δ`-tubes, outer bodies are the *actual* cell bodies, and the
parent map is `Kakeya.Section6PartBData.cellOfFine`, i.e. the coarse cell map composed with the
fine-to-coarse assignment.  Both proof fields come from the datum: a fine tube lies in its coarse
parent (`decomp.leaf_le_parent`), which lies in the body of its cell (`factor.le_body`).

The fibres of this family are **not** Frostman, and no such claim is made anywhere in this file. -/
def toFineFactorFamily : ShadedBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι D.factor.Cell where
  innerSet := q
  innerBody := fun i => (T i).toShadedBody
  outerSet := D.factor.cells
  outerBody := D.factor.body
  parent := D.cellOfFine
  parent_mem := fun i hi => D.factor.cellOf_mem _ (D.decomp.assign_mem i hi)
  inner_le_parent := fun i hi =>
    le_trans (D.decomp.leaf_le_parent i hi) (D.factor.le_body _ (D.decomp.assign_mem i hi))

@[simp] theorem toFineFactorFamily_innerSet : D.toFineFactorFamily.innerSet = q := rfl

@[simp] theorem toFineFactorFamily_outerSet :
    D.toFineFactorFamily.outerSet = D.factor.cells := rfl

@[simp] theorem toFineFactorFamily_outerBody :
    D.toFineFactorFamily.outerBody = D.factor.body := rfl

@[simp] theorem toFineFactorFamily_parent :
    D.toFineFactorFamily.parent = D.cellOfFine := rfl

/-- **The fine family has `2`-similar shape.**

The one geometric hypothesis of `ShadedBody.factoringAndMultPropCore` that Part (B) *does* satisfy
outright: all inner bodies are `δ`-tubes, so their thickness sequences agree up to the absolute
factor `2` once `δ ≤ 1/2` (`Kakeya.Tube.thickness_le_two_mul_thickness`).  The other hypothesis,
`ShadedBody.FactorFamily.HasFrostmanFibers`, is false for this family; that is what
`Kakeya.Section6PartBData.Remark53Prop51` replaces. -/
theorem innerHasSimilarShape (hδ : (δ : ℝ) ≤ 1 / 2) :
    D.toFineFactorFamily.InnerHasSimilarShape 2 := by
  intro i _ i' _ n
  simpa [toFineFactorFamily] using
    Tube.thickness_le_two_mul_thickness hδ (T i).toTube (T i').toTube n

/-- **The output of GWZ Proposition 5.1 on the Part-(B) fine family.**

`𝒲'` is `outerSet`, the induced shading `Y_{𝒲'}` is carried by `outerBody`, and the refinement
`(𝒯', Y')` of the fine family is carried by `innerSet`/`innerBody`.  This proof-independent view is
used only for the Section 6 presentation contract; the canonical constructed output is exposed by
`Kakeya.Section6PartBData.prop51CoreAtScaleOfRemark53`. -/
def fineOutput : ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) ι D.factor.Cell where
  innerSet := q
  innerBody := fun i ↦ (T i).toShadedBody
  outerSet := D.factor.cells
  outerBody := fun x ↦ ShadedBody.inducedShading
    (D.toFineFactorFamily.fiber x) D.toFineFactorFamily.innerBody (D.factor.body x)
  parent := D.cellOfFine
  parent_mem := fun i hi ↦ D.factor.cellOf_mem _ (D.decomp.assign_mem i hi)
  inner_le_parent := fun i hi ↦
    (D.toFineFactorFamily.inner_le_parent i hi).trans
      (ConvexSpaceBody.self_le_cthickening (D.factor.body (D.cellOfFine i))
        (D.factor.body (D.cellOfFine i)).scale)
  shade_subset_parent := by
    intro i hi x hxi
    apply ShadedBody.cthickening_scale_iUnionShade_subset_shade_inducedShading
      (s := D.toFineFactorFamily.fiber (D.cellOfFine i))
      (V := D.toFineFactorFamily.innerBody)
    · intro p hp
      have hle := D.toFineFactorFamily.inner_le_parent p (Finset.mem_filter.mp hp).1
      simpa [(Finset.mem_filter.mp hp).2] using hle
    · apply Metric.self_subset_cthickening
      exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, hxi⟩

/-! ## The Section-6 outer view: representative planks -/

/-- **The Section-6 outer view of the Part-(B) Proposition-5.1 outer bodies.**

The shade produced by Proposition 5.1 is kept verbatim, clipped to the representative so that the
definition is total, and re-presented on the exact `a × b × 1` representative plank
`D.factor.repr x`.  The result is a `Kakeya.ShadedPlank`, which is what
`Kakeya.factoringAndMultPropGlobal` demands of its outer family.

This is the Part-(B) sibling of `Kakeya.Section6FactorData.outerView`, and the obstruction recorded
in `Kakeya.Section6FactorData.shade_outerView_of_mem` applies verbatim: the carrier is enlarged and
the shade is untouched, because clipping the shade down into the actual body admits no
constant-mass bound. -/
def outerPlanks (x : D.factor.Cell) : ShadedPlank a b hab hb1 where
  toPrism3D := D.factor.repr x
  shade := (D.fineOutput.outerBody x).shade
    ∩ ((D.factor.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
  measurableSet_shade := (D.fineOutput.outerBody x).measurableSet_shade.inter
    (D.factor.repr x).isCompact.isClosed.measurableSet
  shade_subset := Set.inter_subset_right

theorem shade_outerPlanks_eq (x : D.factor.Cell) :
    (D.outerPlanks x).shade = (D.fineOutput.outerBody x).shade
      ∩ ((D.factor.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3))) := rfl

theorem carrier_outerPlanks (x : D.factor.Cell) :
    ((D.outerPlanks x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ((D.factor.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3))) := rfl

/-- **The selected outer planks lie in the working window.**

This is the outer window clause of `Kakeya.factoringAndMultPropGlobal`.  It is exactly the datum's
own `Kakeya.Section6PartBFactorisation.repr_window` read on the selected cells: the outer plank of a
cell *is* its representative, by `Kakeya.Section6PartBData.carrier_outerPlanks`.

It cannot be derived from the rest of the datum — see that field's docstring for the `a = b = 1`
configuration which defeats every argument from the fine tubes alone — which is why the containment
is carried by the factorisation rather than reconstructed here. -/
theorem outerPlanks_window_of_subset {ts : Finset D.factor.Cell} (hsub : ts ⊆ D.factor.cells) :
    ∀ x ∈ ts, ((D.outerPlanks x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ) :=
  fun x hx => D.factor.repr_window x (hsub hx)

/-! ## GWZ Remark 5.3: the single explicit mathematical leaf -/

/-- **GWZ Remark 5.3 for Part (B).**

Nine of the ten fields below are the conjuncts of `ShadedBody.factoringAndMultPropCore`, read for
the fine factor family `Kakeya.Section6PartBData.toFineFactorFamily`, with the Frostman constant
taken to be `Kakeya.remark53Const Cfib CF` instead of a fine-fibre Frostman constant that does not
exist.

The tenth, `fiber_card_comparable`, is of a different kind: it is a *proof-level* output of
Proposition 5.1 — a property of the pigeonholing inside the construction rather than one of its
seven stated items — which the Remark-5.3 extension preserves.  It is stated separately, with an
absolute constant, precisely because it is not derivable from the other nine; see its own
docstring.

**Why the outer clauses are stated on the representative planks.**  Generic Proposition 5.1 returns
its outer shading on the `scale`-collar `N_r(W)` of the input outer body, not on the body itself
(`ShadedBody.outerFactoringFamily_carrier`): the induced shading of GWZ Definition 5.7 genuinely
sticks out.  An earlier version of this interface recorded that collar identity and reshaped
afterwards, which forced the *consumer* to supply

`(body y).cthickening ((body y).scale) ≤ repr y`.

That containment is **false** for a general `Kakeya.Section6PartBFactorisation`: the least thickness
of a cell body is at least the coarse radius `ρ`, so its `ρ`-collar need not fit inside the
`a × b × 1` representative.  Making it a hypothesis of Proposition 6.6(B) would therefore have
imported a false assumption.

Since this structure records the Section 6 presentation of the Proposition 5.1 output, its outer
clauses are stated where Section 6 consumes them — on
`Kakeya.Section6PartBData.outerPlanks`, the shading re-presented on `D.factor.repr`.  No reshaping
step, and hence no collar containment, is needed anywhere downstream.  The inner clauses are
unchanged; only the outer family is named differently.

This structure is an explicit input to the Section 6 assembly, not an axiom or an unconditional
constructor.  The canonical actual-body Remark-5.3 theorem is already proved; the remaining fields
are exactly the representative-plank and cardinality contracts owned by Section 6 geometry.

What Part (B) *does* prove unconditionally, and what makes the constant honest, is the special case
`Kakeya.Section6PartBData.remark53_card_fine_le`: the fine non-concentration count with exactly the
constant `Kakeya.remark53Const Cfib CF`, from the coarse Frostman datum and fibre comparability
alone. -/
structure Remark53Prop51 (Cprop : ℝ≥0) : Prop where
  /-- The selected outer cells are cells of the datum (Proposition 5.1, structural). -/
  outerSet_subset : D.fineOutput.outerSet ⊆ D.factor.cells
  /-- The refined fine family consists of the fine tubes over the selected cells. -/
  innerSet_eq :
    D.fineOutput.innerSet = ({i ∈ q | D.cellOfFine i ∈ D.fineOutput.outerSet} : Finset ι)
  /-- The refinement leaves the fine convex bodies unchanged; only the shades shrink. -/
  innerBody_carrier : ∀ i ∈ q,
    (D.fineOutput.innerBody i).toConvexSpaceBody = (T i).toConvexSpaceBody
  /-- Item 1: `(𝒯', Y')` is a `⪆ 1` refinement of `(𝒯, Y)`. -/
  refinement : ShadedBody.IsCRefinement D.fineOutput.innerSet D.fineOutput.innerBody q
    (fun i => (T i).toShadedBody) Cprop⁻¹
  /-- Item 2: `λ(𝒲', Y_{𝒲'}) ⪆ (remark53Const)⁻¹ · λ(𝒯, Y)²`, on the representative planks.  This is
  the one clause where the effective Remark-5.3 constant replaces the Frostman constant of
  Proposition 5.1. -/
  fullness : ((remark53Const Cfib CF : ℝ≥0) : ENNReal)⁻¹
      * (Cprop : ENNReal)⁻¹
      * (ShadedBody.fullness q (fun i => (T i).toShadedBody) : ENNReal) ^ 2
    ≤ (ShadedBody.fullness D.fineOutput.outerSet
        (fun x => (D.outerPlanks x).toShadedBody) : ENNReal)
  /-- Item 3: `(𝒲', Y_{𝒲'})` has constant multiplicity, on the representative planks. -/
  outerConstMult : ShadedBody.HasCConstantMultiplicity D.fineOutput.outerSet
    (fun x => (D.outerPlanks x).toShadedBody) Cprop
  /-- Item 4: for each selected cell the refined fibre has constant pointwise multiplicity, with a
  common value `μinner`.  This is the clause that yields the cardinality relation
  `|𝒲'| · |𝒯_W| ≤ Ccard · |𝒯|` downstream. -/
  innerConstMult : ∃ μinner : ℝ≥0, ∀ x ∈ D.fineOutput.outerSet,
    ∀ y ∈ ⋃ i ∈ D.fineOutput.fiber x, (D.fineOutput.innerBody i).shade,
      (ShadedBody.pointwiseMultiplicity (D.fineOutput.fiber x) D.fineOutput.innerBody y : ℝ≥0)
          ≤ Cprop * μinner ∧
      μinner ≤ Cprop
          * (ShadedBody.pointwiseMultiplicity (D.fineOutput.fiber x) D.fineOutput.innerBody y : ℝ≥0)
  /-- **Fibre-cardinality comparability**: the refined fibres over selected cells have comparable
  cardinality, with the absolute constant `ShadedBody.factoringAndMultPropCombined.C`.

  **Provenance.**  This is *not* a consequence of Item 4.  Item 4 equalises the *pointwise
  multiplicity* of each refined fibre; converting that to a statement about how many tubes a fibre
  contains would additionally need the individual shade volumes and the fibre-union volumes to be
  comparable across cells, and neither is available.  What this field records is a proof-level
  output of Proposition 5.1: the construction pigeonholes the fine family so that the surviving
  fibres have comparable size, and it is that intermediate property — not one of the seven items
  stated in `Kakeya/Factoring/Multiplicity.lean` — which is being asserted here.  GWZ Remark 5.3
  preserves it, because the Remark-5.3 substitution replaces only the Frostman input to the
  pigeonholing, not the pigeonholing itself.

  It carries the absolute constant, so it is legitimate input for a constant that Proposition
  6.6(B) must fix before the configuration.  In particular it must not be restated with
  `Kakeya.remark53Const Cfib CF`: `Cfib` and `CF` are chosen after `Ccard`, and the public
  cardinality clause of `Kakeya.factoringAndMultPropGlobal` has no `δ`-power to absorb them into.

  Downstream this field is consumed only through
  `Kakeya.Section6PartBData.card_mul_card_fiber_le`, which turns it into
  `|𝒲'| · |𝒯_W| ≤ Ccard · |𝒯|` with no further loss. -/
  fiber_card_comparable : ∀ x ∈ D.fineOutput.outerSet, ∀ y ∈ D.fineOutput.outerSet,
    ((D.fineOutput.fiber x).card : ℝ≥0)
      ≤ Cprop * ((D.fineOutput.fiber y).card : ℝ≥0)
  /-- Item 5: the multiplicity split `μ(𝒯, Y) ≤ Csplit · μ(𝒲', Y_{𝒲'}) · μ(𝒯'_W, Y')`, for the
  **fine** family, on the representative planks.  This is the estimate Proposition 6.6(B) actually
  uses, and the reason Remark 5.3 is needed at all. -/
  split : ∀ x ∈ D.fineOutput.outerSet,
    ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
      ≤ (Cprop : ENNReal)
        * ShadedBody.multiplicity D.fineOutput.outerSet
            (fun y => (D.outerPlanks y).toShadedBody)
        * ShadedBody.multiplicity (D.fineOutput.fiber x) D.fineOutput.innerBody
  /-- Item 6: the pointwise shading containment, on the representative planks. -/
  shade_subset : ∀ i ∈ D.fineOutput.innerSet,
    (D.fineOutput.innerBody i).shade ⊆ (D.outerPlanks (D.cellOfFine i)).shade

/- **Retired unconditional Remark-5.3 constructor.**

There is intentionally no theorem manufacturing this Section 6 presentation package from the
canonical core alone.  The actual-body Remark-5.3 output is available from
`Kakeya.Section6PartBData.prop51CoreAtScaleOfRemark53`; representative-plank containment and the
cardinality comparison must be supplied by the Section 6 geometry. -/
-- There is intentionally no unconditional constructor for `Remark53Prop51`: representative-plank
-- containment and fibre-cardinality comparability are Section 6 presentation data, not outputs of
-- the canonical Proposition 5.1 core.

/-! ### The cardinality clause of Proposition 6.6(B)

`Kakeya.factoringAndMultPropGlobal` must produce `|𝒲'| · |𝒯_W| ≤ Ccard · |𝒯|` with `Ccard`
**absolute** — fixed before the configuration, hence before `Cfib` and `CF`.  The two lemmas below
reduce that clause to a single comparability statement about the refined fibres, so that whatever
has to be assumed about Proposition 5.1 is as small as possible.

The first is unconditional and constant-free: the refined fibres are disjoint and sit inside `𝒯`,
so their cardinalities sum to at most `|𝒯|`.  The second is the pigeonhole that turns fibre
comparability into the product bound.  Nothing here uses `Cfib`, `CF`, or any `δ`-power. -/

open Classical in
/-- **The refined fibres sum to at most the fine family, with no constant.**

The fibres of `Kakeya.Section6PartBData.fineOutput` over distinct cells are disjoint, and their
union is the refined inner set, which `Kakeya.Section6PartBData.Remark53Prop51.innerSet_eq` places
inside `q`. -/
theorem sum_card_fiber_le {Cprop : ℝ≥0} (hRem : D.Remark53Prop51 Cprop) :
    (∑ x ∈ D.fineOutput.outerSet, (D.fineOutput.fiber x).card) ≤ q.card := by
  classical
  have hsub : D.fineOutput.innerSet ⊆ q := by
    rw [hRem.innerSet_eq]
    exact Finset.filter_subset _ _
  have hkey : (∑ x ∈ D.fineOutput.outerSet, (D.fineOutput.fiber x).card)
      = ({i ∈ D.fineOutput.innerSet |
            D.fineOutput.parent i ∈ D.fineOutput.outerSet} : Finset ι).card := by
    exact Finset.sum_card_fiberwise_eq_card_filter (s := D.fineOutput.innerSet)
      (t := D.fineOutput.outerSet) (g := D.fineOutput.parent)
  rw [hkey]
  calc
    ({i ∈ D.fineOutput.innerSet |
        D.fineOutput.parent i ∈ D.fineOutput.outerSet} : Finset ι).card
        ≤ D.fineOutput.innerSet.card :=
          Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ q.card := Finset.card_le_card hsub

open Classical in
/-- **Fibre comparability gives the cardinality clause, with an absolute constant.**

If the selected fibre is no larger than `Ccard` times any other selected fibre, then
`|𝒲'| · |𝒯_{W₀}| ≤ Ccard · |𝒯|`.  This is pure pigeonhole on top of
`Kakeya.Section6PartBData.sum_card_fiber_le`: `Ccard` is whatever constant the comparability
hypothesis carries, and no further loss is incurred. -/
theorem card_mul_card_fiber_le {Cprop : ℝ≥0} (hRem : D.Remark53Prop51 Cprop)
    {Ccard : ℝ≥0}
    {x₀ : D.factor.Cell}
    (hcomp : ∀ y ∈ D.fineOutput.outerSet,
      ((D.fineOutput.fiber x₀).card : ℝ≥0) ≤ Ccard * ((D.fineOutput.fiber y).card : ℝ≥0)) :
    ((D.fineOutput.outerSet.card : ℝ≥0)) * ((D.fineOutput.fiber x₀).card : ℝ≥0)
      ≤ Ccard * (q.card : ℝ≥0) := by
  calc
    ((D.fineOutput.outerSet.card : ℝ≥0)) * ((D.fineOutput.fiber x₀).card : ℝ≥0)
        = ∑ y ∈ D.fineOutput.outerSet, ((D.fineOutput.fiber x₀).card : ℝ≥0) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ y ∈ D.fineOutput.outerSet,
          Ccard * ((D.fineOutput.fiber y).card : ℝ≥0) := by
          exact Finset.sum_le_sum hcomp
    _ = Ccard * ∑ y ∈ D.fineOutput.outerSet, ((D.fineOutput.fiber y).card : ℝ≥0) := by
          rw [Finset.mul_sum]
    _ ≤ Ccard * (q.card : ℝ≥0) := by
          have hsum : (∑ y ∈ D.fineOutput.outerSet,
              ((D.fineOutput.fiber y).card : ℝ≥0)) ≤ (q.card : ℝ≥0) := by
            rw [← Nat.cast_sum]
            exact_mod_cast D.sum_card_fiber_le hRem
          gcongr

open Classical in
/-- **At a selected cell the Proposition-5.1 fibre is the datum's own fine fibre.**

`D.fineOutput.fiber x` filters the *refined* inner set by parent, and by
`Kakeya.Section6PartBData.Remark53Prop51.innerSet_eq` that inner set is the fine tubes whose cell is
selected.  At a selected `x` the two filters collapse to the single condition `cellOfFine i = x`,
which is `Kakeya.Section6PartBData.fineFibre`.  This is what lets the inner half of 6.6(B) hand the
cellwise coarse-parent system (`Kakeya.Section6PartBData.coarseParentSystem`, stated on `fineFibre`)
to the Proposition-5.1 fibre. -/
theorem fineOutput_fiber_eq_fineFibre
    (hinnerSet : D.fineOutput.innerSet
      = ({i ∈ q | D.cellOfFine i ∈ D.fineOutput.outerSet} : Finset ι))
    {x : D.factor.Cell} (hx : x ∈ D.fineOutput.outerSet) :
    D.fineOutput.fiber x = D.fineFibre x := by
  ext i
  simp only [ShadedBody.ShadedFactorFamily.fiber, fineFibre, Finset.mem_filter]
  constructor
  · intro h
    constructor
    · rw [hinnerSet] at h
      exact (Finset.mem_filter.mp h.1).1
    · exact h.2
  · intro h
    constructor
    · rw [hinnerSet]
      exact Finset.mem_filter.mpr ⟨h.1, by rw [h.2]; exact hx⟩
    · exact h.2

/-- **On a selected cell the clipping removes nothing.**

The Proposition-5.1 shade lies in the `scale`-collar of the actual body, and `hcth` puts that
collar inside the representative plank.  So the outer view carries the Proposition-5.1 shade
verbatim, and every shade-only quantity transfers with no loss. -/
theorem shade_outerPlanks
    (hcth : ∀ y ∈ D.factor.cells,
      (D.factor.body y).cthickening ((D.factor.body y).scale)
        ≤ (D.factor.repr y).toConvexSpaceBody)
    {x : D.factor.Cell} (hx : x ∈ D.factor.cells)
    (hcar : (D.fineOutput.outerBody x).toConvexSpaceBody
      = (D.factor.body x).cthickening ((D.factor.body x).scale)) :
    (D.outerPlanks x).shade = (D.fineOutput.outerBody x).shade := by
  rw [D.shade_outerPlanks_eq x, Set.inter_eq_left]
  exact (D.fineOutput.outerBody x).shade_subset.trans (by
    rw [hcar]
    exact SetLike.coe_subset_coe.mpr (hcth x hx))

/-- The clipping is vacuous on the whole selected outer set. -/
theorem shade_outerPlanks_of_mem
    (hcth : ∀ y ∈ D.factor.cells,
      (D.factor.body y).cthickening ((D.factor.body y).scale)
        ≤ (D.factor.repr y).toConvexSpaceBody)
    (hsub : D.fineOutput.outerSet ⊆ D.factor.cells)
    (hcar : ∀ x ∈ D.fineOutput.outerSet, (D.fineOutput.outerBody x).toConvexSpaceBody
      = (D.factor.body x).cthickening ((D.factor.body x).scale)) :
    ∀ x ∈ D.fineOutput.outerSet, (D.outerPlanks x).shade = (D.fineOutput.outerBody x).shade :=
  fun x hx => D.shade_outerPlanks hcth (hsub hx) (hcar x hx)

/-- **Volume comparison between a representative plank and the Proposition-5.1 outer carrier.** -/
theorem volume_outerPlanks_le {Cdim : ℝ≥0}
    (hvol : ∀ y ∈ D.factor.cells,
      volume ((D.factor.repr y).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ≤ (Cdim : ENNReal) * volume (D.factor.body y).carrier)
    {x : D.factor.Cell} (hx : x ∈ D.factor.cells)
    (hcar : (D.fineOutput.outerBody x).toConvexSpaceBody
      = (D.factor.body x).cthickening ((D.factor.body x).scale)) :
    volume ((D.outerPlanks x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ (Cdim : ENNReal)
        * volume ((D.fineOutput.outerBody x).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  calc
    volume ((D.outerPlanks x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = volume ((D.factor.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3))) := rfl
    _ ≤ (Cdim : ENNReal) * volume ((D.factor.body x).carrier :
          Set (EuclideanSpace ℝ (Fin 3))) := hvol x hx
    _ ≤ (Cdim : ENNReal) * volume ((D.fineOutput.outerBody x).carrier :
          Set (EuclideanSpace ℝ (Fin 3))) := by
      gcongr
      calc
        ((D.factor.body x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            ⊆ (((D.factor.body x).cthickening ((D.factor.body x).scale)).carrier :
                Set (EuclideanSpace ℝ (Fin 3))) :=
          ConvexSpaceBody.self_le_cthickening (D.factor.body x) ((D.factor.body x).scale)
        _ = ((D.fineOutput.outerBody x).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
          simpa using congrArg ConvexSpaceBody.carrier hcar.symm

/-- **Fullness is transferred at the cost of the dimension-comparison constant `Cdim`** — the only
loss the reshaping incurs, and it is Definition-4.2 clause (4c), not an unavailable estimate. -/
theorem fullness'_outerPlanks {Cdim : ℝ≥0} (hCdim0 : Cdim ≠ 0)
    (hcth : ∀ y ∈ D.factor.cells,
      (D.factor.body y).cthickening ((D.factor.body y).scale)
        ≤ (D.factor.repr y).toConvexSpaceBody)
    (hvol : ∀ y ∈ D.factor.cells,
      volume ((D.factor.repr y).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ≤ (Cdim : ENNReal) * volume (D.factor.body y).carrier)
    (hsub : D.fineOutput.outerSet ⊆ D.factor.cells)
    (hcar : ∀ x ∈ D.fineOutput.outerSet, (D.fineOutput.outerBody x).toConvexSpaceBody
      = (D.factor.body x).cthickening ((D.factor.body x).scale)) :
    ShadedBody.fullness' D.fineOutput.outerSet D.fineOutput.outerBody
      ≤ (Cdim : ENNReal)
        * ShadedBody.fullness' D.fineOutput.outerSet
            (fun x => (D.outerPlanks x).toShadedBody) := by
  refine ShadedBody.fullness'_le_mul_fullness'_reshape _ _ _
    (fun x hx => (D.shade_outerPlanks_of_mem hcth hsub hcar x hx).symm)
    (by exact_mod_cast hCdim0) ENNReal.coe_ne_top ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x hx => D.volume_outerPlanks_le hvol (hsub hx) (hcar x hx)

/-! ## Nonemptiness, derived rather than assumed -/

/-- **The selected outer family is nonempty**, provided the fine family carries some shade.

Not an assumption: if `Kakeya.Section6PartBData.fineOutput`'s outer set were empty then, by
`Remark53Prop51.innerSet_eq`, the refined inner set would be empty too, and the mass half of the
`⪆ 1` refinement (`ShadedBody.IsCRefinement`, second component) would force
`C⁻¹ · ∑_{i ∈ q} |Y(T i)| ≤ 0`.  With `C = 1` that makes the total fine shade null, hence
`λ(𝒯, Y) = 0`, contradicting positivity of the fullness.

In Proposition 6.6(B) the hypothesis is supplied by `δ ^ η ≤ λ(𝒯, Y)` with `0 < δ`. -/
theorem fineOutput_outerSet_nonempty {Cprop : ℝ≥0} (hCprop : Cprop ≠ 0)
    (hRem53 : D.Remark53Prop51 Cprop)
    (hpos : 0 < ShadedBody.fullness q (fun i => (T i).toShadedBody)) :
    D.fineOutput.outerSet.Nonempty := by
  by_contra hne
  have houterEmpty : D.fineOutput.outerSet = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  have hinnerEmpty : D.fineOutput.innerSet = ∅ := by
    rw [hRem53.innerSet_eq]
    simp [houterEmpty]
  have hsum0 : (∑ i ∈ q, volume ((T i).toShadedBody).shade) = 0 := by
    have hle : ((Cprop⁻¹ : ℝ≥0) : ENNReal)
        * (∑ i ∈ q, volume ((T i).toShadedBody).shade)
        ≤ ∑ i ∈ D.fineOutput.innerSet, volume (D.fineOutput.innerBody i).shade :=
      hRem53.refinement.2
    rw [hinnerEmpty] at hle
    have hprod : ((Cprop⁻¹ : ℝ≥0) : ENNReal)
        * (∑ i ∈ q, volume ((T i).toShadedBody).shade) = 0 :=
      le_antisymm hle zero_le
    exact (mul_eq_zero.mp hprod).resolve_left (by exact_mod_cast inv_ne_zero hCprop)
  have hfull0 : (ShadedBody.fullness q (fun i => (T i).toShadedBody) : ENNReal) = 0 := by
    rw [ShadedBody.fullness_def]
    rw [hsum0]
    simp
  have hfull0nn : ShadedBody.fullness q (fun i => (T i).toShadedBody) = 0 :=
    ENNReal.coe_eq_zero.mp hfull0
  exact hpos.ne hfull0nn.symm

/-- **Every selected cell carries a refined fine tube**, provided the fine family has positive
multiplicity.

Not an assumption either: `Remark53Prop51.split` at a selected cell `x` bounds `μ(𝒯, Y)` by a
product one of whose factors is `μ(𝒯'_x, Y')`.  An empty fibre has zero multiplicity
(`ShadedBody.multiplicity_empty`), so an empty fibre at a selected cell would force
`μ(𝒯, Y) = 0`. -/
theorem fineOutput_fiber_nonempty {Cprop : ℝ≥0} (hRem53 : D.Remark53Prop51 Cprop)
    (hpos : 0 < ShadedBody.multiplicity q (fun i => (T i).toShadedBody))
    {x : D.factor.Cell} (hx : x ∈ D.fineOutput.outerSet) :
    (D.fineOutput.fiber x).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hsplit := hRem53.split x hx
  rw [hempty, ShadedBody.multiplicity_empty, mul_zero] at hsplit
  exact absurd hsplit (not_le.mpr hpos)

/-- **Every selected cell carries a coarse tube.**

This is the input `Kakeya.Section6PartBFactorisation.isKatzTao_repr_of_subset` needs, and it is
derived, not assumed: a selected cell has a refined fine tube `i` by
`Kakeya.Section6PartBData.fineOutput_fiber_nonempty`, that `i` lies in `q` and has
`D.cellOfFine i = x`, and its coarse parent `D.decomp.assign i` then lies in
`D.factor.coarseFibre x` by `Kakeya.Section6PartBData.assign_mem_coarseFibre`. -/
theorem coarseFibre_nonempty_of_mem_outerSet {Cprop : ℝ≥0}
    (hRem53 : D.Remark53Prop51 Cprop)
    (hpos : 0 < ShadedBody.multiplicity q (fun i => (T i).toShadedBody))
    {x : D.factor.Cell} (hx : x ∈ D.fineOutput.outerSet) :
    (D.factor.coarseFibre x).Nonempty := by
  rcases D.fineOutput_fiber_nonempty hRem53 hpos hx with ⟨i, hi⟩
  refine ⟨D.decomp.assign i, D.assign_mem_coarseFibre ?_⟩
  rw [D.mem_fineFibre_iff]
  have hi_inner : i ∈ D.fineOutput.innerSet := (Finset.mem_filter.mp hi).1
  constructor
  · rw [hRem53.innerSet_eq] at hi_inner
    exact (Finset.mem_filter.mp hi_inner).1
  · change (D.fineOutput.parent) i = x
    exact (Finset.mem_filter.mp hi).2

end Section6PartBData

end Kakeya

end

end
