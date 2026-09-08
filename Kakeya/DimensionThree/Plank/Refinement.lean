/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.RepresentativeSelection
public import Kakeya.DimensionThree.Plank.ExponentBudget
public import Kakeya.DimensionThree.Plank.WindowPacking
public import Kakeya.DimensionThree.Plank.StrongRefinementCoefficient
public import Kakeya.DimensionThree.Plank.RelativeMultiplicity
public import Kakeya.DimensionThree.Plank.TypicalAngleIncidence

/-!
# The refinement and typical-angle outputs of `Kakeya.plankReduction`

This file assembles, from the *public* hypotheses of `Kakeya.plankReduction` alone (windowed family,
pairwise essential distinctness, `a ^ η ≤ λ`, `a ^ (-η) ≤ μ`, `0 < a < 1`), the refinement block
of that theorem's conclusion: the plain refinement, the fullness retention and the typical-angle
clause, all with constants that are uniform in the configuration.  There is no small-scale
threshold: the chain runs at every `0 < a < 1`.

## The chain

The whole point is that the *strong* branch of `Kakeya.representativeWitness_strong_uniform`
is used, never the weak `a ^ (4 η)` clauses.  Those are polynomial in `η` and cannot produce a
loss of the shape `a ^ ε` with `ε` unrelated to `η`.  The route is:

1. `Plank.card_le_of_windowed_essentiallyDistinct_shaded` turns the windowed hypothesis into the
   plank-count bound `|s| ≤ Cwin · a ^ (-Dwin)` with `Cwin`, `Dwin` absolute.  This is the `hcard`
   input of GWZ Lemma 6.11.
2. `Kakeya.representativeWitness_strong_uniform` is invoked at the geometric constant
   `Cgeom = 1` and at the exponent `εangle + εrepr`.  Its statement is a *continuation*: the
   geometric constants and the
   reserve multiplier `kappa` are delivered first, and only afterwards are the typical-angle
   constants `Ctyp`, `Cuni` supplied.  That ordering is what breaks the circularity between the
   shared constant of Lemma 6.11 and `kappa`, which the witness returns and Lemma 6.11 consumes.
3. `Kakeya.findingTypicalAngleOfIntersection_stable_reserve` is then run at that very `kappa`, at
   the exponent `εangle`, with `C₀ = Cwin` and `Nexp = Dwin`.  It supplies the four
   angular hypotheses of the witness, and its own constant `C₆₁₁` is fed back as
   `Ctyp = Cuni = C₆₁₁`.  Carrying that constant instead of absorbing it
   (`Kakeya.absorb_const_of_eps_split`) is what removes the small-scale threshold.
4. `Kakeya.exists_absorb_strongRefinementCoeff` at the exponent `εsharp` replaces the polynomial
   branch `Cref⁻¹ · a ^ η · a ^ ε` of the strong refinement coefficient by
   `Cref'⁻¹ · a ^ εsharp · a ^ (εangle + εrepr)`, which is the only bound with no `a ^ η` in it.

`Kakeya.exponent_budget` records that the exponents used sum to at most the public `ε`.

## The cardinality clause

`Kakeya.card_le_of_isCRefinement_of_fullness` is the honest conversion of a mass refinement into a
cardinality bound: with all carriers of the same volume, `|s'| / |s| ≥ c · λ`, where `c` is the
retained mass fraction and `λ` the incoming fullness.  The factor `λ` is not an artefact of the
proof — it is an equality up to the fullness of the refined family, which is at most `1` — and it
is why the `cardinality` field of `Kakeya.ReductionData.PreassemblyResult` is stated at
`a ^ η · a ^ ε` rather than at `a ^ ε`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal Real

noncomputable section

namespace Kakeya

variable {ι : Type*}

/-- **A mass refinement is a cardinality refinement, up to the incoming fullness.**

If every carrier of the original family has volume at least `v`, every retained shading has volume
at most `v`, and `(s', V')` retains a `c`-fraction of the mass of `(s, V)` whose fullness is at
least `lam`, then `c · lam · |s| ≤ |s'|`.

The chain is `c · lam · |s| · v ≤ c · ∑_s |Y| ≤ ∑_{s'} |Y'| ≤ |s'| · v`.  The factor `lam` cannot
be removed: the middle inequality is the only information available about `s'`, and the mass of a
family of `|s'|` bodies of carrier volume `v` is at most `|s'| · v`, attained when the retained
family is full. -/
theorem card_le_of_isCRefinement_of_fullness
    {s' s : Finset ι} {V' V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {c lam : ℝ≥0} {v : ENNReal} (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (href : ShadedBody.IsCRefinement s' V' s V c)
    (hlam : lam ≤ ShadedBody.fullness s V)
    (hVlow : ∀ i ∈ s, v ≤ volume (V i).carrier)
    (hV'up : ∀ i ∈ s', volume (V' i).shade ≤ v) :
    (c * lam) * (s.card : ℝ≥0) ≤ (s'.card : ℝ≥0) := by
  -- Work in ENNReal, then cancel `v` and cast back to ℝ≥0.
  have key : v * (((c * lam : ℝ≥0) : ENNReal) * (s.card : ENNReal)) ≤ v * (s'.card : ENNReal) :=
    calc v * (((c * lam : ℝ≥0) : ENNReal) * (s.card : ENNReal))
        = (c : ENNReal) * ((lam : ENNReal) * ((s.card : ENNReal) * v)) := by push_cast; ring
      _ ≤ (c : ENNReal) * ∑ i ∈ s, volume (V i).shade :=
        mul_le_mul_right (ShadedBody.coe_fullness_mul_le_sum_volume_shade s V hlam hVlow) _
      _ ≤ ∑ i ∈ s', volume (V' i).shade := href.2
      _ ≤ v * (s'.card : ENNReal) := by simpa [mul_comm] using Finset.sum_le_sum hV'up
  exact_mod_cast (ENNReal.mul_le_mul_iff_right hv0 hvtop).mp key

namespace ReductionData

/-- **The absolute geometric constant block of the preassembly.**

The eight constants of GWZ Lemma 6.13 that are produced *before* the sub-polynomial exponents `η`
and `ε` and before every geometric datum, together with their validity inequalities.  They come from
`Kakeya.representativeWitness_strong_uniform` at `Cgeom = 1`: `cThk` from
`Plank.exists_thickenedRepr`, `cOv`/`Cset`/`Cang` from `Plank.slabMassDecomposition`, `Nov` from
`Plank.slab_pointwise_overlap_le`, `cN` from the dyadic fibre pigeonhole, and
`Cang2`/`Ccarrier` from the angle-widening and carrier-dilation bookkeeping.

Bundling them is what lets `ShadedPlank.reduction_to_slab` fix its public `cN := 2` and
`Cbox := Kakeya.plankReduction.boxDilation Cang2 Ccarrier` before `η` and `ε` enter: the whole
block is one value, and consumers read it by field name instead of by position in a thirteen-fold
conjunction. -/
structure GeomConstants where
  /-- Dilation constant of the thickened-representative containments. -/
  cThk : ℝ≥0
  /-- Set-comparability constant of the controlled slab family `Plank.inSlabFamilyC`. -/
  Cset : ℝ≥0
  /-- Angle-comparability constant of the controlled slab family. -/
  Cang : ℝ≥0
  /-- Widened angle constant at which the typed anchor prisms meet their slabs. -/
  Cang2 : ℝ≥0
  /-- Bounded-overlap constant of the slab mass decomposition. -/
  cOv : ℝ≥0
  /-- Two-sided fibre-size constant of the dyadic pigeonhole (the literal `2`). -/
  cN : ℝ≥0
  /-- Dilation at which the anchor carriers contain the shadings. -/
  Ccarrier : ℝ≥0
  /-- Pointwise slab-overlap multiplicity. -/
  Nov : ℕ
  one_le_cThk : 1 ≤ cThk
  one_le_Cset : 1 ≤ Cset
  one_le_Cang : 1 ≤ Cang
  one_le_Cang2 : 1 ≤ Cang2
  Cang_le_Cang2 : Cang ≤ Cang2
  one_le_Nov : 1 ≤ Nov
  cOv_pos : 0 < cOv
  one_le_cN : 1 ≤ cN
  cN_le_two : cN ≤ 2
  one_le_Ccarrier : 1 ≤ Ccarrier
  cThk_le_Ccarrier : cThk ≤ Ccarrier
  four_Cang_le_Ccarrier : 4 * Cang + 8 ≤ Ccarrier
  four_Cang2_le_Ccarrier : 4 * Cang2 + 8 ≤ Ccarrier

/-- **The `η`- and `ε`-dependent analytic constant block of the preassembly.**

The constants the preassembly produces once the sub-polynomial exponents are fixed, together with
the internal rate `εint` at which the structural clauses are delivered and the exponent budget
`4 · εint = ε` tying it to the public `ε`.  Unlike `Kakeya.ReductionData.GeomConstants` these
genuinely depend on the exponents: `Cθ` is the typical-angle constant of GWZ Lemma 6.11, `cEta`
and `Cres` the polynomial and sharp branches of the pigeonhole retention, `Cref` the
strong-refinement constant, and
`cP`/`cLam` the public cardinality and fullness constants. -/
structure AnalyticConstants (ε : ℝ) where
  /-- Public cardinality-retention constant. -/
  cP : ℝ≥0
  /-- Public fullness-retention constant. -/
  cLam : ℝ≥0
  /-- Typical-angle comparability constant of GWZ Lemma 6.11. -/
  Cθ : ℝ≥0
  /-- Strong-refinement-coefficient constant. -/
  Cref : ℝ≥0
  /-- Polynomial branch of the fibre-size pigeonhole retention. -/
  cEta : ℝ≥0
  /-- Sharp branch of the fibre-size pigeonhole retention. -/
  Cres : ℝ≥0
  /-- Relative constant-multiplicity constant of the output family. -/
  Cmult : ℝ≥0
  /-- Internal sub-polynomial rate at which the structural clauses are delivered. -/
  εint : ℝ
  cP_pos : 0 < cP
  cLam_pos : 0 < cLam
  one_le_Cθ : 1 ≤ Cθ
  Cmult_pos : 0 < Cmult
  one_le_Cref : 1 ≤ Cref
  cEta_pos : 0 < cEta
  Cres_pos : 0 < Cres
  εint_pos : 0 < εint
  four_εint : 4 * εint = ε

open scoped Classical in
/-- **The configuration-dependent output of the preassembly, on one pair `(s', Y')`.**

Everything `Kakeya.refinement_preassembly_uniform` produces once the configuration
`(ι, s, a, b, Y)` and the exponents are fixed: the retained family, the typical angle, the thickened
representatives, the slab assignment, the pigeonhole scalars, the anchor/carrier data, the typed
anchor prisms, and every invariant relating them.  Named fields replace what used to be a
forty-eight-fold positional conjunction, so inserting or renaming one invariant touches the producer
and only the consumers that mention that field, instead of forcing synchronized positional edits
everywhere.

The record carries data (`s'`, `Y'`, `R`, …), so it lives in `Type`; the theorem that produces it
concludes `Nonempty (PreassemblyResult …)`, which is the `Prop`-level existential wrapper.  Nothing
here is ever computed with.

*Classical scope.*  The declaration sits under `open scoped Classical in` purely so that the
`Finset.filter` and `Finset.image` appearing in `fibreCardinality`, `slabMembership`,
`slabOverlapMass` and `pointwiseSlabOverlap` elaborate: `Slab θ hθ1` and
`Plank.ThickenedPlank θ b hθ1 hb1` carry no `DecidableEq` instance, and adding a global one for
these geometric types would be the wrong fix for what is only a finite-set elaboration detail.  The
result is existential and noncomputational, so the classical choice is invisible downstream.

*Reconstructible data is not stored.*  The representative map, the active representative family and
the active slab family are `R.repr`, `R.indexSet` and `R.indexSet.image slabOf`; the old output
returned each of them as a separate witness together with an equation pinning it, and every consumer
immediately substituted the equations away.  They are used as projections here instead, which also
makes the old clause `𝒯 = s'.image repr` disappear — it is `Plank.ThickenedRepr.indexSet` unfolded.
Validity properties of the two constant blocks stay in `G` and `A` and are not duplicated.

Field order follows the conjunction this record replaces, so the producer's anonymous constructor
and the invariant proofs it feeds in did not have to be reordered.  Downstream code must not depend
on that order. -/
structure PreassemblyResult (G : GeomConstants) {ε : ℝ} (A : AnalyticConstants ε)
    {ι : Type*} (s : Finset ι) {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (Y : ι → ShadedPlank a b hab hb1) (η : ℝ) where
  /-- The retained index set. -/
  s' : Finset ι
  /-- The output shading family. -/
  Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))
  /-- The typical angle. -/
  θ : ℝ≥0
  /-- The typical angle is at most `1`. -/
  hθ1 : θ ≤ 1
  /-- The common representative fibre size. -/
  N : ℕ
  /-- The thickened representatives of the retained planks.  `R.repr` is the representative map and
  `R.indexSet` the active representative family. -/
  R : Plank.ThickenedRepr s' (ShadedPlank.planks Y) θ hθ1 G.cThk
  /-- The canonical slab assignment on representatives. -/
  slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1
  /-- The strong (mass) refinement coefficient. -/
  rRef : ℝ≥0
  /-- Retained fraction of the fibre-size pigeonhole. -/
  cGood : ℝ≥0
  /-- Threshold of the good-point deletion. -/
  q : ℝ≥0
  /-- Refinement coefficient of the incoming typical-angle step. -/
  cAngle : ℝ≥0
  /-- The anchor/carrier data of the active representatives. -/
  acd : Plank.ThickenedAnchorCarrierData (Plank.ThickenedPlank θ b hθ1 hb1)
    s' Y' G.Ccarrier G.cN N
  /-- The typed anchor prisms of the active representatives. -/
  Pr : Plank.ThickenedPlank θ b hθ1 hb1 →
    Prism3D (θ * b) b 1 (Plank.thickenedWidth_le hθ1) hb1
  -- the four public refinement outputs
  /-- The retained index set sits inside the original one. -/
  subset : s' ⊆ s
  /-- The typical angle is at least the plank eccentricity. -/
  θ_lb : a / b ≤ θ
  /-- The output family refines the original one. -/
  isRefinement : ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y)
  /-- Public fullness retention. -/
  fullness : (A.cLam * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
    ShadedBody.fullness s' Y'
  /-- Public two-sided typical angle, at the polynomial rate `ε`. -/
  typicalAngle : IsTypicalPlankAngle s' Y' (ShadedPlank.planks Y) θ (A.Cθ * a ^ (-ε))
    (Real.toNNReal (plankAngleScaleA a))
  /-- Public cardinality retention. -/
  cardinality : ((A.cP * a ^ η) * a ^ ε) * (s.card : ℝ≥0) ≤ (s'.card : ℝ≥0)
  -- the structural package, at the internal rate `A.εint`
  /-- Each output shading sits in its plank. -/
  shade_subset_plank : ∀ i ∈ s', (Y' i).shade ⊆ ((ShadedPlank.planks Y i).carrier :
    Set (EuclideanSpace ℝ (Fin 3)))
  /-- Each output carrier is its plank. -/
  carrier_eq_plank : ∀ i ∈ s', (Y' i).carrier = ((ShadedPlank.planks Y i).carrier :
    Set (EuclideanSpace ℝ (Fin 3)))
  /-- One-sided max plank angle at the typical-angle constant. -/
  maxAngle : HasMaxPlankAngleBound s' Y' (ShadedPlank.planks Y) θ A.Cθ
  /-- Two-sided typical angle at the internal rate, at the output scale. -/
  typicalAngle_out : IsTypicalPlankAngle s' Y' (ShadedPlank.planks Y) θ (A.Cθ * a ^ (-A.εint))
    (Real.toNNReal (max 2 (plankAngleScaleA a)))
  /-- The common fibre size is positive. -/
  one_le_N : 1 ≤ N
  /-- The typical angle is positive. -/
  θ_pos : 0 < θ
  /-- The active representatives are pairwise essentially distinct. -/
  indexSet_pairwise : ((↑R.indexSet : Set (Plank.ThickenedPlank θ b hθ1 hb1)).Pairwise
    (fun t u => PrismNDim.IsEssentiallyDistinct t.toPrismNDim u.toPrismNDim))
  /-- The active slabs are pairwise essentially distinct. -/
  slabFamily_pairwise : ((↑(R.indexSet.image slabOf) : Set (Slab θ hθ1)).Pairwise
    (fun S S' => PrismNDim.IsEssentiallyDistinct S.toPrismNDim S'.toPrismNDim))
  /-- Every retained index lies in the controlled slab family of its representative's slab. -/
  slabMembership : ∀ i ∈ s', slabOf (R.repr i) ∈ R.indexSet.image slabOf ∧
    i ∈ Plank.inSlabFamilyC G.Cset G.Cang s' (ShadedPlank.planks Y) (slabOf (R.repr i))
  /-- Bounded-overlap aggregate slab mass comparison. -/
  slabOverlapMass : (G.cOv : ENNReal) *
      (∑ S ∈ R.indexSet.image slabOf, volume (⋃ i ∈ Plank.inSlabFamilyC G.Cset G.Cang s'
        (ShadedPlank.planks Y) S, (Y' i).shade)) ≤
    volume (⋃ i ∈ s', (Y' i).shade)
  /-- Two-sided representative fibre cardinality, unconditional on the active family. -/
  fibreCardinality : ∀ t ∈ R.indexSet, (s'.filter (fun i => R.repr i = t)).Nonempty ∧
    (N : ℝ) / (G.cN : ℝ) ≤ ((s'.filter (fun i => R.repr i = t)).card : ℝ) ∧
      ((s'.filter (fun i => R.repr i = t)).card : ℝ) ≤ (G.cN : ℝ) * (N : ℝ)
  rRef_pos : 0 < rRef
  rRef_eq : rRef = (cGood - q) * cAngle
  q_eq : q = cGood / 2
  cGood_pos : 0 < cGood
  q_pos : 0 < q
  cAngle_pos : 0 < cAngle
  cAngle_lb : A.Cθ⁻¹ * a ^ A.εint ≤ cAngle
  /-- Polynomial lower bound on the strong refinement coefficient. -/
  rRef_lb : A.Cref⁻¹ * a ^ η * a ^ A.εint ≤ rRef
  /-- Fullness retention at the strong coefficient. -/
  rRef_fullness : rRef * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
    ShadedBody.fullness s' Y'
  /-- Polynomial branch of the pigeonhole retention. -/
  cGood_poly : A.cEta * a ^ η ≤ cGood
  /-- Sharp branch of the pigeonhole retention; the only one the reserve scale can absorb. -/
  cGood_sharp : (A.Cres * Real.toNNReal (plankAngleScaleA a))⁻¹ ≤ cGood
  /-- Each output shading sits in the dilated anchor carrier of its representative. -/
  shade_subset_anchor : ∀ i ∈ s', (Y' i).shade ⊆
    (((R.repr i).toPrismNDim.dilation G.Ccarrier).carrier :
      Set (EuclideanSpace ℝ (Fin 3)))
  /-- Exact volume of an active representative. -/
  volume_active : ∀ t ∈ R.indexSet, volume (t.carrier : Set (EuclideanSpace ℝ (Fin 3)))
    = 8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal)
  /-- Carrier-volume floor for the dilated anchors. -/
  volume_anchor_lb : ∀ t ∈ R.indexSet,
    ((θ * b / a : ℝ≥0) : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))
    ≤ volume ((t.toPrismNDim.dilation G.Ccarrier).carrier :
      Set (EuclideanSpace ℝ (Fin 3)))
  acd_repr : acd.repr = R.repr
  acd_active : acd.active = R.indexSet
  acd_anchor : acd.anchor = (fun t => (t : Plank.ThickenedPlank θ b hθ1 hb1).toPrismNDim)
  acd_carrier : acd.carrier =
    (fun t => (t : Plank.ThickenedPlank θ b hθ1 hb1).toPrismNDim.dilation G.Ccarrier)
  /-- The typed anchor prisms realise the representatives. -/
  Pr_toPrismNDim : ∀ t ∈ R.indexSet, (Pr t).toPrismNDim = t.toPrismNDim
  /-- Representative-to-own-slab angle bound at the absolute constant `G.Cang2`. -/
  reprAngle_own : ∀ i ∈ s', Prism3D.angle (Pr (R.repr i)) (slabOf (R.repr i))
    ≤ (G.Cang2 : ℝ) * (θ : ℝ)
  /-- Pointwise slab-overlap bound. -/
  pointwiseSlabOverlap : ∀ x : EuclideanSpace ℝ (Fin 3),
    ((R.indexSet.image slabOf).filter fun S => x ∈ ⋃ i ∈ Plank.inSlabFamilyC G.Cset G.Cang s'
      (ShadedPlank.planks Y) S, (Y' i).shade).card ≤ G.Nov
  /-- Representative-to-arbitrary-slab angle comparison. -/
  reprAngle_any : ∀ (S : Slab θ hθ1), ∀ i ∈ s', Prism3D.angle (Pr (R.repr i)) S
    ≤ 2 * Prism3D.angle (ShadedPlank.planks Y i) S + 16 * (θ : ℝ)
  /-- Relative constant multiplicity of the output family, at a uniform constant times a declared
  *sub-polynomial* power of `a`; this is what makes the retained-mass half of Item 1
  (`Plank.isCRefinement_restrictShade_of_dense`) callable on `(s', Y')`.  The rate is `A.εint`
  alone: the `a ^ (-η)` the polynomial pigeonhole branch would cost is avoided by absorbing
  `cGood_sharp` instead. -/
  constantMultiplicity : ShadedBody.HasCConstantMultiplicity s' Y' (A.Cmult * a ^ (-A.εint))
  /-- Two-sided typical angle with the overlap multiplier `G.Nov` still in reserve for the later
  dominant-slab deletion. -/
  typicalAngle_reserve : IsTypicalPlankAngle s' Y' (ShadedPlank.planks Y) θ (A.Cθ * a ^ (-A.εint))
    (Real.toNNReal ((G.Nov : ℝ) * max 2 (plankAngleScaleA a)))
  /-- The refinement ledger in *mass* form.  The plain `isRefinement` clause loses the retained
  fraction, and `cardinality` has already spent it.  A later prune of `s'` must compose with this
  via `ShadedBody.IsCRefinement.trans` and convert to a count exactly once, at the very end;
  converting twice would charge `a ^ η` twice and break `cardinality` (see
  `Plank.exists_goodSlabPrune`). -/
  isCRefinement : ShadedBody.IsCRefinement s' Y' s (ShadedPlank.bodies Y) rRef
  /-- The **stop-scale** one-sided stability clause, transported onto the actual output `(s', Y')`.
  GWZ Lemma 6.11 states it on its own intermediate shading; the witness's good-point deletion is
  paid for out of the reserve, so `Kakeya.stopScaleStability_of_fibreRetention` moves the clause to
  `(s', Y')` at the scale `G.Nov · max 2 A(a)` with the angular constant `2 · plankAngleScaleB a`
  untouched.  This is the input the assigned-family local angle concentration of Item 2 consumes;
  the polynomial `IsTypicalPlankAngle` clauses are strictly weaker at the stop scale. -/
  stopScaleStability : ∀ x ∈ ⋃ i ∈ s', (Y' i).shade, ∀ t ⊆ shadeFibre s' Y' x,
    ((G.Nov : ℝ) * max 2 (plankAngleScaleA a))⁻¹ * ((shadeFibre s' Y' x).card : ℝ)
        ≤ (t.card : ℝ) →
      (θ : ℝ) ≤ 2 * plankAngleScaleB a
        * ((maxPlankAngle (ShadedPlank.planks Y) t : ℝ≥0) : ℝ)
  /-- One-sided max plank angle at the *absolute* geometric constant `1`, the form the strong
  witness actually proves.  The `A.Cθ`-widened `maxAngle` is what old consumers use, but `A.Cθ` is
  `ε`-dependent and therefore incomparable with the absolute `G.Cang2` at which the assigned Item 2
  route states its own max-angle hypothesis; only this clause can be widened to `G.Cang2`. -/
  maxAngle_one : HasMaxPlankAngleBound s' Y' (ShadedPlank.planks Y) θ 1

end ReductionData

open scoped Classical in
/-- **The consolidated preassembly for `Kakeya.plankReduction`.**

One invocation returns, on a *single* pair `(s', Y')`, both the four public refinement outputs and
the whole structural package of `Kakeya.representativeWitness_strong_uniform`: the fibre size
`N`, the angle `θ`, the `Plank.ThickenedRepr` `R`, the concrete slab assignment `slabOf`, the strong
refinement coefficient `rRef` with its pigeonhole data `cGood`, `q`, the anchor/carrier data `acd`,
the typed anchor prisms `Pr`, and every containment, packing and mass clause relating them.

This exists so that the final assembly never has to invoke several independent existential theorems
and then *assume* their witnesses coincide.  The internal sub-polynomial rate at which the
structural clauses are delivered is returned explicitly as `εint`, together with `4 * εint = ε`, so
that a caller can see the exponent budget rather than take it on trust.

The package keeps both typical-angle scales: the original `max 2 A(a)` clause and the stronger
`Nov · max 2 A(a)` reserve clause.  Thus old consumers remain source-compatible at the logical
level, while the later dominant-slab deletion can spend the pointwise overlap factor `Nov`.

`a₀`, the constants, and `εint` are all bound before the index type `ι` and before `s`, `a`, `b`
and `Y`, so they are uniform in the configuration. -/
theorem refinement_preassembly_uniform :
    ∃ G : ReductionData.GeomConstants, ∀ {η ε : ℝ}, 0 < η → 0 < ε →
      ∃ A : ReductionData.AnalyticConstants ε,
    ∀ {ι : Type*} (s : Finset ι) {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1),
      0 < a → a < 1 →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      (s : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (Y i).carrier (Y j).carrier) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      Nonempty (ReductionData.PreassemblyResult G A s Y η) := by
  -- 1. plank count (absolute constants)
  obtain ⟨Cwin, Dwin, hCwin, hDwin, hcount⟩ :=
    Plank.card_le_of_windowed_essentiallyDistinct_shaded
  -- 2. the *absolute* geometric block of the strong witness, at Cgeom := 1.  None of these
  -- constants sees `η` or `ε`, which is exactly why they can be published before them.
  obtain ⟨cThk, Cset, Cang, Cang2, cOv, cN, Ccarrier, Nov,
      h1cThk, h1Cset, h1Cang, h1Cang2, hCang_le_Cang2, h1Nov, h0cOv, h1cN, hcNle2,
      h1Ccarrier, hcThk_le_Ccarrier, h4Cang, h4Cang2, h4Ctheta, h4Ctheta2, hUni⟩ :=
    representativeWitness_strong_uniform (1 : ℝ≥0)
  refine ⟨⟨cThk, Cset, Cang, Cang2, cOv, cN, Ccarrier, Nov,
    h1cThk, h1Cset, h1Cang, h1Cang2, hCang_le_Cang2, h1Nov, h0cOv, h1cN, hcNle2,
    h1Ccarrier, hcThk_le_Ccarrier, h4Cang, h4Cang2⟩, ?_⟩
  intro η ε hη hε
  -- 0. epsilon split
  set ea : ℝ := ε/8 with hea_def
  set er : ℝ := ε/8 with her_def
  set es : ℝ := ε/8 with hes_def
  set ew : ℝ := ea + er with hew_def
  obtain ⟨hea_pos, her_pos, hes_pos, -, -, -, -, hew_pos, -, -⟩ :=
    exponent_budget hε rfl rfl rfl rfl rfl rfl
  -- 2'. the `η`-dependent pigeonhole constants and the reserve multiplier, at exponent ew.  The
  -- typical-angle constants are supplied afterwards, so `kappa` is available first.
  obtain ⟨cEta, Cres, kappa, h0cEta, hCres, hkappa1, hkappaNov, hWScont⟩ :=
    hUni (η := η) (ε := ew) hη hew_pos
  -- 3. GWZ Lemma 6.11 at the RESERVE scale, at that very kappa, exponent ea
  obtain ⟨C611, hC611two, h611⟩ :=
    findingTypicalAngleOfIntersection_stable_reserve hkappa1 hea_pos Cwin Dwin
  have hC611one : (1 : ℝ≥0) ≤ C611 := le_trans one_le_two hC611two
  -- 4. the configuration half of the strong witness, at Ctyp = Cuni = C611.  Taking the
  -- typical-angle constant of 6.11 itself as the witness's uniform constant is what removes
  -- the small-scale threshold: no absorption `C611 ≤ a ^ (-er)` is needed anywhere.
  obtain ⟨cP, cLam, Cref, h0cP, h0cLam, h1Cref, hWS⟩ := hWScont C611 C611 hC611one
  -- 5. sharp absorption of the strong refinement coefficient, at exponent es, Cuni := 1
  obtain ⟨Cref', hCref'1, habs⟩ :=
    exists_absorb_strongRefinementCoeff hes_pos hCres hC611one
  -- 6. sharp absorption of the dyadic pigeonhole loss, at the internal rate ew.  This is the
  -- branch that keeps the constant-multiplicity output free of any `a ^ (-η)`: it uses the
  -- sharp estimate `(Cres · A(a))⁻¹ ≤ cGood`, never the polynomial `cEta · a ^ η ≤ cGood`.
  obtain ⟨Cabs, hCabs_pos, hCabsSharp⟩ := exists_absorb_sharp_pigeonhole hew_pos hCres
  have hCref'_inv_pos : 0 < Cref'⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hCref'1)
  refine ⟨⟨Cref'⁻¹, Cref'⁻¹, C611, Cref, cEta, Cres,
    2 * Cabs * C611, ew,
    hCref'_inv_pos, hCref'_inv_pos, hC611one,
    mul_pos (mul_pos two_pos hCabs_pos) (zero_lt_one.trans_le hC611one),
    h1Cref, h0cEta, hCres,
    hew_pos, by rw [hew_def, hea_def, her_def]; ring⟩, ?_⟩
  intro ι s a b hab hb1 Y ha0 ha1 hwin hED hfull hmult
  have ha1' : (a : ℝ) < 1 := ha1
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  -- Step A: run Lemma 6.11
  have hED' : (s : Set ι).Pairwise
      (fun i j => _root_.IsEssentiallyDistinct
        ((ShadedPlank.planks Y i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ((ShadedPlank.planks Y j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
    simpa [ShadedPlank.planks_carrier] using hED
  obtain ⟨Y1, θ, href1, hθlb, hθ1, hconst, _hangle, hstab, hstop, hmax⟩ :=
    h611 s (ShadedPlank.bodies Y) (a := a) (b := b)
      ha0 ha1 hab hb1 (ShadedPlank.planks Y)
      (fun i hi => (Y i).shade_subset_plank) hη hmult
      (hcount s Y ha0 hwin hED)
  -- Step B: the two absorptions
  set cAngle := C611⁻¹ * a ^ ea
  have hcAnglePos : 0 < cAngle :=
    mul_pos (inv_pos.mpr (zero_lt_one.trans_le hC611one)) (NNReal.rpow_pos ha0)
  have ha0_ne : (a : ℝ≥0) ≠ 0 := ha0.ne'
  -- The two absorptions of the 6.11 constant, threshold-free: `C611` is carried as the
  -- witness's own uniform constant rather than dominated by a power of `a`.
  obtain ⟨hcAngleLB, hCle⟩ := absorb_const_of_eps_split C611 ha0 ha1 her_pos hew_def
  -- Convert hstab to the form the witness expects
  have hstab' := reserveStability_mono_const (P := ShadedPlank.planks Y) hCle hstab
  have hshadeP : ∀ i ∈ s, (Y1 i).shade ⊆
      ((ShadedPlank.planks Y i).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    fun i hi => ((href1.1.2 i hi).2).trans (Y i).shade_subset_plank
  -- The carrier of a refined body is the carrier of the original one; this identification feeds
  -- the two volume bounds and the `carrier_eq_plank` clause.
  have hcar1 : ∀ i ∈ s, (Y1 i).carrier = (Y i).carrier := by
    intro i hi
    calc (Y1 i).carrier = ((Y1 i).toConvexSpaceBody).carrier := rfl
      _ = (((ShadedPlank.bodies Y) i).toConvexSpaceBody).carrier := by rw [(href1.1.2 i hi).1]
      _ = ((Y i).toShadedBody).carrier := rfl
      _ = (Y i).carrier := by simp
  have hcarvol : ∀ i ∈ s, 8 * (a : ENNReal) * (b : ENNReal) ≤ volume (Y1 i).carrier := by
    intro i hi
    rw [hcar1 i hi]
    exact (ShadedPlank.volume_carrier (Y i)).ge
  -- Step C: apply the strong witness
  obtain ⟨s2, Y2, N, T, repr, slabOf, SS, rRef, cGood, q, acd, Pr, Rthk, hW⟩ :=
    hWS s (ShadedPlank.bodies Y) Y1 (a := a) (b := b) (hab := hab) (hb1 := hb1)
      (ShadedPlank.planks Y) θ hθ1 cAngle (a ^ η)
      ha0 ha1 hED' hcAnglePos hcAngleLB href1 hθlb hmax hstab'
      hshadeP (NNReal.rpow_pos ha0) le_rfl hfull hcarvol
  -- Destructure the strong witness, including its final reserve-scale angle clause.
  -- `_hW10` is the witness's `T = s2.image repr`; it is `Plank.ThickenedRepr.indexSet` unfolded, so
  -- the record derives the active family as `R.indexSet` instead of storing the equation.
  rcases hW with ⟨hW1, hW2, hW3, hW4, hW5, hW6, hW7, hW8, hW9, _hW10, hW11, hW12, hW13, hW14,
    hW15, hW16, hW17, hW18, hW19, hW20, hW21, hW22, hW23, hW24, hW25, hW26, hW27, hW28, hW29,
    hW30, hW31, hW32, hW33, hW34, hW35, hW36, hW37, hW38, hW39, hW40, hW41, hW42, hW43⟩
  -- Step D: the four conclusions
  -- 1. Fullness: the strong coefficient `rRef` dominates `Cref'⁻¹ * a ^ ε`
  have h_Cref'_eps_le_rRef : Cref'⁻¹ * a ^ ε ≤ rRef :=
    calc Cref'⁻¹ * a ^ ε ≤ Cref'⁻¹ * (a ^ es * a ^ ew) :=
          mul_le_mul_of_nonneg_left
            ((NNReal.rpow_le_rpow_of_exponent_ge ha0 ha1.le (by linarith)).trans_eq
              (NNReal.rpow_add ha0_ne es ew)) zero_le
      _ = Cref'⁻¹ * a ^ es * a ^ ew := (mul_assoc _ _ _).symm
      _ ≤ rRef := habs ha0 ha1' hW24 hW20 hW28 hcAngleLB
  have hfullness : (Cref'⁻¹ * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
      ShadedBody.fullness s2 Y2 :=
    (mul_le_mul_of_nonneg_right h_Cref'_eps_le_rRef zero_le).trans hW23
  -- 2. Typical angle
  have htypical : IsTypicalPlankAngle s2 Y2 (ShadedPlank.planks Y) θ (C611 * a ^ (-ε))
      (Real.toNNReal (plankAngleScaleA a)) := by
    have hwiden : C611 * a ^ (-ew) ≤ C611 * a ^ (-ε) :=
      mul_le_mul_of_nonneg_left
        (NNReal.rpow_le_rpow_of_exponent_ge ha0 ha1.le (by linarith)) zero_le
    exact (hW8.mono_const hwiden).mono_scale (Real.toNNReal_pos.mpr (Real.exp_pos _))
      (Real.toNNReal_le_toNNReal (le_max_right _ _))
  -- the carrier of an output body is the carrier of the incoming one
  have hcar2 : ∀ i, (Y2 i).carrier = (Y1 i).carrier := fun i => by
    show ((Y2 i).toConvexSpaceBody).carrier = ((Y1 i).toConvexSpaceBody).carrier
    rw [hW2 i]
  -- 3. Cardinality: ((Cref'⁻¹ * a ^ η) * a ^ ε) * (s.card : ℝ≥0) ≤ (s2.card : ℝ≥0)
  have hcardinality : ((Cref'⁻¹ * a ^ η) * a ^ ε) * (s.card : ℝ≥0) ≤ (s2.card : ℝ≥0) := by
    have hV'up : ∀ i ∈ s2, volume (Y2 i).shade ≤ 8 * (a : ENNReal) * (b : ENNReal) := by
      intro i hi
      calc volume (Y2 i).shade ≤ volume (Y2 i).carrier := measure_mono (Y2 i).shade_subset
        _ = 8 * (a : ENNReal) * (b : ENNReal) := by
          rw [hcar2 i, hcar1 i (hW1 hi)]; exact ShadedPlank.volume_carrier (Y i)
    have hcard := card_le_of_isCRefinement_of_fullness
      (mul_ne_zero (mul_ne_zero (by norm_num) (ENNReal.coe_ne_zero.mpr ha0.ne'))
        (ENNReal.coe_ne_zero.mpr hb0.ne'))
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top)
        ENNReal.coe_ne_top) hW18 hfull
      (fun i _ => (ShadedPlank.volume_carrier (Y i)).ge) hV'up
    calc ((Cref'⁻¹ * a ^ η) * a ^ ε) * (s.card : ℝ≥0)
        = (Cref'⁻¹ * a ^ ε) * (a ^ η * (s.card : ℝ≥0)) := by ring
      _ ≤ rRef * (a ^ η * (s.card : ℝ≥0)) :=
        mul_le_mul_of_nonneg_right h_Cref'_eps_le_rRef zero_le
      _ = (rRef * a ^ η) * (s.card : ℝ≥0) := by ring
      _ ≤ (s2.card : ℝ≥0) := hcard
  subst hW11
  -- The representative map and the active families are `Rthk.repr`, `Rthk.indexSet` and
  -- `Rthk.indexSet.image slabOf`, so the witness's separate `repr` / `T` outputs are substituted
  -- away rather than stored alongside equations pinning them.
  subst hW41
  subst hW42
  refine ⟨{
    s' := s2, Y' := Y2, θ := θ, hθ1 := hθ1, N := N, R := Rthk, slabOf := slabOf,
    rRef := rRef, cGood := cGood, q := q, cAngle := cAngle, acd := acd, Pr := Pr,
    subset := hW1, θ_lb := hθlb, isRefinement := hW18.1, fullness := hfullness,
    typicalAngle := htypical, cardinality := hcardinality,
    shade_subset_plank := ?_, carrier_eq_plank := ?_,
    maxAngle := hW7.mono_const hC611one, typicalAngle_out := hW8, one_le_N := hW9, θ_pos := ?_,
    indexSet_pairwise := hW12, slabFamily_pairwise := hW13, slabMembership := hW15,
    slabOverlapMass := hW16, fibreCardinality := hW17,
    rRef_pos := hW19, rRef_eq := hW20, q_eq := hW24, cGood_pos := hW25, q_pos := hW26,
    cAngle_pos := hcAnglePos, cAngle_lb := hcAngleLB, rRef_lb := hW21, rRef_fullness := hW23,
    cGood_poly := hW27, cGood_sharp := hW28, shade_subset_anchor := hW30,
    volume_active := hW31, volume_anchor_lb := hW32,
    acd_repr := hW33, acd_active := hW34, acd_anchor := hW35, acd_carrier := hW36,
    Pr_toPrismNDim := hW37, reprAngle_own := hW38, pointwiseSlabOverlap := hW39,
    reprAngle_any := hW40, constantMultiplicity := ?_, typicalAngle_reserve := hW43,
    isCRefinement := hW18, stopScaleStability := ?_, maxAngle_one := hW7 }⟩
  · exact fun i hi => (hW3 i).trans (hshadeP i (hW1 hi))
  · exact fun i hi => (hcar2 i).trans (hcar1 i (hW1 hi))
  · exact (div_pos ha0 hb0).trans_le hθlb
  · -- relative constant multiplicity transported to `(s2, Y2)`
    have hfib : ∀ x, shadeFibre s2 Y2 x ⊆ shadeFibre s Y1 x := by
      intro x i hi
      rw [mem_shadeFibre] at hi ⊢
      exact ⟨hW1 hi.1, hW3 i hi.2⟩
    -- sharp absorption of the pigeonhole retention: `Cabs⁻¹ * a ^ ew ≤ cGood`, so
    -- `q = cGood / 2 ≥ Cabs⁻¹ * a ^ ew / 2`; free of any `a ^ η`.
    have hq2 : Cabs⁻¹ * a ^ ew ≤ 2 * q := by
      rw [hW24, mul_div_cancel₀ cGood (by norm_num : (2 : ℝ≥0) ≠ 0)]
      exact hCabsSharp ha0 ha1 hW28
    have hscale : C611 ≤ q * (2 * Cabs * C611 * a ^ (-ew)) :=
      calc C611 = ((Cabs⁻¹ * Cabs) * C611) * (a ^ ew * a ^ (-ew)) := by
            rw [inv_mul_cancel₀ hCabs_pos.ne', ← NNReal.rpow_add ha0_ne, add_neg_cancel,
              NNReal.rpow_zero]
            simp
        _ = (Cabs⁻¹ * a ^ ew) * Cabs * C611 * a ^ (-ew) := by ring
        _ ≤ (2 * q) * Cabs * C611 * a ^ (-ew) := by gcongr
        _ = q * (2 * Cabs * C611 * a ^ (-ew)) := by ring
    exact Plank.hasCConstantMultiplicity_of_fibreRetention_real hW26 hconst hfib hW29 hscale
  · -- the stop-scale stability clause, transported from Lemma 6.11's `(s, Y1)` onto the actual
    -- output `(s2, Y2)`.  Exactly one factor of `Nov` is spent, out of the reserve.
    have hmNov : (1 : ℝ) ≤ (Nov : ℝ) := by exact_mod_cast h1Nov
    have hA1 : (1 : ℝ) ≤ (Nov : ℝ) * max 2 (plankAngleScaleA a) := by
      simpa using mul_le_mul hmNov (one_le_two.trans (le_max_left 2 (plankAngleScaleA a)))
        zero_le_one (Nat.cast_nonneg _)
    have hBpos : 0 < plankReserveScale kappa a := by
      have hApos : 0 < plankAngleScaleA a := Real.exp_pos _
      have hkappa0 : (0 : ℝ) < kappa := zero_lt_one.trans_le hkappa1
      dsimp [plankReserveScale]
      positivity
    have hbudgetNov : (Nov : ℝ) * max 2 (plankAngleScaleA a)
        ≤ (q : ℝ) * plankReserveScale kappa a := by
      rw [hW24]
      simpa [NNReal.coe_div] using
        outScale_le_half_mul_reserve_mul hCres hmNov hkappaNov ha0 ha1 hW28
    exact stopScaleStability_of_fibreRetention s s2 hW1 Y1 Y2 (ShadedPlank.planks Y) θ
      (2 * plankAngleScaleB a) ((Nov : ℝ) * max 2 (plankAngleScaleA a))
      (plankReserveScale kappa a) (q : ℝ) hA1 hBpos hbudgetNov
      (fun i _ => hW3 i) hW29 hstop

end Kakeya

end
