/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Bootstrap
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.RevisedOriginalEntryW111
public import Kakeya.DimensionThree.FrostmanEstimateMono
public import Kakeya.DimensionThree.FrostmanEstimateOne
public import Kakeya.DimensionThree.MainLemma1.CaseOne
public import Kakeya.DimensionThree.MainLemma1.Cases
public import Kakeya.DimensionThree.MainLemma1.CoarseFibre
public import Kakeya.DimensionThree.MainLemma1.DensityBand
public import Kakeya.DimensionThree.MainLemma1.Envelope
public import Kakeya.DimensionThree.MainLemma1.NodeFamilies
public import Kakeya.DimensionThree.MainLemma1.Rescaling
public import Kakeya.DimensionThree.MainLemma1.Rescaling.WindowTransport
public import Kakeya.DimensionThree.MainLemma1.Rescaling.KatzTaoBallPrefix
public import Kakeya.DimensionThree.MainLemma1.ShadeMass
public import Kakeya.DimensionThree.MainLemma1.ThreePass
public import Kakeya.MultiScaleFac

/-!
# GWZ Main Lemma 1

In `ℝ^3`, the Katz-Tao partial estimate `K_KT(β)` implies the Frostman partial estimate
`K_F(γ)` for every `γ > β`.

The proof is a bootstrap: `Kakeya.KatzTaoEstimate.frostmanEstimate_sub_of_frostmanEstimate`
(GWZ Lemma 8.1) is the self-improving step, and it is turned into
`Kakeya.KatzTaoEstimate.frostmanEstimate` by the base case `Kakeya.frostmanEstimate_one`,
monotonicity `Kakeya.FrostmanEstimate.mono`, and the abstract infimum argument
`Kakeya.ioc_subset_of_sub_mem_of_monotoneOn`.

This top-level file of Section 8 of the adapted blueprint contains

* the bootstrapping lemma `Kakeya.KatzTaoEstimate.frostmanEstimate_sub_of_frostmanEstimate`
  (blueprint `lemmain1boot`, GWZ Lemma 8.1) and its consequence
  `Kakeya.KatzTaoEstimate.frostmanEstimate` (GWZ Main Lemma 1);
* the uniform bootstrapping step `Kakeya.ml1Boot.exists_uniform_step` (blueprint
  `lem:ml1bootUniform`), which is the statement that the whole of the rest of Section 8
  proves, phrased through `Kakeya.frostmanStepSet`;
* `Kakeya.ml1Boot.multiplicity_le_caseTwo` (blueprint `lem:ml1bootCaseIIAssemble`), the second
  of the two steps that turn the output of `StickyKakeya.dividingScalesFrostman` into the input
  of the two-scale factoring and back.  The first of the two is blueprint
  `lem:ml1bootCaseIIData`, whose intended producer `Kakeya.ml1Boot.exists_caseTwoData` is not a
  declaration (see the inventory section below);
* the parts out of which that first step is to be assembled:
  `Kakeya.ml1Boot.caseTwoDataRaw` (blueprint `lem:ml1bootCaseIIDataRaw`), the pure read-off at
  the node families, applied at the exponent `ε' / 8`, and `Kakeya.ml1Boot.repairLower`
  (blueprint `lem:ml1bootRepairLower`), which reads the Frostman *lower* bound off the
  dichotomy at the unrefined node family.  The construction step between them — blueprint
  `lem:ml1bootCaseIIDataRepair`, which is to build the essentially distinct, uniform
  subfamilies in `B₁`, conclude at `ε'` and land in the `mid`-free record
  `Kakeya.ml1Boot.IsCaseTwoRepairData` — has no declaration either; its intended name is
  `Kakeya.ml1Boot.exists_caseTwoDataRepair`.

## Names below that are *intended* declarations and do not exist

Many docstrings in this file name the Case (ii) construction layer by the names it is to be
given. The ones used below are

* `Kakeya.ml1Boot.exists_caseTwoData` (blueprint `lem:ml1bootCaseIIData`);
* `Kakeya.ml1Boot.exists_caseTwoDataRepair` (blueprint `lem:ml1bootCaseIIDataRepair`);
* `Kakeya.ml1Boot.exists_repairThreePass` (blueprint `lem:ml1bootRepairThreePass`);
* `Kakeya.ml1Boot.exists_caseTwoThreePass` (blueprint `lem:ml1bootCaseIIThreePassCall`);
* `Kakeya.ml1Boot.exists_factorTwoScales` (blueprint `lem:ml1bootFactorTwoScales`).

Blueprint `note:ml1bootCaseTwoConstructionLayerEmpty` holds the authoritative inventory of the
whole absent layer, together with what *does* exist either side of it; read it before trusting
any name in the Case (ii) material.  That inventory is itself to be checked against the source
rather than assumed: one of its entries, `Kakeya.ml1Boot.caseTwoThreePassScales`, has since
been written, in `Kakeya/DimensionThree/MainLemma1/ThreePass.lean`.

## Divergences from the informal statements

*Parent index types.*  Blueprint `lem:ml1bootCaseIIData` produces its two parent families *as
the node families of the hierarchy of its own hypotheses* — "with `𝕋_τ` and `𝕋_θ` the node tubes
`P_b(·)` and `P_a(·)` of `𝒰'` themselves", retained as `t_τ ⊆ 𝒰'_b` and `t_θ ⊆ 𝒰'_a`.  So their
index type is the leaf index type `ι`, and that is how the intended
`Kakeya.ml1Boot.exists_caseTwoData` is to name them, matching the intended
`Kakeya.ml1Boot.exists_caseTwoDataRepair`.  Neither is a declaration; the structures they are
to produce, `Kakeya.ml1Boot.IsCaseTwoData` and `Kakeya.ml1Boot.IsCaseTwoRepairData`, are the
ones that fix this reading, and they do use `ι`.

An earlier form existentially quantified the two index *types* and their `DecidableEq`
instances, and with them the unrefined level-`b` index set `tb` that item (iv) speaks about.
That was strictly weaker than the blueprint and unusable by the consumer: with `tb`
existentially bound, the only clause tying it to the rest of the record is
`Kakeya.ml1Boot.IsCaseTwoData.fineRetained`, `tτ ⊆ tb`, and nothing said that `(tb, Tτ)` *was*
the level-`b` node family, so item (iv) could be met at an arbitrary superfamily of `tτ` while
saying nothing whatever about `𝒰'_b`.  Pinning the families to `𝒰'` removes that hole and costs
nothing downstream: `Kakeya.ml1Boot.exists_factorTwoScales` carries `[DecidableEq _]` binders on
its index types and is applied here at `ι` with the ambient instance, so the two
`Kakeya.ml1Boot.fibre` terms still agree syntactically.

*Item (iii) is conditional.*  Blueprint `lem:ml1bootCaseIIData`(iii) asserts the middle bound at
the *retained* parent-map fibre only under the antecedent that `t_τ` is fibrewise
empty-or-share at `δ ^ (3 ε'/4)` over `p_θ`, that antecedent being the one open step of Case (ii)
(`note:ml1bootEssDistinctFibrewiseShare`).  The intended
`Kakeya.ml1Boot.exists_caseTwoData` is therefore to conclude
`Kakeya.ml1Boot.IsCaseTwoRepairData` — items (i), (ii), (iv) and the interface data,
all unconditional — together with the implication
`Kakeya.ml1Boot.IsFibrewiseEmptyOrShare … → Kakeya.ml1Boot.IsCaseTwoData …`, which is
`Kakeya.ml1Boot.IsCaseTwoRepairData.isCaseTwoData` fed by
`Kakeya.ml1Boot.frostmanConstIn_retainedFibre_le`.  Concluding the full
`Kakeya.ml1Boot.IsCaseTwoData` outright would assert the middle bound at a retained node set,
which nothing in this development supplies.

*Fibres.*  Items (ii) and (iii) are stated with the **parent-map** fibres
`Kakeya.ml1Boot.fibre s₀ pτ k` and `Kakeya.ml1Boot.fibre tτ pθ l`, which is what the
blueprint's square brackets `𝕋|_{s₀}[T_{τ,k}]` and `𝕋_τ[T_{θ,l}]` mean in Section 8
(`def:ml1bootParentFamily`; see the warning in `def:nestedBelowBody`, which reserves the
angle brackets `𝕍⟨V⟩` for the containment fibre).  This is also the shape consumed by
`Kakeya.ml1Boot.IsFactorTwoScales.frostman_fine`,
`Kakeya.ml1Boot.IsFactorTwoScales.frostman_mid` and by
`Kakeya.ml1Boot.exists_factorOneScaleUniform`(e).  Item (iv), by contrast, is genuinely a
containment fibre — the anchor is the concentric `σ`-rescaling of a node tube, not a member of
any parent family — and is written with `Kakeya.familyIn`.

*Conclusion (ii) of `dividingScalesLemmaA`.*  Rather than referring to
`StickyKakeya.dividingScalesFrostman`, whose conclusion is a disjunction, the two Case (ii)
lemmas take its Alternative (ii) as an explicit hypothesis, through the named predicate
`StickyKakeya.IsFrostmanDividingBlock`, which *is* the second disjunct of that theorem.  So
the hypotheses are node-anchored: the anchors are the nodes `𝒰'.cover.tube b j` and
`𝒰'.cover.tube a j` of the hierarchy the theorem returns, the families are the leaf classes
`Tube.coverClass` and the node families `Tube.UniformTubeSet.nodesUnder`, the
scales are the grid scales `Tube.gridScale δ (Tube.ssfGridLen δ) a` and
`… b`, and every bound carries the subpolynomial factor `StickyKakeya.totalLoss`.  Everything is
asserted for the *refinement* `s' ⊆ s` and its hierarchy `𝒰'`, never for `s` itself; the
retention bound relating the two is the field `Kakeya.ml1Boot.IsCaseTwoInput.card_le`.

*What the amended dichotomy removed from the Case (ii) proofs.*  The conclusion
`Kakeya.ml1Boot.IsCaseTwoData` is stated in the free-scale language of the factoring chain
(`Kakeya/…/Factoring.lean`, `Kakeya/…/Rescaling.lean`), which is what
`Kakeya.ml1Boot.exists_factorTwoScales` and `Kakeya.ml1Boot.multiplicity_le_middle` consume.
Against the superseded `δ`-independent-grid dichotomy two conversions stood inside the intended
proof of blueprint `lem:ml1bootCaseIIData` and were discharged by nothing — that proof has no
Lean declaration to sit in — an *anchor-set* conversion,
because the lower bound held only on a majority set `F` of fine nodes, and a *scale-window*
conversion, because it held only at grid scales inside the `3 ε`-window.  Both are gone:
`StickyKakeya.IsFrostmanDividingBlock.frostman_lower` is asserted at every node of level `b`
and at every *real* scale of the `ε`-window, so no majority set has to be discarded and no free
scale has to be rounded onto the grid.  With them goes the loss they cost, the `δ ^ (-48 ε²)` of
the old bullet together with the rounding exponent `κ = 6 ε²`: the amended bullet carries
`StickyKakeya.totalLoss`, which is subpolynomial and so absorbable into the
`∀ᶠ δ in 𝓝[>] 0`.

*Item (iv) has been restated to match.*  `Kakeya.ml1Boot.IsCaseTwoData.lower` is
`Kakeya.ml1Boot.IsFreeScaleLowerBound` at the **unrefined** level-`b` node family, on the
`ε`-window `Kakeya.ml1Boot.IsScaleWindow` with the loss `δ ^ ε'`, in place of the retained
fibre, the `5 ε`-window and the loss `δ ^ (ε' + 54 ε²)` that the old input forced.  It carries
no coarse index and no containment clause.  Getting the bound down to the retained fibre was
the business of an assumption (blueprint `prop:ml1bootLowerFrostmanStable`,
`StickyKakeya.exists_dividing_scales_refinement_stable`) that is refuted and undeliverable;
both are deleted, and the item is stated where
`StickyKakeya.IsFrostmanDividingBlock.frostman_lower` asserts it.  The grid-rounding layer that
supplied the narrower form has likewise been deleted; what survived of it — the two
node-to-parent-family lemmas, the majority-node discard and the containment
`T_σ ⊆ 2 · T_{θ,l}` — is in `Kakeya/DimensionThree/MainLemma1/NodeFamilies.lean`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

universe u

namespace ml1Boot

/-! ### The uniform bootstrapping step -/



end ml1Boot

/-! ### The bootstrapping lemma and Main Lemma 1 -/



/-- [GWZ, Main Lemma 1]
For `0 ≤ β < γ ≤ 1`, `K_KT(β)` implies `K_F(γ)` for sets of `δ`-tubes in `B_1 ⊆ ℝ^3`.

The set `S = {γ | K_F(γ)}` is up-closed by `FrostmanEstimate.mono`, contains `1` by
`frostmanEstimate_one`, and is closed under `γ ↦ γ - ν γ` on `Set.Ioc β 1` by
`frostmanEstimate_sub_of_frostmanEstimate`, so `ioc_subset_of_sub_mem_of_monotoneOn` gives
`Set.Ioc β 1 ⊆ S`.

The conclusion is deliberately *not* sharp: the bootstrap increment `ν γ` tends to `0` as
`γ ↓ β`, so iterating Lemma 8.1 reaches every exponent above `β` but never `β` itself, and
forcing `K_F(β)` would require a separate limiting argument. Every consumer of this lemma
tolerates an arbitrarily small loss in the exponent instead; see
`Kakeya.katzTaoEstimateDimensionThree`, which pays for it by halving the step of Main
Lemma 2. -/
theorem KatzTaoEstimate.frostmanEstimate
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, u}
      (E := EuclideanSpace ℝ (Fin 3)))
    {β γ : ℝ} (hβ_nonneg : 0 ≤ β) (hβγ : β < γ)
    (hγ_le : γ ≤ 1) (h : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) :
    FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) γ := by
  exact ml1Boot.RevisedSourceRepairW110.frostmanEstimate_from_revised_w110
    hSFE hβ_nonneg hβγ hγ_le h


namespace ml1Boot

/-! ### Case (ii): from the dividing scales to the factoring chain and back -/

section CaseTwo

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `C_F(𝕋_{σ∣ρ}[i₀], T_{i₀}^{(ρ)})` in the notation of [GWZ, §7]: the Frostman constant of
the family of `σ`-rescalings of those tubes of `𝕋 = (T i)_{i ∈ s}` whose `σ`-rescaling is
contained in the `ρ`-rescaling `T_{i₀}^{(ρ)}` of `T i₀`, measured inside that `ρ`-rescaling.

The blueprint abbreviates `𝕋_{δ∣ρ}[i₀]` to `𝕋[i₀;ρ]`; that family is
`frostmanConstBetweenScales s T δ ρ i₀`.  Restricting the ambient family to a subset
`s' ⊆ s` (the blueprint's `𝕋|_{s'}`) is `frostmanConstBetweenScales s' T σ ρ i₀`.

This used to live in `Kakeya/Sticky.lean` alongside the leaf-anchored Section 7 interfaces.
Those have been superseded by the node-hierarchy statements of `Kakeya/MultiScaleFac.lean`
and `StickyKakeya.StickyFrostmanEstimate`, which do not use this reading.

**Nothing in this development is stated against it any more.**  In particular
`Kakeya.ml1Boot.multiplicity_le_caseTwo`, which used to phrase Conclusion (ii) of
`StickyKakeya.dividingScalesFrostman` this way, now takes that conclusion in the node-anchored
form the theorem actually produces (`StickyKakeya.IsFrostmanDividingBlock`), and blueprint
`lem:ml1bootCaseIIData` — intended producer `Kakeya.ml1Boot.exists_caseTwoData`, not a
declaration — is stated the same way.  The definition is retained only so that the
blueprint notes discussing the retired leaf-anchored reading — `note:stickyFrostmanNodeForm`
and the check note of `section8_factoring.tex` — have a name to point at. -/
noncomputable def frostmanConstBetweenScales {ι : Type*} {δ : NNReal} (s : Finset ι)
    (T : ι → Tube δ E) (σ ρ : NNReal) (i₀ : ι) : ENNReal :=
  ConvexSpaceBody.frostmanConstIn
    (s.filter fun i => ((T i).rescale σ).toConvexSpaceBody ≤ ((T i₀).rescale ρ).toConvexSpaceBody)
    (fun i => ((T i).rescale σ).toConvexSpaceBody)
    ((T i₀).rescale ρ).toConvexSpaceBody

/-- **The family `K_F(γ)` is applied to in Case (ii)** (blueprint `lem:ml1bootCaseIIData`,
the hypotheses on `(𝕋, Y)`).

A nonempty `C_u`-uniform family of shaded, pairwise essentially distinct `δ`-tubes in `B₁`
whose Frostman constant and fullness are both within `δ ^ (∓ η(γ))` of `1` — the exact input
that `Kakeya.FrostmanEstimate` supplies and that the whole Case (ii) chain is run on.

The two exponents are the *same* `p.ηGamma γ`, not independent thresholds: `η(γ)` is defined
in `Kakeya.ml1Boot.params` as a minimum over all the places a fullness or Frostman threshold
is needed, so a single number governs both sides.

Uniformity is carried as `Nonempty (ShadedTube.ShadedUniformTubeSet …)` because that
predicate is data-valued; since the conclusions it feeds are `Prop`s, this loses nothing. -/
structure IsCaseFamily {ι : Type*} {δ : NNReal} (p : Params) (γ : ℝ) (Cunif : NNReal)
    (s : Finset ι) (T : ι → ShadedTube δ E) : Prop where
  /-- The family is nonempty. -/
  nonempty : s.Nonempty
  /-- It is `C_u`-uniform along the grid of Definition 2.2. -/
  unif : Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) Cunif)
  /-- Its members lie in the unit ball. -/
  ball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1
  /-- Its members are pairwise essentially distinct, as `Kakeya.FrostmanEstimate` requires. -/
  essDistinct : (s : Set ι).Pairwise
    (fun i i' => IsEssentiallyDistinct (T i).carrier (T i').carrier)
  /-- `C_F(𝕋, B₁) ≤ δ ^ (-η(γ))`. -/
  frostman : frostmanConstIn s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall ≤ (δ : ENNReal) ^ (-p.ηGamma γ)
  /-- `λ(𝕋, Y) ≥ δ ^ η(γ)`. -/
  fullness : (δ : ENNReal) ^ p.ηGamma γ ≤ ShadedBody.fullness s (fun i => (T i).toShadedBody)

/-- **What Alternative (ii) of `StickyKakeya.dividingScalesFrostman` hands to Case (ii)**
(blueprint `lem:ml1bootCaseIIData`, the hypothesis "Conclusion (ii) holds for `𝕋`").

The dichotomy does not return its conclusion for the input family: it returns a refinement
`s' ⊆ s` retaining all but a `StickyKakeya.totalLoss` share, a fresh hierarchy `𝒰'` on `s'`
along the grid of length `Tube.ssfGridLen δ`, and the block data `a < b`, `m` — and
*everything is then computed in `𝒰'`*.  This structure is that package, with the block itself
delegated to `StickyKakeya.IsFrostmanDividingBlock`, which is literally the second disjunct
of that theorem.

The bounds' constant, the hierarchy's constant and the retention constant are all instantiated
at `Cds`, as the theorem does; the polylogarithmic exponent is `Kds` and the grid-gap exponent
is `cds`.  All three are quantified before `δ`, and `StickyKakeya.totalLoss` is subpolynomial in
`δ`, so a consumer may absorb the whole loss into a `∀ᶠ δ in 𝓝[>] 0`.  The superseded
`δ`-independent-grid form carried instead a fixed exponent `εds`, which could not be absorbed
that way and therefore forced an explicit smallness hypothesis on the Case (ii) lemmas; with
`StickyKakeya.dividingScalesFrostman` that hypothesis is gone.

## The accuracy parameter `ε'`

`ε'` is a further exponent, chosen by the caller and likewise quantified before `δ`.  It occurs
in the first clause `Kakeya.ml1Boot.IsCaseTwoInput.card_le` alone, which reads
`|s| ≤ δ ^ (-ε') |s'|`; one says the bundle is taken *at accuracy `ε'`*.

The clause used to read `|s| ≤ totalLoss Cds Kds cds δ * |s'|`, and nothing in this development
instantiates that form: what the composition of the uniformization and the hierarchy refinement
supplies is `|s| ≤ δ ^ (-ε/2) * totalLoss * |s'|`, and a subpolynomial factor cannot absorb a
fixed power of `δ`.  So the clause is stated at exactly what is buildable, with the exponent
carried as a parameter.  Nothing is lost: the sole consumer of the clause reads it only in the
form `|s| ≤ δ ^ (-ε') |s'|` for a fixed `ε'`.

Because the exponent is the caller's, a consumer is no longer indifferent to it — the clause at
`ε'` is strictly weaker than the same clause at `ε' / 8` — so every consumer names the accuracy
at which it takes the bundle, and the named accuracies meet along the chain:
`Kakeya.ml1Boot.caseTwoDataRaw` and `Kakeya.ml1Boot.repairLower` never read the clause, the
intended `Kakeya.ml1Boot.exists_caseTwoDataRepair` and `Kakeya.ml1Boot.exists_caseTwoData` are
to take it at `ε' / 8` (neither is a declaration; see the module docstring), and
`Kakeya.ml1Boot.multiplicity_le_caseTwo`, which fixes `ε' = p.η 0 / 16`, takes it
at `p.η 0 / 128`. -/
structure IsCaseTwoInput [Nontrivial E] {ι : Type u} {δ : NNReal}
    (p : Params) (ε' : ℝ) (Cds : NNReal) (Kds cds : ℕ)
    (s : Finset ι) (T : ι → ShadedTube δ E) (s' : Finset ι)
    (𝒰' : Tube.UniformTubeSet s' (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cds)
    (a b m : ℕ) : Prop where
  /-- The dichotomy refines the family. -/
  subset : s' ⊆ s
  /-- …and retains all but a `δ ^ ε'` share of it, at the caller's accuracy `ε'`. -/
  card_le : (s.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s'.card : ℝ)
  /-- **Shade-mass retention**: `(𝕋|_{s'}, Y)` is a `δ ^ ε'`-refinement of `(𝕋, Y)`, at the
  *same* caller-chosen accuracy `ε'` as `card_le`, i.e.
  `δ ^ ε' * ∑_{i ∈ s} |Y i| ≤ ∑_{i ∈ s'} |Y i|`.

  Without this clause the bundle says nothing whatever about the shading of the retained family:
  `card_le` is a statement about *counts* and `StickyKakeya.IsFrostmanDividingBlock` is three
  statements about *tubes*.  A shading vanishing on `s'` and equal to the whole tube on `s \ s'`
  then satisfies every other clause while making `ShadedBody.fullness s₀ 𝕋 = 0` for every
  `s₀ ⊆ s'`, which refutes `Kakeya.ml1Boot.IsCaseTwoData.refine_fullness` and with it
  `Kakeya.ml1Boot.exists_caseTwoDataRepair`.  Blueprint `note:ml1bootCaseIIRefineFullnessGap` is
  the record of that counterexample; this field is its repair, at the bundle rather than at the
  consumer.

  It is *not* a new obligation on suppliers: by blueprint `lem:ml1bootCaseTwoInputMassFromCard`
  a supplier meeting `card_le` at accuracy `ε' / 2` together with `band` meets this clause at
  accuracy `ε'`, all `δ`-tubes having one common positive volume. -/
  refine_mass : ShadedBody.IsCRefinement s' (fun i => (T i).toShadedBody) s
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩
  /-- **Banded shade density on the input**: some `λ_* > 0` has
  `λ_* |T i| ≤ |Y i| ≤ 2 λ_* |T i|` for every `i ∈ s`.

  A condition on `(𝕋, Y)` at `s` alone, carrying no accuracy — `s` here is the index set of the
  *uniformized* pair, the one carrying the standing Case hypotheses
  `Kakeya.ml1Boot.IsCaseFamily`, so the banding is asserted of a family that has already been
  pigeonholed to a dyadic shade-density band, and the uniformization is not one of the passages
  `s ⇝ s'` that the bundle's two accuracy-carrying clauses price.

  Its role is to convert counts into shade mass: it is exactly the hypothesis of
  `ShadedBody.card_le_iff_isCRefinement_of_comparable` at `Λ = 2` and `μ₀ = λ_*`, and it
  is what makes `refine_mass` a consequence of `card_le` rather than an independent supplier
  obligation (blueprint `lem:ml1bootCaseTwoInputMassFromCard`). -/
  band : ∃ lam : NNReal, 0 < lam ∧ ∀ i ∈ s,
    (lam : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ 2 * (lam : ENNReal) * volume (T i).carrier
  /-- Alternative (ii) itself, read on `𝒰'`.

  There is deliberately no fourth clause asserting that the block's lower bound survives a
  refinement of the node family.  That assertion (blueprint
  `prop:ml1bootLowerFrostmanStable`) is refuted and undeliverable, and is deleted rather than
  weakened; blueprint `note:ml1bootLowerFrostmanRetired` is the record.  Nothing needs it:
  `Kakeya.ml1Boot.IsCaseTwoData.lower` is stated at the unrefined node family. -/
  block : StickyKakeya.IsFrostmanDividingBlock 𝒰' Cds Kds cds p.η p.ε a b m p.N

/-- **The `w`-window of free scales** (blueprint `eq:ml1bootScaleWindow`).

For a block with fine end `τ` and coarse end `θ`, the free scale `σ` lies in the closed window
`[τ (θ/τ) ^ w, θ (τ/θ) ^ w]` obtained from `[τ, θ]` by trimming a margin of `w` at each end.

`Kakeya.ml1Boot.IsCaseTwoData.lower` reads it at `w = p.ε`, which is the window at which
`StickyKakeya.IsFrostmanDividingBlock.frostman_lower` is asserted.  It used to be read at
`w = 5 ε`: the superseded `δ`-independent-grid dichotomy asserted its bound only at grid scales,
and the extra margin was what the rounding spent to move a free scale onto the grid. -/
structure IsScaleWindow (τ θ : NNReal) (w : ℝ) (σ : NNReal) : Prop where
  /-- The free scale is at least the fine end of the window. -/
  lower : τ * (θ / τ) ^ w ≤ σ
  /-- …and at most its coarse end. -/
  upper : σ ≤ θ * (τ / θ) ^ w

/-- The lower window inequality of `Kakeya.ml1Boot.IsScaleWindow`, read in `ℝ`.

`StickyKakeya.IsFrostmanDividingBlock.frostman_lower` states its two window hypotheses as real
inequalities between coerced grid scales, while the predicate states them in `NNReal`; the two
bridges are this lemma and `Kakeya.ml1Boot.IsScaleWindow.coe_upper`. -/
theorem IsScaleWindow.coe_lower {τ θ : NNReal} {w : ℝ} {σ : NNReal} (h : IsScaleWindow τ θ w σ) :
    (τ : ℝ) * ((θ : ℝ) / (τ : ℝ)) ^ w ≤ (σ : ℝ) := by
  simpa [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_rpow] using NNReal.coe_le_coe.mpr h.lower

/-- The upper window inequality of `Kakeya.ml1Boot.IsScaleWindow`, read in `ℝ`; see
`Kakeya.ml1Boot.IsScaleWindow.coe_lower`. -/
theorem IsScaleWindow.coe_upper {τ θ : NNReal} {w : ℝ} {σ : NNReal} (h : IsScaleWindow τ θ w σ) :
    (σ : ℝ) ≤ (θ : ℝ) * ((τ : ℝ) / (θ : ℝ)) ^ w := by
  simpa [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_rpow] using NNReal.coe_le_coe.mpr h.upper

/-- A scale in the window is positive, the fine end of the window being positive.

This is what lets the seam `Kakeya.ennreal_coe_nnreal_rpow` be crossed at `σ / τ` when the
dichotomy's `ENNReal.ofReal ((σ / τ) ^ η)` is matched against the `ENNReal`-valued power of
`Kakeya.ml1Boot.IsFreeScaleLowerBound`. -/
theorem IsScaleWindow.pos {τ θ : NNReal} {w : ℝ} {σ : NNReal} (h : IsScaleWindow τ θ w σ)
    (hτ : 0 < τ) (hθ : 0 < θ) : 0 < σ := by
  have hdiv : 0 < θ / τ := div_pos hθ hτ
  have hrpow : 0 < (θ / τ) ^ w := NNReal.rpow_pos hdiv
  exact lt_of_lt_of_le (mul_pos hτ hrpow) h.lower

/-- **The free-scale Frostman lower bound at the unrefined level-`b` node family**
(blueprint `lem:ml1bootFreeScaleNodeLower`, `lem:ml1bootRepairLower`,
`lem:ml1bootCaseIIDataRaw`(c) and `lem:ml1bootCaseIIData`(iv)).

For every real scale `σ` of the `ε`-window `Kakeya.ml1Boot.IsScaleWindow` and *every* node
`k ∈ tb`, the members of `tb` lying inside the concentric `σ`-rescaling `(Tb k).rescale σ` of
the node tube are Frostman from below in it, with the loss `δ ^ ε'` on the left.

This is `StickyKakeya.IsFrostmanDividingBlock.frostman_lower` read in the parent-family
language, and `tb` is the *unrefined* level-`b` index set of the hierarchy.  There is no
coarse index, no fibre, no subfamily quantifier and no share hypothesis: a Frostman lower
bound is witnessed by a single test body and does not survive a refinement, so it is stated
where the dichotomy asserts it, and a consumer holding a retained `t ⊆ tb` reads it by
restricting the quantifier.  The containment `T_σ ⊆ 2 · Tθ l'` that this predicate used to
carry alongside the bound went with the coarse index; it is
`Kakeya.ml1Boot.rescale_le_dilate_two`, available wherever a consumer needs it. -/
def IsFreeScaleLowerBound {κ : Type*} {τ : NNReal} (δ : NNReal)
    (p : Params) (ε' : ℝ) (j : ℕ) (θ : NNReal)
    (tb : Finset κ) (Tb : κ → Tube τ E) : Prop :=
  ∀ σ : NNReal, IsScaleWindow τ θ p.ε σ →
    ∀ k ∈ tb,
      (δ : ENNReal) ^ ε' * ((σ / τ : NNReal) : ENNReal) ^ p.η j
        ≤ frostmanConstIn
            (familyIn tb (fun k' => (Tb k').toConvexSpaceBody)
              ((Tb k).rescale σ).toConvexSpaceBody)
            (fun k' => (Tb k').toConvexSpaceBody)
            ((Tb k).rescale σ).toConvexSpaceBody

/-- **The conclusions of blueprint `lem:ml1bootCaseIIData`, one field per clause**

The intended producer is `Kakeya.ml1Boot.exists_caseTwoData`, which is not a declaration; see
the module docstring.  This structure is what it is to conclude.

Here `(𝕋, Y)` is a family of shaded `δ`-tubes indexed by `s`, `s₀ ⊆ s` is the refinement, and
`(tτ, 𝕋_τ, pτ)`, `(tθ, 𝕋_θ, pθ)` are the two named parent families produced at the scales `τ`
and `θ`.  The fields `parentFine`–`coarseEssDistinct` are the interface data that
`Kakeya.ml1Boot.exists_factorTwoScales` consumes; `refine_*` are the four clauses of item (i),
and `fine`, `mid`, `lower` are items (ii), (iii) and (iv). -/
structure IsCaseTwoData {ι κ l : Type*} [DecidableEq κ] [DecidableEq l] {δ τ θ : NNReal}
    (p : Params) (ε' γ : ℝ) (j : ℕ) (s : Finset ι) (T : ι → ShadedTube δ E) (s₀ : Finset ι)
    (tb : Finset κ)
    (tτ : Finset κ) (Tτ : κ → Tube τ E) (pτ : ι → κ)
    (tθ : Finset l) (Tθ : l → Tube θ E) (pθ : κ → l) : Prop where
  /-- `(tτ, 𝕋_τ, pτ)` is a parent family for the retained fine family at scale `τ`. -/
  parentFine : IsParentFamily s₀ (fun i => (T i).toTube) tτ Tτ pτ
  /-- `(tθ, 𝕋_θ, pθ)` is a parent family for `𝕋_τ` at scale `θ`. -/
  parentCoarse : IsParentFamily tτ Tτ tθ Tθ pθ
  /-- The fine parent family is retained inside the unrefined level-`b` node family `tb` of the
  hierarchy of the hypotheses.  This is what lets `lower`, which speaks about `tb`, be stated
  alongside the repaired families. -/
  fineRetained : tτ ⊆ tb
  /-- The middle tubes lie in `B₁`.  This is not implied by `parentFine`: a parent tube may
  stick out of `B₁` even though every tube it covers lies inside. -/
  midBall : ∀ k ∈ tτ, (Tτ k).carrier ⊆ Metric.closedBall 0 1
  /-- The coarse tubes lie in `B₁`, for the same reason. -/
  coarseBall : ∀ l' ∈ tθ, (Tθ l').carrier ⊆ Metric.closedBall 0 1
  /-- The middle tubes are pairwise essentially distinct. -/
  midEssDistinct : (tτ : Set κ).Pairwise
    (fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier)
  /-- The coarse tubes are pairwise essentially distinct. -/
  coarseEssDistinct : (tθ : Set l).Pairwise
    (fun l₁ l₂ => IsEssentiallyDistinct (Tθ l₁).carrier (Tθ l₂).carrier)
  /-- (i) `(𝕋|_{s₀}, Y)` is a `δ ^ ε'`-refinement of `(𝕋, Y)`. -/
  refine_refinement : ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩
  /-- (i) The refinement is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  refine_unif : Nonempty (ShadedTube.ShadedUniformTubeSet s₀ T (Tube.ssfGridLen δ)
    (uniformize.C 3))
  /-- (i) Its Frostman constant in `B₁` has grown by at most `δ ^ (-ε')`. -/
  refine_frostman : frostmanConstIn s₀ (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall
    ≤ (δ : ENNReal) ^ (-ε' - p.ηGamma γ)
  /-- (i) Its fullness has dropped by at most `δ ^ ε'`. -/
  refine_fullness : (δ : ENNReal) ^ (ε' + p.ηGamma γ)
    ≤ ShadedBody.fullness s₀ (fun i => (T i).toShadedBody)
  /-- (ii) The Frostman constant of every fine fibre inside its `τ`-parent. -/
  fine : ∀ k ∈ tτ,
    frostmanConstIn (fibre s₀ pτ k) (fun i => (T i).toConvexSpaceBody)
        (Tτ k).toConvexSpaceBody
      ≤ (δ : ENNReal) ^ (-ε') * ((τ / δ : NNReal) : ENNReal) ^ p.η (j - 1)
  /-- (iii) The Frostman constant of every middle fibre inside its `θ`-parent. -/
  mid : ∀ l' ∈ tθ,
    frostmanConstIn (fibre tτ pθ l') (fun k => (Tτ k).toConvexSpaceBody)
        (Tθ l').toConvexSpaceBody
      ≤ (δ : ENNReal) ^ (-ε') * ((θ / τ : NNReal) : ENNReal) ^ p.η (j - 1)
  /-- (iv) The Frostman **lower** bound at every free scale `σ` in the `ε`-window
  `Kakeya.ml1Boot.IsScaleWindow` and at *every* node of the **unrefined** level-`b` family
  `tb`, inside the concentric `σ`-rescaling of that node's tube.

  Three features of the shape.

  * *The family is the unrefined one.*  The item used to read the Frostman constant of the
    *retained* fibre `fibre tτ pθ l'` inside a `σ`-tube, and getting the dichotomy's bound
    down to that family was what the refinement-stability assumption (blueprint
    `prop:ml1bootLowerFrostmanStable`) was for.  That assumption is refuted and undeliverable,
    so the item is stated where `StickyKakeya.IsFrostmanDividingBlock.frostman_lower` asserts
    it and nowhere else; `fineRetained` is what connects it to `tτ`.
  * *There is no coarse index and no containment clause.*  Where a consumer needs
    `T_σ ⊆ 2 · Tθ l'` it is supplied on the spot by
    `Kakeya.ml1Boot.rescale_le_dilate_two`, a property of the node tubes alone.
  * *The window is the `ε`-window and the loss is `δ ^ ε'`, with no `ε²` term.*  Both are the
    amended dichotomy's: it is asserted at every real scale of that window with a
    subpolynomial loss, so no rounding stands between hypothesis and conclusion. -/
  lower : IsFreeScaleLowerBound δ p ε' j θ tb Tτ

/-- **The output of the Case (ii) repair: `Kakeya.ml1Boot.IsCaseTwoData` without its middle
bound** (blueprint `lem:ml1bootCaseIIDataRepair`).

The intended producer is `Kakeya.ml1Boot.exists_caseTwoDataRepair`, which is not a declaration;
see the module docstring.  This structure is what it is to conclude.

Every field of `Kakeya.ml1Boot.IsCaseTwoData` except `mid`, at the same parameters and with the
same statements.  This is exactly what the repair produces: blueprint
`lem:ml1bootCaseIIDataRepair` concludes items `caseIIRefine`, `caseIIFine` and `caseIILower`
together with the parent-family, essential-distinctness and `B₁` interface data, and *not* item
`caseIIMid`.

## Why the middle bound is not among the fields

The repair delivers the middle bound at the parent-map fibre inside the **full** level-`b` node
family — that is step 0, `Kakeya.ml1Boot.caseTwoRawMidFibre` — and its two later steps delete
`τ`-nodes without controlling what survives inside a coarse fibre.  So nothing in the repair
supplies that bound at the *retained* `tτ` which `Kakeya.ml1Boot.IsCaseTwoData.mid` reads:
passing to the subfamily needs a node-count share *inside each coarse fibre*, and the greedy
selection behind step 1 is charged against one global weight on the leaves, so a discarded node
is charged to a near-copy that need not lie under the same coarse node and a coarse fibre can be
selected down to a concentrated remnant.  Blueprint `note:ml1bootRepairEDMidRetained` is the
account of that, and of the two obstructions standing in the way of the fibrewise selection that
would remove it.  An earlier form of blueprint `lem:ml1bootCaseIIDataRepair` asserted `mid`
anyway; that is retracted, and this structure is the Lean half of the retraction.

## Where the obligation went

It is not silently absorbed.  It is the explicit hypothesis of
`Kakeya.ml1Boot.IsCaseTwoRepairData.isCaseTwoData`, so it is visible in the statement of every
consumer that rebuilds the full record, `Kakeya.ml1Boot.exists_caseTwoData` above all, and no
declaration of this chain asserts the middle bound at a retained node set outright.

What *is* proved about it is the descent, `Kakeya.ml1Boot.frostmanConstIn_retainedFibre_le`:
given the fibrewise empty-or-share dichotomy `Kakeya.ml1Boot.IsFibrewiseEmptyOrShare` for the
retained node set at a share `κ ≠ 0`, step 0's bound at the full fibre transfers to the retained
fibre at the single cost `κ⁻¹`.  At `κ = δ ^ (3 ε' / 4)` — the whole of the budget step 0 leaves,
see `Kakeya.ml1Boot.mid_le_of_share_compose` — that lands the exponent back at exactly `ε'`, so
carrying the dichotomy through to this point would restore `mid` with no change to the
exponents.

The dichotomy is **not** unproducible, and this paragraph used to say otherwise. What is missing is a **caller**: no declaration runs the trim after the repair's
node-deleting selection and carries the dichotomy on to this consumer. The open half is the
assembly, not the dichotomy. -/
structure IsCaseTwoRepairData {ι κ l : Type*} [DecidableEq κ] [DecidableEq l] {δ τ θ : NNReal}
    (p : Params) (ε' γ : ℝ) (j : ℕ) (s : Finset ι) (T : ι → ShadedTube δ E) (s₀ : Finset ι)
    (tb : Finset κ)
    (tτ : Finset κ) (Tτ : κ → Tube τ E) (pτ : ι → κ)
    (tθ : Finset l) (Tθ : l → Tube θ E) (pθ : κ → l) : Prop where
  /-- `(tτ, 𝕋_τ, pτ)` is a parent family for the retained fine family at scale `τ`. -/
  parentFine : IsParentFamily s₀ (fun i => (T i).toTube) tτ Tτ pτ
  /-- `(tθ, 𝕋_θ, pθ)` is a parent family for `𝕋_τ` at scale `θ`. -/
  parentCoarse : IsParentFamily tτ Tτ tθ Tθ pθ
  /-- The fine parent family is retained inside the unrefined level-`b` node family `tb` of the
  hierarchy of the hypotheses.  This is what lets `lower`, which speaks about `tb`, be stated
  alongside the repaired families. -/
  fineRetained : tτ ⊆ tb
  /-- The middle tubes lie in `B₁`.  This is not implied by `parentFine`: a parent tube may
  stick out of `B₁` even though every tube it covers lies inside. -/
  midBall : ∀ k ∈ tτ, (Tτ k).carrier ⊆ Metric.closedBall 0 1
  /-- The coarse tubes lie in `B₁`, for the same reason. -/
  coarseBall : ∀ l' ∈ tθ, (Tθ l').carrier ⊆ Metric.closedBall 0 1
  /-- The middle tubes are pairwise essentially distinct. -/
  midEssDistinct : (tτ : Set κ).Pairwise
    (fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier)
  /-- The coarse tubes are pairwise essentially distinct. -/
  coarseEssDistinct : (tθ : Set l).Pairwise
    (fun l₁ l₂ => IsEssentiallyDistinct (Tθ l₁).carrier (Tθ l₂).carrier)
  /-- (i) `(𝕋|_{s₀}, Y)` is a `δ ^ ε'`-refinement of `(𝕋, Y)`. -/
  refine_refinement : ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩
  /-- (i) The refinement is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  refine_unif : Nonempty (ShadedTube.ShadedUniformTubeSet s₀ T (Tube.ssfGridLen δ)
    (uniformize.C 3))
  /-- (i) Its Frostman constant in `B₁` has grown by at most `δ ^ (-ε')`. -/
  refine_frostman : frostmanConstIn s₀ (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall
    ≤ (δ : ENNReal) ^ (-ε' - p.ηGamma γ)
  /-- (i) Its fullness has dropped by at most `δ ^ ε'`.

  This is the clause that blueprint `note:ml1bootCaseIIRefineFullnessGap` showed had no supplier
  while `Kakeya.ml1Boot.IsCaseTwoInput` linked `s'` to `s` by a cardinality bound alone.  It now
  has one: the bundle's `refine_mass` carries the shade-mass retention, and
  `Kakeya.ml1Boot.fullness_le_of_isCRefinement` descends it along the composed refinement
  `s₀ ⊆ s' ⊆ s`. -/
  refine_fullness : (δ : ENNReal) ^ (ε' + p.ηGamma γ)
    ≤ ShadedBody.fullness s₀ (fun i => (T i).toShadedBody)
  /-- (ii) The Frostman constant of every fine fibre inside its `τ`-parent. -/
  fine : ∀ k ∈ tτ,
    frostmanConstIn (fibre s₀ pτ k) (fun i => (T i).toConvexSpaceBody)
        (Tτ k).toConvexSpaceBody
      ≤ (δ : ENNReal) ^ (-ε') * ((τ / δ : NNReal) : ENNReal) ^ p.η (j - 1)
  /-- (iv) The Frostman **lower** bound at every free scale `σ` in the `ε`-window and at every
  node of the **unrefined** level-`b` family `tb`; see `Kakeya.ml1Boot.IsCaseTwoData.lower`. -/
  lower : IsFreeScaleLowerBound δ p ε' j θ tb Tτ

/-- **Rebuilding the full Case (ii) conclusion from the repair's output together with the
middle bound** (blueprint `lem:ml1bootCaseIIDataRepair`, `lem:ml1bootCaseIIData`).

`Kakeya.ml1Boot.IsCaseTwoRepairData` is `Kakeya.ml1Boot.IsCaseTwoData` minus the field `mid`, so
the two differ by exactly one hypothesis, and this lemma is the record of what that hypothesis
is.  It is stated rather than left implicit so that the consumer which needs the middle bound —
`Kakeya.ml1Boot.exists_caseTwoData` — must name it, and so that the gap of blueprint
`note:ml1bootRepairEDMidRetained` is an edge of the dependency graph rather than a remark in a
proof. -/
theorem IsCaseTwoRepairData.isCaseTwoData {ι κ l : Type*} [DecidableEq κ] [DecidableEq l]
    {δ τ θ : NNReal} {p : Params} {ε' γ : ℝ} {j : ℕ} {s : Finset ι} {T : ι → ShadedTube δ E}
    {s₀ : Finset ι} {tb tτ : Finset κ} {Tτ : κ → Tube τ E} {pτ : ι → κ}
    {tθ : Finset l} {Tθ : l → Tube θ E} {pθ : κ → l}
    (h : IsCaseTwoRepairData p ε' γ j s T s₀ tb tτ Tτ pτ tθ Tθ pθ)
    (hmid : ∀ l' ∈ tθ,
      frostmanConstIn (fibre tτ pθ l') (fun k => (Tτ k).toConvexSpaceBody)
          (Tθ l').toConvexSpaceBody
        ≤ (δ : ENNReal) ^ (-ε') * ((θ / τ : NNReal) : ENNReal) ^ p.η (j - 1)) :
    IsCaseTwoData p ε' γ j s T s₀ tb tτ Tτ pτ tθ Tθ pθ :=
  { parentFine := h.parentFine
    parentCoarse := h.parentCoarse
    fineRetained := h.fineRetained
    midBall := h.midBall
    coarseBall := h.coarseBall
    midEssDistinct := h.midEssDistinct
    coarseEssDistinct := h.coarseEssDistinct
    refine_refinement := h.refine_refinement
    refine_unif := h.refine_unif
    refine_frostman := h.refine_frostman
    refine_fullness := h.refine_fullness
    fine := h.fine
    mid := hmid
    lower := h.lower }

/-- **The two raw Frostman *upper* bounds at the node families** (blueprint
`lem:ml1bootCaseIIDataRaw`, items (a) and (b)).

These are the first two bullets of `StickyKakeya.IsFrostmanDividingBlock` read at the two named
node parent families, with their subpolynomial `StickyKakeya.totalLoss` absorbed into
`δ ^ (-ε')`.  They are split off from the lower bound of
`Kakeya.ml1Boot.IsCaseTwoRawData` because the repair — blueprint
`lem:ml1bootCaseIIDataRepair`, intended producer `Kakeya.ml1Boot.exists_caseTwoDataRepair`,
which is not a declaration — is to consume exactly these two and *not* the lower one:
a Frostman lower bound at a family says nothing about a subfamily, so it cannot be transported
across the repair's refinement and is re-derived there instead, from the block itself.

## The middle bound is a *containment* family, and it cannot be a fibre here

`mid` used to read the Frostman constant of the parent-map fibre `fibre tτ pθ l'`.  That is
**not** what the second bullet of `StickyKakeya.IsFrostmanDividingBlock` asserts: the bullet is
`frostman_nodes`, stated at `Tube.UniformTubeSet.nodesUnder`, i.e. at *all* level-`b`
nodes contained in the coarse node, and the fibre of the induced map `ϖ_{b→a}` is in general a
proper subset of that family (a fine node may lie in several coarse nodes, and `ϖ` picks one of
them through a leaf).  A Frostman constant is a *ratio* — `ConvexSpaceBody.IsFrostmanIn` bounds
`densityIn t W K'` by `C * densityIn t W K` — so passing to a subfamily shrinks numerator and
denominator alike and the bound does **not** transport: `frostmanConstIn` is not monotone in the
index set, and `ConvexSpaceBody.IsFrostmanIn.of_subset` charges a volume share for the step.
This half of the conversion is by design a pure read-off with no refinement and no share
available, so the field is stated where the dichotomy asserts it, as the containment family
`Kakeya.familyIn tτ _ (Tθ l')`, which is exactly `nodesUnder` in the parent-family language.
Supplying the fibre reading that `Kakeya.ml1Boot.IsCaseTwoData.mid` needs is the business of
`Kakeya.ml1Boot.exists_caseTwoDataRepair`, which is where a share is available; blueprint
`note:ml1bootRawMidContainment` records the counting argument that does it.

With the fibre gone the coarse parent map `pθ` is not read by either field, so it is no longer
a parameter of this structure.

The `fine` field is `Kakeya.ml1Boot.IsCaseTwoData.fine` verbatim, stated for the unrefined `s'`
and the full node index sets; the fine-level fibre needs no such repair, being literally the
class `Tube.coverClass` of the first bullet. -/
structure IsCaseTwoRawUpper {ι κ l : Type*} [DecidableEq κ] {δ τ θ : NNReal}
    (p : Params) (ε' : ℝ) (j : ℕ) (s' : Finset ι) (T : ι → ShadedTube δ E)
    (tτ : Finset κ) (Tτ : κ → Tube τ E) (pτ : ι → κ)
    (tθ : Finset l) (Tθ : l → Tube θ E) : Prop where
  /-- (a) The Frostman constant of every fine fibre inside its `τ`-parent. -/
  fine : ∀ k ∈ tτ,
    frostmanConstIn (fibre s' pτ k) (fun i => (T i).toConvexSpaceBody)
        (Tτ k).toConvexSpaceBody
      ≤ (δ : ENNReal) ^ (-ε') * ((τ / δ : NNReal) : ENNReal) ^ p.η (j - 1)
  /-- (b) The Frostman constant of the middle tubes contained in a `θ`-parent, inside it. -/
  mid : ∀ l' ∈ tθ,
    frostmanConstIn (familyIn tτ (fun k => (Tτ k).toConvexSpaceBody) (Tθ l').toConvexSpaceBody)
        (fun k => (Tτ k).toConvexSpaceBody) (Tθ l').toConvexSpaceBody
      ≤ (δ : ENNReal) ^ (-ε') * ((θ / τ : NNReal) : ENNReal) ^ p.η (j - 1)

/-- **The raw Case (ii) data at the node families** (blueprint `lem:ml1bootCaseIIDataRaw`,
items (a), (b), (c)).

The two upper bounds of `Kakeya.ml1Boot.IsCaseTwoRawUpper` together with the Frostman *lower*
bound at every free scale of the `ε`-window, all three read directly off the node families of
the hierarchy.

No essential distinctness, no uniformity, no refinement of `s` and no containment in `B₁` is
asserted: all four are the business of `Kakeya.ml1Boot.exists_caseTwoDataRepair`.  The `lower`
field is `Kakeya.ml1Boot.IsCaseTwoData.lower` verbatim, for the unrefined index sets. -/
structure IsCaseTwoRawData {ι κ l : Type*} [DecidableEq κ] {δ τ θ : NNReal}
    (p : Params) (ε' : ℝ) (j : ℕ) (s' : Finset ι) (T : ι → ShadedTube δ E)
    (tτ : Finset κ) (Tτ : κ → Tube τ E) (pτ : ι → κ)
    (tθ : Finset l) (Tθ : l → Tube θ E) : Prop
    extends IsCaseTwoRawUpper p ε' j s' T tτ Tτ pτ tθ Tθ where
  /-- (c) The Frostman **lower** bound at every free scale `σ` of the `ε`-window and at every
  node of the level-`b` family `tτ`, which here is the unrefined one. -/
  lower : IsFreeScaleLowerBound δ p ε' j θ tτ Tτ

/-- **The fine read-off: the first bullet at the class of a `b`-node** (blueprint
`lem:ml1bootRawFineReadOff`).

`StickyKakeya.IsFrostmanDividingBlock.frostman_leaves`, instantiated at a level-`b` node — the
bullet is asserted at every one of them — with `Tube.coverClass` read as the parent-map
fibre of `assign_b` (`Kakeya.ml1Boot.fibre_eq_coverClass`) and the subpolynomial loss absorbed
into `δ ^ (-ε')` (`Kakeya.ml1Boot.eventually_dichotomyLoss_le`).  No refinement and no counting.

It is a declaration of its own, and not a field proved inline in
`Kakeya.ml1Boot.caseTwoDataRaw`, because each of that lemma's three items carries its own loss
absorption and its own spelling seams. -/
theorem caseTwoRawFine [Nontrivial E] {p : Params} {ε' εin : ℝ} (hε' : 0 < ε')
    (Cds : NNReal) (Kds cds : ℕ) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} [DecidableEq ι] {s s' : Finset ι} (T : ι → ShadedTube δ E)
        (𝒰' : Tube.UniformTubeSet s' (fun i => (T i).toTube)
          (Tube.ssfGridLen δ) Cds)
        (a b m : ℕ),
        IsCaseTwoInput p εin Cds Kds cds s T s' 𝒰' a b m →
        ∀ k ∈ 𝒰'.cover.indexSet b,
          frostmanConstIn (fibre s' (𝒰'.cover.assign b) k) (fun i => (T i).toConvexSpaceBody)
              (𝒰'.cover.tube b k).toConvexSpaceBody
            ≤ (δ : ENNReal) ^ (-ε') *
                ((Tube.gridScale δ (Tube.ssfGridLen δ) b / δ : NNReal) : ENNReal)
                  ^ p.η m := by
  have hδ0event : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, 0 < δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hδ
  filter_upwards [eventually_dichotomyLoss_le Cds Kds cds hε', hδ0event]
    with δ hδloss hδ0
  intro ι _i s s' T 𝒰' a b m hin k hk
  rw [ConvexSpaceBody.frostmanConstIn_eq_frostmanConstant]
  rw [fibre_eq_coverClass s' (𝒰'.cover.assign b) k]
  let L : ENNReal := (Cds : ENNReal) * StickyKakeya.totalLoss Cds Kds cds δ
  let Y : ENNReal :=
    ((Tube.gridScale δ (Tube.ssfGridLen δ) b / δ : NNReal) : ENNReal) ^ p.η m
  have hgR : 0 < (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ) := by
    exact_mod_cast (Tube.gridScale_pos hδ0 (Tube.ssfGridLen δ) b)
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hτdiv : 0 < ((Tube.gridScale δ (Tube.ssfGridLen δ) b / δ : NNReal) : ℝ) := by
    rw [NNReal.coe_div]
    exact div_pos hgR hδR
  have hblock : ConvexSpaceBody.frostmanConstant (Tube.coverClass s' (𝒰'.cover.assign b) k)
      (fun i => (T i).toConvexSpaceBody) (𝒰'.cover.tube b k).toConvexSpaceBody ≤ L * Y := by
    simpa [L, Y, Kakeya.ennreal_coe_nnreal_rpow hτdiv (p.η m), NNReal.coe_div]
      using hin.block.frostman_leaves k hk
  calc
    ConvexSpaceBody.frostmanConstant (Tube.coverClass s' (𝒰'.cover.assign b) k)
        (fun i => (T i).toConvexSpaceBody) (𝒰'.cover.tube b k).toConvexSpaceBody
        ≤ L * Y := hblock
    _ ≤ (δ : ENNReal) ^ (-ε') * Y := mul_le_mul_left hδloss Y

/-- **The middle read-off: the second bullet at the containment family** (blueprint
`lem:ml1bootRawMidReadOff`).

`StickyKakeya.IsFrostmanDividingBlock.frostman_nodes`, instantiated at a level-`a` node, with
`Tube.UniformTubeSet.nodesUnder` read as `Kakeya.familyIn` of the level-`b` index set
(`Kakeya.ml1Boot.familyIn_indexSet_eq_nodesIn`) and the loss absorbed as in
`Kakeya.ml1Boot.caseTwoRawFine`.

The family is the *containment* family — all `b`-nodes inside the coarse node — and **not** the
parent-map fibre of `ϖ_{b→a}`, which is in general a proper subfamily of it and to which the
bound does not descend; blueprint `note:ml1bootRawMidContainment`.  No parent map is read here,
so no coarse parent family is needed to state it. -/
theorem caseTwoRawMid [Nontrivial E] {p : Params} {ε' εin : ℝ} (hε' : 0 < ε')
    (Cds : NNReal) (Kds cds : ℕ) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} [DecidableEq ι] {s s' : Finset ι} (T : ι → ShadedTube δ E)
        (𝒰' : Tube.UniformTubeSet s' (fun i => (T i).toTube)
          (Tube.ssfGridLen δ) Cds)
        (a b m : ℕ),
        IsCaseTwoInput p εin Cds Kds cds s T s' 𝒰' a b m →
        ∀ l' ∈ 𝒰'.cover.indexSet a,
          frostmanConstIn
              (familyIn (𝒰'.cover.indexSet b)
                (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
                (𝒰'.cover.tube a l').toConvexSpaceBody)
              (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
              (𝒰'.cover.tube a l').toConvexSpaceBody
            ≤ (δ : ENNReal) ^ (-ε') *
                ((Tube.gridScale δ (Tube.ssfGridLen δ) a /
                  Tube.gridScale δ (Tube.ssfGridLen δ) b : NNReal) : ENNReal)
                  ^ p.η m := by
  have hδ0event : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, 0 < δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hδ
  filter_upwards [eventually_dichotomyLoss_le Cds Kds cds hε', hδ0event]
    with δ hδloss hδ0
  intro ι _i s s' T 𝒰' a b m hin l' hl'
  have hApos : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) := by
    exact_mod_cast (Tube.gridScale_pos hδ0 (Tube.ssfGridLen δ) a)
  have hBpos : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ) := by
    exact_mod_cast (Tube.gridScale_pos hδ0 (Tube.ssfGridLen δ) b)
  have hdivR : 0 < ((Tube.gridScale δ (Tube.ssfGridLen δ) a /
      Tube.gridScale δ (Tube.ssfGridLen δ) b : NNReal) : ℝ) := by
    rw [NNReal.coe_div]
    exact div_pos hApos hBpos
  rw [familyIn_indexSet_eq_nodesIn 𝒰' b ((𝒰'.cover.tube a l').toConvexSpaceBody)]
  rw [ConvexSpaceBody.frostmanConstIn_eq_frostmanConstant]
  rw [Kakeya.ennreal_coe_nnreal_rpow hdivR (p.η m), NNReal.coe_div]
  let L : ENNReal := (Cds : ENNReal) * StickyKakeya.totalLoss Cds Kds cds δ
  let X : ENNReal := ConvexSpaceBody.frostmanConstant
      (𝒰'.nodesIn b ((𝒰'.cover.tube a l').toConvexSpaceBody))
      (fun j' => (𝒰'.cover.tube b j').toConvexSpaceBody)
      ((𝒰'.cover.tube a l').toConvexSpaceBody)
  have hblock : X ≤ L * ENNReal.ofReal
      (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) /
        (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ p.η m) := by
    simpa [L, X, Tube.UniformTubeSet.nodesUnder] using hin.block.frostman_nodes l' hl'
  calc
    X ≤ L * ENNReal.ofReal
          (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) /
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ p.η m) := hblock
    _ ≤ (δ : ENNReal) ^ (-ε') * ENNReal.ofReal
          (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) /
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ p.η m) := by
      exact mul_le_mul_left hδloss (ENNReal.ofReal
        (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) /
          (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ p.η m))

/-- **Case (ii) repair, step 3: the lower bound at the unrefined node family** (blueprint
`lem:ml1bootRepairLower`).

The third bullet of `Kakeya.ml1Boot.IsCaseTwoInput` read off as
`Kakeya.ml1Boot.IsFreeScaleLowerBound` at the level-`b` node family of the hierarchy, with the
subpolynomial `StickyKakeya.totalLoss` absorbed into `δ ^ ε'`.  Nothing is transported and no
share bound is used.

## What this lemma no longer claims

It used to assert the bound at a *retained* node set `tτ ⊆ 𝒰'_b`, for `k` ranging over a
retained fibre, under a share hypothesis on a nonempty leaf refinement `s₀`, with loss
`δ ^ (4 ε')`.  That transport was its whole content and it rested on the refinement-stability
assumption of blueprint `prop:ml1bootLowerFrostmanStable`, which is refuted and undeliverable
(blueprint `note:ml1bootLowerFrostmanRetired`).  A Frostman lower bound is witnessed by a
single test body and no counting hypothesis, global or per-anchor, repairs that — so the
transport is deleted rather than repaired.  With it go the retained index sets, the share and
nonemptiness hypotheses on `s₀`, the coarse index and its map `pθ`, and the loss drops to
`δ ^ ε'`.  A consumer holding a retained `tτ ⊆ 𝒰'_b` reads the conclusion by restricting the
quantifier, which a universally quantified statement survives for free.  The containment
`T_σ ⊆ 2 · T_{θ,l}` that the conclusion used to carry is
`Kakeya.ml1Boot.rescale_le_dilate_two`.

Having deleted the transport this step does no work of its own beyond
`Kakeya.ml1Boot.caseTwoDataRaw`'s `lower` field; it is kept as a separate declaration because
it is the step blueprint `lem:ml1bootCaseIIDataRepair` cites by name.  Nothing cites it in Lean
yet: that lemma's intended producer `Kakeya.ml1Boot.exists_caseTwoDataRepair` is not a
declaration — see the module docstring.

## The bundle's accuracy is a free binder here

`εin` is unconstrained: this lemma reads the `block` field of
`Kakeya.ml1Boot.IsCaseTwoInput` alone, never the `card_le` clause that the accuracy governs.
It is the binder `Kakeya.ml1Boot.caseTwoDataRaw` uses for the same reason. -/
theorem repairLower [Nontrivial E] (_hdim : Module.finrank ℝ E = 3)
    {β γ₀ : ℝ} {p : Params} (_hp : p.Spec β γ₀) {ε' εin : ℝ} (hε' : 0 < ε')
    (Cds : NNReal) (Kds cds : ℕ) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} [DecidableEq ι] {s s' : Finset ι} (T : ι → ShadedTube δ E)
        (𝒰' : Tube.UniformTubeSet s' (fun i => (T i).toTube)
          (Tube.ssfGridLen δ) Cds)
        (a b m : ℕ),
        IsCaseTwoInput p εin Cds Kds cds s T s' 𝒰' a b m →
        IsFreeScaleLowerBound δ p ε' (m + 1)
          (Tube.gridScale δ (Tube.ssfGridLen δ) a)
          (𝒰'.cover.indexSet b) (𝒰'.cover.tube b) := by
  have hδ0event : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, 0 < δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hδ
  filter_upwards [eventually_dichotomyLoss_le Cds Kds cds hε', hδ0event]
    with δ hδloss hδ0
  intro ι _i s s' T 𝒰' a b m hin σ hσ k hk
  have hσpos : 0 < σ := IsScaleWindow.pos hσ
    (Tube.gridScale_pos hδ0 (Tube.ssfGridLen δ) b)
    (Tube.gridScale_pos hδ0 (Tube.ssfGridLen δ) a)
  have hσR : 0 < (σ : ℝ) := by exact_mod_cast hσpos
  have hτR : 0 < (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ) := by
    exact_mod_cast (Tube.gridScale_pos hδ0 (Tube.ssfGridLen δ) b)
  have hσdiv : 0 <
      ((σ / (Tube.gridScale δ (Tube.ssfGridLen δ) b : NNReal) : NNReal) : ℝ) := by
    rw [NNReal.coe_div]
    exact div_pos hσR hτR
  rw [Kakeya.ennreal_coe_nnreal_rpow hσdiv (p.η (m + 1)), NNReal.coe_div]
  rw [familyIn_indexSet_eq_nodesIn 𝒰' b ((𝒰'.cover.tube b k).rescale σ).toConvexSpaceBody]
  rw [ConvexSpaceBody.frostmanConstIn_eq_frostmanConstant]
  let L : ENNReal := (Cds : ENNReal) * StickyKakeya.totalLoss Cds Kds cds δ
  let X : ENNReal := ConvexSpaceBody.frostmanConstant
      (𝒰'.nodesIn b ((𝒰'.cover.tube b k).rescale σ).toConvexSpaceBody)
      (fun j' => (𝒰'.cover.tube b j').toConvexSpaceBody)
      ((𝒰'.cover.tube b k).rescale σ).toConvexSpaceBody
  have hblock : ENNReal.ofReal
        (((σ : ℝ) / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ p.η (m + 1))
        ≤ L * X := by
    simpa [L, X] using hin.block.frostman_lower σ hσ.coe_lower hσ.coe_upper k hk
  have hpow : (δ : ENNReal) ^ ε' * (δ : ENNReal) ^ (-ε') = 1 := by
    have hδne : (δ : ENNReal) ≠ 0 := by
      exact_mod_cast (ne_of_gt hδ0)
    have hδnt : (δ : ENNReal) ≠ ⊤ := by
      exact ENNReal.coe_ne_top
    rw [← ENNReal.rpow_add ε' (-ε') hδne hδnt]
    simp
  have hle : (δ : ENNReal) ^ ε' * L ≤ 1 := by
    calc
      (δ : ENNReal) ^ ε' * L ≤ (δ : ENNReal) ^ ε' * (δ : ENNReal) ^ (-ε') :=
        mul_le_mul_right hδloss ((δ : ENNReal) ^ ε')
      _ = 1 := by simpa using hpow
  calc
    (δ : ENNReal) ^ ε' * ENNReal.ofReal
          (((σ : ℝ) / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ p.η (m + 1))
        ≤ (δ : ENNReal) ^ ε' * (L * X) :=
          mul_le_mul_right hblock ((δ : ENNReal) ^ ε')
    _ = ((δ : ENNReal) ^ ε' * L) * X := by ac_rfl
    _ ≤ 1 * X := mul_le_mul_left hle X
    _ = X := by simp

/-- **Case (ii), first half: the raw data at the node families** (blueprint
`lem:ml1bootCaseIIDataRaw`).

Alternative (ii) of `StickyKakeya.dividingScalesFrostman`, packaged as
`Kakeya.ml1Boot.IsCaseTwoInput`, is read off at the two node parent families
`(𝒰'_b, P_b, assign_b)` and `(𝒰'_a, P_a, ϖ_{b→a})` of
`Kakeya.ml1Boot.isParentFamily_nodes_fine` and
`Kakeya.ml1Boot.exists_nodeParentFamilies_coarse`, at the grid scales
`τ = gridScale δ (ssfGridLen δ) b` and `θ = gridScale δ (ssfGridLen δ) a`, and with the
subpolynomial `StickyKakeya.totalLoss` of every bullet absorbed into `δ ^ (∓ ε')`.  The
exponent index is `j = m + 1`.

The three items are one declaration each — `Kakeya.ml1Boot.caseTwoRawFine`,
`Kakeya.ml1Boot.caseTwoRawMid` and `Kakeya.ml1Boot.repairLower` — and this lemma is their
conjunction and nothing else, each carrying its own loss absorption and its own spelling seams.

This is the half of blueprint `lem:ml1bootCaseIIData` that is pure read-off: nothing is
constructed and nothing is refined, so the conclusion is stated for `s'` and the full node
index sets, not for a subfamily.  Everything that *is* constructed — essential distinctness,
uniformity, the refinement of `s` and the containment in `B₁` — belongs to blueprint
`lem:ml1bootCaseIIDataRepair`, and the two are to compose into blueprint
`lem:ml1bootCaseIIData`, this half being applied at the smaller exponent `ε' / 8`.  Neither
composition step exists in Lean: their intended producers,
`Kakeya.ml1Boot.exists_caseTwoDataRepair` and `Kakeya.ml1Boot.exists_caseTwoData`, are not
declarations — see the module docstring.

## No coarse parent map is a binder any more

The lemma used to bind the induced map `ϖ_{b→a}` on nodes, with its two characterizing
hypotheses, because item (b) was stated at the fibre of that map.  It is stated at the
containment family instead — see the discussion in `Kakeya.ml1Boot.IsCaseTwoRawUpper`, and
blueprint `note:ml1bootRawMidContainment` — which is where the second bullet of
`StickyKakeya.IsFrostmanDividingBlock` asserts it, so nothing here reads `ϖ` and the binder is
gone.  The parent-family property of the fine half is likewise not read: it is
`Kakeya.ml1Boot.isParentFamily_nodes_fine`, whose extra injectivity input no item below needs.

The Case (ii) input is taken **at any accuracy**: the bundle's exponent enters as the free
binder `εin`, unconstrained and unrelated to `ε'`, because this lemma reads the three Frostman
bullets and never the first clause `Kakeya.ml1Boot.IsCaseTwoInput.card_le`, which is the only
clause the accuracy governs. -/
theorem caseTwoDataRaw [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {β γ₀ : ℝ} {p : Params} (hp : p.Spec β γ₀) {ε' εin : ℝ} (hε' : 0 < ε')
    (Cds : NNReal) (Kds cds : ℕ) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} [DecidableEq ι] {s s' : Finset ι} (T : ι → ShadedTube δ E)
        (𝒰' : Tube.UniformTubeSet s' (fun i => (T i).toTube)
          (Tube.ssfGridLen δ) Cds)
        (a b m : ℕ),
        IsCaseTwoInput p εin Cds Kds cds s T s' 𝒰' a b m →
        IsCaseTwoRawData p ε' (m + 1) s' T
          (𝒰'.cover.indexSet b) (𝒰'.cover.tube b) (𝒰'.cover.assign b)
          (𝒰'.cover.indexSet a) (𝒰'.cover.tube a) := by
  filter_upwards
    [caseTwoRawFine (E := E) hε' Cds Kds cds, caseTwoRawMid (E := E) hε' Cds Kds cds,
      repairLower (E := E) hdim hp hε' Cds Kds cds]
    with δ hfine hmid hd
  intro ι _i s s' T 𝒰' a b m hin
  refine
    { fine := ?_,
      mid := ?_,
      lower := ?_ }
  · intro k hk
    simpa using hfine T 𝒰' a b m hin k hk
  · intro l' hl'
    simpa using hmid T 𝒰' a b m hin l' hl'
  · change δ ∈ {x : NNReal | ∀ {ι : Type u} [DecidableEq ι] {s s' : Finset ι}
        (T : ι → ShadedTube x E) (𝒰' : Tube.UniformTubeSet s'
          (fun i => (T i).toTube) (Tube.ssfGridLen x) Cds) (a₀ b₀ m₀ : ℕ),
        IsCaseTwoInput p εin Cds Kds cds s T s' 𝒰' a₀ b₀ m₀ →
        IsFreeScaleLowerBound x p ε' (m₀ + 1)
          (Tube.gridScale x (Tube.ssfGridLen x) a₀)
          (𝒰'.cover.indexSet b₀) (𝒰'.cover.tube b₀)} at hd
    exact hd T 𝒰' a b m hin

/-- **Case (ii) repair: the mass chain** (blueprint `lem:ml1bootCaseIIRepairMassChain`).

The mass half of `Kakeya.ml1Boot.caseTwoRepairChains`: the three refinement links
`s → s' → s₂ → s₀`, read at the constants the caller and the three passes hand over, composed by
`Kakeya.ml1Boot.repairFullnessChain` at the common exponent `ε' / 4`.

## The links are spelled as the call site produces them

The outer link is the caller's `Kakeya.ml1Boot.IsCaseTwoInput.refine_mass` at accuracy `ε' / 8`;
the middle link is `Kakeya.ml1Boot.IsRepairThreePass.refineMid`, whose constant is `δ ^ (2 ϖ)`
and which therefore appears here as `(δ : ℝ) ^ (2 * (ε' / 8))` and not as the arithmetically
equal `(δ : ℝ) ^ (ε' / 4)`; the inner link is `.refineLast`.  The literal spellings are
deliberate — in Lean `2 * (ε' / 8)` and `ε' / 4` are not definitionally equal — so the exponent
normalisation happens *inside* this proof, where `Kakeya.ml1Boot.isCRefinement_mono` weakens the
two `ε' / 8` links to the common `ε' / 4`, the largest of the three and hence forced.

## What this half does not read

No count, no banding, no containment in `B₁` and no smallness of `δ` beyond `δ ≤ 1`.  In
particular `s₀.Nonempty` is *not* assumed: `Kakeya.ml1Boot.repairFullnessChain` re-derives it
from `hfull`, which is why it is a conjunct of the conclusion here while it is a hypothesis of
`Kakeya.ml1Boot.caseTwoRepairChains` (whose count half does read it).

This half lands at `3 ε' / 4` and stops there; the a-fortiori weakening to `ε'` that the caller
wants is done once, in `Kakeya.ml1Boot.caseTwoRepairChains`. -/
theorem caseTwoRepairMassChain {ι : Type*} {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ε' η : ℝ} (hε' : 0 < ε')
    {s s' s₂ s₀ : Finset ι} (T : ι → ShadedTube δ E)
    (hfull : (δ : ENNReal) ^ η ≤ ShadedBody.fullness s (fun i => (T i).toShadedBody))
    (hrefOuter : ShadedBody.IsCRefinement s' (fun i => (T i).toShadedBody) s
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (ε' / 8), by positivity⟩)
    (hrefMid : ShadedBody.IsCRefinement s₂ (fun i => (T i).toShadedBody) s'
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (2 * (ε' / 8)), by positivity⟩)
    (hrefInner : ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s₂
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (ε' / 8), by positivity⟩) :
    s₀.Nonempty ∧
      ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s
        (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (3 * ε' / 4), by positivity⟩ ∧
      (δ : ENNReal) ^ (3 * ε' / 4 + η)
        ≤ ShadedBody.fullness s₀ (fun i => (T i).toShadedBody) := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hmono : (⟨(δ : ℝ) ^ (ε' / 4), by positivity⟩ : NNReal) ≤
      ⟨(δ : ℝ) ^ (ε' / 8), by positivity⟩ := by
    change (δ : ℝ) ^ (ε' / 4) ≤ (δ : ℝ) ^ (ε' / 8)
    exact Real.rpow_le_rpow_of_exponent_ge hδR hδ1R (by linarith : ε' / 8 ≤ ε' / 4)
  have hrefOuter' : ShadedBody.IsCRefinement s' (fun i => (T i).toShadedBody) s
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (ε' / 4), by positivity⟩ :=
    isCRefinement_mono hrefOuter hmono
  have hrefInner' : ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s₂
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (ε' / 4), by positivity⟩ :=
    isCRefinement_mono hrefInner hmono
  have hrefMid' : ShadedBody.IsCRefinement s₂ (fun i => (T i).toShadedBody) s'
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (ε' / 4), by positivity⟩ := by
    have hmideq : (⟨(δ : ℝ) ^ (ε' / 4), by positivity⟩ : NNReal) =
        ⟨(δ : ℝ) ^ (2 * (ε' / 8)), by positivity⟩ := by
      apply NNReal.coe_injective
      change (δ : ℝ) ^ (ε' / 4) = (δ : ℝ) ^ (2 * (ε' / 8))
      congr 1
      ring
    exact isCRefinement_mono hrefMid (le_of_eq hmideq)
  have hres := repairFullnessChain hδ (T := T) (ε' := ε' / 4) (η := η) (hfull := hfull)
    (h₁ := hrefOuter') (h₂ := hrefMid') (h₃ := hrefInner')
  refine ⟨hres.2.1, ?_, ?_⟩
  · have h_eq : (⟨(δ : ℝ) ^ (3 * ε' / 4), by positivity⟩ : NNReal) =
        ⟨(δ : ℝ) ^ (3 * (ε' / 4)), by positivity⟩ := by
      exact NNReal.coe_injective (by
        change (δ : ℝ) ^ (3 * ε' / 4) = (δ : ℝ) ^ (3 * (ε' / 4))
        congr 1
        ring)
    exact isCRefinement_mono hres.1 (le_of_eq h_eq)
  · have hglob : (δ : ENNReal) ^ (3 * (ε' / 4) + η) = (δ : ENNReal) ^ (3 * ε' / 4 + η) := by
      congr 1
      ring
    simpa [hglob] using hres.2.2

/-- **Case (ii) repair: the count chain** (blueprint `lem:ml1bootCaseIIRepairCountChain`).

The count half of `Kakeya.ml1Boot.caseTwoRepairChains`: the two outer counts and the middle
*refinement* link, run through `Kakeya.ml1Boot.repairCountChain` at the common exponent `ε' / 4`.

## The links are spelled as the call site produces them

The outer count is the caller's `Kakeya.ml1Boot.IsCaseTwoInput.card_le` at accuracy `ε' / 8`;
the middle link is `Kakeya.ml1Boot.IsRepairThreePass.refineMid`, carried here with the constant
`(δ : ℝ) ^ (2 * (ε' / 8))` that the second pass hands over — the same spelling as in
`Kakeya.ml1Boot.caseTwoRepairMassChain`, and the one hypothesis the two halves share — and the
inner count is `.card`.  Monotonicity of `δ ^ (-·)` weakens the two `ε' / 8` counts to `ε' / 4`
inside this proof.

## Where the slack is, and why the middle link is priced as it is

`Kakeya.ml1Boot.repairCountChain` prices the middle link at `2 · ε'/4` and the two outer counts
at `ε'/4` each, so this side lands at *exactly* `4 · ε'/4 = ε'` and has no slack; that is the
binding line of the whole repair.  It consumes the middle link through the banding clause
`hband`, which is what converts a mass share back into a count share, so `hlam`, `hband` and the
containment `hball` are read here and nowhere else in the split.  The side hypothesis
`hsmall : (δ : ℝ) ^ (ε' / 4) ≤ 1 / 4` is not an exponent and is absorbable into the `∀ᶠ δ` of the
consumer by `Kakeya.absorb_const_le_rpow_neg`.

## What this half does not read

No mass, no fullness and no refinement of `(𝕋, Y)` itself: `hrefOuter` and `hrefInner` of
`Kakeya.ml1Boot.caseTwoRepairChains` are the mass half's alone.  The nonemptiness of `s₀` and the
three inclusions are read here, the inclusions being `Kakeya.ml1Boot.repairCountChain`'s; only the
two outer ones are binders, the middle inclusion `s₂ ⊆ s'` being `hrefMid.1.1`. -/
theorem caseTwoRepairCountChain [Nontrivial E] {ι : Type*} {δ : NNReal} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1)
    {ε' : ℝ} (hε' : 0 < ε') (hsmall : (δ : ℝ) ^ (ε' / 4) ≤ 1 / 4)
    {s s' s₂ s₀ : Finset ι} (T : ι → ShadedTube δ E)
    (hs₀ : s₀.Nonempty) (hsub' : s' ⊆ s) (hsub₀ : s₀ ⊆ s₂)
    (hball : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ ConvexSpaceBody.closedUnitBall)
    {lam : NNReal} (hlam : 0 < lam)
    (hband : ∀ i ∈ s, (lam : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ 2 * (lam : ENNReal) * volume (T i).carrier)
    (hcardOuter : (s.card : ℝ) ≤ (δ : ℝ) ^ (-(ε' / 8)) * (s'.card : ℝ))
    (hrefMid : ShadedBody.IsCRefinement s₂ (fun i => (T i).toShadedBody) s'
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (2 * (ε' / 8)), by positivity⟩)
    (hcardInner : (s₂.card : ℝ) ≤ (δ : ℝ) ^ (-(ε' / 8)) * (s₀.card : ℝ)) :
    (s.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s₀.card : ℝ) ∧
      frostmanConstIn s₀ (fun i => (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
        ≤ (δ : ENNReal) ^ (-ε')
          * frostmanConstIn s (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall := by
  classical
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hweaken : (δ : ℝ) ^ (-(ε' / 8)) ≤ (δ : ℝ) ^ (-(ε' / 4)) := by
    exact Real.rpow_le_rpow_of_exponent_ge hδR hδ1R (by linarith : -(ε' / 4) ≤ -(ε' / 8))
  have hcard₁ : (s.card : ℝ) ≤ (δ : ℝ) ^ (-(ε' / 4)) * (s'.card : ℝ) := by
    exact le_trans hcardOuter
      (mul_le_mul_of_nonneg_right hweaken (by exact_mod_cast Nat.zero_le s'.card))
  have hcard₂ : (s₂.card : ℝ) ≤ (δ : ℝ) ^ (-(ε' / 4)) * (s₀.card : ℝ) := by
    exact le_trans hcardInner
      (mul_le_mul_of_nonneg_right hweaken (by exact_mod_cast Nat.zero_le s₀.card))
  have h2 : (2 : ℝ) * (ε' / 8) = ε' / 4 := by ring
  have hrefMid' : ShadedBody.IsCRefinement s₂ (fun i => (T i).toShadedBody) s'
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (ε' / 4), by positivity⟩ := by
    simpa [h2] using hrefMid
  have h4 : (4 : ℝ) * (ε' / 4) = ε' := by ring
  have hc := repairCountChain (ε' := ε' / 4) hδ hδ1 hsmall T hs₀ hsub' (hrefMid.1.1) hsub₀
    hball hlam hband hcard₁ hrefMid' hcard₂
  exact ⟨by simpa [h4] using hc.1, by simpa [h4] using hc.2⟩

/-- **Case (ii) repair: the two chains wired to the three-pass output** (blueprint
`lem:ml1bootCaseIIRepairChains`).

The mass chain `Kakeya.ml1Boot.repairFullnessChain` and the count chain
`Kakeya.ml1Boot.repairCountChain` run along the same three links
`s → s' → s₂ → s₀`, and this lemma is the two of them read at one common exponent and wired to
the shape `Kakeya.ml1Boot.IsRepairThreePass` records, at `ϖ = ε' / 8` — the shape blueprint
`lem:ml1bootRepairThreePass` is to deliver; its intended producer
`Kakeya.ml1Boot.exists_repairThreePass` is not a declaration, see the module docstring.  It is
one of the two pieces split off from the intended proof of blueprint
`lem:ml1bootCaseIIDataRepair`, so that the wiring left to be formalized there is named rather
than described.

## This lemma is now the conjunction of its two halves

The two chains have themselves been split off, into `Kakeya.ml1Boot.caseTwoRepairMassChain` and
`Kakeya.ml1Boot.caseTwoRepairCountChain`, whose hypothesis lists this signature unions — the two
halves share only the middle link `hrefMid` and the ambient `0 < δ ≤ 1`, and each reads its links
at the constants spelled here — and whose conclusions it concatenates.  The one further step is
the a-fortiori weakening of the mass side from `3 ε' / 4` to `ε'`, the last two conjuncts.  The
mass half re-derives `s₀.Nonempty` and returns it; only the count half reads `hs₀`.

It is kept as a statement in its own right, rather than replaced by its two halves, because it is
what the call site in blueprint `lem:ml1bootCaseIIDataRepair` is to apply, the four clauses of
the Case (ii) refinement item being read off it together.  That call site does not exist in
Lean; the intended `Kakeya.ml1Boot.exists_caseTwoDataRepair` is not a declaration.

## The links are spelled as the call site produces them

The outer link is the caller's, `Kakeya.ml1Boot.IsCaseTwoInput.card_le` and `.refine_mass` at
accuracy `ε' / 8`; the middle link is `Kakeya.ml1Boot.IsRepairThreePass.refineMid`, whose
constant is `δ ^ (2 ϖ)` and which therefore appears here as `(δ : ℝ) ^ (2 * (ε' / 8))` and not
as the arithmetically equal `(δ : ℝ) ^ (ε' / 4)`; the inner link is `.refineLast` together with
`.card`.  The literal spellings are deliberate: the point of this lemma is that the three-pass
output and the input bundle apply to it with no massaging at the call site.  They are reproduced
identically in the two halves, since in Lean `2 * (ε' / 8)`, `2 * ε' / 8` and `ε' / 4` are not
definitionally equal and a mismatch would reintroduce at every seam exactly the rewriting the
split removes; the exponent normalisation to the common `ε' / 4` — the largest of the three links
and hence forced — happens inside each half.

## The two exponents of the conclusion, and why both forms are asserted

The count side lands at *exactly* `ε'` (`4 · ε'/4`) and has no slack; the mass side lands at
`3 ε' / 4`.  The first four conjuncts are the sharp bounds, and the last two are the `ε'`
readings of the mass side that `Kakeya.ml1Boot.IsCaseTwoRepairData.refine_refinement` and
`.refine_fullness` ask for verbatim — at `η = p.ηGamma γ` the sixth conjunct *is*
`refine_fullness`.  They are stated rather than left to the consumer for the same reason the
hypotheses are spelled as they are.  The fourth conjunct is the Frostman bound *relative* to
`C_F(𝕋, B₁)`; combining it with `Kakeya.ml1Boot.IsCaseFamily.frostman` is what gives
`.refine_frostman` at `-ε' - p.ηGamma γ`, and that combination is the consumer's.

## The binders

The signature is long because a three-link chain has three link hypotheses, two count
hypotheses and the count chain's own side data — the `B₁` containment, the banding `lam` and
`δ ^ (ε'/4) ≤ 1/4`, which is not an exponent and is absorbable into the `∀ᶠ δ` of the consumer
by `Kakeya.absorb_const_le_rpow_neg`.  There is no shared mathematical concept to bundle them
under: `hband` and `hcardOuter` already live in `Kakeya.ml1Boot.IsCaseTwoInput` and the middle
link in neither bundle.  `Kakeya.ml1Boot.repairCountChain`, whose hypotheses these largely are,
carries the same list for the same reason.  The split into the two halves is what makes the list
readable: each half carries only its own share of it, and this signature is their union.

The three inclusions `s' ⊆ s`, `s₂ ⊆ s'` and `s₀ ⊆ s₂` are *not* binders here, even though the
count half reads them: each is the `.1.1` of the corresponding refinement link `hrefOuter`,
`hrefMid`, `hrefInner`, all three of which this signature already carries, so they are recovered
by projection where `Kakeya.ml1Boot.caseTwoRepairCountChain` is applied.  That half keeps `hsub'`
and `hsub₀` as binders because it does not carry the outer and inner links at all.

The blueprint additionally assumes `η ≥ 0` and that `s`, `s'`, `s₂` are nonempty; none is used —
`hfull` forces `s` nonempty and the other two follow from `hs₀` along the inclusions, which is
also why `s₀.Nonempty` is a hypothesis here (it is `Kakeya.ml1Boot.IsRepairThreePass.nonemptyLast`
at the call site, hence free) rather than a further conjunct of the conclusion. -/
theorem caseTwoRepairChains [Nontrivial E] {ι : Type*} {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ε' η : ℝ} (hε' : 0 < ε') (hsmall : (δ : ℝ) ^ (ε' / 4) ≤ 1 / 4)
    {s s' s₂ s₀ : Finset ι} (T : ι → ShadedTube δ E)
    (hs₀ : s₀.Nonempty)
    (hball : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ ConvexSpaceBody.closedUnitBall)
    (hfull : (δ : ENNReal) ^ η ≤ ShadedBody.fullness s (fun i => (T i).toShadedBody))
    {lam : NNReal} (hlam : 0 < lam)
    (hband : ∀ i ∈ s, (lam : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ 2 * (lam : ENNReal) * volume (T i).carrier)
    (hcardOuter : (s.card : ℝ) ≤ (δ : ℝ) ^ (-(ε' / 8)) * (s'.card : ℝ))
    (hrefOuter : ShadedBody.IsCRefinement s' (fun i => (T i).toShadedBody) s
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (ε' / 8), by positivity⟩)
    (hrefMid : ShadedBody.IsCRefinement s₂ (fun i => (T i).toShadedBody) s'
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (2 * (ε' / 8)), by positivity⟩)
    (hrefInner : ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s₂
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (ε' / 8), by positivity⟩)
    (hcardInner : (s₂.card : ℝ) ≤ (δ : ℝ) ^ (-(ε' / 8)) * (s₀.card : ℝ)) :
    ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s
        (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (3 * ε' / 4), by positivity⟩ ∧
      (δ : ENNReal) ^ (3 * ε' / 4 + η)
        ≤ ShadedBody.fullness s₀ (fun i => (T i).toShadedBody) ∧
      (s.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s₀.card : ℝ) ∧
      frostmanConstIn s₀ (fun i => (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
        ≤ (δ : ENNReal) ^ (-ε')
          * frostmanConstIn s (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall ∧
      ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s
        (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩ ∧
      (δ : ENNReal) ^ (ε' + η) ≤ ShadedBody.fullness s₀ (fun i => (T i).toShadedBody) := by
  obtain ⟨hne, href34, hfull34⟩ :=
    caseTwoRepairMassChain hδ hδ1 hε' T hfull hrefOuter hrefMid hrefInner
  obtain ⟨hcard, hfrost⟩ :=
    caseTwoRepairCountChain hδ hδ1 hε' hsmall T hs₀ hrefOuter.1.1 hrefInner.1.1
      hball hlam hband hcardOuter hrefMid hcardInner
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδR1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have conj5 : ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩ := by
    exact isCRefinement_mono href34 (by
      exact_mod_cast (Real.rpow_le_rpow_of_exponent_ge hδR hδR1 (by linarith)))
  have conj6 : (δ : ENNReal) ^ (ε' + η) ≤
      ShadedBody.fullness s₀ (fun i => (T i).toShadedBody) := by
    exact le_trans
      (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)) hfull34
  exact ⟨href34, hfull34, hcard, hfrost, conj5, conj6⟩

/-- **Case (ii) repair: the fine fibre bound at the retained node set** (blueprint
`lem:ml1bootCaseIIRepairFine`).

Two links on the fibres, composed by one multiplication: the raw fine bound at the *unrefined*
leaf set `s'` — `Kakeya.ml1Boot.IsCaseTwoRawUpper.fine`, which blueprint
`lem:ml1bootCaseIIDataRepair` is to take at `ε' / 8` — and the fibrewise Frostman
transport of the three passes,`Kakeya.ml1Boot.IsRepairThreePass.fibreFrostman` at `ϖ = ε' / 8`.
The output is `Kakeya.ml1Boot.IsCaseTwoRepairData.fine` at the retained node set `t'τ`.  It is
the second of the two pieces split off from the intended proof of that blueprint lemma, whose
producer `Kakeya.ml1Boot.exists_caseTwoDataRepair` is not a declaration — see the module
docstring.

## The three spellings are the call site's

`hraw` carries `δ ^ (-(ε'/8))` and `htrans` carries `δ ^ (-3 * (ε'/8))` because those are what
the two source fields read after their own `ε'` is instantiated at `ε' / 8`; the conclusion
carries `δ ^ (-ε')` because that is what the target field reads.  None of the three is
normalised, so the lemma applies to them with no massaging at the call site.

The side condition of `htrans` is met at `K = (Tτ k).toConvexSpaceBody` by `hcontain`, read at
the members of `fibre s' pτ k`: such an `i` lies in `s'` and has `pτ i = k`, so
`(T i).toConvexSpaceBody ≤ (Tτ (pτ i)).toConvexSpaceBody = (Tτ k).toConvexSpaceBody`.  That is
the only part of the blueprint's parent-family hypothesis this lemma uses, so it is assumed as
the clause itself — `Kakeya.ml1Boot.IsParentFamily.le_parent` — rather than as the bundle; at
the call site it is `Kakeya.ml1Boot.isParentFamily_nodes_fine`'s `le_parent` field.

## The exponent, and where the slack is

`ε'/8 + 3ε'/8 = ε'/2`, so the composition lands at `δ ^ (-ε'/2)`; the conclusion is then the
a-fortiori weakening to `δ ^ (-ε')`, which uses only `0 < δ ≤ 1` and `ε' > 0`.  Unlike the count
chain of `Kakeya.ml1Boot.caseTwoRepairChains`, this item therefore has real slack.

The right-hand factor is carried as an opaque `((τ / δ : NNReal) : ENNReal) ^ ηj`: the two
source fields and the target field all read it at `ηj = p.η (j - 1)`, and nothing here inspects
it.  The blueprint's `δ ≤ τ ≤ 1` and `j ≥ 1` are likewise not used. -/
theorem caseTwoRepairFine {ι κ : Type*} [DecidableEq κ] {δ τ : NNReal} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {ε' ηj : ℝ} (hε' : 0 < ε') {s' s₀ : Finset ι} {tτ t'τ : Finset κ}
    (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ) (hsub : t'τ ⊆ tτ)
    (hcontain : ∀ i ∈ s', (T i).toConvexSpaceBody ≤ (Tτ (pτ i)).toConvexSpaceBody)
    (hraw : ∀ k ∈ tτ,
      frostmanConstIn (fibre s' pτ k) (fun i => (T i).toConvexSpaceBody)
          (Tτ k).toConvexSpaceBody
        ≤ (δ : ENNReal) ^ (-(ε' / 8)) * ((τ / δ : NNReal) : ENNReal) ^ ηj)
    (htrans : ∀ k ∈ t'τ, ∀ K : ConvexSpaceBody E,
      (∀ i ∈ fibre s' pτ k, (T i).toConvexSpaceBody ≤ K) →
      frostmanConstIn (fibre s₀ pτ k) (fun i => (T i).toConvexSpaceBody) K
        ≤ (δ : ENNReal) ^ (-3 * (ε' / 8))
          * frostmanConstIn (fibre s' pτ k) (fun i => (T i).toConvexSpaceBody) K) :
    ∀ k ∈ t'τ,
      frostmanConstIn (fibre s₀ pτ k) (fun i => (T i).toConvexSpaceBody)
          (Tτ k).toConvexSpaceBody
        ≤ (δ : ENNReal) ^ (-ε') * ((τ / δ : NNReal) : ENNReal) ^ ηj := by
  intro k hk
  let X : ENNReal := ((τ / δ : NNReal) : ENNReal) ^ ηj
  have hδne : (δ : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hδ)
  have hδle1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hside : ∀ i ∈ fibre s' pτ k, (T i).toConvexSpaceBody ≤ (Tτ k).toConvexSpaceBody := by
    intro i hi
    have hi' : i ∈ s' ∧ pτ i = k := by
      simpa [fibre] using hi
    rw [← hi'.2]
    exact hcontain i hi'.1
  have htr : frostmanConstIn (fibre s₀ pτ k) (fun i => (T i).toConvexSpaceBody)
        (Tτ k).toConvexSpaceBody
      ≤ (δ : ENNReal) ^ (-3 * (ε' / 8))
        * frostmanConstIn (fibre s' pτ k) (fun i => (T i).toConvexSpaceBody) (Tτ k).toConvexSpaceBody :=
    htrans k hk (Tτ k).toConvexSpaceBody hside
  have hrawk : frostmanConstIn (fibre s' pτ k) (fun i => (T i).toConvexSpaceBody)
        (Tτ k).toConvexSpaceBody
      ≤ (δ : ENNReal) ^ (-(ε' / 8)) * X := by
    simpa [X] using hraw k (hsub hk)
  have hpow : (δ : ENNReal) ^ (-3 * (ε' / 8)) * (δ : ENNReal) ^ (-(ε' / 8))
      = (δ : ENNReal) ^ (-(ε' / 2)) := by
    rw [← ENNReal.rpow_add (-3 * (ε' / 8)) (-(ε' / 8)) hδne ENNReal.coe_ne_top]
    exact congrArg (fun x : ℝ => (δ : ENNReal) ^ x) (by ring)
  have hafort : (δ : ENNReal) ^ (-(ε' / 2)) ≤ (δ : ENNReal) ^ (-ε') := by
    exact ENNReal.rpow_le_rpow_of_exponent_ge hδle1 (by linarith)
  calc
    frostmanConstIn (fibre s₀ pτ k) (fun i => (T i).toConvexSpaceBody) (Tτ k).toConvexSpaceBody
        ≤ (δ : ENNReal) ^ (-3 * (ε' / 8))
            * frostmanConstIn (fibre s' pτ k) (fun i => (T i).toConvexSpaceBody) (Tτ k).toConvexSpaceBody :=
          htr
    _ ≤ (δ : ENNReal) ^ (-3 * (ε' / 8)) * ((δ : ENNReal) ^ (-(ε' / 8)) * X) :=
          mul_le_mul_right hrawk ((δ : ENNReal) ^ (-3 * (ε' / 8)))
    _ = (δ : ENNReal) ^ (-(ε' / 2)) * X := by
          rw [← mul_assoc, hpow]
    _ ≤ (δ : ENNReal) ^ (-ε') * X := by
          exact mul_le_mul_left hafort X

/-- **The trim's share condition holds for all small `δ`** (blueprint
`lem:ml1bootTrimShareCond`).

The `hshare` hypothesis of the three-pass lemma, blueprint `lem:ml1bootRepairThreePass` — whose
intended producer `Kakeya.ml1Boot.exists_repairThreePass` is not a declaration, see the module
docstring — at the brackets
`m₊ = 2 A C_u` and `m₋ = A / C_u` that `Kakeya.ml1Boot.trimBracketUpper` and
`Kakeya.ml1Boot.trimBracketLower` deliver, with `A = λ_* |T| N_b` the factor they share.

That factor cancels formally — it appears on both sides — so the condition is really
`4 C_u ² δ ^ (6 w) ≤ δ ^ w`, that is `4 C_u ² ≤ δ ^ (-5 w)`, which holds eventually because
`C_u` is fixed before `δ`.  Stated for every `A` so that the caller never has to know that the
cancellation is legitimate: no positivity or finiteness of `A` is used. -/
theorem eventually_trimShareCond (C : NNReal) (hC : 0 < C) {w : ℝ} (hw : 0 < w) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ A : ENNReal,
      2 * ((δ : ENNReal) ^ (6 * w) * (2 * (A * (C : ENNReal))))
        ≤ (δ : ENNReal) ^ w * (A * ((C : ENNReal))⁻¹) := by
  have habs : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      4 * ((C : ENNReal) ^ (2 : ℕ)) ≤ (δ : ENNReal) ^ (-(5 * w)) := by
    have hCposR : (0 : ℝ) < 4 * ((C : ℝ) ^ (2 : ℕ)) := by positivity
    filter_upwards [nnreal_eventually_of_real_eventually
        (Kakeya.absorb_const_le_rpow_neg hCposR (show (0 : ℝ) < 5 * w by positivity)),
      self_mem_nhdsWithin] with δ hδabsR hδ0
    have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
    rw [ennreal_coe_nnreal_rpow hδR (-(5 * w))]
    calc
      4 * ((C : ENNReal) ^ (2 : ℕ)) = ENNReal.ofReal (4 * ((C : ℝ) ^ (2 : ℕ))) := by
        simp [pow_two]
      _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(5 * w))) := ENNReal.ofReal_le_ofReal hδabsR
  filter_upwards [habs, self_mem_nhdsWithin] with δ hδabs hδ0
  have hδne : (δ : ENNReal) ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt hδ0)
  have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCne : (C : ENNReal) ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt hC)
  have hCtop : (C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCinvc : (C : ENNReal) ^ (2 : ℕ) * ((C : ENNReal) ⁻¹) = (C : ENNReal) := by
    rw [pow_two, mul_assoc, ENNReal.mul_inv_cancel hCne hCtop, mul_one]
  have hpow : (δ : ENNReal) ^ (-(5 * w)) * (δ : ENNReal) ^ (6 * w) = (δ : ENNReal) ^ w := by
    rw [← ENNReal.rpow_add _ _ hδne hδtop]
    congr 1
    ring
  have hbig : (4 * ((C : ENNReal) ^ (2 : ℕ))) * (δ : ENNReal) ^ (6 * w) ≤ (δ : ENNReal) ^ w := by
    calc
      (4 * ((C : ENNReal) ^ (2 : ℕ))) * (δ : ENNReal) ^ (6 * w)
          ≤ (δ : ENNReal) ^ (-(5 * w)) * (δ : ENNReal) ^ (6 * w) := by
            gcongr
      _ = (δ : ENNReal) ^ w := by simp [hpow]
  have key : 4 * (δ : ENNReal) ^ (6 * w) * (C : ENNReal)
      ≤ (δ : ENNReal) ^ w * ((C : ENNReal))⁻¹ := by
    calc
      4 * (δ : ENNReal) ^ (6 * w) * (C : ENNReal)
          = 4 * (δ : ENNReal) ^ (6 * w) * ((C : ENNReal) ^ (2 : ℕ) * ((C : ENNReal) ⁻¹)) :=
            congrArg (fun x => 4 * (δ : ENNReal) ^ (6 * w) * x) hCinvc.symm
      _ = (4 * ((C : ENNReal) ^ (2 : ℕ))) * (δ : ENNReal) ^ (6 * w) * (C : ENNReal) ⁻¹ := by
            ac_rfl
      _ ≤ (δ : ENNReal) ^ w * ((C : ENNReal))⁻¹ := by
            gcongr
  intro A
  calc
    2 * ((δ : ENNReal) ^ (6 * w) * (2 * (A * (C : ENNReal))))
        = (4 * (δ : ENNReal) ^ (6 * w) * (C : ENNReal)) * A := by
          ring
    _ ≤ ((δ : ENNReal) ^ w * ((C : ENNReal))⁻¹) * A := by
          gcongr
    _ = (δ : ENNReal) ^ w * (A * ((C : ENNReal))⁻¹) := by
          ring

/-- **The fibrewise upper bracket the trim consumes, read off the hierarchy and the banding**
(blueprint `lem:ml1bootTrimBracketUpper`).

The `hplus` hypothesis of the three-pass lemma, blueprint `lem:ml1bootRepairThreePass` (intended
producer `Kakeya.ml1Boot.exists_repairThreePass`, not a declaration — see the module
docstring), at
`m₊ = 2 λ_* |T| C_u N_b`.  It is the upper half of `Kakeya.ml1Boot.sum_bracket_of_band` at the
class of a `b`-node, composed with the upper class bracket
`Tube.UniformTubeSet.card_class_le`; the parent-map fibre and the class are the same
`Finset`, by `Kakeya.ml1Boot.fibre_eq_coverClass`. -/
theorem trimBracketUpper {ι : Type*} [DecidableEq ι] [Nontrivial E] {δ : NNReal}
    {s s' : Finset ι} {T : ι → ShadedTube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s' (fun i => (T i).toTube) N Cu) {b : ℕ} (hb : b ≤ N)
    (hsub : s' ⊆ s) {lam : NNReal} {v : ENNReal}
    (hc : ∀ i ∈ s, volume (T i).carrier = v)
    (hband : ∀ i ∈ s, (lam : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ 2 * ((lam : ENNReal) * volume (T i).carrier))
    {k : ι} (hk : k ∈ 𝒰.cover.indexSet b) :
    (∑ i ∈ fibre s' (𝒰.cover.assign b) k, volume (T i).shade)
      ≤ 2 * ((lam : ENNReal) * v * ((Cu : ENNReal) * (𝒰.branchingN b : ENNReal))) := by
  classical
  have hXsub : fibre s' (𝒰.cover.assign b) k ⊆ s := by
    simpa [fibre] using (Finset.filter_subset (fun i => 𝒰.cover.assign b i = k) s').trans hsub
  have hbks : (∑ i ∈ fibre s' (𝒰.cover.assign b) k, volume (T i).shade) ≤
      2 * ((lam : ENNReal) * v * ((fibre s' (𝒰.cover.assign b) k).card : ENNReal)) := by
    exact (sum_bracket_of_band (s := s) (X := fibre s' (𝒰.cover.assign b) k)
      (hc := hc) (hband := hband) hXsub).2
  have hfcc : (fibre s' (𝒰.cover.assign b) k).card ≤ Cu * (𝒰.branchingN b) := by
    rw [fibre_eq_coverClass s' (𝒰.cover.assign b) k]
    exact 𝒰.card_class_le b hb k hk
  have henc : ((fibre s' (𝒰.cover.assign b) k).card : ENNReal) ≤
      (Cu : ENNReal) * (𝒰.branchingN b : ENNReal) := by
    exact_mod_cast hfcc
  calc
    (∑ i ∈ fibre s' (𝒰.cover.assign b) k, volume (T i).shade)
        ≤ 2 * ((lam : ENNReal) * v * ((fibre s' (𝒰.cover.assign b) k).card : ENNReal)) :=
          hbks
    _ ≤ 2 * ((lam : ENNReal) * v * ((Cu : ENNReal) * (𝒰.branchingN b : ENNReal))) := by
      exact mul_le_mul_right
        (mul_le_mul_right henc ((lam : ENNReal) * v)) (2 : ENNReal)

/-- **The aggregate lower bracket the trim consumes, read off the hierarchy and the banding**
(blueprint `lem:ml1bootTrimBracketLower`).

The `hminus` hypothesis of the three-pass lemma, blueprint `lem:ml1bootRepairThreePass`
(intended producer `Kakeya.ml1Boot.exists_repairThreePass`, not a declaration — see the module
docstring), at
`m₋ = λ_* |T| N_b / C_u`.  This is `Kakeya.ml1Boot.aggregateLower_of_classBracket` at the
hierarchy's own leaf set — that is, at `s₁ = s'` and count retention `r = 1`, where the retention
hypothesis is trivial — followed by division by `C_u`.

The aggregate form is what makes it available at all: no bracket is asserted at an individual
node of the leaf set the passes leave behind.  See blueprint
`note:ml1bootEssDistinctFibrewiseShare`. -/
theorem trimBracketLower {ι : Type*} [Nontrivial E] {δ : NNReal}
    {s s' : Finset ι} {T : ι → ShadedTube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s' (fun i => (T i).toTube) N Cu) (hCu : 0 < Cu)
    {b : ℕ} (hb : b ≤ N) (hsub : s' ⊆ s) {lam : NNReal} {v : ENNReal}
    (hc : ∀ i ∈ s, volume (T i).carrier = v)
    (hband : ∀ i ∈ s, (lam : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ 2 * ((lam : ENNReal) * volume (T i).carrier)) :
    ((lam : ENNReal) * v * (𝒰.branchingN b : ENNReal) * ((Cu : ENNReal))⁻¹)
        * ((𝒰.cover.indexSet b).card : ENNReal)
      ≤ ∑ i ∈ s', volume (T i).shade := by
  classical
  let w : ι → ENNReal := fun i => volume (T i).shade
  have hagg :
      (lam : ENNReal) * v * ((1 : ENNReal) * (𝒰.branchingN b : ENNReal))
          * ((𝒰.cover.indexSet b).card : ENNReal)
        ≤ (Cu : ENNReal) * ∑ i ∈ s', w i := by
    exact
      aggregateLower_of_classBracket (𝒰 := 𝒰) (hb := hb) (s₁ := s')
        (hs₁ := Finset.Subset.refl s') (w := w) (c := fun i => volume (T i).carrier)
        (lam := (lam : ENNReal)) (v := v) (r := 1)
        (hc := fun i hi => hc i (hsub hi))
        (hband := fun i hi => hband i (hsub hi))
        (hretain := by simp)
  have hCu0 : (Cu : ENNReal) ≠ 0 := ne_of_gt (ENNReal.coe_pos.mpr hCu)
  have hCuT : (Cu : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCuinv : (Cu : ENNReal) * (Cu : ENNReal)⁻¹ = 1 := ENNReal.mul_inv_cancel hCu0 hCuT
  calc
    ((lam : ENNReal) * v * (𝒰.branchingN b : ENNReal) * ((Cu : ENNReal))⁻¹)
        * ((𝒰.cover.indexSet b).card : ENNReal)
      = ((lam : ENNReal) * v * ((1 : ENNReal) * (𝒰.branchingN b : ENNReal))
            * ((𝒰.cover.indexSet b).card : ENNReal)) * (Cu : ENNReal)⁻¹ := by
          ring
    _ ≤ ((Cu : ENNReal) * ∑ i ∈ s', w i) * (Cu : ENNReal)⁻¹ := by
          exact mul_le_mul_left hagg (Cu : ENNReal)⁻¹
    _ = (Cu : ENNReal) * (Cu : ENNReal)⁻¹ * (∑ i ∈ s', w i) := by
          ring
    _ = 1 * (∑ i ∈ s', w i) := by
          rw [hCuinv]
    _ = ∑ i ∈ s', w i := by
          rw [one_mul]
    _ = ∑ i ∈ s', volume (T i).shade := by
          rfl

/-- **A coarse parent-map fibre sits inside the containment family** (blueprint
`lem:ml1bootFibreSubsetNodes`).

Over a coarse node `l`, the fibre of `ϖ_{b→a}` inside the level-`b` node index set is contained
in the family of level-`b` nodes *contained in* the tube of `l`.  This is the containment
clause `Kakeya.ml1Boot.IsParentFamily.le_parent` of `Kakeya.ml1Boot.IsCoarseNodeParents.parent`
together with a `Finset.filter` unfolding, and nothing else.

It is the first conjunct of `Kakeya.ml1Boot.card_nodesIn_le_card_coarseFibre` with neither of
that lemma's two extra hypotheses — no lower bound on the hierarchy's constant, and no
membership `l ∈ 𝒰'.cover.indexSet a` — which is what makes it usable as the discharge of the
nonemptiness side condition inside `Kakeya.ml1Boot.caseTwoMidRetained`. -/
theorem fibre_subset_nodesIn {ι : Type*} [DecidableEq ι] {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal}
    (𝒰' : Tube.UniformTubeSet s' T N Cu) {pθ : ι → ι}
    (hcnp : IsCoarseNodeParents 𝒰' a b pθ) (l : ι) :
    fibre (𝒰'.cover.indexSet b) pθ l
      ⊆ 𝒰'.nodesIn b (𝒰'.cover.tube a l).toConvexSpaceBody := by
  intro k hk
  rw [fibre] at hk
  have hk_index : k ∈ 𝒰'.cover.indexSet b := (Finset.mem_filter.mp hk).1
  have hk_pθ : pθ k = l := (Finset.mem_filter.mp hk).2
  rw [Tube.UniformTubeSet.nodesIn, Finset.mem_filter]
  refine ⟨hk_index, ?_⟩
  have hle := hcnp.parent.le_parent k hk_index
  simpa [hk_pθ] using hle

/-- **The exponent bookkeeping of the middle-bound descent** (blueprint
`lem:ml1bootMidShareCompose`).

The arithmetic half of `Kakeya.ml1Boot.caseTwoMidRetained`, isolated so that the geometric
half has no `ENNReal.rpow` manipulation in it.  Composing the share cost `κ⁻¹` at
`κ = δ ^ (3 ε' / 4)` with step 0's bound `δ ^ (-2 (ε' / 8))` gives the exponent
`-3 ε' / 4 - ε' / 4 = -ε'`, which is exactly what the conclusion of
`Kakeya.ml1Boot.IsCaseTwoData.mid` asks for.

*Why `3 ε' / 4` and not `ε' / 4`.*  This lemma is where the budget for `κ` is visible, and
`3 ε' / 4` is the whole of it: step 0 lands at `-2 (ε' / 8) = -ε' / 4` and the target is `-ε'`,
so `κ⁻¹` may cost anything up to `δ ^ (-3 ε' / 4)`.  An earlier form demanded
`κ = δ ^ (ε' / 4)` and then discarded the unused `ε' / 2` by an `a fortiori` step against
`δ ≤ 1` — a demand four times stronger, in units of the repair's own accuracy `ϖ = ε' / 8`, than
the argument needs (`2 ϖ` demanded against a `6 ϖ` budget).  Since a smaller `κ` is a *weaker*
`Kakeya.ml1Boot.IsFibrewiseEmptyOrShare`, weakening the demand to the true budget strengthens
every consumer, and it is what brings the antecedent within reach of what the post-selection trim
of `Kakeya.ml1Boot.fibrewiseTrim` supplies (`δ ^ (3 ϖ)`, comfortably below `δ ^ (6 ϖ)`).  The
composition now lands *exactly* on `-ε'` with no slack, so `hδ1` is still consumed but only at
`le_refl`.

The literal spellings `-2 * (ε' / 8)` and `3 * ε' / 4` are the ones
`Kakeya.ml1Boot.caseTwoRawMidFibre` and `Kakeya.ml1Boot.IsFibrewiseEmptyOrShare` produce at the
call site; in Lean they are not definitionally the arithmetically equal `-(3 * ε' / 4)`, so the
normalisation happens here.

`0 < ε'` is no longer a hypothesis: it was needed only to make the discarded `ε' / 2` point the
right way, and with the exponents landing exactly there is nothing to discard. -/
theorem mid_le_of_share_compose {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {ε' : ℝ} {A B R : ENNReal}
    (hAB : A ≤ ((δ : ENNReal) ^ (3 * ε' / 4))⁻¹ * B)
    (hB : B ≤ (δ : ENNReal) ^ (-2 * (ε' / 8)) * R) :
    A ≤ (δ : ENNReal) ^ (-ε') * R := by
  have hδne : (δ : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt hδ0)
  have hδle1 : (δ : ENNReal) ≤ 1 := by
    exact_mod_cast hδ1
  calc
    A ≤ ((δ : ENNReal) ^ (3 * ε' / 4))⁻¹ * B := hAB
    _ = (δ : ENNReal) ^ (-(3 * ε' / 4)) * B := by
      rw [ENNReal.rpow_neg]
    _ ≤ (δ : ENNReal) ^ (-(3 * ε' / 4)) * ((δ : ENNReal) ^ (-2 * (ε' / 8)) * R) := by
      exact mul_le_mul_of_nonneg_left hB (by positivity)
    _ = (δ : ENNReal) ^ (-(3 * ε' / 4)) * (δ : ENNReal) ^ (-2 * (ε' / 8)) * R := by
      ac_rfl
    _ = (δ : ENNReal) ^ (-(3 * ε' / 4) + -2 * (ε' / 8)) * R := by
      rw [← ENNReal.rpow_add (-(3 * ε' / 4)) (-2 * (ε' / 8)) hδne ENNReal.coe_ne_top]
    _ = (δ : ENNReal) ^ (-ε') * R := by
      congr 1
      congr 1
      ring
    _ ≤ (δ : ENNReal) ^ (-ε') * R := by
      have hstep : (δ : ENNReal) ^ (-ε') ≤ (δ : ENNReal) ^ (-ε') :=
        ENNReal.rpow_le_rpow_of_exponent_ge hδle1 (by linarith)
      exact mul_le_mul_of_nonneg_right hstep (by positivity)

/-- **The middle bound at the retained fine family, given the fibrewise share** (blueprint
`lem:ml1bootMidRetained`).

The composite of step 0 — `Kakeya.ml1Boot.caseTwoRawMidFibre`, which moves the dichotomy's
*containment* family `Kakeya.familyIn` to the coarse parent-map *fibre* at the **unrefined**
level-`b` node family — with the descent
`Kakeya.ml1Boot.frostmanConstIn_retainedFibre_le`, which moves that bound to the fibre of a
*retained* subfamily `tτ` at the cost `κ⁻¹` once `tτ` is fibrewise empty-or-share at `κ`
(`Kakeya.ml1Boot.IsFibrewiseEmptyOrShare`).  At `κ = δ ^ (3 ε' / 4)` and an incoming accuracy of
`ε' / 8` the total lands at `δ ^ (-ε')`, which is exactly
`Kakeya.ml1Boot.IsCaseTwoData.mid`; the arithmetic is
`Kakeya.ml1Boot.mid_le_of_share_compose`, and `3 ε' / 4` is the whole of the budget that
arithmetic leaves for `κ⁻¹` — see that lemma for why the earlier `ε' / 4` was four times
stronger than the argument needs.

This is the one field of `Kakeya.ml1Boot.IsCaseTwoData` that the repair, blueprint
`lem:ml1bootCaseIIDataRepair`, does not deliver — blueprint
`note:ml1bootRepairEDMidRetained` and `Kakeya.ml1Boot.IsCaseTwoRepairData` are the record of
why — so this lemma is precisely what blueprint `lem:ml1bootCaseIIData` needs in order to
discharge the hypothesis of `Kakeya.ml1Boot.IsCaseTwoRepairData.isCaseTwoData` under the
fibrewise dichotomy.  Neither blueprint lemma has a Lean producer: their intended names,
`Kakeya.ml1Boot.exists_caseTwoDataRepair` and `Kakeya.ml1Boot.exists_caseTwoData`, are not
declarations — see the module docstring.

## Nonemptiness is not a hypothesis

`Kakeya.ml1Boot.caseTwoRawMidFibre` asks that the containment family be nonempty at the coarse
node in question.  Here that side condition is discharged rather than assumed: when the
retained fibre is empty the bound is free (`ConvexSpaceBody.frostmanConstIn_empty`), and when
it is not, the retained fibre sits inside the full fibre, which sits inside the containment
family by the containment clause `Kakeya.ml1Boot.IsParentFamily.le_parent` of
`Kakeya.ml1Boot.IsCoarseNodeParents.parent`.

## The hierarchy's constant carries no lower bound

`Kakeya.ml1Boot.caseTwoRawMidFibre` and `Kakeya.ml1Boot.card_nodesIn_le_card_coarseFibre` are
stated at `1 ≤ Cu`, while the `Cds` of `StickyKakeya.dividingScalesFrostman` reaches this
chain through `Kakeya.ml1Boot.IsCaseTwoInput` with no lower bound of its own.  The fix is the
one blueprint `lem:ml1bootCaseIIThreePassCall` prescribes — its intended producer
`Kakeya.ml1Boot.exists_caseTwoThreePass` is not a declaration, so nothing uses it yet; see the
module docstring — namely: run them at `max 1 Cds` against
`Tube.UniformTubeSet.mono`, which leaves the cover, the nodes and the branching
numbers untouched, so every clause above transfers unchanged. -/
theorem caseTwoMidRetained [Nontrivial E] (p : Params) {ε' : ℝ} (hε' : 0 < ε') (Cds : NNReal) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} [DecidableEq ι] {s' : Finset ι} {T : ι → Tube δ E} {N : ℕ}
        (a b m : ℕ) (𝒰' : Tube.UniformTubeSet s' T N Cds) (pθ : ι → ι),
        IsCoarseNodeParents 𝒰' a b pθ →
        (∀ l' ∈ 𝒰'.cover.indexSet a,
          frostmanConstIn
              (familyIn (𝒰'.cover.indexSet b)
                (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
                (𝒰'.cover.tube a l').toConvexSpaceBody)
              (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
              (𝒰'.cover.tube a l').toConvexSpaceBody
            ≤ (δ : ENNReal) ^ (-(ε' / 8)) *
                ((Tube.gridScale δ N a / Tube.gridScale δ N b : NNReal) : ENNReal)
                  ^ p.η m) →
        ∀ {tτ : Finset ι}, tτ ⊆ 𝒰'.cover.indexSet b →
          IsFibrewiseEmptyOrShare (𝒰'.cover.indexSet b) (𝒰'.cover.indexSet a) tτ pθ
              ((δ : ENNReal) ^ (3 * ε' / 4)) →
          ∀ l' ∈ 𝒰'.cover.indexSet a,
            frostmanConstIn (fibre tτ pθ l')
                (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
                (𝒰'.cover.tube a l').toConvexSpaceBody
              ≤ (δ : ENNReal) ^ (-ε') *
                  ((Tube.gridScale δ N a / Tube.gridScale δ N b : NNReal) : ENNReal)
                    ^ p.η m := by
  have hδ1evt : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), δ ≤ 1 := by
    have hReal : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), δ ≤ (1 : ℝ) := by
      apply Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))
      intro δ hδ
      simp only [Set.mem_Ioo] at hδ
      linarith [hδ.2]
    simpa using (nnreal_eventually_of_real_eventually hReal)
  filter_upwards [caseTwoRawMidFibre (E := E) p (ε' := ε' / 8) (by linarith) (le_max_left 1 Cds),
      self_mem_nhdsWithin, hδ1evt] with δ hstep hδ0 hδ1
  intro ι _ s' T N a b m 𝒰' pθ hcnp hmid tτ hsub hshare l' hl'
  by_cases hfib : fibre tτ pθ l' = ∅
  · rw [hfib, ConvexSpaceBody.frostmanConstIn_empty]
    exact zero_le
  · have hk0 : (fibre tτ pθ l').Nonempty := Finset.nonempty_iff_ne_empty.mpr hfib
    obtain ⟨k₀, hk₀⟩ := hk0
    have hm : k₀ ∈ tτ := (Finset.mem_filter.mp hk₀).1
    have hpeq : pθ k₀ = l' := (Finset.mem_filter.mp hk₀).2
    let 𝒱 : Tube.UniformTubeSet s' T N (max 1 Cds) :=
      𝒰'.mono (le_max_right 1 Cds)
    have hcnpV : IsCoarseNodeParents 𝒱 a b pθ := by
      constructor
      · exact hcnp.le_index
      · exact hcnp.le_gridLen
      · exact hcnp.nodes_carry_leaf
      · exact hcnp.assign_comp
      · exact hcnp.parent
    have hlV : l' ∈ 𝒱.cover.indexSet a := by
      exact hl'
    have hmidV : ∀ k ∈ 𝒱.cover.indexSet a,
        frostmanConstIn (𝒱.nodesIn b (𝒱.cover.tube a k).toConvexSpaceBody)
          (fun k' => (𝒱.cover.tube b k').toConvexSpaceBody)
          (𝒱.cover.tube a k).toConvexSpaceBody
          ≤ (δ : ENNReal) ^ (-(ε' / 8)) *
              ((Tube.gridScale δ N a / Tube.gridScale δ N b : NNReal) : ENNReal)
                ^ p.η m := by
      intro k hk
      exact hmid k hk
    have hkV : k₀ ∈ fibre (𝒱.cover.indexSet b) pθ l' := by
      change k₀ ∈ (𝒱.cover.indexSet b).filter (fun i => pθ i = l')
      exact Finset.mem_filter.mpr ⟨by exact hsub hm, by exact hpeq⟩
    have hneV : (𝒱.nodesIn b (𝒱.cover.tube a l').toConvexSpaceBody).Nonempty :=
      ⟨k₀, fibre_subset_nodesIn 𝒱 hcnpV l' hkV⟩
    have hδE : (δ : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hδ0)
    have hδT : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hκ : ((δ : ENNReal) ^ (3 * ε' / 4)) ≠ 0 :=
      ne_of_gt (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ0) hδT)
    have hB : frostmanConstIn (fibre (𝒱.cover.indexSet b) pθ l')
          (fun k => (𝒱.cover.tube b k).toConvexSpaceBody)
          (𝒱.cover.tube a l').toConvexSpaceBody
        ≤ (δ : ENNReal) ^ (-2 * (ε' / 8)) *
            ((Tube.gridScale δ N a / Tube.gridScale δ N b : NNReal) : ENNReal)
              ^ p.η m :=
        hstep a b m 𝒱 pθ hcnpV hmidV l' hlV hneV
    have hAB : frostmanConstIn (fibre tτ pθ l')
        (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
        (𝒰'.cover.tube a l').toConvexSpaceBody
      ≤ ((δ : ENNReal) ^ (3 * ε' / 4))⁻¹ *
          frostmanConstIn (fibre (𝒰'.cover.indexSet b) pθ l')
            (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
            (𝒰'.cover.tube a l').toConvexSpaceBody :=
        frostmanConstIn_retainedFibre_le 𝒰' hcnp hsub hκ hshare hl'
    exact mid_le_of_share_compose hδ0 hδ1 hAB hB

/-- **The coarse node parent bundle, from the Case (ii) input** (blueprint
`lem:ml1bootCoarseParentsFromInput`).

`Kakeya.ml1Boot.exists_nodeParentFamilies_coarse` produces the induced map `ϖ_{b→a}` together
with the two clauses that characterize it; this lemma packages its output with the two index
inequalities read off `StickyKakeya.IsFrostmanDividingBlock` through
`Kakeya.ml1Boot.IsCaseTwoInput.block` — `a < b` and `b ≤ ssfGridLen δ` — into the bundle
`Kakeya.ml1Boot.IsCoarseNodeParents` that `Kakeya.ml1Boot.caseTwoMidRetained` consumes and that
blueprint `lem:ml1bootCaseIIDataRepair` is to consume (its intended producer
`Kakeya.ml1Boot.exists_caseTwoDataRepair` is not a declaration; see the module docstring).

The two hypotheses that are not in the bundle are the standing hypothesis that every level-`b`
node carries a leaf and node-body injectivity at the *coarse* index; both are owed by whoever
builds the hierarchy (blueprint `note:ml1bootNodeBodyInjectivity`), and both are hypotheses of
blueprint `lem:ml1bootCaseIIData`, which is this lemma's only intended caller.  It has no Lean
caller today: `Kakeya.ml1Boot.exists_caseTwoData` is not a declaration — see the module
docstring.  The accuracy `ε'` of the input bundle is a free binder: no clause read here
mentions it. -/
theorem exists_coarseNodeParents_of_caseTwoInput [Nontrivial E] {ι : Type u}
    {δ : NNReal} {p : Params} {ε' : ℝ} {Cds : NNReal} {Kds cds : ℕ}
    {s s' : Finset ι} {T : ι → ShadedTube δ E}
    {𝒰' : Tube.UniformTubeSet s' (fun i => (T i).toTube)
      (Tube.ssfGridLen δ) Cds}
    {a b m : ℕ}
    (hin : IsCaseTwoInput p ε' Cds Kds cds s T s' 𝒰' a b m)
    (hnodes : ∀ k ∈ 𝒰'.cover.indexSet b, ∃ i ∈ s', 𝒰'.cover.assign b i = k)
    (hinjCoarse : Set.InjOn (fun k => (𝒰'.cover.tube a k).toConvexSpaceBody)
      (𝒰'.cover.indexSet a)) :
    ∃ pθ : ι → ι, IsCoarseNodeParents 𝒰' a b pθ := by
  obtain ⟨pθ, hassign, hparent⟩ :=
    exists_nodeParentFamilies_coarse 𝒰' hin.block.coarse_lt_fine.le hin.block.fine_le
      hnodes hinjCoarse
  exact ⟨pθ, hin.block.coarse_lt_fine.le, hin.block.fine_le, hnodes, hassign, hparent⟩

/-- **Case (ii): the three passes at the node families of the hierarchy** (blueprint
`lem:ml1bootCaseIIThreePassCall`, restored form; harvested from `zzk` `cc8a4a299` and
re-verified here).

`Kakeya.ml1Boot.exists_repairThreePass_edUpToMult_banded` specialised to the Case (ii) call
site, landing in the threaded record `Kakeya.ml1Boot.IsRepairThreePassThreaded`.  This is
**additive**: `Kakeya.ml1Boot.caseTwoRepairData_of_isRepairThreePass` and the records
`Kakeya.ml1Boot.IsCaseTwoData` / `Kakeya.ml1Boot.IsCaseTwoRepairData` are untouched, and the
seam between this lemma and them is *not* bridged here — see below.

*What this call site discharges.*  The input band the restored (R2) pass needs comes free from
`Kakeya.ml1Boot.IsCaseTwoInput.band`, restricted along `Kakeya.ml1Boot.IsCaseTwoInput.subset`;
the two trim brackets come from `Kakeya.ml1Boot.trimBracketUpper` and
`Kakeya.ml1Boot.trimBracketLower` at the hierarchy constant corrected to `max 1 Cds` via
`Tube.UniformTubeSet.mono`; the share condition from
`Kakeya.ml1Boot.eventually_trimShareCond`; the scale ladder `δ ≤ τ ≤ θ ≤ 1` from
`Kakeya.ml1Boot.IsCoarseNodeParents`.

*What it does not discharge, and deliberately leaves visible in its signature.*  The two
node-family `Kakeya.IsEDUpToMult` hypotheses at a shared `Co : ℕ` are hypotheses of this lemma
too. Nothing in this development supplies them: `Kakeya.ml1Boot.hasBoundedOverlap_nodes`
supplies only the leaf-mediated `Kakeya.ml1Boot.HasBoundedOverlap`, which does not transfer to
the body-level predicate, and `Kakeya.ml1Boot.not_exists_essDistinct_parentFamily`'s axial
pencil shows that a *fixed* multiplicity is false for node families in general. A supplier
would have to produce a `δ`-dependent multiplicity. -/
theorem exists_caseTwoThreePass_banded [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {β γ₀ : ℝ} {ηKF ηKKT : ℝ → ℝ} {p : Params}
    (_hp : p.Spec β γ₀) (_hpη : p.EtaGammaSpec β γ₀ ηKF ηKKT)
    {γ : ℝ} (_hγ : γ ∈ Set.Icc γ₀ 1) {ε' : ℝ} (hε' : 0 < ε')
    (Cunif Cds : NNReal) (Kds cds Co : ℕ) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} [DecidableEq ι] {s s' : Finset ι} (T : ι → ShadedTube δ E)
        (𝒰' : Tube.UniformTubeSet s' (fun i => (T i).toTube)
          (Tube.ssfGridLen δ) Cds)
        (a b m : ℕ) (pθ : ι → ι),
        IsCaseFamily p γ Cunif s T →
        IsCaseTwoInput p (ε' / 8) Cds Kds cds s T s' 𝒰' a b m →
        IsCoarseNodeParents 𝒰' a b pθ →
        Set.InjOn (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) (𝒰'.cover.indexSet b) →
        IsEDUpToMult (𝒰'.cover.indexSet b) (fun k => (𝒰'.cover.tube b k).carrier) Co →
        IsEDUpToMult (𝒰'.cover.indexSet a) (fun k => (𝒰'.cover.tube a k).carrier) Co →
        ∃ s₂ ⊆ s', ∃ s₀ ⊆ s₂, ∃ t'τ ⊆ 𝒰'.cover.indexSet b, ∃ t'θ ⊆ 𝒰'.cover.indexSet a,
          ∃ Y₃ : ι → ShadedTube δ E,
            IsRepairThreePassThreaded (ε' / 8) T (𝒰'.cover.tube b) (𝒰'.cover.assign b)
              (𝒰'.cover.tube a) pθ (𝒰'.cover.indexSet b) (𝒰'.cover.indexSet a)
              s' s₂ s₀ t'τ t'θ Y₃ := by
  have hReal : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), δ ≤ (1 : ℝ) := by
    apply Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))
    intro δ hδ
    simp only [Set.mem_Ioo] at hδ
    linarith [hδ.2]
  have hδ1evt : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), δ ≤ 1 := by
    simpa using (nnreal_eventually_of_real_eventually hReal)
  let C : ENNReal := ((max 1 Cds : NNReal) : ENNReal)
  have hCposNN : (0 : NNReal) < max 1 Cds :=
    lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) (le_max_left 1 Cds)
  have hshareEv : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ A : ENNReal,
      2 * ((δ : ENNReal) ^ (6 * (ε' / 8)) * (2 * (A * (C : ENNReal))))
        ≤ (δ : ENNReal) ^ (ε' / 8) * (A * ((C : ENNReal))⁻¹) := by
    simpa [C] using eventually_trimShareCond (max 1 Cds) hCposNN
      (show (0 : ℝ) < ε' / 8 by linarith)
  have hTP := exists_repairThreePass_edUpToMult_banded hdim
    (show (0 : ℝ) < ε' / 8 by linarith) Co
  filter_upwards [hTP, self_mem_nhdsWithin, hδ1evt, hshareEv] with δ hTP hδ0 hδ1 hSh
  intro ι inst s s' T 𝒰' a b m pθ hfam hin hcnp hinjFine hEDτ hEDθ
  let N := Tube.ssfGridLen δ
  let τ := Tube.gridScale δ N b
  let θ := Tube.gridScale δ N a
  have hb : b ≤ N := hcnp.le_gridLen
  have hab : a ≤ b := hcnp.le_index
  have ha : a ≤ N := hab.trans hb
  have hδτ : δ ≤ τ := by
    simpa [τ, N] using (le_gridScale hδ1 hb)
  have hτθ : τ ≤ θ := by
    simpa [τ, θ] using (gridScale_le_gridScale hδ1 N hab)
  have hθ1 : θ ≤ 1 := by
    simpa [θ] using (Tube.gridScale_le_one hδ1 N a)
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hShade_s : 0 < ∑ i ∈ s, volume (T i).shade := by
    exact sum_shade_pos_of_fullness_ge hδ0 T hfam.fullness
  have hShade_s' : 0 < ∑ i ∈ s', volume (T i).shade := by
    exact sum_shade_pos_of_isCRefinement hδ0 T hin.refine_mass hShade_s
  have hs'ne : s'.Nonempty := nonempty_of_sum_shade_pos T hShade_s'
  have hBall : ∀ i ∈ s', (T i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    exact hfam.ball i (hin.subset hi)
  have hEd : (s' : Set ι).Pairwise (fun i j =>
      IsEssentiallyDistinct (T i).carrier (T j).carrier) := by
    exact Set.Pairwise.mono (Finset.coe_subset.mpr hin.subset) hfam.essDistinct
  have hFine : IsParentFamily s' (fun i => (T i).toTube) (𝒰'.cover.indexSet b)
      (𝒰'.cover.tube b) (𝒰'.cover.assign b) := by
    simpa [N] using (isParentFamily_nodes_fine 𝒰' hb hinjFine)
  have hCoarse : IsParentFamily (𝒰'.cover.indexSet b) (𝒰'.cover.tube b)
      (𝒰'.cover.indexSet a) (𝒰'.cover.tube a) pθ := hcnp.parent
  have hMassFull : (∑ i ∈ s', volume (T i).shade) ≠ ⊤ := by
    refine ne_of_lt (ENNReal.sum_lt_top.mpr ?_)
    intro i hi
    have hballSub : (T i).shade ⊆ Metric.closedBall 0 1 :=
      (T i).shade_subset.trans (hBall i hi)
    exact lt_of_le_of_lt (measure_mono hballSub) (MeasureTheory.measure_closedBall_lt_top)
  obtain ⟨lam0, hLamPos, hbandRaw⟩ := hin.band
  let lam : ENNReal := (lam0 : ENNReal)
  obtain ⟨i₀, hi₀⟩ := hfam.nonempty
  let v : ENNReal := volume (T i₀).carrier
  have hcarrierAll : ∀ i ∈ s, volume (T i).carrier = v := by
    intro i hi
    simpa [v] using (Tube.volume_carrier_eq_volume_carrier (T i).toTube (T i₀).toTube)
  have hbandS : ∀ i ∈ s, lam * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ 2 * (lam * volume (T i).carrier) := by
    intro i hi
    have h0 := hbandRaw i hi
    constructor
    · simpa [lam] using h0.1
    · simpa [lam, mul_assoc] using h0.2
  have hbandS' : ∀ i ∈ s', (lam0 : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ 2 * (lam0 : ENNReal) * volume (T i).carrier := by
    intro i hi
    exact hbandRaw i (hin.subset hi)
  let 𝒱 : Tube.UniformTubeSet s' (fun i => (T i).toTube) N (max 1 Cds) :=
    𝒰'.mono (le_max_right 1 Cds)
  have hCuV : (0 : NNReal) < max 1 Cds :=
    lt_of_lt_of_le (by norm_num) (le_max_left 1 Cds)
  let A : ENNReal := lam * v * (𝒰'.branchingN b : ENNReal)
  let mplus : ENNReal := 2 * (A * C)
  let mminus : ENNReal := A * C⁻¹
  have hplus : ∀ k ∈ 𝒰'.cover.indexSet b,
      (∑ i ∈ fibre s' (𝒰'.cover.assign b) k, volume (T i).shade) ≤ mplus := by
    intro k hk
    have hup := trimBracketUpper (𝒰 := 𝒱) (hb := hb) (hsub := hin.subset)
      (hc := hcarrierAll) (hband := hbandS) (hk := hk)
    have htest_cov : (𝒱.cover.assign b) = (𝒰'.cover.assign b) := rfl
    have htest_br : (𝒱.branchingN b) = (𝒰'.branchingN b) := rfl
    simpa [mplus, A, C, lam, v, htest_cov, htest_br, mul_assoc, mul_comm, mul_left_comm] using hup
  have hminus : mminus * ((𝒰'.cover.indexSet b).card : ENNReal) ≤
      ∑ i ∈ s', volume (T i).shade := by
    have hlo := trimBracketLower (𝒰 := 𝒱) (hCu := hCuV) (hb := hb) (hsub := hin.subset)
      (hc := hcarrierAll) (hband := hbandS)
    have htest_br' : (𝒱.branchingN b) = (𝒰'.branchingN b) := rfl
    have htest_idx : (𝒱.cover.indexSet b) = (𝒰'.cover.indexSet b) := rfl
    rw [htest_br', htest_idx] at hlo
    simpa [mminus, A, C, lam, v, mul_assoc] using hlo
  have hshare : 2 * ((δ : ENNReal) ^ (6 * (ε' / 8)) * mplus) ≤
      (δ : ENNReal) ^ (ε' / 8) * mminus := by
    simpa [mplus, mminus] using hSh A
  exact hTP τ θ hδτ hτθ hθ1 (ι := ι) (κ := ι) (s' := s') (tτ := 𝒰'.cover.indexSet b)
    (tθ := 𝒰'.cover.indexSet a) T (𝒰'.cover.tube b) (𝒰'.cover.assign b)
    (𝒰'.cover.tube a) pθ mplus mminus hs'ne hShade_s' hMassFull hBall hEd hFine hCoarse
    lam0 hLamPos hbandS' hEDτ hEDθ hplus hminus hshare

/-- **Case (ii): the repair's output record from the three passes** (blueprint
`lem:ml1bootCaseIIDataRepair`, everything in it except the three passes themselves).

Given the Case (ii) input bundle `Kakeya.ml1Boot.IsCaseTwoInput` at accuracy `ε' / 8` and a
three-pass bundle `Kakeya.ml1Boot.IsRepairThreePass` at the same `ε' / 8`, run at the two node
parent families of the hierarchy, this assembles `Kakeya.ml1Boot.IsCaseTwoRepairData` at
accuracy `ε'`.  Every field is a citation:

* the four global clauses of item (i) — the refinement, the fullness, the Frostman constant in
  `B₁` and (through it) the count — are `Kakeya.ml1Boot.caseTwoRepairChains`, fed with the
  bundle's `card_le`, `refine_mass` and `band` and the passes' `refineMid`, `refineLast`,
  `card` and `nonemptyLast`;
* uniformity is `Kakeya.ml1Boot.IsRepairThreePass.unif`, at the same constant
  `Kakeya.ml1Boot.uniformize.C 3` the record asks for;
* the fine fibre bound of item (ii) is `Kakeya.ml1Boot.caseTwoRepairFine`, composing
  `Kakeya.ml1Boot.caseTwoRawFine` at `ε' / 8` with the passes' `fibreFrostman`;
* the free-scale lower bound of item (iv) is `Kakeya.ml1Boot.repairLower` at `ε'`, read at the
  *unrefined* level-`b` node family, which is where the dichotomy asserts it;
* the two parent families and the two essential-distinctness clauses are the passes' own;
* the two `B₁` containments are hypotheses, being facts about the node tubes of the hierarchy
  and owed by whoever builds it.

Together with `Kakeya.ml1Boot.caseTwoData_of_isCaseTwoRepairData` this reduces the whole of
blueprint `lem:ml1bootCaseIIData` — the intended `Kakeya.ml1Boot.exists_caseTwoData` — to a
single missing producer, `Kakeya.ml1Boot.exists_repairThreePass`: the three passes, whose
middle move (R2) is **refuted** in the form the blueprint states it
(`Kakeya.ml1Boot.not_exists_repairUniform`), and which therefore needs a restatement before it
can be proved.  Note that the dichotomy the other bridge consumes is a *field* of this bundle,
`Kakeya.ml1Boot.IsRepairThreePass.dichotomy`, at the share `δ ^ (6 * (ε' / 8)) = δ ^ (3 ε' / 4)`,
so it too comes from the same missing producer and from nowhere else.

The node-body injectivity hypothesis at the fine index is the one blueprint
`note:ml1bootNodeBodyInjectivity` records; it is what turns the level-`b` nodes into a parent
family (`Kakeya.ml1Boot.isParentFamily_nodes_fine`) and hence what the fine fibre bound is read
against. -/
theorem caseTwoRepairData_of_isRepairThreePass [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {β γ₀ : ℝ} {p : Params} (hp : p.Spec β γ₀) {ε' : ℝ} (hε' : 0 < ε')
    (Cds Cunif : NNReal) (Kds cds : ℕ) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} [DecidableEq ι] {γ : ℝ} {s s' s₂ s₀ : Finset ι} (T : ι → ShadedTube δ E)
        (𝒰' : Tube.UniformTubeSet s' (fun i => (T i).toTube)
          (Tube.ssfGridLen δ) Cds)
        (a b m : ℕ) (pθ : ι → ι) {t'τ t'θ : Finset ι},
        IsCaseFamily p γ Cunif s T →
        IsCaseTwoInput p (ε' / 8) Cds Kds cds s T s' 𝒰' a b m →
        Set.InjOn (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) (𝒰'.cover.indexSet b) →
        (∀ k ∈ 𝒰'.cover.indexSet b, (𝒰'.cover.tube b k).carrier ⊆ Metric.closedBall 0 1) →
        (∀ l' ∈ 𝒰'.cover.indexSet a, (𝒰'.cover.tube a l').carrier ⊆ Metric.closedBall 0 1) →
        t'τ ⊆ 𝒰'.cover.indexSet b →
        t'θ ⊆ 𝒰'.cover.indexSet a →
        IsRepairThreePass (ε' / 8) T (𝒰'.cover.tube b) (𝒰'.cover.assign b)
          (𝒰'.cover.tube a) pθ (𝒰'.cover.indexSet b) (𝒰'.cover.indexSet a)
          s' s₂ s₀ t'τ t'θ →
        IsCaseTwoRepairData p ε' γ (m + 1) s T s₀ (𝒰'.cover.indexSet b)
          t'τ (𝒰'.cover.tube b) (𝒰'.cover.assign b) t'θ (𝒰'.cover.tube a) pθ := by
  filter_upwards [caseTwoRawFine (E := E) (p := p) (ε' := ε' / 8) (εin := ε' / 8)
      (by linarith) Cds Kds cds,
    repairLower (E := E) hdim hp (ε' := ε') (εin := ε' / 8) hε' Cds Kds cds,
    eventually_rpow_le_quarter (α := ε' / 4) (by linarith),
    self_mem_nhdsWithin] with δ hrawFine hlow hquarter hδ0
  obtain ⟨hδ1, hsmall⟩ := hquarter
  intro ι _i γ s s' s₂ s₀ T 𝒰' a b m pθ t'τ t'θ hfam hin hinjFine hballB hballA hsubF hsubC h3
  have hparFine : IsParentFamily s' (fun i => (T i).toTube) (𝒰'.cover.indexSet b)
      (𝒰'.cover.tube b) (𝒰'.cover.assign b) :=
    isParentFamily_nodes_fine 𝒰' hin.block.fine_le hinjFine
  obtain ⟨lam, hlam, hband⟩ := hin.band
  have hballCB : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ ConvexSpaceBody.closedUnitBall := by
    intro i hi x hx
    change x ∈ (ConvexSpaceBody.closedUnitBall (E := E)).carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier]
    exact hfam.ball i hi hx
  obtain ⟨_href34, _hfull34, _hcard, hfrost, href, hfull⟩ :=
    caseTwoRepairChains hδ0 hδ1 hε' hsmall T h3.nonemptyLast hballCB hfam.fullness hlam hband
      hin.card_le hin.refine_mass h3.refineMid h3.refineLast h3.card
  have hδne : (δ : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hδ0)
  refine
    { parentFine := h3.parentFine
      parentCoarse := h3.parentCoarse
      fineRetained := hsubF
      midBall := fun k hk => hballB k (hsubF hk)
      coarseBall := fun l' hl' => hballA l' (hsubC hl')
      midEssDistinct := h3.essDistinctFine
      coarseEssDistinct := h3.essDistinctCoarse
      refine_refinement := href
      refine_unif := h3.unif
      refine_frostman := ?_
      refine_fullness := hfull
      fine := ?_
      lower := ?_ }
  · calc
      frostmanConstIn s₀ (fun i => (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
          ≤ (δ : ENNReal) ^ (-ε')
            * frostmanConstIn s (fun i => (T i).toConvexSpaceBody)
                ConvexSpaceBody.closedUnitBall := hfrost
      _ ≤ (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ (-p.ηGamma γ) :=
          mul_le_mul_left' hfam.frostman _
      _ = (δ : ENNReal) ^ (-ε' - p.ηGamma γ) := by
          rw [← ENNReal.rpow_add _ _ hδne ENNReal.coe_ne_top]
          exact congrArg (fun x : ℝ => (δ : ENNReal) ^ x) (by ring)
  · have := caseTwoRepairFine (E := E) hδ0 hδ1 hε' (ηj := p.η m) T (𝒰'.cover.tube b)
      (𝒰'.cover.assign b) hsubF hparFine.le_parent
      (fun k hk => hrawFine T 𝒰' a b m hin k hk)
      (fun k hk K hK => h3.fibreFrostman k hk K hK)
    simpa using this
  · have := hlow T 𝒰' a b m hin
    simpa using this

/-- **Case (ii): the full data record from the repair's output and the fibrewise dichotomy**
(blueprint `lem:ml1bootCaseIIData`, its second half).

This is everything the intended `Kakeya.ml1Boot.exists_caseTwoData` has to do *after* the
repair.  It takes `Kakeya.ml1Boot.IsCaseTwoRepairData` — the record blueprint
`lem:ml1bootCaseIIDataRepair` is to produce, at the two node families of the hierarchy of
`Kakeya.ml1Boot.IsCaseTwoInput` — together with the fibrewise empty-or-share dichotomy
`Kakeya.ml1Boot.IsFibrewiseEmptyOrShare` at the share `δ ^ (3 ε' / 4)`, and returns the full
`Kakeya.ml1Boot.IsCaseTwoData`.  The one field the repair does not deliver, `mid`, is supplied
here by `Kakeya.ml1Boot.caseTwoMidRetained` fed with `Kakeya.ml1Boot.caseTwoRawMid` at the
accuracy `ε' / 8`, which is exactly the composition blueprint `lem:ml1bootMidRetained`
prescribes and which lands on the exponent `-ε'` with no slack
(`Kakeya.ml1Boot.mid_le_of_share_compose`).

So the residual obligation of `Kakeya.ml1Boot.exists_caseTwoData` is *precisely*
`Kakeya.ml1Boot.IsCaseTwoRepairData` plus the dichotomy: no other seam stands between the
Case (ii) input bundle and the Case (ii) data record.  Both remaining inputs are the repair's,
blueprint `lem:ml1bootCaseIIDataRepair`, whose intended producer
`Kakeya.ml1Boot.exists_caseTwoDataRepair` is not a declaration — see the module docstring, and
`Kakeya.ml1Boot.exists_trimmedPass` for the proved producer of the dichotomy that a repair is to
carry through.

## The two containments are hypotheses, not fields

`Kakeya.ml1Boot.IsCaseTwoRepairData.fineRetained` gives `tτ ⊆ tb`, and here `tb` is the
unrefined level-`b` index set, so that containment is the hypothesis `hsubFine` read at the
record's own `tb`; the coarse containment `tθ ⊆ 𝒰'_a` has no field of the record — the record's
only coarse clause is the parent-family one — and it is what lets the middle bound, which
`Kakeya.ml1Boot.caseTwoMidRetained` asserts at every coarse *node*, be read at every member of
`tθ`.  Both are properties of the node families a producer works with by construction.

The accuracy `εin` at which the input bundle is taken is a free binder: only the `block` field
is read, through `Kakeya.ml1Boot.caseTwoRawMid`, and never `card_le`. -/
theorem caseTwoData_of_isCaseTwoRepairData [Nontrivial E] {p : Params} {ε' εin : ℝ}
    (hε' : 0 < ε') (Cds : NNReal) (Kds cds : ℕ) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} [DecidableEq ι] {γ : ℝ} {s s' s₀ : Finset ι} (T : ι → ShadedTube δ E)
        (𝒰' : Tube.UniformTubeSet s' (fun i => (T i).toTube)
          (Tube.ssfGridLen δ) Cds)
        (a b m : ℕ) (pτ pθ : ι → ι) {tτ tθ : Finset ι},
        IsCaseTwoInput p εin Cds Kds cds s T s' 𝒰' a b m →
        IsCoarseNodeParents 𝒰' a b pθ →
        tτ ⊆ 𝒰'.cover.indexSet b →
        tθ ⊆ 𝒰'.cover.indexSet a →
        IsFibrewiseEmptyOrShare (𝒰'.cover.indexSet b) (𝒰'.cover.indexSet a) tτ pθ
          ((δ : ENNReal) ^ (3 * ε' / 4)) →
        IsCaseTwoRepairData p ε' γ (m + 1) s T s₀ (𝒰'.cover.indexSet b)
          tτ (𝒰'.cover.tube b) pτ tθ (𝒰'.cover.tube a) pθ →
        IsCaseTwoData p ε' γ (m + 1) s T s₀ (𝒰'.cover.indexSet b)
          tτ (𝒰'.cover.tube b) pτ tθ (𝒰'.cover.tube a) pθ := by
  filter_upwards [caseTwoRawMid (E := E) (p := p) (ε' := ε' / 8) (εin := εin)
      (by linarith) Cds Kds cds,
    caseTwoMidRetained (E := E) p hε' Cds] with δ hraw hret
  intro ι _i γ s s' s₀ T 𝒰' a b m pτ pθ tτ tθ hin hcnp hsubFine hsubCoarse hshare hrep
  refine hrep.isCaseTwoData ?_
  intro l' hl'
  exact hret a b m 𝒰' pθ hcnp (fun k hk => hraw T 𝒰' a b m hin k hk) hsubFine hshare l'
    (hsubCoarse hl')






end CaseTwo

end ml1Boot

end Kakeya

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The complete fine clause group, obtained directly from the proved Section 2 density-band
interface.  This is the unconditional one-sided replacement for the former auxiliary-interface
reduction. -/
theorem exists_fineUniformBand_direct (hdim : Module.finrank ℝ E = 3)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} {s : Finset ι} (V : ι → ShadedTube δ E),
        s.Nonempty →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        0 < ∑ i ∈ s, volume (V i).shade →
        ∃ s' ⊆ s, ∃ (Z' : ι → ShadedTube δ E) (lamσ : NNReal),
          0 < lamσ ∧ s'.Nonempty ∧
          (∀ i ∈ s', (Z' i).toTube = (V i).toTube ∧ (Z' i).shade ⊆ (V i).shade) ∧
          ShadedBody.IsCRefinement s' (fun i => (Z' i).toShadedBody) s
            (fun i => (V i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩ ∧
          Nonempty (IsOneSidedUniform s' Z' (Tube.ssfGridLen δ)
            (uniformize.C 3)) ∧
          (∀ i ∈ s', (lamσ : ENNReal) * volume (V i).carrier ≤ volume (Z' i).shade ∧
            volume (Z' i).shade ≤ 2 * (lamσ : ENNReal) * volume (V i).carrier) ∧
          (δ : ENNReal) ^ (2 * ε')
            * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lamσ : ENNReal) := by
  haveI : Nontrivial E := Module.finrank_pos_iff.mp (by rw [hdim]; norm_num)
  filter_upwards [
      exists_shadedUniformBand_of_card_le (E := E) hdim
        (α := ε' / 2) (α' := ε' / 2) (by positivity) (by positivity),
      eventually_card_le_rpow_neg_seven hdim,
      eventually_bandLoss_le_rpow_neg (η := ε' / 2) (by positivity),
      ENNReal.eventually_coe_rpow_le_of_pos (ρ := ε' / 2) (by positivity)
        (C := (1 / 2 : ENNReal)) (by simp),
      eventually_le_one_nhdsGT,
      self_mem_nhdsWithin] with
        δ hIFace hCard hBl hHalf hLe1 hMem
  have h0 : 0 < δ := hMem
  intro ι s V hne hball hED hmass
  obtain ⟨i₀, hi₀⟩ := hne
  have hvol : ∀ i, volume (V i).carrier = volume (V i₀).carrier := fun i =>
    _root_.Tube.volume_carrier_eq_volume_carrier (V i).toTube (V i₀).toTube
  obtain ⟨s₂, hs₂s, lam₀, hlam₀, hs₂ne, hwin₂, hmass₂, hfull₂⟩ :=
    exists_massBand h0 s V hmass
  have hc2 : (s₂.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) :=
    hCard δ le_rfl s₂ (fun i => (V i).toTube)
      (fun i hi => hball i (hs₂s hi)) (hED.mono (Finset.coe_subset.mpr hs₂s))
  obtain ⟨s', hss', Z', lam, hns', hlam', htube, hshade, hcardret, hlamret, hdens, huni⟩ :=
    hIFace s₂ V lam₀ hs₂ne hlam₀ (fun i hi => hball i (hs₂s hi)) hc2 hwin₂
  have hLb : bandLoss s.card ≤ (δ : ENNReal) ^ (-(ε' / 2)) :=
    hBl s.card (hCard δ le_rfl s (fun fas => (V fas).toTube) hball hED)
  have htwo : (2 : ENNReal) ≤ (δ : ENNReal) ^ (-(ε' / 2)) := by
    rw [ENNReal.rpow_neg]
    calc
      (2 : ENNReal) = (1 / 2 : ENNReal)⁻¹ := by norm_num
      _ ≤ ((δ : ENNReal) ^ (ε' / 2))⁻¹ := ENNReal.inv_le_inv.mpr hHalf
  have hcardE : (δ : ENNReal) ^ (ε' / 2) * (s₂.card : ENNReal) ≤ (s'.card : ENNReal) :=
    coe_rpow_mul_card_le_card h0 hcardret
  set cref : NNReal := ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩ with hcref_def
  have hcoef : (cref : ENNReal) = (δ : ENNReal) ^ (2 * ε') :=
    coe_nnreal_rpow_eq h0 (rfl : (cref : ℝ) = (δ : ℝ) ^ (2 * ε'))
  refine ⟨s', hss'.trans hs₂s, Z', lam, hlam', hns',
    fun i hi => ⟨htube i, hshade i⟩, ?_, ?_, hdens, ?_⟩
  · refine isCRefinement_of_tube_eq (hss'.trans hs₂s) (fun i _ => htube i)
      (fun i _ => hshade i) ?_
    rw [hcoef]
    exact fine_mass_retention h0 hvol (fun i hi => (hwin₂ i hi).2)
      (fun i hi => (hdens i hi).1) hmass₂ hLb htwo hcardE hlamret
  · exact ⟨huni.some.mono (ssfUniformConst_le_uniformize_C 3)⟩
  · exact fine_fullness_bound h0 hLe1 hε' hfull₂ hLb hlamret

end Kakeya.ml1Boot
