/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThickPlankAux
public import Kakeya.DimensionThree.MainLemma2.ThinConfig
public import Kakeya.DimensionThree.Plank.Factorization
public import Kakeya.DimensionThree.Plank.FrostmanPlankEstimate
public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.PartialEstimates

/-!
# The Section 6 plank interface owed to the thick case of Main Lemma 2

The thick case of Main Lemma 2 (blueprint `lem:ml2thickDensity`, Lean
`Kakeya.VeryNotSticky.exists_denseInBody`) rests on material that Section 6 owns and that is
not formalized: the Frostman estimate for planks (blueprint `plankF`) and the presentation of
a thick-case block as a family of planks in the unit ball (blueprint `lem:ml2thickBlockSelect`,
`lem:ml2thickPlank`, `lem:ml2thickThickenedVol`, `lem:ml2thickMbound`).

Three theorems:

* `Kakeya.VeryNotSticky.plankFrostmanVolume` — blueprint `plankF`, volume form
  `eq:plankF-volume`. It is stated so
  as to be a reduction to the Section 6 statement `Kakeya.FrostmanEstimate.plankEstimate`,
  which is GWZ Lemma 6.4 itself: the non-concentration hypothesis is now Section 6's
  `Plank.IsThickeningNonconcentrated` at an exported dilation `C_NC`, verbatim. An earlier
  version of this file stated it at the *aligned* count of blueprint
  `eq:plank-thickening-nonconcentration` and derived it from `plankEstimate`; that derivation
  was **not available**, because the aligned hypothesis does not imply the dilated one at any
  constant — see the counterexample in the module docstring of
  `Kakeya/DimensionThree/Plank/FrostmanPlankReduction.lean` and the second deviation bullet of
  `Kakeya.VeryNotSticky.PlankFrostmanVolumeAt`;
* `Kakeya.VeryNotSticky.exists_thickFullBlock` — blueprint `lem:ml2thickBlockSelect`. **Proved**, from the per-segment density hypothesis (C5)
  `Kakeya.VeryNotSticky.BallData.segs_density`, which descends to a block for free;
* `Kakeya.VeryNotSticky.denseInBodyRaw_of_thickPlankPresentation` — blueprint
  `lem:ml2thickPlankF`, the assembly. **Proved**, from the arithmetic of
  `Kakeya/DimensionThree/MainLemma2/ThickPlankAux.lean` together with the parameter budget
  `Kakeya.VeryNotSticky.PlankFrostmanUsable`, which it takes as a hypothesis and which
  reaches it from the field `Kakeya.VeryNotSticky.ThickDensityThresholds.plankF`.

What Section 6 still owes — blueprint `lem:ml2thickPlank` together with
`lem:ml2thickThickenedVol` and `lem:ml2thickMbound`, bundled as
`Kakeya.VeryNotSticky.ThickPlankPresentation` — is deliberately *not* a theorem of this file.
It is the predicate `Kakeya.VeryNotSticky.ThickPlankPresentable`, which the thick case carries
as a hypothesis at the *same* comparison constant as its parameter budget; the reason is the
quantifier order discussed below, and the hypothesis reaches its consumers from the field
`Kakeya.VeryNotSticky.ThickDensityThresholds.plankPres`.

`Kakeya.VeryNotSticky.exists_denseInBodyRaw` then combines them, and is proved; and
`Kakeya.VeryNotSticky.exists_denseInBody` in
`Kakeya/DimensionThree/MainLemma2/ThickCase.lean` is derived from it, together with the
already-proved thick-case counting material, by the exponent bookkeeping of blueprint
`def:ml2thickGain`. Nothing in this file strengthens or modifies any statement of Section 6:
`Kakeya.KatzTaoEstimate.plankEstimate` (the *multiplicity* form of GWZ Lemma 6.1) is left
untouched, and `Kakeya.VeryNotSticky.PlankFrostmanVolume` is a separate, usable rendering of
GWZ Lemma 6.4, now at Section 6's own non-concentration hypothesis.

## The two invariants the statements have to make visible

Both are quantifier-order properties, and both are stated rather than merely described,
because prose cannot be consumed by a proof.

**Uniformity.** One constant per exponent must serve every ball `B ∈ 𝔅`, every body
`W ∈ 𝕎_B`, every plank `P ∈ 𝒫` and every thickening parameter `θ ∈ [a/b, 1]`. A constant
depending on the ball centre, on the body or on `θ` would make the reduction of blueprint
`lem:ml2goalfromdens` circular, exactly as recorded for
`Kakeya.VeryNotSticky.exists_aScaleData`. This is why
`Kakeya.VeryNotSticky.ThickPlankPresentable` quantifies the ball and the body — and
`Kakeya.VeryNotSticky.ThickPlankPresentation.nonconcentration` the parameter `θ` — *under* one
fixed pair `(CP, Θ)`, instead of producing a pair for each of them.

**One triple `(CP, Θ, C_NC)`, quantified once and shared with the budget.** All three are
data, for the same reason. `CP` and `Θ` occur on the
*large* side of the presentation and on the *small* side of the parameter budget:
`Kakeya.VeryNotSticky.ThickPlankPresentable bd CP Θ` gets weaker as they grow, while
`Kakeya.VeryNotSticky.PlankFrostmanUsable bd τ CP` gets stronger, both of its thresholds
`CP δ/a ≤ b₀` and `(CP δ/b)^{η_{plankF}} ≤ c₁ δ^{2η}` failing once `CP` is large. So neither may
be quantified inside the other, and neither may be pinned to a value:

* a *universally* quantified budget, `∀ CP ≥ 1, PlankFrostmanUsable bd τ CP`, is refutable at
  any fixed configuration, by taking `CP` large;
* an *existentially* quantified presentation, `∃ CP Θ ≥ 1, ThickPlankPresentable bd CP Θ`, is
  useless, because its witness is then not available to the budget;
* a pair *named by definition* is worse than either. An earlier version of this file supplied
  one, as two `opaque` constants sealed at `1` about which nothing beyond `1 ≤ ·` was
  derivable. The presentation at such a value is neither provable nor refutable: at
  `CP = Θ = 1` the comparability fields `short_lower`–`long_upper` collapse to the exact
  equalities `a' = δ/b`, `b' = δ/a`, `fullness_ge` and `sel_card` to exact identities and
  `frostman` to the bare `C_bias`, none of which the enclosing planks satisfy, while no proof
  may appeal to
  `1 < CP` either. An *independent* statement is strictly worse than an open one.

The dilation `C_NC` of the non-concentration hypothesis is in exactly the same position, and
this is why it is exported rather than bound inside either side.
`Kakeya.VeryNotSticky.ThickPlankPresentation.nonconcentration` gets *stronger* as `C_NC` grows,
`Plank.IsThickeningNonconcentrated` being a demand about a larger container, while
`Kakeya.VeryNotSticky.PlankFrostmanUsable` gets *weaker*, that same predicate being its
hypothesis. So a value quantified inside either one is unusable to the other, and it must be
data too.

The arrangement that works, and the one recorded here, is that `CP`, `Θ` and `C_NC` are
**data**, quantified once and ahead of everything they constrain, and that the *same* triple
carries both the presentation and the budget: the fields
`Kakeya.VeryNotSticky.CaseSideData.CP`, `Kakeya.VeryNotSticky.CaseSideData.Θ` and
`Kakeya.VeryNotSticky.CaseSideData.C_NC`, with
`Kakeya.VeryNotSticky.ThickDensityThresholds.plankPres` and
`Kakeya.VeryNotSticky.ThickDensityThresholds.plankF` asserted at that one triple. It is
satisfiable — take them to be the geometric constants `C_{lem:ml2thickPlank}(C₀)` and
`C_{lem:ml2thickMbound}(C₀)` of blueprint `def:ml2thickPlankConstant` and
`def:ml2thickMboundConstant`, functions of the thickness comparison constant of (C3)–(C4) and
of the ambient dimension alone, for which the two budget thresholds hold once `δ` is small —
and, unlike a sealed constant, it commits to no particular value.

**What is *not* claimed: that a fixed value is `δ`-free.** An earlier version of this file
asserted `δ`-independence structurally, by writing the two constants as functions of `bd.C₀`
alone. That claim is true of the *function* `C₀ ↦ C_{lem:ml2thickPlank}(C₀)` and false of the
*value* it takes here. `Kakeya.VeryNotSticky.BallData.C₀` carries only `1 ≤ C₀`, and `bd` —
hence `bd.C₀`, hence any function of it — is produced *inside* the `∀ᶠ δ` of
`Kakeya.VeryNotSticky.exists_setup_caseSideData`, so no Lean statement here forbids it from
varying with `δ`. What the arrangement above guarantees is the property the budget actually
needs, and that property mentions no `δ`-freeness: for each `δ` the pair `(CP, Θ)` is chosen
*once*, before the ball, the body and `θ`, and is shared. That the smallness threshold on `δ`
which results is uniform in the parameters — which is what makes
`exists_setup_caseSideData` non-vacuous — is a property of the construction of `bd`, recorded
in the note at the end of blueprint subsection `thickCaseSection`; it is an obligation of that
construction and is asserted by no declaration in this file.

**The bias constant is not `δ`-free, and is therefore explicit in both fields that carry it.**
Blueprint `def:factmaxbiasConstant` and the field docstring of
`Kakeya.VeryNotSticky.BallData.Cbias` both record that `C_{lemmafactmaxbias}` depends on
`cfg.δ` and on the cardinality of the family; GWZ p. 39 derives the value of `M` through `⪅`,
which by the convention of GWZ p. 3 hides a factor `C_ε δ^{-ε}`; and blueprint
`def:ml2thickMboundConstant` says in as many words that
`C_{lem:ml2thickMbound} = C_{lem:ml2thickCard}(C₀)² C_{lemmafactmaxbias}
(2³ C_{lem:ml2thickPlank}(C₀)⁴/|B₁|)²` depends on `δ` through `C_{lemmafactmaxbias}`, and that
it is the constant blueprint `lem:ml2thickPlankF` consumes as its parameter `Θ`. In this
development the `δ`-dependent factor is exactly the field `bd.Cbias`, and it enters only
through `Kakeya.VeryNotSticky.BallData.biasedDensity` of (C4), which is the sole source of the
gain `(|K_θ|/|W|)^ϱ`. So `bd.Cbias` appears as an *explicit factor* in both constant-carrying
fields of `Kakeya.VeryNotSticky.ThickPlankPresentation`: in `frostman`, where it always did,
and in `nonconcentration`, where an earlier version of this file omitted it and claimed a
`δ`-free `Θ`. That claim was wrong, and it made the field underivable from (C4). With the
factor explicit, `Θ` is the remaining quantity that blueprint `def:ml2thickMboundConstant`
names, and the field is derivable in principle.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric ShadedBody

universe u

open scoped Classical in
/-- **The Frostman estimate for planks, volume form, at prescribed parameters** (blueprint
`plankF`, display `eq:plankF-volume`; GWZ Lemma 6.4).

Every finite family `𝒫 = (P_i)_{i ∈ s}` of `a × b × 1` planks in `B_1` with shading `Y`, with
`0 < a ≤ b ≤ b₀`, pairwise essentially distinct, of fullness `λ(𝒫, Y) ≥ a^η`, of Frostman
constant `C_F(𝒫) ≤ C_F` *in the unit ball*, and satisfying the non-concentration bound
`|{j ∈ s : P_j ⊆ C_NC · (P_i)_θ}| ≤ M θ` for every `i ∈ s` and every `a/b ≤ θ ≤ 1` at some
`M ≥ 1`, obeys

`a^ε C_F^{β/2-1} b^{2β} (M^{-1} b² |s|)^{β/2} ≤ 64 |U(𝒫, Y)|`.

The parameters `η`, `b₀` and the non-concentration dilation `C_NC` are explicit here, rather
than existentially bound as in `Kakeya.VeryNotSticky.PlankFrostmanVolume`, because
`Kakeya.VeryNotSticky.denseInBodyRaw_of_thickPlankPresentation` has to compare them with the
scales of the configuration: its two threshold hypotheses are inequalities between `b₀`, `η`
and `cfg.δ`, `cfg.a`, `cfg.b`, `cfg.η`, and an existentially bound witness cannot appear in a
hypothesis.

Three deliberate deviations from the blueprint display, each a weakening:

* the Frostman constant is an upper bound `C_F` supplied by the caller rather than the
  extremal `Kakeya.frostmanConstant` of the family. Since `β/2 - 1 < 0` and `C_F ≥ 1`, the
  displayed factor is *decreasing* in the constant, so the version with an upper bound is
  implied by the version with the extremal one; and it is the version the thick case can use,
  because blueprint `lem:ml2thickPlank`(iii) supplies only an upper bound;
* the non-concentration hypothesis is the **dilated** one,
  `Plank.IsThickeningNonconcentrated s 𝒫 C_NC M`, i.e. the count is taken over the planks
  contained in the `C_NC`-dilation `(P_i)_θ.dilation C_NC` of the standard `θ`-thickening, and
  *not* over those contained in `(P_i)_θ` itself. This is a **strengthening of the hypothesis**,
  hence a weakening of the estimate, and it is a genuine departure from blueprint `plankF`,
  whose display `eq:plank-thickening-nonconcentration` is the aligned count
  `|{j : P_j ⊆ (P_i)_θ}| ≤ M θ`. The departure is forced, and it is Section 6's, not this
  file's: `Kakeya.FrostmanEstimate.plankEstimate` — the Section 6 rendering of GWZ Lemma 6.4,
  and the only source from which a volume lower bound is available here — takes exactly
  `Plank.IsThickeningNonconcentrated s (fun i => (V i).toPrism3D) C_NC M`, because its proof
  routes through the representative-fibre bound
  `Plank.ThickenedRepr.card_fibre_le_of_nonconcentration`, whose geometry sees a fibre only
  from inside a fixed dilation of one of its members
  (`Plank.ThickenedRepr.fibre_subset_dilated_thickening`, at
  `C_NC = Plank.ThickenedRepr.fibreDilation cThk = (1 + 2 cThk) cThk ≥ 3`).

  The aligned form does **not** imply the dilated one, and this is not a gap in the search for
  a proof: the module docstring of `Kakeya/DimensionThree/Plank/FrostmanPlankReduction.lean`
  exhibits a family of `a × b × 1` planks that is pairwise essentially distinct, lies in the
  working window, satisfies the aligned count at *every* `θ ∈ [a/b, 1]` with the least
  admissible `M = b/a`, and whose dilated count at `C = 3` is `(θ b / 2a)²`, a ratio
  `θ b / 4a` above `M θ` that is unbounded. The structural reason is that the aligned
  thickening `(P_i)_θ` widens only the *thin* axis, while `PrismNDim.dilation C` widens all
  three — in particular the *unit-length* long axis, along which `Plank.thickenedNbhd P θ`
  reaches only `1 + θ b`. So no restatement of this predicate at the aligned hypothesis is
  derivable from Section 6, at any constant; only the dilated one is. The dilation factor is
  therefore exported as a parameter, and every producer of the hypothesis — here
  `Kakeya.VeryNotSticky.ThickPlankPresentation.nonconcentration` — has to supply it at that
  same `C_NC`. Blueprint `plankF` and its display `eq:plank-thickening-nonconcentration`
  should be corrected to match; that is an edit to `section6_estimates.tex`, not to this file.

  Note also that this is a different hypothesis from the slab-family bound
  `Plank.inSlabFamily` of the multiplicity form `Kakeya.KatzTaoEstimate.plankEstimate`
  (GWZ Lemma 6.1), which is not usable here for the reason given on
  `Kakeya.VeryNotSticky.plankFrostmanVolume`;
* the harmless factor `64` on the volume side, retained from an earlier version of this
  predicate so that the arithmetic of
  `Kakeya/DimensionThree/MainLemma2/ThickPlankAux.lean` need not be restated. It is a fixed
  numeral, independent of every parameter, and
  `Kakeya.VeryNotSticky.exists_denseInBodyRaw` absorbs it into the constant it produces.

**Localization and the Frostman window are both taken at radius `Plank.windowRadius = 4`, not
at the unit ball.** Blueprint `plankF` states the estimate for planks in `B₁`, and an earlier
version of this predicate copied that literally; but the planks the thick case can actually
produce are *enclosing* planks of the images `L(T_p)`, and an enclosing plank of a body in
`B̄(0,1)` is only known to lie in `B̄(0, 4)` — that is exactly what
`Kakeya.VeryNotSticky.plankWindowEnclosure` delivers, and why
`Kakeya.VeryNotSticky.plankBallRadius` is defined from `Plank.windowRadius`. So the
localization hypothesis is `Plank.IsWindowedFamily`, which is the hypothesis of
`Kakeya.FrostmanEstimate.plankEstimate` itself, and the Frostman hypothesis is taken in
`Kakeya.plankWindow` for the same reason: with the planks outside `B₁` there is no longer a
`Kakeya.ConvexSpaceBody.IsFrostmanIn.change_ambient` step available to convert a unit-ball
Frostman bound into a plank-window one, since that conversion needs the bodies to lie in the
unit ball. Both changes make this predicate *weaker*, and both are what
`Kakeya.VeryNotSticky.ThickPlankPresentation` can honestly supply.

Note that the middle plank scale of the thick case is `b = δ/a` up to the comparison constant
`CP`, so the container `((P)_θ).dilation C_NC` — whose half-widths are `C_NC` times those of
the `θ`-thickening, i.e. `(C_NC a, C_NC θ b, C_NC)` at the plank's *own* half-widths — is
comparable to the `N_{θ δ/a}(P)` of blueprint `lem:ml2thickThickenedVol` up to `C_NC` and that
same constant; see `Kakeya.VeryNotSticky.ThickPlankPresentation.nonconcentration` for the
reconciliation and for the extra powers of `C_NC` that `Θ` has to absorb. The name `b` of this
predicate and the working scale `cfg.b` of the thick case are unrelated. -/
def PlankFrostmanVolumeAt (β ε η : ℝ) (b₀ C_NC : NNReal) : Prop :=
  ∀ {ι : Type u} (s : Finset ι) {a b : NNReal} (hab : a ≤ b) (hb1 : b ≤ 1)
    (V : ι → ShadedPlank a b hab hb1),
    0 < a → b ≤ b₀ →
    Plank.IsWindowedFamily s (fun i => (V i).toPrism3D) →
    (s : Set ι).Pairwise
      (fun i j => _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier) →
    a ^ η ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) →
    ∀ CF : NNReal, 1 ≤ CF →
      ConvexSpaceBody.IsFrostmanIn s (fun i => (V i).toConvexSpaceBody)
        Kakeya.plankWindow (CF : ENNReal) →
      ∀ Mn : NNReal, 1 ≤ Mn →
        Plank.IsThickeningNonconcentrated s (fun i => (V i).toPrism3D) C_NC Mn →
        (a : ENNReal) ^ ε * (CF : ENNReal) ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β) *
            ((Mn : ENNReal)⁻¹ * (b : ENNReal) ^ (2 : ℝ) * (s.card : ENNReal)) ^ (β / 2) ≤
          64 * volume (iUnionShade s (fun i => (V i).toShadedBody))

/-- **The Frostman estimate for planks, volume form** (blueprint `plankF`, display
`eq:plankF-volume`; GWZ Lemma 6.4): for some non-concentration dilation `C_NC ≥ 1` and suitable
`η > 0` and `b₀ > 0`, the estimate `Kakeya.VeryNotSticky.PlankFrostmanVolumeAt` holds.

This is a *predicate*, so that the whole statement — including its `∃ C_NC`, `∃ η`, `∃ b₀` —
can be handed around as a hypothesis; see `Kakeya.VeryNotSticky.PlankFrostmanVolumeAt` for the
content and for the four deviations from the blueprint display.

**The binder order mirrors `Kakeya.FrostmanEstimate.plankEstimate`**, whose statement is
`∃ C_NC, 1 ≤ C_NC ∧ ∀ ε > 0, ∃ η > 0, ∃ b₀ > 0, …`: the dilation is quantified *outermost*,
ahead of `ε`, because Section 6 produces it once, from the representative geometry of blueprint
`lemmaredplanktube`, before any exponent is chosen. Here `ε` is a parameter rather than a
binder, so `C_NC` simply comes first. Keeping the order is what lets
`Kakeya.VeryNotSticky.plankFrostmanVolume` be a reduction to that statement rather than a
re-derivation of it. -/
def PlankFrostmanVolume (β ε : ℝ) : Prop :=
  ∃ C_NC : NNReal, 1 ≤ C_NC ∧
    ∃ η > (0 : ℝ), ∃ b₀ > (0 : NNReal), PlankFrostmanVolumeAt.{u} β ε η b₀ C_NC

/-- **The Frostman estimate for planks** (blueprint `plankF`, GWZ Lemma 6.4), in the volume
form `Kakeya.VeryNotSticky.PlankFrostmanVolume`.

This is intended to be *derived*, and not assumed, from the Section 6 statement
`Kakeya.FrostmanEstimate.plankEstimate` of
`Kakeya/DimensionThree/Plank/FrostmanPlankEstimate.lean`, which is GWZ Lemma 6.4 itself and
whose first conjunct is exactly the volume lower bound.

With `Kakeya.VeryNotSticky.PlankFrostmanVolumeAt` now carrying the *dilated* non-concentration
hypothesis at an exported `C_NC`, the bookkeeping between the two is purely a matter of types,
and costs nothing:

* the dilation `C_NC` and its bound `1 ≤ C_NC` are the outermost existential on both sides, in
  the same order; the hypothesis `Plank.IsThickeningNonconcentrated s (fun i => (V i).toPrism3D)
  C_NC Mn` is the Section 6 one verbatim, with the same argument order and the same `ℝ≥0`-valued
  count and parameter, so no conversion is needed at all. This is the whole point of the
  restatement: an earlier version of this predicate stated the *aligned* count
  `|{j ∈ s : P_j ⊆ Plank.thickenedNbhd (P_i) θ}| ≤ M θ` of blueprint
  `eq:plank-thickening-nonconcentration`, and the bridge from Section 6 to it is not merely
  unproved but **false** — see the second deviation bullet of
  `Kakeya.VeryNotSticky.PlankFrostmanVolumeAt`, and the counterexample in the module docstring
  of `Kakeya/DimensionThree/Plank/FrostmanPlankReduction.lean`;
* windowing and the Frostman window are the Section 6 ones on the nose — `Plank.IsWindowedFamily`
  and `Kakeya.plankWindow` — since `Kakeya.VeryNotSticky.PlankFrostmanVolumeAt` was restated at
  radius `Plank.windowRadius = 4`, which is `Kakeya.plankWindowRadius` by `rfl`; see its
  docstring for why the unit-ball form is not what the thick case can supply;
* the Frostman constant is an `NNReal` here and an `ENNReal` with `CF ≠ ⊤` there;
* the middle scale appears as `b ^ (2 : ℝ)` here and as `b ^ 2` there, bridged by
  `ENNReal.rpow_two`;
* the factor `64` on the volume side of `PlankFrostmanVolumeAt` is now pure slack: it used to
  pay for `Kakeya.ConvexSpaceBody.IsFrostmanIn.change_ambient`, which is no longer needed, and
  is retained only so that the downstream arithmetic of
  `Kakeya/DimensionThree/MainLemma2/ThickPlankAux.lean` is unchanged.

Not usable here, by contrast, is the multiplicity form `Kakeya.KatzTaoEstimate.plankEstimate`
of GWZ Lemma 6.1: its conclusion bounds `μ(𝒫, Y)` from above rather than `|U(𝒫, Y)|` from
below, and its non-concentration hypothesis is the slab-family bound of blueprint
`eq:plank-slab-nonconcentration` rather than a thickened-plank containment at all.

The hypothesis `hKF` is the Frostman estimate `K_F(β)` of blueprint `def:KF`; in the thick
case it is supplied by the field `Kakeya.VeryNotSticky.fEstimate` of the configuration. -/
theorem plankFrostmanVolume {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) {ε : ℝ} (hε : 0 < ε) :
    PlankFrostmanVolume.{u} β ε := by
  classical
  obtain ⟨C_NC, hC_NC, H⟩ := FrostmanEstimate.plankEstimate.{u} hβpos hβle hKF
  obtain ⟨η, hη, b₀, hb₀, H'⟩ := H ε hε
  refine ⟨C_NC, hC_NC, η, hη, b₀, hb₀, ?_⟩
  intro ι s a b hab hb1 V ha hb0 hwin hED hfull CF hCF hFr Mn hMn1 hnc
  have hwin' : ∀ i ∈ s, (V i).carrier ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (plankWindowRadius : ℝ) := by
    intro i hi
    have := hwin i hi
    simpa [Kakeya.plankWindowRadius, Plank.windowRadius] using this
  have hCFtop : (CF : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCF' : (1 : ENNReal) ≤ (CF : ENNReal) := by exact_mod_cast hCF
  have hmain := (H' s hab hb1 V ha hb0 hwin' hED hfull Mn hMn1 hnc (CF : ENNReal)
    hCF' hCFtop hFr).1
  rw [← ENNReal.rpow_two] at hmain
  have hvol : volume (iUnionShade s (fun i => (V i).toShadedBody)) =
      volume (⋃ i ∈ s, (V i).shade) := by
    simp [ShadedBody.iUnionShade]
  calc
    (a : ENNReal) ^ ε * (CF : ENNReal) ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β) *
        ((Mn : ENNReal)⁻¹ * (b : ENNReal) ^ (2 : ℝ) * (s.card : ENNReal)) ^ (β / 2)
        ≤ volume (⋃ i ∈ s, (V i).shade) := hmain
    _ ≤ 64 * volume (⋃ i ∈ s, (V i).shade) :=
        le_mul_of_one_le_left zero_le (by norm_num : (1 : ENNReal) ≤ (64 : ENNReal))
    _ = 64 * volume (iUnionShade s (fun i => (V i).toShadedBody)) := by rw [hvol]

open scoped Classical in
/-- **A plank-Frostman exponent at which the estimate is available** (blueprint `plankF`).

`Kakeya.VeryNotSticky.PlankFrostmanVolume` supplies its exponent existentially, but the thick
case has to *name* it: the exponent must be fixed before `cfg.η` is, since the parameter budget
`Kakeya.VeryNotSticky.ThickDensityThresholds.budget` — `2η < τ η_{plankF}` — compares the two,
and `η` is the quantity the parameter lemma `Kakeya.VeryNotSticky.exists_caseParams` chooses
last. This is that name: the exponent the estimate itself provides, defaulting to `1` when the
estimate is unavailable, so that it is positive *unconditionally* and hence usable in
`exists_caseParams`, which does not see `K_F(β)`.

**Why a canonical exponent and not a free parameter.**
`Kakeya.VeryNotSticky.PlankFrostmanVolumeAt` gets *stronger* as the exponent grows: its
fullness hypothesis `a^{η_{plankF}} ≤ λ(𝒫, Y)` weakens, `a` being at most `1`. So the estimate
holds only up to some maximal exponent and is false above it, while the second threshold of
`Kakeya.VeryNotSticky.PlankFrostmanUsable` asks for the exponent to be *large*. A budget stated
against a free exponent parameter would therefore be no budget at all: it would be met by
taking that parameter huge, and at such a value the estimate — hence the field
`Kakeya.VeryNotSticky.ThickDensityThresholds.plankF` — is false. Comparing `η` against an
exponent at which the estimate is *known* to hold is what makes that field satisfiable.

It is `@[irreducible]`: the body is a `dite` on `Kakeya.VeryNotSticky.PlankFrostmanVolume`, a
large universally quantified proposition carrying a `Classical.propDecidable` instance, and
nothing outside the two lemmas below has any use for the body. Without the attribute every
`whnf` reaching this term — for instance inside the `min` that
`Kakeya.VeryNotSticky.exists_caseParams` builds `η` from — tries to reduce that `dite` and
exhausts the heartbeat budget. The two lemmas below still see the body, through the equation
lemmas. -/
@[irreducible] noncomputable def plankFrostmanExponent (β ε : ℝ) : ℝ :=
  if h : PlankFrostmanVolume.{u} β ε then h.choose_spec.2.choose else 1

/-- `Kakeya.VeryNotSticky.plankFrostmanExponent` is positive whether or not the estimate is
available; this is what lets the budget `2η < τ η_{plankF}` be arranged by
`Kakeya.VeryNotSticky.exists_caseParams`, which is stated before `K_F(β)` is assumed. -/
theorem plankFrostmanExponent_pos (β ε : ℝ) : 0 < plankFrostmanExponent.{u} β ε := by
  unfold plankFrostmanExponent
  split_ifs with h
  · exact h.choose_spec.2.choose_spec.1
  · norm_num

/-- When blueprint `plankF` is available at `(β, ε)`, it is available *at the named exponent*
`Kakeya.VeryNotSticky.plankFrostmanExponent β ε`, for some non-concentration dilation
`C_NC ≥ 1` and some positive `b₀`. This is what
`Kakeya.VeryNotSticky.exists_setup_caseSideData` uses to realize the field
`Kakeya.VeryNotSticky.ThickDensityThresholds.plankF` at the exponent its binder `hplankF`
budgets for, and to realize the field `Kakeya.VeryNotSticky.CaseSideData.C_NC` at which the
plank presentation `Kakeya.VeryNotSticky.ThickPlankPresentable` must then be supplied.

`C_NC` is *produced* here and not named canonically, unlike the exponent: nothing outside the
presentation ever compares it with another quantity, so it may travel as data of the bundle
rather than as a `dite` on the estimate. The exponent cannot, because
`Kakeya.VeryNotSticky.ThickDensityThresholds.budget` compares it with `cfg.η`; see
`Kakeya.VeryNotSticky.plankFrostmanExponent`. -/
theorem plankFrostmanVolumeAt_plankFrostmanExponent {β ε : ℝ}
    (h : PlankFrostmanVolume.{u} β ε) :
    ∃ C_NC : NNReal, 1 ≤ C_NC ∧ ∃ b₀ : NNReal, 0 < b₀ ∧
      PlankFrostmanVolumeAt.{u} β ε (plankFrostmanExponent.{u} β ε) b₀ C_NC := by
  classical
  refine ⟨h.choose, h.choose_spec.1, ?_⟩
  obtain ⟨_, b₀, hb₀, H⟩ := h.choose_spec.2.choose_spec
  refine ⟨b₀, hb₀, ?_⟩
  rw [plankFrostmanExponent, dif_pos h]
  exact H

/-- **Section 6 interface stub: choosing a full block of the factoring** (blueprint
`lem:ml2thickBlockSelect`).

There are a ball `B ∈ 𝔅` and a segment `T_B ∈ 𝕋_B` whose block `𝕋_{B,W}`, `W = W(T_B)`,
inherits the fullness of `𝕋_B`, hence the fullness `λ(𝕋_B, Y_B) ≥ c₁ δ^{2η}` of (C5):

`c₁ δ^{2η} ≤ λ(𝕋_{B,W}, Y_B)`.

The body is presented through a segment `T_B` of its own block rather than as a body
`W ∈ 𝕎_B` on the nose. That is not a convenience: a body of `𝕎_B` may have an *empty* block,
and every quantitative statement about the block below — the fullness here, the cardinality
bound `Kakeya.VeryNotSticky.thickPcard_ge`, the plank presentation — is false for it. Choosing
the block through one of its members rules that out once and for all, and the body is then
`bd.blk p₀`, which lies in `bd.bodies B` by `Kakeya.VeryNotSticky.BallData.blk_mem`.

**The proof does not need the mass regrouping of blueprint `lem:ml2thickMassRegroup`.** That
regrouping — `λ(𝕋_B, Y_B) ∑_{T_B ∈ 𝕋_B}|T_B| = ∑_{W' ∈ 𝕎_B} λ(𝕋_{B,W'}, Y_B) ∑_{T_B ∈
𝕋_{B,W'}}|T_B|`, followed by a pigeonhole over `𝕎_B` — is how the blueprint argues, and every
ingredient of it is in fact available: blueprint `lem:ml2multFullness` is
`Kakeya.ShadedBody.sum_volumeReal_shade_eq_fullness_mul`, proved and already cleared of
division, and `Kakeya.exists_sum_div_sum_le` is the mediant pigeonhole. But the development
states (C5) *per segment* rather than in the aggregate — the field
`Kakeya.VeryNotSticky.BallData.segs_density` is `c₁ δ^{2η} |T_B| ≤ |Y_B(T_B)|` for each
`T_B ∈ 𝕋_B` — and a per-segment bound descends to an arbitrary subfamily for free. Summing it
over the block and dividing by the total carrier volume gives the fullness bound directly, so
*every* non-empty block of *every* ball already has fullness `≥ c₁ δ^{2η}`; the ball and the
segment are then chosen arbitrarily, by `Kakeya.VeryNotSticky.BallData.bs_nonempty` and
`Kakeya.VeryNotSticky.BallData.segs_nonempty`.

The two side conditions of the division are the ones the `[0, ∞]`-valued
`ShadedBody.fullness` always needs: the total carrier volume of the block is finite, by
compactness of the carriers, and non-zero, because the block contains `T_B`, whose carrier has
positive volume: the thickness data (C3) of `Kakeya.VeryNotSticky.BallData.segs_thickness`
bounds each of the three affine thicknesses of `T_B` below by `C₀⁻¹ δ > 0`, and
`Convex.volume_pos_of_ethickness_ne_zero` turns that into `0 < |T_B|`. (The packaged form
`Kakeya.VeryNotSticky.thickSegVolRatio` says the same thing, but lives downstream of this
file.)

The constant `c₁` is the per-segment density constant of (C5) — the field
`Kakeya.VeryNotSticky.BallData.c₁`, positive by
`Kakeya.VeryNotSticky.BallData.hc₁` — so no new constant is introduced and uniformity in `B`
and in `W` is automatic: `c₁` is one field of `bd`, not a function of the ball. -/
theorem exists_thickFullBlock {cfg : VeryNotSticky.{u}} (bd : BallData cfg) :
    ∃ B ∈ bd.bs, ∃ p₀ ∈ bd.segs B,
      bd.c₁ * cfg.δ ^ (2 * cfg.η) ≤
        ShadedBody.fullness ((bd.segs B).filter fun p => bd.blk p = bd.blk p₀)
          bd.Y := by
  obtain ⟨B, hB⟩ := bd.bs_nonempty
  obtain ⟨p₀, hp₀⟩ := bd.segs_nonempty B hB
  refine ⟨B, hB, p₀, hp₀, ?_⟩
  set s := (bd.segs B).filter fun p => bd.blk p = bd.blk p₀ with hdefs
  have hp₀s : p₀ ∈ s := by
    rw [hdefs]
    exact Finset.mem_filter.mpr ⟨hp₀, rfl⟩
  have hsub : s ⊆ bd.segs B := by
    rw [hdefs]
    exact Finset.filter_subset _ _
  have hcarPos : 0 < ∑ p ∈ s, volume (bd.Y p).carrier := by
    exact lt_of_lt_of_le (volume_segs_carrier_pos bd hB (hsub hp₀s))
      (Finset.single_le_sum (f := fun p => volume (bd.Y p).carrier)
        (by intro p _; exact zero_le) hp₀s)
  have hcarTop : (∑ p ∈ s, volume (bd.Y p).carrier) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.2 (fun p _ => (bd.Y p).isCompact'.measure_ne_top)
  have hdens_sum : (bd.c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) *
      (∑ p ∈ s, volume (bd.Y p).carrier) ≤ ∑ p ∈ s, volume (bd.Y p).shade := by
    calc
      (bd.c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * (∑ p ∈ s, volume (bd.Y p).carrier)
          = ∑ p ∈ s, (bd.c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) *
              volume (bd.Y p).carrier := by
            rw [Finset.mul_sum]
      _ ≤ ∑ p ∈ s, volume (bd.Y p).shade := by
        exact Finset.sum_le_sum (fun p hp => bd.segs_density B hB p (hsub hp))
  rw [← ENNReal.coe_le_coe, ShadedBody.fullness_def]
  rw [ENNReal.coe_mul]
  rw [ENNReal.coe_rpow_of_ne_zero (ne_of_gt cfg.hδ) (2 * cfg.η)]
  apply (ENNReal.le_div_iff_mul_le (Or.inl hcarPos.ne') (Or.inl hcarTop)).mpr
  exact hdens_sum

/-! ### The two constants of the thick-case plank presentation

Blueprint `def:ml2thickPlankConstant` and `def:ml2thickMboundConstant` introduce
`C_{lem:ml2thickPlank}(C₀)` and `C_{lem:ml2thickMbound}(C₀)` by the properties they must have,
not by values: of the ingredients of the first only the volume one is explicit (`24√3 π`, from
`|B₁|/|L(W)| ≤ 2³|B₁|/(c|Q|)`), the other being the unproved alignment estimate behind
`lem:ml2thickPlank`(i), and two of the three factors of the second are likewise introduced by
their defining property.

They are therefore **not** rendered as Lean definitions. Neither a formula nor a sealed
`opaque` value would be honest: a formula would make the presentation at that value a *false*
statement, and a sealed value about which only `1 ≤ ·` is derivable would make it an
*independent* one, which is worse. They are instead carried as the quantified data `CP`, `Θ`
of `Kakeya.VeryNotSticky.ThickPlankPresentation`,
`Kakeya.VeryNotSticky.ThickPlankPresentable` and
`Kakeya.VeryNotSticky.PlankFrostmanUsable`, fixed once by the fields
`Kakeya.VeryNotSticky.CaseSideData.CP` and `Kakeya.VeryNotSticky.CaseSideData.Θ` and shared by
the presentation and the parameter budget. See the module docstring for why nothing weaker
works, and `Kakeya.VeryNotSticky.ThickPlankPresentable` for the shape of the hypothesis.
-/

open scoped Classical in
/-- **The plank presentation of a thick-case block** (blueprint `lem:ml2thickPlank`, together
with `lem:ml2thickThickenedVol` and `lem:ml2thickMbound`).

The data of the change of variables `L` carrying the outer prism of the body `W = W_j` onto a
cube, applied to the block `𝕋_{B,W}` and its shading: a family `𝒫` of genuine `a' × b' × 1`
planks *enclosing* the images `L(T_p)`, with dimensions comparable to `(δ/b, δ/a)` within the
constant `CP`, localized in the Section 6 window `B̄(0, 4)`, together with a *selected
subfamily* `𝒫_sel` on which the planks are pairwise essentially distinct, retain the block
cardinality up to `CP`, retain the fullness of the block up to `CP`, are `CP C_bias`-Frostman
in the plank window, have shaded union comparing with that of the block, and are
non-concentrated at `M = Θ C_bias (δ/a)^{2+ϱ}|𝕋_{B,W}|` uniformly in the thickening parameter
`θ ∈ [a'/b', 1]` and in the plank.

**Why an enclosing family and a selected subfamily, and not the images themselves.** Both are
forced, and both were wrong in an earlier version of this structure.

* `L(T_p)` is a convex body, not a `Plank`. The only construction of a genuine `Plank` from it
  is `Kakeya.VeryNotSticky.plankWindowEnclosure`, which returns a plank *containing* it. Since
  `ShadedPlank extends Plank, ShadedBody`, the plank's carrier *is* the shaded body's carrier,
  so enclosing enlarges the denominator of `ShadedBody.fullness` and leaves the numerator
  alone: plank fullness is strictly *smaller* than block fullness, and the exact equality
  `λ(𝒫, Y_𝒫) = λ(𝕋_{B,W}, Y_B)` of blueprint `lem:ml2thickPlank`(iv) — which is a statement
  about the *images* — is false for the planks in the direction this development needs, namely
  a lower bound on plank fullness. The field `fullness_ge` is therefore the enclosure-weakened
  one-sided form, at the constant `CP`; that is what
  `Kakeya.VeryNotSticky.plankEnclosureVolume` supplies and it is all
  `Kakeya.VeryNotSticky.thickPres_fullness_ge` needs.
* essential distinctness does *not* survive enclosure. It transports to the images
  (`Kakeya.isEssentiallyDistinct_image_frameScale`), but two essentially distinct bodies may
  have enclosing planks that are not essentially distinct, which is exactly why
  `Kakeya.VeryNotSticky.plankFamilyEnclosure` establishes it only on a subfamily selected by
  `Kakeya.VeryNotSticky.plankSubfamilySelection`. So the structure carries that subfamily,
  `sel`, and states `windowed`, `essDistinct`, `fullness_ge`, `volume_le` and
  `nonconcentration` over it.

**What the selection costs, and that it is only a constant.** `plankSubfamilySelection`
retains a `Csel⁻¹` fraction of *any* nonnegative weight on the family, so at the weight `1` it
retains a `Csel⁻¹` fraction of the cardinality. That is the field `sel_card`, stated at the
one constant `CP`; the loss is a constant factor and nothing more, and
`Kakeya.VeryNotSticky.denseInBodyRaw_of_thickPlankPresentation` pays for it by one further
power of `CP` inside the non-concentration factor. In particular the cardinality bound
`hPcard` of blueprint `lem:ml2thickPcard`, which that lemma consumes to know `M ≥ 1`, is still
stated for the *block* and is untouched by the selection: the parameter `M` of
`nonconcentration` is still `Θ C_bias (δ/a)^{2+ϱ}|𝕋_{B,W}|`, with the block cardinality.

The two constants `CP` and `Θ` are *parameters* of this structure, and they stay parameters
all the way up: `Kakeya.VeryNotSticky.ThickPlankPresentable` quantifies `B` and `j` under a
fixed pair, and that pair is fixed once, ahead of the ball, the body and the thickening
parameter `θ`, by the fields `Kakeya.VeryNotSticky.CaseSideData.CP` and
`Kakeya.VeryNotSticky.CaseSideData.Θ`, which the parameter budget
`Kakeya.VeryNotSticky.PlankFrostmanUsable` shares. That is where uniformity lives; see the
module docstring for why the pair may be neither universally quantified, nor bound inside an
existential, nor named by a definition. The one quantity that is known to depend on `δ`, the
bias constant of blueprint `lemmafactmaxbias`, is not part of `CP` or `Θ` at all: it is the
explicit factor `bd.Cbias` in the fields `frostman` and `nonconcentration`.

Obligation (b) of `Kakeya.VeryNotSticky.exists_denseInBody` is discharged *in the statement*
by the choice to carry genuine `Plank`s together with the comparability fields
`short_lower`–`long_upper`, rather than the block itself: blueprint `plankF` wants planks, the
block consists of convex bodies whose affine thicknesses are merely comparable to
`(δ/b, δ/a, 1)`, and the bridge between them is asserted here — with the constant `CP`, which
is exactly blueprint `C_{lem:ml2thickPlank}(C₀)` — rather than proved. It changes no exponent,
since it only enlarges `CP` and `Θ`.

All four comparabilities are nevertheless available as theorems, so what is missing is the
*assembly* and not any one estimate. `Kakeya/DimensionThree/Plank/NormalisedThickness.lean`
proves `short_lower`–`long_upper` as
`Kakeya.thickness_two_prismNormalise_ge_const_of_subset`,
`Kakeya.thickness_one_prismNormalise_ge_const_of_subset` and their two `le` companions, at the
single constant `Kakeya.normalisedThicknessConstant C₀ = 192 C₀⁵`; the upper halves are also
available in the shape `Kakeya.VeryNotSticky.plankWindowEnclosure` consumes, as
`Kakeya.exists_frame_spread_le` of `Kakeya/DimensionThree/Plank/Alignment.lean`. Likewise
`volume_le` is `Kakeya.volume_preimage_thickenedNbhd_inter_le` of
`Kakeya/DimensionThree/Plank/NormalisedVolume.lean`. The fields are still *asserted* here
rather than derived because this structure is carried as a hypothesis and no construction of it
is given; a construction would have all of the above in hand.

Obligation (c) of the same docstring, the anisotropic change of variables, enters through
`volume_le` and `fullness_ge`, the two places where `|L(E)| = |det L| |E|` is used, and it is
no longer open. `Kakeya.volume_affineImage` and the transport lemmas of `Kakeya/AffineMap.lean`
supply that identity for a general affine equivalence, and the two items that
`Kakeya/Homothety.lean` provided for homotheties only — the invariance of `maxDensity` and of
`IsEssentiallyDistinct`, which enter the fields `frostman` and `essDistinct` below — are
`Kakeya.maxDensity_affineImage` and `IsEssentiallyDistinct.image_affineEquiv` of
`Kakeya/AffineMap.lean`. All of them are equalities or equivalences, so the anisotropy of
`L` costs no constant and enlarges neither `CP` nor `Θ`. Note
that `volume_le` no longer carries a bare `|B₁|`: the constant is the volume of the ball
`B̄(0, Plank.windowRadius)` in which the whole presentation lives, which is `δ`-free and
depends on the ambient dimension alone. It is a weaker constant than `|B₁|` and is available
whether the normalising map is read as landing in `B̄(0,1)` (as
`Kakeya.VeryNotSticky.plankRescaledFamily_subset_closedBall` gives for the homothety `L_B`) or
only in the window. -/
structure ThickPlankPresentation {cfg : VeryNotSticky.{u}} (bd : BallData cfg)
    (B : bd.bι) (j : bd.ω) (CP Θ C_NC : NNReal) where
  /-- The short plank dimension `a' ∼ δ/b`. -/
  a' : NNReal
  /-- The middle plank dimension `b' ∼ δ/a`. -/
  b' : NNReal
  /-- The planks are `a' × b' × 1` planks, so `a' ≤ b'`. -/
  hab' : a' ≤ b'
  /-- The planks are `a' × b' × 1` planks, so `b' ≤ 1`. -/
  hb1' : b' ≤ 1
  /-- `a' ≥ CP⁻¹ δ/b`: blueprint `lem:ml2thickPlank`(i), `τ₂(P) ∼ δ/b`, lower half. -/
  short_lower : (CP : ℝ)⁻¹ * ((cfg.δ : ℝ) / (cfg.b : ℝ)) ≤ (a' : ℝ)
  /-- `a' ≤ CP δ/b`: blueprint `lem:ml2thickPlank`(i), `τ₂(P) ∼ δ/b`, upper half. -/
  short_upper : (a' : ℝ) ≤ (CP : ℝ) * ((cfg.δ : ℝ) / (cfg.b : ℝ))
  /-- `b' ≥ CP⁻¹ δ/a`: blueprint `lem:ml2thickPlank`(i), `τ₁(P) ∼ δ/a`, lower half. -/
  long_lower : (CP : ℝ)⁻¹ * ((cfg.δ : ℝ) / (cfg.a : ℝ)) ≤ (b' : ℝ)
  /-- `b' ≤ CP δ/a`: blueprint `lem:ml2thickPlank`(i), `τ₁(P) ∼ δ/a`, upper half. -/
  long_upper : (b' : ℝ) ≤ (CP : ℝ) * ((cfg.δ : ℝ) / (cfg.a : ℝ))
  /-- The plank family `𝒫` enclosing the images `L(𝕋_{B,W})`, with its transported shading
  `Y_𝒫 = L(Y_B)`. The planks *contain* the images and are not equal to them; see the structure
  docstring for why no other family of genuine `Plank`s is available. -/
  P : bd.σ → ShadedPlank a' b' hab' hb1'
  /-- The subfamily on which the enclosing planks are pairwise essentially distinct
  (blueprint `lem:ml2plankSubfamilySelection`; Lean
  `Kakeya.VeryNotSticky.plankSubfamilySelection`). On the whole block the essential
  distinctness of the planks is *false* for every choice of the enclosure. -/
  sel : Finset bd.σ
  /-- The selection is a subfamily of the block. -/
  sel_subset : sel ⊆ (bd.segs B).filter fun p => bd.blk p = j
  /-- The selection retains the block cardinality up to the one constant `CP`. This is the
  weight clause of `Kakeya.VeryNotSticky.plankSubfamilySelection` read at the constant weight
  `1`, and it is what bounds the cost of the selection: a constant factor, and not a power of
  `δ`. `Kakeya.VeryNotSticky.denseInBodyRaw_of_thickPlankPresentation` pays for it with one
  further power of `CP`. -/
  sel_card : (CP : ENNReal)⁻¹ *
      ((((bd.segs B).filter fun p => bd.blk p = j).card : ℕ) : ENNReal) ≤
    ((sel.card : ℕ) : ENNReal)
  /-- `𝒫_sel` lies in the Section 6 window `B̄(0, Plank.windowRadius)`. This is the radius the
  enclosure `Kakeya.VeryNotSticky.plankWindowEnclosure` actually achieves — its
  `Kakeya.VeryNotSticky.plankBallRadius` derives from `Plank.windowRadius` — and it is the radius
  `Kakeya.FrostmanEstimate.plankEstimate` consumes, through `Plank.IsWindowedFamily`. The unit
  ball of blueprint `plankF` is not available: the images `L(T_p)` lie in `B̄(0,1)`, but the
  planks enclosing them need not. -/
  windowed : Plank.IsWindowedFamily sel (fun p => (P p).toPrism3D)
  /-- The planks are pairwise essentially distinct **on the selected subfamily**, as blueprint
  `plankF` demands of the family it is applied to. For the *images* `L(T_p)` this is
  `Kakeya.isEssentiallyDistinct_image_frameScale`; for the enclosing planks it holds only after
  the selection, which is the whole reason `sel` is part of this structure. -/
  essDistinct : (sel : Set bd.σ).Pairwise
    fun p q => _root_.IsEssentiallyDistinct (P p).carrier (P q).carrier
  /-- Blueprint `lem:ml2thickPlank`(iv), in the enclosure-weakened one-sided form:
  `CP⁻¹ λ(𝕋_{B,W}, Y_B) ≤ λ(𝒫_sel, Y_𝒫)`.

  The blueprint states the exact identity `λ(𝒫, Y_𝒫) = λ(𝕋_{B,W}, Y_B)`, and that is correct
  *about the images* `L(T_p)`, `λ` being a ratio of volumes and hence unchanged by `L`. It is
  false about the planks. `ShadedPlank extends Plank, ShadedBody`, so the plank's carrier is
  the shaded body's carrier and `λ = Σ|shade| / Σ|carrier|`; the enclosure enlarges every
  carrier and leaves every shade alone, so plank fullness is *smaller* than block fullness —
  the wrong way round for `Kakeya.VeryNotSticky.thickPres_fullness_ge`, which needs a lower
  bound on plank fullness. What the enclosure does give is a two-sided comparison of the
  carriers, `|P_p| ≤ C(C₀)|L(T_p)|` (`Kakeya.VeryNotSticky.plankEnclosureVolume`), together
  with the shade-mass retention of the selection; their quotient is this field, at the one
  constant `CP`. -/
  fullness_ge : CP⁻¹ * ShadedBody.fullness ((bd.segs B).filter fun p => bd.blk p = j) bd.Y ≤
    ShadedBody.fullness sel (fun p => (P p).toShadedBody)
  /-- Blueprint `lem:ml2thickPlank`(iii): the Frostman bound `C_F(𝒫_sel) ≤ CP C_bias`, taken in
  the plank window `Kakeya.plankWindow = B̄(0, 4)` and not in the unit ball.

  The window is forced by `windowed`: with the planks outside `B₁` there is no
  `Kakeya.ConvexSpaceBody.IsFrostmanIn.change_ambient` step available to convert a unit-ball
  bound into the plank-window bound that `Kakeya.FrostmanEstimate.plankEstimate` consumes, that
  conversion requiring the bodies to lie in the unit ball. Reading the bound in the window
  costs at most the volume ratio `|B₄|/|B₁| = 64`, a dimensional constant that `CP` absorbs.

  The bias constant `C_bias` is the field `bd.Cbias`, so its own `δ`-dependence — the
  sub-polynomial loss of blueprint `lemmafactmaxbias` — stays visible here rather than being
  hidden in a produced constant. -/
  frostman : ConvexSpaceBody.IsFrostmanIn sel
    (fun p => (P p).toConvexSpaceBody) Kakeya.plankWindow
    ((CP * bd.Cbias : NNReal) : ENNReal)
  /-- Blueprint `lem:ml2thickPlank`(ii), first display, cleared of division:
  `|U(𝒫_sel, Y_𝒫)| |W| ≤ |B̄(0, Plank.windowRadius)| |U(𝕋_{B,W}, Y_B) ∩ W|`.

  The identity behind it is `|U(𝒫, Y_𝒫)| |W| = |L(W)| |U(𝕋_{B,W}, Y_B) ∩ W|`, since `L`
  multiplies every volume by `|det L|`; the constant is therefore any `δ`-free upper bound for
  `|L(W)|`, and the volume of the ball in which the whole presentation lives is one. An earlier
  version wrote `|B₁|`, which asserts `L(W) ⊆ B̄(0,1)` on the nose; that is true for the
  homothety `L_B` of `Kakeya.VeryNotSticky.plankRescaledFamily_subset_closedBall` but not for
  every normalisation the geometry files use, and the weaker constant here is available for all
  of them. It depends only on the ambient dimension. The selection only shrinks the left-hand
  side, `U(𝒫_sel, Y_𝒫) ⊆ U(𝒫, Y_𝒫)`, so it costs nothing here. -/
  volume_le : volume (iUnionShade sel (fun p => (P p).toShadedBody)) *
        volume (bd.Wb j).carrier ≤
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3))
          Plank.windowRadius) *
        volume ((⋃ p ∈ (bd.segs B).filter fun p => bd.blk p = j, (bd.Y p).shade) ∩
          (bd.Wb j).carrier)
  /-- Blueprint `lem:ml2thickMbound`: the non-concentration hypothesis of blueprint `plankF` at
  `M = Θ C_bias (δ/a)^{2+ϱ} |𝒫|`, **uniformly in the plank `P ∈ 𝒫` and in the thickening
  parameter `θ ∈ [a'/b', 1]`**: the one `Θ`, produced before `cfg`, `B`, `j` and `θ`, serves
  all of them.

  **The container is the `C_NC`-dilated thickened prism, not the neighbourhood `N_{θb'}(P)`.**
  The field is `Plank.IsThickeningNonconcentrated sel 𝒫 C_NC M`, i.e.

  `|{q ∈ sel : P_q ⊆ ((P_p)_θ).dilation C_NC}| ≤ M θ`   for all `p ∈ sel`, `a'/b' ≤ θ ≤ 1`,

  where `(P_p)_θ = Plank.thickened (P_p) θ` is the prism of half-widths `(θ b', b', 1)` sharing
  `P_p`'s centre and axes, and `PrismNDim.dilation C_NC` multiplies **all three** half-widths by
  `C_NC`. This is what `Kakeya.VeryNotSticky.PlankFrostmanVolumeAt` — hence
  `Kakeya.FrostmanEstimate.plankEstimate`, hence GWZ Lemma 6.4 as Section 6 renders it —
  consumes, and it is a *stronger* demand than blueprint
  `eq:plank-thickening-nonconcentration`, which counts only the planks inside `N_{θb'}(P_p)`
  itself. Making it that is not a choice: the aligned form does not imply the dilated one at any
  constant, by the counterexample in the module docstring of
  `Kakeya/DimensionThree/Plank/FrostmanPlankReduction.lean`, so a field stated at
  `Plank.thickenedNbhd` — as an earlier version of this structure had it — cannot feed the
  estimate at all. See the second deviation bullet of
  `Kakeya.VeryNotSticky.PlankFrostmanVolumeAt`.

  This field is *assumed*, not derived, so the strengthening adds no proof debt here; it moves
  debt to Section 6's geometry, which is where blueprint `lem:ml2thickMbound` will have to be
  proved. What it does cost is one further factor `C_NC³` inside `Θ`, and the arithmetic is
  worth recording because the constant is what `Θ` must absorb:

  * `|((P_p)_θ).dilation C_NC| = 8 C_NC³ θ (b')²`, by `PrismNDim.volume_carrier` on the
    half-widths `C_NC (θ b', b', 1)`. That is `C_NC³` times `|(P_p)_θ| = 8 θ (b')²`
    (`Plank.volume_thickened`). An earlier version of this docstring argued for the radius of
    `Plank.thickenedNbhd (P_p) θ` and cited `Kakeya.volume_thickenedNbhd_le`, which gives
    `|N_{θb'}(P_p)| ≤ 64 θ (b')²`; that citation is now **wrong as an argument for this field**,
    because `N_{θb'}(P_p)` is not the container being counted in. The correct route is the
    displayed prism volume, and it is *not* available from `volume_thickenedNbhd_le`: the
    dilation grows the *long* axis to half-width `C_NC ≥ 1`, whereas `N_{θb'}(P_p)` reaches only
    `1 + θ b'` there. The two containers are genuinely different sets and neither contains the
    other.
  * blueprint `lem:ml2thickThickenedVol` is then applied to
    `K_θ = L^{-1}(((P_p)_θ).dilation C_NC) ∩ W` rather than to `L^{-1}(N_{θ δ/a}(P_p)) ∩ W`.
    That is legitimate for the same reason the change of radius already was: the proof of
    blueprint `lem:ml2thickMbound` uses `lem:ml2thickThickenedVol` only through a bound of the
    shape `|K_θ|/|W| ≤ Λ₀ θ (δ/a)²` with `Λ₀ ≥ 1` free of `δ`, so it runs verbatim at
    `Λ₀ = C_NC³ · 384 C₀³ CP²` in place of `384 C₀³ CP²`, and the biased comparison
    `Kakeya.VeryNotSticky.BallData.biasedDensity` of (C4) then supplies the gain
    `(|K_θ|/|W|)^ϱ`. Since that proof charges `Λ₀²` to the constant, `Θ` absorbs `C_NC⁶` — the
    cube from the three dilated half-widths, squared by the `ϱ`-absorption step of blueprint
    `lem:ml2thickPowerAbsorb`. All of it is `δ`-free and no exponent moves. `C_NC` is itself
    `δ`-free: Section 6 produces it ahead of `ε`, and it is
    `Plank.ThickenedRepr.fibreDilation cThk` for the geometric constant `cThk` of blueprint
    `lemmaredplanktube`.

  Nothing is ever thickened above parameter `1` and no comparison of radii is needed: the field
  is stated at the plank's *own* `b'`, which is only comparable to `δ/a` (`long_lower`,
  `long_upper`), and the consumer asks for exactly that. (An earlier version of this docstring
  routed the estimate through `N_{θ'' δ/a}(P)` at `θ'' = min (C_P θ) 1`. That route is **false**:
  in the branch `C_P θ > 1` the containment needs `θ b' ≤ δ/a`, whereas `long_upper` gives only
  `θ b' ≤ C_P δ/a` — take `θ = 1` and `b'` at its permitted upper value `C_P δ/a`.) The lower end
  of the range is likewise only shifted by a constant: `lem:ml2thickThickenedVol` uses `θ ≥ a/b`
  solely to conclude `θ δ/a ≥ δ/b`, and `θ ≥ a'/b' ≥ CP⁻²(a/b)` gives `θ δ/a ≥ CP⁻² δ/b`, a
  further two powers of `CP` that `Θ` absorbs as well.

  **The counting is over the selected subfamily `sel`, but the parameter `M` still carries the
  *block* cardinality** `|𝕋_{B,W}|`. Restricting the count only weakens the field, and keeping
  the block cardinality in `M` is what lets `Kakeya.VeryNotSticky.one_le_thickM` be fed by
  blueprint `lem:ml2thickPcard` unchanged. The mismatch between `M`'s `|𝕋_{B,W}|` and the
  `|sel|` that `plankF` returns in its conclusion is exactly the field `sel_card`, and it costs
  one further power of `CP`.

  **The bias factor `bd.Cbias` is explicit, and is not part of `Θ`.** Blueprint
  `def:ml2thickMboundConstant` defines `C_{lem:ml2thickMbound}` as a product one of whose
  factors is `C_{lemmafactmaxbias}`, and says that the constant depends "through the latter, on
  `δ` and on the cardinality of the family". In this development that factor is `bd.Cbias`, and
  it enters through `Kakeya.VeryNotSticky.BallData.biasedDensity` of (C4), which is the only
  source of the gain `(|K_θ|/|W|)^ϱ` that the proof of `lem:ml2thickMbound` uses. Writing this
  field with a `δ`-free `Θ` alone — as an earlier version of this file did — asserts strictly
  more than (C4) gives and is not derivable from it.

  **The thickening parameter ranges over `[a'/b', 1]`, the plank aspect ratio, and not over
  `[a/b, 1]`.** `Plank.IsThickeningNonconcentrated`, and hence
  `Kakeya.VeryNotSticky.PlankFrostmanVolumeAt`, consumes the hypothesis for every `θ` above the
  aspect ratio of the planks it is applied to, which is `a'/b'`; and `a'/b'` is only comparable
  to `a/b`, within `CP²`, so the two ranges are different and the plank one is the larger.

  **`M` is an `ℝ≥0`, not an `ℝ≥0∞`.** That is `Plank.IsThickeningNonconcentrated`'s convention,
  and it is Section 6's; it also removes the `M ≠ ⊤` side condition that an earlier version of
  this file carried. `Kakeya.VeryNotSticky.thickPlankF_apply` pushes the coercion into the
  `[0, ∞]`-valued arithmetic of `Kakeya/DimensionThree/MainLemma2/ThickPlankAux.lean`, which is
  unchanged. -/
  nonconcentration : Plank.IsThickeningNonconcentrated sel (fun p => (P p).toPrism3D) C_NC
    (Θ * bd.Cbias * (cfg.δ / cfg.a) ^ (2 + cfg.ϱ) *
      ((((bd.segs B).filter fun p => bd.blk p = j).card : ℕ) : NNReal))

/-! ### The comparabilities of `lem:ml2thickPlank`(i), in the form the assembly uses

The four fields `short_lower`–`long_upper` are stated in `ℝ`, because that is where
`Metric.thickness` lives, whereas blueprint `plankF` consumes the plank dimensions in `ℝ≥0`
and blueprint `lem:ml2thickPlankF` does its arithmetic in `[0, ∞]`. These five lemmas are the
transport, and nothing else; they are named so that the two consumers below do not each repeat
the cast bookkeeping. -/

/-- `0 < a'`: the short plank dimension is bounded below by `CP⁻¹ δ/b > 0`
(blueprint `lem:ml2thickPlank`(i)). Blueprint `plankF` needs it to speak of `a × b × 1`
planks at all. -/
theorem thickPres_a'_pos {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {B : bd.bι} {j : bd.ω}
    {CP Θ C_NC : NNReal} (hpres : ThickPlankPresentation bd B j CP Θ C_NC) (hCP : 1 ≤ CP) :
    0 < hpres.a' := by
  have hCPpos : (0 : ℝ) < (CP : ℝ) := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hCP)
  have hδpos : (0 : ℝ) < (cfg.δ : ℝ) := by
    exact_mod_cast cfg.hδ
  have hbpos : (0 : ℝ) < (cfg.b : ℝ) := by
    exact_mod_cast (cfg_b_pos cfg)
  have hdivpos : (0 : ℝ) < (cfg.δ : ℝ) / (cfg.b : ℝ) :=
    div_pos hδpos hbpos
  have hlower : (0 : ℝ) < (CP : ℝ)⁻¹ * ((cfg.δ : ℝ) / (cfg.b : ℝ)) :=
    mul_pos (inv_pos.mpr hCPpos) hdivpos
  have hreal : (0 : ℝ) < (hpres.a' : ℝ) :=
    lt_of_lt_of_le hlower hpres.short_lower
  exact NNReal.coe_pos.mp hreal

/-- `a' ≤ CP δ/b` in `ℝ≥0`: blueprint `lem:ml2thickPlank`(i), upper half, transported from
`ℝ`. -/
theorem thickPres_a'_le {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {B : bd.bι} {j : bd.ω}
    {CP Θ C_NC : NNReal} (hpres : ThickPlankPresentation bd B j CP Θ C_NC) :
    hpres.a' ≤ CP * cfg.δ / cfg.b := by
  exact (NNReal.coe_le_coe).mp (by
    rw [NNReal.coe_div, NNReal.coe_mul]
    simpa [mul_div_assoc] using hpres.short_upper)

/-- `b' ≤ CP δ/a` in `ℝ≥0`: blueprint `lem:ml2thickPlank`(i), upper half, transported from
`ℝ`. This is what the threshold `CP δ/a ≤ b₀` of
`Kakeya.VeryNotSticky.PlankFrostmanUsable` is compared against. -/
theorem thickPres_b'_le {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {B : bd.bι} {j : bd.ω}
    {CP Θ C_NC : NNReal} (hpres : ThickPlankPresentation bd B j CP Θ C_NC) :
    hpres.b' ≤ CP * cfg.δ / cfg.a := by
  exact (NNReal.coe_le_coe).mp (by
    rw [NNReal.coe_div, NNReal.coe_mul]
    simpa [mul_div_assoc] using hpres.long_upper)

/-- `CP⁻¹ (δ/b) ≤ a'` in `[0, ∞]`: blueprint `lem:ml2thickPlank`(i), lower half, in the shape
`Kakeya.VeryNotSticky.thickPlankF_product_lower` consumes. -/
theorem thickPres_inv_le_a' {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {B : bd.bι} {j : bd.ω}
    {CP Θ C_NC : NNReal} (hpres : ThickPlankPresentation bd B j CP Θ C_NC) (hCP : 1 ≤ CP) :
    (CP : ENNReal)⁻¹ * ((cfg.δ : ENNReal) / (cfg.b : ENNReal)) ≤ (hpres.a' : ENNReal) := by
  have hCP0 : (CP : NNReal) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hCP)
  have hb0 : (cfg.b : NNReal) ≠ 0 := ne_of_gt (cfg_b_pos cfg)
  have hNN : (CP : NNReal)⁻¹ * (cfg.δ / cfg.b : NNReal) ≤ hpres.a' := by
    exact (NNReal.coe_le_coe).mp (by
      simpa [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_div] using hpres.short_lower)
  calc
    (CP : ENNReal)⁻¹ * ((cfg.δ : ENNReal) / (cfg.b : ENNReal))
        = ((CP : NNReal)⁻¹ * (cfg.δ / cfg.b : NNReal) : ENNReal) := by
          rw [← ENNReal.coe_inv (r := CP) (hr := hCP0)]
          rw [← ENNReal.coe_div (r := cfg.b) (hr := hb0)]
    _ ≤ (hpres.a' : ENNReal) := (ENNReal.coe_le_coe).mpr hNN

/-- `CP⁻¹ (δ/a) ≤ b'` in `[0, ∞]`: blueprint `lem:ml2thickPlank`(i), lower half, in the shape
`Kakeya.VeryNotSticky.thickPlankF_product_lower` consumes. -/
theorem thickPres_inv_le_b' {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {B : bd.bι} {j : bd.ω}
    {CP Θ C_NC : NNReal} (hpres : ThickPlankPresentation bd B j CP Θ C_NC) (hCP : 1 ≤ CP) :
    (CP : ENNReal)⁻¹ * ((cfg.δ : ENNReal) / (cfg.a : ENNReal)) ≤ (hpres.b' : ENNReal) := by
  have hCP0 : (CP : NNReal) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hCP)
  have ha0 : (cfg.a : NNReal) ≠ 0 := ne_of_gt (cfg_a_pos cfg)
  have hNN : (CP : NNReal)⁻¹ * (cfg.δ / cfg.a : NNReal) ≤ hpres.b' := by
    exact (NNReal.coe_le_coe).mp (by
      simpa [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_div] using hpres.long_lower)
  calc
    (CP : ENNReal)⁻¹ * ((cfg.δ : ENNReal) / (cfg.a : ENNReal))
        = ((CP : NNReal)⁻¹ * (cfg.δ / cfg.a : NNReal) : ENNReal) := by
          rw [← ENNReal.coe_inv (r := CP) (hr := hCP0)]
          rw [← ENNReal.coe_div (r := cfg.a) (hr := ha0)]
    _ ≤ (hpres.b' : ENNReal) := (ENNReal.coe_le_coe).mpr hNN

open scoped Classical in
/-- **The fullness hypothesis of blueprint `plankF`, at the plank family** (blueprint
`lem:ml2thickPlank`(iv) followed by the second threshold of
`Kakeya.VeryNotSticky.PlankFrostmanUsable`).

`λ(𝒫_sel, Y_𝒫) ≥ CP⁻¹ λ(𝕋_{B,W}, Y_B) ≥ CP⁻¹ c₁ δ^{2η} ≥ (CP δ/b)^{η_{plankF}} ≥
(a')^{η_{plankF}}`, the first step being `fullness_ge`, the second `hfull`, the third the
threshold `hthr` and the fourth `short_upper` raised to a nonnegative power.

**Why the threshold carries an extra factor `CP`.** The enclosure makes the plank fullness
smaller than the block fullness, not equal to it (see
`Kakeya.VeryNotSticky.ThickPlankPresentation.fullness_ge`), so the chain has to pay `CP⁻¹`
somewhere. It is paid on the threshold, which is the field
`Kakeya.VeryNotSticky.PlankFrostmanUsable`: that predicate now asks for
`CP (CP δ/b)^{η_{plankF}} ≤ c₁ δ^{2η}` rather than `(CP δ/b)^{η_{plankF}} ≤ c₁ δ^{2η}`. Under the
thick-case guard this is the same kind of smallness condition on `δ` as before — the left-hand
side still tends to `0` with `δ` at a fixed `CP`, since `δ/b ≤ δ^τ` — so the budget stays
satisfiable. -/
theorem thickPres_fullness_ge {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {B : bd.bι}
    {j : bd.ω} {CP Θ C_NC : NNReal} (hpres : ThickPlankPresentation bd B j CP Θ C_NC)
    (hCP : 1 ≤ CP) {ηF : ℝ} (hηF : 0 ≤ ηF)
    (hthr : CP * (CP * cfg.δ / cfg.b) ^ ηF ≤ bd.c₁ * cfg.δ ^ (2 * cfg.η))
    (hfull : bd.c₁ * cfg.δ ^ (2 * cfg.η) ≤
      ShadedBody.fullness ((bd.segs B).filter fun p => bd.blk p = j) bd.Y) :
    hpres.a' ^ ηF ≤ ShadedBody.fullness hpres.sel (fun i => (hpres.P i).toShadedBody) := by
  have hCP0 : (CP : NNReal) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hCP)
  calc
    hpres.a' ^ ηF ≤ (CP * cfg.δ / cfg.b) ^ ηF := by
      exact NNReal.rpow_le_rpow (thickPres_a'_le hpres) hηF
    _ ≤ CP⁻¹ * (CP * (CP * cfg.δ / cfg.b) ^ ηF) := by
      rw [← mul_assoc, inv_mul_cancel₀ hCP0, one_mul]
    _ ≤ CP⁻¹ * (bd.c₁ * cfg.δ ^ (2 * cfg.η)) := by
      gcongr
    _ ≤ CP⁻¹ * ShadedBody.fullness ((bd.segs B).filter fun p => bd.blk p = j) bd.Y := by
      gcongr
    _ ≤ ShadedBody.fullness hpres.sel (fun i => (hpres.P i).toShadedBody) := hpres.fullness_ge

open scoped Classical in
/-- **Section 6 interface: the thick-case blocks are plank families, at one pair of constants**
(blueprint `lem:ml2thickPlank`, `lem:ml2thickThickenedVol` and `lem:ml2thickMbound`).

Every ball `B ∈ 𝔅` of the configuration and every block of a body `W ∈ 𝕎_B` presented through
one of its own segments `p₀` admits a `Kakeya.VeryNotSticky.ThickPlankPresentation`, all of
them at the *same* pair `(CP, Θ)`.

**The quantifier order is the statement.** `CP` and `Θ` stand outside the quantifiers over `B`
and `p₀`, and hence outside the quantifier over the thickening parameter `θ` that
`ThickPlankPresentation.nonconcentration` carries: one constant per exponent, valid for every
ball, every body and every `θ`. That is obligation (d) of
`Kakeya.VeryNotSticky.exists_denseInBody` discharged at the level of the statement.

This is a *predicate* and not a theorem, and that too is the statement. `CP` and `Θ` may not be
universally quantified here, since they occur on the *large* side of the comparabilities and of
the non-concentration bound; they may not be produced existentially, since the parameter budget
`Kakeya.VeryNotSticky.PlankFrostmanUsable` has to be asserted at the *same* `CP` and could not
see the witness; and they may not be pinned to a value, since the blueprint introduces them by
their defining property and any value chosen here would make this predicate false or — if the
value were sealed — independent. So they are carried as data, once, by the fields
`Kakeya.VeryNotSticky.CaseSideData.CP` and `Kakeya.VeryNotSticky.CaseSideData.Θ`, and this
predicate and the budget are two fields of
`Kakeya.VeryNotSticky.ThickDensityThresholds` stated at that one pair. See the module docstring.

The bias constant of blueprint `lemmafactmaxbias` is not part of either: it is the explicit
factor `bd.Cbias` in the fields `frostman` and `nonconcentration`.

**What is assumed, and why it is satisfiable.** Take `CP = C_{lem:ml2thickPlank}(bd.C₀)` and
`Θ = C_{lem:ml2thickMbound}(bd.C₀)`, the constants of blueprint `def:ml2thickPlankConstant` and
`def:ml2thickMboundConstant`; at those values the predicate is exactly what blueprint
`lem:ml2thickPlank`, `lem:ml2thickThickenedVol` and `lem:ml2thickMbound` assert. Three distinct
pieces of that are not formalized, and none is thick-case material:

* the alignment estimate behind blueprint `lem:ml2thickPlank`(i) — that a convex body of
  diameter `∼ r₁` contained in a body of thicknesses `∼ (r₁, b, a)` is nearly parallel to the
  long frame direction, so that the anisotropic `L` acts on its frame essentially diagonally.
  The blueprint asserts it with the constant `C_{lem:ml2thickPlank}(C₀)` and does not prove
  it; it belongs in the convex-body chapter next to blueprint `def:outerPrism`;
* the replacement of the images `L(T_B)`, which are convex bodies comparable to planks, by
  genuine `Plank`s. This is obligation (b): it costs constants of the same kind as those
  already carried by `CP` and `Θ`, so it changes no exponent, but it is not carried out;
* for a general anisotropic `L`, the invariance of `maxDensity` and of
  `IsEssentiallyDistinct`. `Kakeya.volume_affineImage` and the transport suite of
  `Kakeya/AffineMap.lean` — built on `MeasureTheory.Measure.addHaar_image_linearMap` — already
  give the volume identity, the fullness and the multiplicity for an arbitrary affine
  equivalence, so this residue is narrower than obligation (c) of
  `Kakeya.VeryNotSticky.exists_denseInBody` records, but `Kakeya/Homothety.lean` still carries
  `maxDensity_homothety` and `IsEssentiallyDistinct.image_homothety` for homotheties only,
  and `L` normalising the outer prism of `W` is anisotropic.

The non-concentration field additionally rests on blueprint `lem:ml2thickThickenedVol`, the
pullback volume bound `|K_θ|/|W| ≤ 2³ C_{lem:ml2thickPlank}^4 |B₁|^{-1} θ (δ/a)²`, and on the
biased comparison `Kakeya.VeryNotSticky.BallData.biasedDensity` of (C4) applied at
`K = L^{-1}((P)_θ) ∩ W`; the first is unformalized, the second is available. -/
def ThickPlankPresentable {cfg : VeryNotSticky.{u}} (bd : BallData cfg) (CP Θ C_NC : NNReal) :
    Prop :=
  ∀ B ∈ bd.bs, ∀ p₀ ∈ bd.segs B,
    Nonempty (ThickPlankPresentation bd B (bd.blk p₀) CP Θ C_NC)

/-- **The thick-case dense-shading estimate in a body, before the surplus is spent**
(blueprint `lem:ml2thickPlankF`, display `plankFexplicit`, transported back to the body `W`).

`δ^ν (a/δ)^{ϱβ/2} δ^{2β} |W| ≤ Θ C₁ a^{2β} |U(𝕋_{B,W}, Y_B) ∩ W|`.

This is the conclusion of blueprint `lem:ml2thickPlankF` at `ε = ν` and prescribed constant
`1`, read through blueprint `lem:ml2thickPlank`(ii) and cleared of division, so that no
positivity or finiteness side condition is needed in `[0, ∞]`. The whole thick-case surplus
`(a/δ)^{ϱβ/2}` is still present on the small side; `Kakeya.VeryNotSticky.exists_denseInBody`
spends it, keeping `δ^{-2ν}` of the `δ^{-4ν}` that `hthick` converts it into and paying the
prescribed constant `Λ` with the rest.

The factor `|B₁|` of blueprint `thickDensityThresholds` does not appear here: it is absorbed
by `Kakeya.VeryNotSticky.denseInBodyRaw_of_thickPlankPresentation`, which is the declaration
that *produces* the pair `Θ'`, `C₁'` of this predicate — subject only to `1 ≤ Θ'`, `1 ≤ C₁'` —
out of the parameters `Θ`, `CP` of the presentation and the volume comparison
`ThickPlankPresentation.volume_le`, where `|B₁|` enters. The parameters `Θ`, `CP` carried by
the presentation itself are untouched by that absorption. -/
def DenseInBodyRaw {cfg : VeryNotSticky.{u}} (bd : BallData cfg) (ν : ℝ) (Θ C₁ : NNReal)
    (B : bd.bι) (j : bd.ω) : Prop :=
  (cfg.δ : ENNReal) ^ ν * ((cfg.a : ENNReal) / (cfg.δ : ENNReal)) ^ (cfg.ϱ * cfg.β / 2) *
      ((cfg.δ : ENNReal) ^ (2 * cfg.β) * volume (bd.Wb j).carrier) ≤
    (Θ : ENNReal) * (C₁ : ENNReal) *
      ((cfg.a : ENNReal) ^ (2 * cfg.β) *
        volume ((⋃ p ∈ (bd.segs B).filter fun p => bd.blk p = j, (bd.Y p).shade) ∩
          (bd.Wb j).carrier))

/-- **The parameter budget of blueprint `plankF`, at the scales of the configuration.**

Blueprint `lem:ml2thickPlankF` applies `plankF` at `ε = ν = ϱβτ/8`, and needs the parameters
`η_{plankF}` and `b₀` that `plankF` produces to be compatible with the configuration: `δ/a` must
be below `b₀`, and `cfg.η` must be below `τ η_{plankF}`. This predicate says exactly that, with
the comparison constant `CP` of blueprint `lem:ml2thickPlank` made explicit, because the plank
family lives at `a' ≤ CP δ/b` and `b' ≤ CP δ/a` rather than at `δ/b` and `δ/a` on the nose.

The second threshold carries one extra factor `CP`, i.e. it reads
`CP (CP δ/b)^{η_{plankF}} ≤ c₁ δ^{2η}`. That factor pays for the enclosure: the planks of
`Kakeya.VeryNotSticky.ThickPlankPresentation` *contain* the images `L(T_p)`, so their fullness
is smaller than the block's by at most `CP` and not equal to it. See
`Kakeya.VeryNotSticky.thickPres_fullness_ge`. It is the same kind of smallness condition on
`δ` as before, `CP` being fixed ahead of `δ`.

The estimate and the threshold on `b₀` are bundled deliberately.
`Kakeya.VeryNotSticky.PlankFrostmanVolumeAt` is antitone in both `η_{plankF}` and `b₀` — the
smaller they are, the weaker the statement — while both thresholds ask for them to be *large*.
So neither parameter can be quantified away from the thresholds, and the honest hypothesis is
that `plankF` holds *at parameters that fit `cfg`*, rather than that it holds and, separately,
that some thresholds are met.

**The exponent `ηF` is a parameter of this predicate, not an existential inside it**, for the
same reason `CP` is: it has to be compared with `cfg.η` from outside. Under the thick-case
guard `δ^{1-τ} ≤ a` the second threshold reads `CP^{1+ηF} δ^{τ ηF - 2η} ≤ c₁` (F8: (C5) at
`δ^{2η}`), so it is met for `δ` small exactly when `2η < τ ηF` —
which is the field `Kakeya.VeryNotSticky.ThickDensityThresholds.budget` since R16-A — and that comparison is a relation between `δ`-free
parameters. With `ηF` bound inside the predicate the relation could not be stated at all, and
nothing would prevent the witness from exceeding the exponent at which the estimate is still
true; see `Kakeya.VeryNotSticky.plankFrostmanExponent`. The relation itself is the field
`Kakeya.VeryNotSticky.ThickDensityThresholds.budget`, and it is arranged, at the canonical
exponent, by `Kakeya.VeryNotSticky.exists_caseParams`.

`Kakeya.VeryNotSticky` and `Kakeya.VeryNotSticky.CaseParams` carry no field for either
threshold, and blueprint `hyp:ml2params` lists no such budget; this is obligation (d) of
`Kakeya.VeryNotSticky.exists_denseInBody`, now named rather than absorbed. -/
def PlankFrostmanUsable {cfg : VeryNotSticky.{u}} (bd : BallData cfg) (τ : ℝ)
    (CP C_NC : NNReal) (ηF : ℝ) : Prop :=
  ∃ b₀ : NNReal,
    PlankFrostmanVolumeAt.{u} cfg.β (cfg.ϱ * cfg.β * τ / 8) ηF b₀ C_NC ∧
      CP * cfg.δ / cfg.a ≤ b₀ ∧
      CP * (CP * cfg.δ / cfg.b) ^ ηF ≤ bd.c₁ * cfg.δ ^ (2 * cfg.η)

open scoped Classical in
/-- **Blueprint `plankF`, applied to the plank presentation of a thick-case block** (the first
half of blueprint `lem:ml2thickPlankF`).

Every hypothesis of `Kakeya.VeryNotSticky.PlankFrostmanVolumeAt` is discharged from the fields
of `Kakeya.VeryNotSticky.ThickPlankPresentation` and the two thresholds of `hbudget`:

* the planks are `a' × b' × 1` planks in the Section 6 window, pairwise essentially distinct
  *on the selected subfamily `sel`*, by `hab'`, `hb1'`, `windowed`, `essDistinct`; `0 < a'`
  because `short_lower` bounds it below by `CP⁻¹ δ/b > 0`; and `b' ≤ b₀` because `long_upper`
  bounds it above by `CP δ/a`, which is the first threshold of `hbudget`;
* the fullness hypothesis `a'^{η_{plankF}} ≤ λ(𝒫_sel, Y_𝒫)` is `short_upper` raised to the
  power `η_{plankF} > 0`, then the second threshold of `hbudget`, then the block fullness
  `hfull` transported by `fullness_ge`;
* the Frostman hypothesis is `frostman` verbatim, at the constant `CP C_bias`, in the plank
  window;
* the non-concentration hypothesis is `nonconcentration` verbatim, at
  `M = Θ C_bias (δ/a)^{2+ϱ}|𝕋_{B,W}|`, whose two side conditions `1 ≤ M` and `M ≠ ⊤` are
  `Kakeya.VeryNotSticky.one_le_thickM` — where `hPcard`, blueprint `lem:ml2thickPcard`, is
  used — and `Kakeya.VeryNotSticky.thickM_ne_top`. Note that `M` carries the *block*
  cardinality while `plankF` is applied to the *selected* family, so its conclusion carries
  `|sel|`; the two are compared by `sel_card`, in
  `Kakeya.VeryNotSticky.denseInBodyRaw_of_thickPlankPresentation`.

The conclusion is the display of blueprint `plankF` at `ε = ν = ϱβτ/8`, in the shape that
`Kakeya.VeryNotSticky.thickPlankF_product_lower` bounds from below. -/
theorem thickPlankF_apply {cfg : VeryNotSticky.{u}} (bd : BallData cfg) {τ : ℝ}
    {CP Θ C_NC : NNReal} (hCP : 1 ≤ CP) (hΘ : 1 ≤ Θ) {ηF : ℝ} (hηF : 0 < ηF)
    (hbudget : PlankFrostmanUsable bd τ CP C_NC ηF)
    {B : bd.bι} {p₀ : bd.σ}
    (hpres : ThickPlankPresentation bd B (bd.blk p₀) CP Θ C_NC)
    (hfull : bd.c₁ * cfg.δ ^ (2 * cfg.η) ≤
      ShadedBody.fullness ((bd.segs B).filter fun p => bd.blk p = bd.blk p₀)
        bd.Y)
    (hPcard : ((cfg.a : ENNReal) / (cfg.δ : ENNReal)) ^ (2 + cfg.ϱ) ≤
      ((((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℕ) : ENNReal)) :
    (hpres.a' : ENNReal) ^ (cfg.ϱ * cfg.β * τ / 8) *
          ((CP : ENNReal) * (bd.Cbias : ENNReal)) ^ (cfg.β / 2 - 1) *
          (hpres.b' : ENNReal) ^ (2 * cfg.β) *
          (((Θ : ENNReal) * (bd.Cbias : ENNReal) *
                  ((cfg.δ : ENNReal) / (cfg.a : ENNReal)) ^ (2 + cfg.ϱ) *
                  ((((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℕ) : ENNReal))⁻¹ *
              (hpres.b' : ENNReal) ^ (2 : ℝ) *
              ((hpres.sel.card : ℕ) : ENNReal)) ^
            (cfg.β / 2) ≤
      64 * volume (iUnionShade hpres.sel (fun p => (hpres.P p).toShadedBody)) := by
  obtain ⟨b₀, hPF, hb₀, hthr⟩ := hbudget
  have hane : cfg.a ≠ 0 := ne_of_gt (cfg_a_pos cfg)
  have hdiv0 : cfg.δ / cfg.a ≠ 0 := div_ne_zero (ne_of_gt cfg.hδ) hane
  -- the non-concentration parameter, in `ℝ≥0` as `Plank.IsThickeningNonconcentrated` wants it
  set Mn : NNReal := Θ * bd.Cbias * (cfg.δ / cfg.a) ^ (2 + cfg.ϱ) *
      ((((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℕ) : NNReal) with hMndef
  have hMc : (Mn : ENNReal) = (Θ : ENNReal) * (bd.Cbias : ENNReal) *
      ((cfg.δ : ENNReal) / (cfg.a : ENNReal)) ^ (2 + cfg.ϱ) *
      ((((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℕ) : ENNReal) := by
    rw [hMndef, ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_mul,
      ENNReal.coe_rpow_of_ne_zero hdiv0, ENNReal.coe_div hane]
    norm_cast
  have hM1 : 1 ≤ (Θ : ENNReal) * (bd.Cbias : ENNReal) *
      ((cfg.δ : ENNReal) / (cfg.a : ENNReal)) ^ (2 + cfg.ϱ) *
      ((((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℕ) : ENNReal) := by
    exact one_le_thickM (by exact_mod_cast hΘ) (by exact_mod_cast bd.hCbias)
      (ne_of_gt (by exact_mod_cast cfg.hδ)) ENNReal.coe_ne_top
      (ne_of_gt (by exact_mod_cast cfg_a_pos cfg)) ENNReal.coe_ne_top hPcard
  have hMn1 : (1 : NNReal) ≤ Mn := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_one, hMc]
    exact hM1
  have hmain := hPF hpres.sel hpres.hab' hpres.hb1' hpres.P
      (thickPres_a'_pos hpres hCP) (le_trans (thickPres_b'_le hpres) hb₀)
      hpres.windowed hpres.essDistinct
      (thickPres_fullness_ge hpres hCP hηF.le hthr hfull)
      (CP * bd.Cbias) (one_le_mul hCP bd.hCbias) hpres.frostman
      Mn hMn1 hpres.nonconcentration
  rw [hMc] at hmain
  simpa [ENNReal.coe_mul] using hmain

/-- **Section 6 interface stub: the plank estimate in the thick case** (blueprint
`lem:ml2thickPlankF`).

Feeding a `Kakeya.VeryNotSticky.ThickPlankPresentation` of a block, the plank estimate
`Kakeya.VeryNotSticky.PlankFrostmanVolume` at `ε = ν = ϱβτ/8`, and the cardinality bound
`(a/δ)^{2+ϱ} ≤ |𝕋_{B,W}|` of blueprint `lem:ml2thickPcard` — which makes the parameter
`M = Θ (δ/a)^{2+ϱ}|𝒫|` of `ThickPlankPresentation.nonconcentration` at least `1`, as
`plankF` requires — into each other yields
`Kakeya.VeryNotSticky.DenseInBodyRaw` at `Θ` and `C₁ = CP C_bias`.

**Proved.** The parameter budget of blueprint `plankF` is now the hypothesis `hbudget`, and
each step of the assembly is a proved lemma of
`Kakeya/DimensionThree/MainLemma2/ThickPlankAux.lean`:

* the three constant-carrying factors of the `plankF` conclusion, bounded as in the proof of
  blueprint `lem:ml2thickPlankF`: `(a')^ν ≥ CP^{-ν} δ^ν` since `a' ≥ CP⁻¹ δ/b ≥ CP⁻¹ δ`;
  `C_F^{β/2-1} ≥ (CP C_bias)⁻¹` since `-1 ≤ β/2 - 1 < 0`; and
  `(M^{-1}(b')²|𝒫|)^{β/2} ≥ CP^{-β} Θ^{-1}(a/δ)^{ϱβ/2}` by the value of `M` and
  `0 < β/2 ≤ 1`. Each is a `δ`-free inequality between rpow-expressions in `[0, ∞]`; they are
  `Kakeya.VeryNotSticky.rpow_mul_le_rpow_of_inv_mul_le`,
  `Kakeya.VeryNotSticky.inv_le_rpow_of_neg_one_le` and `Kakeya.VeryNotSticky.thickM_lower`
  with `Kakeya.VeryNotSticky.rpow_thickM_lower`, combined by
  `Kakeya.VeryNotSticky.thickPlankF_product_lower`;
* the comparabilities `a' ∼ δ/b`, `b' ∼ δ/a` of `ThickPlankPresentation`, which turn the
  plank-scale conclusion into the `(δ/a)^{2β}` of `DenseInBodyRaw` at the cost of a further
  power of `CP`, and the volume comparison `ThickPlankPresentation.volume_le`, which transports
  the conclusion from `𝒫_sel` back to the block inside `W` and is where the window volume
  `|B̄(0, Plank.windowRadius)|` comes from. Both are
  `Kakeya.VeryNotSticky.thickPlankF_conclude`.

**The cost of the selection.** `plankF` is applied to the selected subfamily, so its conclusion
carries `|sel|`, whereas the non-concentration parameter `M` carries the block cardinality
`|𝕋_{B,W}|`. The field `ThickPlankPresentation.sel_card` compares them, `CP⁻¹|𝕋_{B,W}| ≤ |sel|`,
and `Kakeya.VeryNotSticky.exists_denseConst_of_plankF` absorbs the resulting `CP⁻¹` by running
its arithmetic at `CP Θ C_bias` in place of `Θ C_bias`. So the whole cost of carrying an
*enclosing*, *selected* family rather than the images themselves is one further power of `CP`
in the produced constant — no exponent moves, and in particular nothing is lost that depends on
`δ`.

The parameter budget itself is the hypothesis `hbudget`, i.e.
`Kakeya.VeryNotSticky.PlankFrostmanUsable`: `plankF` has to be applied at parameters
`(η_{plankF}, b₀)` compatible with the configuration, namely `CP δ/a ≤ b₀(ν, β)` and
`(CP δ/b)^{η_{plankF}} ≤ c₁ δ^{2η}`. Two points about it:

* the estimate and its thresholds cannot be separated. `PlankFrostmanVolumeAt` is *antitone*
  in both `η_{plankF}` and `b₀` — the smaller they are, the weaker the statement — while both
  thresholds ask for them to be *large*. So the honest hypothesis is
  `PlankFrostmanUsable`, which bundles them, and not `PlankFrostmanVolume` together with two
  separate inequalities. The exponent `η_{plankF}` is nonetheless a *binder* of this
  signature, `ηF`, and not an existential inside the predicate: the relation `2 cfg.η < τ ηF`
  that the second threshold needs is `δ`-free and has to be arranged where the parameters are
  chosen, which is `Kakeya.VeryNotSticky.exists_caseParams`. Only `b₀`, which no budget
  outside the predicate mentions, stays bound inside it;
* it is supplied by the field `Kakeya.VeryNotSticky.ThickDensityThresholds.plankF` of the
  structure of blueprint `thickDensityThresholds`, which is already how `hδ₂` and `hΛ` reach
  the thick case, and it travels here through
  `Kakeya.VeryNotSticky.exists_denseInBodyRaw`, `Kakeya.VeryNotSticky.exists_denseInBody` and
  `Kakeya.VeryNotSticky.goalMult_of_a_ge`. Like the field `density` of that structure it is
  guarded by the thick-case hypothesis `δ^{1-τ} ≤ a`, without which it is refutable; see the
  structure's docstring.

**The constants produced.** `thickPlankF_conclude` delivers the bound at
`64 |B̄(0,4)| CP^{ν+3β} (CP Θ C_bias)(CP C_bias)`, and this lemma splits that product as
`Θ' = CP Θ C_bias²` and `C₁' = max 1 (64 |B̄(0,4)| CP^{ν+3β} CP)`, i.e. the whole bias
contribution is put into `Θ'` and the whole `δ`-free geometric contribution into `C₁'`. The
choice is
immaterial to every consumer — `Kakeya.VeryNotSticky.ThickDensityThresholds.density` and
`Kakeya.VeryNotSticky.goalMult_of_a_ge` quantify over `Θ`, `C₁ ≥ 1` and use only the product —
and it is compatible with blueprint `setupSideDataDensityThreshold`, which budgets
`C_{lemmafactmaxbias}` explicitly. The bias enters squared rather than once because steps 1's
correction makes it explicit in `nonconcentration` as well as in `frostman`; since
`Θ C_bias ≥ 1` and `β/2 ≤ 1`, the extra factor is paid at the exponent `-1` rather than
`-β/2`, which is what `Kakeya.VeryNotSticky.inv_le_rpow_of_neg_one_le` supplies. -/
theorem denseInBodyRaw_of_thickPlankPresentation {cfg : VeryNotSticky.{u}} (bd : BallData cfg)
    {τ : ℝ} (hτ : 0 < τ) (hβ1 : cfg.β ≤ 1)
    {CP Θ C_NC : NNReal} (hCP : 1 ≤ CP) (hΘ : 1 ≤ Θ) {ηF : ℝ} (hηF : 0 < ηF)
    (hbudget : PlankFrostmanUsable bd τ CP C_NC ηF)
    {B : bd.bι} {p₀ : bd.σ} (hp₀ : p₀ ∈ bd.segs B)
    (hpres : ThickPlankPresentation bd B (bd.blk p₀) CP Θ C_NC)
    (hfull : bd.c₁ * cfg.δ ^ (2 * cfg.η) ≤
      ShadedBody.fullness ((bd.segs B).filter fun p => bd.blk p = bd.blk p₀)
        bd.Y)
    (hPcard : ((cfg.a : ENNReal) / (cfg.δ : ENNReal)) ^ (2 + cfg.ϱ) ≤
      ((((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℕ) : ENNReal)) :
    ∃ Θ' C₁' : NNReal, 1 ≤ Θ' ∧ 1 ≤ C₁' ∧
      DenseInBodyRaw bd (cfg.ϱ * cfg.β * τ / 8) Θ' C₁' B (bd.blk p₀) := by
  have hp₀s : p₀ ∈ (bd.segs B).filter fun p => bd.blk p = bd.blk p₀ :=
    Finset.mem_filter.mpr ⟨hp₀, rfl⟩
  have hcard : ((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card ≠ 0 :=
    Finset.card_ne_zero_of_mem hp₀s
  have hN0 : ((((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℕ) : ENNReal) ≠ 0 := by
    exact_mod_cast hcard
  have hd0 : (cfg.δ : ENNReal) ≠ 0 := by simpa using (ne_of_gt cfg.hδ)
  have hna0 : (cfg.a : ENNReal) ≠ 0 := by simpa using (ne_of_gt (cfg_a_pos cfg))
  have hnb0 : (cfg.b : ENNReal) ≠ 0 := by simpa using (ne_of_gt (cfg_b_pos cfg))
  have hnb1 : (cfg.b : ENNReal) ≤ 1 := by exact_mod_cast (cfg_b_le_one cfg)
  have hB1 : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3))
      Plank.windowRadius) ≠ ⊤ :=
    (MeasureTheory.measure_closedBall_lt_top).ne
  have hν : (0 : ℝ) ≤ cfg.ϱ * cfg.β * τ / 8 := by
    have h1 : 0 < cfg.ϱ := cfg.hϱ
    have h2 : 0 < cfg.β := cfg.hβ
    positivity
  exact exists_denseConst_of_plankF hCP hΘ bd.hCbias hN0 (ENNReal.natCast_ne_top _)
    hd0 ENNReal.coe_ne_top hna0 ENNReal.coe_ne_top hnb0 hnb1 hB1 hν cfg.hβ hβ1
    (thickPres_inv_le_a' hpres hCP) (thickPres_inv_le_b' hpres hCP)
    hpres.sel_card
    (thickPlankF_apply bd hCP hΘ hηF hbudget hpres hfull hPcard)
    hpres.volume_le

/-- **The thick case delivers a dense body, before the surplus is spent** (blueprint
`lem:ml2thickDensity`, the part of it that Section 6 owns).

There are constants `Θ, C₁ ≥ 1` — produced, hence available to a caller as bounds on a
prescribed constant — a ball `B ∈ 𝔅` and a body `W ∈ 𝕎_B` with
`Kakeya.VeryNotSticky.DenseInBodyRaw`, i.e.

`δ^ν (a/δ)^{ϱβ/2} δ^{2β} |W| ≤ Θ C₁ a^{2β} |U(𝕋_{B,W}, Y_B) ∩ W|`, `ν = ϱβτ/8`.

This is the single entry point that `Kakeya.VeryNotSticky.exists_denseInBody` consumes. It is
*proved*: it selects the ball and the block with
`Kakeya.VeryNotSticky.exists_thickFullBlock`, reads the plank presentation of that block off
the hypothesis `hpres`, applies the plank estimate at
`ε = ν` — legitimate since `ν > 0` by `cfg.hϱ`, `cfg.hβ` and `hτ` — and assembles the three
with `Kakeya.VeryNotSticky.denseInBodyRaw_of_thickPlankPresentation`.

The cardinality hypothesis `hPcard` is blueprint `lem:ml2thickPcard`, in the form `M ≥ 1` at
any `Θ ≥ 1`: it is supplied by the caller, because it is *proved* there —
`Kakeya.VeryNotSticky.thickPcard_ge` derives it from
`Kakeya.VeryNotSticky.thickBlockCard_ge` and the threshold `hδ₂`, both of which live with the
thick-case counting material. It is stated for every segment of every ball, and not only for
the selected one, because the selection happens inside this proof; `hpres` is stated over the
same range and for the same reason.

The plank estimate itself reaches this statement only through the hypothesis `hbudget`:
`Kakeya.VeryNotSticky.plankFrostmanVolume`, which asserts it unconditionally from `K_F(β)`, is
proved and kernel-clean, but is not applied here. What is assumed is the plank presentation `hpres`
(blueprint `lem:ml2thickPlank`, `lem:ml2thickThickenedVol`, `lem:ml2thickMbound`) and the
compatibility of the estimate's parameters with `cfg`, the hypothesis `hbudget`. Both are
stated at the *same* triple `CP`, `Θ`, `C_NC`, which is the point of the arrangement described
in the module docstring; they reach their consumers from the fields
`Kakeya.VeryNotSticky.ThickDensityThresholds.plankPres` and
`Kakeya.VeryNotSticky.ThickDensityThresholds.plankF`. -/
theorem exists_denseInBodyRaw {cfg : VeryNotSticky.{u}} (bd : BallData cfg) {τ : ℝ}
    (hτ : 0 < τ) (hβ1 : cfg.β ≤ 1) {CP Θ₀ C_NC : NNReal} (hCP : 1 ≤ CP) (hΘ₀ : 1 ≤ Θ₀)
    {ηF : ℝ} (hηF : 0 < ηF)
    (hbudget : PlankFrostmanUsable bd τ CP C_NC ηF)
    (hpres : ThickPlankPresentable bd CP Θ₀ C_NC)
    (hPcard : ∀ B ∈ bd.bs, ∀ p₀ ∈ bd.segs B,
      ((cfg.a : ENNReal) / (cfg.δ : ENNReal)) ^ (2 + cfg.ϱ) ≤
        ((((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℕ) : ENNReal)) :
    ∃ Θ C₁ : NNReal, 1 ≤ Θ ∧ 1 ≤ C₁ ∧
      ∃ B ∈ bd.bs, ∃ j ∈ bd.bodies B,
        DenseInBodyRaw bd (cfg.ϱ * cfg.β * τ / 8) Θ C₁ B j := by
  obtain ⟨B, hB, p₀, hp₀, hfull⟩ := exists_thickFullBlock bd
  obtain ⟨pres⟩ := hpres B hB p₀ hp₀
  obtain ⟨Θ, C₁, hΘ, hC₁, hraw⟩ :=
    denseInBodyRaw_of_thickPlankPresentation bd hτ hβ1 hCP hΘ₀ hηF hbudget hp₀ pres hfull
      (hPcard B hB p₀ hp₀)
  exact ⟨Θ, C₁, hΘ, hC₁, B, hB, bd.blk p₀, bd.blk_mem B hB p₀ hp₀, hraw⟩

end Kakeya.VeryNotSticky
