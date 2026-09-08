/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.CThickening
public import Kakeya.DimensionThree.MainLemma2.ThinBookkeeping
public import Kakeya.DimensionThree.MainLemma2.ThinAssembly
public import Kakeya.DimensionThree.MainLemma2.ThinCore
public import Kakeya.DimensionThree.MainLemma2.ThinFactorFamily
public import Kakeya.Frostman
public import Kakeya.Multiplicity

/-!
# The thin-case configuration of Main Lemma 2

This file formalizes blueprint Definition `hyp:ml2thinsetup` (the thin-case refinement of
Subsection `subsec:thincase`) and the lemmas that produce it.

The blueprint states the configuration globally, for all balls `B ∈ 𝔅` of the covering
family of Configuration `hyp:ml2setup` at once. Every lemma that *uses* it, however, first
fixes a ball `B ∈ 𝔅`, so we bundle the data per ball: `Kakeya.ThinCase.ThinBall` records,
for a single ball, the family `𝕋_B` of tube segments with its shading `Y_B`, the factoring
`𝕋_B = ⨆_{W ∈ 𝕎_B} 𝕋_{B,W}`, and the thin-case output `(Y'_B, 𝒮_B, 𝕎'_B, Y_{𝕎'_B})`
subject to (T1)–(T6). The uniformity in `B` demanded by the blueprint — a *single* pair of
constants serving for every ball — is expressed by making the comparison constant `C` a
*parameter* of the structure: the production lemma `Kakeya.ThinCase.perBall` supplies a
value of `C` depending only on the ball-independent input constants.

The two genuinely global assertions of (T1) — that the amalgamated shading `Y'` on `𝕋` is
a `⪆ 1` refinement of `Y`, and the two-way compatibility of `Y'` with the per-ball `Y'_B` —
are the content of `Kakeya.ThinCase.globalShading` and `Kakeya.ThinCase.localToGlobal`,
which are stated directly in terms of the pieces `B̂` of the subordinate partition.
-/

@[expose] public section

namespace Kakeya.ThinCase

open MeasureTheory Metric Set ShadedBody

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Constant in Definition `hyp:ml2thinsetup`** (blueprint `def:ml2thinW1Constant`).

A constant `≥ 1` such that the shortest dimension `w₁ = τ₂(W)` of every body `W ∈ 𝕎_B`
satisfies `(w1Constant C₀)⁻¹ a ≤ w₁ ≤ w1Constant C₀ * a`; the radius used by every covering
argument of the thin case is then `A = w1Constant C₀ * a ≥ w₁`.

It is a function of the implicit constant `C₀` of the thickness comparison `τ₂(W) ∼ a` of
(C4) alone, and not of `δ`, of `B` or of `W`. The value `4 * C₀` is what the two hypotheses
of `Kakeya.ThinCase.perBall` give: `HasThicknesses (Wb j).carrier C₀ ![r₁, b, a]` bounds
`τ₂(W) ≤ C₀ a`, and `w₁ ≤ 2 τ₂(W)`. The factor `4` rather than `2` is there because the
neighbourhood radius that the shading of the bodies actually comes with is `2 τ₂(W)` and not
`τ₂(W)`: the outer shaded bodies of the corrected factoring proposition are enlargements, and
`ShadedBody.outerFactoringFamily_outerShadeSubset` places their shade in the
`2 τ₂(W)`-neighbourhood of the shaded block. Accordingly `ThinBall.w_le` asks for
`2 τ₂(W) ≤ A`, which needs `2 C₀ ≤ w1Constant C₀`, and the remaining margin is what keeps
`w₁ ≤ A` available at the same time. The displayed value is provisional. -/
noncomputable def w1Constant (C₀ : NNReal) : NNReal := max 1 (4 * C₀)

lemma one_le_w1Constant (C₀ : NNReal) : 1 ≤ w1Constant C₀ := le_max_left _ _

lemma four_mul_le_w1Constant (C₀ : NNReal) : 4 * C₀ ≤ w1Constant C₀ := le_max_right _ _

lemma two_mul_le_w1Constant (C₀ : NNReal) : 2 * C₀ ≤ w1Constant C₀ := by
  calc
    2 * C₀ ≤ 4 * C₀ := by
      exact mul_le_mul_of_nonneg_right (by norm_num : (2 : NNReal) ≤ 4) (by positivity)
    _ ≤ w1Constant C₀ := four_mul_le_w1Constant C₀

/-- The radius `A = C_{w₁}(C₀) a` at which every covering argument of the thin case is carried
out (blueprint `def:ml2thinW1Constant`); it satisfies `A ∼ a` and `A ≥ w₁`. -/
noncomputable def rad (C₀ a : NNReal) : NNReal := w1Constant C₀ * a

/-- **The thin-case configuration attached to one ball** (blueprint `hyp:ml2thinsetup`).

Here `segs` indexes the family `𝕋_B` of tube segments of (C3) with shading `Y`
(the blueprint's `Y_B`), `bodies` indexes the family `𝕎_B` of factoring bodies of (C4),
`Wb` is the body itself and `blk` the block map of the factoring
`𝕋_B = ⨆_{W ∈ 𝕎_B} 𝕋_{B,W}`. The scale `a` is the shortest dimension of the bodies and
`δ` the thickness of the tubes; `η` is the density exponent.

The single constant `C` absorbs every `∼`, `≈`, `⪆` and `⪅` of (T1)–(T6); it is a
parameter, not a field, so that a statement quantified over the balls `B ∈ 𝔅` can demand
the *same* constant for every ball, as the amalgamation of the per-ball refinements
requires. The second constant `C₀` is the thickness comparison constant of (C3)/(C4); it
enters only through the radius `A = rad C₀ a` of blueprint `def:ml2thinW1Constant`, at which
(T4)(c) and (T6) are stated. -/
structure ThinBall (C C₀ : NNReal) {σ ω : Type*} [DecidableEq ω] (segs : Finset σ)
    (Y : σ → ShadedBody E) (bodies : Finset ω) (Wb : ω → ConvexSpaceBody E) (blk : σ → ω)
    (δ a : NNReal) (η : ℝ) where
  /-- The comparison constant is at least one. -/
  one_le_C : 1 ≤ C
  /-- The refined shading `Y'_B` of (T1), carried by the *same* index family `𝕋_B`:
  no tube segment is discarded and `𝕋_B` is not renamed. -/
  Y' : σ → ShadedBody E
  /-- `Y'_B` shades the same tube segments as `Y_B`. -/
  carrier_Y' : ∀ p ∈ segs, (Y' p).toConvexSpaceBody = (Y p).toConvexSpaceBody
  /-- (T1) `Y'_B(T_B) ⊆ Y_B(T_B)` for every `T_B ∈ 𝕋_B`. -/
  shade_Y'_subset : ∀ p ∈ segs, (Y' p).shade ⊆ (Y p).shade
  /-- (T1) the non-empty subfamily `𝒮_B ⊆ 𝕋_B` on which the refinement is termwise. -/
  S : Finset σ
  /-- `𝒮_B` is a subfamily of `𝕋_B`. -/
  S_subset : S ⊆ segs
  /-- `𝒮_B` is non-empty. -/
  S_nonempty : S.Nonempty
  /-- (T1) `𝒮_B` carries a `⪆ 1` fraction of the mass of `Y_B`. -/
  mass_S : ∑ p ∈ segs, volume (Y p).shade ≤ C * ∑ p ∈ S, volume (Y p).shade
  /-- (T1) the refinement loses at most a factor `C` on each segment of `𝒮_B`. -/
  refine_S : ∀ p ∈ S, volume (Y p).shade ≤ C * volume (Y' p).shade
  /-- The subfamily `𝕎'_B ⊆ 𝕎_B` produced by the factoring proposition. -/
  bodies' : Finset ω
  /-- `𝕎'_B` is a subfamily of `𝕎_B`. -/
  bodies'_subset : bodies' ⊆ bodies
  /-- The shading `Y_{𝕎'_B}` on `𝕎'_B`; its carrier is the *enlarged* outer body, not the
  geometric body `Wb j`. -/
  W : ω → ShadedBody E
  /-- Lower half of the enlargement sandwich: the geometric body of `𝕎_B` sits inside the
  carrier of the shaded body. -/
  Wb_le_W : ∀ j ∈ bodies', Wb j ≤ (W j).toConvexSpaceBody
  /-- Upper half of the enlargement sandwich: the carrier of the shaded body is contained in
  the closed `τ₂(Wb j)`-neighbourhood of the geometric body. Together with `Wb_le_W` this is
  the construction-independent replacement of the (false) equality
  `(W j).toConvexSpaceBody = Wb j`: the outer shaded bodies of the corrected factoring
  proposition carry the enlargement `N_{τ₂(W)}(W)` as their carrier. Every downstream fact
  follows from the sandwich — volume control via
  `ConvexSpaceBody.volume_cthickening_le`, the thickness profile via
  `ConvexSpaceBody.hasThicknesses_of_between`, ball localisation and positivity — and neither
  field mentions `C`, so `ThinBall.mono` passes both through unchanged. -/
  W_le_cthickening : ∀ j ∈ bodies', (W j).toConvexSpaceBody ≤ (Wb j).cthickening (Wb j).scale
  /-- **(T2) the density bound `λ(𝕎'_B, Y_{𝕎'_B}) ⪆ δ^{3η}`.**

  **Why `3η` and not `2η`.** The only route to this clause is the biased-factoring pipeline of
  `Kakeya.ThinCase.factoringApply`, whose conjunct (i) is proved by transporting the input
  fullness `δ^η ≤ Cfull · λ(𝕋_B, Y_B)` through Frostman (`ConvexSpaceBody.IsFrostmanIn`) and the
  Córdoba density estimate, and that transport charges a `δ^{-η}` — the price of converting a
  *shade*-mass retention into the *carrier*-mass retention that
  `ConvexSpaceBody.IsFrostmanIn.of_le_of_subset` needs. So the honest output exponent is
  `η + η + η`, not `η + η`; the `δ^{-η}` is exhibited by the exact identity
  `θ³ (δ^η)³ C = 2 CF Cfull³ lam²` of that transport, not hidden in a constant.

  **Read at the index `2 · cfg.η`.** The (C5) clause
  `Kakeya.VeryNotSticky.BallData.segs_density` reads `c₁ δ^{2η}`, and
  `Kakeya.VeryNotSticky.ThinConfig.tb` instantiates this structure at `η := 2 · cfg.η`; at a ball
  of the configuration this clause therefore reads `δ^{6 cfg.η}`, `denseBall` (T5) reads
  `C⁻¹ δ^{2 cfg.η}`, and the budgets below are read at that index (`slabDensity : 6η < exscal`
  from `η ≤ exscal/8`; the tangential chain at `8η`, `SlabMultKT.fullness_threshold : 9η ≤ η₁`;
  the transverse chain at `3τ + 7η`; the slab chain at the honest `11η + 10 exscal + 3τ` with the
  `4η` margin of `slabVolumeGoal` spent). The paragraphs below describe the move `2η ↝ 3η` of
  this field in its own index and are kept as its record.

  **The extra `η` is free.** `η` is chosen *last*, as a `min` of eight upper bounds
  (`Kakeya.VeryNotSticky.exists_caseParams`), and every field of
  `Kakeya.VeryNotSticky.CaseParams` mentioning `η` bounds it from above only — its own
  `Kakeya.VeryNotSticky.CaseParams.transverse` docstring says so, and records two earlier
  instances of exactly this move (`η+ϱ ↝ 2η+ϱ`, `3τ+9η ↝ 3τ+12η`). Raising a coefficient from
  `2` to `3` costs picking `η` two thirds as large, and the *choice* of `η` in
  `exists_caseParams` does not move at all: the only `CaseParams` field that has to follow is
  `slabDensity`, from `2η < exscal` to `3η < exscal`, and that is discharged from the
  **unchanged** `η ≤ exscal/4`.

  **What follows it, in full.** Three of the five sites that read this field are
  exponent-agnostic — `Kakeya.VeryNotSticky.slabBodiesNonempty`,
  `Kakeya.VeryNotSticky.thinBallPositivity_nonempty` and
  `Kakeya.VeryNotSticky.thinBallPositivity_shade_pos` use only `0 < δ^{2η}` through
  `ENNReal.rpow_pos`. `Kakeya.VeryNotSticky.slabPrismDensity` needs the hypothesis field
  `Kakeya.VeryNotSticky.SlabInputs.densityThreshold` (and its companion
  `Kakeya.VeryNotSticky.SlabScale.density`) at `δ^{3η}`, which is the budget above.
  `Kakeya.VeryNotSticky.slabBodyMassBound` propagates mechanically along the slab chain, and
  that chain lands inside `Kakeya.VeryNotSticky.CaseParams.slab`, which this move left
  unchanged at its then text `9η + 10exscal + 3τ < β/2`, spending `1η` of the `5η` of unused
  headroom it was carrying, so that `4η` remained. (The budget reads `12η + 12exscal + 3τ < β/2`: the extra `3η + 2exscal` is the explicit `δ^{2η}`
  loss of the repaired clause (T7), `Kakeya.VeryNotSticky.ThinConfig.segment_mass`, plus the
  fibre-count budget `δ^{-(η+2exscal)}` of `Kakeya.VeryNotSticky.SlabScale.fibreMass`; the `4η`
  of margin is kept — see the docstring of `CaseParams.slab`.) Two further readers each lose
  one `η` in their conclusion —
  `Kakeya.VeryNotSticky.typicalAngleRefinedFullness` and
  `Kakeya.VeryNotSticky.tangentialDensityChain`, `4η ↝ 5η` — which moves
  `Kakeya.VeryNotSticky.TypicalAngleData.hfull` (no term-level users) and
  `Kakeya.VeryNotSticky.IsDenseSlab.dense`, and hence
  `Kakeya.VeryNotSticky.SlabMultKT.fullness_threshold` from `5η ≤ η₁` to `6η ≤ η₁` — a bound on
  the Katz–Tao exponent `η₁`, which is chosen after `η`, not on `η`.

  **Not re-indexing `ThinBall` at `3η/2`.** That would reach the same exponent here but would
  also weaken this structure's *other* `η`-field, `denseBall` (T5), which nothing asks for; and
  it would still be a field change, of `Kakeya.VeryNotSticky.ThinConfig.tb`. Editing this one
  field is strictly better. -/
  fullness_bodies : (δ : ENNReal) ^ (3 * η) ≤ (C : ENNReal) * (fullness bodies' W : ENNReal)
  /-- (T3) the pointwise containment: every segment shading a point `x` lies in a block
  whose body is shaded at `x`. -/
  shade_containment : ∀ p ∈ segs, ∀ x ∈ (Y' p).shade, blk p ∈ bodies' ∧ x ∈ (W (blk p)).shade
  /-- (T4)(a) `(𝕎'_B, Y_{𝕎'_B})` has constant multiplicity. -/
  constMult_bodies : HasCConstantMultiplicity bodies' W C
  /-- The common inner multiplicity of the blocks, appearing in (T4)(b). -/
  μinner : NNReal
  /-- (T4)(b) each block `(𝕋_{B,W}, Y'_B)` has constant multiplicity, and this multiplicity
  is the same for all `W ∈ 𝕎'_B`. -/
  constMult_blocks : ∀ j ∈ bodies',
    ∀ x ∈ iUnionShade (segs.filter fun p => blk p = j) Y',
      (pointwiseMultiplicity (segs.filter fun p => blk p = j) Y' x : ENNReal) ≤ C * μinner ∧
      (μinner : ENNReal) ≤
        C * (pointwiseMultiplicity (segs.filter fun p => blk p = j) Y' x : ENNReal)
  /-- (T4)(c) the *centred* multiplicity statement at radius `A = C_{w₁} a`: the quantity
  `|U(𝕋_B, Y'_B) ∩ B(x, A)|` is the same up to a factor `≈ 1` for every `x` in
  `U(𝕋_B, Y'_B)`. The variant quantifying over all `A`-balls merely *meeting* the union is
  false: such a ball can touch the union tangentially. -/
  centredMult : ∀ x ∈ iUnionShade segs Y', ∀ y ∈ iUnionShade segs Y',
    volume (iUnionShade segs Y' ∩ ball x ((rad C₀ a : NNReal) : ℝ)) ≤
      C * volume (iUnionShade segs Y' ∩ ball y ((rad C₀ a : NNReal) : ℝ))
  /-- (T5) the typical-density estimate for the *final* shading: every segment of `𝒮_B`
  contains a `δ`-ball on which `Y'_B` has density `≳ δ^η`. -/
  denseBall : ∀ p ∈ S, ∃ x : E, (C : ENNReal)⁻¹ * (δ : ENNReal) ^ η *
    volume (ball x (δ : ℝ)) ≤ volume (ball x (δ : ℝ) ∩ (Y' p).shade)
  /-- The radius `w₁ = τ₂(W)` of the induced shading (T6), *per body*: it is the shortest
  dimension of the body `W` itself, i.e. `Metric.thickness ℝ (Wb j).carrier (finrank ℝ E - 1)`
  in the applications, as in `ShadedBody.inducedShading`. The bodies of `𝕎_B` have shortest
  dimension only *comparable* to `a`, not equal to it, so a single radius shared by all of
  them would be a genuine extra assumption. -/
  w : ω → ℝ
  /-- `2 * w j ≤ A = rad C₀ a` for every body of `𝕎'_B`, as in blueprint
  `def:ml2thinW1Constant`; this is the only property of `w` that the thin case uses. The
  doubled left-hand side is the radius that `shade_W_subset` below actually comes with, and it
  is what lets `Kakeya.ThinCase.bodiesInTubeNbhd` conclude `UW ⊆ N_A(U)` unchanged. -/
  w_le : ∀ j ∈ bodies', 2 * w j ≤ (rad C₀ a : ℝ)
  /-- (T6) `Y_{𝕎'_B}(W) ⊆ N_{2w₁}(U(𝕋_{B,W}, Y'_B))` at twice the per-body radius
  `w₁ = τ₂(W)`, as in blueprint `compatibilityOfShadingOnWWwithVV`.

  This one-sided containment replaces the former equality
  `(W j).shade = (Wb j).carrier ∩ N_{w j}(…)`, which is false for the corrected factoring
  proposition: its outer shaded bodies are genuine enlargements, their shade is
  `N_{w j}(Wb j) ∩ N_{2 w j}(…)` and need not lie in `Wb j` at all. The radius `2 * w j` is the
  one delivered by `ShadedBody.outerFactoringFamily_outerShadeSubset`, and the containment is
  all that any consumer uses. -/
  shade_W_subset : ∀ j ∈ bodies', (W j).shade ⊆
    cthickening (2 * w j) (iUnionShade (segs.filter fun p => blk p = j) Y')

namespace ThinBall

variable {C C₀ : NNReal} {σ ω : Type*} [DecidableEq ω] {segs : Finset σ} {Y : σ → ShadedBody E}
  {bodies : Finset ω} {Wb : ω → ConvexSpaceBody E} {blk : σ → ω} {δ a : NNReal} {η : ℝ}

/-- The shaded union `U(𝕋_B, Y'_B)` of the tube segments. -/
def U (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η) : Set E := iUnionShade segs tb.Y'

/-- The shaded union `U(𝕎'_B, Y_{𝕎'_B})` of the factoring bodies. -/
def UW (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η) : Set E := iUnionShade tb.bodies' tb.W

/-- `ThinBall` is monotone in its comparison constant `C`: if a ball realises the thin-case
data at constant `C`, the *same* data realises it at any larger constant `C'`. The fields
carrying `C` on the larger side (`mass_S`, `refine_S`, `fullness_bodies`, `constMult_blocks`,
`centredMult`) weaken by monotonicity of the product, and `denseBall`, where `C` is inverted,
weakens by the antitone inverse. Neither half of the enlargement sandwich (`Wb_le_W`,
`W_le_cthickening`) nor `shade_W_subset` mentions `C`, so all three are passed through
unchanged. This is what lets `Kakeya.ThinCase.thinSetupExists` pass from
the per-ball constant `perBallConstant` of `Kakeya.ThinCase.perBall` to the global
`thinSetupConstant` without disturbing the data. -/
noncomputable def mono {C C' : NNReal} (hCC' : C ≤ C')
    (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η) :
    ThinBall C' C₀ segs Y bodies Wb blk δ a η := by
  have hCem : (C : ENNReal) ≤ (C' : ENNReal) := ENNReal.coe_le_coe.mpr hCC'
  refine ThinBall.mk ?one_le_C ?Y' ?carrier_Y' ?shade_Y'_subset ?S ?S_subset ?S_nonempty
    ?mass_S ?refine_S ?bodies' ?bodies'_subset ?W ?Wb_le_W ?W_le_cthickening ?fullness_bodies
    ?shade_containment ?constMult_bodies ?μinner ?constMult_blocks ?centredMult ?denseBall
    ?w ?w_le ?shade_W_subset
  · exact le_trans tb.one_le_C hCC'
  · exact tb.Y'
  · exact tb.carrier_Y'
  · exact tb.shade_Y'_subset
  · exact tb.S
  · exact tb.S_subset
  · exact tb.S_nonempty
  · exact le_trans tb.mass_S (mul_le_mul' hCem le_rfl)
  · intro p hp
    exact (tb.refine_S p hp).trans (mul_le_mul' hCem le_rfl)
  · exact tb.bodies'
  · exact tb.bodies'_subset
  · exact tb.W
  · exact tb.Wb_le_W
  · exact tb.W_le_cthickening
  · exact le_trans tb.fullness_bodies (mul_le_mul' hCem le_rfl)
  · exact tb.shade_containment
  · exact HasCConstantMultiplicity.mono tb.bodies' tb.W hCC' tb.constMult_bodies
  · exact tb.μinner
  · intro j hj x hx
    rcases tb.constMult_blocks j hj x hx with ⟨h1, h2⟩
    exact ⟨h1.trans (mul_le_mul' hCem le_rfl), h2.trans (mul_le_mul' hCem le_rfl)⟩
  · intro x hx y hy
    exact (tb.centredMult x hx y hy).trans (mul_le_mul' hCem le_rfl)
  · intro p hp
    rcases tb.denseBall p hp with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hinv : (C' : ENNReal)⁻¹ ≤ (C : ENNReal)⁻¹ := ENNReal.inv_le_inv' hCem
    exact (mul_le_mul' (mul_le_mul' hinv le_rfl) le_rfl).trans hx
  · exact tb.w
  · exact tb.w_le
  · exact tb.shade_W_subset

end ThinBall

end

/-! ### Transfer along the enlargement

The five lemmas of this section are the only interface a consumer needs in order to work with
the *original* geometric bodies `Wb j` while the thin-case bundle actually carries the enlarged
outer carriers `(W j).toConvexSpaceBody`. Each is derived from the sandwich
`ThinBall.Wb_le_W` / `ThinBall.W_le_cthickening` alone, and from no property of the factoring
construction, so none of them has to be revisited when Proposition 5.1 is completed. -/

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

namespace ThinBall

variable {C C₀ : NNReal} {σ ω : Type*} [DecidableEq ω] {segs : Finset σ} {Y : σ → ShadedBody E}
  {bodies : Finset ω} {Wb : ω → ConvexSpaceBody E} {blk : σ → ω} {δ a : NNReal} {η : ℝ}

omit [Nontrivial E] in
/-- **The geometric body is no larger than the shaded one** (blueprint
`lem:ml2thinVolumeWbLe`): the lower half of the sandwich, in volume. -/
theorem volume_Wb_le (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η) :
    ∀ j ∈ tb.bodies', volume (Wb j).carrier ≤ volume (tb.W j).carrier := by
  intro j hj
  exact measure_mono (SetLike.coe_subset_coe.mpr (tb.Wb_le_W j hj))

omit [Nontrivial E] in
/-- **The summed form of `ThinBall.volume_Wb_le`** (blueprint `lem:ml2thinVolumeWbLe`): the
shape in which the plank presentation of the slab case consumes it. -/
theorem sum_volume_Wb_le (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η) :
    ∑ j ∈ tb.bodies', volume (Wb j).carrier ≤ ∑ j ∈ tb.bodies', volume (tb.W j).carrier := by
  exact Finset.sum_le_sum tb.volume_Wb_le

/-- **The shaded bodies are a volume-controlled enlargement of the geometric ones** (blueprint
`lem:ml2thinVolumeControlled`).

This is the form in which `Δ_max` and the Katz--Tao property transfer from `Wb` to `W`, by
composing with `ConvexSpaceBody.IsVolumeControlledEnlargement.maxDensity_le` and
`ConvexSpaceBody.IsVolumeControlledEnlargement.isKatzTao`; those two consequences are
deliberately not restated here. The constant is the dimensional volume comparison constant, and
in particular does not depend on the ball, on `δ` or on the body. -/
theorem isVolumeControlledEnlargement (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η) :
    ConvexSpaceBody.IsVolumeControlledEnlargement tb.bodies' Wb
      (fun j ↦ (tb.W j).toConvexSpaceBody)
      (volume_comparison.C (Module.finrank ℝ E) : ENNReal) := by
  intro j hj
  constructor
  · exact tb.Wb_le_W j hj
  · let r : NNReal := (Wb j).scale.toNNReal
    have hscale : 0 ≤ (Wb j).scale := by
      exact Metric.thickness_nonneg (Wb j).carrier (Module.finrank ℝ E - 1)
    have hr : (r : ℝ) = (Wb j).scale := by
      exact Real.coe_toNNReal (Wb j).scale hscale
    calc
      volume ((tb.W j).toConvexSpaceBody).carrier
          ≤ volume ((Wb j).cthickening (Wb j).scale).carrier := by
            exact measure_mono (SetLike.coe_subset_coe.mpr (tb.W_le_cthickening j hj))
      _ ≤ volume ((Wb j).cthickening (r : ℝ)).carrier := by
            rw [← hr]
      _ ≤ (volume_comparison.C (Module.finrank ℝ E) : ENNReal) * volume (Wb j).carrier := by
            exact ConvexSpaceBody.volume_cthickening_le (Wb j) r (le_of_eq hr)

/-- **The thickness profile of the enlarged bodies** (blueprint `lem:ml2thinHasThicknessesW`): a
profile assumed of the geometric bodies `Wb j` is available for the enlarged carriers at the
cost of a single factor `2`.

The lower half of the profile comes from `ThinBall.Wb_le_W`, the upper half from
`ThinBall.W_le_cthickening` together with
`ConvexSpaceBody.hasThicknesses_cthickening`; both are packaged in
`ConvexSpaceBody.hasThicknesses_of_between`. No lower bound on the input constant is needed,
only `0 ≤ t k`. -/
theorem hasThicknesses_W {m : ℕ} {C₁ : NNReal} {t : Fin m → ℝ}
    (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η) (ht : ∀ k, 0 ≤ t k)
    (hWb : ∀ j ∈ tb.bodies', HasThicknesses (Wb j).carrier C₁ t) :
    ∀ j ∈ tb.bodies', HasThicknesses (tb.W j).carrier (2 * C₁) t := by
  intro j hj
  have hnonneg : 0 ≤ (Wb j).scale := by
    dsimp [ConvexSpaceBody.scale]
    exact Metric.thickness_nonneg (Wb j).carrier (Module.finrank ℝ E - 1)
  have hcoeff : ((Real.toNNReal (Wb j).scale : NNReal) : ℝ) = (Wb j).scale :=
    Real.coe_toNNReal (Wb j).scale hnonneg
  exact ConvexSpaceBody.hasThicknesses_of_between (K := Wb j) (L := (tb.W j).toConvexSpaceBody)
    (r := Real.toNNReal (Wb j).scale) (by rw [hcoeff])
    (tb.Wb_le_W j hj) (by rw [hcoeff]; exact tb.W_le_cthickening j hj) ht (hWb j hj)

omit [Nontrivial E] in
/-- **Ball localisation of the enlarged bodies** (blueprint `lem:ml2thinCarrierBall`): if every
geometric body of `𝕎'_B` lies in `B̄(ctr, r)` and every one of them has scale at most `s`, then
every enlarged carrier lies in `B̄(ctr, r + s)`.

The enlargement is by the scale of the body itself, so the localisation survives with the
radius increased by a bound for that scale — which in the applications is `∼ a`, of the same
order as the bodies. -/
theorem carrier_subset_closedBall (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η)
    {ctr : E} {r s : ℝ}
    (hball : ∀ j ∈ tb.bodies', (Wb j).carrier ⊆ closedBall ctr r)
    (hs : ∀ j ∈ tb.bodies', (Wb j).scale ≤ s) :
    ∀ j ∈ tb.bodies', (tb.W j).carrier ⊆ closedBall ctr (r + s) := by
  intro j hj
  have hscale_nonneg : 0 ≤ (Wb j).scale := by
    simpa using (Metric.thickness_nonneg (Wb j).carrier (Module.finrank ℝ E - 1))
  have hs0 : 0 ≤ s := le_trans hscale_nonneg (hs j hj)
  rcases (Wb j).nonempty with ⟨x, hx⟩
  have hr0 : 0 ≤ r := by
    exact Metric.nonempty_closedBall.mp ⟨x, hball j hj hx⟩
  calc
    (tb.W j).carrier ⊆ Metric.cthickening (Wb j).scale (Wb j).carrier := by
      exact SetLike.coe_subset_coe.mpr (tb.W_le_cthickening j hj)
    _ ⊆ Metric.cthickening s (Wb j).carrier := Metric.cthickening_mono (hs j hj) (Wb j).carrier
    _ ⊆ Metric.cthickening s (closedBall ctr r) :=
      Metric.cthickening_subset_of_subset s (hball j hj)
    _ ⊆ closedBall ctr (r + s) := by
      rw [cthickening_closedBall hs0 hr0 ctr, add_comm s r]

omit [Nontrivial E] in
/-- **Positivity of the enlarged volumes** (blueprint `lem:ml2thinVolumeWPos`): immediate from
the lower half of the sandwich. -/
theorem volume_W_pos (tb : ThinBall C C₀ segs Y bodies Wb blk δ a η)
    (hpos : ∀ j ∈ tb.bodies', 0 < volume (Wb j).carrier) :
    ∀ j ∈ tb.bodies', 0 < volume (tb.W j).carrier := by
  intro j hj
  exact lt_of_lt_of_le (hpos j hj) (measure_mono (tb.Wb_le_W j hj))

end ThinBall

end Transfer

/-! ### Producing the configuration -/

section Produce

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Constant in Lemma `lem:ml2thinFactoringApply`.**

The comparison constant of the conclusions of `Kakeya.ThinCase.factoringApply`: it is a
function of the Frostman constant `CF` of (C4) and of the constant `Cfull` in the fullness
hypothesis `δ^η ⪅ λ(𝕋_B, Y_B)`, and of the core envelope `Ccore` of the dyadic-pigeonhole
losses of Proposition 5.1 at the family in question. The displayed value is provisional.

**Why `Ccore` is present, and why the statement is false without it.** The former value
`max 1 (2 * volume_comparison.C 3 * CF * Cfull ^ 2)` — a function of `CF` and `Cfull` alone —
makes `Kakeya.ThinCase.factoringApply` a *false* statement, in two independent ways.

The first is degenerate: with no `0 < δ`, no `δ ≤ w₁ ≤ 1`, no `1 ≤ CF` and `η` free, the
fullness hypothesis `δ^η ≤ Cfull * λ(𝕋_B, Y_B)` is satisfiable with `Cfull` arbitrarily small,
collapsing the constant to `1`; and at `C = 1` clause (vi) demands exact mass preservation and
clause (iv) exact pointwise maximality, which two far-separated unit balls with different shade
volumes refute. The `max Ccore` branch together with the binder `2 ≤ Ccore` closes this.

The second is robust, and is the reason `Ccore` must depend on the family and not only on the
constants. Take unit balls as bodies, pairwise separated by `10` times their radius, and split
them into `K` dyadic mass classes, class `i` holding `2^i` bodies of shade volume `V 2^{-i-1}`,
so that every class carries the same total mass `V / 2`. All the hypotheses hold at
`CF = Cfull = 1`. Clause (iv) then pins every positive retained mass into `[m, C m]`, so at most
`V / m` bodies contribute and `∑ v'_j ≤ C V`, while clause (vi) demands `∑ v'_j ≥ C⁻¹ K V / 2`.
Hence `K ≤ 2 C²`. Since `K` is free while `CF`, `Cfull`, `δ`, `η`, `w₁` and the dimension are all
fixed, *no* constant depending only on `CF` and `Cfull` can be correct; the necessary growth is
`C ≳ √(log₂ |𝕋_B|)`. The `max Ccore` branch closes this too, because
`Kakeya.ThinCase.factoringApplyCore` dominates `⌊log₂ |𝕎_B|⌋ + 1` and
`(ShadedBody.outerFactoringFamily_refinement.c 3 |𝕋_B| δ)⁻¹ ≥ 4 (⌊log₂ |𝕋_B|⌋ + 1)^4`.

This is *not* a departure from GWZ. GWZ Proposition 5.1 states its items with `⪆`/`⪅`,
formalized in this repository as `Kakeya.LEApprox` — up to `ρ^{-ε}` for every `ε > 0` — which is
exactly what absorbs a dyadic pigeonhole logarithm. Pinning the constant to `CF` and `Cfull`
alone asserted something strictly *stronger* than GWZ, and that is why it was false. That the
repair stays inside the `⪅` budget is `Kakeya.ThinCase.factoringApplyCore_leApprox_one`.

Two factors beyond `CF * Cfull ^ 2 * Ccore` are carried because the outer bodies of the corrected
Proposition 5.1 are enlargements rather than the blocks themselves. The dimensional volume
comparison constant `volume_comparison.C 3`, which is the constant
`ShadedBody.outerFactoringFamily_volumeControlled.C 3` of the volume-controlled enlargement, is
what the passage from `volume (Wb j).carrier` to `volume (W j).carrier` costs in the density
conclusion (i); and the factor `2` is the one that
`ConvexSpaceBody.hasThicknesses_cthickening` charges for the thickness profile of the enlarged
carrier. `Cfull` enters *squared* because item (i) of the proposition produces a lower bound
proportional to `CF⁻¹ λ(𝕋_B, Y_B) ^ 2`. -/
noncomputable def factoringApplyConstant (CF Cfull Ccore : NNReal) : NNReal :=
  max 1 (max Ccore (2 * volume_comparison.C 3 * CF * Cfull ^ 2 * Ccore))

lemma one_le_factoringApplyConstant {CF Cfull Ccore : NNReal} :
    1 ≤ factoringApplyConstant CF Cfull Ccore :=
  le_max_left _ _

/-- The core envelope is dominated by the comparison constant. This is the `max Ccore` branch of
`Kakeya.ThinCase.factoringApplyConstant`, and it is what makes the constant grow with the number
of dyadic mass classes of the family, as it must: see
`Kakeya.ThinCase.factoringApplyCore`. -/
lemma core_le_factoringApplyConstant {CF Cfull Ccore : NNReal} :
    Ccore ≤ factoringApplyConstant CF Cfull Ccore :=
  le_trans (le_max_left _ _) (le_max_right _ _)

/-- With `2 ≤ Ccore` the comparison constant is at least `2`; this is the branch of the constant
that rules out the degenerate refutation of the un-repaired statement, in which `Cfull → 0`
collapses the constant to `1` and clauses (iv) and (vi) become exact pointwise maximality and
exact mass preservation. -/
lemma two_le_factoringApplyConstant {CF Cfull Ccore : NNReal} (hCcore : 2 ≤ Ccore) :
    2 ≤ factoringApplyConstant CF Cfull Ccore :=
  le_trans hCcore core_le_factoringApplyConstant

/-! #### The bookkeeping clauses of `factoringApply`

Four of the thirteen conjuncts of `Kakeya.ThinCase.factoringApply` are pure bookkeeping about the
*shape* of the outer bodies: the two halves of the enlargement sandwich, the pointwise containment
(ii), and the neighbourhood containment (v). They hold for the canonical choice of outer shaded
body below, and they hold for *every* refinement `(segs', Y')` of the input family, so nothing
about them depends on which refinement the quantitative clauses eventually force. They are
isolated here so that a proof of `factoringApply` has only the quantitative clauses (i), (iii),
(iv) — Items 2, 3, 4 and 7 of GWZ Proposition 5.1 — left to supply, and so that this much survives
independently of how those are settled. -/

section BlockOuterBody

variable {σ ω : Type*} [DecidableEq ω]

/-- **The canonical enlarged outer shaded body of block `j`.**

Its carrier is the enlargement `N_{τ₂(Wb j)}(Wb j)` that the structural clause
`ShadedBody.outerFactoringFamily_carrier` of the corrected Proposition 5.1 gives the outer bodies
of the factoring, and its shading is the union `⋃_{p : blk p = j} Y'(p)` of the shadings of the
segments of block `j`, which is the smallest shading compatible with clause (ii) of
`Kakeya.ThinCase.factoringApply`. -/
noncomputable def blockOuterBody (segs' : Finset σ) (Y' : σ → ShadedBody E)
    (Wb : ω → ConvexSpaceBody E) (blk : σ → ω)
    (hle : ∀ p ∈ segs', (Y' p).toConvexSpaceBody ≤ Wb (blk p)) (j : ω) : ShadedBody E where
  toConvexSpaceBody := (Wb j).cthickening (Wb j).scale
  shade := iUnionShade (segs'.filter fun p => blk p = j) Y'
  measurableSet_shade :=
    Finset.measurableSet_biUnion _ fun p _ => (Y' p).measurableSet_shade
  shade_subset := by
    refine Set.iUnion₂_subset fun p hp => ?_
    obtain ⟨hpsegs, hpblk⟩ := Finset.mem_filter.mp hp
    have hcar : (Y' p).carrier ⊆ (Wb j).carrier := by
      have h := hle p hpsegs
      rw [hpblk] at h
      exact h
    exact ((Y' p).shade_subset.trans hcar).trans (Metric.self_subset_cthickening _)

variable {segs' : Finset σ} {Y' : σ → ShadedBody E} {Wb : ω → ConvexSpaceBody E} {blk : σ → ω}
  {hle : ∀ p ∈ segs', (Y' p).toConvexSpaceBody ≤ Wb (blk p)}

omit [BorelSpace E] in
@[simp] lemma blockOuterBody_toConvexSpaceBody (j : ω) :
    (blockOuterBody segs' Y' Wb blk hle j).toConvexSpaceBody =
      (Wb j).cthickening (Wb j).scale := rfl

omit [BorelSpace E] in
@[simp] lemma blockOuterBody_shade (j : ω) :
    (blockOuterBody segs' Y' Wb blk hle j).shade =
      iUnionShade (segs'.filter fun p => blk p = j) Y' := rfl

omit [BorelSpace E] in
/-- The lower half of the enlargement sandwich: the block body sits inside its enlargement. -/
lemma Wb_le_blockOuterBody (j : ω) :
    Wb j ≤ (blockOuterBody segs' Y' Wb blk hle j).toConvexSpaceBody :=
  (Wb j).self_le_cthickening _

omit [BorelSpace E] in
/-- The upper half of the enlargement sandwich, with equality: the carrier of the outer body *is*
`(Wb j).cthickening (Wb j).scale`. -/
lemma blockOuterBody_le_cthickening (j : ω) :
    (blockOuterBody segs' Y' Wb blk hle j).toConvexSpaceBody ≤
      (Wb j).cthickening (Wb j).scale := le_rfl

omit [BorelSpace E] in
/-- Clause (ii) of `Kakeya.ThinCase.factoringApply`: every shaded point of a segment is a shaded
point of the outer body of its block. -/
lemma mem_blockOuterBody_shade {p : σ} (hp : p ∈ segs') {x : E} (hx : x ∈ (Y' p).shade) :
    x ∈ (blockOuterBody segs' Y' Wb blk hle (blk p)).shade :=
  Set.mem_iUnion₂.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩, hx⟩

omit [BorelSpace E] in
/-- Clause (v) of `Kakeya.ThinCase.factoringApply`: the outer shading lies in the neighbourhood of
the blockwise shaded union at twice the per-body radius `τ₂(Wb j)`. For this choice of outer
shading the containment is the trivial one, a set inside its own closed neighbourhood. -/
lemma blockOuterBody_shade_subset_cthickening (j : ω) :
    (blockOuterBody segs' Y' Wb blk hle j).shade ⊆
      Metric.cthickening (2 * Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1))
        (iUnionShade (segs'.filter fun p => blk p = j) Y') :=
  Metric.self_subset_cthickening _

omit [BorelSpace E] in
/-- The outer shaded union of the canonical family is the inner shaded union: no shading is
created and none is lost by passing to the blocks. This is what clauses (i), (iii) and (iv) of
`Kakeya.ThinCase.factoringApply` are quantitative statements about. -/
lemma blockOuterBody_iUnionShade {bodies' : Finset ω} (hblk : ∀ p ∈ segs', blk p ∈ bodies') :
    iUnionShade bodies' (blockOuterBody segs' Y' Wb blk hle) = iUnionShade segs' Y' := by
  ext x
  simp only [iUnionShade, blockOuterBody_shade, Set.mem_iUnion, exists_prop,
    Finset.mem_filter]
  constructor
  · rintro ⟨j, -, p, ⟨hp, -⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨blk p, hblk p hp, p, ⟨hp, rfl⟩, hx⟩

end BlockOuterBody

/-- Clause (vi) of `Kakeya.ThinCase.factoringApply` in the trivial case `segs' = segs`,
`Y' = Y`: a constant `≥ 1` always admits the identity refinement. -/
lemma inv_mul_sum_shade_le_self {σ : Type*} {C : NNReal} (hC : 1 ≤ C) (s : Finset σ)
    (V : σ → ShadedBody E) :
    (C : ENNReal)⁻¹ * ∑ p ∈ s, volume (V p).shade ≤ ∑ p ∈ s, volume (V p).shade := by
  have h1 : (C : ENNReal)⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]
    exact_mod_cast hC
  calc (C : ENNReal)⁻¹ * ∑ p ∈ s, volume (V p).shade
      ≤ 1 * ∑ p ∈ s, volume (V p).shade := by gcongr
    _ = ∑ p ∈ s, volume (V p).shade := one_mul _

/-- Clause (vi) of `Kakeya.ThinCase.factoringApply` from a `C⁻¹`-refinement: the two formulations
of "the refinement keeps at least a `C⁻¹` fraction of the mass" agree. -/
lemma inv_mul_sum_shade_le_of_isCRefinement {σ : Type*} {C : NNReal} (hC : C ≠ 0)
    {segs segs' : Finset σ} {Y Y' : σ → ShadedBody E}
    (h : ShadedBody.IsCRefinement segs' Y' segs Y C⁻¹) :
    (C : ENNReal)⁻¹ * ∑ p ∈ segs, volume (Y p).shade ≤
      ∑ p ∈ segs', volume (Y' p).shade := by
  have := h.2
  rwa [ENNReal.coe_inv hC] at this

/-- **Applying the factoring proposition in a single ball** (blueprint
`lem:ml2thinFactoringApply`).

The two hypotheses of blueprint Proposition `factoringAndMultPropCombined` hold for the
factoring `𝕋_B = ⨆_{W ∈ 𝕎_B} 𝕋_{B,W}` of (C4): each block is `CF`-Frostman in its body
with `CF ∼ 1` (a maximal density factoring with bias still has Frostman constant `∼ 1`),
and by (C3) the members of `𝕋_B` have approximately equal dimensions. Reading off the
conclusions gives items (i)–(vi) below, at the common shortest dimension `w₁` of the
bodies.

Note that the proposition returns a *subfamily* `segs' ⊆ 𝕋_B`, and that item (vi)
produces the refinement only in the *summed* sense; both gaps are closed later, by
`extendByEmpty` and by `massMarkovUpgrade` respectively.

The bodies are *not* returned with carrier `Wb j`. The outer shaded bodies of the corrected
Proposition 5.1 carry the enlargement `N_{r_j}(Wb j)`, `r_j = τ₂(Wb j) = (Wb j).scale`, so the
output is described by the sandwich `Wb j ≤ (W j).toConvexSpaceBody ≤ (Wb j).cthickening
(Wb j).scale` and item (v) is a one-sided neighbourhood containment at radius `2 τ₂(Wb j)`.

**The `hloc`-free form of this statement is refuted.**
`Kakeya.ThinCase.Refute.factoringApply_refuted`
(`Kakeya/DimensionThree/MainLemma2/ThinFactoringRefute.lean`) derives `False` from
`Kakeya.ThinCase.Refute.FactoringApplyStatement`, which is this statement with `hloc` deleted
and everything else — the discretization hypotheses `hscale`, `hCcoreRef₀`, `hCcoreMult₀`
included — kept; `Kakeya.ThinCase.Refute.statement_of_universal_loc` is the tripwire, deriving
that `Prop` from this declaration by granting `hloc` universally and passing every other
argument verbatim. Items (iv) and (vi) are jointly unachievable with a
constant whose only inputs are `CF`, `Cfull`, `segs.card`, `bodies.card` and `δ`: one segment in
one long body, shaded on `M` pairwise `2 w₁`-separated blobs of harmonic mass, satisfies every
hypothesis below while forcing `∑_{k<M} (k+1)⁻¹ ≤ (factoringApplyConstant CF Cfull Ccore) ^ 2`.
The missing hypothesis is `ConvexSpaceBody.IsDiscretizedAtScale.subset_unitBall`, the first
field of `ShadedBody.FactorFamily.InnerIsDiscretizedAtScale`, which every item of the
Proposition 5.1 API assumes and which caps the number of `w₁`-balls needed to cover the shaded
union — the quantity the pigeonhole behind item (iv) actually pays for. See
`Kakeya.ThinCase.Localise.exists_localised_refinement_of_subset_ball` for the positive half.

The Proposition 5.1 API this should compose is, in the namespace `ShadedBody` of
`Kakeya/Factoring/Multiplicity.lean` (the one this file transitively imports): the carrier
sandwich is `ShadedBody.outerFactoringFamily_carrier`, which identifies the outer carrier with
`(Wb j).cthickening (Wb j).scale` outright, so both halves hold, the upper one with equality;
item (vi) is `ShadedBody.outerFactoringFamily_refinement`; item (i) is
`ShadedBody.outerFactoringFamily_lambda`; item (iii)(a) is
`ShadedBody.outerFactoringFamily_outerConstMultFat` (through
`ShadedBody.outerFactoringOuterRefined`); item (iii)(b) is
`ShadedBody.outerFactoringFamily_innerConstMult`; item (ii) is
`ShadedBody.outerFactoringFamily_shadingContainment`; and item (iv) is
`ShadedBody.outerFactoringFamily_avgMultOnBalls`, whose right-hand ball has radius `7 * w₁`,
not `w₁` — its own docstring records that the equal-radius form is false for the constructed
family, which is the drift this statement inherited.

Three names cited by earlier versions of this docstring —
`ShadedBody.outerFactoringFamily_outerBodyGe`,
`ShadedBody.outerFactoringFamily_volumeControlled` and
`ShadedBody.outerFactoringFamily_hasThicknesses` — **do not exist anywhere in the tree**, and a
fourth, `ShadedBody.outerFactoringFamily_outerShadeSubset`, exists only in the un-imported
`ShadedBody.AtScale` namespace of `Kakeya/Factoring/MultiplicityAtScale.lean`. Item (v) has no
deliverer in the imported namespace.

The output constant is the *explicit* `factoringApplyConstant CF Cfull Ccore`, not an
existentially quantified one: an existential constant would be allowed to depend on the ball
`B`, and the ball-independence of `perBallConstant` — on which the amalgamation of the per-ball
refinements rests — could then not be derived.

`Ccore` is a *parameter* subject to the four envelope binders, not a formula in `segs.card`,
`bodies.card` and `δ`. So the envelope formula
`Kakeya.ThinCase.factoringApplyCore` may change without touching this statement or any
downstream one, and what the amalgamation actually needs — ball-*uniformity*, one constant for
all balls, and not cardinality-independence — is achieved by quantification: see
`Kakeya.VeryNotSticky.exists_thinConfig`, which instantiates `Ccore` with the supremum over the
finitely many balls of the canonical envelope at that ball. Cardinality-independence is not
available and is not needed: `Kakeya.VeryNotSticky.ThinConfig.tb` takes one `C` for all balls,
`Kakeya.ThinCase.ThinBall.mono` only weakens upward, and
`Kakeya.VeryNotSticky.ThinConfig.C` is an existential field, so no downstream statement pins
the shape of the constant.

**Proof route.** The plain Proposition 5.1 API named above is *not* what the proof composes:
the thin case runs the **weighted** pipeline through `Kakeya.ThinCase.exists_factoringApplyData`
(`Kakeya.DimensionThree.MainLemma2.ThinAssembly`), which delivers all thirteen conjuncts at
explicit constants — item (i) by GWZ's Item 2 accounting over a fibre-density band, item (iv) by
the finer ball net, item (v) from the cell shading's defining equation. What remains here is the
envelope: (iii)(a)/(b) at `2 ≤ Ccore`, and (i), (iv), (vi) at the four branches of
`Kakeya.ThinCase.thinEnvelopeTerm`, which `hCcoreNet` dominates; the six binders `hCcoreRef`,
`hCcoreMult`, `hCcoreDyad`, `hCcoreFrost`, `hCcoreRef₀`, `hCcoreMult₀` are not consumed by this
proof (the pipeline losses they price are folded into the uniform retained fraction inside
`thinEnvelopeTerm`). -/
theorem factoringApply (hdim : Module.finrank ℝ E = 3)
    {σ ω : Type*} [DecidableEq ω] (segs : Finset σ) (Y : σ → ShadedBody E)
    (bodies : Finset ω) (Wb : ω → ConvexSpaceBody E) (blk : σ → ω)
    {δ w₁ : NNReal} {η : ℝ} {CF Cfull Ccore : NNReal}
    -- the scale conditions under which the corrected Proposition 5.1 is stated: every one of
    -- its entry points asks for `0 < δ` and `w₁ ∈ Set.Icc δ 1`
    (hδ : 0 < δ) (hδw₁ : δ ≤ w₁) (hw₁one : w₁ ≤ 1)
    -- **`η` is a loss exponent, so it is non-negative.** This is what conjunct (i) needs and the
    -- only thing it needs beyond the weighted pipeline's own Córdoba estimate: that estimate
    -- delivers `δ ^ (2 * η)` (`Kakeya.ThinCase.thinFullness_sum`), conjunct (i) asks for the
    -- weaker `δ ^ (3 * η)`, and passing between them is `δ ^ η ≤ 1`, i.e. `0 ≤ η` given
    -- `δ ≤ w₁ ≤ 1`. It is *not* derivable from the other binders: `hdens` and `hfullness` bound
    -- `δ ^ η` from above only, and every `η < 0` instance of them is satisfied by enlarging
    -- `Cfull`. Nor can it be traded for a larger constant: the binder-free route prices conjunct
    -- (i) at `Cfull ^ 3 * CF / K`, while `Kakeya.ThinCase.factoringApplyConstant` supplies only
    -- `2 * volume_comparison.C 3 * CF * Cfull ^ 2 * Ccore`, and no `hCcore*` binder bounds
    -- `Cfull` in terms of `Ccore`.
    -- It is free at every call site: `Kakeya.VeryNotSticky.VeryNotSticky.hη` is `0 < η`, and both
    -- refutation configurations instantiate `η` at a natural number.
    (hη : (0:ℝ) ≤ η)
    -- the Frostman constant of (C4) is a genuine loss; this is a field of `IsBallFactoring`,
    -- so it is free at the call site
    (hCF : 1 ≤ CF)
    -- the core envelope: `Ccore` dominates every dyadic-pigeonhole loss of Proposition 5.1 at
    -- this family. `Kakeya.ThinCase.factoringApplyCore` satisfies all four bounds
    -- unconditionally (`Kakeya.ThinCase.factoringApplyCore_spec`), and is `⪅ 1` in `δ` for
    -- polynomially bounded cardinalities
    -- (`Kakeya.ThinCase.factoringApplyCore_leApprox_one`), so the bundle is inhabited and the
    -- repair does not blow the `δ ^ (-η)` budget of
    -- `Kakeya.VeryNotSticky.CaseScale.transverse_ballFill`.
    (hCcore2 : 2 ≤ Ccore)
    (hCcoreRef : (ShadedBody.outerFactoringFamily_refinement.c 3 segs.card δ)⁻¹ ≤ Ccore)
    (hCcoreMult : ShadedBody.outerFactoringFamily_outerConstMultFat.c 3 bodies.card δ ≤ Ccore)
    (hCcoreDyad : ((Nat.log 2 bodies.card + 1 : ℕ) : NNReal) ≤ Ccore)
    -- the fifth envelope bound, and the only one that mentions `CF`. Conclusion (i) comes from
    -- GWZ Item 2 (`ShadedBody.outerFactoringFamily_lambda`), whose loss
    -- `ShadedBody.lambdaForInducedShading.C N` is linear in the *eccentricity exponent* `N`
    -- (`volume (outerBody j) ≤ 2^N * volume (innerBody i)` for every `i` in the fibre).
    -- `hdims` and `hFr` bound it by `N ≤ log₂ CF + log₂ segs.card + O(1)`
    -- (`Kakeya.ThinCase.Produce.volume_carrier_le_of_isFrostmanIn` is the `CF` half), and the
    -- `hCcoreRef` binder already forces `Ccore ≳ (log₂ segs.card + 1) ^ 4`, which pays for the
    -- `segs.card` part and the absolute part; the `log₂ CF` part is paid for here and nowhere
    -- else, the spare factor `CF` of `factoringApplyConstant` having been consumed by Item 2's
    -- own constant. Like the other four this is a *lower* bound on a parameter, so it can only
    -- shrink the set of admissible `Ccore`; `Kakeya.VeryNotSticky.exists_thinConfig` discharges
    -- it by enlarging its `Ccore` by this one term.
    (hCcoreFrost : ((Nat.log 2 ⌈CF⌉₊ + 1 : ℕ) : NNReal) ≤ Ccore)
    (hblk : ∀ p ∈ segs, blk p ∈ bodies)
    (hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p))
    (hdims : ∀ p ∈ segs, ∀ q ∈ segs,
      Metric.thickness ℝ (Y p).carrier ≤ 2 • Metric.thickness ℝ (Y q).carrier)
    (hFr : ∀ j ∈ bodies, ConvexSpaceBody.IsFrostmanIn (segs.filter fun p => blk p = j)
      (fun p => (Y p).toConvexSpaceBody) (Wb j) CF)
    (hw₁ : ∀ j ∈ bodies,
      Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1) ≤ 2 * w₁ ∧
        (w₁ : ℝ) ≤ 2 * Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1))
    -- **The localisation hypothesis, restored.** Every body of the family lies in one ball of
    -- radius `1`. This is `ConvexSpaceBody.IsDiscretizedAtScale.subset_unitBall`, the first
    -- field of `ShadedBody.FactorFamily.InnerIsDiscretizedAtScale`, which every item of the
    -- corrected Proposition 5.1 assumes and which an earlier revision of this statement
    -- dropped; the centre is existentially quantified because nothing here distinguishes the
    -- origin. Without it the statement is **false**:
    -- `Kakeya.ThinCase.Refute.factoringApply_refuted` refutes the `hloc`-free form, and the
    -- mechanism is exactly that `hloc` is what bounds the number of `w₁`-balls needed to cover
    -- the shaded union — the quantity the Step 5 dyadic mass pigeonhole
    -- (`Kakeya.factoringStep5SelfPigeonholeConstant`, bounded through
    -- `Kakeya.card_le_step5PackingRatio` by `(4/δ)^n`) pays for, and the one quantity
    -- `factoringApplyConstant CF Cfull Ccore` cannot see.
    -- It is supplied at the sole call site: `Kakeya.ThinCase.perBall` carries it as a binder,
    -- which `Kakeya.ThinCase.thinSetupExists` passes on and
    -- `Kakeya.VeryNotSticky.exists_thinConfig` discharges from
    -- `Kakeya.VeryNotSticky.BallData.bodies_subset_ball` together with `r₁ = δ^exscal ≤ 1`.
    (hloc : ∃ z : E, ∀ j ∈ bodies, (Wb j).carrier ⊆ Metric.closedBall z 1)
    -- **The discretization scale of the segments**, the second field of
    -- `ShadedBody.FactorFamily.InnerIsDiscretizedAtScale`, which every item of the corrected
    -- Proposition 5.1 assumes and which — like `hloc` — this statement had dropped. It is *not*
    -- derivable from the other hypotheses: `Kakeya.ThinCase.le_scale_not_derivable`
    -- exhibits a family satisfying all of them whose single segment is a ball of radius `δ / 2`,
    -- because `hle` bounds a segment's thickness only from *above* (by its body's) and `hdims`
    -- only compares segments with one another. The scale is a *parameter* `δ₀` rather than `δ`
    -- itself because the call site cannot supply `δ`: `Kakeya.ThinCase.IsBallFactoring.thick`
    -- gives `HasThicknesses (Y p).carrier C₀ ![r₁, δ, δ]`, hence `C₀⁻¹ δ ≤ τ_k` at every rank,
    -- and the comparison constant `C₀` of (C3) cannot be removed. `Kakeya.ThinCase.perBall`
    -- discharges `hscale` at `δ₀ = δ / C₀`.
    {δ₀ : NNReal} (hδ₀ : 0 < δ₀) (hδ₀w₁ : δ₀ ≤ w₁)
    (hscale : ∀ p ∈ segs, (δ₀ : ENNReal) ≤ Metric.ethickness.scale ℝ (Y p).carrier)
    -- the two scale-dependent envelope bounds, read at the scale the pipeline is actually run
    -- at. They are what stops `δ₀` from being a free parameter that drives the pipeline losses
    -- up without moving the constant — the `ν`-uniformity defect that made
    -- `Kakeya.VeryNotSticky.coarseKatzTaoBound` false. Since `δ₀ ≤ δ` at the call site and
    -- both constants are
    -- antitone in the scale, they *imply* `hCcoreRef` and `hCcoreMult`, which are kept because
    -- nothing here forces `δ₀ ≤ δ`. `Kakeya.VeryNotSticky.exists_thinConfig` discharges them by
    -- enlarging its `Ccore` with the envelope read at `cfg.δ / C₀`.
    (hCcoreRef₀ : (ShadedBody.outerFactoringFamily_refinement.c 3 segs.card δ₀)⁻¹ ≤ Ccore)
    (hCcoreMult₀ : ShadedBody.outerFactoringFamily_outerConstMultFat.c 3 bodies.card δ₀ ≤ Ccore)
    -- **the eighth envelope bound**, and the only one that mentions the *second* pigeonhole.
    -- Conjunct (iv) is unreachable from the Proposition 5.1 API alone — Item 7
    -- (`ShadedBody.outerFactoringFamily_avgMultOnBalls`) compares `ball x w₁` with
    -- `closedBall y (7 w₁)` and its own docstring records that the equal-radius form is false
    -- for the constructed family — and the missing step is a second, finer ball-net pigeonhole
    -- at scale `w₁ / 8` (`Kakeya.ThinCase.exists_comparableNet`,
    -- `Kakeya.ThinCase.centredMult_of_separatedNet`). Its loss is
    -- `Kakeya.ThinCase.ballNetLoss`, one further logarithmic factor of the same shape as the
    -- pipeline's own Step-5 loss and bounded by none of the seven binders above. The localisation
    -- radius is `2` because `hloc` puts every body in `closedBall z 1`.
    -- Like the other seven this is a *lower* bound on a parameter, so it only shrinks the set of
    -- admissible `Ccore`; `Kakeya.VeryNotSticky.exists_thinConfig` discharges it by enlarging its
    -- `Ccore` with this one term.
    (hCcoreNet : thinEnvelopeTerm 3 segs.card bodies.card CF w₁ ≤ Ccore)
    -- the *pointwise* form of the fullness hypothesis. GWZ Item 2
    -- (`ShadedBody.outerFactoringFamily_lambda`) needs a per-body density lower bound on the
    -- shading, which `hfullness` — an aggregate statement about the ratio of two sums — does
    -- not give: the recurring defect of this development is exactly an aggregate bound consumed
    -- as a pointwise one. It is *not* an extra assumption on the caller: it is verbatim
    -- `Kakeya.ThinCase.IsBallFactoring.dens`, clause (C5) of Configuration `hyp:ml2setup`, read
    -- at `Cfull = c₁⁻¹`. It implies `hfullness` when the total carrier volume is positive and
    -- finite, but `hfullness` is kept because that implication needs those side conditions.
    (hdens : ∀ p ∈ segs,
      (δ : ENNReal) ^ η * volume (Y p).carrier ≤ (Cfull : ENNReal) * volume (Y p).shade)
    (hfullness : (δ : ENNReal) ^ η ≤ (Cfull : ENNReal) * (fullness segs Y : ENNReal)) :
    ∃ (segs' : Finset σ) (bodies' : Finset ω)
      (Y' : σ → ShadedBody E) (W : ω → ShadedBody E),
      segs' ⊆ segs ∧ bodies' ⊆ bodies ∧
      (∀ p ∈ segs, (Y' p).toConvexSpaceBody = (Y p).toConvexSpaceBody) ∧
      (∀ p ∈ segs', (Y' p).shade ⊆ (Y p).shade) ∧
      -- the enlargement sandwich for the outer bodies
      (∀ j ∈ bodies', Wb j ≤ (W j).toConvexSpaceBody) ∧
      (∀ j ∈ bodies', (W j).toConvexSpaceBody ≤ (Wb j).cthickening (Wb j).scale) ∧
      -- (i) the density bound `λ(𝕎'_B, Y_{𝕎'_B}) ⪆ δ^{3η}`.  The exponent is `3η`, not `2η`,
      -- because the Frostman/Córdoba transport of the input fullness charges a `δ^{-η}` for
      -- converting a *shade*-mass retention into the *carrier*-mass retention that
      -- `ConvexSpaceBody.IsFrostmanIn.of_le_of_subset` needs; see
      -- `Kakeya.ThinCase.ThinBall.fullness_bodies`, the field this conjunct feeds.
      ((δ : ENNReal) ^ (3 * η) ≤
        (factoringApplyConstant CF Cfull Ccore : ENNReal) * (fullness bodies' W : ENNReal)) ∧
      -- (ii) the pointwise containment
      (∀ p ∈ segs', ∀ x ∈ (Y' p).shade, blk p ∈ bodies' ∧ x ∈ (W (blk p)).shade) ∧
      -- (iii) constant multiplicity of the bodies, and of each block with a common value
      (HasCConstantMultiplicity bodies' W (factoringApplyConstant CF Cfull Ccore)) ∧
      (∃ μinner : NNReal, ∀ j ∈ bodies',
        ∀ x ∈ iUnionShade (segs'.filter fun p => blk p = j) Y',
          (pointwiseMultiplicity (segs'.filter fun p => blk p = j) Y' x : ENNReal) ≤
              (factoringApplyConstant CF Cfull Ccore : ENNReal) * μinner ∧
            (μinner : ENNReal) ≤ (factoringApplyConstant CF Cfull Ccore : ENNReal) *
              (pointwiseMultiplicity (segs'.filter fun p => blk p = j) Y' x : ENNReal)) ∧
      -- (iv) the centred multiplicity statement at radius `w₁`
      (∀ x ∈ iUnionShade bodies' W, ∀ y ∈ iUnionShade bodies' W,
        volume (iUnionShade segs' Y' ∩ ball x (w₁ : ℝ)) ≤
          (factoringApplyConstant CF Cfull Ccore : ENNReal) *
            volume (iUnionShade segs' Y' ∩ ball y (w₁ : ℝ))) ∧
      -- (v) the shading of the bodies lies in the neighbourhood of the shaded blocks at twice
      -- the *per-body* radius `τ₂(W) = thickness ℝ (Wb j).carrier (finrank ℝ E - 1)`, which is
      -- the radius of `ShadedBody.outerFactoringFamily_outerShadeSubset`
      (∀ j ∈ bodies', (W j).shade ⊆
        cthickening (2 * Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1))
          (iUnionShade (segs'.filter fun p => blk p = j) Y')) ∧
      -- (vi) the refinement, in the summed sense, with a ball-independent constant
      ((factoringApplyConstant CF Cfull Ccore : ENNReal)⁻¹ * ∑ p ∈ segs, volume (Y p).shade ≤
        ∑ p ∈ segs', volume (Y' p).shade) := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  obtain ⟨z, hzz⟩ := hloc
  have hCF0 : (0 : NNReal) < CF := lt_of_lt_of_le zero_lt_one hCF
  have hw₁pos : (0 : NNReal) < w₁ := lt_of_lt_of_le hδ hδw₁
  -- the carriers are non-degenerate: `hscale` puts every segment at scale `≥ δ₀ > 0`
  have hVpos : ∀ p ∈ segs, volume (Y p).carrier ≠ 0 := fun p hp =>
    ((Y p).convex.volume_pos_of_scale_ne_zero
      (ne_bot_of_le_ne_bot (by simpa using hδ₀.ne') (hscale p hp))).ne'
  have hdisc : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀ :=
    thinFactorFamily_innerIsDiscretizedAtScale hzz hscale
  -- the assembled data, at the eccentricity datum `Kakeya.ThinCase.thinVolumeRatio`
  obtain ⟨segs', bodies', Y', W, hsub, hbsub, hcar, hshade, hWbLe, hWle, hi, hcontain, hWshade,
      hcmult, hinner, hcent, hvi⟩ :=
    exists_factoringApplyData hdim segs Y bodies Wb blk hδ hδw₁ hw₁one hη hCF0 hδ₀ hδ₀w₁ hblk hle
      hdims hFr z hzz hdisc (thinVolumeRatio segs Y bodies Wb blk z hblk hle hdims hFr hVpos) hw₁
      hdens hfullness
  rw [thinVolumeRatio_exponent] at hi hvi
  -- the envelope, read at the dimension `Module.finrank ℝ E = 3`
  have hCcoreNet' :
      thinEnvelopeTerm (Module.finrank ℝ E) segs.card bodies.card CF w₁ ≤ Ccore := by
    rw [hdim]; exact hCcoreNet
  have hcore : Ccore ≤ factoringApplyConstant CF Cfull Ccore := core_le_factoringApplyConstant
  have hCfact2 : (2 : NNReal) ≤ factoringApplyConstant CF Cfull Ccore :=
    two_le_factoringApplyConstant hCcore2
  have hCfact2' : (2 : ENNReal) ≤ (factoringApplyConstant CF Cfull Ccore : ENNReal) := by
    exact_mod_cast hCfact2
  refine ⟨segs', bodies', Y', W, hsub, hbsub, hcar, hshade, hWbLe, hWle, ?_, hcontain, ?_, ?_, ?_,
    hWshade, ?_⟩
  · -- (i): the cell-fullness constant against the third branch of `factoringApplyConstant`
    refine le_trans hi (mul_le_mul_left (ENNReal.coe_le_coe.mpr ?_) _)
    calc thinCellFullnessConstant (Module.finrank ℝ E) segs.card bodies.card CF Cfull w₁
          (thinEccentricityExponent (Module.finrank ℝ E) segs.card CF)
        ≤ 2 * volume_comparison.C (Module.finrank ℝ E) * CF * Cfull ^ 2 *
            thinEnvelopeTerm (Module.finrank ℝ E) segs.card bodies.card CF w₁ :=
          thinCellFullnessConstant_le_mul_thinEnvelopeTerm _ _ _ _ _ _
      _ ≤ 2 * volume_comparison.C (Module.finrank ℝ E) * CF * Cfull ^ 2 * Ccore :=
          mul_le_mul_right hCcoreNet' _
      _ = 2 * volume_comparison.C 3 * CF * Cfull ^ 2 * Ccore := by rw [hdim]
      _ ≤ factoringApplyConstant CF Cfull Ccore := le_trans (le_max_right _ _) (le_max_right _ _)
  · -- (iii)(a): constant multiplicity `2` of the bodies, weakened to the output constant
    exact HasCConstantMultiplicity.mono bodies' W hCfact2 hcmult
  · -- (iii)(b): the common inner value, with `2` weakened to the output constant
    obtain ⟨μinner, hμ⟩ := hinner
    refine ⟨μinner, fun j hj x hx => ?_⟩
    obtain ⟨h1, h2⟩ := hμ j hj x hx
    have h1' : (pointwiseMultiplicity (segs'.filter fun p => blk p = j) Y' x : ENNReal) ≤
        2 * (μinner : ENNReal) := by exact_mod_cast h1
    have h2' : (μinner : ENNReal) ≤
        2 * (pointwiseMultiplicity (segs'.filter fun p => blk p = j) Y' x : ENNReal) := by
      exact_mod_cast h2
    exact ⟨h1'.trans (mul_le_mul_left hCfact2' _), h2'.trans (mul_le_mul_left hCfact2' _)⟩
  · -- (iv): the equal-radius constant is the first branch of the envelope term
    intro x hx y hy
    refine (hcent x hx y hy).trans (mul_le_mul_left (ENNReal.coe_le_coe.mpr ?_) _)
    exact le_trans (equalRadiusMultConstant_le_thinEnvelopeTerm _ _ _ _ _)
      (le_trans hCcoreNet' hcore)
  · -- (vi): the global retention `θ = c / (L · B)` against the third branch of the envelope term
    have hδη : (0 : ENNReal) < (δ : ENNReal) ^ η :=
      ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ) ENNReal.coe_ne_top
    have hmass : ∑ p ∈ segs, volume (Y p).shade ≠ 0 := by
      intro h0
      have hf : (fullness segs Y : ENNReal) = 0 := by
        rw [fullness_def, h0, ENNReal.zero_div]
      rw [hf, mul_zero] at hfullness
      exact hδη.ne' (le_antisymm hfullness zero_le)
    have hcpos := thinUniformRefinementConstant_pos segs Y bodies Wb blk z hblk hle hδ₀ hw₁pos
      hdisc (thinVolumeRatio segs Y bodies Wb blk z hblk hle hdims hFr hVpos) hmass
    rw [thinVolumeRatio_exponent] at hcpos
    have hBtop : fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    refine inv_mul_le_of_mul_le_mul hcpos.ne' (ENNReal.mul_ne_top ENNReal.coe_ne_top hBtop)
      hvi ?_
    rw [← ENNReal.coe_toNNReal hBtop, ← ENNReal.coe_mul, ← ENNReal.coe_inv hcpos.ne',
      ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    refine le_trans (le_of_eq ?_) (le_trans (inv_thinGlobalRetention_le_thinEnvelopeTerm _ _ _ _ _)
      (le_trans hCcoreNet' hcore))
    simp only [thinGlobalRetention, mul_inv, inv_inv]

end Produce

/-! ### Bookkeeping around the factoring output

The two lemmas of this section are pure bookkeeping and use neither the inner product, nor
finite-dimensionality, nor the Borel structure of `E`; they are stated with the weakest
typeclass assumptions under which they make sense, so that they can be reused verbatim in
other settings. -/

section ExtendByEmpty

variable {E : Type*} [TopologicalSpace E] [Convexity.ConvexSpace ℝ E] [MeasureSpace E]

/-- **Extending the factoring shading by `∅`** (blueprint `lem:ml2thinExtendByEmpty`).

Extending the shading produced on the subfamily `segs'` to all of `segs` by the empty set
changes none of the three quantities the conclusions of `factoringApply` speak about: the
shaded unions (globally and blockwise), the pointwise multiplicities, and the total mass.
Consequently items (i)–(vi) hold verbatim with `segs'` replaced by `segs`. -/
theorem extendByEmpty {σ ω : Type*} [DecidableEq ω] (segs segs' : Finset σ) (hsub : segs' ⊆ segs)
    (blk : σ → ω) (Y' Y'' : σ → ShadedBody E)
    (hext : ∀ p ∈ segs', (Y'' p).shade = (Y' p).shade)
    (hempty : ∀ p ∈ segs, p ∉ segs' → (Y'' p).shade = ∅) :
    iUnionShade segs Y'' = iUnionShade segs' Y' ∧
      (∀ j : ω, iUnionShade (segs.filter fun p => blk p = j) Y'' =
        iUnionShade (segs'.filter fun p => blk p = j) Y') ∧
      (∀ j : ω, ∀ x : E, pointwiseMultiplicity (segs.filter fun p => blk p = j) Y'' x =
        pointwiseMultiplicity (segs'.filter fun p => blk p = j) Y' x) ∧
      ∑ p ∈ segs, volume (Y'' p).shade = ∑ p ∈ segs', volume (Y' p).shade := by
  -- The unions (globally and blockwise) miss the added empty-shaded segments, so the two
  -- families of shaded unions agree.  This is used for the first two conjuncts.
  have hUnionAux : ∀ {A A' : Finset σ}, A' ⊆ A →
      (∀ p ∈ A', (Y'' p).shade = (Y' p).shade) →
      (∀ p ∈ A, p ∉ A' → (Y'' p).shade = ∅) →
      iUnionShade A Y'' = iUnionShade A' Y' := by
    intro A A' hAA' he' he0
    ext x
    simp only [iUnionShade, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨p, hpA, hxshade⟩
      by_cases hp' : p ∈ A'
      · exact ⟨p, hp', by simpa [he' p hp'] using hxshade⟩
      · have h0 : (Y'' p).shade = ∅ := he0 p hpA hp'
        simp [h0] at hxshade
    · rintro ⟨p, hpA', hxshade⟩
      exact ⟨p, hAA' hpA', by simpa [he' p hpA'] using hxshade⟩
  constructor
  · exact hUnionAux hsub hext hempty
  constructor
  · intro j
    apply hUnionAux
    · intro p hp
      exact Finset.mem_filter.mpr
        ⟨hsub (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
    · intro p hp
      exact hext p (Finset.mem_filter.mp hp).1
    · intro p hp hnot
      exact hempty p (Finset.mem_filter.mp hp).1 (by
        intro hpseg'
        exact hnot (Finset.mem_filter.mpr ⟨hpseg', (Finset.mem_filter.mp hp).2⟩))
  constructor
  · intro j x
    simp only [pointwiseMultiplicity]
    apply congrArg Finset.card
    apply Finset.ext
    intro p
    simp only [Finset.mem_filter]
    constructor
    · intro hx
      have hpseg : p ∈ segs := hx.1.1
      have hpj : blk p = j := hx.1.2
      have hxshade : x ∈ (Y'' p).shade := hx.2
      by_cases hp' : p ∈ segs'
      · exact ⟨⟨hp', hpj⟩, by simpa [hext p hp'] using hxshade⟩
      · have h0 : (Y'' p).shade = ∅ := hempty p hpseg hp'
        simp [h0] at hxshade
    · intro hx
      have hpseg' : p ∈ segs' := hx.1.1
      have hpj : blk p = j := hx.1.2
      have hxshade : x ∈ (Y' p).shade := hx.2
      exact ⟨⟨hsub hpseg', hpj⟩, by simpa [hext p hpseg'] using hxshade⟩
  · calc
      ∑ p ∈ segs, volume (Y'' p).shade
          = ∑ p ∈ segs', volume (Y'' p).shade := by
              exact (Finset.sum_subset hsub (by intro p hp hp'; simp [hempty p hp hp'])).symm
      _ = ∑ p ∈ segs', volume (Y' p).shade := by
              apply Finset.sum_congr rfl
              intro p hp
              exact congrArg volume (hext p hp)

end ExtendByEmpty

section TubesInBodies

variable {E : Type*} [PseudoMetricSpace E] [Convexity.ConvexSpace ℝ E] [MeasurableSpace E]

/-- **The tube segments lie in the shaded bodies** (blueprint `lem:ml2thinTubesInBodies`).

By (C4) each segment is contained in the body of its block, and by (T6) the shading of
that body is the intersection of the body with the `w₁`-neighbourhood of the shaded
block, at the *per-body* radius `w j` of `Kakeya.ThinCase.ThinBall.w` — in the application
`w j = Metric.thickness ℝ (Wb j).carrier (finrank ℝ E - 1)`, the radius of
`ShadedBody.inducedShading`. Nothing at all is assumed about `w`, so the radius is left as an
unconstrained function; the containment is read off from `hW` alone.

The lemma is applied with `bodies := 𝕎'_B`, a *proper* subfamily of the family `𝕎_B` of
(C4), so a segment need not have its block in `bodies`; what the factoring proposition
guarantees is that such a segment is unshaded. This is the disjunction in `hblk`. -/
theorem tubesInBodies {σ ω : Type*} [DecidableEq ω] (segs : Finset σ) (bodies : Finset ω)
    (blk : σ → ω)
    (Y' : σ → ShadedBody E) (Wb : ω → ConvexSpaceBody E) (W : ω → ShadedBody E) (w : ω → ℝ)
    (hblk : ∀ p ∈ segs, blk p ∈ bodies ∨ (Y' p).shade = ∅)
    (hle : ∀ p ∈ segs, (Y' p).carrier ⊆ (Wb (blk p)).carrier)
    (hW : ∀ j ∈ bodies, (W j).shade =
      (Wb j).carrier ∩ cthickening (w j) (iUnionShade (segs.filter fun p => blk p = j) Y')) :
    (∀ p ∈ segs, (Y' p).shade ⊆ (W (blk p)).shade) ∧
      iUnionShade segs Y' ⊆ iUnionShade bodies W := by
  have hshade : ∀ p ∈ segs, (Y' p).shade ⊆ (W (blk p)).shade := by
    intro p hp
    by_cases eq : (Y' p).shade = ∅
    · rw [eq]
      exact Set.empty_subset _
    · have hj : blk p ∈ bodies := (hblk p hp).resolve_right eq
      rw [hW (blk p) hj]
      refine Set.subset_inter ?hcarrier ?hcthick
      · exact (Y' p).shade_subset.trans (hle p hp)
      · have hmem : (Y' p).shade ⊆
            iUnionShade (segs.filter fun q => blk q = blk p) Y' := by
          exact Set.subset_iUnion₂_of_subset p
            (Finset.mem_filter.mpr ⟨hp, rfl⟩) Set.Subset.rfl
        exact hmem.trans (Metric.self_subset_cthickening _)
  constructor
  · exact hshade
  · apply Set.iUnion₂_subset
    intro p hp
    by_cases eq : (Y' p).shade = ∅
    · rw [eq]
      exact Set.empty_subset _
    · have hj : blk p ∈ bodies := (hblk p hp).resolve_right eq
      exact (hshade p hp).trans
        (Set.subset_iUnion₂_of_subset (blk p) hj Set.Subset.rfl)

end TubesInBodies

/-! ### From the factoring output to the configuration -/

section Assemble

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Constant in Lemma `lem:ml2thinCentredMult`.**

The comparison constant produced by `Kakeya.ThinCase.centredMult`: covering an `A`-ball by
`w₁`-balls centred at a maximal `w₁`-separated subset costs a factor bounded in terms of the
ratio bound `A ≤ C₁ w₁` and the dimension `n` only, and the comparison at radius `w₁` costs
the factor `C`. The displayed value is provisional. -/
noncomputable def centredMultConstant (C C₁ : NNReal) (n : ℕ) : NNReal :=
  max 1 (C * (4 * C₁) ^ n)

lemma one_le_centredMultConstant {C C₁ : NNReal} {n : ℕ} : 1 ≤ centredMultConstant C C₁ n :=
  le_max_left _ _

/-- **The centred multiplicity statement at radius `A`** (blueprint
`lem:ml2thinCentredMult`).

The factoring proposition compares `|U ∩ B(x, w₁)|` across the points of the larger union
`UW = U(𝕎'_B, Y_{𝕎'_B})`. Covering an `A`-ball by boundedly many `w₁`-balls centred at a
maximal `w₁`-separated subset of `U ∩ B(x, A)` — each of whose points lies in `U ⊆ UW` —
upgrades this to a comparison of `|U ∩ B(x, A)|` across the points of `U`, at the radius
`A ∼ w₁` actually used by the thin case.

The output constant is the *explicit* `centredMultConstant`: the number of `w₁`-balls needed
depends on the ratio `A / w₁` and on the ambient dimension, but not on `U`, so an
existentially quantified constant would needlessly be allowed to depend on the ball. -/
theorem centredMult {U UW : Set E} (hUUW : U ⊆ UW) {w₁ A : ℝ} (hw₁ : 0 < w₁) (hle : w₁ ≤ A)
    {C₁ : NNReal} (hA : A ≤ C₁ * w₁) {C : NNReal}
    (hcomp : ∀ x ∈ UW, ∀ y ∈ UW,
      volume (U ∩ ball x w₁) ≤ (C : ENNReal) * volume (U ∩ ball y w₁)) :
    ∀ x ∈ U, ∀ y ∈ U, volume (U ∩ ball x A) ≤
      (centredMultConstant C C₁ (Module.finrank ℝ E) : ENNReal) * volume (U ∩ ball y A) := by
  intro x hx y hy
  let n : ℕ := Module.finrank ℝ E
  let K : NNReal := (4 * C₁) ^ n
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le hw₁ hle
  have hC₁ : (1 : ℝ) ≤ (C₁ : ℝ) := by
    have hw' : (1 : ℝ) * w₁ ≤ (C₁ : ℝ) * w₁ := by simpa using le_trans hle hA
    exact (mul_le_mul_iff_of_pos_right hw₁).mp hw'
  have hq : (A / w₁ : ℝ) ≤ (C₁ : ℝ) := (div_le_iff₀ hw₁).2 hA
  -- a maximal `w₁`-separated subset of `U ∩ ball x A`
  have hbounded : Bornology.IsBounded (U ∩ ball x A) := by
    exact Metric.isBounded_ball.subset (inter_subset_right : U ∩ ball x A ⊆ ball x A)
  rcases exists_maximal_separated hbounded hw₁ with ⟨N, hNsub, hsep, hmax⟩
  have hNball : (↑N : Set E) ⊆ ball x A := by
    intro z hz
    exact (hNsub hz).2
  have hcard := finite_and_card_le_of_separated hw₁ hApos.le x (hsep := hsep) (hN := hNball)
  have hcardR : (N.card : ℝ) ≤ (K : ℝ) := by
    have hbase : (1 : ℝ) + 2 * A / w₁ ≤ 4 * (C₁ : ℝ) := by
      have hbase2 : (2 * A / w₁ : ℝ) ≤ 2 * (C₁ : ℝ) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hq (by norm_num)
      calc
        (1 : ℝ) + 2 * A / w₁ ≤ 1 + 2 * (C₁ : ℝ) := by
          rw [mul_div_assoc]
          gcongr
        _ ≤ 4 * (C₁ : ℝ) := by nlinarith [hC₁]
    have hbase0 : (0 : ℝ) ≤ 1 + 2 * A / w₁ := by
      have hposA : (0 : ℝ) ≤ A / w₁ := le_of_lt (div_pos hApos hw₁)
      have hterm : (0 : ℝ) ≤ (2 * A) / w₁ := by
        rw [mul_div_assoc]
        exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hposA
      linarith
    have hpow : (1 + 2 * A / w₁) ^ n ≤ (4 * (C₁ : ℝ)) ^ n := pow_le_pow_left₀ hbase0 hbase n
    have hKreal : (K : ℝ) = (4 * (C₁ : ℝ)) ^ n := by
      simp [K, NNReal.coe_pow]
    simpa [Set.ncard_coe_finset, hKreal] using le_trans hcard.2 hpow
  have hcardNN : (N.card : NNReal) ≤ K := by
    exact NNReal.coe_le_coe.mp (by simpa using hcardR)
  have hcardE : (N.card : ENNReal) ≤ (K : ENNReal) := by
    simpa using ENNReal.coe_le_coe.mpr hcardNN
  -- the covering of `U ∩ ball x A` by the `w₁`-balls at the net
  have hcover : U ∩ ball x A ⊆ ⋃ z ∈ N, (U ∩ ball z w₁) := by
    intro u hu
    rcases hmax u hu with ⟨z, hzN, hzdist⟩
    exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hzN, ⟨hu.1, hzdist⟩⟩⟩
  calc
    volume (U ∩ ball x A) ≤ volume (⋃ z ∈ N, (U ∩ ball z w₁)) := measure_mono hcover
    _ ≤ ∑ z ∈ N, volume (U ∩ ball z w₁) := measure_biUnion_finset_le N (fun z => U ∩ ball z w₁)
    _ ≤ (N.card : ENNReal) * ((C : ENNReal) * volume (U ∩ ball y w₁)) := by
      have h : ∀ z ∈ N, volume (U ∩ ball z w₁) ≤ (C : ENNReal) * volume (U ∩ ball y w₁) := by
        intro z hz
        have hzU : z ∈ U := (hNsub hz).1
        exact hcomp z (hUUW hzU) y (hUUW hy)
      calc
        (∑ z ∈ N, volume (U ∩ ball z w₁)) ≤ N.card • ((C : ENNReal) * volume (U ∩ ball y w₁)) :=
          Finset.sum_le_card_nsmul N (fun z => volume (U ∩ ball z w₁))
            ((C : ENNReal) * volume (U ∩ ball y w₁)) h
        _ = (N.card : ENNReal) * ((C : ENNReal) * volume (U ∩ ball y w₁)) := by simp
    _ ≤ (N.card : ENNReal) * ((C : ENNReal) * volume (U ∩ ball y A)) := by
      have hvolle : volume (U ∩ ball y w₁) ≤ volume (U ∩ ball y A) := by
        refine measure_mono ?_
        rintro z ⟨hzU, hzb⟩
        exact ⟨hzU, ball_subset_ball hle hzb⟩
      have hinner : (C : ENNReal) * volume (U ∩ ball y w₁) ≤
          (C : ENNReal) * volume (U ∩ ball y A) :=
        mul_le_mul_of_nonneg_left hvolle zero_le
      exact mul_le_mul_of_nonneg_left hinner zero_le
    _ ≤ (K : ENNReal) * ((C : ENNReal) * volume (U ∩ ball y A)) := by
      exact mul_le_mul_of_nonneg_right hcardE zero_le
    _ ≤ (centredMultConstant C C₁ n : ENNReal) * volume (U ∩ ball y A) := by
      have hKC : (C * K : NNReal) ≤ centredMultConstant C C₁ n := by
        rw [centredMultConstant]
        change (C * K : NNReal) ≤ max 1 (C * (4 * C₁) ^ n)
        exact le_max_right _ _
      have hKCE : ((C * K : NNReal) : ENNReal) ≤ (centredMultConstant C C₁ n : ENNReal) :=
        ENNReal.coe_le_coe.mpr hKC
      have heq : (K : ENNReal) * ((C : ENNReal) * volume (U ∩ ball y A)) =
          ((C * K : NNReal) : ENNReal) * volume (U ∩ ball y A) := by
        calc (K : ENNReal) * ((C : ENNReal) * volume (U ∩ ball y A))
            = ((K : ENNReal) * (C : ENNReal)) * volume (U ∩ ball y A) := by rw [mul_assoc]
        _ = ((C : ENNReal) * (K : ENNReal)) * volume (U ∩ ball y A) := by
          rw [mul_comm (K : ENNReal) (C : ENNReal)]
        _ = ((C * K : NNReal) : ENNReal) * volume (U ∩ ball y A) := by
          rw [← ENNReal.coe_mul]
      rw [heq]
      exact mul_le_mul_of_nonneg_right hKCE zero_le

/-- **Constant in Lemma `lem:ml2thinPerBall`.**

The comparison constant of the `ThinBall` produced by `Kakeya.ThinCase.perBall`: it is a
function of the thickness comparison constant `C₀` of (C3), the Frostman constant `CF` of
(C4), the density constant `c₁` of (C5) and the overlap constant `D` of the `δ`-ball covers
alone, and in particular does not depend on the ball `B`. This ball-independence is what
makes the amalgamation of the per-ball refinements possible.

The displayed value is provisional, but it is built so as to dominate each of the losses the
proof of `Kakeya.ThinCase.perBall` actually incurs, so that `ThinBall.one_le_C` and (T1)–(T6)
are not made unprovable by an accidentally too small constant. It is a four-way `max`:

* the cap `1`, so that `1 ≤ perBallConstant` holds unconditionally — without it the value
  would be `< 1` as soon as `c₁ > 1`, which the hypotheses of `perBall` permit;
* `2 * factoringApplyConstant CF c₁⁻¹ Ccore`, the factor `2` of the mass–Markov upgrade
  `Kakeya.ThinCase.massMarkovUpgrade` applied to the loss
  `factoringApplyConstant CF c₁⁻¹ Ccore` of `Kakeya.ThinCase.factoringApply` (whose fullness
  constant is `c₁⁻¹` there, and which enters *squared*, so this term is already of size
  `c₁⁻²`);
* `centredMultConstant (factoringApplyConstant CF c₁⁻¹ Ccore) (8 * C₀ ^ 2) 3`, the loss of
  `Kakeya.ThinCase.centredMult` at the ratio bound `rad C₀ a ≤ 8 C₀² w₁` supplied by (C4)
  (and hence cubic in `C₀`); the ratio is `8 C₀²` and no longer `4 C₀²` because
  `w1Constant C₀ = max 1 (4 C₀)` now carries the factor `2` of the neighbourhood radius of
  `ThinBall.shade_W_subset`;
* `2 * (D + 1) * tubeSegmentNbhdConstant C₀ * c₁⁻¹ * centredMultConstant …`, the reciprocal
  of the `δ`-ball density constant `deltaBallConstant D C₀ c c₁`, which is what (T5) asks
  for (with `c = perBallConstant …⁻¹`).

Taking each term of the outer `max` separately — rather than one product carrying the
`c₁⁻¹` shrink factors — is essential: the `c₁⁻¹` factors can shrink without bound (the
hypotheses of `perBall` only require `0 < c₁`, not `c₁ ≤ 1`), so a single product containing
them would fail to dominate the `2 * factoringApplyConstant …` and `centredMultConstant …`
terms once `c₁` is large. -/
noncomputable def perBallConstant (C₀ CF c₁ Ccore : NNReal) (D : ℕ) : NNReal :=
  max 1 (max (2 * factoringApplyConstant CF c₁⁻¹ Ccore)
    (max (centredMultConstant (factoringApplyConstant CF c₁⁻¹ Ccore) (8 * C₀ ^ 2) 3)
      (2 * ((D : NNReal) + 1) * tubeSegmentNbhdConstant C₀ * c₁⁻¹ *
        centredMultConstant (factoringApplyConstant CF c₁⁻¹ Ccore) (8 * C₀ ^ 2) 3)))

lemma one_le_perBallConstant {C₀ CF c₁ Ccore : NNReal} {D : ℕ} :
    1 ≤ perBallConstant C₀ CF c₁ Ccore D :=
  le_max_left _ _

/-- **Configuration `hyp:ml2setup`, clauses (C3)–(C5), at a single ball.**

The hypotheses that Configuration `hyp:ml2setup` makes about one ball `B ∈ 𝔅` of the covering
family, in the form `Kakeya.ThinCase.perBall` consumes them: the family `segs = 𝕋_B` of tube
segments with shading `Y = Y_B`, the factoring `𝕋_B = ⨆_{W ∈ 𝕎_B} 𝕋_{B,W}` over
`bodies = 𝕎_B` with block map `blk` and bodies `Wb`, and the four scales `δ ≤ a ≤ b ≤ r₁`
together with the shortest body dimension `w₁ ∼ a`.

The clauses are grouped as in the blueprint. `blk_mem` and `le_block` say that the factoring
is a factoring; `thick` and `dims` are (C3), the affine thicknesses `∼ (r₁, δ, δ)` of the
segments and their pairwise comparability; `body`, `width` and `frostman` are (C4), the
thicknesses `∼ (r₁, b, a)` of the bodies, the comparability of their shortest dimension with
`w₁`, and the Frostman condition of the blocks; `dens` is (C5), the per-segment density bound
`|Y_B(T_B)| ≥ c₁ δ^η |T_B|`.

The three scale and constant clauses `one_le_C₀`, `one_le_CF`, `c₁_pos`, the ordering
`δ_pos`–`b_le_r₁` and `segs_nonempty` are fields rather than separate binders of `perBall`
because they are exactly the standing assumptions of `hyp:ml2setup` on the data this
structure is about, and because none of them is derivable from the others.

`dims` — the segments of `𝕋_B` have pairwise comparable affine thicknesses with the *numerical*
factor `2` — is the second hypothesis of `ShadedBody.factoringAndMultPropCombined`, and it is
*not* derivable from `thick`: the thickness vector comparison only bounds
`τ_i(Y p) ≤ C₀² τ_i(Y q)`, and nothing trades `C₀²` for `2`.

`c₁_pos` is essential and not cosmetic. With `c₁ = 0` the clause `dens` is vacuous, so `Y`
may be everywhere unshaded, and then the fields `ThinBall.S_nonempty` and `ThinBall.denseBall`
of the conclusion of `perBall` are contradictory. It is also what supplies the fullness
constant `Cfull := c₁⁻¹` when `Kakeya.ThinCase.factoringApply` is invoked. -/
structure IsBallFactoring {σ ω : Type*} [DecidableEq ω] (segs : Finset σ) (Y : σ → ShadedBody E)
    (bodies : Finset ω) (Wb : ω → ConvexSpaceBody E) (blk : σ → ω)
    (δ a b r₁ w₁ : NNReal) (η : ℝ) (C₀ CF c₁ : NNReal) : Prop where
  /-- the thickness comparison constant of (C3) and (C4) is a genuine loss -/
  one_le_C₀ : 1 ≤ C₀
  /-- the Frostman constant of the blocks of (C4) is a genuine loss -/
  one_le_CF : 1 ≤ CF
  /-- the density constant of (C5) is positive -/
  c₁_pos : 0 < c₁
  /-- the tube scale is positive -/
  δ_pos : 0 < δ
  /-- the four scales are ordered: `δ ≤ a` -/
  δ_le_a : δ ≤ a
  /-- `a ≤ b` -/
  a_le_b : a ≤ b
  /-- `b ≤ r₁` -/
  b_le_r₁ : b ≤ r₁
  /-- the ball carries at least one segment -/
  segs_nonempty : segs.Nonempty
  /-- (C4): every segment lies in a block of the factoring -/
  blk_mem : ∀ p ∈ segs, blk p ∈ bodies
  /-- (C4): a segment is contained in the body of its block -/
  le_block : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p)
  /-- (C3): the segments have affine thicknesses `∼ (r₁, δ, δ)` -/
  thick : ∀ p ∈ segs, HasThicknesses (Y p).carrier C₀ ![r₁, δ, δ]
  /-- (C3): the segments have *comparable* affine thicknesses, in the exact form
  `ShadedBody.factoringAndMultPropCombined` demands -/
  dims : ∀ p ∈ segs, ∀ q ∈ segs,
    Metric.thickness ℝ (Y p).carrier ≤ 2 • Metric.thickness ℝ (Y q).carrier
  /-- (C4): the bodies have affine thicknesses `∼ (r₁, b, a)`, so shortest dimension `∼ a` -/
  body : ∀ j ∈ bodies, HasThicknesses (Wb j).carrier C₀ ![r₁, b, a]
  /-- (C4): the shortest dimension of every body is comparable with `w₁` -/
  width : ∀ j ∈ bodies,
    Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1) ≤ 2 * w₁ ∧
      (w₁ : ℝ) ≤ 2 * Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1)
  /-- (C4): each block is Frostman with constant `CF` inside its body -/
  frostman : ∀ j ∈ bodies, ConvexSpaceBody.IsFrostmanIn (segs.filter fun p => blk p = j)
    (fun p => (Y p).toConvexSpaceBody) (Wb j) CF
  /-- (C5): the per-segment density bound `|Y_B(T_B)| ≥ c₁ δ^η |T_B|` -/
  dens : ∀ p ∈ segs,
    (c₁ : ENNReal) * (δ : ENNReal) ^ η * volume (Y p).carrier ≤ volume (Y p).shade

/-- **The `δ`-ball covers of (T5)** (blueprint `lem:ml2thinDeltaBall`).

For each tube segment `T_B ∈ 𝕋_B`, a `D`-boundedly overlapping cover `𝒞(T_B)` of its carrier
by `δ`-balls, every one of which meets the carrier. This is the input of the averaging step
that produces clause (T5) of Definition `hyp:ml2thinsetup`, and it is data — the index type of
the balls, their centres, and the assignment of a cover to each segment — so it is bundled as
a structure rather than as a predicate.

`one_le_D` belongs here because `D` is the overlap constant of *these* covers and of nothing
else. -/
structure DeltaBallCovers {σ : Type*} (segs : Finset σ) (Y : σ → ShadedBody E)
    (δ : NNReal) (D : ℕ) where
  /-- the index type of the covering balls -/
  γ : Type*
  /-- the cover `𝒞(T_B)` attached to a segment -/
  cov : σ → Finset γ
  /-- the centre of a covering ball -/
  ctr : γ → E
  /-- the overlap constant is a genuine loss -/
  one_le_D : 1 ≤ D
  /-- each `𝒞(T_B)` is a `D`-boundedly overlapping cover of the segment's carrier by
  `δ`-balls -/
  isCover : ∀ p ∈ segs,
    IsBoundedlyOverlappingCover (cov p) ctr (fun _ => (δ : ℝ)) D (Y p).carrier
  /-- every ball of the cover meets the segment it covers -/
  meets : ∀ p ∈ segs, ∀ i ∈ cov p, (ball (ctr i) (δ : ℝ) ∩ (Y p).carrier).Nonempty

/-- **The thin-case refinement in a single ball** (blueprint `lem:ml2thinPerBall`, together
with the `δ`-ball estimate of `lem:ml2thinDeltaBall` which supplies (T5)).

Applying the factoring proposition (`factoringApply`), extending its shading by `∅`
(`extendByEmpty`), upgrading its summed refinement to a termwise one on a large subfamily
(`massMarkovUpgrade`) and passing from radius `w₁` to radius `A` (`centredMult`) produces
the data of Definition `hyp:ml2thinsetup` for the ball, with a constant that does not
depend on the ball.

Two temptations must be resisted, and both would break the composition with
`Kakeya.ThinCase.lift`: one must not pass to `𝒮_B` and rename it `𝕋_B`, and one must not
truncate `Y'_B` to `∅` off `𝒮_B`. Keeping `Y'_B` on all of `𝕋_B` and recording `𝒮_B`
separately avoids both.

The field `ThinBall.w_le`, i.e. `2 * w j ≤ rad C₀ a` for the per-body radius `w j = τ₂(W_j)` of
(T6), is *not* a hypothesis here: it is derived from `hfac.body`, which gives
`2 τ₂(W_j) ≤ 2 C₀ a ≤ w1Constant C₀ * a` by the definition of `w1Constant C₀ ≥ 2 C₀`. Assuming
it separately would make the lemma vacuous whenever the two constants disagree.

Only three of the binders are hypotheses. `hdim` fixes the ambient dimension;
`hfac : Kakeya.ThinCase.IsBallFactoring …` is clauses (C3)–(C5) of Configuration
`hyp:ml2setup` at this ball, together with the standing constant and scale conditions they
are stated under; and `bc : Kakeya.ThinCase.DeltaBallCovers …` is the (T5) `δ`-ball cover data.
Everything else — `segs`, `Y`, `bodies`, `Wb`, `blk`, the scales `δ, a, b, r₁, w₁`, the
exponent `η` and the constants `C₀, CF, c₁, D` — is the data the conclusion is about. See
those two structures for what each clause says and why none of them is derivable from the
others. -/
theorem perBall (hdim : Module.finrank ℝ E = 3)
    {σ ω : Type*} [DecidableEq ω] (segs : Finset σ) (Y : σ → ShadedBody E)
    (bodies : Finset ω) (Wb : ω → ConvexSpaceBody E) (blk : σ → ω)
    {δ a b r₁ w₁ : NNReal} {η : ℝ} {C₀ CF c₁ Ccore : NNReal} {D : ℕ}
    (hfac : IsBallFactoring segs Y bodies Wb blk δ a b r₁ w₁ η C₀ CF c₁)
    (bc : DeltaBallCovers segs Y δ D)
    -- the `w₁` window of the corrected Proposition 5.1, passed to
    -- `Kakeya.ThinCase.factoringApply`. It is *not* derivable from `IsBallFactoring`: `body`
    -- and `width` together give only `δ ≤ 2 * C₀ * w₁`, and nothing bounds `w₁` above by `1`.
    (hδw₁ : δ ≤ w₁) (hw₁one : w₁ ≤ 1)
    -- `η` is a loss exponent; see the same binder on `Kakeya.ThinCase.factoringApply`, which is
    -- where it is used. Free at the call site: `Kakeya.VeryNotSticky.VeryNotSticky.hη` is `0 < η`.
    (hη : (0:ℝ) ≤ η)
    -- the localisation of the bodies, the hypothesis whose absence makes
    -- `Kakeya.ThinCase.factoringApply` — and, through it, this lemma — false. It is *not* a
    -- field of `IsBallFactoring`, for the same reason `hδw₁` and `hw₁one` are not: `body` pins
    -- the *shape* `(r₁, b, a)` of the bodies but leaves `r₁` free and says nothing about where
    -- in space they sit. `Kakeya.ThinCase.PerBallRefute.perBall_refuted` refutes the
    -- `hloc`-free form of this lemma, and
    -- `Kakeya.ThinCase.PerBallRefute.not_subset_closedBall_one` is the check that the
    -- refuting configuration violates precisely this hypothesis and nothing else.
    -- `Kakeya.VeryNotSticky.exists_thinConfig` discharges it from
    -- `Kakeya.VeryNotSticky.BallData.bodies_subset_ball` and `r₁ = δ^exscal ≤ 1`.
    (hloc : ∃ z : E, ∀ j ∈ bodies, (Wb j).carrier ⊆ Metric.closedBall z 1)
    -- the core envelope of `Kakeya.ThinCase.factoringApply`
    (hCcore2 : 2 ≤ Ccore)
    (hCcoreRef : (ShadedBody.outerFactoringFamily_refinement.c 3 segs.card δ)⁻¹ ≤ Ccore)
    (hCcoreMult : ShadedBody.outerFactoringFamily_outerConstMultFat.c 3 bodies.card δ ≤ Ccore)
    (hCcoreDyad : ((Nat.log 2 bodies.card + 1 : ℕ) : NNReal) ≤ Ccore)
    -- the fifth envelope bound of `Kakeya.ThinCase.factoringApply`, the one that pays for the
    -- `log₂ CF` part of the eccentricity exponent behind conclusion (i)
    (hCcoreFrost : ((Nat.log 2 ⌈CF⌉₊ + 1 : ℕ) : NNReal) ≤ Ccore)
    -- the two scale-dependent envelope bounds of `Kakeya.ThinCase.factoringApply`, read at the
    -- scale `δ / C₀` at which `hfac.thick` discretizes the segments. They are not derivable from
    -- their `δ`-versions above: the pipeline losses grow as the scale shrinks, and `C₀` is the
    -- comparison constant of (C3), invisible to `factoringApplyCore … δ`.
    -- `Kakeya.VeryNotSticky.exists_thinConfig` discharges them by enlarging its `Ccore`.
    (hCcoreRef₀ :
      (ShadedBody.outerFactoringFamily_refinement.c 3 segs.card (δ / C₀))⁻¹ ≤ Ccore)
    (hCcoreMult₀ :
      ShadedBody.outerFactoringFamily_outerConstMultFat.c 3 bodies.card (δ / C₀) ≤ Ccore)
    -- the eighth envelope bound of `Kakeya.ThinCase.factoringApply`; see its docstring
    (hCcoreNet : thinEnvelopeTerm 3 segs.card bodies.card CF w₁ ≤ Ccore) :
    Nonempty (ThinBall (perBallConstant C₀ CF c₁ Ccore D) C₀ segs Y bodies Wb blk δ a η) := by
  classical
  obtain ⟨hC₀, hCF, hc₁, hδ, hδa, hab, hbr₁, hsegs, hblk, hle, hthick, hdims, hbody, hw₁,
    hFr, hdens⟩ := hfac
  obtain ⟨_, cov, covCtr, hD, hcov, hcovMeets⟩ := bc
  let C : NNReal := perBallConstant C₀ CF c₁ Ccore D
  let Cfact : NNReal := factoringApplyConstant CF c₁⁻¹ Ccore
  -- the ratio bound is `rad C₀ a ≤ 8 C₀² w₁`, not `4 C₀² w₁`: `w1Constant C₀ = max 1 (4 C₀)`
  -- carries the factor `2` of the neighbourhood radius of `ThinBall.shade_W_subset`
  let Ccent : NNReal := centredMultConstant Cfact (8 * C₀ ^ 2) 3
  have hCfact_gt0 : (0 : NNReal) < Cfact := by
    simpa [Cfact] using
      lt_of_lt_of_le (by norm_num : (0 : NNReal) < (1 : NNReal))
        (one_le_factoringApplyConstant (CF := CF) (Cfull := c₁⁻¹) (Ccore := Ccore))
  have hCfact_ne : Cfact ≠ 0 := ne_of_gt hCfact_gt0
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  -- positivity bookkeeping
  have hδpos : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδnonneg : (0 : ℝ) ≤ (δ : ℝ) := le_of_lt hδpos
  have hr₁pos : (0 : ℝ) < (r₁ : ℝ) :=
    lt_of_lt_of_le hδpos (by exact_mod_cast (le_trans hδa (le_trans hab hbr₁)))
  have hC₀pos : (0 : ℝ) < (C₀ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) hC₀)
  have hc₁ne0 : (c₁ : ENNReal) ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt hc₁)
  -- the total carrier volume is positive (a segment guaranteed by `hsegs` has positive volume)
  let S_car : ENNReal := ∑ p ∈ segs, volume (Y p).carrier
  have hcarrier_pos : ∀ p ∈ segs, 0 < volume (Y p).carrier := by
    intro p hp
    have hthickp : HasThicknesses (Y p).carrier C₀ ![r₁, δ, δ] := hthick p hp
    have hconv : Convex ℝ (Y p).carrier := (Y p).convex
    have hbdd : Bornology.IsBounded (Y p).carrier := (Y p).isCompact.isBounded
    have hthick_ne_zero : ∀ i ∈ Finset.range (Module.finrank ℝ E),
        Metric.ethickness ℝ (Y p).carrier i ≠ 0 := by
      intro i hi
      rw [Finset.mem_range, hdim] at hi
      let k : Fin 3 := ⟨i, hi⟩
      rcases hthickp k with ⟨hle, _⟩
      have h_val_pos : 0 < (![(r₁ : ℝ), (δ : ℝ), (δ : ℝ)] k) := by
        match k with
        | 0 => simp [hr₁pos]
        | 1 => simp [hδpos]
        | 2 => simp [hδpos]
      have hle' : ((C₀ : ℝ)⁻¹ * (![(r₁ : ℝ), (δ : ℝ), (δ : ℝ)] k : ℝ)) ≤
          Metric.thickness ℝ (Y p).carrier (k : ℕ) := by
        simpa using hle
      have hprodpos : 0 < (C₀ : ℝ)⁻¹ * (![(r₁ : ℝ), (δ : ℝ), (δ : ℝ)] k) :=
        mul_pos (inv_pos.mpr hC₀pos) h_val_pos
      have hpos : 0 < Metric.thickness ℝ (Y p).carrier (k : ℕ) := by linarith
      rw [Metric.ethickness_thickness' hbdd k.val]
      rw [ENNReal.ofReal_ne_zero_iff]
      simpa [k] using hpos
    exact hconv.volume_pos_of_ethickness_ne_zero hthick_ne_zero
  have hS_car_pos : 0 < S_car := by
    obtain ⟨p0, hp0⟩ := hsegs
    exact lt_of_lt_of_le (hcarrier_pos p0 hp0)
      (Finset.single_le_sum (s := segs) (f := fun p => volume (Y p).carrier)
        (by intro p _; exact zero_le) hp0)
  have hS_car_ne_top : S_car ≠ ⊤ := by
    dsimp [S_car]
    exact ENNReal.sum_ne_top.2 (fun p _ => (Y p).isCompact'.measure_ne_top)
  let S_sha : ENNReal := ∑ p ∈ segs, volume (Y p).shade
  have hdens_sum : (c₁ : ENNReal) * (δ : ENNReal) ^ η * S_car ≤ S_sha := by
    calc
      (c₁ : ENNReal) * (δ : ENNReal) ^ η * S_car
          = ∑ p ∈ segs, (c₁ : ENNReal) * (δ : ENNReal) ^ η * volume (Y p).carrier := by
            dsimp [S_car]
            rw [Finset.mul_sum]
      _ ≤ S_sha := by
        dsimp [S_sha]
        exact Finset.sum_le_sum (fun p hp => hdens p hp)
  -- the fullness hypothesis of `factoringApply`: `δ^η ≤ c₁⁻¹ * fullness segs Y`
  have hcl : (c₁ : ENNReal) * (δ : ENNReal) ^ η ≤ (fullness segs Y : ENNReal) := by
    rw [fullness_def]
    apply (ENNReal.le_div_iff_mul_le (Or.inl hS_car_pos.ne') (Or.inl hS_car_ne_top)).mpr
    exact hdens_sum
  have hfull : (δ : ENNReal) ^ η ≤ ((c₁⁻¹ : NNReal) : ENNReal) * (fullness segs Y : ENNReal) := by
    calc
      (δ : ENNReal) ^ η = ((c₁⁻¹ : NNReal) : ENNReal) * ((c₁ : ENNReal) * (δ : ENNReal) ^ η) := by
        rw [ENNReal.coe_inv (ne_of_gt hc₁)]
        rw [← mul_assoc]
        rw [ENNReal.inv_mul_cancel hc₁ne0 (by exact ENNReal.coe_ne_top)]
        rw [one_mul]
      _ ≤ ((c₁⁻¹ : NNReal) : ENNReal) * (fullness segs Y : ENNReal) := by
        gcongr
  -- the pointwise form of (C5), in the shape `Kakeya.ThinCase.factoringApply` consumes it:
  -- `Cfull = c₁⁻¹` there, so `hdens` is `IsBallFactoring.dens` divided by `c₁`
  have hdens_pt : ∀ p ∈ segs, (δ : ENNReal) ^ η * volume (Y p).carrier ≤
      ((c₁⁻¹ : NNReal) : ENNReal) * volume (Y p).shade := by
    intro p hp
    rw [ENNReal.coe_inv (ne_of_gt hc₁)]
    calc (δ : ENNReal) ^ η * volume (Y p).carrier
        = (c₁ : ENNReal)⁻¹ * ((c₁ : ENNReal) * ((δ : ENNReal) ^ η * volume (Y p).carrier)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc₁ne0 ENNReal.coe_ne_top, one_mul]
      _ ≤ (c₁ : ENNReal)⁻¹ * volume (Y p).shade := by
          refine mul_le_mul_right ?_ _
          rw [← mul_assoc]
          exact hdens p hp
  -- the discretization scale of the segments, `δ / C₀`, straight from (C3)
  have hC₀pos' : (0 : NNReal) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hδ₀pos : (0 : NNReal) < δ / C₀ := div_pos hδ hC₀pos'
  have hδ₀le : δ / C₀ ≤ δ := by
    rw [div_le_iff₀ hC₀pos']
    exact le_mul_of_one_le_right (by simp) hC₀
  have hδ₀w₁ : δ / C₀ ≤ w₁ := hδ₀le.trans hδw₁
  have hδr₁ : (δ : ℝ) ≤ (r₁ : ℝ) := by
    exact_mod_cast (hδa.trans (hab.trans hbr₁))
  have hscale : ∀ p ∈ segs,
      (((δ / C₀ : NNReal)) : ENNReal) ≤ Metric.ethickness.scale ℝ (Y p).carrier := by
    intro p hp
    rw [Metric.ethickness.le_scale_iff]
    intro n
    have hn3 : (n : ℕ) < 3 := by rw [← hdim]; exact n.isLt
    have hk := (hthick p hp) ⟨(n : ℕ), hn3⟩
    have hval : ∀ k : Fin 3, (δ : ℝ) ≤ ![(r₁ : ℝ), (δ : ℝ), (δ : ℝ)] k := by
      intro k; fin_cases k <;> simp [hδr₁]
    have hbdd : Bornology.IsBounded (Y p).carrier := (Y p).isCompact.isBounded
    have hthk : (δ : ℝ) / (C₀ : ℝ) ≤ Metric.thickness ℝ (Y p).carrier (n : ℕ) := by
      refine le_trans ?_ hk.1
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (hval _) (by positivity)
    rw [Metric.ethickness_thickness' hbdd]
    have hcoe : (((δ / C₀ : NNReal)) : ENNReal) = ENNReal.ofReal ((δ : ℝ) / (C₀ : ℝ)) := by
      rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_div]
    rw [hcoe]
    exact ENNReal.ofReal_le_ofReal hthk
  -- apply the factoring proposition in this ball
  rcases factoringApply hdim segs Y bodies Wb blk (δ := δ) (w₁ := w₁) (η := η) (CF := CF)
      (Cfull := c₁⁻¹) (Ccore := Ccore) hδ hδw₁ hw₁one hη hCF hCcore2 hCcoreRef hCcoreMult
      hCcoreDyad hCcoreFrost hblk hle hdims hFr hw₁ hloc
      (δ₀ := δ / C₀) hδ₀pos hδ₀w₁ hscale hCcoreRef₀ hCcoreMult₀ hCcoreNet hdens_pt hfull with
    ⟨segs', bodies', Yf, Wf, h_segs_sub, h_bodies_sub, h_car, h_shade,
     h_WbLe, h_WleCth,
     h_full, h_contain, h_cmult, h_inner, h_centw1, h_Wshade, h_refsum⟩
  -- extend the shading by `∅` off `segs'`, to live on all of `segs`
  let Yext : σ → ShadedBody E := fun p =>
    { toConvexSpaceBody := (Y p).toConvexSpaceBody
      shade := if hsegsp : p ∈ segs' then (Yf p).shade else ∅
      measurableSet_shade := by
        by_cases hsegsp : p ∈ segs'
        · simpa [hsegsp] using (Yf p).measurableSet_shade
        · simp [hsegsp]
      shade_subset := by
        intro x hx
        by_cases hsegsp : p ∈ segs'
        · change x ∈ (if p ∈ segs' then (Yf p).shade else ∅) at hx
          rw [if_pos hsegsp] at hx
          have hs : (Yf p).shade ⊆ (Yf p).carrier := (Yf p).shade_subset
          exact (by simpa [h_car p (h_segs_sub hsegsp)] using (hs hx) : x ∈ (Y p).carrier)
        · simp [hsegsp] at hx }
  have hext_shade : ∀ p ∈ segs', (Yext p).shade = (Yf p).shade := by
    intro p hp
    simp [Yext, hp]
  have hempty_shade : ∀ p ∈ segs, p ∉ segs' → (Yext p).shade = ∅ := by
    intro p hp hnot
    simp [Yext, hnot]
  rcases extendByEmpty segs segs' h_segs_sub blk Yf Yext hext_shade hempty_shade with
    ⟨hU, hUj, hpm, hsumExt⟩
  -- the summed refinement `(vi)` transported to all of `segs`
  have h_coe_invC : ((Cfact⁻¹ : NNReal) : ENNReal) = ((Cfact : ENNReal)⁻¹) := by
    exact ENNReal.coe_inv hCfact_ne
  have h_refsum_ext : ((Cfact⁻¹ : NNReal) : ENNReal) * ∑ p ∈ segs, volume (Y p).shade ≤
      ∑ p ∈ segs, volume (Yext p).shade := by
    rw [hsumExt]
    rw [h_coe_invC]
    simpa [Cfact] using h_refsum
  -- mass--Markov upgrade: a large subfamily `S` carrying a termwise and summed refinement
  have hsubYext : ∀ p ∈ segs, (Yext p).shade ⊆ (Y p).shade := by
    intro p hp
    by_cases hp' : p ∈ segs'
    · have hs := h_shade p hp'
      simpa [Yext, hp'] using hs
    · simp [Yext, hp']
  have hfinY : ∀ p ∈ segs, volume (Y p).shade ≠ ⊤ := by
    intro p hp
    exact ne_top_of_le_ne_top (Y p).isCompact'.measure_ne_top (measure_mono (Y p).shade_subset)
  -- `Cfact^{-1} M ≤ N` for massMarkovUpgrade (this is `h_refsum_ext` above, extended)
  let t : NNReal := tubeSegmentNbhdConstant C₀
  let B : NNReal := (2 : NNReal) * ((D : NNReal) + 1) * t * c₁⁻¹ * Ccent
  have hdom : C = max 1 (max (2 * Cfact) (max Ccent B)) := rfl
  have hle_2Cfact : (2 : NNReal) * Cfact ≤ C := by
    rw [hdom]
    exact le_trans (le_max_left (2 * Cfact) (max Ccent B))
      (le_max_right 1 (max (2 * Cfact) (max Ccent B)))
  have hle_Ccent : Ccent ≤ C := by
    rw [hdom]
    exact le_trans
      (le_trans (le_max_left Ccent B) (le_max_right (2 * Cfact) (max Ccent B)))
      (le_max_right 1 (max (2 * Cfact) (max Ccent B)))
  have hle_Cfact : Cfact ≤ C := by
    have hrun : Cfact ≤ Cfact * 2 := by
      exact le_mul_of_one_le_right (show (0 : NNReal) ≤ Cfact from by positivity)
        (by norm_num : (1 : NNReal) ≤ (2 : NNReal))
    exact le_trans (by simpa [mul_comm] using hrun) hle_2Cfact
  have hle_B : B ≤ C := by
    rw [hdom]
    exact le_trans
      (le_trans (le_max_right Ccent B) (le_max_right (2 * Cfact) (max Ccent B)))
      (le_max_right 1 (max (2 * Cfact) (max Ccent B)))
  -- the mass--Markov upgrade
  let k : NNReal := Cfact⁻¹ / 2
  let S : Finset σ :=
    segs.filter fun p => ((k : NNReal) : ENNReal) * volume (Y p).shade ≤ volume (Yext p).shade
  have hhmm : ((k : NNReal) : ENNReal) * ∑ p ∈ segs, volume (Y p).shade ≤
      ∑ p ∈ S, volume (Y p).shade := by
    simpa [S, k] using
      (massMarkovUpgrade segs (fun p => (Y p).shade) (fun p => (Yext p).shade)
        hsubYext hfinY (κ := Cfact⁻¹) h_refsum_ext)
  -- the defining cancellation `k * 2Cfact = 1`, i.e. `(Cfact⁻¹/2)⁻¹ = 2Cfact`
  have hprod : k * (2 * Cfact : NNReal) = 1 := by
    dsimp [k]
    exact_mod_cast (by
      field_simp [show (Cfact : ℝ) ≠ 0 from by exact_mod_cast hCfact_ne])
  have hkE : ((k : NNReal) : ENNReal) * ((2 * Cfact : NNReal) : ENNReal) = 1 := by
    exact_mod_cast hprod
  have hkm : (((2 * Cfact : NNReal) : ENNReal) * (k : NNReal)) = 1 := by
    rw [mul_comm]
    exact hkE
  -- `mass_S : ∑_{segs} ≤ C ∑_S`
  have hmass : ∑ p ∈ segs, volume (Y p).shade ≤ (C : ENNReal) * ∑ p ∈ S, volume (Y p).shade := by
    have htmp : ∑ p ∈ segs, volume (Y p).shade ≤
        ((2 * Cfact : NNReal) : ENNReal) * ∑ p ∈ S, volume (Y p).shade := by
      calc
        ∑ p ∈ segs, volume (Y p).shade
            = ((2 * Cfact : NNReal) : ENNReal) *
                ((k : NNReal) * ∑ p ∈ segs, volume (Y p).shade) := by
                symm
                calc
                  ((2 * Cfact : NNReal) : ENNReal) *
                      ((k : NNReal) * ∑ p ∈ segs, volume (Y p).shade)
                      = (((2 * Cfact : NNReal) : ENNReal) * (k : NNReal)) *
                          ∑ p ∈ segs, volume (Y p).shade := by rw [← mul_assoc]
                  _ = 1 * ∑ p ∈ segs, volume (Y p).shade := by rw [hkm]
                  _ = ∑ p ∈ segs, volume (Y p).shade := by rw [one_mul]
        _ ≤ ((2 * Cfact : NNReal) : ENNReal) * ∑ p ∈ S, volume (Y p).shade := by
            exact mul_le_mul_of_nonneg_left hhmm (by positivity)
    exact le_trans htmp (mul_le_mul_of_nonneg_right (by exact_mod_cast hle_2Cfact) (by positivity))
  -- `refine_S : volume (Y p) ≤ C * volume (Yext p)` on `S`
  have hrefine : ∀ p ∈ S, volume (Y p).shade ≤ (C : ENNReal) * volume (Yext p).shade := by
    intro p hp
    dsimp [S] at hp
    have hcond : ((k : NNReal) : ENNReal) * volume (Y p).shade ≤ volume (Yext p).shade :=
      (Finset.mem_filter.mp hp).2
    have htmp : volume (Y p).shade ≤
        ((2 * Cfact : NNReal) : ENNReal) * volume (Yext p).shade := by
      calc
        volume (Y p).shade
            = ((2 * Cfact : NNReal) : ENNReal) *
                ((k : NNReal) * volume (Y p).shade) := by
                symm
                calc
                  ((2 * Cfact : NNReal) : ENNReal) *
                      ((k : NNReal) * volume (Y p).shade)
                      = (((2 * Cfact : NNReal) : ENNReal) * (k : NNReal)) *
                          volume (Y p).shade := by rw [← mul_assoc]
                  _ = 1 * volume (Y p).shade := by rw [hkm]
                  _ = volume (Y p).shade := by rw [one_mul]
        _ ≤ ((2 * Cfact : NNReal) : ENNReal) * volume (Yext p).shade := by
            exact mul_le_mul_of_nonneg_left hcond (by positivity)
    exact le_trans htmp (mul_le_mul_of_nonneg_right (by exact_mod_cast hle_2Cfact) (by positivity))
  -- positivity of the segment volumes (density (C5) + convexity)
  have hδpow_ne0 : (δ : ENNReal) ^ η ≠ 0 := by
    exact ne_of_gt (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ) ENNReal.coe_ne_top)
  have hseg_vol_pos : ∀ p ∈ segs, 0 < volume (Y p).shade := by
    intro p hp
    have hdensp := hdens p hp
    have hpos : (0 : ENNReal) < (c₁ : ENNReal) * (δ : ENNReal) ^ η * volume (Y p).carrier := by
      exact ENNReal.mul_pos
        (ne_of_gt (ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr (ne_of_gt hc₁)) hδpow_ne0))
        (ne_of_gt (hcarrier_pos p hp))
    exact lt_of_lt_of_le hpos hdensp
  have hMpos : (0 : ENNReal) < ∑ p ∈ segs, volume (Y p).shade := by
    obtain ⟨p0, hp0⟩ := hsegs
    exact lt_of_lt_of_le (hseg_vol_pos p0 hp0)
      (Finset.single_le_sum (s := segs) (f := fun p => volume (Y p).shade)
        (by intro p _; exact zero_le) hp0)
  have hS_nonempty : S.Nonempty := by
    by_contra hSne
    have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
    have hSsum0 : ∑ p ∈ S, volume (Y p).shade = 0 := by simp [hSempty]
    have hmass0 : ∑ p ∈ segs, volume (Y p).shade ≤ 0 := by
      simpa [hSsum0] using hmass
    exact (not_lt_of_ge hmass0) hMpos
  -- the per-body radius `w` and the bound `2 * w ≤ rad C₀ a` ((T6)); the *doubled* radius is
  -- the one at which item (v) of `factoringApply` places the shade of the enlarged outer body,
  -- which is why `w1Constant C₀ = max 1 (4 * C₀)` and not `max 1 (2 * C₀)`
  let w : ω → ℝ := fun j => Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1)
  have hw_le : ∀ j ∈ bodies', 2 * w j ≤ (rad C₀ a : ℝ) := by
    intro j hj
    dsimp [w]
    have hbody_j : HasThicknesses (Wb j).carrier C₀ ![r₁, b, a] := hbody j (h_bodies_sub hj)
    have hvals : ∀ k : Fin 3,
        (C₀ : ℝ)⁻¹ * (![(r₁ : ℝ), (b : ℝ), (a : ℝ)]) k ≤
            Metric.thickness ℝ (Wb j).carrier (k : ℕ) ∧
          Metric.thickness ℝ (Wb j).carrier (k : ℕ) ≤
            (C₀ : ℝ) * (![(r₁ : ℝ), (b : ℝ), (a : ℝ)]) k := by
      simpa [HasThicknesses] using hbody_j
    have h2 : Metric.thickness ℝ (Wb j).carrier 2 ≤ (C₀ : ℝ) * a := by
      simpa using (hvals 2).2
    have hfin : Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1) ≤ (C₀ : ℝ) * a := by
      rw [hdim]
      simpa using h2
    have ha0 : (0 : ℝ) ≤ a := by
      exact le_of_lt (by exact_mod_cast (lt_of_lt_of_le hδ hδa))
    have h2Ca : 2 * (C₀ : ℝ) ≤ (w1Constant C₀ : ℝ) := by
      exact_mod_cast two_mul_le_w1Constant C₀
    calc
      2 * Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1)
          ≤ 2 * ((C₀ : ℝ) * a) := mul_le_mul_of_nonneg_left hfin (by norm_num)
      _ = (2 * (C₀ : ℝ)) * a := by ring
      _ ≤ (w1Constant C₀ : ℝ) * a := mul_le_mul_of_nonneg_right h2Ca ha0
      _ = (rad C₀ a : ℝ) := by dsimp [rad]
  -- the δ-ball density constant for (T5)
  let db : NNReal := deltaBallConstant D C₀ k c₁
  have hBdb_nn : (1 : NNReal) ≤ B * db := by
    have ht_ne : tubeSegmentNbhdConstant C₀ ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : NNReal) < (1 : NNReal))
        (one_le_tubeSegmentNbhdConstant (C₀ := C₀)))
    have hc1_ne : c₁ ≠ 0 := ne_of_gt hc₁
    have hDne : (D : NNReal) ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : NNReal) < (1 : NNReal))
        (by exact_mod_cast hD))
    have hCf_le_Ccn : Cfact ≤ Ccent := by
      have hC0sq : (1 : NNReal) ≤ C₀ ^ 2 := by
        rw [pow_two]
        simpa using (mul_le_mul hC₀ hC₀ (by norm_num) (by norm_num))
      have hbig : (1 : NNReal) ≤ 4 * (8 * C₀ ^ 2) := by
        calc
          (1 : NNReal) ≤ 32 * C₀ ^ 2 := by
            calc
              (1 : NNReal) ≤ (32 : NNReal) := by norm_num
              _ ≤ 32 * C₀ ^ 2 := by
                simpa using (mul_le_mul_of_nonneg_left hC0sq (by norm_num : (0 : NNReal) ≤ 32))
          _ = 4 * (8 * C₀ ^ 2) := by ring
      have hpow : (1 : NNReal) ≤ (4 * (8 * C₀ ^ 2)) ^ 3 := by
        simpa using (pow_le_pow_left₀ (show (0 : NNReal) ≤ 1 from by norm_num) hbig 3)
      dsimp [Ccent]
      calc
        Cfact = Cfact * 1 := by rw [mul_one]
        _ ≤ Cfact * ((4 * (8 * C₀ ^ 2)) ^ 3) := mul_le_mul_of_nonneg_left hpow (by positivity)
        _ ≤ max 1 (Cfact * ((4 * (8 * C₀ ^ 2)) ^ 3)) := le_max_right _ _
    have hcc : (1 : NNReal) ≤ Ccent * Cfact⁻¹ := by
      calc
        (1 : NNReal) = Cfact * Cfact⁻¹ := (mul_inv_cancel₀ hCfact_ne).symm
        _ ≤ Ccent * Cfact⁻¹ := mul_le_mul_of_nonneg_right hCf_le_Ccn (by positivity)
    have hDpp : (1 : NNReal) ≤ ((D : NNReal) + 1) * (D : NNReal)⁻¹ := by
      calc
        (1 : NNReal) = (D : NNReal) * (D : NNReal)⁻¹ := (mul_inv_cancel₀ hDne).symm
        _ ≤ ((D : NNReal) + 1) * (D : NNReal)⁻¹ :=
          mul_le_mul_of_nonneg_right
            (show (D : NNReal) ≤ (D : NNReal) + 1 from le_add_of_nonneg_right (by norm_num))
            (by positivity)
    have hprod : B * db = (((D : NNReal) + 1) * (D : NNReal)⁻¹) * (Ccent * Cfact⁻¹) := by
      dsimp [B, db, deltaBallConstant, deltaBallSingleConstant, t, k]
      exact_mod_cast (by
        field_simp [
          show (D : ℝ) ≠ 0 from by exact_mod_cast hDne,
          show ((tubeSegmentNbhdConstant C₀) : ℝ) ≠ 0 from by exact_mod_cast ht_ne,
          show (c₁ : ℝ) ≠ 0 from by exact_mod_cast hc1_ne,
          show (Cfact : ℝ) ≠ 0 from by exact_mod_cast hCfact_ne]
        simp [mul_assoc, mul_comm, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat])
    simpa using le_trans (mul_le_mul' hDpp hcc) hprod.ge
  have hdense_const : (C : ENNReal)⁻¹ ≤ (db : ENNReal) := by
    have hB_ne : B ≠ 0 := by
      intro hB0
      have hge : (1 : NNReal) ≤ 0 := by
        simpa only [hB0, zero_mul] using hBdb_nn
      exact (not_lt_of_ge hge) (by norm_num : (0 : NNReal) < (1 : NNReal))
    have hCpos : (0 : NNReal) < C := by
      exact lt_of_lt_of_le (by norm_num : (0 : NNReal) < (1 : NNReal))
        (by
          simpa [C] using one_le_perBallConstant (C₀ := C₀) (CF := CF) (c₁ := c₁)
            (Ccore := Ccore) (D := D))
    have hC_ne : C ≠ 0 := ne_of_gt hCpos
    have hBinv_le_db : B⁻¹ ≤ db := by
      calc
        B⁻¹ = B⁻¹ * 1 := by rw [mul_one]
        _ ≤ B⁻¹ * (B * db) := mul_le_mul_of_nonneg_left hBdb_nn (by positivity)
        _ = (B⁻¹ * B) * db := by rw [← mul_assoc]
        _ = db := by rw [inv_mul_cancel₀ hB_ne, one_mul]
    have hC_le_B : C⁻¹ ≤ B⁻¹ := by
      have hBpos : (0 : NNReal) < B := lt_of_le_of_ne (by positivity) (Ne.symm hB_ne)
      exact (inv_le_inv₀ hCpos hBpos).mpr hle_B
    have hC_le_db : C⁻¹ ≤ db := le_trans hC_le_B hBinv_le_db
    rw [← ENNReal.coe_inv hC_ne]
    exact_mod_cast hC_le_db
  rcases h_inner with ⟨μinner, hμblocks⟩
  refine ⟨{
    one_le_C := by
      simpa [C] using
        one_le_perBallConstant (C₀ := C₀) (CF := CF) (c₁ := c₁) (Ccore := Ccore) (D := D)
    Y' := Yext
    carrier_Y' := fun p _ => rfl
    shade_Y'_subset := hsubYext
    S := S
    S_subset := by
      exact Finset.filter_subset
        (fun p : σ => ((k : NNReal) : ENNReal) * volume (Y p).shade ≤ volume (Yext p).shade)
          segs
    S_nonempty := hS_nonempty
    mass_S := hmass
    refine_S := hrefine
    bodies' := bodies'
    bodies'_subset := h_bodies_sub
    W := Wf
    Wb_le_W := h_WbLe
    W_le_cthickening := h_WleCth
    fullness_bodies := by
      exact le_trans h_full
        (mul_le_mul' (ENNReal.coe_le_coe.mpr hle_Cfact) le_rfl)
    shade_containment := by
      intro p hp x hx
      by_cases hp' : p ∈ segs'
      · have hx' : x ∈ (Yf p).shade := by simpa [hext_shade p hp'] using hx
        exact h_contain p hp' x hx'
      · rw [hempty_shade p hp hp'] at hx
        exact hx.elim
    constMult_bodies := HasCConstantMultiplicity.mono bodies' Wf hle_Cfact h_cmult
    μinner := μinner
    constMult_blocks := by
      intro j hj x hx
      have hx' : x ∈ iUnionShade (segs'.filter fun p => blk p = j) Yf := by
        simpa [hUj j] using hx
      rcases hμblocks j hj x hx' with ⟨hle1, hle2⟩
      have hfc : (Cfact : ENNReal) ≤ (C : ENNReal) := ENNReal.coe_le_coe.mpr hle_Cfact
      have hle1' : (pointwiseMultiplicity (segs.filter fun p => blk p = j) Yext x : ENNReal) ≤
          (Cfact : ENNReal) * (μinner : ENNReal) := by
        simpa [hpm j x] using hle1
      have hle2' : (μinner : ENNReal) ≤ (Cfact : ENNReal) *
          (pointwiseMultiplicity (segs.filter fun p => blk p = j) Yext x : ENNReal) := by
        simpa [hpm j x] using hle2
      constructor
      · exact le_trans hle1' (mul_le_mul' hfc le_rfl)
      · exact le_trans hle2' (mul_le_mul' hfc le_rfl)
    centredMult := by
      intro x hx y hy
      by_cases hne : (iUnionShade segs Yext).Nonempty
      · obtain ⟨x0, hx0⟩ := hne
        rcases Set.mem_iUnion₂.mp hx0 with ⟨p, hp, hx0sha⟩
        have hcent : ∀ p ∈ segs, ∀ x ∈ (Yext p).shade,
            blk p ∈ bodies' ∧ x ∈ (Wf (blk p)).shade := by
          intro p hp x hx
          by_cases hp' : p ∈ segs'
          · have hx' : x ∈ (Yf p).shade := by simpa [hext_shade p hp'] using hx
            exact h_contain p hp' x hx'
          · rw [hempty_shade p hp hp'] at hx
            exact hx.elim
        let j0 : ω := blk p
        have hj0 : j0 ∈ bodies' := (hcent p hp x0 hx0sha).1
        have hvals : ∀ kk : Fin 3,
            (C₀ : ℝ)⁻¹ * (![(r₁ : ℝ), (b : ℝ), (a : ℝ)]) kk ≤
              Metric.thickness ℝ (Wb j0).carrier (kk : ℕ) ∧
            Metric.thickness ℝ (Wb j0).carrier (kk : ℕ) ≤
              (C₀ : ℝ) * (![(r₁ : ℝ), (b : ℝ), (a : ℝ)]) kk := by
          simpa [HasThicknesses] using hbody j0 (h_bodies_sub hj0)
        let τ₂ : ℝ := Metric.thickness ℝ (Wb j0).carrier 2
        have hτ2_lb : (C₀ : ℝ)⁻¹ * (a : ℝ) ≤ τ₂ := by
          simpa [τ₂] using (hvals 2).1
        have hτ2_le_C0a : τ₂ ≤ (C₀ : ℝ) * (a : ℝ) := by
          simpa [τ₂] using (hvals 2).2
        have hwj0 : Metric.thickness ℝ (Wb j0).carrier (Module.finrank ℝ E - 1) ≤ 2 * w₁ ∧
            (w₁ : ℝ) ≤ 2 * Metric.thickness ℝ (Wb j0).carrier (Module.finrank ℝ E - 1) :=
          hw₁ j0 (h_bodies_sub hj0)
        have hτ2_le_2w1 : τ₂ ≤ 2 * (w₁ : ℝ) := by
          simpa [τ₂, hdim] using hwj0.1
        have hw1_le_2τ2 : (w₁ : ℝ) ≤ 2 * τ₂ := by
          simpa [τ₂, hdim] using hwj0.2
        have ha_pos : (0 : ℝ) < (a : ℝ) := lt_of_lt_of_le hδpos (by exact_mod_cast hδa)
        have hw1pos : (0 : ℝ) < (w₁ : ℝ) := by
          have hτ2pos : (0 : ℝ) < τ₂ :=
            lt_of_lt_of_le (mul_pos (inv_pos.mpr hC₀pos) ha_pos) hτ2_lb
          have h2pos : (0 : ℝ) < 2 * (w₁ : ℝ) := lt_of_lt_of_le hτ2pos hτ2_le_2w1
          nlinarith
        have hw1_le_2C0a : (w₁ : ℝ) ≤ 2 * (C₀ : ℝ) * (a : ℝ) := by
          calc
            (w₁ : ℝ) ≤ 2 * τ₂ := hw1_le_2τ2
            _ ≤ 2 * ((C₀ : ℝ) * (a : ℝ)) := mul_le_mul_of_nonneg_left hτ2_le_C0a (by norm_num)
            _ = 2 * (C₀ : ℝ) * (a : ℝ) := by ring
        have hw1_le_rad : (w₁ : ℝ) ≤ (rad C₀ a : ℝ) := by
          calc
            (w₁ : ℝ) ≤ 2 * (C₀ : ℝ) * (a : ℝ) := hw1_le_2C0a
            _ ≤ (w1Constant C₀ : ℝ) * (a : ℝ) := by
              have htw : ((2 * C₀ : NNReal) : ℝ) ≤ (w1Constant C₀ : ℝ) := by
                exact_mod_cast two_mul_le_w1Constant C₀
              exact mul_le_mul_of_nonneg_right htw (le_of_lt ha_pos)
            _ = (rad C₀ a : ℝ) := by rfl
        have hC0nz : (C₀ : ℝ) ≠ 0 := ne_of_gt hC₀pos
        have ha_le : (a : ℝ) ≤ (C₀ : ℝ) * τ₂ := by
          calc
            (a : ℝ) = (C₀ : ℝ) * ((C₀ : ℝ)⁻¹ * (a : ℝ)) := by
              rw [← mul_assoc, mul_inv_cancel₀ hC0nz, one_mul]
            _ ≤ (C₀ : ℝ) * τ₂ := mul_le_mul_of_nonneg_left hτ2_lb (le_of_lt hC₀pos)
        have ha_le_2C0w1 : (a : ℝ) ≤ (C₀ : ℝ) * (2 * (w₁ : ℝ)) :=
          le_trans ha_le (mul_le_mul_of_nonneg_left hτ2_le_2w1 (le_of_lt hC₀pos))
        have h1le4C0 : (1 : NNReal) ≤ 4 * C₀ := by
          calc (1 : NNReal) ≤ C₀ := hC₀
            _ ≤ 4 * C₀ := by
              simpa [mul_comm] using
                (le_mul_of_one_le_right (by positivity : (0 : NNReal) ≤ C₀)
                  (by norm_num : (1 : NNReal) ≤ 4))
        have hw1C_le : (w1Constant C₀ : NNReal) ≤ 4 * C₀ := by
          dsimp [w1Constant]
          exact (max_le_iff).2 ⟨h1le4C0, le_rfl⟩
        have hrad_le_4C0a : (rad C₀ a : ℝ) ≤ 4 * (C₀ : ℝ) * (a : ℝ) := by
          calc
            (rad C₀ a : ℝ) = (w1Constant C₀ : ℝ) * (a : ℝ) := by rfl
            _ ≤ ((4 * C₀ : NNReal) : ℝ) * (a : ℝ) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hw1C_le) (le_of_lt ha_pos)
            _ = 4 * (C₀ : ℝ) * (a : ℝ) := by norm_num
        have hA : (rad C₀ a : ℝ) ≤ ((8 * C₀ ^ 2 : NNReal) : ℝ) * (w₁ : ℝ) := by
          calc
            (rad C₀ a : ℝ) ≤ 4 * (C₀ : ℝ) * (a : ℝ) := hrad_le_4C0a
            _ ≤ 4 * (C₀ : ℝ) * ((C₀ : ℝ) * (2 * (w₁ : ℝ))) := by
              exact mul_le_mul_of_nonneg_left ha_le_2C0w1 (by positivity)
            _ = (8 * (C₀ : ℝ) ^ 2) * (w₁ : ℝ) := by ring
            _ = ((8 * C₀ ^ 2 : NNReal) : ℝ) * (w₁ : ℝ) := by norm_num
        have hUUW : iUnionShade segs Yext ⊆ iUnionShade bodies' Wf := by
          apply Set.iUnion₂_subset
          intro p hp x hx
          have hpc := hcent p hp x hx
          exact Set.mem_iUnion₂.mpr ⟨blk p, hpc.1, hpc.2⟩
        have hcomp : ∀ x ∈ iUnionShade bodies' Wf, ∀ y ∈ iUnionShade bodies' Wf,
            volume (iUnionShade segs Yext ∩ ball x (w₁ : ℝ)) ≤
              (Cfact : ENNReal) * volume (iUnionShade segs Yext ∩ ball y (w₁ : ℝ)) := by
          intro x hx y hy
          simpa [Cfact, hU] using h_centw1 x hx y hy
        have hres : ∀ x ∈ iUnionShade segs Yext, ∀ y ∈ iUnionShade segs Yext,
            volume (iUnionShade segs Yext ∩ ball x (rad C₀ a : ℝ)) ≤
              (centredMultConstant Cfact (8 * C₀ ^ 2) (Module.finrank ℝ E) : ENNReal) *
                volume (iUnionShade segs Yext ∩ ball y (rad C₀ a : ℝ)) := by
          exact centredMult hUUW hw1pos hw1_le_rad (C₁ := 8 * C₀ ^ 2) hA
            (C := Cfact) hcomp
        have hres' :
            volume (iUnionShade segs Yext ∩ ball x ((rad C₀ a : NNReal) : ℝ)) ≤
              (Ccent : ENNReal) *
                volume (iUnionShade segs Yext ∩ ball y ((rad C₀ a : NNReal) : ℝ)) := by
          simpa [Ccent, hdim] using hres x hx y hy
        exact le_trans hres'
          (mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.mpr hle_Ccent) zero_le)
      · have hUe : iUnionShade segs Yext = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        simp [hUe]
    denseBall := by
      intro p hp
      have hp' : p ∈ segs.filter (fun q : σ => ((k : NNReal) : ENNReal) *
          volume (Y q).shade ≤ volume (Yext q).shade) := by
        simpa [S] using hp
      have hmem : p ∈ segs := (Finset.mem_filter.mp hp').1
      have hcond : ((k : NNReal) : ENNReal) * volume (Y p).shade ≤ volume (Yext p).shade :=
        (Finset.mem_filter.mp hp').2
      have hδr1 : (δ : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast (hδa.trans (hab.trans hbr₁))
      have hroot := exists_ball_volume_inter_ge_of_subset hdim (C₀ := C₀) (hC₀ := hC₀)
        (δ := δ) (hδ := hδ) (r₁ := r₁) (hδr₁ := hδr1) η
        (K := (Y p).toConvexSpaceBody) (hthick := hthick p hmem)
        (D := D) (hD := hD) (cov := cov p) (ctr := covCtr)
        (hcover := hcov p hmem) (hmeets := hcovMeets p hmem)
        ((Y p).shade) ((Yext p).shade) (hZY := hsubYext p hmem) (hYK := (Y p).shade_subset)
        (c := k) (c₁ := c₁) (hY := hdens p hmem) (hZ := hcond)
      rcases hroot with ⟨i, hi, hs⟩
      refine ⟨covCtr i, ?_⟩
      calc
        (C : ENNReal)⁻¹ * (δ : ENNReal) ^ η * volume (ball (covCtr i) (δ : ℝ))
            = (C : ENNReal)⁻¹ * ((δ : ENNReal) ^ η * volume (ball (covCtr i) (δ : ℝ))) := by
              rw [mul_assoc]
        _ ≤ (db : ENNReal) * ((δ : ENNReal) ^ η * volume (ball (covCtr i) (δ : ℝ))) := by
              exact mul_le_mul_of_nonneg_right hdense_const zero_le
        _ = (db : ENNReal) * (δ : ENNReal) ^ η * volume (ball (covCtr i) (δ : ℝ)) := by
              rw [← mul_assoc]
        _ ≤ volume (ball (covCtr i) (δ : ℝ) ∩ (Yext p).shade) := by
              rw [Set.inter_comm]
              exact hs
    w := w
    w_le := hw_le
    shade_W_subset := by
      intro j hj
      rw [hUj j]
      dsimp [w]
      exact h_Wshade j hj
  }⟩

end Assemble

/-! ### The global shading -/

section Global

/-- **The global shading of (T1)** (blueprint `lem:ml2thinGlobalShading`).

The per-ball shadings `Y'_B` are amalgamated into a single global shading on `𝕋` by
`Y'(T) = ⨆_{B ∈ 𝔅} (Y(T) ∩ Y'_B(T_B) ∩ B̂)`, with `T_B` the unique parent segment of `T`
in `B`. This is a `⪆ 1` refinement of `(𝕋, Y)`, and `Y'(T) ∩ B̂ ⊆ Y'_B(T_B)`.

Insisting on a *single* global shading — rather than one refined separately in each ball —
is what allows the slab case to sum its estimate over all `B ∈ 𝔅`. -/
theorem globalShading {E : Type*} [MeasureSpace E]
    {ι β : Type*} (I : Finset ι) (bs : Finset β) (P : β → Set E)
    (hdisj : (bs : Set β).PairwiseDisjoint P) (hPmeas : ∀ B ∈ bs, MeasurableSet (P B))
    (Y : ι → Set E) (hYmeas : ∀ T ∈ I, MeasurableSet (Y T))
    (hcov : ∀ T ∈ I, Y T ⊆ ⋃ B ∈ bs, P B)
    (Z : β → ι → Set E) (hZ : ∀ B ∈ bs, ∀ T ∈ I, Z B T ⊆ P B)
    (hZmeas : ∀ B ∈ bs, ∀ T ∈ I, MeasurableSet (Z B T))
    {c : NNReal}
    (hlift : ∀ B ∈ bs, (c : ENNReal) * ∑ T ∈ I, volume (Y T ∩ P B) ≤
      ∑ T ∈ I, volume (Y T ∩ Z B T))
    (Y' : ι → Set E) (hY' : ∀ T ∈ I, Y' T = ⋃ B ∈ bs, Y T ∩ Z B T ∩ P B) :
    (∀ T ∈ I, Y' T ⊆ Y T) ∧
      (∀ T ∈ I, MeasurableSet (Y' T)) ∧
      (∀ B ∈ bs, ∀ T ∈ I, Y' T ∩ P B ⊆ Z B T) ∧
      (c : ENNReal) * ∑ T ∈ I, volume (Y T) ≤ ∑ T ∈ I, volume (Y' T) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  -- Conjunct 1: `Y' T ⊆ Y T`, termwise from the shape of the union.
  · intro T hT
    rw [hY' T hT]
    exact Set.iUnion₂_subset fun B hB =>
      Set.inter_subset_left.trans Set.inter_subset_left
  -- Conjunct 2: measurability, a finite union of intersections of measurable sets.
  · intro T hT
    rw [hY' T hT]
    exact Finset.measurableSet_biUnion bs fun B hB => by
      simpa [Set.inter_assoc] using
        (hYmeas T hT).inter ((hZmeas B hB T hT).inter (hPmeas B hB))
  -- Conjunct 3: `Y' T ∩ P B ⊆ Z B T`, from the pairwise disjointness of the pieces.
  · intro B hB T hT
    simpa [hY' T hT] using
      (amalgamateContainment bs P hdisj (fun B' => Z B' T) (Y T)).2 B hB
  -- Conjunct 4: the mass bound, exactly `amalgamateCost`.
  · let Y2 : β → ι → Set E := fun B T => Y T ∩ Z B T ∩ P B
    have hsub : ∀ B ∈ bs, ∀ T ∈ I, Y2 B T ⊆ Y T ∩ P B := by
      intro B hB T hT
      dsimp [Y2]
      exact Set.inter_subset_inter (Set.inter_subset_left) (Set.Subset.rfl : P B ⊆ P B)
    -- `Y2 B T = Y T ∩ Z B T`, since `Z B T ⊆ P B`; hence `hlift` applies verbatim.
    have hZvol : ∀ B ∈ bs, ∀ T ∈ I, volume (Y2 B T) = volume (Y T ∩ Z B T) := by
      intro B hB T hT
      dsimp [Y2]
      rw [Set.inter_eq_self_of_subset_left (Set.inter_subset_right.trans (hZ B hB T hT))]
    have hlift' : ∀ B ∈ bs, (c : ENNReal) * ∑ T ∈ I, volume (Y T ∩ P B) ≤
        ∑ T ∈ I, volume (Y2 B T) := by
      intro B hB
      rw [Finset.sum_congr rfl (fun T hT => hZvol B hB T hT)]
      exact hlift B hB
    exact amalgamateCost I bs P hdisj hPmeas Y hcov Y2 hsub hlift' Y' (by
      intro T hT
      dsimp [Y2]
      exact hY' T hT)

/-- **The reverse containment of (T1)** (blueprint `lem:ml2thinLocalToGlobal`).

For *every* segment `T_B ∈ 𝕋_B` — not only for those in `𝒮_B` — the per-ball shading
`Y'_B(T_B)` is covered by the global shadings of the tubes of `𝕋(T_B)`, whence
`U(𝕋_B, Y'_B) ⊆ U(𝕋, Y')`. This is where it matters that `Y'_B` was not truncated off
`𝒮_B`: for a truncated shading the statement would be vacuous and the unions appearing in
(T4) and (T6) would have shrunk.

The statement is purely set-theoretic: no measure on `E` is involved. -/
theorem localToGlobal {E ι β σ : Type*} (I : Finset ι) (bs : Finset β) (P : β → Set E)
    (Y : ι → Set E) (segs : β → Finset σ) (fam : σ → Finset ι) (Zb : σ → Set E)
    (hfam : ∀ B ∈ bs, ∀ p ∈ segs B, fam p ⊆ I)
    (hZb_piece : ∀ B ∈ bs, ∀ p ∈ segs B, Zb p ⊆ P B)
    (hZb_cov : ∀ B ∈ bs, ∀ p ∈ segs B, Zb p ⊆ ⋃ T ∈ fam p, Y T)
    (Z : β → ι → Set E)
    (hZ : ∀ B ∈ bs, ∀ p ∈ segs B, ∀ T ∈ fam p, Z B T = Zb p)
    (Y' : ι → Set E) (hY' : ∀ T ∈ I, Y' T = ⋃ B ∈ bs, Y T ∩ Z B T ∩ P B) :
    ∀ B ∈ bs, ∀ p ∈ segs B, Zb p ⊆ ⋃ T ∈ fam p, Y' T := by
  intro B hB p hp x hx
  rcases Set.mem_iUnion.mp (hZb_cov B hB p hp hx) with ⟨T, hTcov⟩
  rcases Set.mem_iUnion.mp hTcov with ⟨hTin, hxYT⟩
  have hTinI : T ∈ I := hfam B hB p hp hTin
  refine Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨hTin, ?_⟩⟩
  rw [hY' T hTinI]
  refine Set.mem_iUnion.mpr ⟨B, Set.mem_iUnion.mpr ⟨hB, ⟨⟨hxYT, ?_⟩, hZb_piece B hB p hp hx⟩⟩⟩
  rw [hZ B hB p hp T hTin]
  exact hx

end Global

/-! ### Assembling the configuration -/

section Exists

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Constant in Lemma `lem:ml2thinsetupexists`.**

The comparison constant of the data produced by `Kakeya.ThinCase.thinSetupExists`. Each ball
contributes the loss `perBallConstant C₀ CF c₁ Ccore D` of `Kakeya.ThinCase.perBall`, and the
amalgamation `Kakeya.ThinCase.amalgamateCost` of the per-ball refinements composes it with
itself once, since `Kakeya.ThinCase.lift` is applied with `c = κ = (perBallConstant …)⁻¹`;
this is the factor `perBallConstant C₀ CF c₁ Ccore D ^ 2`.

The remaining factor `Cm ^ 2` is the loss of `Kakeya.ThinCase.lift` itself: the passage from
the per-ball shadings to the global one goes through the fibre count of
`Kakeya.ThinCase.liftFibre`, which is used twice — once for `Y_B` and once for `Y'_B` — and
each use costs the comparison constant `Cm` of the (C5) fibre-count hypothesis
`|𝕋(T_B)_Y(x)| ≈ m`. This dependence is *not* removable and must not be hidden inside a
`⪆`: the fibre count is what relates the mass of the global shading on the piece `B̂` to the
mass of the per-ball shading, and without a bound on it the amalgamated refinement carries no
information at all. The displayed value is otherwise provisional. -/
noncomputable def thinSetupConstant (C₀ CF c₁ Ccore : NNReal) (D : ℕ) (Cm : NNReal) : NNReal :=
  perBallConstant C₀ CF c₁ Ccore D ^ 2 * Cm ^ 2

lemma one_le_thinSetupConstant {C₀ CF c₁ Ccore Cm : NNReal} {D : ℕ} (hCm : 1 ≤ Cm) :
    1 ≤ thinSetupConstant C₀ CF c₁ Ccore D Cm := by
  change (1 : NNReal) ≤ perBallConstant C₀ CF c₁ Ccore D ^ 2 * Cm ^ 2
  simpa using mul_le_mul' (one_le_pow₀ one_le_perBallConstant) (one_le_pow₀ hCm)

open scoped Classical in
/-- **The thin-case configuration can be arranged** (blueprint `lem:ml2thinsetupexists`).

Assuming Configuration `hyp:ml2setup` — here spelled out as the per-ball data of (C3),
(C4), (C5) together with the subordinate partition of (C2) — there is data realizing
Configuration `hyp:ml2thinsetup` for the *same* pair `(𝕋, Y)`: a single global shading `Y'`
on `𝕋` which is a `⪆ 1` refinement of `Y`, and, for every ball `B ∈ 𝔅`, a
`Kakeya.ThinCase.ThinBall` with the *same* comparison constant, compatible with `Y'` in both
directions.

The pair `(𝕋, Y)` itself is not modified: `Y'` is auxiliary data attached to it.

Two features of the statement matter. First, the constant is the *explicit*
`thinSetupConstant C₀ CF c₁ D`, so it is one and the same in every ball and the losses in the
different balls do not compound; an existentially quantified constant would be allowed to
depend on the ball, and a bound with `B`-dependent constants would be worthless when the
per-ball refinements are amalgamated. (This is the same point as in the docstring of
`Kakeya.ThinCase.factoringApply`.) Second, the `δ`-ball estimate (T5) is read off *after* the
factoring proposition has been applied, so that no subsequent shrinking of the shading can
invalidate it; being a pure averaging statement it leaves (T1)–(T4) and (T6) untouched.

The thin-case hypothesis `a ≤ δ^{1-τ}` of blueprint Definition `hyp:ml2thinsetup` is *not*
assumed: none of (T1)–(T6) uses it. It first enters in
`Kakeya.ThinCase.unionLower_thin` and `Kakeya.ThinCase.transfer_thin`, where it is a
hypothesis.

As in `Kakeya.ThinCase.perBall`, the positivity `0 < c₁` of the density constant of (C5) is
essential: with `c₁ = 0` the hypothesis `hdens` is vacuous and the `ThinBall` demanded by the
conclusion cannot exist for an everywhere unshaded `Y`. The hypothesis `hdims` is likewise
the one of `Kakeya.ThinCase.perBall`, quantified over the balls.

The (C5) fibre-count data — the scale `m`, the comparison constant `Cm ≥ 1` and the
hypothesis `hfibre` asserting `|𝕋(T_B)_Y(x)| ≈ m` on `Y_B(T_B)` — is not decoration. The
refinement conclusion is reached only through `Kakeya.ThinCase.lift`, hence through
`Kakeya.ThinCase.liftFibre`, and without a bound on the fibre count it is *false*: a segment
`T_B ∉ 𝒮_B` whose family `𝕋(T_B)` is arbitrarily large contributes arbitrarily much to
`∑_T |Y(T)|` while `Y'` gains nothing from it, so the loss in the third conjunct of the
conclusion is unbounded. Accordingly `Cm` appears explicitly in
`Kakeya.ThinCase.thinSetupConstant`.

The segment-mass inequality (T7) of Configuration `hyp:ml2thinsetup` is not produced here: it is
a *theorem* of the data this lemma returns, `Kakeya.VeryNotSticky.segment_mass_of_compat`. The former pass-through `{mass}`/`hsegmass`, a consumer-dead binder whose
sole caller instantiated it at `mass := 0`, was removed by pack F14; the
statements with and without it are equivalent. The `ThinBall` family is produced as a single
existential rather than one per ball because (T7) is a statement about all the balls at once. -/
theorem thinSetupExists (hdim : Module.finrank ℝ E = 3)
    {ι bι σ ω : Type*} [DecidableEq ω]
    -- (C1) the global family `(𝕋, Y)`
    (I : Finset ι) (Yg : ι → Set E) (hYgmeas : ∀ T ∈ I, MeasurableSet (Yg T))
    -- (C2) the balls `𝔅` and the subordinate partition `(B̂)`
    (bs : Finset bι) (P : bι → Set E)
    (hPdisj : (bs : Set bι).PairwiseDisjoint P) (hPmeas : ∀ B ∈ bs, MeasurableSet (P B))
    (hPcov : ∀ T ∈ I, Yg T ⊆ ⋃ B ∈ bs, P B)
    -- (C3) the tube segments `𝕋_B` with the shading `Y_B` and the families `𝕋(T_B)`
    (segs : bι → Finset σ) (Y : σ → ShadedBody E) (fam : σ → Finset ι)
    (hsegs : ∀ B ∈ bs, (segs B).Nonempty)
    (hfam : ∀ B ∈ bs, ∀ p ∈ segs B, fam p ⊆ I)
    (hfam_disj : ∀ B ∈ bs, (segs B : Set σ).Pairwise fun p q => Disjoint (fam p) (fam q))
    -- (C3) the shading lives in the piece `B̂`; the conjunct `(Y p).shade ⊆ (Y p).carrier` is
    -- omitted, being `ShadedBody.shade_subset`
    (hYb_piece : ∀ B ∈ bs, ∀ p ∈ segs B, (Y p).shade ⊆ P B)
    -- (C4) the factoring `𝕋_B = ⨆_{W ∈ 𝕎_B} 𝕋_{B,W}` at the single pair of scales `(a, b)`
    (bodies : bι → Finset ω) (Wb : ω → ConvexSpaceBody E) (blk : σ → ω)
    {δ a b r₁ w₁ : NNReal} {η : ℝ} {C₀ CF c₁ Ccore : NNReal} {D : ℕ}
    (hC₀ : 1 ≤ C₀) (hCF : 1 ≤ CF) (hc₁ : 0 < c₁) (hD : 1 ≤ D)
    (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b) (hbr₁ : b ≤ r₁)
    -- the `w₁` window and the core envelope of `Kakeya.ThinCase.factoringApply`, quantified
    -- over the balls: a *single* `Ccore` serves every ball, which is the ball-uniformity the
    -- amalgamation of the per-ball refinements needs. Cardinality-independence is *not* needed
    -- and is not available: `ThinConfig.tb` takes one `C` for all balls and `ThinBall.mono`
    -- only weakens upward.
    (hδw₁ : δ ≤ w₁) (hw₁one : w₁ ≤ 1)
    -- `η` is a loss exponent; see the binder on `Kakeya.ThinCase.factoringApply`.
    (hη : (0:ℝ) ≤ η)
    -- the localisation of the bodies of each ball, passed straight to
    -- `Kakeya.ThinCase.perBall`. `Kakeya.VeryNotSticky.exists_thinConfig` discharges it from
    -- `Kakeya.VeryNotSticky.BallData.bodies_subset_ball` together with `r₁ = δ^exscal ≤ 1`.
    (hloc : ∀ B ∈ bs, ∃ z : E, ∀ j ∈ bodies B, (Wb j).carrier ⊆ Metric.closedBall z 1)
    (hCcore2 : 2 ≤ Ccore)
    (hCcoreRef : ∀ B ∈ bs,
      (ShadedBody.outerFactoringFamily_refinement.c 3 (segs B).card δ)⁻¹ ≤ Ccore)
    (hCcoreMult : ∀ B ∈ bs,
      ShadedBody.outerFactoringFamily_outerConstMultFat.c 3 (bodies B).card δ ≤ Ccore)
    (hCcoreDyad : ∀ B ∈ bs, ((Nat.log 2 (bodies B).card + 1 : ℕ) : NNReal) ≤ Ccore)
    -- the fifth envelope bound of `Kakeya.ThinCase.factoringApply`; it does not depend on the
    -- ball, `CF` being one constant for all of them
    (hCcoreFrost : ((Nat.log 2 ⌈CF⌉₊ + 1 : ℕ) : NNReal) ≤ Ccore)
    -- the two scale-dependent envelope bounds at the discretization scale `δ / C₀` of the
    -- segments; see `Kakeya.ThinCase.perBall`
    (hCcoreRef₀ : ∀ B ∈ bs,
      (ShadedBody.outerFactoringFamily_refinement.c 3 (segs B).card (δ / C₀))⁻¹ ≤ Ccore)
    (hCcoreMult₀ : ∀ B ∈ bs,
      ShadedBody.outerFactoringFamily_outerConstMultFat.c 3 (bodies B).card (δ / C₀) ≤ Ccore)
    -- the eighth envelope bound of `Kakeya.ThinCase.factoringApply`; see its docstring
    (hCcoreNet : ∀ B ∈ bs, thinEnvelopeTerm 3 (segs B).card (bodies B).card CF w₁ ≤ Ccore)
    (hblk : ∀ B ∈ bs, ∀ p ∈ segs B, blk p ∈ bodies B)
    (hle : ∀ B ∈ bs, ∀ p ∈ segs B, (Y p).toConvexSpaceBody ≤ Wb (blk p))
    (hthick : ∀ B ∈ bs, ∀ p ∈ segs B, HasThicknesses (Y p).carrier C₀ ![r₁, δ, δ])
    -- (C3) the segments of a ball have *comparable* affine thicknesses, in the exact form
    -- `ShadedBody.factoringAndMultPropCombined` demands
    (hdims : ∀ B ∈ bs, ∀ p ∈ segs B, ∀ q ∈ segs B,
      Metric.thickness ℝ (Y p).carrier ≤ 2 • Metric.thickness ℝ (Y q).carrier)
    -- the bodies of (C4) have affine thicknesses `∼ (r₁, b, a)`: the middle scale `b` is a
    -- genuinely separate parameter, and it is its size that later splits the thin case into
    -- the slab and non-slab cases
    (hbody : ∀ B ∈ bs, ∀ j ∈ bodies B, HasThicknesses (Wb j).carrier C₀ ![r₁, b, a])
    (hw₁ : ∀ B ∈ bs, ∀ j ∈ bodies B,
      Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1) ≤ 2 * w₁ ∧
        (w₁ : ℝ) ≤ 2 * Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1))
    (hFr : ∀ B ∈ bs, ∀ j ∈ bodies B,
      ConvexSpaceBody.IsFrostmanIn ((segs B).filter fun p => blk p = j)
        (fun p => (Y p).toConvexSpaceBody) (Wb j) CF)
    -- (C5) the uniformity properties
    (hdens : ∀ B ∈ bs, ∀ p ∈ segs B,
      (c₁ : ENNReal) * (δ : ENNReal) ^ η * volume (Y p).carrier ≤ volume (Y p).shade)
    (hparent : ∀ B ∈ bs, ∀ T ∈ I, (Yg T ∩ P B).Nonempty → ∃ p ∈ segs B, T ∈ fam p)
    (hinto : ∀ B ∈ bs, ∀ p ∈ segs B, ∀ T ∈ fam p, Yg T ∩ P B ⊆ (Y p).shade)
    (hback : ∀ B ∈ bs, ∀ p ∈ segs B, (Y p).shade ⊆ ⋃ T ∈ fam p, Yg T)
    -- (C5) the fibre count `|𝕋(T_B)_Y(x)| ≈ m` on `Y_B(T_B)`, with a single scale `m` and a
    -- single comparison constant `Cm` for every ball; this is what `Kakeya.ThinCase.lift`
    -- consumes, and it is what makes the refinement conclusion below true
    {m Cm : NNReal} (hCm : 1 ≤ Cm)
    (hfibre : ∀ B ∈ bs, ∀ p ∈ segs B, ∀ x ∈ (Y p).shade,
      (m : ENNReal) ≤ Cm * {T ∈ fam p | x ∈ Yg T}.card ∧
        ({T ∈ fam p | x ∈ Yg T}.card : ENNReal) ≤ Cm * m)
    -- the `δ`-ball covers of (T5)
    {γ : Type*} (cov : σ → Finset γ) (covCtr : γ → E)
    (hcov : ∀ B ∈ bs, ∀ p ∈ segs B,
      IsBoundedlyOverlappingCover (cov p) covCtr (fun _ => (δ : ℝ)) D (Y p).carrier)
    (hcovMeets : ∀ B ∈ bs, ∀ p ∈ segs B, ∀ i ∈ cov p,
      (ball (covCtr i) (δ : ℝ) ∩ (Y p).carrier).Nonempty) :
    ∃ Y' : ι → Set E,
      -- `(𝕋, Y')` is a `⪆ 1` refinement of `(𝕋, Y)`
      (∀ T ∈ I, Y' T ⊆ Yg T) ∧
      (∀ T ∈ I, MeasurableSet (Y' T)) ∧
      ((thinSetupConstant C₀ CF c₁ Ccore D Cm : ENNReal)⁻¹ * ∑ T ∈ I, volume (Yg T) ≤
        ∑ T ∈ I, volume (Y' T)) ∧
      -- for each ball, the thin-case data, compatible with `Y'` in both directions
      ∃ tb : (∀ B ∈ bs, ThinBall (thinSetupConstant C₀ CF c₁ Ccore D Cm) C₀
          (segs B) Y (bodies B) Wb blk δ a η),
        (∀ (B : bι) (hB : B ∈ bs),
          (∀ p ∈ segs B, ∀ T ∈ fam p, Y' T ∩ (Y p).carrier ∩ P B ⊆ ((tb B hB).Y' p).shade) ∧
          (∀ p ∈ segs B, ((tb B hB).Y' p).shade ⊆ ⋃ T ∈ fam p, Y' T)) := by
  classical
  let cPB : NNReal := perBallConstant C₀ CF c₁ Ccore D
  let cTS : NNReal := thinSetupConstant C₀ CF c₁ Ccore D Cm
  -- (1) Per-ball production at `cPB`, via `perBall`.
  let tbf : ∀ B ∈ bs, ThinBall cPB C₀ (segs B) Y (bodies B) Wb blk δ a η :=
    fun B hB => Classical.choice (perBall hdim (segs B) Y (bodies B) Wb blk (δ := δ) (a := a)
      (b := b) (r₁ := r₁) (w₁ := w₁) (η := η) (C₀ := C₀) (CF := CF) (c₁ := c₁)
      (Ccore := Ccore) (D := D)
      { one_le_C₀ := hC₀, one_le_CF := hCF, c₁_pos := hc₁, δ_pos := hδ, δ_le_a := hδa
        a_le_b := hab, b_le_r₁ := hbr₁, segs_nonempty := hsegs B hB, blk_mem := hblk B hB
        le_block := hle B hB, thick := hthick B hB, dims := hdims B hB, body := hbody B hB
        width := hw₁ B hB, frostman := hFr B hB, dens := hdens B hB }
      { γ := γ, cov := cov, ctr := covCtr, one_le_D := hD, isCover := hcov B hB
        meets := hcovMeets B hB }
      hδw₁ hw₁one hη (hloc B hB) hCcore2 (hCcoreRef B hB) (hCcoreMult B hB) (hCcoreDyad B hB)
      hCcoreFrost (hCcoreRef₀ B hB) (hCcoreMult₀ B hB) (hCcoreNet B hB))
  -- (2) `cPB ≤ cTS`, and the weakening of `ThinBall` in its comparison constant.
  have hpb_le_ts : cPB ≤ cTS := by
    dsimp [cTS, cPB, thinSetupConstant]
    calc
      perBallConstant C₀ CF c₁ Ccore D ≤ perBallConstant C₀ CF c₁ Ccore D * Cm ^ 2 := by
        exact le_mul_of_one_le_right
          (by positivity : 0 ≤ (perBallConstant C₀ CF c₁ Ccore D : NNReal))
          (one_le_pow₀ hCm)
      _ ≤ perBallConstant C₀ CF c₁ Ccore D ^ 2 * Cm ^ 2 := by
        have hle : perBallConstant C₀ CF c₁ Ccore D ≤ perBallConstant C₀ CF c₁ Ccore D ^ 2 := by
          rw [pow_two]
          exact le_mul_of_one_le_left
            (by positivity : 0 ≤ (perBallConstant C₀ CF c₁ Ccore D : NNReal))
            (one_le_perBallConstant (C₀ := C₀) (CF := CF) (c₁ := c₁) (Ccore := Ccore) (D := D))
        exact mul_le_mul' hle le_rfl
      _ = thinSetupConstant C₀ CF c₁ Ccore D Cm := by rw [thinSetupConstant]
  let tbw : ∀ B ∈ bs, ThinBall cTS C₀ (segs B) Y (bodies B) Wb blk δ a η :=
    fun B hB => ThinBall.mono hpb_le_ts (tbf B hB)
  -- (3) The global shading.
  let Z : bι → ι → Set E := fun B T => if hB : B ∈ bs then
    ⋃ p ∈ segs B, if T ∈ fam p then ((tbw B hB).Y' p).shade else ∅ else ∅
  let Y' : ι → Set E := fun T => ⋃ B ∈ bs, Yg T ∩ Z B T ∩ P B
  have hbY' : ∀ T ∈ I, Y' T = ⋃ B ∈ bs, Yg T ∩ Z B T ∩ P B := by
    intro T hT
    rfl
  -- Uniqueness of the parent segment of a tube in a ball: the families `fam p` are pairwise
  -- disjoint on `segs B`, so a tube meeting both `fam p` and `fam q` forces `p = q`.
  have huniq : ∀ B ∈ bs, ∀ p ∈ segs B, ∀ q ∈ segs B, ∀ T : ι,
      T ∈ fam p → T ∈ fam q → p = q := by
    intro B hB p hp q hq T hTp hTq
    by_contra hpq
    exact (Finset.disjoint_left.mp (hfam_disj B hB hp hq hpq) hTp hTq)
  have hcPB0 : (cPB : NNReal) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one
      (one_le_perBallConstant (C₀ := C₀) (CF := CF) (c₁ := c₁) (Ccore := Ccore) (D := D)))
  have hcm0 : (Cm : NNReal) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hCm)
  have hcts0 : (cTS : NNReal) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_thinSetupConstant (hCm := hCm)))
  have hcPBco0 : (cPB : ENNReal) ≠ 0 := ne_of_gt (ENNReal.coe_pos.mpr
    (lt_of_lt_of_le zero_lt_one
      (one_le_perBallConstant (C₀ := C₀) (CF := CF) (c₁ := c₁) (Ccore := Ccore) (D := D))))
  have hcmco0 : (Cm : ENNReal) ≠ 0 := ne_of_gt (ENNReal.coe_pos.mpr
    (lt_of_lt_of_le zero_lt_one hCm))
  have hctsco0 : (cTS : ENNReal) ≠ 0 := ne_of_gt (ENNReal.coe_pos.mpr
    (lt_of_lt_of_le zero_lt_one (one_le_thinSetupConstant (hCm := hCm))))
  /- `Z B T` is the shading of the unique parent segment `p`: for `T ∈ fam p` it is
  `((tb B) .Y' p).shade`, and it is `∅` when no `p ∈ segs B` has `T ∈ fam p`. -/
  have hZ_eq : ∀ {B : bι} (hB : B ∈ bs), ∀ p ∈ segs B, ∀ T ∈ fam p,
      Z B T = ((tbw B hB).Y' p).shade := by
    intro B hB p hp T hT
    change (if hB : B ∈ bs then ⋃ p ∈ segs B,
        (if T ∈ fam p then ((tbw B hB).Y' p).shade else ∅) else ∅) = ((tbw B hB).Y' p).shade
    simp only [dif_pos hB]
    apply Set.Subset.antisymm
    · intro x hx
      rcases Set.mem_iUnion₂.mp hx with ⟨q, hq, hxq⟩
      by_cases hTq : T ∈ fam q
      · have hx' : x ∈ ((tbw B hB).Y' q).shade := by simpa [hTq] using hxq
        have hqp : q = p := (huniq B hB p hp q hq T hT hTq).symm
        simpa [hqp] using hx'
      · simp [hTq] at hxq
    · intro x hx
      exact Set.mem_iUnion₂.mpr ⟨p, hp, by simpa [hT] using hx⟩
  /- If no `p ∈ segs B` has `T ∈ fam p`, then `Z B T` is empty. -/
  have hZ_empty : ∀ {B : bι} (hB : B ∈ bs) (T : ι), (∀ p ∈ segs B, T ∉ fam p) → Z B T = ∅ := by
    intro B hB T hnone
    change (if hB' : B ∈ bs then ⋃ p ∈ segs B,
      (if T ∈ fam p then ((tbw B hB').Y' p).shade else ∅) else ∅) = ∅
    simp only [dif_pos hB, iUnion_eq_empty, ite_eq_right_iff]
    intro i hi hTi
    exact absurd hTi (hnone i hi)
  have hZ_sup : ∀ {B : bι} (hB : B ∈ bs), ∀ p ∈ segs B, ∀ T ∈ fam p,
      ((tbw B hB).Y' p).shade ⊆ Z B T := by
    intro B hB p hp T hT x hx
    rw [hZ_eq hB p hp T hT]
    exact hx
  have hZ_sub : ∀ {B : bι} (hB : B ∈ bs), ∀ T ∈ I, Z B T ⊆ P B := by
    intro B hB T hT x hx
    by_cases hpar : ∃ p ∈ segs B, T ∈ fam p
    · rcases hpar with ⟨p, hp, hTfam⟩
      rw [hZ_eq hB p hp T hTfam] at hx
      exact hYb_piece B hB p hp ((tbw B hB).shade_Y'_subset p hp hx)
    · have hpar' : ∀ p ∈ segs B, T ∉ fam p := by
        intro p hp hTfam
        exact hpar ⟨p, hp, hTfam⟩
      rw [hZ_empty hB T hpar'] at hx
      exact hx.elim
  have hZ_meas : ∀ {B : bι} (hB : B ∈ bs), ∀ T ∈ I, MeasurableSet (Z B T) := by
    intro B hB T hT
    by_cases hpar : ∃ p ∈ segs B, T ∈ fam p
    · rcases hpar with ⟨p, hp, hTp⟩
      rw [hZ_eq hB p hp T hTp]
      exact ((tbw B hB).Y' p).measurableSet_shade
    · have hpar' : ∀ p ∈ segs B, T ∉ fam p := by
        intro p hp hTp
        exact hpar ⟨p, hp, hTp⟩
      rw [hZ_empty hB T hpar']
      exact MeasurableSet.empty
  -- (4) The fibre-based `hlift` hypothesis for `globalShading`.
  have hlift_gs : ∀ B ∈ bs, ((cTS⁻¹ : NNReal) : ENNReal) * ∑ T ∈ I, volume (Yg T ∩ P B) ≤
      ∑ T ∈ I, volume (Yg T ∩ Z B T) := by
    intro B hB
    let Ssum : ENNReal := ∑ T ∈ I, volume (Yg T ∩ P B)
    let Zsum : ENNReal := ∑ T ∈ I, volume (Yg T ∩ Z B T)
    -- `Y2 := Yg T ∩ Z B T` matches `Zb := ((tbf B hB).Y' p).shade` on the parent segment.
    have hY2 : ∀ p ∈ segs B, ∀ T ∈ fam p,
        Yg T ∩ Z B T = Yg T ∩ ((tbf B hB).Y' p).shade := by
      intro p hp T hT
      rw [hZ_eq hB p hp T hT]
      rfl
    -- On a tube with no parent segment, `Z B T = ∅`, so the lifted shading is empty.
    have hY2_empty : ∀ T ∈ I, (∀ p ∈ segs B, T ∉ fam p) → Yg T ∩ Z B T = ∅ := by
      intro T hT hnone
      rw [hZ_empty hB T hnone]
      simp
    -- Dividing a bound `a ≤ cPB * b` by `cPB` (which costs nothing, `cPB⁻¹ * cPB = 1`).
    have hdiv : ∀ a b : ENNReal, a ≤ (cPB : ENNReal) * b →
        ((cPB⁻¹ : NNReal) : ENNReal) * a ≤ b := by
      intro a b hab
      calc
        ((cPB⁻¹ : NNReal) : ENNReal) * a
            ≤ ((cPB⁻¹ : NNReal) : ENNReal) * ((cPB : ENNReal) * b) :=
              mul_le_mul_of_nonneg_left hab zero_le
        _ = (((cPB⁻¹ : NNReal) : ENNReal) * (cPB : ENNReal)) * b := by rw [mul_assoc]
        _ = 1 * b := by
              congr 1
              rw [ENNReal.coe_inv hcPB0]
              exact ENNReal.inv_mul_cancel hcPBco0 (ne_top_of_lt (ENNReal.coe_lt_top (r := cPB)))
        _ = b := by simp
    have hmass : ((cPB⁻¹ : NNReal) : ENNReal) * ∑ p ∈ segs B, volume ((Y p).shade) ≤
        ∑ p ∈ (tbf B hB).S, volume ((Y p).shade) := by
      exact hdiv (∑ p ∈ segs B, volume ((Y p).shade))
        (∑ p ∈ (tbf B hB).S, volume ((Y p).shade)) (tbf B hB).mass_S
    have hterm : ∀ p ∈ (tbf B hB).S,
        ((cPB⁻¹ : NNReal) : ENNReal) * volume ((Y p).shade) ≤
          volume (((tbf B hB).Y' p).shade) := by
      intro p hp
      exact hdiv (volume ((Y p).shade)) (volume (((tbf B hB).Y' p).shade))
        ((tbf B hB).refine_S p hp)
    have hfibreB : ∀ p ∈ segs B, ∀ x ∈ (Y p).shade,
        (m : ENNReal) ≤ (Cm : ENNReal) * {T ∈ fam p | x ∈ Yg T}.card ∧
          ({T ∈ fam p | x ∈ Yg T}.card : ENNReal) ≤ (Cm : ENNReal) * m :=
      hfibre B hB
    have hLift : ((cPB⁻¹ * cPB⁻¹ : NNReal) : ENNReal) * Ssum ≤ (Cm : ENNReal)^2 * Zsum := by
      simpa [Ssum, Zsum] using
        (lift I Yg (P B) (segs B) (fun p => (Y p).shade)
          (fun p => ((tbf B hB).Y' p).shade) fam (fun T => Yg T ∩ Z B T)
          (hPmeas B hB) hYgmeas
          (fun p hp => (Y p).measurableSet_shade)
          (fun p hp => ((tbf B hB).Y' p).measurableSet_shade)
          (fun p hp => hfam B hB p hp) (hfam_disj B hB)
          (fun p hp => (tbf B hB).shade_Y'_subset p hp)
          (fun p hp => hYb_piece B hB p hp)
          (fun T hT => hparent B hB T hT) (fun p hp T hT => hinto B hB p hp T hT)
          hY2 hY2_empty hCm hfibreB
          (c := cPB⁻¹) (κ := cPB⁻¹) (S := (tbf B hB).S) (hS := (tbf B hB).S_subset)
          hmass hterm)
    let pc : ENNReal := ((cPB⁻¹ : NNReal) : ENNReal)
    let qc : ENNReal := ((Cm⁻¹ : NNReal) : ENNReal)
    have hLift' : pc * pc * Ssum ≤ (Cm : ENNReal)^2 * Zsum := by
      simpa [pc, ENNReal.coe_mul] using hLift
    have hqc : qc * qc = (Cm : ENNReal)⁻¹ * (Cm : ENNReal)⁻¹ := by
      dsimp [qc]
      rw [ENNReal.coe_inv hcm0]
    have hcmPair : (Cm : ENNReal)⁻¹ * (Cm : ENNReal) = 1 :=
      ENNReal.inv_mul_cancel hcmco0 (ne_top_of_lt (ENNReal.coe_lt_top (r := Cm)))
    have hqmul : qc * qc * ((Cm : ENNReal)^2 * Zsum) = Zsum := by
      rw [hqc, pow_two]
      calc
        ((Cm : ENNReal)⁻¹ * (Cm : ENNReal)⁻¹) * ((Cm : ENNReal) * (Cm : ENNReal) * Zsum)
            = ((Cm : ENNReal)⁻¹ * Cm) * ((Cm : ENNReal)⁻¹ * Cm) * Zsum := by ring
        _ = 1 * 1 * Zsum := by rw [hcmPair]
        _ = Zsum := by simp
    -- `cTS = cPB ^ 2 * Cm ^ 2`, so `cTS⁻¹ = cPB⁻¹ * cPB⁻¹ * Cm⁻¹ * Cm⁻¹`.
    have hcts_def : (cTS⁻¹ : NNReal) = cPB⁻¹ * cPB⁻¹ * Cm⁻¹ * Cm⁻¹ := by
      dsimp [cTS, cPB, thinSetupConstant]
      rw [pow_two, pow_two]
      field_simp [hcPB0, hcm0]
    calc
      ((cTS⁻¹ : NNReal) : ENNReal) * Ssum
          = ((cPB⁻¹ * cPB⁻¹ * Cm⁻¹ * Cm⁻¹ : NNReal) : ENNReal) * Ssum := by rw [hcts_def]
      _ = pc * pc * qc * qc * Ssum := by
            simp [pc, qc, ENNReal.coe_mul, mul_assoc, mul_comm]
      _ = qc * qc * (pc * pc * Ssum) := by ring
      _ ≤ qc * qc * ((Cm : ENNReal)^2 * Zsum) :=
            mul_le_mul_of_nonneg_left hLift' (show 0 ≤ qc * qc by positivity)
      _ = Zsum := hqmul
  have hcoinv : (cTS : ENNReal)⁻¹ = ((cTS⁻¹ : NNReal) : ENNReal) := by
    simpa using (ENNReal.coe_inv hcts0).symm
  have hgs := globalShading I bs P hPdisj hPmeas Yg hYgmeas hPcov Z
    (fun B hB => hZ_sub hB) (fun B hB => hZ_meas hB)
    (c := cTS⁻¹) hlift_gs Y' hbY'
  -- (5) Compatibility in both directions, from `hgs` and the shape of `Y'`.
  have hfwd : ∀ {B : bι} (hB : B ∈ bs), ∀ p ∈ segs B, ∀ T ∈ fam p,
      Y' T ∩ (Y p).carrier ∩ P B ⊆ ((tbw B hB).Y' p).shade := by
    intro B hB p hp T hT x hx
    have hTI : T ∈ I := hfam B hB p hp hT
    have hxY'P : x ∈ Y' T ∩ P B := ⟨hx.1.1, hx.2⟩
    have hxZ : x ∈ Z B T := hgs.2.2.1 B hB T hTI hxY'P
    simpa [hZ_eq hB p hp T hT] using hxZ
  have hbwd : ∀ {B : bι} (hB : B ∈ bs), ∀ p ∈ segs B,
      ((tbw B hB).Y' p).shade ⊆ ⋃ T ∈ fam p, Y' T := by
    intro B hB p hp x hx
    have hxY : x ∈ (Y p).shade := (tbw B hB).shade_Y'_subset p hp hx
    have hxYg : x ∈ ⋃ T ∈ fam p, Yg T := hback B hB p hp hxY
    rcases Set.mem_iUnion₂.mp hxYg with ⟨T, hT, hxT⟩
    have hTI : T ∈ I := hfam B hB p hp hT
    refine Set.mem_iUnion₂.mpr ⟨T, hT, ?_⟩
    rw [hbY' T hTI]
    refine Set.mem_iUnion₂.mpr ⟨B, hB, ?_⟩
    refine ⟨⟨hxT, hZ_sup hB p hp T hT hx⟩, hYb_piece B hB p hp hxY⟩
  -- (6) Assemble.
  refine ⟨Y', ?_, ?_, ?_, ⟨tbw, ?_⟩⟩
  · exact hgs.1
  · exact hgs.2.1
  · change (cTS : ENNReal)⁻¹ * (∑ T ∈ I, volume (Yg T)) ≤ ∑ T ∈ I, volume (Y' T)
    rw [hcoinv]
    exact hgs.2.2.2
  · intro B hB
    exact ⟨hfwd hB, hbwd hB⟩

end Exists

end Kakeya.ThinCase
namespace Kakeya.ThinCase

open MeasureTheory Metric Set ShadedBody

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {σ ω : Type*} [DecidableEq ω]

/-- Canonical outer shaded body used by the structural clauses of `factoringApply`. -/
noncomputable def blockOuterBodyCandidate (segs' : Finset σ) (Y' : σ → ShadedBody E)
    (Wb : ω → ConvexSpaceBody E) (blk : σ → ω)
    (hle : ∀ p ∈ segs', (Y' p).toConvexSpaceBody ≤ Wb (blk p)) (j : ω) : ShadedBody E where
  toConvexSpaceBody := (Wb j).cthickening (Wb j).scale
  shade := iUnionShade (segs'.filter fun p => blk p = j) Y'
  measurableSet_shade :=
    Finset.measurableSet_biUnion _ fun p _ => (Y' p).measurableSet_shade
  shade_subset := by
    refine Set.iUnion₂_subset fun p hp => ?_
    obtain ⟨hpsegs, hpblk⟩ := Finset.mem_filter.mp hp
    have hcar : (Y' p).carrier ⊆ (Wb j).carrier := by
      have h := hle p hpsegs
      rw [hpblk] at h
      exact h
    exact ((Y' p).shade_subset.trans hcar).trans (Metric.self_subset_cthickening _)

variable {segs' : Finset σ} {Y' : σ → ShadedBody E} {Wb : ω → ConvexSpaceBody E}
  {blk : σ → ω} {hle : ∀ p ∈ segs', (Y' p).toConvexSpaceBody ≤ Wb (blk p)}

omit [BorelSpace E] in
@[simp] lemma blockOuterBodyCandidate_toConvexSpaceBody (j : ω) :
    (blockOuterBodyCandidate segs' Y' Wb blk hle j).toConvexSpaceBody =
      (Wb j).cthickening (Wb j).scale := rfl

omit [BorelSpace E] in
@[simp] lemma blockOuterBodyCandidate_shade (j : ω) :
    (blockOuterBodyCandidate segs' Y' Wb blk hle j).shade =
      iUnionShade (segs'.filter fun p => blk p = j) Y' := rfl

omit [BorelSpace E] in
lemma Wb_le_blockOuterBodyCandidate (j : ω) :
    Wb j ≤ (blockOuterBodyCandidate segs' Y' Wb blk hle j).toConvexSpaceBody :=
  (Wb j).self_le_cthickening _

omit [BorelSpace E] in
lemma blockOuterBodyCandidate_le_cthickening (j : ω) :
    (blockOuterBodyCandidate segs' Y' Wb blk hle j).toConvexSpaceBody ≤
      (Wb j).cthickening (Wb j).scale := le_rfl

omit [BorelSpace E] in
lemma mem_blockOuterBodyCandidate_shade {p : σ} (hp : p ∈ segs') {x : E}
    (hx : x ∈ (Y' p).shade) :
    x ∈ (blockOuterBodyCandidate segs' Y' Wb blk hle (blk p)).shade :=
  Set.mem_iUnion₂.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩, hx⟩

omit [BorelSpace E] in
lemma blockOuterBodyCandidate_shade_subset_cthickening (j : ω) :
    (blockOuterBodyCandidate segs' Y' Wb blk hle j).shade ⊆
      Metric.cthickening
        (2 * Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1))
        (iUnionShade (segs'.filter fun p => blk p = j) Y') :=
  Metric.self_subset_cthickening _

omit [BorelSpace E] in
lemma blockOuterBodyCandidate_iUnionShade {bodies' : Finset ω}
    (hblk : ∀ p ∈ segs', blk p ∈ bodies') :
    iUnionShade bodies' (blockOuterBodyCandidate segs' Y' Wb blk hle) =
      iUnionShade segs' Y' := by
  ext x
  simp only [iUnionShade, blockOuterBodyCandidate_shade, Set.mem_iUnion, exists_prop,
    Finset.mem_filter]
  constructor
  · rintro ⟨j, -, p, ⟨hp, -⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨blk p, hblk p hp, p, ⟨hp, rfl⟩, hx⟩

lemma inv_mul_sum_shade_le_self_candidate {C : NNReal} (hC : 1 ≤ C)
    (s : Finset σ) (V : σ → ShadedBody E) :
    (C : ENNReal)⁻¹ * ∑ p ∈ s, volume (V p).shade ≤ ∑ p ∈ s, volume (V p).shade := by
  have h1 : (C : ENNReal)⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]
    exact_mod_cast hC
  calc
    (C : ENNReal)⁻¹ * ∑ p ∈ s, volume (V p).shade
        ≤ 1 * ∑ p ∈ s, volume (V p).shade := by gcongr
    _ = ∑ p ∈ s, volume (V p).shade := one_mul _

lemma inv_mul_sum_shade_le_of_isCRefinement_candidate {C : NNReal} (hC : C ≠ 0)
    {segs segs' : Finset σ} {Y Y' : σ → ShadedBody E}
    (h : ShadedBody.IsCRefinement segs' Y' segs Y C⁻¹) :
    (C : ENNReal)⁻¹ * ∑ p ∈ segs, volume (Y p).shade ≤
      ∑ p ∈ segs', volume (Y' p).shade := by
  have hmass := h.2
  rwa [ENNReal.coe_inv hC] at hmass

end

end Kakeya.ThinCase
