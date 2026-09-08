/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Prop66BChainResidueProof
public import Kakeya.DimensionThree.Plank.Factorization

/-!
# GWZ Proposition 6.6(B): the project statement, proved

`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` is GWZ Proposition 6.6(B) in the form pinned as
`Kakeya.Prop66BScale.statement_of_universal_prop66B_essDistinct_parentWindow`.  Its proof is the
one-line composition of the fine-ED chain with its proved residue,
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_parentWindow_of_katzTaoEstimate`
(`Kakeya/DimensionThree/Plank/Prop66BChainResidueProof.lean`;,
).

**Why the theorem lives here and not in `Kakeya/DimensionThree/Plank/Factorization.lean`, where it
was stated** (`s9-66b-close-w123`). That file is in the import closure of the proof
(`Prop66BChainResidueProof ← Prop66BChainResidue ← Prop66BCoarseScale ← Factorization`), so the
proof term cannot be written there without an import cycle. Two consequences for the reader:

* the theorem's docstring below came verbatim from its previous home. The theorem is proved, and its axioms are
  `propext`, `Classical.choice`, `Quot.sound`;
* the two pin `example`s (the compatibility at the pin, and the residue-implies-statement record) moved
  here with it, since both mention the theorem and the pin's file is now upstream of it.

`Kakeya.GlobalPlankFactorization` and the other definitions the statement uses stay in
`Factorization.lean`.  The only code consumer, `Kakeya.ML2Reduction.exists_threshold_eccentric`
(`Kakeya/DimensionThree/MainLemma2/Reduction/SpineEccentric.lean`), imports this file.

The unused-variable linter is silenced on the theorem only: `hKF` (Frostman) is a hypothesis of the
condition statement that the proof does not need, and `hδ0`, `Fz` are named binders of the condition
telescope; renaming any of them would change the condition text.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal

noncomputable section

universe u

namespace Kakeya

set_option linter.unusedVariables false in
open Classical in
/-- GWZ Proposition 6.6(B): global plank factorization.

The proof applies
`tubeMultiplicityOfGlobalPlankFactorisation_parentWindow_of_katzTaoEstimate`
to `0 < β ≤ 1` and the Katz-Tao hypothesis `hKKT`; `hKF` is unused.

The geometric datum is `GlobalPlankFactorization`. Its `le_plank` field places
the convex hull of each block inside a plank, while `wide` gives a flat disc
of radius `min b (1 / 2) / Cw` inside that hull. Exact equality of a tube hull
with a plank would be impossible: the positive-radius tube hull is a Minkowski
sum with a ball, whereas a plank has corners; see `convexHull_tubes_ne_prism`.
The inclusion and disc conditions can hold simultaneously. The explicit
comparability constant `Cw` accommodates the constants in covering and
John-ellipsoid comparisons, and its loss is bounded by `Cw ≤ δ ^ (-η)`.
Without the transverse lower bound, an `a × a × 1` plank could be assigned
the parameter `b = 1`, falsely claiming the gain `a ^ β`.

The parent structure `Tube.IsUniformAtScale` supplies covering, bounded overlap,
injectivity and two-sided branching counts. Fine-family essential distinctness
is explicit: GWZ Definition 2.1(ii), applied at the finest scale `ρ = δ`,
entails it, whereas the local shading-uniformity predicate alone allows repeated
tubes. The proof uses this hypothesis to extract essentially distinct inner
planks. No extra maximal-density hypothesis is imposed on the fine family.

The scale condition `δ ^ (1 - ε₂) ≤ ρ ≤ a` supplies the inner-scale threshold
`δ ≤ s₀ * a`, through `Prop66BScale.le_mul_of_plankScale_le`. Allowing `ρ = δ`
would not supply that threshold when `s₀ < 1`.

The branching floor `(max 1 Cpar) ^ 2 ≤ PS.branchingN` gives enough leaves to
assign a nonempty fibre to every coarse index in use. The parent window
`∀ k ∈ PS.parent, (PS.parentTube k).carrier ⊆ Metric.closedBall 0 1`
provides the bounded ambient region for the coarse family. It is supplied at
the application site by `PlankFactoringData.ball`; the leaf-window construction
can also obtain it from the room condition `r + 4 * ρ ≤ 1`.

The source is `factoringThoughFlatPrismsB` in
`blueprint/src/GWZAdapted/section6_estimates.tex`. The inherited
`ConvexSpaceBody.Factorization` fields retain its Katz-Tao, density and
dimension-comparability conditions.
-/
theorem tubeMultiplicityOfGlobalPlankFactorisation {β : ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β)
    {ε₂ : ℝ} (hε₂0 : 0 < ε₂) (hε₂1 : ε₂ ≤ 1) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0),
      ∀ {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        δ ≤ δ₀ →
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (q : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (∃ C : ℝ≥0, C ≤ δ ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet q T
            (Tube.ssfGridLen δ) C)) →
        (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1) (Cw Cpar C₀ : ℝ≥0),
          Cw ≤ δ ^ (-η) → Cpar ≤ δ ^ (-η) → C₀ ≤ δ ^ (-η) →
          (δ : ℝ≥0) ^ (1 - ε₂) ≤ ρ → ρ ≤ a →
          ∀ (PS : Tube.IsUniformAtScale q (fun i ↦ (T i).toTube) ρ Cpar),
          (max 1 Cpar) ^ 2 ≤ PS.branchingN →
          (∀ k ∈ PS.parent, (PS.parentTube k).carrier ⊆ Metric.closedBall 0 1) →
          ∀ (Fz : GlobalPlankFactorization Cw a b hab hb1 PS.parent
            (fun k ↦ (PS.parentTube k).toConvexSpaceBody) C₀),
          ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
            (δ : ENNReal) ^ (-ε)
              * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
              * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β := by
  exact fun ε hε =>
    tubeMultiplicityOfGlobalPlankFactorisation_parentWindow_of_katzTaoEstimate hβpos hβle hKKT
      hε₂0 hε₂1 ε hε

/-! ### The pin is the project statement -/

/-- **compatibility, pinned to the real theorem**.  If the shape of
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` changes again, this breaks.  It lives here,
beside the theorem, because the pin it targets is defined in
`Kakeya/DimensionThree/Plank/Prop66BChainResidue.lean`, which is now upstream of the theorem and
cannot import this file. -/
example {β ε₂ : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hε₂0 : 0 < ε₂) (hε₂1 : ε₂ ≤ 1) :
    Prop66BScale.statement_of_universal_prop66B_essDistinct_parentWindow β ε₂ :=
  tubeMultiplicityOfGlobalPlankFactorisation hβpos hβle hKKT hKF hε₂0 hε₂1

/-- **The residue implies the project statement, at the project statement's own type.**  The type
ascribed is literally the type of `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` (via
`type_of%`) and the term is the chain assembly
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_parentWindow_of_chainConstructed` at the same
universe, so `Kakeya.Prop66BPartBChainConstructed.{u, u} β` was the one obligation between the
fine-ED chain and Proposition 6.6(B) as stated — discharged by
`Kakeya.prop66BPartBChainConstructed_of_katzTaoEstimate`, which is how the theorem above is proved.
Kept as the record of that interface.  `hKKT` and `hKF` are taken only so that the statement's type
can be formed; the chain does not use them. -/
example {β ε₂ : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hε₂0 : 0 < ε₂) (hε₂1 : ε₂ ≤ 1) (hres : Prop66BPartBChainConstructed.{u, u} β) :
    type_of% (tubeMultiplicityOfGlobalPlankFactorisation.{u} hβpos hβle hKKT hKF hε₂0 hε₂1) :=
  tubeMultiplicityOfGlobalPlankFactorisation_parentWindow_of_chainConstructed.{u}
    hβpos hβle hε₂0 hε₂1 hres

end Kakeya

end
