/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupCaseSideDataClosed

/-!
# The very-not-sticky case and Lemma 9.1

This module assembles `exists_setup_caseSideData`, `exists_setup`, and
`multiplicity_le_of_card_isEssDistinct_ge`, together with the uniform
companions `vnsBody_of_params`, `lemma91_of_vnsBody_of_params`, and
`lemma91Uniform_of_uniformPlankExponent`.

The setup type is available upstream as `SetupCaseSideDataAt`, allowing
the geometric and analytic construction modules to use its interface.
The final setup theorem unfolds that type and applies the assembled
construction.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

universe u

open MeasureTheory Topology Filter ShadedBody in
/-- **The configuration and its side data can be arranged** (blueprint
`lem:ml2setupSideData`).

The strengthening of `Kakeya.VeryNotSticky.exists_setup` that the proof of blueprint
`lemmain2vns` actually runs on: besides realizing Configuration `hyp:ml2setup`, it delivers
the bundle `Kakeya.VeryNotSticky.CaseSideData`, the side data that
`Kakeya.VeryNotSticky.exists_goalMult` consumes beyond `cfg`, `bd`, `params` and `β ≤ 1`. See
that structure for what its seven fields are and for which of them the blueprint assumes
rather than discharges.

**Divergence from the blueprint.** The extra conjunct is exactly this bundle; blueprint
`lem:ml2setupexists`, rendered by `Kakeya.VeryNotSticky.exists_setup`, stops at the
configuration and the refinement comparison, and is a corollary of this statement. The
hypotheses, the binder list and the refinement comparison are otherwise the same in both; see
`exists_setup` for a discussion of each.

**The extra binder `hplankF` is the exponent budget of blueprint `plankF`,**
`Kakeya.VeryNotSticky.PlankFrostmanBudget`: `2η < τ ηF` for *some* exponent `ηF > 0` at which
the plank-Frostman volume estimate holds, together with that estimate's two constants.
Without it this statement is **false**, not merely unproved: the field
`Kakeya.VeryNotSticky.ThickDensityThresholds.plankF` of the bundle it produces asserts the
plank estimate at an exponent whose second threshold, under the thick-case guard, reads
`CP^{1+ηF} δ^{τ ηF - 2η} ≤ c₁`; and the estimate itself is false above a maximal exponent, so
the two can be met at once only when `2η < τ ηF` for an `ηF` at which the estimate still holds.
That is a relation between `δ`-free parameters, of the same kind as the fields of
`Kakeya.VeryNotSticky.CaseParams`, and it is arranged by
`Kakeya.VeryNotSticky.exists_caseParams` alongside them. It travels as a binder rather than as
a field of `CaseParams` because `CaseParams` is declared upstream of the Section 6 plank
interface and so cannot mention the exponent — the same remedy, and for the same reason, as
`hβ1`.

The binder used to read `η < τ * plankFrostmanExponent β (ϱβτ/8)`, naming a `Classical.choose` witness. It was replaced by the existential
form, which is **weaker** — hence this statement is **strengthened**, never weakened — because
(i) the three fields of
`Kakeya.VeryNotSticky.ThickDensityThresholds` it feeds, `hηF`, `budget` and `plankF`, take the
exponent free already, so the canonical value was never used, and (ii) nothing in the
development bounds `plankFrostmanExponent` from below, so a statement that mentions it is
neither checkable nor transportable in `β`. `Kakeya.VeryNotSticky.plankFrostmanBudget_of_lt`
recovers the new form from the old one and `hF`, which is how
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge` still discharges it out of
`Kakeya.VeryNotSticky.exists_caseParams`. -/
theorem exists_setup_caseSideData {β ζ exscal ϱ η τ τ' : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∀ i ∈ s, (T i).toTube.IsCentred) →
        (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        ∃ (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (e : cfg.ι ≃ ι) (c : NNReal),
          (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧
              cfg.η = η) ∧
          ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
              (fun i ↦ (cfg.T (e.symm i)).toShadedBody)
              s (fun i ↦ (T i).toShadedBody) c ∧
          (δ : ENNReal) ^ η ≤ (c : ENNReal) ∧
          Nonempty (CaseSideData cfg bd τ τ') :=
  exists_setup_caseSideData_closed hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w

/-- **A6-C1:** the relocated leaf's type is *literally* the carrier
`Kakeya.VeryNotSticky.SetupCaseSideDataAt …` — carrier-vs-leaf drift with both still compiling is the
`SetupCaseSideDataStatementOld` hazard, and this `rfl` fires on it. -/
example {β ζ exscal ϱ η τ τ' : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal) :
    type_of% (exists_setup_caseSideData.{u} hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w) =
      SetupCaseSideDataAt.{u} hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w := rfl

open MeasureTheory Topology Filter ShadedBody in
/-- **The configuration can be arranged** (blueprint `lem:ml2setupexists`).

Fix `β, ζ > 0` and the parameters of Definition `hyp:ml2params`, assume `K_KT(β)` and
`K_F(β)`, and let `(𝕋, Y)` be a uniform family of `δ`-tubes in `B_1` satisfying the three
bulleted hypotheses of blueprint `lemmain2vns` — the bound `Δ_max(𝕋) ≤ δ^{-η}`, the fullness
bound `λ(𝕋, Y) ≥ δ^η`, and the `ρ`-tube count `|𝕋_ρ| ≥ ρ^{-2-ζ}` over the window
`ρ ∈ [δ^{1-exscal}, δ^{exscal}]`. Then, for `δ` below a threshold depending on the parameters
alone, some `⪆ 1` refinement of `(𝕋, Y)` carries data realizing Configuration `hyp:ml2setup`,
i.e. a `cfg : Kakeya.VeryNotSticky` with the prescribed exponents together with per-ball data
`bd : Kakeya.VeryNotSticky.BallData cfg`.

**This is an interface statement.** Its construction is not
formalized: it is Lemma `lem:ml2murho` for (C1), the `D`-boundedly overlapping cover by
`r₁`-balls with the subordinate partition of `lem:subordinatePartition` for (C2), the segment
families for (C3), three dyadic pigeonholings (`lem:dyadicPigeonhole`, using the mass identity
`lem:partitionMassIdentity` for the third) for (C5) and the non-emptiness of `𝔅`, and the
biased maximal density factoring `lemmafactmaxbias` followed by one further pigeonholing of
the dyadic pair `(b, a)` across all balls for (C4).

Three clauses of the configuration are, by the blueprint proof, *not* produced by those steps
and are left to the construction at the point where the corresponding step runs:

* the tube count `ml2setupTubeCount`, Lean `Kakeya.VeryNotSticky.tube_count`, read off from
  the `ρ`-count hypothesis at the coarse endpoint `ρ = δ^{1-exscal}` — legitimate here, and
  only here, because a family `𝕋_ρ` realizing that hypothesis is in hand at this point;
* the anti-clustering bound `ml2setupBodiesAntiClustering`, Lean
  `Kakeya.VeryNotSticky.BallData.bodies_antiClustering`, which is the second conclusion
  `factmaxmod2` of the same application of `lemmafactmaxbias` that produces the factoring,
  combined with `|W|/|B| ⪆ δ²`, at the cost of enlarging `C_bias`;
* the dilation comparison `ml2setupSegsDilation`, Lean
  `Kakeya.VeryNotSticky.BallData.segs_dilation`, the geometric statement of (C3) applied to
  the segment families just constructed, whose formalization needs the companion of
  `lem:maxDensityHomothety` discussed there.

**The refinement comparison.** The refinement is recorded through the existing
`def:cRefinement` API: `cfg`'s pair is a `c`-refinement of the given `(𝕋, Y)` with
`δ^η ≤ c`, which is this development's rendering of `⪆ 1` (`η` being the smallest positive
exponent of the section). Since a `c`-refinement keeps a subfamily of the *same* index type,
the construction may take `cfg.ι := ι`; the statement records the identification as an
equivalence `e : cfg.ι ≃ ι` and reindexes `cfg`'s family along it with
`Finset.map e.toEmbedding`, so that the comparison is literally
`ShadedBody.IsCRefinement`. An equivalence rather than a type equality with `Equiv.cast` is
what keeps consumers from having to `subst` a `Type u` equation. Together with
`ShadedBody.IsCRefinement.mul_multiplicity_le` (blueprint `lem:ml2multRefine`) and
`cfg.s.card ≤ s.card`, which the refinement also gives, this is exactly what turns
`cfg.goalMult ν` into the conclusion
`multiplicity s (fun i ↦ (T i).toShadedBody) ≤ δ^(ν - η) * (s.card)^β` of
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`.

The side data that `Kakeya.VeryNotSticky.exists_goalMult` consumes beyond `cfg`, `bd`,
`params` and `β ≤ 1` is *not* part of this conclusion: it is
`Kakeya.VeryNotSticky.CaseSideData`, arranged by
`Kakeya.VeryNotSticky.exists_setup_caseSideData`, of which this statement is the corollary
obtained by forgetting that bundle.

The binder list is long because Configuration `hyp:ml2params` has seven exponent parameters
and the three bulleted hypotheses of `lemmain2vns` are five separate conditions on `(𝕋, Y)`;
each is reproduced verbatim from `Kakeya.multiplicity_le_of_card_isEssDistinct_ge`, so that
the caller can discharge them by assumption. The positivity hypotheses `hβ`, `hζ`, `hexscal`,
`hϱ`, `hη` are exactly what the fields `hβ`, `hζ`, `hexscal`, `hϱ`, `hη` of
`Kakeya.VeryNotSticky` demand, and `hKT`, `hF` are its fields `ktEstimate`, `fEstimate`;
without them no configuration with the prescribed exponents exists. -/
theorem exists_setup {β ζ exscal ϱ η τ τ' : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ)
    (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∀ i ∈ s, (T i).toTube.IsCentred) →
        (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        ∃ (cfg : VeryNotSticky.{u}) (e : cfg.ι ≃ ι) (c : NNReal),
          (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧
              cfg.η = η) ∧
          ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
              (fun i ↦ (cfg.T (e.symm i)).toShadedBody)
              s (fun i ↦ (T i).toShadedBody) c ∧
          (δ : ENNReal) ^ η ≤ (c : ENNReal) ∧
          Nonempty (BallData cfg) := by
  filter_upwards [exists_setup_caseSideData hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w]
    with δ hδ
  intro ι s T hball hcen huni hmax hfull hcount
  obtain ⟨cfg, bd, e, c, hexp, href, hc, -⟩ := hδ s T hball hcen huni hmax hfull hcount
  exact ⟨cfg, e, c, hexp, href, hc, ⟨bd⟩⟩

/-- The tripwire pinning `Kakeya.VeryNotSticky.SetupCaseSideDataStatement` to the real
declaration. (Moved here from `SetupAbsorption.lean`.) -/
example : SetupCaseSideDataStatement.{u} := @exists_setup_caseSideData.{u}

end Kakeya.VeryNotSticky

namespace Kakeya

universe u

open Kakeya.VeryNotSticky

open MeasureTheory Topology Filter ShadedBody in
/-- Reindexing `multiplicity` along an equivalence of index types: the multiplicity of the
family transported by `e.symm` over the reindexed set `s.map e.toEmbedding` equals that of the
original family over `s`. -/
private lemma multiplicity_map_equiv {α β : Type u} (s : Finset α) (e : α ≃ β)
    (V : α → ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    ShadedBody.multiplicity (s.map e.toEmbedding) (fun j => (V (e.symm j))) =
      ShadedBody.multiplicity s V := by
  classical
  unfold ShadedBody.multiplicity
  congr 1
  · rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro a ha
    simp [Equiv.symm_apply_apply]
  · have hset : (⋃ j ∈ s.map e.toEmbedding, (V (e.symm j)).shade) =
        (⋃ i ∈ s, (V i).shade) := by
      ext x
      simp only [Set.mem_iUnion₂]
      constructor
      · rintro ⟨j, hj, hx⟩
        rcases Finset.mem_map.mp hj with ⟨a, ha, rfl⟩
        exact ⟨a, ha, by simpa using hx⟩
      · rintro ⟨a, ha, hx⟩
        refine ⟨e a, Finset.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
        simpa using hx
    rw [hset]

open MeasureTheory Topology Filter ShadedBody in
/-- [GWZ, Lemma 9.1] (Very not sticky case of Main Lemma 2).
For every `β > 0` there is a scale exponent `ϖ = ϖ(β) > 0` such that for every
`ζ > 0` there are `ν = ν(β, ζ) > 0` and `η = η(β, ζ) > 0` with the following
property. Assume `K_KT(β)` and `K_F(β)` hold in `ℝ^3`. Then for all sufficiently
small `δ`, whenever `(T, Y)` is a family of `δ`-tubes in `B_1` that is *uniform* in the
sense of GWZ Definitions 2.1/2.2 at a constant `1 ≤ C ≤ δ^{-η}`, with
`Δ_max(T) ≤ δ^{-η}` and `λ(T, Y) ≥ δ^η`, and for every scale
`ρ ∈ [δ^{1-ϖ}, δ^ϖ]` there is an essentially-distinct family of `ρ`-tubes, each
containing a member of `T`, with at least `ρ^{-2-ζ}` members, then
`μ(T, Y) ≤ δ^ν |T|^β`.

The uniformity hypothesis is `ShadedTube.ShadedUniformTubeSet` on the standard grid at a
constant `1 ≤ C ≤ δ^{-η}` — GWZ's `∼1`/`≈1` (`gwz.txt` l.153, l.182–198) read at the lemma's own
smallness exponent `η`. The earlier rendering `∃ C, Nonempty …` with
`C` unbounded was compiled-vacuous (`Kakeya.VeryNotSticky.exists_shadedUniformTubeSet_of_axes_injOn`
inhabits it for every family with distinct axes, at `C = |T| + 1`), so the lemma then claimed
its conclusion for families GWZ's Lemma 9.1 does not speak about. The count hypothesis
`|T_ρ| ≥ ρ^{-2-ζ}` is rendered in the /6 form: the *existence*, at each scale of the
window, of an essentially distinct, all-used `ρ`-tube family of that cardinality.

The upper bound `hβ1 : β ≤ 1` is not decoration. The whole proof chain requires it:
`Kakeya.VeryNotSticky.exists_goalMult` takes it as an explicit binder, the thick branch
`Kakeya.VeryNotSticky.goalMult_of_a_ge` consumes it, and in the non-slab branches it is what
`Kakeya.VeryNotSticky.nonslabKKTPow` spends turning `|𝕋[T_{ρ₂*}]| ≤ C ρ₂^{2+ζ}|𝕋|` into its
`β`-th power. The blueprint statement of `lemmain2vns` reads "for all `0 < β ≤ 1`" for that
reason, and the sole consumer,
`Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate`, already restricts to that
range, so the hypothesis is free. -/
theorem multiplicity_le_of_card_isEssDistinct_ge {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ ϖ > (0 : ℝ), ∀ ζ > (0 : ℝ), ∃ ν > (0 : ℝ), ∃ η > (0 : ℝ),
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∀ i ∈ s, (T i).toTube.IsCentred) →
        (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - ϖ)) (δ ^ ϖ) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        multiplicity s (fun i ↦ (T i).toShadedBody) ≤
          (δ : ENNReal) ^ ν * (s.card : ENNReal) ^ β := by
  classical
  by_cases hKT0 : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β
  case neg =>
    -- `Kakeya.lemma91_shape_of_imp`: the hypothesis sits inside the innermost binder, so it may
    -- be assumed outside all of them.  Without it every instance is vacuous.
    exact ⟨1, one_pos, fun _ _ ↦ ⟨1, one_pos, 1, one_pos, fun hKT _ ↦ absurd hKT hKT0⟩⟩
  rcases exists_caseParams hβ with ⟨exscal, hexscal, hparams_ζ⟩
  refine ⟨exscal, hexscal, ?_⟩
  intro ζ hζ
  rcases hparams_ζ ζ hζ with ⟨τ, τ', ϱ, η₀, hτ, hτ', hϱ, hη₀, params₀, hη₀_le, hplankF₀⟩
  -- the coarse Katz--Tao window pair, read at the `β`- and `η`-free loss exponent `ϱ²β/1440`
  have hwe0 : (0 : ℝ) < ϱ ^ 2 * β / 1440 := by positivity
  obtain ⟨pp, hp1, hp2, hp3, hwin⟩ := Kakeya.exists_windowFour hβ.le hβ1 hKT0 hwe0
  set η : ℝ := min η₀ (min (exscal * pp.1 / 3) (exscal * (ϱ ^ 2 * β / 1440) / 3)) with hηdef
  have hηη₀ : η ≤ η₀ := by rw [hηdef]; exact min_le_left _ _
  have hηA : η ≤ exscal * pp.1 / 3 := by
    rw [hηdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hηB : η ≤ exscal * (ϱ ^ 2 * β / 1440) / 3 := by
    rw [hηdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hη : 0 < η := by
    rw [hηdef]; exact lt_min hη₀ (lt_min (by positivity) (by positivity))
  have params : CaseParams β ζ exscal ϱ η τ τ' := VNSUniform.CaseParams.mono_eta hηη₀ params₀
  have hη_le : η ≤ casesplitExponent β ζ exscal τ τ' ϱ / 2 := le_trans hηη₀ hη₀_le
  have hplankF : 2 * η < τ * plankFrostmanExponent.{u} β (ϱ * β * τ / 8) := by
    linarith [hηη₀, hplankF₀]
  have w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal :=
    { wb := β, hwb0 := hβ, hwb := le_rfl,
      we := ϱ ^ 2 * β / 1440, hwe0 := hwe0, hwe := le_rfl,
      wη := pp.1, hwη := hp1, wρ := pp.2, hwρ0 := hp2, hwρhalf := hp3, hwin := hwin,
      hηKT := by linarith, hηbud := by linarith }
  let cs : ℝ := casesplitExponent β ζ exscal τ τ' ϱ
  let ν : ℝ := cs - η
  have hcs_pos : 0 < cs := by
    dsimp [cs]
    exact casesplitExponent_pos hβ hζ hexscal hτ hτ' hϱ
  have hν_pos : 0 < ν := by
    dsimp [ν]
    have hη_le_cs : η ≤ cs / 2 := by simpa [cs] using hη_le
    nlinarith [hη_le_cs, hcs_pos]
  refine ⟨ν, hν_pos, η, hη, ?_⟩
  intro hKT hF
  have hQ : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∀ i ∈ s, (T i).toTube.IsCentred) →
        (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        ∃ (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (e : cfg.ι ≃ ι) (c : NNReal),
          (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧
              cfg.η = η) ∧
          ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
              (fun i ↦ (cfg.T (e.symm i)).toShadedBody)
              s (fun i ↦ (T i).toShadedBody) c ∧
          (δ : ENNReal) ^ η ≤ (c : ENNReal) ∧
          Nonempty (CaseSideData cfg bd τ τ') :=
    exists_setup_caseSideData hβ hβ1 hζ hexscal hϱ hη params
      (plankFrostmanBudget_of_lt hβ hβ1
        (div_pos (mul_pos (mul_pos hϱ hβ) hτ) (by norm_num)) hF hplankF) hKT hF w
  have hδpos : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, (0 : NNReal) < δ := by
    simpa [Filter.Eventually, Set.Ioi] using
      (self_mem_nhdsWithin (s := Set.Ioi (0 : NNReal)) (a := (0 : NNReal)))
  refine (hQ.and hδpos).mono ?_
  intro δ hδ
  rcases hδ with ⟨hδQ, hδpos⟩
  intro ι s T hcarrier hcen huni hmax hfull hcount
  obtain ⟨cfg, bd, e, c, hexp, href, hcδ, ⟨sd⟩⟩ := hδQ s T hcarrier hcen huni hmax hfull hcount
  have hparams' : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ' := by
    simpa [← hexp.1, ← hexp.2.1, ← hexp.2.2.2.1, ← hexp.2.2.2.2.1, ← hexp.2.2.2.2.2]
      using params
  have hβ1' : cfg.β ≤ 1 := by
    simpa [← hexp.1] using hβ1
  have hgoal : cfg.goalMult (casesplitExponent cfg.β cfg.ζ cfg.exscal τ τ' cfg.ϱ) :=
    exists_goalMult cfg hparams' bd hβ1' sd.thick sd.thr sd.thr_thick
      ⟨sd.tc, sd.slabScale, sd.caseScale, fun h₁ h₂ => ⟨sd.tangential h₁ h₂⟩⟩
  have hcs_eq : casesplitExponent cfg.β cfg.ζ cfg.exscal τ τ' cfg.ϱ = cs := by
    dsimp [cs]
    rw [hexp.1, hexp.2.1, hexp.2.2.2.1, hexp.2.2.2.2.1]
  rw [hcs_eq] at hgoal
  have hgoalMul : multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ENNReal) ^ cs * (cfg.s.card : ENNReal) ^ cfg.β := by
    simpa [Kakeya.VeryNotSticky.goalMult] using hgoal
  have hcfgbound : multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤
      (δ : ENNReal) ^ cs * (cfg.s.card : ENNReal) ^ β := by
    have hδcast : (cfg.δ : ENNReal) = (δ : ENNReal) := by rw [hexp.2.2.1]
    rwa [hδcast, hexp.1] at hgoalMul
  have hδenn : 0 < (δ : ENNReal) := ENNReal.coe_pos.mpr hδpos
  have hδnz : (δ : ENNReal) ≠ 0 := ne_of_gt hδenn
  have hδntop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδpow : 0 < (δ : ENNReal) ^ η := ENNReal.rpow_pos_of_nonneg hδenn (le_of_lt hη)
  have hcpos : 0 < (c : ENNReal) := lt_of_lt_of_le hδpow hcδ
  have hcne : (c : ENNReal) ≠ 0 := ne_of_gt hcpos
  have hctop : (c : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hreindex : multiplicity (cfg.s.map e.toEmbedding)
      (fun i => (cfg.T (e.symm i)).toShadedBody) =
      multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) :=
    multiplicity_map_equiv cfg.s e (fun a => (cfg.T a).toShadedBody)
  have href_mul : (c : ENNReal) * multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      multiplicity (cfg.s.map e.toEmbedding) (fun i => (cfg.T (e.symm i)).toShadedBody) :=
    ShadedBody.IsCRefinement.mul_multiplicity_le (s' := cfg.s.map e.toEmbedding)
      (V' := fun i => (cfg.T (e.symm i)).toShadedBody) (s := s)
      (V := fun i => (T i).toShadedBody) href
  have hinv : multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      (c : ENNReal)⁻¹ * multiplicity (cfg.s.map e.toEmbedding)
        (fun i => (cfg.T (e.symm i)).toShadedBody) := by
    calc
      multiplicity s (fun i ↦ (T i).toShadedBody)
          = (c : ENNReal)⁻¹ * ((c : ENNReal) * multiplicity s (fun i ↦ (T i).toShadedBody)) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hcne hctop, one_mul]
      _ ≤ (c : ENNReal)⁻¹ * multiplicity (cfg.s.map e.toEmbedding)
              (fun i => (cfg.T (e.symm i)).toShadedBody) := by
            exact mul_le_mul_of_nonneg_left href_mul (zero_le : 0 ≤ (c : ENNReal)⁻¹)
  have hcardNN : cfg.s.card ≤ s.card := by
    calc
      cfg.s.card = (cfg.s.map e.toEmbedding).card := by rw [Finset.card_map]
      _ ≤ s.card := Finset.card_le_card href.1.1
  have hcard_le : (cfg.s.card : ENNReal) ≤ (s.card : ENNReal) := by
    exact_mod_cast hcardNN
  have hcard_pow : (cfg.s.card : ENNReal) ^ β ≤ (s.card : ENNReal) ^ β :=
    ENNReal.rpow_le_rpow hcard_le (le_of_lt hβ)
  have hc_le : (c : ENNReal)⁻¹ ≤ (δ : ENNReal) ^ (-η) := by
    calc
      (c : ENNReal)⁻¹ ≤ ((δ : ENNReal) ^ η)⁻¹ := ENNReal.inv_le_inv' hcδ
      _ = (δ : ENNReal) ^ (-η) := by rw [ENNReal.rpow_neg]
  calc
    multiplicity s (fun i ↦ (T i).toShadedBody)
        ≤ (c : ENNReal)⁻¹ * multiplicity (cfg.s.map e.toEmbedding)
            (fun i => (cfg.T (e.symm i)).toShadedBody) := hinv
    _ = (c : ENNReal)⁻¹ * multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) := by
        rw [hreindex]
    _ ≤ (c : ENNReal)⁻¹ * ((δ : ENNReal) ^ cs * (cfg.s.card : ENNReal) ^ β) := by
        exact mul_le_mul_of_nonneg_left hcfgbound (zero_le : 0 ≤ (c : ENNReal)⁻¹)
    _ ≤ (δ : ENNReal) ^ (-η) * ((δ : ENNReal) ^ cs * (cfg.s.card : ENNReal) ^ β) := by
        gcongr
    _ = (δ : ENNReal) ^ (-η) * (δ : ENNReal) ^ cs * (cfg.s.card : ENNReal) ^ β := by
        rw [mul_assoc]
    _ ≤ (δ : ENNReal) ^ (-η) * (δ : ENNReal) ^ cs * (s.card : ENNReal) ^ β := by
        gcongr
    _ = (δ : ENNReal) ^ (cs - η) * (s.card : ENNReal) ^ β := by
        congr 1
        calc
          (δ : ENNReal) ^ (-η) * (δ : ENNReal) ^ cs
              = (δ : ENNReal) ^ cs * (δ : ENNReal) ^ (-η) := mul_comm _ _
          _ = (δ : ENNReal) ^ (cs + (-η)) :=
              (ENNReal.rpow_add (x := (δ : ENNReal)) (y := cs) (z := -η) hδnz hδntop).symm
          _ = (δ : ENNReal) ^ (cs - η) := by congr 1
    _ = (δ : ENNReal) ^ ν * (s.card : ENNReal) ^ β := by dsimp [ν]

end Kakeya

namespace Kakeya.ML2Assembly

universe u

/-- **Fidelity tripwire.**  `Lemma91` is the conclusion of the protected
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`, with every binder written out.  If the two
ever drift apart, this `example` stops compiling. (Moved here from `Reduction/Assembly.lean`.) -/
example : Lemma91.{u} :=
  fun _β hβ hβ1 ↦ Kakeya.multiplicity_le_of_card_isEssDistinct_ge hβ hβ1

end Kakeya.ML2Assembly

namespace Kakeya.VNSUniform

universe u

open Kakeya.VeryNotSticky

open MeasureTheory Topology Filter ShadedBody in
/-- Reindexing `multiplicity` along an equivalence of index types.  A verbatim copy of the
`private` lemma of the same name in
`Kakeya/DimensionThree/MainLemma2/VeryNotStickyCase.lean`, which cannot be referred to from
another file. -/
private lemma multiplicity_map_equiv' {α β : Type u} (s : Finset α) (e : α ≃ β)
    (V : α → ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    ShadedBody.multiplicity (s.map e.toEmbedding) (fun j => (V (e.symm j))) =
      ShadedBody.multiplicity s V := by
  classical
  unfold ShadedBody.multiplicity
  congr 1
  · rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro a ha
    simp [Equiv.symm_apply_apply]
  · have hset : (⋃ j ∈ s.map e.toEmbedding, (V (e.symm j)).shade) =
        (⋃ i ∈ s, (V i).shade) := by
      ext x
      simp only [Set.mem_iUnion₂]
      constructor
      · rintro ⟨j, hj, hx⟩
        rcases Finset.mem_map.mp hj with ⟨a, ha, rfl⟩
        exact ⟨a, ha, by simpa using hx⟩
      · rintro ⟨a, ha, hx⟩
        refine ⟨e a, Finset.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
        simpa using hx
    rw [hset]

open MeasureTheory Topology Filter ShadedBody in
/-- **The body of GWZ Lemma 9.1, with the parameters of Configuration `hyp:ml2params` as
arguments.**

Every hypothesis is one that `Kakeya.VeryNotSticky.exists_caseParams` arranges, and the proof is
that of `Kakeya.multiplicity_le_of_card_isEssDistinct_ge` from the point where the `rcases` on
`exists_caseParams` ends.  Note the conclusion's gain: the case-split exponent minus the
refinement loss `η`, exactly as in the protected declaration. -/
theorem vnsBody_of_params {β ζ exscal ϱ η τ τ' : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : 2 * η < τ * plankFrostmanExponent.{u} β (ϱ * β * τ / 8))
    (w : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      Kakeya.CoarseKTWindow.{u} β ϱ η exscal) :
    VNSBody.{u} β exscal ζ (casesplitExponent β ζ exscal τ τ' ϱ - η) η := by
  classical
  intro hKT hF
  let cs : ℝ := casesplitExponent β ζ exscal τ τ' ϱ
  have hQ := exists_setup_caseSideData.{u} hβ hβ1 hζ hexscal hϱ hη params
    (plankFrostmanBudget_of_lt hβ hβ1
      (div_pos (mul_pos (mul_pos hϱ hβ) params.hτ) (by norm_num)) hF hplankF) hKT hF (w hKT hF)
  have hδpos : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, (0 : NNReal) < δ := by
    simpa [Filter.Eventually, Set.Ioi] using
      (self_mem_nhdsWithin (s := Set.Ioi (0 : NNReal)) (a := (0 : NNReal)))
  refine (hQ.and hδpos).mono ?_
  intro δ hδ
  rcases hδ with ⟨hδQ, hδpos⟩
  intro ι s T hcarrier hcen huni hmax hfull hcount
  obtain ⟨cfg, bd, e, c, hexp, href, hcδ, ⟨sd⟩⟩ := hδQ s T hcarrier hcen huni hmax hfull hcount
  have hparams' : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ' := by
    simpa [← hexp.1, ← hexp.2.1, ← hexp.2.2.2.1, ← hexp.2.2.2.2.1, ← hexp.2.2.2.2.2]
      using params
  have hβ1' : cfg.β ≤ 1 := by
    simpa [← hexp.1] using hβ1
  have hgoal : cfg.goalMult (casesplitExponent cfg.β cfg.ζ cfg.exscal τ τ' cfg.ϱ) :=
    exists_goalMult cfg hparams' bd hβ1' sd.thick sd.thr sd.thr_thick
      ⟨sd.tc, sd.slabScale, sd.caseScale, fun h₁ h₂ => ⟨sd.tangential h₁ h₂⟩⟩
  have hcs_eq : casesplitExponent cfg.β cfg.ζ cfg.exscal τ τ' cfg.ϱ = cs := by
    dsimp [cs]
    rw [hexp.1, hexp.2.1, hexp.2.2.2.1, hexp.2.2.2.2.1]
  rw [hcs_eq] at hgoal
  have hgoalMul : multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ENNReal) ^ cs * (cfg.s.card : ENNReal) ^ cfg.β := by
    simpa [Kakeya.VeryNotSticky.goalMult] using hgoal
  have hcfgbound : multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤
      (δ : ENNReal) ^ cs * (cfg.s.card : ENNReal) ^ β := by
    have hδcast : (cfg.δ : ENNReal) = (δ : ENNReal) := by rw [hexp.2.2.1]
    rwa [hδcast, hexp.1] at hgoalMul
  have hδenn : 0 < (δ : ENNReal) := ENNReal.coe_pos.mpr hδpos
  have hδnz : (δ : ENNReal) ≠ 0 := ne_of_gt hδenn
  have hδntop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδpow : 0 < (δ : ENNReal) ^ η := ENNReal.rpow_pos_of_nonneg hδenn (le_of_lt hη)
  have hcpos : 0 < (c : ENNReal) := lt_of_lt_of_le hδpow hcδ
  have hcne : (c : ENNReal) ≠ 0 := ne_of_gt hcpos
  have hctop : (c : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hreindex : multiplicity (cfg.s.map e.toEmbedding)
      (fun i => (cfg.T (e.symm i)).toShadedBody) =
      multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) :=
    multiplicity_map_equiv' cfg.s e (fun a => (cfg.T a).toShadedBody)
  have href_mul : (c : ENNReal) * multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      multiplicity (cfg.s.map e.toEmbedding) (fun i => (cfg.T (e.symm i)).toShadedBody) :=
    ShadedBody.IsCRefinement.mul_multiplicity_le (s' := cfg.s.map e.toEmbedding)
      (V' := fun i => (cfg.T (e.symm i)).toShadedBody) (s := s)
      (V := fun i => (T i).toShadedBody) href
  have hinv : multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      (c : ENNReal)⁻¹ * multiplicity (cfg.s.map e.toEmbedding)
        (fun i => (cfg.T (e.symm i)).toShadedBody) := by
    calc
      multiplicity s (fun i ↦ (T i).toShadedBody)
          = (c : ENNReal)⁻¹ * ((c : ENNReal) * multiplicity s (fun i ↦ (T i).toShadedBody)) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hcne hctop, one_mul]
      _ ≤ (c : ENNReal)⁻¹ * multiplicity (cfg.s.map e.toEmbedding)
              (fun i => (cfg.T (e.symm i)).toShadedBody) := by
            exact mul_le_mul_of_nonneg_left href_mul (zero_le : 0 ≤ (c : ENNReal)⁻¹)
  have hcardNN : cfg.s.card ≤ s.card := by
    calc
      cfg.s.card = (cfg.s.map e.toEmbedding).card := by rw [Finset.card_map]
      _ ≤ s.card := Finset.card_le_card href.1.1
  have hcard_le : (cfg.s.card : ENNReal) ≤ (s.card : ENNReal) := by
    exact_mod_cast hcardNN
  have hcard_pow : (cfg.s.card : ENNReal) ^ β ≤ (s.card : ENNReal) ^ β :=
    ENNReal.rpow_le_rpow hcard_le (le_of_lt hβ)
  have hc_le : (c : ENNReal)⁻¹ ≤ (δ : ENNReal) ^ (-η) := by
    calc
      (c : ENNReal)⁻¹ ≤ ((δ : ENNReal) ^ η)⁻¹ := ENNReal.inv_le_inv' hcδ
      _ = (δ : ENNReal) ^ (-η) := by rw [ENNReal.rpow_neg]
  calc
    multiplicity s (fun i ↦ (T i).toShadedBody)
        ≤ (c : ENNReal)⁻¹ * multiplicity (cfg.s.map e.toEmbedding)
            (fun i => (cfg.T (e.symm i)).toShadedBody) := hinv
    _ = (c : ENNReal)⁻¹ * multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) := by
        rw [hreindex]
    _ ≤ (c : ENNReal)⁻¹ * ((δ : ENNReal) ^ cs * (cfg.s.card : ENNReal) ^ β) := by
        exact mul_le_mul_of_nonneg_left hcfgbound (zero_le : 0 ≤ (c : ENNReal)⁻¹)
    _ ≤ (δ : ENNReal) ^ (-η) * ((δ : ENNReal) ^ cs * (cfg.s.card : ENNReal) ^ β) := by
        gcongr
    _ = (δ : ENNReal) ^ (-η) * (δ : ENNReal) ^ cs * (cfg.s.card : ENNReal) ^ β := by
        rw [mul_assoc]
    _ ≤ (δ : ENNReal) ^ (-η) * (δ : ENNReal) ^ cs * (s.card : ENNReal) ^ β := by
        gcongr
    _ = (δ : ENNReal) ^ (cs - η) * (s.card : ENNReal) ^ β := by
        congr 1
        calc
          (δ : ENNReal) ^ (-η) * (δ : ENNReal) ^ cs
              = (δ : ENNReal) ^ cs * (δ : ENNReal) ^ (-η) := mul_comm _ _
          _ = (δ : ENNReal) ^ (cs + (-η)) :=
              (ENNReal.rpow_add (x := (δ : ENNReal)) (y := cs) (z := -η) hδnz hδntop).symm
          _ = (δ : ENNReal) ^ (cs - η) := by congr 1



/-- **Second fidelity check.**  Feeding `Kakeya.VNSUniform.vnsBody_of_params` the parameters that
`Kakeya.VeryNotSticky.exists_caseParams` produces recovers GWZ Lemma 9.1 on the nose.  Together
with the tripwire `example : Lemma91 := …` above this pins the extracted core to the protected
declaration from both sides. -/
theorem lemma91_of_vnsBody_of_params : Lemma91.{u} := by
  intro β hβ hβ1
  by_cases hKT0 : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β
  case neg =>
    exact ⟨1, one_pos, fun _ _ ↦ ⟨1, one_pos, 1, one_pos, fun hKT _ ↦ absurd hKT hKT0⟩⟩
  obtain ⟨exscal, hexscal, hpar⟩ := exists_caseParams.{u} hβ
  refine ⟨exscal, hexscal, fun ζ hζ ↦ ?_⟩
  obtain ⟨τ, τ', ϱ, η₀, hτ, hτ', hϱ, hη₀, params₀, hη₀_le, hplankF₀⟩ := hpar ζ hζ
  have hwe0 : (0 : ℝ) < ϱ ^ 2 * β / 1440 := by positivity
  obtain ⟨pp, hp1, hp2, hp3, hwin⟩ := Kakeya.exists_windowFour hβ.le hβ1 hKT0 hwe0
  set η : ℝ := min η₀ (min (exscal * pp.1 / 3) (exscal * (ϱ ^ 2 * β / 1440) / 3)) with hηdef
  have hηη₀ : η ≤ η₀ := by rw [hηdef]; exact min_le_left _ _
  have hηA : η ≤ exscal * pp.1 / 3 := by
    rw [hηdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hηB : η ≤ exscal * (ϱ ^ 2 * β / 1440) / 3 := by
    rw [hηdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hη : 0 < η := by
    rw [hηdef]; exact lt_min hη₀ (lt_min (by positivity) (by positivity))
  have params : CaseParams β ζ exscal ϱ η τ τ' := CaseParams.mono_eta hηη₀ params₀
  have hplankF : 2 * η < τ * plankFrostmanExponent.{u} β (ϱ * β * τ / 8) := by
    linarith [hηη₀, hplankF₀]
  have w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal :=
    { wb := β, hwb0 := hβ, hwb := le_rfl,
      we := ϱ ^ 2 * β / 1440, hwe0 := hwe0, hwe := le_rfl,
      wη := pp.1, hwη := hp1, wρ := pp.2, hwρ0 := hp2, hwρhalf := hp3, hwin := hwin,
      hηKT := by linarith, hηbud := by linarith }
  have hcs_pos : 0 < casesplitExponent β ζ exscal τ τ' ϱ :=
    casesplitExponent_pos hβ hζ hexscal hτ hτ' hϱ
  exact ⟨casesplitExponent β ζ exscal τ τ' ϱ - η, by linarith [le_trans hηη₀ hη₀_le], η, hη,
    vnsBody_of_params hβ hβ1 hζ hexscal hϱ hη params hplankF (fun _ _ ↦ w)⟩

open MeasureTheory Topology Filter ShadedBody VeryNotSticky

/-- **GWZ Lemma 9.1, uniformly in `β` on every window `[β₀, 1]`, given the residual.**

This is the hypothesis `Kakeya.ML2Assembly.Lemma91Uniform` of the GWZ reduction, proved from the
protected Lemma 9.1's own machinery with the parameters chosen once at the threshold.  The only
input beyond that machinery is `Kakeya.VNSUniform.UniformPlankExponent`, isolated above and shown
there to be exactly the `β`-uniform form of the one binder that does not transport. -/
theorem lemma91Uniform_of_uniformPlankExponent
    (h : ∀ β₀ : ℝ, 0 < β₀ → β₀ ≤ 1 → UniformPlankExponent.{u} β₀) : Lemma91Uniform.{u} := by
  intro β₀ hβ₀ hβ₀1
  obtain ⟨exscal, hexscal, H⟩ := exists_uniform_caseParams hβ₀ (h β₀ hβ₀ hβ₀1)
  refine ⟨exscal, hexscal, fun ζ hζ ↦ ?_⟩
  obtain ⟨τ, τ', ϱ, η₀, hτ, hτ', hϱ, hη₀, hparams₀, hη₀_le, hplank₀⟩ := H ζ hζ
  -- ONE window pair for the whole of `[β₀,1]`, from `estimateSet_shape`; no residual
  have hwe0 : (0 : ℝ) < ϱ ^ 2 * β₀ / 1440 := by positivity
  obtain ⟨q, hq1, hq2, hq3, hqspec⟩ := Kakeya.exists_uniformWindowPair hβ₀ hβ₀1 hwe0
  set η : ℝ := min η₀ (min (exscal * q.1 / 3) (exscal * (ϱ ^ 2 * β₀ / 1440) / 3)) with hηdef
  have hηη₀ : η ≤ η₀ := by rw [hηdef]; exact min_le_left _ _
  have hηA : η ≤ exscal * q.1 / 3 := by
    rw [hηdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hηB : η ≤ exscal * (ϱ ^ 2 * β₀ / 1440) / 3 := by
    rw [hηdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hη : 0 < η := by
    rw [hηdef]; exact lt_min hη₀ (lt_min (by positivity) (by positivity))
  have hparams : ∀ β ∈ Set.Icc β₀ 1, CaseParams β ζ exscal ϱ η τ τ' :=
    fun β hβ ↦ CaseParams.mono_eta hηη₀ (hparams₀ β hβ)
  have hplank : ∀ β ∈ Set.Icc β₀ 1,
      2 * η < τ * plankFrostmanExponent.{u} β (ϱ * β * τ / 8) :=
    fun β hβ ↦ by linarith [hηη₀, hplank₀ β hβ]
  have hcs₀ : 0 < casesplitExponent β₀ ζ exscal τ τ' ϱ :=
    casesplitExponent_pos hβ₀ hζ hexscal hτ hτ' hϱ
  refine ⟨casesplitExponent β₀ ζ exscal τ τ' ϱ - η, by
    linarith [le_trans hηη₀ hη₀_le], η, hη, fun β hβ ↦ ?_⟩
  have hβpos : 0 < β := lt_of_lt_of_le hβ₀ hβ.1
  have hmono : casesplitExponent β₀ ζ exscal τ τ' ϱ ≤ casesplitExponent β ζ exscal τ τ' ϱ :=
    casesplitExponent_mono_beta hexscal.le hζ.le hτ.le hτ'.le hϱ.le hβ.1
  have hbody := vnsBody_of_params hβpos hβ.2 hζ hexscal hϱ hη (hparams β hβ) (hplank β hβ)
    (fun hKT hF ↦
      { wb := β₀, hwb0 := hβ₀, hwb := hβ.1,
        we := ϱ ^ 2 * β₀ / 1440, hwe0 := hwe0, hwe := le_rfl,
        wη := q.1, hwη := hq1, wρ := q.2, hwρ0 := hq2, hwρhalf := hq3,
        hwin := hqspec β hβ hKT hF,
        hηKT := by linarith, hηbud := by linarith })
  exact VNSBody.mono_gain (by linarith) hbody

/-- **Fidelity tripwire.**  `Kakeya.VNSUniform.Lemma91` is the conclusion of the protected
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge` with every binder written out.  If the two
ever drift apart, this `example` stops compiling — which is what makes
`Kakeya.VNSUniform.VNSBody` a faithful copy rather than a paraphrase. (Moved here from `VeryNotStickyUniform.lean`.) -/
example : Lemma91.{u} :=
  fun _β hβ hβ1 ↦ Kakeya.multiplicity_le_of_card_isEssDistinct_ge hβ hβ1

end Kakeya.VNSUniform

end
