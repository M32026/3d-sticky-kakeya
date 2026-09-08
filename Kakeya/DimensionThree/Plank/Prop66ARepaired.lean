/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.RhoFreeParentCount

/-!
# GWZ Proposition 6.6(A), restated faithfully and proved

`Kakeya.tubeMultiplicityOfLocalPlankFactorisation`
(`Kakeya/DimensionThree/Plank/Factorization.lean`) is the development's existing statement of GWZ
Proposition 6.6(A). This file states the proposition GWZ
actually proves, proves it, and certifies that its hypotheses are inhabited.

**Nothing here edits `Plank/Factorization.lean` or `Plank/Prop66AGuardrails.lean`.**  The old
statement, its `exfalso` proof, the compatibility `example` and the two vacuity theorems all stay
exactly where they are: they are the record of what went wrong, and the record must survive the
repair.

## The two defects of the existing statement, and their independence

**(i) The datum is empty.**  `Kakeya.PlankFactorization.parts_are_planks` demands the *equality*
`part.convexHull_biUnion V = Q.toConvexSpaceBody` with `Q` a `Kakeya.Plank a b`.  Over `δ`-tubes
with `δ > 0` the hull of a nonempty part is a Minkowski sum `K + closedBall 0 δ`, which has no
corner, whereas a plank carrier does (`Kakeya.convexHull_tubes_ne_prism`).  Hence
`Kakeya.localPlankFactorisation_hypotheses_uninhabited`.

**(ii) The scale ordering is backwards.**  The existing statement carries part (B)'s ordering
`δ ≤ ρ ≤ a ≤ b`.  In part (A) the planks sit *inside* the coarse `ρ`-tube — that is the entire
difference between the two halves — so the transverse width of an outer body is bounded by the
coarse radius, and the correct ordering is `δ ≤ a ≤ b ≤ ρ ≤ 1`.
`Kakeya.localPlankFactorisationRepaired_backwards_ordering_kills_gain` below makes this
mechanical *in the repaired vocabulary*: from `Kakeya.IsPlankOfDimensions Cw a b` on the part
hulls plus the coarse containment one gets `b ≤ Cw * ρ`, so under the existing ordering `ρ ≤ a`
the eccentricity gain obeys `Cw⁻¹ ≤ a / b`, i.e. it never exceeds the sub-polynomial budget
`Cw ≤ δ ^ (-η)` that the conclusion's `δ ^ (-ε)` already grants.

The two are **independent**: the containment repair of (i) leaves (ii) in force (that is what
`Kakeya.localPlankFactorisation_scaleOrder_collapses` and the theorem just named prove, both over
*repaired* data), and flipping the ordering leaves `parts_are_planks` unsatisfiable
(`convexHull_tubes_ne_prism` reads neither `ρ` nor `a` nor `b`).  Their common cause is one
geometric fact — in part (A) the planks live inside the coarse tube — with two separate effects.

## What this file contains

* `Kakeya.LocalPlankFactorisationRepairedStatement` — the faithful 6.6(A) as a `Prop`, in the
  *shape* of the existing statement (`∀ ε, ∃ η, ∃ δ₀, ∀ δ ≤ δ₀`, over
  `ShadedTube δ (EuclideanSpace ℝ (Fin 3))`, with the coarse family presented as
  `r`/`R`/`assign`, and with the Frostman constant `CF` supplied as a hypothesis) so that it is a
  drop-in replacement, and with the three repairs listed below.
* `Kakeya.tubeMultiplicityOfLocalPlankFactorisation_repaired` — **the proof.**  It is a citation
  of `Kakeya.multiplicity_le_of_factorsThroughFlatPrisms_of_coarseEssDistinct`
  (`Kakeya/Factoring/FlatPrisms.lean`, proved), plus the presentation work: the
  `∀ᶠ σ in 𝓝[>] 0` to `∃ δ₀` conversion, the two-sided-to-one-sided uniformity projection, the
  `ℝ≥0`-to-`ENNReal` coercions of the two `δ ^ (±η)` brackets, and the replacement of
  `frostmanConstIn` by the hypothesised `CF`.
* `Kakeya.LocalPlankFactorisationRepairedHypotheses` and
  `Kakeya.localPlankFactorisationRepaired_bound_of_hypotheses` — the statement's hypothesis
  block, isolated as a `Prop`, together with the lemma that pins it to the statement (the
  analogue here of the guardrail file's compatibility `example`).
* `Kakeya.exists_localPlankFactorisationRepairedHypotheses` — **the non-vacuity certificate.**
  Every hypothesis of the repaired statement is satisfiable at once, at explicit absolute
  constants and at arbitrarily small `δ`.  This is the clause that matters most here, because
  the existing statement's whole failure is that its hypotheses are contradictory.
* `Kakeya.nonempty_shadedUniformTubeSet_of_card_le` — the input the certificate needed and the
  tree did not have: every family of at most `C` distinct `σ`-tubes satisfies GWZ Definition
  2.2 at `C`, **two-sidedly**, on the prescribed family.
* `Kakeya.localPlankFactorisationRepaired_backwards_ordering_kills_gain` — defect (ii), in the
  repaired vocabulary.

## The three repairs, and the two hypotheses that are not in the existing statement

Repairs, relative to `Kakeya.tubeMultiplicityOfLocalPlankFactorisation`:

1. `Kakeya.PlankFactorization a b hab hb1 …` is replaced by
   `ConvexSpaceBody.Factorization … 2` together with
   `Kakeya.IsPlankFamilyOfDimensions Cw a b` on the part hulls.  This is `def:Factors` at the
   absolute constant `2` that `lemmafactmax` produces, plus `def:plank` read **two-sidedly with
   an explicit comparability constant** — the same `⪆`-rendered-as-`1` defect that the 6.6(B)
   side repaired with its `Cw`, here fixed by using the vocabulary the rest of the tree already
   speaks.
2. The ordering `δ ≤ ρ → ρ ≤ a` becomes `δ ≤ a → a ≤ b → b ≤ ρ → ρ ≤ 1`.
3. `C₀ ≤ δ ^ (-η)` disappears, `C₀` being the absolute `2`; `Cw` takes its place and is bound
   **before** `ε`, hence before `η` — because the plank comparability constant produced by the
   pigeonhole is not absolute.  `Cw` is *not* asked to be `≤ δ ^ (-η)`: it is a parameter of the
   statement, and a consumer that has `Cw ≤ δ ^ (-η)` gets the sub-polynomial reading for free.

Two hypotheses are present here and absent there, and both are load-bearing:

* **leaf-scale pairwise essential distinctness of `𝕋`.**  Not optional, and not a formalization
  convenience: replacing each tube by `M` copies multiplies `μ` by `M` and the right-hand side
  only by `M ^ (1 - β / 2)`, so without it 6.6(A) is *false* for every `β > 0`. GWZ supplies it
  at the outset (`lem:refineToEssDistinctLeaves`); its absence from the existing statement is a
  second reason that statement could never have been proved. * **pairwise essential distinctness of the coarse `ρ`-tubes.**  Implicit in GWZ's opening move
  "refine so that each fine tube belongs to a unique `ρ`-tube". It is a hypothesis and not a
  lemma here for a compiler-checked reason:
  `Kakeya.not_card_assignedParents_le_const_of_isFlatPrismFamily`
  (`Kakeya/Factoring/RhoFreeParentCount.lean`) exhibits configurations satisfying *every* other
  clause of this statement whose occupied-coarse-parent count inside one plank-shaped test body
  is `≍ ρ ^ (-1)`, so the outer-plank non-concentration step has no `ρ`-free constant without it.

## Presentation divergences that carry no mathematics

`{ι κ : Type u}` with `[DecidableEq ι] [DecidableEq κ]` replaces the existing statement's
`{ι : Type*}`, `{κ : Type}` and `open Classical`; the instances are what
`{i ∈ q | assign i = k}` and the cited theorem need.  The existing statement's `q = ∅` case is kept
(no nonemptiness hypothesis is added): it is discharged by `ShadedBody.multiplicity_empty`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

universe u

/-- **GWZ Proposition 6.6(A), faithfully.**

For the clause-by-clause comparison with the existing
`Kakeya.tubeMultiplicityOfLocalPlankFactorisation`, and for why each of the two extra
essential-distinctness hypotheses is load-bearing, see the module docstring.

The parameter order is the blueprint's choice order:
`β`, `K_KT(β)`, `K_F(β)`, `Cw` — then `ε` — then `η` and `δ₀`, which see nothing below them —
then `δ`, then the family, then `ρ, a, b`, then the coarse family and the plank factorisations. -/
def LocalPlankFactorisationRepairedStatement (β : ℝ) (Cw : ℝ≥0) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0),
    ∀ {ι κ : Type u} [DecidableEq ι] [DecidableEq κ]
      (q : Finset ι) {δ : ℝ≥0} (_hδ0 : 0 < δ)
      (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      δ ≤ δ₀ →
      (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (q : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      (∃ C : ℝ≥0, C ≤ δ ^ (-η) ∧
        Nonempty (ShadedTube.ShadedUniformTubeSet q T (Tube.ssfGridLen δ) C)) →
      (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
      ∀ (ρ a b : ℝ≥0), δ ≤ a → a ≤ b → b ≤ ρ → ρ ≤ 1 →
        ∀ (r : Finset κ) (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (assign : ι → κ),
          (∀ i ∈ q, assign i ∈ r ∧
            (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody) →
          (r : Set κ).Pairwise
            (fun k l => IsEssentiallyDistinct (R k).carrier (R l).carrier) →
          (∀ k ∈ r, ∃ F : ConvexSpaceBody.Factorization {i ∈ q | assign i = k}
                (fun i => (T i).toConvexSpaceBody) 2,
              IsPlankFamilyOfDimensions Cw a b F.parts
                (fun part =>
                  part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody))) →
          ∀ (CF : ENNReal), 1 ≤ CF → CF ≠ ⊤ →
            IsFrostmanIn q (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall CF →
            ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
              (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2)
                * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
                * (δ : ENNReal) ^ (-2 * β)
                * ((δ : ENNReal) ^ 2 * (q.card : ENNReal)) ^ (1 - β / 2)

/-- **GWZ Proposition 6.6(A) is provable as GWZ states it**, once the two defects of
`Kakeya.tubeMultiplicityOfLocalPlankFactorisation` are removed: the hull-equals-plank demand that
empties its datum, and its backwards scale ordering.

The mathematics is
`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms_of_coarseEssDistinct`
(`Kakeya/Factoring/FlatPrisms.lean`, proved from
`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms_of_parentPresentation` at parent dilation
`1`).  What is added here is presentation, in four steps, none of which touches the estimate:

* `∀ᶠ σ in 𝓝[>] 0` becomes `∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀`, via
  `mem_nhdsGT_iff_exists_Ioc_subset` — this is the blueprint's own `δ₀` and the shape the existing
  statement uses;
* GWZ Definition 2.2 proper (`ShadedTube.ShadedUniformTubeSet`, two-sided) is projected onto the
  one-sided `Kakeya.IsFlatPrismUniform` by
  `Kakeya.IsFlatPrismUniform.of_shadedUniformTubeSet`.  So this statement asks for **more**
  uniformity than the cited theorem needs; that is deliberate, because Definition 2.2 is what GWZ
  and the existing statement say.  Asking only for the one-sided half would give a strictly stronger
  theorem — `Kakeya.IsFlatPrismUniform` drops `ShadedTube.ShadedUniformTubeSet.le_card_shadeClass`
  and `ShadedTube.ShadedUniformTubeSet.branchingN_le` — with the same proof minus the projection
  line; it is not done here, because fidelity to Definition 2.2 is this file's point;
* `1 ≤ Cunif` is **not** assumed, exactly as the existing statement does not assume it: the constant
  is raised to `max Cunif 1` by `ShadedTube.ShadedUniformTubeSet.mono`, which stays inside the
  budget because `1 ≤ δ ^ (-η)` — and that is the only reason the produced `δ₀` is capped at `1`;
* the two `δ ^ (±η)` brackets are stated in `ℝ≥0` as in the existing statement and coerced by
  `ENNReal.coe_rpow_of_ne_zero`, which is where `0 < δ` is used;
* `frostmanConstIn 𝕋 B₁` is replaced by the hypothesised `C_F`, using
  `ConvexSpaceBody.frostmanConstIn_le` and monotonicity of `x ↦ x ^ (1 - β / 2)` — legitimate
  because `β ≤ 1`, so `1 - β / 2 ≥ 1 / 2 > 0`.

The `q = ∅` branch is kept, exactly as the existing statement kept it, so that no nonemptiness
hypothesis has to be added: `ShadedBody.multiplicity_empty`. -/
theorem tubeMultiplicityOfLocalPlankFactorisation_repaired {β : ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (Cw : ℝ≥0) (hCw : 1 ≤ Cw) :
    LocalPlankFactorisationRepairedStatement.{u} β Cw := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ :=
    multiplicity_le_of_factorsThroughFlatPrisms_of_coarseEssDistinct
      (E := EuclideanSpace ℝ (Fin 3)) finrank_euclideanSpace_fin hβpos.le hβle hKKT hKF Cw hCw
      ε hε
  rw [Filter.eventually_iff_exists_mem] at hev
  obtain ⟨U, hUmem, hUb⟩ := hev
  rw [mem_nhdsGT_iff_exists_Ioc_subset] at hUmem
  obtain ⟨u, hu, hIoc⟩ := hUmem
  rw [Set.mem_Ioi] at hu
  refine ⟨η, hη, min u 1, lt_min hu (by norm_num), ?_⟩
  intro ι κ _ _ q δ hδ0 T hδu hball hED hunif hfull ρ a b hδa hab hbρ hρ1 r R assign
    hassign hEDcoarse hFz CF hCF1 hCFtop hFr
  rcases q.eq_empty_or_nonempty with rfl | hq
  · simp
  have hδ1 : δ ≤ 1 := hδu.trans (min_le_right _ _)
  have h1le : (1 : ℝ≥0) ≤ δ ^ (-η) := by
    calc (1 : ℝ≥0) = δ ^ (0 : ℝ) := (NNReal.rpow_zero δ).symm
      _ ≤ δ ^ (-η) := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  obtain ⟨Cunif₀, hCunifδ₀, hU2⟩ := hunif
  obtain ⟨𝒰₀⟩ := hU2
  -- `1 ≤ Cunif` is not a hypothesis of GWZ 6.6(A) and is not assumed here: the constant is
  -- raised to `max Cunif₀ 1` by `ShadedTube.ShadedUniformTubeSet.mono`, and `1 ≤ δ ^ (-η)`
  -- because `δ ≤ 1` — which is why `δ₀` was capped at `1` above.
  set Cunif : ℝ≥0 := max Cunif₀ 1 with hCunifdef
  have hCunif1 : (1 : ℝ≥0) ≤ Cunif := le_max_right _ _
  have hCunifδ : Cunif ≤ δ ^ (-η) := max_le hCunifδ₀ h1le
  have 𝒰 : ShadedTube.ShadedUniformTubeSet q T (Tube.ssfGridLen δ) Cunif :=
    𝒰₀.mono (le_max_left _ _)
  have hδU : δ ∈ U := hIoc ⟨hδ0, hδu.trans (min_le_left _ _)⟩
  have hCunifE : (Cunif : ENNReal) ≤ (δ : ENNReal) ^ (-η) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hδ0.ne' (-η)]
    exact ENNReal.coe_le_coe.mpr hCunifδ
  have hfullE : (δ : ENNReal) ^ η ≤
      (ShadedBody.fullness q (fun i => (T i).toShadedBody) : ENNReal) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hδ0.ne' η]
    exact ENNReal.coe_le_coe.mpr hfull
  have hfam : IsFlatPrismFamily η Cunif q T :=
    { nonempty := hq
      unif := ⟨IsFlatPrismUniform.of_shadedUniformTubeSet 𝒰⟩
      ball := hball
      essDistinct := hED
      fullness := hfullE }
  have hbound := hUb δ hδU Cunif hCunif1 hCunifE a b ρ hδa hab hbρ hρ1 T R assign hfam
    (fun i hi => (hassign i hi).1) (fun i hi => (hassign i hi).2) hEDcoarse hFz
  refine hbound.trans ?_
  have hFC : frostmanConstIn q (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall ≤ CF := frostmanConstIn_le hFr
  have hexp : (0 : ℝ) ≤ 1 - β / 2 := by linarith
  have hpow : (frostmanConstIn q (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall) ^ (1 - β / 2) ≤ CF ^ (1 - β / 2) :=
    ENNReal.rpow_le_rpow hFC hexp
  rw [mul_comm ((q.card : ENNReal)) ((δ : ENNReal) ^ (2 : ℕ))]
  exact mul_le_mul_left (mul_le_mul_left (mul_le_mul_left
    (mul_le_mul_right hpow _) _) _) _

/-! ### GWZ Definition 2.2 for a small family, **two-sidedly**

`Kakeya.nonempty_isFlatPrismUniform_of_card_le` (`Kakeya/Factoring/RhoFreeParentCount.lean`)
shows that a family of at most `C` injectively indexed `σ`-tubes is `C`-uniform in the
**one-sided** sense of `Kakeya.IsFlatPrismUniform`.  The non-vacuity certificate below needs the
**two-sided** GWZ Definition 2.2, because that is what the repaired statement asks for, and no
producer of it for a prescribed family existed.  The identity hierarchy delivers it: every cover
class and every shade class is a *singleton*, so the two lower brackets that the one-sided
predicate drops — `Tube.UniformTubeSet.le_card_class` and
`ShadedTube.ShadedUniformTubeSet.le_card_shadeClass` — hold at `branchingN = localN = 1` for the
same reason the upper ones do.
-/

section SmallFamilyUniform

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **A family of at most `C` injectively indexed shaded `σ`-tubes satisfies GWZ Definition 2.2
at the constant `C`, two-sidedly**, at every grid length `N`.

The hierarchy is the identity one: each member is its own node at every grid scale, the node being
the member's own tube rescaled to the grid radius `ρ_k`.  Then every cover class `s⟨j⟩` and every
shade class is exactly `{j}`, so the four shaded brackets and the two class brackets all reduce to
`1 ≤ C`.

This is the two-sided companion of `Kakeya.nonempty_isFlatPrismUniform_of_card_le`, and unlike the
shaded uniformizers of `Kakeya/ShadedUniform.lean` it delivers Definition 2.2 **on the prescribed
family**, at no cardinality or mass loss — which is exactly what a non-vacuity certificate needs,
and is available only because the family is small. -/
theorem nonempty_shadedUniformTubeSet_of_card_le {σ : ℝ≥0} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    {ι : Type*} (s : Finset ι) (V : ι → ShadedTube σ E) (N : ℕ) {C : ℝ≥0} (hC : 1 ≤ C)
    (hcard : (s.card : ℝ≥0) ≤ C)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, (V i).toTube.x = (V j).toTube.x →
      (V i).toTube.y = (V j).toTube.y → i = j) :
    Nonempty (ShadedTube.ShadedUniformTubeSet s V N C) := by
  classical
  let gcs : Tube.GridCoverSystem s (fun i => (V i).toTube) N :=
    { indexSet := fun _ => s
      assign := fun _ i => i
      tube := fun k i => (V i).toTube.rescale (Tube.gridScale σ N k)
      assign_mem := by intro k hk i hi; exact hi
      le_tube_assign := by
        intro k hk i hi
        exact Tube.le_rescale (V i).toTube (le_gridScale_of_le hσ0 hσ1 hk)
      nested := by intro k hk i hi j hj h; exact h
      tube_nested := by
        intro k hk i hi
        exact Tube.rescale_le_rescale_of_radius_le (V i).toTube
          (Tube.gridScale_antitone hσ0 hσ1 N (Nat.le_succ k)) }
  have hclass : ∀ (k : ℕ) (j : ι),
      Tube.coverClass s (gcs.assign k) j ⊆ ({j} : Finset ι) := by
    intro k j i hi
    simp only [Tube.coverClass, Finset.mem_filter] at hi
    simpa using hi.2
  have hmemclass : ∀ (k : ℕ) (j : ι), j ∈ s → j ∈ Tube.coverClass s (gcs.assign k) j := by
    intro k j hj
    simp only [Tube.coverClass, Finset.mem_filter]
    exact ⟨hj, rfl⟩
  let utu : Tube.UniformTubeSet s (fun i => (V i).toTube) N C :=
    { cover := gcs
      branchingN := fun _ => 1
      tube_injOn := by
        intro k hk a ha b hb hab
        have hx : (V a).toTube.x = (V b).toTube.x := by
          have := congrArg Tube.x hab
          simpa [gcs, Tube.rescale] using this
        have hy : (V a).toTube.y = (V b).toTube.y := by
          have := congrArg Tube.y hab
          simpa [gcs, Tube.rescale] using this
        exact hinj a ha b hb hx hy
      boundedOverlap := by
        intro k hk W
        refine le_trans ?_ hcard
        exact_mod_cast Finset.card_filter_le _ _
      card_class_le := by
        intro k hk j hj
        have hcd : ((Tube.coverClass s (gcs.assign k) j).card : ℝ≥0) ≤ 1 := by
          exact_mod_cast (Finset.card_le_card (hclass k j)).trans (by simp)
        simpa using hcd.trans (by simpa using hC)
      le_card_class := by
        intro k hk j hj
        have hpos : 0 < (Tube.coverClass s (gcs.assign k) j).card :=
          Finset.card_pos.mpr ⟨j, hmemclass k j hj⟩
        have h1 : (1 : ℝ≥0) ≤ ((Tube.coverClass s (gcs.assign k) j).card : ℝ≥0) := by
          exact_mod_cast hpos
        simpa using le_trans hC (by
          simpa using mul_le_mul_right h1 C) }
  refine ⟨{ tubeUniform := utu
            branchingN := fun _ => 1
            localN := fun _ _ => 1
            card_shadeClass_le := ?_
            le_card_shadeClass := ?_
            branchingN_le := ?_
            le_branchingN := ?_ }⟩
  · intro x hx k hk i hi hxi
    have hsub := ShadedTube.shadeClass_subset s V (utu.cover.assign k)
      (utu.cover.assign k i) x
    have hsub2 : Tube.coverClass s (utu.cover.assign k) (utu.cover.assign k i)
        ⊆ ({i} : Finset ι) := by
      intro z hz
      simp only [Tube.coverClass, Finset.mem_filter] at hz
      simpa [utu, gcs] using hz.2
    have hle : ((ShadedTube.shadeClass s V (utu.cover.assign k)
        (utu.cover.assign k i) x).card : ℝ≥0) ≤ 1 := by
      exact_mod_cast (Finset.card_le_card (hsub.trans hsub2)).trans (by simp)
    simpa using hle.trans (by simpa using hC)
  · intro x hx k hk i hi hxi
    have hmem : i ∈ ShadedTube.shadeClass s V (utu.cover.assign k)
        (utu.cover.assign k i) x := by
      simp only [ShadedTube.shadeClass, Tube.coverClass, Finset.mem_filter]
      exact ⟨⟨hi, trivial⟩, hxi⟩
    have hpos : 0 < (ShadedTube.shadeClass s V (utu.cover.assign k)
        (utu.cover.assign k i) x).card := Finset.card_pos.mpr ⟨i, hmem⟩
    have h1 : (1 : ℝ≥0) ≤ ((ShadedTube.shadeClass s V (utu.cover.assign k)
        (utu.cover.assign k i) x).card : ℝ≥0) := by exact_mod_cast hpos
    simpa using le_trans hC (by simpa using mul_le_mul_right h1 C)
  · intro x hx k hk; simpa using hC
  · intro x hx k hk; simpa using hC

end SmallFamilyUniform

/-! ### Defect (ii), in the repaired vocabulary -/

/-- **The existing statement's scale ordering destroys the eccentricity gain, even after the datum
is repaired.**

From the *repaired* plank clause `Kakeya.IsPlankOfDimensions Cw a b` on the part hulls, together
with the coarse containment `T i ≤ R (assign i)` that GWZ 6.6(A) carries, one gets
`b ≤ Cw * ρ`: a plank inscribed in a `ρ`-tube has middle thickness at most the tube's radius, up
to the comparability constant.

Consequently, under the existing statement's own scale hypothesis `ρ ≤ a`, one has `b ≤ Cw * a`,
so its advertised gain obeys `(a / b) ^ (3 β / 2) ≥ Cw ^ (-3 β / 2)`.  Where `Cw ≤ δ ^ (-η)` — the
sub-polynomial budget every consumer imposes — the whole "gain" is inside the `δ ^ (-ε)` that the
conclusion already grants, so the ordering `ρ ≤ a` makes 6.6(A) quantitatively empty *even if its
datum is repaired*.  This is the second defect of the module docstring, and it is independent of
the first: nothing here mentions `parts_are_planks`, and no analytic input (`K_KT`, `K_F`) is used.

The companion over the older `Kakeya.ComparableBodyFactorization` datum is
`Kakeya.localPlankFactorisation_scaleOrder_collapses` (`Plank/Prop66AGuardrails.lean`), which
gives `b ≤ 2 * a`; this version is stated over the datum the repair actually uses, and it exhibits
the exact price, `Cw`. -/
theorem localPlankFactorisationRepaired_backwards_ordering_kills_gain
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {δ ρ a b Cw C₀ : ℝ≥0} (hCw : 1 ≤ Cw)
    {q : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {r : Finset κ} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))} {assign : ι → κ}
    (hq : q.Nonempty)
    (hassign : ∀ i ∈ q, assign i ∈ r ∧
      (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody)
    (hFz : ∀ k ∈ r, ∃ F : ConvexSpaceBody.Factorization {i ∈ q | assign i = k}
          (fun i => (T i).toConvexSpaceBody) C₀,
        IsPlankFamilyOfDimensions Cw a b F.parts
          (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody))) :
    b ≤ Cw * ρ := by
  classical
  obtain ⟨i, hi⟩ := hq
  obtain ⟨hk, -⟩ := hassign i hi
  obtain ⟨F, hdims⟩ := hFz (assign i) hk
  obtain ⟨part, hpart, hipart⟩ :=
    F.toFinpartition.exists_mem (Finset.mem_filter.2 ⟨hi, rfl⟩)
  have hne : part.Nonempty := ⟨i, hipart⟩
  have hsubfib : part ⊆ {i' ∈ q | assign i' = assign i} := F.subset hpart
  have hhull : part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody) ≤
      (R (assign i)).toConvexSpaceBody := by
    rw [hne.convexHull_biUnion_le_iff]
    intro i' hi'
    obtain ⟨hi'q, hi'k⟩ := Finset.mem_filter.1 (hsubfib hi')
    have := (hassign i' hi'q).2
    rwa [hi'k] at this
  have hlow : (Cw : ENNReal)⁻¹ * (b : ENNReal) ≤
      Metric.ethickness ℝ
        (part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier 1 :=
    (hdims part hpart).2.1.1
  have hmono : Metric.ethickness ℝ
      (part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier 1 ≤
      Metric.ethickness ℝ ((R (assign i)).carrier : Set (EuclideanSpace ℝ (Fin 3))) 1 :=
    Metric.ethickness_monotone (SetLike.coe_subset_coe.mpr hhull) 1
  have hρ : Metric.ethickness ℝ ((R (assign i)).carrier : Set (EuclideanSpace ℝ (Fin 3))) 1
      ≤ (ρ : ENNReal) := (R (assign i)).ethickness_one_le
  have hkey : (Cw : ENNReal)⁻¹ * (b : ENNReal) ≤ (ρ : ENNReal) :=
    hlow.trans (hmono.trans hρ)
  have hCw0 : (Cw : ENNReal) ≠ 0 := by
    simpa using (lt_of_lt_of_le zero_lt_one hCw).ne'
  have hfinal : (b : ENNReal) ≤ (Cw : ENNReal) * (ρ : ENNReal) := by
    calc (b : ENNReal) = (Cw : ENNReal) * ((Cw : ENNReal)⁻¹ * (b : ENNReal)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hCw0 ENNReal.coe_ne_top, one_mul]
      _ ≤ (Cw : ENNReal) * (ρ : ENNReal) := by
          exact mul_le_mul_right hkey _
  have := hfinal
  rw [← ENNReal.coe_mul] at this
  exact_mod_cast this

/-! ### Non-vacuity

The whole failure of `Kakeya.tubeMultiplicityOfLocalPlankFactorisation` is an *empty datum*
(`Kakeya.localPlankFactorisation_hypotheses_uninhabited`), so a restatement is worth nothing until
its hypotheses are exhibited.  This section does that, in the pattern of
`Kakeya.exists_globalPlankFactorization_singleton` (`Plank/Prop66BNonVacuity.lean`): the
hypothesis block is isolated as a `Prop`, *linked to the statement by a lemma* so that it cannot
drift from it, and then inhabited at explicit absolute constants and at arbitrarily small `δ`.
-/

/-- **The hypothesis block of `Kakeya.LocalPlankFactorisationRepairedStatement`**, isolated so
that its inhabitation can be stated as a theorem.

Kept honest by `Kakeya.localPlankFactorisationRepaired_bound_of_hypotheses`, which is the analogue
here of the compatibility `example` in `Plank/Prop66AGuardrails.lean`: it type-checks only while this
`Prop` really is the statement's hypothesis list, so a certificate for it really is a certificate
for the statement.  `q.Nonempty` is added — the statement itself does not need it, since it covers
`q = ∅` by `ShadedBody.multiplicity_empty`, but a certificate that produced `q = ∅` would certify
nothing. -/
def LocalPlankFactorisationRepairedHypotheses (η : ℝ) (Cw : ℝ≥0)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (q : Finset ι) {δ : ℝ≥0} (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (ρ a b : ℝ≥0) (r : Finset κ) (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (assign : ι → κ) : Prop :=
  0 < δ ∧ q.Nonempty ∧
    (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) ∧
    (q : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) ∧
    (∃ C : ℝ≥0, C ≤ δ ^ (-η) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet q T (Tube.ssfGridLen δ) C)) ∧
    (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) ∧
    δ ≤ a ∧ a ≤ b ∧ b ≤ ρ ∧ ρ ≤ 1 ∧
    (∀ i ∈ q, assign i ∈ r ∧
      (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody) ∧
    (r : Set κ).Pairwise
      (fun k l => IsEssentiallyDistinct (R k).carrier (R l).carrier) ∧
    (∀ k ∈ r, ∃ F : ConvexSpaceBody.Factorization {i ∈ q | assign i = k}
          (fun i => (T i).toConvexSpaceBody) 2,
        IsPlankFamilyOfDimensions Cw a b F.parts
          (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))

/-- **The link between `Kakeya.LocalPlankFactorisationRepairedHypotheses` and the statement.**

This is the guard on the non-vacuity certificate below.  It type-checks only while the `Prop` above
really is the hypothesis list of `Kakeya.LocalPlankFactorisationRepairedStatement`; if the
statement is ever edited, this lemma breaks rather than the certificate silently ceasing to
certify anything. -/
theorem localPlankFactorisationRepaired_bound_of_hypotheses {β : ℝ} {Cw : ℝ≥0}
    (hS : LocalPlankFactorisationRepairedStatement.{u} β Cw) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0),
      ∀ {ι κ : Type u} [DecidableEq ι] [DecidableEq κ]
        (q : Finset ι) {δ : ℝ≥0} (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (ρ a b : ℝ≥0) (r : Finset κ) (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
        (assign : ι → κ),
        δ ≤ δ₀ →
        LocalPlankFactorisationRepairedHypotheses η Cw q T ρ a b r R assign →
        ∀ (CF : ENNReal), 1 ≤ CF → CF ≠ ⊤ →
          IsFrostmanIn q (fun i => (T i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall CF →
          ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
            (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2)
              * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
              * (δ : ENNReal) ^ (-2 * β)
              * ((δ : ENNReal) ^ 2 * (q.card : ENNReal)) ^ (1 - β / 2) := by
  obtain ⟨η, hη, δ₀, hδ₀, hbound⟩ := hS ε hε
  refine ⟨η, hη, δ₀, hδ₀, ?_⟩
  intro ι κ _ _ q δ T ρ a b r R assign hδδ₀ hyp CF hCF1 hCFtop hFr
  obtain ⟨hδ0, -, hball, hED, hunif, hfull, hδa, hab, hbρ, hρ1, hassign, hEDr, hFz⟩ := hyp
  exact hbound q hδ0 T hδδ₀ hball hED hunif hfull ρ a b hδa hab hbρ hρ1 r R assign
    hassign hEDr hFz CF hCF1 hCFtop hFr

/-- The unit-length `σ`-tube whose core is the segment from `-e₀/2` to `e₀/2`; its carrier lies in
`closedBall 0 (1/2 + σ)`, hence in the unit ball as soon as `σ ≤ 1/2`. -/
def centralUnitTube (σ : ℝ≥0) : Tube σ (EuclideanSpace ℝ (Fin 3)) :=
  Tube.mk' σ
    (x := -((2 : ℝ)⁻¹ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))
    (y := (2 : ℝ)⁻¹ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
    (by
      rw [dist_eq_norm]
      have h : -((2 : ℝ)⁻¹ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
            - ((2 : ℝ)⁻¹ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
            = -(EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) := by module
      rw [h, norm_neg]
      rw [PiLp.norm_single]
      norm_num)

/-- A tube with its whole carrier shaded, so that the family `{T}` has fullness exactly `1`. -/
def fullyShadedTube {σ : ℝ≥0} (T : Tube σ (EuclideanSpace ℝ (Fin 3))) :
    ShadedTube σ (EuclideanSpace ℝ (Fin 3)) where
  toTube := T
  shade := T.carrier
  measurableSet_shade := T.isCompact.measurableSet
  shade_subset := subset_rfl

/-- The centre of `Kakeya.centralUnitTube` is the origin. -/
theorem midpoint_centralUnitTube (σ : ℝ≥0) :
    midpoint ℝ (centralUnitTube σ).x (centralUnitTube σ).y
      = (0 : EuclideanSpace ℝ (Fin 3)) := by
  show midpoint ℝ (-((2 : ℝ)⁻¹ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))
      ((2 : ℝ)⁻¹ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) = 0
  rw [midpoint_eq_smul_add]
  simp

/-- `Kakeya.centralUnitTube σ` lies in the closed unit ball whenever `σ ≤ 1 / 2`. -/
theorem centralUnitTube_carrier_subset_closedBall {σ : ℝ≥0} (hσ : σ ≤ 1 / 2) :
    ((centralUnitTube σ).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 1 := by
  have h := Tube.carrier_subset_closedBall_midpoint _ (centralUnitTube σ)
  rw [midpoint_centralUnitTube] at h
  refine h.trans (Metric.closedBall_subset_closedBall ?_)
  have : (σ : ℝ) ≤ 1 / 2 := by exact_mod_cast hσ
  linarith

/-- **The hypotheses of the repaired GWZ 6.6(A) are satisfiable, at arbitrarily small `δ`.**

For every fullness/uniformity exponent `η > 0`, every scale threshold `δ₀ > 0` and every plank
comparability constant `Cw ≥ 2` there is a leaf scale `δ ≤ δ₀` and a configuration meeting
**every** clause of `Kakeya.LocalPlankFactorisationRepairedHypotheses`: the fine family, its
containment in `B₁`, its leaf-scale essential distinctness, GWZ Definition 2.2 at the constant
`1`, fullness exactly `1`, the repaired scale ordering `δ ≤ a ≤ b ≤ ρ ≤ 1`, the coarse family,
its essential distinctness, and a `2`-factorisation of the fibre by bodies with the dimensions of
an `a × b × 1` plank.

The configuration is the one-member family `{0}` carrying the fully shaded `δ`-tube
`Kakeya.centralUnitTube δ`, inside the single coarse tube obtained by rescaling it to radius `1`,
at `a = b = δ` and `ρ = 1`.  The three `def:Factors` clauses come from
`Kakeya.exists_factorization_singleton`, the plank dimensions from
`Kakeya.isPlankOfDimensions_tube`, Definition 2.2 from
`Kakeya.nonempty_shadedUniformTubeSet_of_card_le`, and the coarse containment from
`Tube.le_rescale`.

**Contrast with the existing statement**: by
`Kakeya.localPlankFactorisation_hypotheses_uninhabited` its hypotheses admit *no* configuration
with `q` nonempty, at any scales whatsoever.  The repair therefore does not merely fix the
conclusion's bookkeeping; it turns an empty datum into an inhabited one.

**What is not certified, and is flagged rather than claimed**: a configuration with `a ≪ b`, i.e.
one that exercises the eccentricity gain.  That needs a part which is Frostman-dense in a flat
plank — a `δ`-net of about `b / δ` parallel tubes filling an `a × b × 1` plank — because
`def:Factors` (ii), `Δ_max(𝕍) ≤ 2 Δ(𝕍_t, W_t)`, fails for a sparse part: two tubes inside a
`δ × 1 × 1` plank have `Δ_max ≍ 1` while their density in the plank is `≍ δ`.  The certificate
below is therefore a certificate of inhabitation, exactly as
`Kakeya.exists_globalPlankFactorization_singleton` is on the 6.6(B) side, and not a certificate
that the gain factor is ever nontrivially exercised. -/
theorem exists_localPlankFactorisationRepairedHypotheses
    {η : ℝ} (hη : 0 < η) {δ₀ : ℝ≥0} (hδ₀ : 0 < δ₀) {Cw : ℝ≥0} (hCw : 2 ≤ Cw) :
    ∃ (δ : ℝ≥0) (T : ℕ → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (ρ a b : ℝ≥0) (R : ℕ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      0 < δ ∧ δ ≤ δ₀ ∧
      LocalPlankFactorisationRepairedHypotheses η Cw
        ({0} : Finset ℕ) T ρ a b ({0} : Finset ℕ) R (fun _ => 0) := by
  classical
  set δ : ℝ≥0 := min δ₀ (1 / 2) with hδdef
  have hδ0 : 0 < δ := lt_min hδ₀ (by norm_num)
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδ1 : δ ≤ 1 := hδhalf.trans (by norm_num)
  refine ⟨δ, fun _ => fullyShadedTube (centralUnitTube δ), 1, δ, δ,
    fun _ => (centralUnitTube δ).rescale 1, hδ0, hδδ₀, hδ0, ⟨0, by simp⟩, ?_, ?_, ?_, ?_,
    le_rfl, le_rfl, hδ1, le_rfl, ?_, ?_, ?_⟩
  · -- containment in the unit ball
    intro i _
    exact centralUnitTube_carrier_subset_closedBall hδhalf
  · -- leaf-scale essential distinctness, vacuous on a one-member family
    simp
  · -- GWZ Definition 2.2, two-sidedly, at the constant `1`
    refine ⟨1, ?_, ?_⟩
    · calc (1 : ℝ≥0) = δ ^ (0 : ℝ) := (NNReal.rpow_zero δ).symm
        _ ≤ δ ^ (-η) := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
    · exact nonempty_shadedUniformTubeSet_of_card_le hδ0 hδ1 ({0} : Finset ℕ)
        (fun _ => fullyShadedTube (centralUnitTube δ)) (Tube.ssfGridLen δ) le_rfl
        (by simp) (by
          intro i hi j hj _ _
          rw [Finset.mem_singleton] at hi hj
          rw [hi, hj])
  · -- fullness is exactly `1`
    have hvol := Tube.volume_pos_and_lt_top hδ0 hδ1 (centralUnitTube δ)
    have hf : (ShadedBody.fullness ({0} : Finset ℕ)
        (fun _ => (fullyShadedTube (centralUnitTube δ)).toShadedBody) : ENNReal) = 1 := by
      rw [ShadedBody.fullness_def]
      simp only [Finset.sum_singleton]
      exact ENNReal.div_self hvol.1.ne' hvol.2.ne
    have hf1 : ShadedBody.fullness ({0} : Finset ℕ)
        (fun _ => (fullyShadedTube (centralUnitTube δ)).toShadedBody) = 1 := by
      exact_mod_cast hf
    rw [hf1]
    exact NNReal.rpow_le_one hδ1 hη.le
  · -- the coarse containment, at the single coarse tube
    intro i _
    exact ⟨by simp, Tube.le_rescale (centralUnitTube δ) hδ1⟩
  · -- essential distinctness of the coarse family, vacuous on a one-member family
    simp
  · -- the plank factorisation of the fibre
    intro k hk
    rw [Finset.mem_singleton] at hk
    subst hk
    have hfib : {i ∈ ({0} : Finset ℕ) | (0 : ℕ) = 0} = ({0} : Finset ℕ) := by simp
    have hvol := Tube.volume_pos_and_lt_top hδ0 hδ1 (centralUnitTube δ)
    rw [hfib]
    obtain ⟨F, hFparts⟩ := exists_factorization_singleton
      (fun _ : ℕ => (fullyShadedTube (centralUnitTube δ)).toConvexSpaceBody) 0
      hvol.1 hvol.2.ne
    refine ⟨F, ?_⟩
    intro part hpart
    rw [hFparts, Finset.mem_singleton] at hpart
    subst hpart
    show IsPlankOfDimensions Cw δ δ
      (({0} : Finset ℕ).convexHull_biUnion
        (fun _ : ℕ => (fullyShadedTube (centralUnitTube δ)).toConvexSpaceBody))
    rw [Finset.convexHull_biUnion_singleton]
    exact isPlankOfDimensions_tube finrank_euclideanSpace_fin hδ1 hCw (centralUnitTube δ)

end Kakeya

end

end
