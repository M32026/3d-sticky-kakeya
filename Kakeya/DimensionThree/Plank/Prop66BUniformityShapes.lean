/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Prop66BUniverseFree
public import Kakeya.ChainUniform
public import Kakeya.Uniform.PerScale

/-!
# The two renderings of GWZ Definition 2.2 in Proposition 6.6(B), and what connects them

GWZ Definition 2.2 (a *uniform shaded family of tubes*) has two renderings in this development:

* the **grid** rendering `ShadedTube.ShadedUniformTubeSet q T N C`
  (`Kakeya/ShadedUniform.lean`), a nested hierarchy of covers along the geometric grid
  `ρ_k = δ^{k/N}`, `k ≤ N`, which is what the project statement
  `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` carries at `N = Tube.ssfGridLen δ`;
* the **per-scale** rendering `ShadedTube.IsUniform q T scales C`
  (`Kakeya/Uniform/PerScale.lean`), a family of unrelated single-scale bundles, one for each scale
  in `scales`, which the Part-(B) chain carried at `scales = Set.Icc δ 1`.

They are genuinely different objects.  The docstring of `Kakeya/Uniform.lean` says why the
per-scale rendering does not imply the grid one: it "relates the parent families at different
scales in *no way at all*", whereas the grid rendering carries a *nested* system of covers.  In the
other direction the grid rendering constrains the family only at the `N + 1` grid scales, so it
says nothing at a scale strictly between two of them.  **Neither implication is proved here or
anywhere in this development, and the second is not expected to be provable for a fixed family**:
comparability of the leaf counts at an intermediate scale is a pigeonhole conclusion, so it is
normally bought by passing to a subfamily.  That last sentence is a reading of the definitions, not
a theorem; what *is* below is the common refinement of §3.

## What this file establishes

**1. The Part-(B) chain never used the per-scale clause.**  Every statement of the chain

  `Kakeya.factoringAndMultPropGlobal_of_remark53` → `Kakeya.factoringAndMultPropGlobal`
  → `Kakeya.globalCoarsePlankFallback`
  → `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_masterScaleLemma61`
  → `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData`
  → `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData_univ`

carried `∃ C ≤ δ^(-η), Nonempty (ShadedTube.IsUniform q T (Set.Icc δ 1) C)` as a hypothesis, and
not one of them eliminated it: at the bottom of the chain it was `intro`d and never mentioned
again.  The binder has therefore been deleted from all six statements, which *strengthens* every
one of them; the compiler confirms that no proof step depended on it.  Uniformity has not
disappeared from the argument — it is absorbed into `Kakeya.Section6PartBData` and
`Kakeya.Section6PartBData.Remark53Prop51`, which the chain does consume — so the obligation moves
to whoever builds that datum, and it is *there* that the grid clause of Proposition 6.6(B) has to
be spent.

**2. Nothing is lost by the deletion**, and both renderings remain available: a hypothesis-free
theorem implies each of the two hypothesis-carrying forms.
`statement_of_universal_partBData_everyScaleUniform` pins the pre-deletion statement verbatim and
`statement_of_universal_partBData_everyScaleUniform_holds` proves it;
`statement_of_universal_partBData_gridUniform` is the same statement with the *grid*
clause — the one `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` actually supplies — and
`statement_of_universal_partBData_gridUniform_holds` proves that too.  So the Part-(B) chain is now
applicable, as far as uniformity is concerned, under either rendering and under none.

**3. The two renderings do meet, on the grid scale set.**  `Tube.gridScales δ N ⊆ Set.Icc δ 1`
(`gridScales_subset_Icc`), so the per-scale rendering restricts to `Tube.gridScales δ N`; and the
grid rendering *also* delivers the per-scale rendering there, with the constant squared, by the
recovery `Tube.ChainUniformTubeSet.uniformAt` that `Kakeya/Uniform.lean`'s docstring promises
("the containment reading is recoverable from it whenever some consumer of the old per-scale API
wants it").  `isUniform_gridScales_of_shadedUniformTubeSet` is the composite.  That is the honest
extent of the bridge: **on the grid scales, in the tube-level clause, in the direction
grid → per-scale.**  What is *not* here, and is not available, is the extension to non-grid scales
and the four shading clauses of `ShadedTube.IsUniform`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody
open scoped ENNReal NNReal

noncomputable section

universe u

namespace Kakeya

namespace Prop66BUniformity

/-! ### The scale sets -/

/-- **The grid scales lie in `[δ, 1]`.**  `δ = ρ_N ≤ ρ_k ≤ ρ_0 = 1` for `k ≤ N`, so the per-scale
rendering on `Set.Icc δ 1` restricts to the grid scale set at no cost. -/
theorem gridScales_subset_Icc {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ} (hN : 0 < N) :
    Tube.gridScales δ N ⊆ Set.Icc δ 1 := by
  rintro ρ ⟨k, hk, rfl⟩
  refine ⟨?_, Tube.gridScale_le_one hδ1 N k⟩
  have h := Tube.gridScale_antitone hδ0 hδ1 N hk
  rwa [Tube.gridScale_self δ hN] at h

/-! ### Restricting the per-scale rendering to a smaller scale set -/

section Restrict

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {ι : Type*} {δ : ℝ≥0}

/-- The tube-level per-scale rendering is antitone in the scale set. -/
theorem isUniform_of_subset_scales {s : Finset ι} {T : ι → Tube δ E} {scales scales' : Set ℝ≥0}
    {C : ℝ≥0} (hsub : scales' ⊆ scales) (h : Tube.IsUniform s T scales C) :
    Tube.IsUniform s T scales' C :=
  fun ρ hρ => h ρ (hsub hρ)

variable [MeasureSpace E]

/-- The shaded per-scale rendering is antitone in the scale set: every field is a `∀ ρ ∈ scales`,
so restricting the scale set restricts each of them. -/
def shadedIsUniform_of_subset_scales {s : Finset ι} {V : ι → ShadedTube δ E}
    {scales scales' : Set ℝ≥0} {C : ℝ≥0} (hsub : scales' ⊆ scales)
    (U : ShadedTube.IsUniform s V scales C) : ShadedTube.IsUniform s V scales' C where
  tubeUniform := isUniform_of_subset_scales hsub U.tubeUniform
  branchingN ρ hρ := U.branchingN ρ (hsub hρ)
  localUniform x hx ρ hρ := U.localUniform x hx ρ (hsub hρ)
  branchingN_le x hx ρ hρ := U.branchingN_le x hx ρ (hsub hρ)
  le_branchingN x hx ρ hρ := U.le_branchingN x hx ρ (hsub hρ)

end Restrict

/-! ### The per-scale rendering recovered from the grid rendering, on the grid scales -/

section Recover

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} {δ : ℝ≥0}

/-- **The grid hierarchy gives the per-scale rendering at the grid scales, with `C ^ 2`.**

This is the recovery the docstring of `Kakeya/Uniform.lean` promises: the class bracket of
`Tube.UniformTubeSet` implies the containment bracket of `Tube.IsUniformAtScale`, at the cost of
squaring the constant, because a node may contain members of at most `C` other classes.  The proof
is `Tube.UniformTubeSet.toChain` followed by `Tube.ChainUniformTubeSet.uniformAt`. -/
theorem isUniform_gridScales_of_uniformTubeSet {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : ℝ≥0} (𝒰 : Tube.UniformTubeSet s T N C) (hC : 1 ≤ C) :
    Tube.IsUniform s T (Tube.gridScales δ N) (C ^ 2) := by
  rintro ρ ⟨k, hk, rfl⟩
  exact ⟨𝒰.toChain.uniformAt hC hk⟩

variable [Nontrivial E] [MeasureSpace E] [BorelSpace E]

omit [Nontrivial E] [BorelSpace E] in
/-- **The tube-level clause of the per-scale rendering, from the grid rendering of Definition 2.2.**

`ShadedTube.IsUniform.tubeUniform` is the first of the five clauses of the per-scale rendering, and
it is the one the grid rendering supplies on the grid scale set.  The remaining four are the
shading clauses, which are stated against per-point bundles the grid rendering does not carry in
that form. -/
theorem isUniform_gridScales_of_shadedUniformTubeSet {s : Finset ι} {V : ι → ShadedTube δ E}
    {N : ℕ} {C : ℝ≥0} (𝒱 : ShadedTube.ShadedUniformTubeSet s V N C) (hC : 1 ≤ C) :
    Tube.IsUniform s (fun i => (V i).toTube) (Tube.gridScales δ N) (C ^ 2) :=
  isUniform_gridScales_of_uniformTubeSet 𝒱.tubeUniform hC

end Recover

/-! ### The two hypothesis-carrying forms of the Part-(B) chain, both recovered -/

/-- **The pre-deletion statement of
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData`, verbatim**, carrying the
per-scale rendering of Definition 2.2 on `Set.Icc δ 1`.

Kept as a named `Prop` rather than as a compatibility `example`, for the reason recorded at
`Kakeya.Prop66BScale.statement_of_universal_prop66B_freeCoarseScale`: a plain compatibility cannot
survive a changed binder.  It is *not* refuted — it is simply weaker than what is now proved. -/
def statement_of_universal_partBData_everyScaleUniform (Cprop : ℝ≥0) (β : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0), ∃ s₀ > (0 : ℝ≥0),
    ∀ {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (_hδ0 : 0 < δ)
      (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      δ ≤ δ₀ →
      (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (∃ C : ℝ≥0, C ≤ δ ^ (-η) ∧
        Nonempty (ShadedTube.IsUniform q T (Set.Icc δ 1) C)) →
      (q : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
      ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
        {κ : Type} (r : Finset κ)
        (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib CF C₀ : ℝ≥0),
        C₀ ≤ δ ^ (-η) → CF ≤ δ ^ (-η) → Cfib ≤ δ ^ (-η) →
        δ ≤ ρ → ρ ≤ a → δ ≤ s₀ * a →
        ∀ (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀),
        D.Remark53Prop51 Cprop →
        (D.factor.cells : Set D.factor.Cell).Pairwise
          (fun x y => _root_.IsEssentiallyDistinct
            (D.factor.repr x).carrier (D.factor.repr y).carrier) →
        ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
          (δ : ENNReal) ^ (-ε) * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
            * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β

/-- **The same statement with the grid rendering** — the clause
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` actually carries, at
`N = Tube.ssfGridLen δ`.  Neither this nor
`Kakeya.Prop66BUniformity.statement_of_universal_partBData_everyScaleUniform` implies the other;
both follow from the hypothesis-free theorem. -/
def statement_of_universal_partBData_gridUniform (Cprop : ℝ≥0) (β : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0), ∃ s₀ > (0 : ℝ≥0),
    ∀ {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (_hδ0 : 0 < δ)
      (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      δ ≤ δ₀ →
      (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (∃ C : ℝ≥0, C ≤ δ ^ (-η) ∧
        Nonempty (ShadedTube.ShadedUniformTubeSet q T (Tube.ssfGridLen δ) C)) →
      (q : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
      ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
        {κ : Type} (r : Finset κ)
        (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib CF C₀ : ℝ≥0),
        C₀ ≤ δ ^ (-η) → CF ≤ δ ^ (-η) → Cfib ≤ δ ^ (-η) →
        δ ≤ ρ → ρ ≤ a → δ ≤ s₀ * a →
        ∀ (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀),
        D.Remark53Prop51 Cprop →
        (D.factor.cells : Set D.factor.Cell).Pairwise
          (fun x y => _root_.IsEssentiallyDistinct
            (D.factor.repr x).carrier (D.factor.repr y).carrier) →
        ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
          (δ : ENNReal) ^ (-ε) * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
            * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β

/-- The pre-deletion form is still a theorem: the deleted binder was never used. -/
theorem statement_of_universal_partBData_everyScaleUniform_holds (Cprop : ℝ≥0) (hCprop : 1 ≤ Cprop)
    {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β) :
    statement_of_universal_partBData_everyScaleUniform Cprop β := by
  intro ε hε
  obtain ⟨η, hη, δ₀, hδ₀, s₀, hs₀, H⟩ :=
    tubeMultiplicityOfGlobalPlankFactorisation_of_partBData Cprop hCprop hβpos hβle hKKT hKF ε hε
  refine ⟨η, hη, δ₀, hδ₀, s₀, hs₀, ?_⟩
  intro ι q δ hδ0 T hδδ₀ hball _huni hED hfull ρ a b hab hb1 κ r R m Cfib CF C₀
    hC₀ hCF hCfib hδρ hρa hδsa D hRem hDED
  exact H q hδ0 T hδδ₀ hball hED hfull ρ a b hab hb1 r R m Cfib CF C₀
    hC₀ hCF hCfib hδρ hρa hδsa D hRem hDED

/-- The grid form — the one Proposition 6.6(B) supplies — is a theorem for the same reason. -/
theorem statement_of_universal_partBData_gridUniform_holds (Cprop : ℝ≥0) (hCprop : 1 ≤ Cprop)
    {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β) :
    statement_of_universal_partBData_gridUniform Cprop β := by
  intro ε hε
  obtain ⟨η, hη, δ₀, hδ₀, s₀, hs₀, H⟩ :=
    tubeMultiplicityOfGlobalPlankFactorisation_of_partBData Cprop hCprop hβpos hβle hKKT hKF ε hε
  refine ⟨η, hη, δ₀, hδ₀, s₀, hs₀, ?_⟩
  intro ι q δ hδ0 T hδδ₀ hball _huni hED hfull ρ a b hab hb1 κ r R m Cfib CF C₀
    hC₀ hCF hCfib hδρ hρa hδsa D hRem hDED
  exact H q hδ0 T hδδ₀ hball hED hfull ρ a b hab hb1 r R m Cfib CF C₀
    hC₀ hCF hCfib hδρ hρa hδsa D hRem hDED

end Prop66BUniformity

end Kakeya

end

end
