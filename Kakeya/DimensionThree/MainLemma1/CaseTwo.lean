/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Cases
public import Kakeya.DimensionThree.MainLemma1.Setup
public import Kakeya.DimensionThree.MainLemma1.FixedTreeRegularize
public import Kakeya.DimensionThree.MainLemma1.AnalyticEndgame
public import Kakeya.DimensionThree.MainLemma1.B3PostCertificateCoreW50
public import Kakeya.DimensionThree.MainLemma1.RichPostLedgerAssemblyUpstreamW50
public import Kakeya.DimensionThree.MainLemma1.CoarseBallUpstreamW50
public import Kakeya.DimensionThree.MainLemma1.CountedExactCoarseAnalyticW50
public import Kakeya.DimensionThree.MainLemma1.CountedHonestCoarseFieldW50
public import Kakeya.DimensionThree.MainLemma1.NoEDHonestCoarseConsumerW52
public import Kakeya.DimensionThree.MainLemma1.NoEDHonestCoarseAdapterW52
public import Kakeya.DimensionThree.MainLemma1.NoEDHonestCoarseReferenceAdapterW52
public import Kakeya.DimensionThree.MainLemma1.FullAmbientStructuralBridgeModuleW51
public import Kakeya.DimensionThree.MainLemma1.CountedExactCoarseW50
public import Kakeya.DimensionThree.MainLemma1.EndpointGeometryHonestEDW50
public import Kakeya.DimensionThree.MainLemma1.EndpointCountedGeometryW51
public import Kakeya.DimensionThree.MainLemma1.UpstreamMiddlePaymentsW50
public import Kakeya.DimensionThree.MainLemma1.UpstreamMiddlePaymentHelpersW50
public import Kakeya.DimensionThree.MainLemma1.UpstreamMiddleFrostmanW50
public import Kakeya.DimensionThree.MainLemma1.RawMiddleBlockModuleW51
public import Kakeya.DimensionThree.MainLemma1.EndpointPacketCoarseModuleW48
public import Kakeya.DimensionThree.MainLemma1.EndpointHonestMiddleDirectW48ModuleSafe
public import Kakeya.DimensionThree.MainLemma1.EndpointHierarchySelectedPacketModuleSafeW53
public import Kakeya.DimensionThree.MainLemma1.EndpointPacketHierarchyModuleBridgeSafeW48
public import Kakeya.DimensionThree.MainLemma1.EndpointMiddleSplitModuleSafeW53
public import Kakeya.DimensionThree.MainLemma1.CountedHonestTwoScaleAdapterW50
public import Kakeya.DimensionThree.MainLemma1.CountedSameWitnessAssemblyFieldsW50
public import Kakeya.DimensionThree.MainLemma1.FineEndpointBlockFacingW50
public import Kakeya.DimensionThree.MainLemma1.FullAmbientFirstSelectedW51
public import Kakeya.DimensionThree.MainLemma1.AmbientHonestFullSkeletonW51
public import Kakeya.DimensionThree.MainLemma1.HonestNoEDPaymentsW52
public import Kakeya.DimensionThree.MainLemma1.CountedExactCoarseActualProducerW50
public import Kakeya.DimensionThree.MainLemma1.UpstreamCountedRawProducerW50Module
public import Kakeya.DimensionThree.MainLemma1.RawCountedAdapterFieldsW51
public import Kakeya.DimensionThree.MainLemma1.FineEndpointCoreW50
public import Kakeya.DimensionThree.MainLemma1.RawAmbientMultiplicityBridgeW50
public import Kakeya.DimensionThree.MainLemma1.CanonicalMiddleUpstreamW50
public import Kakeya.DimensionThree.MainLemma1.FineEndpointCountedW50
public import Kakeya.DimensionThree.MainLemma1.AllCountedFineEndpointFieldUpstreamW50
public import Kakeya.DimensionThree.MainLemma1.ExactCountedMiddleW50
public import Kakeya.DimensionThree.MainLemma1.CaseTwoUpstreamSameWitnessW50
public import Kakeya.DimensionThree.MainLemma1.CaseTwoUpstreamRawFactorW50
public import Kakeya.DimensionThree.MainLemma1.CountedExactCoarseProductBridgeW50
public import Kakeya.DimensionThree.MainLemma1.ReorderedProductAssemblyW50
public import Kakeya.DimensionThree.MainLemma1.ReorderedProductAssemblyCorrectedW50
public import Kakeya.DimensionThree.MainLemma1.DirectFactorsHonestProductBridgeW50
public import Kakeya.DimensionThree.MainLemma1.DirectFactorsHonestProductBridgeCorrectedW50
public import Kakeya.DimensionThree.MainLemma1.QuotientAwareQV5W58
public import Kakeya.MultiScaleFac

/-!
# Case (ii) of GWZ Lemma 8.1: the dividing-block branch

`Kakeya.ml1Boot.exists_uniform_step_general` splits on
`StickyKakeya.dividingScalesFrostman`. The every-scale branch is treated in
`CaseOne.lean`; this file proves the dividing-block bound
`Kakeya.ml1Boot.multiplicity_le_caseTwoStep`.

The construction uses three index sets: the original family `s`, the banded
tube-uniform subfamily `s₂`, and the dichotomy's refinement `s' ⊆ s₂`.
The fullness bound on `s₂` is hereditary: every nonempty subfamily is
`δ ^ η₀`-full. This is needed because fullness is a ratio of two sums and a
bound on the whole family alone does not give the same bound on a subfamily.
The dichotomy retains all but a `StickyKakeya.totalLoss` share.

`Kakeya.ml1Boot.exists_factorTwoScales_of_frostmanDividingBlock` constructs
an `IsFactorTwoScales` bundle at the block endpoints
`τ = gridScale … b` and `θ = gridScale … a`. The fine, middle, coarse, and
collapse estimates from `Cases.lean` then yield the multiplicity conclusion,
with the additional `δ ^ (-ε')` slack.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya

namespace ml1Boot

universe u

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]





/-! ### The coarse end of a block: an unsatisfiable node clause

The Case (ii) construction layer, and in particular the protected endpoint
`Kakeya.ml1Boot.multiplicity_le_caseTwo`, asks its supplier for the two clauses

```
(∀ k ∈ 𝒰'.cover.indexSet b, (𝒰'.cover.tube b k).carrier ⊆ Metric.closedBall 0 1)
(∀ l' ∈ 𝒰'.cover.indexSet a, (𝒰'.cover.tube a l').carrier ⊆ Metric.closedBall 0 1)
```

— the node tubes at the two ends of the block lie in the unit ball.  Nothing in
`StickyKakeya.IsFrostmanDividingBlock` forbids `a = 0`: its clauses are `m < N`, `a < b` and
`b ≤ Tube.ssfGridLen δ`.  But `Tube.gridScale δ N 0 = 1`, so at `a = 0` the coarse node tubes are
`1`-tubes, and a `Kakeya.Tube` has a core of length exactly `1`, hence diameter `1 + 2 ρ`; by
`Kakeya.ml1Boot.tube_not_subset_closedBall_of_half_lt` no `ρ`-tube with `ρ > 1/2` lies in a ball
of radius `1`.  The clause therefore *cannot be met* at `a = 0` unless the hierarchy has no
level-`0` node at all, which by `Tube.GridCoverSystem.assign_mem` happens only for an empty leaf
set.

The consequence is recorded below and is a live gap in the intended Case (ii) route, not a
curiosity: `Kakeya.ml1Boot.multiplicity_le_caseTwo` is quantified over all `a`, and its `a = 0`
instance has a contradictory hypothesis bundle, so it says nothing there — while the case split
in `Kakeya.ml1Boot.exists_uniform_step_general` receives its `a` from
`StickyKakeya.dividingScalesFrostman` with no lower bound at all.  This is why
`Kakeya.ml1Boot.multiplicity_le_caseTwoStep` above carries **no** node-ball clause: a Case (ii)
statement that carried one would be closing its `a = 0` instance vacuously.
-/

/-- **A hierarchy whose level-`0` nodes lie in the unit ball has no leaves.**

`Tube.gridScale δ N 0 = 1`, so the level-`0` nodes are `1`-tubes, and no `ρ`-tube with `ρ > 1/2`
is contained in a ball of radius `1` (`Kakeya.ml1Boot.tube_not_subset_closedBall_of_half_lt`).
Every leaf is assigned to a level-`0` node, so a nonempty leaf set produces one. -/
theorem not_nodeBall_at_grid_zero {ι : Type u} [Nontrivial E] {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : Tube.UniformTubeSet s T N C)
    (hs : s.Nonempty)
    (hnode : ∀ k ∈ 𝒰.cover.indexSet 0,
      (𝒰.cover.tube 0 k).carrier ⊆ Metric.closedBall (0 : E) 1) :
    False := by
  obtain ⟨i, hi⟩ := hs
  have hmem := 𝒰.cover.assign_mem 0 (Nat.zero_le N) i hi
  have hsub := hnode _ hmem
  have hρ : (1 : ℝ) / 2 < ((Tube.gridScale δ N 0 : NNReal) : ℝ) := by
    rw [Tube.gridScale_zero]; norm_num
  exact tube_not_subset_closedBall_of_half_lt hρ (𝒰.cover.tube 0 (𝒰.cover.assign 0 i)) 0 hsub

/-- **The Case (ii) coarse node-ball clause is unsatisfiable at `a = 0`.**

Stated at the exact shape `Kakeya.ml1Boot.multiplicity_le_caseTwo` asks for.  Since
`StickyKakeya.IsFrostmanDividingBlock` permits `a = 0` and the leaf set of a Case (ii) hierarchy
is nonempty (`Kakeya.ml1Boot.caseTwoInput_nonempty`), that instance of the endpoint is a
statement over a contradictory bundle. -/
theorem not_caseTwoCoarseNodeBall_of_coarse_eq_zero {ι : Type u} [Nontrivial E] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰' : Tube.UniformTubeSet s' T N C) (hs' : s'.Nonempty) {a : ℕ} (ha : a = 0)
    (hcoarse : ∀ l' ∈ 𝒰'.cover.indexSet a,
      (𝒰'.cover.tube a l').carrier ⊆ Metric.closedBall (0 : E) 1) :
    False := by
  subst ha
  exact not_nodeBall_at_grid_zero 𝒰' hs' hcoarse

end ml1Boot

end Kakeya
