/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeFillSep

/-!
# `T-S2b`'s witness form: the fill from **any** subfamily attaining the maximum

`Kakeya.ML2Core.fillAt_one_of_maximizer` asks the level-`q` node's cells to be
`Kakeya.density_maximizer (𝒰.nodesUnder c k j) W` — the subfamily `Finset.exists_max_image`
**chooses**.  For `T-S2b` that is the wrong shape, and the reason is worth stating precisely.

 asks for a subfamily whose density maximizer is **proper**, so that the rescue by
restriction is demonstrably non-trivial.  But on the grid family the leaves are pairwise disjoint,
so `Kakeya.ML2Core.maxDensity_le_one_of_pairwiseDisjoint'` gives `Δ_max ≤ 1` while a single cell's
own density gives `Δ_max ≥ 1`: **the maximum is exactly `1` and *every* nonempty subfamily attains
it.**  Whether `density_maximizer` returns a *proper* subset is then a property of
`Classical.choice`, not of the configuration — and a certificate that depends on which subset the
choice function happens to pick certifies nothing.

`Kakeya.ML2Core.fillAt_one_of_maximizer_witness` removes the dependence: it asks only that the
level-`q` node's cells **attain** the maximum, whoever they are.  `T-S2b` can then exhibit a proper
witness and be a statement about the configuration.

The existing `Kakeya.ML2Core.fillAt_one_of_maximizer` (`Reduction/SpineFloorShapeFillSep.lean`, the estimate,
`decl_md5 69350e13652fa0a975176c13049f92b4`) is the *same statement* as the instance of the witness
form at `t := Kakeya.density_maximizer …`, whose `hattain` would be `rfl`.  **It is therefore not
restated here**: consumers needing the choice-based form call the existing name, and this file adds
only what the existing file does not have.  ((1) makes the witness form primary;
an earlier draft of this leaf carried a second copy of the existing statement, which is the
duplication the aggregator caught once already for `shade_le_of_comparableDensities`.)
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section FillWitness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ C : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}

omit [Nontrivial E] in
open scoped Classical in
/-- **`T-S2b`'s witness form.**  If the level-`q` node's cells **attain** the maximal density of the
level-`k` cells — whoever they are — and the node is no larger than their convex hull, then
`Kakeya.ML2Core.FillAt` holds at `κ = 1`.

The hypothesis is about a *witness*, not about `Kakeya.density_maximizer`'s choice; see the module
docstring for why that distinction is the whole point on a pairwise-disjoint family. -/
theorem fillAt_one_of_maximizer_witness (𝒰 : Tube.UniformTubeSet s T N C) {c k q : ℕ} {j jq : ι}
    (hsub : 𝒰.nodesUnder c q jq ⊆ 𝒰.nodesUnder c k j)
    (hattain : Kakeya.densityInConvexHulliUnion
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) (𝒰.nodesUnder c q jq)
      = Kakeya.maxDensity (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody))
    (hvol : volume (𝒰.cover.tube q jq).carrier
      ≤ volume (Convexity.convexHull ℝ (⋃ j' ∈ 𝒰.nodesUnder c q jq,
          (𝒰.cover.tube c j').carrier))) :
    FillAt 𝒰 1 q c jq := by
  classical
  unfold FillAt
  rw [ENNReal.ofReal_one, one_mul, densityIn_nodesUnder_self 𝒰 c q jq]
  calc Kakeya.maxDensity (𝒰.nodesUnder c q jq)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      ≤ Kakeya.maxDensity (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := Kakeya.maxDensity_mono _ hsub
    _ = (∑ j' ∈ 𝒰.nodesUnder c q jq, volume (𝒰.cover.tube c j').carrier)
        / volume (Convexity.convexHull ℝ (⋃ j' ∈ 𝒰.nodesUnder c q jq,
            (𝒰.cover.tube c j').carrier)) := hattain.symm
    _ ≤ (∑ j' ∈ 𝒰.nodesUnder c q jq, volume (𝒰.cover.tube c j').carrier)
        / volume (𝒰.cover.tube q jq).carrier := by gcongr

end FillWitness

/-! ### Control -/

section Control

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {ι : Type*}

omit [Nontrivial E] in
/-- **Control: attaining the maximum is strictly weaker than *being* the maximizer.**  Any subfamily
attaining `Δ_max` works, so `T-S2b` may exhibit a *proper* witness even when
`Kakeya.density_maximizer` picks the whole family.  Compiled as the fact that the witness hypothesis
is an equation on a *given* `t`, not an identification of `t` with the chosen maximizer: two
different `t` can both satisfy it. -/
theorem maximizer_witness_not_unique {s t : Finset ι} {W : ι → ConvexSpaceBody E}
    (hs : Kakeya.densityInConvexHulliUnion W s = Kakeya.maxDensity s W)
    (ht : Kakeya.densityInConvexHulliUnion W t = Kakeya.maxDensity s W) :
    Kakeya.densityInConvexHulliUnion W s = Kakeya.densityInConvexHulliUnion W t := by
  rw [hs, ht]

end Control

end Kakeya.ML2Core
