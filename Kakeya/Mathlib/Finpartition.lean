/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Order.Partition.Finpartition

/-!
# Finpartition
-/

@[expose] public section

namespace Finset

/-- Blueprint `lem:sumOverDisjointBlocks`: summing a function over a family `P` of pairwise
disjoint finsets, block by block, gives the sum over their union `P.sup id`. -/
theorem sum_sum_eq_sum_sup_id [DecidableEq ι] {M : Type*} [AddCommMonoid M]
    {P : Finset (Finset ι)} (hP : (P : Set (Finset ι)).PairwiseDisjoint id) (f : ι → M) :
    ∑ t ∈ P, ∑ i ∈ t, f i = ∑ i ∈ P.sup id, f i := by
  rw [Finset.sup_eq_biUnion, Finset.sum_biUnion hP]
  rfl

end Finset

namespace Finpartition
variable
  [DecidableEq ι]
  {s : Finset ι}
  (P : Finpartition s)

/-- A Fubini-type formula -/
theorem sum_eq_sum_parts_sum {R} [AddCommMonoid R] (f : ι → R) :
    ∑ i ∈ s, f i = ∑ t ∈ P.parts, ∑ i ∈ t, f i := by
  grind [Finset.sum_biUnion P.disjoint, P.biUnion_parts]

end Finpartition
