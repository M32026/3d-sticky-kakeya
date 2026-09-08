/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.KatzTao

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot

/-- The location clause produced by the plank-tube construction has a uniform
absolute radius once its width side condition is imposed. -/
theorem plankTube_dynamicBall_subset_elevenHalves
    {E : Type*} [NormedAddCommGroup E] {bq : NNReal} {A : Set E}
    (hbq : bq <= 1)
    (hA : A ⊆ Metric.closedBall (0 : E) (5 / 2 + 3 * (bq : Real))) :
    A ⊆ Metric.closedBall (0 : E) (11 / 2) := by
  refine hA.trans (Metric.closedBall_subset_closedBall ?_)
  have hbqR : (bq : Real) <= 1 := by exact_mod_cast hbq
  linarith

/-- Family form of `plankTube_dynamicBall_subset_elevenHalves`, matching the
location hypothesis of `multiplicity_coarse_raw_ball`. -/
theorem plankTube_family_subset_elevenHalves
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
    {κ : Type*} {t : Finset κ}
    {b bq : NNReal} (Tb : κ -> ShadedTube b E) (hbq : bq <= 1)
    (hloc : ∀ j ∈ t,
      (Tb j).carrier ⊆ Metric.closedBall (0 : E) (5 / 2 + 3 * (bq : Real))) :
    ∀ j ∈ t, (Tb j).carrier ⊆ Metric.closedBall (0 : E) (11 / 2) := by
  intro j hj
  exact plankTube_dynamicBall_subset_elevenHalves hbq (hloc j hj)

end Kakeya.ml1Boot
