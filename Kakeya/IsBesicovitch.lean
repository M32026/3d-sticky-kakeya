/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# The Kakeya Conjecture
-/

@[expose] public section

/--
A Besicovitch set is a compact subset of ${\mathbb{R}}^n$
that contains a unit line segment pointing in every direction.
(This definition is adapted from the one at FormalConjectures)
-/
def IsBesicovitch (S : Set (EuclideanSpace ℝ (Fin n))) :=
    IsCompact S ∧ ∀ v, ‖v‖ = 1 → ∃ a, affineSegment ℝ a (a + v) ⊆ S

/--
The Kakeya Set Conjecture
(This definition is adapted from the one at FormalConjectures)
-/
def KakeyaSetConjecture (n : ℕ) : Prop :=
  ∀ (S : Set (EuclideanSpace ℝ (Fin n))), IsBesicovitch S → dimH S = n
