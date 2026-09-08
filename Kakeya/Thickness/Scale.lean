/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Thickness.Basic
public import Kakeya.Mathlib.Convex.Body

/-!
Scale of a convex body is the minimal thickness
-/

@[expose] public section

open Metric

variable
  {V} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {P} [PseudoMetricSpace P] [NormedAddTorsor V P]
  {cs : Convexity.ConvexSpace ℝ P}

namespace ConvexSpaceBody

variable (K : @ConvexSpaceBody P _ cs)

/-- The scale of a convex body is its smallest affine thickness: the thickness at rank one less
than the ambient finrank. -/
noncomputable abbrev scale : ℝ :=
  thickness ℝ K.carrier (Module.finrank ℝ V - 1)

/-- The scale is at most every affine thickness of rank below the ambient dimension: it is the
smallest member of the decreasing sequence.  Blueprint `lem:convexBodyScale`. -/
theorem scale_le {n} (hn : n < Module.finrank ℝ V) :
    K.scale ≤ thickness ℝ K.carrier n := by
  apply thickness_antitone
  · exact K.isBounded
  · omega

/-- A real number is below the scale exactly when it is below every affine thickness of rank
below the ambient dimension.  Blueprint `lem:convexBodyScale`. -/
theorem le_scale_iff [FiniteDimensional ℝ V] [Nontrivial V] {δ : ℝ} :
    δ ≤ K.scale ↔
      ∀ n : ℕ, (n < Module.finrank ℝ V → δ ≤ thickness ℝ K.carrier n) := by
  constructor
  · intro h n hn
    grw [h]
    exact scale_le _ hn
  · intro h
    apply h (Module.finrank ℝ V - 1)
    simp [Module.finrank_pos]

/-- The bridge between the two scale APIs: the `ℝ≥0∞`-valued `Metric.ethickness.scale`, which is
the form the bulk of the development uses, is the `ENNReal.ofReal` of the `ℝ`-valued
`ConvexSpaceBody.scale`, which is the form a `Metric.cthickening` radius has to be given in. -/
theorem ethickness_scale_eq_ofReal_scale [FiniteDimensional ℝ V] [Nontrivial V] :
    Metric.ethickness.scale ℝ K.carrier = ENNReal.ofReal K.scale := by
  rw [Metric.ethickness.scale_eq]
  exact Metric.ethickness_thickness' K.isBounded _

end ConvexSpaceBody
