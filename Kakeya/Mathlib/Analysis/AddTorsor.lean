/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Algebra.Group.Torsor
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# AddTorsor of a T2Space is a T2Space

Honestly, this should be in Mathlib, but somehow `infer_instance` does not work here.
-/

@[expose] public section

variable {n : ℕ} {E S : Type*} [SeminormedAddCommGroup E] [T2Space E]
    [AddTorsor E S] [TopologicalSpace S] [IsTopologicalAddTorsor S]

instance : T2Space S := by
  obtain ⟨s⟩ := (by infer_instance : Nonempty S)
  apply T2Space.of_injective_continuous (f := fun v ↦ v -ᵥ s)
  · exact vsub_left_injective s
  · apply Continuous.vsub
    · exact continuous_id'
    · exact continuous_const
