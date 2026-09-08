/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Lipschitz
/-!
# Some elementary statements about Lipschitz functions.

-/

@[expose] public section

open Metric

namespace LipschitzWith
variable
  [PseudoEMetricSpace α] [EMetricSpace β] {K : NNReal} {s t : Set α} {f : α → β}

theorem subsingleton (h : LipschitzWith 0 f) : Set.Subsingleton (f '' s) := by
  intro x hx y hy
  simp only [Set.mem_image] at hx hy
  obtain ⟨a, _, hax⟩ := hx
  obtain ⟨b, _, hby⟩ := hy
  simpa [← hax, ← hby, ← edist_eq_zero] using h a b

theorem infEDist_le_mul_of_ne_zero {C} (hC : C ≠ 0) (h : LipschitzWith C f)
    (x : α) (s : Set α) : infEDist (f x) (f '' s) ≤ C * infEDist x s := by
  simp only [infEDist, ENNReal.mul_iInf_of_ne (ENNReal.coe_ne_zero.mpr hC) ENNReal.coe_ne_top]
  refine le_iInf₂ fun y hy => ?_
  exact (infEDist_le_edist_of_mem (Set.mem_image_of_mem f hy)).trans (h x y)

theorem infEDist_le_mul {C} (h : LipschitzWith C f) (x : α) {s : Set α} (hs : s.Nonempty) :
    infEDist (f x) (f '' s) ≤ C * infEDist x s := by
  by_cases hC : C = 0
  · obtain ⟨y, hy⟩ := hs
    calc infEDist (f x) (f '' s)
        ≤ edist (f x) (f y) := infEDist_le_edist_of_mem (Set.mem_image_of_mem f hy)
      _ = 0 := by have := hC ▸ h x y; simpa
      _ ≤ _ := zero_le
  · apply infEDist_le_mul_of_ne_zero hC h

end LipschitzWith
