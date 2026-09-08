/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

import Kakeya.Tube.Basic -- shake: keep

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Transfer between Euclidean and sup-norm function spaces

This file records the measure-preserving identification between
`EuclideanSpace ℝ ι` and `ι → ℝ`, together with the one-sided metric comparison needed to
transfer upper bounds from the Euclidean metric to the sup metric.
-/

@[expose] public section

open scoped ENNReal NNReal MeasureTheory Topology Pointwise

namespace Kakeya.IsBesicovitch

/-- Forget the Euclidean (`ℓ²`) norm and regard a vector as a function with the sup norm. -/
def toPi {ι : Type*} (x : EuclideanSpace ℝ ι) : ι → ℝ :=
  WithLp.ofLp x

/-- Regard a real-valued function on a finite type as a vector in Euclidean space. -/
def fromPi {ι : Type*} (x : ι → ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 x

@[simp]
lemma toPi_fromPi {ι : Type*} (x : ι → ℝ) : toPi (fromPi x) = x := rfl

@[simp]
lemma fromPi_toPi {ι : Type*} (x : EuclideanSpace ℝ ι) : fromPi (toPi x) = x := rfl

/-- The canonical map from Euclidean space to the function space preserves Lebesgue volume. -/
lemma volume_image_toPi {ι : Type*} [Fintype ι] {S : Set (EuclideanSpace ℝ ι)}
    : MeasureTheory.volume (toPi '' S) = MeasureTheory.volume S := by
  rw [show toPi '' S = fromPi ⁻¹' S by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨fromPi x, hx, rfl⟩]
  exact MeasureTheory.MeasurePreserving.measure_preimage_equiv
    (f := MeasurableEquiv.toLp 2 (ι → ℝ)) (PiLp.volume_preserving_toLp ι) S

/-- The canonical map from the function space to Euclidean space preserves Lebesgue volume. -/
lemma volume_image_fromPi {ι : Type*} [Fintype ι] {S : Set (ι → ℝ)}
    : MeasureTheory.volume (fromPi '' S) = MeasureTheory.volume S := by
  rw [show fromPi '' S = toPi ⁻¹' S by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨toPi x, hx, rfl⟩]
  exact MeasureTheory.MeasurePreserving.measure_preimage_equiv
    (f := (MeasurableEquiv.toLp 2 (ι → ℝ)).symm) (PiLp.volume_preserving_ofLp ι) S

/-- The sup distance between the underlying functions is at most their Euclidean distance. -/
lemma dist_toPi_le {ι : Type*} [Fintype ι]
    (u v : EuclideanSpace ℝ ι) : dist (toPi u) (toPi v) ≤ dist u v := by
  rw [dist_eq_norm, pi_norm_le_iff_of_nonneg dist_nonneg]
  intro i
  have hi : dist (u i) (v i) ^ 2 ≤ ∑ j, dist (u j) (v j) ^ 2 := by
    refine Finset.single_le_sum (f := fun j ↦ dist (u j) (v j) ^ 2) ?_ (Finset.mem_univ i)
    intro j _
    positivity
  rw [EuclideanSpace.dist_eq]
  rw [show ‖(toPi u - toPi v) i‖ = dist (u i) (v i) by
    simp [toPi, Real.dist_eq, Real.norm_eq_abs]]
  exact (Real.sqrt_sq dist_nonneg).symm.le.trans (Real.sqrt_le_sqrt hi)

/-- The canonical identification commutes with real line segments. -/
lemma image_segment_toPi {ι : Type*} (x y : EuclideanSpace ℝ ι) :
    toPi '' segment ℝ x y = segment ℝ (toPi x) (toPi y) := by
  simpa [toPi] using
    (image_segment ℝ ((WithLp.linearEquiv 2 ℝ (ι → ℝ)).toAffineMap) x y)

/-- Mapping an open Euclidean thickening to the function space can only enlarge it. -/
lemma image_thickening_subset {ι : Type*} [Fintype ι] (δ : ℝ)
    (S : Set (EuclideanSpace ℝ ι)) :
    toPi '' Metric.thickening δ S ⊆ Metric.thickening δ (toPi '' S) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Metric.mem_thickening_iff] at hx ⊢
  obtain ⟨y, hy, hxy⟩ := hx
  exact ⟨toPi y, ⟨y, hy, rfl⟩, (dist_toPi_le x y).trans_lt hxy⟩

/-- Mapping a closed Euclidean thickening to the function space can only enlarge it. -/
lemma image_cthickening_subset {ι : Type*} [Fintype ι] (δ : ℝ) (hδ : 0 ≤ δ)
    (S : Set (EuclideanSpace ℝ ι)) :
    toPi '' Metric.cthickening δ S ⊆ Metric.cthickening δ (toPi '' S) := by
  rw [Metric.cthickening_eq_biUnion_closedBall S hδ]
  rintro _ ⟨x, hx, rfl⟩
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  rw [Metric.cthickening_eq_biUnion_closedBall (toPi '' S) hδ]
  refine Set.mem_iUnion.mpr ⟨toPi y, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact mem_closure_image
      (PiLp.continuous_ofLp (p := 2) (β := fun _ : ι ↦ ℝ)).continuousAt hy
  · exact (dist_toPi_le x y).trans hxy

end Kakeya.IsBesicovitch
