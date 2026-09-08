/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.AffineMap

/-!
# Affine transport compatibility API

This file provides the parameter-free transport notation used by the three-dimensional slab
normalisation. The measure-theoretic content is supplied by Kakeya.AffineMap; the declarations
here package the canonical continuity and measurable-embedding proofs available for affine
equivalences of finite-dimensional spaces.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace Kakeya

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The absolute Jacobian of an affine equivalence. -/
def affineJacobian (f : E ≃ᵃ[ℝ] E) : ENNReal :=
  ENNReal.ofReal |LinearMap.det (f.linear : E →ₗ[ℝ] E)|

/-- The Jacobian of an affine equivalence is nonzero. -/
theorem affineJacobian_ne_zero (f : E ≃ᵃ[ℝ] E) : affineJacobian f ≠ 0 := by
  rw [affineJacobian]
  exact ENNReal.ofReal_ne_zero_iff.mpr
    (abs_pos.mpr (LinearEquiv.isUnit_det' f.linear).ne_zero)

/-- The Jacobian of an affine equivalence is finite. -/
theorem affineJacobian_ne_top (f : E ≃ᵃ[ℝ] E) : affineJacobian f ≠ ⊤ := by
  simp [affineJacobian]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Affine equivalences carry measurable sets to measurable sets. -/
theorem measurableSet_affineEquiv_image (f : E ≃ᵃ[ℝ] E) {A : Set E}
    (hA : MeasurableSet A) : MeasurableSet (f '' A) := by
  exact (AffineEquiv.toContinuousAffineEquiv f).toHomeomorph.measurableEmbedding
    |>.measurableSet_image' hA

/-- An affine equivalence scales every volume by its absolute Jacobian. -/
theorem volume_image_affineEquiv (f : E ≃ᵃ[ℝ] E) (A : Set E) :
    volume (f '' A) = affineJacobian f * volume A := by
  simpa [affineJacobian] using volume_affineImage f A

end Kakeya

namespace ConvexSpaceBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Transport a convex body along an affine equivalence. -/
def mapAffine (K : ConvexSpaceBody E) (f : E ≃ᵃ[ℝ] E) : ConvexSpaceBody E :=
  K.affineImage f.toAffineMap f.continuous_of_finiteDimensional

/-- The carrier of an affine transport is the affine image of the carrier. -/
@[simp]
theorem mapAffine_carrier (K : ConvexSpaceBody E) (f : E ≃ᵃ[ℝ] E) :
    (K.mapAffine f).carrier = f '' K.carrier := rfl

/-- Transporting forward and then backward recovers the original body. -/
theorem mapAffine_symm_mapAffine (K : ConvexSpaceBody E) (f : E ≃ᵃ[ℝ] E) :
    (K.mapAffine f).mapAffine f.symm = K := by
  apply ConvexSpaceBody.ext
  change (f.symm '' (f '' (K : Set E)) : Set E) = K
  rw [AffineEquiv.image_symm, Set.preimage_image_eq (K : Set E) f.injective]

/-- Transporting backward and then forward recovers the original body. -/
theorem symm_mapAffine_mapAffine (K : ConvexSpaceBody E) (f : E ≃ᵃ[ℝ] E) :
    (K.mapAffine f.symm).mapAffine f = K := by
  apply ConvexSpaceBody.ext
  change (f '' (f.symm '' (K : Set E)) : Set E) = K
  rw [Set.image_image]
  simp [AffineEquiv.apply_symm_apply]

/-- Affine transport preserves and reflects containment. -/
@[simp]
theorem mapAffine_le_mapAffine_iff {K L : ConvexSpaceBody E} (f : E ≃ᵃ[ℝ] E) :
    K.mapAffine f ≤ L.mapAffine f ↔ K ≤ L := by
  change f '' K.carrier ⊆ f '' L.carrier ↔ K.carrier ⊆ L.carrier
  exact Set.image_subset_image_iff f.injective

/-- Affine transport scales body volume by the absolute Jacobian. -/
theorem volume_mapAffine [MeasurableSpace E] [BorelSpace E]
    (K : ConvexSpaceBody E) (f : E ≃ᵃ[ℝ] E) :
    volume (K.mapAffine f).carrier = Kakeya.affineJacobian f * volume K.carrier := by
  change volume (f.toAffineMap '' K.carrier) = _
  simpa [Kakeya.affineJacobian] using Kakeya.volume_affineImage f K.carrier

end ConvexSpaceBody

namespace ShadedBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Transport a shaded body along an affine equivalence. -/
def mapAffine (V : ShadedBody E) (f : E ≃ᵃ[ℝ] E) : ShadedBody E :=
  V.affineImage f.toAffineMap f.continuous_of_finiteDimensional
    (AffineEquiv.toContinuousAffineEquiv f).toHomeomorph.measurableEmbedding

/-- The shading of an affine transport is the affine image of the shading. -/
@[simp]
theorem mapAffine_shade (V : ShadedBody E) (f : E ≃ᵃ[ℝ] E) :
    (V.mapAffine f).shade = f '' V.shade := rfl

/-- Multiplicity is invariant under affine transport. -/
theorem multiplicity_mapAffine {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E)
    (f : E ≃ᵃ[ℝ] E) :
    multiplicity s (fun i ↦ (V i).mapAffine f) = multiplicity s V := by
  simpa [mapAffine] using
    multiplicity_affineImage s V f f.continuous_of_finiteDimensional
      (AffineEquiv.toContinuousAffineEquiv f).toHomeomorph.measurableEmbedding

end ShadedBody

namespace Kakeya

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Density in a test body is invariant under affine transport. -/
theorem densityIn_mapAffine {ι : Type*} (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) (f : E ≃ᵃ[ℝ] E) :
    densityIn s (fun i ↦ (W i).mapAffine f) (K.mapAffine f) = densityIn s W K := by
  classical
  unfold densityIn
  have hfilter : s.filter (fun i ↦ (W i).mapAffine f ≤ K.mapAffine f) =
      s.filter (fun i ↦ W i ≤ K) := by
    apply Finset.filter_congr
    intro i _
    exact ConvexSpaceBody.mapAffine_le_mapAffine_iff f
  rw [hfilter]
  simp only [ConvexSpaceBody.volume_mapAffine]
  rw [← Finset.mul_sum, ENNReal.mul_div_mul_left _ _
    (affineJacobian_ne_zero f) (affineJacobian_ne_top f)]

/-- Maximal density is invariant under affine transport. -/
theorem maxDensity_mapAffine {ι : Type*} (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (f : E ≃ᵃ[ℝ] E) :
    maxDensity s (fun i ↦ (W i).mapAffine f) = maxDensity s W := by
  apply le_antisymm
  · rw [maxDensity_le_iff]
    intro K
    have hK : K = (K.mapAffine f.symm).mapAffine f :=
      (ConvexSpaceBody.symm_mapAffine_mapAffine K f).symm
    rw [hK, densityIn_mapAffine]
    exact le_maxDensity s W (K.mapAffine f.symm)
  · rw [maxDensity_le_iff]
    intro K
    rw [← densityIn_mapAffine s W K f]
    exact le_maxDensity s (fun i ↦ (W i).mapAffine f) (K.mapAffine f)

end Kakeya
