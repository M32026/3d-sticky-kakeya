/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimates
public import Kakeya.Mathlib.Analysis.InnerProductSpace
public import Kakeya.ShadedUniform

/-!
# Transport between three-dimensional real inner-product spaces

This file supplies the cross-space isometric transport needed to apply the coordinate model in
`EuclideanSpace ℝ (Fin 3)` to a theorem stated in an arbitrary real inner-product space of
finrank three.  The index types are unchanged by the transport.
-/

@[expose] public section

open MeasureTheory Metric

noncomputable section

namespace Kakeya

/-- The coordinate isometry associated to the standard orthonormal basis of a real
three-dimensional inner-product space. -/
def dimThreeLinearIsometryEquiv (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 3) :
    E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ((stdOrthonormalBasis ℝ E).reindex (finCongr hdim)).repr

@[simp]
theorem mem_image_linearIsometryEquiv_iff {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E ≃ₗᵢ[ℝ] F) (A : Set E) (x : F) :
    x ∈ f '' A ↔ f.symm x ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa
  · intro hx
    exact ⟨f.symm x, hx, f.apply_symm_apply x⟩

end Kakeya

namespace Metric

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Affine thickness is invariant under a surjective linear isometry. -/
theorem ethickness_image_linearIsometryEquiv (f : E ≃ₗᵢ[ℝ] F) (X : Set E) (n : ℕ) :
    ethickness ℝ (f '' X) n = ethickness ℝ X n := by
  apply le_antisymm
  · have h := (f.isometry.lipschitz.ethickness_image_le
      (f := f.toLinearEquiv.toAffineEquiv.toAffineMap) X) n
    simpa [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul] using h
  · have h := (f.symm.isometry.lipschitz.ethickness_image_le
      (f := f.symm.toLinearEquiv.toAffineEquiv.toAffineMap) (f '' X)) n
    have hss : f.symm.toLinearEquiv.toAffineEquiv.toAffineMap '' (f '' X) = X := by
      rw [Set.image_image]
      simp
    rw [hss] at h
    simpa [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul] using h

end Metric

namespace ConvexSpaceBody

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The image of a convex space body under a linear isometry equivalence between two spaces. -/
def mapLinearIsometryEquiv (K : ConvexSpaceBody E) (f : E ≃ₗᵢ[ℝ] F) : ConvexSpaceBody F where
  carrier := f '' K.carrier
  convex' :=
    (K.convex'.convex.affine_image f.toLinearEquiv.toAffineEquiv.toAffineMap).isConvexSet
  isCompact' := K.isCompact'.image f.continuous
  nonempty' := K.nonempty'.image f

@[simp]
theorem mapLinearIsometryEquiv_carrier (K : ConvexSpaceBody E) (f : E ≃ₗᵢ[ℝ] F) :
    (K.mapLinearIsometryEquiv f).carrier = f '' K.carrier := rfl

@[simp]
theorem mapLinearIsometryEquiv_symm_mapLinearIsometryEquiv
    (K : ConvexSpaceBody E) (f : E ≃ₗᵢ[ℝ] F) :
    (K.mapLinearIsometryEquiv f).mapLinearIsometryEquiv f.symm = K := by
  apply ConvexSpaceBody.ext
  change f.symm '' (f '' K.carrier) = K.carrier
  rw [Set.image_image]
  simp

@[simp]
theorem symm_mapLinearIsometryEquiv_mapLinearIsometryEquiv
    (K : ConvexSpaceBody F) (f : E ≃ₗᵢ[ℝ] F) :
    (K.mapLinearIsometryEquiv f.symm).mapLinearIsometryEquiv f = K := by
  apply ConvexSpaceBody.ext
  change f '' (f.symm '' K.carrier) = K.carrier
  rw [Set.image_image]
  simp

@[simp]
theorem mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff
    {K L : ConvexSpaceBody E} (f : E ≃ₗᵢ[ℝ] F) :
    K.mapLinearIsometryEquiv f ≤ L.mapLinearIsometryEquiv f ↔ K ≤ L := by
  change f '' K.carrier ⊆ f '' L.carrier ↔ K.carrier ⊆ L.carrier
  exact Set.image_subset_image_iff f.injective

/-- One-sided containment transport, allowing the body in the target space to be arbitrary. -/
@[simp]
theorem mapLinearIsometryEquiv_le_iff
    (K : ConvexSpaceBody E) (L : ConvexSpaceBody F) (f : E ≃ₗᵢ[ℝ] F) :
    K.mapLinearIsometryEquiv f ≤ L ↔ K ≤ L.mapLinearIsometryEquiv f.symm := by
  constructor
  · intro h x hx
    change x ∈ (L.mapLinearIsometryEquiv f.symm).carrier
    rw [mapLinearIsometryEquiv_carrier, Kakeya.mem_image_linearIsometryEquiv_iff]
    exact h (by
      change f x ∈ (K.mapLinearIsometryEquiv f).carrier
      rw [mapLinearIsometryEquiv_carrier]
      exact ⟨x, hx, rfl⟩)
  · intro h y hy
    change y ∈ L.carrier
    have hy' : y ∈ f '' K.carrier := by
      change y ∈ (K.mapLinearIsometryEquiv f).carrier at hy
      rwa [mapLinearIsometryEquiv_carrier] at hy
    rcases hy' with ⟨x, hx, rfl⟩
    have hback := h hx
    change x ∈ (L.mapLinearIsometryEquiv f.symm).carrier at hback
    rwa [mapLinearIsometryEquiv_carrier, Kakeya.mem_image_linearIsometryEquiv_iff] at hback

/-- The shortest affine scale is invariant under a linear isometry equivalence. -/
@[simp]
theorem mapLinearIsometryEquiv_scale (K : ConvexSpaceBody E) (f : E ≃ₗᵢ[ℝ] F) :
    (K.mapLinearIsometryEquiv f).scale = K.scale := by
  rw [scale, scale, ← f.toLinearEquiv.finrank_eq]
  rw [← Metric.toReal_ethickness (K.mapLinearIsometryEquiv f).isCompact'.isBounded,
    ← Metric.toReal_ethickness K.isCompact'.isBounded]
  congr 1
  exact Metric.ethickness_image_linearIsometryEquiv f K.carrier _

/-- Closed metric collars commute with a linear isometry equivalence. -/
@[simp]
theorem mapLinearIsometryEquiv_cthickening (K : ConvexSpaceBody E) (f : E ≃ₗᵢ[ℝ] F)
    (r : NNReal) :
    (K.cthickening r).mapLinearIsometryEquiv f =
      (K.mapLinearIsometryEquiv f).cthickening r := by
  apply ConvexSpaceBody.ext
  change f '' Metric.cthickening (r : ℝ) K.carrier =
    Metric.cthickening (r : ℝ) (f '' K.carrier)
  exact Metric.image_cthickening_isometryEquiv f.toIsometryEquiv (r : ℝ) K.carrier

end ConvexSpaceBody

namespace Tube

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A linear isometry equivalence sends a tube to the tube with the transported endpoints. -/
def mapLinearIsometryEquiv {δ : NNReal} (T : Tube δ E) (f : E ≃ₗᵢ[ℝ] F) : Tube δ F :=
  Tube.mk' δ (x := f T.x) (y := f T.y) (by simpa using T.dist_eq_one)

@[simp]
theorem mapLinearIsometryEquiv_x {δ : NNReal} (T : Tube δ E) (f : E ≃ₗᵢ[ℝ] F) :
    (T.mapLinearIsometryEquiv f).x = f T.x := rfl

@[simp]
theorem mapLinearIsometryEquiv_y {δ : NNReal} (T : Tube δ E) (f : E ≃ₗᵢ[ℝ] F) :
    (T.mapLinearIsometryEquiv f).y = f T.y := rfl

@[simp]
theorem mapLinearIsometryEquiv_center {δ : NNReal} (T : Tube δ E)
    (f : E ≃ₗᵢ[ℝ] F) :
    (T.mapLinearIsometryEquiv f).center = f T.center := by
  simp [Tube.center, midpoint_eq_smul_add]

@[simp]
theorem mapLinearIsometryEquiv_carrier {δ : NNReal} (T : Tube δ E)
    (f : E ≃ₗᵢ[ℝ] F) : (T.mapLinearIsometryEquiv f).carrier = f '' T.carrier := by
  have hseg : segment ℝ (f T.x) (f T.y) = f '' segment ℝ T.x T.y := by
    simpa using
      (image_segment ℝ f.toLinearEquiv.toAffineEquiv.toAffineMap T.x T.y).symm
  rw [(T.mapLinearIsometryEquiv f).carrier_eq, mapLinearIsometryEquiv_x,
    mapLinearIsometryEquiv_y, T.carrier_eq, Set.image_iUnion₂, hseg, Set.biUnion_image]
  refine Set.iUnion₂_congr fun z _ ↦ ?_
  exact (f.image_closedBall z δ).symm

@[simp]
theorem mapLinearIsometryEquiv_toConvexSpaceBody {δ : NNReal} (T : Tube δ E)
    (f : E ≃ₗᵢ[ℝ] F) :
    (T.mapLinearIsometryEquiv f).toConvexSpaceBody =
      T.toConvexSpaceBody.mapLinearIsometryEquiv f := by
  apply ConvexSpaceBody.ext
  exact T.mapLinearIsometryEquiv_carrier f

@[simp]
theorem mapLinearIsometryEquiv_symm_mapLinearIsometryEquiv {δ : NNReal}
    (T : Tube δ E) (f : E ≃ₗᵢ[ℝ] F) :
    (T.mapLinearIsometryEquiv f).mapLinearIsometryEquiv f.symm = T := by
  apply Tube.ext
  · rw [mapLinearIsometryEquiv_carrier, mapLinearIsometryEquiv_carrier, Set.image_image]
    simp
  · simp
  · simp

/-- Containment can be tested after transporting the left tube into the target space
or, equivalently, after pulling the right tube back to the source space. -/
@[simp]
theorem mapLinearIsometryEquiv_le_iff {δ ρ : NNReal} (T : Tube δ E) (U : Tube ρ F)
    (f : E ≃ₗᵢ[ℝ] F) :
    (T.mapLinearIsometryEquiv f).toConvexSpaceBody ≤ U.toConvexSpaceBody ↔
      T.toConvexSpaceBody ≤ (U.mapLinearIsometryEquiv f.symm).toConvexSpaceBody := by
  rw [mapLinearIsometryEquiv_toConvexSpaceBody, mapLinearIsometryEquiv_toConvexSpaceBody]
  exact ConvexSpaceBody.mapLinearIsometryEquiv_le_iff T.toConvexSpaceBody U.toConvexSpaceBody f

end Tube

namespace ShadedBody

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Cross-space isometric transport of a shaded convex body. -/
def mapLinearIsometryEquiv (V : ShadedBody E) (f : E ≃ₗᵢ[ℝ] F) : ShadedBody F where
  toConvexSpaceBody := V.toConvexSpaceBody.mapLinearIsometryEquiv f
  shade := f '' V.shade
  measurableSet_shade := by
    change MeasurableSet (f '' V.shade)
    rw [show f '' V.shade = (f.symm : F → E) ⁻¹' V.shade by
      exact congrFun
        (Set.image_eq_preimage_of_inverse f.symm_apply_apply f.apply_symm_apply) V.shade]
    exact f.symm.continuous.measurable V.measurableSet_shade
  shade_subset := Set.image_mono V.shade_subset

@[simp]
theorem mapLinearIsometryEquiv_carrier (V : ShadedBody E) (f : E ≃ₗᵢ[ℝ] F) :
    (V.mapLinearIsometryEquiv f).carrier = f '' V.carrier := rfl

@[simp]
theorem mapLinearIsometryEquiv_shade (V : ShadedBody E) (f : E ≃ₗᵢ[ℝ] F) :
    (V.mapLinearIsometryEquiv f).shade = f '' V.shade := rfl

end ShadedBody

namespace Kakeya

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Linear isometry equivalences preserve Euclidean volume across ambient spaces. -/
theorem volume_image_linearIsometryEquiv (f : E ≃ₗᵢ[ℝ] F) (A : Set E) :
    volume (f '' A) = volume A := by
  rw [show f '' A = (f.symm : F → E) ⁻¹' A by
    exact congrFun
      (Set.image_eq_preimage_of_inverse f.symm_apply_apply f.apply_symm_apply) A]
  let e : F ≃ᵐ E := f.symm.toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e volume volume := f.symm.measurePreserving
  exact he.measure_preimage_equiv A

end Kakeya

namespace ShadedTube

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Cross-space isometric transport of a shaded tube. -/
def mapLinearIsometryEquiv {δ : NNReal} (V : ShadedTube δ E)
    (f : E ≃ₗᵢ[ℝ] F) : ShadedTube δ F where
  __ := V.toTube.mapLinearIsometryEquiv f
  shade := f '' V.shade
  measurableSet_shade := by
    change MeasurableSet (f '' V.shade)
    rw [show f '' V.shade = (f.symm : F → E) ⁻¹' V.shade by
      exact congrFun
        (Set.image_eq_preimage_of_inverse f.symm_apply_apply f.apply_symm_apply) V.shade]
    exact f.symm.continuous.measurable V.measurableSet_shade
  shade_subset := by
    rw [Tube.mapLinearIsometryEquiv_carrier]
    exact Set.image_mono V.shade_subset

@[simp]
theorem mapLinearIsometryEquiv_toTube {δ : NNReal} (V : ShadedTube δ E)
    (f : E ≃ₗᵢ[ℝ] F) :
    (V.mapLinearIsometryEquiv f).toTube = V.toTube.mapLinearIsometryEquiv f := rfl

@[simp]
theorem mapLinearIsometryEquiv_carrier {δ : NNReal} (V : ShadedTube δ E)
    (f : E ≃ₗᵢ[ℝ] F) : (V.mapLinearIsometryEquiv f).carrier = f '' V.carrier := by
  exact Tube.mapLinearIsometryEquiv_carrier V.toTube f

@[simp]
theorem mapLinearIsometryEquiv_shade {δ : NNReal} (V : ShadedTube δ E)
    (f : E ≃ₗᵢ[ℝ] F) : (V.mapLinearIsometryEquiv f).shade = f '' V.shade := rfl

@[simp]
theorem mapLinearIsometryEquiv_toConvexSpaceBody {δ : NNReal} (V : ShadedTube δ E)
    (f : E ≃ₗᵢ[ℝ] F) :
    (V.mapLinearIsometryEquiv f).toConvexSpaceBody =
      V.toConvexSpaceBody.mapLinearIsometryEquiv f := by
  exact Tube.mapLinearIsometryEquiv_toConvexSpaceBody V.toTube f

variable {ι : Type*}

/-- The untruncated fullness ratio is invariant under cross-space isometric transport. -/
@[simp]
theorem fullness'_mapLinearIsometryEquiv {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ E) (f : E ≃ₗᵢ[ℝ] F) :
    ShadedBody.fullness' s (fun i => (V i).mapLinearIsometryEquiv f |>.toShadedBody) =
      ShadedBody.fullness' s (fun i => (V i).toShadedBody) := by
  unfold ShadedBody.fullness'
  congr 1
  · exact Finset.sum_congr rfl fun i _ =>
      Kakeya.volume_image_linearIsometryEquiv f (V i).shade
  · exact Finset.sum_congr rfl fun i _ => by
      rw [mapLinearIsometryEquiv_carrier]
      exact Kakeya.volume_image_linearIsometryEquiv f (V i).carrier

/-- Fullness of a shaded-tube family is invariant under cross-space isometric transport. -/
@[simp]
theorem fullness_mapLinearIsometryEquiv {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ E) (f : E ≃ₗᵢ[ℝ] F) :
    ShadedBody.fullness s (fun i => (V i).mapLinearIsometryEquiv f |>.toShadedBody) =
      ShadedBody.fullness s (fun i => (V i).toShadedBody) := by
  unfold ShadedBody.fullness ShadedBody.fullness'
  have hshade : (∑ i ∈ s, volume ((V i).mapLinearIsometryEquiv f).shade) =
      ∑ i ∈ s, volume (V i).shade := by
    exact Finset.sum_congr rfl fun i _ => Kakeya.volume_image_linearIsometryEquiv f (V i).shade
  have hcarrier : (∑ i ∈ s, volume ((V i).mapLinearIsometryEquiv f).carrier) =
      ∑ i ∈ s, volume (V i).carrier := by
    exact Finset.sum_congr rfl fun i _ => by
      rw [mapLinearIsometryEquiv_carrier]
      exact Kakeya.volume_image_linearIsometryEquiv f (V i).carrier
  rw [hshade, hcarrier]

/-- The shading-union volume of a shaded-tube family is invariant under isometric transport. -/
@[simp]
theorem volume_iUnion_mapLinearIsometryEquiv_shade {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ E) (f : E ≃ₗᵢ[ℝ] F) :
    volume (⋃ i ∈ s, ((V i).mapLinearIsometryEquiv f).shade) =
      volume (⋃ i ∈ s, (V i).shade) := by
  rw [show (⋃ i ∈ s, ((V i).mapLinearIsometryEquiv f).shade) =
      f '' (⋃ i ∈ s, (V i).shade) by simp [Set.image_iUnion₂]]
  exact Kakeya.volume_image_linearIsometryEquiv f _

/-- Multiplicity of a shaded-tube family is invariant under isometric transport. -/
@[simp]
theorem multiplicity_mapLinearIsometryEquiv {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ E) (f : E ≃ₗᵢ[ℝ] F) :
    ShadedBody.multiplicity s (fun i => (V i).mapLinearIsometryEquiv f |>.toShadedBody) =
      ShadedBody.multiplicity s (fun i => (V i).toShadedBody) := by
  unfold ShadedBody.multiplicity
  rw [volume_iUnion_mapLinearIsometryEquiv_shade]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Kakeya.volume_image_linearIsometryEquiv f (V i).shade

end ShadedTube

namespace Tube

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {ι : Type*}

/-- Transport every geometric tube in a grid cover while preserving its exact index tree. -/
def GridCoverSystem.mapLinearIsometryEquiv {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} (G : GridCoverSystem s T N)
    (f : E ≃ₗᵢ[ℝ] F) :
    GridCoverSystem s (fun i => (T i).mapLinearIsometryEquiv f) N where
  indexSet := G.indexSet
  assign := G.assign
  tube k j := (G.tube k j).mapLinearIsometryEquiv f
  assign_mem := G.assign_mem
  le_tube_assign := by
    intro k hk i hi
    simpa only [Tube.mapLinearIsometryEquiv_toConvexSpaceBody,
      ConvexSpaceBody.mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff] using
      G.le_tube_assign k hk i hi
  nested := G.nested
  tube_nested := by
    intro k hk i hi
    simpa only [Tube.mapLinearIsometryEquiv_toConvexSpaceBody,
      ConvexSpaceBody.mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff] using
      G.tube_nested k hk i hi

@[simp]
theorem GridCoverSystem.mapLinearIsometryEquiv_indexSet {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} (G : GridCoverSystem s T N)
    (f : E ≃ₗᵢ[ℝ] F) :
    (G.mapLinearIsometryEquiv f).indexSet = G.indexSet := rfl

@[simp]
theorem GridCoverSystem.mapLinearIsometryEquiv_assign {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} (G : GridCoverSystem s T N)
    (f : E ≃ₗᵢ[ℝ] F) :
    (G.mapLinearIsometryEquiv f).assign = G.assign := rfl

@[simp]
theorem GridCoverSystem.mapLinearIsometryEquiv_tube {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} (G : GridCoverSystem s T N)
    (f : E ≃ₗᵢ[ℝ] F) (k : ℕ) (j : ι) :
    (G.mapLinearIsometryEquiv f).tube k j =
      (G.tube k j).mapLinearIsometryEquiv f := rfl

/-- Isometric transport of a uniform hierarchy.  The node indices, assignments,
and branching numbers are definitionally the original ones. -/
def UniformTubeSet.mapLinearIsometryEquiv {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (U : UniformTubeSet s T N C)
    (f : E ≃ₗᵢ[ℝ] F) :
    UniformTubeSet s (fun i => (T i).mapLinearIsometryEquiv f) N C where
  cover := U.cover.mapLinearIsometryEquiv f
  branchingN := U.branchingN
  tube_injOn := by
    intro k hk j hj j' hj' heq
    apply U.tube_injOn k hk hj hj'
    have h := congrArg (fun W => W.mapLinearIsometryEquiv f.symm) heq
    simpa using h
  boundedOverlap := by
    intro k hk V
    have hfilter :
        (U.cover.indexSet k).filter (fun j => ∃ i ∈ s,
          ((T i).mapLinearIsometryEquiv f).toConvexSpaceBody ≤
            ((U.cover.tube k j).mapLinearIsometryEquiv f).toConvexSpaceBody ∧
          ((T i).mapLinearIsometryEquiv f).toConvexSpaceBody ≤ V.toConvexSpaceBody) =
        (U.cover.indexSet k).filter (fun j => ∃ i ∈ s,
          (T i).toConvexSpaceBody ≤ (U.cover.tube k j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤
            (V.mapLinearIsometryEquiv f.symm).toConvexSpaceBody) := by
      apply Finset.filter_congr
      intro j hj
      constructor
      · rintro ⟨i, hi, hnode, htest⟩
        exact ⟨i, hi,
          (ConvexSpaceBody.mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff f).mp
            (by simpa only [Tube.mapLinearIsometryEquiv_toConvexSpaceBody] using hnode),
          (Tube.mapLinearIsometryEquiv_le_iff (T i) V f).mp htest⟩
      · rintro ⟨i, hi, hnode, htest⟩
        exact ⟨i, hi,
          (by
            simpa only [Tube.mapLinearIsometryEquiv_toConvexSpaceBody] using
              (ConvexSpaceBody.mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff f).mpr
                hnode),
          (Tube.mapLinearIsometryEquiv_le_iff (T i) V f).mpr htest⟩
    change ((U.cover.indexSet k).filter (fun j => ∃ i ∈ s,
      ((T i).mapLinearIsometryEquiv f).toConvexSpaceBody ≤
        ((U.cover.tube k j).mapLinearIsometryEquiv f).toConvexSpaceBody ∧
      ((T i).mapLinearIsometryEquiv f).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤ C
    rw [hfilter]
    exact U.boundedOverlap k hk (V.mapLinearIsometryEquiv f.symm)
  card_class_le := U.card_class_le
  le_card_class := U.le_card_class

@[simp]
theorem UniformTubeSet.mapLinearIsometryEquiv_cover {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (U : UniformTubeSet s T N C)
    (f : E ≃ₗᵢ[ℝ] F) :
    (U.mapLinearIsometryEquiv f).cover = U.cover.mapLinearIsometryEquiv f := rfl

@[simp]
theorem UniformTubeSet.mapLinearIsometryEquiv_branchingN {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (U : UniformTubeSet s T N C)
    (f : E ≃ₗᵢ[ℝ] F) :
    (U.mapLinearIsometryEquiv f).branchingN = U.branchingN := rfl

end Tube

namespace ShadedTube

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {ι : Type*}

@[simp]
theorem shadeClass_mapLinearIsometryEquiv {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ E) (assign : ι → ι) (j : ι) (x : F)
    (f : E ≃ₗᵢ[ℝ] F) :
    shadeClass s (fun i => (V i).mapLinearIsometryEquiv f) assign j x =
      shadeClass s V assign j (f.symm x) := by
  classical
  ext i
  simp only [shadeClass, Finset.mem_filter, mapLinearIsometryEquiv_shade]
  rw [Kakeya.mem_image_linearIsometryEquiv_iff]

@[simp]
theorem mem_iUnion_mapLinearIsometryEquiv_shade_iff {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ E) (x : F) (f : E ≃ₗᵢ[ℝ] F) :
    x ∈ (⋃ i ∈ s, ((V i).mapLinearIsometryEquiv f).shade) ↔
      f.symm x ∈ (⋃ i ∈ s, (V i).shade) := by
  rw [show (⋃ i ∈ s, ((V i).mapLinearIsometryEquiv f).shade) =
      f '' (⋃ i ∈ s, (V i).shade) by simp [Set.image_iUnion₂]]
  exact Kakeya.mem_image_linearIsometryEquiv_iff f _ x

/-- Isometric transport of shaded uniformity on exactly the transported tube
hierarchy.  No new hierarchy or subfamily is selected. -/
def ShadedUniformTubeSet.mapLinearIsometryEquiv {δ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C : NNReal}
    (S : ShadedUniformTubeSet s V N C) (f : E ≃ₗᵢ[ℝ] F) :
    ShadedUniformTubeSet s (fun i => (V i).mapLinearIsometryEquiv f) N C where
  tubeUniform := S.tubeUniform.mapLinearIsometryEquiv f
  branchingN := S.branchingN
  localN x := S.localN (f.symm x)
  card_shadeClass_le := by
    intro x hx k hk i hi hxi
    have hx' : f.symm x ∈ (⋃ i ∈ s, (V i).shade) := by
      exact (mem_iUnion_mapLinearIsometryEquiv_shade_iff s V x f).mp hx
    have hxi' : f.symm x ∈ (V i).shade := by
      exact (Kakeya.mem_image_linearIsometryEquiv_iff f (V i).shade x).mp
        (by simpa only [mapLinearIsometryEquiv_shade] using hxi)
    simpa only [Tube.UniformTubeSet.mapLinearIsometryEquiv_cover,
      Tube.GridCoverSystem.mapLinearIsometryEquiv_assign,
      shadeClass_mapLinearIsometryEquiv] using
      S.card_shadeClass_le (f.symm x) hx' k hk i hi hxi'
  le_card_shadeClass := by
    intro x hx k hk i hi hxi
    have hx' : f.symm x ∈ (⋃ i ∈ s, (V i).shade) := by
      exact (mem_iUnion_mapLinearIsometryEquiv_shade_iff s V x f).mp hx
    have hxi' : f.symm x ∈ (V i).shade := by
      exact (Kakeya.mem_image_linearIsometryEquiv_iff f (V i).shade x).mp
        (by simpa only [mapLinearIsometryEquiv_shade] using hxi)
    simpa only [Tube.UniformTubeSet.mapLinearIsometryEquiv_cover,
      Tube.GridCoverSystem.mapLinearIsometryEquiv_assign,
      shadeClass_mapLinearIsometryEquiv] using
      S.le_card_shadeClass (f.symm x) hx' k hk i hi hxi'
  branchingN_le := by
    intro x hx k hk
    have hx' : f.symm x ∈ (⋃ i ∈ s, (V i).shade) := by
      exact (mem_iUnion_mapLinearIsometryEquiv_shade_iff s V x f).mp hx
    exact S.branchingN_le (f.symm x) hx' k hk
  le_branchingN := by
    intro x hx k hk
    have hx' : f.symm x ∈ (⋃ i ∈ s, (V i).shade) := by
      exact (mem_iUnion_mapLinearIsometryEquiv_shade_iff s V x f).mp hx
    exact S.le_branchingN (f.symm x) hx' k hk

@[simp]
theorem ShadedUniformTubeSet.mapLinearIsometryEquiv_tubeUniform
    {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E} {N : ℕ} {C : NNReal}
    (S : ShadedUniformTubeSet s V N C) (f : E ≃ₗᵢ[ℝ] F) :
    (S.mapLinearIsometryEquiv f).tubeUniform =
      S.tubeUniform.mapLinearIsometryEquiv f := rfl

end ShadedTube

namespace ConvexSpaceBody

open Kakeya

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- The volume of a convex body is unchanged by cross-space isometric transport. -/
@[simp]
theorem volume_mapLinearIsometryEquiv (K : ConvexSpaceBody E) (f : E ≃ₗᵢ[ℝ] F) :
    volume (K.mapLinearIsometryEquiv f).carrier = volume K.carrier := by
  exact volume_image_linearIsometryEquiv f K.carrier

/-- The closed unit ball is carried to the closed unit ball. -/
@[simp]
theorem closedUnitBall_mapLinearIsometryEquiv (f : E ≃ₗᵢ[ℝ] F) :
    (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).mapLinearIsometryEquiv f =
      ConvexSpaceBody.closedUnitBall := by
  apply ConvexSpaceBody.ext
  change f '' Metric.closedBall 0 1 = Metric.closedBall 0 1
  simpa using f.image_closedBall (0 : E) 1

end ConvexSpaceBody

namespace ShadedBody

open Kakeya

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {ι : Type*}

/-- Shading volume is unchanged by cross-space isometric transport. -/
@[simp]
theorem volume_mapLinearIsometryEquiv_shade (V : ShadedBody E) (f : E ≃ₗᵢ[ℝ] F) :
    volume (V.mapLinearIsometryEquiv f).shade = volume V.shade := by
  exact volume_image_linearIsometryEquiv f V.shade

/-- The transported shading union is the image of the original shading union. -/
theorem iUnion_shade_mapLinearIsometryEquiv (s : Finset ι) (V : ι → ShadedBody E)
    (f : E ≃ₗᵢ[ℝ] F) :
    (⋃ i ∈ s, ((V i).mapLinearIsometryEquiv f).shade) =
      f '' (⋃ i ∈ s, (V i).shade) := by
  simp [Set.image_iUnion₂]

/-- The total union volume is unchanged by cross-space isometric transport. -/
@[simp]
theorem volume_iUnion_mapLinearIsometryEquiv_shade (s : Finset ι) (V : ι → ShadedBody E)
    (f : E ≃ₗᵢ[ℝ] F) :
    volume (⋃ i ∈ s, ((V i).mapLinearIsometryEquiv f).shade) =
      volume (⋃ i ∈ s, (V i).shade) := by
  rw [iUnion_shade_mapLinearIsometryEquiv]
  exact volume_image_linearIsometryEquiv f _

/-- Fullness is unchanged by cross-space isometric transport. -/
@[simp]
theorem fullness_mapLinearIsometryEquiv (s : Finset ι) (V : ι → ShadedBody E)
    (f : E ≃ₗᵢ[ℝ] F) :
    fullness s (fun i => (V i).mapLinearIsometryEquiv f) = fullness s V := by
  unfold fullness fullness'
  have hshade : (∑ i ∈ s, volume ((V i).mapLinearIsometryEquiv f).shade) =
      ∑ i ∈ s, volume (V i).shade := by
    exact Finset.sum_congr rfl fun i _ => volume_mapLinearIsometryEquiv_shade (V i) f
  have hcarrier : (∑ i ∈ s, volume ((V i).mapLinearIsometryEquiv f).carrier) =
      ∑ i ∈ s, volume (V i).carrier := by
    exact Finset.sum_congr rfl fun i _ =>
      ConvexSpaceBody.volume_mapLinearIsometryEquiv (V i).toConvexSpaceBody f
  rw [hshade, hcarrier]

/-- Multiplicity is unchanged by cross-space isometric transport. -/
@[simp]
theorem multiplicity_mapLinearIsometryEquiv (s : Finset ι) (V : ι → ShadedBody E)
    (f : E ≃ₗᵢ[ℝ] F) :
    multiplicity s (fun i => (V i).mapLinearIsometryEquiv f) = multiplicity s V := by
  unfold multiplicity
  rw [volume_iUnion_mapLinearIsometryEquiv_shade]
  congr 1
  exact Finset.sum_congr rfl fun i _ => volume_mapLinearIsometryEquiv_shade (V i) f

end ShadedBody

namespace Kakeya

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {ι : Type*}

/-- Density in a container is unchanged when the family and container are transported together. -/
@[simp]
theorem densityIn_mapLinearIsometryEquiv (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) (f : E ≃ₗᵢ[ℝ] F) :
    densityIn s (fun i => (W i).mapLinearIsometryEquiv f)
      (K.mapLinearIsometryEquiv f) = densityIn s W K := by
  classical
  unfold densityIn
  have hfilter : s.filter (fun i => (W i).mapLinearIsometryEquiv f ≤
      K.mapLinearIsometryEquiv f) = s.filter (fun i => W i ≤ K) := by
    apply Finset.filter_congr
    intro i _
    exact ConvexSpaceBody.mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff f
  rw [hfilter]
  congr 1
  · exact Finset.sum_congr rfl fun i _ =>
      ConvexSpaceBody.volume_mapLinearIsometryEquiv (W i) f
  · exact ConvexSpaceBody.volume_mapLinearIsometryEquiv K f

/-- Maximum density is unchanged by cross-space isometric transport. -/
@[simp]
theorem maxDensity_mapLinearIsometryEquiv (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (f : E ≃ₗᵢ[ℝ] F) :
    maxDensity s (fun i => (W i).mapLinearIsometryEquiv f) = maxDensity s W := by
  apply le_antisymm
  · rw [maxDensity_le_iff]
    intro K
    have hK : K = (K.mapLinearIsometryEquiv f.symm).mapLinearIsometryEquiv f := by simp
    rw [hK, densityIn_mapLinearIsometryEquiv]
    exact le_maxDensity s W (K.mapLinearIsometryEquiv f.symm)
  · rw [maxDensity_le_iff]
    intro K
    rw [← densityIn_mapLinearIsometryEquiv s W K f]
    exact le_maxDensity s (fun i => (W i).mapLinearIsometryEquiv f)
      (K.mapLinearIsometryEquiv f)

end Kakeya

namespace ConvexSpaceBody

open Kakeya

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {ι : Type*} {s : Finset ι} {W : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E}
  {C : ENNReal}

/-- A Frostman condition is preserved, with the same constant, by isometric transport. -/
theorem IsFrostmanIn.mapLinearIsometryEquiv (h : IsFrostmanIn s W K C)
    (f : E ≃ₗᵢ[ℝ] F) :
    IsFrostmanIn s (fun i => (W i).mapLinearIsometryEquiv f)
      (K.mapLinearIsometryEquiv f) C := fun K' hK' ↦ by
  convert h (K'.mapLinearIsometryEquiv f.symm) (by
    have := ConvexSpaceBody.mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff
      (K := K') (L := K.mapLinearIsometryEquiv f) f.symm
    simpa using this.mpr hK') using 1
  · nth_rw 1 [← ConvexSpaceBody.symm_mapLinearIsometryEquiv_mapLinearIsometryEquiv
      (K := K') (f := f)]
    exact densityIn_mapLinearIsometryEquiv s W (K'.mapLinearIsometryEquiv f.symm) f
  · exact congrArg (C * ·) (densityIn_mapLinearIsometryEquiv s W K f)

/-- The cross-space isometric Frostman transport is an equivalence. -/
theorem IsFrostmanIn.mapLinearIsometryEquiv_iff (f : E ≃ₗᵢ[ℝ] F) :
    IsFrostmanIn s (fun i => (W i).mapLinearIsometryEquiv f)
      (K.mapLinearIsometryEquiv f) C ↔ IsFrostmanIn s W K C := by
  constructor
  · intro h
    simpa using h.mapLinearIsometryEquiv f.symm
  · exact fun h => h.mapLinearIsometryEquiv f

/-- A Katz--Tao condition is preserved, with the same constant, by isometric transport. -/
theorem IsKatzTao.mapLinearIsometryEquiv (h : IsKatzTao s W C) (f : E ≃ₗᵢ[ℝ] F) :
    IsKatzTao s (fun i => (W i).mapLinearIsometryEquiv f) C := by
  rw [IsKatzTao_def, maxDensity_mapLinearIsometryEquiv]
  exact h

/-- The cross-space isometric Katz--Tao transport is an equivalence. -/
theorem IsKatzTao.mapLinearIsometryEquiv_iff (f : E ≃ₗᵢ[ℝ] F) :
    IsKatzTao s (fun i => (W i).mapLinearIsometryEquiv f) C ↔ IsKatzTao s W C := by
  rw [IsKatzTao_def, IsKatzTao_def, maxDensity_mapLinearIsometryEquiv]

end ConvexSpaceBody

section EssentiallyDistinct

open Kakeya

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Essential distinctness is preserved by cross-space isometric transport. -/
theorem IsEssentiallyDistinct.mapLinearIsometryEquiv {U V : Set E}
    (h : IsEssentiallyDistinct U V) (f : E ≃ₗᵢ[ℝ] F) :
    IsEssentiallyDistinct (f '' U) (f '' V) := by
  unfold IsEssentiallyDistinct at *
  rw [← Set.image_inter f.injective]
  simpa only [Kakeya.volume_image_linearIsometryEquiv] using h

/-- Essential distinctness is invariant under cross-space isometric transport. -/
theorem IsEssentiallyDistinct.mapLinearIsometryEquiv_iff {U V : Set E}
    (f : E ≃ₗᵢ[ℝ] F) :
    IsEssentiallyDistinct (f '' U) (f '' V) ↔ IsEssentiallyDistinct U V := by
  constructor
  · intro h
    convert h.mapLinearIsometryEquiv f.symm using 1 <;>
      rw [Set.image_image] <;> simp
  · exact fun h => h.mapLinearIsometryEquiv f

end EssentiallyDistinct

namespace Kakeya

universe u

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- The partial Katz--Tao estimate is invariant under a linear isometry equivalence of ambient
spaces. -/
theorem KatzTaoEstimate.mapLinearIsometryEquiv {β : ℝ} (h : KatzTaoEstimate.{u} E β)
    (f : E ≃ₗᵢ[ℝ] F) : KatzTaoEstimate.{u} F β := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ
  intro ι s T hball hKT hfull
  let T' : ι → ShadedTube δ E := fun i => (T i).mapLinearIsometryEquiv f.symm
  have hball' : ∀ i ∈ s, (T' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    dsimp only [T']
    rw [ShadedTube.mapLinearIsometryEquiv_carrier]
    calc
      f.symm '' (T i).carrier ⊆ f.symm '' Metric.closedBall 0 1 :=
        Set.image_mono (hball i hi)
      _ = Metric.closedBall 0 1 := by
        simpa using f.symm.image_closedBall (0 : F) 1
  have hKT' : ConvexSpaceBody.IsKatzTao s (fun i => (T' i).toConvexSpaceBody)
      (δ ^ (-η)) := by
    simpa only [T', ShadedTube.mapLinearIsometryEquiv_toConvexSpaceBody] using
      hKT.mapLinearIsometryEquiv f.symm
  have hfull' : ShadedBody.fullness s (fun i => (T' i).toShadedBody) ≥ δ ^ η := by
    simpa only [T', ShadedTube.fullness_mapLinearIsometryEquiv] using hfull
  have hres := hδ s T' hball' hKT' hfull'
  have hsum : (∑ i ∈ s, volume (T' i).shade) = ∑ i ∈ s, volume (T i).shade := by
    exact Finset.sum_congr rfl fun i _ => by
      simpa only [T', ShadedTube.mapLinearIsometryEquiv_shade] using
        volume_image_linearIsometryEquiv f.symm (T i).shade
  have hunion : volume (⋃ i ∈ s, (T' i).shade) = volume (⋃ i ∈ s, (T i).shade) := by
    simpa only [T'] using
      ShadedTube.volume_iUnion_mapLinearIsometryEquiv_shade s T f.symm
  rw [hsum, hunion] at hres
  exact hres

/-- The partial Frostman estimate is invariant under a linear isometry equivalence of ambient
spaces. -/
theorem FrostmanEstimate.mapLinearIsometryEquiv {β : ℝ} (h : FrostmanEstimate.{u} E β)
    (f : E ≃ₗᵢ[ℝ] F) : FrostmanEstimate.{u} F β := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ
  intro ι s T hball hED hFrost hfull
  let T' : ι → ShadedTube δ E := fun i => (T i).mapLinearIsometryEquiv f.symm
  have hball' : ∀ i ∈ s, (T' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    dsimp only [T']
    rw [ShadedTube.mapLinearIsometryEquiv_carrier]
    calc
      f.symm '' (T i).carrier ⊆ f.symm '' Metric.closedBall 0 1 :=
        Set.image_mono (hball i hi)
      _ = Metric.closedBall 0 1 := by
        simpa using f.symm.image_closedBall (0 : F) 1
  have hED' : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T' i).carrier (T' j).carrier) := by
    intro i hi j hj hij
    simpa only [T', ShadedTube.mapLinearIsometryEquiv_carrier] using
      (hED hi hj hij).mapLinearIsometryEquiv f.symm
  have hFrost' : ConvexSpaceBody.IsFrostmanIn s (fun i => (T' i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall (δ ^ (-η)) := by
    simpa only [T', ShadedTube.mapLinearIsometryEquiv_toConvexSpaceBody,
      ConvexSpaceBody.closedUnitBall_mapLinearIsometryEquiv] using
      hFrost.mapLinearIsometryEquiv f.symm
  have hfull' : ShadedBody.fullness s (fun i => (T' i).toShadedBody) ≥ δ ^ η := by
    simpa only [T', ShadedTube.fullness_mapLinearIsometryEquiv] using hfull
  have hres := hδ s T' hball' hED' hFrost' hfull'
  have hmult : ShadedBody.multiplicity s (fun i => (T' i).toShadedBody) =
      ShadedBody.multiplicity s (fun i => (T i).toShadedBody) := by
    simpa only [T'] using ShadedTube.multiplicity_mapLinearIsometryEquiv s T f.symm
  rw [hmult, f.toLinearEquiv.finrank_eq] at hres
  exact hres

end Kakeya

namespace Kakeya

universe v

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A universe-polymorphic partial Katz--Tao estimate may be used on `Type 0` index families.

The plank estimate internally introduces representative index types in `Type 0`.  Reindexing a
`Type 0` family along `Equiv.ulift` puts it in `Type v`; all sums, unions, density, fullness and
cardinality terms are unchanged. -/
theorem KatzTaoEstimate.toTypeZero {β : ℝ} (h : KatzTaoEstimate.{v} E β) :
    KatzTaoEstimate.{0} E β := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ
  intro ι s T hB hKT hFull
  let e : ι ↪ ULift.{v} ι := ⟨fun i => ⟨i⟩, by
    intro i j hij
    exact congrArg ULift.down hij⟩
  let s' : Finset (ULift.{v} ι) := s.map e
  let T' : ULift.{v} ι → ShadedTube δ E := fun i => T i.down
  have hB' : ∀ i ∈ s', (T' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp (by simpa only [s'] using hi)
    change (T j).carrier ⊆ Metric.closedBall 0 1
    exact hB j hj
  have hKT' : ConvexSpaceBody.IsKatzTao s'
      (fun i => (T' i).toConvexSpaceBody) (δ ^ (-η)) := by
    rw [ConvexSpaceBody.isKatzTao_iff] at hKT ⊢
    intro K
    simpa [s', T', e, densityIn, Finset.sum_map, Finset.filter_map] using hKT K
  have hFull' : ShadedBody.fullness s' (fun i => (T' i).toShadedBody) ≥ δ ^ η := by
    simpa [s', T', e, ShadedBody.fullness, ShadedBody.fullness', Finset.sum_map] using hFull
  have hBound := hδ s' T' hB' hKT' hFull'
  have hcard : s'.card = s.card := Finset.card_map _
  have hsum : ∑ i ∈ s', volume (T' i).shade = ∑ i ∈ s, volume (T i).shade :=
    Finset.sum_map _ _ _
  have hUnion : (⋃ i ∈ s', (T' i).shade) = ⋃ i ∈ s, (T i).shade := by
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨i, hi, hxi⟩
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      exact ⟨j, hj, hxi⟩
    · rintro ⟨i, hi, hxi⟩
      exact ⟨e i, Finset.mem_map_of_mem e hi, hxi⟩
  simpa only [hsum, hUnion, hcard] using hBound

end Kakeya
