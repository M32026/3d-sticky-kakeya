/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionTwo.Cordoba
public import Kakeya.Mathlib.Geometry.Projection

/-!
# The planar Cordoba `L²` estimate on an affine subspace

The planar Cordoba estimate `ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim` is stated on a
two-dimensional *vector* space. The single-body reduction of GWZ Lemma 5.9
(`ShadedBody.lambdaInducedSingleWUniform`) must, however, apply it to the shadow of a slab under
orthogonal projection onto a codimension-one affine subspace `H`, whose underlying type `↑H` is an
affine space (a `NormedAddTorsor` over `H.direction`), *not* a vector space.

This file records the affine-subspace form. The area on `↑H` is the two-dimensional Euclidean
Hausdorff measure `μHE[finrank ℝ H.direction]`, supplied by the scoped `MeasureSpace` instance
`Kakeya.AffineSubspaceArea.instMeasureSpaceAffineSubspace`. Restricting this instance to
affine-subspace subtypes (rather than to all `NormedAddTorsor`s) avoids a measure-instance diamond:
on a vector space the Euclidean Hausdorff measure equals `volume` only propositionally, not
definitionally, so a general torsor instance would clash with the canonical `volume` that vector
spaces already carry.

The estimate is derived from `ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim` by transport
along an affine isometry `↑H ≃ᵃⁱ[ℝ] H.direction` (`AffineIsometryEquiv.constVSub` at a basepoint),
whose measure-preservation is `Isometry.euclideanHausdorffMeasure_image`.
-/

@[expose] public section

open MeasureTheory Metric Module
open scoped NNReal ENNReal

namespace Kakeya.AffineSubspaceArea

/-- The area on an affine-subspace subtype is the Euclidean Hausdorff measure of its dimension.
This is a `scoped` instance: it fires only on types of the form `↑A` for `A : AffineSubspace ℝ E`,
so it does not conflict with the canonical `volume` on the ambient vector space `E`. Open it with
`open scoped Kakeya.AffineSubspaceArea`. -/
noncomputable scoped instance instMeasureSpaceAffineSubspace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {A : AffineSubspace ℝ E} [Nonempty ↑A] : MeasureSpace ↑A :=
  ⟨μHE[finrank ℝ A.direction]⟩

end Kakeya.AffineSubspaceArea

open scoped Kakeya.AffineSubspaceArea

namespace ConvexSpaceBody.IsFrostmanIn

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The image of a shaded body under an affine isometry equivalence, pushing forward both the
underlying convex body (via `ConvexSpaceBody.affineImage`) and the shading. -/
private noncomputable def ShadedBody.map {V P : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [PseudoMetricSpace P] [NormedAddTorsor V P] [MeasurableSpace P] [BorelSpace P]
    {W Q : Type*} [SeminormedAddCommGroup W] [NormedSpace ℝ W]
    [PseudoMetricSpace Q] [NormedAddTorsor W Q] [MeasurableSpace Q] [BorelSpace Q]
    (e : P ≃ᵃⁱ[ℝ] Q) (S : ShadedBody P) : ShadedBody Q where
  toConvexSpaceBody := S.toConvexSpaceBody.affineImage e.toAffineMap e.continuous
  shade := e '' S.shade
  measurableSet_shade := by
    have hpre : e '' S.shade = e.symm ⁻¹' S.shade := e.toEquiv.image_eq_preimage_symm S.shade
    rw [hpre]
    exact e.symm.continuous.measurable S.measurableSet_shade
  shade_subset := Set.image_mono S.shade_subset

@[simp]
private lemma ShadedBody.map_shade {V P : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [PseudoMetricSpace P] [NormedAddTorsor V P] [MeasurableSpace P] [BorelSpace P]
    {W Q : Type*} [SeminormedAddCommGroup W] [NormedSpace ℝ W]
    [PseudoMetricSpace Q] [NormedAddTorsor W Q] [MeasurableSpace Q] [BorelSpace Q]
    (e : P ≃ᵃⁱ[ℝ] Q) (S : ShadedBody P) : (ShadedBody.map e S).shade = e '' S.shade := rfl

/-- Affine-plane form of `ConvexSpaceBody.volume_le_of_thickness_le`.  Pairwise factor-two
comparability of affine thicknesses gives carrier-volume comparability with the same explicit
two-dimensional constant. -/
theorem volume_le_of_thickness_le_affineSubspace
    {A : AffineSubspace ℝ E} [Nonempty ↑A] [Fact (finrank ℝ A.direction = 2)]
    {W W' : ConvexSpaceBody ↑A}
    (h : thickness ℝ W.carrier ≤ 2 • thickness ℝ W'.carrier) :
    volume W.carrier ≤ (Metric.volume_comparison.C 2 : ENNReal) * volume W'.carrier := by
  let p : ↑A := Nonempty.some ‹Nonempty ↑A›
  let e : ↑A ≃ᵃⁱ[ℝ] ↥A.direction := AffineIsometryEquiv.constVSub ℝ p
  let Q : ConvexSpaceBody ↥A.direction := W.affineImage e.toAffineMap e.continuous
  let Q' : ConvexSpaceBody ↥A.direction := W'.affineImage e.toAffineMap e.continuous
  have hvol_image {S : Set ↑A} :
      (volume : Measure ↥A.direction) (e '' S) = (volume : Measure ↑A) S := by
    rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ↥A.direction)]
    rw [Isometry.euclideanHausdorffMeasure_image e.isometry]
    rfl
  have heth (X : Set ↑A) (n : ℕ) :
      Metric.ethickness ℝ (e '' X) n = Metric.ethickness ℝ X n := by
    apply le_antisymm
    · have he := (e.isometry.lipschitz.ethickness_image_le (f := e.toAffineMap) X) n
      simpa [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul] using he
    · have he := (e.symm.isometry.lipschitz.ethickness_image_le (f := e.symm.toAffineMap)
        (e '' X)) n
      have hss : e.symm.toAffineMap '' (e '' X) = X := by
        simp [Set.image_image, AffineIsometryEquiv.symm_apply_apply]
      rw [hss] at he
      simpa [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul] using he
  have hthick (R : ConvexSpaceBody ↑A) :
      thickness ℝ (R.affineImage e.toAffineMap e.continuous).carrier =
        thickness ℝ R.carrier := by
    funext n
    rw [← Metric.toReal_ethickness (𝕜 := ℝ)
        (s := (R.affineImage e.toAffineMap e.continuous).carrier)
        ((R.affineImage e.toAffineMap e.continuous).isCompact.isBounded) n,
      ← Metric.toReal_ethickness (𝕜 := ℝ) (s := R.carrier) (R.isCompact.isBounded) n]
    congr 1
    change Metric.ethickness ℝ (e '' R.carrier) n = Metric.ethickness ℝ R.carrier n
    exact heth R.carrier n
  have hQ : thickness ℝ Q.carrier ≤ 2 • thickness ℝ Q'.carrier := by
    simpa only [Q, Q', hthick] using h
  have hv := ConvexSpaceBody.volume_le_of_thickness_le hQ
  change volume (e '' W.carrier) ≤
    (Metric.volume_comparison.C (finrank ℝ A.direction) : ENNReal) *
      volume (e '' W'.carrier) at hv
  rw [show finrank ℝ A.direction = 2 from Fact.out] at hv
  simpa only [hvol_image] using hv

/-- **Aggregate planar Cordoba `L²` estimate on an affine subspace**.

The affine-subspace form of `le_volume_biUnion_TwoDim`: the convex bodies and shadings live in a
two-dimensional affine subspace `A` of a Euclidean space `E`, with area the two-dimensional
Euclidean Hausdorff measure supplied by the scoped instance `Kakeya.AffineSubspaceArea`. The
hypotheses and conclusion match `le_volume_biUnion_TwoDim` verbatim, with the same explicit constant
`le_volume_biUnion_TwoDim.c`.

Obtained from `le_volume_biUnion_TwoDim` by transport along the affine isometry
`↑A ≃ᵃⁱ[ℝ] A.direction` (`AffineIsometryEquiv.constVSub` at a basepoint): the transported family
satisfies the hypotheses in the two-dimensional inner product space `A.direction`, and the
conclusion transports back through measure-preservation of the isometry. -/
theorem le_volume_biUnion_TwoDim_affineSubspace_aggregate
    {A : AffineSubspace ℝ E} [Nonempty ↑A] [Fact (finrank ℝ A.direction = 2)]
    {ι : Type*} {s : Finset ι}
    (V : ι → ShadedBody ↑A)
    (K : ConvexSpaceBody ↑A)
    {C μ : ℝ≥0∞} {N : ℕ}
    (hs : s.Nonempty)
    (hN : ∀ i ∈ s, volume K.carrier ≤ 2 ^ N * volume (V i).carrier)
    (hunif : ∀ i ∈ s, ∀ j ∈ s, thickness ℝ (V i).carrier ≤ 2 • thickness ℝ (V j).carrier)
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ K.carrier)
    (hvol : ∀ i ∈ s, 0 < volume (V i).carrier)
    (hfull : μ * (∑ i ∈ s, volume (V i).carrier) ≤
      ∑ i ∈ s, volume (V i).shade)
    (hFro : IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) K C) :
    (le_volume_biUnion_TwoDim.c : ℝ≥0∞) * μ ^ 2 * volume K.carrier
      ≤ ((N : ℝ≥0∞) + 1) * C * volume (⋃ i ∈ s, (V i).shade) := by
  classical
  -- The affine isometry equivalence `↑A ≃ᵃⁱ[ℝ] A.direction` at a basepoint `p`.
  let p : ↑A := Nonempty.some ‹Nonempty ↑A›
  let e : ↑A ≃ᵃⁱ[ℝ] ↥A.direction := AffineIsometryEquiv.constVSub ℝ p
  -- Transported objects.
  let K' : ConvexSpaceBody ↥A.direction := K.affineImage e.toAffineMap e.continuous
  let V' : ι → ShadedBody ↥A.direction := fun i => ShadedBody.map e (V i)
  -- `e` and `e.symm` are inverse isometries, so images of images are the original sets.
  have himage_symm (S : Set ↥A.direction) : e '' (e.symm '' S) = S := by
    simp [Set.image_image, AffineIsometryEquiv.apply_symm_apply]
  have hsymm_image (S : Set ↑A) : e.symm '' (e '' S) = S := by
    simp [Set.image_image, AffineIsometryEquiv.symm_apply_apply]
  -- `e` preserves the two-dimensional Euclidean Hausdorff measures (which are `volume` on
  -- `A.direction` and on `↑A` respectively), for *arbitrary* sets.
  have hvol_image {S : Set ↑A} :
      (volume : Measure ↥A.direction) (e '' S) = (volume : Measure ↑A) S := by
    rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ↥A.direction)]
    rw [Isometry.euclideanHausdorffMeasure_image e.isometry]
    rfl
  have hvol_pull {S : Set ↥A.direction} :
      (volume : Measure ↑A) (e.symm '' S) = (volume : Measure ↥A.direction) S := by
    rw [← hvol_image (S := e.symm '' S)]
    rw [himage_symm S]
  -- Volume invariance for carriers, shades, and the shaded union.
  have hvol_carrier (i : ι) : volume (V' i).carrier = volume (V i).carrier := by
    change volume (e '' (V i).carrier) = volume (V i).carrier
    exact hvol_image
  have hvol_shade (i : ι) : volume (V' i).shade = volume (V i).shade := by
    change volume (e '' (V i).shade) = volume (V i).shade
    exact hvol_image
  have hvol_K : volume K'.carrier = volume K.carrier := by
    change volume (e '' K.carrier) = volume K.carrier
    exact hvol_image
  have hvol_union : volume (⋃ i ∈ s, (V' i).shade) = volume (⋃ i ∈ s, (V i).shade) := by
    have hunion : (⋃ i ∈ s, (V' i).shade) = e '' (⋃ i ∈ s, (V i).shade) := by
      symm
      rw [Set.image_iUnion₂]
      simp [V']
    rw [hunion]
    exact hvol_image
  -- Affine thickness is invariant under the isometry.
  have heth (X : Set ↑A) (n : ℕ) : Metric.ethickness ℝ (e '' X) n = Metric.ethickness ℝ X n := by
    apply le_antisymm
    · have h := (e.isometry.lipschitz.ethickness_image_le (f := e.toAffineMap) X) n
      simpa [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul] using h
    · have h := (e.symm.isometry.lipschitz.ethickness_image_le (f := e.symm.toAffineMap)
        (e '' X)) n
      have hss : e.symm.toAffineMap '' (e '' X) = X := by
        simp [Set.image_image, AffineIsometryEquiv.symm_apply_apply]
      rw [hss] at h
      simpa [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul] using h
  have hthick (i : ι) : thickness ℝ (V' i).carrier = thickness ℝ (V i).carrier := by
    funext n
    rw [← Metric.toReal_ethickness (𝕜 := ℝ) (s := (V' i).carrier)
        ((V' i).isCompact.isBounded) n,
      ← Metric.toReal_ethickness (𝕜 := ℝ) (s := (V i).carrier)
        ((V i).isCompact.isBounded) n]
    congr 1
    change Metric.ethickness ℝ (e '' (V i).carrier) n = Metric.ethickness ℝ (V i).carrier n
    exact heth (V i).carrier n
  -- The transported family satisfies the hypotheses of `le_volume_biUnion_TwoDim`.
  have hN' : ∀ i ∈ s, volume K'.carrier ≤ 2 ^ N * volume (V' i).carrier := by
    intro i hi
    rw [hvol_K, hvol_carrier i]
    exact hN i hi
  have hunif' : ∀ i ∈ s, ∀ j ∈ s,
      thickness ℝ (V' i).carrier ≤ 2 • thickness ℝ (V' j).carrier := by
    intro i hi j hj
    rw [hthick i, hthick j]
    exact hunif i hi j hj
  have hsub' : ∀ i ∈ s, (V' i).carrier ⊆ K'.carrier := by
    intro i hi
    change e '' (V i).carrier ⊆ e '' K.carrier
    exact Set.image_mono (hsub i hi)
  have hvol' : ∀ i ∈ s, 0 < volume (V' i).carrier := by
    intro i hi
    rw [hvol_carrier i]
    exact hvol i hi
  have hfull' : μ * (∑ i ∈ s, volume (V' i).carrier) ≤
      ∑ i ∈ s, volume (V' i).shade := by
    simpa only [Finset.sum_apply, hvol_carrier, hvol_shade] using hfull
  -- `densityIn` is invariant under the transport.
  have h_density :
      Kakeya.densityIn s (fun i => (V i).toConvexSpaceBody) K =
        Kakeya.densityIn s (fun i => (V' i).toConvexSpaceBody) K' := by
    unfold Kakeya.densityIn
    congr 1
    · have hfilter : {i ∈ s | (V i).toConvexSpaceBody ≤ K} =
          {i ∈ s | (V' i).toConvexSpaceBody ≤ K'} := by
        refine Finset.filter_congr (fun i hi => ?_)
        change (V i).carrier ⊆ K.carrier ↔ (V' i).carrier ⊆ e '' K.carrier
        rw [← Set.image_subset_image_iff e.injective]
        rfl
      rw [hfilter]
      refine Finset.sum_congr rfl (fun i _ => (hvol_carrier i).symm)
    · exact hvol_K.symm
  have h_density_pull (K₀ : ConvexSpaceBody ↥A.direction) :
      Kakeya.densityIn s (fun i => (V i).toConvexSpaceBody)
          (K₀.affineImage e.symm.toAffineMap e.symm.continuous) =
        Kakeya.densityIn s (fun i => (V' i).toConvexSpaceBody) K₀ := by
    unfold Kakeya.densityIn
    congr 1
    · have hfilter : {i ∈ s | (V i).toConvexSpaceBody ≤
            K₀.affineImage e.symm.toAffineMap e.symm.continuous} =
          {i ∈ s | (V' i).toConvexSpaceBody ≤ K₀} := by
        refine Finset.filter_congr (fun i hi => ?_)
        change (V i).carrier ⊆ e.symm '' K₀.carrier ↔ (V' i).carrier ⊆ K₀.carrier
        rw [← Set.image_subset_image_iff e.injective]
        rw [himage_symm K₀.carrier]
        rfl
      rw [hfilter]
      refine Finset.sum_congr rfl (fun i _ => (hvol_carrier i).symm)
    · change (volume : Measure ↑A) (e.symm '' K₀.carrier) =
          (volume : Measure ↥A.direction) K₀.carrier
      exact hvol_pull
  -- The Frostman property transports.
  have hFro' : IsFrostmanIn s (fun i => (V' i).toConvexSpaceBody) K' C := by
    intro K₀ hK₀
    let K₀' : ConvexSpaceBody ↑A := K₀.affineImage e.symm.toAffineMap e.symm.continuous
    have hK₀' : K₀' ≤ K := by
      change e.symm '' K₀.carrier ⊆ K.carrier
      rw [← Set.image_subset_image_iff e.injective]
      rw [himage_symm K₀.carrier]
      change K₀.carrier ⊆ K'.carrier
      exact hK₀
    have hstep := hFro K₀' hK₀'
    rw [h_density_pull K₀, h_density] at hstep
    exact hstep
  -- Apply the planar theorem in `A.direction` and transport the conclusion back.
  have hplanar := le_volume_biUnion_TwoDim_aggregate (E := ↥A.direction) V' K' hs hN' hunif'
    hsub' hvol' hfull' hFro'
  rw [← hvol_K, ← hvol_union]
  exact hplanar

/-- **Planar Cordoba `L²` estimate on an affine subspace**
(blueprint `lem:cordoba2Daffine`).  The bodywise interface follows by summing and applying the
aggregate affine theorem. -/
theorem le_volume_biUnion_TwoDim_affineSubspace
    {A : AffineSubspace ℝ E} [Nonempty ↑A] [Fact (finrank ℝ A.direction = 2)]
    {ι : Type*} {s : Finset ι}
    (V : ι → ShadedBody ↑A)
    (K : ConvexSpaceBody ↑A)
    {C μ : ℝ≥0∞} {N : ℕ}
    (hs : s.Nonempty)
    (hN : ∀ i ∈ s, volume K.carrier ≤ 2 ^ N * volume (V i).carrier)
    (hunif : ∀ i ∈ s, ∀ j ∈ s, thickness ℝ (V i).carrier ≤ 2 • thickness ℝ (V j).carrier)
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ K.carrier)
    (hvol : ∀ i ∈ s, 0 < volume (V i).carrier)
    (hfull : ∀ i ∈ s, μ * volume (V i).carrier ≤ volume (V i).shade)
    (hFro : IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) K C) :
    (le_volume_biUnion_TwoDim.c : ℝ≥0∞) * μ ^ 2 * volume K.carrier
      ≤ ((N : ℝ≥0∞) + 1) * C * volume (⋃ i ∈ s, (V i).shade) := by
  apply le_volume_biUnion_TwoDim_affineSubspace_aggregate V K hs hN hunif hsub hvol
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum hfull
  · exact hFro

end ConvexSpaceBody.IsFrostmanIn
