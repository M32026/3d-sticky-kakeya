/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Frostman
public import Kakeya.Mathlib.Geometry.Projection

/-!
# Projection from a thin slab

This file records the projection interfaces needed to reduce the single-body form of GWZ
Lemma 5.9 to the planar Cordoba estimate. If a family lies in the closed r-neighborhood of
a codimension-one affine subspace H, orthogonal projection onto H compares ambient volume
with the volume of the shadow. Under an explicit reverse volume comparison for the bodies in
the family, density and the Frostman property pass to the projected family.

The proofs are intentionally deferred. This file fixes the statements and the constants needed
by the later assembly of GWZ Lemma 5.9.
-/

@[expose] public section

open EuclideanGeometry Kakeya MeasureTheory Metric Module
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The volume on an affine subspace is the Euclidean Hausdorff measure in its dimension. -/
noncomputable local instance instMeasureSpaceAffineSubspace
    {H : AffineSubspace ℝ E} [Nonempty ↑H] : MeasureSpace ↑H :=
  ⟨μHE[finrank ℝ H.direction]⟩

omit [FiniteDimensional ℝ E] in
@[simp]
theorem volume_affineSubspace {H : AffineSubspace ℝ E} [Nonempty ↑H] :
    (volume : Measure ↑H) = μHE[finrank ℝ H.direction] := rfl

section SlabGeometry

/-- The shadow of a convex body under orthogonal projection onto an affine subspace. -/
noncomputable def ConvexSpaceBody.orthogonalProjectionImage (K : ConvexSpaceBody E)
    (H : AffineSubspace ℝ E) [Nonempty ↑H] : ConvexSpaceBody ↑H :=
  K.affineImage (orthogonalProjection H).toAffineMap (orthogonalProjection H).cont

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem ConvexSpaceBody.coe_orthogonalProjectionImage (K : ConvexSpaceBody E)
    (H : AffineSubspace ℝ E) [Nonempty ↑H] :
    ((K.orthogonalProjectionImage H : ConvexSpaceBody ↑H) : Set ↑H) =
      orthogonalProjection H '' K.carrier := rfl

/-- The part of the r-neighborhood of H lying over K has volume 2r times the volume of K. -/
theorem volume_preimage_orthogonalProjection_inter_cthickening
    (H : AffineSubspace ℝ E) [Nonempty ↑H]
    (hcodim : finrank ℝ E = finrank ℝ H.direction + 1)
    (K : ConvexSpaceBody ↑H) (r : NNReal) :
    volume ((orthogonalProjection H ⁻¹' K.carrier) ∩ cthickening r (H : Set E)) =
      2 * (r : ENNReal) * volume K.carrier := by
  have hKmeas : MeasurableSet K.carrier := K.isCompact.measurableSet
  rw [Set.inter_comm, volume_affineSubspace]
  apply le_antisymm
  · exact volume_cthickening_inter_preimage_orthogonalProjection_le hcodim r hKmeas
  · exact two_mul_le_volume_cthickening_inter_preimage_orthogonalProjection hcodim r hKmeas

omit [MeasurableSpace E] [BorelSpace E] in
/-- For a set in the r-neighborhood of H, containment over K is equivalent to containment of
its shadow in K. -/
theorem subset_preimage_orthogonalProjection_inter_cthickening_iff
    (H : AffineSubspace ℝ E) [Nonempty ↑H]
    {A : Set E} (K : ConvexSpaceBody ↑H) (r : NNReal)
    (hAslab : A ⊆ cthickening r (H : Set E)) :
    A ⊆ (orthogonalProjection H ⁻¹' K.carrier) ∩ cthickening r (H : Set E) ↔
      orthogonalProjection H '' A ⊆ K.carrier := by
  rw [Set.subset_inter_iff, and_iff_left hAslab, Set.image_subset_iff]

/-- A set in a slab has volume at most the slab width times the volume of its shadow. -/
theorem volume_le_two_mul_volume_orthogonalProjection_image
    (H : AffineSubspace ℝ E) [Nonempty ↑H]
    (hcodim : finrank ℝ E = finrank ℝ H.direction + 1)
    {r : NNReal} {s : Set E} (hs : s ⊆ cthickening r (H : Set E)) :
    volume s ≤ 2 * (r : ENNReal) * volume (orthogonalProjection H '' s) :=
  volume_image_orthogonalProjection hcodim hs

omit [MeasurableSpace E] [BorelSpace E] in
/-- The full preimage of the shadow inside the slab lies in the 2r-thickening. -/
theorem preimage_image_orthogonalProjection_inter_cthickening_subset_cthickening
    (H : AffineSubspace ℝ E) [Nonempty ↑H]
    {r : ℝ} (hr : 0 ≤ r) {s : Set E} (hs : s ⊆ cthickening r (H : Set E)) :
    (orthogonalProjection H ⁻¹' (orthogonalProjection H '' s)) ∩ cthickening r (H : Set E)
      ⊆ cthickening (2 * r) s := by
  intro x hx
  obtain ⟨hxpre, hxN⟩ := hx
  have hproj : orthogonalProjection H x ∈ orthogonalProjection H '' s := hxpre
  obtain ⟨a, has, hax⟩ := hproj
  -- a ∈ s and orthogonalProjection H a = orthogonalProjection H x
  have hx_cthick : x ∈ cthickening r (H : Set E) := hxN
  have ha_cthick : a ∈ cthickening r (H : Set E) := hs has
  -- Show x ∈ cthickening (2*r) s
  rw [Metric.mem_cthickening_iff]
  -- Goal: Metric.infEDist x s ≤ ENNReal.ofReal (2*r)
  have hdist : dist x a ≤ 2*r := by
    let p := (orthogonalProjection H x : E)
    have hax' : (orthogonalProjection H a : E) = p := by
      simpa [p] using congrArg Subtype.val hax
    have hx_infDist : dist x p = Metric.infDist x H := by
      simpa using EuclideanGeometry.dist_orthogonalProjection_eq_infDist H x
    have ha_infDist : dist a p = Metric.infDist a H := by
      calc
        dist a p = dist a (orthogonalProjection H a : E) := by rw [hax']
        _ = Metric.infDist a H := EuclideanGeometry.dist_orthogonalProjection_eq_infDist H a
    have hx_infDist_le_r : Metric.infDist x H ≤ r := by
      have hx_infEDist : Metric.infEDist x (H : Set E) ≤ ENNReal.ofReal r :=
        Metric.mem_cthickening_iff.mp hx_cthick
      rw [Metric.infDist, ← ENNReal.toReal_ofReal hr]
      exact ENNReal.toReal_mono (by exact ENNReal.ofReal_ne_top) hx_infEDist
    have ha_infDist_le_r : Metric.infDist a H ≤ r := by
      have ha_infEDist : Metric.infEDist a (H : Set E) ≤ ENNReal.ofReal r :=
        Metric.mem_cthickening_iff.mp ha_cthick
      rw [Metric.infDist, ← ENNReal.toReal_ofReal hr]
      exact ENNReal.toReal_mono (by exact ENNReal.ofReal_ne_top) ha_infEDist
    calc
      dist x a ≤ dist x p + dist p a := dist_triangle x p a
      _ = dist x p + dist a p := by rw [dist_comm p a]
      _ = Metric.infDist x H + Metric.infDist a H := by rw [hx_infDist, ha_infDist]
      _ ≤ r + r := add_le_add hx_infDist_le_r ha_infDist_le_r
      _ = 2*r := by ring
  calc
    Metric.infEDist x s ≤ edist x a := Metric.infEDist_le_edist_of_mem has
    _ = ENNReal.ofReal (dist x a) := edist_dist x a
    _ ≤ ENNReal.ofReal (2*r) := ENNReal.ofReal_le_ofReal hdist

/-- The 2r-thickening has at least the volume of the full preimage of the shadow inside
the slab. -/
theorem volume_orthogonalProjection_image_le_volume_cthickening
    (H : AffineSubspace ℝ E) [Nonempty ↑H]
    (hcodim : finrank ℝ E = finrank ℝ H.direction + 1)
    {r : NNReal} {s : Set E} (_hs : s ⊆ cthickening r (H : Set E))
    (hπs : MeasurableSet (orthogonalProjection H '' s)) :
    2 * (r : ENNReal) * volume (orthogonalProjection H '' s) ≤
      volume (cthickening (2 * r) s) := by
  set π := orthogonalProjection H with hπ_def
  have hcth : MeasurableSet (cthickening (2*(r:ℝ)) s) :=
    isClosed_cthickening.measurableSet
  have hpt : ∀ y : ↑H, (π '' s).indicator (fun _ => 2*(r:ENNReal)) y ≤
      μHE[finrank ℝ (H.directionᗮ : Submodule ℝ E)]
        (orthogonalFiber H (cthickening (2*(r:ℝ)) s) y) := by
    intro y
    by_cases hy : y ∈ π '' s
    · rw [Set.indicator_of_mem hy]
      obtain ⟨a, ha, rfl⟩ := hy
      have hsub : closedBall (a : E) (2*(r:ℝ)) ⊆ cthickening (2*(r:ℝ)) s :=
        Metric.closedBall_subset_cthickening ha (2*(r:ℝ))
      have hpos : 0 ≤ 2*(r:ℝ) := mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (NNReal.coe_nonneg r)
      have hball : 2*(r:ENNReal) ≤ 2*ENNReal.ofReal (2*(r:ℝ)) := by
        calc
          2*(r:ENNReal) = 2*ENNReal.ofReal (r:ℝ) := by
            simp [ENNReal.ofReal_coe_nnreal]
          _ ≤ 2*ENNReal.ofReal (2*(r:ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ENNReal) ≤ 2)
            exact ENNReal.ofReal_le_ofReal (by
              have h0 : 0 ≤ (r:ℝ) := NNReal.coe_nonneg r
              nlinarith)
      have hfiber : 2*ENNReal.ofReal (2*(r:ℝ)) ≤
          μHE[finrank ℝ (H.directionᗮ : Submodule ℝ E)]
            (orthogonalFiber H (closedBall (a : E) (2*(r:ℝ))) (π a)) :=
        two_mul_ofReal_le_μHE_orthogonalFiber_closedBall hcodim (a : E) hpos
      have hmono : μHE[finrank ℝ (H.directionᗮ : Submodule ℝ E)]
          (orthogonalFiber H (closedBall (a : E) (2*(r:ℝ))) (π a)) ≤
          μHE[finrank ℝ (H.directionᗮ : Submodule ℝ E)]
            (orthogonalFiber H (cthickening (2*(r:ℝ)) s) (π a)) :=
        measure_mono (orthogonalFiber_mono H hsub (π a))
      calc
        2*(r:ENNReal) ≤ 2*ENNReal.ofReal (2*(r:ℝ)) := hball
        _ ≤ μHE[finrank ℝ (H.directionᗮ : Submodule ℝ E)]
              (orthogonalFiber H (closedBall (a : E) (2*(r:ℝ))) (π a)) := hfiber
        _ ≤ μHE[finrank ℝ (H.directionᗮ : Submodule ℝ E)]
              (orthogonalFiber H (cthickening (2*(r:ℝ)) s) (π a)) := hmono
    · rw [Set.indicator_of_notMem hy]
      simp
  calc
    2*(r:ENNReal) * volume (π '' s) = 2*(r:ENNReal) * μHE[finrank ℝ H.direction] (π '' s) := by
      rw [volume_affineSubspace]
    _ = ∫⁻ y, (π '' s).indicator (fun _ => 2*(r:ENNReal)) y ∂μHE[finrank ℝ H.direction] := by
      rw [lintegral_indicator_const hπs]
    _ ≤ ∫⁻ y, μHE[finrank ℝ (H.directionᗮ : Submodule ℝ E)]
          (orthogonalFiber H (cthickening (2*(r:ℝ)) s) y) ∂μHE[finrank ℝ H.direction] :=
      lintegral_mono hpt
    _ = volume (cthickening (2*(r:ℝ)) s) := by
      rw [AffineSubspace.volume_eq_lintegral H hcth]
    _ = volume (cthickening (2 * r) s) := by simp

/-- The shadow volume lower bound with an arbitrary radius `ρ ≥ 0`: the full `ρ`-normal fiber over
the projected set lies in the `ρ`-thickening of `s`, so `2ρ·|π(s)| ≤ |N_ρ(s)|`. This generalizes
`volume_orthogonalProjection_image_le_volume_cthickening` (the case `ρ = 2r`) to the radius used by
the RHS full-fiber lift in the single-body reduction. -/
theorem two_mul_ofReal_mul_volume_orthogonalProjection_image_le_volume_cthickening
    (H : AffineSubspace ℝ E) [Nonempty ↑H]
    (hcodim : finrank ℝ E = finrank ℝ H.direction + 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ) {s : Set E}
    (hπs : MeasurableSet (orthogonalProjection H '' s)) :
    2 * ENNReal.ofReal ρ * volume (orthogonalProjection H '' s) ≤
      volume (cthickening ρ s) := by
  set π := orthogonalProjection H with hπ_def
  have hcth : MeasurableSet (cthickening ρ s) :=
    isClosed_cthickening.measurableSet
  have hpt : ∀ y : ↑H, (π '' s).indicator (fun _ => 2 * ENNReal.ofReal ρ) y ≤
      μHE[finrank ℝ (H.directionᗮ : Submodule ℝ E)]
        (orthogonalFiber H (cthickening ρ s) y) := by
    intro y
    by_cases hy : y ∈ π '' s
    · rw [Set.indicator_of_mem hy]
      obtain ⟨a, ha, rfl⟩ := hy
      have hsub : closedBall (a : E) ρ ⊆ cthickening ρ s :=
        Metric.closedBall_subset_cthickening ha ρ
      have hfiber : 2 * ENNReal.ofReal ρ ≤
          μHE[finrank ℝ (H.directionᗮ : Submodule ℝ E)]
            (orthogonalFiber H (closedBall (a : E) ρ) (π a)) :=
        two_mul_ofReal_le_μHE_orthogonalFiber_closedBall hcodim (a : E) hρ
      have hmono : μHE[finrank ℝ (H.directionᗮ : Submodule ℝ E)]
          (orthogonalFiber H (closedBall (a : E) ρ) (π a)) ≤
          μHE[finrank ℝ (H.directionᗮ : Submodule ℝ E)]
            (orthogonalFiber H (cthickening ρ s) (π a)) :=
        measure_mono (orthogonalFiber_mono H hsub (π a))
      exact hfiber.trans hmono
    · rw [Set.indicator_of_notMem hy]
      simp
  calc
    2 * ENNReal.ofReal ρ * volume (π '' s)
        = 2 * ENNReal.ofReal ρ * μHE[finrank ℝ H.direction] (π '' s) := by
      rw [volume_affineSubspace]
    _ = ∫⁻ y, (π '' s).indicator (fun _ => 2 * ENNReal.ofReal ρ) y
          ∂μHE[finrank ℝ H.direction] := by
      rw [lintegral_indicator_const hπs]
    _ ≤ ∫⁻ y, μHE[finrank ℝ (H.directionᗮ : Submodule ℝ E)]
          (orthogonalFiber H (cthickening ρ s) y) ∂μHE[finrank ℝ H.direction] :=
      lintegral_mono hpt
    _ = volume (cthickening ρ s) := by
      rw [AffineSubspace.volume_eq_lintegral H hcth]

end SlabGeometry

section ProjectionDensity

variable {ι : Type*}

/-- A body that is the full part of the slab over its shadow has volume `2r` times the volume of
its shadow. -/
theorem volume_eq_two_mul_volume_orthogonalProjectionImage
    (H : AffineSubspace ℝ E) [Nonempty ↑H]
    (hcodim : finrank ℝ E = finrank ℝ H.direction + 1)
    (K : ConvexSpaceBody E) (r : NNReal)
    (hKproduct : K.carrier =
      (orthogonalProjection H ⁻¹' (orthogonalProjection H '' K.carrier)) ∩
        cthickening r (H : Set E)) :
    volume K.carrier =
      2 * (r : ENNReal) * volume (K.orthogonalProjectionImage H).carrier := by
  have hT1 := volume_preimage_orthogonalProjection_inter_cthickening H hcodim
    (K.orthogonalProjectionImage H) r
  have hcarrier_eq : (K.orthogonalProjectionImage H).carrier =
      (orthogonalProjection H '' K.carrier) :=
    ConvexSpaceBody.coe_orthogonalProjectionImage K H
  rw [hcarrier_eq] at hT1
  rw [← hKproduct] at hT1
  rw [hcarrier_eq]
  exact hT1

omit [MeasurableSpace E] [BorelSpace E] in
/-- For a body contained in the slab and a body `K` equal to the full part of the slab over its
shadow, containment in `K` is equivalent to containment of the shadows. -/
theorem orthogonalProjectionImage_le_iff
    (H : AffineSubspace ℝ E) [Nonempty ↑H]
    (V K : ConvexSpaceBody E) (r : NNReal)
    (hV : V.carrier ⊆ cthickening r (H : Set E))
    (hKproduct : K.carrier =
      (orthogonalProjection H ⁻¹' (orthogonalProjection H '' K.carrier)) ∩
        cthickening r (H : Set E)) :
    V ≤ K ↔ V.orthogonalProjectionImage H ≤ K.orthogonalProjectionImage H := by
  rw [← SetLike.coe_subset_coe, ← SetLike.coe_subset_coe]
  simp only [ConvexSpaceBody.coe_orthogonalProjectionImage]
  have hπK_carrier :
      (K.orthogonalProjectionImage H).carrier = orthogonalProjection H '' K.carrier :=
    calc
      (K.orthogonalProjectionImage H).carrier
          = ((K.orthogonalProjectionImage H : ConvexSpaceBody ↑H) : Set ↑H) := rfl
      _ = orthogonalProjection H '' K.carrier :=
        ConvexSpaceBody.coe_orthogonalProjectionImage K H
  have key := subset_preimage_orthogonalProjection_inter_cthickening_iff H
    (K.orthogonalProjectionImage H) r hV
  rw [hπK_carrier] at key
  rw [← hKproduct] at key
  exact key

/-- Density in a body that is the full part of the slab over its shadow is at most density of
the projected family in that shadow. -/
theorem le_densityIn_orthogonalProjection_image
    (s : Finset ι)
    (H : AffineSubspace ℝ E) [Nonempty ↑H]
    (hcodim : finrank ℝ E = finrank ℝ H.direction + 1)
    (A : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E)
    {r : NNReal} (hr : 0 < r)
    (hAslab : ∀ i ∈ s, (A i).carrier ⊆ cthickening r (H : Set E))
    (hKproduct : K.carrier =
      (orthogonalProjection H ⁻¹' (orthogonalProjection H '' K.carrier)) ∩
        cthickening r (H : Set E)) :
    densityIn s A K ≤
      densityIn s (fun i ↦ (A i).orthogonalProjectionImage H)
        (K.orthogonalProjectionImage H) := by
  set PA : ι → ConvexSpaceBody ↑H := fun i ↦ (A i).orthogonalProjectionImage H with hPA
  set PK : ConvexSpaceBody ↑H := K.orthogonalProjectionImage H with hPK
  have hKvol : volume K.carrier = 2*(r:ENNReal)*volume PK.carrier :=
    volume_eq_two_mul_volume_orthogonalProjectionImage H hcodim K r hKproduct
  have hfilter : {i ∈ s | A i ≤ K} = {i ∈ s | PA i ≤ PK} :=
    Finset.filter_congr fun i hi =>
      orthogonalProjectionImage_le_iff H (A i) K r (hAslab i hi) hKproduct
  rw [Kakeya.densityIn_le_iff]
  calc
    ∑ i ∈ s with A i ≤ K, volume (A i).carrier
        ≤ ∑ i ∈ {i ∈ s | A i ≤ K}, 2*(r:ENNReal)*volume (PA i).carrier := by
      apply Finset.sum_le_sum
      intro i hi
      have hmem : i ∈ s := (Finset.mem_filter.mp hi).1
      have hcarrier_eq : (PA i).carrier = orthogonalProjection H '' (A i).carrier :=
        ConvexSpaceBody.coe_orthogonalProjectionImage (A i) H
      simpa [hcarrier_eq] using
        volume_le_two_mul_volume_orthogonalProjection_image H hcodim (hAslab i hmem)
    _ = ∑ i ∈ {i ∈ s | PA i ≤ PK}, 2*(r:ENNReal)*volume (PA i).carrier := by rw [hfilter]
    _ = 2*(r:ENNReal) * (∑ i ∈ s with PA i ≤ PK, volume (PA i).carrier) := by
      rw [Finset.mul_sum]
    _ = 2*(r:ENNReal) * (densityIn s PA PK * volume PK.carrier) := by
      have hsum : ∑ i ∈ s with PA i ≤ PK, volume (PA i).carrier
          = densityIn s PA PK * volume PK.carrier := by
        by_cases hKvol0 : volume PK.carrier = 0
        · have hsum0 : ∑ i ∈ s with PA i ≤ PK, volume (PA i).carrier = 0 := by
            refine Finset.sum_eq_zero (fun i hi => ?_)
            have hPAi_le_PK : PA i ≤ PK := (Finset.mem_filter.mp hi).2
            have hsub : (PA i).carrier ⊆ PK.carrier := hPAi_le_PK
            exact measure_mono_null hsub hKvol0
          rw [hsum0, hKvol0, mul_zero]
        · have hPKvol_ne_top : volume PK.carrier ≠ ∞ := by
            intro h
            have hKvol_inf : volume K.carrier = ∞ := by
              rw [hKvol, h]
              simp [hr.ne']
            exact K.isCompact.measure_ne_top hKvol_inf
          rw [densityIn, ENNReal.div_mul_cancel hKvol0 hPKvol_ne_top]
      rw [hsum]
    _ = (2*(r:ENNReal) * densityIn s PA PK) * volume PK.carrier := by ring
    _ = densityIn s PA PK * (2*(r:ENNReal) * volume PK.carrier) := by ring
    _ = densityIn s PA PK * volume K.carrier := by rw [hKvol]

/-- A reverse volume comparison for every body gives the reverse density comparison. -/
theorem densityIn_orthogonalProjection_image_le
    (s : Finset ι)
    (H : AffineSubspace ℝ E) [Nonempty ↑H]
    (hcodim : finrank ℝ E = finrank ℝ H.direction + 1)
    (A : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E)
    {r : NNReal} (hr : 0 < r) {D : ENNReal}
    (hAslab : ∀ i ∈ s, (A i).carrier ⊆ cthickening r (H : Set E))
    (hKproduct : K.carrier =
      (orthogonalProjection H ⁻¹' (orthogonalProjection H '' K.carrier)) ∩
        cthickening r (H : Set E))
    (hvolume : ∀ i ∈ s,
      2 * (r : ENNReal) * volume ((A i).orthogonalProjectionImage H).carrier ≤
        D * volume (A i).carrier) :
    densityIn s (fun i ↦ (A i).orthogonalProjectionImage H)
        (K.orthogonalProjectionImage H) ≤
      D * densityIn s A K := by
  set PA : ι → ConvexSpaceBody ↑H := fun i ↦ (A i).orthogonalProjectionImage H with hPA
  set PK : ConvexSpaceBody ↑H := K.orthogonalProjectionImage H
  have hKvol : volume K.carrier = 2 * (r : ENNReal) * volume PK.carrier :=
    volume_eq_two_mul_volume_orthogonalProjectionImage H hcodim K r hKproduct
  have hfilter : {i ∈ s | A i ≤ K} = {i ∈ s | PA i ≤ PK} :=
    Finset.filter_congr fun i hi ↦
      orthogonalProjectionImage_le_iff H (A i) K r (hAslab i hi) hKproduct
  have hcalc :
      2 * (r : ENNReal) * (∑ i ∈ s with PA i ≤ PK, volume (PA i).carrier) ≤
        D * (∑ i ∈ s with A i ≤ K, volume (A i).carrier) := by
    rw [Finset.mul_sum, ← hfilter, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi ↦ by
      simpa [hPA] using hvolume i (Finset.mem_filter.mp hi).1
  simp only [Kakeya.densityIn, hKvol]
  calc
    (∑ i ∈ s with PA i ≤ PK, volume (PA i).carrier) / volume PK.carrier =
        (2 * (r : ENNReal) * (∑ i ∈ s with PA i ≤ PK, volume (PA i).carrier)) /
          (2 * (r : ENNReal) * volume PK.carrier) :=
      (ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)).symm
    _ ≤ (D * (∑ i ∈ s with A i ≤ K, volume (A i).carrier)) /
        (2 * (r : ENNReal) * volume PK.carrier) :=
      ENNReal.div_le_div_right hcalc _
    _ = D * ((∑ i ∈ s with A i ≤ K, volume (A i).carrier) /
        (2 * (r : ENNReal) * volume PK.carrier)) := by rw [mul_div_assoc]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Any convex body contained in the shadow of a product body `K` is itself the shadow of a
product body contained in `K`. -/
theorem exists_pullback_of_le_orthogonalProjectionImage
    (H : AffineSubspace ℝ E) [Nonempty ↑H]
    (K : ConvexSpaceBody E) (r : NNReal)
    (hKproduct : K.carrier =
      (orthogonalProjection H ⁻¹' (orthogonalProjection H '' K.carrier)) ∩
        cthickening r (H : Set E))
    (K' : ConvexSpaceBody ↑H) (hK' : K' ≤ K.orthogonalProjectionImage H) :
    ∃ L : ConvexSpaceBody E, L ≤ K ∧ L.orthogonalProjectionImage H = K' ∧
      L.carrier =
        (orthogonalProjection H ⁻¹' (orthogonalProjection H '' L.carrier)) ∩
          cthickening r (H : Set E) := by
  have hK'sub : (K' : Set (↑H)) ⊆ orthogonalProjection H '' (K : Set E) := by
    have hsub' :
        (K' : Set (↑H)) ⊆ ((K.orthogonalProjectionImage H : ConvexSpaceBody ↑H) : Set (↑H)) :=
      (SetLike.coe_subset_coe.mpr hK')
    calc
      (K' : Set (↑H)) ⊆ ((K.orthogonalProjectionImage H : ConvexSpaceBody ↑H) : Set (↑H)) := hsub'
      _ = orthogonalProjection H '' (K : Set E) := ConvexSpaceBody.coe_orthogonalProjectionImage K H
  set Lcarrier := (orthogonalProjection H ⁻¹' (K' : Set (↑H))) ∩ (K : Set E) with hLcarrier
  have hconvex : Convexity.IsConvexSet ℝ Lcarrier := by
    rw [hLcarrier]
    exact
      (Convexity.IsConvexSet.affineMap_preimage (orthogonalProjection H).toAffineMap
        K'.convex').inter K.convex'
  have hcompact : IsCompact Lcarrier := by
    rw [hLcarrier]
    have hclosed : IsClosed (orthogonalProjection H ⁻¹' (K' : Set (↑H))) :=
      K'.isCompact.isClosed.preimage (orthogonalProjection H).continuous
    exact K.isCompact.inter_left hclosed
  have hnonempty : Lcarrier.Nonempty := by
    obtain ⟨k', hk'⟩ := K'.nonempty
    obtain ⟨x, hxK, hx⟩ := hK'sub hk'
    refine ⟨x, ?_, hxK⟩
    have hx' : orthogonalProjection H x = k' := hx
    simpa [hx'] using hk'
  let L : ConvexSpaceBody E :=
    { carrier := Lcarrier
      convex' := hconvex
      isCompact' := hcompact
      nonempty' := hnonempty
    }
  have hLπ_eq_K' : orthogonalProjection H '' (L : Set E) = (K' : Set (↑H)) := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hxL, rfl⟩
      have hx_carrier : x ∈ Lcarrier := hxL
      rw [hLcarrier] at hx_carrier
      exact hx_carrier.1
    · rintro y hy
      have hy' : y ∈ orthogonalProjection H '' (K : Set E) := hK'sub hy
      obtain ⟨x, hxK, hx⟩ := hy'
      have hxpre : x ∈ orthogonalProjection H ⁻¹' (K' : Set (↑H)) := by
        simpa [hx] using hy
      have hxL : x ∈ (L : Set E) := ⟨hxpre, hxK⟩
      exact ⟨x, hxL, hx⟩
  have hcarrier_eq : L.carrier =
      (orthogonalProjection H ⁻¹' (orthogonalProjection H '' L.carrier)) ∩
        cthickening r (H : Set E) := by
    have hcarrier_eq_inter : (L : Set E)
        = (orthogonalProjection H ⁻¹' (K' : Set (↑H))) ∩ cthickening r (H : Set E) := by
      apply Set.ext
      intro x
      constructor
      · rintro ⟨hxpre, hxK⟩
        have hxK' : x ∈ K.carrier := hxK
        rw [hKproduct] at hxK'
        obtain ⟨_, hxN⟩ := hxK'
        exact ⟨hxpre, hxN⟩
      · rintro ⟨hxpre, hxN⟩
        have hx_pre_prod : x ∈ orthogonalProjection H ⁻¹' (orthogonalProjection H '' K.carrier) :=
          Set.preimage_mono hK'sub hxpre
        have hxK : x ∈ K.carrier := by
          apply (Set.ext_iff.mp hKproduct x).mpr
          exact ⟨hx_pre_prod, hxN⟩
        exact ⟨hxpre, hxK⟩
    calc
      L.carrier = (L : Set E) := rfl
      _ = (orthogonalProjection H ⁻¹' (K' : Set (↑H))) ∩ cthickening r (H : Set E) :=
        hcarrier_eq_inter
      _ = (orthogonalProjection H ⁻¹' (orthogonalProjection H '' (L : Set E)))
            ∩ cthickening r (H : Set E) := by
        rw [hLπ_eq_K']
      _ = (orthogonalProjection H ⁻¹' (orthogonalProjection H '' L.carrier))
            ∩ cthickening r (H : Set E) := rfl
  refine ⟨L, ?_, ?_, ?_⟩
  · -- L ≤ K
    have hsub : (L : Set E) ⊆ (K : Set E) := by
      intro x hx
      have : x ∈ Lcarrier := hx
      rw [hLcarrier] at this
      exact this.2
    exact SetLike.coe_subset_coe.mp hsub
  · -- L.orthogonalProjectionImage H = K'
    apply ConvexSpaceBody.ext
    calc
      ((L.orthogonalProjectionImage H : ConvexSpaceBody ↑H) : Set (↑H)) =
          orthogonalProjection H '' L.carrier := ConvexSpaceBody.coe_orthogonalProjectionImage L H
      _ = orthogonalProjection H '' (L : Set E) := rfl
      _ = (K' : Set (↑H)) := hLπ_eq_K'
      _ = ((K' : ConvexSpaceBody ↑H) : Set (↑H)) := rfl
  · -- L.carrier =... as above
    exact hcarrier_eq

end ProjectionDensity

namespace ConvexSpaceBody.IsFrostmanIn

variable {ι : Type*}

/-- A Frostman family in the full part of a slab over its shadow remains Frostman after
projection, provided every body satisfies the stated reverse volume comparison. -/
theorem image_orthogonalProjection
    (s : Finset ι)
    (H : AffineSubspace ℝ E) [Nonempty ↑H]
    (hcodim : finrank ℝ E = finrank ℝ H.direction + 1)
    (A : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E)
    {r : NNReal} (hr : 0 < r) {C D : ENNReal}
    (hAslab : ∀ i ∈ s, (A i).carrier ⊆ Metric.cthickening r (H : Set E))
    (hKproduct : K.carrier =
      (orthogonalProjection H ⁻¹' (orthogonalProjection H '' K.carrier)) ∩
        Metric.cthickening r (H : Set E))
    (hvolume : ∀ i ∈ s,
      2 * (r : ENNReal) * volume ((A i).orthogonalProjectionImage H).carrier ≤
        D * volume (A i).carrier)
    (hFrostman : IsFrostmanIn s A K C) :
    IsFrostmanIn s (fun i ↦ (A i).orthogonalProjectionImage H)
      (K.orthogonalProjectionImage H) (D * C) := by
  set PA : ι → ConvexSpaceBody ↑H := fun i ↦ (A i).orthogonalProjectionImage H with hPA
  set PK : ConvexSpaceBody ↑H := K.orthogonalProjectionImage H with hPK
  intro K' hK'
  -- hK' : K' ≤ PK
  obtain ⟨L, hLK, hLproj, hLproduct⟩ :=
    exists_pullback_of_le_orthogonalProjectionImage H K r hKproduct K' hK'
  calc
    densityIn s PA K'
        = densityIn s PA (L.orthogonalProjectionImage H) := by rw [hLproj]
    _ ≤ D * densityIn s A L :=
      densityIn_orthogonalProjection_image_le s H hcodim A L hr hAslab hLproduct hvolume
    _ ≤ D * (C * densityIn s A K) := by
      gcongr
      exact hFrostman L hLK
    _ ≤ D * (C * densityIn s PA PK) := by
      gcongr
      exact le_densityIn_orthogonalProjection_image s H hcodim A K hr hAslab hKproduct
    _ = (D * C) * densityIn s PA PK := by ring

end ConvexSpaceBody.IsFrostmanIn
