import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalCleanupSourceReregularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalGrainTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.SaturationPlaneMapExtension

/-!
# Local-grain provenance for the affine-diagonal final family

This module records the exact source shading paired with the twice-regularized
affine-diagonal target.  It deliberately separates the exact affine image
from the cubical saturation: inverse-transpose normals are defined on the
former, and a later extension step is responsible for the latter.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

namespace PureWZ2ExternalWeightRegularizationData

/-- The twice-selected source shading whose index type agrees literally with
the final affine-diagonal target family. -/
def cleanupTargetSourceShading
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount) :
    WZ1PaperTubeShading data.selected.family :=
  restrictPaperShading data.selected
    (restrictPaperShading regularized.selected popular.popular.restricted)

/-- The genuine Node-5 local-grain field restricted through exactly the two
source selections used by the final affine-diagonal target. -/
def cleanupTargetSourceLocalGrains
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount) :
    PureWZ2LocalGrainData
      (cleanupTargetSourceShading (regularized := regularized)
        (cleanup := cleanup) (outputConstant := outputConstant)
          (outputLevelCount := outputLevelCount) data) sigma
      band.sourceConstant :=
  (popular.localGrains.subfamily regularized.selected).subfamily data.selected

/-- The final target shading is precisely the target-grid saturation of the
affine image of its synchronized twice-selected source carrier. -/
theorem cleanupTargetShading_carrier_eq_saturation
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount)
    (index : Fin data.selected.family.card) :
    (cleanupTargetShading (cleanup := cleanup) data).carrier index =
      wz1PaperCubicalSaturation scale.targetDelta
        (pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope
            cleanup.raw.center scale.slopeData.heightScale
              scale.slopeData.transverseScale 1 ''
          (cleanupTargetSourceShading (regularized := regularized)
            (cleanup := cleanup) (outputConstant := outputConstant)
              (outputLevelCount := outputLevelCount) data).carrier index) := by
  change cleanup.raw.shading.carrier
      (cleanup.selected.orderEmbOfFin rfl
        (cleanupSourcePreimage (cleanup := cleanup) data index)) = _
  rw [cleanup.raw.shading_carrier]
  congr 2
  have hindex : cleanup.selected.orderEmbOfFin rfl
        (cleanupSourcePreimage (cleanup := cleanup) data index) =
      data.selected.embedding index :=
    cleanupSourcePreimage_ambient (cleanup := cleanup) data index
  rw [hindex]
  rfl

/-- The exact affine image before target-grid saturation. -/
def cleanupTargetExactShading
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount) :
    WZ1PaperTubeShading
      (cleanupTargetSubfamily (cleanup := cleanup) data).family where
  carrier index :=
    (pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope
          cleanup.raw.center scale.slopeData.heightScale
            scale.slopeData.transverseScale (1 : ℝ) ''
        (cleanupTargetSourceShading (regularized := regularized)
          (cleanup := cleanup) (outputConstant := outputConstant)
            (outputLevelCount := outputLevelCount) data).carrier index) ∩
      (cleanupTargetShading (cleanup := cleanup) data).carrier index
  measurable_carrier index := by
    let equivalence := pureWZ2AffineDiagonalAffineEquivCentered
      scale.slopeData.frameSlope cleanup.raw.center
      scale.slopeData.heightScale scale.slopeData.transverseScale (1 : ℝ)
      (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
      scale.transverse_pos.ne' one_ne_zero
    have heq :
        pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope
              cleanup.raw.center scale.slopeData.heightScale
                scale.slopeData.transverseScale (1 : ℝ) ''
            (cleanupTargetSourceShading (regularized := regularized)
              (cleanup := cleanup) (outputConstant := outputConstant)
                (outputLevelCount := outputLevelCount) data).carrier index =
          equivalence ''
            (cleanupTargetSourceShading (regularized := regularized)
              (cleanup := cleanup) (outputConstant := outputConstant)
                (outputLevelCount := outputLevelCount) data).carrier index := by
      ext point
      simp only [Set.mem_image]
      constructor <;> rintro ⟨source, hsource, rfl⟩
      · exact ⟨source, hsource,
          pureWZ2AffineDiagonalAffineEquivCentered_apply _ _ _ _ _ _ _ _ _⟩
      · exact ⟨source, hsource,
          (pureWZ2AffineDiagonalAffineEquivCentered_apply _ _ _ _ _ _ _ _ _).symm⟩
    rw [heq]
    exact (equivalence.toHomeomorphOfFiniteDimensional.toMeasurableEquiv
      |>.measurableSet_image.mpr
        ((cleanupTargetSourceShading (regularized := regularized)
          (cleanup := cleanup) (outputConstant := outputConstant)
            (outputLevelCount := outputLevelCount) data).measurable_carrier index)).inter
      ((cleanupTargetShading (cleanup := cleanup) data).measurable_carrier index)
  subset_body index := Set.inter_subset_right.trans
    ((cleanupTargetShading (cleanup := cleanup) data).subset_body index)

@[simp] theorem cleanupTargetExactShading_carrier
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount) (index) :
    (cleanupTargetExactShading (regularized := regularized)
      (cleanup := cleanup) (outputConstant := outputConstant)
        (outputLevelCount := outputLevelCount) data).carrier index =
      (pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope
            cleanup.raw.center scale.slopeData.heightScale
              scale.slopeData.transverseScale (1 : ℝ) ''
          (cleanupTargetSourceShading (regularized := regularized)
            (cleanup := cleanup) (outputConstant := outputConstant)
              (outputLevelCount := outputLevelCount) data).carrier index) ∩
        (cleanupTargetShading (cleanup := cleanup) data).carrier index := rfl

theorem cleanupTargetExactShading_subshading
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount) :
    ∀ index,
      (cleanupTargetExactShading (regularized := regularized)
        (cleanup := cleanup) (outputConstant := outputConstant)
          (outputLevelCount := outputLevelCount) data).carrier index ⊆
      (cleanupTargetShading (cleanup := cleanup) data).carrier index := by
  intro index point hpoint
  change Fin data.selected.family.card at index
  exact hpoint.2

/-- The exact affine-image union is literally the image of the synchronized
source union.  This supplies the canonical inverse-image point used by the
inverse-transpose normal field. -/
theorem cleanupTargetExactShading_union
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount) :
    (cleanupTargetExactShading (regularized := regularized)
      (cleanup := cleanup) data).union =
      pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope
          cleanup.raw.center scale.slopeData.heightScale
            scale.slopeData.transverseScale 1 ''
        (cleanupTargetSourceShading (regularized := regularized)
          (cleanup := cleanup) data).union := by
  ext point
  constructor
  · rintro ⟨index, hpoint⟩
    rcases hpoint.1 with ⟨source, hsource, heq⟩
    exact ⟨source, ⟨index, hsource⟩, heq⟩
  · rintro ⟨source, ⟨index, hsource⟩, rfl⟩
    refine ⟨index, ⟨⟨source, hsource, rfl⟩, ?_⟩⟩
    rw [cleanupTargetShading_carrier_eq_saturation
      (regularized := regularized) (cleanup := cleanup) data]
    exact ⟨_, ⟨source, hsource, rfl⟩, rfl⟩

/-- Canonical source preimage of a point in the exact affine-image shading. -/
def cleanupTargetExactSourcePoint
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount)
    (target : {point : Point3 // point ∈
      (cleanupTargetExactShading (regularized := regularized)
        (cleanup := cleanup) data).union}) :
    {point : Point3 // point ∈
      (cleanupTargetSourceShading (regularized := regularized)
        (cleanup := cleanup) data).union} :=
  let equivalence := pureWZ2AffineDiagonalAffineEquivCentered
    scale.slopeData.frameSlope cleanup.raw.center
    scale.slopeData.heightScale scale.slopeData.transverseScale 1
    (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
    scale.transverse_pos.ne' one_ne_zero
  ⟨equivalence.symm target, by
    have htargetImageMap : target.1 ∈
        pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope
            cleanup.raw.center scale.slopeData.heightScale
              scale.slopeData.transverseScale 1 ''
          (cleanupTargetSourceShading (regularized := regularized)
            (cleanup := cleanup) data).union := by
      rw [← cleanupTargetExactShading_union
        (regularized := regularized) (cleanup := cleanup) data]
      exact target.property
    have htargetImage : target.1 ∈ equivalence ''
        (cleanupTargetSourceShading (regularized := regularized)
          (cleanup := cleanup) data).union := by
      rcases htargetImageMap with ⟨source, hsource, heq⟩
      exact ⟨source, hsource, by
        rw [pureWZ2AffineDiagonalAffineEquivCentered_apply]
        exact heq⟩
    rcases htargetImage with ⟨source, hsource, heq⟩
    have htargetEq : target.1 = equivalence source := heq.symm
    rw [htargetEq, AffineEquiv.symm_apply_apply]
    exact hsource⟩

@[simp] theorem cleanupTarget_map_exactSourcePoint
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount)
    (target : {point : Point3 // point ∈
      (cleanupTargetExactShading (regularized := regularized)
        (cleanup := cleanup) data).union}) :
    pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope
        cleanup.raw.center scale.slopeData.heightScale
          scale.slopeData.transverseScale 1
          (cleanupTargetExactSourcePoint (regularized := regularized)
            (cleanup := cleanup) data target) = target := by
  rw [← pureWZ2AffineDiagonalAffineEquivCentered_apply]
  exact AffineEquiv.apply_symm_apply _ _

/-- Normalized inverse-transpose of the genuine restricted Node-5 normal. -/
def cleanupTargetExactPlaneMap
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount)
    (target : {point : Point3 // point ∈
      (cleanupTargetExactShading (regularized := regularized)
        (cleanup := cleanup) data).union}) : Point3 :=
  let transported := pureWZ2AffineDiagonalInvTranspose
    scale.slopeData.frameSlope scale.slopeData.heightScale
      scale.slopeData.transverseScale 1
      ((cleanupTargetSourceLocalGrains (regularized := regularized)
        (cleanup := cleanup) data).planeMap
          (cleanupTargetExactSourcePoint (regularized := regularized)
            (cleanup := cleanup) data target))
  (‖transported‖⁻¹ : ℝ) • transported

/-- A unit normal cannot collapse under the affine-diagonal inverse
transpose.  The height stretch is the largest singular scale used here. -/
theorem pureWZ2AffineDiagonalInvTranspose_norm_lower_of_unit
    (frameSlope : ℝ)
    {heightScale transverseScale : ℝ}
    (hheight : 1 ≤ heightScale)
    (htransverse : 0 < transverseScale)
    (htransverseOne : transverseScale ≤ 1)
    {normal : Point3} (hnormal : ‖normal‖ = 1) :
    1 / heightScale ≤
      ‖pureWZ2AffineDiagonalInvTranspose frameSlope heightScale
        transverseScale 1 normal‖ := by
  let image := pureWZ2AffineDiagonalLinear frameSlope heightScale
    transverseScale 1 normal
  let transported := pureWZ2AffineDiagonalInvTranspose frameSlope heightScale
    transverseScale 1 normal
  have hidentity : inner ℝ image transported = inner ℝ normal normal := by
    exact pureWZ2AffineDiagonal_inner_identity frameSlope
      (by linarith) htransverse.ne' one_ne_zero normal normal
  have hinner : (1 : ℝ) ≤ ‖image‖ * ‖transported‖ := by
    calc
      (1 : ℝ) = |inner ℝ normal normal| := by
        rw [real_inner_self_eq_norm_sq, hnormal]
        norm_num
      _ = |inner ℝ image transported| := by rw [hidentity]
      _ ≤ ‖image‖ * ‖transported‖ := abs_real_inner_le_norm _ _
  have himage : ‖image‖ ≤ heightScale := by
    simpa [image, hnormal] using
      pureWZ2AffineDiagonalLinear_norm_le_height frameSlope hheight
        htransverse.le htransverseOne normal
  have hheightPos : 0 < heightScale := lt_of_lt_of_le zero_lt_one hheight
  apply (div_le_iff₀ hheightPos).2
  calc
    1 ≤ ‖image‖ * ‖transported‖ := hinner
    _ ≤ heightScale * ‖transported‖ := by gcongr
    _ = ‖pureWZ2AffineDiagonalInvTranspose frameSlope heightScale
        transverseScale 1 normal‖ * heightScale := by
      dsimp only [transported]
      ring

/-- The exact transported normal has unit norm after normalization. -/
theorem cleanupTargetExactPlaneMap_unit
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount)
    (target : {point : Point3 // point ∈
      (cleanupTargetExactShading (regularized := regularized)
        (cleanup := cleanup) data).union}) :
    ‖cleanupTargetExactPlaneMap (regularized := regularized)
      (cleanup := cleanup) data target‖ = 1 := by
  let sourceLocal := cleanupTargetSourceLocalGrains
    (regularized := regularized) (cleanup := cleanup) data
  let source := cleanupTargetExactSourcePoint
    (regularized := regularized) (cleanup := cleanup) data target
  let transported := pureWZ2AffineDiagonalInvTranspose
    scale.slopeData.frameSlope scale.slopeData.heightScale
      scale.slopeData.transverseScale 1 (sourceLocal.planeMap source)
  have htransportedLower : 1 / scale.slopeData.heightScale ≤
      ‖transported‖ := by
    exact pureWZ2AffineDiagonalInvTranspose_norm_lower_of_unit
      scale.slopeData.frameSlope (by linarith [scale.height_lower])
      scale.transverse_pos (scale.transverse_le.trans (by norm_num))
      (sourceLocal.planeMap_unit source)
  have htransportedPos : 0 < ‖transported‖ := by
    have hheightPos : 0 < scale.slopeData.heightScale := by
      linarith [scale.height_lower]
    exact lt_of_lt_of_le (by positivity : 0 < 1 / scale.slopeData.heightScale)
      htransportedLower
  change ‖(‖transported‖⁻¹ : ℝ) • transported‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp [htransportedPos.ne']

/-- The exact source-preimage map has the Lipschitz constant of the inverse
linear equivalence. -/
theorem cleanupTargetExactSourcePoint_lipschitz
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount) :
    LipschitzWith
      ‖(pureWZ2AffineDiagonalLinearEquiv scale.slopeData.frameSlope
          scale.slopeData.heightScale scale.slopeData.transverseScale 1
          (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
          scale.transverse_pos.ne' one_ne_zero).symm
            |>.toContinuousLinearEquiv.toContinuousLinearMap‖₊
      (cleanupTargetExactSourcePoint (regularized := regularized)
        (cleanup := cleanup) data) := by
  let equivalence := pureWZ2AffineDiagonalAffineEquivCentered
    scale.slopeData.frameSlope cleanup.raw.center
    scale.slopeData.heightScale scale.slopeData.transverseScale 1
    (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
    scale.transverse_pos.ne' one_ne_zero
  let inverseLinear :=
    (pureWZ2AffineDiagonalLinearEquiv scale.slopeData.frameSlope
      scale.slopeData.heightScale scale.slopeData.transverseScale 1
      (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
      scale.transverse_pos.ne' one_ne_zero).symm.toContinuousLinearEquiv
  apply LipschitzWith.of_dist_le_mul
  intro first second
  have hfirst :
      (cleanupTargetExactSourcePoint (regularized := regularized)
        (cleanup := cleanup) data first : Point3) =
          equivalence.symm first := rfl
  have hsecond :
      (cleanupTargetExactSourcePoint (regularized := regularized)
        (cleanup := cleanup) data second : Point3) =
          equivalence.symm second := rfl
  have hsub : equivalence.symm first - equivalence.symm second =
      inverseLinear ((first : Point3) - (second : Point3)) := by
    have h := AffineMap.linearMap_vsub equivalence.symm.toAffineMap
      (first : Point3) (second : Point3)
    change equivalence.symm.linear (first.1 - second.1) =
      equivalence.symm first.1 - equivalence.symm second.1 at h
    rw [AffineEquiv.linear_symm equivalence] at h
    exact h.symm
  have hlinear := inverseLinear.lipschitz.dist_le_mul
    (first : Point3) (second : Point3)
  rw [Subtype.dist_eq, hfirst, hsecond, dist_eq_norm, hsub]
  rw [dist_eq_norm, ← map_sub] at hlinear
  simpa only [inverseLinear, Subtype.dist_eq] using hlinear

/-- Explicit finite Lipschitz constant of the normalized exact plane map. -/
def cleanupTargetExactPlaneMapK
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized}
    (_data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount) : NNReal :=
  ⟨2 * scale.slopeData.heightScale, by
      linarith [scale.height_lower]⟩ *
    ‖LinearMap.toContinuousLinearMap
      (pureWZ2AffineDiagonalInvTransposeLinear scale.slopeData.frameSlope
        scale.slopeData.heightScale scale.slopeData.transverseScale 1)‖₊ *
    ‖(pureWZ2AffineDiagonalLinearEquiv scale.slopeData.frameSlope
      scale.slopeData.heightScale scale.slopeData.transverseScale 1
      (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
      scale.transverse_pos.ne' one_ne_zero).symm
        |>.toContinuousLinearEquiv.toContinuousLinearMap‖₊

theorem cleanupTargetExactPlaneMap_lipschitz
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount) :
    LipschitzWith (cleanupTargetExactPlaneMapK
      (regularized := regularized) (cleanup := cleanup) data)
      (cleanupTargetExactPlaneMap (regularized := regularized)
        (cleanup := cleanup) data) := by
  let sourceLocal := cleanupTargetSourceLocalGrains
    (regularized := regularized) (cleanup := cleanup) data
  let sourceMap := cleanupTargetExactSourcePoint
    (regularized := regularized) (cleanup := cleanup) data
  let inverseTransposeK :=
    ‖LinearMap.toContinuousLinearMap
      (pureWZ2AffineDiagonalInvTransposeLinear scale.slopeData.frameSlope
        scale.slopeData.heightScale scale.slopeData.transverseScale 1)‖₊
  let sourcePreimageK :=
    ‖(pureWZ2AffineDiagonalLinearEquiv scale.slopeData.frameSlope
      scale.slopeData.heightScale scale.slopeData.transverseScale 1
      (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
      scale.transverse_pos.ne' one_ne_zero).symm
        |>.toContinuousLinearEquiv.toContinuousLinearMap‖₊
  let unnormalized := fun target =>
    pureWZ2AffineDiagonalInvTranspose scale.slopeData.frameSlope
      scale.slopeData.heightScale scale.slopeData.transverseScale 1
        (sourceLocal.planeMap (sourceMap target))
  have hsourceMap : LipschitzWith sourcePreimageK sourceMap := by
    simpa only [sourceMap, sourcePreimageK] using
      cleanupTargetExactSourcePoint_lipschitz
        (regularized := regularized) (cleanup := cleanup) data
  have hunnormalized : LipschitzWith
      (inverseTransposeK * 1 * sourcePreimageK) unnormalized := by
    have hlinear : LipschitzWith inverseTransposeK
        (pureWZ2AffineDiagonalInvTranspose scale.slopeData.frameSlope
          scale.slopeData.heightScale scale.slopeData.transverseScale 1) := by
      simpa only [inverseTransposeK] using
        pureWZ2AffineDiagonalInvTranspose_lipschitz
          scale.slopeData.frameSlope scale.slopeData.heightScale
            scale.slopeData.transverseScale 1
    simpa only [unnormalized, sourceMap, sourceLocal, Function.comp_def,
      mul_assoc] using
        hlinear.comp
          ((cleanupTargetSourceLocalGrains (regularized := regularized)
            (cleanup := cleanup) data).planeMap_lipschitz.comp hsourceMap)
  apply LipschitzWith.of_dist_le_mul
  intro first second
  have hfirstLower : 1 / scale.slopeData.heightScale ≤
      ‖unnormalized first‖ := by
    exact pureWZ2AffineDiagonalInvTranspose_norm_lower_of_unit
      scale.slopeData.frameSlope (by linarith [scale.height_lower])
      scale.transverse_pos (scale.transverse_le.trans (by norm_num))
      (sourceLocal.planeMap_unit (sourceMap first))
  have hsecondLower : 1 / scale.slopeData.heightScale ≤
      ‖unnormalized second‖ := by
    exact pureWZ2AffineDiagonalInvTranspose_norm_lower_of_unit
      scale.slopeData.frameSlope (by linarith [scale.height_lower])
      scale.transverse_pos (scale.transverse_le.trans (by norm_num))
      (sourceLocal.planeMap_unit (sourceMap second))
  have hnormal := normalization_lipschitz
    (x := unnormalized first) (y := unnormalized second)
    (m := 1 / scale.slopeData.heightScale) (by
      have : 0 < scale.slopeData.heightScale := by
        linarith [scale.height_lower]
      positivity)
    hfirstLower hsecondLower
  have hraw := hunnormalized.dist_le_mul first second
  change dist
      (cleanupTargetExactPlaneMap (regularized := regularized)
        (cleanup := cleanup) data first)
      (cleanupTargetExactPlaneMap (regularized := regularized)
        (cleanup := cleanup) data second) ≤ _
  rw [dist_eq_norm]
  calc
    ‖cleanupTargetExactPlaneMap (regularized := regularized)
          (cleanup := cleanup) data first -
        cleanupTargetExactPlaneMap (regularized := regularized)
          (cleanup := cleanup) data second‖
        ≤ (2 / (1 / scale.slopeData.heightScale)) *
            ‖unnormalized first - unnormalized second‖ := by
          simpa only [cleanupTargetExactPlaneMap, unnormalized,
            sourceLocal, sourceMap] using hnormal
    _ ≤ (2 * scale.slopeData.heightScale) *
        (((inverseTransposeK * 1 * sourcePreimageK : NNReal) : ℝ) *
          dist first second) := by
      have hfactor : 2 / (1 / scale.slopeData.heightScale) =
          2 * scale.slopeData.heightScale := by
        have hheight : scale.slopeData.heightScale ≠ 0 :=
          (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
        rw [one_div]
        field_simp [hheight]
      rw [hfactor]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm] using hraw)
        (by linarith [scale.height_lower])
    _ = ((cleanupTargetExactPlaneMapK (regularized := regularized)
          (cleanup := cleanup) data : NNReal) : ℝ) * dist first second := by
      change (2 * scale.slopeData.heightScale) *
          ((inverseTransposeK : ℝ) * 1 * (sourcePreimageK : ℝ) *
            dist first second) =
        ((2 * scale.slopeData.heightScale) * (inverseTransposeK : ℝ) *
          (sourcePreimageK : ℝ)) * dist first second
      ring

/-- Exact incidence before cubical saturation.  The loss `3` is the fixed
normalization denominator paid by the affine direction/normal pair. -/
theorem cleanupTargetExactPlaneMap_incidence_source
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount) :
    ∀ index point, ∀ hpoint : point ∈
      (cleanupTargetExactShading (regularized := regularized)
        (cleanup := cleanup) data).carrier index,
      |inner ℝ
          ((cleanupTargetSubfamily (cleanup := cleanup) data).family.tube index).direction
          (cleanupTargetExactPlaneMap (regularized := regularized)
            (cleanup := cleanup) data ⟨point, ⟨index, hpoint⟩⟩)| ≤
        3 * delta := by
  intro index point hpoint
  change Fin data.selected.family.card at index
  rcases hpoint.1 with ⟨sourcePoint, hsourcePoint, heq⟩
  let target : {point : Point3 // point ∈
      (cleanupTargetExactShading (regularized := regularized)
        (cleanup := cleanup) data).union} :=
    ⟨point, ⟨index, hpoint⟩⟩
  let sourceLocal := cleanupTargetSourceLocalGrains
    (regularized := regularized) (cleanup := cleanup) data
  let source : {point : Point3 // point ∈
      (cleanupTargetSourceShading (regularized := regularized)
        (cleanup := cleanup) data).union} :=
    cleanupTargetExactSourcePoint (regularized := regularized)
      (cleanup := cleanup) data target
  have hsourceEq : (source : Point3) = sourcePoint := by
    apply (pureWZ2AffineDiagonalAffineEquivCentered
      scale.slopeData.frameSlope cleanup.raw.center
      scale.slopeData.heightScale scale.slopeData.transverseScale 1
      (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
      scale.transverse_pos.ne' one_ne_zero).injective
    rw [pureWZ2AffineDiagonalAffineEquivCentered_apply,
      pureWZ2AffineDiagonalAffineEquivCentered_apply,
      cleanupTarget_map_exactSourcePoint
        (regularized := regularized) (cleanup := cleanup) data]
    exact heq.symm
  have hsourceCarrier : (source : Point3) ∈
      (cleanupTargetSourceShading (regularized := regularized)
        (cleanup := cleanup) data).carrier index := by
    rwa [hsourceEq]
  let directionImage := pureWZ2AffineDiagonalLinear
    scale.slopeData.frameSlope scale.slopeData.heightScale
      scale.slopeData.transverseScale 1
      (wz1PaperDirection (data.selected.family.tube index))
  let normalImage := pureWZ2AffineDiagonalInvTranspose
    scale.slopeData.frameSlope scale.slopeData.heightScale
      scale.slopeData.transverseScale 1 (sourceLocal.planeMap source)
  have hdirectionPos : 0 < ‖directionImage‖ := by
    have hdirectionNonzero :
        wz1PaperDirection (data.selected.family.tube index) ≠ 0 := by
      intro hzero
      have := congrArg norm hzero
      rw [wz1PaperDirection_norm, norm_zero] at this
      norm_num at this
    apply norm_pos_iff.mpr
    intro hzero
    have hinverse := pureWZ2AffineDiagonalLinearInverse_linear
      scale.slopeData.frameSlope
      (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
      scale.transverse_pos.ne' one_ne_zero
      (wz1PaperDirection (data.selected.family.tube index))
    rw [show pureWZ2AffineDiagonalLinear scale.slopeData.frameSlope
        scale.slopeData.heightScale scale.slopeData.transverseScale 1
          (wz1PaperDirection (data.selected.family.tube index)) = directionImage by rfl,
      hzero] at hinverse
    simp [pureWZ2AffineDiagonalLinearInverse, point3] at hinverse
    exact hdirectionNonzero hinverse.symm
  have hnormalLower : 1 / scale.slopeData.heightScale ≤ ‖normalImage‖ := by
    exact pureWZ2AffineDiagonalInvTranspose_norm_lower_of_unit
      scale.slopeData.frameSlope (by linarith [scale.height_lower])
      scale.transverse_pos (scale.transverse_le.trans (by norm_num))
      (sourceLocal.planeMap_unit source)
  have hnormalPos : 0 < ‖normalImage‖ := by
    exact lt_of_lt_of_le (by
      have : 0 < scale.slopeData.heightScale := by
        linarith [scale.height_lower]
      positivity) hnormalLower
  have hdirectionLower : scale.slopeData.heightScale / 2 ≤
      ‖directionImage‖ := by
    have hvertical := (band.lemma31.data.cfg.line_class
      (regularized.selected.embedding (data.selected.embedding index))).1
    have hsourceTube : data.selected.family.tube index =
        band.lemma31.data.cfg.family.tube
          (regularized.selected.embedding (data.selected.embedding index)) := by
      rw [data.selected.tube_eq, regularized.selected.tube_eq]
    have hcoord : |directionImage 2| ≤ ‖directionImage‖ := by
      exact PiLp.norm_apply_le directionImage 2
    have himageTwo : directionImage 2 =
        scale.slopeData.heightScale *
          wz1PaperDirection (data.selected.family.tube index) 2 := by
      simp [directionImage, pureWZ2AffineDiagonalLinear, point3,
        pureWZ2HorizontalRotation_coord_two]
    rw [himageTwo, abs_mul,
      abs_of_pos (by linarith [scale.height_lower])] at hcoord
    have hsourceVertical : (1 / 2 : ℝ) ≤
        wz1PaperDirection (data.selected.family.tube index) 2 := by
      rw [hsourceTube]
      exact hvertical
    have hsourceVerticalNonneg : 0 ≤
        wz1PaperDirection (data.selected.family.tube index) 2 := by linarith
    rw [abs_of_nonneg hsourceVerticalNonneg] at hcoord
    nlinarith
  have hproduct : (1 / 2 : ℝ) ≤ ‖directionImage‖ * ‖normalImage‖ := by
    have hheightNonzero : scale.slopeData.heightScale ≠ 0 :=
      (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
    have hidentity : (1 : ℝ) = scale.slopeData.heightScale /
        scale.slopeData.heightScale := by field_simp [hheightNonzero]
    calc
      (1 / 2 : ℝ) = (scale.slopeData.heightScale / 2) *
          (1 / scale.slopeData.heightScale) := by
        rw [show (scale.slopeData.heightScale / 2) *
            (1 / scale.slopeData.heightScale) =
          (1 / 2) * (scale.slopeData.heightScale /
            scale.slopeData.heightScale) by ring, ← hidentity]
        ring
      _ ≤ ‖directionImage‖ * ‖normalImage‖ := by
        exact mul_le_mul hdirectionLower hnormalLower
          (by
            have : 0 < scale.slopeData.heightScale := by
              linarith [scale.height_lower]
            positivity)
          (norm_nonneg _)
  have hinnerIdentity : inner ℝ directionImage normalImage =
      inner ℝ (wz1PaperDirection (data.selected.family.tube index))
        (sourceLocal.planeMap source) := by
    exact pureWZ2AffineDiagonal_inner_identity scale.slopeData.frameSlope
      (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
      scale.transverse_pos.ne' one_ne_zero _ _
  have hsourceIncidence := sourceLocal.planeMap_incidence
    index (source : Point3) hsourceCarrier
  have hsourceIncidencePaper :
      |inner ℝ (wz1PaperDirection (data.selected.family.tube index))
        (sourceLocal.planeMap source)| ≤ delta := by
    unfold wz1PaperDirection
    split_ifs
    · exact hsourceIncidence
    · simpa [inner_neg_left, abs_neg] using hsourceIncidence
  have htargetDirection :
      ((cleanupTargetSubfamily (cleanup := cleanup) data).family.tube index).direction =
        (‖directionImage‖⁻¹ : ℝ) • directionImage := by
    have hraw := cleanup.final_direction_source
      (cleanupTargetEmbedding (cleanup := cleanup) data index)
    have hindex : cleanup.selected.orderEmbOfFin rfl
        (cleanupTargetEmbedding (cleanup := cleanup) data index) =
      data.selected.embedding index := by
      rw [cleanupTargetEmbedding_eq_preimage]
      exact cleanupSourcePreimage_ambient (cleanup := cleanup) data index
    change (cleanup.finalFamily.tube
      (cleanupTargetEmbedding (cleanup := cleanup) data index)).direction = _
    rw [hraw]
    change pureWZ2AffineDiagonalDirection scale.slopeData.frameSlope
        scale.slopeData.heightScale scale.slopeData.transverseScale 1
          (wz1PaperDirection (regularized.selected.family.tube
            (cleanup.selected.orderEmbOfFin rfl
              (cleanupTargetEmbedding (cleanup := cleanup) data index)))) = _
    rw [hindex]
    change _ = pureWZ2AffineDiagonalDirection scale.slopeData.frameSlope
      scale.slopeData.heightScale scale.slopeData.transverseScale 1
        (wz1PaperDirection (data.selected.family.tube index))
    rw [data.selected.tube_eq index]
  have htargetNormal :
      cleanupTargetExactPlaneMap (regularized := regularized)
          (cleanup := cleanup) data target =
        (‖normalImage‖⁻¹ : ℝ) • normalImage := by
    rfl
  rw [htargetDirection, htargetNormal]
  have hnormalized :
      |inner ℝ ((‖directionImage‖⁻¹ : ℝ) • directionImage)
          ((‖normalImage‖⁻¹ : ℝ) • normalImage)| =
        |inner ℝ directionImage normalImage| /
          (‖directionImage‖ * ‖normalImage‖) := by
    rw [inner_smul_left, inner_smul_right]
    simp only [starRingEnd_apply, star_trivial, abs_mul,
      abs_of_pos (inv_pos.mpr hdirectionPos),
      abs_of_pos (inv_pos.mpr hnormalPos)]
    field_simp [hdirectionPos.ne', hnormalPos.ne']
  rw [hnormalized, hinnerIdentity]
  calc
    |inner ℝ (wz1PaperDirection (data.selected.family.tube index))
        (sourceLocal.planeMap source)| /
          (‖directionImage‖ * ‖normalImage‖)
        ≤ 2 * |inner ℝ (wz1PaperDirection (data.selected.family.tube index))
            (sourceLocal.planeMap source)| := by
          apply (div_le_iff₀ (by positivity)).2
          nlinarith [abs_nonneg (inner ℝ
            (wz1PaperDirection (data.selected.family.tube index))
            (sourceLocal.planeMap source))]
    _ ≤ 2 * delta := by
      exact mul_le_mul_of_nonneg_left hsourceIncidencePaper (by norm_num)
    _ ≤ 3 * delta := by linarith [band.lemma31.data.cfg.extremal.delta_pos]

/-- The affine-diagonal exact normal field, before extending across the final
cubical saturation. -/
structure PureWZ2AffineDiagonalExactPlaneMapData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount) where
  K : NNReal
  planeMap : {point : Point3 // point ∈
    (cleanupTargetExactShading (regularized := regularized)
      (cleanup := cleanup) data).union} → Point3
  planeMap_eq : planeMap = cleanupTargetExactPlaneMap
    (regularized := regularized) (cleanup := cleanup) data
  planeMap_lipschitz : LipschitzWith K planeMap
  planeMap_unit : ∀ point, ‖planeMap point‖ = 1
  planeMap_incidence_source :
    ∀ index point, ∀ hpoint : point ∈
      (cleanupTargetExactShading (regularized := regularized)
        (cleanup := cleanup) data).carrier index,
      |inner ℝ
          ((cleanupTargetSubfamily (cleanup := cleanup) data).family.tube index).direction
          (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ 3 * delta
  planeMap_incidence :
    ∀ index point, ∀ hpoint : point ∈
      (cleanupTargetExactShading (regularized := regularized)
        (cleanup := cleanup) data).carrier index,
      |inner ℝ
          ((cleanupTargetSubfamily (cleanup := cleanup) data).family.tube index).direction
          (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ scale.targetDelta

/-- Assemble all exact-image plane-map data from the genuine Node-5 local
grains and the affine-diagonal map. -/
def toAffineDiagonalExactPlaneMapData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount) :
    PureWZ2AffineDiagonalExactPlaneMapData data :=
  { K := cleanupTargetExactPlaneMapK
      (regularized := regularized) (cleanup := cleanup) data
    planeMap := cleanupTargetExactPlaneMap
      (regularized := regularized) (cleanup := cleanup) data
    planeMap_eq := rfl
    planeMap_lipschitz := cleanupTargetExactPlaneMap_lipschitz
      (regularized := regularized) (cleanup := cleanup) data
    planeMap_unit := cleanupTargetExactPlaneMap_unit
      (regularized := regularized) (cleanup := cleanup) data
    planeMap_incidence_source := cleanupTargetExactPlaneMap_incidence_source
      (regularized := regularized) (cleanup := cleanup) data
    planeMap_incidence := by
      intro index point hpoint
      exact (cleanupTargetExactPlaneMap_incidence_source
        (regularized := regularized) (cleanup := cleanup) data
        index point hpoint).trans (by
          rw [scale.targetDelta_eq]
          nlinarith [band.lemma31.data.cfg.extremal.delta_pos,
            scale.height_lower]) }

end PureWZ2ExternalWeightRegularizationData

end Kakeya.Assouad

end
