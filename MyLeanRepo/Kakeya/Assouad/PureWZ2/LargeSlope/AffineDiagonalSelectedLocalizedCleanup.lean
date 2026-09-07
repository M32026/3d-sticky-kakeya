import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalSelectedFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperCenteredConflictDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperCenteredWeightedSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperParameterFrostman
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalCenteredCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalizedOrdinaryDistinctnessToLineDistance

/-!
# Localized centered cleanup on the public-regularized source indices

The midpoint-rebased family is the ordinary provenance carrier.  The family
defined here uses the same selected source indices and the same affine image
lines, but chooses the height-zero representative needed for the localized
paper conflict count.  Its cropped carrier and literal shading are unchanged.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

def pureWZ2AffineDiagonalSelectedLocalizedFamily
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    (scale : PureWZ2AffineDiagonalScaleData subband)
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount) :
    Kakeya.Streamlined.TubeFamily scale.targetDelta :=
  { card := regularized.selected.family.card
    tube := fun index =>
      pureWZ2PaperZeroBasedTube
        (pureWZ2AffineDiagonalRawTube scale.slopeData.frameSlope
          (pureWZ2AffineDiagonalCommonCenter popular
            (height := scale.slopeData.anchor))
          scale.slopeData.heightScale scale.slopeData.transverseScale 1
          (regularized.selected.family.tube index)
          (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
          scale.transverse_pos.ne' one_ne_zero) }

namespace PureWZ2AffineDiagonalSelectedFamilyData

def localizedFamily
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (_data : PureWZ2AffineDiagonalSelectedFamilyData
      popular scale regularized) :
    Kakeya.Streamlined.TubeFamily scale.targetDelta :=
  pureWZ2AffineDiagonalSelectedLocalizedFamily popular scale regularized

def localizedToPublicIndex
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedFamilyData
      popular scale regularized)
    (index : Fin data.localizedFamily.card) :
    Fin (pureWZ2AffineDiagonalSelectedFamily popular scale regularized).card :=
  ⟨index.val, by
    simpa [localizedFamily, pureWZ2AffineDiagonalSelectedLocalizedFamily,
      pureWZ2AffineDiagonalSelectedFamily] using index.isLt⟩

theorem localized_axis
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedFamilyData
      popular scale regularized)
    (index : Fin data.localizedFamily.card) :
    tubeAxisLine (data.localizedFamily.tube index) =
      pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope data.center
        scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
          tubeAxisLine (regularized.selected.family.tube index) := by
  rw [data.center_eq]
  change tubeAxisLine
      (pureWZ2PaperZeroBasedTube
        (pureWZ2AffineDiagonalRawTube scale.slopeData.frameSlope
          (pureWZ2AffineDiagonalCommonCenter popular
            (height := scale.slopeData.anchor))
          scale.slopeData.heightScale scale.slopeData.transverseScale 1
          (regularized.selected.family.tube index)
          (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
          scale.transverse_pos.ne' one_ne_zero)) = _
  rw [pureWZ2PaperZeroBasedTube_axis]
  exact pureWZ2AffineDiagonalRawTube_axis
    scale.slopeData.frameSlope
    (pureWZ2AffineDiagonalCommonCenter popular
      (height := scale.slopeData.anchor))
    (regularized.selected.family.tube index)
    (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
    scale.transverse_pos.ne' one_ne_zero

theorem localized_axis_ambient
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedFamilyData
      popular scale regularized)
    (index : Fin data.localizedFamily.card) :
    tubeAxisLine (data.localizedFamily.tube index) =
      pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope data.center
        scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
          tubeAxisLine (band.lemma31.data.cfg.family.tube
            (regularized.selected.embedding index)) := by
  rw [data.localized_axis index, regularized.selected.tube_eq index]

theorem localized_axis_eq_public
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedFamilyData
      popular scale regularized)
    (index : Fin data.localizedFamily.card) :
    tubeAxisLine (data.localizedFamily.tube index) =
      tubeAxisLine ((pureWZ2AffineDiagonalSelectedFamily
        popular scale regularized).tube
          (data.localizedToPublicIndex index)) := by
  have hindex : data.localizedToPublicIndex index = index := rfl
  rw [data.localized_axis index, hindex, data.axis index]

theorem localized_carrier_eq_public
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedFamilyData
      popular scale regularized)
    (index : Fin data.localizedFamily.card) :
    wz1PaperTubeCarrier (data.localizedFamily.tube index) =
      wz1PaperTubeCarrier ((pureWZ2AffineDiagonalSelectedFamily
        popular scale regularized).tube
          (data.localizedToPublicIndex index)) := by
  unfold wz1PaperTubeCarrier
  rw [data.localized_axis_eq_public index]

def localizedShading
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedFamilyData
      popular scale regularized) :
    WZ1PaperTubeShading data.localizedFamily where
  carrier := fun index => data.shading.carrier (data.localizedToPublicIndex index)
  measurable_carrier := fun index =>
    data.shading.measurable_carrier (data.localizedToPublicIndex index)
  subset_body index := by
    change data.shading.carrier (data.localizedToPublicIndex index) ⊆
      wz1PaperTubeCarrier (data.localizedFamily.tube index)
    rw [data.localized_carrier_eq_public index]
    exact data.shading.subset_body (data.localizedToPublicIndex index)

theorem localizedShading_mass
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedFamilyData
      popular scale regularized) :
    data.localizedShading.mass = data.shading.mass := by
  apply Finset.sum_bij (fun index _ => data.localizedToPublicIndex index)
  · intro index _
    exact Finset.mem_univ _
  · intro first _ second _ heq
    exact Fin.ext (congrArg Fin.val heq)
  · intro publicIndex _
    let localIndex : Fin data.localizedFamily.card :=
      ⟨publicIndex.val, by
        simpa [localizedFamily, pureWZ2AffineDiagonalSelectedLocalizedFamily,
          pureWZ2AffineDiagonalSelectedFamily] using publicIndex.isLt⟩
    exact ⟨localIndex, Finset.mem_univ _, by apply Fin.ext; rfl⟩
  · intro index _
    rfl

theorem localized_cubical
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedFamilyData
      popular scale regularized) :
    WZ1PaperIsCubicalShading data.localizedShading := by
  intro index point hpoint
  exact data.cubical (data.localizedToPublicIndex index) point hpoint

theorem localized_line_class
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedFamilyData
      popular scale regularized) :
    WZ1PaperIsLineClass data.localizedFamily := by
  intro index
  let rawTube : Kakeya.DeltaTube scale.targetDelta :=
    pureWZ2AffineDiagonalRawTube
    scale.slopeData.frameSlope
    (pureWZ2AffineDiagonalCommonCenter popular
      (height := scale.slopeData.anchor))
    scale.slopeData.heightScale scale.slopeData.transverseScale 1
    (regularized.selected.family.tube index)
    (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
    scale.transverse_pos.ne' one_ne_zero
  let publicTube := (pureWZ2AffineDiagonalSelectedFamily
    popular scale regularized).tube (data.localizedToPublicIndex index)
  have hdir : rawTube.direction = publicTube.direction := rfl
  have hvertical : (1 / 2 : ℝ) ≤ |rawTube.direction 2| := by
    simpa [hdir] using
      (data.line_class (data.localizedToPublicIndex index)).vertical
  have hzero : wz1TubeAxisZeroPoint rawTube =
      wz1TubeAxisZeroPoint publicTube := by
    apply wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero hvertical
    · have hrawAxis : tubeAxisLine rawTube = tubeAxisLine publicTube := by
        have hpublicIndex : data.localizedToPublicIndex index = index := rfl
        calc
          tubeAxisLine rawTube =
              pureWZ2AffineDiagonalMapCentered
                scale.slopeData.frameSlope
                (pureWZ2AffineDiagonalCommonCenter popular
                  (height := scale.slopeData.anchor))
                scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
                  tubeAxisLine (regularized.selected.family.tube index) :=
            pureWZ2AffineDiagonalRawTube_axis
              scale.slopeData.frameSlope
              (pureWZ2AffineDiagonalCommonCenter popular
                (height := scale.slopeData.anchor))
              (regularized.selected.family.tube index)
              (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
              scale.transverse_pos.ne' one_ne_zero
          _ = pureWZ2AffineDiagonalMapCentered
                scale.slopeData.frameSlope data.center
                scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
                  tubeAxisLine
                    (regularized.selected.family.tube
                      (data.localizedToPublicIndex index)) := by
            rw [data.center_eq, hpublicIndex]
          _ = tubeAxisLine publicTube := by
            exact (data.axis (data.localizedToPublicIndex index)).symm
      rw [hrawAxis]
      exact wz1TubeAxisZeroPoint_mem_axis publicTube
    · exact wz1TubeAxisZeroPoint_coord_two publicTube (by
        simpa [hdir] using hvertical)
  have hpaperDir : wz1PaperDirection rawTube =
      wz1PaperDirection publicTube := by
    simp [wz1PaperDirection, hdir]
  have hrawLine : WZ1PaperTubeInLineClass rawTube := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hpaperDir]
      exact (data.line_class (data.localizedToPublicIndex index)).1
    · rw [hzero]
      exact (data.line_class (data.localizedToPublicIndex index)).2.1
    · rw [hzero]
      exact (data.line_class (data.localizedToPublicIndex index)).2.2
  change WZ1PaperTubeInLineClass (pureWZ2PaperZeroBasedTube rawTube)
  exact pureWZ2PaperZeroBasedTube_lineClass hrawLine

/-- Every localized target tube remembers that it is the height-zero based
canonical representative of its affine raw line. -/
theorem localized_zeroBased
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedFamilyData
      popular scale regularized)
    (index : Fin data.localizedFamily.card) :
    pureWZ2PaperZeroBasedTube (data.localizedFamily.tube index) =
      data.localizedFamily.tube index := by
  change
    pureWZ2PaperZeroBasedTube
        (pureWZ2PaperZeroBasedTube
          (pureWZ2AffineDiagonalRawTube scale.slopeData.frameSlope
            (pureWZ2AffineDiagonalCommonCenter popular
              (height := scale.slopeData.anchor))
            scale.slopeData.heightScale scale.slopeData.transverseScale 1
            (regularized.selected.family.tube index)
            (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
            scale.transverse_pos.ne' one_ne_zero)) =
      pureWZ2PaperZeroBasedTube
        (pureWZ2AffineDiagonalRawTube scale.slopeData.frameSlope
          (pureWZ2AffineDiagonalCommonCenter popular
            (height := scale.slopeData.anchor))
          scale.slopeData.heightScale scale.slopeData.transverseScale 1
          (regularized.selected.family.tube index)
          (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
          scale.transverse_pos.ne' one_ne_zero)
  exact pureWZ2PaperZeroBasedTube_idempotent _
    (data.localized_line_class index)

theorem localized_midpoint_le_three
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedFamilyData
      popular scale regularized)
    (index : Fin data.localizedFamily.card) :
    ‖wz2PaperTubeMidpoint (data.localizedFamily.tube index)‖ ≤ 3 := by
  let tube := data.localizedFamily.tube index
  have hline := data.localized_line_class index
  have hvertical : tube.direction 2 ≠ 0 := by
    intro hzero
    have h := hline.vertical
    rw [hzero, abs_zero] at h
    norm_num at h
  have hbaseTwo : tube.base 2 = 0 := by
    change (wz1TubeAxisZeroPoint
      (pureWZ2AffineDiagonalRawTube scale.slopeData.frameSlope
        (pureWZ2AffineDiagonalCommonCenter popular
          (height := scale.slopeData.anchor))
        scale.slopeData.heightScale scale.slopeData.transverseScale 1
        (regularized.selected.family.tube index)
        (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
        scale.transverse_pos.ne' one_ne_zero)) 2 = 0
    exact wz1TubeAxisZeroPoint_coord_two _ (by
      have hsourceLine : WZ1PaperTubeInLineClass
          (regularized.selected.family.tube index) := by
        rw [regularized.selected.tube_eq index]
        exact band.lemma31.data.cfg.line_class
          (regularized.selected.embedding index)
      have hraw := pureWZ2AffineDiagonalDirection_vertical
        scale.slopeData.frameSlope scale.height_lower
        scale.transverse_pos.le (scale.transverse_le.trans (by norm_num))
        (regularized.selected.family.tube index).direction_unit
        hsourceLine.vertical
      exact hraw)
  have hzero : wz1TubeAxisZeroPoint tube = tube.base := by
    simp [wz1TubeAxisZeroPoint, hbaseTwo, hvertical]
  have hxSq : (tube.base 0) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    have hx : |tube.base 0| ≤ 1 / 3 := by
      rw [← hzero]
      exact hline.2.1
    nlinarith [sq_abs (tube.base 0), abs_nonneg (tube.base 0)]
  have hySq : (tube.base 1) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    have hy : |tube.base 1| ≤ 1 / 3 := by
      rw [← hzero]
      exact hline.2.2
    nlinarith [sq_abs (tube.base 1), abs_nonneg (tube.base 1)]
  have hbaseNorm : ‖tube.base‖ ≤ 1 := by
    have hnorm := point3_coord_norm_sq tube.base
    have hnormSq : ‖tube.base‖ ^ 2 ≤ 1 := by
      rw [hnorm, hbaseTwo]
      nlinarith
    nlinarith [norm_nonneg tube.base]
  calc
    ‖wz2PaperTubeMidpoint tube‖ =
        ‖tube.base + (1 / 2 : ℝ) • tube.direction‖ := rfl
    _ ≤ ‖tube.base‖ + ‖(1 / 2 : ℝ) • tube.direction‖ :=
      norm_add_le _ _
    _ = ‖tube.base‖ + 1 / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num),
        tube.direction_unit]
      ring
    _ ≤ 3 := by linarith

end PureWZ2AffineDiagonalSelectedFamilyData

structure PureWZ2AffineDiagonalSelectedLocalizedCleanupData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    (scale : PureWZ2AffineDiagonalScaleData subband)
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount) where
  raw : PureWZ2AffineDiagonalSelectedFamilyData popular scale regularized
  conflict_width_le_one : pureWZ2AffineDiagonalConflictWidth scale ≤ 1
  selected : Finset (Fin raw.localizedFamily.card)
  distinct : WZ2PaperOrdinaryIsEssentiallyDistinct
    (Kakeya.Streamlined.TubeSubfamily.fromFinset
      raw.localizedFamily selected).family
  maximal : ∀ index : Fin raw.localizedFamily.card,
    index ∈ selected ∨ ∃ representative ∈ selected,
      pureWZ2PaperCenteredConflict raw.localizedFamily index representative
  mass_lower : raw.localizedShading.mass ≤
    (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
      (restrictPaperShading
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          raw.localizedFamily selected) raw.localizedShading).mass

theorem PureWZ2AffineDiagonalSelectedFamilyData.toLocalizedCleanup
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (raw : PureWZ2AffineDiagonalSelectedFamilyData popular scale regularized)
    (hwidthOne : pureWZ2AffineDiagonalConflictWidth scale ≤ 1) :
    Nonempty (PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) := by
  let sourceFamily := band.lemma31.data.cfg.family
  let targetFamily := raw.localizedFamily
  let sourceParent : Fin targetFamily.card → Fin sourceFamily.card :=
    regularized.selected.embedding
  have hsourceVertical : ∀ source : Fin sourceFamily.card,
      (sourceFamily.tube source).direction 2 ≠ 0 := by
    intro source hzero
    have h := (band.lemma31.data.cfg.line_class source).vertical
    rw [hzero, abs_zero] at h
    norm_num at h
  have htargetVertical : ∀ target : Fin targetFamily.card,
      (targetFamily.tube target).direction 2 ≠ 0 := by
    intro target hzero
    have h := (raw.localized_line_class target).vertical
    rw [hzero, abs_zero] at h
    norm_num at h
  have hfiber : ∀ source : Fin sourceFamily.card,
      ((Finset.univ : Finset (Fin targetFamily.card)).filter fun target =>
        sourceParent target = source).card ≤ 1 := by
    intro source
    apply Finset.card_le_one.mpr
    intro first hfirst second hsecond
    exact regularized.selected.embedding.injective
      ((Finset.mem_filter.mp hfirst).2.trans
        (Finset.mem_filter.mp hsecond).2.symm)
  have hFrostman : TubeParameterFrostmanBound sourceFamily
      (3200 * band.sourceConstant) :=
    paper_tubeParameterFrostmanBound_of_croppedConvexWolff
      band.lemma31.data.cfg.extremal.delta_pos sourceFamily
      band.lemma31.data.cfg.line_class band.sourceConstant
      band.lemma31.data.cfg.top_level_cwa
  let width := pureWZ2AffineDiagonalConflictWidth scale
  have hwidthPos : 0 < width := by
    dsimp only [width, pureWZ2AffineDiagonalConflictWidth]
    exact mul_pos
      (mul_pos
        (mul_pos (by norm_num) (by linarith [scale.height_lower]))
        (by
          have hinvPos : 0 < scale.slopeData.transverseScale⁻¹ :=
            inv_pos.mpr scale.transverse_pos
          linarith))
      (mul_pos (by norm_num) scale.targetDelta_pos)
  have hsourceWidth : delta ≤ width := by
    have hinvNonneg : 0 ≤ scale.slopeData.transverseScale⁻¹ :=
      inv_nonneg.mpr scale.transverse_pos.le
    have hfactor : 1 ≤ 16 * (1 + scale.slopeData.heightScale) *
        (1 + scale.slopeData.transverseScale⁻¹) * 600 := by
      have hheightOne : 1 ≤ 1 + scale.slopeData.heightScale := by
        linarith [scale.height_lower]
      have hinvOne : 1 ≤ 1 + scale.slopeData.transverseScale⁻¹ := by
        linarith
      nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 16)
        (by linarith [scale.height_lower]),
        mul_nonneg
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16)
            (by linarith [scale.height_lower])) (by linarith)]
    calc
      delta ≤ scale.targetDelta := scale.source_le_target
      _ ≤ width := by
        dsimp only [width, pureWZ2AffineDiagonalConflictWidth]
        rw [show 16 * (1 + scale.slopeData.heightScale) *
            (1 + scale.slopeData.transverseScale⁻¹) *
              (600 * scale.targetDelta) =
            (16 * (1 + scale.slopeData.heightScale) *
              (1 + scale.slopeData.transverseScale⁻¹) * 600) *
                scale.targetDelta by ring]
        exact (le_mul_iff_one_le_left scale.targetDelta_pos).2 hfactor
  have hdegree : ∀ reference : Fin targetFamily.card,
      (((Finset.univ : Finset (Fin targetFamily.card)).filter
        (pureWZ2PaperCenteredConflict targetFamily reference)).card :
          ENNReal) ≤ pureWZ2AffineDiagonalConflictDegreeBound scale := by
    have h := affine_centered_conflict_degree_le
      scale.slopeData.frameSlope raw.center
      scale.slopeData.heightScale scale.slopeData.transverseScale
      scale.slopeData.frameSlope_bound
      (by
        have hcenterHeight : raw.center 2 = scale.slopeData.anchor := by
          rw [raw.center_eq]
          simp [pureWZ2AffineDiagonalCommonCenter, point3]
        rw [hcenterHeight]
        rw [abs_le]
        exact ⟨band.lemma31.data.scaleData.slabLeft_mem.trans
            (band.left_mem.trans <| subband.left_mem.trans
              scale.slope_anchor_mem.1),
          scale.slope_anchor_mem.2.trans <| subband.right_mem.trans <|
            band.right_mem.trans
            band.lemma31.data.scaleData.slabRight_mem⟩)
      scale.targetDelta_pos
      (by linarith [scale.height_lower]) scale.transverse_pos
      sourceFamily targetFamily sourceParent 1 hfiber
      band.lemma31.data.cfg.line_class raw.localized_line_class
      raw.localized_midpoint_le_three raw.localized_axis_ambient
      hsourceVertical htargetVertical (3200 * band.sourceConstant)
      sourceFamily.enncard hFrostman width rfl hsourceWidth hwidthOne
    intro reference
    simpa [pureWZ2AffineDiagonalConflictDegreeBound, width, sourceFamily,
      targetFamily, sourceParent] using h reference
  rcases pureWZ2_paper_weighted_centered_distinct_selection_ennreal
      targetFamily raw.localizedShading
      (pureWZ2AffineDiagonalConflictDegreeBound scale) hdegree with
    ⟨selected, hdistinct, hmaximal, hmass⟩
  exact ⟨{
    raw := raw
    conflict_width_le_one := hwidthOne
    selected := selected
    distinct := hdistinct
    maximal := hmaximal
    mass_lower := hmass
  }⟩

namespace PureWZ2AffineDiagonalSelectedLocalizedCleanupData

/-- The unique paper-facing family after centered cleanup.  This is the
localized ordinary representative itself; no midpoint-rebased coaxial family
is substituted into Definition 2.12. -/
def finalSubfamily
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) :
    Kakeya.Streamlined.TubeSubfamily data.raw.localizedFamily :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset
    data.raw.localizedFamily data.selected

def finalFamily
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) :
    Kakeya.Streamlined.TubeFamily scale.targetDelta :=
  { card := data.selected.card
    tube := fun index =>
      data.raw.localizedFamily.tube
        (data.selected.orderEmbOfFin rfl index) }

def finalShading
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) :
    WZ1PaperTubeShading data.finalFamily :=
  restrictPaperShading data.finalSubfamily data.raw.localizedShading

/-- The source tubes with exactly the same selected index type as the final
localized target family. -/
def finalSourceSubfamily
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) :
    Kakeya.Streamlined.TubeSubfamily regularized.selected.family :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset
    regularized.selected.family data.selected

theorem final_distinct
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) :
    WZ2PaperOrdinaryIsEssentiallyDistinct data.finalFamily := by
  exact data.distinct

theorem final_line_class
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) :
    WZ1PaperIsLineClass data.finalFamily := by
  exact data.raw.localized_line_class.subfamily data.finalSubfamily

theorem final_zeroBased
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized)
    (index : Fin data.finalFamily.card) :
    pureWZ2PaperZeroBasedTube (data.finalFamily.tube index) =
      data.finalFamily.tube index := by
  change pureWZ2PaperZeroBasedTube
      (data.raw.localizedFamily.tube
        (data.selected.orderEmbOfFin rfl index)) =
    data.raw.localizedFamily.tube
      (data.selected.orderEmbOfFin rfl index)
  exact data.raw.localized_zeroBased
    (data.selected.orderEmbOfFin rfl index)

theorem final_cubical
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) :
    WZ1PaperIsCubicalShading data.finalShading := by
  exact restrictPaperShading_cubical
    data.finalSubfamily data.raw.localized_cubical

theorem final_midpoint_le_three
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized)
    (index : Fin data.finalFamily.card) :
    ‖wz2PaperTubeMidpoint (data.finalFamily.tube index)‖ ≤ 3 := by
  change ‖wz2PaperTubeMidpoint
    (data.raw.localizedFamily.tube
      (data.selected.orderEmbOfFin rfl index))‖ ≤ 3
  exact data.raw.localized_midpoint_le_three
    (data.selected.orderEmbOfFin rfl index)

theorem final_nonempty
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) :
    data.finalFamily.Nonempty := by
  have hraw : data.raw.localizedFamily.Nonempty := by
    change 0 < regularized.selected.family.card
    exact regularized.selected_nonempty
  let index : Fin data.raw.localizedFamily.card :=
    ⟨0, by simpa [Kakeya.Streamlined.TubeFamily.Nonempty] using hraw⟩
  have hselected : data.selected.Nonempty := by
    rcases data.maximal index with hindex | ⟨representative, hrepresentative, _⟩
    · exact ⟨index, hindex⟩
    · exact ⟨representative, hrepresentative⟩
  change 0 < data.selected.card
  exact hselected.card_pos

theorem final_axis_ambient
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized)
    (index : Fin data.finalFamily.card) :
    tubeAxisLine (data.finalFamily.tube index) =
      pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope data.raw.center
        scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
          tubeAxisLine (band.lemma31.data.cfg.family.tube
            (regularized.selected.embedding
              (data.selected.orderEmbOfFin rfl index))) := by
  change tubeAxisLine
      (data.raw.localizedFamily.tube
        (data.selected.orderEmbOfFin rfl index)) = _
  exact data.raw.localized_axis_ambient
    (data.selected.orderEmbOfFin rfl index)

/-- The final localized target direction is the normalized affine image of
the positively oriented source direction. -/
theorem final_direction_source
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized)
    (index : Fin data.finalFamily.card) :
    (data.finalFamily.tube index).direction =
      pureWZ2AffineDiagonalDirection scale.slopeData.frameSlope
        scale.slopeData.heightScale scale.slopeData.transverseScale 1
          (wz1PaperDirection (data.finalSourceSubfamily.family.tube index)) := by
  change (pureWZ2PaperZeroBasedTube
      (pureWZ2AffineDiagonalRawTube scale.slopeData.frameSlope
        (pureWZ2AffineDiagonalCommonCenter popular
          (height := scale.slopeData.anchor))
        scale.slopeData.heightScale scale.slopeData.transverseScale 1
        (regularized.selected.family.tube
          (data.selected.orderEmbOfFin rfl index))
        (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
        scale.transverse_pos.ne' one_ne_zero)).direction = _
  change wz1PaperDirection
      (pureWZ2AffineDiagonalRawTube scale.slopeData.frameSlope
        (pureWZ2AffineDiagonalCommonCenter popular
          (height := scale.slopeData.anchor))
        scale.slopeData.heightScale scale.slopeData.transverseScale 1
        (regularized.selected.family.tube
          (data.selected.orderEmbOfFin rfl index))
        (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
        scale.transverse_pos.ne' one_ne_zero) = _
  change _ = pureWZ2AffineDiagonalDirection scale.slopeData.frameSlope
      scale.slopeData.heightScale scale.slopeData.transverseScale 1
        (wz1PaperDirection (regularized.selected.family.tube
          (data.selected.orderEmbOfFin rfl index)))
  exact wz1PaperDirection_affineDiagonalRawTube
      (targetDelta := scale.targetDelta) scale.slopeData.frameSlope
      (pureWZ2AffineDiagonalCommonCenter popular
        (height := scale.slopeData.anchor))
      (regularized.selected.family.tube
        (data.selected.orderEmbOfFin rfl index))
      (by linarith [scale.height_lower]) scale.transverse_pos.ne'
      (by norm_num)

/-- The literal popular-box weight survives both public regularization and
centered cleanup. -/
theorem final_mass_lower
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) :
    ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
        regularized.selectedWeight ≤
      (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
        data.finalShading.mass := by
  calc
    ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
          regularized.selectedWeight
        ≤ data.raw.shading.mass := data.raw.mass_lower
    _ = data.raw.localizedShading.mass :=
      data.raw.localizedShading_mass.symm
    _ ≤ (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
          data.finalShading.mass := data.mass_lower

theorem selectedWeightLevel_mul_sourceCard_le
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (_data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) :
    regularized.selectedWeightLevel * regularized.selected.family.enncard ≤
      regularized.selectedWeight := by
  rw [regularized.selectedWeight_eq]
  calc
    regularized.selectedWeightLevel * regularized.selected.family.enncard =
        ∑ _index : Fin regularized.selected.family.card,
          regularized.selectedWeightLevel := by
      simp [Kakeya.Streamlined.TubeFamily.enncard, Finset.sum_const]
      ring
    _ ≤ ∑ index : Fin regularized.selected.family.card,
        pureWZ2PopularSourceWeight popular
          (regularized.selected.embedding index) :=
      Finset.sum_le_sum fun index _ =>
        (regularized.selected_weight_band index).1

/-- Every final shaded carrier lies in the fixed crop box of volume eight. -/
theorem finalShading_mass_le_eight_mul_enncard
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) :
    data.finalShading.mass ≤ 8 * data.finalFamily.enncard := by
  calc
    data.finalShading.mass =
        ∑ index : Fin data.finalFamily.card,
          volume (data.finalShading.carrier index) := rfl
    _ ≤ ∑ _index : Fin data.finalFamily.card, (8 : ENNReal) := by
      apply Finset.sum_le_sum
      intro index _
      have hsubset : data.finalShading.carrier index ⊆
          Kakeya.Streamlined.axisBox 2 2 2 := by
        intro point hpoint
        exact (data.finalShading.subset_body index hpoint).2
      calc
        volume (data.finalShading.carrier index) ≤
            volume (Kakeya.Streamlined.axisBox 2 2 2) :=
          measure_mono hsubset
        _ = 8 := by
          rw [Kakeya.Streamlined.volume_axisBox 2 2 2] <;> norm_num
    _ = 8 * data.finalFamily.enncard := by
      simp [Kakeya.Streamlined.TubeFamily.enncard, Finset.sum_const]
      ring

/-- Honest normalization loss from the ambient Node-5 family to the final
localized cleanup.  It combines public nearby regularization, the positive
external-weight band, and centered cleanup; no unweighted subfamily transfer
is used. -/
theorem ambient_weighted_cardinality_retention
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) :
    (ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
        regularized.selectedWeightLevel *
        pureWZ2PopularSourceNormalization (band := band)) *
        band.lemma31.data.cfg.family.enncard ≤
      (regularized.retentionConstant *
        (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) * 8) *
          data.finalFamily.enncard := by
  have hsource : regularized.selectedWeightLevel *
        regularized.selected.family.enncard ≤
      regularized.selectedWeight :=
    data.selectedWeightLevel_mul_sourceCard_le
  have hcleanup : ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
        regularized.selectedWeight ≤
      (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
        data.finalShading.mass :=
    data.final_mass_lower
  have hfinalUpper := data.finalShading_mass_le_eight_mul_enncard
  calc
    (ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
          regularized.selectedWeightLevel *
          pureWZ2PopularSourceNormalization (band := band)) *
        band.lemma31.data.cfg.family.enncard =
      (ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
          regularized.selectedWeightLevel) *
        (pureWZ2PopularSourceNormalization (band := band) *
          band.lemma31.data.cfg.family.enncard) := by ring
    _ ≤ (ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
          regularized.selectedWeightLevel) *
        (regularized.retentionConstant *
          regularized.selected.family.enncard) := by
      exact mul_le_mul_left' regularized.cardinality_retention _
    _ = regularized.retentionConstant *
        (ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
          (regularized.selectedWeightLevel *
            regularized.selected.family.enncard)) := by ring
    _ ≤ regularized.retentionConstant *
        (ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
          regularized.selectedWeight) := by gcongr
    _ ≤ regularized.retentionConstant *
        ((pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
          data.finalShading.mass) := by gcongr
    _ ≤ regularized.retentionConstant *
        ((pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
          (8 * data.finalFamily.enncard)) := by gcongr
    _ = (regularized.retentionConstant *
          (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) * 8) *
        data.finalFamily.enncard := by ring

end PureWZ2AffineDiagonalSelectedLocalizedCleanupData

end Kakeya.Assouad

end
