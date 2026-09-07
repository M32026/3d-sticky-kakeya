import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalSelectedLocalizedCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalTopLevelCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PureExternalWeightRegularization

/-!
# Public nearby CWA after the centered affine cleanup

The centered cleanup is geometrically necessary, but an arbitrary tube
subfamily does not inherit Assouad's nearby-scale CWA.  This module runs the
already closed finite public regularization a second time, using the cleanup
indicator as an external weight.  Positive selected weight then forces every
new source tube to belong to the centered cleanup.

The output also records the synchronized target subfamily.  Source and target
indices are literally the same; only their tube data differ by the fixed
horizontal rotation and diagonal dilation.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Fixed cardinality loss which pays for the centered conflict cleanup. -/
def pureWZ2AffineDiagonalCleanupIndicatorUpper
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (scale : PureWZ2AffineDiagonalScaleData subband) : ENNReal :=
  (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) * 8

/-- Positive normalization retained before the centered cleanup. -/
def pureWZ2AffineDiagonalCleanupNormalization
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (scale : PureWZ2AffineDiagonalScaleData subband)
    (regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount) : ENNReal :=
  ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
    regularized.selectedWeightLevel

/-- The exact source index underlying one paper-facing final target tube. -/
def PureWZ2AffineDiagonalSelectedLocalizedCleanupData.finalTargetSourceIndex
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) :
    Fin cleanup.finalFamily.card ↪
      Fin regularized.selected.family.card where
  toFun target := cleanup.selected.orderEmbOfFin rfl target
  inj' := (cleanup.selected.orderEmbOfFin rfl).injective

/-- Target shaded mass attached to one ambient selected-source index.  The
sum is written over the cleanup target indices, so it is definitionally zero
off the cleanup image and has at most one nonzero summand on that image. -/
def pureWZ2AffineDiagonalCleanupIndicator
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized)
    (index : Fin regularized.selected.family.card) : ENNReal :=
  ∑ target : Fin cleanup.finalFamily.card,
    if cleanup.finalTargetSourceIndex target = index then
      (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
        MeasureTheory.volume (cleanup.finalShading.carrier target)
    else 0

theorem PureWZ2AffineDiagonalSelectedLocalizedCleanupData.cleanup_source_cardinality_retention
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) :
    pureWZ2AffineDiagonalCleanupNormalization scale regularized *
        regularized.selected.family.enncard ≤
      pureWZ2AffineDiagonalCleanupIndicatorUpper scale *
        cleanup.finalFamily.enncard := by
  have hsource := cleanup.selectedWeightLevel_mul_sourceCard_le
  have hcleanup := cleanup.final_mass_lower
  have htarget := cleanup.finalShading_mass_le_eight_mul_enncard
  calc
    pureWZ2AffineDiagonalCleanupNormalization scale regularized *
          regularized.selected.family.enncard =
        ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
          (regularized.selectedWeightLevel *
            regularized.selected.family.enncard) := by
      simp [pureWZ2AffineDiagonalCleanupNormalization]
      ring
    _ ≤ ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
          regularized.selectedWeight := by gcongr
    _ ≤ (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
          cleanup.finalShading.mass := hcleanup
    _ ≤ (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
          (8 * cleanup.finalFamily.enncard) := by gcongr
    _ = pureWZ2AffineDiagonalCleanupIndicatorUpper scale *
          cleanup.finalFamily.enncard := by
      simp [pureWZ2AffineDiagonalCleanupIndicatorUpper]
      ring

/-- The exact external-weight mass inequality consumed by the second public
regularization. -/
theorem PureWZ2AffineDiagonalSelectedLocalizedCleanupData.cleanup_indicator_mass
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) :
    pureWZ2AffineDiagonalCleanupNormalization scale regularized *
        regularized.selected.family.enncard ≤
      ∑ index : Fin regularized.selected.family.card,
        pureWZ2AffineDiagonalCleanupIndicator cleanup index := by
  have hsource := cleanup.selectedWeightLevel_mul_sourceCard_le
  have hcleanup := cleanup.final_mass_lower
  have hsum :
      (∑ index : Fin regularized.selected.family.card,
          pureWZ2AffineDiagonalCleanupIndicator cleanup index) =
        (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
          cleanup.finalShading.mass := by
    unfold pureWZ2AffineDiagonalCleanupIndicator
    rw [Finset.sum_comm]
    change
      (∑ target : Fin cleanup.finalFamily.card,
        ∑ index : Fin regularized.selected.family.card,
          if cleanup.finalTargetSourceIndex target = index then
            (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
              MeasureTheory.volume
                (cleanup.finalShading.carrier target) else 0) = _
    change _ = (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
      ∑ target : Fin cleanup.finalFamily.card,
        MeasureTheory.volume (cleanup.finalShading.carrier target)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro target _
    rw [Fintype.sum_ite_eq]
  calc
    pureWZ2AffineDiagonalCleanupNormalization scale regularized *
          regularized.selected.family.enncard =
        ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
          (regularized.selectedWeightLevel *
            regularized.selected.family.enncard) := by
      simp [pureWZ2AffineDiagonalCleanupNormalization]
      ring
    _ ≤ ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
          regularized.selectedWeight := by gcongr
    _ ≤ (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
          cleanup.finalShading.mass := hcleanup
    _ = ∑ index : Fin regularized.selected.family.card,
          pureWZ2AffineDiagonalCleanupIndicator cleanup index := hsum.symm

/-- Source-side public regularization supported entirely inside the centered
cleanup. -/
abbrev PureWZ2AffineDiagonalCleanupSourceRegularizationData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized)
    (outputConstant : ENNReal) (outputLevelCount : ℕ) :=
  PureWZ2ExternalWeightRegularizationData
    regularized.outputConstant outputConstant
      (pureWZ2AffineDiagonalCleanupNormalization scale regularized)
      (pureWZ2AffineDiagonalCleanupIndicatorUpper scale)
      outputLevelCount
      (pureWZ2AffineDiagonalCleanupIndicator cleanup)

theorem pureWZ2_affineDiagonal_cleanup_source_reregularization
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized)
    (outputConstant : ENNReal)
    (houtputFinite : WZ2PaperFiniteErrorConstant outputConstant)
    (outputLevelCount : ℕ)
    (hambientTwo : 2 < regularized.outputConstant)
    (hlevels : ENNReal.ofReal (1 / delta) ≤
      regularized.outputConstant ^ outputLevelCount)
    (houtput : regularized.outputConstant * regularized.outputConstant ≤
      outputConstant) :
    Nonempty (PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount) := by
  have hnormalizationZero :
      pureWZ2AffineDiagonalCleanupNormalization scale regularized ≠ 0 := by
    exact (ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr scale.slopeData.rotatedSlopeScale_pos).ne'
      regularized.selectedWeightLevel_pos.ne').ne'
  have hnormalizationTop :
      pureWZ2AffineDiagonalCleanupNormalization scale regularized ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      regularized.selectedWeightLevel_ne_top
  have hconflictTop :
      pureWZ2AffineDiagonalConflictDegreeBound scale ≠ ⊤ := by
    have hsourceConstantTop : band.sourceConstant ≠ ⊤ := by
      simp [PureWZ2Lemma32DerivativeBandAssembly.sourceConstant,
        Kakeya.realRpowENN]
    unfold pureWZ2AffineDiagonalConflictDegreeBound
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num)
          hsourceConstantTop)
        (by simp [Kakeya.realRpowENN]))
      (by simp [Kakeya.Streamlined.TubeFamily.enncard])
  have hweightUpperTop :
      pureWZ2AffineDiagonalCleanupIndicatorUpper scale ≠ ⊤ := by
    unfold pureWZ2AffineDiagonalCleanupIndicatorUpper
    exact ENNReal.mul_ne_top
      (ENNReal.add_ne_top.mpr ⟨hconflictTop, by norm_num⟩)
      (by norm_num)
  exact pureWZ2_external_weight_regularization
    (ambientCWA := regularized.cwa_nearby)
    (hfamily := regularized.selected_nonempty)
    (hdeltaOne := band.lemma31.data.cfg.extremal.delta_le_one)
    (hscheduleFinite := houtputFinite)
    (hnormalizationZero := hnormalizationZero)
    (hnormalizationTop := hnormalizationTop)
    (hweightUpperTop := hweightUpperTop)
    (externalWeight := pureWZ2AffineDiagonalCleanupIndicator cleanup)
    (hmass := cleanup.cleanup_indicator_mass)
    (hweight := by
      intro index
      unfold pureWZ2AffineDiagonalCleanupIndicator
      by_cases hexists : ∃ target : Fin cleanup.finalFamily.card,
          cleanup.finalTargetSourceIndex target = index
      · rcases hexists with ⟨target, htarget⟩
        have hunique : ∀ other : Fin cleanup.finalFamily.card,
            cleanup.finalTargetSourceIndex other = index →
              other = target := by
          intro other hother
          apply cleanup.finalTargetSourceIndex.injective
          exact hother.trans htarget.symm
        have hcondition : ∀ other : Fin cleanup.finalFamily.card,
            (cleanup.finalTargetSourceIndex other = index) ↔
              other = target := by
          intro other
          constructor
          · exact hunique other
          · intro heq
            rw [heq]
            exact htarget
        calc
          (∑ other, if cleanup.finalTargetSourceIndex other = index
              then (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
                MeasureTheory.volume
                  (cleanup.finalShading.carrier other) else 0) =
              (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
                MeasureTheory.volume
                  (cleanup.finalShading.carrier target) := by
            simp_rw [hcondition]
            rw [Fintype.sum_ite_eq']
          _ ≤ (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) * 8 := by
            gcongr
            have hsubset : cleanup.finalShading.carrier target ⊆
                Kakeya.Streamlined.axisBox 2 2 2 := by
              intro point hpoint
              exact (cleanup.finalShading.subset_body target hpoint).2
            calc
              MeasureTheory.volume (cleanup.finalShading.carrier target) ≤
                  MeasureTheory.volume
                    (Kakeya.Streamlined.axisBox 2 2 2) :=
                MeasureTheory.measure_mono hsubset
              _ = 8 := by
                rw [Kakeya.Streamlined.volume_axisBox 2 2 2] <;> norm_num
          _ = pureWZ2AffineDiagonalCleanupIndicatorUpper scale := by
            simp [pureWZ2AffineDiagonalCleanupIndicatorUpper]
      · change
          (∑ target : Fin cleanup.finalFamily.card,
            if cleanup.finalTargetSourceIndex target = index then
              (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
                MeasureTheory.volume (cleanup.finalShading.carrier target)
            else 0) ≤ _
        have hnone : ∀ target : Fin cleanup.finalFamily.card,
            cleanup.finalTargetSourceIndex target ≠ index := by
          intro target heq
          exact hexists ⟨target, heq⟩
        rw [show
          (∑ target : Fin cleanup.finalFamily.card,
            if cleanup.finalTargetSourceIndex target = index then
              (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
                MeasureTheory.volume (cleanup.finalShading.carrier target)
            else 0) = 0 by
              apply Finset.sum_eq_zero
              intro target _
              rw [if_neg (hnone target)]]
        exact bot_le)
    (levelCount := outputLevelCount)
    (hambientTwo := hambientTwo)
    (hlevels := hlevels)
    (hscheduleConstant := houtput)

namespace PureWZ2ExternalWeightRegularizationData

/-- Every tube selected by the second regularization lies in the centered
cleanup. -/
theorem cleanup_support
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
    data.selected.embedding index ∈
      Finset.univ.map cleanup.finalTargetSourceIndex := by
  have hpositive := data.selected_weight_pos index
  unfold pureWZ2AffineDiagonalCleanupIndicator at hpositive
  by_contra hnot
  have hnone : ¬∃ target : Fin cleanup.finalFamily.card,
      cleanup.finalTargetSourceIndex target =
        data.selected.embedding index := by
    intro hexists
    rcases hexists with ⟨target, htarget⟩
    exact hnot (Finset.mem_map.mpr
      ⟨target, Finset.mem_univ _, htarget⟩)
  have hzero :
      (∑ target : Fin cleanup.finalFamily.card,
        if cleanup.finalTargetSourceIndex target =
            data.selected.embedding index then
          (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
            MeasureTheory.volume (cleanup.finalShading.carrier target)
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro target _
    rw [if_neg (fun heq => hnone ⟨target, heq⟩)]
  rw [hzero] at hpositive
  exact (lt_irrefl 0 hpositive).elim

/-- The unique cleanup-source index underlying one twice-regularized source
index. -/
def cleanupSourcePreimage
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
    Fin cleanup.finalFamily.card :=
  (Finset.mem_map.mp
    (cleanup_support (cleanup := cleanup) data index)).choose

theorem cleanupSourcePreimage_ambient
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
    cleanup.finalTargetSourceIndex
        (cleanupSourcePreimage (cleanup := cleanup) data index) =
      data.selected.embedding index :=
  (Finset.mem_map.mp
    (cleanup_support (cleanup := cleanup) data index)).choose_spec.2

/-- The index embedding from the twice-regularized source family into the
paper-facing final affine family. -/
def cleanupTargetEmbedding
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
    Fin data.selected.family.card ↪ Fin cleanup.finalFamily.card where
  toFun index :=
    let sourceIndex :=
      cleanupSourcePreimage (cleanup := cleanup) data index
    ⟨sourceIndex.val, by
      change sourceIndex.val < cleanup.selected.card
      exact sourceIndex.isLt⟩
  inj' := by
    intro first second heq
    apply data.selected.embedding.injective
    rw [← cleanupSourcePreimage_ambient (cleanup := cleanup) data first,
      ← cleanupSourcePreimage_ambient (cleanup := cleanup) data second]
    have hpre :
        cleanupSourcePreimage (cleanup := cleanup) data first =
          cleanupSourcePreimage (cleanup := cleanup) data second := by
      apply Fin.ext
      exact congrArg Fin.val heq
    rw [hpre]

/-- The synchronized target family after the second source regularization. -/
def cleanupTargetSubfamily
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
    Kakeya.Streamlined.TubeSubfamily cleanup.finalFamily where
  family :=
    { card := data.selected.family.card
      tube := fun index =>
        cleanup.finalFamily.tube
          (cleanupTargetEmbedding (cleanup := cleanup) data index) }
  embedding := cleanupTargetEmbedding (cleanup := cleanup) data
  tube_eq _ := rfl

/-- Literal target shading synchronized with the twice-regularized source
family. -/
def cleanupTargetShading
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
      (cleanupTargetSubfamily (cleanup := cleanup) data).family :=
  restrictPaperShading
    (cleanupTargetSubfamily (cleanup := cleanup) data)
    cleanup.finalShading

@[simp] theorem cleanupTargetEmbedding_eq_preimage
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
    cleanupTargetEmbedding (cleanup := cleanup) data index =
      cleanupSourcePreimage (cleanup := cleanup) data index := by
  apply Fin.ext
  rfl

theorem cleanupTargetShading_cubical
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
    WZ1PaperIsCubicalShading
      (cleanupTargetShading (cleanup := cleanup) data) :=
  restrictPaperShading_cubical
    (cleanupTargetSubfamily (cleanup := cleanup) data)
    cleanup.final_cubical

theorem cleanupTarget_line_class
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
    WZ1PaperIsLineClass
      (cleanupTargetSubfamily (cleanup := cleanup) data).family :=
  cleanup.final_line_class.subfamily
    (cleanupTargetSubfamily (cleanup := cleanup) data)

theorem cleanupTarget_distinct
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
    WZ2PaperOrdinaryIsEssentiallyDistinct
      (cleanupTargetSubfamily (cleanup := cleanup) data).family := by
  let selected : WZ2PaperPureTubeSubfamily cleanup.finalFamily :=
    { family := (cleanupTargetSubfamily (cleanup := cleanup) data).family
      embedding :=
        (cleanupTargetSubfamily (cleanup := cleanup) data).embedding
      tube_eq :=
        (cleanupTargetSubfamily (cleanup := cleanup) data).tube_eq }
  exact cleanup.final_distinct.subfamily selected

/-- The zero-based public ordinary model makes centered distinctness strong
enough for the paper line-distance packing lemmas. -/
theorem cleanupTarget_paper_essentially_distinct
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
    WZ1PaperIsEssentiallyDistinct
      (cleanupTargetSubfamily (cleanup := cleanup) data).family := by
  apply pureWZ2_zeroBased_ordinaryDistinct_implies_paperDistinct
    scale.targetDelta_pos
    (cleanupTarget_line_class (cleanup := cleanup) data)
  intro first second hne
  have hfirst :
      pureWZ2PaperZeroBasedTube
          ((cleanupTargetSubfamily (cleanup := cleanup) data).family.tube first) =
        (cleanupTargetSubfamily (cleanup := cleanup) data).family.tube first := by
    change pureWZ2PaperZeroBasedTube
        (cleanup.finalFamily.tube
          (cleanupTargetEmbedding (cleanup := cleanup) data first)) =
      cleanup.finalFamily.tube
        (cleanupTargetEmbedding (cleanup := cleanup) data first)
    exact cleanup.final_zeroBased
      (cleanupTargetEmbedding (cleanup := cleanup) data first)
  have hsecond :
      pureWZ2PaperZeroBasedTube
          ((cleanupTargetSubfamily (cleanup := cleanup) data).family.tube second) =
        (cleanupTargetSubfamily (cleanup := cleanup) data).family.tube second := by
    change pureWZ2PaperZeroBasedTube
        (cleanup.finalFamily.tube
          (cleanupTargetEmbedding (cleanup := cleanup) data second)) =
      cleanup.finalFamily.tube
        (cleanupTargetEmbedding (cleanup := cleanup) data second)
    exact cleanup.final_zeroBased
      (cleanupTargetEmbedding (cleanup := cleanup) data second)
  simpa only [pureWZ2PaperZeroBasedFamily, hfirst, hsecond] using
    cleanupTarget_distinct (cleanup := cleanup) data first second hne

/-- The second public regularization retains genuine target shaded mass, not
just indexed cardinality. -/
theorem cleanupTarget_mass_retention
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
    (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
        cleanup.finalShading.mass ≤
      data.regularizationLoss *
        (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
          (cleanupTargetShading (cleanup := cleanup) data).mass := by
  have hretained := data.retained_weight
  have hambient :
      (∑ index : Fin regularized.selected.family.card,
          pureWZ2AffineDiagonalCleanupIndicator cleanup index) =
        (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
          cleanup.finalShading.mass := by
    unfold pureWZ2AffineDiagonalCleanupIndicator
    rw [Finset.sum_comm]
    change
      (∑ target : Fin cleanup.finalFamily.card,
        ∑ index : Fin regularized.selected.family.card,
          if cleanup.finalTargetSourceIndex target = index then
            (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
              MeasureTheory.volume
                (cleanup.finalShading.carrier target) else 0) = _
    change _ = (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
      ∑ target : Fin cleanup.finalFamily.card,
        MeasureTheory.volume (cleanup.finalShading.carrier target)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro target _
    rw [Fintype.sum_ite_eq]
  have hselected :
      (∑ index : Fin data.selected.family.card,
          pureWZ2AffineDiagonalCleanupIndicator cleanup
            (data.selected.embedding index)) =
        (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
          (cleanupTargetShading (cleanup := cleanup) data).mass := by
    unfold cleanupTargetShading
    rw [restrictPaperShading_mass]
    change
      (∑ index : Fin data.selected.family.card,
          pureWZ2AffineDiagonalCleanupIndicator cleanup
            (data.selected.embedding index)) =
        (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) *
          ∑ index : Fin data.selected.family.card,
            MeasureTheory.volume
              (cleanup.finalShading.carrier
                (cleanupTargetEmbedding (cleanup := cleanup) data index))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    unfold pureWZ2AffineDiagonalCleanupIndicator
    let target := cleanupSourcePreimage (cleanup := cleanup) data index
    have htarget := cleanupSourcePreimage_ambient
      (cleanup := cleanup) data index
    have hunique : ∀ other : Fin cleanup.finalFamily.card,
        cleanup.finalTargetSourceIndex other = data.selected.embedding index ↔
          other = target := by
      intro other
      constructor
      · intro hother
        apply cleanup.finalTargetSourceIndex.injective
        exact hother.trans htarget.symm
      · rintro rfl
        exact htarget
    simp_rw [hunique]
    rw [Fintype.sum_ite_eq']
    rw [cleanupTargetEmbedding_eq_preimage]
  rw [data.selectedWeight_eq] at hretained
  rw [hambient, hselected] at hretained
  simpa [mul_assoc] using hretained

theorem cleanupTarget_axis_source
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
    tubeAxisLine
        ((cleanupTargetSubfamily (cleanup := cleanup) data).family.tube index) =
      pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope
          cleanup.raw.center scale.slopeData.heightScale
            scale.slopeData.transverseScale 1 ''
        tubeAxisLine (data.selected.family.tube index) := by
  change tubeAxisLine
      (cleanup.finalFamily.tube
        (cleanupTargetEmbedding (cleanup := cleanup) data index)) = _
  rw [cleanup.final_axis_ambient
      (cleanupTargetEmbedding (cleanup := cleanup) data index)]
  rw [data.selected.tube_eq index, regularized.selected.tube_eq]
  congr 3
  exact congrArg regularized.selected.embedding <| by
    change cleanup.finalTargetSourceIndex
        (cleanupSourcePreimage (cleanup := cleanup) data index) =
      data.selected.embedding index
    exact cleanupSourcePreimage_ambient (cleanup := cleanup) data index

/-- The normalized top-level cropped CWA survives the second source
regularization by its explicit weighted cardinality retention. -/
theorem cleanupTarget_top_level_cwa
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
    WZ2PaperConvexWolffBound
      (cleanupTargetSubfamily (cleanup := cleanup) data).family
      ((pureWZ2AffineDiagonalCleanupNormalization scale regularized)⁻¹ *
        data.retentionConstant *
          (cleanup.finalTopLevelAffineLoss *
            ((cleanup.finalTopLevelSourceWeight⁻¹ *
              cleanup.finalTopLevelCardinalityLoss) *
                band.sourceConstant))) := by
  let weight := pureWZ2AffineDiagonalCleanupNormalization scale regularized
  have hweightZero : weight ≠ 0 := by
    exact (ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr scale.slopeData.rotatedSlopeScale_pos).ne'
      regularized.selectedWeightLevel_pos.ne').ne'
  have hweightTop : weight ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      regularized.selectedWeightLevel_ne_top
  have hfinalCard : cleanup.finalFamily.enncard ≤
      regularized.selected.family.enncard := by
    change (cleanup.finalFamily.card : ENNReal) ≤
      (regularized.selected.family.card : ENNReal)
    have hnat : cleanup.finalFamily.card ≤
        regularized.selected.family.card := by
      simpa [Fintype.card_fin] using
        Fintype.card_le_of_injective cleanup.finalTargetSourceIndex
          cleanup.finalTargetSourceIndex.injective
    exact_mod_cast hnat
  have hcard : weight * cleanup.finalFamily.enncard ≤
      data.retentionConstant * data.selected.family.enncard := by
    calc
      weight * cleanup.finalFamily.enncard ≤
          weight * regularized.selected.family.enncard := by gcongr
      _ ≤ data.retentionConstant * data.selected.family.enncard :=
        data.cardinality_retention
  have hraw := cleanup.final_top_level_cwa.subfamily_of_weighted_cardinality
    (cleanupTargetSubfamily (cleanup := cleanup) data)
    hweightZero hweightTop hcard
  simpa [weight, mul_assoc] using hraw

end PureWZ2ExternalWeightRegularizationData

end Kakeya.Assouad

end
