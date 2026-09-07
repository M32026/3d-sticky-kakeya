import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicPaperCenteredCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PureExternalWeightRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalizedRelabelParent

/-!
# Source-side nearby regularization after triangular centered cleanup

An arbitrary target subfamily does not inherit nearby-scale CWA.  After the
public centered cleanup, we therefore put the retained target shaded mass
back on its unique source indices and run the closed source-side public
regularization once more.  Positive selected weight synchronizes the new
source family with a genuine subfamily of the cleaned triangular target.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

def anisotropicPaperCleanupIndicatorUpper
    {sourceDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceConstant : ENNReal) (targetDelta c d m : ℝ) : ENNReal :=
  (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
      targetDelta c d m + 1) * 8

/-- Sharp per-source cleanup weight bound at the genuine target tube scale. -/
def anisotropicPaperCleanupIndicatorQuadraticUpper
    {sourceDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceConstant : ENNReal) (targetDelta c d m : ℝ) : ENNReal :=
  (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
      targetDelta c d m + 1) *
    ((55296 * Kakeya.deltaTubeVolume 1) *
      Kakeya.realRpowENN targetDelta 2)

def anisotropicPaperCleanupNormalization
    (m : ℝ) (sourceNormalization : ENNReal) : ENNReal :=
  ENNReal.ofReal m * sourceNormalization

/-- Target shaded mass, extended by zero to every source index. -/
def anisotropicPaperCleanupIndicator
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant : ENNReal}
    (cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant)
    (source : Fin sourceFamily.card) : ENNReal :=
  ∑ target : Fin cleanup.family.card,
    if cleanup.sourceIndex target = source then
      (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
          targetDelta c d m + 1) *
        MeasureTheory.volume (cleanup.shading.carrier target)
    else 0

theorem PureWZ2AnisotropicPaperCenteredCleanupData.indicator_mass
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNormalization : ENNReal}
    (cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant)
    (hsourceMass : sourceNormalization * sourceFamily.enncard ≤
      sourceShading.mass) :
    anisotropicPaperCleanupNormalization m sourceNormalization *
        sourceFamily.enncard ≤
      ∑ source : Fin sourceFamily.card,
        anisotropicPaperCleanupIndicator cleanup source := by
  have hsum :
      (∑ source : Fin sourceFamily.card,
          anisotropicPaperCleanupIndicator cleanup source) =
        (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
            targetDelta c d m + 1) * cleanup.shading.mass := by
    unfold anisotropicPaperCleanupIndicator
    rw [Finset.sum_comm]
    change
      (∑ target : Fin cleanup.family.card,
        ∑ source : Fin sourceFamily.card,
          if cleanup.sourceIndex target = source then
            (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
                targetDelta c d m + 1) *
              MeasureTheory.volume (cleanup.shading.carrier target)
          else 0) = _
    change _ =
      (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
          targetDelta c d m + 1) *
        ∑ target : Fin cleanup.family.card,
          MeasureTheory.volume (cleanup.shading.carrier target)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro target _
    rw [Fintype.sum_ite_eq]
  calc
    anisotropicPaperCleanupNormalization m sourceNormalization *
          sourceFamily.enncard =
        ENNReal.ofReal m *
          (sourceNormalization * sourceFamily.enncard) := by
      simp [anisotropicPaperCleanupNormalization]
      ring
    _ ≤ ENNReal.ofReal m * sourceShading.mass := by gcongr
    _ ≤ raw.shading.mass := raw.mass_lower
    _ ≤ (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
          targetDelta c d m + 1) * cleanup.shading.mass :=
      cleanup.raw_mass_le
    _ = ∑ source : Fin sourceFamily.card,
          anisotropicPaperCleanupIndicator cleanup source := hsum.symm

theorem PureWZ2AnisotropicPaperCenteredCleanupData.indicator_le
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant : ENNReal}
    (cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant)
    (source : Fin sourceFamily.card) :
    anisotropicPaperCleanupIndicator cleanup source ≤
      anisotropicPaperCleanupIndicatorUpper sourceFamily sourceConstant
        targetDelta c d m := by
  unfold anisotropicPaperCleanupIndicator
  by_cases hexists : ∃ target : Fin cleanup.family.card,
      cleanup.sourceIndex target = source
  · rcases hexists with ⟨target, htarget⟩
    have hunique : ∀ other : Fin cleanup.family.card,
        cleanup.sourceIndex other = source → other = target := by
      intro other hother
      apply cleanup.sourceIndex_injective
      exact hother.trans htarget.symm
    have hcondition : ∀ other : Fin cleanup.family.card,
        cleanup.sourceIndex other = source ↔ other = target := by
      intro other
      constructor
      · exact hunique other
      · rintro rfl
        exact htarget
    simp_rw [hcondition]
    rw [Fintype.sum_ite_eq']
    unfold anisotropicPaperCleanupIndicatorUpper
    gcongr
    have hsubset : cleanup.shading.carrier target ⊆
        Kakeya.Streamlined.axisBox 2 2 2 := by
      intro point hpoint
      exact (cleanup.shading.subset_body target hpoint).2
    calc
      MeasureTheory.volume (cleanup.shading.carrier target) ≤
          MeasureTheory.volume (Kakeya.Streamlined.axisBox 2 2 2) :=
        MeasureTheory.measure_mono hsubset
      _ = 8 := by
        rw [Kakeya.Streamlined.volume_axisBox 2 2 2] <;> norm_num
  · have hnone : ∀ target : Fin cleanup.family.card,
        cleanup.sourceIndex target ≠ source := by
      intro target heq
      exact hexists ⟨target, heq⟩
    rw [show
      (∑ target : Fin cleanup.family.card,
        if cleanup.sourceIndex target = source then
          (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
              targetDelta c d m + 1) *
            MeasureTheory.volume (cleanup.shading.carrier target)
        else 0) = 0 by
          apply Finset.sum_eq_zero
          intro target _
          rw [if_neg (hnone target)]]
    exact bot_le

/-- Sharp version of `indicator_le` for a genuine paper target family.  It
keeps the quadratic target-scale volume factor instead of discarding it via
the ambient axis box. -/
theorem PureWZ2AnisotropicPaperCenteredCleanupData.indicator_le_quadratic
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant : ENNReal}
    (cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant)
    (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 24)
    (source : Fin sourceFamily.card) :
    anisotropicPaperCleanupIndicator cleanup source ≤
      (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
          targetDelta c d m + 1) *
        ((55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN targetDelta 2) := by
  unfold anisotropicPaperCleanupIndicator
  by_cases hexists : ∃ target : Fin cleanup.family.card,
      cleanup.sourceIndex target = source
  · rcases hexists with ⟨target, htarget⟩
    have hunique : ∀ other : Fin cleanup.family.card,
        cleanup.sourceIndex other = source → other = target := by
      intro other hother
      apply cleanup.sourceIndex_injective
      exact hother.trans htarget.symm
    have hcondition : ∀ other : Fin cleanup.family.card,
        cleanup.sourceIndex other = source ↔ other = target := by
      intro other
      exact ⟨hunique other, fun h => h ▸ htarget⟩
    simp_rw [hcondition]
    rw [Fintype.sum_ite_eq']
    gcongr
    exact (wz2PaperTubeCarrier_convex_and_volume_quadratic
      wz2_paper_tube_carrier_geometry htargetDelta htargetDeltaSmall
      (cleanup.family.tube target) (cleanup.line_class target)).2.trans'
        (MeasureTheory.measure_mono (cleanup.shading.subset_body target))
  · have hnone : ∀ target : Fin cleanup.family.card,
        cleanup.sourceIndex target ≠ source := by
      intro target heq
      exact hexists ⟨target, heq⟩
    rw [show
      (∑ target : Fin cleanup.family.card,
        if cleanup.sourceIndex target = source then
          (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
              targetDelta c d m + 1) *
            MeasureTheory.volume (cleanup.shading.carrier target)
        else 0) = 0 by
          apply Finset.sum_eq_zero
          intro target _
          rw [if_neg (hnone target)]]
    exact bot_le

theorem PureWZ2AnisotropicPaperCenteredCleanupData.indicator_le_quadraticUpper
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant : ENNReal}
    (cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant)
    (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 24)
    (source : Fin sourceFamily.card) :
    anisotropicPaperCleanupIndicator cleanup source ≤
      anisotropicPaperCleanupIndicatorQuadraticUpper sourceFamily
        sourceConstant targetDelta c d m := by
  exact cleanup.indicator_le_quadratic htargetDelta htargetDeltaSmall source

abbrev PureWZ2AnisotropicCleanupSourceRegularizationData
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant : ENNReal}
    (cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant)
    (sourceNearbyConstant outputConstant sourceNormalization : ENNReal)
    (levelCount : ℕ) :=
  PureWZ2ExternalWeightRegularizationData
    sourceNearbyConstant outputConstant
      (anisotropicPaperCleanupNormalization m sourceNormalization)
      (anisotropicPaperCleanupIndicatorQuadraticUpper sourceFamily sourceConstant
        targetDelta c d m)
      levelCount (anisotropicPaperCleanupIndicator cleanup)

theorem pureWZ2_anisotropic_cleanup_source_regularization
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    (cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant)
    (sourceCWA : WZ2PaperPureCWAAtNearbyScales
      sourceFamily sourceNearbyConstant)
    (hsourceNonempty : sourceFamily.Nonempty)
    (hsourceDeltaOne : sourceDelta ≤ 1)
    (hsourceMass : sourceNormalization * sourceFamily.enncard ≤
      sourceShading.mass)
    (hsourceNormalizationZero : sourceNormalization ≠ 0)
    (hsourceNormalizationTop : sourceNormalization ≠ ⊤)
    (hsourceConstantTop : sourceConstant ≠ ⊤)
    (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 24)
    (houtputFinite : WZ2PaperFiniteErrorConstant outputConstant)
    (levelCount : ℕ)
    (hsourceTwo : 2 < sourceNearbyConstant)
    (hlevels : ENNReal.ofReal (1 / sourceDelta) ≤
      sourceNearbyConstant ^ levelCount)
    (houtput : sourceNearbyConstant * sourceNearbyConstant ≤
      outputConstant) :
    Nonempty (PureWZ2AnisotropicCleanupSourceRegularizationData
      cleanup sourceNearbyConstant outputConstant sourceNormalization
        levelCount) := by
  have hnormalizationZero :
      anisotropicPaperCleanupNormalization m sourceNormalization ≠ 0 := by
    unfold anisotropicPaperCleanupNormalization
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr hm).ne'
      hsourceNormalizationZero
  have hnormalizationTop :
      anisotropicPaperCleanupNormalization m sourceNormalization ≠ ⊤ := by
    unfold anisotropicPaperCleanupNormalization
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      hsourceNormalizationTop
  have hweightUpperTop :
      anisotropicPaperCleanupIndicatorQuadraticUpper sourceFamily sourceConstant
          targetDelta c d m ≠ ⊤ := by
    unfold anisotropicPaperCleanupIndicatorQuadraticUpper
    apply ENNReal.mul_ne_top
    · apply ENNReal.add_ne_top.mpr
      refine ⟨?_, by norm_num⟩
      unfold anisotropicPaperConflictDegreeBound
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) <| by
          exact hsourceConstantTop) (by simp [Kakeya.realRpowENN]))
        (by simp [Kakeya.Streamlined.TubeFamily.enncard])
    · exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top)
        (by simp [Kakeya.realRpowENN])
  exact pureWZ2_external_weight_regularization sourceCWA
    hsourceNonempty hsourceDeltaOne houtputFinite
    hnormalizationZero hnormalizationTop hweightUpperTop
    (anisotropicPaperCleanupIndicator cleanup)
    (cleanup.indicator_mass hsourceMass)
    (cleanup.indicator_le_quadraticUpper htargetDelta htargetDeltaSmall)
    levelCount hsourceTwo hlevels houtput

namespace PureWZ2ExternalWeightRegularizationData

theorem anisotropic_cleanup_support
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount)
    (index : Fin data.selected.family.card) :
    data.selected.embedding index ∈
      Finset.univ.image cleanup.sourceIndex := by
  have hpositive := data.selected_weight_pos index
  unfold anisotropicPaperCleanupIndicator at hpositive
  by_contra hnot
  have hnone : ∀ target : Fin cleanup.family.card,
      cleanup.sourceIndex target ≠ data.selected.embedding index := by
    intro target heq
    exact hnot (Finset.mem_image.mpr
      ⟨target, Finset.mem_univ _, heq⟩)
  have hzero :
      (∑ target : Fin cleanup.family.card,
        if cleanup.sourceIndex target = data.selected.embedding index then
          (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
              targetDelta c d m + 1) *
            MeasureTheory.volume (cleanup.shading.carrier target)
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro target _
    rw [if_neg (hnone target)]
  rw [hzero] at hpositive
  exact (lt_irrefl 0 hpositive).elim

def anisotropicCleanupTargetPreimage
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount)
    (index : Fin data.selected.family.card) : Fin cleanup.family.card :=
  (Finset.mem_image.mp (anisotropic_cleanup_support data index)).choose

theorem anisotropicCleanupTargetPreimage_source
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount)
    (index : Fin data.selected.family.card) :
    cleanup.sourceIndex (anisotropicCleanupTargetPreimage data index) =
      data.selected.embedding index :=
  (Finset.mem_image.mp
    (anisotropic_cleanup_support data index)).choose_spec.2

def anisotropicCleanupTargetEmbedding
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount) :
    Fin data.selected.family.card ↪ Fin cleanup.family.card where
  toFun := anisotropicCleanupTargetPreimage data
  inj' := by
    intro first second heq
    apply data.selected.embedding.injective
    rw [← anisotropicCleanupTargetPreimage_source data first,
      ← anisotropicCleanupTargetPreimage_source data second, heq]

def anisotropicCleanupTargetSubfamily
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount) :
    Kakeya.Streamlined.TubeSubfamily cleanup.family where
  family :=
    { card := data.selected.family.card
      tube := fun index => cleanup.family.tube
        (anisotropicCleanupTargetEmbedding data index) }
  embedding := anisotropicCleanupTargetEmbedding data
  tube_eq _ := rfl

def anisotropicCleanupTargetShading
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount) :
    WZ1PaperTubeShading
      (anisotropicCleanupTargetSubfamily data).family :=
  restrictPaperShading (anisotropicCleanupTargetSubfamily data)
    cleanup.shading

@[simp] theorem anisotropicCleanupTargetShading_carrier
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount)
    (target : Fin data.selected.family.card) :
    (anisotropicCleanupTargetShading data).carrier target =
      raw.shading.carrier (data.selected.embedding target) := by
  change cleanup.shading.carrier
      (anisotropicCleanupTargetEmbedding data target) = _
  change cleanup.shading.carrier
      (anisotropicCleanupTargetPreimage data target) = _
  change raw.shading.carrier
      (cleanup.sourceIndex (anisotropicCleanupTargetPreimage data target)) = _
  rw [anisotropicCleanupTargetPreimage_source data target]

theorem anisotropicCleanupTarget_line_class
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount) :
    WZ1PaperIsLineClass (anisotropicCleanupTargetSubfamily data).family :=
  cleanup.line_class.subfamily (anisotropicCleanupTargetSubfamily data)

/-- Each synchronized cleanup target is literally the exact triangular tube
of the source with the same reindexed coordinate. -/
theorem anisotropicCleanupTarget_tube_eq
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount) :
    ∀ target,
      (anisotropicCleanupTargetSubfamily data).family.tube target =
        anisotropicPaperTargetTube g c d m center targetDelta hcd hm
          (data.selected.family.tube target) := by
  intro target
  change anisotropicPaperTargetTube g c d m center targetDelta hcd hm
      (sourceFamily.tube
        (cleanup.sourceIndex
          (anisotropicCleanupTargetPreimage data target))) = _
  rw [data.selected.tube_eq]
  exact congrArg
    (fun source => anisotropicPaperTargetTube g c d m center
      targetDelta hcd hm (sourceFamily.tube source))
    (anisotropicCleanupTargetPreimage_source data target)

theorem anisotropicCleanupTarget_cubical
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount) :
    WZ1PaperIsCubicalShading
      (anisotropicCleanupTargetShading data) :=
  restrictPaperShading_cubical
    (anisotropicCleanupTargetSubfamily data) cleanup.cubical

theorem anisotropicCleanupTarget_distinct
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount) :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      (anisotropicCleanupTargetSubfamily data).family := by
  let selected : WZ2PaperPureTubeSubfamily cleanup.family :=
    { family := (anisotropicCleanupTargetSubfamily data).family
      embedding := (anisotropicCleanupTargetSubfamily data).embedding
      tube_eq := (anisotropicCleanupTargetSubfamily data).tube_eq }
  exact cleanup.distinct.subfamily selected

theorem anisotropicCleanupTarget_nonempty
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount) :
    (anisotropicCleanupTargetSubfamily data).family.Nonempty := by
  change 0 < data.selected.family.card
  exact data.selected_nonempty

theorem anisotropicCleanupTarget_midpoint_local
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount)
    (index : Fin data.selected.family.card) :
    ‖wz2PaperTubeMidpoint
      ((anisotropicCleanupTargetSubfamily data).family.tube index)‖ ≤ 3 := by
  change ‖wz2PaperTubeMidpoint
    ((anisotropicPaperTargetFamily sourceFamily g c d m center targetDelta
      hcd hm).tube
        ((Kakeya.Streamlined.TubeSubfamily.fromFinset
          (anisotropicPaperTargetFamily sourceFamily g c d m center
            targetDelta hcd hm) cleanup.selected).embedding
          (anisotropicCleanupTargetEmbedding data index)))‖ ≤ 3
  exact raw.midpoint_local
    ((Kakeya.Streamlined.TubeSubfamily.fromFinset
      (anisotropicPaperTargetFamily sourceFamily g c d m center
        targetDelta hcd hm) cleanup.selected).embedding
      (anisotropicCleanupTargetEmbedding data index))

/-- The exact triangular target tubes are already in the canonical
midpoint-centered form used by the representative-parent construction. -/
theorem anisotropicCleanupTarget_centered
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount)
    (index : Fin data.selected.family.card) :
    pureWZ2PaperCenteredTube
        ((anisotropicCleanupTargetSubfamily data).family.tube index) =
      (anisotropicCleanupTargetSubfamily data).family.tube index := by
  let tube := (anisotropicCleanupTargetSubfamily data).family.tube index
  have hline : WZ1PaperTubeInLineClass tube :=
    data.anisotropicCleanupTarget_line_class index
  apply pureWZ2PaperCenteredTube_eq_self tube hline
  · apply le_of_lt
    change 0 <
      ((anisotropicPaperTargetFamily sourceFamily g c d m center targetDelta
        hcd hm).tube _).direction 2
    exact raw.direction_two_pos _
  · change wz2PaperTubeMidpoint tube 2 = 0
    change wz2PaperTubeMidpoint
        ((anisotropicPaperTargetFamily sourceFamily g c d m center
          targetDelta hcd hm).tube _) 2 = 0
    exact raw.midpoint_height_zero _

/-- Ordinary centered distinctness of the synchronized target family implies
paper line-distance distinctness for the canonical radius-`2 delta / 3`
packing representatives. -/
theorem anisotropicCleanupTarget_centeredPacking_paper_distinct
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount)
    (htargetDelta : 0 < targetDelta) :
    WZ1PaperIsEssentiallyDistinct
      (pureWZ2CenteredPackingFamily
        (anisotropicCleanupTargetSubfamily data).family) := by
  apply pureWZ2_centered_ordinaryDistinct_packingFamily_paperDistinct
    htargetDelta data.anisotropicCleanupTarget_line_class
  intro first second hne
  simpa only [data.anisotropicCleanupTarget_centered first,
    data.anisotropicCleanupTarget_centered second] using
      data.anisotropicCleanupTarget_distinct first second hne

/-- The second source regularization retains the actual cleaned target
shaded mass because its external weight is supported on the injective target
index map. -/
theorem anisotropicCleanupTarget_mass_retention
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount) :
    (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
        targetDelta c d m + 1) * cleanup.shading.mass ≤
      data.regularizationLoss *
        (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
          targetDelta c d m + 1) *
          (anisotropicCleanupTargetShading data).mass := by
  have hretained := data.retained_weight
  have hambient :
      (∑ source : Fin sourceFamily.card,
          anisotropicPaperCleanupIndicator cleanup source) =
        (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
            targetDelta c d m + 1) * cleanup.shading.mass := by
    unfold anisotropicPaperCleanupIndicator
    rw [Finset.sum_comm]
    change
      (∑ target : Fin cleanup.family.card,
        ∑ source : Fin sourceFamily.card,
          if cleanup.sourceIndex target = source then
            (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
                targetDelta c d m + 1) *
              MeasureTheory.volume (cleanup.shading.carrier target)
          else 0) = _
    change _ =
      (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
          targetDelta c d m + 1) *
        ∑ target : Fin cleanup.family.card,
          MeasureTheory.volume (cleanup.shading.carrier target)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro target _
    rw [Fintype.sum_ite_eq]
  have hselected :
      (∑ index : Fin data.selected.family.card,
          anisotropicPaperCleanupIndicator cleanup
            (data.selected.embedding index)) =
        (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
            targetDelta c d m + 1) *
          (anisotropicCleanupTargetShading data).mass := by
    unfold anisotropicCleanupTargetShading
    rw [restrictPaperShading_mass]
    change
      (∑ index : Fin data.selected.family.card,
          anisotropicPaperCleanupIndicator cleanup
            (data.selected.embedding index)) =
        (anisotropicPaperConflictDegreeBound sourceFamily sourceConstant
            targetDelta c d m + 1) *
          ∑ index : Fin data.selected.family.card,
            MeasureTheory.volume
              (cleanup.shading.carrier
                (anisotropicCleanupTargetEmbedding data index))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    unfold anisotropicPaperCleanupIndicator
    let target := anisotropicCleanupTargetPreimage data index
    have htarget := anisotropicCleanupTargetPreimage_source data index
    have hunique : ∀ other : Fin cleanup.family.card,
        cleanup.sourceIndex other = data.selected.embedding index ↔
          other = target := by
      intro other
      constructor
      · intro hother
        apply cleanup.sourceIndex_injective
        exact hother.trans htarget.symm
      · rintro rfl
        exact htarget
    simp_rw [hunique]
    rw [Fintype.sum_ite_eq']
    rfl
  rw [data.selectedWeight_eq] at hretained
  rw [hambient, hselected] at hretained
  simpa [mul_assoc] using hretained

/-- The synchronized target still has the exact centered triangular source
line for each of its indices. -/
theorem anisotropicCleanupTarget_axis_source
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw sourceConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount)
    (index : Fin data.selected.family.card) :
    tubeAxisLine ((anisotropicCleanupTargetSubfamily data).family.tube index) =
      anisotropicCenteredRescalingMap g c d m center ''
        tubeAxisLine (data.selected.family.tube index) := by
  change tubeAxisLine
      (cleanup.family.tube (anisotropicCleanupTargetEmbedding data index)) = _
  rw [cleanup.axis_source (anisotropicCleanupTargetEmbedding data index)]
  rw [data.selected.tube_eq]
  congr 3
  exact anisotropicCleanupTargetPreimage_source data index

/-- The source re-regularization keeps enough indexed mass to provide a
cardinality normalization for the later joint quotient selection. -/
theorem selectedWeightLevel_mul_sourceCard_le
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {cleanupConstant sourceNearbyConstant outputConstant
      sourceNormalization : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      raw cleanupConstant}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      sourceNearbyConstant outputConstant sourceNormalization levelCount) :
    data.selectedWeightLevel * data.selected.family.enncard ≤
      data.selectedWeight := by
  rw [data.selectedWeight_eq]
  calc
    data.selectedWeightLevel * data.selected.family.enncard =
        ∑ _index : Fin data.selected.family.card,
          data.selectedWeightLevel := by
      simp [Kakeya.Streamlined.TubeFamily.enncard, Finset.sum_const]
      ring
    _ ≤ ∑ index : Fin data.selected.family.card,
        anisotropicPaperCleanupIndicator cleanup
          (data.selected.embedding index) :=
      Finset.sum_le_sum fun index _ => (data.selected_weight_band index).1

end PureWZ2ExternalWeightRegularizationData

end Kakeya.Assouad

end
