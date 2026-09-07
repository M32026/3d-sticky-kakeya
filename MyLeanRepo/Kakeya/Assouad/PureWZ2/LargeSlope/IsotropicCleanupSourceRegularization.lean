import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicDistinctCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PureExternalWeightRegularization

/-!
# Source nearby-CWA regularization supported on the final-isotropic cleanup

An arbitrary essentially-distinct cleanup does not inherit nearby-scale CWA.
This module puts the retained target shading mass back on the corresponding
source indices and runs the closed external-weight regularizer there.  Every
positive-weight output index therefore belongs to the target cleanup, giving
synchronized source and target subfamilies with one common index type.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2IsotropicDistinctCleanupData

/-- The cleanup target index regarded as its original source index. -/
def sourceIndex
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    (cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading) :
    Fin cleanup.targetSubfamily.family.card ↪ Fin sourceFamily.card :=
  cleanup.targetSubfamily.embedding

/-- Retained target shaded mass, extended by zero to all source indices. -/
def sourceWeight
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    (cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading)
    (index : Fin sourceFamily.card) : ENNReal :=
  ∑ target : Fin cleanup.targetSubfamily.family.card,
    if cleanup.sourceIndex target = index then
      volume (cleanup.restrictedShading.carrier target)
    else 0

/-- Summing the zero-extended source weight recovers exactly the retained
target shading mass. -/
theorem sourceWeight_sum
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    (cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading) :
    (∑ index : Fin sourceFamily.card, cleanup.sourceWeight index) =
      cleanup.restrictedShading.mass := by
  unfold sourceWeight
  rw [Finset.sum_comm]
  change
    (∑ target : Fin cleanup.targetSubfamily.family.card,
      ∑ index : Fin sourceFamily.card,
        if cleanup.sourceIndex target = index then
          volume (cleanup.restrictedShading.carrier target) else 0) =
      ∑ target : Fin cleanup.targetSubfamily.family.card,
        volume (cleanup.restrictedShading.carrier target)
  apply Finset.sum_congr rfl
  intro target _
  rw [Fintype.sum_ite_eq]

/-- Each cleanup-supported source weight is bounded by the fixed crop-box
volume. -/
theorem sourceWeight_le_eight
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    (cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading)
    (index : Fin sourceFamily.card) :
    cleanup.sourceWeight index ≤ 8 := by
  unfold sourceWeight
  by_cases hexists : ∃ target : Fin cleanup.targetSubfamily.family.card,
      cleanup.sourceIndex target = index
  · rcases hexists with ⟨target, htarget⟩
    have hunique : ∀ other : Fin cleanup.targetSubfamily.family.card,
        cleanup.sourceIndex other = index → other = target := by
      intro other hother
      apply cleanup.sourceIndex.injective
      exact hother.trans htarget.symm
    have hcondition : ∀ other : Fin cleanup.targetSubfamily.family.card,
        cleanup.sourceIndex other = index ↔ other = target := by
      intro other
      constructor
      · exact hunique other
      · rintro rfl
        exact htarget
    simp_rw [hcondition]
    rw [Fintype.sum_ite_eq']
    have hsubset : cleanup.restrictedShading.carrier target ⊆
        Kakeya.Streamlined.axisBox 2 2 2 := by
      intro point hpoint
      exact (cleanup.restrictedShading.subset_body target hpoint).2
    calc
      volume (cleanup.restrictedShading.carrier target) ≤
          volume (Kakeya.Streamlined.axisBox 2 2 2) := measure_mono hsubset
      _ = 8 := by
        rw [Kakeya.Streamlined.volume_axisBox 2 2 2] <;> norm_num
  · have hnone : ∀ target : Fin cleanup.targetSubfamily.family.card,
        cleanup.sourceIndex target ≠ index := by
      intro target heq
      exact hexists ⟨target, heq⟩
    calc
      (∑ target : Fin cleanup.targetSubfamily.family.card,
        if cleanup.sourceIndex target = index then
          volume (cleanup.restrictedShading.carrier target) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro target _
        rw [if_neg (hnone target)]
      _ ≤ 8 := bot_le

end PureWZ2IsotropicDistinctCleanupData

/-- Source-side regularization whose positive support lies in one fixed
final-isotropic distinctness cleanup. -/
abbrev PureWZ2IsotropicCleanupSourceRegularizationData
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    (cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading)
    (sourceConstant scheduleConstant normalizationWeight : ENNReal)
    (levelCount : ℕ) :=
  PureWZ2ExternalWeightRegularizationData
    sourceConstant scheduleConstant normalizationWeight 8 levelCount
      cleanup.sourceWeight

/-- Restore source nearby-scale CWA while forcing every selected index to
remain inside the already chosen target distinctness cleanup. -/
theorem pureWZ2_isotropic_cleanup_source_regularization
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    (ambientCWA : WZ2PaperPureCWAAtNearbyScales
      sourceFamily sourceConstant)
    (hfamily : sourceFamily.Nonempty)
    (hsourceDeltaOne : sourceDelta ≤ 1)
    (cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading)
    (hnormalizationZero : normalizationWeight ≠ 0)
    (hnormalizationTop : normalizationWeight ≠ ⊤)
    (hmass : normalizationWeight * sourceFamily.enncard ≤
      cleanup.restrictedShading.mass)
    (levelCount : ℕ)
    (hsourceTwo : 2 < sourceConstant)
    (hlevels : ENNReal.ofReal (1 / sourceDelta) ≤
      sourceConstant ^ levelCount)
    (hscheduleFinite : WZ2PaperFiniteErrorConstant scheduleConstant)
    (hscheduleConstant : sourceConstant * sourceConstant ≤ scheduleConstant) :
    Nonempty (PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount) := by
  apply pureWZ2_external_weight_regularization
    (ambientCWA := ambientCWA)
    (hfamily := hfamily)
    (hdeltaOne := hsourceDeltaOne)
    (hscheduleFinite := hscheduleFinite)
    (hnormalizationZero := hnormalizationZero)
    (hnormalizationTop := hnormalizationTop)
    (hweightUpperTop := by norm_num)
    (externalWeight := cleanup.sourceWeight)
    (hmass := ?_)
    (hweight := cleanup.sourceWeight_le_eight)
    (levelCount := levelCount)
    (hambientTwo := hsourceTwo)
    (hlevels := hlevels)
    (hscheduleConstant := hscheduleConstant)
  rw [cleanup.sourceWeight_sum]
  exact hmass

namespace PureWZ2ExternalWeightRegularizationData

/-- Every source tube selected by cleanup-supported regularization comes from
the target cleanup. -/
theorem isotropicCleanup_support
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount)
    (index : Fin data.selected.family.card) :
    data.selected.embedding index ∈
      Finset.univ.map cleanup.sourceIndex := by
  have hpositive := data.selected_weight_pos index
  unfold PureWZ2IsotropicDistinctCleanupData.sourceWeight at hpositive
  by_contra hnot
  have hnone : ¬∃ target : Fin cleanup.targetSubfamily.family.card,
      cleanup.sourceIndex target = data.selected.embedding index := by
    intro hexists
    rcases hexists with ⟨target, htarget⟩
    exact hnot (Finset.mem_map.mpr
      ⟨target, Finset.mem_univ _, htarget⟩)
  have hzero :
      (∑ target : Fin cleanup.targetSubfamily.family.card,
        if cleanup.sourceIndex target = data.selected.embedding index then
          volume (cleanup.restrictedShading.carrier target) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro target _
    rw [if_neg (fun heq => hnone ⟨target, heq⟩)]
  rw [hzero] at hpositive
  exact (lt_irrefl 0 hpositive).elim

/-- The unique target-cleanup index underlying a twice-selected source
index. -/
def isotropicCleanupTargetPreimage
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount)
    (index : Fin data.selected.family.card) :
    Fin cleanup.targetSubfamily.family.card :=
  (Finset.mem_map.mp (data.isotropicCleanup_support index)).choose

theorem isotropicCleanupTargetPreimage_source
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount)
    (index : Fin data.selected.family.card) :
    cleanup.sourceIndex (data.isotropicCleanupTargetPreimage index) =
      data.selected.embedding index :=
  (Finset.mem_map.mp (data.isotropicCleanup_support index)).choose_spec.2

/-- The synchronized target family, indexed literally by the regularized
source family. -/
def isotropicCleanupTargetSubfamily
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount) :
    Kakeya.Streamlined.TubeSubfamily cleanup.targetSubfamily.family where
  family :=
    { card := data.selected.family.card
      tube := fun index => cleanup.targetSubfamily.family.tube
        (data.isotropicCleanupTargetPreimage index) }
  embedding :=
    { toFun := data.isotropicCleanupTargetPreimage
      inj' := by
        intro first second heq
        apply data.selected.embedding.injective
        rw [← data.isotropicCleanupTargetPreimage_source first,
          ← data.isotropicCleanupTargetPreimage_source second, heq] }
  tube_eq _ := rfl

/-- The synchronized target tube is the centered isotropic image of the
source tube with the same final index. -/
theorem isotropicCleanupTargetSubfamily_tube
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount)
    (index : Fin data.selected.family.card) :
    (data.isotropicCleanupTargetSubfamily.family.tube index) =
      pureWZ2PaperCenteredTube
        (pureWZ2IsotropicPaperTube center scale
          (data.selected.family.tube index)) := by
  change cleanup.targetSubfamily.family.tube
      (data.isotropicCleanupTargetPreimage index) = _
  rw [cleanup.targetSubfamily.tube_eq, data.selected.tube_eq]
  change pureWZ2PaperCenteredTube
      (pureWZ2IsotropicPaperTube center scale
        (sourceFamily.tube
          (cleanup.sourceIndex (data.isotropicCleanupTargetPreimage index)))) = _
  rw [data.isotropicCleanupTargetPreimage_source]

/-- Ordinary distinctness is inherited from the fixed cleanup. -/
theorem isotropicCleanupTargetSubfamily_distinct
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount) :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      data.isotropicCleanupTargetSubfamily.family := by
  let selected : WZ2PaperPureTubeSubfamily cleanup.targetSubfamily.family :=
    { family := data.isotropicCleanupTargetSubfamily.family
      embedding := data.isotropicCleanupTargetSubfamily.embedding
      tube_eq := data.isotropicCleanupTargetSubfamily.tube_eq }
  exact cleanup.distinct.subfamily selected

/-- Literal retained target shading on the synchronized final indices. -/
def isotropicCleanupTargetShading
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount) :
    WZ1PaperTubeShading data.isotropicCleanupTargetSubfamily.family :=
  restrictPaperShading data.isotropicCleanupTargetSubfamily
    cleanup.restrictedShading

/-- The canonical final family used by the representative-parent quotient
schedule.  Its indices are exactly the twice-selected source indices. -/
def isotropicCleanupFinalFamily
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount) :
    Kakeya.Streamlined.TubeFamily targetDelta :=
  pureWZ2IsotropicCenteredPaperFamily data.selected.family center scale

theorem isotropicCleanupTargetSubfamily_tube_eq_final
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount)
    (index : Fin data.selected.family.card) :
    data.isotropicCleanupTargetSubfamily.family.tube index =
      data.isotropicCleanupFinalFamily.tube index := by
  exact data.isotropicCleanupTargetSubfamily_tube index

/-- The retained target shading, transported along the pointwise identity to
the canonical midpoint-centered final family. -/
def isotropicCleanupFinalShading
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount) :
    WZ1PaperTubeShading data.isotropicCleanupFinalFamily where
  carrier index := data.isotropicCleanupTargetShading.carrier index
  measurable_carrier index :=
    data.isotropicCleanupTargetShading.measurable_carrier index
  subset_body index := by
    have hsubset := data.isotropicCleanupTargetShading.subset_body index
    change data.isotropicCleanupTargetShading.carrier index ⊆
      wz1PaperTubeCarrier
        (data.isotropicCleanupTargetSubfamily.family.tube index) at hsubset
    change data.isotropicCleanupTargetShading.carrier index ⊆
      wz1PaperTubeCarrier (data.isotropicCleanupFinalFamily.tube index)
    rw [data.isotropicCleanupTargetSubfamily_tube_eq_final index] at hsubset
    exact hsubset

@[simp] theorem isotropicCleanupFinalShading_carrier
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount)
    (index : Fin data.selected.family.card) :
    data.isotropicCleanupFinalShading.carrier index =
      targetShading.carrier (data.selected.embedding index) := by
  change cleanup.restrictedShading.carrier
      (data.isotropicCleanupTargetPreimage index) = _
  change targetShading.carrier
      (cleanup.sourceIndex (data.isotropicCleanupTargetPreimage index)) = _
  rw [data.isotropicCleanupTargetPreimage_source]

/-- The canonical final family inherits ordinary distinctness from the fixed
cleanup without changing indices. -/
theorem isotropicCleanupFinalFamily_distinct
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount) :
    WZ2PaperOrdinaryIsEssentiallyDistinct data.isotropicCleanupFinalFamily := by
  intro first second hne
  simpa only [data.isotropicCleanupTargetSubfamily_tube_eq_final] using
    data.isotropicCleanupTargetSubfamily_distinct first second hne

/-- The regularizer's selected weight is exactly the mass of the canonical
final shading. -/
theorem selectedWeight_eq_isotropicCleanupFinalShading_mass
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount) :
    data.selectedWeight = data.isotropicCleanupFinalShading.mass := by
  rw [data.selectedWeight_eq]
  change
    (∑ index : Fin data.selected.family.card,
      cleanup.sourceWeight (data.selected.embedding index)) =
    ∑ index : Fin data.selected.family.card,
      volume (cleanup.restrictedShading.carrier
        (data.isotropicCleanupTargetPreimage index))
  apply Finset.sum_congr rfl
  intro index _
  unfold PureWZ2IsotropicDistinctCleanupData.sourceWeight
  let target := data.isotropicCleanupTargetPreimage index
  have htarget := data.isotropicCleanupTargetPreimage_source index
  have hunique : ∀ other : Fin cleanup.targetSubfamily.family.card,
      cleanup.sourceIndex other = data.selected.embedding index ↔
        other = target := by
    intro other
    constructor
    · intro hother
      apply cleanup.sourceIndex.injective
      exact hother.trans htarget.symm
    · rintro rfl
      exact htarget
  simp_rw [hunique]
  rw [Fintype.sum_ite_eq']

theorem selected_sourceWeight_eq_finalShading_volume
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount)
    (index : Fin data.selected.family.card) :
    cleanup.sourceWeight (data.selected.embedding index) =
      volume (data.isotropicCleanupFinalShading.carrier index) := by
  change cleanup.sourceWeight (data.selected.embedding index) =
    volume (cleanup.restrictedShading.carrier
      (data.isotropicCleanupTargetPreimage index))
  unfold PureWZ2IsotropicDistinctCleanupData.sourceWeight
  let target := data.isotropicCleanupTargetPreimage index
  have htarget := data.isotropicCleanupTargetPreimage_source index
  have hunique : ∀ other : Fin cleanup.targetSubfamily.family.card,
      cleanup.sourceIndex other = data.selected.embedding index ↔
        other = target := by
    intro other
    constructor
    · intro hother
      apply cleanup.sourceIndex.injective
      exact hother.trans htarget.symm
    · rintro rfl
      exact htarget
  simp_rw [hunique]
  rw [Fintype.sum_ite_eq']

/-- Quantitative shaded-mass retention through the cleanup-supported source
nearby-CWA regularization. -/
theorem isotropicCleanupFinalShading_mass_retention
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount) :
    cleanup.restrictedShading.mass ≤ data.regularizationLoss *
      data.isotropicCleanupFinalShading.mass := by
  have hretained := data.retained_weight
  rw [cleanup.sourceWeight_sum,
    data.selectedWeight_eq_isotropicCleanupFinalShading_mass] at hretained
  exact hretained

end PureWZ2ExternalWeightRegularizationData

end Kakeya.Assouad

end
