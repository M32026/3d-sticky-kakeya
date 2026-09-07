import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleToSource
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05SynchronizedPostGrainRefresh
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantSource

/-!
# Re-entry-preserving one-scale hierarchy state

The fixed-family hierarchy iterator remembers only a grain configuration.
The synchronized Node-5 route genuinely changes the tube family, and its
ordinary normalization trace is needed by the next sticky call and by the
source-specific critical-floor bridge.  This module packages those data in
one dependent state and shows that one selected step retains the complete
locally-linear geometry on its exact next source.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Regard a one-scale output as a genuine grain refinement of its input
shading.  The retained global slope is the one constructed by the one-scale
argument, hence remains definitionally tied to that output. -/
noncomputable def PureWZ2LocallyLinearOneScaleData.toGrainRefinementData
    {sigma inputLoss delta outputLoss rho : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2LocallyLinearOneScaleData source outputLoss rho)
    (hinputOutput : inputLoss ≤ outputLoss) :
    PureWZ2GrainRefinementData source.shading sigma outputLoss where
  shading := data.shading
  subshading := data.subshading
  line_class := source.line_class
  cubical := data.whole_cells
  extremal := data.extremal
  top_level_cwa := source.top_level_cwa.mono_constant
    (pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one hinputOutput)
  volume_lower := data.volume_lower
  globalGrains := data.globalGrains
  localGrains := data.localGrains
  planeMap_vertical_bound := data.planeMap_vertical_bound

/-- One ordinary scale followed by synchronized tube pruning.  The next grain
source comes from the selected grain receipt, while its re-entry is refreshed
on the same selected family instead of retaining mass relative to the original
ordinary source. -/
structure PureWZ2ReentrantOneScaleStepData
    {sigma inputLoss delta : ℝ}
    {normalizationExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent)
    (grainLoss outputLoss rho outputEta : ℝ)
    (croppedMassFraction : ENNReal) where
  oneScale : PureWZ2LocallyLinearOneScaleData current.grain grainLoss rho
  input_loss_le : inputLoss ≤ grainLoss
  grain_loss_le : grainLoss ≤ outputLoss
  core : PureWZ2Node05SynchronizedPostGrainCore
    (pureWZ2Node05PostGrainIdentityRefinement current.grain.shading)
    current.reentry (oneScale.toGrainRefinementData input_loss_le)
    outputEta croppedMassFraction
  receipt : PureWZ2Node05SelectedGrainReceipt core outputLoss
  nextOrdinaryLoss : ℝ
  refreshedReentry : PureWZ2PropStickyReentryData
    (sigma := sigma) receipt.toGrainConfiguration.shading
    normalizationExponent nextOrdinaryLoss outputLoss
  refreshed_axial_window_eighth :
    ∀ index point,
      point ∈
          refreshedReentry.geometry.frame ''
            refreshedReentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8

namespace PureWZ2ReentrantOneScaleStepData

variable
    {sigma inputLoss delta grainLoss outputLoss rho outputEta : ℝ}
    {normalizationExponent : ℕ}
    {croppedMassFraction : ENNReal}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}

/-- The exact selected source for the next hierarchy level. -/
noncomputable def nextSource
    (step : PureWZ2ReentrantOneScaleStepData current grainLoss outputLoss rho
      outputEta croppedMassFraction) :
    PureWZ2QuantitativeGrainConfiguration sigma outputLoss delta :=
  step.receipt.toQuantitativeGrainConfiguration <| by
    intro z hz
    change |step.oneScale.globalGrains.slope z| ≤ 3
    rw [step.oneScale.slope_eq]
    exact current.grain.globalGrains.slope_bound z hz

/-- The exact selected re-entry for the next hierarchy level. -/
noncomputable def nextReentry
    (step : PureWZ2ReentrantOneScaleStepData current grainLoss outputLoss rho
      outputEta croppedMassFraction) :
    PureWZ2PropStickyReentryData
      (sigma := sigma) step.nextSource.shading normalizationExponent
      step.nextOrdinaryLoss outputLoss :=
  step.refreshedReentry

/-- Package the two definitionally synchronized projections as the next
reentrant hierarchy state. -/
noncomputable def next
    (step : PureWZ2ReentrantOneScaleStepData current grainLoss outputLoss rho
      outputEta croppedMassFraction) :
    PureWZ2ReentrantGrainSource
      sigma outputLoss delta normalizationExponent where
  ordinaryLoss := step.nextOrdinaryLoss
  grain := step.nextSource
  reentry := step.refreshedReentry
  ordinary_axial_window_eighth := step.refreshed_axial_window_eighth

/-- The selected next source is a literal subfamily/subshading of the raw
one-scale output. -/
theorem nextSource_union_subset
    (step : PureWZ2ReentrantOneScaleStepData current grainLoss outputLoss rho
      outputEta croppedMassFraction) :
    step.nextSource.shading.union ⊆ step.oneScale.shading.union := by
  rintro point ⟨index, hpoint⟩
  exact ⟨
    (pureWZ2Node05PostGrainSelectedSubfamily
      current.grain.family step.core.retained).embedding index,
    hpoint⟩

/-- Reindex the locally-linear output onto the exact selected next source.
All trapezoid geometry is unchanged; active-height statements are restricted
along the literal selected-shading inclusion. -/
noncomputable def selectedOneScale
    (step : PureWZ2ReentrantOneScaleStepData current grainLoss outputLoss rho
      outputEta croppedMassFraction) :
    PureWZ2LocallyLinearOneScaleData step.nextSource outputLoss rho where
  rho_pos := step.oneScale.rho_pos
  delta_le_rho := step.oneScale.delta_le_rho
  rho_le_one := step.oneScale.rho_le_one
  shading := step.nextSource.shading
  subshading := fun _ => Set.Subset.rfl
  whole_cells := step.nextSource.cubical
  extremal := step.nextSource.extremal
  volume_lower := step.nextSource.volume_lower
  localGrains := step.nextSource.localGrains
  planeMap_vertical_bound := step.nextSource.planeMap_vertical_bound
  globalGrains := step.nextSource.globalGrains
  slope_eq := rfl
  trapezoids := step.oneScale.trapezoids
  trapezoids_nonempty := step.oneScale.trapezoids_nonempty
  height_eq := step.oneScale.height_eq
  slope_bound := step.oneScale.slope_bound
  length_bounds := by
    intro trapezoid htrapezoid
    have hlower : Real.rpow rho (1 / 2 + outputLoss) ≤
        Real.rpow rho (1 / 2 + grainLoss) :=
      Real.rpow_le_rpow_of_exponent_ge step.oneScale.rho_pos
        step.oneScale.rho_le_one (by linarith [step.grain_loss_le])
    exact ⟨hlower.trans (step.oneScale.length_bounds trapezoid htrapezoid).1,
      (step.oneScale.length_bounds trapezoid htrapezoid).2⟩
  separated_cores := step.oneScale.separated_cores
  slope_approximation := by
    intro trapezoid htrapezoid z hz hslice
    have hsourceSlice : horizontalSlice step.oneScale.shading.union z ≠ ∅ := by
      apply Set.Nonempty.ne_empty
      apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr hslice)
      intro point hpoint
      exact ⟨step.nextSource_union_subset hpoint.1, hpoint.2⟩
    change |step.oneScale.globalGrains.slope z - trapezoid.affine z| ≤ rho
    exact step.oneScale.slope_approximation
      trapezoid htrapezoid z hz hsourceSlice
  active_height_coverage := by
    intro z hz hslice
    have hsourceSlice : horizontalSlice step.oneScale.shading.union z ≠ ∅ := by
      apply Set.Nonempty.ne_empty
      apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr hslice)
      intro point hpoint
      exact ⟨step.nextSource_union_subset hpoint.1, hpoint.2⟩
    exact step.oneScale.active_height_coverage z hz hsourceSlice

end PureWZ2ReentrantOneScaleStepData

end Kakeya.Assouad

end
