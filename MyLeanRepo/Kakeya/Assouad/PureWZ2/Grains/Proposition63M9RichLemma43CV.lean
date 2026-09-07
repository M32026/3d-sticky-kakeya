import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9PaperCVWitness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RichStickyKernel

/-!
# Proposition 6.3 M9: rich-terminal CV adapter

This module specializes the fixed paper CV witness to the exact selected
family and refined shading of a rich terminal.  The normalization envelope
then enlarges the fixed CV constant to the normalization power used by the
ambient Lemma 4.3 restoration.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- Adapt the pre-runtime paper CV witness to the exact rich-terminal family
and shading.  The support inclusion is not needed by the universal CV theorem.
The output constant is definitionally the requested normalization power. -/
theorem proposition63_m9_rich_lemma43_cv
    {delta sigma outputLoss sourceLoss normalizationLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (cv : Proposition63M9PaperCVConstantWitness)
    (envelope : Proposition63M9NormalizationPowerEnvelope
      cv normalizationLoss)
    (hdeltaCutoff : delta ≤ envelope.cutoff)
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho) :
    ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ rich.data.refined.union → ∀ (L : ENNReal),
        (∀ point ∈ E, L ≤
          (paperShadingTrilinearMultiplicity rich.data.refined point) ^
            (1 / 2 : ℝ)) →
        L * volume E ≤
          Kakeya.realRpowENN delta (-normalizationLoss) *
            (ENNReal.ofReal (delta ^ 2) *
              rich.data.selected.family.enncard) ^ (3 / 2 : ℝ) := by
  intro E measurable_E _hE L lower_bound
  exact (cv.broad_set_estimate delta
    reentry.cropped_extremal.delta_pos
    reentry.cropped_extremal.delta_le_one
    rich.data.selected.family rich.data.refined E L measurable_E
    lower_bound).trans <| by
      gcongr
      exact envelope.constant_le_power delta
        reentry.cropped_extremal.delta_pos hdeltaCutoff

end Kakeya.Assouad.PureWZ2

end
