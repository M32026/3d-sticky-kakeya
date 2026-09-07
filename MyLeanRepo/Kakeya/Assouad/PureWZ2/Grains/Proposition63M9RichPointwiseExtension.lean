import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9PaperLemma43Robust
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RichStickyKernel
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SubfamilyGrainConfigurationExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WeakLipschitzPlaneMapRefinement

/-!
# Proposition 6.3 M9: rich pointwise zero-extension

This module transports a pointwise weak-plane-map refinement on the exact
terminal family selected by a rich Node 3 output back to the ambient cropped
family.  It only performs the structural zero-extension.  In particular, it
does not restore extremality or run any later regularization step.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- A pointwise weak-plane-map refinement represented on the ambient cropped
family, together with the cubical receipt supplied by its selected-family
producer. -/
structure Proposition63M9RichPointwiseExtensionData
    {delta incidenceBudget : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    (croppedShading : WZ1PaperTubeShading croppedFamily) where
  pointwise : Proposition63PointwiseWeakMapRefinementData
    croppedShading incidenceBudget
  cubical : WZ1PaperIsCubicalShading pointwise.shading

/-- Zero-extend a pointwise Lemma 4.3 refinement along the selected family of
a rich terminal output.  Cubicality is deliberately an explicit input.  The
ambient mass receipt includes exactly the Node 3 retention factor on the
left and introduces no further loss on the right. -/
noncomputable def proposition63_m9_rich_pointwise_extension
    {delta sigma outputLoss sourceLoss normalizationLoss incidenceBudget : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (pointwise : Proposition63PointwiseWeakMapRefinementData
      rich.data.refined incidenceBudget)
    (hdeltaOne : delta < 1)
    (pointwiseCubical : WZ1PaperIsCubicalShading pointwise.shading) :
    Proposition63M9RichPointwiseExtensionData
      (incidenceBudget := incidenceBudget) croppedShading where
  pointwise := {
    shading := extendShading rich.data.selected pointwise.shading
    subshading := extendShading_subshading rich.data.selected fun index =>
      (pointwise.subshading index).trans (rich.data.subshading index)
    planeMap := PaperWZ1WeakPlaneMapData.extendSubfamily
      rich.data.selected pointwise.planeMap
    leftFactor :=
      wz2PaperPureRefinementFraction delta 61 * pointwise.leftFactor
    rightFactor := pointwise.rightFactor
    leftFactor_pos := by
      apply ENNReal.mul_pos
      · unfold wz2PaperPureRefinementFraction
        exact (ENNReal.pow_pos
          (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) 61).ne'
      · exact pointwise.leftFactor_pos.ne'
    leftFactor_ne_top := by
      apply ENNReal.mul_ne_top
      · unfold wz2PaperPureRefinementFraction
        apply ENNReal.pow_ne_top
        apply ENNReal.inv_ne_top.mpr
        exact (ENNReal.ofReal_pos.mpr <| Real.log_pos <|
          one_lt_one_div reentry.cropped_extremal.delta_pos hdeltaOne).ne'
      · exact pointwise.leftFactor_ne_top
    rightFactor_ne_top := pointwise.rightFactor_ne_top
    mass_retention := by
      calc
        (wz2PaperPureRefinementFraction delta 61 * pointwise.leftFactor) *
            croppedShading.mass =
          pointwise.leftFactor *
            (wz2PaperPureRefinementFraction delta 61 *
              croppedShading.mass) := by ring
        _ ≤ pointwise.leftFactor * rich.data.refined.mass := by
          exact mul_le_mul_right rich.total_mass_retention _
        _ ≤ pointwise.rightFactor * pointwise.shading.mass :=
          pointwise.mass_retention
        _ = pointwise.rightFactor *
            (extendShading rich.data.selected pointwise.shading).mass := by
          rw [extendShading_mass]
  }
  cubical := Kakeya.Assouad.extendShading_cubical
    rich.data.selected pointwiseCubical

/-- Restore cropped extremality after the rich-terminal pointwise refinement
has been zero-extended to the ambient family.  The absorption hypothesis is
stated for the combined ambient mass receipt, so the Node 3 retention factor
cannot be omitted or paid twice by a downstream caller. -/
theorem Proposition63M9RichPointwiseExtensionData.restore
    {delta sigma sourceLoss targetLoss incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (data : Proposition63M9RichPointwiseExtensionData
      (incidenceBudget := incidenceBudget) source)
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss family source)
    (htargetLoss : 0 < targetLoss)
    (hsourceTarget : sourceLoss ≤ targetLoss)
    (hrestore :
      proposition63Lemma43MassLoss
          data.pointwise.leftFactor data.pointwise.rightFactor *
        Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta sourceLoss) :
    Nonempty (Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget) := by
  let massLoss := proposition63Lemma43MassLoss
    data.pointwise.leftFactor data.pointwise.rightFactor
  have hmassLossPos : 0 < massLoss :=
    proposition63Lemma43MassLoss_pos _ _
  have hmassLossTop : massLoss ≠ ⊤ :=
    proposition63Lemma43MassLoss_ne_top data.pointwise.leftFactor_pos
      data.pointwise.rightFactor_ne_top
  have hinverse :
      massLoss⁻¹ * source.mass ≤ data.pointwise.shading.mass :=
    proposition63Lemma43MassLoss_inv_mul_le
      data.pointwise.leftFactor_pos data.pointwise.leftFactor_ne_top
      data.pointwise.rightFactor_ne_top data.pointwise.mass_retention
  have hextremal : WZ2PaperCroppedIsExtremal
      sigma targetLoss family data.pointwise.shading := by
    apply transfer_cropped_extremal_to_subshading massLoss
      hmassLossPos hmassLossTop sourceExtremal data.pointwise.subshading
      hinverse data.cubical hsourceTarget
    · exact hrestore
    · exact sourceExtremal.delta_pos
    · exact sourceExtremal.delta_le_one
    · exact htargetLoss
  exact ⟨{
    shading := data.pointwise.shading
    subshading := data.pointwise.subshading
    planeMap := data.pointwise.planeMap
    leftFactor := data.pointwise.leftFactor
    rightFactor := data.pointwise.rightFactor
    leftFactor_pos := data.pointwise.leftFactor_pos
    leftFactor_ne_top := data.pointwise.leftFactor_ne_top
    rightFactor_ne_top := data.pointwise.rightFactor_ne_top
    mass_retention := data.pointwise.mass_retention
    cubical := data.cubical
    extremal := hextremal }⟩

end Kakeya.Assouad.PureWZ2

end
