import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SubfamilyGrainConfigurationExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SelectedCardinalityCancellation
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper

/-!
# Extremality after extending a selected paper family

The paper sometimes proves density on a genuinely selected tube family and
then uses its shading as a current state inside the ambient family carrying
the ordinary normalization.  Since cropped paper-tube carriers meet a fixed
box, equal radii do not make their volumes definitionally equal.  This module
therefore performs that lift with the explicit uniform carrier-volume
constant and a genuine indexed-cardinality retention receipt.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

/-- Lift cropped extremality from a selected tube family to its zero-extension
on an ambient family.  Density pays the selected-to-ambient cardinality loss
and the uniform cropped-paper carrier-volume constant.  Nearby CWA and the
volume upper bound remain on the original ambient family. -/
theorem subfamily_extension_cropped_extremal_of_cardinality
    {delta sigma ambientLoss selectedLoss targetLoss : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambient}
    (selected : Kakeya.Streamlined.TubeSubfamily ambient)
    {selectedShading : WZ1PaperTubeShading selected.family}
    (ambientExtremal : WZ2PaperCroppedIsExtremal
      sigma ambientLoss ambient ambientShading)
    (selectedExtremal : WZ2PaperCroppedIsExtremal
      sigma selectedLoss selected.family selectedShading)
    (hselectedSub : ∀ index, selectedShading.carrier index ⊆
      ambientShading.carrier (selected.embedding index))
    (hambientTarget : ambientLoss ≤ targetLoss)
    (leftFactor rightFactor : ENNReal)
    (hleftZero : leftFactor ≠ 0)
    (hleftTop : leftFactor ≠ ⊤)
    (hcardinality :
      leftFactor * ambient.enncard ≤
        rightFactor * selected.family.enncard)
    (habsorb :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) * rightFactor *
          Kakeya.realRpowENN delta targetLoss ≤
        leftFactor * Kakeya.realRpowENN delta selectedLoss)
    (htargetLoss : 0 < targetLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hline : WZ1PaperIsLineClass ambient) :
    WZ2PaperCroppedIsExtremal sigma targetLoss ambient
      (extendShading selected selectedShading) := by
  let geometryConstant : ENNReal :=
    (55296 : ENNReal) * Kakeya.deltaTubeVolume 1
  let scaleMass : ENNReal := Kakeya.realRpowENN delta 2
  let fullAmbient : WZ1PaperTubeShading ambient :=
    { carrier := fun index => wz1PaperTubeCarrier (ambient.tube index)
      measurable_carrier := fun index =>
        wz1PaperTubeCarrier_measurable (ambient.tube index)
      subset_body := fun _ => Set.Subset.rfl }
  have hambientBody :
      (wz1PaperBodyFamily ambient).mass ≤
        geometryConstant * scaleMass * ambient.enncard := by
    have upper := wz2_paper_shading_mass_upper
      ambientExtremal.delta_pos hdeltaSmall hline fullAmbient
    change (wz1PaperBodyFamily ambient).mass ≤
      (55296 * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN delta 2 * ambient.enncard at upper
    simpa only [geometryConstant, scaleMass] using upper
  have hselectedBody :
      scaleMass * selected.family.enncard ≤
        (wz1PaperBodyFamily selected.family).mass := by
    exact paperBodyFamily_mass_lower_rpow_two ambientExtremal.delta_pos
      (hdeltaSmall.trans (by norm_num)) (hline.subfamily selected)
  have hdenseScaled :
      leftFactor *
          (Kakeya.realRpowENN delta targetLoss *
            (wz1PaperBodyFamily ambient).mass) ≤
        leftFactor * selectedShading.mass := by
    calc
      leftFactor *
            (Kakeya.realRpowENN delta targetLoss *
              (wz1PaperBodyFamily ambient).mass) ≤
          leftFactor *
            (Kakeya.realRpowENN delta targetLoss *
              (geometryConstant * scaleMass * ambient.enncard)) := by
        gcongr
      _ = (geometryConstant * Kakeya.realRpowENN delta targetLoss *
              scaleMass) * (leftFactor * ambient.enncard) := by ring
      _ ≤ (geometryConstant * Kakeya.realRpowENN delta targetLoss *
              scaleMass) *
            (rightFactor * selected.family.enncard) := by gcongr
      _ = (geometryConstant * rightFactor *
              Kakeya.realRpowENN delta targetLoss) *
            (scaleMass * selected.family.enncard) := by ring
      _ ≤ (leftFactor * Kakeya.realRpowENN delta selectedLoss) *
            (wz1PaperBodyFamily selected.family).mass := by gcongr
      _ ≤ leftFactor * selectedShading.mass := by
        simpa only [mul_assoc] using
          mul_le_mul_left' selectedExtremal.dense leftFactor
  have hdense :
      Kakeya.realRpowENN delta targetLoss *
          (wz1PaperBodyFamily ambient).mass ≤ selectedShading.mass := by
    rw [mul_comm leftFactor
        (Kakeya.realRpowENN delta targetLoss *
          (wz1PaperBodyFamily ambient).mass),
      mul_comm leftFactor selectedShading.mass] at hdenseScaled
    exact (ENNReal.mul_le_mul_iff_left hleftZero hleftTop).mp hdenseScaled
  let weakened := ambientExtremal.mono_loss hambientTarget
  have hextendedSub : PaperIsSubshading
      (extendShading selected selectedShading) ambientShading :=
    extendShading_subshading selected hselectedSub
  have hunion : (extendShading selected selectedShading).union ⊆
      ambientShading.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, hextendedSub index hpoint⟩
  exact
    { delta_pos := weakened.delta_pos
      delta_le_one := weakened.delta_le_one
      nonempty := weakened.nonempty
      cwa_nearby_scales := weakened.cwa_nearby_scales
      cubical := extendShading_cubical selected selectedExtremal.cubical
      dense := by
        change Kakeya.realRpowENN delta targetLoss *
          (wz1PaperBodyFamily ambient).mass ≤
            (extendShading selected selectedShading).mass
        rw [extendShading_mass]
        exact hdense
      volume_upper :=
        (measure_mono hunion).trans weakened.volume_upper }

end Kakeya.Assouad.PureWZ2

end
