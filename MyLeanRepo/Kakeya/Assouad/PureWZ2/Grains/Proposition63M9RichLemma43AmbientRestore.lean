import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RichLemma43Preparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RichPointwiseExtension

/-!
# Proposition 6.3 M9: ambient Lemma 4.3 restoration

This module mechanically assembles the rich-terminal pointwise Lemma 4.3
producer, its zero-extension to the ambient cropped family, and the ambient
extremality restoration wrapper.  The restoration hypothesis records the
combined rich-retention and pointwise mass loss explicitly.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- M9-private Lemma 4.3 output retaining the vertical bound proved from the
actual transverse-pair construction. -/
structure Proposition63M9Lemma43VerticalData
    {delta sigma sourceLoss targetLoss incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family) where
  lemma43 : Proposition63Lemma43Data
    (sigma := sigma) (sourceLoss := sourceLoss)
    (targetLoss := targetLoss) source incidenceBudget
  planeMap_vertical_bound : ∀ point ∈ lemma43.shading.union,
    |lemma43.planeMap.planeMap point (2 : Fin 3)| ≤ 1 / 2

/-- Run the rich-terminal pointwise Lemma 4.3 core, zero-extend its output to
the ambient cropped family, and restore cropped extremality there.  The
absorption input uses the combined ambient left factor, including the Node 3
retention factor exactly once. -/
theorem proposition63_m9_rich_lemma43_ambient_restore
    {delta sigma outputLoss sourceLoss normalizationLoss densityLoss theta
      incidenceBudget targetLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (richPrepared : Proposition63M9RichLemma43Preparation
      (densityLoss := densityLoss) rich)
    (hCV : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ rich.data.refined.union → ∀ (L : ENNReal),
        (∀ point ∈ E, L ≤
          (paperShadingTrilinearMultiplicity rich.data.refined point) ^
            (1 / 2 : ℝ)) →
        L * volume E ≤
          C * (ENNReal.ofReal (delta ^ 2) *
            rich.data.selected.family.enncard) ^ (3 / 2 : ℝ))
    (hrhoSmall : rho.1 ≤ 1 / 10000)
    (hdegree : (96 : ENNReal) * stickyCoarseCloseCount ≤
      (rich.terminal.fineDegreeFloor : ENNReal))
    (htheta : 0 < theta)
    (hincidence : theta / rho.1 ≤ incidenceBudget)
    (hbroadAbsorb :
      let m := 2 ^ richPrepared.prepared.band.level
      let Q : ℕ := m ^ 3 / 4
      (2 : ENNReal) * (2 * m : ℕ) * C *
          (ENNReal.ofReal (delta ^ 2) *
            rich.data.selected.family.enncard) ^ (3 / 2 : ℝ) ≤
        (((Q : ENNReal) * ENNReal.ofReal theta) ^ (1 / 2 : ℝ)) *
          richPrepared.prepared.band.band.mass)
    (hdeltaOne : delta < 1)
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma normalizationLoss croppedFamily croppedShading)
    (htargetLoss : 0 < targetLoss)
    (hsourceTarget : normalizationLoss ≤ targetLoss)
    (hrestore :
      proposition63Lemma43MassLoss
          (wz2PaperPureRefinementFraction delta 61 * (1 / 16))
          ((Nat.log 2 rich.data.selected.family.card + 1 : ℕ) : ENNReal) *
        Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta normalizationLoss) :
    Nonempty (Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := normalizationLoss)
      (targetLoss := targetLoss) croppedShading incidenceBudget) := by
  rcases proposition63_m9_rich_pointwise_weak_map_from_preparation
      rich richPrepared hCV hrhoSmall hdegree htheta hincidence
      hbroadAbsorb with
    ⟨pointwise, pointwiseCubical, hleftFactor, hrightFactor⟩
  let ambient := proposition63_m9_rich_pointwise_extension
    rich pointwise hdeltaOne pointwiseCubical
  apply ambient.restore sourceExtremal htargetLoss hsourceTarget
  simpa only [ambient, proposition63_m9_rich_pointwise_extension,
      hleftFactor, hrightFactor] using hrestore

/-- Construction-aware ambient restoration.  The family-direction hypothesis
is inherited from the first literal rescaling; it is consumed only to prove
the private vertical bound and is not added to the public Lemma 4.3 record. -/
theorem proposition63_m9_rich_lemma43_ambient_restore_vertical
    {delta sigma outputLoss sourceLoss normalizationLoss densityLoss theta
      incidenceBudget targetLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (richPrepared : Proposition63M9RichLemma43Preparation
      (densityLoss := densityLoss) rich)
    (hCV : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ rich.data.refined.union → ∀ (L : ENNReal),
        (∀ point ∈ E, L ≤
          (paperShadingTrilinearMultiplicity rich.data.refined point) ^
            (1 / 2 : ℝ)) →
        L * volume E ≤
          C * (ENNReal.ofReal (delta ^ 2) *
            rich.data.selected.family.enncard) ^ (3 / 2 : ℝ))
    (hrhoSmall : rho.1 ≤ 1 / 10000)
    (hdegree : (96 : ENNReal) * stickyCoarseCloseCount ≤
      (rich.terminal.fineDegreeFloor : ENNReal))
    (htheta : 0 < theta)
    (hincidence : theta / rho.1 ≤ incidenceBudget)
    (hbroadAbsorb :
      let m := 2 ^ richPrepared.prepared.band.level
      let Q : ℕ := m ^ 3 / 4
      (2 : ENNReal) * (2 * m : ℕ) * C *
          (ENNReal.ofReal (delta ^ 2) *
            rich.data.selected.family.enncard) ^ (3 / 2 : ℝ) ≤
        (((Q : ENNReal) * ENNReal.ofReal theta) ^ (1 / 2 : ℝ)) *
          richPrepared.prepared.band.band.mass)
    (hdeltaOne : delta < 1)
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma normalizationLoss croppedFamily croppedShading)
    (htargetLoss : 0 < targetLoss)
    (hsourceTarget : normalizationLoss ≤ targetLoss)
    (hrestore :
      proposition63Lemma43MassLoss
          (wz2PaperPureRefinementFraction delta 61 * (1 / 16))
          ((Nat.log 2 rich.data.selected.family.card + 1 : ℕ) : ENNReal) *
        Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta normalizationLoss)
    (hfamilyVertical : ∀ index, Real.sqrt 3 / 2 ≤
      wz1PaperDirection (croppedFamily.tube index) (2 : Fin 3)) :
    Nonempty (Proposition63M9Lemma43VerticalData
      (sigma := sigma) (sourceLoss := normalizationLoss)
      (targetLoss := targetLoss) (incidenceBudget := incidenceBudget)
      croppedShading) := by
  rcases proposition63_m9_rich_pointwise_weak_map_witness_from_preparation
      rich richPrepared hCV hrhoSmall hdegree htheta hincidence
      hbroadAbsorb with ⟨witness, pointwiseCubical, hleftFactor, hrightFactor⟩
  let ambient := proposition63_m9_rich_pointwise_extension
    rich witness.data hdeltaOne pointwiseCubical
  let massLoss := proposition63Lemma43MassLoss
    ambient.pointwise.leftFactor ambient.pointwise.rightFactor
  have hmassLossPos : 0 < massLoss :=
    proposition63Lemma43MassLoss_pos _ _
  have hmassLossTop : massLoss ≠ ⊤ :=
    proposition63Lemma43MassLoss_ne_top ambient.pointwise.leftFactor_pos
      ambient.pointwise.rightFactor_ne_top
  have hinverse : massLoss⁻¹ * croppedShading.mass ≤
      ambient.pointwise.shading.mass :=
    proposition63Lemma43MassLoss_inv_mul_le
      ambient.pointwise.leftFactor_pos ambient.pointwise.leftFactor_ne_top
      ambient.pointwise.rightFactor_ne_top ambient.pointwise.mass_retention
  have hextremal : WZ2PaperCroppedIsExtremal sigma targetLoss croppedFamily
      ambient.pointwise.shading := by
    apply transfer_cropped_extremal_to_subshading massLoss
      hmassLossPos hmassLossTop sourceExtremal ambient.pointwise.subshading
      hinverse ambient.cubical hsourceTarget
    · simpa [massLoss, ambient, proposition63_m9_rich_pointwise_extension,
        hleftFactor, hrightFactor, proposition63PaperLemma43MassLoss] using
          hrestore
    · exact sourceExtremal.delta_pos
    · exact sourceExtremal.delta_le_one
    · exact htargetLoss
  let lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := normalizationLoss)
      (targetLoss := targetLoss) croppedShading incidenceBudget := {
    shading := ambient.pointwise.shading
    subshading := ambient.pointwise.subshading
    planeMap := ambient.pointwise.planeMap
    leftFactor := ambient.pointwise.leftFactor
    rightFactor := ambient.pointwise.rightFactor
    leftFactor_pos := ambient.pointwise.leftFactor_pos
    leftFactor_ne_top := ambient.pointwise.leftFactor_ne_top
    rightFactor_ne_top := ambient.pointwise.rightFactor_ne_top
    mass_retention := ambient.pointwise.mass_retention
    cubical := ambient.cubical
    extremal := hextremal }
  refine ⟨{ lemma43 := lemma43, planeMap_vertical_bound := ?_ }⟩
  intro point hpoint
  have hpointInner : point ∈ witness.data.shading.union := by
    change point ∈ (extendShading rich.data.selected
      witness.data.shading).union at hpoint
    simpa only [extendShading_union] using hpoint
  have hrichVertical : ∀ index, Real.sqrt 3 / 2 ≤
      wz1PaperDirection
        (rich.data.selected.family.tube index) (2 : Fin 3) := by
    intro index
    rw [rich.data.selected.tube_eq]
    exact hfamilyVertical (rich.data.selected.embedding index)
  change |witness.data.planeMap.planeMap point (2 : Fin 3)| ≤ 1 / 2
  exact witness.vertical_bound hrichVertical point hpointInner

end Kakeya.Assouad.PureWZ2

end
