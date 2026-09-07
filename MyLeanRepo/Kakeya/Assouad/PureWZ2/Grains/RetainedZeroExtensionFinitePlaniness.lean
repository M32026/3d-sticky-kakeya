import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.StickyZeroExtensionFinitePlaniness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ExtremalTransfer

/-!
# Finite planiness on any quantitatively retained selected shading

This is the general zero-extension entry point used after analytic
Property-Three pullback.  Extremality of the zero-extension is proved from an
explicit source-to-selected mass inequality; nearby CWA remains on the ambient
tube family throughout.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- Variable-`Q` finite planiness before imposing any artificial target on
the incidence error.  The dense and sparse branches carry their actual
incidence scales; Proposition 6.3 only needs to compare that scale with the
later power scale `Delta`. -/
theorem finite_planiness_of_extremal_with_mass_pos_unbounded
    {delta sigma targetLoss densityLoss kappa eta coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal
      sigma targetLoss family shading)
    (hline : WZ1PaperIsLineClass family)
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hsmall : Kakeya.realRpowENN delta targetLoss < 1 / 4)
    (hfixedAbsorb :
      (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * targetLoss))
    (hsparsePackage : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) shading
      (Kakeya.realRpowENN delta (2 - sigma + 3 * targetLoss)),
        Nonempty (SparseRelativeBandCVPackage shading prepared))
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaPositive : 0 < kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (heta : 0 < eta)
    (hetaHalf : eta ≤ 1 / 2)
    (hcoefficient : 0 < coefficient)
    (hactualSmall : ∀ coordinate, coordinate < 1 →
      (extremal.cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < 1 / 8)
    (hparentKappa : ∀ coordinate, coordinate < 1 →
      8 * (extremal.cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < kappa) :
    ∃ data : BalancedFinitePlaninessData
        (coefficient := coefficient) shading,
      0 < data.refinement.shading.mass := by
  rcases high_multiplicity_balanced_direction_dichotomy
      extremal hline hdeltaSmall hdensityLoss htargetLoss hsmall
      hfixedAbsorb with ⟨dichotomy⟩
  rcases high_multiplicity_balanced_weak_finite_lipschitz_coefficient
      extremal.cwa_nearby_scales extremal.nonempty hline
      (by simpa [hdensityLoss] using dichotomy) hsparsePackage
      1 schedule.requested schedule.spatialScale schedule.variationScale
      schedule.K hkappaNonnegative hkappaPositive hkappaHalf
      extremal.delta_pos heta hetaHalf hcoefficient hactualSmall hparentKappa
      schedule.spatial_pos schedule.variation_pos schedule.K_pos
      schedule.spatial_aligned schedule.covers with
    ⟨finite⟩
  let data := finite.toPlaniness extremal.delta_pos
  refine ⟨data, ?_⟩
  exact finite.refinement_mass_pos extremal.delta_pos
    (cropped_extremal_shading_mass_pos extremal hline hdeltaSmall)

/-- Variable-`Q` finite planiness on a shading whose cropped extremality has
already been verified. -/
theorem finite_planiness_of_extremal
    {delta sigma targetLoss densityLoss kappa eta coefficient
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal
      sigma targetLoss family shading)
    (hline : WZ1PaperIsLineClass family)
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hsmall : Kakeya.realRpowENN delta targetLoss < 1 / 4)
    (hfixedAbsorb :
      (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * targetLoss))
    (hsparsePackage : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) shading
      (Kakeya.realRpowENN delta (2 - sigma + 3 * targetLoss)),
        Nonempty (SparseRelativeBandCVPackage shading prepared))
    (hdenseIncidence : eta ≤ incidenceBudget)
    (hsparseIncidence : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) shading
      (Kakeya.realRpowENN delta (2 - sigma + 3 * targetLoss)),
      ∀ package : SparseRelativeBandCVPackage shading prepared,
        package.tau / kappa ≤ incidenceBudget)
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaPositive : 0 < kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (heta : 0 < eta)
    (hetaHalf : eta ≤ 1 / 2)
    (hcoefficient : 0 < coefficient)
    (hactualSmall : ∀ coordinate, coordinate < 1 →
      (extremal.cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < 1 / 8)
    (hparentKappa : ∀ coordinate, coordinate < 1 →
      8 * (extremal.cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < kappa) :
    Nonempty (BoundedBalancedFinitePlaninessData
      (coefficient := coefficient) shading incidenceBudget) := by
  rcases high_multiplicity_balanced_direction_dichotomy
      extremal hline hdeltaSmall hdensityLoss htargetLoss hsmall
      hfixedAbsorb with ⟨dichotomy⟩
  rcases high_multiplicity_balanced_weak_finite_lipschitz_coefficient
      extremal.cwa_nearby_scales extremal.nonempty hline
      (by simpa [hdensityLoss] using dichotomy) hsparsePackage
      1 schedule.requested schedule.spatialScale schedule.variationScale
      schedule.K hkappaNonnegative hkappaPositive hkappaHalf
      extremal.delta_pos heta hetaHalf hcoefficient hactualSmall hparentKappa
      schedule.spatial_pos schedule.variation_pos schedule.K_pos
      schedule.spatial_aligned schedule.covers with
    ⟨finite⟩
  have hincidence : finite.incidence ≤ incidenceBudget := by
    rcases finite.branch_formula with hdense | hsparse
    · rw [hdense.1]
      exact hdenseIncidence
    · rcases hsparse with
        ⟨prepared, package, hincidence, _hleft, _hright⟩
      rw [hincidence]
      exact hsparseIncidence prepared package
  let data := finite.toPlaniness extremal.delta_pos
  exact ⟨{ data := data, incidence_le := hincidence }⟩

/-- The finite-planiness output together with the positive retained mass
needed by aligned exact rebalancing. -/
theorem finite_planiness_of_extremal_with_mass_pos
    {delta sigma targetLoss densityLoss kappa eta coefficient
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal
      sigma targetLoss family shading)
    (hline : WZ1PaperIsLineClass family)
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hsmall : Kakeya.realRpowENN delta targetLoss < 1 / 4)
    (hfixedAbsorb :
      (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * targetLoss))
    (hsparsePackage : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) shading
      (Kakeya.realRpowENN delta (2 - sigma + 3 * targetLoss)),
        Nonempty (SparseRelativeBandCVPackage shading prepared))
    (hdenseIncidence : eta ≤ incidenceBudget)
    (hsparseIncidence : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) shading
      (Kakeya.realRpowENN delta (2 - sigma + 3 * targetLoss)),
      ∀ package : SparseRelativeBandCVPackage shading prepared,
        package.tau / kappa ≤ incidenceBudget)
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaPositive : 0 < kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (heta : 0 < eta)
    (hetaHalf : eta ≤ 1 / 2)
    (hcoefficient : 0 < coefficient)
    (hactualSmall : ∀ coordinate, coordinate < 1 →
      (extremal.cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < 1 / 8)
    (hparentKappa : ∀ coordinate, coordinate < 1 →
      8 * (extremal.cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < kappa) :
    ∃ bounded : BoundedBalancedFinitePlaninessData
        (coefficient := coefficient) shading incidenceBudget,
      0 < bounded.data.refinement.shading.mass := by
  rcases high_multiplicity_balanced_direction_dichotomy
      extremal hline hdeltaSmall hdensityLoss htargetLoss hsmall
      hfixedAbsorb with ⟨dichotomy⟩
  rcases high_multiplicity_balanced_weak_finite_lipschitz_coefficient
      extremal.cwa_nearby_scales extremal.nonempty hline
      (by simpa [hdensityLoss] using dichotomy) hsparsePackage
      1 schedule.requested schedule.spatialScale schedule.variationScale
      schedule.K hkappaNonnegative hkappaPositive hkappaHalf
      extremal.delta_pos heta hetaHalf hcoefficient hactualSmall hparentKappa
      schedule.spatial_pos schedule.variation_pos schedule.K_pos
      schedule.spatial_aligned schedule.covers with
    ⟨finite⟩
  have hincidence : finite.incidence ≤ incidenceBudget := by
    rcases finite.branch_formula with hdense | hsparse
    · rw [hdense.1]
      exact hdenseIncidence
    · rcases hsparse with
        ⟨prepared, package, hincidence, _hleft, _hright⟩
      rw [hincidence]
      exact hsparseIncidence prepared package
  let bounded : BoundedBalancedFinitePlaninessData
      (coefficient := coefficient) shading incidenceBudget :=
    { data := (finite.toPlaniness extremal.delta_pos)
      incidence_le := hincidence }
  refine ⟨bounded, ?_⟩
  exact finite.refinement_mass_pos extremal.delta_pos
    (cropped_extremal_shading_mass_pos extremal hline hdeltaSmall)

/-- Clean variable-`Q` entry point once extremality of the ambient
zero-extension has already been verified. -/
theorem zero_extension_finite_planiness_of_extremal
    {delta sigma targetLoss densityLoss kappa eta coefficient
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {fineShading : WZ1PaperTubeShading selected.family}
    (extremal : WZ2PaperCroppedIsExtremal sigma targetLoss family
      (extendShading selected fineShading))
    (hline : WZ1PaperIsLineClass family)
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hsmall : Kakeya.realRpowENN delta targetLoss < 1 / 4)
    (hfixedAbsorb :
      (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * targetLoss))
    (hsparsePackage : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) (extendShading selected fineShading)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * targetLoss)),
        Nonempty (SparseRelativeBandCVPackage
          (extendShading selected fineShading) prepared))
    (hdenseIncidence : eta ≤ incidenceBudget)
    (hsparseIncidence : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) (extendShading selected fineShading)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * targetLoss)),
      ∀ package : SparseRelativeBandCVPackage
        (extendShading selected fineShading) prepared,
        package.tau / kappa ≤ incidenceBudget)
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaPositive : 0 < kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (heta : 0 < eta)
    (hetaHalf : eta ≤ 1 / 2)
    (hcoefficient : 0 < coefficient)
    (hactualSmall : ∀ coordinate, coordinate < 1 →
      (extremal.cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < 1 / 8)
    (hparentKappa : ∀ coordinate, coordinate < 1 →
      8 * (extremal.cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < kappa) :
    Nonempty (BoundedBalancedFinitePlaninessData
      (coefficient := coefficient) fineShading incidenceBudget) := by
  rcases finite_planiness_of_extremal extremal hline schedule
      hdensityLoss htargetLoss hdeltaSmall hsmall hfixedAbsorb
      hsparsePackage hdenseIncidence hsparseIncidence hkappaNonnegative
      hkappaPositive hkappaHalf heta hetaHalf hcoefficient
      hactualSmall hparentKappa with ⟨bounded⟩
  exact ⟨bounded.restrictZeroExtension selected⟩

/-- Run variable-`Q` finite planiness on a retained selected shading after
zero-extension to its ambient extremal family, then restrict back exactly. -/
theorem retained_zero_extension_finite_planiness
    {delta sigma sourceLoss targetLoss densityLoss kappa eta coefficient
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {fineShading : WZ1PaperTubeShading selected.family}
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss family sourceShading)
    (hline : WZ1PaperIsLineClass family)
    (hsub : ∀ index, fineShading.carrier index ⊆
      sourceShading.carrier (selected.embedding index))
    (hcubical : WZ1PaperIsCubicalShading fineShading)
    (massLoss : ENNReal)
    (hmassLossPos : 0 < massLoss)
    (hmassLossTop : massLoss ≠ ⊤)
    (hmass : massLoss⁻¹ * sourceShading.mass ≤ fineShading.mass)
    (hsourceTarget : sourceLoss ≤ targetLoss)
    (hslack : massLoss * Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta sourceLoss)
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hsmall : Kakeya.realRpowENN delta targetLoss < 1 / 4)
    (hfixedAbsorb :
      (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * targetLoss))
    (hsparsePackage : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) (extendShading selected fineShading)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * targetLoss)),
        Nonempty (SparseRelativeBandCVPackage
          (extendShading selected fineShading) prepared))
    (hdenseIncidence : eta ≤ incidenceBudget)
    (hsparseIncidence : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) (extendShading selected fineShading)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * targetLoss)),
      ∀ package : SparseRelativeBandCVPackage
        (extendShading selected fineShading) prepared,
        package.tau / kappa ≤ incidenceBudget)
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaPositive : 0 < kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (heta : 0 < eta)
    (hetaHalf : eta ≤ 1 / 2)
    (hcoefficient : 0 < coefficient)
    (hactualSmall : ∀ coordinate, coordinate < 1 →
      ((transfer_cropped_extremal_to_subshading massLoss hmassLossPos
          hmassLossTop sourceExtremal
          (fun ambientIndex point hpoint => by
            by_cases himage : ∃ index,
                selected.embedding index = ambientIndex
            · rcases himage with ⟨index, rfl⟩
              rw [extendShading_carrier_mem] at hpoint
              exact hsub index hpoint
            · rw [extendShading_carrier_empty himage] at hpoint
              exact False.elim hpoint)
          (by simpa [extendShading_mass] using hmass)
          (Kakeya.Assouad.extendShading_cubical selected hcubical)
          hsourceTarget hslack sourceExtremal.delta_pos
          sourceExtremal.delta_le_one htargetLoss).cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < 1 / 8)
    (hparentKappa : ∀ coordinate, coordinate < 1 →
      8 * ((transfer_cropped_extremal_to_subshading massLoss hmassLossPos
          hmassLossTop sourceExtremal
          (fun ambientIndex point hpoint => by
            by_cases himage : ∃ index,
                selected.embedding index = ambientIndex
            · rcases himage with ⟨index, rfl⟩
              rw [extendShading_carrier_mem] at hpoint
              exact hsub index hpoint
            · rw [extendShading_carrier_empty himage] at hpoint
              exact False.elim hpoint)
          (by simpa [extendShading_mass] using hmass)
          (Kakeya.Assouad.extendShading_cubical selected hcubical)
          hsourceTarget hslack sourceExtremal.delta_pos
          sourceExtremal.delta_le_one htargetLoss).cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < kappa) :
    Nonempty (BoundedBalancedFinitePlaninessData
      (coefficient := coefficient) fineShading incidenceBudget) := by
  let ambient : WZ1PaperTubeShading family :=
    extendShading selected fineShading
  have hambientSub : PaperIsSubshading ambient sourceShading := by
    intro ambientIndex point hpoint
    by_cases himage : ∃ index, selected.embedding index = ambientIndex
    · rcases himage with ⟨index, rfl⟩
      rw [extendShading_carrier_mem] at hpoint
      exact hsub index hpoint
    · rw [extendShading_carrier_empty himage] at hpoint
      exact False.elim hpoint
  have hambientMass : massLoss⁻¹ * sourceShading.mass ≤ ambient.mass := by
    simpa [ambient, extendShading_mass] using hmass
  let extremal : WZ2PaperCroppedIsExtremal
      sigma targetLoss family ambient :=
    transfer_cropped_extremal_to_subshading massLoss hmassLossPos
      hmassLossTop sourceExtremal hambientSub hambientMass
      (Kakeya.Assouad.extendShading_cubical selected hcubical)
      hsourceTarget hslack sourceExtremal.delta_pos
      sourceExtremal.delta_le_one htargetLoss
  rcases high_multiplicity_balanced_direction_dichotomy
      extremal hline hdeltaSmall hdensityLoss htargetLoss hsmall
      hfixedAbsorb with ⟨dichotomy⟩
  rcases high_multiplicity_balanced_weak_finite_lipschitz_coefficient
      extremal.cwa_nearby_scales extremal.nonempty hline
      (by simpa [hdensityLoss] using dichotomy) hsparsePackage
      1 schedule.requested schedule.spatialScale schedule.variationScale
      schedule.K hkappaNonnegative hkappaPositive hkappaHalf
      sourceExtremal.delta_pos heta hetaHalf hcoefficient
      hactualSmall hparentKappa schedule.spatial_pos schedule.variation_pos
      schedule.K_pos schedule.spatial_aligned schedule.covers with
    ⟨finite⟩
  have hincidence : finite.incidence ≤ incidenceBudget := by
    rcases finite.branch_formula with hdense | hsparse
    · rw [hdense.1]
      exact hdenseIncidence
    · rcases hsparse with
        ⟨prepared, package, hincidence, _hleft, _hright⟩
      rw [hincidence]
      exact hsparseIncidence prepared package
  let bounded : BoundedBalancedFinitePlaninessData
      (coefficient := coefficient) ambient incidenceBudget := {
    data := (finite.toPlaniness sourceExtremal.delta_pos)
    incidence_le := hincidence
  }
  exact ⟨bounded.restrictZeroExtension selected⟩

/-- The retained zero-extension producer together with positive mass of its
actual selected-family output. -/
theorem retained_zero_extension_finite_planiness_with_mass_pos
    {delta sigma sourceLoss targetLoss densityLoss kappa eta coefficient
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {fineShading : WZ1PaperTubeShading selected.family}
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss family sourceShading)
    (hline : WZ1PaperIsLineClass family)
    (hsub : ∀ index, fineShading.carrier index ⊆
      sourceShading.carrier (selected.embedding index))
    (hcubical : WZ1PaperIsCubicalShading fineShading)
    (massLoss : ENNReal)
    (hmassLossPos : 0 < massLoss)
    (hmassLossTop : massLoss ≠ ⊤)
    (hmass : massLoss⁻¹ * sourceShading.mass ≤ fineShading.mass)
    (hsourceTarget : sourceLoss ≤ targetLoss)
    (hslack : massLoss * Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta sourceLoss)
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hsmall : Kakeya.realRpowENN delta targetLoss < 1 / 4)
    (hfixedAbsorb :
      (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * targetLoss))
    (hsparsePackage : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) (extendShading selected fineShading)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * targetLoss)),
        Nonempty (SparseRelativeBandCVPackage
          (extendShading selected fineShading) prepared))
    (hdenseIncidence : eta ≤ incidenceBudget)
    (hsparseIncidence : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) (extendShading selected fineShading)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * targetLoss)),
      ∀ package : SparseRelativeBandCVPackage
        (extendShading selected fineShading) prepared,
        package.tau / kappa ≤ incidenceBudget)
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaPositive : 0 < kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (heta : 0 < eta)
    (hetaHalf : eta ≤ 1 / 2)
    (hcoefficient : 0 < coefficient)
    (hactualSmall : ∀ coordinate, coordinate < 1 →
      ((transfer_cropped_extremal_to_subshading massLoss hmassLossPos
          hmassLossTop sourceExtremal
          (fun ambientIndex point hpoint => by
            by_cases himage : ∃ index,
                selected.embedding index = ambientIndex
            · rcases himage with ⟨index, rfl⟩
              rw [extendShading_carrier_mem] at hpoint
              exact hsub index hpoint
            · rw [extendShading_carrier_empty himage] at hpoint
              exact False.elim hpoint)
          (by simpa [extendShading_mass] using hmass)
          (Kakeya.Assouad.extendShading_cubical selected hcubical)
          hsourceTarget hslack sourceExtremal.delta_pos
          sourceExtremal.delta_le_one htargetLoss).cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < 1 / 8)
    (hparentKappa : ∀ coordinate, coordinate < 1 →
      8 * ((transfer_cropped_extremal_to_subshading massLoss hmassLossPos
          hmassLossTop sourceExtremal
          (fun ambientIndex point hpoint => by
            by_cases himage : ∃ index,
                selected.embedding index = ambientIndex
            · rcases himage with ⟨index, rfl⟩
              rw [extendShading_carrier_mem] at hpoint
              exact hsub index hpoint
            · rw [extendShading_carrier_empty himage] at hpoint
              exact False.elim hpoint)
          (by simpa [extendShading_mass] using hmass)
          (Kakeya.Assouad.extendShading_cubical selected hcubical)
          hsourceTarget hslack sourceExtremal.delta_pos
          sourceExtremal.delta_le_one htargetLoss).cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < kappa) :
    ∃ bounded : BoundedBalancedFinitePlaninessData
        (coefficient := coefficient) fineShading incidenceBudget,
      0 < bounded.data.refinement.shading.mass := by
  let ambient : WZ1PaperTubeShading family :=
    extendShading selected fineShading
  have hambientSub : PaperIsSubshading ambient sourceShading := by
    intro ambientIndex point hpoint
    by_cases himage : ∃ index, selected.embedding index = ambientIndex
    · rcases himage with ⟨index, rfl⟩
      rw [extendShading_carrier_mem] at hpoint
      exact hsub index hpoint
    · rw [extendShading_carrier_empty himage] at hpoint
      exact False.elim hpoint
  have hambientMass : massLoss⁻¹ * sourceShading.mass ≤ ambient.mass := by
    simpa [ambient, extendShading_mass] using hmass
  let extremal : WZ2PaperCroppedIsExtremal
      sigma targetLoss family ambient :=
    transfer_cropped_extremal_to_subshading massLoss hmassLossPos
      hmassLossTop sourceExtremal hambientSub hambientMass
      (Kakeya.Assouad.extendShading_cubical selected hcubical)
      hsourceTarget hslack sourceExtremal.delta_pos
      sourceExtremal.delta_le_one htargetLoss
  rcases finite_planiness_of_extremal_with_mass_pos extremal hline schedule
      hdensityLoss htargetLoss hdeltaSmall hsmall hfixedAbsorb
      hsparsePackage hdenseIncidence hsparseIncidence hkappaNonnegative
      hkappaPositive hkappaHalf heta hetaHalf hcoefficient
      hactualSmall hparentKappa with ⟨ambientBounded, hambientPositive⟩
  let bounded := ambientBounded.restrictZeroExtension selected
  refine ⟨bounded, ?_⟩
  rw [show bounded.data.refinement.shading.mass =
      ambientBounded.data.refinement.shading.mass by
    exact ambientBounded.data.refinement.restrictZeroExtension_mass selected]
  exact hambientPositive

end Kakeya.Assouad.PureWZ2

end
