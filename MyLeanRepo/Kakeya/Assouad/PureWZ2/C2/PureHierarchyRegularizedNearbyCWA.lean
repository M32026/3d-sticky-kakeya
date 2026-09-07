import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05SynchronizedPostGrainExtremality
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ExtremalSpatialCellCWAProducer
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureCWAReindex

/-!
# Synchronized post-grain selection with nearby CWA

The post-grain core must already be regular at the nearby CWA parent maps.
This module performs simultaneous weighted degree regularization directly on
the ordinary/cropped overlap weights and repackages the exact selected indices
as the synchronized core.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- One synchronized post-grain core whose exact selected family already has
the requested nearby-CWA certificate. -/
structure PureWZ2Node05RegularizedPostGrainCore
    {delta sigma sourceLoss normalizationLoss grainLoss outputEta : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    (coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent)
    (ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss)
    (coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss)
    (croppedMassFraction outputConstant : ENNReal)
    (epsilon : ℝ) where
  core : PureWZ2Node05SynchronizedPostGrainCore
    coarseRefinement ancestor coarseGrains outputEta croppedMassFraction
  retentionLoss_eq : core.retentionLoss =
    pureWZ2SpatialCellRegularizationLoss epsilon
      coarseRefinement.selected.family.card
  nearby : WZ2PaperPureCWAAtNearbyScales
    (pureWZ2Node05PostGrainSelectedSubfamily
      coarseRefinement.selected.family core.retained).family
    outputConstant

/-- Simultaneous nearby-parent regularization on the exact post-grain overlap.
The same finite selection supplies nearby CWA, cardinality retention, both mass
ledgers, and the pointwise ordinary-overlap lower bound. -/
theorem exists_pureWZ2Node05RegularizedPostGrainCore
    {delta sigma sourceLoss normalizationLoss grainLoss
      inputEta outputEta epsilon : ℝ}
    {ambientConstant : ENNReal}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    (coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent)
    (ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss)
    (coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss)
    (croppedMassFraction outputConstant : ENNReal)
    (ambient : WZ2PaperPureCWAAtNearbyScales
      coarseRefinement.selected.family
      ambientConstant)
    (hdeltaSmall : delta ≤ 1 / 12)
    (densitySeparation :
      Kakeya.realRpowENN delta outputEta ≤
        (1 / 2 : ENNReal) * Kakeya.realRpowENN delta inputEta)
    (inputDensityAbsorption :
      Kakeya.realRpowENN delta inputEta ≤
        (100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          Kakeya.realRpowENN delta grainLoss)
    (croppedMassAbsorption :
      croppedMassFraction ≤
        (100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity)
    (epsilon_pos : 0 < epsilon)
    (delta_lt_one : delta < 1)
    (output_ne_top : outputConstant ≠ ⊤)
    (roundingAbsorption :
      ENNReal.ofReal (Real.rpow delta (-epsilon)) *
          ambientConstant ≤
        outputConstant)
    (restrictionAbsorption :
      wz2PaperPureNearbyRestrictionConstant
          ambientConstant
          (Kakeya.realRpowENN delta inputEta *
            Kakeya.deltaTubeVolume delta)
          (pureWZ2SpatialCellDegreeConstant epsilon
            coarseRefinement.selected.family.card)
          (pureWZ2SpatialCellRegularizationLoss epsilon
              coarseRefinement.selected.family.card *
            Kakeya.deltaTubeVolume delta) ≤
        outputConstant)
    (cardinalityAbsorption :
      Kakeya.realRpowENN delta outputEta *
          pureWZ2SpatialCellRegularizationLoss epsilon
            coarseRefinement.selected.family.card ≤
        Kakeya.realRpowENN delta inputEta) :
    Nonempty (PureWZ2Node05RegularizedPostGrainCore (outputEta := outputEta)
      coarseRefinement ancestor coarseGrains croppedMassFraction
      outputConstant epsilon) := by
  let family := coarseRefinement.selected.family
  let overlap := pureWZ2Node05PostGrainOverlapShading
    coarseRefinement ancestor coarseGrains
  let tubeVolume := Kakeya.deltaTubeVolume delta
  let normalizationWeight :=
    Kakeya.realRpowENN delta inputEta * tubeVolume
  let preSelected : WZ2PaperPureTubeSubfamily family :=
    { family := family
      embedding := Function.Embedding.refl _
      tube_eq := fun _ => rfl }
  let externalWeight : Fin family.card → ENNReal :=
    fun index => volume (overlap.carrier index)
  have familyNonempty : family.Nonempty :=
    ancestor.cropped_extremal.nonempty
  have tubeVolumePos : 0 < tubeVolume :=
    (tube_volume_scaling.2.1 delta ancestor.cropped_extremal.delta_pos
      ancestor.cropped_extremal.delta_le_one).1
  have tubeVolumeTop : tubeVolume ≠ ⊤ :=
    (tube_volume_scaling.2.1 delta ancestor.cropped_extremal.delta_pos
      ancestor.cropped_extremal.delta_le_one).2
  have overlapDense : overlap.IsLambdaDense
      ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
        Kakeya.realRpowENN delta grainLoss) :=
    pureWZ2Node05PostGrainOverlap_dense
      coarseRefinement ancestor coarseGrains hdeltaSmall
  have inputDensityLe : Kakeya.realRpowENN delta inputEta ≤
      (100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
        Kakeya.realRpowENN delta grainLoss := inputDensityAbsorption
  have inputDense : overlap.IsLambdaDense
      (Kakeya.realRpowENN delta inputEta) := by
    calc
      Kakeya.realRpowENN delta inputEta * family.toBodyFamily.mass ≤
          ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
            Kakeya.realRpowENN delta grainLoss) * family.toBodyFamily.mass := by
        gcongr
      _ ≤ overlap.mass := overlapDense
  have totalWeight :
      (∑ index : Fin preSelected.family.card, externalWeight index) =
        overlap.mass := rfl
  have familyMass : family.toBodyFamily.mass =
      family.enncard * tubeVolume := by
    rw [tubeFamily_mass_eq_nominal]
    rfl
  have totalWeightLower :
      normalizationWeight * family.enncard ≤
        ∑ index : Fin preSelected.family.card, externalWeight index := by
    rw [totalWeight]
    change (Kakeya.realRpowENN delta inputEta * tubeVolume) *
        family.enncard ≤ overlap.mass
    calc
      (Kakeya.realRpowENN delta inputEta * tubeVolume) *
          family.enncard =
        Kakeya.realRpowENN delta inputEta * family.toBodyFamily.mass := by
          rw [familyMass]
          ring
      _ ≤ overlap.mass := inputDense
  have weightUpper : ∀ index, externalWeight index ≤ tubeVolume := by
    intro index
    calc
      externalWeight index ≤ volume (family.tube index).carrier :=
        measure_mono (overlap.subset_body index)
      _ = tubeVolume := tube_volume_scaling.1 delta (family.tube index)
  have normalizationZero : normalizationWeight ≠ 0 :=
    mul_ne_zero
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos ancestor.cropped_extremal.delta_pos inputEta)).ne'
      tubeVolumePos.ne'
  have normalizationTop : normalizationWeight ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN]) tubeVolumeTop
  have restrictionAbsorption' :
      wz2PaperPureNearbyRestrictionConstant
          ambientConstant
          normalizationWeight
          (pureWZ2SpatialCellDegreeConstant epsilon family.card)
          (pureWZ2SpatialCellRegularizationLoss epsilon family.card *
            tubeVolume) ≤ outputConstant := by
    simpa [family, tubeVolume, normalizationWeight] using restrictionAbsorption
  rcases pureWZ2_weighted_restricted_cwa_actual
      ambient preSelected familyNonempty externalWeight
      normalizationWeight tubeVolume normalizationZero normalizationTop
      tubeVolumeTop totalWeightLower weightUpper epsilon epsilon_pos ambient.1
      delta_lt_one output_ne_top roundingAbsorption restrictionAbsorption' with
    ⟨selectedPre, selectedNonempty, ⟨selectedIndices, selectedPreEq⟩,
      retainedWeight, selectedWeightFloor, selectedNearby⟩
  subst selectedPre
  let selectedPre := WZ2PaperPureTubeSubfamily.fromFinset
    preSelected.family selectedIndices
  let selected := WZ2PaperPureTubeSubfamily.comp preSelected selectedPre
  let regularizationLoss :=
    pureWZ2SpatialCellRegularizationLoss epsilon family.card
  have regularizationZero : regularizationLoss ≠ 0 := by
    dsimp only [regularizationLoss, pureWZ2SpatialCellRegularizationLoss]
    positivity
  have regularizationTop : regularizationLoss ≠ ⊤ := by
    dsimp only [regularizationLoss, pureWZ2SpatialCellRegularizationLoss]
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (by simp))
  let selectedTube := pureWZ2Node05PostGrainSelectedSubfamily
    family selectedIndices
  have selectedIndicesNonempty : selectedIndices.Nonempty := by
    exact Finset.card_pos.mp selectedNonempty
  let selectedEquiv : Fin selectedTube.family.card ≃
      Fin (WZ2PaperPureTubeSubfamily.comp preSelected
        (WZ2PaperPureTubeSubfamily.fromFinset
          preSelected.family selectedIndices)).family.card :=
    selectedIndices.equivFin.symm.trans
      (selectedIndices.orderIsoOfFin rfl).symm.toEquiv
  have selectedTubeEq : ∀ index : Fin selectedTube.family.card,
      selectedTube.family.tube index =
        (WZ2PaperPureTubeSubfamily.comp preSelected
          (WZ2PaperPureTubeSubfamily.fromFinset
            preSelected.family selectedIndices)).family.tube
              (selectedEquiv index) := by
    intro index
    change family.tube ((selectedIndices.equivFin.symm index).1) =
      family.tube
        (selectedIndices.orderEmbOfFin rfl (selectedEquiv index))
    congr 1
    exact (congrArg Subtype.val <|
      (selectedIndices.orderIsoOfFin rfl).apply_symm_apply
        (selectedIndices.equivFin.symm index)).symm
  have selectedNearby' : WZ2PaperPureCWAAtNearbyScales
      selectedTube.family outputConstant :=
    selectedNearby.reindex selectedEquiv selectedTubeEq
  have selectedWeightSum :
      (∑ index : Fin selectedPre.family.card,
          externalWeight (selectedPre.embedding index)) =
        (selectedTubeShading overlap selectedIndices).mass := by
    let equivalence : Fin selectedIndices.card ≃ selectedIndices :=
      (selectedIndices.orderIsoOfFin rfl).toEquiv
    calc
      (∑ index : Fin selectedIndices.card,
          externalWeight
            ((WZ2PaperPureTubeSubfamily.fromFinset family
              selectedIndices).embedding index)) =
        ∑ index : selectedIndices, externalWeight index.1 := by
          exact Fintype.sum_equiv equivalence
            (fun index : Fin selectedIndices.card =>
              externalWeight
                ((WZ2PaperPureTubeSubfamily.fromFinset family
                  selectedIndices).embedding index))
            (fun index : selectedIndices => externalWeight index.1)
            (fun _ => rfl)
      _ = ∑ index ∈ selectedIndices, externalWeight index := by
        exact Finset.sum_coe_sort selectedIndices externalWeight
      _ = (selectedTubeShading overlap selectedIndices).mass := by
        rw [selectedTubeShading_mass]
  have overlapRetention : overlap.mass ≤
      regularizationLoss *
        (selectedTubeShading overlap selectedIndices).mass := by
    rw [← totalWeight, ← selectedWeightSum]
    exact retainedWeight
  have selectedCardinality' :
      Kakeya.realRpowENN delta outputEta * family.enncard ≤
        selectedTube.family.enncard := by
    have selectedWeightUpper :
        (∑ index : Fin selectedPre.family.card,
          externalWeight (selectedPre.embedding index)) ≤
      (WZ2PaperPureTubeSubfamily.comp preSelected
        (WZ2PaperPureTubeSubfamily.fromFinset
          preSelected.family selectedIndices)).family.enncard *
            tubeVolume := by
      change (∑ index : Fin selectedPre.family.card,
          externalWeight (selectedPre.embedding index)) ≤
        (selectedPre.family.card : ENNReal) * tubeVolume
      calc
        (∑ index : Fin selectedPre.family.card,
            externalWeight (selectedPre.embedding index)) ≤
          ∑ _index : Fin selectedPre.family.card, tubeVolume := by
            exact Finset.sum_le_sum fun index _ =>
              weightUpper (selectedPre.embedding index)
        _ = (selectedPre.family.card : ENNReal) * tubeVolume := by
          simp [Finset.sum_const]
    have selectedCardinalityRaw :
        normalizationWeight * family.enncard ≤
          (regularizationLoss * tubeVolume) *
            (WZ2PaperPureTubeSubfamily.comp preSelected
              (WZ2PaperPureTubeSubfamily.fromFinset
                preSelected.family selectedIndices)).family.enncard := by
      calc
        normalizationWeight * family.enncard ≤
          ∑ index : Fin preSelected.family.card, externalWeight index :=
            totalWeightLower
        _ ≤ regularizationLoss *
          ∑ index : Fin selectedPre.family.card,
            externalWeight (selectedPre.embedding index) := retainedWeight
        _ ≤ regularizationLoss * (selected.family.enncard * tubeVolume) := by
          gcongr
        _ = (regularizationLoss * tubeVolume) * selected.family.enncard := by
          ring
    have inputCardinality :
        Kakeya.realRpowENN delta inputEta * family.enncard ≤
          regularizationLoss *
            (WZ2PaperPureTubeSubfamily.comp preSelected
              (WZ2PaperPureTubeSubfamily.fromFinset
                preSelected.family selectedIndices)).family.enncard := by
      apply (ENNReal.mul_le_mul_iff_left tubeVolumePos.ne' tubeVolumeTop).mp
      simpa [normalizationWeight, mul_comm, mul_left_comm, mul_assoc] using
        selectedCardinalityRaw
    have scaled : regularizationLoss *
        (Kakeya.realRpowENN delta outputEta * family.enncard) ≤
      regularizationLoss *
        (WZ2PaperPureTubeSubfamily.comp preSelected
          (WZ2PaperPureTubeSubfamily.fromFinset
            preSelected.family selectedIndices)).family.enncard := by
      calc
        regularizationLoss *
            (Kakeya.realRpowENN delta outputEta * family.enncard) =
          (Kakeya.realRpowENN delta outputEta * regularizationLoss) *
            family.enncard := by ring
        _ ≤ Kakeya.realRpowENN delta inputEta * family.enncard := by gcongr
        _ ≤ regularizationLoss * selected.family.enncard := inputCardinality
    have final : Kakeya.realRpowENN delta outputEta * family.enncard ≤
        (WZ2PaperPureTubeSubfamily.comp preSelected
          (WZ2PaperPureTubeSubfamily.fromFinset
            preSelected.family selectedIndices)).family.enncard :=
      (ENNReal.mul_le_mul_iff_left regularizationZero regularizationTop).mp <| by
        simpa [mul_comm] using scaled
    have selectedENNCardEq : selectedTube.family.enncard =
        selected.family.enncard := by
      change (selectedIndices.card : ENNReal) = (selectedIndices.card : ENNReal)
      rfl
    rw [selectedENNCardEq]
    exact final
  have averageFloor :
      (Kakeya.realRpowENN delta inputEta / 2) * tubeVolume ≤
        overlap.mass / (2 * family.card : ENNReal) := by
    apply (ENNReal.le_div_iff_mul_le
      (by
        have familyCardPos : 0 < family.card := familyNonempty
        exact Or.inl <| mul_ne_zero (by norm_num)
          (by exact_mod_cast familyCardPos.ne'))
      (Or.inl <| ENNReal.mul_ne_top (by norm_num) (by simp))).2
    calc
      (Kakeya.realRpowENN delta inputEta / 2 * tubeVolume) *
          (2 * (family.card : ENNReal)) =
        Kakeya.realRpowENN delta inputEta * family.toBodyFamily.mass := by
          rw [familyMass]
          change
            (Kakeya.realRpowENN delta inputEta * (2 : ENNReal)⁻¹ *
                tubeVolume) * (2 * family.enncard) =
              Kakeya.realRpowENN delta inputEta *
                (family.enncard * tubeVolume)
          calc
            (Kakeya.realRpowENN delta inputEta * (2 : ENNReal)⁻¹ *
                tubeVolume) * (2 * family.enncard) =
              Kakeya.realRpowENN delta inputEta *
                ((2 : ENNReal)⁻¹ * 2) *
                (family.enncard * tubeVolume) := by ring
            _ = Kakeya.realRpowENN delta inputEta *
                (family.enncard * tubeVolume) := by
              rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
              rw [mul_one]
      _ ≤ overlap.mass := inputDense
  have selectedPerTube : ∀ index : Fin selectedTube.family.card,
      Kakeya.realRpowENN delta outputEta *
          (selectedTube.family.tube index).volume ≤
        volume ((selectedTubeShading overlap selectedIndices).carrier index) := by
    intro index
    let target := selectedEquiv index
    have floor := selectedWeightFloor target
    have ambientIndexEq : selectedTube.embedding index =
        selectedPre.embedding target := by
      change (selectedIndices.equivFin.symm index).1 =
        selectedIndices.orderEmbOfFin rfl target
      exact (congrArg Subtype.val <|
        (selectedIndices.orderIsoOfFin rfl).apply_symm_apply
          (selectedIndices.equivFin.symm index)).symm
    calc
      Kakeya.realRpowENN delta outputEta *
          (selectedTube.family.tube index).volume =
        Kakeya.realRpowENN delta outputEta * tubeVolume := by
          rw [tube_volume_scaling.1 delta]
      _ ≤ (Kakeya.realRpowENN delta inputEta / 2) * tubeVolume := by
        gcongr
        simpa [div_eq_mul_inv, mul_comm] using densitySeparation
      _ ≤ overlap.mass / (2 * family.card : ENNReal) := averageFloor
      _ = (∑ source : Fin preSelected.family.card, externalWeight source) /
          (2 * preSelected.family.card : ENNReal) := by
            rw [totalWeight]
      _ ≤ externalWeight (selectedPre.embedding target) := floor
      _ = volume ((selectedTubeShading overlap selectedIndices).carrier index) := by
        change volume (overlap.carrier (selectedPre.embedding target)) =
          volume (overlap.carrier (selectedTube.embedding index))
        exact congrArg (fun ambientIndex =>
          volume (overlap.carrier ambientIndex)) ambientIndexEq.symm
  have croppedDemand :
      croppedMassFraction * coarseGrains.shading.mass ≤ overlap.mass :=
    (mul_le_mul_left croppedMassAbsorption
      coarseGrains.shading.mass).trans
        (pureWZ2Node05PostGrainOverlap_cropped_mass_lower
          coarseRefinement ancestor coarseGrains)
  have selectedOverlapLeCropped :
      (selectedTubeShading overlap selectedIndices).mass ≤
        (restrictPaperShading selectedTube coarseGrains.shading).mass := by
    change (∑ index : Fin selectedTube.family.card,
      volume (overlap.carrier (selectedTube.embedding index))) ≤
      ∑ index : Fin selectedTube.family.card,
        volume (coarseGrains.shading.carrier (selectedTube.embedding index))
    exact Finset.sum_le_sum fun index _ =>
      measure_mono Set.inter_subset_right
  have croppedRetention :
      croppedMassFraction * coarseGrains.shading.mass ≤
        regularizationLoss *
          (restrictPaperShading selectedTube coarseGrains.shading).mass :=
    croppedDemand.trans <| overlapRetention.trans <| by gcongr
  let core : PureWZ2Node05SynchronizedPostGrainCore
      coarseRefinement ancestor coarseGrains outputEta croppedMassFraction :=
    { retained := selectedIndices
      retained_nonempty := selectedIndicesNonempty
      retentionLoss := regularizationLoss
      retentionLoss_ne_zero := by
        exact regularizationZero
      retentionLoss_ne_top := regularizationTop
      cardinality_retention := selectedCardinality'
      overlap_mass_retention := overlapRetention
      cropped_mass_retention := croppedRetention
      ordinary_overlap_per_tube := selectedPerTube }
  exact ⟨⟨core, rfl, selectedNearby'⟩⟩

end Kakeya.Assouad

end
