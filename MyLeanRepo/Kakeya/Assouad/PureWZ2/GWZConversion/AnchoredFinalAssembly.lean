import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AnchoredSchedule
import MyLeanRepo.Kakeya.Streamlined.Targets.StickyImpliesGeneral

/-!
# Final corrected GWZ-to-WZ2 conversion

This is the quantitative assembly of the localized coaxial route.  It uses
only complete GWZ full fibers, one finite reference-scale list, and one
simultaneous weighted selection.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

private theorem pureWZ2_fixed_support_shading_finite
    {delta R : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceSupport : PureWZ2FixedBallSupport source R)
    (shading : Kakeya.Streamlined.TubeShading source) :
    shading.mass ≠ ⊤ := by
  have hcarrier :
      ∀ index : Fin source.card,
        volume (shading.carrier index) ≠ ⊤ := by
    intro index
    have hsubset :
        shading.carrier index ⊆
          Metric.closedBall (0 : Point3) R :=
      (shading.subset_body index).trans
        (sourceSupport index)
    exact
      ne_top_of_le_ne_top
        MeasureTheory.measure_closedBall_lt_top.ne
        (measure_mono hsubset)
  dsimp only [Kakeya.Streamlined.Shading.mass]
  exact ENNReal.sum_ne_top.mpr fun index _ =>
    hcarrier index

private theorem pureWZ2_nonempty_family_mass_pos
    {delta : ℝ}
    (hdelta : 0 < delta)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (familyNonempty : family.Nonempty) :
    0 < family.toBodyFamily.mass := by
  have hvolume :
      0 < Kakeya.deltaTubeVolume delta := by
    let index : Fin family.card :=
      ⟨0, familyNonempty⟩
    have hlower :=
      tube_volume_lower_pi hdelta (family.tube index)
    rw [tube_volume_scaling.1 delta (family.tube index)] at hlower
    exact
      (ENNReal.ofReal_pos.mpr
        (by positivity :
          0 < Real.pi * delta ^ 2)).trans_le hlower
  rw [Kakeya.Streamlined.family_mass_eq_nominal]
  exact
    ENNReal.mul_pos
      (by
        change (family.card : ENNReal) ≠ 0
        exact_mod_cast familyNonempty.ne')
      hvolume.ne'

private theorem pureWZ2_reanchored_family_mass_le_source
    {delta : ℝ}
    {source reanchored :
      Kakeya.Streamlined.TubeFamily delta}
    (sourceIndex : Fin reanchored.card ↪ Fin source.card) :
    reanchored.toBodyFamily.mass ≤
      source.toBodyFamily.mass := by
  rw [Kakeya.Streamlined.family_mass_eq_nominal,
    Kakeya.Streamlined.family_mass_eq_nominal]
  apply mul_le_mul_right'
  change (reanchored.card : ENNReal) ≤
    (source.card : ENNReal)
  have hcard :
      reanchored.card ≤ source.card := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective
        sourceIndex sourceIndex.injective
  exact_mod_cast
    hcard

private theorem pureWZ2_card_log_of_embedding
    {delta R : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hdeltaSmall : delta < 1 / 16)
    (hR : 1 ≤ R)
    {source reanchored :
      Kakeya.Streamlined.TubeFamily delta}
    (sourceNonempty : source.Nonempty)
    (sourceSupport : PureWZ2FixedBallSupport source R)
    (sourceDistinct : source.IsEssentiallyDistinct)
    (sourceIndex : Fin reanchored.card ↪ Fin source.card) :
    (Nat.log 2 (2 * reanchored.card) + 1 : ℝ) ≤
      pureWZ2FixedBallCardLogConstant R *
        (1 + Real.log delta⁻¹) := by
  have hsource :=
    pureWZ2_fixed_ball_card_log_bound
      hdelta hdeltaOne hdeltaSmall hR
      sourceNonempty sourceSupport sourceDistinct
  have hcard :
      reanchored.card ≤ source.card := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective
        sourceIndex sourceIndex.injective
  have hdouble :
      2 * reanchored.card ≤ 2 * source.card :=
    Nat.mul_le_mul_left 2 hcard
  have hlog :
      Nat.log 2 (2 * reanchored.card) ≤
        Nat.log 2 (2 * source.card) :=
    Nat.log_mono_right hdouble
  have hlogReal :
      (Nat.log 2 (2 * reanchored.card) + 1 : ℝ) ≤
        (Nat.log 2 (2 * source.card) + 1 : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hlog 1
  exact hlogReal.trans hsource

private theorem pureWZ2_raw_mass_to_refinement
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta < 1)
    (logExponent : ℕ)
    {sourceMass selectedMass rawLoss : ENNReal}
    (hraw :
      sourceMass ≤ rawLoss * selectedMass)
    (hloss :
      rawLoss ≤
        (ENNReal.ofReal
          (Real.log (1 / delta))) ^ logExponent) :
    wz2PaperPureRefinementFraction delta logExponent *
        sourceMass ≤
      selectedMass := by
  let logBase : ENNReal :=
    ENNReal.ofReal (Real.log (1 / delta))
  have hlogPos :
      0 < Real.log (1 / delta) := by
    exact Real.log_pos
      (one_lt_one_div hdelta hdeltaOne)
  have hlogZero : logBase ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hlogPos).ne'
  have hlogTop : logBase ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hpowerZero :
      logBase ^ logExponent ≠ 0 :=
    pow_ne_zero _ hlogZero
  have hpowerTop :
      logBase ^ logExponent ≠ ⊤ :=
    ENNReal.pow_ne_top hlogTop
  calc
    wz2PaperPureRefinementFraction delta logExponent *
          sourceMass
        ≤
      wz2PaperPureRefinementFraction delta logExponent *
          (rawLoss * selectedMass) :=
      mul_le_mul_left' hraw _
    _ ≤
      wz2PaperPureRefinementFraction delta logExponent *
          (logBase ^ logExponent * selectedMass) := by
      exact mul_le_mul_left'
        (mul_le_mul_right' hloss selectedMass) _
    _ = selectedMass := by
      have hfraction :
          wz2PaperPureRefinementFraction
              delta logExponent =
            (logBase ^ logExponent)⁻¹ := by
        dsimp only [wz2PaperPureRefinementFraction,
          logBase]
        rw [ENNReal.inv_pow]
      rw [hfraction]
      rw [show
        (logBase ^ logExponent)⁻¹ *
              (logBase ^ logExponent * selectedMass) =
            ((logBase ^ logExponent)⁻¹ *
              logBase ^ logExponent) * selectedMass by
        ring]
      rw [ENNReal.inv_mul_cancel
        hpowerZero hpowerTop, one_mul]

private theorem pureWZ2_actual_constants_le_fixed
    {delta A R radius : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading :
      Kakeya.Streamlined.TubeShading source}
    (fine :
      PureWZ2LocalizedDistinctReanchoringData
        sourceShading)
    (hcell :
      fine.cellCount =
        pureWZ2LocalizationCellCount R radius)
    (coordinateCount familyCard : ℕ)
    (density inputConstant : ENNReal) :
    let selectionRetention :=
      pureWZ2FiniteAnchoredRetentionConstant
        A coordinateCount familyCard
    let degreeConstant :=
      pureWZ2FiniteAnchoredDegreeConstant
        coordinateCount familyCard
    let actualGlobal :=
      pureWZ2ReanchoredGlobalRetentionConstant
        density fine.cellCount fine.distinctnessLoss
          selectionRetention
    let fixedGlobal :=
      pureWZ2ReanchoredGlobalRetentionConstant
        density
        (pureWZ2LocalizationCellCount R radius)
        pureWZ2ReanchoredPaperConflictLossBound
        selectionRetention
    let actualFiber :=
      pureWZ2ReanchoredFiberRatioConstant
        inputConstant
        (pureWZ2CompleteFiberOverlapBound A)
        actualGlobal degreeConstant
    let fixedFiber :=
      pureWZ2ReanchoredFiberRatioConstant
        inputConstant
        (pureWZ2CompleteFiberOverlapBound A)
        fixedGlobal degreeConstant
    pureWZ2AnchoredReferenceScaleConstant
        degreeConstant inputConstant actualFiber ≤
      pureWZ2AnchoredReferenceScaleConstant
        degreeConstant inputConstant fixedFiber ∧
    pureWZ2TopScaleConstant
        inputConstant
        (pureWZ2UnitScaleCompleteFiberOverlapBound A)
        actualGlobal ≤
      pureWZ2TopScaleConstant
        inputConstant
        (pureWZ2UnitScaleCompleteFiberOverlapBound A)
        fixedGlobal ∧
    ((fine.cellCount : ENNReal) *
        (fine.distinctnessLoss : ENNReal) *
        selectionRetention) ≤
      ((pureWZ2LocalizationCellCount R radius : ENNReal) *
        (pureWZ2ReanchoredPaperConflictLossBound : ENNReal) *
        selectionRetention) := by
  dsimp only
  have hcellENN :
      (fine.cellCount : ENNReal) =
        (pureWZ2LocalizationCellCount R radius :
          ENNReal) := by
    exact_mod_cast hcell
  have hdistinctENN :
      (fine.distinctnessLoss : ENNReal) ≤
        (pureWZ2ReanchoredPaperConflictLossBound :
          ENNReal) := by
    exact_mod_cast fine.distinctnessLoss_le
  have hglobal :
      pureWZ2ReanchoredGlobalRetentionConstant
          density fine.cellCount fine.distinctnessLoss
          (pureWZ2FiniteAnchoredRetentionConstant
            A coordinateCount familyCard) ≤
        pureWZ2ReanchoredGlobalRetentionConstant
          density
          (pureWZ2LocalizationCellCount R radius)
          pureWZ2ReanchoredPaperConflictLossBound
          (pureWZ2FiniteAnchoredRetentionConstant
            A coordinateCount familyCard) := by
    dsimp only [pureWZ2ReanchoredGlobalRetentionConstant]
    rw [hcellENN]
    gcongr
  constructor
  · dsimp only [pureWZ2AnchoredReferenceScaleConstant,
      pureWZ2ReanchoredStrictFrostmanConstant,
      pureWZ2ReanchoredFiberRatioConstant]
    gcongr
  constructor
  · dsimp only [pureWZ2TopScaleConstant,
      pureWZ2UnitScaleAggregateFrostmanConstant]
    gcongr
  · rw [hcellENN]
    exact mul_le_mul_right'
      (mul_le_mul_left' hdistinctENN _) _

/-- The corrected Node 9 conversion theorem. -/
theorem pureWZ2_anchored_final_conversion :
    PureWZ2GWZReanchoredConversionStatement := by
  intro A R hA hR outputLoss houtputLoss
  let radius : ℝ := 1 / 8
  let coordinateCount :=
    pureWZ2AnchoredCoordinateCount outputLoss
  rcases
      pureWZ2_anchored_coordinate_count houtputLoss with
    ⟨hcoordinateCount, hcoordinateLoss⟩
  let logExponent := coordinateCount + 2
  let inputLoss := outputLoss / 4
  have hinputLoss : 0 < inputLoss := by
    dsimp only [inputLoss]
    linarith
  have hinputOutput : inputLoss < outputLoss := by
    dsimp only [inputLoss]
    linarith
  have htriple :
      3 * inputLoss < outputLoss := by
    dsimp only [inputLoss]
    linarith
  rcases
      pureWZ2_anchored_absorption
        A R radius outputLoss inputLoss
        hA hR (by norm_num) houtputLoss hinputLoss
        htriple coordinateCount hcoordinateCount with
    ⟨deltaAbsorb, hdeltaAbsorb,
      hdeltaAbsorbOne, habsorb⟩
  rcases
      gwz_exponent_inequality_of_inputLoss
        (1 : ENNReal) (by norm_num)
        outputLoss inputLoss hinputLoss hinputOutput
        logExponent with
    ⟨deltaDensity, hdeltaDensity,
      hdeltaDensityOne, hdensityAbsorb⟩
  let radiusConstant : ENNReal :=
    ENNReal.ofReal (8 * A + 1)
  rcases
      exists_delta_realRpowENN_bound
        radiusConstant ENNReal.ofReal_ne_top
        houtputLoss with
    ⟨deltaRadius, hdeltaRadius,
      hdeltaRadiusOne, hradiusAbsorb⟩
  let deltaSchedule :=
    pureWZ2AnchoredScheduleThreshold
      A coordinateCount
  have hdeltaSchedule : 0 < deltaSchedule := by
    dsimp only [deltaSchedule,
      pureWZ2AnchoredScheduleThreshold]
    exact Real.rpow_pos_of_pos (by positivity) _
  let delta₀ :=
    min (1 / 200)
      (min deltaAbsorb
        (min deltaDensity
          (min deltaRadius deltaSchedule)))
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans (by norm_num)
  refine
    ⟨logExponent, inputLoss, delta₀,
      hinputLoss, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaSmall source
    sourceNonempty sourceSupport sourceDistinct
    fullFiberData sourceShading sourceDense
  have hdelta200 : delta ≤ 1 / 200 :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaOne : delta ≤ 1 :=
    hdeltaSmall.trans hdelta₀One
  have hdeltaStrict : delta < 1 := by
    linarith
  have hdeltaAbsorb' : delta ≤ deltaAbsorb :=
    hdeltaSmall.trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaDensity' : delta ≤ deltaDensity :=
    hdeltaSmall.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans
          (min_le_left _ _)
  have hdeltaRadius' : delta ≤ deltaRadius :=
    hdeltaSmall.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans
            (min_le_left _ _)
  have hdeltaSchedule' : delta ≤ deltaSchedule :=
    hdeltaSmall.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans
            (min_le_right _ _)
  have hsourceMassPos :
      0 < source.toBodyFamily.mass :=
    pureWZ2_nonempty_family_mass_pos
      hdelta sourceNonempty
  have hdensityPos :
      0 < Kakeya.realRpowENN delta inputLoss := by
    simp [Kakeya.realRpowENN]
    positivity
  have hsourceShadingPos :
      0 < sourceShading.mass := by
    exact
      (ENNReal.mul_pos hdensityPos.ne'
        hsourceMassPos.ne').trans_le sourceDense
  have hsourceShadingFinite :
      sourceShading.mass ≠ ⊤ :=
    pureWZ2_fixed_support_shading_finite
      sourceSupport sourceShading
  rcases
      pureWZ2_localized_distinct_reanchoring
        hdelta hdelta200 (by linarith : 0 < R)
        (by norm_num : 0 < radius)
        (by
          dsimp only [radius]
          linarith)
        sourceSupport sourceDistinct sourceShading
        hsourceShadingPos hsourceShadingFinite with
    ⟨fine, hcell, hfineRadiusEq⟩
  have hcardLog :=
    pureWZ2_card_log_of_embedding
      hdelta hdeltaOne (by linarith) hR
      sourceNonempty sourceSupport sourceDistinct
      fine.sourceIndex
  rcases
      habsorb delta hdelta hdeltaAbsorb'
        fine.family.card hcardLog with
    ⟨hreferenceFixed, htopFixed, hmassFixed⟩
  let inputConstant :=
    Kakeya.realRpowENN delta (-inputLoss)
  let density :=
    Kakeya.realRpowENN delta inputLoss
  let outputConstant :=
    Kakeya.realRpowENN delta (-outputLoss)
  rcases
      pureWZ2_actual_constants_le_fixed
        fine hcell coordinateCount fine.family.card
        density inputConstant with
    ⟨hreferenceMono, htopMono, hmassMono⟩
  have hreference :
      let selectionRetention :=
        pureWZ2FiniteAnchoredRetentionConstant
          A coordinateCount fine.family.card
      let degreeConstant :=
        pureWZ2FiniteAnchoredDegreeConstant
          coordinateCount fine.family.card
      let globalRetention :=
        pureWZ2ReanchoredGlobalRetentionConstant
          density fine.cellCount fine.distinctnessLoss
            selectionRetention
      let fiberRatio :=
        pureWZ2ReanchoredFiberRatioConstant
          inputConstant
          (pureWZ2CompleteFiberOverlapBound A)
          globalRetention degreeConstant
      pureWZ2AnchoredReferenceScaleConstant
          degreeConstant inputConstant fiberRatio ≤
        outputConstant :=
    hreferenceMono.trans hreferenceFixed
  have htop :
      let selectionRetention :=
        pureWZ2FiniteAnchoredRetentionConstant
          A coordinateCount fine.family.card
      let globalRetention :=
        pureWZ2ReanchoredGlobalRetentionConstant
          density fine.cellCount fine.distinctnessLoss
            selectionRetention
      pureWZ2TopScaleConstant
          inputConstant
          (pureWZ2UnitScaleCompleteFiberOverlapBound A)
          globalRetention ≤
        outputConstant :=
    htopMono.trans htopFixed
  rcases
      pureWZ2_anchored_schedule
        hdelta hdeltaStrict hA houtputLoss
        coordinateCount hcoordinateCount
        hcoordinateLoss hdeltaSchedule' with
    ⟨hratioOne, hschedule, hsmallScale,
      hratioOutput⟩
  let ratio :=
    pureWZ2AnchoredScheduleRatio
      delta coordinateCount
  have houtputOne : 1 ≤ outputConstant := by
    dsimp only [outputConstant,
      Kakeya.realRpowENN]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_mono
    exact
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        hdelta hdeltaOne (by linarith)
  have houtputTop : outputConstant ≠ ⊤ := by
    exact ENNReal.ofReal_ne_top
  have hradiusBound :=
    hradiusAbsorb delta hdelta hdeltaRadius'
  have hradiusStrict :
      ENNReal.ofReal (8 * A) < outputConstant := by
    have hfixed :
        ENNReal.ofReal (8 * A) <
          radiusConstant := by
      dsimp only [radiusConstant]
      exact
        (ENNReal.ofReal_lt_ofReal_iff
          (by linarith : 0 < 8 * A + 1)).mpr
            (by linarith)
    exact hfixed.trans_le hradiusBound
  have hdensityZero : density ≠ 0 := by
    dsimp only [density, Kakeya.realRpowENN]
    exact
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hdelta _)).ne'
  have hdensityTop : density ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  let nearby :=
    Classical.choice
      (pureWZ2_anchored_nearby_assembly
        hdelta hdeltaOne hA fine
        (by
          rw [hfineRadiusEq]
          norm_num [radius])
        coordinateCount hcoordinateCount
        ratio hratioOne hschedule hsmallScale
        inputConstant density outputConstant
        hdensityZero hdensityTop sourceDense
        fullFiberData houtputOne houtputTop
        hradiusStrict hratioOutput
        hreference htop)
  have hmassLoss :
      (fine.cellCount : ENNReal) *
            (fine.distinctnessLoss : ENNReal) *
            nearby.selectionRetentionConstant ≤
        (ENNReal.ofReal
          (Real.log (1 / delta))) ^ logExponent := by
    rw [nearby.selectionRetentionConstant_eq]
    exact hmassMono.trans hmassFixed
  have hretained :
      wz2PaperPureRefinementFraction
            delta logExponent *
          sourceShading.mass ≤
        nearby.shading.mass :=
    pureWZ2_raw_mass_to_refinement
      hdelta hdeltaStrict logExponent
      nearby.retained_mass_raw hmassLoss
  let finalSourceIndex :
      Fin nearby.selected.family.card ↪
        Fin source.card :=
    nearby.selected.embedding.trans fine.sourceIndex
  have hfamilyMass :
      nearby.selected.family.toBodyFamily.mass ≤
        source.toBodyFamily.mass :=
    pureWZ2_reanchored_family_mass_le_source
      finalSourceIndex
  have hscale :=
    hdensityAbsorb delta hdelta hdeltaDensity'
  have hfinalDense :
      nearby.shading.IsLambdaDense
        (Kakeya.realRpowENN delta outputLoss) := by
    calc
      Kakeya.realRpowENN delta outputLoss *
            nearby.selected.family.toBodyFamily.mass
          ≤
        Kakeya.realRpowENN delta outputLoss *
            source.toBodyFamily.mass := by
        gcongr
      _ ≤
        (wz2PaperPureRefinementFraction
              delta logExponent *
            Kakeya.realRpowENN delta inputLoss) *
              source.toBodyFamily.mass := by
        simpa using
          mul_le_mul_right' hscale
            source.toBodyFamily.mass
      _ =
        wz2PaperPureRefinementFraction
            delta logExponent *
          (Kakeya.realRpowENN delta inputLoss *
            source.toBodyFamily.mass) := by
        ring
      _ ≤
        wz2PaperPureRefinementFraction
            delta logExponent *
          sourceShading.mass := by
        exact
          mul_le_mul_left' sourceDense
            (wz2PaperPureRefinementFraction
              delta logExponent)
      _ ≤ nearby.shading.mass := hretained
  have hfinalMassPos :
      0 < nearby.shading.mass := by
    have hfractionPos :
        0 <
          wz2PaperPureRefinementFraction
            delta logExponent := by
      dsimp only [wz2PaperPureRefinementFraction]
      have hlog :
          0 < ENNReal.ofReal
            (Real.log (1 / delta)) := by
        exact
          ENNReal.ofReal_pos.mpr
            (Real.log_pos
              (one_lt_one_div hdelta hdeltaStrict))
      have hinverse :
          (ENNReal.ofReal
            (Real.log (1 / delta)))⁻¹ ≠ 0 :=
        ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
      exact
        (zero_lt_iff.mpr
          (pow_ne_zero logExponent hinverse))
    exact
      (ENNReal.mul_pos hfractionPos.ne'
        hsourceShadingPos.ne').trans_le hretained
  have hfinalNonempty :
      nearby.selected.family.Nonempty := by
    by_contra hnot
    have hcard :
        nearby.selected.family.card = 0 := by
      simpa [Kakeya.Streamlined.TubeFamily.Nonempty,
        not_lt] using hnot
    have hzero : nearby.shading.mass = 0 := by
      have hempty :
          IsEmpty
            (Fin nearby.selected.family.toBodyFamily.card) := by
        rw [show
          nearby.selected.family.toBodyFamily.card =
            nearby.selected.family.card by rfl,
          hcard]
        infer_instance
      exact Fintype.sum_empty _
    rw [hzero] at hfinalMassPos
    exact (lt_irrefl 0 hfinalMassPos)
  let data :
      PureWZ2GWZReanchoredConversionData
        sourceShading outputConstant logExponent := {
    reanchored := nearby.selected.family
    sourceIndex := finalSourceIndex
    axialShift := fun index =>
      fine.axialShift
        (nearby.selected.embedding index)
    direction_eq := by
      intro index
      rw [nearby.selected.tube_eq]
      exact
        fine.direction_eq
          (nearby.selected.embedding index)
    source_base_eq := by
      intro index
      change
        (source.tube
          (fine.sourceIndex
            (nearby.selected.embedding index))).base =
          (nearby.selected.family.tube index).base +
            fine.axialShift
                (nearby.selected.embedding index) •
              (nearby.selected.family.tube index).direction
      rw [nearby.selected.tube_eq]
      exact
        fine.source_base_eq
          (nearby.selected.embedding index)
    axialShift_bound := fun index =>
      fine.axialShift_bound
        (nearby.selected.embedding index)
    shading := nearby.shading
    subshading := nearby.subshading
    retained_mass := hretained
    reanchored_paper_distinct :=
      nearby.literal_cwa.2.2.1
    literal_cwa := nearby.literal_cwa
  }
  exact ⟨data, hfinalNonempty, hfinalDense⟩

end Kakeya.Assouad

end
