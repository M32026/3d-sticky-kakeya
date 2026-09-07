import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerUniversalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PostDeletionUniversalInputAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyPostDeletionScalarAbsorptions
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalLossHierarchy

/-!
# Scalar boundary for the same-family owner witness

The public output loss admits the same quadratic floor/strong hierarchy used
by the closed paper mainline.  This file also keeps the quantitative
provenance supplied by the canonical finite caller-center constructor instead
of reasoning about arbitrary manually assembled records.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- A bounded positive copy of the requested output loss. -/
def pureWZ2SameFamilyOwnerScaleLoss (outputLoss : ℝ) : ℝ :=
  min outputLoss 1

/-- The critical floor loss on the same-family owner route. -/
def pureWZ2SameFamilyOwnerFloorLoss (outputLoss : ℝ) : ℝ :=
  wz2PaperCriticalFloorLoss
    (pureWZ2SameFamilyOwnerScaleLoss outputLoss)

/-- The strong loss used by the final multiplicity package. -/
def pureWZ2SameFamilyOwnerStrongLoss (outputLoss : ℝ) : ℝ :=
  wz2PaperInternalStrongLoss
    (pureWZ2SameFamilyOwnerScaleLoss outputLoss)

/-- The fixed loss hierarchy that is independent of every later scale. -/
structure SameFamilyOwnerFixedLossHierarchy
    (outputLoss : ℝ) where
  scaleLoss : ℝ
  scaleLoss_eq :
    scaleLoss = pureWZ2SameFamilyOwnerScaleLoss outputLoss
  scaleLoss_pos : 0 < scaleLoss
  scaleLoss_le_one : scaleLoss ≤ 1
  scaleLoss_le_output : scaleLoss ≤ outputLoss
  floorLoss : ℝ
  floorLoss_eq :
    floorLoss = pureWZ2SameFamilyOwnerFloorLoss outputLoss
  floorLoss_pos : 0 < floorLoss
  strongLoss : ℝ
  strongLoss_eq :
    strongLoss = pureWZ2SameFamilyOwnerStrongLoss outputLoss
  strongLoss_pos : 0 < strongLoss
  floor_strong : floorLoss < strongLoss
  output_budget : 3 * strongLoss ≤ outputLoss

/-- Choose the same paper-feasible hierarchy for every positive output loss. -/
theorem sameFamilyOwnerFixedLossHierarchy
    (outputLoss : ℝ)
    (outputLossPos : 0 < outputLoss) :
    Nonempty (SameFamilyOwnerFixedLossHierarchy outputLoss) := by
  let scaleLoss := pureWZ2SameFamilyOwnerScaleLoss outputLoss
  let floorLoss := pureWZ2SameFamilyOwnerFloorLoss outputLoss
  let strongLoss := pureWZ2SameFamilyOwnerStrongLoss outputLoss
  have scaleLossPos : 0 < scaleLoss := by
    dsimp only [scaleLoss, pureWZ2SameFamilyOwnerScaleLoss]
    exact lt_min outputLossPos zero_lt_one
  have scaleLossOne : scaleLoss ≤ 1 := by
    dsimp only [scaleLoss, pureWZ2SameFamilyOwnerScaleLoss]
    exact min_le_right _ _
  have scaleLossOutput : scaleLoss ≤ outputLoss := by
    dsimp only [scaleLoss, pureWZ2SameFamilyOwnerScaleLoss]
    exact min_le_left _ _
  have scaleLossSquare : scaleLoss ^ 2 ≤ scaleLoss := by
    nlinarith
  have floorLossPos : 0 < floorLoss := by
    dsimp only [floorLoss, pureWZ2SameFamilyOwnerFloorLoss,
      wz2PaperCriticalFloorLoss]
    positivity
  have strongLossPos : 0 < strongLoss := by
    dsimp only [strongLoss, pureWZ2SameFamilyOwnerStrongLoss,
      wz2PaperInternalStrongLoss]
    positivity
  have floorStrong : floorLoss < strongLoss := by
    dsimp only [floorLoss, strongLoss,
      pureWZ2SameFamilyOwnerFloorLoss,
      pureWZ2SameFamilyOwnerStrongLoss,
      wz2PaperCriticalFloorLoss,
      wz2PaperInternalStrongLoss]
    nlinarith [sq_pos_of_pos scaleLossPos]
  have outputBudget : 3 * strongLoss ≤ outputLoss := by
    have strongBound : 3 * strongLoss ≤ scaleLoss := by
      dsimp only [strongLoss, pureWZ2SameFamilyOwnerStrongLoss,
        wz2PaperInternalStrongLoss]
      nlinarith
    exact strongBound.trans scaleLossOutput
  exact
    ⟨{
      scaleLoss := scaleLoss
      scaleLoss_eq := rfl
      scaleLoss_pos := scaleLossPos
      scaleLoss_le_one := scaleLossOne
      scaleLoss_le_output := scaleLossOutput
      floorLoss := floorLoss
      floorLoss_eq := rfl
      floorLoss_pos := floorLossPos
      strongLoss := strongLoss
      strongLoss_eq := rfl
      strongLoss_pos := strongLossPos
      floor_strong := floorStrong
      output_budget := outputBudget
    }⟩

/--
The scalar part that can genuinely be selected before the physical scale.
It contains the pure critical floor and one common threshold for the caller
window, the critical-scale condition, and the literal multiplicity
absorption.  It is independent of every later family selection.
-/
structure SameFamilyOwnerUniformScalarThresholds
    (sigma outputLoss : ℝ) where
  hierarchy : SameFamilyOwnerFixedLossHierarchy outputLoss
  critical :
    PureWZ2CriticalFloorSelectionData
      sigma hierarchy.floorLoss hierarchy.strongLoss
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  caller_scalars :
    ∀ {delta rho : ℝ},
      0 < delta →
      delta ≤ delta₀ →
      0 < rho →
      Real.rpow delta (1 - outputLoss) ≤ rho →
      rho ≤ Real.rpow delta outputLoss →
        rho ≤ 1 / 24 ∧
          0 < delta / rho ∧
          delta / rho ≤ 1 ∧
          delta / rho ≤ 1 / 24 ∧
          delta / rho ≤ critical.delta₀ ∧
          2 * (55296 * Kakeya.deltaTubeVolume 1) ≤
            Kakeya.realRpowENN (delta / rho)
              (-(hierarchy.strongLoss - hierarchy.floorLoss))

/--
Choose the complete uniform scalar core.  The only ingredients are the fixed
loss hierarchy, Node 2's pure critical floor, and three small-scale
thresholds combined by `min`.
-/
theorem sameFamilyOwnerUniformScalarThresholds
    (sigma outputLoss : ℝ)
    (criticalPackage : PureWZ2CriticalPackage sigma)
    (outputLossPos : 0 < outputLoss) :
    Nonempty
      (SameFamilyOwnerUniformScalarThresholds sigma outputLoss) := by
  let hierarchy :=
    Classical.choice <|
      sameFamilyOwnerFixedLossHierarchy outputLoss outputLossPos
  let critical :=
    Classical.choice <|
      criticalPackage.select_pure_floor
        hierarchy.floorLoss_pos hierarchy.strongLoss_pos
  rcases
      PureWZ2SameFamilyPositiveParentDeletionData.exists_node3_uniform_twenty_four_scale
        outputLoss outputLossPos
    with
    ⟨windowScale, windowScalePos, windowScaleOne, windowSmall⟩
  rcases
      pure_wz2_exists_delta₀_rpow_le
        critical.delta₀_pos outputLossPos
    with
    ⟨criticalScale, criticalScalePos, criticalScaleOne,
      criticalSmall⟩
  let gap := hierarchy.strongLoss - hierarchy.floorLoss
  have gapPos : 0 < gap := by
    dsimp only [gap]
    exact sub_pos.mpr hierarchy.floor_strong
  let multiplicityConstant : ENNReal :=
    2 * (55296 * Kakeya.deltaTubeVolume 1)
  have multiplicityConstantFinite : multiplicityConstant ≠ ⊤ := by
    dsimp only [multiplicityConstant]
    exact
      ENNReal.mul_ne_top
        (by norm_num)
        (ENNReal.mul_ne_top
          (by norm_num) deltaTubeVolume_one_ne_top)
  have absorptionGapPos : 0 < outputLoss * gap :=
    mul_pos outputLossPos gapPos
  rcases
      exists_delta_realRpowENN_bound
        multiplicityConstant multiplicityConstantFinite
        absorptionGapPos
    with
    ⟨multiplicityScale, multiplicityScalePos, multiplicityScaleOne,
      multiplicitySmall⟩
  let delta₀ :=
    min windowScale (min criticalScale multiplicityScale)
  have delta₀Pos : 0 < delta₀ := by
    dsimp only [delta₀]
    exact
      lt_min windowScalePos
        (lt_min criticalScalePos multiplicityScalePos)
  have delta₀One : delta₀ ≤ 1 := by
    exact (min_le_left _ _).trans windowScaleOne
  refine
    ⟨{
      hierarchy := hierarchy
      critical := critical
      delta₀ := delta₀
      delta₀_pos := delta₀Pos
      delta₀_le_one := delta₀One
      caller_scalars := ?_
    }⟩
  intro delta rho deltaPos deltaBound rhoPos rhoLower rhoUpper
  have deltaWindow : delta ≤ windowScale :=
    deltaBound.trans (min_le_left _ _)
  have deltaCritical : delta ≤ criticalScale :=
    deltaBound.trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have deltaMultiplicity : delta ≤ multiplicityScale :=
    deltaBound.trans <|
      (min_le_right _ _).trans (min_le_right _ _)
  rcases
      windowSmall delta deltaPos deltaWindow rho rhoPos
        rhoLower rhoUpper
    with
    ⟨rhoSmall, ratioSmall⟩
  have ratioPos : 0 < delta / rho := div_pos deltaPos rhoPos
  have ratioOne : delta / rho ≤ 1 :=
    ratioSmall.trans (by norm_num)
  have ratioPower :
      delta / rho ≤ Real.rpow delta outputLoss :=
    PureWZ2SameFamilyPositiveParentDeletionData.node3_fiber_ratio_le_power
        deltaPos rhoPos rhoLower
  have ratioCritical : delta / rho ≤ critical.delta₀ :=
    ratioPower.trans <|
      criticalSmall delta deltaPos deltaCritical
  have constantBound :
      multiplicityConstant ≤
        Kakeya.realRpowENN delta (-(outputLoss * gap)) :=
    multiplicitySmall delta deltaPos deltaMultiplicity
  have powerTransfer :
      Kakeya.realRpowENN delta (-(outputLoss * gap)) ≤
        Kakeya.realRpowENN (delta / rho) (-gap) := by
    unfold Kakeya.realRpowENN
    apply ENNReal.ofReal_mono
    calc
      Real.rpow delta (-(outputLoss * gap)) =
          Real.rpow delta (outputLoss * (-gap)) := by
        congr 1
        ring
      _ =
          Real.rpow (Real.rpow delta outputLoss) (-gap) :=
        Real.rpow_mul deltaPos.le outputLoss (-gap)
      _ ≤ Real.rpow (delta / rho) (-gap) :=
        Real.rpow_le_rpow_of_nonpos ratioPos ratioPower (by linarith)
  exact
    ⟨rhoSmall, ratioPos, ratioOne, ratioSmall, ratioCritical,
      by
        simpa [multiplicityConstant, gap] using
          constantBound.trans powerTransfer⟩

/-- Actual simultaneous degree constant returned by the weighted selector. -/
def pureWZ2SameFamilyOwnerActualDegreeConstant
    (epsilon : ℝ) (cardinality : ℕ) : ENNReal :=
  16 * (geometricScaleCount epsilon : ENNReal) *
    (Nat.log 2 (2 * cardinality) + 1 : ENNReal) ^
      geometricScaleCount epsilon

/-- Actual retained-weight loss returned by the weighted selector. -/
def pureWZ2SameFamilyOwnerActualRegularizationLoss
    (epsilon : ℝ) (cardinality : ℕ) : ENNReal :=
  8 *
    (Nat.log 2 (2 * cardinality) + 1 : ENNReal) ^
      (geometricScaleCount epsilon + 1)

/--
The weighted restricted-CWA selector with absorption checked only at the
constants it actually returns.
-/
private theorem pureWZ2_weighted_restricted_cwa_actual_owner
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (preSelected : WZ2PaperPureTubeSubfamily fine)
    (preSelectedNonempty : preSelected.family.Nonempty)
    (externalWeight :
      Fin preSelected.family.card → ENNReal)
    (normalizationWeight weightUpper : ENNReal)
    (normalizationWeight_ne_zero : normalizationWeight ≠ 0)
    (normalizationWeight_ne_top : normalizationWeight ≠ ⊤)
    (weightUpper_ne_top : weightUpper ≠ ⊤)
    (total_weight_lower :
      normalizationWeight * fine.enncard ≤
        ∑ index : Fin preSelected.family.card,
          externalWeight index)
    (weight_upper :
      ∀ index, externalWeight index ≤ weightUpper)
    (epsilon : ℝ)
    (epsilon_pos : 0 < epsilon)
    (delta_pos : 0 < delta)
    (delta_lt_one : delta < 1)
    (output_ne_top : outputConstant ≠ ⊤)
    (rounding_absorption :
      ENNReal.ofReal (Real.rpow delta (-epsilon)) *
          ambientConstant ≤
        outputConstant)
    (restriction_absorption :
      wz2PaperPureNearbyRestrictionConstant
          ambientConstant normalizationWeight
          (pureWZ2SameFamilyOwnerActualDegreeConstant
            epsilon preSelected.family.card)
          (pureWZ2SameFamilyOwnerActualRegularizationLoss
              epsilon preSelected.family.card *
            weightUpper) ≤
        outputConstant) :
    ∃ (selectedPre :
        WZ2PaperPureTubeSubfamily preSelected.family)
      (selectedWeightLevel : ENNReal),
      selectedPre.family.Nonempty ∧
      0 < selectedWeightLevel ∧
      selectedWeightLevel ≠ ⊤ ∧
      (∑ index : Fin preSelected.family.card,
          externalWeight index) ≤
        pureWZ2SameFamilyOwnerActualRegularizationLoss
            epsilon preSelected.family.card *
          ∑ index : Fin selectedPre.family.card,
            externalWeight (selectedPre.embedding index) ∧
      (∀ index,
        selectedWeightLevel ≤
            externalWeight (selectedPre.embedding index) ∧
          externalWeight (selectedPre.embedding index) ≤
            2 * selectedWeightLevel) ∧
      WZ2PaperPureCWAAtNearbyScales
        (WZ2PaperPureTubeSubfamily.comp
          preSelected selectedPre).family
        outputConstant := by
  let coordinateCount := geometricScaleCount epsilon
  have coordinateCountPos : 0 < coordinateCount :=
    Nat.succ_pos _
  let scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta :=
    geometricRequestedScales
      delta epsilon delta_pos delta_lt_one
      epsilon_pos coordinateCount
  let coverData :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant :=
    fun coordinate =>
      Classical.choice (ambient.2.2.2 (scales coordinate))
  let Vertex : Fin coordinateCount → Type :=
    fun coordinate =>
      Fin (coverData coordinate).scaleData.coarse.card
  let parent :
      ∀ coordinate,
        Fin preSelected.family.card → Vertex coordinate :=
    fun coordinate source =>
      (coverData coordinate).scaleData.cover.parent
        (preSelected.embedding source)
  rcases
      wz2_finite_weighted_degree_selection
        coordinateCount Vertex parent externalWeight
        coordinateCountPos
    with
    ⟨regularized⟩
  let selectedIndices := regularized.selected
  let selectedPre :=
    WZ2PaperPureTubeSubfamily.fromFinset
      preSelected.family selectedIndices
  let selected :=
    WZ2PaperPureTubeSubfamily.comp preSelected selectedPre
  let degreeConstant :=
    pureWZ2SameFamilyOwnerActualDegreeConstant
      epsilon preSelected.family.card
  let regularizationLoss :=
    pureWZ2SameFamilyOwnerActualRegularizationLoss
      epsilon preSelected.family.card
  have totalWeightPos :
      0 <
        ∑ index : Fin preSelected.family.card,
          externalWeight index := by
    have fineCardPos : 0 < fine.card := by
      have preCardPos : 0 < preSelected.family.card :=
        preSelectedNonempty
      exact
        lt_of_le_of_lt (Nat.zero_le _)
          (preSelected.embedding ⟨0, preCardPos⟩).isLt
    have fineENNPos : 0 < fine.enncard := by
      change (0 : ENNReal) < (fine.card : ENNReal)
      exact_mod_cast fineCardPos
    exact
      (ENNReal.mul_pos
        normalizationWeight_ne_zero fineENNPos.ne').trans_le
        total_weight_lower
  have selectedIndicesNonempty : selectedIndices.Nonempty := by
    by_contra hnonempty
    have selectedEmpty : selectedIndices = ∅ := by
      simpa using hnonempty
    have retained := regularized.retained_weight
    have selectedSumZero :
        (∑ index ∈ regularized.selected,
          externalWeight index) = 0 := by
      have hregularizedEmpty :
          regularized.selected = ∅ := by
        simpa [selectedIndices] using selectedEmpty
      rw [hregularizedEmpty]
      simp
    rw [selectedSumZero, mul_zero] at retained
    exact (not_le_of_gt totalWeightPos) retained
  have selectedNonempty : selected.family.Nonempty := by
    change 0 < selectedIndices.card
    exact selectedIndicesNonempty.card_pos
  have degreeTop : degreeConstant ≠ ⊤ := by
    dsimp only [degreeConstant,
      pureWZ2SameFamilyOwnerActualDegreeConstant]
    exact ENNReal.coe_ne_top
  have regularizationTop : regularizationLoss ≠ ⊤ := by
    dsimp only [regularizationLoss,
      pureWZ2SameFamilyOwnerActualRegularizationLoss]
    exact ENNReal.coe_ne_top
  have embeddingMem :
      ∀ index : Fin selectedPre.family.card,
        selectedPre.embedding index ∈ selectedIndices := by
    intro index
    exact Finset.orderEmbOfFin_mem selectedIndices rfl index
  have imageUniv :
      Finset.image selectedPre.embedding
          (Finset.univ :
            Finset (Fin selectedPre.family.card)) =
        selectedIndices := by
    have subset :
        Finset.image selectedPre.embedding
            (Finset.univ :
              Finset (Fin selectedPre.family.card)) ⊆
          selectedIndices := by
      intro source hsource
      rcases Finset.mem_image.mp hsource with
        ⟨index, _, rfl⟩
      exact embeddingMem index
    have cardEq :
        (Finset.image selectedPre.embedding
          (Finset.univ :
            Finset (Fin selectedPre.family.card))).card =
          selectedIndices.card := by
      rw [Finset.card_image_of_injective _
        selectedPre.embedding.injective]
      change
        (Finset.univ :
          Finset (Fin selectedIndices.card)).card =
            selectedIndices.card
      simp
    exact
      Finset.eq_of_subset_of_card_le subset
        (by rw [cardEq])
  have embeddingSurjective :
      ∀ source ∈ selectedIndices,
        ∃ index : Fin selectedPre.family.card,
          selectedPre.embedding index = source := by
    intro source hsource
    have sourceImage :
        source ∈
          Finset.image selectedPre.embedding
            (Finset.univ :
              Finset (Fin selectedPre.family.card)) := by
      rw [imageUniv]
      exact hsource
    rcases Finset.mem_image.mp sourceImage with
      ⟨index, _, hindex⟩
    exact ⟨index, hindex⟩
  have selectedWeightEq :
      (∑ index : Fin selectedPre.family.card,
          externalWeight (selectedPre.embedding index)) =
        ∑ source ∈ selectedIndices,
          externalWeight source := by
    calc
      (∑ index : Fin selectedPre.family.card,
          externalWeight (selectedPre.embedding index)) =
          ∑ source ∈
              Finset.image selectedPre.embedding
                (Finset.univ :
                  Finset (Fin selectedPre.family.card)),
            externalWeight source := by
        exact
          (Finset.sum_image
            (fun first _ second _ heq =>
              selectedPre.embedding.injective heq)).symm
      _ =
          ∑ source ∈ selectedIndices,
            externalWeight source := by
        rw [imageUniv]
  have retainedWeight :
      (∑ index : Fin preSelected.family.card,
          externalWeight index) ≤
        regularizationLoss *
          ∑ index : Fin selectedPre.family.card,
            externalWeight (selectedPre.embedding index) := by
    have retained := regularized.retained_weight
    have cardFin :
        Fintype.card (Fin preSelected.family.card) =
          preSelected.family.card := by
      simp
    rw [cardFin] at retained
    change
      (∑ index : Fin preSelected.family.card,
          externalWeight index) ≤
        regularizationLoss *
          ∑ index ∈ selectedIndices,
            externalWeight index at retained
    simpa [regularizationLoss,
      pureWZ2SameFamilyOwnerActualRegularizationLoss,
      coordinateCount] using
      (selectedWeightEq ▸ retained)
  have selectedWeightBand :
      ∀ index : Fin selectedPre.family.card,
        regularized.weightLevel ≤
            externalWeight (selectedPre.embedding index) ∧
          externalWeight (selectedPre.embedding index) ≤
            2 * regularized.weightLevel := by
    intro index
    exact regularized.weight_band
      (selectedPre.embedding index) (embeddingMem index)
  have selectedWeightUpper :
      (∑ index : Fin selectedPre.family.card,
          externalWeight (selectedPre.embedding index)) ≤
        selected.family.enncard * weightUpper := by
    change
      (∑ index : Fin selectedPre.family.card,
          externalWeight (selectedPre.embedding index)) ≤
        (selectedPre.family.card : ENNReal) * weightUpper
    calc
      (∑ index : Fin selectedPre.family.card,
          externalWeight (selectedPre.embedding index)) ≤
          ∑ _index : Fin selectedPre.family.card,
            weightUpper := by
        exact
          Finset.sum_le_sum fun index _ =>
            weight_upper (selectedPre.embedding index)
      _ =
          (selectedPre.family.card : ENNReal) * weightUpper := by
        simp [Finset.sum_const]
  have cardinalityRetention :
      normalizationWeight * fine.enncard ≤
        (regularizationLoss * weightUpper) *
          selected.family.enncard := by
    calc
      normalizationWeight * fine.enncard ≤
          ∑ index : Fin preSelected.family.card,
            externalWeight index :=
        total_weight_lower
      _ ≤
          regularizationLoss *
            ∑ index : Fin selectedPre.family.card,
              externalWeight (selectedPre.embedding index) :=
        retainedWeight
      _ ≤
          regularizationLoss *
            (selected.family.enncard * weightUpper) := by
        gcongr
      _ =
          (regularizationLoss * weightUpper) *
            selected.family.enncard := by
        ring
  have filterCard :
      ∀ (coordinate : Fin coordinateCount)
        (vertex :
          Fin (coverData coordinate).scaleData.coarse.card),
        (selectedIndices.filter fun source =>
          parent coordinate source = vertex).card =
        ((Finset.univ :
          Finset (Fin selected.family.card)).filter fun source =>
            (coverData coordinate).scaleData.cover.parent
              (selected.embedding source) = vertex).card := by
    intro coordinate vertex
    let left :=
      selectedIndices.filter fun source =>
        parent coordinate source = vertex
    let right :=
      (Finset.univ :
        Finset (Fin selectedPre.family.card)).filter fun source =>
          parent coordinate (selectedPre.embedding source) =
            vertex
    have imageEq :
        Finset.image selectedPre.embedding right = left := by
      ext source
      simp only [left, right, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨index, hparent, rfl⟩
        exact ⟨embeddingMem index, hparent⟩
      · rintro ⟨hsource, hparent⟩
        rcases embeddingSurjective source hsource with
          ⟨index, hindex⟩
        refine ⟨index, ?_, hindex⟩
        rwa [hindex]
    have cardEq :
        (Finset.image selectedPre.embedding right).card =
          right.card :=
      Finset.card_image_of_injective
        right selectedPre.embedding.injective
    change left.card = right.card
    rw [← imageEq, cardEq]
  have degreeUniform :
      ∀ coordinate : Fin coordinateCount,
        ∀ first second :
            Fin (coverData coordinate).scaleData.coarse.card,
          0 <
              ((Finset.univ :
                Finset (Fin selected.family.card)).filter fun source =>
                  (coverData coordinate).scaleData.cover.parent
                      (selected.embedding source) =
                    first).card →
          0 <
              ((Finset.univ :
                Finset (Fin selected.family.card)).filter fun source =>
                  (coverData coordinate).scaleData.cover.parent
                      (selected.embedding source) =
                    second).card →
          (((Finset.univ :
            Finset (Fin selected.family.card)).filter fun source =>
              (coverData coordinate).scaleData.cover.parent
                  (selected.embedding source) =
                first).card : ENNReal) ≤
            degreeConstant *
              (((Finset.univ :
                Finset (Fin selected.family.card)).filter fun source =>
                  (coverData coordinate).scaleData.cover.parent
                      (selected.embedding source) =
                    second).card : ENNReal) := by
    intro coordinate first second hfirst hsecond
    have hfirst' :
        0 <
          (selectedIndices.filter fun source =>
            parent coordinate source = first).card := by
      rw [filterCard coordinate first]
      exact hfirst
    have hsecond' :
        0 <
          (selectedIndices.filter fun source =>
            parent coordinate source = second).card := by
      rw [filterCard coordinate second]
      exact hsecond
    have main :=
      regularized.degree_uniform
        coordinate first second hfirst' hsecond'
    have cardFin :
        Fintype.card (Fin preSelected.family.card) =
          preSelected.family.card := by
      simp
    simpa [selectedIndices, degreeConstant,
      pureWZ2SameFamilyOwnerActualDegreeConstant,
      coordinateCount, cardFin,
      filterCard coordinate first,
      filterCard coordinate second] using main
  let roundingConstant : ENNReal :=
    ENNReal.ofReal (Real.rpow delta (-epsilon))
  have roundingConstantPos : 0 < roundingConstant :=
    ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos delta_pos _)
  have roundingConstantTop : roundingConstant ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have roundingConstantOne : 1 ≤ roundingConstant := by
    have h :
        (1 : ℝ) < Real.rpow delta (-epsilon) :=
      Real.one_lt_rpow_of_pos_of_lt_one_of_neg
        delta_pos delta_lt_one (by linarith)
    simpa [roundingConstant] using ENNReal.ofReal_le_ofReal h.le
  have rounding :
      ∀ requested : WZ2PaperRequestedScale delta,
        ∃ coordinate : Fin coordinateCount,
          requested.1 ≤ (scales coordinate).1 ∧
          ENNReal.ofReal (scales coordinate).1 <
            roundingConstant * ENNReal.ofReal requested.1 :=
    geometricRequestedScale_rounding
      delta_pos delta_lt_one epsilon_pos
      (rfl :
        coordinateCount = geometricScaleCount epsilon)
  let retentionConstant :=
    regularizationLoss * weightUpper
  have retentionTop : retentionConstant ≠ ⊤ :=
    ENNReal.mul_ne_top regularizationTop weightUpper_ne_top
  have selectedCWA :
      WZ2PaperPureCWAAtNearbyScales
        selected.family outputConstant :=
    pure_cwa_restrict_with_rounding
      ambient selected selectedNonempty
      coordinateCount coordinateCountPos scales
      degreeConstant retentionConstant
      normalizationWeight
      normalizationWeight_ne_zero normalizationWeight_ne_top
      retentionTop degreeTop
      cardinalityRetention degreeUniform
      roundingConstantPos roundingConstantTop roundingConstantOne
      rounding rounding_absorption output_ne_top
      (by
        simpa [degreeConstant, regularizationLoss,
          retentionConstant,
          pureWZ2SameFamilyOwnerActualDegreeConstant,
          pureWZ2SameFamilyOwnerActualRegularizationLoss] using
          restriction_absorption)
  exact
    ⟨selectedPre, regularized.weightLevel,
      selectedNonempty, regularized.weightLevel_pos,
      by
        have selectedWeightLevelTop :
            regularized.weightLevel ≠ ⊤ := by
          let selectedIndex : Fin selectedPre.family.card :=
            ⟨0, selectedNonempty⟩
          exact
            ne_top_of_le_ne_top
              (weightUpper_ne_top)
              ((selectedWeightBand selectedIndex).1.trans
                (weight_upper
                  (selectedPre.embedding selectedIndex)))
        exact selectedWeightLevelTop,
      retainedWeight, selectedWeightBand, selectedCWA⟩

/--
The exact finite CWA constant required by the actual owner-parent weighted
selection.  It is the maximum of the rounding and restriction constants that
the closed selector really uses.
-/
noncomputable def pureWZ2SameFamilyOwnerActualOutputConstant
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (support : PureWZ2PositiveCallerSupportData quotient)
    (coordinateCount : ℕ)
    (regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount)
    (merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled)
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation)
    (epsilon : ℝ) : ENNReal :=
  let owner := pureWZ2SameFamilyDirectOwner balancing
  let ownerLoss := pureWZ2SameFamilyOwnerLoss balancing owner
  let normalizationWeight := sameFamily.parentMassLevel / ownerLoss
  let packed :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      sameFamily.selectedCoarse.family
      owner.exactified.retainedParents
  let degreeConstant :=
    pureWZ2SameFamilyOwnerActualDegreeConstant
      epsilon packed.family.card
  let regularizationLoss :=
    pureWZ2SameFamilyOwnerActualRegularizationLoss
      epsilon packed.family.card
  max
    (ENNReal.ofReal
        (Real.rpow callerRequested.1 (-epsilon)) *
      coarseConstant)
    (wz2PaperPureNearbyRestrictionConstant
      coarseConstant normalizationWeight degreeConstant
      (regularizationLoss * (2 * sameFamily.parentMassLevel)))

/--
Actual-specialized owner-parent selection.

Unlike the historical wrapper, this constructor checks absorption only for
the degree and regularization constants returned by the finite weighted
selector.  Its output constant is chosen canonically as the maximum of those
two exact requirements.
-/
theorem pureWZ2_same_family_owner_parent_selection_actual
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (support : PureWZ2PositiveCallerSupportData quotient)
    (coordinateCount : ℕ)
    (regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount)
    (merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled)
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation)
    (epsilon : ℝ)
    (epsilon_pos : 0 < epsilon)
    (caller_lt_one : callerRequested.1 < 1) :
    Nonempty
      (WZ2PaperOwnerParentSelectedData
        (pureWZ2SameFamilyDirectOwner balancing)
        (pureWZ2SameFamilyOwnerActualOutputConstant
          actualNearby quotient support coordinateCount regularized merged
          scales scheduled sameFamily scaleSeparation balancing epsilon)) := by
  let owner :
      WZ2PaperDirectOwnerPreparationData
        balancing.balanced.finalData.producer :=
    pureWZ2SameFamilyDirectOwner balancing
  let packed :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      sameFamily.selectedCoarse.family
      owner.exactified.retainedParents
  let preSelected :=
    WZ2PaperPureTubeSubfamily.ofTubeSubfamily packed
  let ownerFiberMass : Fin packed.family.card → ENNReal :=
    fun parent =>
      (restrictPaperShading
        (owner.exactified.restrictedCover.fullFiberSubfamily parent)
        owner.exactified.refined).mass
  let ownerLoss := pureWZ2SameFamilyOwnerLoss balancing owner
  let normalizationWeight := sameFamily.parentMassLevel / ownerLoss
  let degreeConstant :=
    pureWZ2SameFamilyOwnerActualDegreeConstant
      epsilon preSelected.family.card
  let regularizationLoss :=
    pureWZ2SameFamilyOwnerActualRegularizationLoss
      epsilon preSelected.family.card
  let outputConstant :=
    pureWZ2SameFamilyOwnerActualOutputConstant
      actualNearby quotient support coordinateCount regularized merged
      scales scheduled sameFamily scaleSeparation balancing epsilon
  have parentMassLevel_ne_top :
      sameFamily.parentMassLevel ≠ ⊤ := by
    let parent : Fin sameFamily.selectedCoarse.family.card :=
      ⟨0, sameFamily.selectedCoarse_nonempty⟩
    let fiberShading :=
      restrictPaperShading
        ((sameFamily.pullback.internalPartitioningCover scaleSeparation)
          |>.fullFiberSubfamily parent)
        sameFamily.pullback.selectedFineShading
    have lower :
        sameFamily.parentMassLevel ≤ fiberShading.mass := by
      rw [(sameFamily.pullback.internalPartitioningCover scaleSeparation)
        |>.fullFiberShading_mass
          sameFamily.pullback.selectedFineShading parent]
      exact (sameFamily.parent_mass_band parent).1
    exact
      ne_top_of_le_ne_top
        (wz1PaperTubeShading_mass_ne_top fiberShading)
        lower
  have ownerLoss_ne_zero : ownerLoss ≠ 0 := by
    dsimp only [ownerLoss, pureWZ2SameFamilyOwnerLoss]
    unfold pureWZ2SameFamilyFixedOriginBalancingLoss
    unfold wz2PaperFinalBalancedCoverLoss
    unfold wz2PaperDominantOwnerLoss
    rw [owner.exactified.countBins_eq]
    simp only [wz2PaperBalancedParentDegreeCap]
    positivity
  have ownerLoss_ne_top : ownerLoss ≠ ⊤ := by
    dsimp only [ownerLoss, pureWZ2SameFamilyOwnerLoss]
    unfold pureWZ2SameFamilyFixedOriginBalancingLoss
    unfold wz2PaperFinalBalancedCoverLoss
    unfold wz2PaperDominantOwnerLoss
    rw [owner.exactified.countBins_eq]
    simp only [wz2PaperBalancedParentDegreeCap]
    repeat' apply ENNReal.mul_ne_top
    all_goals
      first
      | exact ENNReal.natCast_ne_top _
      | exact
          ENNReal.add_ne_top.mpr
            ⟨ENNReal.natCast_ne_top _, by norm_num⟩
      | norm_num
  have normalizationWeight_ne_zero : normalizationWeight ≠ 0 := by
    dsimp only [normalizationWeight]
    exact
      ENNReal.div_ne_zero.mpr
        ⟨sameFamily.parentMassLevel_pos.ne', ownerLoss_ne_top⟩
  have normalizationWeight_ne_top : normalizationWeight ≠ ⊤ := by
    dsimp only [normalizationWeight]
    exact ENNReal.div_ne_top parentMassLevel_ne_top ownerLoss_ne_zero
  have ownerFiberUpper :
      ∀ parent : Fin packed.family.card,
        ownerFiberMass parent ≤ 2 * sameFamily.parentMassLevel := by
    intro parent
    let ambientCover :=
      sameFamily.pullback.internalPartitioningCover scaleSeparation
    calc
      ownerFiberMass parent ≤
          (restrictPaperShading
            (ambientCover.fullFiberSubfamily
              (packed.embedding parent))
            sameFamily.pullback.selectedFineShading).mass := by
        apply
          wz2_paper_complete_fiber_mass_le
            ambientCover owner.exactified.selected
            owner.exactified.restrictedCover
            owner.exactified.refined
            sameFamily.pullback.selectedFineShading
        · intro index
          exact
            (owner.exactified_subshading index).trans
              (balancing.finalFine_subshading
                (owner.exactified.selected.embedding index))
        · exact owner.exactified.full_fiber_complete parent
      _ ≤ 2 * sameFamily.parentMassLevel := by
        rw [ambientCover.fullFiberShading_mass
          sameFamily.pullback.selectedFineShading
          (packed.embedding parent)]
        exact
          (sameFamily.parent_mass_band
            (packed.embedding parent)).2
  have ownerMassSum :
      (∑ parent : Fin packed.family.card, ownerFiberMass parent) =
        owner.exactified.refined.mass :=
    owner.exactified.restrictedCover
      |>.sum_fullFiberShading_mass owner.exactified.refined
  have preCardMass :
      sameFamily.parentMassLevel *
          sameFamily.selectedCoarse.family.enncard ≤
        sameFamily.pullback.selectedFineShading.mass := by
    let ambientCover :=
      sameFamily.pullback.internalPartitioningCover scaleSeparation
    rw [← ambientCover.sum_fullFiberShading_mass
      sameFamily.pullback.selectedFineShading]
    calc
      sameFamily.parentMassLevel *
            sameFamily.selectedCoarse.family.enncard =
          ∑ _parent : Fin sameFamily.selectedCoarse.family.card,
            sameFamily.parentMassLevel := by
        simp [Kakeya.Streamlined.TubeFamily.enncard,
          Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤
          ∑ parent : Fin sameFamily.selectedCoarse.family.card,
            (restrictPaperShading
              (ambientCover.fullFiberSubfamily parent)
              sameFamily.pullback.selectedFineShading).mass := by
        exact
          Finset.sum_le_sum fun parent _ => by
            rw [ambientCover.fullFiberShading_mass
              sameFamily.pullback.selectedFineShading parent]
            exact (sameFamily.parent_mass_band parent).1
  have ownerMassRetention :
      sameFamily.parentMassLevel *
          sameFamily.selectedCoarse.family.enncard ≤
        ownerLoss * owner.exactified.refined.mass := by
    let finalBalancedFine :=
      balancing.balanced.finalData.producer.coarseBand
        |>.selectedFineShading
    calc
      sameFamily.parentMassLevel *
            sameFamily.selectedCoarse.family.enncard ≤
          sameFamily.pullback.selectedFineShading.mass :=
        preCardMass
      _ ≤
          pureWZ2SameFamilyFixedOriginBalancingLoss balancing.balanced *
            finalBalancedFine.mass :=
        balancing.selected_mass_retention
      _ =
          pureWZ2SameFamilyFixedOriginBalancingLoss balancing.balanced *
            owner.exactAdapter.exact.refined.mass := by
        rw [owner.exactAdapter.exact_refined_eq]
      _ ≤
          pureWZ2SameFamilyFixedOriginBalancingLoss balancing.balanced *
            (wz2PaperDominantOwnerLoss owner.exactified *
              owner.exactified.refined.mass) := by
        gcongr
        exact
          wz2_paper_dominant_owner_mass_comparison
            owner.degree owner.dominant owner.exactified
      _ = ownerLoss * owner.exactified.refined.mass := by
        simp only [ownerLoss, pureWZ2SameFamilyOwnerLoss]
        ring
  have totalWeightLower :
      normalizationWeight *
          sameFamily.selectedCoarse.family.enncard ≤
        ∑ parent : Fin packed.family.card, ownerFiberMass parent := by
    rw [ownerMassSum]
    have divided :
        (sameFamily.parentMassLevel *
            sameFamily.selectedCoarse.family.enncard) / ownerLoss ≤
          owner.exactified.refined.mass := by
      rw [ENNReal.div_le_iff ownerLoss_ne_zero ownerLoss_ne_top]
      simpa [mul_comm] using ownerMassRetention
    simpa [normalizationWeight, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using divided
  have output_ne_top : outputConstant ≠ ⊤ := by
    dsimp only [outputConstant,
      pureWZ2SameFamilyOwnerActualOutputConstant]
    apply max_ne_top
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        sameFamily.coarse_pure_cwa.2.1.2
    · unfold wz2PaperPureNearbyRestrictionConstant
      apply max_ne_top sameFamily.coarse_pure_cwa.2.1.2
      apply max_ne_top
      · dsimp only [degreeConstant,
          pureWZ2SameFamilyOwnerActualDegreeConstant]
        exact ENNReal.coe_ne_top
      · have inverseTop : normalizationWeight⁻¹ ≠ ⊤ :=
          ENNReal.inv_ne_top.mpr normalizationWeight_ne_zero
        have degreeTop : degreeConstant ≠ ⊤ := by
          dsimp only [degreeConstant,
            pureWZ2SameFamilyOwnerActualDegreeConstant]
          exact ENNReal.coe_ne_top
        have regularizationTop : regularizationLoss ≠ ⊤ := by
          dsimp only [regularizationLoss,
            pureWZ2SameFamilyOwnerActualRegularizationLoss]
          exact ENNReal.coe_ne_top
        have weightUpperTop :
            regularizationLoss *
                (2 * sameFamily.parentMassLevel) ≠ ⊤ :=
          ENNReal.mul_ne_top regularizationTop
            (ENNReal.mul_ne_top (by norm_num) parentMassLevel_ne_top)
        exact
          ENNReal.mul_ne_top
            (ENNReal.mul_ne_top inverseTop
              (ENNReal.mul_ne_top
                (ENNReal.mul_ne_top
                  sameFamily.coarse_pure_cwa.2.1.2
                  weightUpperTop)
                degreeTop))
            sameFamily.coarse_pure_cwa.2.1.2
  have rounding_absorption :
      ENNReal.ofReal
            (Real.rpow callerRequested.1 (-epsilon)) *
          coarseConstant ≤
        outputConstant := by
    dsimp only [outputConstant,
      pureWZ2SameFamilyOwnerActualOutputConstant]
    exact le_max_left _ _
  have restriction_absorption :
      wz2PaperPureNearbyRestrictionConstant
          coarseConstant normalizationWeight degreeConstant
          (regularizationLoss * (2 * sameFamily.parentMassLevel)) ≤
        outputConstant := by
    dsimp only [outputConstant,
      pureWZ2SameFamilyOwnerActualOutputConstant]
    exact le_max_right _ _
  rcases
      pureWZ2_weighted_restricted_cwa_actual_owner
        sameFamily.coarse_pure_cwa preSelected
        owner.exactified.retainedParents_nonempty.card_pos
        ownerFiberMass normalizationWeight
        (2 * sameFamily.parentMassLevel)
        normalizationWeight_ne_zero normalizationWeight_ne_top
        (ENNReal.mul_ne_top (by norm_num) parentMassLevel_ne_top)
        totalWeightLower ownerFiberUpper epsilon epsilon_pos
        (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
        caller_lt_one output_ne_top rounding_absorption
        (by
          simpa [degreeConstant, regularizationLoss,
            normalizationWeight] using restriction_absorption)
    with
    ⟨selectedPre, selectedFiberMassLevel,
      selectedNonempty, selectedFiberMassLevelPos,
      selectedFiberMassLevelTop, retainedWeight,
      selectedWeightBand, pureCWA⟩
  let selectedPackedOrdinary := selectedPre.toTubeSubfamily
  let balancedPullback :
      WZ2PaperOwnerParentBalancedPullbackData
        owner selectedPackedOrdinary :=
    Classical.choice <|
      wz2_paper_owner_subfamily_balanced_pullback
        owner selectedPackedOrdinary selectedNonempty
  have retainedSelectedMass :
      owner.exactified.refined.mass ≤
        regularizationLoss *
          balancedPullback.pullback.selectedFineShading.mass := by
    calc
      owner.exactified.refined.mass =
          ∑ parent : Fin packed.family.card,
            ownerFiberMass parent := ownerMassSum.symm
      _ ≤
          regularizationLoss *
            ∑ parent : Fin selectedPre.family.card,
              ownerFiberMass (selectedPre.embedding parent) :=
        retainedWeight
      _ =
          regularizationLoss *
            balancedPullback.pullback.selectedFineShading.mass := by
        rw [balancedPullback.pullback.selectedFineShading_mass_eq]
        rfl
  exact
    ⟨{
      selectedPacked := selectedPackedOrdinary
      selected_nonempty := selectedNonempty
      selectionEpsilon := epsilon
      selectionEpsilon_pos := epsilon_pos
      degreeConstant := degreeConstant
      degreeConstant_ne_top := by
        dsimp only [degreeConstant,
          pureWZ2SameFamilyOwnerActualDegreeConstant]
        exact ENNReal.coe_ne_top
      degreeConstant_eq := rfl
      regularizationLoss := regularizationLoss
      regularizationLoss_ne_top := by
        dsimp only [regularizationLoss,
          pureWZ2SameFamilyOwnerActualRegularizationLoss]
        exact ENNReal.coe_ne_top
      regularizationLoss_eq := rfl
      selectedFiberMassLevel := selectedFiberMassLevel
      selectedFiberMassLevel_pos := selectedFiberMassLevelPos
      selectedFiberMassLevel_ne_top := selectedFiberMassLevelTop
      retained_fiber_mass := by
        change
          owner.exactified.refined.mass ≤
            regularizationLoss *
              ∑ parent : Fin selectedPre.family.card,
                ownerFiberMass (selectedPre.embedding parent)
        rw [← ownerMassSum]
        exact retainedWeight
      selected_fiber_mass_band := selectedWeightBand
      balancedPullback := balancedPullback
      retained_selected_mass := retainedSelectedMass
      pure_cwa := pureCWA
    }⟩

/--
The constants chosen before the canonical post-deletion constructors are
explicitly finite.  In particular, the construction does not obtain a
top-valued regularization or same-family CWA constant.
-/
theorem PureWZ2PostDeletionUniversalConstructionWitness.constants_finite
    {delta sigma loss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma loss delta}
    {normalizationExponent deletionExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := loss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (witness :
      PureWZ2PostDeletionUniversalConstructionWitness
        normalized callerRequested deletionExponent) :
    witness.regularizationConstant ≠ ⊤ ∧
      witness.fiberConstant ≠ ⊤ ∧
      witness.coarseConstant ≠ ⊤ :=
  ⟨witness.regularizationConstant_ne_top,
    witness.fiberConstant_ne_top,
    witness.coarseConstant_ne_top⟩

/-- The actual finite caller-center retention formula never equals `⊤`. -/
theorem pureWZ2FiniteCallerCenterRetentionConstant_ne_top
    (coordinateCount callerCard : ℕ)
    (Color : Fin coordinateCount → Type)
    [∀ coordinate, Fintype (Color coordinate)] :
    pureWZ2FiniteCallerCenterRetentionConstant
        coordinateCount callerCard Color ≠
      ⊤ := by
  unfold pureWZ2FiniteCallerCenterRetentionConstant
  exact
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.natCast_ne_top _) (by norm_num))
      (ENNReal.pow_ne_top <|
        ENNReal.add_ne_top.mpr
          ⟨ENNReal.natCast_ne_top _, by norm_num⟩)

/--
The finite caller-center selection preserves the defining retention formula,
hence its actual selected retention constant is finite.
-/
theorem
    PureWZ2FiniteCallerCenterSelectionData.retentionConstant_ne_top
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {callerBase :
      WZ2PaperPureTubeSubfamily quotient.callerCoarse}
    {coordinateCount : ℕ}
    {scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    {Color : Fin coordinateCount → Type}
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    {coloring :
      ∀ coordinate,
        PureWZ2CallerCenterEnvelopeColoringData
          quotient (scheduled coordinate) callerBase
          (Color coordinate)}
    {weight : Fin callerBase.family.card → ENNReal}
    (selection :
      PureWZ2FiniteCallerCenterSelectionData
        quotient callerBase coordinateCount scales scheduled
        Color coloring weight) :
    selection.retentionConstant ≠ ⊤ := by
  rw [selection.retentionConstant_eq]
  exact
    pureWZ2FiniteCallerCenterRetentionConstant_ne_top
      coordinateCount callerBase.family.card Color

/--
The exact fields still needed after the actual-specialized owner selection
and the uniform scalar threshold producer.  No family, shading, cover, or
provenance datum occurs here.
-/
structure SameFamilyOwnerActualRemainingQuantitative
    {delta sigma outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (support : PureWZ2PositiveCallerSupportData quotient)
    (coordinateCount : ℕ)
    (regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount)
    (merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled)
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation)
    (epsilon : ℝ)
    (data :
      WZ2PaperOwnerParentSelectedData
        (pureWZ2SameFamilyDirectOwner balancing)
        (pureWZ2SameFamilyOwnerActualOutputConstant
          actualNearby quotient support coordinateCount regularized merged
          scales scheduled sameFamily scaleSeparation balancing epsilon))
    (logExponent : ℕ) : Prop where
  retention_absorption :
    wz2PaperPureRefinementFraction delta logExponent *
        ((((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            pureWZ2CompleteParentRegularizationLoss
              actualNearby.scaleData.coarse.card coordinateCount *
            sameFamily.retentionConstant) *
          pureWZ2SameFamilyOwnerLoss balancing
            (pureWZ2SameFamilyDirectOwner balancing)) *
          data.regularizationLoss) ≤
      1
  coarse_cwa_absorption :
    pureWZ2SameFamilyOwnerActualOutputConstant
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing epsilon ≤
      Kakeya.realRpowENN callerRequested.1 (-outputLoss)
  coarse_density_absorption :
    Kakeya.realRpowENN callerRequested.1 outputLoss *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN callerRequested.1 2) *
          data.selectedPacked.family.enncard *
          (2 ^
            (balancing.balanced.finalData.producer.fiberBand.level + 1) :
              ENNReal) ≤
      data.finalFineShading.mass
  coarse_volume_scalar :
    MeasureTheory.volume data.finalFineShading.union *
          MeasureTheory.volume
            (wz1PaperGridCube callerRequested.1 (0, 0, 0)) ≤
      Kakeya.realRpowENN callerRequested.1
          (sigma - outputLoss) *
        data.publicBalanced.cellMass
  coarse_cardinality_absorption :
    (48 : ENNReal) *
        pureWZ2SameFamilyOwnerActualOutputConstant
          actualNearby quotient support coordinateCount regularized merged
          scales scheduled sameFamily scaleSeparation balancing epsilon ≤
      Kakeya.realRpowENN callerRequested.1
        (-2 * pureWZ2SameFamilyOwnerStrongLoss outputLoss)

end Kakeya.Assouad

end
