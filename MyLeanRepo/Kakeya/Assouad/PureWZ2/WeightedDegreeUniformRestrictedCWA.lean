import MyLeanRepo.Kakeya.Assouad.PureWZ2.DegreeUniformRestrictedCWA

/-!
# Weighted degree-uniform pure CWA restriction

The final Section 6 selection must retain shaded mass, not merely indexed
cardinality.  This module applies the finite simultaneous-degree regularizer
to arbitrary external tube weights.  A per-tube weight upper bound converts
weighted retention into the cardinality retention required by the closed pure
CWA restriction theorem.

The same selected subfamily therefore carries:

* external weighted-mass retention;
* simultaneous parent-degree uniformity on the geometric scale schedule;
* quantitative indexed-cardinality retention; and
* pure Definition 2.12 at every nearby scale.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Actual finite simultaneous-degree constant used by the weighted
regularizer. -/
def pureWZ2WeightedDegreeConstant
    (epsilon : ℝ) (parentCount : ℕ) : ENNReal :=
  16 * (geometricScaleCount epsilon : ENNReal) *
    (Nat.log 2 (2 * parentCount) + 1 : ENNReal) ^
      geometricScaleCount epsilon

/-- Actual dyadic weight-regularization loss used by the weighted
regularizer. -/
def pureWZ2WeightedRegularizationLoss
    (epsilon : ℝ) (parentCount : ℕ) : ENNReal :=
  8 * (Nat.log 2 (2 * parentCount) + 1 : ENNReal) ^
    (geometricScaleCount epsilon + 1)

/--
Weighted simultaneous regularization on an already selected subfamily,
followed by pure nearby-CWA recovery.
-/
theorem weighted_degree_uniform_restricted_cwa
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
    (normalizationWeight_ne_zero :
      normalizationWeight ≠ 0)
    (normalizationWeight_ne_top :
      normalizationWeight ≠ ⊤)
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
          (pureWZ2WeightedDegreeConstant
            epsilon preSelected.family.card)
          (pureWZ2WeightedRegularizationLoss
              epsilon preSelected.family.card *
            weightUpper) ≤
        outputConstant) :
    ∃ (selected : WZ2PaperPureTubeSubfamily fine)
      (selectedPre :
        WZ2PaperPureTubeSubfamily preSelected.family)
      (degreeConstant regularizationLoss selectedWeightLevel : ENNReal),
      selected.family.Nonempty ∧
      degreeConstant ≠ ⊤ ∧
      regularizationLoss ≠ ⊤ ∧
      0 < selectedWeightLevel ∧
      selectedWeightLevel ≠ ⊤ ∧
      degreeConstant =
        16 * (geometricScaleCount epsilon : ENNReal) *
          (Nat.log 2
            (2 * preSelected.family.card) + 1 :
          ENNReal) ^ geometricScaleCount epsilon ∧
      regularizationLoss =
        8 *
          (Nat.log 2
            (2 * preSelected.family.card) + 1 :
          ENNReal) ^ (geometricScaleCount epsilon + 1) ∧
      selected.family = selectedPre.family ∧
      selected =
        WZ2PaperPureTubeSubfamily.comp preSelected selectedPre ∧
      selected.family.card = selectedPre.family.card ∧
      (∃ reindex :
          Fin selected.family.card →
            Fin selectedPre.family.card,
        ∀ index,
          selected.embedding index =
            preSelected.embedding
              (selectedPre.embedding
                (reindex index))) ∧
      (∑ index : Fin preSelected.family.card,
          externalWeight index) ≤
        regularizationLoss *
          ∑ index : Fin selectedPre.family.card,
            externalWeight (selectedPre.embedding index) ∧
      (∀ index,
        selectedWeightLevel ≤
            externalWeight
              (selectedPre.embedding index) ∧
          externalWeight
              (selectedPre.embedding index) ≤
            2 * selectedWeightLevel) ∧
      normalizationWeight * fine.enncard ≤
        (regularizationLoss * weightUpper) *
          selected.family.enncard ∧
      WZ2PaperPureCWAAtNearbyScales
        selected.family outputConstant := by
  let coordinateCount := geometricScaleCount epsilon
  have coordinateCountPos : 0 < coordinateCount :=
    Nat.succ_pos _
  let scales :
      Fin coordinateCount →
        WZ2PaperRequestedScale delta :=
    geometricRequestedScales
      delta epsilon delta_pos delta_lt_one
        epsilon_pos coordinateCount
  let coverData :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant :=
    fun coordinate =>
      Classical.choice
        (ambient.2.2.2 (scales coordinate))
  let Vertex : Fin coordinateCount → Type :=
    fun coordinate =>
      Fin (coverData coordinate).scaleData.coarse.card
  let parent :
      ∀ coordinate,
        Fin preSelected.family.card →
          Vertex coordinate :=
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
  let selected : WZ2PaperPureTubeSubfamily fine :=
    {
      family := selectedPre.family
      embedding :=
        {
          toFun := fun index =>
            preSelected.embedding
              (selectedPre.embedding index)
          inj' :=
            Function.Injective.comp
              preSelected.embedding.inj'
              selectedPre.embedding.inj'
        }
      tube_eq := fun index =>
        (selectedPre.tube_eq index).trans
          (preSelected.tube_eq
            (selectedPre.embedding index))
    }
  let degreeConstant : ENNReal :=
    16 * (coordinateCount : ENNReal) *
      (Nat.log 2
          (2 * preSelected.family.card) + 1 :
        ENNReal) ^ coordinateCount
  let regularizationLoss : ENNReal :=
    8 *
      (Nat.log 2
          (2 * preSelected.family.card) + 1 :
        ENNReal) ^ (coordinateCount + 1)
  have totalWeightPos :
      0 <
        ∑ index : Fin preSelected.family.card,
          externalWeight index := by
    have fineCardPos : 0 < fine.card := by
      have preCardPos :
          0 < preSelected.family.card :=
        preSelectedNonempty
      have index : Fin preSelected.family.card :=
        ⟨0, preCardPos⟩
      have hindex :=
        (preSelected.embedding index).isLt
      omega
    have fineENNPos : 0 < fine.enncard := by
      change (0 : ENNReal) < (fine.card : ENNReal)
      exact_mod_cast fineCardPos
    exact
      (ENNReal.mul_pos
        normalizationWeight_ne_zero fineENNPos.ne').trans_le
        total_weight_lower
  have selectedIndicesNonempty :
      selectedIndices.Nonempty := by
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
    exact
      (not_le_of_gt totalWeightPos) retained
  have selectedNonempty :
      selected.family.Nonempty := by
    change 0 < selectedIndices.card
    exact selectedIndicesNonempty.card_pos
  have degreeTop : degreeConstant ≠ ⊤ :=
    ENNReal.coe_ne_top
  have regularizationTop :
      regularizationLoss ≠ ⊤ :=
    ENNReal.coe_ne_top
  have embeddingMem :
      ∀ index : Fin selectedPre.family.card,
        selectedPre.embedding index ∈ selectedIndices := by
    intro index
    exact
      Finset.orderEmbOfFin_mem
        selectedIndices rfl index
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
          externalWeight
            (selectedPre.embedding index)) =
        ∑ source ∈ selectedIndices,
          externalWeight source := by
    calc
      (∑ index : Fin selectedPre.family.card,
          externalWeight
            (selectedPre.embedding index)) =
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
            externalWeight
              (selectedPre.embedding index) := by
    have retained := regularized.retained_weight
    have cardFin :
        Fintype.card
            (Fin preSelected.family.card) =
          preSelected.family.card := by
      simp
    rw [cardFin] at retained
    change
      (∑ index : Fin preSelected.family.card,
          externalWeight index) ≤
        regularizationLoss *
          ∑ index ∈ selectedIndices,
            externalWeight index at retained
    rwa [selectedWeightEq]
  have selectedWeightBand :
      ∀ index : Fin selectedPre.family.card,
        regularized.weightLevel ≤
            externalWeight
              (selectedPre.embedding index) ∧
          externalWeight
              (selectedPre.embedding index) ≤
            2 * regularized.weightLevel := by
    intro index
    exact
      regularized.weight_band
        (selectedPre.embedding index)
        (embeddingMem index)
  have selectedWeightLevelTop :
      regularized.weightLevel ≠ ⊤ := by
    let index : Fin selectedPre.family.card :=
      ⟨0, selectedNonempty⟩
    have lower :=
      (selectedWeightBand index).1
    have externalTop :
        externalWeight
            (selectedPre.embedding index) ≠ ⊤ :=
      ne_top_of_le_ne_top weightUpper_ne_top
        (weight_upper
          (selectedPre.embedding index))
    intro weightLevelTop
    rw [weightLevelTop] at lower
    exact externalTop (top_unique lower)
  have selectedWeightUpper :
      (∑ index : Fin selectedPre.family.card,
          externalWeight
            (selectedPre.embedding index)) ≤
        selected.family.enncard * weightUpper := by
    calc
      (∑ index : Fin selectedPre.family.card,
          externalWeight
            (selectedPre.embedding index)) ≤
          ∑ _index : Fin selectedPre.family.card,
            weightUpper := by
        apply Finset.sum_le_sum
        intro index _
        exact
          weight_upper
            (selectedPre.embedding index)
      _ =
          selected.family.enncard * weightUpper := by
        have cardEq :
            selectedPre.family.card =
              selected.family.card := rfl
        simp [Finset.sum_const,
          Kakeya.Streamlined.TubeFamily.enncard,
          cardEq]
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
              externalWeight
                (selectedPre.embedding index) :=
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
              (selected.embedding source) =
                vertex).card := by
    intro coordinate vertex
    let left :=
      selectedIndices.filter fun source =>
        parent coordinate source = vertex
    let right :=
      (Finset.univ :
        Finset (Fin selectedPre.family.card)).filter fun source =>
          parent coordinate
              (selectedPre.embedding source) =
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
        Fintype.card
            (Fin preSelected.family.card) =
          preSelected.family.card := by
      simp
    have main' :
        ((selectedIndices.filter fun source =>
          parent coordinate source = first).card : ENNReal) ≤
          degreeConstant *
            ((selectedIndices.filter fun source =>
              parent coordinate source = second).card : ENNReal) := by
      simpa [selectedIndices, degreeConstant, cardFin] using main
    rwa [filterCard coordinate first,
      filterCard coordinate second] at main'
  let R : ENNReal :=
    ENNReal.ofReal (Real.rpow delta (-epsilon))
  have RPos : 0 < R :=
    ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos delta_pos _)
  have RTop : R ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have ROne : 1 ≤ R := by
    have h :
        (1 : ℝ) <
          Real.rpow delta (-epsilon) :=
      Real.one_lt_rpow_of_pos_of_lt_one_of_neg
        delta_pos delta_lt_one (by linarith)
    simpa [R] using
      ENNReal.ofReal_le_ofReal h.le
  have rounding :
      ∀ requested : WZ2PaperRequestedScale delta,
        ∃ coordinate : Fin coordinateCount,
          requested.1 ≤ (scales coordinate).1 ∧
          ENNReal.ofReal (scales coordinate).1 <
            R * ENNReal.ofReal requested.1 :=
    geometricRequestedScale_rounding
      delta_pos delta_lt_one epsilon_pos
      (rfl :
        coordinateCount =
          geometricScaleCount epsilon)
  let retentionConstant :=
    regularizationLoss * weightUpper
  have retentionTop : retentionConstant ≠ ⊤ :=
    ENNReal.mul_ne_top
      regularizationTop weightUpper_ne_top
  have restricted :
      wz2PaperPureNearbyRestrictionConstant
          ambientConstant normalizationWeight
          degreeConstant retentionConstant ≤
        outputConstant :=
    by
      simpa [degreeConstant, regularizationLoss,
        pureWZ2WeightedDegreeConstant,
        pureWZ2WeightedRegularizationLoss, coordinateCount]
        using restriction_absorption
  have selectedCWA :
      WZ2PaperPureCWAAtNearbyScales
        selected.family outputConstant :=
    pure_cwa_restrict_with_rounding
      ambient selected selectedNonempty
      coordinateCount coordinateCountPos scales
      degreeConstant retentionConstant
      normalizationWeight
      normalizationWeight_ne_zero
      normalizationWeight_ne_top
      retentionTop degreeTop
      cardinalityRetention degreeUniform
      RPos RTop ROne rounding
      rounding_absorption output_ne_top restricted
  exact
    ⟨selected, selectedPre,
      degreeConstant, regularizationLoss,
      regularized.weightLevel,
      selectedNonempty, degreeTop,
      regularizationTop,
      regularized.weightLevel_pos,
      selectedWeightLevelTop,
      rfl, rfl,
      rfl, rfl, rfl, ⟨fun index => index, fun _ => rfl⟩,
      retainedWeight,
      selectedWeightBand,
      cardinalityRetention,
      selectedCWA⟩

end Kakeya.Assouad

end
