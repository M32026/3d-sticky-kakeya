import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureFiniteNearbyScheduleRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteRegularizedRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization

/-!
# Pure nearby-scale regularization with external tube weights

This is the pure Definition 2.12 analogue of the historical external-weight
regularizer.  A finite representative schedule is already supplied.  We
select one whole-tube subfamily whose external weights lie in a common
dyadic band and whose parent degrees are regular at every representative
scale.  Weighted cardinality retention and degree regularity then recover
the complete pure nearby-scale CWA predicate on the selected family.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure WZ2PaperPureExternalWeightRegularizationData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {levelCount : ℕ}
    (schedule :
      WZ2PaperPureFiniteNearbyScheduleData
        (fine := family) ambientConstant outputConstant levelCount)
    (normalizationWeight weightUpper : ENNReal)
    (externalWeight : Fin family.card → ENNReal) where
  selectedIndices : Finset (Fin family.card)
  selected : Kakeya.Streamlined.TubeSubfamily family
  selected_eq :
    selected = Kakeya.Streamlined.TubeSubfamily.fromFinset
      family selectedIndices
  selected_embedding_mem :
    ∀ index : Fin selected.family.card,
      selected.embedding index ∈ selectedIndices
  selected_embedding_surjective :
    ∀ ambientIndex ∈ selectedIndices,
      ∃ index : Fin selected.family.card,
        selected.embedding index = ambientIndex
  selected_nonempty : selected.family.Nonempty
  weightLevel : ENNReal
  weightLevel_pos : 0 < weightLevel
  weightLevel_ne_top : weightLevel ≠ ⊤
  weight_band :
    ∀ index : Fin selected.family.card,
      weightLevel ≤ externalWeight (selected.embedding index) ∧
        externalWeight (selected.embedding index) ≤ 2 * weightLevel
  normalizationWeight_le_four_weightLevel :
    normalizationWeight ≤ 4 * weightLevel
  regularizationLoss : ENNReal
  regularizationLoss_eq :
    regularizationLoss =
      (8 : ENNReal) *
        (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
          (schedule.scaleCount + 1)
  retained_weight :
    (∑ index : Fin family.card, externalWeight index) ≤
      regularizationLoss *
        ∑ index : Fin selected.family.card,
          externalWeight (selected.embedding index)
  degreeConstant : ENNReal
  degreeConstant_eq :
    degreeConstant =
      16 * (schedule.scaleCount : ENNReal) *
        (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
          schedule.scaleCount
  degree_uniform :
    ∀ coordinate,
      ∀ first second :
          Fin (schedule.witness coordinate).scaleData.coarse.card,
        0 <
            ((Finset.univ :
              Finset (Fin selected.family.card)).filter fun source =>
                (schedule.witness coordinate).scaleData.cover.parent
                    (selected.embedding source) = first).card →
          0 <
            ((Finset.univ :
              Finset (Fin selected.family.card)).filter fun source =>
                (schedule.witness coordinate).scaleData.cover.parent
                    (selected.embedding source) = second).card →
          (((Finset.univ :
            Finset (Fin selected.family.card)).filter fun source =>
              (schedule.witness coordinate).scaleData.cover.parent
                  (selected.embedding source) = first).card : ENNReal) ≤
            degreeConstant *
              (((Finset.univ :
                Finset (Fin selected.family.card)).filter fun source =>
                  (schedule.witness coordinate).scaleData.cover.parent
                      (selected.embedding source) = second).card : ENNReal)
  cardinality_retention :
    normalizationWeight * family.enncard ≤
      (regularizationLoss * weightUpper) *
        selected.family.enncard
  pure_cwa_nearby :
    WZ2PaperPureCWAAtNearbyScales
      selected.family outputConstant

/-- Apply simultaneous weighted selection to one pure finite nearby schedule. -/
theorem WZ2PaperPureFiniteNearbyScheduleData.regularizeExternalWeight
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule :
      WZ2PaperPureFiniteNearbyScheduleData
        (fine := family) ambientConstant outputConstant levelCount)
    (ambient :
      WZ2PaperPureCWAAtNearbyScales family ambientConstant)
    (familyNonempty : family.Nonempty)
    (externalWeight : Fin family.card → ENNReal)
    (normalizationWeight_ne_zero : normalizationWeight ≠ 0)
    (normalizationWeight_ne_top : normalizationWeight ≠ ⊤)
    (weightUpper_ne_top : weightUpper ≠ ⊤)
    (mass_lower :
      normalizationWeight * family.enncard ≤
        ∑ index : Fin family.card, externalWeight index)
    (weight_upper : ∀ index, externalWeight index ≤ weightUpper)
    (output_finite : WZ2PaperFiniteErrorConstant outputConstant)
    (absorb :
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
            schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
            (schedule.scaleCount + 1)
      max degreeConstant
          ((normalizationWeight⁻¹ *
              (ambientConstant *
                (regularizationLoss * weightUpper) *
                degreeConstant)) *
            ambientConstant) ≤
        outputConstant) :
    Nonempty
      (WZ2PaperPureExternalWeightRegularizationData
        schedule normalizationWeight weightUpper externalWeight) := by
  classical
  let Parent : Fin schedule.scaleCount → Type :=
    fun coordinate =>
      Fin (schedule.witness coordinate).scaleData.coarse.card
  let parent : ∀ coordinate, Fin family.card → Parent coordinate :=
    fun coordinate =>
      (schedule.witness coordinate).scaleData.cover.parent
  rcases
      simultaneous_degree_regularization_with_support_and_weight_band
        schedule.scaleCount Parent parent externalWeight
    with
      ⟨selectedIndices, degreeUniformRaw, retainedWeightRaw,
        weightPositiveRaw, weightFloorRaw, weightBandRaw⟩
  rcases weightBandRaw schedule.scaleCount_pos with
    ⟨weightLevel, weightLevelPos, weightBandSelected⟩
  let selected : Kakeya.Streamlined.TubeSubfamily family :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset family selectedIndices
  let regularizationLoss : ENNReal :=
    (8 : ENNReal) *
      (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
        (schedule.scaleCount + 1)
  let degreeConstant : ENNReal :=
    16 * (schedule.scaleCount : ENNReal) *
      (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
        schedule.scaleCount
  have hcard : Fintype.card (Fin family.card) = family.card := by simp
  have hembedding_mem :
      ∀ index : Fin selected.family.card,
        selected.embedding index ∈ selectedIndices := by
    intro index
    exact Finset.orderEmbOfFin_mem selectedIndices rfl index
  have hselected_sum :
      (∑ index : Fin selected.family.card,
          externalWeight (selected.embedding index)) =
        ∑ index ∈ selectedIndices, externalWeight index := by
    have himage :
        Finset.image selected.embedding
            (Finset.univ : Finset (Fin selected.family.card)) =
          selectedIndices := by
      ext index
      constructor
      · rintro (hindex : index ∈ Finset.image selected.embedding Finset.univ)
        rcases Finset.mem_image.mp hindex with ⟨source, _, rfl⟩
        exact hembedding_mem source
      · intro hindex
        let source : Fin selected.family.card :=
          (selectedIndices.orderIsoOfFin rfl).symm ⟨index, hindex⟩
        have heq : selected.embedding source = index := by
          exact congrArg Subtype.val
            ((selectedIndices.orderIsoOfFin rfl).apply_symm_apply
              ⟨index, hindex⟩)
        exact Finset.mem_image.mpr ⟨source, Finset.mem_univ _, heq⟩
    calc
      (∑ index : Fin selected.family.card,
          externalWeight (selected.embedding index)) =
          ∑ index ∈ Finset.image selected.embedding Finset.univ,
            externalWeight index := by
        exact (Finset.sum_image (fun first _ second _ heq =>
          selected.embedding.injective heq)).symm
      _ = ∑ index ∈ selectedIndices, externalWeight index := by
        rw [himage]
  have hretained :
      (∑ index : Fin family.card, externalWeight index) ≤
        regularizationLoss *
          ∑ index : Fin selected.family.card,
            externalWeight (selected.embedding index) := by
    rw [hselected_sum]
    simpa [regularizationLoss, hcard] using retainedWeightRaw
  have htotal_pos :
      0 < ∑ index : Fin family.card, externalWeight index := by
    have hfamilyCardPos : 0 < family.enncard := by
      change 0 < (family.card : ENNReal)
      exact_mod_cast familyNonempty
    have hleft : 0 < normalizationWeight * family.enncard :=
      ENNReal.mul_pos normalizationWeight_ne_zero hfamilyCardPos.ne'
    exact hleft.trans_le mass_lower
  have hselected_nonempty : selected.family.Nonempty := by
    by_contra hnot
    have hcardZero : selected.family.card = 0 := by
      simpa [Kakeya.Streamlined.TubeFamily.Nonempty, not_lt] using hnot
    have hsumZero :
        (∑ index : Fin selected.family.card,
          externalWeight (selected.embedding index)) = 0 := by
      apply Finset.sum_eq_zero
      intro index _
      exact Fin.elim0 (Fin.cast hcardZero index)
    rw [hsumZero, mul_zero] at hretained
    exact (not_le.mpr htotal_pos) hretained
  have hweightBand :
      ∀ index : Fin selected.family.card,
        weightLevel ≤ externalWeight (selected.embedding index) ∧
          externalWeight (selected.embedding index) ≤ 2 * weightLevel := by
    intro index
    exact weightBandSelected
      (selected.embedding index) (hembedding_mem index)
  have hweightLevelTop : weightLevel ≠ ⊤ := by
    let index : Fin selected.family.card :=
      ⟨0, hselected_nonempty⟩
    have hupper :
        externalWeight (selected.embedding index) ≠ ⊤ :=
      ne_top_of_le_ne_top weightUpper_ne_top
        (weight_upper (selected.embedding index))
    intro htop
    have hlower := (hweightBand index).1
    rw [htop] at hlower
    exact hupper (top_unique hlower)
  have hnormalizationWeightLe :
      normalizationWeight ≤ 4 * weightLevel := by
    let selectedIndex : Fin selected.family.card :=
      ⟨0, hselected_nonempty⟩
    have hfloor :
        (∑ source : Fin family.card, externalWeight source) /
              (2 * family.enncard) ≤
          externalWeight (selected.embedding selectedIndex) := by
      simpa [Kakeya.Streamlined.TubeFamily.enncard] using
        weightFloorRaw schedule.scaleCount_pos
          (selected.embedding selectedIndex)
          (hembedding_mem selectedIndex)
    have hweight :
        externalWeight (selected.embedding selectedIndex) ≤
          2 * weightLevel :=
      (hweightBand selectedIndex).2
    have hdenominatorZero : 2 * family.enncard ≠ 0 := by
      apply mul_ne_zero (by norm_num)
      change (family.card : ENNReal) ≠ 0
      exact_mod_cast (Nat.ne_of_gt familyNonempty)
    have hdenominatorTop : 2 * family.enncard ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by norm_num) (by simp
        [Kakeya.Streamlined.TubeFamily.enncard])
    have hfamilyCardZero : family.enncard ≠ 0 := by
      change (family.card : ENNReal) ≠ 0
      exact_mod_cast (Nat.ne_of_gt familyNonempty)
    have hfamilyCardTop : family.enncard ≠ ⊤ := by
      simp [Kakeya.Streamlined.TubeFamily.enncard]
    have htotalUpper :
        (∑ source : Fin family.card, externalWeight source) ≤
          (2 * weightLevel) * (2 * family.enncard) := by
      apply (ENNReal.div_le_iff hdenominatorZero hdenominatorTop).mp
      exact hfloor.trans hweight
    have hscaled :
        normalizationWeight * family.enncard ≤
          (4 * weightLevel) * family.enncard := by
      calc
        normalizationWeight * family.enncard ≤
            ∑ source : Fin family.card, externalWeight source := mass_lower
        _ ≤ (2 * weightLevel) * (2 * family.enncard) := htotalUpper
        _ = (4 * weightLevel) * family.enncard := by ring
    exact (ENNReal.mul_le_mul_iff_left
      hfamilyCardZero hfamilyCardTop).mp hscaled
  have hdegree :
      ∀ coordinate,
        ∀ first second :
            Fin (schedule.witness coordinate).scaleData.coarse.card,
          0 <
              ((Finset.univ :
                Finset (Fin selected.family.card)).filter fun source =>
                  parent coordinate (selected.embedding source) = first).card →
            0 <
              ((Finset.univ :
                Finset (Fin selected.family.card)).filter fun source =>
                  parent coordinate (selected.embedding source) = second).card →
            (((Finset.univ :
              Finset (Fin selected.family.card)).filter fun source =>
                parent coordinate (selected.embedding source) = first).card : ENNReal) ≤
              degreeConstant *
                (((Finset.univ :
                  Finset (Fin selected.family.card)).filter fun source =>
                    parent coordinate (selected.embedding source) = second).card : ENNReal) := by
    intro coordinate first second hfirst hsecond
    have hfirstCard :=
      fromFinset_filter_card selectedIndices (parent coordinate) first
    have hsecondCard :=
      fromFinset_filter_card selectedIndices (parent coordinate) second
    have hfirstRaw :
        0 < (selectedIndices.filter fun index =>
          parent coordinate index = first).card := by
      rw [← hfirstCard]
      exact hfirst
    have hsecondRaw :
        0 < (selectedIndices.filter fun index =>
          parent coordinate index = second).card := by
      rw [← hsecondCard]
      exact hsecond
    have hraw :=
      degreeUniformRaw coordinate first second hfirstRaw hsecondRaw
    rw [← hfirstCard, ← hsecondCard] at hraw
    change
      (((Finset.univ :
        Finset (Fin selectedIndices.card)).filter fun source =>
          parent coordinate (selectedIndices.orderEmbOfFin rfl source) =
            first).card : ENNReal) ≤
        degreeConstant *
          (((Finset.univ :
            Finset (Fin selectedIndices.card)).filter fun source =>
              parent coordinate (selectedIndices.orderEmbOfFin rfl source) =
                second).card : ENNReal)
    simpa [degreeConstant, hcard] using hraw
  have hselectedWeightUpper :
      (∑ index : Fin selected.family.card,
          externalWeight (selected.embedding index)) ≤
        weightUpper * selected.family.enncard := by
    calc
      (∑ index : Fin selected.family.card,
          externalWeight (selected.embedding index)) ≤
          ∑ _index : Fin selected.family.card, weightUpper := by
        apply Finset.sum_le_sum
        intro index _
        exact weight_upper (selected.embedding index)
      _ = weightUpper * selected.family.enncard := by
        simp [Finset.sum_const,
          Kakeya.Streamlined.TubeFamily.enncard, mul_comm]
  have hcardinality :
      normalizationWeight * family.enncard ≤
        (regularizationLoss * weightUpper) *
          selected.family.enncard := by
    calc
      normalizationWeight * family.enncard ≤
          ∑ index : Fin family.card, externalWeight index := mass_lower
      _ ≤ regularizationLoss *
            ∑ index : Fin selected.family.card,
              externalWeight (selected.embedding index) := hretained
      _ ≤ regularizationLoss *
            (weightUpper * selected.family.enncard) := by gcongr
      _ = (regularizationLoss * weightUpper) *
            selected.family.enncard := by ring
  have hpureCWA :
      WZ2PaperPureCWAAtNearbyScales
        selected.family outputConstant :=
    schedule.regularize ambient selected hselected_nonempty
      output_finite normalizationWeight_ne_zero
      normalizationWeight_ne_top hcardinality hdegree (by
        simpa [regularizationLoss, degreeConstant] using absorb)
  exact
    ⟨{
      selectedIndices := selectedIndices
      selected := selected
      selected_eq := rfl
      selected_embedding_mem := hembedding_mem
      selected_embedding_surjective := by
        intro ambientIndex hambient
        let index : Fin selected.family.card :=
          (selectedIndices.orderIsoOfFin rfl).symm
            ⟨ambientIndex, hambient⟩
        exact ⟨index, congrArg Subtype.val
          ((selectedIndices.orderIsoOfFin rfl).apply_symm_apply
            ⟨ambientIndex, hambient⟩)⟩
      selected_nonempty := hselected_nonempty
      weightLevel := weightLevel
      weightLevel_pos := weightLevelPos
      weightLevel_ne_top := hweightLevelTop
      weight_band := hweightBand
      normalizationWeight_le_four_weightLevel := hnormalizationWeightLe
      regularizationLoss := regularizationLoss
      regularizationLoss_eq := rfl
      retained_weight := hretained
      degreeConstant := degreeConstant
      degreeConstant_eq := rfl
      degree_uniform := hdegree
      cardinality_retention := hcardinality
      pure_cwa_nearby := hpureCWA
    }⟩

end Kakeya.Assouad

end
