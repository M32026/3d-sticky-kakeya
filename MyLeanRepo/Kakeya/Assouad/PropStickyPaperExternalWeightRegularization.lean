import MyLeanRepo.Kakeya.Assouad.PropStickyPaperExternalWeightRegularizationStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteRegularizedRefinement

/-! # Nearby-scale regularization using external source shaded-mass weights -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_external_weight_regularization :
    WZ2PaperExternalWeightRegularizationStatement := by
  intro hSchedule delta hdelta hdelta1 family hfamily hline
    ambientConstant outputConstant normalizationWeight weightUpper
    hnorm_nz hnorm_top hweight_top externalWeight hmass_lower hweight_upper
    levelCount hambient hambient_top hpower hout hcwa
    degreeConstant regularizationLoss habsorb
  classical

  rcases
      hSchedule levelCount hdelta hdelta1 hambient hambient_top
        hpower hout hcwa
    with ⟨schedule⟩

  let Parent : Fin schedule.scaleCount → Type :=
    fun coordinate =>
      Fin (schedule.witness coordinate).scaleData.coarse.card
  let parent :
      ∀ coordinate, Fin family.card → Parent coordinate :=
    fun coordinate =>
      (schedule.witness coordinate).scaleData.cover.parent

  rcases
      simultaneous_degree_regularization_with_support_and_weight_band
        schedule.scaleCount Parent parent externalWeight
    with
      ⟨selectedIndices, huniform, hretained_raw,
        hpositive, hfloor_raw, hweight_band_raw⟩
  rcases hweight_band_raw schedule.scaleCount_pos with
    ⟨selectedWeightLevel, hselectedWeightLevelPos,
      hselectedWeightBandRaw⟩

  let logTerm : ENNReal :=
    (Nat.log 2 (2 * family.card) + 1 : ENNReal)
  have hcard :
      Fintype.card (Fin family.card) = family.card := by
    simp
  have hlog_eq :
      (Nat.log 2 (2 * Fintype.card (Fin family.card)) + 1 :
          ENNReal) =
        logTerm := by
    rw [hcard]

  let actualDegreeConstant : ENNReal :=
    16 * (schedule.scaleCount : ENNReal) *
      logTerm ^ schedule.scaleCount
  let actualRegularizationLoss : ENNReal :=
    (8 : ENNReal) *
      logTerm ^ (schedule.scaleCount + 1)

  have hlog_one : (1 : ENNReal) ≤ logTerm := by
    dsimp only [logTerm]
    have hnonnegative :
        (0 : ENNReal) ≤
          (Nat.log 2 (2 * family.card) : ENNReal) := by
      positivity
    exact le_add_of_nonneg_left hnonnegative

  have hscale_count :
      (schedule.scaleCount : ENNReal) ≤
        ((levelCount + 1 : ℕ) : ENNReal) := by
    exact_mod_cast schedule.scaleCount_le

  have hdegree_constant :
      actualDegreeConstant ≤ degreeConstant := by
    dsimp only [actualDegreeConstant]
    calc
      16 * (schedule.scaleCount : ENNReal) *
            logTerm ^ schedule.scaleCount ≤
          16 * ((levelCount + 1 : ℕ) : ENNReal) *
            logTerm ^ schedule.scaleCount := by
        gcongr
      _ ≤ 16 * ((levelCount + 1 : ℕ) : ENNReal) *
            logTerm ^ (levelCount + 1) := by
        exact
          mul_le_mul_right
            (pow_le_pow_right' hlog_one schedule.scaleCount_le) _

  have hexponent :
      schedule.scaleCount + 1 ≤ levelCount + 2 := by
    simpa [Nat.add_assoc] using
      Nat.add_le_add_right schedule.scaleCount_le 1

  have hregularization_loss :
      actualRegularizationLoss ≤ regularizationLoss := by
    dsimp only [actualRegularizationLoss]
    exact
      mul_le_mul_right
        (pow_le_pow_right' hlog_one hexponent) _

  have hretained :
      (∑ index : Fin family.card, externalWeight index) ≤
        actualRegularizationLoss *
          (∑ index ∈ selectedIndices, externalWeight index) := by
    rw [hlog_eq] at hretained_raw
    exact hretained_raw

  have hfloor :
      0 < schedule.scaleCount →
        ∀ index ∈ selectedIndices,
          (∑ source : Fin family.card, externalWeight source) /
                (2 * family.card : ENNReal) ≤
            externalWeight index := by
    intro hcount
    have h := hfloor_raw hcount
    intro index hindex
    have hindex_floor := h index hindex
    rw [hcard] at hindex_floor
    exact hindex_floor

  let totalWeight : ENNReal :=
    ∑ index : Fin family.card, externalWeight index

  let selected : Kakeya.Streamlined.TubeSubfamily family :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      family selectedIndices

  let selectedWeight : ENNReal :=
    ∑ index : Fin selected.family.card,
      externalWeight (selected.embedding index)

  have hembedding_mem :
      ∀ index : Fin selected.family.card,
        selected.embedding index ∈ selectedIndices := by
    intro index
    dsimp only [selected]
    exact
      Finset.orderEmbOfFin_mem selectedIndices rfl index

  have himage :
      Finset.image selected.embedding
          (Finset.univ :
            Finset (Fin selected.family.card)) =
        selectedIndices := by
    ext index
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨selectedIndex, rfl⟩
      exact hembedding_mem selectedIndex
    · intro hindex
      let selectedValue : {i // i ∈ selectedIndices} :=
        ⟨index, hindex⟩
      let selectedIndex : Fin selected.family.card :=
        (selectedIndices.orderIsoOfFin rfl).symm selectedValue
      have heq : selected.embedding selectedIndex = index := by
        dsimp only [selected, selectedIndex, selectedValue]
        exact
          congrArg Subtype.val
            ((selectedIndices.orderIsoOfFin rfl).apply_symm_apply
              ⟨index, hindex⟩)
      exact ⟨selectedIndex, heq⟩

  have hselected_weight_sum :
      selectedWeight =
        ∑ index ∈ selectedIndices, externalWeight index := by
    dsimp only [selectedWeight]
    have hsum :
        (∑ index : Fin selected.family.card,
            externalWeight (selected.embedding index)) =
          ∑ index ∈
              Finset.image selected.embedding
                (Finset.univ :
                  Finset (Fin selected.family.card)),
            externalWeight index := by
      exact
        (Finset.sum_image
          (fun first _ second _ heq =>
            selected.embedding.injective heq)).symm
    rw [hsum, himage]

  have hnormalization_pos : 0 < normalizationWeight :=
    zero_lt_iff.mpr hnorm_nz
  have hfamily_card_pos : 0 < family.card := by
    simpa [Kakeya.Streamlined.TubeFamily.Nonempty] using hfamily
  have hfamily_enncard_pos : 0 < family.enncard := by
    dsimp only [Kakeya.Streamlined.TubeFamily.enncard]
    exact_mod_cast hfamily_card_pos
  have htotal_pos : 0 < totalWeight := by
    have hproduct :
        0 < normalizationWeight * family.enncard :=
      ENNReal.mul_pos hnorm_nz hfamily_enncard_pos.ne'
    exact hproduct.trans_le hmass_lower
  have hselected_indices_nonempty :
      selectedIndices.Nonempty := by
    by_contra hempty
    have hselected_empty :
        selectedIndices = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hsum :
        ∑ index ∈ selectedIndices, externalWeight index = 0 := by
      rw [hselected_empty]
      simp
    have hzero :
        (∑ index : Fin family.card, externalWeight index) ≤ 0 := by
      rw [hsum] at hretained
      simpa using hretained
    exact (not_le.mpr htotal_pos) hzero

  have hselected_card_pos : 0 < selected.family.card := by
    dsimp only [selected]
    exact Finset.Nonempty.card_pos hselected_indices_nonempty

  have hselected_nonempty : selected.Nonempty := by
    dsimp only [selected,
      Kakeya.Streamlined.TubeSubfamily.Nonempty,
      Kakeya.Streamlined.TubeFamily.Nonempty]
    exact hselected_card_pos

  have hselected_weight_pos :
      ∀ index : Fin selected.family.card,
        0 < externalWeight (selected.embedding index) := by
    intro index
    exact
      hpositive (selected.embedding index)
        (hembedding_mem index)

  have hselected_weight_band :
      ∀ index : Fin selected.family.card,
        selectedWeightLevel ≤
            externalWeight (selected.embedding index) ∧
          externalWeight (selected.embedding index) ≤
            2 * selectedWeightLevel := by
    intro index
    exact
      hselectedWeightBandRaw
        (selected.embedding index) (hembedding_mem index)

  have hselectedWeightLevelTop :
      selectedWeightLevel ≠ ⊤ := by
    intro htop
    let index : Fin selected.family.card :=
      ⟨0, hselected_card_pos⟩
    have hLower :=
      (hselected_weight_band index).1
    have hExternalTop :
        externalWeight (selected.embedding index) ≠ ⊤ :=
      ne_top_of_le_ne_top hweight_top
        (hweight_upper (selected.embedding index))
    rw [htop] at hLower
    exact hExternalTop (top_unique hLower)

  have hselected_weight_floor :
      0 < levelCount →
        ∀ index : Fin selected.family.card,
          totalWeight / (2 * family.card : ENNReal) ≤
            externalWeight (selected.embedding index) := by
    intro _ index
    exact
      hfloor schedule.scaleCount_pos
        (selected.embedding index) (hembedding_mem index)

  have hretained' :
      totalWeight ≤
        regularizationLoss * selectedWeight := by
    have hactual :
        totalWeight ≤
          actualRegularizationLoss * selectedWeight := by
      rw [hselected_weight_sum]
      exact hretained
    exact hactual.trans (by
      gcongr)

  have hdegree_uniform :
      ∀ coordinate,
        ∀ first second :
            Fin (schedule.witness coordinate).scaleData.coarse.card,
          0 <
              ((Finset.univ :
                  Finset (Fin selected.family.card)).filter
                fun source =>
                  parent coordinate (selected.embedding source) =
                    first).card →
          0 <
              ((Finset.univ :
                  Finset (Fin selected.family.card)).filter
                fun source =>
                  parent coordinate (selected.embedding source) =
                    second).card →
          ((((Finset.univ :
              Finset (Fin selected.family.card)).filter
            fun source =>
              parent coordinate (selected.embedding source) =
                first).card : ℕ) : ENNReal) ≤
            degreeConstant *
              ((((Finset.univ :
                  Finset (Fin selected.family.card)).filter
                fun source =>
                  parent coordinate (selected.embedding source) =
                    second).card : ℕ) : ENNReal) := by
    intro coordinate first second hfirst hsecond
    have hfilter_first :
        ((Finset.univ :
            Finset (Fin selected.family.card)).filter
          fun source =>
            parent coordinate (selected.embedding source) =
              first).card =
          (selectedIndices.filter
            (fun index => parent coordinate index = first)).card :=
      fromFinset_filter_card
        selectedIndices (parent coordinate) first
    have hfilter_second :
        ((Finset.univ :
            Finset (Fin selected.family.card)).filter
          fun source =>
            parent coordinate (selected.embedding source) =
              second).card =
          (selectedIndices.filter
            (fun index => parent coordinate index = second)).card :=
      fromFinset_filter_card
        selectedIndices (parent coordinate) second
    have hfirst' :
        0 <
          (selectedIndices.filter
            (fun index => parent coordinate index = first)).card := by
      rw [← hfilter_first]
      exact hfirst
    have hsecond' :
        0 <
          (selectedIndices.filter
            (fun index => parent coordinate index = second)).card := by
      rw [← hfilter_second]
      exact hsecond
    have hraw :=
      huniform coordinate first second hfirst' hsecond'
    rw [hlog_eq] at hraw
    have hmain :
        ((selectedIndices.filter
            (fun index =>
              parent coordinate index = first)).card : ENNReal) ≤
          actualDegreeConstant *
            ((selectedIndices.filter
              (fun index =>
                parent coordinate index = second)).card :
              ENNReal) := by
      simpa [actualDegreeConstant] using hraw
    have hfirst_cast :
        (((Finset.univ :
            Finset (Fin selected.family.card)).filter
          fun source =>
            parent coordinate (selected.embedding source) =
              first).card : ENNReal) =
          ((selectedIndices.filter
            (fun index =>
              parent coordinate index = first)).card :
            ENNReal) := by
      exact_mod_cast hfilter_first
    have hsecond_cast :
        (((Finset.univ :
            Finset (Fin selected.family.card)).filter
          fun source =>
            parent coordinate (selected.embedding source) =
              second).card : ENNReal) =
          ((selectedIndices.filter
            (fun index =>
              parent coordinate index = second)).card :
            ENNReal) := by
      exact_mod_cast hfilter_second
    calc
      (((Finset.univ :
          Finset (Fin selected.family.card)).filter
        fun source =>
          parent coordinate (selected.embedding source) =
            first).card : ENNReal) =
          ((selectedIndices.filter
            (fun index =>
              parent coordinate index = first)).card :
            ENNReal) := hfirst_cast
      _ ≤ actualDegreeConstant *
            ((selectedIndices.filter
              (fun index =>
                parent coordinate index = second)).card :
              ENNReal) := hmain
      _ ≤ degreeConstant *
            ((selectedIndices.filter
              (fun index =>
                parent coordinate index = second)).card :
              ENNReal) := by
        gcongr
      _ = degreeConstant *
            (((Finset.univ :
                Finset (Fin selected.family.card)).filter
              fun source =>
                parent coordinate (selected.embedding source) =
                  second).card : ENNReal) := by
        rw [hsecond_cast]

  have hselected_weight_upper :
      selectedWeight ≤
        weightUpper * selected.family.enncard := by
    dsimp only [selectedWeight]
    calc
      (∑ index : Fin selected.family.card,
          externalWeight (selected.embedding index)) ≤
          ∑ _index : Fin selected.family.card, weightUpper := by
        apply Finset.sum_le_sum
        intro index _
        exact hweight_upper (selected.embedding index)
      _ = weightUpper * selected.family.enncard := by
        simp [Finset.sum_const, mul_comm,
          Kakeya.Streamlined.TubeFamily.enncard]

  have hcardinality_retention :
      normalizationWeight * family.enncard ≤
        (regularizationLoss * weightUpper) *
          selected.family.enncard := by
    calc
      normalizationWeight * family.enncard ≤
          totalWeight := hmass_lower
      _ ≤ regularizationLoss * selectedWeight := hretained'
      _ ≤ regularizationLoss *
            (weightUpper * selected.family.enncard) := by
        gcongr
      _ = (regularizationLoss * weightUpper) *
            selected.family.enncard := by
        ring

  have hambient_one : (1 : ENNReal) ≤ ambientConstant := by
    have htwo : (1 : ENNReal) < 2 := by norm_num
    exact le_of_lt (htwo.trans hambient)
  have houtput_one : 1 ≤ outputConstant := by
    have hsquare :
        (1 : ENNReal) ≤ ambientConstant * ambientConstant := by
      calc
        (1 : ENNReal) = 1 * 1 := by norm_num
        _ ≤ ambientConstant * ambientConstant := by
          gcongr
    exact hsquare.trans hout

  have hcwa_nearby :
      WZ2PaperCWACoversAtNearbyScales
        selected.family outputConstant :=
    schedule.regularize houtput_one hline selected
      normalizationWeight
      (regularizationLoss * weightUpper)
      degreeConstant hnorm_nz hnorm_top
      hcardinality_retention hdegree_uniform habsorb

  exact
    ⟨schedule, selected, hselected_nonempty,
      selectedWeight, rfl,
      selectedWeightLevel, hselectedWeightLevelPos,
      hselectedWeightLevelTop,
      hselected_weight_band, hselected_weight_pos,
      hselected_weight_floor, regularizationLoss, rfl,
      hretained', degreeConstant, rfl, hdegree_uniform,
      hcardinality_retention, hcwa_nearby⟩

end Kakeya.Assouad

end
