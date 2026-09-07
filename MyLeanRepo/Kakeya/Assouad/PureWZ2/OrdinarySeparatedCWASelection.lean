import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryLineConflictPacking
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ExtremalSpatialCellCWAProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PaperShadingMassFinite
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.WeightedGraphSelection

/-!
# Pre-balancing ordinary separation with rebuilt pure CWA

Select one weighted independent set in the frozen literal source-conflict
graph.  The selection is made before balancing.  Pure nearby CWA is rebuilt
on the selected family by the closed weighted restriction theorem; it is not
inherited by an arbitrary subfamily.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The fixed loss paid by one ordinary source-separation coloring. -/
def pureWZ2OrdinarySeparationLoss : ENNReal :=
  pureWZ2OrdinaryLineConflictDegree + 1

/--
One pre-balancing source-separated selection with a fresh pure nearby CWA.
-/
structure PureWZ2OrdinarySeparatedCWASelectionData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) where
  selected : WZ2PaperPureTubeSubfamily family
  selected_nonempty : selected.family.Nonempty
  selectedShading : WZ1PaperTubeShading selected.family
  selectedShading_eq :
    selectedShading =
      restrictPaperShading selected.toTubeSubfamily shading
  selected_mass_pos : 0 < selectedShading.mass
  retentionLoss : ENNReal
  retentionLoss_ne_top : retentionLoss ≠ ⊤
  retention_loss_le :
    retentionLoss ≤
      pureWZ2OrdinarySeparationLoss *
        pureWZ2SpatialCellRegularizationLoss 1 family.card
  retained_mass :
    shading.mass ≤
      retentionLoss * selectedShading.mass
  strongly_separated :
    ∀ first second, first ≠ second →
      wz2PaperLiteralSourceSeparationFactor * delta <
        wz1PaperLineDistance
          (selected.family.tube first)
          (selected.family.tube second)
  outputConstant : ENNReal
  outputConstant_ne_top : outputConstant ≠ ⊤
  pure_cwa :
    WZ2PaperPureCWAAtNearbyScales
      selected.family outputConstant

/--
Select a source-separated subfamily and rebuild pure nearby CWA on it.

The output constant is explicit so a caller may absorb both the finite
coloring loss and the actual finite CWA restriction constants uniformly.
-/
theorem pureWZ2_ordinary_separated_cwa_selection
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (ambientConstant : ENNReal)
    (ambient :
      WZ2PaperPureCWAAtNearbyScales family ambientConstant)
    (line : WZ1PaperIsLineClass family)
    (boundedBase : HasBoundedBase family 4)
    (shadingMassPos : 0 < shading.mass)
    (deltaLtOne : delta < 1) :
    Nonempty
      (PureWZ2OrdinarySeparatedCWASelectionData
        shading) := by
  let relation : Fin family.card → Fin family.card → Prop :=
    fun first second =>
      first ≠ second ∧
        wz1PaperLineDistance
            (family.tube first) (family.tube second) ≤
          wz2PaperLiteralSourceSeparationFactor * delta
  have relationSymmetric :
      ∀ first second,
        relation first second → relation second first := by
    intro first second related
    refine ⟨related.1.symm, ?_⟩
    rw [wz1PaperLineDistance_symm]
    exact related.2
  have relationIrreflexive :
      ∀ index, ¬ relation index index := by
    intro index related
    exact related.1 rfl
  have relationDegree :
      ∀ fixed,
        (Finset.univ.filter fun other =>
          relation fixed other).card ≤
            pureWZ2OrdinaryLineConflictDegree := by
    intro fixed
    have boundedBaseEight : HasBoundedBase family 8 := by
      intro index
      exact (boundedBase index).trans (by norm_num)
    let allConflicts :=
      Finset.univ.filter fun other =>
        wz1PaperLineDistance
            (family.tube other) (family.tube fixed) ≤
          wz2PaperLiteralSourceSeparationFactor * delta
    have subset :
        (Finset.univ.filter fun other =>
          relation fixed other) ⊆ allConflicts := by
      intro other otherMem
      have related := (Finset.mem_filter.mp otherMem).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [wz1PaperLineDistance_symm]
      exact related.2
    exact
      (Finset.card_le_card subset).trans <|
        pureWZ2_ordinary_line_conflict_degree
          ambient.1 line boundedBaseEight ambient.2.2.1 fixed
  let weight : Fin family.card → ENNReal :=
    fun index => volume (shading.carrier index)
  rcases
      pureWZ2_greedy_independent_set_weighted
        (D := pureWZ2OrdinaryLineConflictDegree)
        (weight := weight)
        relationSymmetric relationIrreflexive
        (fun index => by
          simpa only [relation] using relationDegree index)
    with
    ⟨selectedIndices, independent, retained⟩
  let selectedPre :=
    WZ2PaperPureTubeSubfamily.fromFinset family selectedIndices
  have totalWeight :
      (∑ index : Fin family.card, weight index) = shading.mass := by
    rfl
  have selectedWeight :
      (∑ index ∈ selectedIndices, weight index) =
        ∑ index : Fin selectedPre.family.card,
          weight (selectedPre.embedding index) := by
    let equivalence : Fin selectedIndices.card ≃ selectedIndices :=
      (selectedIndices.orderIsoOfFin rfl).toEquiv
    exact (
      (Fintype.sum_equiv equivalence
        (fun index : Fin selectedIndices.card =>
          weight (selectedPre.embedding index))
        (fun index : selectedIndices => weight index.1)
        (fun _ => rfl)).trans
          (Finset.sum_coe_sort selectedIndices weight)).symm
  have selectedIndicesNonempty : selectedIndices.Nonempty := by
    by_contra empty
    have selectedEq : selectedIndices = ∅ := by
      simpa using empty
    have selectedSumZero :
        (∑ index ∈ selectedIndices, weight index) = 0 := by
      rw [selectedEq]
      simp
    rw [selectedSumZero, mul_zero, totalWeight] at retained
    exact (not_le_of_gt shadingMassPos) retained
  have selectedPreNonempty : selectedPre.family.Nonempty := by
    exact selectedIndicesNonempty.card_pos
  have strongSeparation :
      ∀ first second, first ≠ second →
        wz2PaperLiteralSourceSeparationFactor * delta <
          wz1PaperLineDistance
            (selectedPre.family.tube first)
            (selectedPre.family.tube second) := by
    intro first second indicesNe
    have firstMem :
        selectedPre.embedding first ∈ selectedIndices :=
      Finset.orderEmbOfFin_mem selectedIndices rfl first
    have secondMem :
        selectedPre.embedding second ∈ selectedIndices :=
      Finset.orderEmbOfFin_mem selectedIndices rfl second
    have ambientNe :
        selectedPre.embedding first ≠
          selectedPre.embedding second :=
      selectedPre.embedding.injective.ne indicesNe
    have notRelated :=
      independent
        (selectedPre.embedding first) firstMem
        (selectedPre.embedding second) secondMem ambientNe
    rw [selectedPre.tube_eq, selectedPre.tube_eq]
    exact
      lt_of_not_ge fun distanceLe =>
        notRelated ⟨ambientNe, distanceLe⟩
  have familyNonempty : family.Nonempty := by
    exact
      lt_of_le_of_lt (Nat.zero_le _)
        (selectedPre.embedding ⟨0, selectedPreNonempty⟩).isLt
  have familyCardNe : family.enncard ≠ 0 := by
    change (family.card : ENNReal) ≠ 0
    exact_mod_cast (Nat.ne_of_gt familyNonempty)
  have familyCardTop : family.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have shadingMassTop : shading.mass ≠ ⊤ :=
    wz1PaperTubeShading_mass_ne_top shading
  have separationLossNe :
      pureWZ2OrdinarySeparationLoss ≠ 0 := by
    simp [pureWZ2OrdinarySeparationLoss]
  have separationLossTop :
      pureWZ2OrdinarySeparationLoss ≠ ⊤ := by
    simp [pureWZ2OrdinarySeparationLoss]
  let normalizationWeight :=
    shading.mass * pureWZ2OrdinarySeparationLoss⁻¹ *
      family.enncard⁻¹
  have normalizationWeightNe : normalizationWeight ≠ 0 := by
    apply mul_ne_zero
    · exact
        mul_ne_zero shadingMassPos.ne'
          (ENNReal.inv_ne_zero.mpr separationLossTop)
    · exact ENNReal.inv_ne_zero.mpr familyCardTop
  have normalizationWeightTop : normalizationWeight ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact
        ENNReal.mul_ne_top shadingMassTop
          (ENNReal.inv_ne_top.mpr separationLossNe)
    · exact ENNReal.inv_ne_top.mpr familyCardNe
  have normalizationIdentity :
      normalizationWeight * family.enncard =
        shading.mass * pureWZ2OrdinarySeparationLoss⁻¹ := by
    dsimp only [normalizationWeight]
    rw [mul_assoc,
      ENNReal.inv_mul_cancel familyCardNe familyCardTop,
      mul_one]
  have totalWeightLower :
      normalizationWeight * family.enncard ≤
        ∑ index : Fin selectedPre.family.card,
          weight (selectedPre.embedding index) := by
    rw [normalizationIdentity, ← selectedWeight]
    calc
      shading.mass * pureWZ2OrdinarySeparationLoss⁻¹ =
          (∑ index : Fin family.card, weight index) *
            pureWZ2OrdinarySeparationLoss⁻¹ := by
        rw [totalWeight]
      _ ≤
          (pureWZ2OrdinarySeparationLoss *
            ∑ index ∈ selectedIndices, weight index) *
              pureWZ2OrdinarySeparationLoss⁻¹ := by
        gcongr
        simpa [pureWZ2OrdinarySeparationLoss] using retained
      _ =
          ∑ index ∈ selectedIndices, weight index := by
        calc
          (pureWZ2OrdinarySeparationLoss *
                (∑ index ∈ selectedIndices, weight index)) *
                  pureWZ2OrdinarySeparationLoss⁻¹ =
              (∑ index ∈ selectedIndices, weight index) *
                (pureWZ2OrdinarySeparationLoss *
                  pureWZ2OrdinarySeparationLoss⁻¹) := by
            ac_rfl
          _ = ∑ index ∈ selectedIndices, weight index := by
            rw [ENNReal.mul_inv_cancel
              separationLossNe separationLossTop, mul_one]
  have weightUpper : ∀ index, weight (selectedPre.embedding index) ≤
      shading.mass := by
    intro index
    rw [← totalWeight]
    exact
      Finset.single_le_sum
        (fun _ _ => bot_le) (Finset.mem_univ _)
  let outputConstant : ENNReal :=
    max
      (ENNReal.ofReal (Real.rpow delta (-1)) * ambientConstant)
      (wz2PaperPureNearbyRestrictionConstant
        ambientConstant normalizationWeight
        (pureWZ2SpatialCellDegreeConstant
          1 selectedPre.family.card)
        (pureWZ2SpatialCellRegularizationLoss
            1 selectedPre.family.card *
          shading.mass))
  have outputTop : outputConstant ≠ ⊤ := by
    apply max_ne_top
    · exact
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          ambient.2.1.2
    · unfold wz2PaperPureNearbyRestrictionConstant
      apply max_ne_top ambient.2.1.2
      apply max_ne_top ENNReal.coe_ne_top
      exact
        ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.inv_ne_top.mpr normalizationWeightNe)
            (ENNReal.mul_ne_top
              (ENNReal.mul_ne_top ambient.2.1.2
                (ENNReal.mul_ne_top ENNReal.coe_ne_top
                  shadingMassTop))
              ENNReal.coe_ne_top))
          ambient.2.1.2
  have roundingAbsorption :
      ENNReal.ofReal (Real.rpow delta (-1)) *
          ambientConstant ≤ outputConstant :=
    le_max_left _ _
  have restrictionAbsorption :
      wz2PaperPureNearbyRestrictionConstant
          ambientConstant normalizationWeight
          (pureWZ2SpatialCellDegreeConstant
            1 selectedPre.family.card)
          (pureWZ2SpatialCellRegularizationLoss
              1 selectedPre.family.card *
            shading.mass) ≤
        outputConstant :=
    le_max_right _ _
  rcases
      pureWZ2_weighted_restricted_cwa_actual
        ambient selectedPre selectedPreNonempty
        (fun index => weight (selectedPre.embedding index))
        normalizationWeight shading.mass
        normalizationWeightNe normalizationWeightTop shadingMassTop
        totalWeightLower weightUpper
        1 (by norm_num) ambient.1 deltaLtOne
        outputTop roundingAbsorption
        restrictionAbsorption
    with
    ⟨selectedPost, selectedPostNonempty, _selectedPostIndices,
      postRetained, _selectedWeightFloor, selectedCWA⟩
  let selected :=
    WZ2PaperPureTubeSubfamily.comp selectedPre selectedPost
  let selectedShading :=
    restrictPaperShading selected.toTubeSubfamily shading
  have finalStrongSeparation :
      ∀ first second, first ≠ second →
        wz2PaperLiteralSourceSeparationFactor * delta <
          wz1PaperLineDistance
            (selected.family.tube first)
            (selected.family.tube second) := by
    intro first second indicesNe
    change
      wz2PaperLiteralSourceSeparationFactor * delta <
        wz1PaperLineDistance
          (selectedPost.family.tube first)
          (selectedPost.family.tube second)
    rw [selectedPost.tube_eq, selectedPost.tube_eq]
    exact
      strongSeparation
        (selectedPost.embedding first)
        (selectedPost.embedding second)
        (selectedPost.embedding.injective.ne indicesNe)
  have finalRetention :
      shading.mass ≤
        (pureWZ2OrdinarySeparationLoss *
          pureWZ2SpatialCellRegularizationLoss
            1 selectedPre.family.card) *
          selectedShading.mass := by
    calc
      shading.mass =
          ∑ index : Fin family.card, weight index := totalWeight.symm
      _ ≤
          pureWZ2OrdinarySeparationLoss *
            ∑ index : Fin selectedPre.family.card,
              weight (selectedPre.embedding index) := by
        simpa [pureWZ2OrdinarySeparationLoss, selectedWeight] using
          retained
      _ ≤
          pureWZ2OrdinarySeparationLoss *
            (pureWZ2SpatialCellRegularizationLoss
                1 selectedPre.family.card *
              ∑ index : Fin selectedPost.family.card,
                weight
                  (selectedPre.embedding
                    (selectedPost.embedding index))) := by
        gcongr
      _ ≤
          pureWZ2OrdinarySeparationLoss *
            (pureWZ2SpatialCellRegularizationLoss
                1 selectedPre.family.card *
              selectedShading.mass) := by
        rfl
      _ =
          (pureWZ2OrdinarySeparationLoss *
            pureWZ2SpatialCellRegularizationLoss
              1 selectedPre.family.card) *
            selectedShading.mass := by ring
  have selectedMassPos : 0 < selectedShading.mass := by
    by_contra massNotPos
    have massZero : selectedShading.mass = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp massNotPos)
    rw [massZero, mul_zero] at finalRetention
    exact (not_le_of_gt shadingMassPos) finalRetention
  have selectedPreCardLe :
      selectedPre.family.card ≤ family.card := by
    change selectedIndices.card ≤ family.card
    simpa using Finset.card_le_univ selectedIndices
  have regularizationLossLe :
      pureWZ2SpatialCellRegularizationLoss
          1 selectedPre.family.card ≤
        pureWZ2SpatialCellRegularizationLoss 1 family.card := by
    have logLe :
        Nat.log 2 (2 * selectedPre.family.card) ≤
          Nat.log 2 (2 * family.card) :=
      Nat.log_mono_right
        (Nat.mul_le_mul_left 2 selectedPreCardLe)
    unfold pureWZ2SpatialCellRegularizationLoss
    gcongr
  have retentionLossTop :
      pureWZ2OrdinarySeparationLoss *
          pureWZ2SpatialCellRegularizationLoss
            1 selectedPre.family.card ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have retentionLossLe :
      pureWZ2OrdinarySeparationLoss *
          pureWZ2SpatialCellRegularizationLoss
            1 selectedPre.family.card ≤
        pureWZ2OrdinarySeparationLoss *
          pureWZ2SpatialCellRegularizationLoss 1 family.card := by
    gcongr
  exact
    ⟨{
      selected := selected
      selected_nonempty := selectedPostNonempty
      selectedShading := selectedShading
      selectedShading_eq := rfl
      selected_mass_pos := selectedMassPos
      retentionLoss :=
        pureWZ2OrdinarySeparationLoss *
          pureWZ2SpatialCellRegularizationLoss
            1 selectedPre.family.card
      retentionLoss_ne_top := retentionLossTop
      retention_loss_le := retentionLossLe
      retained_mass := finalRetention
      strongly_separated := finalStrongSeparation
      outputConstant := outputConstant
      outputConstant_ne_top := outputTop
      pure_cwa := selectedCWA
    }⟩

end Kakeya.Assouad

end
