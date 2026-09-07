import MyLeanRepo.Kakeya.Assouad.PropStickyNestedWeightedParentRegularization
import MyLeanRepo.Kakeya.Assouad.PropStickyNestedFiberUniformity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCallerCoarsePrefixClasses
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDirectOwnerPreparation

/-!
# Fixed-loss nested selection of final owner parents

The index set is the retained owner-parent family itself, not the whole
ambient caller family.  Apply nested lower pruning with constant weight one
along the actual caller-prefix quotient classes.  The resulting lower floors
are therefore literal parent-count floors.  The only combinatorial loss is
`2 ^ prefixDepth`; no logarithmic factor is paid per scale.

This package does not by itself claim normalized nearby CWA.  That final
transfer additionally needs one global ambient-to-retained owner cardinality
estimate.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure WZ2PaperOwnerParentNestedSelectionData
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {cover :
      WZ2PaperPartitioningCover
        fine prepared.callerStrict.coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := caller.1) fineShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover fineShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < caller.1}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover fineShading coarseCells availableFineCells
        balancing coarseData}
    (owner : WZ2PaperDirectOwnerPreparationData producer)
    (schedule :
      WZ2PaperCallerCoarsePrefixScheduleData prepared) where
  pruning :
    WZ2PaperNestedWeightedParentRegularizationData
      (Fin
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          prepared.callerStrict.coarse
          owner.exactified.retainedParents).family.card)
      (fun _ => (1 : ENNReal))
      (wz2PaperCallerCoarsePrefixScaleCount prepared)
      (fun coordinate =>
        WZ2PaperCallerCoarsePrefixClass schedule coordinate)
      (fun coordinate parent =>
        schedule.classParent coordinate
          ((Kakeya.Streamlined.TubeSubfamily.fromFinset
            prepared.callerStrict.coarse
            owner.exactified.retainedParents).embedding parent))
  selected_nonempty : pruning.selected.Nonempty
  cardinality_retention :
    (Kakeya.Streamlined.TubeSubfamily.fromFinset
        prepared.callerStrict.coarse
        owner.exactified.retainedParents).family.enncard ≤
      (2 : ENNReal) ^
          wz2PaperCallerCoarsePrefixScaleCount prepared *
        (pruning.selected.card : ENNReal)

namespace WZ2PaperOwnerParentNestedSelectionData

noncomputable def packed
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {cover :
      WZ2PaperPartitioningCover
        fine prepared.callerStrict.coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := caller.1) fineShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover fineShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < caller.1}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover fineShading coarseCells availableFineCells
        balancing coarseData}
    {owner : WZ2PaperDirectOwnerPreparationData producer}
    {schedule :
      WZ2PaperCallerCoarsePrefixScheduleData prepared}
    (_data :
      WZ2PaperOwnerParentNestedSelectionData owner schedule) :
    Kakeya.Streamlined.TubeSubfamily
      prepared.callerStrict.coarse :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset
    prepared.callerStrict.coarse owner.exactified.retainedParents

noncomputable def selectedPacked
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {cover :
      WZ2PaperPartitioningCover
        fine prepared.callerStrict.coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := caller.1) fineShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover fineShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < caller.1}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover fineShading coarseCells availableFineCells
        balancing coarseData}
    {owner : WZ2PaperDirectOwnerPreparationData producer}
    {schedule :
      WZ2PaperCallerCoarsePrefixScheduleData prepared}
    (data :
      WZ2PaperOwnerParentNestedSelectionData owner schedule) :
    Kakeya.Streamlined.TubeSubfamily data.packed.family :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset
    data.packed.family data.pruning.selected

noncomputable def selected
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {cover :
      WZ2PaperPartitioningCover
        fine prepared.callerStrict.coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := caller.1) fineShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover fineShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < caller.1}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover fineShading coarseCells availableFineCells
        balancing coarseData}
    {owner : WZ2PaperDirectOwnerPreparationData producer}
    {schedule :
      WZ2PaperCallerCoarsePrefixScheduleData prepared}
    (data :
      WZ2PaperOwnerParentNestedSelectionData owner schedule) :
    Kakeya.Streamlined.TubeSubfamily
      prepared.callerStrict.coarse :=
  data.packed.comp data.selectedPacked

theorem selected_nonempty_family
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {cover :
      WZ2PaperPartitioningCover
        fine prepared.callerStrict.coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := caller.1) fineShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover fineShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < caller.1}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover fineShading coarseCells availableFineCells
        balancing coarseData}
    {owner : WZ2PaperDirectOwnerPreparationData producer}
    {schedule :
      WZ2PaperCallerCoarsePrefixScheduleData prepared}
    (data :
      WZ2PaperOwnerParentNestedSelectionData owner schedule) :
    data.selected.family.Nonempty := by
  change 0 < data.pruning.selected.card
  exact data.selected_nonempty.card_pos

theorem selected_filter_card_eq
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {cover :
      WZ2PaperPartitioningCover
        fine prepared.callerStrict.coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := caller.1) fineShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover fineShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < caller.1}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover fineShading coarseCells availableFineCells
        balancing coarseData}
    {owner : WZ2PaperDirectOwnerPreparationData producer}
    {schedule :
      WZ2PaperCallerCoarsePrefixScheduleData prepared}
    (data :
      WZ2PaperOwnerParentNestedSelectionData owner schedule)
    (predicate :
      Fin prepared.callerStrict.coarse.card → Prop)
    [DecidablePred predicate] :
    ((Finset.univ : Finset (Fin data.selected.family.card)).filter
      fun parent => predicate (data.selected.embedding parent)).card =
      (data.pruning.selected.filter fun parent =>
        predicate (data.packed.embedding parent)).card := by
  let selectedIndices :
      Finset (Fin data.packed.family.card) :=
    data.pruning.selected
  let selectedPacked' :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      data.packed.family selectedIndices
  have hSelectedPacked :
      data.selectedPacked = selectedPacked' := rfl
  let enumeration :
      Fin selectedIndices.card ≃ selectedIndices :=
    (selectedIndices.orderIsoOfFin rfl).toEquiv
  apply Finset.card_bij
    (fun parent _ => data.selectedPacked.embedding parent)
  · intro parent hparent
    apply Finset.mem_filter.mpr
    refine
      ⟨Finset.orderEmbOfFin_mem
        data.pruning.selected rfl parent, ?_⟩
    exact (Finset.mem_filter.mp hparent).2
  · intro first _ second _ heq
    exact data.selectedPacked.embedding.injective heq
  · intro packedParent hpacked
    have hselected :
        packedParent ∈ selectedIndices :=
      (Finset.mem_filter.mp hpacked).1
    let subtypeParent : selectedIndices :=
      ⟨packedParent, hselected⟩
    let parent : Fin data.selected.family.card :=
      enumeration.symm subtypeParent
    refine ⟨parent, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hEmbedding :
          data.selectedPacked.embedding parent = packedParent :=
        congrArg Subtype.val
          (enumeration.apply_symm_apply subtypeParent)
      change predicate
        (data.packed.embedding
          (data.selectedPacked.embedding parent))
      rw [hEmbedding]
      exact (Finset.mem_filter.mp hpacked).2
    · exact congrArg Subtype.val
        (enumeration.apply_symm_apply subtypeParent)

end WZ2PaperOwnerParentNestedSelectionData

theorem wz2_paper_owner_parent_nested_selection
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {cover :
      WZ2PaperPartitioningCover
        fine prepared.callerStrict.coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := caller.1) fineShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover fineShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < caller.1}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover fineShading coarseCells availableFineCells
        balancing coarseData}
    (owner : WZ2PaperDirectOwnerPreparationData producer)
    (schedule :
      WZ2PaperCallerCoarsePrefixScheduleData prepared) :
    Nonempty
      (WZ2PaperOwnerParentNestedSelectionData
        owner schedule) := by
  let packed :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      prepared.callerStrict.coarse
      owner.exactified.retainedParents
  have hWeightFinite :
      (∑ _parent : Fin packed.family.card, (1 : ENNReal)) ≠ ⊤ := by
    simp
  rcases
      wz2_prop_sticky_nested_weighted_parent_regularization
        (Fin packed.family.card) (fun _ => (1 : ENNReal))
        hWeightFinite
        (wz2PaperCallerCoarsePrefixScaleCount prepared)
        (fun coordinate =>
          WZ2PaperCallerCoarsePrefixClass schedule coordinate)
        (fun coordinate parent =>
          schedule.classParent coordinate (packed.embedding parent))
        (by
          intro level hnext first second heq
          exact
            schedule.classParent_nested level hnext
              (packed.embedding first) (packed.embedding second) heq)
    with ⟨pruning⟩
  have hSelectedWeightPos :
      0 < ∑ _parent ∈ pruning.selected, (1 : ENNReal) := by
    have hAmbientPos :
        0 < ∑ _parent : Fin packed.family.card, (1 : ENNReal) := by
      have hCard : 0 < packed.family.card := by
        change 0 < owner.exactified.retainedParents.card
        exact owner.exactified.retainedParents_nonempty.card_pos
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      have hFinCard :
          0 < Fintype.card (Fin packed.family.card) := by
        simpa using hCard
      exact_mod_cast hFinCard
    by_contra hzero
    have hSelectedZero :
        (∑ _parent ∈ pruning.selected, (1 : ENNReal)) = 0 := by
      simpa using hzero
    have hAmbientZero :
        (∑ _parent : Fin packed.family.card, (1 : ENNReal)) ≤ 0 := by
      calc
        (∑ _parent : Fin packed.family.card, (1 : ENNReal)) ≤
            (2 : ENNReal) ^
                wz2PaperCallerCoarsePrefixScaleCount prepared *
              ∑ _parent ∈ pruning.selected, (1 : ENNReal) :=
          pruning.retained_weight
        _ = 0 := by rw [hSelectedZero, mul_zero]
    exact (not_le.mpr hAmbientPos) hAmbientZero
  have hSelectedNonempty : pruning.selected.Nonempty := by
    by_contra hempty
    have hEq : pruning.selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [hEq] at hSelectedWeightPos
    simp at hSelectedWeightPos
  have hCardinalityRetention :
      packed.family.enncard ≤
        (2 : ENNReal) ^
            wz2PaperCallerCoarsePrefixScaleCount prepared *
          (pruning.selected.card : ENNReal) := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard,
      Finset.sum_const, nsmul_eq_mul] using
      pruning.retained_weight
  exact
    ⟨{
      pruning := pruning
      selected_nonempty := hSelectedNonempty
      cardinality_retention := hCardinalityRetention
    }⟩

end Kakeya.Assouad

end
