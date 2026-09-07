import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AmbientMetricCoreBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryMetricFiber
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryMetricFiberCardinalityBin

/-!
# Proposition 6.2: canonical ancestry auxiliary core

Assemble the paper's one augmented-tree cleanup:

* the auxiliary label is `(s-mesh cell, complete old ancestry)`;
* the preliminary ambient leaf set already lies in the complete packet hull;
* the final ambient core is pulled back exactly to that hull;
* the genuine Section 6 metric cover is restricted only after this pullback.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62AncestryMetricPreliminaryOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow}
    {scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {coordinateCount : ℕ}
    {Color : Fin coordinateCount → Type*}
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    {color : ∀ coordinate, Fin fine.card → Color coordinate}
    {weight : Fin fine.card → ENNReal}
    {preliminary :
      PureWZ2Prop62AncestryPreliminarySelectionData
        schedule scheduled rho width packetCoordinate
        Color color weight}
    {M : ℝ}
    (output :
      PureWZ2Prop62AncestryMetricPreliminaryOutput
        schedule scheduled width packetCoordinate
        Color color weight preliminary M)

/-- The canonical complete-ancestry level inserted immediately above `s`. -/
noncomputable def ancestryAuxiliary :
    PureWZ2Prop62AuxiliaryLevel
      schedule
      (schedule.CompleteAncestryLabel packetCoordinate
        (schedule.packetLineCell packetCoordinate width)) :=
  let _ := output
  schedule.completeAncestryAuxiliaryLevel
    packetCoordinate
    (schedule.packetLineCell packetCoordinate width)
    (schedule.packetLineCell_parent_invariant packetCoordinate width)

@[simp] theorem ancestryAuxiliary_label
    (source : Fin fine.card) :
    output.ancestryAuxiliary.label source =
      schedule.completeAncestryLabel packetCoordinate
        (schedule.packetLineCell packetCoordinate width) source := by
  rfl

theorem binnedPreliminary_subset_packetHull :
    output.binnedAmbientPreliminary ⊆
      output.metric.mesh.complete.selectedFineIndices := by
  exact output.binnedAmbientPreliminary_subset_packetHull

/--
One final ambient core together with its exact packet-hull and Section 6
views.
-/
noncomputable def ancestryAuxiliaryCore :
    PureWZ2Prop62AmbientMetricCoreBridgeData
      output.metric schedule output.ancestryAuxiliary
      output.binnedAmbientPreliminary :=
  Classical.choice <|
    pureWZ2_prop62_ambient_metric_core_bridge
      output.metric schedule output.ancestryAuxiliary
      output.binnedAmbientPreliminary
      output.binnedAmbientPreliminary_nonempty
      output.binnedPreliminary_subset_packetHull

theorem ancestryAuxiliaryCore_ambientCore_eq :
    output.ancestryAuxiliaryCore.ambientCore =
      output.ancestryAuxiliary.coreIndices
        output.binnedAmbientPreliminary :=
  output.ancestryAuxiliaryCore.ambientCore_eq

theorem ancestryAuxiliaryCore_pullback_image_eq :
    Finset.image
        output.metric.mesh.complete.selectedFine.embedding
        output.ancestryAuxiliaryCore.pullback.pulledBack =
      output.ancestryAuxiliaryCore.ambientCore :=
  output.ancestryAuxiliaryCore.pullback.image_eq

/--
The final Section 6 fine family and the packet-core pure family enumerate the
same pulled-back core finset.
-/
noncomputable def finalToPacketCoreEquiv :
    Fin output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family.card ≃
      Fin output.ancestryAuxiliaryCore.pullback.packetCoreFine.family.card :=
  Equiv.ofBijective
    (fun source =>
      (output.ancestryAuxiliaryCore.pullback.pulledBack.orderIsoOfFin rfl).symm
        ⟨output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding source,
          by
            have sourceImage :
                output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding source ∈
                  Finset.image
                    output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
                    Finset.univ :=
              Finset.mem_image.mpr
                ⟨source, Finset.mem_univ source, rfl⟩
            simpa only [
              output.ancestryAuxiliaryCore.metricRestriction.fine_image_univ
            ] using sourceImage⟩)
    ⟨by
      intro first second indexEq
      apply output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding.injective
      have valueEq := congrArg Subtype.val <|
        congrArg
          (output.ancestryAuxiliaryCore.pullback.pulledBack.orderIsoOfFin rfl)
          indexEq
      simpa using valueEq,
     by
      intro packetSource
      have packetMem :
          output.ancestryAuxiliaryCore.pullback.packetCoreFine.embedding
              packetSource ∈
            output.ancestryAuxiliaryCore.pullback.pulledBack :=
        Finset.orderEmbOfFin_mem _ rfl packetSource
      have selectedImage :
          output.ancestryAuxiliaryCore.pullback.packetCoreFine.embedding
              packetSource ∈
            Finset.image
              output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
              Finset.univ := by
        rw [output.ancestryAuxiliaryCore.metricRestriction.fine_image_univ]
        exact packetMem
      rcases Finset.mem_image.mp selectedImage with
        ⟨source, _, sourceEq⟩
      refine ⟨source, ?_⟩
      apply
        ((output.ancestryAuxiliaryCore.pullback.pulledBack.orderIsoOfFin rfl)
          |>.symm_apply_eq).2
      apply Subtype.ext
      change
        output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
            source =
          output.ancestryAuxiliaryCore.pullback.pulledBack.orderEmbOfFin
            rfl packetSource at sourceEq
      exact sourceEq⟩

theorem finalToPacketCoreEquiv_embedding
    (source :
      Fin output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family.card) :
    output.ancestryAuxiliaryCore.pullback.packetCoreFine.embedding
        (output.finalToPacketCoreEquiv source) =
      output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
        source := by
  unfold finalToPacketCoreEquiv
  change
    output.ancestryAuxiliaryCore.pullback.pulledBack.orderEmbOfFin rfl
        ((output.ancestryAuxiliaryCore.pullback.pulledBack.orderIsoOfFin rfl).symm
          ⟨output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
              source, _⟩) =
      output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
        source
  exact congrArg Subtype.val <|
    (output.ancestryAuxiliaryCore.pullback.pulledBack.orderIsoOfFin rfl).apply_symm_apply _

/-- Final Section 6 fine indices reindexed directly to the ambient tree core. -/
noncomputable def finalToAmbientCoreEquiv :
    Fin output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family.card ≃
      Fin output.ancestryAuxiliaryCore.pullback.ambientCoreFine.family.card :=
  output.finalToPacketCoreEquiv.trans
    output.ancestryAuxiliaryCore.pullback.packetCoreEquiv

theorem finalToAmbientCoreEquiv_embedding
    (source :
      Fin output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family.card) :
    output.ancestryAuxiliaryCore.pullback.ambientCoreFine.embedding
        (output.finalToAmbientCoreEquiv source) =
      output.metric.mesh.complete.selectedFine.embedding
        (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
          source) := by
  rw [finalToAmbientCoreEquiv, Equiv.trans_apply,
    output.ancestryAuxiliaryCore.pullback.packetCoreEquiv_embedding]
  exact congrArg
    output.metric.mesh.complete.selectedFine.embedding
    (output.finalToPacketCoreEquiv_embedding source)

theorem finalToAmbientCoreEquiv_tube
    (source :
      Fin output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family.card) :
    output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family.tube
        source =
      output.ancestryAuxiliaryCore.pullback.ambientCoreFine.family.tube
        (output.finalToAmbientCoreEquiv source) := by
  rw [output.ancestryAuxiliaryCore.metricRestriction.fineSelected.tube_eq,
    output.metric.mesh.complete.selectedFine.tube_eq,
    output.ancestryAuxiliaryCore.pullback.ambientCoreFine.tube_eq,
    output.finalToAmbientCoreEquiv_embedding]

/--
The ambient-core finset and the auxiliary `coreFine` finset are propositionally
equal; this is their exact order-enumeration equivalence.
-/
noncomputable def ambientCoreToAuxiliaryCoreEquiv :
    Fin output.ancestryAuxiliaryCore.pullback.ambientCoreFine.family.card ≃
      Fin
        (output.ancestryAuxiliary.coreFine
          output.binnedAmbientPreliminary).family.card :=
  Equiv.ofBijective
    (fun source =>
      ((output.ancestryAuxiliary.coreIndices
          output.binnedAmbientPreliminary).orderIsoOfFin rfl).symm
        ⟨output.ancestryAuxiliaryCore.pullback.ambientCoreFine.embedding source,
          by
            have sourceMem :
                output.ancestryAuxiliaryCore.pullback.ambientCoreFine.embedding
                    source ∈
                  output.ancestryAuxiliaryCore.ambientCore :=
              Finset.orderEmbOfFin_mem _ rfl source
            exact
              (Finset.ext_iff.mp
                output.ancestryAuxiliaryCore.ambientCore_eq
                (output.ancestryAuxiliaryCore.pullback.ambientCoreFine.embedding
                  source)).mp sourceMem⟩)
    ⟨by
      intro first second indexEq
      apply
        output.ancestryAuxiliaryCore.pullback.ambientCoreFine.embedding.injective
      have valueEq := congrArg Subtype.val <|
        congrArg
          ((output.ancestryAuxiliary.coreIndices
            output.binnedAmbientPreliminary).orderIsoOfFin rfl)
          indexEq
      simpa using valueEq,
     by
      intro coreSource
      have coreMem :
          (output.ancestryAuxiliary.coreFine
            output.binnedAmbientPreliminary).embedding coreSource ∈
            output.ancestryAuxiliary.coreIndices
              output.binnedAmbientPreliminary :=
        Finset.orderEmbOfFin_mem _ rfl coreSource
      have ambientMem :
          (output.ancestryAuxiliary.coreFine
            output.binnedAmbientPreliminary).embedding coreSource ∈
            output.ancestryAuxiliaryCore.ambientCore := by
        exact
          (Finset.ext_iff.mp
            output.ancestryAuxiliaryCore.ambientCore_eq
            ((output.ancestryAuxiliary.coreFine
              output.binnedAmbientPreliminary).embedding coreSource)).mpr
            coreMem
      let source :
          Fin output.ancestryAuxiliaryCore.pullback.ambientCoreFine.family.card :=
        (output.ancestryAuxiliaryCore.ambientCore.orderIsoOfFin rfl).symm
          ⟨(output.ancestryAuxiliary.coreFine
              output.binnedAmbientPreliminary).embedding coreSource,
            ambientMem⟩
      refine ⟨source, ?_⟩
      apply
        (((output.ancestryAuxiliary.coreIndices
          output.binnedAmbientPreliminary).orderIsoOfFin rfl)
          |>.symm_apply_eq).2
      apply Subtype.ext
      change
        output.ancestryAuxiliaryCore.pullback.ambientCoreFine.embedding source =
          (output.ancestryAuxiliary.coreFine
            output.binnedAmbientPreliminary).embedding coreSource
      unfold source
      change
        output.ancestryAuxiliaryCore.ambientCore.orderEmbOfFin rfl
            ((output.ancestryAuxiliaryCore.ambientCore.orderIsoOfFin rfl).symm
              ⟨(output.ancestryAuxiliary.coreFine
                  output.binnedAmbientPreliminary).embedding coreSource,
                ambientMem⟩) =
          (output.ancestryAuxiliary.coreFine
            output.binnedAmbientPreliminary).embedding coreSource
      exact congrArg Subtype.val <|
        Equiv.apply_symm_apply
          (output.ancestryAuxiliaryCore.ambientCore.orderIsoOfFin rfl).toEquiv
          _⟩

theorem ambientCoreToAuxiliaryCoreEquiv_embedding
    (source :
      Fin output.ancestryAuxiliaryCore.pullback.ambientCoreFine.family.card) :
    (output.ancestryAuxiliary.coreFine
        output.binnedAmbientPreliminary).embedding
        (output.ambientCoreToAuxiliaryCoreEquiv source) =
      output.ancestryAuxiliaryCore.pullback.ambientCoreFine.embedding source := by
  unfold ambientCoreToAuxiliaryCoreEquiv
  change
    (output.ancestryAuxiliary.coreIndices
      output.binnedAmbientPreliminary).orderEmbOfFin rfl
        (((output.ancestryAuxiliary.coreIndices
          output.binnedAmbientPreliminary).orderIsoOfFin rfl).symm
          ⟨output.ancestryAuxiliaryCore.pullback.ambientCoreFine.embedding
              source, _⟩) =
      output.ancestryAuxiliaryCore.pullback.ambientCoreFine.embedding source
  exact congrArg Subtype.val <|
    ((output.ancestryAuxiliary.coreIndices
      output.binnedAmbientPreliminary).orderIsoOfFin rfl).apply_symm_apply _

/-- Final Section 6 indices reindexed to the actual auxiliary core family. -/
noncomputable def finalToAuxiliaryCoreEquiv :
    Fin output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family.card ≃
      Fin
        (output.ancestryAuxiliary.coreFine
          output.binnedAmbientPreliminary).family.card :=
  output.finalToAmbientCoreEquiv.trans
    output.ambientCoreToAuxiliaryCoreEquiv

theorem finalToAuxiliaryCoreEquiv_embedding
    (source :
      Fin output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family.card) :
    (output.ancestryAuxiliary.coreFine
        output.binnedAmbientPreliminary).embedding
        (output.finalToAuxiliaryCoreEquiv source) =
      output.metric.mesh.complete.selectedFine.embedding
        (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
          source) := by
  rw [finalToAuxiliaryCoreEquiv, Equiv.trans_apply,
    output.ambientCoreToAuxiliaryCoreEquiv_embedding,
    output.finalToAmbientCoreEquiv_embedding]

theorem finalToAuxiliaryCoreEquiv_tube
    (source :
      Fin output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family.card) :
    output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family.tube
        source =
      (output.ancestryAuxiliary.coreFine
        output.binnedAmbientPreliminary).family.tube
        (output.finalToAuxiliaryCoreEquiv source) := by
  rw [output.ancestryAuxiliaryCore.metricRestriction.fineSelected.tube_eq,
    output.metric.mesh.complete.selectedFine.tube_eq,
    (output.ancestryAuxiliary.coreFine
      output.binnedAmbientPreliminary).tube_eq,
    output.finalToAuxiliaryCoreEquiv_embedding]

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
