import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64TransportedCombinedSelection

/-!
# Literal covers from the Proposition 6.4 combined selection

This file performs no further selection.  It converts the one selected final
family into the occupied transported quotient parents at every coordinate,
uses monochromaticity to prove doubled-fibre disjointness, and exports the
joint target-owner/source-owner degree and local-fanout-one receipts.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

variable
    {sigma workLoss sourceDelta targetDelta₀ outputLoss : ℝ}
    {Grid : Type*} [PureWZ2Proposition64TargetGrid Grid]
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    (frostman : SelectedSourceFrostmanReceipt geometry)
    (floor : Grid)

private noncomputable abbrev schedule :=
  quantitativeVerticalRequestedScaleScheduleFor quantitativeOutput geometry floor

namespace QuantitativeVerticalTransportedSourceParentQuotientData

/-- Public output of the one combined selection.  The family is selected
once; all covers and source-owner pair data refer to that same family. -/
structure QuantitativeVerticalTransportedCombinedSelectionData
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw) where
  selected : WZ2PaperPureTubeSubfamily
    (quantitativeVerticalPaperED quantitativeOutput geometry frostman
      ).subfamily.family
  selected_nonempty : selected.family.Nonempty
  targetParents : ∀ coordinate, WZ2PaperPureTubeSubfamily
    (data.quotientParents quantitativeOutput geometry frostman floor coordinate)
  targetCover : ∀ coordinate, WZ2PaperPurePartitioningCover selected.family
    (targetParents coordinate).family
  targetParent_ambient_eq : ∀ coordinate source,
    (targetParents coordinate).embedding
        ((targetCover coordinate).parent source) =
      data.assignedParent quantitativeOutput geometry frostman floor coordinate
        (selected.embedding source)
  sourceOwner : ∀ coordinate, Fin selected.family.card →
    Fin (quantitativeVerticalMatchedSourceNearby
      quantitativeOutput geometry floor coordinate).scaleData.coarse.card
  sourceOwner_eq : ∀ coordinate source,
    sourceOwner coordinate source =
      data.sourceOwner quantitativeOutput geometry frostman floor coordinate
        (selected.embedding source)
  degreeConstant : ENNReal
  degreeConstant_eq : degreeConstant =
    quantitativeVerticalTransportedPairDegreeConstant
      quantitativeOutput geometry frostman floor
  fullFiberUniform : ∀ coordinate,
    WZ2PaperPureFullFibersAreCUniform selected.family
      (targetParents coordinate).family degreeConstant
  pair_degree_uniform : ∀ coordinate,
    ∀ first second : Fin (targetParents coordinate).family.card ×
      Fin (quantitativeVerticalMatchedSourceNearby
        quantitativeOutput geometry floor coordinate).scaleData.coarse.card,
      0 < pureWZ2Proposition64OwnerPairCount
          (targetCover coordinate) (sourceOwner coordinate) first →
      0 < pureWZ2Proposition64OwnerPairCount
          (targetCover coordinate) (sourceOwner coordinate) second →
      pureWZ2Proposition64OwnerPairCount
          (targetCover coordinate) (sourceOwner coordinate) first ≤
        degreeConstant * pureWZ2Proposition64OwnerPairCount
          (targetCover coordinate) (sourceOwner coordinate) second
  localFanout : ∀ coordinate sourceParent,
    (((Finset.univ : Finset (Fin (targetParents coordinate).family.card)).filter
      fun targetParent => 0 < pureWZ2Proposition64OwnerPairCount
        (targetCover coordinate) (sourceOwner coordinate)
        (targetParent, sourceParent)).card : ENNReal) ≤ 1
  retentionConstant : ENNReal
  retentionConstant_eq : retentionConstant =
    quantitativeVerticalTransportedSelectionRetention
      quantitativeOutput geometry frostman floor
  retentionConstant_ne_top : retentionConstant ≠ ⊤
  retained_mass :
    (quantitativeVerticalPaperED quantitativeOutput geometry frostman
      ).finalShading.mass ≤ retentionConstant *
      (restrictPaperShading selected.toTubeSubfamily
        (quantitativeVerticalPaperED quantitativeOutput geometry frostman
          ).finalShading).mass
  weightLevel : ENNReal
  weightLevel_pos : 0 < weightLevel
  weight_band : ∀ source,
    weightLevel ≤ volume
        ((quantitativeVerticalPaperED quantitativeOutput geometry frostman
          ).finalShading.carrier (selected.embedding source)) ∧
      volume ((quantitativeVerticalPaperED quantitativeOutput geometry frostman
        ).finalShading.carrier (selected.embedding source)) ≤ 2 * weightLevel

namespace QuantitativeVerticalTransportedCombinedSelectionData

/-- The joint ED weight band cancels before the combined-selection
retention loss is charged.  No global ED-loss or ambient cardinality enters
this same-shading comparison. -/
theorem initial_cardinality_le_selected
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data) :
    (quantitativeVerticalPaperED quantitativeOutput geometry frostman
      ).subfamily.family.enncard ≤
      2 * selected.retentionConstant * selected.selected.family.enncard := by
  let joint :=
    quantitativeVerticalJointPaperED quantitativeOutput geometry frostman
  let ed :=
    quantitativeVerticalPaperED quantitativeOutput geometry frostman
  have hselectedMassUpper :
      (restrictPaperShading selected.selected.toTubeSubfamily
          ed.finalShading).mass ≤
        (2 * joint.weightLevel) * selected.selected.family.enncard := by
    rw [restrictPaperShading_mass]
    calc
      (∑ index : Fin selected.selected.family.card,
          volume (ed.finalShading.carrier
            (selected.selected.embedding index))) ≤
          ∑ _index : Fin selected.selected.family.card,
            2 * joint.weightLevel := by
        apply Finset.sum_le_sum
        intro index _
        exact (joint.carrier_volume_band
          (selected.selected.embedding index)).2
      _ = (2 * joint.weightLevel) *
          selected.selected.family.enncard := by
        simp [Kakeya.Streamlined.TubeFamily.enncard, mul_comm]
  have hweighted :
      joint.weightLevel *
          (quantitativeVerticalPaperED quantitativeOutput geometry frostman
            ).subfamily.family.enncard ≤
        joint.weightLevel *
          (2 * selected.retentionConstant *
            selected.selected.family.enncard) := by
    calc
      joint.weightLevel *
          (quantitativeVerticalPaperED quantitativeOutput geometry frostman
            ).subfamily.family.enncard ≤
          (quantitativeVerticalPaperED quantitativeOutput geometry frostman
            ).finalShading.mass := by
        exact joint.shaded_mass_lower
      _ ≤ selected.retentionConstant *
          (restrictPaperShading selected.selected.toTubeSubfamily
            (quantitativeVerticalPaperED quantitativeOutput geometry frostman
              ).finalShading).mass :=
        selected.retained_mass
      _ ≤ selected.retentionConstant *
          ((2 * joint.weightLevel) *
            selected.selected.family.enncard) := by
        exact mul_le_mul_left' hselectedMassUpper _
      _ = joint.weightLevel *
          (2 * selected.retentionConstant *
            selected.selected.family.enncard) := by ring
  let source : Fin selected.selected.family.card :=
    ⟨0, selected.selected_nonempty⟩
  have hweightTop : joint.weightLevel ≠ ⊤ := by
    have hweightLe :=
      (joint.carrier_volume_band
        (selected.selected.embedding source)).1
    exact ne_top_of_le_ne_top
      (ed.finalShading.carrier_volume_ne_top
        (selected.selected.embedding source))
      hweightLe
  exact (ENNReal.mul_le_mul_iff_right
    joint.weightLevel_pos.ne' hweightTop).mp hweighted

/-- The joint selector's ambient-average carrier floor passes to every
combined-selected tube on the same shading. -/
theorem finalShading_dense_of_jointAverage
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data)
    {structuralLoss structuralDelta₀ : ℝ}
    (scalars : PureWZ2Proposition64JointDensityScalarReceipt
      sourceDelta
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
      quantitativeOutput.densityLoss
      quantitativeOutput.normalized.prepared.normalization
      quantitativeOutput.normalized.prepared.slab.halfHeight
      structuralLoss structuralDelta₀) :
    (restrictPaperShading selected.selected.toTubeSubfamily
      (quantitativeVerticalPaperED quantitativeOutput geometry frostman
        ).finalShading).IsLambdaDense
      (Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        structuralLoss) := by
  let joint :=
    quantitativeVerticalJointPaperED quantitativeOutput geometry frostman
  let targetDensity :=
    Kakeya.realRpowENN
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) structuralLoss
  let bodyConstant :=
    (55296 * Kakeya.deltaTubeVolume 1) *
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2
  have haverage : targetDensity * bodyConstant ≤
      geometry.cleanup.finalShading.mass /
        (2 * (paperPositiveMassSubfamily
          geometry.cleanup.finalShading).family.card : ENNReal) := by
    exact geometry.quantitativeVerticalJointPaperED_haverage
      quantitativeOutput scalars
  have hline : WZ1PaperIsLineClass selected.selected.family :=
    (geometry.paperED_lineClass
      (quantitativeVerticalPaperED quantitativeOutput geometry frostman)
      ).subfamily selected.selected.toTubeSubfamily
  let fullShading : WZ1PaperTubeShading selected.selected.family := {
    carrier := fun index =>
      wz1PaperTubeCarrier (selected.selected.family.tube index)
    measurable_carrier := fun index =>
      wz1PaperTubeCarrier_measurable (selected.selected.family.tube index)
    subset_body := fun _ => Set.Subset.rfl }
  have hbody :
      (wz1PaperBodyFamily selected.selected.family).mass ≤
        bodyConstant * selected.selected.family.enncard := by
    have h := wz2_paper_shading_mass_upper
      geometry.scales.finalDelta_pos
      (geometry.scales.finalDelta_le_one_ninety_six.trans (by norm_num))
      hline fullShading
    change fullShading.mass ≤ _
    simpa [bodyConstant, mul_assoc] using h
  have hcarrierSum :
      (geometry.cleanup.finalShading.mass /
          (2 * (paperPositiveMassSubfamily
            geometry.cleanup.finalShading).family.card : ENNReal)) *
          selected.selected.family.enncard ≤
        (restrictPaperShading selected.selected.toTubeSubfamily
          (quantitativeVerticalPaperED quantitativeOutput geometry frostman
            ).finalShading).mass := by
    rw [restrictPaperShading_mass]
    calc
      (geometry.cleanup.finalShading.mass /
          (2 * (paperPositiveMassSubfamily
            geometry.cleanup.finalShading).family.card : ENNReal)) *
          selected.selected.family.enncard =
        ∑ _index : Fin selected.selected.family.card,
          geometry.cleanup.finalShading.mass /
            (2 * (paperPositiveMassSubfamily
              geometry.cleanup.finalShading).family.card : ENNReal) := by
        simp [Kakeya.Streamlined.TubeFamily.enncard, mul_comm]
      _ ≤ ∑ index : Fin selected.selected.family.card,
          volume
            ((quantitativeVerticalPaperED quantitativeOutput geometry frostman
              ).finalShading.carrier
                (selected.selected.embedding index)) := by
        apply Finset.sum_le_sum
        intro index _
        exact joint.average_carrier_floor
          (selected.selected.embedding index)
  unfold Kakeya.Streamlined.Shading.IsLambdaDense
  calc
    targetDensity *
        (wz1PaperBodyFamily selected.selected.family).mass ≤
      targetDensity *
        (bodyConstant * selected.selected.family.enncard) := by
      exact mul_le_mul_left' hbody _
    _ = (targetDensity * bodyConstant) *
        selected.selected.family.enncard := by ring
    _ ≤ (geometry.cleanup.finalShading.mass /
          (2 * (paperPositiveMassSubfamily
            geometry.cleanup.finalShading).family.card : ENNReal)) *
        selected.selected.family.enncard := by
      exact mul_le_mul_right' haverage _
    _ ≤ (restrictPaperShading selected.selected.toTubeSubfamily
          (quantitativeVerticalPaperED quantitativeOutput geometry frostman
            ).finalShading).mass :=
      hcarrierSum

end QuantitativeVerticalTransportedCombinedSelectionData

namespace QuantitativeVerticalTransportedCombinedSelectionCoreData

noncomputable def targetParents
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    WZ2PaperPureTubeSubfamily
      (data.quotientParents quantitativeOutput geometry frostman floor
        coordinate) :=
  (data.toPreAssignedParentCover quantitativeOutput geometry frostman floor
    coordinate).hitParentSubfamily
      (core.selected quantitativeOutput geometry frostman floor)

theorem targetParents_separated
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (first second : Fin
      (core.targetParents quantitativeOutput geometry frostman floor coordinate
        ).family.card)
    (hne : first ≠ second) :
    2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
        quantitativeVerticalTransportedQuotientScale
          quantitativeOutput geometry floor coordinate <
      wz1PaperLineDistance
        ((core.targetParents quantitativeOutput geometry frostman floor
          coordinate).family.tube first)
        ((core.targetParents quantitativeOutput geometry frostman floor
          coordinate).family.tube second) := by
  let selected := core.selected quantitativeOutput geometry frostman floor
  let pre := data.toPreAssignedParentCover quantitativeOutput geometry frostman
    floor coordinate
  have hambientNe :
      (pre.hitParentSubfamily selected).embedding first ≠
        (pre.hitParentSubfamily selected).embedding second :=
    (pre.hitParentSubfamily selected).embedding.injective.ne hne
  rcases pre.hitParent_surjective selected first with ⟨firstSource, hfirst⟩
  rcases pre.hitParent_surjective selected second with ⟨secondSource, hsecond⟩
  have hfirstOwner :
      data.assignedParent quantitativeOutput geometry frostman floor coordinate
          (selected.embedding firstSource) =
        (pre.hitParentSubfamily selected).embedding first := by
    change pre.assignedParent (selected.embedding firstSource) = _
    rw [← pre.hitParent_ambient selected firstSource, hfirst]
  have hsecondOwner :
      data.assignedParent quantitativeOutput geometry frostman floor coordinate
          (selected.embedding secondSource) =
        (pre.hitParentSubfamily selected).embedding second := by
    change pre.assignedParent (selected.embedding secondSource) = _
    rw [← pre.hitParent_ambient selected secondSource, hsecond]
  have hcolors := core.monochromatic quantitativeOutput geometry frostman floor
    coordinate firstSource secondSource
  rw [hfirstOwner, hsecondOwner] at hcolors
  by_contra hnot
  have hconflict : data.conflict quantitativeOutput geometry frostman floor
      coordinate ((pre.hitParentSubfamily selected).embedding first)
      ((pre.hitParentSubfamily selected).embedding second) := by
    unfold QuantitativeVerticalTransportedSourceParentQuotientData.conflict
    rw [← (pre.hitParentSubfamily selected).tube_eq first,
      ← (pre.hitParentSubfamily selected).tube_eq second]
    exact not_lt.mp hnot
  exact (core.coloring.proper coordinate _ _ hambientNe hconflict) hcolors

noncomputable def selectedCoverData
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    PureWZ2LocalizedAssignedParentCoverData
      (core.selected quantitativeOutput geometry frostman floor).family
      (core.targetParents quantitativeOutput geometry frostman floor
        coordinate).family := by
  let selected := core.selected quantitativeOutput geometry frostman floor
  let pre := data.toPreAssignedParentCover quantitativeOutput geometry frostman
    floor coordinate
  exact pre.restrictToSeparatedHitParents selected
    (core.targetParents_separated quantitativeOutput geometry frostman floor
      coordinate)

noncomputable def targetCover
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    WZ2PaperPurePartitioningCover
      (core.selected quantitativeOutput geometry frostman floor).family
      (core.targetParents quantitativeOutput geometry frostman floor
        coordinate).family :=
  (core.selectedCoverData quantitativeOutput geometry frostman floor
    coordinate).toPartitioningCover

def selectedSourceOwner
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    Fin (core.selected quantitativeOutput geometry frostman floor).family.card →
      Fin (quantitativeVerticalMatchedSourceNearby quantitativeOutput geometry
        floor coordinate).scaleData.coarse.card :=
  fun source => data.sourceOwner quantitativeOutput geometry frostman floor
    coordinate
    ((core.selected quantitativeOutput geometry frostman floor).embedding source)

theorem targetParent_ambient_eq
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (source : Fin
      (core.selected quantitativeOutput geometry frostman floor).family.card) :
    (core.targetParents quantitativeOutput geometry frostman floor coordinate
      ).embedding
        ((core.targetCover quantitativeOutput geometry frostman floor coordinate
          ).parent source) =
      data.assignedParent quantitativeOutput geometry frostman floor coordinate
        ((core.selected quantitativeOutput geometry frostman floor).embedding
          source) := by
  rw [(core.selectedCoverData quantitativeOutput geometry frostman floor
    coordinate).parent_eq_assigned]
  exact (data.toPreAssignedParentCover quantitativeOutput geometry frostman
    floor coordinate).hitParent_ambient
      (core.selected quantitativeOutput geometry frostman floor) source

theorem ambient_owner_fiber_nonempty
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (parent : Fin (core.targetParents quantitativeOutput geometry frostman floor
      coordinate).family.card) :
    0 < ((Finset.univ : Finset (Fin
      (core.selected quantitativeOutput geometry frostman floor).family.card)
      ).filter fun source =>
        data.assignedParent quantitativeOutput geometry frostman floor coordinate
          ((core.selected quantitativeOutput geometry frostman floor).embedding
            source) =
          (core.targetParents quantitativeOutput geometry frostman floor
            coordinate).embedding parent).card := by
  let selected := core.selected quantitativeOutput geometry frostman floor
  let coverData := core.selectedCoverData quantitativeOutput geometry frostman
    floor coordinate
  let parents := core.targetParents quantitativeOutput geometry frostman floor
    coordinate
  let cover := core.targetCover quantitativeOutput geometry frostman floor
    coordinate
  rcases coverData.assignedParent_surjective parent with ⟨source, hsource⟩
  apply Finset.card_pos.mpr
  refine ⟨source, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  calc
    data.assignedParent quantitativeOutput geometry frostman floor coordinate
        (selected.embedding source) =
      parents.embedding (cover.parent source) :=
        (core.targetParent_ambient_eq quantitativeOutput geometry frostman floor
          coordinate source).symm
    _ = parents.embedding parent := by
      apply congrArg
      exact (coverData.parent_eq_assigned source).trans hsource

theorem assignedFiber_eq_ambient
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (parent : Fin (core.targetParents quantitativeOutput geometry frostman floor
      coordinate).family.card) :
    ((Finset.univ : Finset (Fin
      (core.selected quantitativeOutput geometry frostman floor).family.card)
      ).filter fun source =>
        (core.selectedCoverData quantitativeOutput geometry frostman floor
          coordinate).assignedParent source = parent) =
      (Finset.univ : Finset (Fin
        (core.selected quantitativeOutput geometry frostman floor).family.card)
        ).filter fun source =>
          data.assignedParent quantitativeOutput geometry frostman floor
            coordinate
            ((core.selected quantitativeOutput geometry frostman floor
              ).embedding source) =
          (core.targetParents quantitativeOutput geometry frostman floor
            coordinate).embedding parent := by
  let selected := core.selected quantitativeOutput geometry frostman floor
  let coverData := core.selectedCoverData quantitativeOutput geometry frostman
    floor coordinate
  let parents := core.targetParents quantitativeOutput geometry frostman floor
    coordinate
  let cover := core.targetCover quantitativeOutput geometry frostman floor
    coordinate
  ext source
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hparent : coverData.assignedParent source = cover.parent source :=
    (coverData.parent_eq_assigned source).symm
  rw [hparent]
  constructor
  · intro h
    rw [← core.targetParent_ambient_eq quantitativeOutput geometry frostman
      floor coordinate source, h]
  · intro h
    apply parents.embedding.injective
    rw [core.targetParent_ambient_eq quantitativeOutput geometry frostman
      floor coordinate source]
    exact h

theorem fullFiberUniform
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    WZ2PaperPureFullFibersAreCUniform
      (core.selected quantitativeOutput geometry frostman floor).family
      (core.targetParents quantitativeOutput geometry frostman floor coordinate
        ).family
      (quantitativeVerticalTransportedPairDegreeConstant
        quantitativeOutput geometry frostman floor) := by
  let selected := core.selected quantitativeOutput geometry frostman floor
  let coverData := core.selectedCoverData quantitativeOutput geometry frostman
    floor coordinate
  let parents := core.targetParents quantitativeOutput geometry frostman floor
    coordinate
  let cover := core.targetCover quantitativeOutput geometry frostman floor
    coordinate
  apply coverData.fullFibers_uniform
  intro first second
  rw [core.assignedFiber_eq_ambient quantitativeOutput geometry frostman floor
    coordinate first,
    core.assignedFiber_eq_ambient quantitativeOutput geometry frostman floor
      coordinate second]
  apply core.direct_degree_uniform quantitativeOutput geometry frostman floor
  · exact core.ambient_owner_fiber_nonempty quantitativeOutput geometry frostman
      floor coordinate first
  · exact core.ambient_owner_fiber_nonempty quantitativeOutput geometry frostman
      floor coordinate second

theorem ownerPairCount_eq_ambient
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (pair : Fin (core.targetParents quantitativeOutput geometry frostman floor
          coordinate).family.card ×
      Fin (quantitativeVerticalMatchedSourceNearby quantitativeOutput geometry
        floor coordinate).scaleData.coarse.card) :
    pureWZ2Proposition64OwnerPairCount
        (core.targetCover quantitativeOutput geometry frostman floor coordinate)
        (core.selectedSourceOwner quantitativeOutput geometry frostman floor
          coordinate) pair =
      (((Finset.univ : Finset (Fin
        (core.selected quantitativeOutput geometry frostman floor).family.card)
        ).filter fun source =>
          (data.assignedParent quantitativeOutput geometry frostman floor
              coordinate
              ((core.selected quantitativeOutput geometry frostman floor
                ).embedding source),
            data.sourceOwner quantitativeOutput geometry frostman floor
              coordinate
              ((core.selected quantitativeOutput geometry frostman floor
                ).embedding source)) =
            ((core.targetParents quantitativeOutput geometry frostman floor
              coordinate).embedding pair.1, pair.2)).card : ENNReal) := by
  let selected := core.selected quantitativeOutput geometry frostman floor
  let parents := core.targetParents quantitativeOutput geometry frostman floor
    coordinate
  let cover := core.targetCover quantitativeOutput geometry frostman floor
    coordinate
  have hsets :
      (Finset.univ : Finset (Fin selected.family.card)).filter
          (fun source =>
            (cover.parent source,
              core.selectedSourceOwner quantitativeOutput geometry frostman
                floor coordinate source) = pair) =
        (Finset.univ : Finset (Fin selected.family.card)).filter
          (fun source =>
            (data.assignedParent quantitativeOutput geometry frostman floor
                coordinate (selected.embedding source),
              data.sourceOwner quantitativeOutput geometry frostman floor
                coordinate (selected.embedding source)) =
              (parents.embedding pair.1, pair.2)) := by
    ext source
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hpair
      apply Prod.ext
      · exact (core.targetParent_ambient_eq quantitativeOutput geometry frostman
          floor coordinate source).symm.trans
          (congrArg parents.embedding (congrArg Prod.fst hpair))
      · simpa only [selectedSourceOwner] using congrArg Prod.snd hpair
    · intro hpair
      apply Prod.ext
      · apply parents.embedding.injective
        exact (core.targetParent_ambient_eq quantitativeOutput geometry frostman
          floor coordinate source).trans (congrArg Prod.fst hpair)
      · simpa only [selectedSourceOwner] using congrArg Prod.snd hpair
  unfold pureWZ2Proposition64OwnerPairCount
  exact congrArg (fun indices : Finset (Fin selected.family.card) =>
    (indices.card : ENNReal)) hsets

theorem pair_degree_uniform_public
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (first second : Fin (core.targetParents quantitativeOutput geometry frostman
          floor coordinate).family.card ×
      Fin (quantitativeVerticalMatchedSourceNearby quantitativeOutput geometry
        floor coordinate).scaleData.coarse.card)
    (hfirst : 0 < pureWZ2Proposition64OwnerPairCount
      (core.targetCover quantitativeOutput geometry frostman floor coordinate)
      (core.selectedSourceOwner quantitativeOutput geometry frostman floor
        coordinate) first)
    (hsecond : 0 < pureWZ2Proposition64OwnerPairCount
      (core.targetCover quantitativeOutput geometry frostman floor coordinate)
      (core.selectedSourceOwner quantitativeOutput geometry frostman floor
        coordinate) second) :
    pureWZ2Proposition64OwnerPairCount
        (core.targetCover quantitativeOutput geometry frostman floor coordinate)
        (core.selectedSourceOwner quantitativeOutput geometry frostman floor
          coordinate) first ≤
      quantitativeVerticalTransportedPairDegreeConstant
          quantitativeOutput geometry frostman floor *
        pureWZ2Proposition64OwnerPairCount
          (core.targetCover quantitativeOutput geometry frostman floor coordinate)
          (core.selectedSourceOwner quantitativeOutput geometry frostman floor
            coordinate) second := by
  rw [core.ownerPairCount_eq_ambient quantitativeOutput geometry frostman floor,
    core.ownerPairCount_eq_ambient quantitativeOutput geometry frostman floor]
  apply core.pair_degree_uniform quantitativeOutput geometry frostman floor
  · have h : (0 : ENNReal) < (((Finset.univ : Finset (Fin
        (core.selected quantitativeOutput geometry frostman floor).family.card)
        ).filter fun source =>
          (data.assignedParent quantitativeOutput geometry frostman floor
              coordinate
              ((core.selected quantitativeOutput geometry frostman floor
                ).embedding source),
            data.sourceOwner quantitativeOutput geometry frostman floor
              coordinate
              ((core.selected quantitativeOutput geometry frostman floor
                ).embedding source)) =
            ((core.targetParents quantitativeOutput geometry frostman floor
              coordinate).embedding first.1, first.2)).card : ENNReal) := by
      rw [← core.ownerPairCount_eq_ambient quantitativeOutput geometry frostman
        floor]
      exact hfirst
    exact_mod_cast h
  · have h : (0 : ENNReal) < (((Finset.univ : Finset (Fin
        (core.selected quantitativeOutput geometry frostman floor).family.card)
        ).filter fun source =>
          (data.assignedParent quantitativeOutput geometry frostman floor
              coordinate
              ((core.selected quantitativeOutput geometry frostman floor
                ).embedding source),
            data.sourceOwner quantitativeOutput geometry frostman floor
              coordinate
              ((core.selected quantitativeOutput geometry frostman floor
                ).embedding source)) =
            ((core.targetParents quantitativeOutput geometry frostman floor
              coordinate).embedding second.1, second.2)).card : ENNReal) := by
      rw [← core.ownerPairCount_eq_ambient quantitativeOutput geometry frostman
        floor]
      exact hsecond
    exact_mod_cast h

theorem localFanout_one
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (sourceParent : Fin (quantitativeVerticalMatchedSourceNearby
      quantitativeOutput geometry floor coordinate).scaleData.coarse.card) :
    (((Finset.univ : Finset (Fin
      (core.targetParents quantitativeOutput geometry frostman floor coordinate
        ).family.card)).filter fun targetParent =>
        0 < pureWZ2Proposition64OwnerPairCount
          (core.targetCover quantitativeOutput geometry frostman floor coordinate)
          (core.selectedSourceOwner quantitativeOutput geometry frostman floor
            coordinate) (targetParent, sourceParent)).card : ENNReal) ≤ 1 := by
  exact_mod_cast (by
    rw [Finset.card_le_one]
    intro first hfirst second hsecond
    have hfirstPos := (Finset.mem_filter.mp hfirst).2
    have hsecondPos := (Finset.mem_filter.mp hsecond).2
    unfold pureWZ2Proposition64OwnerPairCount at hfirstPos hsecondPos
    have hfirstNat : 0 < ((Finset.univ : Finset (Fin
        (core.selected quantitativeOutput geometry frostman floor).family.card)
        ).filter fun source =>
          ((core.targetCover quantitativeOutput geometry frostman floor
              coordinate).parent source,
            core.selectedSourceOwner quantitativeOutput geometry frostman floor
              coordinate source) = (first, sourceParent)).card := by
      exact_mod_cast hfirstPos
    have hsecondNat : 0 < ((Finset.univ : Finset (Fin
        (core.selected quantitativeOutput geometry frostman floor).family.card)
        ).filter fun source =>
          ((core.targetCover quantitativeOutput geometry frostman floor
              coordinate).parent source,
            core.selectedSourceOwner quantitativeOutput geometry frostman floor
              coordinate source) = (second, sourceParent)).card := by
      exact_mod_cast hsecondPos
    rcases Finset.card_pos.mp hfirstNat with ⟨firstSource, hfirstSource⟩
    rcases Finset.card_pos.mp hsecondNat with ⟨secondSource, hsecondSource⟩
    have hfirstPair := (Finset.mem_filter.mp hfirstSource).2
    have hsecondPair := (Finset.mem_filter.mp hsecondSource).2
    have hsourceOwner :
        data.sourceOwner quantitativeOutput geometry frostman floor coordinate
            ((core.selected quantitativeOutput geometry frostman floor
              ).embedding firstSource) =
          data.sourceOwner quantitativeOutput geometry frostman floor coordinate
            ((core.selected quantitativeOutput geometry frostman floor
              ).embedding secondSource) := by
      simpa only [selectedSourceOwner] using
        (congrArg Prod.snd hfirstPair).trans
          (congrArg Prod.snd hsecondPair).symm
    have htargetOwner := data.assignedParent_eq_of_sourceOwner_eq
      quantitativeOutput geometry frostman floor coordinate
      ((core.selected quantitativeOutput geometry frostman floor
        ).embedding firstSource)
      ((core.selected quantitativeOutput geometry frostman floor
        ).embedding secondSource) hsourceOwner
    let parents := core.targetParents quantitativeOutput geometry frostman floor
      coordinate
    apply parents.embedding.injective
    calc
      parents.embedding first =
          data.assignedParent quantitativeOutput geometry frostman floor
            coordinate ((core.selected quantitativeOutput geometry frostman
              floor).embedding firstSource) :=
        (congrArg parents.embedding (congrArg Prod.fst hfirstPair)).symm.trans
          (core.targetParent_ambient_eq quantitativeOutput geometry frostman
            floor coordinate firstSource)
      _ = data.assignedParent quantitativeOutput geometry frostman floor
            coordinate ((core.selected quantitativeOutput geometry frostman
              floor).embedding secondSource) := htargetOwner
      _ = parents.embedding second :=
        (core.targetParent_ambient_eq quantitativeOutput geometry frostman floor
          coordinate secondSource).symm.trans
          (congrArg parents.embedding (congrArg Prod.fst hsecondPair)))

theorem weight_band
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (source : Fin
      (core.selected quantitativeOutput geometry frostman floor).family.card) :
    core.selection.regularized.weightLevel ≤ volume
        ((quantitativeVerticalPaperED quantitativeOutput geometry frostman
          ).finalShading.carrier
          ((core.selected quantitativeOutput geometry frostman floor
            ).embedding source)) ∧
      volume ((quantitativeVerticalPaperED quantitativeOutput geometry frostman
        ).finalShading.carrier
          ((core.selected quantitativeOutput geometry frostman floor
            ).embedding source)) ≤
        2 * core.selection.regularized.weightLevel := by
  have hselected := core.selected_mem quantitativeOutput geometry frostman floor
    source
  have hclass := core.selection.selected_subset_colorClass hselected
  have hband := core.selection.regularized.weight_band
    ((core.selected quantitativeOutput geometry frostman floor).embedding source)
    hselected
  rw [if_pos hclass] at hband
  exact hband

/-- The single selected family with all literal public-cover and owner-pair
certificates exposed for downstream actual-John transport. -/
noncomputable def toCombinedSelection
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data) :
    QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data where
  selected := core.selected quantitativeOutput geometry frostman floor
  selected_nonempty := core.selected_nonempty quantitativeOutput geometry
    frostman floor
  targetParents := core.targetParents quantitativeOutput geometry frostman floor
  targetCover := core.targetCover quantitativeOutput geometry frostman floor
  targetParent_ambient_eq := core.targetParent_ambient_eq quantitativeOutput
    geometry frostman floor
  sourceOwner := core.selectedSourceOwner quantitativeOutput geometry frostman
    floor
  sourceOwner_eq := fun _ _ => rfl
  degreeConstant := quantitativeVerticalTransportedPairDegreeConstant
    quantitativeOutput geometry frostman floor
  degreeConstant_eq := rfl
  fullFiberUniform := core.fullFiberUniform quantitativeOutput geometry frostman
    floor
  pair_degree_uniform := core.pair_degree_uniform_public quantitativeOutput
    geometry frostman floor
  localFanout := core.localFanout_one quantitativeOutput geometry frostman floor
  retentionConstant := core.retentionConstant quantitativeOutput geometry
    frostman floor
  retentionConstant_eq := rfl
  retentionConstant_ne_top := core.retentionConstant_ne_top quantitativeOutput
    geometry frostman floor
  retained_mass := core.retained_mass quantitativeOutput geometry frostman floor
  weightLevel := core.selection.regularized.weightLevel
  weightLevel_pos := core.selection.regularized.weightLevel_pos
  weight_band := core.weight_band quantitativeOutput geometry frostman floor

theorem exists_quantitativeVerticalTransportedCombinedSelection
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw) :
    Nonempty (QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data) := by
  rcases exists_quantitativeVerticalTransportedCombinedSelectionCore
    quantitativeOutput geometry frostman floor data with ⟨core⟩
  exact ⟨core.toCombinedSelection quantitativeOutput geometry frostman floor⟩

end QuantitativeVerticalTransportedCombinedSelectionCoreData

end QuantitativeVerticalTransportedSourceParentQuotientData

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end
