import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ExtremalVolumeUpper

/-!
# Proposition 6.2: fine-only critical quantitative tail

This is the Node 6 quantitative tail after the critical input has been
localized to the fine rescaled fibers.  In particular, no coarse critical
volume floor or coarse critical constant absorption is assumed here.

The coarse lower bound uses the product estimate against the fine critical
cap.  The coarse volume estimate then uses that lower bound directly.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62PacketCellInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover sourceShading)
    (multiplicity : input.FineMultiplicityClassData)
    (parentClass : input.ParentClassData multiplicity)
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        coarse ambientConstant scaleWindow}
    (treeCleanup :
      input.ParentTreeCleanupData
        multiplicity parentClass schedule)
    (exactification :
      input.PacketCellExactificationData
        multiplicity parentClass treeCleanup)
    (parentDegree :
      input.ReferenceParentDegreeData
        multiplicity parentClass treeCleanup exactification)
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    {A0 : ℕ}
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
        exactification parentDegree bins A0)
    {degreeLoss : ℕ}
    (good : core.ranges.GoodBalancingSampleData degreeLoss)
    (families :
      input.TerminalCompleteFamiliesData
        multiplicity parentClass treeCleanup exactification
          core.ranges)
    {fiberConstant densityConstant : ENNReal}
    {logExponent : ℕ}
    (output :
      input.FourDegreeLemmaOutputData
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          fiberConstant densityConstant logExponent)

namespace FourDegreeLemmaOutputData

/-- The critical data used by this tail are only the fine rescaled data. -/
structure FineCriticalMultiplicityInputsData
    {sigma floorLoss capLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss) : Prop where
  ratio_small : delta / rho ≤ 1 / 24
  ratio_critical : delta / rho ≤ critical.delta₀
  fiber_witness :
    ∀ parent :
        Fin families.restriction.coarseSelected.family.card,
      Nonempty
        (PureWZ2Prop62CriticalRescaledFiberFloorWitness
          (loss := critical.structuralLoss)
          (output.terminalFiberShading
            input multiplicity parentClass treeCleanup exactification
              parentDegree core good families parent)
          (families.restriction.coarseSelected.family.tube parent)
          input.rho_pos)
  fine_constant_absorption :
    55296 * Kakeya.deltaTubeVolume 1 ≤
      Kakeya.realRpowENN (delta / rho)
        (-(capLoss - floorLoss))

/-- The critical cap for `muFine` needs only the rescaled fine-fiber data. -/
theorem fine_multiplicity_upper_of_fine_critical_inputs
    {sigma floorLoss capLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (fineInputs :
      output.FineCriticalMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families critical) :
    ∀ parent :
        Fin families.restriction.coarseSelected.family.card,
      (output.muFine : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - capLoss) *
          (families.terminalFiber
            input multiplicity parentClass treeCleanup exactification
              parentDegree core parent).family.enncard := by
  intro parent
  let sourceFamily :=
    (families.terminalFiber
      input multiplicity parentClass treeCleanup exactification
        parentDegree core parent).family
  let sourceFiberShading :=
    output.terminalFiberShading
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent
  let witness := Classical.choice (fineInputs.fiber_witness parent)
  let targetShading := witness.literalShading.targetShading
  have ratioPos : 0 < delta / rho :=
    div_pos input.delta_pos input.rho_pos
  have sourceFloor :
      ∀ point ∈ sourceFiberShading.union,
        (output.muFine : ENNReal) ≤
          (sourceFiberShading.pointMultiplicity point : ENNReal) := by
    intro point pointMem
    exact
      output.terminalFiberShading_multiplicity_lower
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent pointMem
  have targetFloor :
      ∀ point ∈ targetShading.union,
        (output.muFine : ENNReal) ≤
          (targetShading.pointMultiplicity point : ENNReal) :=
    wz2_paper_literal_image_multiplicity_floor
      wz2_paper_literal_image_multiplicity
      witness.familyData sourceFiberShading
      witness.literalShading output.muFine sourceFloor
  have ordinaryVolumeFloor :
      Kakeya.realRpowENN (delta / rho)
          (sigma + floorLoss) ≤
        volume witness.ordinaryShading.union :=
    critical.volume_floor
      (delta / rho) ratioPos fineInputs.ratio_critical
      witness.ordinaryFamily witness.ordinary_nonempty
      witness.ordinaryShading witness.ordinary_cwa
      witness.ordinary_dense
  have targetVolumeFloor :
      Kakeya.realRpowENN (delta / rho)
          (sigma + floorLoss) ≤
        volume targetShading.union :=
    ordinaryVolumeFloor.trans <|
      measure_mono witness.ordinary_union_subset_target
  have targetMassUpper :
      targetShading.mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN (delta / rho) 2 *
          sourceFamily.enncard := by
    have targetCardinality :=
      (wz2_paper_literal_image_multiplicity
        (familyData := witness.familyData)
        (sourceShading := sourceFiberShading)
        (shadingData := witness.literalShading)).1
    have raw :=
      wz2_paper_shading_mass_upper
        ratioPos fineInputs.ratio_small
        witness.familyData.target_line_class targetShading
    calc
      targetShading.mass ≤
          (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN (delta / rho) 2 *
            witness.familyData.targetFamily.enncard :=
        raw
      _ =
          (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN (delta / rho) 2 *
            sourceFamily.enncard := by
        rw [targetCardinality]
  exact
    pureWZ2_multiplicity_cap_from_volume_floor_and_mass_upper
      ratioPos targetShading output.muFine sourceFamily.enncard
      (55296 * Kakeya.deltaTubeVolume 1)
      targetVolumeFloor targetFloor targetMassUpper
      fineInputs.fine_constant_absorption

/--
The coarse component floor uses the product lower bound and the fine critical
cap, without a coarse critical-volume premise.
-/
theorem coarse_multiplicity_lower_of_fine_critical_inputs
    {sigma floorLoss capLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (fineInputs :
      output.FineCriticalMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families critical)
    {desiredProduct massLower volumeUpper : ENNReal}
    (productInputs :
      ProductMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families
          (logExponent := logExponent)
          desiredProduct massLower volumeUpper)
    {desiredFine desiredCoarse : ENNReal}
    (componentInputs :
      output.ComponentMultiplicityFloorInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          critical desiredProduct desiredFine desiredCoarse) :
    desiredCoarse *
        families.restriction.coarseSelected.family.enncard ≤
      (output.muCoarse : ENNReal) := by
  let coarseCard :=
    families.restriction.coarseSelected.family.enncard
  let fiberFloor : ENNReal := output.fiberFloor
  let fineCoefficient :=
    Kakeya.realRpowENN (delta / rho) (2 - sigma - capLoss)
  let coarseLoss : ENNReal := output.coarseLoss
  let coarseFactor := (coarseLoss * fineCoefficient) * 2
  let parent :
      Fin families.restriction.coarseSelected.family.card :=
    ⟨0,
      finalCoarse_card_pos
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families⟩
  have productLower :=
    output.product_multiplicity_lower
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families productInputs
  have fineCap :=
    output.fine_multiplicity_upper_of_fine_critical_inputs
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families
        critical fineInputs parent
  have fiberFloorZero : fiberFloor ≠ 0 := by
    change (output.fiberFloor : ENNReal) ≠ 0
    exact_mod_cast output.fiberFloor_pos.ne'
  have fiberFloorTop : fiberFloor ≠ ⊤ := by
    exact ENNReal.natCast_ne_top _
  have withFiberFloor :
      desiredProduct * coarseCard ≤
        coarseFactor * (output.muCoarse : ENNReal) := by
    apply
      (ENNReal.mul_le_mul_iff_right
        fiberFloorZero fiberFloorTop).mp
    calc
      fiberFloor * (desiredProduct * coarseCard) =
          desiredProduct * (fiberFloor * coarseCard) := by
        ring
      _ ≤
          desiredProduct *
            families.restriction.fineSelected.family.enncard := by
        gcongr
        exact
          output.fiberFloor_mul_coarse_enncard_le_fine_enncard
            input multiplicity parentClass treeCleanup exactification
              parentDegree core good families
      _ ≤
          ((output.coarseLoss * output.muCoarse : ENNReal) *
            output.muFine) :=
        productLower
      _ ≤
          ((output.coarseLoss : ENNReal) *
            output.muCoarse) *
            (fineCoefficient *
              (families.terminalFiber
                input multiplicity parentClass treeCleanup exactification
                  parentDegree core parent).family.enncard) := by
        gcongr
      _ ≤
          ((output.coarseLoss : ENNReal) *
            output.muCoarse) *
            (fineCoefficient * (2 * fiberFloor)) := by
        gcongr
        exact
          output.terminalFiber_enncard_le_two_mul_fiberFloor
            input multiplicity parentClass treeCleanup exactification
              parentDegree core good families parent
      _ =
          fiberFloor *
            (coarseFactor * (output.muCoarse : ENNReal)) := by
        ring
  have coarseFactorZero : coarseFactor ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · change (output.coarseLoss : ENNReal) ≠ 0
        exact_mod_cast
          (output.coarseLoss_pos
            input multiplicity parentClass treeCleanup exactification
              parentDegree core good families).ne'
      · simp [
          fineCoefficient,
          Kakeya.realRpowENN,
          Real.rpow_pos_of_pos
            (div_pos input.delta_pos input.rho_pos)
        ]
    · norm_num
  have coarseFactorTop : coarseFactor ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.natCast_ne_top _)
        (by simp [fineCoefficient, Kakeya.realRpowENN]))
      (by norm_num)
  apply
    (ENNReal.mul_le_mul_iff_left
      coarseFactorZero coarseFactorTop).mp
  calc
    (desiredCoarse * coarseCard) * coarseFactor =
        (desiredCoarse * coarseFactor) * coarseCard := by
      ring
    _ ≤ desiredProduct * coarseCard := by
      gcongr
      exact componentInputs.coarse_scalar
    _ ≤ (output.muCoarse : ENNReal) * coarseFactor := by
      simpa [mul_comm] using withFiberFloor

theorem coarse_volume_upper_of_fine_critical_inputs
    (rho_small : rho ≤ 1 / 24)
    {sigma floorLoss capLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (fineInputs :
      output.FineCriticalMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families critical)
    {desiredProduct massLower sourceVolumeUpper : ENNReal}
    (productInputs :
      ProductMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families
          (logExponent := logExponent)
          desiredProduct massLower sourceVolumeUpper)
    {desiredFine desiredCoarse : ENNReal}
    (componentInputs :
      output.ComponentMultiplicityFloorInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          critical desiredProduct desiredFine desiredCoarse)
    {fineVolumeUpper coarseVolumeUpper : ENNReal}
    (volumeAbsorption :
      ExtremalVolumeAbsorptionData
        (delta := delta) (rho := rho)
        desiredFine desiredCoarse fineVolumeUpper coarseVolumeUpper) :
    volume output.coarseShading.union ≤ coarseVolumeUpper := by
  have multiplicityFloor :
      (output.muCoarse : ENNReal) *
          volume output.coarseShading.union ≤
        output.coarseShading.mass :=
    multiplicity_floor_le_mass <| by
      intro point pointMem
      exact
        output.coarse_pointMultiplicity_lower
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families pointMem
  have massUpper :
      output.coarseShading.mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN rho 2 *
          families.restriction.coarseSelected.family.enncard :=
    wz2_paper_shading_mass_upper
      input.rho_pos rho_small
      families.restriction.section6Cover.coarse_line_class
      output.coarseShading
  have componentFloor :=
    output.coarse_multiplicity_lower_of_fine_critical_inputs
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families
        critical fineInputs productInputs componentInputs
  have muCoarseZero : (output.muCoarse : ENNReal) ≠ 0 := by
    exact_mod_cast output.muCoarse_pos.ne'
  have muCoarseTop : (output.muCoarse : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply
    (ENNReal.mul_le_mul_iff_left
      muCoarseZero muCoarseTop).mp
  calc
    volume output.coarseShading.union *
          (output.muCoarse : ENNReal) =
        (output.muCoarse : ENNReal) *
          volume output.coarseShading.union := by
      ring
    _ ≤ output.coarseShading.mass :=
      multiplicityFloor
    _ ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN rho 2 *
          families.restriction.coarseSelected.family.enncard :=
      massUpper
    _ ≤
        (desiredCoarse * coarseVolumeUpper) *
          families.restriction.coarseSelected.family.enncard := by
      exact
        mul_le_mul_right'
          volumeAbsorption.coarse_scalar
          families.restriction.coarseSelected.family.enncard
    _ =
        (desiredCoarse *
          families.restriction.coarseSelected.family.enncard) *
          coarseVolumeUpper := by
      ring
    _ ≤
        (output.muCoarse : ENNReal) * coarseVolumeUpper := by
      gcongr
    _ =
        coarseVolumeUpper * (output.muCoarse : ENNReal) := by
      ring

/--
Summing the fine cap on each genuine terminal parent fiber gives the global
fine point-multiplicity cap, with no coarse critical input.
-/
theorem fine_pointMultiplicity_upper_by_fine_critical_fiber_sum
    {sigma floorLoss capLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (fineInputs :
      output.FineCriticalMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families critical) :
    ∀ point,
      (output.fineShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - capLoss) *
          families.restriction.fineSelected.family.enncard := by
  intro point
  let lineCover := families.restriction.lineCover
  let fineAtPoint :
      Finset (Fin families.restriction.fineSelected.family.card) :=
    Finset.univ.filter fun source =>
      point ∈ output.fineShading.carrier source
  have hmaps :
      Set.MapsTo lineCover.parent
        (fineAtPoint : Set
          (Fin families.restriction.fineSelected.family.card))
        ((Finset.univ :
          Finset (Fin families.restriction.coarseSelected.family.card)) :
          Set (Fin families.restriction.coarseSelected.family.card)) := by
    intro source _
    exact Finset.mem_univ (lineCover.parent source)
  have hdecompositionNat :
      fineAtPoint.card =
        ∑ parent :
            Fin families.restriction.coarseSelected.family.card,
          (fineAtPoint.filter fun source =>
            lineCover.parent source = parent).card := by
    simpa using Finset.card_eq_sum_card_fiberwise (H := hmaps)
  have hfiberEq :
      ∀ parent :
          Fin families.restriction.coarseSelected.family.card,
        (fineAtPoint.filter fun source =>
          lineCover.parent source = parent).card =
          (lineCover.fiberIndices parent |>.filter fun source =>
            point ∈ output.fineShading.carrier source).card := by
    intro parent
    congr 1
    ext source
    constructor
    · intro sourceMem
      have outer := Finset.mem_filter.mp sourceMem
      have pointMem := (Finset.mem_filter.mp outer.1).2
      have parentMem := outer.2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, parentMem⟩, pointMem⟩
    · intro sourceMem
      have outer := Finset.mem_filter.mp sourceMem
      have parentMem := (Finset.mem_filter.mp outer.1).2
      have pointMem := outer.2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, pointMem⟩, parentMem⟩
  have hdecomposition :
      (output.fineShading.pointMultiplicity point : ENNReal) =
        ∑ parent :
            Fin families.restriction.coarseSelected.family.card,
          (((lineCover.fiberIndices parent).filter fun source =>
            point ∈ output.fineShading.carrier source).card : ENNReal) := by
    change (fineAtPoint.card : ENNReal) = _
    exact_mod_cast (by simpa [hfiberEq] using hdecompositionNat)
  have hfiber :
      ∀ parent :
          Fin families.restriction.coarseSelected.family.card,
        (((lineCover.fiberIndices parent).filter fun source =>
          point ∈ output.fineShading.carrier source).card : ENNReal) ≤
          Kakeya.realRpowENN (delta / rho)
              (2 - sigma - capLoss) *
            ((lineCover.fiberIndices parent).card : ENNReal) := by
    intro parent
    have hraw :=
      output.fine_multiplicity_upper_of_fine_critical_inputs
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families critical fineInputs parent
    have lineFiberEq :
        lineCover.fiberIndices parent =
          wz2PaperFullFiberIndices
            families.restriction.fineSelected.family
            families.restriction.coarseSelected.family parent := by
      ext source
      exact
        mem_lineCover_fiberIndices_iff_fullFiber
          input multiplicity parentClass treeCleanup exactification
            parentDegree core families parent source
    change
      (output.muFine : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - capLoss) *
          ((wz2PaperFullFiberIndices
            families.restriction.fineSelected.family
            families.restriction.coarseSelected.family parent).card :
              ENNReal) at hraw
    rw [← lineFiberEq] at hraw
    change
      (lineCover.fiberPointMultiplicity
        output.fineShading parent point : ENNReal) ≤ _
    exact
      (output.fiber_pointMultiplicity_le
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent point).trans hraw
  have hsumCard :
      (∑ parent :
          Fin families.restriction.coarseSelected.family.card,
        ((lineCover.fiberIndices parent).card : ENNReal)) =
        families.restriction.fineSelected.family.enncard := by
    have hmapsAll :
        Set.MapsTo lineCover.parent
          (Finset.univ :
            Finset (Fin families.restriction.fineSelected.family.card))
          (Finset.univ :
            Finset (Fin families.restriction.coarseSelected.family.card)) :=
      fun _ _ => Finset.mem_univ _
    have hraw := Finset.card_eq_sum_card_fiberwise (H := hmapsAll)
    have hrawNat :
        ∑ parent :
            Fin families.restriction.coarseSelected.family.card,
          (lineCover.fiberIndices parent).card =
          families.restriction.fineSelected.family.card := by
      simpa [WZ1PaperTubeCover.fiberIndices] using hraw.symm
    have hcast :=
      congrArg (fun cardinality : ℕ => (cardinality : ENNReal)) hrawNat
    simpa [Nat.cast_sum, Kakeya.Streamlined.TubeFamily.enncard] using hcast
  rw [hdecomposition]
  calc
    (∑ parent :
        Fin families.restriction.coarseSelected.family.card,
      (((lineCover.fiberIndices parent).filter fun source =>
        point ∈ output.fineShading.carrier source).card : ENNReal)) ≤
      ∑ parent :
          Fin families.restriction.coarseSelected.family.card,
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - capLoss) *
          ((lineCover.fiberIndices parent).card : ENNReal) := by
      exact Finset.sum_le_sum fun parent _ => hfiber parent
    _ =
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - capLoss) *
          ∑ parent :
              Fin families.restriction.coarseSelected.family.card,
            ((lineCover.fiberIndices parent).card : ENNReal) := by
      rw [Finset.mul_sum]
    _ =
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - capLoss) *
          families.restriction.fineSelected.family.enncard := by
      rw [hsumCard]

end FourDegreeLemmaOutputData

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
