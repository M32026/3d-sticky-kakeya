import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProductMultiplicityLower

/-!
# Proposition 6.2: component multiplicity floors

The global product lower bound is split into separate lower bounds for
`muFine` and `muCoarse` using the opposite critical cap.

The final fine family is first identified with the disjoint union of the
complete genuine metric fibers.  The only comparison loss is the already
frozen factor-two fiber-cardinality band.  No assigned packet or new
subfamily appears.
-/

noncomputable section

namespace Kakeya.Assouad

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

/-- The final fine cardinality is the exact sum of the complete metric fibers. -/
theorem sum_terminalFiber_enncard :
    (∑ parent :
        Fin families.restriction.coarseSelected.family.card,
      (families.terminalFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent).family.enncard) =
      families.restriction.fineSelected.family.enncard := by
  have naturalSum :
      (∑ parent :
          Fin families.restriction.coarseSelected.family.card,
        (families.restriction.lineCover.fiberIndices parent).card) =
        families.restriction.fineSelected.family.card := by
    have fiberwise :=
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ :
          Finset
            (Fin families.restriction.fineSelected.family.card))
        (Finset.univ :
          Finset
            (Fin families.restriction.coarseSelected.family.card))
        families.restriction.lineCover.parent
    simpa [WZ1PaperTubeCover.fiberIndices] using fiberwise
  calc
    (∑ parent :
        Fin families.restriction.coarseSelected.family.card,
      (families.terminalFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent).family.enncard) =
        ∑ parent :
            Fin families.restriction.coarseSelected.family.card,
          ((families.restriction.lineCover.fiberIndices parent).card :
            ENNReal) := by
      apply Finset.sum_congr rfl
      intro parent _
      change
        ((wz2PaperFullFiberIndices
          families.restriction.fineSelected.family
          families.restriction.coarseSelected.family parent).card :
            ENNReal) =
          ((families.restriction.lineCover.fiberIndices parent).card :
            ENNReal)
      have fiberEq :
          wz2PaperFullFiberIndices
              families.restriction.fineSelected.family
              families.restriction.coarseSelected.family parent =
            families.restriction.lineCover.fiberIndices parent := by
        ext source
        exact
          (mem_lineCover_fiberIndices_iff_fullFiber
            input multiplicity parentClass treeCleanup exactification
              parentDegree core families parent source).symm
      rw [fiberEq]
    _ =
        (families.restriction.fineSelected.family.card : ENNReal) := by
      rw [← Nat.cast_sum]
      exact_mod_cast naturalSum
    _ =
        families.restriction.fineSelected.family.enncard := by
      simp [Kakeya.Streamlined.TubeFamily.enncard]

theorem fiberFloor_mul_coarse_enncard_le_fine_enncard :
    (output.fiberFloor : ENNReal) *
        families.restriction.coarseSelected.family.enncard ≤
      families.restriction.fineSelected.family.enncard := by
  rw [← sum_terminalFiber_enncard
    input multiplicity parentClass treeCleanup exactification
      parentDegree core families]
  calc
    (output.fiberFloor : ENNReal) *
          families.restriction.coarseSelected.family.enncard =
        ∑ _parent :
            Fin families.restriction.coarseSelected.family.card,
          (output.fiberFloor : ENNReal) := by
      simp [
        Kakeya.Streamlined.TubeFamily.enncard,
        Finset.sum_const,
        nsmul_eq_mul
      ]
      ring
    _ ≤
        ∑ parent :
            Fin families.restriction.coarseSelected.family.card,
          (families.terminalFiber
            input multiplicity parentClass treeCleanup exactification
              parentDegree core parent).family.enncard := by
      exact
        Finset.sum_le_sum fun parent _ => by
          change
            (output.fiberFloor : ENNReal) ≤
              ((wz2PaperFullFiberIndices
                families.restriction.fineSelected.family
                families.restriction.coarseSelected.family parent).card :
                  ENNReal)
          exact_mod_cast (output.fiber_cardinality parent).1

theorem terminalFiber_enncard_le_two_mul_fiberFloor
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    (families.terminalFiber
      input multiplicity parentClass treeCleanup exactification
        parentDegree core parent).family.enncard ≤
      2 * (output.fiberFloor : ENNReal) := by
  change
    ((wz2PaperFullFiberIndices
      families.restriction.fineSelected.family
      families.restriction.coarseSelected.family parent).card : ENNReal) ≤
        2 * (output.fiberFloor : ENNReal)
  exact_mod_cast (output.fiber_cardinality parent).2.le

theorem finalCoarse_card_pos :
    0 < families.restriction.coarseSelected.family.card := by
  have fineCardPos :
      0 < families.restriction.fineSelected.family.card := by
    rw [families.restriction.fineSelected_eq]
    change 0 < families.terminalFine.card
    exact families.terminalFine_nonempty.card_pos
  let source :
      Fin families.restriction.fineSelected.family.card :=
    ⟨0, fineCardPos⟩
  have parentLt :=
    (families.restriction.lineCover.parent source).isLt
  omega

theorem coarseLoss_pos :
    0 < output.coarseLoss := by
  rw [output.coarseLoss_eq]
  unfold FourDegreeCoreAssemblyData.terminalCoarseMultiplicityLoss
  exact Nat.mul_pos (by norm_num) (pow_pos core.A0_pos 2)

/--
The two scalar absorptions that convert the product lower bound and opposite
critical caps into the paper's component floors.
-/
structure ComponentMultiplicityFloorInputsData
    {sigma floorLoss capLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (desiredProduct desiredFine desiredCoarse : ENNReal) : Prop where
  fine_scalar :
    (desiredFine * 2) *
        ((output.coarseLoss : ENNReal) *
          Kakeya.realRpowENN rho (2 - sigma - capLoss)) ≤
      desiredProduct
  coarse_scalar :
    desiredCoarse *
        (((output.coarseLoss : ENNReal) *
          Kakeya.realRpowENN (delta / rho)
            (2 - sigma - capLoss)) * 2) ≤
      desiredProduct

theorem fine_multiplicity_lower
    {sigma floorLoss capLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (criticalInputs :
      output.CriticalMultiplicityInputsData
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
    ∀ parent :
        Fin families.restriction.coarseSelected.family.card,
      desiredFine *
          (families.terminalFiber
            input multiplicity parentClass treeCleanup exactification
              parentDegree core parent).family.enncard ≤
        (output.muFine : ENNReal) := by
  intro parent
  let coarseCard :=
    families.restriction.coarseSelected.family.enncard
  let fiberFloor : ENNReal := output.fiberFloor
  let coarseCoefficient :=
    Kakeya.realRpowENN rho (2 - sigma - capLoss)
  let coarseFactor :=
    (output.coarseLoss : ENNReal) * coarseCoefficient
  have productLower :=
    output.product_multiplicity_lower
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families productInputs
  have coarseCap :=
    output.coarse_multiplicity_upper_of_critical_inputs
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families critical criticalInputs
  have coarseCardZero : coarseCard ≠ 0 := by
    have cardPos :=
      finalCoarse_card_pos
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families
    simp [
      coarseCard,
      Kakeya.Streamlined.TubeFamily.enncard,
      Nat.ne_of_gt cardPos
    ]
  have coarseCardTop : coarseCard ≠ ⊤ := by
    exact ENNReal.natCast_ne_top _
  have withCoarseCard :
      desiredProduct * fiberFloor ≤
        coarseFactor * (output.muFine : ENNReal) := by
    apply
      (ENNReal.mul_le_mul_iff_right
        coarseCardZero coarseCardTop).mp
    calc
      coarseCard * (desiredProduct * fiberFloor) =
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
            (coarseCoefficient * coarseCard)) *
              output.muFine := by
        gcongr
      _ =
          coarseCard *
            (coarseFactor * (output.muFine : ENNReal)) := by
        ring
  have coarseFactorZero : coarseFactor ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast
        (output.coarseLoss_pos
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families).ne'
    · simp [
        coarseCoefficient,
        Kakeya.realRpowENN,
        Real.rpow_pos_of_pos input.rho_pos
      ]
  have coarseFactorTop : coarseFactor ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top _)
      (by simp [coarseCoefficient, Kakeya.realRpowENN])
  have fineFloor :
      desiredFine * (2 * fiberFloor) ≤
        (output.muFine : ENNReal) := by
    apply
      (ENNReal.mul_le_mul_iff_left
        coarseFactorZero coarseFactorTop).mp
    calc
      (desiredFine * (2 * fiberFloor)) * coarseFactor =
          ((desiredFine * 2) * coarseFactor) * fiberFloor := by
        ring
      _ ≤ desiredProduct * fiberFloor := by
        gcongr
        exact componentInputs.fine_scalar
      _ ≤ (output.muFine : ENNReal) * coarseFactor := by
        simpa [mul_comm] using withCoarseCard
  calc
    desiredFine *
        (families.terminalFiber
          input multiplicity parentClass treeCleanup exactification
            parentDegree core parent).family.enncard ≤
      desiredFine * (2 * fiberFloor) := by
        gcongr
        exact
          output.terminalFiber_enncard_le_two_mul_fiberFloor
            input multiplicity parentClass treeCleanup exactification
              parentDegree core good families parent
    _ ≤ (output.muFine : ENNReal) := fineFloor

theorem coarse_multiplicity_lower
    {sigma floorLoss capLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (criticalInputs :
      output.CriticalMultiplicityInputsData
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
    output.fine_multiplicity_upper_of_critical_inputs
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families
        critical criticalInputs parent
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

end FourDegreeLemmaOutputData

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
