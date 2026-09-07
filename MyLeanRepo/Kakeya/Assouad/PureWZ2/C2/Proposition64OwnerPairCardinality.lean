import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteFiberRatio
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureFiberRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BodyCWAFiberwiseAssembly

/-!
# Source/target owner-pair cardinality

A target family is partitioned simultaneously by its target pure-cover parent
and by the parent of its source-provenance index in one source pure cover.
Source-fiber uniformity, uniformity of the nonempty pair classes, and one
global cardinality-retention inequality give a pointwise source-fiber to pair-
class ratio.  The source-parent count cancels; only the target-parent count
remains.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Cardinality of one joint target-parent/source-parent class. -/
def pureWZ2Proposition64OwnerPairCount
    {sourceParentCount : ℕ}
    {targetDelta targetRho : ℝ}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {targetCoarse : Kakeya.Streamlined.TubeFamily targetRho}
    (targetCover : WZ2PaperPurePartitioningCover targetFine targetCoarse)
    (sourceOwner : Fin targetFine.card → Fin sourceParentCount)
    (pair : Fin targetCoarse.card × Fin sourceParentCount) : ENNReal :=
  ((Finset.univ.filter fun index =>
    (targetCover.parent index, sourceOwner index) = pair).card : ENNReal)

/-- The joint owner classes partition the target family exactly. -/
theorem pureWZ2Proposition64_sum_ownerPairCount
    {sourceParentCount : ℕ}
    {targetDelta targetRho : ℝ}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {targetCoarse : Kakeya.Streamlined.TubeFamily targetRho}
    (targetCover : WZ2PaperPurePartitioningCover targetFine targetCoarse)
    (sourceOwner : Fin targetFine.card → Fin sourceParentCount) :
    (∑ pair : Fin targetCoarse.card × Fin sourceParentCount,
        pureWZ2Proposition64OwnerPairCount targetCover sourceOwner pair) =
      targetFine.enncard := by
  change
    (∑ pair : Fin targetCoarse.card × Fin sourceParentCount,
      (((Finset.univ : Finset (Fin targetFine.card)).filter fun index =>
        (targetCover.parent index, sourceOwner index) = pair).card :
          ENNReal)) =
      (targetFine.card : ENNReal)
  rw [← Nat.cast_sum]
  exact_mod_cast
    ((Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin targetFine.card))
      (Finset.univ :
        Finset (Fin targetCoarse.card × Fin sourceParentCount))
      (fun index => (targetCover.parent index, sourceOwner index))).trans
        (by simp))

/-- Inside one target full fiber, filtering by the pulled-back source owner is
exactly the corresponding global target/source owner-pair class. -/
theorem pureWZ2Proposition64_ownerPairCount_eq_bodyParentFiber_enncard
    {sourceParentCount : ℕ}
    {targetDelta targetRho : ℝ}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {targetCoarse : Kakeya.Streamlined.TubeFamily targetRho}
    (targetCover : WZ2PaperPurePartitioningCover targetFine targetCoarse)
    (htargetRho : 0 ≤ targetRho)
    (sourceOwner : Fin targetFine.card → Fin sourceParentCount)
    (targetParent : Fin targetCoarse.card)
    (targetJohn : WZ2PaperAssouadUnitRescalingData
      (targetCoarse.tube targetParent))
    (sourceParent : Fin sourceParentCount) :
    pureWZ2Proposition64OwnerPairCount targetCover sourceOwner
        (targetParent, sourceParent) =
      (wz2PaperBodyParentFiber
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := targetFine) (coarse := targetCoarse)
          targetParent targetJohn)
        (fun index => sourceOwner
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1)
        sourceParent).enncard := by
  let targetFiber :=
    wz2PaperOrdinaryFullFiberIndices targetFine targetCoarse targetParent
  let targetFiberEquiv :=
    wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := targetFine) (coarse := targetCoarse) targetParent
  let sourceIndices : Finset (Fin targetFine.card) :=
    Finset.univ.filter fun index =>
      (targetCover.parent index, sourceOwner index) =
        (targetParent, sourceParent)
  let fiberIndices : Finset (Fin targetFiber.card) :=
    Finset.univ.filter fun index =>
      sourceOwner (targetFiberEquiv index).1 = sourceParent
  have imageEq :
      Finset.image (fun index => (targetFiberEquiv index).1) fiberIndices =
        sourceIndices := by
    ext index
    simp only [Finset.mem_image, fiberIndices, Finset.mem_filter,
      Finset.mem_univ, true_and, sourceIndices]
    constructor
    · rintro ⟨fiberIndex, howner, rfl⟩
      have hparent :
          targetCover.parent (targetFiberEquiv fiberIndex).1 =
            targetParent :=
        (targetCover.mem_fullFiber_iff_parent_eq htargetRho
          targetParent (targetFiberEquiv fiberIndex).1).mp
            (targetFiberEquiv fiberIndex).2
      exact Prod.ext hparent howner
    · intro hpair
      have hparent : targetCover.parent index = targetParent :=
        congrArg Prod.fst hpair
      have howner : sourceOwner index = sourceParent :=
        congrArg Prod.snd hpair
      have hmem : index ∈ targetFiber :=
        (targetCover.mem_fullFiber_iff_parent_eq htargetRho
          targetParent index).mpr hparent
      let fiberIndex : Fin targetFiber.card :=
        targetFiberEquiv.symm ⟨index, hmem⟩
      refine ⟨fiberIndex, ?_, ?_⟩
      · simpa [fiberIndex, targetFiberEquiv] using howner
      · simpa [fiberIndex, targetFiberEquiv]
  change (sourceIndices.card : ENNReal) =
    (fiberIndices.card : ENNReal)
  exact_mod_cast (calc
    sourceIndices.card =
        (Finset.image (fun index => (targetFiberEquiv index).1)
          fiberIndices).card := by rw [imageEq]
    _ = fiberIndices.card :=
      Finset.card_image_of_injective _
        (fun _ _ equality =>
          targetFiberEquiv.injective (Subtype.ext equality)))

/-- A nonempty owner pair controls its complete source fiber.  The source
parent count cancels, leaving the target-parent count as the only multiplicity
factor. -/
theorem pureWZ2Proposition64_sourceFiberCount_le_ownerPairCount
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {targetCoarse : Kakeya.Streamlined.TubeFamily targetRho}
    {sourceConstant weight retentionConstant pairConstant : ENNReal}
    (sourceScale : WZ2PaperPureScaleCoverData
      sourceFine sourceRho sourceConstant)
    (sourceParentCountPos : 0 < sourceScale.coarse.card)
    (targetCover : WZ2PaperPurePartitioningCover targetFine targetCoarse)
    (sourceOwner : Fin targetFine.card → Fin sourceScale.coarse.card)
    (globalRetention :
      weight * sourceFine.enncard ≤
        retentionConstant * targetFine.enncard)
    (pairUniform :
      ∀ first second :
          Fin targetCoarse.card × Fin sourceScale.coarse.card,
        0 < pureWZ2Proposition64OwnerPairCount
            targetCover sourceOwner first →
        0 < pureWZ2Proposition64OwnerPairCount
            targetCover sourceOwner second →
        pureWZ2Proposition64OwnerPairCount
            targetCover sourceOwner first ≤
          pairConstant *
            pureWZ2Proposition64OwnerPairCount
              targetCover sourceOwner second)
    (targetParent : Fin targetCoarse.card)
    (sourceParent : Fin sourceScale.coarse.card)
    (blockNonempty :
      0 < pureWZ2Proposition64OwnerPairCount targetCover sourceOwner
        (targetParent, sourceParent)) :
    weight *
        wz2PaperOrdinaryFullFiberCount
          sourceFine sourceScale.coarse sourceParent ≤
      (sourceConstant * retentionConstant * targetCoarse.enncard *
        pairConstant) *
        pureWZ2Proposition64OwnerPairCount targetCover sourceOwner
          (targetParent, sourceParent) := by
  let sourceParentCount : ENNReal := sourceScale.coarse.enncard
  let targetParentCount : ENNReal := targetCoarse.enncard
  let sourceCount : Fin sourceScale.coarse.card → ENNReal := fun parent =>
    wz2PaperOrdinaryFullFiberCount sourceFine sourceScale.coarse parent
  let pairCount :
      Fin targetCoarse.card × Fin sourceScale.coarse.card → ENNReal :=
    pureWZ2Proposition64OwnerPairCount targetCover sourceOwner
  have hsourceParentCountZero : sourceParentCount ≠ 0 := by
    change (sourceScale.coarse.card : ENNReal) ≠ 0
    exact_mod_cast (Nat.ne_of_gt sourceParentCountPos)
  have hsourceParentCountTop : sourceParentCount ≠ ⊤ := by
    simp [sourceParentCount, Kakeya.Streamlined.TubeFamily.enncard]
  have hsourceSum :
      (∑ parent, sourceCount parent) = sourceFine.enncard := by
    exact sourceScale.cover.sum_fullFiberCount sourceScale.rho_pos.le
  have hsourceAverage :
      sourceParentCount * sourceCount sourceParent ≤
        sourceConstant * sourceFine.enncard := by
    calc
      sourceParentCount * sourceCount sourceParent =
          ∑ _parent : Fin sourceScale.coarse.card,
            sourceCount sourceParent := by
        simp [sourceParentCount,
          Kakeya.Streamlined.TubeFamily.enncard]
      _ ≤ ∑ parent : Fin sourceScale.coarse.card,
          sourceConstant * sourceCount parent := by
        exact Finset.sum_le_sum fun parent _ =>
          sourceScale.full_fiber_uniform sourceParent parent
      _ = sourceConstant * ∑ parent, sourceCount parent := by
        rw [Finset.mul_sum]
      _ = sourceConstant * sourceFine.enncard := by rw [hsourceSum]
  have htargetSum :
      (∑ pair, pairCount pair) = targetFine.enncard :=
    pureWZ2Proposition64_sum_ownerPairCount targetCover sourceOwner
  have hpairSum :
      targetFine.enncard ≤
        (targetParentCount * sourceParentCount) *
          (pairConstant * pairCount (targetParent, sourceParent)) := by
    rw [← htargetSum]
    calc
      (∑ pair, pairCount pair) ≤
          ∑ _pair : Fin targetCoarse.card × Fin sourceScale.coarse.card,
            pairConstant * pairCount (targetParent, sourceParent) := by
        apply Finset.sum_le_sum
        intro pair _
        by_cases hpairZero : pairCount pair = 0
        · rw [hpairZero]
          exact bot_le
        · exact pairUniform pair (targetParent, sourceParent)
            (bot_lt_iff_ne_bot.mpr hpairZero) blockNonempty
      _ = (targetParentCount * sourceParentCount) *
          (pairConstant * pairCount (targetParent, sourceParent)) := by
        simp [targetParentCount, sourceParentCount,
          Kakeya.Streamlined.TubeFamily.enncard, Fintype.card_prod]
  have hwithSourceParentCount :
      sourceParentCount *
          (weight * sourceCount sourceParent) ≤
        sourceParentCount *
          ((sourceConstant * retentionConstant * targetParentCount *
              pairConstant) *
            pairCount (targetParent, sourceParent)) := by
    calc
      sourceParentCount * (weight * sourceCount sourceParent) =
          weight * (sourceParentCount * sourceCount sourceParent) := by ring
      _ ≤ weight * (sourceConstant * sourceFine.enncard) := by gcongr
      _ = sourceConstant * (weight * sourceFine.enncard) := by ring
      _ ≤ sourceConstant *
          (retentionConstant * targetFine.enncard) := by gcongr
      _ ≤ sourceConstant *
          (retentionConstant *
            ((targetParentCount * sourceParentCount) *
              (pairConstant * pairCount (targetParent, sourceParent)))) := by
        gcongr
      _ = sourceParentCount *
          ((sourceConstant * retentionConstant * targetParentCount *
              pairConstant) *
            pairCount (targetParent, sourceParent)) := by ring
  apply (ENNReal.mul_le_mul_iff_left
    hsourceParentCountZero hsourceParentCountTop).mp
  simpa [sourceParentCount, targetParentCount, sourceCount, pairCount,
    mul_comm] using hwithSourceParentCount

/-- A local-fanout version of the owner-pair estimate.  Instead of paying for
all target parents, it counts only the target parents paired with one fixed
source parent.  This is the form needed after a geometric affine transport:
the source-parent count then cancels exactly, while the local target fanout is
handled by geometry. -/
theorem
    pureWZ2Proposition64_sourceFiberCount_le_ownerPairCount_of_localFanout
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {targetCoarse : Kakeya.Streamlined.TubeFamily targetRho}
    {sourceConstant weight retentionConstant pairConstant
      targetMultiplicity : ENNReal}
    (sourceScale : WZ2PaperPureScaleCoverData
      sourceFine sourceRho sourceConstant)
    (sourceParentCountPos : 0 < sourceScale.coarse.card)
    (targetCover : WZ2PaperPurePartitioningCover targetFine targetCoarse)
    (sourceOwner : Fin targetFine.card → Fin sourceScale.coarse.card)
    (globalRetention :
      weight * sourceFine.enncard ≤
        retentionConstant * targetFine.enncard)
    (pairUniform :
      ∀ first second :
          Fin targetCoarse.card × Fin sourceScale.coarse.card,
        0 < pureWZ2Proposition64OwnerPairCount
            targetCover sourceOwner first →
        0 < pureWZ2Proposition64OwnerPairCount
            targetCover sourceOwner second →
        pureWZ2Proposition64OwnerPairCount
            targetCover sourceOwner first ≤
          pairConstant *
            pureWZ2Proposition64OwnerPairCount
              targetCover sourceOwner second)
    (localFanout : ∀ sourceParent : Fin sourceScale.coarse.card,
      (((Finset.univ : Finset (Fin targetCoarse.card)).filter fun targetParent =>
          0 < pureWZ2Proposition64OwnerPairCount targetCover sourceOwner
            (targetParent, sourceParent)).card : ENNReal) ≤
        targetMultiplicity)
    (targetParent : Fin targetCoarse.card)
    (sourceParent : Fin sourceScale.coarse.card)
    (blockNonempty :
      0 < pureWZ2Proposition64OwnerPairCount targetCover sourceOwner
        (targetParent, sourceParent)) :
    weight *
        wz2PaperOrdinaryFullFiberCount
          sourceFine sourceScale.coarse sourceParent ≤
      (sourceConstant * retentionConstant * targetMultiplicity *
        pairConstant) *
        pureWZ2Proposition64OwnerPairCount targetCover sourceOwner
          (targetParent, sourceParent) := by
  let sourceParentCount : ENNReal := sourceScale.coarse.enncard
  let sourceCount : Fin sourceScale.coarse.card → ENNReal := fun parent =>
    wz2PaperOrdinaryFullFiberCount sourceFine sourceScale.coarse parent
  let pairCount :
      Fin targetCoarse.card × Fin sourceScale.coarse.card → ENNReal :=
    pureWZ2Proposition64OwnerPairCount targetCover sourceOwner
  have hsourceParentCountZero : sourceParentCount ≠ 0 := by
    change (sourceScale.coarse.card : ENNReal) ≠ 0
    exact_mod_cast (Nat.ne_of_gt sourceParentCountPos)
  have hsourceParentCountTop : sourceParentCount ≠ ⊤ := by
    simp [sourceParentCount, Kakeya.Streamlined.TubeFamily.enncard]
  have hsourceSum :
      (∑ parent, sourceCount parent) = sourceFine.enncard := by
    exact sourceScale.cover.sum_fullFiberCount sourceScale.rho_pos.le
  have hsourceAverage :
      sourceParentCount * sourceCount sourceParent ≤
        sourceConstant * sourceFine.enncard := by
    calc
      sourceParentCount * sourceCount sourceParent =
          ∑ _parent : Fin sourceScale.coarse.card,
            sourceCount sourceParent := by
        simp [sourceParentCount,
          Kakeya.Streamlined.TubeFamily.enncard]
      _ ≤ ∑ parent : Fin sourceScale.coarse.card,
          sourceConstant * sourceCount parent := by
        exact Finset.sum_le_sum fun parent _ =>
          sourceScale.full_fiber_uniform sourceParent parent
      _ = sourceConstant * ∑ parent, sourceCount parent := by
        rw [Finset.mul_sum]
      _ = sourceConstant * sourceFine.enncard := by rw [hsourceSum]
  have htargetSum :
      (∑ pair, pairCount pair) = targetFine.enncard :=
    pureWZ2Proposition64_sum_ownerPairCount targetCover sourceOwner
  have hlocalSum : ∀ otherSource : Fin sourceScale.coarse.card,
      (∑ otherTarget : Fin targetCoarse.card,
          pairCount (otherTarget, otherSource)) ≤
        targetMultiplicity *
          (pairConstant * pairCount (targetParent, sourceParent)) := by
    intro otherSource
    let active : Finset (Fin targetCoarse.card) :=
      Finset.univ.filter fun otherTarget =>
        0 < pairCount (otherTarget, otherSource)
    have hsumActive :
        (∑ otherTarget : Fin targetCoarse.card,
            pairCount (otherTarget, otherSource)) =
          ∑ otherTarget ∈ active,
            pairCount (otherTarget, otherSource) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro otherTarget _ hnot
      have hnonpos : ¬0 < pairCount (otherTarget, otherSource) := by
        simpa [active] using hnot
      exact nonpos_iff_eq_zero.mp (not_lt.mp hnonpos)
    rw [hsumActive]
    calc
      (∑ otherTarget ∈ active,
          pairCount (otherTarget, otherSource)) ≤
          ∑ _otherTarget ∈ active,
            pairConstant * pairCount (targetParent, sourceParent) := by
        apply Finset.sum_le_sum
        intro otherTarget hactive
        exact pairUniform (otherTarget, otherSource)
          (targetParent, sourceParent)
          (by simpa [active] using (Finset.mem_filter.mp hactive).2)
          blockNonempty
      _ = (active.card : ENNReal) *
          (pairConstant * pairCount (targetParent, sourceParent)) := by
        simp
      _ ≤ targetMultiplicity *
          (pairConstant * pairCount (targetParent, sourceParent)) := by
        gcongr
        exact localFanout otherSource
  have hpairSum :
      targetFine.enncard ≤
        sourceParentCount *
          (targetMultiplicity *
            (pairConstant * pairCount (targetParent, sourceParent))) := by
    rw [← htargetSum, Fintype.sum_prod_type, Finset.sum_comm]
    calc
      (∑ otherSource : Fin sourceScale.coarse.card,
          ∑ otherTarget : Fin targetCoarse.card,
            pairCount (otherTarget, otherSource)) ≤
          ∑ _otherSource : Fin sourceScale.coarse.card,
            targetMultiplicity *
              (pairConstant * pairCount (targetParent, sourceParent)) := by
        exact Finset.sum_le_sum fun otherSource _ => hlocalSum otherSource
      _ = sourceParentCount *
          (targetMultiplicity *
            (pairConstant * pairCount (targetParent, sourceParent))) := by
        simp [sourceParentCount,
          Kakeya.Streamlined.TubeFamily.enncard]
  have hwithSourceParentCount :
      sourceParentCount * (weight * sourceCount sourceParent) ≤
        sourceParentCount *
          ((sourceConstant * retentionConstant * targetMultiplicity *
              pairConstant) *
            pairCount (targetParent, sourceParent)) := by
    calc
      sourceParentCount * (weight * sourceCount sourceParent) =
          weight * (sourceParentCount * sourceCount sourceParent) := by ring
      _ ≤ weight * (sourceConstant * sourceFine.enncard) := by gcongr
      _ = sourceConstant * (weight * sourceFine.enncard) := by ring
      _ ≤ sourceConstant *
          (retentionConstant * targetFine.enncard) := by gcongr
      _ ≤ sourceConstant *
          (retentionConstant *
            (sourceParentCount *
              (targetMultiplicity *
                (pairConstant * pairCount
                  (targetParent, sourceParent))))) := by
        gcongr
      _ = sourceParentCount *
          ((sourceConstant * retentionConstant * targetMultiplicity *
              pairConstant) *
            pairCount (targetParent, sourceParent)) := by ring
  apply (ENNReal.mul_le_mul_iff_left
    hsourceParentCountZero hsourceParentCountTop).mp
  simpa [sourceParentCount, sourceCount, pairCount, mul_comm]
    using hwithSourceParentCount

end Kakeya.Assouad

end
