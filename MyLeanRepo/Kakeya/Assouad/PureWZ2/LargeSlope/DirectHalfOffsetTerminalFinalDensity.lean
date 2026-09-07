import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalFinalRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalExtremalBudgets

/-!
# Density and nonemptiness receipts for the actual final half-offset family

The requested-scale construction ends at a literal jointly selected target
family.  Density is therefore certified from a mass budget for that literal
family and its literal restricted shading; it is not inherited from the
ambient terminal shading.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

namespace PureWZ2DirectCommonYSourceAssembly
namespace TerminalGeometry
namespace PureWZ2ExternalWeightRegularizationData

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

/-- On the cleanup-supported pre-target, the external source weight is the
literal mass of the corresponding restricted carrier. -/
theorem selected_sourceWeight_eq_preTargetShading_volume
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount)
    (index : Fin (DirectHalfOffsetTerminalRequestedCWAPreTarget
      (commonSource := commonSource) regularization).card) :
    cleanup.sourceWeight (regularization.selected.embedding index) =
      volume ((halfOffsetTerminalCleanupTargetShading
        (commonSource := commonSource) regularization).carrier index) := by
  change cleanup.sourceWeight (regularization.selected.embedding index) =
    volume (cleanup.shading.carrier
      (halfOffsetTerminalCleanupTargetPreimage
        (commonSource := commonSource) regularization index))
  unfold PureWZ2HalfOffsetTerminalDistinctCleanupData.sourceWeight
  let target := halfOffsetTerminalCleanupTargetPreimage
    (commonSource := commonSource) regularization index
  have htarget := halfOffsetTerminalCleanupTargetPreimage_source
    (commonSource := commonSource) regularization index
  have hunique : ∀ other : Fin cleanup.family.family.card,
      cleanup.sourceIndex other = regularization.selected.embedding index ↔
        other = target := by
    intro other
    constructor
    · intro hother
      apply cleanup.sourceIndex_injective
      exact hother.trans htarget.symm
    · rintro rfl
      exact htarget
  simp_rw [hunique]
  rw [Fintype.sum_ite_eq']

/-- The selected dyadic source-weight level is retained by the literal final
joint shading.  The proof sums actual final carrier volumes, not an ambient
density certificate. -/
theorem DirectHalfOffsetTerminalRequestedCWAData.selectedWeightLevel_mul_finalCard_le_finalShading_mass
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant) :
    regularization.selectedWeightLevel * data.finalTarget.enncard ≤
      data.finalShading.mass := by
  change regularization.selectedWeightLevel * (data.finalTarget.card : ENNReal) ≤
    ∑ index : Fin data.finalTarget.card,
      volume ((halfOffsetTerminalCleanupTargetShading
        (commonSource := commonSource) regularization).carrier
          (data.finalTargetSubfamily.embedding index))
  calc
    regularization.selectedWeightLevel * (data.finalTarget.card : ENNReal) =
        ∑ _index : Fin data.finalTarget.card, regularization.selectedWeightLevel := by
          simp [mul_comm]
    _ ≤ ∑ index : Fin data.finalTarget.card,
        data.weight (data.finalTargetSubfamily.embedding index) := by
      apply Finset.sum_le_sum
      intro index _
      rw [data.weight_provenance]
      exact (regularization.selected_weight_band
        (data.finalTargetSubfamily.embedding index)).1
    _ = ∑ index : Fin data.finalTarget.card,
        volume ((halfOffsetTerminalCleanupTargetShading
          (commonSource := commonSource) regularization).carrier
            (data.finalTargetSubfamily.embedding index)) := by
      apply Finset.sum_congr rfl
      intro index _
      rw [data.weight_provenance]
      exact selected_sourceWeight_eq_preTargetShading_volume
        (commonSource := commonSource) regularization
          (data.finalTargetSubfamily.embedding index)

/-- The first complete-fiber selection retains positive total direct weight. -/
theorem DirectHalfOffsetTerminalRequestedCWAData.separated_weight_pos
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant) :
    0 < ∑ index : Fin
      (data.quotientSchedule.separatedFine data.weight data.selection).family.card,
        data.weight ((data.quotientSchedule.separatedFine data.weight
          data.selection).embedding index) := by
  let preTarget := DirectHalfOffsetTerminalRequestedCWAPreTarget
    (commonSource := commonSource) regularization
  have hsourceCard : 0 < regularization.selected.family.enncard := by
    change (0 : ENNReal) < (regularization.selected.family.card : ENNReal)
    exact_mod_cast regularization.selected_nonempty
  have hlevel : 0 < regularization.selectedWeightLevel *
      regularization.selected.family.enncard :=
    ENNReal.mul_pos regularization.selectedWeightLevel_pos.ne' hsourceCard.ne'
  have htotal : 0 < ∑ index : Fin preTarget.card, data.weight index := by
    have hbound : regularization.selectedWeightLevel *
        (preTarget.card : ENNReal) ≤
        ∑ index : Fin preTarget.card, data.weight index := by
      calc
        regularization.selectedWeightLevel * (preTarget.card : ENNReal) =
            ∑ _index : Fin preTarget.card, regularization.selectedWeightLevel := by
              simp [mul_comm]
        _ ≤ ∑ index : Fin preTarget.card, data.weight index := by
          apply Finset.sum_le_sum
          intro index _
          rw [data.weight_provenance]
          exact (regularization.selected_weight_band index).1
    change (0 : ENNReal) < ∑ index : Fin preTarget.card, data.weight index
    have hlevel' : 0 < regularization.selectedWeightLevel *
        (preTarget.card : ENNReal) := by
      change 0 < regularization.selectedWeightLevel *
        (preTarget.card : ENNReal) at hlevel
      exact hlevel
    exact hlevel'.trans_le hbound
  have hselectedPositive : 0 < ∑ index ∈ data.selection.selected,
      data.weight index :=
    pos_of_mul_pos_right (htotal.trans_le data.selection.retained_weight)
      (show (0 : ENNReal) ≤
        (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
          data.sourceSchedule.scaleCount from bot_le)
  let separated := data.quotientSchedule.separatedFine data.weight data.selection
  have hsum :
      (∑ index : Fin separated.family.card,
          data.weight (separated.embedding index)) =
        ∑ index ∈ data.selection.selected, data.weight index := by
    let indices := data.selection.selected
    have himageSum :
        (∑ index : Fin separated.family.card,
            data.weight (separated.embedding index)) =
          ∑ index ∈ Finset.image separated.embedding
              (Finset.univ : Finset (Fin separated.family.card)),
            data.weight index := by
      exact (Finset.sum_image
        (fun first _ second _ heq => separated.embedding.injective heq)).symm
    have himage : Finset.image separated.embedding
        (Finset.univ : Finset (Fin separated.family.card)) = indices := by
      change Finset.image (indices.orderEmbOfFin rfl)
          (Finset.univ : Finset (Fin indices.card)) = indices
      exact Finset.image_orderEmbOfFin_univ indices rfl
    exact himageSum.trans <| congrArg
      (fun selected => ∑ index ∈ selected, data.weight index) himage
  simpa only [separated] using hsum.symm ▸ hselectedPositive

/-- The second simultaneous selection cannot be empty, because it retains
positive total weight from the first complete-fiber selection. -/
theorem DirectHalfOffsetTerminalRequestedCWAData.joint_selected_nonempty
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant) :
    data.joint.selected.Nonempty := by
  have hpositive := data.separated_weight_pos
  have hretained := data.joint.retained_weight
  have hfinal : 0 < ∑ index ∈ data.joint.selected,
      data.weight ((data.quotientSchedule.separatedFine data.weight
        data.selection).embedding index) :=
    pos_of_mul_pos_right (hpositive.trans_le hretained)
      (show (0 : ENNReal) ≤ ((8 : ENNReal) *
        (Nat.log 2
          (2 * (data.quotientSchedule.separatedFine data.weight
            data.selection).family.card) + 1 : ENNReal) ^
            (data.sourceSchedule.scaleCount +
              data.sourceSchedule.scaleCount + 1)) from bot_le)
  by_contra hempty
  have hempty' : data.joint.selected = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  rw [hempty'] at hfinal
  simp at hfinal

/-- The actual final jointly selected target family is nonempty. -/
theorem DirectHalfOffsetTerminalRequestedCWAData.finalTarget_nonempty
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant) :
    data.finalTarget.Nonempty := by
  change 0 < data.joint.selected.card
  exact Finset.card_pos.mpr data.joint_selected_nonempty

/-- A nonempty joint selection gives a nonempty actual final target family.
This is only the structural passage from the selected finite index set to its
literal subfamily; any quantitative retention certificate belongs upstream. -/
theorem DirectHalfOffsetTerminalRequestedCWAData.finalTarget_nonempty_of_joint_selected
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant)
    (hselected : data.joint.selected.Nonempty) :
    data.finalTarget.Nonempty := by
  change 0 < data.joint.selected.card
  exact Finset.card_pos.mpr hselected

/-- The literal final jointly selected cubical shading is dense once its own
mass/cardinality budget is supplied.  The budget is deliberately expressed
using `data.finalTarget` and `data.finalShading`, so no ambient-density
restriction can discharge it. -/
theorem DirectHalfOffsetTerminalRequestedCWAData.finalShading_dense_of_mass_budget
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant)
    (outputLoss : ℝ)
    (hbudget :
      Kakeya.realRpowENN terminal.targetDelta outputLoss *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN terminal.targetDelta 2 *
              data.finalTarget.enncard) ≤
        data.finalShading.mass) :
    data.finalShading.IsLambdaDense
      (Kakeya.realRpowENN terminal.targetDelta outputLoss) := by
  apply pureWZ2_affineDiagonal_dense_of_mass_budget data.finalShading
    commonSource.halfOffsetLineClassTargetDelta_pos
    (le_trans (le_of_lt commonSource.halfOffsetLineClassTargetDelta_small)
      (by norm_num))
    data.finalTarget_line_class
    (Kakeya.realRpowENN terminal.targetDelta outputLoss)
  exact hbudget

/-- The selected-weight threshold supplies the final literal mass budget and
hence density of the actual final jointly selected shading. -/
theorem DirectHalfOffsetTerminalRequestedCWAData.finalShading_dense_of_selectedWeightLevel_budget
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant)
    (outputLoss : ℝ)
    (hbudget :
      Kakeya.realRpowENN terminal.targetDelta outputLoss *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN terminal.targetDelta 2) ≤
        regularization.selectedWeightLevel) :
    data.finalShading.IsLambdaDense
      (Kakeya.realRpowENN terminal.targetDelta outputLoss) := by
  apply data.finalShading_dense_of_mass_budget outputLoss
  calc
    Kakeya.realRpowENN terminal.targetDelta outputLoss *
        ((55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN terminal.targetDelta 2 *
            data.finalTarget.enncard) =
      (Kakeya.realRpowENN terminal.targetDelta outputLoss *
        ((55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN terminal.targetDelta 2)) *
            data.finalTarget.enncard := by ring
    _ ≤ regularization.selectedWeightLevel * data.finalTarget.enncard :=
      mul_le_mul_left hbudget _
    _ ≤ data.finalShading.mass :=
      data.selectedWeightLevel_mul_finalCard_le_finalShading_mass

end PureWZ2ExternalWeightRegularizationData
end TerminalGeometry
end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
