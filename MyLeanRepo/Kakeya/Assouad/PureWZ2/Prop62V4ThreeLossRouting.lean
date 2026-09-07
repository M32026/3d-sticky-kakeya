import MyLeanRepo.Kakeya.Assouad.PureWZ2.CompleteFiberNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4CriticalFloorRouting

/-!
# Proposition 6.2 V4 three-loss routing

This module separates the source loss used by complete-fiber normalization,
the normalization loss used by the cropped output, and the working loss used
by the V4 refinement.  It does not assemble the final universal or Node 3
output.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open Kakeya.Assouad

/--
The three loss scales needed to pass a complete-fiber normalization into the
V4 continuation without changing the shared final-loss hierarchy.
-/
structure Prop62V4ThreeLossRoutingData
    {polylogExponent cwaPower packetDensityExponent cwaLossExponent : ℕ}
    {sigma outputLoss : ℝ}
    (routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss) where
  sourceLoss : ℝ
  normalizationLoss : ℝ
  workingEta : ℝ
  sourceLoss_eq :
    sourceLoss =
      pureWZ2CompleteNormalizationFinalLoss normalizationLoss
  normalizationLoss_eq :
    normalizationLoss = routing.numerics.hierarchy.sourceLoss
  workingEta_eq :
    workingEta = routing.numerics.hierarchy.stableLoss
  sourceLoss_pos : 0 < sourceLoss
  normalizationLoss_pos : 0 < normalizationLoss
  workingEta_pos : 0 < workingEta
  sourceLoss_le_eighth :
    sourceLoss ≤ normalizationLoss / 8
  sourceLoss_le_half :
    sourceLoss ≤ normalizationLoss / 2
  sourceLoss_le_hierarchy :
    sourceLoss ≤ routing.numerics.hierarchy.sourceLoss
  normalizationLoss_lt_workingEta :
    normalizationLoss < workingEta
  normalizationLoss_output_budget :
    2 * normalizationLoss < outputLoss

/--
Choose the normalization source loss from the complete-fiber normalization
hierarchy, while reusing the existing V4 hierarchy source loss as the cropped
normalization loss and its stable loss as the working refinement parameter.
-/
theorem prop62V4_three_loss_routing
    {polylogExponent cwaPower packetDensityExponent cwaLossExponent : ℕ}
    {sigma outputLoss : ℝ}
    (routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss)
    (outputLossLeOne : outputLoss ≤ 1) :
    Nonempty (Prop62V4ThreeLossRoutingData routing) := by
  let hierarchy := routing.numerics.hierarchy
  let normalizationLoss := hierarchy.sourceLoss
  let sourceLoss :=
    pureWZ2CompleteNormalizationFinalLoss normalizationLoss
  let workingEta := hierarchy.stableLoss
  have normalizationLossPos : 0 < normalizationLoss :=
    hierarchy.sourceLoss_pos
  have sourceLossPos : 0 < sourceLoss := by
    dsimp only [sourceLoss, pureWZ2CompleteNormalizationFinalLoss]
    exact lt_min (by positivity) (by norm_num)
  have workingEtaPos : 0 < workingEta :=
    normalizationLossPos.trans hierarchy.source_stable
  have sourceLossLeEighth :
      sourceLoss ≤ normalizationLoss / 8 := by
    dsimp only [sourceLoss, pureWZ2CompleteNormalizationFinalLoss]
    exact min_le_left _ _
  have sourceLossLeHalf :
      sourceLoss ≤ normalizationLoss / 2 := by
    nlinarith
  have sourceLossLeHierarchy :
      sourceLoss ≤ hierarchy.sourceLoss := by
    change sourceLoss ≤ normalizationLoss
    nlinarith
  have normalizationLossWorking :
      normalizationLoss < workingEta :=
    hierarchy.source_stable
  have structuralFinal :
      routing.critical.structuralLoss < outputLoss / 4 := by
    calc
      routing.critical.structuralLoss <
          hierarchy.finalStrongLoss :=
        routing.numerics.structural_final
      _ = outputLoss / 4 := by
        rw [hierarchy.finalStrongLoss_eq]
        rfl
  have structuralLeOne :
      routing.critical.structuralLoss ≤ 1 := by
    nlinarith [routing.critical.structuralLoss_pos]
  have structuralSquareLe :
      routing.critical.structuralLoss ^ 2 ≤
        routing.critical.structuralLoss := by
    nlinarith [routing.critical.structuralLoss_pos]
  have normalizationLossOutput :
      2 * normalizationLoss < outputLoss := by
    rw [show normalizationLoss = hierarchy.sourceLoss by rfl,
      hierarchy.sourceLoss_eq]
    dsimp only [wz2PaperFinalSourceLoss]
    nlinarith
  exact
    ⟨{
      sourceLoss := sourceLoss
      normalizationLoss := normalizationLoss
      workingEta := workingEta
      sourceLoss_eq := rfl
      normalizationLoss_eq := rfl
      workingEta_eq := rfl
      sourceLoss_pos := sourceLossPos
      normalizationLoss_pos := normalizationLossPos
      workingEta_pos := workingEtaPos
      sourceLoss_le_eighth := sourceLossLeEighth
      sourceLoss_le_half := sourceLossLeHalf
      sourceLoss_le_hierarchy := sourceLossLeHierarchy
      normalizationLoss_lt_workingEta := normalizationLossWorking
      normalizationLoss_output_budget := normalizationLossOutput
    }⟩

end Kakeya.Assouad.Prop62PaperAudit.V4

end
