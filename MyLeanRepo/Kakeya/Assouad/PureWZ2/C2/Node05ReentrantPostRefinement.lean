import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.StickyRefinementData
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ExactNode4ReentryAdapter

/-!
# Reentrant sticky output after the Node 5 simultaneous refinement

This module packages one exact `PureWZ2ReentrantPropStickyData` with the
receipts created strictly after that seed.  It does not derive a
same-extremizer theorem from the paper-facing Node 4 conjunction.

The seed already supplies all ordinary Proposition 6.2 fields through
`seed.data`.  The receipt below contains only the subsequent fine/coarse
refinements, their dependent identifications with the final public-shaped
data, and the six quantitative conclusions required by
`PureWZ2Node5StickyData`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Explicit facts produced after one reentrant Proposition 6.2 seed. -/
structure PureWZ2Node05PostRefinementReceipt
    {delta sigma seedLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {seedNormalizationExponent seedLogExponent logExponent : ℕ}
    (seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent) where
  fineRefinementExponent : ℕ
  fineRefinement :
    WZ1PaperRefinement seed.data.refined fineRefinementExponent
  coarseRefinementExponent : ℕ
  coarseRefinement :
    WZ1PaperRefinement
      seed.data.croppedCoarseShading coarseRefinementExponent
  data :
    PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent
  logExponent_eq :
    logExponent = seedLogExponent + fineRefinementExponent
  selected_eq :
    data.selected = seed.data.selected.comp fineRefinement.selected
  refined_eq : HEq data.refined fineRefinement.refined
  coarse_eq : data.coarse = coarseRefinement.selected.family
  croppedCoarseShading_eq :
    HEq data.croppedCoarseShading coarseRefinement.refined
  balanced : PureWZ2Node5BalancedCoverData data.balanced
  fineMultiplicity : ℕ
  fineMultiplicity_pos : 0 < fineMultiplicity
  refined_multiplicity_band :
    data.refined.HasConstantMultiplicity
      fineMultiplicity (2 * fineMultiplicity)
  refined_extremal :
    WZ2PaperCroppedIsExtremal
      sigma outputLoss data.selected.family data.refined
  refined_volume_lower :
    Kakeya.realRpowENN delta (sigma + outputLoss) ≤
      volume data.refined.union
  full_fiber_uniform :
    ∀ first second : Fin data.coarse.card,
      ((wz2PaperFullFiberIndices
          data.selected.family data.coarse first).card : ENNReal) ≤
        Kakeya.realRpowENN rho.1 (-outputLoss) *
          ((wz2PaperFullFiberIndices
            data.selected.family data.coarse second).card : ENNReal)
  coarse_volume_lower :
    Kakeya.realRpowENN rho.1 (sigma + outputLoss) ≤
      volume data.croppedCoarseShading.union

/-- A single exact reentrant seed paired with its post-refinement receipt. -/
structure PureWZ2Node05ReentrantPostRefinementData
    {delta sigma seedLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading source)
    (rho : WZ2PaperRequestedScale delta)
    (seedNormalizationExponent seedLogExponent logExponent : ℕ) where
  seed :
    PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent
  post :
    PureWZ2Node05PostRefinementReceipt
      (outputLoss := outputLoss) (logExponent := logExponent) seed

namespace PureWZ2Node05ReentrantPostRefinementData

variable
    {delta sigma seedLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {seedNormalizationExponent seedLogExponent logExponent : ℕ}

/-- Forget only the wrapper and expose the exact final public sticky data. -/
abbrev finalData
    (output : PureWZ2Node05ReentrantPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent
        logExponent) :=
  output.post.data

/-- Assemble the downstream Node 5 object.  All ordinary sticky fields are
inherited through `post.data`; only genuine post-refinement receipts are
copied from `post`. -/
def toNode5StickyData
    (output : PureWZ2Node05ReentrantPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent
        logExponent) :
    PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent where
  seedLoss := seedLoss
  seedNormalizationExponent := seedNormalizationExponent
  seedLogExponent := seedLogExponent
  seed := output.seed
  fineRefinementExponent := output.post.fineRefinementExponent
  fineRefinement := output.post.fineRefinement
  coarseRefinementExponent := output.post.coarseRefinementExponent
  coarseRefinement := output.post.coarseRefinement
  data := output.post.data
  logExponent_eq := output.post.logExponent_eq
  selected_eq := output.post.selected_eq
  refined_eq := output.post.refined_eq
  coarse_eq := output.post.coarse_eq
  croppedCoarseShading_eq := output.post.croppedCoarseShading_eq
  balanced := output.post.balanced
  fineMultiplicity := output.post.fineMultiplicity
  fineMultiplicity_pos := output.post.fineMultiplicity_pos
  refined_multiplicity_band := output.post.refined_multiplicity_band
  refined_extremal := output.post.refined_extremal
  refined_volume_lower := output.post.refined_volume_lower
  full_fiber_uniform := output.post.full_fiber_uniform
  coarse_volume_lower := output.post.coarse_volume_lower

/-- The assembled output is certified to refine this exact reentrant seed. -/
theorem toNode5StickyData_refines_seed
    (output : PureWZ2Node05ReentrantPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent
        logExponent) :
    PureWZ2Node5StickyRefinesReentrantSeed
      output.seed output.toNode5StickyData where
  seedLoss_eq := rfl
  seedNormalizationExponent_eq := rfl
  seedLogExponent_eq := rfl
  seed_eq := HEq.rfl

@[simp] theorem toNode5StickyData_data
    (output : PureWZ2Node05ReentrantPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent
        logExponent) :
    output.toNode5StickyData.data = output.finalData := rfl

@[simp] theorem toNode5StickyData_seed
    (output : PureWZ2Node05ReentrantPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent
        logExponent) :
    HEq output.toNode5StickyData.seed output.seed := HEq.rfl

@[simp] theorem toNode5StickyData_selected
    (output : PureWZ2Node05ReentrantPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent
        logExponent) :
    output.toNode5StickyData.selected = output.finalData.selected := rfl

@[simp] theorem toNode5StickyData_refined
    (output : PureWZ2Node05ReentrantPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent
        logExponent) :
    HEq output.toNode5StickyData.refined output.finalData.refined := HEq.rfl

@[simp] theorem toNode5StickyData_coarse
    (output : PureWZ2Node05ReentrantPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent
        logExponent) :
    output.toNode5StickyData.coarse = output.finalData.coarse := rfl

@[simp] theorem toNode5StickyData_croppedCoarseShading
    (output : PureWZ2Node05ReentrantPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent
        logExponent) :
    HEq output.toNode5StickyData.croppedCoarseShading
      output.finalData.croppedCoarseShading := HEq.rfl

@[simp] theorem toNode5StickyData_cover
    (output : PureWZ2Node05ReentrantPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent
        logExponent) :
    HEq output.toNode5StickyData.cover output.finalData.cover := HEq.rfl

end PureWZ2Node05ReentrantPostRefinementData

end Kakeya.Assouad

end
