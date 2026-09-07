import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantPrefix
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalExactLiftedMultiWindow
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerTwoCallAssembly

/-!
# Exact terminal production on a reentrant hierarchy source

The terminal call must use the precise family and shading retained by the
ordinary prefix.  This file records the direct Node-5 owner call on that
source and then routes the resulting sticky data through the existing lifted
multi-window terminal assembly.

The owner input is indexed by `current.reentry.toNormalizationData`; hence its
cropped source is definitionally `current.grain.shading`.  No family or
normalization witness is reselected.  The final conditional record isolates
the remaining source-indexed terminal construction as one dependent value.
-/

noncomputable section

namespace Kakeya.Assouad

/-- One exact owner call at the terminal `sqrt delta` scale, based on the
normalization trace already stored in the current hierarchy source. -/
structure PureWZ2ReentrantTerminalOwnerCall
    {sigma inputLoss delta : ℝ}
    {normalizationExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent)
    (stickyLoss : ℝ) where
  seedLoss : ℝ
  seedLogExponent : ℕ
  outputLogExponent : ℕ
  sqrtRequested : WZ2PaperRequestedScale delta
  sqrtRequested_eq : sqrtRequested.1 = Real.sqrt delta
  seed : PureWZ2ReentrantPropStickyData
    (sigma := sigma) (outputLoss := seedLoss) current.grain.shading
    sqrtRequested normalizationExponent seedLogExponent
  call : PureWZ2Node05DeterministicOwnerCallReceipt
    seed stickyLoss outputLogExponent

namespace PureWZ2ReentrantTerminalOwnerCall

variable
    {sigma inputLoss delta stickyLoss : ℝ}
    {normalizationExponent : ℕ}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}

/-- Forget the exact-multiplicity implementation after the owner call and
retain precisely the sticky package consumed by terminal geometry. -/
noncomputable def toTerminalScaleStickyData
    (owner : PureWZ2ReentrantTerminalOwnerCall current stickyLoss) :
    PureWZ2TerminalScaleStickyData
      current.grain stickyLoss owner.outputLogExponent where
  sqrtRequested := owner.sqrtRequested
  sqrtRequested_eq := owner.sqrtRequested_eq
  sticky := owner.call.output.toNode5StickyData.toTerminalStickyCore

@[simp] theorem toTerminalScaleStickyData_sticky
    (owner : PureWZ2ReentrantTerminalOwnerCall current stickyLoss) :
    owner.toTerminalScaleStickyData.sticky =
      owner.call.output.toNode5StickyData.toTerminalStickyCore := rfl

end PureWZ2ReentrantTerminalOwnerCall

/--
The remaining source-indexed terminal leaf after the exact owner call.  All
fields refer to the same `terminal`, so a chain, an absorption receipt, or a
height lift from a different source cannot be substituted.  Once this value
is supplied, the final residue selection and exact-level packaging are the
closed `TerminalExactLiftedMultiWindow` construction.
-/
structure PureWZ2ReentrantTerminalLiftedLeaf
    {sigma inputLoss delta outputLoss : ℝ}
    {normalizationExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent) where
  stickyLoss : ℝ
  eta : ℝ
  theoremEta : ℝ
  extraLoss : ℝ
  owner : PureWZ2ReentrantTerminalOwnerCall current stickyLoss
  paperADBridge : PureWZ2PaperADBridgeStatement
  budget : PureWZ2TerminalChainBudget
    sigma inputLoss delta stickyLoss eta theoremEta outputLoss
  certificates : PureWZ2TerminalChainCertificates
    eta theoremEta outputLoss owner.toTerminalScaleStickyData
  extraCost :
    ∀ {terminalSource : PureWZ2TerminalPreparedSource
          current.grain owner.toTerminalScaleStickyData}
      {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
      {window : PureWZ2TerminalWindow prepared}
      (chain : PureWZ2TerminalWindowChainOutput
        (eta := eta) (theoremEta := theoremEta)
        (outputLoss := outputLoss) window),
      (chain.preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow delta (-extraLoss)
  input_loss_le : inputLoss ≤ outputLoss
  finalAbsorption :
    ∀ {terminalSource : PureWZ2TerminalPreparedSource
          current.grain owner.toTerminalScaleStickyData}
      (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
      {good : PureWZ2TerminalExactGoodBlockFamilyData
        (eta := eta) (theoremEta := theoremEta)
        (outputLoss := outputLoss) prepared}
      (_data : PureWZ2TerminalExactBlockFamilyData good),
      64 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
          pureWZ2TerminalExactHeightRetentionCost delta good.extraLoss *
          Kakeya.realRpowENN delta (sigma + outputLoss) ≤
        MeasureTheory.volume prepared.shadow.union *
          owner.toTerminalScaleStickyData.sticky.balanced.cellMass *
            pureWZ2TerminalExactRichFloor delta outputLoss

namespace PureWZ2ReentrantTerminalLiftedLeaf

variable
    {sigma inputLoss delta outputLoss : ℝ}
    {normalizationExponent : ℕ}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}

/-- Execute the complete lifted multi-window assembly on the literal current
grain source. -/
theorem exactTerminal_nonempty
    (leaf : PureWZ2ReentrantTerminalLiftedLeaf
      (outputLoss := outputLoss) current) :
    Nonempty (PureWZ2ExactTerminalLevelData current.grain outputLoss) :=
  leaf.owner.toTerminalScaleStickyData.toLiftedExactTerminalLevelOfBudgets
    leaf.paperADBridge leaf.budget leaf.certificates leaf.extraCost
    leaf.input_loss_le leaf.finalAbsorption

/-- Package the same result in the final-source interface of the reentrant
prefix. -/
theorem exactTerminalOutput_nonempty
    (leaf : PureWZ2ReentrantTerminalLiftedLeaf
      (outputLoss := outputLoss) current) :
    Nonempty
      (PureWZ2ReentrantPrefixChain.ExactTerminalOutput current outputLoss) := by
  rcases leaf.exactTerminal_nonempty with ⟨terminal⟩
  exact ⟨{ terminal := terminal }⟩

end PureWZ2ReentrantTerminalLiftedLeaf

/-- Uniform, quantifier-ordered form of the sole remaining dependent terminal
leaf.  Both thresholds are selected before the runtime reentrant source. -/
def PureWZ2ReentrantTerminalLiftedLeafAt
    (sigma : ℝ) (normalizationExponent : ℕ) : Prop :=
  ∀ outputLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < outputLoss →
      ∃ sourceLossCeiling delta₀ : ℝ,
        0 < sourceLossCeiling ∧
        sourceLossCeiling ≤ outputLoss / 100 ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ inputLoss : ℝ,
          0 < inputLoss → inputLoss ≤ sourceLossCeiling →
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ current : PureWZ2ReentrantGrainSource
                sigma inputLoss delta normalizationExponent,
              Nonempty
                (PureWZ2ReentrantTerminalLiftedLeaf
                  (outputLoss := outputLoss) current)

/-- The explicit lifted leaf implies the exact terminal statement required by
the reentrant prefix.  This closes every final selection and record-packaging
step without changing the runtime source. -/
theorem pureWZ2_reentrantExactTerminalScaleAt_of_liftedLeaf
    {sigma : ℝ} {normalizationExponent : ℕ}
    (leaf : PureWZ2ReentrantTerminalLiftedLeafAt
      sigma normalizationExponent) :
    PureWZ2ReentrantExactTerminalScaleAtStatement
      sigma normalizationExponent := by
  intro outputLoss hsigma hsigmaOne houtputLoss
  rcases leaf outputLoss hsigma hsigmaOne houtputLoss with
    ⟨sourceLossCeiling, delta₀, hsourceLossCeiling,
      hsourceLossCeilingLe, hdelta₀, hdelta₀One, produce⟩
  refine ⟨sourceLossCeiling, delta₀, hsourceLossCeiling,
    hsourceLossCeilingLe, hdelta₀, hdelta₀One, ?_⟩
  intro inputLoss hinputLoss hinputLossLe delta hdelta hdeltaLe current
  rcases produce inputLoss hinputLoss hinputLossLe delta hdelta hdeltaLe
      current with ⟨terminalLeaf⟩
  exact terminalLeaf.exactTerminal_nonempty

end Kakeya.Assouad

end
