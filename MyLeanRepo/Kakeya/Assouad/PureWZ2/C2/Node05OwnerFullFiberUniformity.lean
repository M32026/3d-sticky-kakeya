import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerReentryCompanion
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerExactMultiplicity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ExactMultiplicityRefinement

/-!
# Full-fiber uniformity adapter for the deterministic owner output

The owner premise is stated directly on the final selected fine and packed
coarse families.  Both families are retained definitionally by the re-entry
companion, and the exact-multiplicity refinement uses the identity fine
subfamily.  Hence the premise is exactly the full-fiber uniformity input used
by the concrete Node 5 call.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Transport owner full-fiber uniformity through deterministic re-entry and
the identity-family exact-multiplicity refinement. -/
theorem pureWZ2Node05Owner_fullFiberUniformity
    {delta sigma sourceLoss normalizationLoss seedLoss outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent seedLogExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (input : PureWZ2CroppedPropStickyUniversalInput
      (outputLoss := seedLoss) normalized callerRequested seedLogExponent)
    (companion : PureWZ2Node05OwnerReentryCompanion input)
    (fineExponent : ℕ)
    (refinementScalar :
      2 * wz1PaperRefinementFraction delta fineExponent ≤ 1)
    (ownerUniform :
      ∀ first second : Fin input.data.selectedPacked.family.card,
        ((wz2PaperFullFiberIndices
            input.data.selectedFine.family
            input.data.selectedPacked.family first).card : ENNReal) ≤
          Kakeya.realRpowENN callerRequested.1 (-outputLoss) *
            ((wz2PaperFullFiberIndices
              input.data.selectedFine.family
              input.data.selectedPacked.family second).card : ENNReal)) :
    ∀ first second : Fin companion.toReentrant.data.coarse.card,
      ((wz2PaperFullFiberIndices
          (companion.toReentrant.data.selected.comp
            (input.data.toExactMultiplicityData.truncation.toPaperRefinement
              fineExponent refinementScalar).selected).family
          companion.toReentrant.data.coarse first).card : ENNReal) ≤
        Kakeya.realRpowENN callerRequested.1 (-outputLoss) *
          ((wz2PaperFullFiberIndices
            (companion.toReentrant.data.selected.comp
              (input.data.toExactMultiplicityData.truncation.toPaperRefinement
                fineExponent refinementScalar).selected).family
            companion.toReentrant.data.coarse second).card : ENNReal) := by
  exact ownerUniform

end Kakeya.Assouad

end
