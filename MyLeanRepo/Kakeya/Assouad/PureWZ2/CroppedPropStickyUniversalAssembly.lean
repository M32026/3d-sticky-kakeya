import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerUniversalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationTopLevelAssembly

/-!
# Universal cropped prop-sticky assembly

This module packages every dependent object consumed by the same-family
owner assembly at one normalized source and one requested caller scale.
The resulting leaf has exactly the quantifier order of
`PureWZ2CroppedPropStickyAt`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2CroppedPropStickyUniversalInput
    {delta sigma sourceLoss normalizationLoss outputLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent)
    (callerRequested : WZ2PaperRequestedScale delta)
    (logExponent : ℕ) where
  ambientConstant : ENNReal
  fiberConstant : ENNReal
  coarseConstant : ENNReal
  outputConstant : ENNReal
  actualRequested : WZ2PaperRequestedScale delta
  actualNearby :
    WZ2PaperPureNearbyScaleCoverData
      normalized.croppedFamily actualRequested ambientConstant
  quotient :
    PureWZ2ParentQuotientNetSelectionData
      actualNearby callerRequested normalized.croppedRefined
  support : PureWZ2PositiveCallerSupportData quotient
  coordinateCount : ℕ
  regularized :
    PureWZ2AllPositiveCallerRegularizationData
      (outputConstant := fiberConstant)
      actualNearby quotient support coordinateCount
  merged :
    PureWZ2MergedCallerClassRegularizationData
      actualNearby quotient support coordinateCount regularized
  scales : Fin coordinateCount → WZ2PaperRequestedScale delta
  scheduled :
    ∀ coordinate,
      WZ2PaperPureNearbyScaleCoverData
        normalized.croppedFamily
        (scales coordinate) ambientConstant
  sameFamily :
    PureWZ2SameFamilyCallerNearbyAssemblyData
      (coarseConstant := coarseConstant)
      actualNearby quotient support coordinateCount regularized merged
      scales scheduled
  scaleSeparation : 18 * delta ≤ callerRequested.1
  fixedBalancing :
    PureWZ2SameFamilyFixedOriginBalancingData
      actualNearby quotient support coordinateCount regularized merged
      scales scheduled sameFamily scaleSeparation
  owner :
    WZ2PaperDirectOwnerPreparationData
      fixedBalancing.balanced.finalData.producer
  data :
    WZ2PaperOwnerParentSelectedData owner outputConstant
  floorLoss : ℝ
  strongLoss : ℝ
  witness :
    WZ2PaperOwnerParentSelectedData.SameFamilyOwnerUniversalWitness
      (outputLoss := outputLoss)
      normalized actualNearby quotient support coordinateCount
      regularized merged scales scheduled sameFamily scaleSeparation
      fixedBalancing owner data logExponent floorLoss strongLoss

namespace PureWZ2CroppedPropStickyUniversalInput

theorem output
    {delta sigma sourceLoss normalizationLoss outputLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent logExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (input :
      PureWZ2CroppedPropStickyUniversalInput
        (outputLoss := outputLoss)
        normalized callerRequested logExponent) :
    Nonempty
      (PureWZ2PropStickyData
        (sigma := sigma) (outputLoss := outputLoss)
        normalized.croppedRefined callerRequested logExponent) :=
  WZ2PaperOwnerParentSelectedData.sameFamilyOwnerUniversalAssembly
    (outputLoss := outputLoss)
    normalized input.actualNearby input.quotient input.support
    input.coordinateCount input.regularized input.merged
    input.scales input.scheduled input.sameFamily
    input.scaleSeparation input.fixedBalancing input.owner input.data
    logExponent input.witness

end PureWZ2CroppedPropStickyUniversalInput

def PureWZ2CroppedPropStickyUniversalLeafAt
    (normalizationExponent logExponent : ℕ) : Prop :=
  ∀ sigma : ℝ,
    ∀ critical : PureWZ2CriticalPackage sigma,
    ∀ outputLoss : ℝ, 0 < outputLoss →
      ∃ sourceLoss normalizationLoss delta₀ : ℝ,
        0 < sourceLoss ∧
        0 < normalizationLoss ∧
        sourceLoss ≤ normalizationLoss / 2 ∧
        normalizationLoss < outputLoss ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ source :
              PureWZ2ExtremalConfiguration
                sigma sourceLoss delta,
            ∀ normalized :
                PureWZ2CroppedCriticalNormalizationData
                  (outputLoss := normalizationLoss)
                  source normalizationExponent,
                ∀ rho : WZ2PaperRequestedScale delta,
                  Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                  rho.1 ≤ Real.rpow delta outputLoss →
                    Nonempty
                      (PureWZ2CroppedPropStickyUniversalInput
                        (outputLoss := outputLoss)
                        normalized rho logExponent)

theorem pureWZ2_cropped_prop_sticky_of_universal_leaf
    (normalizationExponent logExponent : ℕ)
    (leaf :
      PureWZ2CroppedPropStickyUniversalLeafAt
        normalizationExponent logExponent) :
    PureWZ2CroppedPropStickyAt
      normalizationExponent logExponent := by
  intro sigma critical outputLoss outputLossPos
  rcases
      leaf sigma critical outputLoss outputLossPos
    with
    ⟨sourceLoss, normalizationLoss, delta₀,
      sourceLossPos, normalizationLossPos, sourceLossLeHalf,
      normalizationLossLt,
      delta₀Pos, delta₀One, produce⟩
  refine
    ⟨sourceLoss, normalizationLoss, delta₀,
      sourceLossPos, normalizationLossPos, sourceLossLeHalf,
      normalizationLossLt,
      delta₀Pos, delta₀One, ?_⟩
  intro delta deltaPos deltaSmall source normalized rho
    rhoLower rhoUpper
  rcases
      produce delta deltaPos deltaSmall source normalized rho
        rhoLower rhoUpper
    with
    ⟨input⟩
  exact input.output

theorem pureWZ2_prop_sticky_from_critical_of_leaves
    (normalizationExponent logExponent : ℕ)
    (normalization :
      PureWZ2CroppedCriticalNormalizationAt normalizationExponent)
    (croppedLeaf :
      PureWZ2CroppedPropStickyUniversalLeafAt
        normalizationExponent logExponent)
    (realization :
      PureWZ2PropStickyRealizationAt
        normalizationExponent logExponent) :
    PureWZ2PropStickyFromCriticalStatement :=
  ⟨normalizationExponent, logExponent, normalization,
    pureWZ2_cropped_prop_sticky_of_universal_leaf
      normalizationExponent logExponent croppedLeaf,
    realization⟩

theorem pureWZ2_prop_sticky_of_leaves
    (normalizationExponent logExponent : ℕ)
    (normalization :
      PureWZ2CroppedCriticalNormalizationAt normalizationExponent)
    (croppedLeaf :
      PureWZ2CroppedPropStickyUniversalLeafAt
        normalizationExponent logExponent)
    (realization :
      PureWZ2PropStickyRealizationAt
        normalizationExponent logExponent) :
    PureWZ2PropStickyLegacyStatement := by
  intro _subunit _criticalExtraction
  exact
    pureWZ2_prop_sticky_from_critical_of_leaves
      normalizationExponent logExponent
      normalization croppedLeaf realization

theorem pureWZ2_prop_sticky_of_derived_normalization_and_cropped_leaf
    (normalizationExponent logExponent : ℕ)
    (normalizationLeaf :
      PureWZ2CroppedCriticalNormalizationSourceDerivedLeafAt
        normalizationExponent)
    (croppedLeaf :
      PureWZ2CroppedPropStickyUniversalLeafAt
        normalizationExponent logExponent)
    (realization :
      PureWZ2PropStickyRealizationAt
        normalizationExponent logExponent) :
    PureWZ2PropStickyLegacyStatement :=
  pureWZ2_prop_sticky_of_leaves
    normalizationExponent logExponent
    (pureWZ2_cropped_critical_normalization_of_sourceDerivedLeaf
      normalizationExponent normalizationLeaf)
    croppedLeaf realization

end Kakeya.Assouad

end
