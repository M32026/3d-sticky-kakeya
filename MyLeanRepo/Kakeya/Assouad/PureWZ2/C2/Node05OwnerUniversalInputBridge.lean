import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedPropStickyUniversalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerCriticalExactImageBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerUniversalWitnessProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PreselectedPostDeletionUniversalInputAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GenericOwnerSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GenericOwnerPropSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropStickyReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05GenericOwnerExactInput

/-!
# Node 5 actual-owner universal-input bridge

This module packages the existing uniform scalar thresholds, the remaining
actual-owner quantitative receipt, and the per-parent rescaling receipts into
the universal owner witness.  It then applies that package to the exact
normalized source and caller scale stored in a post-deletion input.

The positive-deletion field is intentionally not consumed: the post-deletion
record is the shortest existing constructor of the same-family data used by
the actual owner selection.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Deterministic direct-owner preparation attached to the corrected
selected-caller balancing output. -/
noncomputable def pureWZ2PreselectedDirectOwner
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (post :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent) :
    WZ2PaperDirectOwnerPreparationData
      post.post.balanced.finalData.producer :=
  Classical.choice <|
    wz2_paper_direct_owner_preparation
      post.post.balanced.finalData.producer

/-- Layer-2 selected-owner prefix.  This is the exact point where the generic
owner-parent selector must be applied to the selected balancing producer.
No all-positive family or legacy same-family package occurs in its type. -/
structure PureWZ2PreselectedCanonicalOwnerPrefix
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (post :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent) where
  outputConstant : ENNReal
  owner :
    WZ2PaperDirectOwnerPreparationData
      post.post.balanced.finalData.producer
  owner_eq : owner = pureWZ2PreselectedDirectOwner post
  data : PureWZ2GenericOwnerSelectedData owner outputConstant
  source_mass_ledger :
    normalized.croppedRefined.mass ≤
      (((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          post.preselection.retentionConstant) *
        pureWZ2CompleteParentRegularizationLoss
          post.actualNearby.scaleData.coarse.card post.coordinateCount) *
        post.sameFamily.selectedFineShading.mass
  local_fiber_constant :
    post.fiberConstant =
      post.preselection.localFiberConstant
        post.localFiberR post.localFiberWeightUpper

/-- Construct the selected Layer-2 prefix from the actual balanced producer.
The only scalar premise is the restriction constant evaluated at the exact
weighted-regularizer formulas and the exact retained-parent cardinality. -/
theorem pureWZ2_preselected_canonical_owner_prefix
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (post :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent)
    (epsilon : ℝ)
    (epsilon_pos : 0 < epsilon)
    (caller_lt_one : callerRequested.1 < 1)
    (outputConstant : ENNReal)
    (output_ne_top : outputConstant ≠ ⊤)
    (rounding_absorption :
      ENNReal.ofReal (Real.rpow callerRequested.1 (-epsilon)) *
          post.coarseConstant ≤
        outputConstant)
    (restriction_absorption :
      wz2PaperPureNearbyRestrictionConstant
          post.coarseConstant
          ((pureWZ2PreselectedDirectOwner post).exactified.refined.mass /
            post.preselection.selected.family.enncard)
          (pureWZ2WeightedDegreeConstant epsilon
            (WZ2PaperPureTubeSubfamily.ofTubeSubfamily
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                post.preselection.selected.family
                (pureWZ2PreselectedDirectOwner
                  post).exactified.retainedParents)).family.card)
          (pureWZ2WeightedRegularizationLoss epsilon
              (WZ2PaperPureTubeSubfamily.ofTubeSubfamily
                (Kakeya.Streamlined.TubeSubfamily.fromFinset
                  post.preselection.selected.family
                  (pureWZ2PreselectedDirectOwner
                    post).exactified.retainedParents)).family.card *
            (pureWZ2PreselectedDirectOwner
              post).exactified.refined.mass) ≤
        outputConstant) :
    Nonempty (PureWZ2PreselectedCanonicalOwnerPrefix post) := by
  let owner := pureWZ2PreselectedDirectOwner post
  rcases
      pureWZ2_generic_owner_selection owner
        post.sameFamily.coarse_pure_cwa epsilon epsilon_pos
        caller_lt_one output_ne_top rounding_absorption
        (by
          simpa [owner] using restriction_absorption)
    with
    ⟨data⟩
  exact
    ⟨{
      outputConstant := outputConstant
      owner := owner
      owner_eq := rfl
      data := data
      source_mass_ledger :=
        post.sameFamily.source_mass_retention
      local_fiber_constant := post.fiberConstant_eq
    }⟩

/-- Exact selected-caller universal owner input.  Unlike the legacy input,
this stores only the generic owner output and its geometric/scalar leaves;
there is no cast back to the all-positive caller assembly. -/
structure PureWZ2PreselectedPropStickyUniversalInput
    {delta sigma sourceLoss normalizationLoss outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent logExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (post :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent)
    (ownerPrefix : PureWZ2PreselectedCanonicalOwnerPrefix post) where
  leaves :
    ownerPrefix.data.PropStickyLeaves
      (sigma := sigma) (outputLoss := outputLoss)
      (source := normalized.croppedFamily)
      (sourceShading := normalized.croppedRefined)
      logExponent
  retentionConstant : ENNReal
  retentionConstant_eq :
    retentionConstant = post.preselection.retentionConstant
  localFiberConstant : ENNReal
  localFiberConstant_eq :
    localFiberConstant =
      post.preselection.localFiberConstant
        post.localFiberR post.localFiberWeightUpper
  fiberConstant_eq : post.fiberConstant = localFiberConstant

namespace PureWZ2PreselectedPropStickyUniversalInput

/-- Deterministic frozen Node-3 data produced by the selected generic owner
path. -/
noncomputable def deterministicData
    {delta sigma sourceLoss normalizationLoss outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent logExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    {post :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent}
    {ownerPrefix : PureWZ2PreselectedCanonicalOwnerPrefix post}
    (input : PureWZ2PreselectedPropStickyUniversalInput
      (outputLoss := outputLoss) (logExponent := logExponent)
      post ownerPrefix) :
    PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      normalized.croppedRefined callerRequested logExponent :=
  input.leaves.assemble

theorem output
    {delta sigma sourceLoss normalizationLoss outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent logExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    {post :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent}
    {ownerPrefix : PureWZ2PreselectedCanonicalOwnerPrefix post}
    (input : PureWZ2PreselectedPropStickyUniversalInput
      (outputLoss := outputLoss) (logExponent := logExponent)
      post ownerPrefix) :
    Nonempty
      (PureWZ2PropStickyData
        (sigma := sigma) (outputLoss := outputLoss)
        normalized.croppedRefined callerRequested logExponent) :=
  ⟨input.deterministicData⟩

end PureWZ2PreselectedPropStickyUniversalInput

/-- Exact coarse re-entry companion for the selected deterministic output.
This mirrors the legacy receipt without mentioning its old universal-input
type. -/
structure PureWZ2PreselectedOwnerReentryCompanion
    {delta sigma sourceLoss normalizationLoss seedLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent seedLogExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    {post :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent}
    {ownerPrefix : PureWZ2PreselectedCanonicalOwnerPrefix post}
    (input : PureWZ2PreselectedPropStickyUniversalInput
      (outputLoss := seedLoss) (logExponent := seedLogExponent)
      post ownerPrefix) where
  coarseSourceLoss : ℝ
  coarseNormalizationLoss : ℝ
  coarseSourceLoss_pos : 0 < coarseSourceLoss
  coarseNormalizationLoss_pos : 0 < coarseNormalizationLoss
  coarseSourceLoss_budget : 3 * coarseSourceLoss ≤ seedLoss
  coarseNormalizationLoss_eq :
    coarseNormalizationLoss = (7 / 2 : ℝ) * coarseSourceLoss
  coarseReentry :
    PureWZ2PropStickyReentryData
      (sigma := sigma) input.deterministicData.croppedCoarseShading
      normalizationExponent coarseSourceLoss coarseNormalizationLoss

namespace PureWZ2PreselectedOwnerReentryCompanion

noncomputable def toReentrant
    {delta sigma sourceLoss normalizationLoss seedLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent seedLogExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    {post :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent}
    {ownerPrefix : PureWZ2PreselectedCanonicalOwnerPrefix post}
    {input : PureWZ2PreselectedPropStickyUniversalInput
      (outputLoss := seedLoss) (logExponent := seedLogExponent)
      post ownerPrefix}
    (companion : PureWZ2PreselectedOwnerReentryCompanion input) :
    PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      normalized.croppedRefined callerRequested normalizationExponent
      seedLogExponent where
  data := input.deterministicData
  coarseSourceLoss := companion.coarseSourceLoss
  coarseNormalizationLoss := companion.coarseNormalizationLoss
  coarseSourceLoss_pos := companion.coarseSourceLoss_pos
  coarseNormalizationLoss_pos := companion.coarseNormalizationLoss_pos
  coarseSourceLoss_budget := companion.coarseSourceLoss_budget
  coarseNormalizationLoss_eq := companion.coarseNormalizationLoss_eq
  coarseReentry := companion.coarseReentry

/-- Exact multiplicity truncation and whole-cell nesting constructed directly
from the same selected generic owner datum used by `deterministicData`. -/
noncomputable def deterministicExactInput
    {delta sigma sourceLoss normalizationLoss seedLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent seedLogExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    {post :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent}
    {ownerPrefix : PureWZ2PreselectedCanonicalOwnerPrefix post}
    {input : PureWZ2PreselectedPropStickyUniversalInput
      (outputLoss := seedLoss) (logExponent := seedLogExponent)
      post ownerPrefix}
    (companion : PureWZ2PreselectedOwnerReentryCompanion input)
    (hdelta : 0 < delta) :
    PureWZ2Node05DeterministicExactInput companion.toReentrant hdelta := by
  let m : ℕ :=
    2 ^ post.post.balanced.finalData.producer.fiberBand.level
  have hm : 0 < m := by positivity
  let truncation :=
    pureWZ2Node05_exactMultiplicityTruncation
      companion.toReentrant.data.refined hdelta
      input.leaves.final_fine_cubical m hm
      (by
        simpa [m, PureWZ2PreselectedPropStickyUniversalInput.deterministicData,
          PureWZ2PreselectedOwnerReentryCompanion.toReentrant,
          PureWZ2GenericOwnerSelectedData.PropStickyLeaves.assemble] using
          ownerPrefix.data.finalFineShading_constantMultiplicity
            input.leaves.fine_line input.leaves.coarse_line
            input.leaves.coarse_distinct)
  exact
    { m := m
      m_pos := hm
      truncation := truncation
      fineCellNested := by
        simpa [PureWZ2PreselectedPropStickyUniversalInput.deterministicData,
          PureWZ2PreselectedOwnerReentryCompanion.toReentrant,
          PureWZ2GenericOwnerSelectedData.PropStickyLeaves.assemble] using
          ownerPrefix.data.fineCellNested input.leaves.fine_line
            input.leaves.coarse_line input.leaves.coarse_distinct }

/-- Selected-caller deterministic density refresh.  The parentwise factor-two
mass retention is proved from the generic owner construction; only the
quantitative density inequality remains as a scalar premise. -/
noncomputable def deterministicDensity
    {delta sigma sourceLoss normalizationLoss seedLoss outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent seedLogExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    {post :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent}
    {ownerPrefix : PureWZ2PreselectedCanonicalOwnerPrefix post}
    {input : PureWZ2PreselectedPropStickyUniversalInput
      (outputLoss := seedLoss) (logExponent := seedLogExponent)
      post ownerPrefix}
    (companion : PureWZ2PreselectedOwnerReentryCompanion input)
    (hdelta : 0 < delta)
    (seed_le_output : seedLoss ≤ outputLoss)
    (ratioSmall : delta / callerRequested.1 ≤ 1 / 24)
    (densityAbsorption :
      ∀ parent : Fin companion.toReentrant.data.coarse.card,
        Kakeya.realRpowENN (delta / callerRequested.1) outputLoss *
              (55296 * Kakeya.deltaTubeVolume 1) ≤
          ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            (((restrictPaperShading
                  (Kakeya.Streamlined.TubeSubfamily.fromFinset
                    companion.toReentrant.data.selected.family
                    (wz2PaperFullFiberIndices
                      companion.toReentrant.data.selected.family
                      companion.toReentrant.data.coarse parent))
                  companion.toReentrant.data.refined).mass / 2) /
              ((Kakeya.Streamlined.TubeSubfamily.fromFinset
                companion.toReentrant.data.selected.family
                (wz2PaperFullFiberIndices
                  companion.toReentrant.data.selected.family
                  companion.toReentrant.data.coarse parent)).family.enncard *
                Kakeya.realRpowENN delta 2))) :
    PureWZ2Node05DeterministicDensityReceipt
      (outputLoss := outputLoss) companion.toReentrant
      (companion.deterministicExactInput hdelta) := by
  apply pureWZ2Node05Deterministic_density companion.toReentrant
    (companion.deterministicExactInput hdelta) seed_le_output ratioSmall
  · intro parent
    have retained :=
      ownerPrefix.data.exact_restrict_fullFiber_mass_retention
        input.leaves.fine_line input.leaves.coarse_line
        input.leaves.coarse_distinct
        (companion.deterministicExactInput hdelta).m
        (companion.deterministicExactInput hdelta).m_pos
        (by
          simp [PureWZ2PreselectedOwnerReentryCompanion.deterministicExactInput])
        (companion.deterministicExactInput hdelta).truncation parent
    simpa [PureWZ2PreselectedOwnerReentryCompanion.toReentrant,
      PureWZ2PreselectedPropStickyUniversalInput.deterministicData,
      PureWZ2GenericOwnerSelectedData.PropStickyLeaves.assemble,
      PureWZ2GenericOwnerSelectedData.internalCover,
      WZ2PaperPartitioningCover.fullFiberSubfamily,
      wz2PaperFullFiberSubfamily] using retained
  · exact densityAbsorption

end PureWZ2PreselectedOwnerReentryCompanion

/-- Selected-caller Node 5 receipt.  Its deterministic seed and coarse
re-entry are definitionally the two projections of the same selected input
and companion. -/
structure PureWZ2PreselectedNode05OwnerCallReceipt
    {delta sigma sourceLoss normalizationLoss seedLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent seedLogExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    {post :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent}
    {ownerPrefix : PureWZ2PreselectedCanonicalOwnerPrefix post}
    (input : PureWZ2PreselectedPropStickyUniversalInput
      (outputLoss := seedLoss) (logExponent := seedLogExponent)
      post ownerPrefix)
    (companion : PureWZ2PreselectedOwnerReentryCompanion input)
    (outputLoss : ℝ) (outputLogExponent : ℕ) where
  call :
    PureWZ2Node05DeterministicOwnerCallReceipt companion.toReentrant
      outputLoss outputLogExponent

namespace PureWZ2PreselectedNode05OwnerCallReceipt

noncomputable def output
    {delta sigma sourceLoss normalizationLoss seedLoss outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent seedLogExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    {post :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent}
    {ownerPrefix : PureWZ2PreselectedCanonicalOwnerPrefix post}
    {input : PureWZ2PreselectedPropStickyUniversalInput
      (outputLoss := seedLoss) (logExponent := seedLogExponent)
      post ownerPrefix}
    {companion : PureWZ2PreselectedOwnerReentryCompanion input}
    {outputLogExponent : ℕ}
    (receipt : PureWZ2PreselectedNode05OwnerCallReceipt
      input companion outputLoss outputLogExponent) :
    PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      normalized.croppedRefined callerRequested normalizationExponent
      seedLogExponent outputLogExponent :=
  receipt.call.output

theorem retentionConstant_eq
    {delta sigma sourceLoss normalizationLoss seedLoss outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent seedLogExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    {post :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent}
    {ownerPrefix : PureWZ2PreselectedCanonicalOwnerPrefix post}
    {input : PureWZ2PreselectedPropStickyUniversalInput
      (outputLoss := seedLoss) (logExponent := seedLogExponent)
      post ownerPrefix}
    {companion : PureWZ2PreselectedOwnerReentryCompanion input}
    {outputLogExponent : ℕ}
    (_receipt : PureWZ2PreselectedNode05OwnerCallReceipt
      input companion outputLoss outputLogExponent) :
    input.retentionConstant = post.preselection.retentionConstant :=
  input.retentionConstant_eq

theorem fiberConstant_eq_localFiberConstant
    {delta sigma sourceLoss normalizationLoss seedLoss outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent seedLogExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    {post :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent}
    {ownerPrefix : PureWZ2PreselectedCanonicalOwnerPrefix post}
    {input : PureWZ2PreselectedPropStickyUniversalInput
      (outputLoss := seedLoss) (logExponent := seedLogExponent)
      post ownerPrefix}
    {companion : PureWZ2PreselectedOwnerReentryCompanion input}
    {outputLogExponent : ℕ}
    (_receipt : PureWZ2PreselectedNode05OwnerCallReceipt
      input companion outputLoss outputLogExponent) :
    post.fiberConstant =
      post.preselection.localFiberConstant
        post.localFiberR post.localFiberWeightUpper := by
  rw [input.fiberConstant_eq, input.localFiberConstant_eq]

end PureWZ2PreselectedNode05OwnerCallReceipt

namespace WZ2PaperOwnerParentSelectedData

/-- Assemble the universal owner witness from the two scalar receipts and the
exact bounded-normalization witness on every selected final fiber. -/
noncomputable def sameFamilyOwnerUniversalWitness_of_actual
    {delta sigma sourceLoss normalizationLoss outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent)
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby : WZ2PaperPureNearbyScaleCoverData
      normalized.croppedFamily actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    (quotient : PureWZ2ParentQuotientNetSelectionData
      actualNearby callerRequested normalized.croppedRefined)
    (support : PureWZ2PositiveCallerSupportData quotient)
    (coordinateCount : ℕ)
    (regularized : PureWZ2AllPositiveCallerRegularizationData
      (outputConstant := fiberConstant)
      actualNearby quotient support coordinateCount)
    (merged : PureWZ2MergedCallerClassRegularizationData
      actualNearby quotient support coordinateCount regularized)
    (scales : Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled : ∀ coordinate, WZ2PaperPureNearbyScaleCoverData
      normalized.croppedFamily (scales coordinate) ambientConstant)
    (sameFamily : PureWZ2SameFamilyCallerNearbyAssemblyData
      (coarseConstant := coarseConstant)
      actualNearby quotient support coordinateCount regularized merged
      scales scheduled)
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (balancing : PureWZ2SameFamilyFixedOriginBalancingData
      actualNearby quotient support coordinateCount regularized merged
      scales scheduled sameFamily scaleSeparation)
    (epsilon : ℝ)
    (data : WZ2PaperOwnerParentSelectedData
      (pureWZ2SameFamilyDirectOwner balancing)
      (pureWZ2SameFamilyOwnerActualOutputConstant
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing epsilon))
    (logExponent : ℕ)
    (thresholds : SameFamilyOwnerUniformScalarThresholds sigma outputLoss)
    (sigma_pos : 0 < sigma)
    (delta_pos : 0 < delta)
    (delta_small : delta ≤ thresholds.delta₀)
    (rho_lower : Real.rpow delta (1 - outputLoss) ≤ callerRequested.1)
    (rho_upper : callerRequested.1 ≤ Real.rpow delta outputLoss)
    (remaining : SameFamilyOwnerActualRemainingQuantitative
      (sigma := sigma) (outputLoss := outputLoss)
      actualNearby quotient support coordinateCount regularized merged
      scales scheduled sameFamily scaleSeparation balancing epsilon data
      logExponent)
    (geometry : ∀ parent : Fin data.selectedPacked.family.card,
      FinalFiberRescalingGeometry data parent)
    (absorptions : ∀ parent : Fin data.selectedPacked.family.card,
      FinalFiberRescalingScalarAbsorptions
        (sigma := sigma)
        (outputLoss := thresholds.critical.structuralLoss)
        data parent
        ((thresholds.caller_scalars delta_pos delta_small
          (delta_pos.trans_le callerRequested.2.1)
          rho_lower rho_upper).2.2.2.1)) :
    SameFamilyOwnerUniversalWitness
      (outputLoss := outputLoss) normalized actualNearby quotient support
      coordinateCount regularized merged scales scheduled sameFamily
      scaleSeparation balancing (pureWZ2SameFamilyDirectOwner balancing)
      data logExponent thresholds.hierarchy.floorLoss
      thresholds.hierarchy.strongLoss := by
  have scalars := thresholds.caller_scalars delta_pos delta_small
    (delta_pos.trans_le callerRequested.2.1) rho_lower rho_upper
  refine {
    retention_absorption := remaining.retention_absorption
    coarse_cwa_absorption := remaining.coarse_cwa_absorption
    rho_small := scalars.1
    coarse_density_absorption := remaining.coarse_density_absorption
    coarse_volume_scalar := remaining.coarse_volume_scalar
    final_multiplicity := ?_
  }
  refine {
    rho_le_one := callerRequested.2.2
    sigma_pos := sigma_pos
    strongLoss_pos := thresholds.hierarchy.strongLoss_pos
    loss_budget := thresholds.hierarchy.output_budget
    coarse_cardinality_absorption := by
      rw [thresholds.hierarchy.strongLoss_eq]
      exact remaining.coarse_cardinality_absorption
    ratio_pos := scalars.2.1
    ratio_le_one := scalars.2.2.1
    ratio_small := scalars.2.2.2.1
    critical := thresholds.critical
    ratio_critical := scalars.2.2.2.2.1
    floor_strong := thresholds.hierarchy.floor_strong
    multiplicity_absorption := scalars.2.2.2.2.2
    critical_rescaled := ?_
  }
  · intro parent
    let leaves := (geometry parent).toLeaves (absorptions parent)
    exact ⟨leaves.criticalRescaledWitness_of_bounded_normalization normalized⟩

end WZ2PaperOwnerParentSelectedData

/-- Receipts indexed by the exact data returned by the canonical actual owner
selection. -/
structure SameFamilyOwnerActualReceipts
    {delta sigma sourceLoss normalizationLoss outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent logExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (post : PureWZ2CroppedPostDeletionUniversalInput
      normalized callerRequested deletionExponent)
    (thresholds : SameFamilyOwnerUniformScalarThresholds sigma outputLoss)
    (delta_pos : 0 < delta)
    (delta_small : delta ≤ thresholds.delta₀)
    (rho_lower : Real.rpow delta (1 - outputLoss) ≤ callerRequested.1)
    (rho_upper : callerRequested.1 ≤ Real.rpow delta outputLoss)
    (data : WZ2PaperOwnerParentSelectedData
      (pureWZ2SameFamilyDirectOwner post.fixedBalancing)
      (pureWZ2SameFamilyOwnerActualOutputConstant post.actualNearby
        post.quotient post.support post.coordinateCount post.regularized
        post.merged post.scales post.scheduled post.sameFamily
        post.scaleSeparation post.fixedBalancing post.scheduleEpsilon)) : Prop where
  remaining : SameFamilyOwnerActualRemainingQuantitative
    (sigma := sigma) (outputLoss := outputLoss) post.actualNearby post.quotient
    post.support post.coordinateCount post.regularized post.merged post.scales
    post.scheduled post.sameFamily post.scaleSeparation post.fixedBalancing
    post.scheduleEpsilon data logExponent
  geometry : ∀ parent : Fin data.selectedPacked.family.card,
    WZ2PaperOwnerParentSelectedData.FinalFiberRescalingGeometry data parent
  absorptions : ∀ parent : Fin data.selectedPacked.family.card,
    WZ2PaperOwnerParentSelectedData.FinalFiberRescalingScalarAbsorptions
      (sigma := sigma) (outputLoss := thresholds.critical.structuralLoss)
      data parent
      ((thresholds.caller_scalars delta_pos delta_small
        (delta_pos.trans_le callerRequested.2.1) rho_lower rho_upper).2.2.2.1)

/--
The canonical actual-owner selection attached to one exact post-deletion
construction.  Naming this choice removes the need for downstream runtime
code to accept a callback over every possible owner selection.
-/
noncomputable def pureWZ2PostDeletionCanonicalActualOwnerData
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (post : PureWZ2CroppedPostDeletionUniversalInput
      normalized callerRequested deletionExponent) :
    WZ2PaperOwnerParentSelectedData
      (pureWZ2SameFamilyDirectOwner post.fixedBalancing)
      (pureWZ2SameFamilyOwnerActualOutputConstant post.actualNearby
        post.quotient post.support post.coordinateCount post.regularized
        post.merged post.scales post.scheduled post.sameFamily
        post.scaleSeparation post.fixedBalancing post.scheduleEpsilon) :=
  Classical.choice <|
    pureWZ2_same_family_owner_parent_selection_actual post.actualNearby
      post.quotient post.support post.coordinateCount post.regularized
      post.merged post.scales post.scheduled post.sameFamily
      post.scaleSeparation post.fixedBalancing post.scheduleEpsilon
      post.scheduleEpsilon_pos post.caller_lt_one

/--
Assemble the exact universal input from the single receipt indexed by the
canonical actual-owner selection.  This is the callback-free form used by the
terminal runtime.
-/
noncomputable def pureWZ2CroppedPropStickyUniversalInputOfCanonicalActual
    {delta sigma sourceLoss normalizationLoss outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent logExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (post : PureWZ2CroppedPostDeletionUniversalInput
      normalized callerRequested deletionExponent)
    (thresholds : SameFamilyOwnerUniformScalarThresholds sigma outputLoss)
    (sigma_pos : 0 < sigma)
    (delta_pos : 0 < delta)
    (delta_small : delta ≤ thresholds.delta₀)
    (rho_lower : Real.rpow delta (1 - outputLoss) ≤ callerRequested.1)
    (rho_upper : callerRequested.1 ≤ Real.rpow delta outputLoss)
    (receipt : SameFamilyOwnerActualReceipts (logExponent := logExponent)
      post thresholds delta_pos delta_small rho_lower rho_upper
        (pureWZ2PostDeletionCanonicalActualOwnerData post)) :
    PureWZ2CroppedPropStickyUniversalInput
      (outputLoss := outputLoss) normalized callerRequested logExponent := by
  let data := pureWZ2PostDeletionCanonicalActualOwnerData post
  let witness :=
    WZ2PaperOwnerParentSelectedData.sameFamilyOwnerUniversalWitness_of_actual
      normalized post.actualNearby post.quotient post.support
      post.coordinateCount post.regularized post.merged post.scales
      post.scheduled post.sameFamily post.scaleSeparation post.fixedBalancing
      post.scheduleEpsilon data logExponent thresholds sigma_pos delta_pos
      delta_small rho_lower rho_upper receipt.remaining receipt.geometry
      receipt.absorptions
  exact {
    ambientConstant := Kakeya.realRpowENN delta (-normalizationLoss)
    fiberConstant := post.fiberConstant
    coarseConstant := post.coarseConstant
    outputConstant := pureWZ2SameFamilyOwnerActualOutputConstant
      post.actualNearby post.quotient post.support post.coordinateCount
      post.regularized post.merged post.scales post.scheduled post.sameFamily
      post.scaleSeparation post.fixedBalancing post.scheduleEpsilon
    actualRequested := post.actualRequested
    actualNearby := post.actualNearby
    quotient := post.quotient
    support := post.support
    coordinateCount := post.coordinateCount
    regularized := post.regularized
    merged := post.merged
    scales := post.scales
    scheduled := post.scheduled
    sameFamily := post.sameFamily
    scaleSeparation := post.scaleSeparation
    fixedBalancing := post.fixedBalancing
    owner := pureWZ2SameFamilyDirectOwner post.fixedBalancing
    data := data
    floorLoss := thresholds.hierarchy.floorLoss
    strongLoss := thresholds.hierarchy.strongLoss
    witness := witness
  }

/--
Choose the canonical actual owner selection and package a universal input on
exactly the normalized source and requested scale carried by `post`.

`post.positiveDeletion` is intentionally unused: the actual owner selector is
indexed by the pre-deletion same-family output `post.fixedBalancing`.
-/
theorem pureWZ2_cropped_prop_sticky_universal_input_of_postDeletion
    {delta sigma sourceLoss normalizationLoss outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent logExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (post : PureWZ2CroppedPostDeletionUniversalInput
      normalized callerRequested deletionExponent)
    (thresholds : SameFamilyOwnerUniformScalarThresholds sigma outputLoss)
    (sigma_pos : 0 < sigma)
    (delta_pos : 0 < delta)
    (delta_small : delta ≤ thresholds.delta₀)
    (rho_lower : Real.rpow delta (1 - outputLoss) ≤ callerRequested.1)
    (rho_upper : callerRequested.1 ≤ Real.rpow delta outputLoss)
    (receipts : ∀ data : WZ2PaperOwnerParentSelectedData
      (pureWZ2SameFamilyDirectOwner post.fixedBalancing)
      (pureWZ2SameFamilyOwnerActualOutputConstant post.actualNearby
        post.quotient post.support post.coordinateCount post.regularized
        post.merged post.scales post.scheduled post.sameFamily
        post.scaleSeparation post.fixedBalancing post.scheduleEpsilon),
      Nonempty (SameFamilyOwnerActualReceipts (logExponent := logExponent)
        post thresholds delta_pos delta_small rho_lower rho_upper data)) :
    Nonempty (PureWZ2CroppedPropStickyUniversalInput
      (outputLoss := outputLoss) normalized callerRequested logExponent) := by
  rcases pureWZ2_same_family_owner_parent_selection_actual post.actualNearby
      post.quotient post.support post.coordinateCount post.regularized
      post.merged post.scales post.scheduled post.sameFamily
      post.scaleSeparation post.fixedBalancing post.scheduleEpsilon
      post.scheduleEpsilon_pos post.caller_lt_one with ⟨data⟩
  rcases receipts data with ⟨receipt⟩
  let witness :=
    WZ2PaperOwnerParentSelectedData.sameFamilyOwnerUniversalWitness_of_actual
      normalized post.actualNearby post.quotient post.support
      post.coordinateCount post.regularized post.merged post.scales
      post.scheduled post.sameFamily post.scaleSeparation post.fixedBalancing
      post.scheduleEpsilon data logExponent thresholds sigma_pos delta_pos
      delta_small rho_lower rho_upper receipt.remaining receipt.geometry
      receipt.absorptions
  exact ⟨{
    ambientConstant := Kakeya.realRpowENN delta (-normalizationLoss)
    fiberConstant := post.fiberConstant
    coarseConstant := post.coarseConstant
    outputConstant := pureWZ2SameFamilyOwnerActualOutputConstant
      post.actualNearby post.quotient post.support post.coordinateCount
      post.regularized post.merged post.scales post.scheduled post.sameFamily
      post.scaleSeparation post.fixedBalancing post.scheduleEpsilon
    actualRequested := post.actualRequested
    actualNearby := post.actualNearby
    quotient := post.quotient
    support := post.support
    coordinateCount := post.coordinateCount
    regularized := post.regularized
    merged := post.merged
    scales := post.scales
    scheduled := post.scheduled
    sameFamily := post.sameFamily
    scaleSeparation := post.scaleSeparation
    fixedBalancing := post.fixedBalancing
    owner := pureWZ2SameFamilyDirectOwner post.fixedBalancing
    data := data
    floorLoss := thresholds.hierarchy.floorLoss
    strongLoss := thresholds.hierarchy.strongLoss
    witness := witness
  }⟩

end Kakeya.Assouad

end
