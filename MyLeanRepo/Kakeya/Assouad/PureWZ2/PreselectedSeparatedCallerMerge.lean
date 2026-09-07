import MyLeanRepo.Kakeya.Assouad.PureWZ2.PreselectedSeparatedCallerClass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.MergedCallerClassRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyInternalPartitioningCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PostDeletionFixedBalancingInput
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFiberwiseRefinementMerge

/-!
# Merge source-separated selected caller fibers

The caller band is fixed before this module is used.  Each complete selected
caller fiber is first refined by the ordinary source-conflict selection and
its nearby CWA is rebuilt.  Only then are the fibers merged.  This is the
order required by the Proposition 6.4 rescaling step: essential distinctness
is a property of the genuine source fiber, not something inherited by an
arbitrary image family.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Transport a paper refinement across an exact finite reindexing of its
source family and shading. -/
noncomputable def WZ1PaperRefinement.reindexSource
    {delta : ℝ}
    {sourceFamily targetFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {targetShading : WZ1PaperTubeShading targetFamily}
    {logExponent : ℕ}
    (refinement : WZ1PaperRefinement sourceShading logExponent)
    (indexEquiv : Fin targetFamily.card ≃ Fin sourceFamily.card)
    (tube_eq : ∀ index,
      targetFamily.tube index = sourceFamily.tube (indexEquiv index))
    (carrier_eq : ∀ index,
      targetShading.carrier index = sourceShading.carrier (indexEquiv index)) :
    WZ1PaperRefinement targetShading logExponent := by
  let selectedEmbedding :
      Fin refinement.selected.family.card ↪ Fin targetFamily.card :=
    refinement.selected.embedding.trans indexEquiv.symm.toEmbedding
  let selected : Kakeya.Streamlined.TubeSubfamily targetFamily :=
    { family := refinement.selected.family
      embedding := selectedEmbedding
      tube_eq := fun index => by
        calc
          refinement.selected.family.tube index =
              sourceFamily.tube (refinement.selected.embedding index) :=
            refinement.selected.tube_eq index
          _ = targetFamily.tube (selectedEmbedding index) := by
            rw [tube_eq]
            simp [selectedEmbedding] }
  have mass_eq : targetShading.mass = sourceShading.mass := by
    let weight : Fin sourceFamily.card → ENNReal := fun index =>
      volume (sourceShading.carrier index)
    calc
      targetShading.mass =
          ∑ index : Fin targetFamily.card,
            volume (targetShading.carrier index) := rfl
      _ = ∑ index : Fin targetFamily.card, weight (indexEquiv index) := by
        apply Finset.sum_congr rfl
        intro index _
        exact congrArg volume (carrier_eq index)
      _ = ∑ index : Fin sourceFamily.card, weight index :=
        Equiv.sum_comp indexEquiv weight
      _ = sourceShading.mass := rfl
  exact
    { selected := selected
      refined := refinement.refined
      subshading := fun index => by
        have sourceSubset := refinement.subshading index
        have targetCarrier :
            targetShading.carrier (selectedEmbedding index) =
              sourceShading.carrier (refinement.selected.embedding index) := by
          simpa [selectedEmbedding] using carrier_eq (selectedEmbedding index)
        rw [targetCarrier]
        exact sourceSubset
      retained_mass := by
        rw [mass_eq]
        exact refinement.retained_mass }

/-- The genuine ordinary-separated local output for every caller retained by
the caller-weight preselection. -/
structure PureWZ2PreselectedSeparatedCallerRegularizationData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (coordinateCount : ℕ)
    {scales : Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    (preselection :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (regularized :
      PureWZ2PreselectedCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient coordinateCount preselection) where
  fiberData :
    ∀ parent : Fin preselection.selected.family.card,
      PureWZ2SeparatedCallerClassRegularizationData
        actualNearby quotient
        ((pureWZ2PostDeletionPositiveCallerBase quotient).embedding
          (preselection.selected.embedding parent))
        coordinateCount (regularized.fiberData parent)

namespace PureWZ2PreselectedSeparatedCallerRegularizationData

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {coordinateCount : ℕ}
    {scales : Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    {preselection :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled}
    {regularized :
      PureWZ2PreselectedCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient coordinateCount preselection}
    (data : PureWZ2PreselectedSeparatedCallerRegularizationData
      actualNearby quotient coordinateCount preselection regularized)

/-- A family-free common loss dominating every local source-conflict
refinement.  The local complete family embeds in the original ambient fine
family, so the spatial-cell logarithmic loss is bounded by the corresponding
ambient-cardinality loss. -/
def commonLoss (_data : PureWZ2PreselectedSeparatedCallerRegularizationData
    actualNearby quotient coordinateCount preselection regularized) : ENNReal :=
  pureWZ2OrdinarySeparationLoss *
    pureWZ2SpatialCellRegularizationLoss 1 fine.card

/-- A finite common nearby-CWA constant dominating every rebuilt local
constant. -/
def commonConstant : ENNReal :=
  ∑ parent : Fin preselection.selected.family.card,
    (data.fiberData parent).separated.outputConstant

/-- Total pre-balancing loss from the ambient source to the global separated
merge. -/
def totalSelectionLoss : ENNReal :=
  (((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
      preselection.retentionConstant) *
    pureWZ2CompleteParentRegularizationLoss
      actualNearby.scaleData.coarse.card coordinateCount) * data.commonLoss

theorem fiber_loss_le (parent : Fin preselection.selected.family.card) :
    (data.fiberData parent).separated.retentionLoss ≤ data.commonLoss := by
  refine (data.fiberData parent).separated.retention_loss_le.trans ?_
  have cardLe :
      (regularized.fiberData parent).complete.selectedFine.family.card ≤
        fine.card := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective
        (regularized.fiberData parent).complete.selectedFine.embedding
        (regularized.fiberData parent).complete.selectedFine.embedding.injective
  have logLe :
      Nat.log 2
          (2 *
            (regularized.fiberData parent).complete.selectedFine.family.card) ≤
        Nat.log 2 (2 * fine.card) :=
    Nat.log_mono_right (Nat.mul_le_mul_left 2 cardLe)
  unfold commonLoss pureWZ2SpatialCellRegularizationLoss
  gcongr
  exact cardLe

theorem fiber_constant_le (parent : Fin preselection.selected.family.card) :
    (data.fiberData parent).separated.outputConstant ≤
      data.commonConstant := by
  change (data.fiberData parent).separated.outputConstant ≤
    ∑ currentParent : Fin preselection.selected.family.card,
      (data.fiberData currentParent).separated.outputConstant
  exact Finset.single_le_sum
    (fun currentParent _ =>
      (show (0 : ENNReal) ≤
        (data.fiberData currentParent).separated.outputConstant from bot_le))
    (Finset.mem_univ parent)

theorem commonLoss_ne_top : data.commonLoss ≠ ⊤ := by
  exact ENNReal.mul_ne_top
    (by simp [pureWZ2OrdinarySeparationLoss])
    (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top (by simp)))

theorem commonConstant_ne_top : data.commonConstant ≠ ⊤ := by
  simp only [commonConstant, ENNReal.sum_ne_top]
  exact fun parent _ =>
    (data.fiberData parent).separated.outputConstant_ne_top

end PureWZ2PreselectedSeparatedCallerRegularizationData

/-- Run the ordinary source-conflict refinement independently inside every
caller retained by the preselection. -/
theorem pureWZ2_preselected_separated_caller_regularization
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (coordinateCount : ℕ)
    (scales : Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (preselection :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (regularized :
      PureWZ2PreselectedCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient coordinateCount preselection)
    (boundedBase : HasBoundedBase fine 4)
    (deltaLtOne : delta < 1) :
    Nonempty (PureWZ2PreselectedSeparatedCallerRegularizationData
      actualNearby quotient coordinateCount preselection regularized) := by
  let fiberData := fun parent : Fin preselection.selected.family.card =>
    Classical.choice <|
      pureWZ2_separated_caller_class_regularization
        actualNearby quotient
        ((pureWZ2PostDeletionPositiveCallerBase quotient).embedding
          (preselection.selected.embedding parent))
        coordinateCount (regularized.fiberData parent)
        (preselection.weightLevel_pos.trans_le
          (preselection.weight_band parent).1)
        boundedBase deltaLtOne
  exact ⟨{ fiberData := fiberData }⟩

/-- The exact internal partitioning cover on the old preselected merge.  This
is constructed before the local source-conflict refinements, whose global
merge will then restrict its fine side. -/
noncomputable def pureWZ2PreselectedMergedInternalCover
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (coordinateCount : ℕ)
    {scales : Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    (preselection :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (regularized :
      PureWZ2PreselectedCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient coordinateCount preselection)
    (merged :
      PureWZ2GenericMergedCallerClassRegularizationData
        actualNearby quotient
        preselection.selectedCallerBase.toTubeSubfamily
        coordinateCount regularized.toCallerSubfamily
        ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          preselection.retentionConstant))
    (scaleSeparation : 18 * delta ≤ callerRequested.1) :
    WZ2PaperPartitioningCover
      merged.merged.family preselection.selected.family := by
  have callerPos : 0 < callerRequested.1 :=
    actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1
  have stronglySeparated :
      ∀ first second : Fin preselection.selected.family.card,
        first ≠ second →
          1600 * callerRequested.1 <
            wz1PaperLineDistance
              (preselection.selected.family.tube first)
              (preselection.selected.family.tube second) := by
    intro first second hne
    rw [preselection.selected.tube_eq, preselection.selected.tube_eq,
      (pureWZ2PostDeletionPositiveCallerBase quotient).tube_eq,
      (pureWZ2PostDeletionPositiveCallerBase quotient).tube_eq]
    exact quotient.caller_strongly_separated _ _
      ((pureWZ2PostDeletionPositiveCallerBase quotient).embedding.injective.ne
        (preselection.selected.embedding.injective.ne hne))
  have parentCarrier :
      ∀ source,
        WZ2PaperTubeCarrierCovers
          (merged.merged.family.tube source)
          (preselection.selected.family.tube
            (merged.callerCover.parent source)) := by
    intro source
    exact
      wz1PaperTubeCarrier_subset_of_lineCover_eighteen
        actualNearby.scaleData.delta_pos callerPos scaleSeparation _ _
        (merged.section6Cover.fine_line_class source)
        (merged.section6Cover.coarse_line_class
          (merged.callerCover.parent source))
        (merged.callerCover.parent_covers source)
  exact
    merged.callerCover.toInternalPartitioningOfStrongSeparation
      actualNearby.scaleData.delta_pos callerPos
      merged.section6Cover.fine_line_class
      merged.section6Cover.coarse_line_class
      parentCarrier stronglySeparated

/-- Reindex each separated local caller output onto the corresponding genuine
full fiber of the preselected same-family cover. -/
noncomputable def pureWZ2PreselectedSeparatedFiberRefinement
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (coordinateCount : ℕ)
    (scales : Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (preselection :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (regularized :
      PureWZ2PreselectedCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient coordinateCount preselection)
    (merged :
      PureWZ2GenericMergedCallerClassRegularizationData
        actualNearby quotient
        preselection.selectedCallerBase.toTubeSubfamily
        coordinateCount regularized.toCallerSubfamily
        ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          preselection.retentionConstant))
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (separated : PureWZ2PreselectedSeparatedCallerRegularizationData
      actualNearby quotient coordinateCount preselection regularized)
    (logExponent : ℕ)
    (absorption : ∀ parent,
      wz1PaperRefinementFraction delta logExponent *
          (separated.fiberData parent).separated.retentionLoss ≤ 1) :
    ∀ parent : Fin preselection.selected.family.card,
      WZ1PaperRefinement
        (restrictPaperShading
          ((pureWZ2PreselectedMergedInternalCover
              actualNearby quotient coordinateCount preselection
              regularized merged scaleSeparation)
            |>.fullFiberSubfamily parent)
          merged.mergedShading)
        logExponent := by
  intro parent
  let sourceFamily :=
    (regularized.fiberData parent).complete.selectedFine.toTubeSubfamily
  let targetFamily :=
    (pureWZ2PreselectedMergedInternalCover
      actualNearby quotient coordinateCount preselection regularized merged
      scaleSeparation)
      |>.fullFiberSubfamily parent
  let indexEquiv : Fin targetFamily.family.card ≃
      Fin sourceFamily.family.card := merged.fiberIndexEquiv parent
  have tubeEq : ∀ index,
      targetFamily.family.tube index =
        sourceFamily.family.tube (indexEquiv index) := by
    intro index
    rw [targetFamily.tube_eq, sourceFamily.tube_eq]
    rw [merged.merged.tube_eq]
    exact congrArg fine.tube (merged.fiber_ambient_eq parent index)
  let sourceShading := restrictPaperShading sourceFamily shading
  let targetShading :=
    restrictPaperShading targetFamily merged.mergedShading
  have carrierEq : ∀ index,
      targetShading.carrier index =
        sourceShading.carrier (indexEquiv index) := by
    intro index
    change merged.mergedShading.carrier
        (targetFamily.embedding index) = _
    rw [merged.mergedShading_eq]
    change shading.carrier
        (merged.merged.embedding (targetFamily.embedding index)) = _
    exact congrArg shading.carrier (merged.fiber_ambient_eq parent index)
  exact
    ((separated.fiberData parent).toPaperRefinement
      logExponent (absorption parent)).reindexSource
        indexEquiv tubeEq carrierEq

/-- Global output after every selected caller fiber has undergone the paper's
ordinary source-conflict refinement. -/
structure PureWZ2PreselectedSeparatedCallerMergeData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (coordinateCount : ℕ)
    {scales : Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    (preselection :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (regularized :
      PureWZ2PreselectedCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient coordinateCount preselection)
    (merged :
      PureWZ2GenericMergedCallerClassRegularizationData
        actualNearby quotient
        preselection.selectedCallerBase.toTubeSubfamily
        coordinateCount regularized.toCallerSubfamily
        ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          preselection.retentionConstant))
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (separated : PureWZ2PreselectedSeparatedCallerRegularizationData
      actualNearby quotient coordinateCount preselection regularized)
    (logExponent : ℕ)
    (absorption : ∀ parent,
      wz1PaperRefinementFraction delta logExponent *
          (separated.fiberData parent).separated.retentionLoss ≤ 1) where
  fiberRefinement :
    ∀ parent : Fin preselection.selected.family.card,
      WZ1PaperRefinement
        (restrictPaperShading
          ((pureWZ2PreselectedMergedInternalCover
              actualNearby quotient coordinateCount preselection
              regularized merged scaleSeparation)
            |>.fullFiberSubfamily parent)
          merged.mergedShading)
        logExponent
  fiberRefinement_eq :
    fiberRefinement =
      pureWZ2PreselectedSeparatedFiberRefinement
        actualNearby quotient coordinateCount scales scheduled preselection
        regularized merged
        scaleSeparation separated logExponent absorption
  mergedRefinement :
    WZ2PaperFiberwiseRefinementMergeData
      (pureWZ2PreselectedMergedInternalCover
        actualNearby quotient coordinateCount preselection regularized merged
        scaleSeparation)
      merged.mergedShading logExponent fiberRefinement
  fullFiberReindex :
    ∀ parent : Fin preselection.selected.family.card,
      WZ2PaperFiberwiseMergedFullFiberReindexData
        mergedRefinement parent
  selected_nonempty :
    mergedRefinement.refinement.selected.family.Nonempty
  internalCover :
    WZ2PaperPartitioningCover
      mergedRefinement.refinement.selected.family
      preselection.selected.family
  internalCover_parent :
    ∀ index, internalCover.parent index =
      (pureWZ2PreselectedMergedInternalCover
        actualNearby quotient coordinateCount preselection regularized merged
        scaleSeparation).parent
          (mergedRefinement.refinement.selected.embedding index)
  section6Cover :
    PureWZ2Section6Cover
      mergedRefinement.refinement.selected.family
      preselection.selected.family
  source_mass_retention :
    shading.mass ≤ separated.totalSelectionLoss *
      mergedRefinement.refinement.refined.mass
  fiber_pure_cwa :
    ∀ parent : Fin preselection.selected.family.card,
      WZ2PaperPureCWAAtNearbyScales
        (wz2PaperFullFiberSubfamily
          mergedRefinement.refinement.selected.family
          preselection.selected.family parent).family
        separated.commonConstant
  fiber_strongly_separated :
    ∀ parent first second, first ≠ second →
      wz2PaperLiteralSourceSeparationFactor * delta <
        wz1PaperLineDistance
          ((wz2PaperFullFiberSubfamily
            mergedRefinement.refinement.selected.family
            preselection.selected.family parent).family.tube first)
          ((wz2PaperFullFiberSubfamily
            mergedRefinement.refinement.selected.family
            preselection.selected.family parent).family.tube second)

/-- Merge all separated selected caller fibers while retaining exact local
CWA and source-separation certificates on every complete merged fiber. -/
theorem pureWZ2_preselected_separated_caller_merge
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (coordinateCount : ℕ)
    (scales : Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (preselection :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (regularized :
      PureWZ2PreselectedCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient coordinateCount preselection)
    (merged :
      PureWZ2GenericMergedCallerClassRegularizationData
        actualNearby quotient
        preselection.selectedCallerBase.toTubeSubfamily
        coordinateCount regularized.toCallerSubfamily
        ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          preselection.retentionConstant))
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (separated : PureWZ2PreselectedSeparatedCallerRegularizationData
      actualNearby quotient coordinateCount preselection regularized)
    (logExponent : ℕ)
    (absorption : ∀ parent,
      wz1PaperRefinementFraction delta logExponent *
          (separated.fiberData parent).separated.retentionLoss ≤ 1) :
    Nonempty (PureWZ2PreselectedSeparatedCallerMergeData
      actualNearby quotient coordinateCount preselection regularized merged
      scaleSeparation separated logExponent absorption) := by
  let cover := pureWZ2PreselectedMergedInternalCover
    actualNearby quotient coordinateCount preselection regularized merged
    scaleSeparation
  let fiberRefinement := pureWZ2PreselectedSeparatedFiberRefinement
    actualNearby quotient coordinateCount scales scheduled preselection
    regularized merged
    scaleSeparation separated logExponent absorption
  let mergedRefinement := Classical.choice <|
    wz2_paper_fiberwise_refinement_merge
      cover merged.mergedShading logExponent fiberRefinement
  let fullFiberReindex : ∀ parent,
      WZ2PaperFiberwiseMergedFullFiberReindexData
        mergedRefinement parent := fun parent =>
    Classical.choice (mergedRefinement.fullFiberReindex parent)
  have selectedNonempty :
      mergedRefinement.refinement.selected.family.Nonempty := by
    let parent : Fin preselection.selected.family.card :=
      ⟨0, preselection.selected_nonempty⟩
    have localNonempty :=
      (separated.fiberData parent).selected_nonempty
    let localIndex :
        Fin (fiberRefinement parent).selected.family.card :=
      ⟨0, localNonempty⟩
    exact Fin.pos_iff_nonempty.mpr
      ⟨mergedRefinement.indexEquiv.symm ⟨parent, localIndex⟩⟩
  have parentSurjective : Function.Surjective fun index =>
      cover.parent (mergedRefinement.refinement.selected.embedding index) := by
    intro parent
    have localNonempty := (separated.fiberData parent).selected_nonempty
    let localIndex :
        Fin (fiberRefinement parent).selected.family.card :=
      ⟨0, localNonempty⟩
    let index := mergedRefinement.indexEquiv.symm ⟨parent, localIndex⟩
    refine ⟨index, ?_⟩
    have embeddingEq := mergedRefinement.selected_embedding_eq index
    have sigmaEq : mergedRefinement.indexEquiv index =
        (⟨parent, localIndex⟩ :
          Σ currentParent : Fin preselection.selected.family.card,
            Fin (fiberRefinement currentParent).selected.family.card) :=
      mergedRefinement.indexEquiv.apply_symm_apply _
    rw [sigmaEq] at embeddingEq
    change cover.parent
      (mergedRefinement.refinement.selected.embedding index) = parent
    rw [embeddingEq]
    exact (cover.mem_fullFiber_iff_parent parent _).mp
      (cover.fullFiberSubfamily_mem parent _ )
  let internalCover := cover.restrictFine
    mergedRefinement.refinement.selected parentSurjective
  have internalCoverParent : ∀ index, internalCover.parent index =
      cover.parent
        (mergedRefinement.refinement.selected.embedding index) := fun _ => rfl
  let section6Cover : PureWZ2Section6Cover
      mergedRefinement.refinement.selected.family
      preselection.selected.family :=
    { fine_line_class :=
        merged.section6Cover.fine_line_class.subfamily
          mergedRefinement.refinement.selected
      coarse_line_class := merged.section6Cover.coarse_line_class
      covers := fun source =>
        ⟨internalCover.parent source, internalCover.parent_covers source⟩
      parent_hit := by
        intro parent
        rcases internalCover.parent_surjective parent with ⟨source, hsource⟩
        exact ⟨source, by rw [← hsource]; exact internalCover.parent_covers source⟩
      coarse_essentially_distinct :=
        merged.section6Cover.coarse_essentially_distinct }
  have fiberMassEq : ∀ parent,
      (fiberRefinement parent).refined.mass =
        (separated.fiberData parent).separated.selectedShading.mass := by
    intro parent
    rfl
  have previousMassLe : merged.mergedShading.mass ≤
      separated.commonLoss *
        mergedRefinement.refinement.refined.mass := by
    rw [merged.mergedShading_mass_eq]
    change (∑ parent : Fin preselection.selected.family.card,
        (restrictPaperShading
          (regularized.fiberData parent).complete.selectedFine.toTubeSubfamily
          shading).mass) ≤ _
    rw [show mergedRefinement.refinement.refined.mass =
        ∑ parent : Fin preselection.selected.family.card,
          (fiberRefinement parent).refined.mass from
      mergedRefinement.refined_mass_eq]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro parent _
    calc
      (restrictPaperShading
          (regularized.fiberData parent).complete.selectedFine.toTubeSubfamily
          shading).mass ≤
          (separated.fiberData parent).separated.retentionLoss *
            (separated.fiberData parent).separated.selectedShading.mass :=
        (separated.fiberData parent).separated.retained_mass
      _ ≤ separated.commonLoss *
          (separated.fiberData parent).separated.selectedShading.mass := by
        gcongr
        exact separated.fiber_loss_le parent
      _ = separated.commonLoss *
          (fiberRefinement parent).refined.mass := by
        rw [fiberMassEq parent]
  have sourceMassRetention : shading.mass ≤
      separated.totalSelectionLoss *
          mergedRefinement.refinement.refined.mass := by
    calc
      shading.mass ≤
          ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            preselection.retentionConstant) *
          pureWZ2CompleteParentRegularizationLoss
            actualNearby.scaleData.coarse.card coordinateCount *
          merged.mergedShading.mass := merged.source_mass_retention
      _ ≤
          ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            preselection.retentionConstant) *
          pureWZ2CompleteParentRegularizationLoss
            actualNearby.scaleData.coarse.card coordinateCount *
          (separated.commonLoss *
            mergedRefinement.refinement.refined.mass) := by
        gcongr
      _ =
          separated.totalSelectionLoss *
              mergedRefinement.refinement.refined.mass := by
        simp only [
          PureWZ2PreselectedSeparatedCallerRegularizationData.totalSelectionLoss]
        ac_rfl
  have fiberCWA : ∀ parent,
      WZ2PaperPureCWAAtNearbyScales
        (wz2PaperFullFiberSubfamily
          mergedRefinement.refinement.selected.family
          preselection.selected.family parent).family
        separated.commonConstant := by
    intro parent
    let reindex := fullFiberReindex parent
    let indexEquiv := Equiv.ofBijective
      reindex.localIndex reindex.localIndex_bijective
    have localCWA : WZ2PaperPureCWAAtNearbyScales
        (separated.fiberData parent).selected.family
        separated.commonConstant :=
      WZ2PaperPureCWAAtNearbyScales.mono
        (separated.fiber_constant_le parent)
        separated.commonConstant_ne_top
        (separated.fiberData parent).pure_cwa
    exact localCWA.reindex indexEquiv reindex.tube_eq
  have fiberStrong : ∀ parent first second, first ≠ second →
      wz2PaperLiteralSourceSeparationFactor * delta <
        wz1PaperLineDistance
          ((wz2PaperFullFiberSubfamily
            mergedRefinement.refinement.selected.family
            preselection.selected.family parent).family.tube first)
          ((wz2PaperFullFiberSubfamily
            mergedRefinement.refinement.selected.family
            preselection.selected.family parent).family.tube second) := by
    intro parent first second hne
    let reindex := fullFiberReindex parent
    rw [reindex.tube_eq, reindex.tube_eq]
    exact (separated.fiberData parent).strongly_separated _ _
      (reindex.localIndex_bijective.1.ne hne)
  exact ⟨{
    fiberRefinement := fiberRefinement
    fiberRefinement_eq := rfl
    mergedRefinement := mergedRefinement
    fullFiberReindex := fullFiberReindex
    selected_nonempty := selectedNonempty
    internalCover := internalCover
    internalCover_parent := internalCoverParent
    section6Cover := section6Cover
    source_mass_retention := sourceMassRetention
    fiber_pure_cwa := fiberCWA
    fiber_strongly_separated := fiberStrong
  }⟩

namespace PureWZ2PreselectedSeparatedCallerMergeData

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {coordinateCount : ℕ}
    {scales : Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    {preselection :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled}
    {regularized :
      PureWZ2PreselectedCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient coordinateCount preselection}
    {merged :
      PureWZ2GenericMergedCallerClassRegularizationData
        actualNearby quotient
        preselection.selectedCallerBase.toTubeSubfamily
        coordinateCount regularized.toCallerSubfamily
        ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          preselection.retentionConstant)}
    {scaleSeparation : 18 * delta ≤ callerRequested.1}
    {separated : PureWZ2PreselectedSeparatedCallerRegularizationData
      actualNearby quotient coordinateCount preselection regularized}
    {logExponent : ℕ}
    {absorption : ∀ parent,
      wz1PaperRefinementFraction delta logExponent *
          (separated.fiberData parent).separated.retentionLoss ≤ 1}
    (data : PureWZ2PreselectedSeparatedCallerMergeData
      actualNearby quotient coordinateCount preselection regularized merged
      scaleSeparation separated logExponent absorption)

/-- The final separated merge, with its exact ambient source provenance. -/
noncomputable def selected : WZ2PaperPureTubeSubfamily fine :=
  merged.merged.comp
    { family := data.mergedRefinement.refinement.selected.family
      embedding := data.mergedRefinement.refinement.selected.embedding
      tube_eq := data.mergedRefinement.refinement.selected.tube_eq }

/-- The final selected shading after all local source-conflict refinements. -/
noncomputable def selectedShading :
    WZ1PaperTubeShading data.selected.family :=
  data.mergedRefinement.refinement.refined

/-- The merged full-fiber mass is exactly the mass of the separated local
caller output used to construct it. -/
theorem fiberShading_mass_eq_local
    (parent : Fin preselection.selected.family.card) :
    (restrictPaperShading
      (data.internalCover.fullFiberSubfamily parent)
      data.selectedShading).mass =
      (separated.fiberData parent).separated.selectedShading.mass := by
  let reindex := data.fullFiberReindex parent
  let indexEquiv := Equiv.ofBijective
    reindex.localIndex reindex.localIndex_bijective
  have mergedMassEq :
      (restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        data.selectedShading).mass =
        (data.fiberRefinement parent).refined.mass := by
    change
      (∑ index : Fin
          (data.internalCover.fullFiberSubfamily parent).family.card,
        volume
          ((restrictPaperShading
            (data.internalCover.fullFiberSubfamily parent)
            data.selectedShading).carrier index)) =
        ∑ index : Fin (data.fiberRefinement parent).selected.family.card,
          volume ((data.fiberRefinement parent).refined.carrier index)
    exact Fintype.sum_equiv indexEquiv
      (fun index => volume
        ((restrictPaperShading
          (data.internalCover.fullFiberSubfamily parent)
          data.selectedShading).carrier index))
      (fun index => volume
        ((data.fiberRefinement parent).refined.carrier index))
      (fun index => congrArg volume (reindex.carrier_eq index))
  calc
    (restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        data.selectedShading).mass =
        (data.fiberRefinement parent).refined.mass := mergedMassEq
    _ = (separated.fiberData parent).separated.selectedShading.mass := by
      rw [congrFun data.fiberRefinement_eq parent]
      rfl

/-- The forward selected caller weight bound survives ordinary separation and
is expressed on the exact complete fiber of the global separated merge. -/
theorem fiber_source_mass_retention
    (parent : Fin preselection.selected.family.card) :
    pureWZ2PostDeletionPositiveCallerWeight quotient
        (preselection.selected.embedding parent) ≤
      (pureWZ2CompleteParentRegularizationLoss
          actualNearby.scaleData.coarse.card coordinateCount *
        separated.commonLoss) *
        (restrictPaperShading
          (data.internalCover.fullFiberSubfamily parent)
          data.selectedShading).mass := by
  have hLocal := (separated.fiberData parent).caller_weight_retention
  have hLocal' :
      quotient.callerActualWeight
          ((pureWZ2PostDeletionPositiveCallerBase quotient).embedding
            (preselection.selected.embedding parent)) ≤
        ((regularized.fiberData parent).regularizationLoss *
          (separated.fiberData parent).separated.retentionLoss) *
          (separated.fiberData parent).separated.selectedShading.mass := by
    rw [← (separated.fiberData parent).selectedShading_eq_separated]
    exact hLocal
  have hLocal'' :
      quotient.callerActualWeight
          ((pureWZ2PostDeletionPositiveCallerBase quotient).embedding
            (preselection.selected.embedding parent)) ≤
        (pureWZ2CompleteParentRegularizationLoss
            actualNearby.scaleData.coarse.card coordinateCount *
          (separated.fiberData parent).separated.retentionLoss) *
          (separated.fiberData parent).separated.selectedShading.mass := by
    rw [← (regularized.fiberData parent).regularizationLoss_eq]
    exact hLocal'
  have hBound :
      quotient.callerActualWeight
          ((pureWZ2PostDeletionPositiveCallerBase quotient).embedding
            (preselection.selected.embedding parent)) ≤
        (pureWZ2CompleteParentRegularizationLoss
            actualNearby.scaleData.coarse.card coordinateCount *
          separated.commonLoss) *
          (separated.fiberData parent).separated.selectedShading.mass := by
    exact hLocal''.trans <| by
      gcongr
      exact separated.fiber_loss_le parent
  calc
    pureWZ2PostDeletionPositiveCallerWeight quotient
          (preselection.selected.embedding parent) =
        quotient.callerActualWeight
          ((pureWZ2PostDeletionPositiveCallerBase quotient).embedding
            (preselection.selected.embedding parent)) := rfl
    _ ≤
        (pureWZ2CompleteParentRegularizationLoss
            actualNearby.scaleData.coarse.card coordinateCount *
          separated.commonLoss) *
          (separated.fiberData parent).separated.selectedShading.mass := hBound
    _ =
        (pureWZ2CompleteParentRegularizationLoss
            actualNearby.scaleData.coarse.card coordinateCount *
          separated.commonLoss) *
          (restrictPaperShading
            (data.internalCover.fullFiberSubfamily parent)
            data.selectedShading).mass := by
      rw [data.fiberShading_mass_eq_local parent]

/-- The generic balancing input specialized to the genuinely separated
pre-balancing family.  All geometric estimates are reproved from the ambient
normalized source and the exact forward mass ledger. -/
theorem fixed_balancing_input
    {sigma sourceLoss internalLoss publicLoss selectionLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := internalLoss) source normalizationExponent)
    (ambient_eq : fine = normalized.croppedFamily)
    (ambientConstant_eq : ambientConstant =
      Kakeya.realRpowENN delta (-internalLoss))
    (shading_eq : HEq shading normalized.croppedRefined)
    (internalLossPos : 0 < internalLoss)
    (selectionLossPos : 0 < selectionLoss)
    (sourcePublicGap : 16 * (internalLoss + selectionLoss) < publicLoss)
    (callerLower : Real.rpow delta (1 - publicLoss) ≤ callerRequested.1)
    (callerUpper : callerRequested.1 ≤ Real.rpow delta publicLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (periodicScale : 50 * delta ≤ callerRequested.1)
    (selectionAbsorption :
      Kakeya.realRpowENN delta selectionLoss *
          separated.totalSelectionLoss ≤ 1)
    (selectedLogBound :
      ((Nat.log 2 data.selected.family.card + 1 : ℕ) : ENNReal) ≤
        ENNReal.ofReal
          (wz2PaperBoundaryLogCoefficient * (1 + Real.log delta⁻¹)))
    (numerical : WZ2PaperFinalGeometricNumericalData
      (internalLoss + selectionLoss) publicLoss publicLoss 0 0)
    (hdeltaNumerical : delta ≤ numerical.delta₀)
    (hdeltaFinal : delta ≤ pureWZ2PostDeletionFinalBalancingScale) :
    WZ2PaperDirectGeometricInputData data.internalCover data.selectedShading
      actualNearby.scaleData.delta_pos
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1) := by
  subst fine
  subst ambientConstant
  cases shading_eq
  have separatedCubical : ∀ parent,
      WZ1PaperIsCubicalShading (data.fiberRefinement parent).refined := by
    intro parent
    rw [congrFun data.fiberRefinement_eq parent]
    change WZ1PaperIsCubicalShading
      (separated.fiberData parent).separated.selectedShading
    rw [(separated.fiberData parent).separated.selectedShading_eq]
    exact restrictPaperShading_cubical
      (separated.fiberData parent).separated.selected.toTubeSubfamily
      (restrictPaperShading_cubical
        (regularized.fiberData parent).complete.selectedFine.toTubeSubfamily
        normalized.cropped_cubical)
  exact pureWZ2_postDeletion_fixed_balancing_input_from_selected
    normalized callerRequested actualNearby data.selected.toTubeSubfamily
    preselection.selected.family data.internalCover data.selectedShading
    data.selected_nonempty preselection.selected_nonempty
    data.section6Cover.fine_line_class data.section6Cover.coarse_line_class
    data.section6Cover.coarse_essentially_distinct
    (data.mergedRefinement.refined_cubical separatedCubical)
    separated.totalSelectionLoss data.source_mass_retention
    scaleSeparation internalLossPos selectionLossPos sourcePublicGap
    callerLower callerUpper hdeltaSmall periodicScale selectionAbsorption
    selectedLogBound numerical hdeltaNumerical hdeltaFinal

end PureWZ2PreselectedSeparatedCallerMergeData

end Kakeya.Assouad

end
