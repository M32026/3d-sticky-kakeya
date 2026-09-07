import MyLeanRepo.Kakeya.Assouad.PureWZ2.MergedCallerClassRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PreselectedCallerNearbyAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyInternalPartitioningCover

/-!
# Same-family assembly after caller-weight preselection

The preselected merge already consists of complete fibers over exactly the
selected caller band.  Thus its pullback is the identity: no second
caller-center selection and no additional mass loss occur.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2PreselectedSameFamilyCallerNearbyAssemblyData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
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
    (nearby :
      PureWZ2PreselectedCallerNearbyAssemblyData
        quotient coordinateCount scales scheduled preselection
        coarseConstant) where
  selectedFine : Kakeya.Streamlined.TubeSubfamily merged.merged.family
  selectedFine_eq :
    selectedFine =
      {
        family := merged.merged.family
        embedding := Equiv.toEmbedding (Equiv.refl _)
        tube_eq := fun _ => rfl
      }
  selectedFineShading : WZ1PaperTubeShading selectedFine.family
  selectedFineShading_eq :
    selectedFineShading =
      restrictPaperShading selectedFine merged.mergedShading
  callerCover :
    WZ1PaperTubeCover
      selectedFine.family preselection.selected.family
  section6Cover :
    PureWZ2Section6Cover
      selectedFine.family preselection.selected.family
  fiber_pure_cwa :
    ∀ parent : Fin preselection.selected.family.card,
      WZ2PaperPureCWAAtNearbyScales
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          selectedFine.family
          (wz2PaperFullFiberIndices
            selectedFine.family preselection.selected.family parent)).family
        fiberConstant
  coarse_pure_cwa :
    WZ2PaperPureCWAAtNearbyScales
      preselection.selected.family coarseConstant
  selectedFineShading_mass_eq :
    selectedFineShading.mass = merged.mergedShading.mass
  source_mass_retention :
    shading.mass ≤
      (((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          preselection.retentionConstant) *
        pureWZ2CompleteParentRegularizationLoss
          actualNearby.scaleData.coarse.card coordinateCount) *
        selectedFineShading.mass

theorem pureWZ2_preselected_same_family_caller_nearby_assembly
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
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
    (nearby :
      PureWZ2PreselectedCallerNearbyAssemblyData
        quotient coordinateCount scales scheduled preselection
        coarseConstant) :
    Nonempty
      (PureWZ2PreselectedSameFamilyCallerNearbyAssemblyData
        actualNearby quotient coordinateCount scales scheduled
        preselection regularized merged nearby) := by
  let selectedFine : Kakeya.Streamlined.TubeSubfamily merged.merged.family :=
    {
      family := merged.merged.family
      embedding := Equiv.toEmbedding (Equiv.refl _)
      tube_eq := fun _ => rfl
    }
  let selectedFineShading :=
    restrictPaperShading selectedFine merged.mergedShading
  have shadingMassEq :
      selectedFineShading.mass = merged.mergedShading.mass := by
    rfl
  have callerCover :
      WZ1PaperTubeCover
        selectedFine.family preselection.selected.family := by
    change
      WZ1PaperTubeCover
        merged.merged.family preselection.selected.family
    change
      WZ1PaperTubeCover
        merged.merged.family preselection.selected.family
    have raw := merged.callerCover
    change
      WZ1PaperTubeCover
        merged.merged.family preselection.selected.family
      at raw
    exact raw
  have section6Cover :
      PureWZ2Section6Cover
        selectedFine.family preselection.selected.family := by
    change
      PureWZ2Section6Cover
        merged.merged.family preselection.selected.family
    change
      PureWZ2Section6Cover
        merged.merged.family preselection.selected.family
    have raw := merged.section6Cover
    change
      PureWZ2Section6Cover
        merged.merged.family preselection.selected.family
      at raw
    exact raw
  have fiberCWA :
      ∀ parent : Fin preselection.selected.family.card,
        WZ2PaperPureCWAAtNearbyScales
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            selectedFine.family
            (wz2PaperFullFiberIndices
              selectedFine.family preselection.selected.family parent)).family
          fiberConstant := by
    change
      ∀ parent : Fin preselection.selected.family.card,
        WZ2PaperPureCWAAtNearbyScales
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            merged.merged.family
            (wz2PaperFullFiberIndices
              merged.merged.family preselection.selected.family parent)).family
          fiberConstant
    change
      ∀ parent : Fin preselection.selected.family.card,
        WZ2PaperPureCWAAtNearbyScales
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            merged.merged.family
            (wz2PaperFullFiberIndices
              merged.merged.family preselection.selected.family parent)).family
          fiberConstant
    have raw := merged.fiber_pure_cwa
    change
      ∀ parent : Fin preselection.selected.family.card,
        WZ2PaperPureCWAAtNearbyScales
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            merged.merged.family
            (wz2PaperFullFiberIndices
              merged.merged.family preselection.selected.family parent)).family
          fiberConstant
      at raw
    exact raw
  exact
    ⟨{
      selectedFine := selectedFine
      selectedFine_eq := rfl
      selectedFineShading := selectedFineShading
      selectedFineShading_eq := rfl
      callerCover := callerCover
      section6Cover := section6Cover
      fiber_pure_cwa := fiberCWA
      coarse_pure_cwa := nearby.literal_cwa
      selectedFineShading_mass_eq := shadingMassEq
      source_mass_retention := by
        rw [shadingMassEq]
        simpa [mul_assoc] using merged.source_mass_retention
    }⟩

namespace PureWZ2PreselectedSameFamilyCallerNearbyAssemblyData

/-- The selected same-family assembly preserves the local caller-class mass
lower bound before balancing and owner exactification. -/
theorem fiber_source_mass_retention
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
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
    {nearby :
      PureWZ2PreselectedCallerNearbyAssemblyData
        quotient coordinateCount scales scheduled preselection
        coarseConstant}
    (data :
      PureWZ2PreselectedSameFamilyCallerNearbyAssemblyData
        actualNearby quotient coordinateCount scales scheduled
        preselection regularized merged nearby)
    (parent : Fin preselection.selected.family.card) :
    pureWZ2PostDeletionPositiveCallerWeight quotient
        (preselection.selected.embedding parent) ≤
      pureWZ2CompleteParentRegularizationLoss
          actualNearby.scaleData.coarse.card coordinateCount *
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            data.selectedFine.family
            (wz2PaperFullFiberIndices
              data.selectedFine.family preselection.selected.family parent))
          data.selectedFineShading).mass := by
  have raw := merged.fiber_mass_retention parent
  change
    pureWZ2PostDeletionPositiveCallerWeight quotient
          (preselection.selected.embedding parent) ≤
      pureWZ2CompleteParentRegularizationLoss
          actualNearby.scaleData.coarse.card coordinateCount *
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            merged.merged.family
            (wz2PaperFullFiberIndices
              merged.merged.family preselection.selected.family parent))
          merged.mergedShading).mass at raw
  rw [data.selectedFineShading_eq, data.selectedFine_eq]
  let identity :
      Kakeya.Streamlined.TubeSubfamily merged.merged.family :=
    {
      family := merged.merged.family
      embedding := Equiv.toEmbedding (Equiv.refl _)
      tube_eq := fun _ => rfl
    }
  let localFiber :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      merged.merged.family
      (wz2PaperFullFiberIndices
        merged.merged.family preselection.selected.family parent)
  have massEq :
      (restrictPaperShading
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          identity.family
          (wz2PaperFullFiberIndices
            identity.family preselection.selected.family parent))
        (restrictPaperShading identity merged.mergedShading)).mass =
      (restrictPaperShading localFiber merged.mergedShading).mass := by
    apply restrictPaperShading_fromFinset_reindex_mass_eq
      identity localFiber merged.mergedShading
      (wz2PaperFullFiberIndices
        identity.family preselection.selected.family parent)
      (Equiv.refl _)
    intro index
    rfl
  rw [massEq]
  exact raw

noncomputable def internalPartitioningCover
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
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
    {nearby :
      PureWZ2PreselectedCallerNearbyAssemblyData
        quotient coordinateCount scales scheduled preselection
        coarseConstant}
    (data :
      PureWZ2PreselectedSameFamilyCallerNearbyAssemblyData
        actualNearby quotient coordinateCount scales scheduled
        preselection regularized merged nearby)
    (scaleSeparation : 18 * delta ≤ callerRequested.1) :
    WZ2PaperPartitioningCover
      data.selectedFine.family preselection.selected.family := by
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
    rw [preselection.selected.tube_eq,
      preselection.selected.tube_eq,
      (pureWZ2PostDeletionPositiveCallerBase quotient).tube_eq,
      (pureWZ2PostDeletionPositiveCallerBase quotient).tube_eq]
    exact
      quotient.caller_strongly_separated _ _
        ((pureWZ2PostDeletionPositiveCallerBase quotient).embedding.injective.ne
          (preselection.selected.embedding.injective.ne hne))
  have parentCarrier :
      ∀ source,
        WZ2PaperTubeCarrierCovers
          (data.selectedFine.family.tube source)
          (preselection.selected.family.tube
            (data.callerCover.parent source)) := by
    intro source
    exact
      wz1PaperTubeCarrier_subset_of_lineCover_eighteen
        actualNearby.scaleData.delta_pos callerPos scaleSeparation
        _ _
        (data.section6Cover.fine_line_class source)
        (data.section6Cover.coarse_line_class
          (data.callerCover.parent source))
        (data.callerCover.parent_covers source)
  exact
    data.callerCover.toInternalPartitioningOfStrongSeparation
      actualNearby.scaleData.delta_pos callerPos
      data.section6Cover.fine_line_class
      data.section6Cover.coarse_line_class
      parentCarrier stronglySeparated

end PureWZ2PreselectedSameFamilyCallerNearbyAssemblyData

end Kakeya.Assouad

end
