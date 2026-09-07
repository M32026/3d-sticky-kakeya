import MyLeanRepo.Kakeya.Assouad.PureWZ2.GenericOwnerMultiplicity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05FinalCoverExactMultiplicityBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05DeterministicOwnerCall
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGlobalMultiplicityHelpers

/-!
# Exact Node 5 input for a generic owner selection

These proofs use only the generic owner-parent ABI.  In particular they apply
to the selected-caller construction without reconstructing the historical
all-positive caller family.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

private lemma point_mem_union_of_pointMultiplicity_pos
    {bodyFamily : Kakeya.Streamlined.BodyFamily}
    (shading : Kakeya.Streamlined.Shading bodyFamily)
    {point : Point3}
    (hpos : 0 < shading.pointMultiplicity point) :
    point ∈ shading.union := by
  rw [Kakeya.Streamlined.Shading.pointMultiplicity] at hpos
  rcases Finset.card_pos.mp hpos with ⟨index, hindex⟩
  exact ⟨index, (Finset.mem_filter.mp hindex).2⟩

namespace PureWZ2GenericOwnerSelectedData

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) fineShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover fineShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover fineShading coarseCells availableFineCells
        balancing coarseData}
    {owner : WZ2PaperDirectOwnerPreparationData producer}
    {outputConstant : ENNReal}
    (data : PureWZ2GenericOwnerSelectedData owner outputConstant)

theorem finalFineShading_pointMultiplicity_eq_fiberPointMultiplicity
    (fineLine : WZ1PaperIsLineClass fine)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (coarseDistinct : WZ1PaperIsEssentiallyDistinct coarse)
    (source : Fin data.selectedFine.family.card)
    (point : Point3)
    (hsource : point ∈ data.finalFineShading.carrier source) :
    data.finalFineShading.pointMultiplicity point =
      data.internalCover.toWZ1PaperTubeCover.fiberPointMultiplicity
        data.finalFineShading (data.internalCover.parent source) point := by
  let coarseAtPoint : Finset (Fin data.selectedPacked.family.card) :=
    Finset.univ.filter fun parent =>
      point ∈ data.finalCoarseShading.carrier parent
  have hsourceParent : data.internalCover.parent source ∈ coarseAtPoint := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (data.publicBalanced fineLine coarseLine
        coarseDistinct).point_compatibility source
        (data.internalCover.parent source)
        (data.internalCover.parent_covers source) point hsource⟩
  have hcoarseCard : coarseAtPoint.card ≤ 1 := by
    exact_mod_cast data.coarse_pointMultiplicity_le_one point
  unfold Kakeya.Streamlined.Shading.pointMultiplicity
  unfold WZ1PaperTubeCover.fiberPointMultiplicity
  congr 1
  ext other
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hother
    refine ⟨?_, hother⟩
    have hotherParent : data.internalCover.parent other ∈ coarseAtPoint := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (data.publicBalanced fineLine coarseLine
          coarseDistinct).point_compatibility other
          (data.internalCover.parent other)
          (data.internalCover.parent_covers other) point hother⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Finset.card_le_one.mp hcoarseCard _ hotherParent _ hsourceParent⟩
  · exact fun h => h.2

theorem finalFineShading_constantMultiplicity
    (fineLine : WZ1PaperIsLineClass fine)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (coarseDistinct : WZ1PaperIsEssentiallyDistinct coarse) :
    data.finalFineShading.HasConstantMultiplicity
      (2 ^ producer.fiberBand.level)
      (2 * 2 ^ producer.fiberBand.level) := by
  intro point hpoint
  rcases hpoint with ⟨source, hsource⟩
  let parent := data.internalCover.parent source
  have heq :
      data.finalFineShading.pointMultiplicity point =
        data.internalCover.toWZ1PaperTubeCover.fiberPointMultiplicity
          data.finalFineShading parent point :=
    data.finalFineShading_pointMultiplicity_eq_fiberPointMultiplicity
      fineLine coarseLine coarseDistinct source point hsource
  let ownerShading :=
    restrictPaperShading
      (owner.exactified.restrictedCover.fullFiberSubfamily
        (data.selectedPacked.embedding parent))
      owner.exactified.refined
  have hglobalOwnerEq :
      data.finalFineShading.pointMultiplicity point =
        ownerShading.pointMultiplicity point := by
    calc
      data.finalFineShading.pointMultiplicity point =
          data.internalCover.toWZ1PaperTubeCover.fiberPointMultiplicity
            data.finalFineShading parent point := heq
      _ = (restrictPaperShading
            (data.internalCover.fullFiberSubfamily parent)
            data.finalFineShading).pointMultiplicity point := by
          symm
          exact data.internalCover.restrict_fullFiber_pointMultiplicity_eq
            data.finalFineShading parent point
      _ = ownerShading.pointMultiplicity point :=
        data.balancedPullback.pullback.full_fiber_pointMultiplicity_eq
          parent point
  have hglobalPos : 0 < data.finalFineShading.pointMultiplicity point := by
    unfold Kakeya.Streamlined.Shading.pointMultiplicity
    exact Finset.card_pos.mpr
      ⟨source, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsource⟩⟩
  have hownerPos : 0 < ownerShading.pointMultiplicity point := by
    rwa [← hglobalOwnerEq]
  have hownerMem : point ∈ ownerShading.union :=
    point_mem_union_of_pointMultiplicity_pos _ hownerPos
  have hband := owner.fiber_multiplicity_band
    (data.selectedPacked.embedding parent) point hownerMem
  norm_cast at hband
  rw [hglobalOwnerEq]
  constructor
  · simpa only [ownerShading] using hband.1
  · simpa only [ownerShading, pow_succ, mul_comm] using hband.2.le

theorem fineCellNested
    (fineLine : WZ1PaperIsLineClass fine)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (coarseDistinct : WZ1PaperIsEssentiallyDistinct coarse) :
    ∀ source point, point ∈ data.finalFineShading.carrier source →
      ∃ cell ∈ (data.publicBalanced fineLine coarseLine
        coarseDistinct).activeCells,
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          wz1PaperGridCube rho cell := by
  intro source point hpoint
  let exactifiedIndex : Fin owner.exactified.selected.family.card :=
    data.balancedPullback.pullback.selectedFine.embedding source
  let adapterIndex :=
    owner.exactified.selected.embedding exactifiedIndex
  have hExactifiedPoint :
      point ∈ owner.exactified.refined.carrier exactifiedIndex :=
    data.balancedPullback.pullback.selectedFine_subshading source hpoint
  have hFinalPoint :
      point ∈ producer.coarseBand.selectedFineShading.carrier adapterIndex :=
    owner.exactified_subshading exactifiedIndex hExactifiedPoint
  have hAdapterPoint :
      point ∈ owner.exactAdapter.exact.refined.carrier adapterIndex := by
    rw [owner.exactAdapter.exact_refined_eq]
    exact hFinalPoint
  rcases owner.exactAdapter.fineCellNested
      adapterIndex point hAdapterPoint with
    ⟨adapterCell, hAdapterCell, hFineCellSubset⟩
  rcases owner.exactified.refined_owner
      exactifiedIndex point hExactifiedPoint with
    ⟨ownerCell, hOwnerCell, hPointOwnerCell, hOwnerParent⟩
  have hPointFineCell :
      point ∈ wz1PaperGridCube delta (wz1PaperGridIndex delta point) :=
    (mem_wz1PaperGridCube delta _ point).mpr rfl
  have hPointAdapterCell :
      point ∈ wz1PaperGridCube rho adapterCell :=
    hFineCellSubset hPointFineCell
  have hCellEq : adapterCell = ownerCell := by
    by_contra hNe
    exact Set.disjoint_left.mp
      (wz1PaperGridCube_disjoint hNe)
      hPointAdapterCell hPointOwnerCell
  have hRestrictedParent :
      owner.exactified.restrictedCover.parent exactifiedIndex =
        data.selectedPacked.embedding (data.internalCover.parent source) := by
    calc
      owner.exactified.restrictedCover.parent exactifiedIndex =
          data.selectedPacked.embedding
            (data.balancedPullback.pullback.parent source) :=
        (data.balancedPullback.pullback.parent_ambient_eq source).symm
      _ = data.selectedPacked.embedding
          (data.balancedPullback.pullback.restrictedCover.parent source) :=
        congrArg data.selectedPacked.embedding
          (data.balancedPullback.pullback.restricted_parent_eq source).symm
      _ = data.selectedPacked.embedding (data.internalCover.parent source) := rfl
  have hOwnerSelected : ownerCell ∈ data.balancedPullback.selectedCells := by
    rw [data.balancedPullback.selectedCells_eq]
    apply Finset.mem_filter.mpr
    refine ⟨hOwnerCell, ?_⟩
    refine ⟨data.internalCover.parent source, ?_⟩
    exact hOwnerParent.symm.trans
      (congrArg (PureWZ2GenericOwnerSelectedData.packed
        (owner := owner)).embedding hRestrictedParent)
  have hAdapterSelected :
      adapterCell ∈ data.balancedPullback.selectedCells := by
    rwa [hCellEq]
  refine ⟨adapterCell, ?_, hFineCellSubset⟩
  change adapterCell ∈ data.balancedPullback.balanced.activeCells
  rw [data.balancedPullback.balanced_activeCells_eq]
  exact hAdapterSelected

private theorem parent_eq_of_mem_finalFineShading
    (fineLine : WZ1PaperIsLineClass fine)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (coarseDistinct : WZ1PaperIsEssentiallyDistinct coarse)
    (first second : Fin data.selectedFine.family.card)
    (point : Point3)
    (hfirst : point ∈ data.finalFineShading.carrier first)
    (hsecond : point ∈ data.finalFineShading.carrier second) :
    data.internalCover.parent first = data.internalCover.parent second := by
  let coarseAtPoint : Finset (Fin data.selectedPacked.family.card) :=
    Finset.univ.filter fun parent =>
      point ∈ data.finalCoarseShading.carrier parent
  have hcard : coarseAtPoint.card ≤ 1 := by
    exact_mod_cast data.coarse_pointMultiplicity_le_one point
  have hfirstParent : data.internalCover.parent first ∈ coarseAtPoint := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (data.publicBalanced fineLine coarseLine
        coarseDistinct).point_compatibility first
        (data.internalCover.parent first)
        (data.internalCover.parent_covers first) point hfirst⟩
  have hsecondParent : data.internalCover.parent second ∈ coarseAtPoint := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (data.publicBalanced fineLine coarseLine
        coarseDistinct).point_compatibility second
        (data.internalCover.parent second)
        (data.internalCover.parent_covers second) point hsecond⟩
  exact Finset.card_le_one.mp hcard _ hfirstParent _ hsecondParent

theorem exact_restrict_fullFiber_union_eq
    (fineLine : WZ1PaperIsLineClass fine)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (coarseDistinct : WZ1PaperIsEssentiallyDistinct coarse)
    (m : ℕ)
    (exact :
      PureWZ2Node05ExactMultiplicityTruncationData
        data.finalFineShading hdelta m)
    (parent : Fin data.selectedPacked.family.card) :
    (restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        exact.truncated).union =
      (restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        data.finalFineShading).union := by
  apply Set.Subset.antisymm
  · rintro point ⟨source, hpoint⟩
    exact ⟨source, exact.subshading
      ((data.internalCover.fullFiberSubfamily parent).embedding source)
      hpoint⟩
  · rintro point ⟨oldSource, holdPoint⟩
    have holdAmbient :
        point ∈ data.finalFineShading.carrier
          ((data.internalCover.fullFiberSubfamily parent).embedding oldSource) :=
      holdPoint
    have hpointNewUnion : point ∈ exact.truncated.union := by
      rw [exact.union_eq]
      exact
        ⟨(data.internalCover.fullFiberSubfamily parent).embedding oldSource,
          holdAmbient⟩
    rcases hpointNewUnion with ⟨newSource, hnewPoint⟩
    have hnewOld : point ∈ data.finalFineShading.carrier newSource :=
      exact.subshading newSource hnewPoint
    have hparent : data.internalCover.parent newSource = parent := by
      calc
        data.internalCover.parent newSource =
            data.internalCover.parent
              ((data.internalCover.fullFiberSubfamily parent).embedding
                oldSource) :=
          data.parent_eq_of_mem_finalFineShading
            fineLine coarseLine coarseDistinct newSource _ point
            hnewOld holdAmbient
        _ = parent :=
          (data.internalCover.mem_fullFiber_iff_parent parent _).mp
            (data.internalCover.fullFiberSubfamily_mem parent oldSource)
    have hnewMem : newSource ∈ wz2PaperFullFiberIndices
        data.selectedFine.family data.selectedPacked.family parent :=
      (data.internalCover.mem_fullFiber_iff_parent parent _).mpr hparent
    let fiberSource : Fin
        (data.internalCover.fullFiberSubfamily parent).family.card :=
      ((wz2PaperFullFiberIndices data.selectedFine.family
        data.selectedPacked.family parent).orderIsoOfFin rfl).symm
          ⟨newSource, hnewMem⟩
    have hembed :
        (data.internalCover.fullFiberSubfamily parent).embedding fiberSource =
          newSource := by
      change
        ((wz2PaperFullFiberIndices data.selectedFine.family
          data.selectedPacked.family parent).orderEmbOfFin rfl) fiberSource =
            newSource
      have hval :
          (((wz2PaperFullFiberIndices data.selectedFine.family
            data.selectedPacked.family parent).orderIsoOfFin rfl)
              fiberSource).1 = newSource := by
        simp [fiberSource]
      exact hval
    refine ⟨fiberSource, ?_⟩
    change point ∈ exact.truncated.carrier
      ((data.internalCover.fullFiberSubfamily parent).embedding fiberSource)
    rwa [hembed]

theorem exact_restrict_fullFiber_mass_retention
    (fineLine : WZ1PaperIsLineClass fine)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (coarseDistinct : WZ1PaperIsEssentiallyDistinct coarse)
    (m : ℕ) (hm : 0 < m)
    (m_eq : m = 2 ^ producer.fiberBand.level)
    (exact :
      PureWZ2Node05ExactMultiplicityTruncationData
        data.finalFineShading hdelta m)
    (parent : Fin data.selectedPacked.family.card) :
    (restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        data.finalFineShading).mass ≤
      2 *
        (restrictPaperShading
          (data.internalCover.fullFiberSubfamily parent)
          exact.truncated).mass := by
  let oldFiber := restrictPaperShading
    (data.internalCover.fullFiberSubfamily parent) data.finalFineShading
  let newFiber := restrictPaperShading
    (data.internalCover.fullFiberSubfamily parent) exact.truncated
  have holdBand : oldFiber.HasConstantMultiplicity m (2 * m) := by
    intro point hpoint
    rcases hpoint with ⟨source, hsource⟩
    have hambient : point ∈ data.finalFineShading.carrier
        ((data.internalCover.fullFiberSubfamily parent).embedding source) :=
      hsource
    have heq : oldFiber.pointMultiplicity point =
        data.finalFineShading.pointMultiplicity point := by
      calc
        oldFiber.pointMultiplicity point =
            data.internalCover.toWZ1PaperTubeCover.fiberPointMultiplicity
              data.finalFineShading parent point :=
          data.internalCover.restrict_fullFiber_pointMultiplicity_eq
            data.finalFineShading parent point
        _ = data.finalFineShading.pointMultiplicity point := by
          symm
          simpa only [
            (data.internalCover.mem_fullFiber_iff_parent parent _).mp
              (data.internalCover.fullFiberSubfamily_mem parent source)] using
            data.finalFineShading_pointMultiplicity_eq_fiberPointMultiplicity
              fineLine coarseLine coarseDistinct
              ((data.internalCover.fullFiberSubfamily parent).embedding source)
              point hambient
    rw [heq]
    have hband := data.finalFineShading_constantMultiplicity
      fineLine coarseLine coarseDistinct point ⟨_, hambient⟩
    simpa [m_eq] using hband
  have hnewBand : newFiber.HasConstantMultiplicity m (2 * m) := by
    intro point hpoint
    rcases hpoint with ⟨source, hsource⟩
    have hsourceOld : point ∈ data.finalFineShading.carrier
        ((data.internalCover.fullFiberSubfamily parent).embedding source) :=
      exact.subshading _ hsource
    have heq : newFiber.pointMultiplicity point =
        exact.truncated.pointMultiplicity point := by
      calc
        newFiber.pointMultiplicity point =
            data.internalCover.toWZ1PaperTubeCover.fiberPointMultiplicity
              exact.truncated parent point :=
          data.internalCover.restrict_fullFiber_pointMultiplicity_eq
            exact.truncated parent point
        _ = exact.truncated.pointMultiplicity point := by
          symm
          have hparent : data.internalCover.parent
              ((data.internalCover.fullFiberSubfamily parent).embedding source) =
                parent :=
            (data.internalCover.mem_fullFiber_iff_parent parent _).mp
              (data.internalCover.fullFiberSubfamily_mem parent source)
          unfold Kakeya.Streamlined.Shading.pointMultiplicity
          congr 1
          ext candidate
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hcand
            exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              have hcandOld := exact.subshading candidate hcand
              exact hparent ▸ data.parent_eq_of_mem_finalFineShading
                fineLine coarseLine coarseDistinct candidate _ point
                hcandOld hsourceOld⟩, hcand⟩
          · exact fun hcand => hcand.2
    rw [heq]
    have hexact := exact.exact_multiplicity point ⟨_, hsource⟩
    exact ⟨hexact.1, hexact.2.trans (by omega)⟩
  have hvolume : volume oldFiber.union ≤ 1 * volume newFiber.union := by
    rw [one_mul, data.exact_restrict_fullFiber_union_eq
      fineLine coarseLine coarseDistinct m exact parent]
  have hmass := constant_multiplicity_mass_le_of_union_volume_le
    holdBand hnewBand 1 hvolume
  simpa [oldFiber, newFiber] using hmass

end PureWZ2GenericOwnerSelectedData

end Kakeya.Assouad

end
