import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-!
# Complete-fiber pullback of a coarse tube selection

Selecting coarse parents induces a canonical fine subfamily: retain every
fine tube in the complete fibers of the selected parents.  This module records
the resulting strict partitioning cover and the restricted shadings.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperCompleteCoarseSelectionPullbackData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse)
    (selectedCoarse : Kakeya.Streamlined.TubeSubfamily coarse) where
  selectedFineIndices : Finset (Fin fine.card)
  selectedFineIndices_eq :
    selectedFineIndices =
      Finset.univ.filter fun source =>
        ∃ parent : Fin selectedCoarse.family.card,
          cover.parent source = selectedCoarse.embedding parent
  selectedFine : Kakeya.Streamlined.TubeSubfamily fine
  selectedFine_eq :
    selectedFine =
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        fine selectedFineIndices
  selectedFineShading : WZ1PaperTubeShading selectedFine.family
  selectedFineShading_eq :
    selectedFineShading =
      restrictPaperShading selectedFine fineShading
  selectedFine_subshading :
    ∀ index,
      selectedFineShading.carrier index ⊆
        fineShading.carrier (selectedFine.embedding index)
  selectedFine_cubical :
    WZ1PaperIsCubicalShading selectedFineShading
  parent :
    Fin selectedFine.family.card →
      Fin selectedCoarse.family.card
  parent_ambient_eq :
    ∀ index,
      selectedCoarse.embedding (parent index) =
        cover.parent (selectedFine.embedding index)
  restrictedCover :
    WZ2PaperPartitioningCover
      selectedFine.family selectedCoarse.family
  restricted_parent_eq :
    ∀ index, restrictedCover.parent index = parent index
  full_fiber_complete :
    ∀ parentIndex : Fin selectedCoarse.family.card,
      Finset.image selectedFine.embedding
          (wz2PaperFullFiberIndices
            selectedFine.family selectedCoarse.family parentIndex) =
        wz2PaperFullFiberIndices
          fine coarse (selectedCoarse.embedding parentIndex)
  selectedCoarseShading :
    WZ1PaperTubeShading selectedCoarse.family
  selectedCoarseShading_eq :
    selectedCoarseShading =
      restrictPaperShading selectedCoarse coarseShading
  selectedCoarse_cubical :
    WZ1PaperIsCubicalShading selectedCoarseShading
  point_compatibility :
    ∀ source point,
      point ∈ selectedFineShading.carrier source →
        point ∈
          selectedCoarseShading.carrier
            (restrictedCover.parent source)

def WZ2PaperCompleteCoarseSelectionPullbackStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ (cover : WZ2PaperPartitioningCover fine coarse),
          ∀ (fineShading : WZ1PaperTubeShading fine),
            ∀ (coarseShading : WZ1PaperTubeShading coarse),
              WZ1PaperIsCubicalShading fineShading →
              WZ1PaperIsCubicalShading coarseShading →
              (∀ source point,
                point ∈ fineShading.carrier source →
                  point ∈
                    coarseShading.carrier (cover.parent source)) →
              ∀ (selectedCoarse :
                  Kakeya.Streamlined.TubeSubfamily coarse),
                Nonempty
                  (WZ2PaperCompleteCoarseSelectionPullbackData
                    cover fineShading coarseShading selectedCoarse)

end Kakeya.Assouad

end
