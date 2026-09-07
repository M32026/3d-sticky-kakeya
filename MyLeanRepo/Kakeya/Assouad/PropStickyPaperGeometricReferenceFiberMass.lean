import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentDeletionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCompleteFiberReindex

/-!
# Geometric reference mass for final whole-cell parent deletion

The deletion comparison must use the unshaded geometric mass of each complete
parent fiber, not the already-refined shaded mass.  This is the WZ1 quantity
`fiberMass`: the full-fiber tube count times the nominal `delta^2` tube scale.
-/

noncomputable section

namespace Kakeya.Assouad

def wz2PaperGeometricReferenceFiberMass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (parent : Fin coarse.card) : ENNReal :=
  (cover.fullFiberSubfamily parent).family.enncard *
    Kakeya.realRpowENN delta 2

theorem sum_wz2PaperGeometricReferenceFiberMass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse) :
    (∑ parent : Fin coarse.card,
        wz2PaperGeometricReferenceFiberMass cover parent) =
      fine.enncard * Kakeya.realRpowENN delta 2 := by
  simp only [wz2PaperGeometricReferenceFiberMass]
  rw [← Finset.sum_mul]
  have hsumCardinality :
      (∑ parent : Fin coarse.card,
        (cover.fullFiberSubfamily parent).family.enncard) =
        fine.enncard := by
    have hfiberCardinality :
        ∀ parent,
          (cover.fullFiberSubfamily parent).family.enncard =
            ((cover.fiberIndices parent).card : ENNReal) := by
      intro parent
      change
        ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal) =
          ((cover.fiberIndices parent).card : ENNReal)
      rw [cover.fullFiberIndices_eq parent]
    calc
      ∑ parent : Fin coarse.card,
          (cover.fullFiberSubfamily parent).family.enncard =
          ∑ parent : Fin coarse.card,
            ((cover.fiberIndices parent).card : ENNReal) := by
        apply Finset.sum_congr rfl
        intro parent _
        exact hfiberCardinality parent
      _ = fine.enncard := by
        have hfiberwise :=
          Finset.sum_card_fiberwise_eq_card_filter
            (Finset.univ : Finset (Fin fine.card))
            (Finset.univ : Finset (Fin coarse.card))
            cover.parent
        have hnatural :
            ∑ parent ∈
                (Finset.univ : Finset (Fin coarse.card)),
                ((Finset.univ : Finset (Fin fine.card)).filter
                  fun source => cover.parent source = parent).card =
              (Finset.univ : Finset (Fin fine.card)).card := by
          simpa [Finset.mem_univ] using hfiberwise
        have hnatural' :
            ∑ parent : Fin coarse.card,
                ((Finset.univ : Finset (Fin fine.card)).filter
                  fun source => cover.parent source = parent).card =
              fine.card := by
          simpa using hnatural
        change
          (∑ parent : Fin coarse.card,
              (((Finset.univ : Finset (Fin fine.card)).filter
                fun source => cover.parent source = parent).card :
                  ENNReal)) =
            (fine.card : ENNReal)
        exact_mod_cast hnatural'
  rw [hsumCardinality]

theorem wz2PaperFinalParentDeletion_geometric_fiber_mass_floor
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover sourceShading coarseCells availableFineCells
        balancing coarseData}
    {threshold : ENNReal}
    (deletion :
      WZ2PaperFinalParentDeletionData
        producer
        (wz2PaperGeometricReferenceFiberMass cover)
        threshold) :
    ∀ parent :
        Fin
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            coarse deletion.deletion.retainedParents).family.card,
      threshold *
            (deletion.restriction.restrictedCover.fullFiberSubfamily
              parent).family.enncard *
            Kakeya.realRpowENN delta 2 ≤
        (restrictPaperShading
          (deletion.restriction.restrictedCover.fullFiberSubfamily parent)
          deletion.restriction.selectedFineShading).mass := by
  intro parent
  let coarseSub :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      coarse deletion.deletion.retainedParents
  let ambientParent := coarseSub.embedding parent
  have hFloor :=
    deletion.restriction.parent_fiber_mass_floor parent
  rcases
      wz2_paper_complete_fiber_reindex
        cover deletion.restriction.selected
        deletion.restriction.restrictedCover
        parent ambientParent
        (deletion.restriction.full_fiber_complete parent)
    with ⟨reindex⟩
  have hCard :
      (deletion.restriction.restrictedCover.fullFiberSubfamily
          parent).family.enncard =
        (cover.fullFiberSubfamily ambientParent).family.enncard := by
    change
      ((deletion.restriction.restrictedCover.fullFiberSubfamily
          parent).family.card : ENNReal) =
        ((cover.fullFiberSubfamily ambientParent).family.card : ENNReal)
    norm_cast
    simpa only [Fintype.card_fin] using
      Fintype.card_congr
        (Equiv.ofBijective reindex.localIndex reindex.localIndex_bijective)
  rw [hCard]
  simpa [wz2PaperGeometricReferenceFiberMass, ambientParent, coarseSub,
    mul_assoc] using hFloor

end Kakeya.Assouad

end
