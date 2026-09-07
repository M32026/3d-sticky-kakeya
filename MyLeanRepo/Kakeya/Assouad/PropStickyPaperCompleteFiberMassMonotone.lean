import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCompleteFiberReindex

/-!
# Mass monotonicity for a complete reindexed fiber

If a selected fine family contains the complete ambient fiber over one
selected coarse parent and its shading is a subshading of the ambient
shading, then the selected full-fiber mass is at most the ambient full-fiber
mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

theorem wz2_paper_complete_fiber_mass_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    {selectedCoarse : Kakeya.Streamlined.TubeFamily rho}
    (restrictedCover :
      WZ2PaperPartitioningCover selected.family selectedCoarse)
    (selectedShading : WZ1PaperTubeShading selected.family)
    (ambientShading : WZ1PaperTubeShading fine)
    (subshading :
      ∀ index,
        selectedShading.carrier index ⊆
          ambientShading.carrier (selected.embedding index))
    (parent : Fin selectedCoarse.card)
    (ambientParent : Fin coarse.card)
    (complete :
      Finset.image selected.embedding
          (wz2PaperFullFiberIndices
            selected.family selectedCoarse parent) =
        wz2PaperFullFiberIndices fine coarse ambientParent) :
    (restrictPaperShading
      (restrictedCover.fullFiberSubfamily parent)
      selectedShading).mass ≤
      (restrictPaperShading
        (cover.fullFiberSubfamily ambientParent)
        ambientShading).mass := by
  rcases
      wz2_paper_complete_fiber_reindex
        cover selected restrictedCover parent ambientParent complete
    with ⟨reindex⟩
  let localFiber := restrictedCover.fullFiberSubfamily parent
  let ambientFiber := cover.fullFiberSubfamily ambientParent
  let equivalence :
      Fin localFiber.family.card ≃ Fin ambientFiber.family.card :=
    Equiv.ofBijective reindex.localIndex reindex.localIndex_bijective
  have hCarrier :
      ∀ index : Fin localFiber.family.card,
        selectedShading.carrier (localFiber.embedding index) ⊆
          ambientShading.carrier
            (ambientFiber.embedding (reindex.localIndex index)) := by
    intro index
    have h := subshading (localFiber.embedding index)
    rw [reindex.ambient_eq index] at h
    exact h
  have hSum :
      (∑ index : Fin localFiber.family.card,
          volume
            (selectedShading.carrier (localFiber.embedding index))) ≤
        ∑ index : Fin localFiber.family.card,
          volume
            (ambientShading.carrier
              (ambientFiber.embedding (reindex.localIndex index))) := by
    exact Finset.sum_le_sum fun index _ =>
      measure_mono (hCarrier index)
  have hReindex :
      (∑ index : Fin localFiber.family.card,
          volume
            (ambientShading.carrier
              (ambientFiber.embedding (reindex.localIndex index)))) =
        ∑ index : Fin ambientFiber.family.card,
          volume
            (ambientShading.carrier (ambientFiber.embedding index)) := by
    exact
      Fintype.sum_equiv equivalence
        (fun index =>
          volume
            (ambientShading.carrier
              (ambientFiber.embedding (reindex.localIndex index))))
        (fun index =>
          volume
            (ambientShading.carrier (ambientFiber.embedding index)))
        (fun _ => rfl)
  exact hSum.trans_eq hReindex

end Kakeya.Assouad

end
