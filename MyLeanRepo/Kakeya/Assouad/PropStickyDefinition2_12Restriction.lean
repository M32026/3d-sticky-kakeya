import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Extremal

/-!
# Restriction of pure Definition 2.12 full fibers

The full fiber in selected fine and coarse subfamilies is exactly the ambient
full fiber over the corresponding ambient parent, intersected with the
selected fine indices.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Ambient selected fine indices in one ambient strict full fiber. -/
def wz2PaperSelectedAmbientFullFiberIndices
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (selectedFine : WZ2PaperPureTubeSubfamily fine)
    (ambientParent : Fin coarse.card) :
    Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    source ∈ Finset.image selectedFine.embedding Finset.univ ∧
      source ∈
        wz2PaperOrdinaryFullFiberIndices fine coarse ambientParent

/-- Restricting both fine and coarse families gives the ambient full fiber
intersected with the selected fine family. -/
theorem wz2_paper_selected_fullFiber_image
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (selectedFine : WZ2PaperPureTubeSubfamily fine)
    (selectedCoarse : WZ2PaperPureTubeSubfamily coarse)
    (parent : Fin selectedCoarse.family.card) :
    Finset.image selectedFine.embedding
        (wz2PaperOrdinaryFullFiberIndices
          selectedFine.family selectedCoarse.family parent) =
      wz2PaperSelectedAmbientFullFiberIndices
        selectedFine (selectedCoarse.embedding parent) := by
  ext ambientSource
  constructor
  · intro hsource
    rcases Finset.mem_image.mp hsource with
      ⟨selectedSource, hselectedFiber, heq⟩
    apply Finset.mem_filter.mpr
    refine
      ⟨Finset.mem_univ ambientSource,
        Finset.mem_image.mpr
          ⟨selectedSource, Finset.mem_univ selectedSource, heq⟩,
        ?_⟩
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    rw [← heq]
    simpa only [
      selectedFine.tube_eq,
      selectedCoarse.tube_eq
    ] using
      (mem_wz2PaperOrdinaryFullFiberIndices_iff
        parent selectedSource).mp hselectedFiber
  · intro hsource
    rcases Finset.mem_filter.mp hsource with
      ⟨_hambient, hselected, hfiber⟩
    rcases Finset.mem_image.mp hselected with
      ⟨selectedSource, _hsourceUniv, heq⟩
    apply Finset.mem_image.mpr
    refine ⟨selectedSource, ?_, heq⟩
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    simp only [
      selectedFine.tube_eq,
      selectedCoarse.tube_eq
    ]
    rw [← heq] at hfiber
    exact
      (mem_wz2PaperOrdinaryFullFiberIndices_iff
        (selectedCoarse.embedding parent)
        (selectedFine.embedding selectedSource)).mp hfiber

/-- Cardinality of a selected full fiber equals the ambient selected
intersection cardinality. -/
theorem wz2_paper_selected_fullFiber_card
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (selectedFine : WZ2PaperPureTubeSubfamily fine)
    (selectedCoarse : WZ2PaperPureTubeSubfamily coarse)
    (parent : Fin selectedCoarse.family.card) :
    (wz2PaperOrdinaryFullFiberIndices
        selectedFine.family selectedCoarse.family parent).card =
      (wz2PaperSelectedAmbientFullFiberIndices
        selectedFine (selectedCoarse.embedding parent)).card := by
  rw [← wz2_paper_selected_fullFiber_image selectedFine selectedCoarse parent]
  exact
    (Finset.card_image_of_injective _ selectedFine.embedding.injective).symm

/-- If all ambient members of a parent fiber were selected, the selected full
fiber reindexes exactly to the whole ambient full fiber. -/
theorem wz2_paper_selected_fullFiber_complete
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (selectedFine : WZ2PaperPureTubeSubfamily fine)
    (selectedCoarse : WZ2PaperPureTubeSubfamily coarse)
    (parent : Fin selectedCoarse.family.card)
    (complete :
      wz2PaperSelectedAmbientFullFiberIndices
          selectedFine (selectedCoarse.embedding parent) =
        wz2PaperOrdinaryFullFiberIndices
          fine coarse (selectedCoarse.embedding parent)) :
    Finset.image selectedFine.embedding
        (wz2PaperOrdinaryFullFiberIndices
          selectedFine.family selectedCoarse.family parent) =
      wz2PaperOrdinaryFullFiberIndices
        fine coarse (selectedCoarse.embedding parent) := by
  rw [wz2_paper_selected_fullFiber_image, complete]

end Kakeya.Assouad

end
