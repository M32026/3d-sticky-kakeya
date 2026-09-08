import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AnchoredCoarseConflictDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.WeightedGraphSelection

/-!
# One-scale coloring of the anchored owner cover

Color the active reanchored parents so that parents of the same color have
disjoint doubled ordinary fibers.  No fine subfamily is selected at this
stage.  A later simultaneous multi-scale selection may choose one color at
every reference scale.

For any later monochromatic fine subfamily, this module constructs the exact
hit-parent literal partitioning cover.  Its strict full fibers are exactly the
classes of the auxiliary complete-incidence owner map inside that selected
subfamily.  These owner classes are only proved to lie in the corresponding
complete GWZ fibers; they are not identified with the complete fibers.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Streamlined

attribute [local instance] Classical.propDecidable

/-- A proper coloring of the active anchored parent conflict graph. -/
structure PureWZ2OneScaleAnchoredColoringData
    {delta A : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    (fine : PureWZ2LocalizedDistinctReanchoringData sourceShading)
    {constant : ENNReal}
    {scale : Kakeya.Streamlined.AdmissibleScale delta}
    (scaleData :
      PureWZ2GWZScaleData (A := A) source scale constant)
    (oneScale :
      PureWZ2OneScaleAnchoredOwnerCoverData fine scaleData) where
  coarseColor :
    Fin oneScale.coarse.card →
      Fin (pureWZ2AnchoredCoarseConflictDegree A + 1)
  fineColor :
    Fin fine.family.card →
      Fin (pureWZ2AnchoredCoarseConflictDegree A + 1)
  fineColor_eq :
    ∀ sourceIndex,
      fineColor sourceIndex =
        coarseColor (oneScale.cover.parent sourceIndex)
  proper :
    ∀ first second,
      first ≠ second →
      (wz2PaperOrdinaryDilatedFiberIndices
          2 fine.family oneScale.coarse first ∩
        wz2PaperOrdinaryDilatedFiberIndices
          2 fine.family oneScale.coarse second).Nonempty →
      coarseColor first ≠ coarseColor second

/--
One monochromatic restriction of a one-scale anchored coloring.

The literal strict fibers are identified with auxiliary owner classes.  The
last field records only the mathematically valid inclusion of each such class
in its original complete GWZ full fiber.
-/
structure PureWZ2OneScaleMonochromaticCoverData
    {delta A : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    {fine : PureWZ2LocalizedDistinctReanchoringData sourceShading}
    {constant : ENNReal}
    {scale : Kakeya.Streamlined.AdmissibleScale delta}
    {scaleData :
      PureWZ2GWZScaleData (A := A) source scale constant}
    {oneScale :
      PureWZ2OneScaleAnchoredOwnerCoverData fine scaleData}
    (selected : WZ2PaperPureTubeSubfamily fine.family) where
  selectedCoarse :
    WZ2PaperPureTubeSubfamily oneScale.coarse
  cover :
    WZ2PaperPurePartitioningCover
      selected.family selectedCoarse.family
  fullFiberIndices_eq_owner :
    ∀ parent,
      wz2PaperOrdinaryFullFiberIndices
          selected.family selectedCoarse.family parent =
        Finset.univ.filter fun selectedIndex =>
          oneScale.cover.parent
              (selected.embedding selectedIndex) =
            selectedCoarse.embedding parent
  full_fiber_nonempty :
    ∀ parent,
      (wz2PaperOrdinaryFullFiberIndices
        selected.family selectedCoarse.family parent).Nonempty
  strict_fiber_mem_complete_fiber :
    ∀ parent selectedIndex,
      selectedIndex ∈
          wz2PaperOrdinaryFullFiberIndices
            selected.family selectedCoarse.family parent →
        fine.sourceIndex (selected.embedding selectedIndex) ∈
          scaleData.fullFiberIndices
            (oneScale.originalParent
              (selectedCoarse.embedding parent))

/-- Produce the proper coarse coloring from the uniform conflict-degree bound. -/
theorem pureWZ2_one_scale_anchored_coloring
    {delta A : ℝ}
    (hdelta : 0 < delta)
    (hA : 1 ≤ A)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    (fine : PureWZ2LocalizedDistinctReanchoringData sourceShading)
    (hfineRadius : fine.radius ≤ 1 / 4)
    {constant : ENNReal}
    {scale : Kakeya.Streamlined.AdmissibleScale delta}
    (scaleData :
      PureWZ2GWZScaleData (A := A) source scale constant)
    (hscaleSmall : scale.1 ≤ 1 / (200 * A))
    (oneScale :
      PureWZ2OneScaleAnchoredOwnerCoverData fine scaleData) :
    Nonempty
      (PureWZ2OneScaleAnchoredColoringData
        fine scaleData oneScale) := by
  rcases
      pureWZ2_anchored_coarse_conflict_degree
        hdelta hA fine hfineRadius scaleData hscaleSmall oneScale
    with hdegree
  let conflictRelation :
      Fin oneScale.coarse.card →
        Fin oneScale.coarse.card → Prop := fun first second =>
    second ≠ first ∧
      (wz2PaperOrdinaryDilatedFiberIndices
          2 fine.family oneScale.coarse first ∩
        wz2PaperOrdinaryDilatedFiberIndices
          2 fine.family oneScale.coarse second).Nonempty
  have hsymm :
      ∀ first second, conflictRelation first second →
        conflictRelation second first := by
    intro first second hconflict
    exact
      ⟨hconflict.1.symm, by
        simpa [Finset.inter_comm] using hconflict.2⟩
  have hirrefl :
      ∀ parent, ¬ conflictRelation parent parent := by
    intro parent hconflict
    exact hconflict.1 rfl
  have hconflictDegree :
      ∀ parent,
        (Finset.univ.filter fun other =>
          other ≠ parent ∧
            (wz2PaperOrdinaryDilatedFiberIndices
                2 fine.family oneScale.coarse parent ∩
              wz2PaperOrdinaryDilatedFiberIndices
                2 fine.family oneScale.coarse other).Nonempty).card ≤
          pureWZ2AnchoredCoarseConflictDegree A := by
    exact hdegree
  rcases
      @pureWZ2_greedy_proper_coloring
        oneScale.coarse.card
        (pureWZ2AnchoredCoarseConflictDegree A)
        (fun first second =>
          second ≠ first ∧
            (wz2PaperOrdinaryDilatedFiberIndices
                2 fine.family oneScale.coarse first ∩
              wz2PaperOrdinaryDilatedFiberIndices
                2 fine.family oneScale.coarse second).Nonempty)
        hsymm hirrefl
        (fun parent => by
          rw [Finset.filter_congr_decidable]
          exact hconflictDegree parent) with
    ⟨coarseColor, hproper⟩
  let fineColor :
      Fin fine.family.card →
        Fin (pureWZ2AnchoredCoarseConflictDegree A + 1) :=
    fun sourceIndex =>
      coarseColor (oneScale.cover.parent sourceIndex)
  exact
    ⟨{
      coarseColor := coarseColor
      fineColor := fineColor
      fineColor_eq := fun _ => rfl
      proper := by
        intro first second hne hoverlap
        exact hproper first second ⟨hne.symm, hoverlap⟩
    }⟩

/--
Construct the literal hit-parent cover after a later selection that is
monochromatic for this scale.
-/
theorem PureWZ2OneScaleAnchoredColoringData.monochromatic_cover
    {delta A : ℝ}
    (hdelta : 0 < delta)
    (hA : 1 ≤ A)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    {fine : PureWZ2LocalizedDistinctReanchoringData sourceShading}
    {constant : ENNReal}
    {scale : Kakeya.Streamlined.AdmissibleScale delta}
    {scaleData :
      PureWZ2GWZScaleData (A := A) source scale constant}
    {oneScale :
      PureWZ2OneScaleAnchoredOwnerCoverData fine scaleData}
    (coloring :
      PureWZ2OneScaleAnchoredColoringData
        fine scaleData oneScale)
    (selected : WZ2PaperPureTubeSubfamily fine.family)
    (color :
      Fin (pureWZ2AnchoredCoarseConflictDegree A + 1))
    (monochromatic :
      ∀ selectedIndex,
        coloring.fineColor
            (selected.embedding selectedIndex) =
          color) :
    Nonempty
      (PureWZ2OneScaleMonochromaticCoverData
        (A := A) (scaleData := scaleData)
        (oneScale := oneScale) selected) := by
  have hcoarseRadius : 0 ≤ 8 * A * scale.1 := by
    have hscale : 0 < scale.1 :=
      hdelta.trans_le scale.property.1
    positivity
  let parentIndices : Finset (Fin oneScale.coarse.card) :=
    Finset.univ.image fun selectedIndex =>
      oneScale.cover.parent (selected.embedding selectedIndex)
  let selectedCoarse :
      WZ2PaperPureTubeSubfamily oneScale.coarse :=
    WZ2PaperPureTubeSubfamily.fromFinset
      oneScale.coarse parentIndices
  let parentEquiv : Fin parentIndices.card ≃ parentIndices :=
    (parentIndices.orderIsoOfFin rfl).toEquiv
  have hparentMem :
      ∀ selectedIndex,
        oneScale.cover.parent
            (selected.embedding selectedIndex) ∈
          parentIndices := by
    intro selectedIndex
    exact Finset.mem_image.mpr
      ⟨selectedIndex, Finset.mem_univ selectedIndex, rfl⟩
  let selectedParent :
      Fin selected.family.card →
        Fin selectedCoarse.family.card := fun selectedIndex =>
    parentEquiv.symm
      ⟨oneScale.cover.parent
          (selected.embedding selectedIndex),
        hparentMem selectedIndex⟩
  have hselectedParentAmbient :
      ∀ selectedIndex,
        selectedCoarse.embedding
            (selectedParent selectedIndex) =
          oneScale.cover.parent
            (selected.embedding selectedIndex) := by
    intro selectedIndex
    change
      parentIndices.orderEmbOfFin rfl
          (parentEquiv.symm
            ⟨oneScale.cover.parent
                (selected.embedding selectedIndex),
              hparentMem selectedIndex⟩) =
        oneScale.cover.parent
          (selected.embedding selectedIndex)
    exact congrArg Subtype.val
      (parentEquiv.apply_symm_apply
        ⟨oneScale.cover.parent
            (selected.embedding selectedIndex),
          hparentMem selectedIndex⟩)
  have hcoarseColor :
      ∀ parent : Fin selectedCoarse.family.card,
        coloring.coarseColor
            (selectedCoarse.embedding parent) =
          color := by
    intro parent
    have hparent :
        selectedCoarse.embedding parent ∈ parentIndices :=
      Finset.orderEmbOfFin_mem parentIndices rfl parent
    rcases Finset.mem_image.mp hparent with
      ⟨selectedIndex, _, hselectedIndex⟩
    have hmono := monochromatic selectedIndex
    rw [coloring.fineColor_eq] at hmono
    rwa [hselectedIndex] at hmono
  have hselectedNested :
      ∀ selectedIndex,
        (selected.family.tube selectedIndex).carrier ⊆
          (selectedCoarse.family.tube
            (selectedParent selectedIndex)).carrier := by
    intro selectedIndex
    rw [selected.tube_eq, selectedCoarse.tube_eq,
      hselectedParentAmbient]
    exact oneScale.cover.nested
      (selected.embedding selectedIndex)
  have hcoverExistence :
      ∀ selectedIndex,
        ∃ parent : Fin selectedCoarse.family.card,
          selectedIndex ∈
            wz2PaperOrdinaryFullFiberIndices
              selected.family selectedCoarse.family parent := by
    intro selectedIndex
    refine ⟨selectedParent selectedIndex, ?_⟩
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    exact hselectedNested selectedIndex
  have hdoubled :
      ∀ first second : Fin selectedCoarse.family.card,
        first ≠ second →
        Disjoint
          (wz2PaperOrdinaryDilatedFiberIndices
            2 selected.family selectedCoarse.family first)
          (wz2PaperOrdinaryDilatedFiberIndices
            2 selected.family selectedCoarse.family second) := by
    intro first second hne
    rw [Finset.disjoint_left]
    intro selectedIndex hfirst hsecond
    have hambientFirst :
        selected.embedding selectedIndex ∈
          wz2PaperOrdinaryDilatedFiberIndices
            2 fine.family oneScale.coarse
            (selectedCoarse.embedding first) := by
      simpa only [
        mem_wz2PaperOrdinaryDilatedFiberIndices_iff,
        selected.tube_eq, selectedCoarse.tube_eq
      ] using hfirst
    have hambientSecond :
        selected.embedding selectedIndex ∈
          wz2PaperOrdinaryDilatedFiberIndices
            2 fine.family oneScale.coarse
            (selectedCoarse.embedding second) := by
      simpa only [
        mem_wz2PaperOrdinaryDilatedFiberIndices_iff,
        selected.tube_eq, selectedCoarse.tube_eq
      ] using hsecond
    have hambientNe :
        selectedCoarse.embedding first ≠
          selectedCoarse.embedding second :=
      selectedCoarse.embedding.injective.ne hne
    have hcolorNe :=
      coloring.proper
        (selectedCoarse.embedding first)
        (selectedCoarse.embedding second)
        hambientNe
        ⟨selected.embedding selectedIndex,
          Finset.mem_inter.mpr
            ⟨hambientFirst, hambientSecond⟩⟩
    exact hcolorNe
      ((hcoarseColor first).trans
        (hcoarseColor second).symm)
  let cover :
      WZ2PaperPurePartitioningCover
        selected.family selectedCoarse.family :=
    {
      covers := hcoverExistence
      doubled_fibers_disjoint := hdoubled
    }
  have hfullFiberIndices :
      ∀ parent,
        wz2PaperOrdinaryFullFiberIndices
            selected.family selectedCoarse.family parent =
          Finset.univ.filter fun selectedIndex =>
            oneScale.cover.parent
                (selected.embedding selectedIndex) =
              selectedCoarse.embedding parent := by
    intro parent
    ext selectedIndex
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    constructor
    · intro hstrict
      have hambientStrict :
          (fine.family.tube
              (selected.embedding selectedIndex)).carrier ⊆
            (oneScale.coarse.tube
              (selectedCoarse.embedding parent)).carrier := by
        simpa only [selected.tube_eq, selectedCoarse.tube_eq] using
          hstrict
      let ownerParent :=
        oneScale.cover.parent
          (selected.embedding selectedIndex)
      by_contra hne
      have hselectedDoubled :
          selected.embedding selectedIndex ∈
            wz2PaperOrdinaryDilatedFiberIndices
              2 fine.family oneScale.coarse
              (selectedCoarse.embedding parent) := by
        rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
        exact hambientStrict.trans
          (wz2_paper_carrier_subset_centeredDilatedTwo
            (oneScale.coarse.tube
              (selectedCoarse.embedding parent))
            hcoarseRadius)
      have hownerDoubled :
          selected.embedding selectedIndex ∈
            wz2PaperOrdinaryDilatedFiberIndices
              2 fine.family oneScale.coarse ownerParent := by
        rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
        exact
          (oneScale.cover.nested
            (selected.embedding selectedIndex)).trans
            (wz2_paper_carrier_subset_centeredDilatedTwo
              (oneScale.coarse.tube ownerParent)
              hcoarseRadius)
      have hcolorNe :=
        coloring.proper
          ownerParent
          (selectedCoarse.embedding parent)
          hne
          ⟨selected.embedding selectedIndex,
            Finset.mem_inter.mpr
              ⟨hownerDoubled, hselectedDoubled⟩⟩
      have hownerColor :
          coloring.coarseColor ownerParent = color := by
        have hmono := monochromatic selectedIndex
        rw [coloring.fineColor_eq] at hmono
        exact hmono
      exact hcolorNe
        (hownerColor.trans (hcoarseColor parent).symm)
    · intro hparent
      rw [selected.tube_eq, selectedCoarse.tube_eq,
        ← hparent]
      exact oneScale.cover.nested
        (selected.embedding selectedIndex)
  have hfullFiberNonempty :
      ∀ parent,
        (wz2PaperOrdinaryFullFiberIndices
          selected.family selectedCoarse.family parent).Nonempty := by
    intro parent
    have hparent :
        selectedCoarse.embedding parent ∈ parentIndices :=
      Finset.orderEmbOfFin_mem parentIndices rfl parent
    rcases Finset.mem_image.mp hparent with
      ⟨selectedIndex, _, hselectedIndex⟩
    refine ⟨selectedIndex, ?_⟩
    rw [hfullFiberIndices parent]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ selectedIndex, hselectedIndex⟩
  have hcomplete :
      ∀ parent selectedIndex,
        selectedIndex ∈
            wz2PaperOrdinaryFullFiberIndices
              selected.family selectedCoarse.family parent →
          fine.sourceIndex (selected.embedding selectedIndex) ∈
            scaleData.fullFiberIndices
              (oneScale.originalParent
                (selectedCoarse.embedding parent)) := by
    intro parent selectedIndex hstrict
    have hownerEq :
        oneScale.cover.parent
            (selected.embedding selectedIndex) =
          selectedCoarse.embedding parent := by
      rw [hfullFiberIndices parent] at hstrict
      exact (Finset.mem_filter.mp hstrict).2
    have hownerOriginal :=
      oneScale.cover_original_owner
        (selected.embedding selectedIndex)
    rw [hownerEq] at hownerOriginal
    rw [hownerOriginal]
    exact oneScale.owner_mem
      (selected.embedding selectedIndex)
  exact
    ⟨{
      selectedCoarse := selectedCoarse
      cover := cover
      fullFiberIndices_eq_owner := hfullFiberIndices
      full_fiber_nonempty := hfullFiberNonempty
      strict_fiber_mem_complete_fiber := hcomplete
    }⟩

end Kakeya.Assouad

end
