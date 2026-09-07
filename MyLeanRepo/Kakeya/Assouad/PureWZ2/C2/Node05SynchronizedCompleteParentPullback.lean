import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05SynchronizedPostGrainExtremality
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Section6CoverAdapter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ExactMultiplicityPostRefinement

/-!
# Complete-parent pullback for a pure Section-6 cover

After synchronized post-grain pruning chooses coarse parents, the first sticky
output must be restricted to all fine tubes in those parents' complete fibers.
This module records only that structural operation.  Quantitative retention,
balance, multiplicity, extremality, and rescaled-fiber refresh remain explicit
downstream obligations.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The ambient fine indices whose canonical Section-6 parent is retained. -/
def pureWZ2Node05CompleteParentFineIndices
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (selectedCoarse : Kakeya.Streamlined.TubeSubfamily coarse) :
    Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    ∃ parent : Fin selectedCoarse.family.card,
      cover.toWZ1PaperTubeCover.parent source =
        selectedCoarse.embedding parent

/-- Structural restriction of a pure Section-6 cover to selected coarse
parents and all of their complete fine fibers. -/
structure PureWZ2Node05CompleteParentPullbackData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse)
    (selectedCoarse : Kakeya.Streamlined.TubeSubfamily coarse) where
  selectedFine : Kakeya.Streamlined.TubeSubfamily fine
  selectedFine_eq : selectedFine =
    Kakeya.Streamlined.TubeSubfamily.fromFinset fine
      (pureWZ2Node05CompleteParentFineIndices cover selectedCoarse)
  selectedFine_nonempty : selectedFine.family.Nonempty
  selectedFineShading : WZ1PaperTubeShading selectedFine.family
  selectedFineShading_eq : selectedFineShading =
    restrictPaperShading selectedFine fineShading
  selectedCoarseShading : WZ1PaperTubeShading selectedCoarse.family
  selectedCoarseShading_eq : selectedCoarseShading =
    restrictPaperShading selectedCoarse coarseShading
  restrictedCover :
    PureWZ2Section6Cover selectedFine.family selectedCoarse.family
  parent_ambient_eq : ∀ source,
    selectedCoarse.embedding
        (restrictedCover.toWZ1PaperTubeCover.parent source) =
      cover.toWZ1PaperTubeCover.parent (selectedFine.embedding source)
  full_fiber_complete : ∀ parent : Fin selectedCoarse.family.card,
    Finset.image selectedFine.embedding
        (wz2PaperFullFiberIndices
          selectedFine.family selectedCoarse.family parent) =
      wz2PaperFullFiberIndices fine coarse
        (selectedCoarse.embedding parent)
  point_compatibility : ∀ source point,
    point ∈ selectedFineShading.carrier source →
      point ∈ selectedCoarseShading.carrier
        (restrictedCover.toWZ1PaperTubeCover.parent source)

/-- Construct the exact complete-parent pullback.  No quantitative conclusion
is inferred from the choice of parents. -/
theorem exists_pureWZ2Node05CompleteParentPullbackData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse)
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (selectedCoarse : Kakeya.Streamlined.TubeSubfamily coarse)
    (selectedCoarseNonempty : selectedCoarse.family.Nonempty) :
    Nonempty (PureWZ2Node05CompleteParentPullbackData
      cover fineShading coarseShading selectedCoarse) := by
  let ambientCover := cover.toWZ1PaperTubeCover
  let indices := pureWZ2Node05CompleteParentFineIndices cover selectedCoarse
  let selectedFine :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset fine indices
  have hselectedMem : ∀ source : Fin selectedFine.family.card,
      selectedFine.embedding source ∈ indices := fun source =>
    Finset.orderEmbOfFin_mem indices rfl source
  have hparentExists : ∀ source : Fin selectedFine.family.card,
      ∃ parent : Fin selectedCoarse.family.card,
        ambientCover.parent (selectedFine.embedding source) =
          selectedCoarse.embedding parent := by
    intro source
    exact (Finset.mem_filter.mp (hselectedMem source)).2
  let parent : Fin selectedFine.family.card →
      Fin selectedCoarse.family.card := fun source =>
    Classical.choose (hparentExists source)
  have hparentAmbient : ∀ source,
      selectedCoarse.embedding (parent source) =
        ambientCover.parent (selectedFine.embedding source) := fun source =>
    (Classical.choose_spec (hparentExists source)).symm
  have hselectedSurjective : ∀ source ∈ indices,
      ∃ index : Fin selectedFine.family.card,
        selectedFine.embedding index = source := by
    intro source hsource
    let member : indices := ⟨source, hsource⟩
    let index : Fin selectedFine.family.card :=
      (indices.orderIsoOfFin rfl).symm member
    exact
      ⟨index, congrArg Subtype.val
        (indices.orderIsoOfFin rfl |>.apply_symm_apply member)⟩
  have hparentSurjective : Function.Surjective parent := by
    intro selectedParent
    rcases ambientCover.parent_surjective
        (selectedCoarse.embedding selectedParent) with
      ⟨ambientSource, hsourceParent⟩
    have hsourceSelected : ambientSource ∈ indices := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, ⟨selectedParent, hsourceParent⟩⟩
    rcases hselectedSurjective ambientSource hsourceSelected with
      ⟨source, hsource⟩
    refine ⟨source, ?_⟩
    apply selectedCoarse.embedding.injective
    rw [hparentAmbient source, hsource, hsourceParent]
  let restrictedCover :
      PureWZ2Section6Cover selectedFine.family selectedCoarse.family :=
    { fine_line_class := cover.fine_line_class.subfamily selectedFine
      coarse_line_class := cover.coarse_line_class.subfamily selectedCoarse
      covers := by
        intro source
        refine ⟨parent source, ?_⟩
        rw [selectedFine.tube_eq, selectedCoarse.tube_eq, hparentAmbient]
        exact ambientCover.parent_covers (selectedFine.embedding source)
      parent_hit := by
        intro selectedParent
        rcases hparentSurjective selectedParent with ⟨source, hsource⟩
        refine ⟨source, ?_⟩
        have hcovering :=
          ambientCover.parent_covers (selectedFine.embedding source)
        rw [← hparentAmbient source, hsource] at hcovering
        simpa only [selectedFine.tube_eq, selectedCoarse.tube_eq] using hcovering
      coarse_essentially_distinct :=
        cover.coarse_essentially_distinct.subfamily selectedCoarse }
  have hrestrictedParent : ∀ source,
      restrictedCover.toWZ1PaperTubeCover.parent source = parent source := by
    intro source
    exact (restrictedCover.toWZ1PaperTubeCover.parent_unique
      source (parent source) (by
        rw [selectedFine.tube_eq, selectedCoarse.tube_eq, hparentAmbient]
        exact ambientCover.parent_covers
          (selectedFine.embedding source))).symm
  have hfullFiberComplete : ∀ selectedParent :
      Fin selectedCoarse.family.card,
      Finset.image selectedFine.embedding
          (wz2PaperFullFiberIndices
            selectedFine.family selectedCoarse.family selectedParent) =
        wz2PaperFullFiberIndices fine coarse
          (selectedCoarse.embedding selectedParent) := by
    intro selectedParent
    ext ambientSource
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨source, hsource, rfl⟩
      have hparent :
          restrictedCover.toWZ1PaperTubeCover.parent source =
            selectedParent :=
        (restrictedCover.mem_fullFiber_iff_parent selectedParent source).mp
          hsource
      have hparent' : parent source = selectedParent := by
        rw [← hrestrictedParent source]
        exact hparent
      apply (cover.mem_fullFiber_iff_parent
        (selectedCoarse.embedding selectedParent)
        (selectedFine.embedding source)).mpr
      calc
        ambientCover.parent (selectedFine.embedding source) =
            selectedCoarse.embedding (parent source) :=
          (hparentAmbient source).symm
        _ = selectedCoarse.embedding selectedParent := congrArg _ hparent'
    · intro hsource
      have hsourceParent : ambientCover.parent ambientSource =
          selectedCoarse.embedding selectedParent :=
        (cover.mem_fullFiber_iff_parent
          (selectedCoarse.embedding selectedParent) ambientSource).mp hsource
      have hsourceSelected : ambientSource ∈ indices := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, ⟨selectedParent, hsourceParent⟩⟩
      rcases hselectedSurjective ambientSource hsourceSelected with
        ⟨source, hsourceEq⟩
      refine ⟨source, ?_, hsourceEq⟩
      apply (restrictedCover.mem_fullFiber_iff_parent selectedParent source).mpr
      rw [hrestrictedParent source]
      apply selectedCoarse.embedding.injective
      rw [hparentAmbient source, hsourceEq, hsourceParent]
  let selectedFineShading := restrictPaperShading selectedFine fineShading
  let selectedCoarseShading :=
    restrictPaperShading selectedCoarse coarseShading
  have hpointCompatibility : ∀ source point,
      point ∈ selectedFineShading.carrier source →
        point ∈ selectedCoarseShading.carrier
          (restrictedCover.toWZ1PaperTubeCover.parent source) := by
    intro source point hpoint
    change point ∈ fineShading.carrier (selectedFine.embedding source) at hpoint
    change point ∈ coarseShading.carrier
      (selectedCoarse.embedding
        (restrictedCover.toWZ1PaperTubeCover.parent source))
    have hcovering := ambientCover.parent_covers
      (selectedFine.embedding source)
    rw [← hparentAmbient source, ← hrestrictedParent source] at hcovering
    exact balanced.point_compatibility
      (selectedFine.embedding source)
      (selectedCoarse.embedding
        (restrictedCover.toWZ1PaperTubeCover.parent source))
      hcovering
      point hpoint
  have hselectedFineNonempty : selectedFine.family.Nonempty := by
    let selectedParent : Fin selectedCoarse.family.card :=
      ⟨0, selectedCoarseNonempty⟩
    rcases hparentSurjective selectedParent with ⟨source, _⟩
    exact Nat.zero_lt_of_lt source.isLt
  exact
    ⟨{ selectedFine := selectedFine
       selectedFine_eq := rfl
       selectedFine_nonempty := hselectedFineNonempty
       selectedFineShading := selectedFineShading
       selectedFineShading_eq := rfl
       selectedCoarseShading := selectedCoarseShading
       selectedCoarseShading_eq := rfl
       restrictedCover := restrictedCover
       parent_ambient_eq := by
         intro source
         rw [hrestrictedParent]
         exact hparentAmbient source
       full_fiber_complete := hfullFiberComplete
       point_compatibility := hpointCompatibility }⟩

namespace PureWZ2Node05CompleteParentPullbackData

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {selectedCoarse : Kakeya.Streamlined.TubeSubfamily coarse}
    (data : PureWZ2Node05CompleteParentPullbackData
      cover fineShading coarseShading selectedCoarse)

/-- Complete-parent restriction preserves each retained fiber's indexed
shaded mass exactly. -/
theorem full_fiber_mass_eq
    (parent : Fin selectedCoarse.family.card) :
    (restrictPaperShading
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        data.selectedFine.family
        (wz2PaperFullFiberIndices data.selectedFine.family
          selectedCoarse.family parent))
      data.selectedFineShading).mass =
    (restrictPaperShading
      (Kakeya.Streamlined.TubeSubfamily.fromFinset fine
        (wz2PaperFullFiberIndices fine coarse
          (selectedCoarse.embedding parent)))
      fineShading).mass := by
  rw [restrictPaperShading_fromFinset_mass,
    restrictPaperShading_fromFinset_mass, data.selectedFineShading_eq]
  change
    (∑ index ∈ wz2PaperFullFiberIndices data.selectedFine.family
      selectedCoarse.family parent,
        volume (fineShading.carrier (data.selectedFine.embedding index))) =
      ∑ index ∈ wz2PaperFullFiberIndices fine coarse
        (selectedCoarse.embedding parent),
          volume (fineShading.carrier index)
  calc
    (∑ index ∈ wz2PaperFullFiberIndices data.selectedFine.family
        selectedCoarse.family parent,
          volume (fineShading.carrier (data.selectedFine.embedding index))) =
      ∑ index ∈ Finset.image data.selectedFine.embedding
        (wz2PaperFullFiberIndices data.selectedFine.family
          selectedCoarse.family parent),
          volume (fineShading.carrier index) :=
        (Finset.sum_image
          (s := wz2PaperFullFiberIndices data.selectedFine.family
            selectedCoarse.family parent)
          (g := data.selectedFine.embedding)
          (f := fun index => volume (fineShading.carrier index))
          data.selectedFine.embedding.injective.injOn).symm
    _ = ∑ index ∈ wz2PaperFullFiberIndices fine coarse
        (selectedCoarse.embedding parent),
          volume (fineShading.carrier index) := by
      rw [data.full_fiber_complete parent]

/-- The same finite reindexing preserves point multiplicity on every retained
complete parent fiber. -/
theorem full_fiber_pointMultiplicity_eq
    (parent : Fin selectedCoarse.family.card) (point : Point3) :
    (restrictPaperShading
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        data.selectedFine.family
        (wz2PaperFullFiberIndices data.selectedFine.family
          selectedCoarse.family parent))
      data.selectedFineShading).pointMultiplicity point =
    (restrictPaperShading
      (Kakeya.Streamlined.TubeSubfamily.fromFinset fine
        (wz2PaperFullFiberIndices fine coarse
          (selectedCoarse.embedding parent)))
      fineShading).pointMultiplicity point := by
  rw [data.restrictedCover.c2_fullFiberIndices_eq parent,
    cover.c2_fullFiberIndices_eq (selectedCoarse.embedding parent)]
  rw [data.restrictedCover.toWZ1PaperTubeCover.restrict_fiber_pointMultiplicity
    data.selectedFineShading parent point,
    cover.toWZ1PaperTubeCover.restrict_fiber_pointMultiplicity
      fineShading (selectedCoarse.embedding parent) point]
  unfold WZ1PaperTubeCover.fiberPointMultiplicity
  apply Finset.card_bij (fun source _ => data.selectedFine.embedding source)
  · intro source hsource
    have hsource' := Finset.mem_filter.mp hsource
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · have hlocal : source ∈ wz2PaperFullFiberIndices
          data.selectedFine.family selectedCoarse.family parent := by
        rw [data.restrictedCover.c2_fullFiberIndices_eq parent]
        exact hsource'.1
      have himage : data.selectedFine.embedding source ∈
          Finset.image data.selectedFine.embedding
            (wz2PaperFullFiberIndices data.selectedFine.family
              selectedCoarse.family parent) :=
        Finset.mem_image.mpr ⟨source, hlocal, rfl⟩
      rw [data.full_fiber_complete parent,
        cover.c2_fullFiberIndices_eq (selectedCoarse.embedding parent)] at himage
      exact himage
    · rw [data.selectedFineShading_eq] at hsource'
      exact hsource'.2
  · intro first _ second _ h
    exact data.selectedFine.embedding.injective h
  · intro ambientSource hsource
    have hsource' := Finset.mem_filter.mp hsource
    have hambient : ambientSource ∈ wz2PaperFullFiberIndices fine coarse
        (selectedCoarse.embedding parent) := by
      rw [cover.c2_fullFiberIndices_eq (selectedCoarse.embedding parent)]
      exact hsource'.1
    have himage : ambientSource ∈ Finset.image data.selectedFine.embedding
        (wz2PaperFullFiberIndices data.selectedFine.family
          selectedCoarse.family parent) := by
      rw [data.full_fiber_complete parent]
      exact hambient
    rcases Finset.mem_image.mp himage with ⟨source, hlocal, hembed⟩
    refine ⟨source, ?_, hembed⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · rw [← data.restrictedCover.c2_fullFiberIndices_eq parent]
      exact hlocal
    · rw [data.selectedFineShading_eq]
      change point ∈ fineShading.carrier (data.selectedFine.embedding source)
      rw [hembed]
      exact hsource'.2

/-- The selected fine mass is the exact sum of the retained ambient complete
fiber masses. -/
theorem selectedFineShading_mass_eq :
    data.selectedFineShading.mass =
      ∑ parent : Fin selectedCoarse.family.card,
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset fine
            (wz2PaperFullFiberIndices fine coarse
              (selectedCoarse.embedding parent)))
          fineShading).mass := by
  rw [← data.restrictedCover.toWZ1PaperTubeCover.sum_fiberShadedMass
    data.selectedFineShading]
  apply Finset.sum_congr rfl
  intro parent _
  unfold WZ1PaperTubeCover.fiberShadedMass
  rw [← data.restrictedCover.c2_fullFiberIndices_eq parent,
    ← restrictPaperShading_fromFinset_mass]
  exact data.full_fiber_mass_eq parent

/-- If the ambient coarse shading has multiplicity at most one, then every
fine source meeting a selected coarse carrier has exactly that selected
parent. -/
theorem ambient_parent_eq_of_mem
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (coarseMultiplicityOne : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ 1)
    (parent : Fin selectedCoarse.family.card)
    (source : Fin fine.card) (point : Point3)
    (hparent : point ∈ data.selectedCoarseShading.carrier parent)
    (hsource : point ∈ fineShading.carrier source) :
    cover.toWZ1PaperTubeCover.parent source =
      selectedCoarse.embedding parent := by
  let activeParents : Finset (Fin coarse.card) :=
    Finset.univ.filter fun index =>
      point ∈ coarseShading.carrier index
  have hcard : activeParents.card ≤ 1 := by
    have h := coarseMultiplicityOne point
    change (activeParents.card : ENNReal) ≤ 1 at h
    exact_mod_cast h
  have hsourceParent :
      cover.toWZ1PaperTubeCover.parent source ∈ activeParents := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact balanced.point_compatibility source
      (cover.toWZ1PaperTubeCover.parent source)
      (cover.toWZ1PaperTubeCover.parent_covers source) point hsource
  have hselectedParent : selectedCoarse.embedding parent ∈ activeParents := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [data.selectedCoarseShading_eq] at hparent
    exact hparent
  exact Finset.card_le_one.mp hcard _ hsourceParent _ hselectedParent

/-- On every active selected coarse cell, complete-parent restriction leaves
the ambient fine union unchanged. -/
theorem fine_inter_activeCell_eq
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (coarseMultiplicityOne : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ 1)
    (hrho : 0 < rho)
    (cell : ℤ × ℤ × ℤ)
    (hcell : cell ∈
      wz1PaperActiveCells data.selectedCoarseShading hrho) :
    data.selectedFineShading.union ∩ wz1PaperGridCube rho cell =
      fineShading.union ∩ wz1PaperGridCube rho cell := by
  apply Set.Subset.antisymm
  · rintro point ⟨⟨source, hsource⟩, hpointCell⟩
    exact ⟨⟨data.selectedFine.embedding source, by
      rw [data.selectedFineShading_eq] at hsource
      exact hsource⟩, hpointCell⟩
  · rintro point ⟨⟨source, hsource⟩, hpointCell⟩
    have hselectedCubical :
        WZ1PaperIsCubicalShading data.selectedCoarseShading := by
      rw [data.selectedCoarseShading_eq]
      exact restrictPaperShading_cubical selectedCoarse
        balanced.coarse_cubical
    have hselectedCell := hselectedCubical.inter_activeCell_eq hrho hcell
    have hpointSelectedUnion : point ∈ data.selectedCoarseShading.union := by
      have hinter : point ∈ data.selectedCoarseShading.union ∩
          wz1PaperGridCube rho cell := by
        rw [hselectedCell]
        exact hpointCell
      exact hinter.1
    rcases hpointSelectedUnion with ⟨parent, hparent⟩
    have hparentEq := data.ambient_parent_eq_of_mem balanced
      coarseMultiplicityOne parent source point hparent hsource
    have hambientFiber : source ∈ wz2PaperFullFiberIndices fine coarse
        (selectedCoarse.embedding parent) :=
      (cover.mem_fullFiber_iff_parent
        (selectedCoarse.embedding parent) source).mpr hparentEq
    have himage : source ∈ Finset.image data.selectedFine.embedding
        (wz2PaperFullFiberIndices data.selectedFine.family
          selectedCoarse.family parent) := by
      rw [data.full_fiber_complete parent]
      exact hambientFiber
    rcases Finset.mem_image.mp himage with
      ⟨selectedSource, _, hembed⟩
    refine ⟨⟨selectedSource, ?_⟩, hpointCell⟩
    rw [data.selectedFineShading_eq]
    change point ∈ fineShading.carrier
      (data.selectedFine.embedding selectedSource)
    rwa [hembed]

/-- The selected coarse active cells are genuine ambient balanced cells. -/
theorem selected_activeCells_subset
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hrho : 0 < rho) :
    wz1PaperActiveCells data.selectedCoarseShading hrho ⊆
      balanced.activeCells := by
  intro cell hcell
  rw [mem_wz1PaperActiveCells] at hcell
  rcases hcell.2 with ⟨point, hselected, hpointCell⟩
  have hambient : point ∈ coarseShading.union := by
    rcases hselected with ⟨parent, hparent⟩
    refine ⟨selectedCoarse.embedding parent, ?_⟩
    rw [data.selectedCoarseShading_eq] at hparent
    exact hparent
  rw [balanced.coarse_union_eq] at hambient
  rcases Set.mem_iUnion₂.mp hambient with
    ⟨ambientCell, hambientCell, hpointAmbient⟩
  have hcellEq : ambientCell = cell :=
    ((mem_wz1PaperGridCube rho ambientCell point).mp hpointAmbient).symm.trans
      ((mem_wz1PaperGridCube rho cell point).mp hpointCell)
  rwa [hcellEq] at hambientCell

/-- Unique coarse ownership transports the exact balanced cover to the
complete-parent restriction without changing its physical `cellMass`. -/
noncomputable def toBalanced
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (coarseMultiplicityOne : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ 1)
    (hrho : 0 < rho) :
    PureWZ2BalancedCoverData data.restrictedCover
      data.selectedFineShading data.selectedCoarseShading where
  point_compatibility := by
    intro source parent hcovered point hpoint
    have hparentEq : parent =
        data.restrictedCover.toWZ1PaperTubeCover.parent source :=
      data.restrictedCover.toWZ1PaperTubeCover.parent_unique
        source parent hcovered
    rw [hparentEq]
    exact data.point_compatibility source point hpoint
  coarse_cubical := by
    rw [data.selectedCoarseShading_eq]
    exact restrictPaperShading_cubical selectedCoarse balanced.coarse_cubical
  activeCells := wz1PaperActiveCells data.selectedCoarseShading hrho
  coarse_union_eq := by
    have hcubical : WZ1PaperIsCubicalShading data.selectedCoarseShading := by
      rw [data.selectedCoarseShading_eq]
      exact restrictPaperShading_cubical selectedCoarse
        balanced.coarse_cubical
    exact hcubical.union_eq_activeCells hrho
  cellMass := balanced.cellMass
  cellMass_pos := balanced.cellMass_pos
  cellMass_ne_top := balanced.cellMass_ne_top
  fine_cell_mass := by
    intro cell hcell
    rw [data.fine_inter_activeCell_eq balanced coarseMultiplicityOne
      hrho cell hcell]
    exact balanced.fine_cell_mass cell
      (data.selected_activeCells_subset balanced hrho hcell)

/-- At every point of the selected fine union, unique coarse ownership makes
the restricted and ambient fine multiplicities identical. -/
theorem selectedFine_pointMultiplicity_eq
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (coarseMultiplicityOne : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ 1)
    (point : Point3) (hpoint : point ∈ data.selectedFineShading.union) :
    data.selectedFineShading.pointMultiplicity point =
      fineShading.pointMultiplicity point := by
  rcases hpoint with ⟨selectedSource, hselectedSource⟩
  have hselectedAmbient : point ∈ fineShading.carrier
      (data.selectedFine.embedding selectedSource) := by
    rw [data.selectedFineShading_eq] at hselectedSource
    exact hselectedSource
  have hselectedParent : point ∈ data.selectedCoarseShading.carrier
      (data.restrictedCover.toWZ1PaperTubeCover.parent selectedSource) :=
    data.point_compatibility selectedSource point hselectedSource
  unfold Kakeya.Streamlined.Shading.pointMultiplicity
  apply Finset.card_bij (fun source _ => data.selectedFine.embedding source)
  · intro source hsource
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by
      rw [data.selectedFineShading_eq] at hsource
      exact (Finset.mem_filter.mp hsource).2⟩
  · intro first _ second _ heq
    exact data.selectedFine.embedding.injective heq
  · intro ambientSource hsource
    have hsourceMem := (Finset.mem_filter.mp hsource).2
    let selectedParent :=
      data.restrictedCover.toWZ1PaperTubeCover.parent selectedSource
    have hparentEq := data.ambient_parent_eq_of_mem balanced
      coarseMultiplicityOne selectedParent ambientSource point
      hselectedParent hsourceMem
    have hambientFiber : ambientSource ∈ wz2PaperFullFiberIndices fine coarse
        (selectedCoarse.embedding selectedParent) :=
      (cover.mem_fullFiber_iff_parent
        (selectedCoarse.embedding selectedParent) ambientSource).mpr hparentEq
    have himage : ambientSource ∈ Finset.image data.selectedFine.embedding
        (wz2PaperFullFiberIndices data.selectedFine.family
          selectedCoarse.family selectedParent) := by
      rw [data.full_fiber_complete selectedParent]
      exact hambientFiber
    rcases Finset.mem_image.mp himage with
      ⟨source, _, hembed⟩
    refine ⟨source, ?_, hembed⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [data.selectedFineShading_eq]
    change point ∈ fineShading.carrier (data.selectedFine.embedding source)
    rwa [hembed]

/-- A global fine multiplicity band therefore survives the complete-parent
restriction with exactly the same endpoints. -/
theorem selectedFine_constantMultiplicity
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (coarseMultiplicityOne : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ 1)
    {m M : ℕ}
    (ambientMultiplicity : fineShading.HasConstantMultiplicity m M) :
    data.selectedFineShading.HasConstantMultiplicity m M := by
  intro point hpoint
  rw [data.selectedFine_pointMultiplicity_eq balanced
    coarseMultiplicityOne point hpoint]
  rcases hpoint with ⟨source, hsource⟩
  apply ambientMultiplicity point
  exact ⟨data.selectedFine.embedding source, by
    rw [data.selectedFineShading_eq] at hsource
    exact hsource⟩

/-- Fine-cell nesting also survives complete-parent restriction.  The chosen
coarse cell is the literal grid cell through the retained point, so it is
automatically active for the selected coarse shading. -/
theorem selectedFine_cell_nested
    {ambientBase :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (balanced : PureWZ2Node5BalancedCoverData ambientBase)
    (hrho : 0 < rho) :
    ∀ source point, point ∈ data.selectedFineShading.carrier source →
      ∃ cell ∈ wz1PaperActiveCells data.selectedCoarseShading hrho,
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          wz1PaperGridCube rho cell := by
  intro source point hpoint
  have hambientPoint : point ∈ fineShading.carrier
      (data.selectedFine.embedding source) := by
    rw [data.selectedFineShading_eq] at hpoint
    exact hpoint
  rcases balanced.fine_cell_nested
      (data.selectedFine.embedding source) point hambientPoint with
    ⟨cell, _hcell, hnested⟩
  have hpointFineCell : point ∈
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) :=
    (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta point) point).mpr rfl
  have hpointCell : point ∈ wz1PaperGridCube rho cell :=
    hnested hpointFineCell
  have hindex : wz1PaperGridIndex rho point = cell :=
    (mem_wz1PaperGridCube rho cell point).mp hpointCell
  have hselectedCoarse : point ∈ data.selectedCoarseShading.carrier
      (data.restrictedCover.toWZ1PaperTubeCover.parent source) :=
    data.point_compatibility source point hpoint
  have hbody := data.selectedCoarseShading.subset_body
    (data.restrictedCover.toWZ1PaperTubeCover.parent source) hselectedCoarse
  have hwindow : wz1PaperGridIndex rho point ∈
      wz1PaperGridIndicesInWindow rho hrho :=
    paper_point_gridIndex_in_window hrho hbody.2
  have hactive : wz1PaperGridIndex rho point ∈
      wz1PaperActiveCells data.selectedCoarseShading hrho := by
    apply (mem_wz1PaperActiveCells data.selectedCoarseShading hrho _).mpr
    exact ⟨hwindow, ⟨point, ⟨_, hselectedCoarse⟩,
      (mem_wz1PaperGridCube rho
        (wz1PaperGridIndex rho point) point).mpr rfl⟩⟩
  refine ⟨wz1PaperGridIndex rho point, hactive, ?_⟩
  rw [hindex]
  exact hnested

/-- Under unique coarse ownership, an ambient exact fine multiplicity
certificate upgrades the restricted balanced cover to the full Node-5
indexed-incidence receipt without changing `cellMass`. -/
noncomputable def toNode5BalancedOfExactMultiplicity
    {ambientBase :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (balanced : PureWZ2Node5BalancedCoverData ambientBase)
    (coarseMultiplicityOne : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ 1)
    (hrho : 0 < rho)
    (m : ℕ) (hm : 0 < m)
    (ambientExact : fineShading.HasConstantMultiplicity m m) :
    PureWZ2Node5BalancedCoverData
      (data.toBalanced ambientBase coarseMultiplicityOne hrho) :=
  (data.toBalanced ambientBase coarseMultiplicityOne hrho)
    |>.toNode5OfExactMultiplicity m hm
      (data.selectedFine_constantMultiplicity ambientBase
        coarseMultiplicityOne ambientExact)
      (data.selectedFine_cell_nested balanced hrho)

/-- Every retained complete fiber has exactly the cardinality of its ambient
counterpart. -/
theorem full_fiber_card_eq
    (parent : Fin selectedCoarse.family.card) :
    (wz2PaperFullFiberIndices data.selectedFine.family
        selectedCoarse.family parent).card =
      (wz2PaperFullFiberIndices fine coarse
        (selectedCoarse.embedding parent)).card := by
  calc
    (wz2PaperFullFiberIndices data.selectedFine.family
        selectedCoarse.family parent).card =
      (Finset.image data.selectedFine.embedding
        (wz2PaperFullFiberIndices data.selectedFine.family
          selectedCoarse.family parent)).card :=
      (Finset.card_image_of_injective _
        data.selectedFine.embedding.injective).symm
    _ = (wz2PaperFullFiberIndices fine coarse
        (selectedCoarse.embedding parent)).card :=
      congrArg Finset.card (data.full_fiber_complete parent)

/-- Complete-parent restriction transports the ambient Node-5 fiber
cardinality comparison without changing its constant. -/
theorem full_fiber_uniform
    (constant : ENNReal)
    (ambientUniform : ∀ first second : Fin coarse.card,
      ((wz2PaperFullFiberIndices fine coarse first).card : ENNReal) ≤
        constant *
          ((wz2PaperFullFiberIndices fine coarse second).card : ENNReal)) :
    ∀ first second : Fin selectedCoarse.family.card,
      ((wz2PaperFullFiberIndices data.selectedFine.family
          selectedCoarse.family first).card : ENNReal) ≤
        constant *
          ((wz2PaperFullFiberIndices data.selectedFine.family
            selectedCoarse.family second).card : ENNReal) := by
  intro first second
  rw [data.full_fiber_card_eq first, data.full_fiber_card_eq second]
  exact ambientUniform
    (selectedCoarse.embedding first) (selectedCoarse.embedding second)

end PureWZ2Node05CompleteParentPullbackData

end Kakeya.Assouad

end
