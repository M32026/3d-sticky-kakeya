import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantOwnerExactificationHelpers

/-! # Exact whole-cell balance inside complete dominant-owner fibers -/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem wz2_paper_dominant_owner_exactification :
    WZ2PaperDominantOwnerExactificationStatement := by
  intro delta rho hdelta hrho fine coarse cover sourceShading coarseCells
    availableFineCells balancing coarseData active multiplicityLevel degree
    dominant owned
  let f : WZ2PaperCellIndex → ℕ := fun cell =>
    (owned.ownedFineCells cell).card
  let s : Finset WZ2PaperCellIndex := dominant.selectedCells
  have hs : s.Nonempty := dominant.selectedCells_nonempty
  have hpos : ∀ cell ∈ s, 0 < f cell := by
    intro cell hcell
    exact Finset.card_pos.mpr (owned.ownedFineCells_nonempty cell hcell)
  let total : ℕ := ∑ cell ∈ s, f cell
  let countBins : ℕ := Nat.log 2 (2 * total) + 1
  have hK : ∀ cell ∈ s, Nat.log 2 (f cell) < countBins := by
    intro cell hcell
    have h1 : f cell ≤ total :=
      Finset.single_le_sum (fun index _ => Nat.zero_le (f index)) hcell
    have h2 : f cell ≤ 2 * total := by linarith
    have h3 : Nat.log 2 (f cell) ≤ Nat.log 2 (2 * total) :=
      Nat.log_mono_right h2
    dsimp only [countBins]
    omega
  rcases dyadic_cardinality_pigeonhole s f hs hpos countBins hK with
    ⟨level, retainedCells, hretained_nonempty, hretained_subset, hband,
      hcard⟩
  have hselect :
      ∀ cell ∈ retainedCells,
        ∃ sub : Finset WZ2PaperCellIndex,
          sub ⊆ owned.ownedFineCells cell ∧ sub.card = 2 ^ level := by
    intro cell hcell
    have h1 : 2 ^ level ≤ (owned.ownedFineCells cell).card :=
      (hband cell hcell).1
    exact Finset.exists_subset_card_eq h1
  choose selectedOwnerFineCellsAux hsel_sub_aux hsel_card_aux using hselect
  let selectedOwnerFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex :=
    fun cell =>
      if h : cell ∈ retainedCells then
        selectedOwnerFineCellsAux cell h
      else ∅
  have hsel_sub :
      ∀ cell ∈ retainedCells,
        selectedOwnerFineCells cell ⊆ owned.ownedFineCells cell := by
    intro cell hcell
    simp [selectedOwnerFineCells, hcell]
    <;> exact hsel_sub_aux cell hcell
  have hsel_card :
      ∀ cell ∈ retainedCells,
        (selectedOwnerFineCells cell).card = 2 ^ level := by
    intro cell hcell
    simp [selectedOwnerFineCells, hcell]
    <;> exact hsel_card_aux cell hcell
  let retainedFineCells : Finset WZ2PaperCellIndex :=
    retainedCells.biUnion selectedOwnerFineCells
  let retainedParents : Finset (Fin coarse.card) :=
    retainedCells.image dominant.dominantParent
  have hretainedParents_nonempty : retainedParents.Nonempty :=
    Finset.Nonempty.image hretained_nonempty dominant.dominantParent
  let selectedFineIndices : Finset (Fin fine.card) :=
    Finset.univ.filter fun source =>
      cover.parent source ∈ retainedParents
  let selected : Kakeya.Streamlined.TubeSubfamily fine :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset fine selectedFineIndices
  let coarseSub : Kakeya.Streamlined.TubeSubfamily coarse :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset coarse retainedParents
  let restrictedCover :
      WZ2PaperPartitioningCover selected.family coarseSub.family :=
    cover.restrict retainedParents hretainedParents_nonempty
  have h_restrictedParent_spec :
      ∀ index : Fin selected.family.card,
        coarseSub.embedding (restrictedCover.parent index) =
          cover.parent (selected.embedding index) :=
    cover.restrict_parent_spec retainedParents hretainedParents_nonempty
  let matchingCells (source : Fin fine.card) :
      Finset WZ2PaperCellIndex :=
    retainedCells.filter fun cell =>
      cover.parent source = dominant.dominantParent cell
  let refinedCarrierSet (source : Fin fine.card) : Set Point3 :=
    ⋃ cell ∈ matchingCells source,
      ⋃ fineCell ∈ selectedOwnerFineCells cell,
        wz1PaperGridCube delta fineCell
  have h_refinedCarrierSet_measurable :
      ∀ source, MeasurableSet (refinedCarrierSet source) := by
    intro source
    have h1 :
        ∀ cell ∈ matchingCells source,
          MeasurableSet
            (⋃ fineCell ∈ selectedOwnerFineCells cell,
              wz1PaperGridCube delta fineCell) := by
      intro cell _
      have h2 :
          ∀ fineCell ∈ selectedOwnerFineCells cell,
            MeasurableSet (wz1PaperGridCube delta fineCell) :=
        fun fineCell _ => wz1PaperGridCube_measurable fineCell
      exact Finset.measurableSet_biUnion (selectedOwnerFineCells cell) h2
    exact Finset.measurableSet_biUnion (matchingCells source) h1
  let refined : WZ1PaperTubeShading selected.family :=
    { carrier := fun index =>
        balancing.refined.carrier (selected.embedding index) ∩
          refinedCarrierSet (selected.embedding index)
      measurable_carrier := fun index =>
        (balancing.refined.measurable_carrier
          (selected.embedding index)).inter
          (h_refinedCarrierSet_measurable (selected.embedding index))
      subset_body := fun index =>
        Set.inter_subset_left.trans
          (balancing.refined.subset_body (selected.embedding index)) }
  let coarseShadingCarrier
      (parent : Fin coarseSub.family.card) : Set Point3 :=
    ⋃ cell ∈ retainedCells,
      if coarseSub.embedding parent = dominant.dominantParent cell then
        wz1PaperGridCube rho cell
      else ∅
  have h_coarseShadingCarrier_measurable :
      ∀ parent, MeasurableSet (coarseShadingCarrier parent) := by
    intro parent
    apply Finset.measurableSet_biUnion
    intro cell _
    by_cases h :
        coarseSub.embedding parent = dominant.dominantParent cell
    · rw [if_pos h]
      exact wz1PaperGridCube_measurable cell
    · rw [if_neg h]
      exact MeasurableSet.empty
  have h_coarseShadingCarrier_subset_body :
      ∀ parent : Fin coarseSub.family.card,
        coarseShadingCarrier parent ⊆
          wz1PaperTubeCarrier (coarseSub.family.tube parent) := by
    intro parent point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hif⟩
    have h_eq :
        coarseSub.embedding parent = dominant.dominantParent cell := by
      by_cases h :
          coarseSub.embedding parent = dominant.dominantParent cell
      · exact h
      · rw [if_neg h] at hif
        simp at hif
    have hpointcell : point ∈ wz1PaperGridCube rho cell := by
      rw [if_pos h_eq] at hif
      exact hif
    have h_in_balancing : cell ∈ balancing.retainedCoarseCells :=
      dominant.selectedCells_subset (hretained_subset hcell)
    have h_dom :
        dominant.dominantParent cell ∈ active.activeParents cell :=
      dominant.dominantParent_mem cell h_in_balancing
    have h_pcell :
        cell ∈ coarseData.parentCells (dominant.dominantParent cell) := by
      rw [active.activeParents_eq] at h_dom
      simpa using h_dom
    have h_cont :
        wz1PaperGridCube rho cell ⊆
          coarseData.coarseShading.carrier
            (dominant.dominantParent cell) := by
      rw [coarseData.coarseShading_carrier_eq
        (dominant.dominantParent cell)]
      exact Set.subset_biUnion_of_mem h_pcell
    have h_body :
        coarseData.coarseShading.carrier
            (dominant.dominantParent cell) ⊆
          wz1PaperTubeCarrier
            (coarse.tube (dominant.dominantParent cell)) :=
      coarseData.coarseShading.subset_body
        (dominant.dominantParent cell)
    have h_tube_eq :
        coarseSub.family.tube parent =
          coarse.tube (dominant.dominantParent cell) := by
      rw [coarseSub.tube_eq, h_eq]
    rw [h_tube_eq]
    exact h_body (h_cont hpointcell)
  let coarseShading : WZ1PaperTubeShading coarseSub.family :=
    { carrier := coarseShadingCarrier
      measurable_carrier := h_coarseShadingCarrier_measurable
      subset_body := h_coarseShadingCarrier_subset_body }
  let balanced_cellMass : ENNReal :=
    (2 ^ level : ENNReal) * active.fiberCellMass
  have h_refined_carrier_eq :
      ∀ index,
        refined.carrier index =
          balancing.refined.carrier (selected.embedding index) ∩
          ⋃ cell ∈ retainedCells,
            if
                cover.parent (selected.embedding index) =
                  dominant.dominantParent cell
            then
              ⋃ fineCell ∈ selectedOwnerFineCells cell,
                wz1PaperGridCube delta fineCell
            else ∅ := by
    intro index
    have h_eq :
        refinedCarrierSet (selected.embedding index) =
          ⋃ cell ∈ retainedCells,
            if
                cover.parent (selected.embedding index) =
                  dominant.dominantParent cell
            then
              ⋃ fineCell ∈ selectedOwnerFineCells cell,
                wz1PaperGridCube delta fineCell
            else ∅ := by
      ext point
      constructor
      · intro h
        rcases Set.mem_iUnion₂.mp h with
          ⟨cell, hcellcond, hpointcell⟩
        have hfilter := Finset.mem_filter.mp hcellcond
        have hcell : cell ∈ retainedCells := hfilter.1
        have hcond :
            cover.parent (selected.embedding index) =
              dominant.dominantParent cell :=
          hfilter.2
        rcases Set.mem_iUnion₂.mp hpointcell with
          ⟨fineCell, hfc, hpoint⟩
        exact Set.mem_iUnion₂.mpr
          ⟨cell, hcell, by
            rw [if_pos hcond]
            exact Set.mem_iUnion₂.mpr ⟨fineCell, hfc, hpoint⟩⟩
      · intro h
        rcases Set.mem_iUnion₂.mp h with ⟨cell, hcell, hif⟩
        by_cases hcond :
            cover.parent (selected.embedding index) =
              dominant.dominantParent cell
        · rw [if_pos hcond] at hif
          rcases Set.mem_iUnion₂.mp hif with
            ⟨fineCell, hfc, hpoint⟩
          have h_in_matching :
              cell ∈ matchingCells (selected.embedding index) := by
            simp only [matchingCells, Finset.mem_filter]
            exact ⟨hcell, hcond⟩
          exact Set.mem_iUnion₂.mpr
            ⟨cell, h_in_matching,
              Set.mem_iUnion₂.mpr ⟨fineCell, hfc, hpoint⟩⟩
        · rw [if_neg hcond] at hif
          simp at hif
    have h_def :
        refined.carrier index =
          balancing.refined.carrier (selected.embedding index) ∩
            refinedCarrierSet (selected.embedding index) := by
      rfl
    rw [h_def, h_eq]
  have h_refined_cubical :
      WZ1PaperIsCubicalShading refined := by
    intro index point hpoint
    have h1 :
        point ∈ balancing.refined.carrier (selected.embedding index) :=
      hpoint.1
    have h2 :
        point ∈ refinedCarrierSet (selected.embedding index) :=
      hpoint.2
    rcases Set.mem_iUnion₂.mp h2 with
      ⟨cell, hcellcond, hpointcell⟩
    have hfilter := Finset.mem_filter.mp hcellcond
    have hcell : cell ∈ retainedCells := hfilter.1
    have hcond :
        cover.parent (selected.embedding index) =
          dominant.dominantParent cell :=
      hfilter.2
    rcases Set.mem_iUnion₂.mp hpointcell with
      ⟨fineCell, hfc, hpointfc⟩
    have hidx : wz1PaperGridIndex delta point = fineCell :=
      (mem_wz1PaperGridCube delta fineCell point).mp hpointfc
    have hcube_sub :
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          balancing.refined.carrier (selected.embedding index) :=
      balancing.refined_cubical (selected.embedding index) point h1
    have h_in_matching :
        cell ∈ matchingCells (selected.embedding index) := by
      simp only [matchingCells, Finset.mem_filter]
      exact ⟨hcell, hcond⟩
    have hcube_in_U :
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          refinedCarrierSet (selected.embedding index) := by
      rw [hidx]
      intro other other_mem
      exact Set.mem_iUnion₂.mpr
        ⟨cell, h_in_matching,
          Set.mem_iUnion₂.mpr ⟨fineCell, hfc, other_mem⟩⟩
    intro other other_mem
    exact ⟨hcube_sub other_mem, hcube_in_U other_mem⟩
  have h_owned_union_for_cell :
      ∀ cell ∈ retainedCells,
        (⋃ fineCell ∈ selectedOwnerFineCells cell,
          wz1PaperGridCube delta fineCell) ⊆
        (restrictPaperShading
          (cover.fullFiberSubfamily (dominant.dominantParent cell))
          balancing.refined).union := by
    intro cell hcell
    let fiberSub :=
      cover.fullFiberSubfamily (dominant.dominantParent cell)
    let restrictedFiberShading :=
      restrictPaperShading fiberSub balancing.refined
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨fineCell, hfc, hpointfc⟩
    have h_owned :
        fineCell ∈ owned.ownedFineCells cell :=
      hsel_sub cell hcell hfc
    have h_filter :
        fineCell ∈
          Finset.filter
            (fun candidate : WZ2PaperCellIndex =>
              (wz1PaperGridCube delta candidate ∩
                restrictedFiberShading.union).Nonempty)
            (balancing.selectedFineCells cell) := by
      rw [owned.ownedFineCells_eq cell] at h_owned
      exact h_owned
    have h_nonempty :
        (wz1PaperGridCube delta fineCell ∩
          restrictedFiberShading.union).Nonempty :=
      (Finset.mem_filter.mp h_filter).2
    rcases h_nonempty with ⟨sourcePoint, source_cube, source_union⟩
    rcases source_union with ⟨source, source_carrier⟩
    have source_index :
        wz1PaperGridIndex delta sourcePoint = fineCell :=
      (mem_wz1PaperGridCube delta fineCell sourcePoint).mp source_cube
    have cube_subset :
        wz1PaperGridCube delta fineCell ⊆
          balancing.refined.carrier (fiberSub.embedding source) := by
      rw [← source_index]
      exact
        balancing.refined_cubical
          (fiberSub.embedding source) sourcePoint source_carrier
    have point_carrier :
        point ∈ balancing.refined.carrier (fiberSub.embedding source) :=
      cube_subset hpointfc
    exact ⟨source, point_carrier⟩
  let fullUnionSet : Set Point3 :=
    ⋃ cell ∈ retainedCells,
      ⋃ fineCell ∈ selectedOwnerFineCells cell,
        wz1PaperGridCube delta fineCell
  have h_refined_union_eq : refined.union = fullUnionSet := by
    ext point
    simp only [Kakeya.Streamlined.Shading.union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨index, hpoint⟩
      have h2 :
          point ∈ refinedCarrierSet (selected.embedding index) :=
        hpoint.2
      rcases Set.mem_iUnion₂.mp h2 with
        ⟨cell, hcellcond, hpointcell⟩
      have hfilter := Finset.mem_filter.mp hcellcond
      have hcell : cell ∈ retainedCells := hfilter.1
      rcases Set.mem_iUnion₂.mp hpointcell with
        ⟨fineCell, hfc, hpointfc⟩
      exact Set.mem_iUnion₂.mpr
        ⟨cell, hcell,
          Set.mem_iUnion₂.mpr ⟨fineCell, hfc, hpointfc⟩⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨cell, hcell, hpointcell⟩
      rcases Set.mem_iUnion₂.mp hpointcell with
        ⟨fineCell, hfc, hpointfc⟩
      let fiberSub :=
        cover.fullFiberSubfamily (dominant.dominantParent cell)
      let restrictedFiberShading :=
        restrictPaperShading fiberSub balancing.refined
      have h_in_union : point ∈ restrictedFiberShading.union :=
        h_owned_union_for_cell cell hcell hpointcell
      rcases h_in_union with ⟨source, hsource⟩
      have h_parent :
          cover.parent (fiberSub.embedding source) =
            dominant.dominantParent cell := by
        have h_mem :
            fiberSub.embedding source ∈
              wz2PaperFullFiberIndices fine coarse
                (dominant.dominantParent cell) :=
          Finset.orderEmbOfFin_mem _ _ _
        exact
          (cover.mem_fullFiber_iff_parent _ _).mp h_mem
      have h_sel :
          fiberSub.embedding source ∈ selectedFineIndices := by
        simp only [selectedFineIndices, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rw [h_parent]
        exact Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
      let index : Fin selected.family.card :=
        (selectedFineIndices.orderIsoOfFin rfl).symm
          ⟨fiberSub.embedding source, h_sel⟩
      have embedding_eq :
          selected.embedding index = fiberSub.embedding source := by
        have h3 :
            (selectedFineIndices.orderIsoOfFin rfl) index =
              ⟨fiberSub.embedding source, h_sel⟩ :=
          (selectedFineIndices.orderIsoOfFin rfl).apply_symm_apply _
        exact congrArg Subtype.val h3
      have h1 :
          point ∈ balancing.refined.carrier (selected.embedding index) := by
        rw [embedding_eq]
        exact hsource
      have h2 :
          point ∈ refinedCarrierSet (selected.embedding index) := by
        have h_in_matching :
            cell ∈ matchingCells (selected.embedding index) := by
          simp only [matchingCells, Finset.mem_filter]
          exact ⟨hcell, by rw [embedding_eq, h_parent]⟩
        exact Set.mem_iUnion₂.mpr
          ⟨cell, h_in_matching,
            Set.mem_iUnion₂.mpr ⟨fineCell, hfc, hpointfc⟩⟩
      exact ⟨index, ⟨h1, h2⟩⟩
  have h_coarse_cubical :
      WZ1PaperIsCubicalShading coarseShading := by
    intro parent point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hif⟩
    have h_eq :
        coarseSub.embedding parent = dominant.dominantParent cell := by
      by_cases h :
          coarseSub.embedding parent = dominant.dominantParent cell
      · exact h
      · rw [if_neg h] at hif
        simp at hif
    have hpointcell : point ∈ wz1PaperGridCube rho cell := by
      rw [if_pos h_eq] at hif
      exact hif
    have point_index : wz1PaperGridIndex rho point = cell :=
      (mem_wz1PaperGridCube rho cell point).mp hpointcell
    intro other other_mem
    rw [point_index] at other_mem
    exact Set.mem_iUnion₂.mpr
      ⟨cell, hcell, by rw [if_pos h_eq]; exact other_mem⟩
  have h_coarse_union_eq :
      coarseShading.union =
        ⋃ cell ∈ retainedCells, wz1PaperGridCube rho cell := by
    ext point
    simp only [Kakeya.Streamlined.Shading.union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨parent, hpoint⟩
      rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hif⟩
      have h_eq :
          coarseSub.embedding parent = dominant.dominantParent cell := by
        by_cases h :
            coarseSub.embedding parent = dominant.dominantParent cell
        · exact h
        · rw [if_neg h] at hif
          simp at hif
      have hpointcell : point ∈ wz1PaperGridCube rho cell := by
        rw [if_pos h_eq] at hif
        exact hif
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointcell⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨cell, hcell, hpointcell⟩
      have parent_mem :
          dominant.dominantParent cell ∈ retainedParents :=
        Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
      let parent : Fin coarseSub.family.card :=
        (retainedParents.orderIsoOfFin rfl).symm
          ⟨dominant.dominantParent cell, parent_mem⟩
      have embedding_eq :
          coarseSub.embedding parent = dominant.dominantParent cell := by
        have h3 :
            (retainedParents.orderIsoOfFin rfl) parent =
              ⟨dominant.dominantParent cell, parent_mem⟩ :=
          (retainedParents.orderIsoOfFin rfl).apply_symm_apply _
        exact congrArg Subtype.val h3
      have point_mem : point ∈ coarseShading.carrier parent := by
        exact Set.mem_iUnion₂.mpr
          ⟨cell, hcell, by
            rw [if_pos embedding_eq]
            exact hpointcell⟩
      exact ⟨parent, point_mem⟩
  have h_fine_cell_containment :
      ∀ cell ∈ retainedCells,
        ∀ fineCell ∈ selectedOwnerFineCells cell,
          wz1PaperGridCube delta fineCell ⊆
            wz1PaperGridCube rho cell := by
    intro cell hcell fineCell hfc
    have h1 : fineCell ∈ owned.ownedFineCells cell :=
      hsel_sub cell hcell hfc
    have h2 : fineCell ∈ balancing.selectedFineCells cell :=
      owned.ownedFineCells_subset cell (hretained_subset hcell) h1
    exact
      balancing.fine_cell_containment
        cell (dominant.selectedCells_subset (hretained_subset hcell))
        fineCell h2
  have h_point_compatibility :
      ∀ source point,
        point ∈ refined.carrier source →
          point ∈ coarseShading.carrier
            (restrictedCover.parent source) := by
    intro source point hpoint
    have h2 :
        point ∈ refinedCarrierSet (selected.embedding source) :=
      hpoint.2
    rcases Set.mem_iUnion₂.mp h2 with
      ⟨cell, hcellcond, hpointcell⟩
    have hfilter := Finset.mem_filter.mp hcellcond
    have hcell : cell ∈ retainedCells := hfilter.1
    have hcond :
        cover.parent (selected.embedding source) =
          dominant.dominantParent cell :=
      hfilter.2
    rcases Set.mem_iUnion₂.mp hpointcell with
      ⟨fineCell, hfc, hpointfc⟩
    have h_fine_cont :
        wz1PaperGridCube delta fineCell ⊆
          wz1PaperGridCube rho cell :=
      h_fine_cell_containment cell hcell fineCell hfc
    have hpoint_rho : point ∈ wz1PaperGridCube rho cell :=
      h_fine_cont hpointfc
    have hparent :
        coarseSub.embedding (restrictedCover.parent source) =
          dominant.dominantParent cell := by
      rw [h_restrictedParent_spec source, hcond]
    exact Set.mem_iUnion₂.mpr
      ⟨cell, hcell, by
        rw [if_pos hparent]
        exact hpoint_rho⟩
  have h_refined_union_inter_cell :
      ∀ cell ∈ retainedCells,
        refined.union ∩ wz1PaperGridCube rho cell =
          ⋃ fineCell ∈ selectedOwnerFineCells cell,
            wz1PaperGridCube delta fineCell := by
    intro cell hcell
    rw [h_refined_union_eq]
    ext point
    constructor
    · intro h
      have point_rho : point ∈ wz1PaperGridCube rho cell := h.2
      rcases Set.mem_iUnion₂.mp h.1 with
        ⟨otherCell, other_mem, other_union⟩
      rcases Set.mem_iUnion₂.mp other_union with
        ⟨fineCell, fine_mem, point_fine⟩
      have containment :
          wz1PaperGridCube delta fineCell ⊆
            wz1PaperGridCube rho otherCell :=
        h_fine_cell_containment
          otherCell other_mem fineCell fine_mem
      have point_other :
          point ∈ wz1PaperGridCube rho otherCell :=
        containment point_fine
      have cell_eq : otherCell = cell := by
        have first :
            wz1PaperGridIndex rho point = otherCell :=
          (mem_wz1PaperGridCube rho otherCell point).mp point_other
        have second :
            wz1PaperGridIndex rho point = cell :=
          (mem_wz1PaperGridCube rho cell point).mp point_rho
        exact first.symm.trans second
      subst cell_eq
      exact Set.mem_iUnion₂.mpr ⟨fineCell, fine_mem, point_fine⟩
    · intro h
      rcases Set.mem_iUnion₂.mp h with
        ⟨fineCell, fine_mem, point_fine⟩
      have containment :
          wz1PaperGridCube delta fineCell ⊆
            wz1PaperGridCube rho cell :=
        h_fine_cell_containment cell hcell fineCell fine_mem
      have point_union : point ∈ fullUnionSet :=
        Set.mem_iUnion₂.mpr
          ⟨cell, hcell,
            Set.mem_iUnion₂.mpr ⟨fineCell, fine_mem, point_fine⟩⟩
      exact ⟨point_union, containment point_fine⟩
  have h_cellMass_pos : 0 < balanced_cellMass := by
    dsimp only [balanced_cellMass]
    have h1 : (2 ^ level : ENNReal) ≠ 0 := by positivity
    have h2 : active.fiberCellMass ≠ 0 :=
      active.fiberCellMass_pos.ne'
    have h3 :
        (2 ^ level : ENNReal) * active.fiberCellMass ≠ 0 := by
      intro h
      rcases mul_eq_zero.mp h with h4 | h4
      · exact h1 h4
      · exact h2 h4
    exact h3.bot_lt
  have h_cellMass_ne_top : balanced_cellMass ≠ ⊤ := by
    dsimp only [balanced_cellMass]
    have h1 : (2 ^ level : ENNReal) ≠ ⊤ := by
      exact_mod_cast (by simp)
    exact ENNReal.mul_ne_top h1 active.fiberCellMass_ne_top
  have h_fine_cell_mass :
      ∀ cell ∈ retainedCells,
        volume (refined.union ∩ wz1PaperGridCube rho cell) =
          balanced_cellMass := by
    intro cell hcell
    rw [h_refined_union_inter_cell cell hcell]
    rw [wz1PaperGridCube_volume_biUnion
      hdelta (selectedOwnerFineCells cell)]
    rw [hsel_card cell hcell]
    simp [balanced_cellMass, active.fiberCellMass_eq]
  let balanced :
      WZ1PaperBalancedCoverData
        restrictedCover.toWZ1PaperTubeCover refined coarseShading :=
    { point_compatibility := h_point_compatibility
      coarse_cubical := h_coarse_cubical
      activeCells := retainedCells
      coarse_union_eq := h_coarse_union_eq
      cellMass := balanced_cellMass
      cellMass_pos := h_cellMass_pos
      cellMass_ne_top := h_cellMass_ne_top
      fine_cell_mass := h_fine_cell_mass }
  have h_owner_surjective :
      ∀ parent ∈ retainedParents,
        ∃ cell ∈ retainedCells,
          dominant.dominantParent cell = parent := by
    intro parent hparent
    rcases Finset.mem_image.mp hparent with ⟨cell, hcell, rfl⟩
    exact ⟨cell, hcell, rfl⟩
  have h_full_fiber_complete :
      ∀ parent : Fin coarseSub.family.card,
        Finset.image selected.embedding
            (wz2PaperFullFiberIndices
              selected.family coarseSub.family parent) =
          wz2PaperFullFiberIndices fine coarse
            (coarseSub.embedding parent) := by
    intro parent
    ext source
    simp only [Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨source', source_mem, rfl⟩
      have parent_eq :
          restrictedCover.parent source' = parent :=
        (restrictedCover.mem_fullFiber_iff_parent parent source').mp
          source_mem
      have ambient_parent :
          cover.parent (selected.embedding source') =
            coarseSub.embedding parent := by
        have h3 :
            coarseSub.embedding (restrictedCover.parent source') =
              cover.parent (selected.embedding source') :=
          h_restrictedParent_spec source'
        rw [parent_eq] at h3
        exact h3.symm
      exact
        (cover.mem_fullFiber_iff_parent
          (coarseSub.embedding parent)
          (selected.embedding source')).mpr ambient_parent
    · intro h
      have ambient_parent :
          cover.parent source = coarseSub.embedding parent :=
        (cover.mem_fullFiber_iff_parent
          (coarseSub.embedding parent) source).mp h
      have source_selected : source ∈ selectedFineIndices := by
        simp only [selectedFineIndices, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rw [ambient_parent]
        exact Finset.orderEmbOfFin_mem retainedParents rfl parent
      let source' : Fin selected.family.card :=
        (selectedFineIndices.orderIsoOfFin rfl).symm
          ⟨source, source_selected⟩
      have embedding_eq : selected.embedding source' = source := by
        have h3 :
            (selectedFineIndices.orderIsoOfFin rfl) source' =
              ⟨source, source_selected⟩ :=
          (selectedFineIndices.orderIsoOfFin rfl).apply_symm_apply _
        exact congrArg Subtype.val h3
      have restricted_parent :
          restrictedCover.parent source' = parent := by
        apply coarseSub.embedding.injective
        have h5 :
            coarseSub.embedding (restrictedCover.parent source') =
              cover.parent (selected.embedding source') :=
          h_restrictedParent_spec source'
        rw [h5, embedding_eq, ambient_parent]
      have restricted_mem :
          source' ∈
            wz2PaperFullFiberIndices
              selected.family coarseSub.family parent :=
        (restrictedCover.mem_fullFiber_iff_parent parent source').mpr
          restricted_parent
      exact ⟨source', restricted_mem, embedding_eq⟩
  have h_refined_owner :
      ∀ index point,
        point ∈ refined.carrier index →
          ∃ cell ∈ retainedCells,
            point ∈ wz1PaperGridCube rho cell ∧
              coarseSub.embedding (restrictedCover.parent index) =
                dominant.dominantParent cell := by
    intro index point hpoint
    have h2 :
        point ∈ refinedCarrierSet (selected.embedding index) :=
      hpoint.2
    rcases Set.mem_iUnion₂.mp h2 with
      ⟨cell, hcellcond, hpointcell⟩
    have hfilter := Finset.mem_filter.mp hcellcond
    have hcell : cell ∈ retainedCells := hfilter.1
    have hcond :
        cover.parent (selected.embedding index) =
          dominant.dominantParent cell :=
      hfilter.2
    rcases Set.mem_iUnion₂.mp hpointcell with
      ⟨fineCell, hfc, hpointfc⟩
    have containment :
        wz1PaperGridCube delta fineCell ⊆
          wz1PaperGridCube rho cell :=
      h_fine_cell_containment cell hcell fineCell hfc
    have point_rho : point ∈ wz1PaperGridCube rho cell :=
      containment hpointfc
    have parent_eq :
        coarseSub.embedding (restrictedCover.parent index) =
          dominant.dominantParent cell := by
      rw [h_restrictedParent_spec index, hcond]
    exact ⟨cell, hcell, point_rho, parent_eq⟩
  have h_refined_mass_lower :
      (retainedCells.card : ENNReal) *
            (2 ^ level : ENNReal) * active.fiberCellMass ≤
        refined.mass := by
    have h1 : volume refined.union ≤ refined.mass :=
      paperShading_union_volume_le_mass refined
    rw [h_refined_union_eq] at h1
    have h_disj :
        ∀ first ∈ retainedCells,
          ∀ second ∈ retainedCells,
            first ≠ second →
              Disjoint
                (selectedOwnerFineCells first)
                (selectedOwnerFineCells second) :=
      fun first first_mem second second_mem hne =>
        selected_fine_cells_disjoint_across_coarse
          hdelta h_fine_cell_containment
          first_mem second_mem hne
    have h2 :
        volume fullUnionSet =
          (retainedCells.card : ENNReal) *
            (2 ^ level : ENNReal) * active.fiberCellMass :=
      selected_fine_cells_union_volume
        hdelta hsel_card h_disj
        active.fiberCellMass active.fiberCellMass_eq
    rw [h2] at h1
    exact h1
  have h_dominant_mass_retention :
      (∑ cell ∈ dominant.selectedCells,
          dominant.dominantMass cell) ≤
        (4 * (2 ^ (multiplicityLevel + 1) : ENNReal) *
          (countBins : ENNReal)) * refined.mass := by
    have h_retained_pos : 0 < retainedCells.card :=
      Finset.card_pos.mpr hretained_nonempty
    rcases hretained_nonempty with ⟨cell0, hcell0⟩
    have h1 :
        ∀ cell ∈ dominant.selectedCells,
          dominant.dominantMass cell ≤
            2 * dominant.dominantCellMass := by
      intro cell hcell
      exact (dominant.dominant_mass_band cell hcell).2
    have h2 :
        (∑ cell ∈ dominant.selectedCells,
            dominant.dominantMass cell) ≤
          (dominant.selectedCells.card : ENNReal) *
            (2 * dominant.dominantCellMass) := by
      calc
        (∑ cell ∈ dominant.selectedCells,
            dominant.dominantMass cell)
            ≤ ∑ _cell ∈ dominant.selectedCells,
                2 * dominant.dominantCellMass := by
          apply Finset.sum_le_sum
          intro cell hcell
          exact h1 cell hcell
        _ =
            (dominant.selectedCells.card : ENNReal) *
              (2 * dominant.dominantCellMass) := by
          simp [Finset.sum_const]
    have h3 :
        (dominant.selectedCells.card : ENNReal) ≤
          (countBins : ENNReal) *
            (retainedCells.card : ENNReal) := by
      exact_mod_cast hcard
    have h4 :
        dominant.dominantCellMass ≤ dominant.dominantMass cell0 :=
      (dominant.dominant_mass_band
        cell0 (hretained_subset hcell0)).1
    have h5 :
        dominant.dominantMass cell0 ≤
          (2 ^ (multiplicityLevel + 1) : ENNReal) *
            ((owned.ownedFineCells cell0).card : ENNReal) *
              active.fiberCellMass :=
      owned.owned_cardinality_lower
        cell0 (hretained_subset hcell0)
    have h6 :
        (owned.ownedFineCells cell0).card < 2 ^ (level + 1) :=
      (hband cell0 hcell0).2
    have h6' :
        ((owned.ownedFineCells cell0).card : ENNReal) <
          (2 ^ (level + 1) : ENNReal) := by
      exact_mod_cast h6
    have h_fiber_ne_zero : active.fiberCellMass ≠ 0 :=
      active.fiberCellMass_pos.ne'
    have h_fiber_ne_top : active.fiberCellMass ≠ ⊤ :=
      active.fiberCellMass_ne_top
    have h_inner :
        ((owned.ownedFineCells cell0).card : ENNReal) *
              active.fiberCellMass <
          (2 ^ (level + 1) : ENNReal) * active.fiberCellMass := by
      have h :=
        ENNReal.mul_lt_mul_right
          h_fiber_ne_zero h_fiber_ne_top h6'
      simpa [mul_comm] using h
    have h_mult_ne_zero :
        (2 ^ (multiplicityLevel + 1) : ENNReal) ≠ 0 := by
      positivity
    have h_mult_ne_top :
        (2 ^ (multiplicityLevel + 1) : ENNReal) ≠ ⊤ := by
      exact_mod_cast (by simp)
    have h_outer :
        (2 ^ (multiplicityLevel + 1) : ENNReal) *
              (((owned.ownedFineCells cell0).card : ENNReal) *
                active.fiberCellMass) <
          (2 ^ (multiplicityLevel + 1) : ENNReal) *
            ((2 ^ (level + 1) : ENNReal) *
              active.fiberCellMass) :=
      ENNReal.mul_lt_mul_right h_mult_ne_zero h_mult_ne_top h_inner
    have h7 :
        dominant.dominantCellMass <
          (2 ^ (multiplicityLevel + 1) : ENNReal) *
            (2 ^ (level + 1) : ENNReal) *
              active.fiberCellMass := by
      calc
        dominant.dominantCellMass
            ≤ dominant.dominantMass cell0 := h4
        _ ≤
            (2 ^ (multiplicityLevel + 1) : ENNReal) *
              ((owned.ownedFineCells cell0).card : ENNReal) *
                active.fiberCellMass := h5
        _ <
            (2 ^ (multiplicityLevel + 1) : ENNReal) *
              (2 ^ (level + 1) : ENNReal) *
                active.fiberCellMass := by
          rw [mul_assoc, mul_assoc]
          exact h_outer
    have h_pow :
        (2 ^ (level + 1) : ENNReal) =
          2 * (2 ^ level : ENNReal) := by
      simp [pow_succ, mul_comm]
    have h_countBins_pos : 0 < countBins := by
      dsimp only [countBins]
      omega
    have h_const_ne_zero :
        (countBins : ENNReal) *
            (retainedCells.card : ENNReal) * 2 ≠ 0 := by
      have count_ne : (countBins : ENNReal) ≠ 0 := by
        exact_mod_cast h_countBins_pos.ne'
      have retained_ne : (retainedCells.card : ENNReal) ≠ 0 := by
        exact_mod_cast h_retained_pos.ne'
      positivity
    have h_const_ne_top :
        (countBins : ENNReal) *
            (retainedCells.card : ENNReal) * 2 ≠ ⊤ := by
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.natCast_ne_top countBins)
          (ENNReal.natCast_ne_top retainedCells.card))
        (by norm_num)
    have h_strict :
        (countBins : ENNReal) *
              (retainedCells.card : ENNReal) * 2 *
                dominant.dominantCellMass <
          (countBins : ENNReal) *
            (retainedCells.card : ENNReal) * 2 *
              ((2 ^ (multiplicityLevel + 1) : ENNReal) *
                (2 ^ (level + 1) : ENNReal) *
                  active.fiberCellMass) :=
      ENNReal.mul_lt_mul_right h_const_ne_zero h_const_ne_top h7
    calc
      (∑ cell ∈ dominant.selectedCells,
          dominant.dominantMass cell)
          ≤
            (dominant.selectedCells.card : ENNReal) *
              (2 * dominant.dominantCellMass) := h2
      _ ≤
          ((countBins : ENNReal) *
            (retainedCells.card : ENNReal)) *
              (2 * dominant.dominantCellMass) := by
        gcongr
      _ =
          (countBins : ENNReal) *
            (retainedCells.card : ENNReal) * 2 *
              dominant.dominantCellMass := by ring
      _ ≤
          (countBins : ENNReal) *
            (retainedCells.card : ENNReal) * 2 *
              ((2 ^ (multiplicityLevel + 1) : ENNReal) *
                (2 ^ (level + 1) : ENNReal) *
                  active.fiberCellMass) :=
        le_of_lt h_strict
      _ =
          (4 * (2 ^ (multiplicityLevel + 1) : ENNReal) *
            (countBins : ENNReal)) *
              ((retainedCells.card : ENNReal) *
                (2 ^ level : ENNReal) * active.fiberCellMass) := by
        rw [h_pow]
        simp [mul_assoc, mul_comm, mul_left_comm]
        ring
      _ ≤
          (4 * (2 ^ (multiplicityLevel + 1) : ENNReal) *
            (countBins : ENNReal)) * refined.mass := by
        gcongr
  have h_parent_fiber_mass_floor :
      ∀ parent : Fin coarseSub.family.card,
        balanced_cellMass ≤
          (restrictPaperShading
            (restrictedCover.fullFiberSubfamily parent)
            refined).mass := by
    intro parent
    have hsurj :
        ∃ cell ∈ retainedCells,
          dominant.dominantParent cell = coarseSub.embedding parent :=
      h_owner_surjective
        (coarseSub.embedding parent)
        (Finset.orderEmbOfFin_mem retainedParents rfl parent)
    rcases hsurj with ⟨cell, hcell, hparent⟩
    let fiberSub := restrictedCover.fullFiberSubfamily parent
    let restrictedFiberShading :=
      restrictPaperShading fiberSub refined
    have h_union_contains :
        (⋃ fineCell ∈ selectedOwnerFineCells cell,
          wz1PaperGridCube delta fineCell) ⊆
            restrictedFiberShading.union := by
      intro point hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨fineCell, hfc, hpointfc⟩
      let ambientFiberSub :=
        cover.fullFiberSubfamily (dominant.dominantParent cell)
      let ambientFiberShading :=
        restrictPaperShading ambientFiberSub balancing.refined
      have h_in_ambient_union : point ∈ ambientFiberShading.union :=
        h_owned_union_for_cell cell hcell hpoint
      rcases h_in_ambient_union with ⟨source, hsource⟩
      have h_parent :
          cover.parent (ambientFiberSub.embedding source) =
            dominant.dominantParent cell := by
        have h_mem :
            ambientFiberSub.embedding source ∈
              wz2PaperFullFiberIndices fine coarse
                (dominant.dominantParent cell) :=
          Finset.orderEmbOfFin_mem _ _ _
        exact (cover.mem_fullFiber_iff_parent _ _).mp h_mem
      have h_sel :
          ambientFiberSub.embedding source ∈ selectedFineIndices := by
        simp only [selectedFineIndices, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rw [h_parent, hparent]
        exact Finset.orderEmbOfFin_mem retainedParents rfl parent
      let index : Fin selected.family.card :=
        (selectedFineIndices.orderIsoOfFin rfl).symm
          ⟨ambientFiberSub.embedding source, h_sel⟩
      have embedding_eq :
          selected.embedding index = ambientFiberSub.embedding source := by
        have h3 :
            (selectedFineIndices.orderIsoOfFin rfl) index =
              ⟨ambientFiberSub.embedding source, h_sel⟩ :=
          (selectedFineIndices.orderIsoOfFin rfl).apply_symm_apply _
        exact congrArg Subtype.val h3
      have h_in_fiber :
          index ∈
            wz2PaperFullFiberIndices
              selected.family coarseSub.family parent := by
        have restricted_parent :
            restrictedCover.parent index = parent := by
          apply coarseSub.embedding.injective
          have h5 :
              coarseSub.embedding (restrictedCover.parent index) =
                cover.parent (selected.embedding index) :=
            h_restrictedParent_spec index
          rw [h5, embedding_eq, h_parent, hparent]
        exact
          (restrictedCover.mem_fullFiber_iff_parent parent index).mpr
            restricted_parent
      let fiberIndex : Fin fiberSub.family.card :=
        (wz2PaperFullFiberIndices
          selected.family coarseSub.family parent).orderIsoOfFin rfl
          |>.symm ⟨index, h_in_fiber⟩
      have fiber_embedding : fiberSub.embedding fiberIndex = index := by
        have h3 :
            (wz2PaperFullFiberIndices
              selected.family coarseSub.family parent).orderIsoOfFin rfl
                fiberIndex =
              ⟨index, h_in_fiber⟩ :=
          (wz2PaperFullFiberIndices
            selected.family coarseSub.family parent).orderIsoOfFin rfl
            |>.apply_symm_apply _
        exact congrArg Subtype.val h3
      have h1 :
          point ∈ balancing.refined.carrier (selected.embedding index) := by
        rw [embedding_eq]
        exact hsource
      have h2 :
          point ∈ refinedCarrierSet (selected.embedding index) := by
        have h_in_matching :
            cell ∈ matchingCells (selected.embedding index) := by
          simp only [matchingCells, Finset.mem_filter]
          exact ⟨hcell, by rw [embedding_eq, h_parent]⟩
        exact Set.mem_iUnion₂.mpr
          ⟨cell, h_in_matching,
            Set.mem_iUnion₂.mpr ⟨fineCell, hfc, hpointfc⟩⟩
      have point_refined : point ∈ refined.carrier index := ⟨h1, h2⟩
      have point_final :
          point ∈ restrictedFiberShading.carrier fiberIndex := by
        simpa [restrictedFiberShading, restrictPaperShading,
          fiber_embedding] using point_refined
      exact ⟨fiberIndex, point_final⟩
    have h_volume :
        volume
            (⋃ fineCell ∈ selectedOwnerFineCells cell,
              wz1PaperGridCube delta fineCell) =
          balanced_cellMass := by
      rw [wz1PaperGridCube_volume_biUnion
        hdelta (selectedOwnerFineCells cell)]
      rw [hsel_card cell hcell]
      simp [balanced_cellMass, active.fiberCellMass_eq]
    have h_mass_ge :
        volume restrictedFiberShading.union ≤
          restrictedFiberShading.mass :=
      paperShading_union_volume_le_mass restrictedFiberShading
    calc
      balanced_cellMass =
          volume
            (⋃ fineCell ∈ selectedOwnerFineCells cell,
              wz1PaperGridCube delta fineCell) :=
        h_volume.symm
      _ ≤ volume restrictedFiberShading.union := by
        gcongr
      _ ≤ restrictedFiberShading.mass := h_mass_ge
  exact
    ⟨{
      countBins := countBins
      countBins_eq := by rfl
      level := level
      retainedCells := retainedCells
      retainedCells_subset := hretained_subset
      retainedCells_nonempty := hretained_nonempty
      owned_count_band := hband
      selectedOwnerFineCells := selectedOwnerFineCells
      selectedOwnerFineCells_subset := hsel_sub
      selectedOwnerFineCells_card := hsel_card
      retainedCells_cardinality := hcard
      retainedFineCells := retainedFineCells
      retainedFineCells_eq := by rfl
      selectedFineIndices := selectedFineIndices
      selectedFineIndices_eq := by rfl
      selected := selected
      selected_eq := by rfl
      refined := refined
      refined_carrier_eq := h_refined_carrier_eq
      refined_cubical := h_refined_cubical
      refined_union_eq := h_refined_union_eq
      retainedParents := retainedParents
      retainedParents_eq := by rfl
      retainedParents_nonempty := hretainedParents_nonempty
      selectedFineIndices_eq_retainedParents := by rfl
      owner_surjective := h_owner_surjective
      restrictedCover := restrictedCover
      full_fiber_complete := h_full_fiber_complete
      coarseShading := coarseShading
      coarse_carrier_eq := by
        intro parent
        rfl
      refined_owner := h_refined_owner
      balanced := balanced
      balanced_activeCells_eq := by rfl
      balanced_cellMass := balanced_cellMass
      balanced_cellMass_eq := by rfl
      dominant_mass_retention := h_dominant_mass_retention
      parent_fiber_mass_floor := h_parent_fiber_mass_floor
    }⟩

end Kakeya.Assouad

end
