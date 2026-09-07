import MyLeanRepo.Kakeya.Assouad.PropStickyPaperParentCellRestrictionStatements

/-!
# Restrict fine shading to selected parent-cell incidences

Restrict every fine tube by the union of the selected literal `rho`-cells
belonging to its unique coarse parent.  Prove cubicality, exact additive mass,
and the resulting logarithmic fine-mass retention.  This intermediate shading
is not asserted to be balanced.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem wz2_paper_parent_cell_restriction :
    WZ2PaperParentCellRestrictionStatement := by
  intro delta rho hdelta hrho fine coarse cover sourceShading coarseCells
    availableFineCells balancing coarseData active fiberBand band

  let selectedCells : Finset WZ2PaperCellIndex :=
    band.retainedPairs.image Prod.fst

  let selectedCellsForParent : Fin coarse.card → Finset WZ2PaperCellIndex :=
    fun parent => selectedCells.filter fun cell => (cell, parent) ∈ band.retainedPairs

  let refined : WZ1PaperTubeShading fine :=
    { carrier := fun source =>
        fiberBand.refined.carrier source ∩
          ⋃ cell ∈ selectedCellsForParent (cover.parent source),
            wz1PaperGridCube rho cell
      measurable_carrier := fun source =>
        (fiberBand.refined.measurable_carrier source).inter
          (by
            apply MeasurableSet.biUnion (Set.Finite.countable (Finset.finite_toSet _))
            intro i _
            exact wz1PaperGridCube_measurable i)
      subset_body := fun source =>
        Set.inter_subset_left.trans (fiberBand.refined.subset_body source)
    }

  have h_pair_iff : ∀ (cell : WZ2PaperCellIndex) (parent : Fin coarse.card),
      cell ∈ selectedCellsForParent parent ↔ (cell, parent) ∈ band.retainedPairs := by
    intro cell parent
    constructor
    · intro h; exact (Finset.mem_filter.mp h).2
    · intro h
      have hcell : cell ∈ selectedCells :=
        Finset.mem_image.mpr ⟨(cell, parent), h, rfl⟩
      exact Finset.mem_filter.mpr ⟨hcell, h⟩

  have h_selectedCells_nonempty : selectedCells.Nonempty :=
    Finset.Nonempty.image band.retainedPairs_nonempty Prod.fst

  have h_selectedCells_subset : selectedCells ⊆ balancing.retainedCoarseCells := by
    intro cell hcell
    rcases Finset.mem_image.mp hcell with ⟨pair, hpair, rfl⟩
    have h_pos : pair ∈ wz2PaperPositiveParentCellPairs active fiberBand.refined :=
      band.retainedPairs_subset hpair
    have h_in_all : pair ∈ wz2PaperParentCellPairs active :=
      (Finset.mem_filter.mp h_pos).1
    have h_in_all' : ∃ c ∈ balancing.retainedCoarseCells,
        ∃ p ∈ active.activeParents c, (c, p) = pair := by
      simpa [wz2PaperParentCellPairs, Finset.mem_biUnion] using h_in_all
    rcases h_in_all' with ⟨c, hc, p, _, rfl⟩
    exact hc

  have h_refined_subshading :
      ∀ source, refined.carrier source ⊆ fiberBand.refined.carrier source := by
    intro source
    exact Set.inter_subset_left

  have h_containment : ∀ source, fiberBand.refined.carrier source ⊆
      ⋃ cell ∈ balancing.retainedCoarseCells, wz1PaperGridCube rho cell := by
    intro source
    have h1 : fiberBand.refined.carrier source ⊆ balancing.refined.carrier source :=
      fiberBand.refined_subshading source
    have h2 : balancing.refined.carrier source ⊆
        coarseData.coarseShading.carrier (cover.parent source) :=
      coarseData.balancedCover.point_compatibility source
    have h3 : coarseData.coarseShading.carrier (cover.parent source) ⊆
        ⋃ cell ∈ balancing.retainedCoarseCells, wz1PaperGridCube rho cell := by
      rw [coarseData.coarseShading_carrier_eq (cover.parent source)]
      intro x hx
      have h_exists : ∃ c, c ∈ coarseData.parentCells (cover.parent source) ∧
          x ∈ wz1PaperGridCube rho c := by
        simpa [Set.mem_biUnion] using hx
      rcases h_exists with ⟨c, hc, hxc⟩
      have h4 : c ∈ balancing.retainedCoarseCells :=
        coarseData.parentCells_subset (cover.parent source) hc
      exact Set.mem_biUnion h4 hxc
    exact subset_trans h1 (subset_trans h2 h3)

  have h_refined_cubical : WZ1PaperIsCubicalShading refined := by
    intro source point hpoint
    let D := wz1PaperGridCube delta (wz1PaperGridIndex delta point)
    have h_in_fiber : point ∈ fiberBand.refined.carrier source := hpoint.1
    have hD_fiber : D ⊆ fiberBand.refined.carrier source :=
      fiberBand.refined_cubical source point h_in_fiber
    have h2 : point ∈
        (⋃ cell ∈ selectedCellsForParent (cover.parent source),
          wz1PaperGridCube rho cell) := hpoint.2
    have h3 : ∃ (cell : WZ2PaperCellIndex),
        cell ∈ selectedCellsForParent (cover.parent source) ∧
          point ∈ wz1PaperGridCube rho cell := by
      simpa [Set.mem_iUnion] using h2
    rcases h3 with ⟨selectedCell, hsel, hpointCell⟩
    have h_in_bal_union : point ∈ balancing.refined.union := by
      have h1 : point ∈ fiberBand.refined.carrier source := h_in_fiber
      have h2 : point ∈ balancing.refined.carrier source :=
        fiberBand.refined_subshading source h1
      exact ⟨source, h2⟩
    have h_fine_exists : ∃ (fineCell : WZ2PaperCellIndex),
        fineCell ∈ balancing.retainedFineCells ∧
          point ∈ wz1PaperGridCube delta fineCell := by
      rw [balancing.refined_union_eq] at h_in_bal_union
      simpa [Set.mem_biUnion] using h_in_bal_union
    rcases h_fine_exists with ⟨fineCell, hfine, hpointFine⟩
    have h_D_eq : D = wz1PaperGridCube delta fineCell := by
      have h1 : wz1PaperGridIndex delta point = fineCell :=
        (mem_wz1PaperGridCube delta fineCell point).mp hpointFine
      simp [D, h1]
    have h_coarse_exists : ∃ (coarseCell : WZ2PaperCellIndex),
        coarseCell ∈ balancing.retainedCoarseCells ∧
          fineCell ∈ balancing.selectedFineCells coarseCell := by
      rw [balancing.retainedFineCells_eq] at hfine
      simpa [Finset.mem_biUnion] using hfine
    rcases h_coarse_exists with ⟨coarseCell, hcoarse, hfineInCoarse⟩
    have h_D_sub_rho : D ⊆ wz1PaperGridCube rho coarseCell := by
      rw [h_D_eq]
      exact balancing.fine_cell_containment coarseCell hcoarse fineCell hfineInCoarse
    have h_point_in_coarse : point ∈ wz1PaperGridCube rho coarseCell :=
      h_D_sub_rho
        ((mem_wz1PaperGridCube delta
          (wz1PaperGridIndex delta point) point).mpr rfl)
    have h_cells_eq : coarseCell = selectedCell := by
      by_contra hne
      have h_disj :
          Disjoint (wz1PaperGridCube rho coarseCell)
            (wz1PaperGridCube rho selectedCell) :=
        wz1PaperGridCube_disjoint hne
      exact Set.disjoint_left.mp h_disj h_point_in_coarse hpointCell
    have h_D_sub_selected : D ⊆ wz1PaperGridCube rho selectedCell := by
      rw [h_cells_eq] at h_D_sub_rho
      exact h_D_sub_rho
    intro point' hpoint'
    have h1 : point' ∈ fiberBand.refined.carrier source := hD_fiber hpoint'
    have h2 : point' ∈ wz1PaperGridCube rho selectedCell :=
      h_D_sub_selected hpoint'
    exact ⟨h1, Set.mem_biUnion hsel h2⟩

  have h_refined_union_subset :
      refined.union ⊆ ⋃ cell ∈ selectedCells, wz1PaperGridCube rho cell := by
    intro point hpoint
    rcases hpoint with ⟨source, hsource⟩
    have h2 : ∃ (cell : WZ2PaperCellIndex),
        cell ∈ selectedCellsForParent (cover.parent source) ∧
          point ∈ wz1PaperGridCube rho cell := by
      simpa [Set.mem_iUnion] using hsource.2
    rcases h2 with ⟨cell, hcell, hpointCell⟩
    have h_pair_in : (cell, cover.parent source) ∈ band.retainedPairs :=
      (h_pair_iff cell (cover.parent source)).mp hcell
    have h_cell_in_selected : cell ∈ selectedCells :=
      Finset.mem_image.mpr
        ⟨(cell, cover.parent source), h_pair_in, rfl⟩
    exact Set.mem_biUnion h_cell_in_selected hpointCell

  have h_parentCellMass_eq :
      ∀ (cell : WZ2PaperCellIndex) (parent : Fin coarse.card),
        wz2PaperParentCellMass cover fiberBand.refined (cell, parent) =
          ∑ source ∈ cover.fiberIndices parent,
            volume
              (fiberBand.refined.carrier source ∩
                wz1PaperGridCube rho cell) := by
    intro cell parent
    dsimp only [wz2PaperParentCellMass, restrictPaperShading]
    let indices := wz2PaperFullFiberIndices fine coarse parent
    let equivalence : Fin indices.card ≃ indices :=
      (indices.orderIsoOfFin rfl).toEquiv
    calc
      ∑ index : Fin (cover.fullFiberSubfamily parent).family.card,
          volume
            (fiberBand.refined.carrier
                ((cover.fullFiberSubfamily parent).embedding index) ∩
              wz1PaperGridCube rho cell)
        = ∑ source : indices,
            volume
              (fiberBand.refined.carrier source.val ∩
                wz1PaperGridCube rho cell) := by
          exact Fintype.sum_equiv equivalence
            (fun index =>
              volume
                (fiberBand.refined.carrier
                    ((cover.fullFiberSubfamily parent).embedding index) ∩
                  wz1PaperGridCube rho cell))
            (fun source =>
              volume
                (fiberBand.refined.carrier source.val ∩
                  wz1PaperGridCube rho cell))
            (fun _ => rfl)
      _ = ∑ source ∈ indices,
          volume
            (fiberBand.refined.carrier source ∩
              wz1PaperGridCube rho cell) := by
          exact Finset.sum_coe_sort indices fun source =>
            volume
              (fiberBand.refined.carrier source ∩
                wz1PaperGridCube rho cell)
      _ = ∑ source ∈ cover.fiberIndices parent,
          volume
            (fiberBand.refined.carrier source ∩
              wz1PaperGridCube rho cell) := by
          exact Finset.sum_congr
            (cover.fullFiberIndices_eq parent) (fun _ _ => rfl)

  have h_vol_decomp_refined : ∀ source,
      volume (refined.carrier source) =
        ∑ cell ∈ selectedCellsForParent (cover.parent source),
          volume
            (fiberBand.refined.carrier source ∩
              wz1PaperGridCube rho cell) := by
    intro source
    let A := fiberBand.refined.carrier source
    let S := selectedCellsForParent (cover.parent source)
    have h_disj : ∀ c1 ∈ S, ∀ c2 ∈ S, c1 ≠ c2 →
        Disjoint (A ∩ wz1PaperGridCube rho c1)
          (A ∩ wz1PaperGridCube rho c2) := by
      intro c1 _ c2 _ hne
      have h : Disjoint (wz1PaperGridCube rho c1)
          (wz1PaperGridCube rho c2) :=
        wz1PaperGridCube_disjoint hne
      exact h.mono (fun x hx => hx.2) (fun x hx => hx.2)
    have h_eq : refined.carrier source =
        ⋃ cell ∈ S, (A ∩ wz1PaperGridCube rho cell) := by
      ext x
      simp only [refined, Set.mem_inter_iff, Set.mem_iUnion]
      tauto
    rw [h_eq]
    exact MeasureTheory.measure_biUnion_finset h_disj
      (fun _ _ =>
        (fiberBand.refined.measurable_carrier source).inter
          (wz1PaperGridCube_measurable _))

  have h_fiber_sum : ∀ (parent : Fin coarse.card),
      ∑ source ∈ cover.fiberIndices parent,
          volume (refined.carrier source) =
        ∑ cell ∈ selectedCellsForParent parent,
          wz2PaperParentCellMass cover fiberBand.refined
            (cell, parent) := by
    intro parent
    have h1 : ∑ source ∈ cover.fiberIndices parent,
          volume (refined.carrier source) =
        ∑ source ∈ cover.fiberIndices parent,
          ∑ cell ∈ selectedCellsForParent parent,
            volume
              (fiberBand.refined.carrier source ∩
                wz1PaperGridCube rho cell) := by
      apply Finset.sum_congr rfl
      intro source hsource
      have h_parent : cover.parent source = parent := by
        simpa [WZ1PaperTubeCover.fiberIndices,
          Finset.mem_filter, Finset.mem_univ] using hsource
      have h_vol : volume (refined.carrier source) =
          ∑ cell ∈ selectedCellsForParent (cover.parent source),
            volume
              (fiberBand.refined.carrier source ∩
                wz1PaperGridCube rho cell) :=
        h_vol_decomp_refined source
      have h_vol2 :
          ∑ cell ∈ selectedCellsForParent (cover.parent source),
              volume
                (fiberBand.refined.carrier source ∩
                  wz1PaperGridCube rho cell) =
            ∑ cell ∈ selectedCellsForParent parent,
              volume
                (fiberBand.refined.carrier source ∩
                  wz1PaperGridCube rho cell) := by
        rw [h_parent]
      rw [h_vol, h_vol2]
    rw [h1]
    have h2 :
        ∑ source ∈ cover.fiberIndices parent,
            ∑ cell ∈ selectedCellsForParent parent,
              volume
                (fiberBand.refined.carrier source ∩
                  wz1PaperGridCube rho cell) =
          ∑ cell ∈ selectedCellsForParent parent,
            ∑ source ∈ cover.fiberIndices parent,
              volume
                (fiberBand.refined.carrier source ∩
                  wz1PaperGridCube rho cell) := by
      rw [Finset.sum_comm]
    rw [h2]
    apply Finset.sum_congr rfl
    intro cell _
    rw [h_parentCellMass_eq cell parent]

  have h_all_selected_pairs_eq :
      (Finset.biUnion (Finset.univ : Finset (Fin coarse.card))
        (fun parent =>
          (selectedCellsForParent parent).image
            (fun cell => (cell, parent)))) =
        band.retainedPairs := by
    ext pair
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · rintro ⟨p, c, hc, h_eq⟩
      have h1 : (c, p) = pair := h_eq
      rw [← h1]
      exact (h_pair_iff c p).mp hc
    · intro h
      refine ⟨pair.2, pair.1,
        (h_pair_iff pair.1 pair.2).mpr h, rfl⟩

  have h_sum_biUnion :
      ∑ pair ∈
          (Finset.biUnion (Finset.univ : Finset (Fin coarse.card))
            (fun parent =>
              (selectedCellsForParent parent).image
                (fun cell => (cell, parent)))),
        wz2PaperParentCellMass cover fiberBand.refined pair =
      ∑ parent : Fin coarse.card,
        ∑ cell ∈ selectedCellsForParent parent,
          wz2PaperParentCellMass cover fiberBand.refined
            (cell, parent) := by
    have h_disj : ∀ p1 ∈ (Finset.univ : Finset (Fin coarse.card)),
        ∀ p2 ∈ (Finset.univ : Finset (Fin coarse.card)), p1 ≠ p2 →
          Disjoint
            ((selectedCellsForParent p1).image (fun cell => (cell, p1)))
            ((selectedCellsForParent p2).image
              (fun cell => (cell, p2))) := by
      intro p1 _ p2 _ hne
      rw [Finset.disjoint_left]
      intro pair h1 h2
      rcases Finset.mem_image.mp h1 with ⟨c1, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨c2, _, h_eq⟩
      injection h_eq with _ h_parent
      exact hne h_parent.symm
    rw [Finset.sum_biUnion h_disj]
    apply Finset.sum_congr rfl
    intro parent _
    rw [Finset.sum_image]
    intro x y _ _ h
    injection h

  have h_refined_mass_eq :
      refined.mass =
        ∑ pair ∈ band.retainedPairs,
          wz2PaperParentCellMass cover fiberBand.refined pair := by
    have h_fiber_eq : ∀ parent : Fin coarse.card,
        cover.fiberIndices parent =
          Finset.univ.filter
            (fun source => cover.parent source = parent) := by
      intro parent
      ext source
      simp [WZ1PaperTubeCover.fiberIndices, Finset.mem_filter,
        Finset.mem_univ]
    calc
      refined.mass =
          ∑ source : Fin fine.card,
            volume (refined.carrier source) := by rfl
      _ = ∑ parent : Fin coarse.card,
            ∑ source ∈ cover.fiberIndices parent,
              volume (refined.carrier source) := by
          simp_rw [h_fiber_eq]
          rw [Finset.sum_fiberwise_of_maps_to
            (s := Finset.univ) (t := Finset.univ)
            (g := cover.parent)
            (fun _ _ => Finset.mem_univ _)]
      _ = ∑ parent : Fin coarse.card,
            ∑ cell ∈ selectedCellsForParent parent,
              wz2PaperParentCellMass cover fiberBand.refined
                (cell, parent) := by
          apply Finset.sum_congr rfl
          intro parent _
          exact h_fiber_sum parent
      _ = ∑ pair ∈
            (Finset.biUnion
              (Finset.univ : Finset (Fin coarse.card))
              (fun parent =>
                (selectedCellsForParent parent).image
                  (fun cell => (cell, parent)))),
            wz2PaperParentCellMass cover fiberBand.refined pair := by
          exact h_sum_biUnion.symm
      _ = ∑ pair ∈ band.retainedPairs,
            wz2PaperParentCellMass cover fiberBand.refined pair := by
          rw [h_all_selected_pairs_eq]

  have h_vol_decomp_ambient : ∀ source,
      volume (fiberBand.refined.carrier source) =
        ∑ cell ∈ balancing.retainedCoarseCells,
          volume
            (fiberBand.refined.carrier source ∩
              wz1PaperGridCube rho cell) := by
    intro source
    let A := fiberBand.refined.carrier source
    have hA_subset : A ⊆
        ⋃ cell ∈ balancing.retainedCoarseCells,
          wz1PaperGridCube rho cell :=
      h_containment source
    have h_disj : ∀ c1 ∈ balancing.retainedCoarseCells,
        ∀ c2 ∈ balancing.retainedCoarseCells, c1 ≠ c2 →
          Disjoint (A ∩ wz1PaperGridCube rho c1)
            (A ∩ wz1PaperGridCube rho c2) := by
      intro c1 _ c2 _ hne
      have h : Disjoint (wz1PaperGridCube rho c1)
          (wz1PaperGridCube rho c2) :=
        wz1PaperGridCube_disjoint hne
      exact h.mono (fun x hx => hx.2) (fun x hx => hx.2)
    have h_inter_union :
        A ∩
            (⋃ cell ∈ balancing.retainedCoarseCells,
              wz1PaperGridCube rho cell) =
          ⋃ cell ∈ balancing.retainedCoarseCells,
            (A ∩ wz1PaperGridCube rho cell) := by
      ext x
      simp
    have h_eq : A =
        ⋃ cell ∈ balancing.retainedCoarseCells,
          (A ∩ wz1PaperGridCube rho cell) := by
      have h' :
          A ∩
              (⋃ cell ∈ balancing.retainedCoarseCells,
                wz1PaperGridCube rho cell) =
            A := by
        rw [Set.inter_eq_left.mpr hA_subset]
      rw [h_inter_union] at h'
      exact h'.symm
    have h_vol : volume A =
        ∑ cell ∈ balancing.retainedCoarseCells,
          volume (A ∩ wz1PaperGridCube rho cell) := by
      let B :=
        ⋃ cell ∈ balancing.retainedCoarseCells,
          (A ∩ wz1PaperGridCube rho cell)
      have h_eqB : A = B := h_eq
      have h1 : volume A = volume B := congr_arg volume h_eqB
      rw [h1]
      exact MeasureTheory.measure_biUnion_finset h_disj
        (fun _ _ =>
          (fiberBand.refined.measurable_carrier source).inter
            (wz1PaperGridCube_measurable _))
    simpa [A] using h_vol

  have h_total_eq_mass :
      (∑ cell ∈ balancing.retainedCoarseCells,
          wz2PaperCellIncidenceMass
            (rho := rho) fiberBand.refined cell) =
        fiberBand.refined.mass := by
    dsimp only [wz2PaperCellIncidenceMass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro source _
    exact (h_vol_decomp_ambient source).symm

  have h_ambient_mass_eq :
      fiberBand.refined.mass =
        ∑ pair ∈
            wz2PaperPositiveParentCellPairs active fiberBand.refined,
          wz2PaperParentCellMass cover fiberBand.refined pair := by
    exact Eq.trans h_total_eq_mass.symm band.total_pair_mass_eq.symm

  have h_retained_mass :
      fiberBand.refined.mass /
          (2 *
            (Nat.log 2
              (2 *
                (wz2PaperPositiveParentCellPairs
                  active fiberBand.refined).card) + 1) :
            ENNReal) ≤
        refined.mass := by
    rw [h_ambient_mass_eq, h_refined_mass_eq]
    exact band.retained_mass

  have h_fiber_multiplicity_band :
      ∀ parent point,
        point ∈
            (restrictPaperShading
              (cover.fullFiberSubfamily parent) refined).union →
          (2 ^ fiberBand.level : ENNReal) ≤
              ((restrictPaperShading
                (cover.fullFiberSubfamily parent)
                refined).pointMultiplicity point : ENNReal) ∧
          ((restrictPaperShading
            (cover.fullFiberSubfamily parent)
            refined).pointMultiplicity point : ENNReal) <
            (2 ^ (fiberBand.level + 1) : ENNReal) := by
    intro parent point hpoint
    let S := cover.fullFiberSubfamily parent
    let R := restrictPaperShading S refined
    let F := restrictPaperShading S fiberBand.refined
    rcases hpoint with ⟨j, hj⟩
    have h_j_in : point ∈ refined.carrier (S.embedding j) := hj
    have h2 : ∃ (cell : WZ2PaperCellIndex),
        cell ∈ selectedCellsForParent parent ∧
          point ∈ wz1PaperGridCube rho cell := by
      have h_parent : cover.parent (S.embedding j) = parent :=
        (cover.mem_fullFiber_iff_parent parent (S.embedding j)).mp
          (cover.fullFiberSubfamily_mem parent j)
      have h_union : point ∈
          (⋃ cell ∈ selectedCellsForParent
              (cover.parent (S.embedding j)),
            wz1PaperGridCube rho cell) :=
        h_j_in.2
      rw [h_parent] at h_union
      simpa [Set.mem_iUnion] using h_union
    rcases h2 with ⟨cell, hcell, hpointCell⟩
    have h_iff : ∀ (i : Fin S.family.card),
        point ∈ R.carrier i ↔ point ∈ F.carrier i := by
      intro i
      simp only [R, F, restrictPaperShading]
      constructor
      · intro h
        exact h.1
      · intro h
        have h_parent_i : cover.parent (S.embedding i) = parent :=
          (cover.mem_fullFiber_iff_parent parent (S.embedding i)).mp
            (cover.fullFiberSubfamily_mem parent i)
        have h_union : point ∈
            (⋃ cell ∈ selectedCellsForParent
                (cover.parent (S.embedding i)),
              wz1PaperGridCube rho cell) := by
          rw [h_parent_i]
          exact Set.mem_biUnion hcell hpointCell
        exact ⟨h, h_union⟩
    have h_multiplicity_eq :
        R.pointMultiplicity point = F.pointMultiplicity point := by
      simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
      congr 1
      apply Finset.filter_congr
      intro i _
      exact h_iff i
    have h_in_F_union : point ∈ F.union := by
      exact ⟨j, (h_iff j).mp hj⟩
    rw [h_multiplicity_eq]
    exact fiberBand.fiber_multiplicity_band parent point h_in_F_union

  exact ⟨selectedCells, rfl, h_selectedCells_nonempty,
    h_selectedCells_subset, selectedCellsForParent, (fun _ => rfl),
    refined, (fun _ => rfl), h_refined_subshading,
    h_refined_cubical, h_refined_union_subset, h_refined_mass_eq,
    h_ambient_mass_eq, h_retained_mass, h_fiber_multiplicity_band⟩

end Kakeya.Assouad

end
