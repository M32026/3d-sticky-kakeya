import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-! # Final fine exact balancing before inducing coarse shading -/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Finset

attribute [local instance] Classical.propDecidable

theorem wz2_paper_final_fine_exact_balancing :
    WZ2PaperFinalFineExactBalancingStatement := by
  intro delta rho hdelta hrho fine coarse cover sourceShading coarseCells
    availableFineCells balancing coarseData active fiberBand pairBand restriction
  classical
  rcases paperDyadicBandPigeonhole restriction.refined_cubical with
    ⟨fineLevel, hfineBand_cubical, hfineBand_mass_retention,
      hfineBand_multiplicity⟩
  let fineBand :=
    wz1PaperDyadicBandSubshading restriction.refined fineLevel
  have hfineBand_union_subset :
      fineBand.union ⊆ restriction.refined.union := by
    intro p hp
    rcases hp with ⟨i, hi⟩
    exact ⟨i, Set.inter_subset_left hi⟩
  have hrestriction_union_subset_balancing :
      restriction.refined.union ⊆ balancing.refined.union := by
    intro p hp
    rcases hp with ⟨i, hi⟩
    exact
      ⟨i, fiberBand.refined_subshading i
        (restriction.refined_subshading i hi)⟩
  have hfineBand_union_subset_balancing :
      fineBand.union ⊆ balancing.refined.union :=
    Set.Subset.trans hfineBand_union_subset
      hrestriction_union_subset_balancing
  rcases balancing.retainedCoarseCells_nonempty with ⟨c, hc⟩
  have h_sel_nonempty : (balancing.selectedFineCells c).Nonempty := by
    have hcard_pos : 0 < (balancing.selectedFineCells c).card := by
      rw [balancing.selectedFineCells_card c hc]
      <;> positivity
    exact Finset.card_pos.mp hcard_pos
  rcases h_sel_nonempty with ⟨f, hf⟩
  have hf_retained : f ∈ balancing.retainedFineCells := by
    rw [balancing.retainedFineCells_eq]
    exact Finset.mem_biUnion.mpr ⟨c, hc, hf⟩
  let p0 : Point3 := cellCorner delta f
  have hp0_cube : p0 ∈ wz1PaperGridCube delta f :=
    cellCorner_mem_gridCube hdelta f
  have hp0_union : p0 ∈ balancing.refined.union := by
    rw [balancing.refined_union_eq]
    exact Set.mem_iUnion₂.mpr ⟨f, hf_retained, hp0_cube⟩
  rcases hp0_union with ⟨idx, hidx⟩
  have h_idx_eq : wz1PaperGridIndex delta p0 = f :=
    (mem_wz1PaperGridCube _ _ _).mp hp0_cube
  have h_cube_in_carrier :
      wz1PaperGridCube delta f ⊆ balancing.refined.carrier idx := by
    have h :
        ∀ y,
          y ∈ wz1PaperGridCube delta (wz1PaperGridIndex delta p0) →
            y ∈ balancing.refined.carrier idx :=
      balancing.refined_cubical idx p0 hidx
    rw [h_idx_eq] at h
    exact h
  have h_balancing_mass_pos : 0 < balancing.refined.mass := by
    have h_vol_pos : 0 < volume (balancing.refined.carrier idx) :=
      (wz1PaperGridCube_volume_pos hdelta f).trans_le
        (measure_mono h_cube_in_carrier)
    dsimp only [Kakeya.Streamlined.Shading.mass]
    have h :
        volume (balancing.refined.carrier idx) ≤
          ∑ i : Fin (wz1PaperBodyFamily fine).card,
            volume (balancing.refined.carrier i) :=
      Finset.single_le_sum
        (fun _ _ => show 0 ≤ volume (balancing.refined.carrier _) by
          positivity)
        (Finset.mem_univ idx)
    exact h_vol_pos.trans_le h
  have h_fiberBand_mass_pos : 0 < fiberBand.refined.mass := by
    have hdenom_ne_top :
        ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) ≠ ⊤ := by simp
    exact
      (ENNReal.div_pos h_balancing_mass_pos.ne' hdenom_ne_top).trans_le
        fiberBand.retained_mass
  have h_restriction_mass_pos : 0 < restriction.refined.mass := by
    have hdenom_eq :
        2 *
            ((Nat.log 2
              (2 *
                (wz2PaperPositiveParentCellPairs
                  active fiberBand.refined).card) : ENNReal) + 1) =
          ↑(2 *
            (Nat.log 2
              (2 *
                (wz2PaperPositiveParentCellPairs
                  active fiberBand.refined).card) + 1)) := by
      norm_cast
    have hdenom_ne_top :
        2 *
            ((Nat.log 2
              (2 *
                (wz2PaperPositiveParentCellPairs
                  active fiberBand.refined).card) : ENNReal) + 1) ≠ ⊤ := by
      rw [hdenom_eq]
      exact ENNReal.coe_ne_top
    exact
      (ENNReal.div_pos h_fiberBand_mass_pos.ne' hdenom_ne_top).trans_le
        restriction.retained_mass
  have h_fineBand_mass_pos : 0 < fineBand.mass := by
    have hdenom_ne_top :
        ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) ≠ ⊤ := by simp
    exact
      (ENNReal.div_pos h_restriction_mass_pos.ne' hdenom_ne_top).trans_le
        hfineBand_mass_retention
  have h_fineBand_union_nonempty : fineBand.union.Nonempty := by
    by_contra h
    have h_empty : fineBand.union = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h
    have h_all_empty : ∀ i, fineBand.carrier i = ∅ := by
      intro i
      have h_sub : fineBand.carrier i ⊆ fineBand.union := by
        intro x hx
        exact ⟨i, hx⟩
      rw [h_empty] at h_sub
      simpa using h_sub
    have h_mass_zero : fineBand.mass = 0 := by
      simp [Kakeya.Streamlined.Shading.mass, h_all_empty]
    rw [h_mass_zero] at h_fineBand_mass_pos
    exact False.elim (lt_irrefl 0 h_fineBand_mass_pos)
  let activeFineCells := wz1PaperActiveCells fineBand hdelta
  rcases h_fineBand_union_nonempty with ⟨p, hp⟩
  have hp_in_balancing : p ∈ balancing.refined.union :=
    hfineBand_union_subset_balancing hp
  rw [balancing.refined_union_eq] at hp_in_balancing
  rcases Set.mem_iUnion₂.mp hp_in_balancing with
    ⟨f, hf_retained, hp_in_fcube⟩
  have hf_window : f ∈ wz1PaperGridIndicesInWindow delta hdelta := by
    have h_idx : wz1PaperGridIndex delta p = f :=
      (mem_wz1PaperGridCube _ _ _).mp hp_in_fcube
    rcases hp with ⟨idx, hidx⟩
    have hbody : p ∈ wz1PaperTubeCarrier (fine.tube idx) :=
      fineBand.subset_body idx hidx
    have h :=
      paper_point_gridIndex_in_window (delta := delta) hdelta hbody.2
    rw [h_idx] at *
    exact h
  have hf_active : f ∈ activeFineCells := by
    rw [mem_wz1PaperActiveCells]
    exact ⟨hf_window, ⟨p, hp, hp_in_fcube⟩⟩
  have h_activeFineCells_nonempty : activeFineCells.Nonempty :=
    ⟨f, hf_active⟩
  have h_fineCell_in_retained :
      ∀ fineCell ∈ activeFineCells,
        fineCell ∈ balancing.retainedFineCells :=
    fun fineCell hfine =>
      activeCell_subset_retainedFineCells
        hfineBand_union_subset_balancing hdelta hfine
  let coarseParent : WZ2PaperCellIndex → WZ2PaperCellIndex :=
    fun fineCell =>
      if h : fineCell ∈ activeFineCells then
        Classical.choose
          (unique_coarseParent_of_retainedFineCell hdelta
            (h_fineCell_in_retained fineCell h))
      else (0, 0, 0)
  have h_coarseParent_spec :
      ∀ fineCell ∈ activeFineCells,
        coarseParent fineCell ∈ balancing.retainedCoarseCells ∧
          fineCell ∈
            balancing.selectedFineCells (coarseParent fineCell) := by
    intro fineCell hfineCell
    have hlet :
        coarseParent fineCell =
          Classical.choose
            (unique_coarseParent_of_retainedFineCell hdelta
              (h_fineCell_in_retained fineCell hfineCell)) := by
      simp [coarseParent, hfineCell]
    rw [hlet]
    exact
      (Classical.choose_spec
        (unique_coarseParent_of_retainedFineCell hdelta
          (h_fineCell_in_retained fineCell hfineCell))).1
  have h_coarseParent_containment :
      ∀ fineCell ∈ activeFineCells,
        wz1PaperGridCube delta fineCell ⊆
          wz1PaperGridCube rho (coarseParent fineCell) := by
    intro fineCell hfineCell
    have hspec := h_coarseParent_spec fineCell hfineCell
    exact
      balancing.fine_cell_containment
        (coarseParent fineCell) hspec.1 fineCell hspec.2
  have h_coarseParent_selected :
      ∀ fineCell ∈ activeFineCells,
        coarseParent fineCell ∈ restriction.selectedCells := by
    intro fineCell hfineCell
    have h_inter :
        (fineBand.union ∩ wz1PaperGridCube delta fineCell).Nonempty :=
      (mem_wz1PaperActiveCells fineBand hdelta fineCell).mp hfineCell |>.2
    rcases h_inter with ⟨p, hp_band, hp_cube⟩
    have h_cont :
        wz1PaperGridCube delta fineCell ⊆
          wz1PaperGridCube rho (coarseParent fineCell) :=
      h_coarseParent_containment fineCell hfineCell
    have hp_rho :
        p ∈ wz1PaperGridCube rho (coarseParent fineCell) :=
      h_cont hp_cube
    have hp_restriction : p ∈ restriction.refined.union :=
      hfineBand_union_subset hp_band
    have hp_in_selected_union :
        p ∈ ⋃ cell ∈ restriction.selectedCells,
          wz1PaperGridCube rho cell :=
      restriction.refined_union_subset hp_restriction
    rcases Set.mem_iUnion₂.mp hp_in_selected_union with
      ⟨c', hc', hp_in_c'⟩
    have h_eq : coarseParent fineCell = c' := by
      have h1 : wz1PaperGridIndex rho p = coarseParent fineCell :=
        (mem_wz1PaperGridCube _ _ _).mp hp_rho
      have h2 : wz1PaperGridIndex rho p = c' :=
        (mem_wz1PaperGridCube _ _ _).mp hp_in_c'
      exact h1.symm.trans h2
    rw [h_eq]
    exact hc'
  have h_activeFineCell_contained :
      ∀ fineCell ∈ activeFineCells,
        coarseParent fineCell ∈ restriction.selectedCells ∧
          wz1PaperGridCube delta fineCell ⊆
            wz1PaperGridCube rho (coarseParent fineCell) := by
    intro fineCell hfineCell
    exact
      ⟨h_coarseParent_selected fineCell hfineCell,
        h_coarseParent_containment fineCell hfineCell⟩
  let finalCoarseCells := activeFineCells.image coarseParent
  let availableFinalFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex :=
    fun cell =>
      activeFineCells.filter
        (fun fineCell => coarseParent fineCell = cell)
  have h_finalCoarseCells_nonempty : finalCoarseCells.Nonempty :=
    Finset.Nonempty.image h_activeFineCells_nonempty coarseParent
  have h_available_nonempty :
      ∀ cell ∈ finalCoarseCells,
        (availableFinalFineCells cell).Nonempty := by
    intro cell hcell
    rcases Finset.mem_image.mp hcell with
      ⟨fineCell, hfineCell, rfl⟩
    have h_mem :
        fineCell ∈ availableFinalFineCells (coarseParent fineCell) := by
      simp [availableFinalFineCells, hfineCell]
    exact ⟨fineCell, h_mem⟩
  have h_available_ready :
      ∀ cell ∈ finalCoarseCells,
        ∀ fineCell ∈ availableFinalFineCells cell,
          fineCell ∈ wz1PaperActiveCells fineBand hdelta ∧
            wz1PaperGridCube delta fineCell ⊆
              wz1PaperGridCube rho cell := by
    intro cell hcell fineCell hfineCell
    have h_in_active : fineCell ∈ activeFineCells :=
      (Finset.mem_filter.mp hfineCell).1
    have h_parent_eq : coarseParent fineCell = cell :=
      (Finset.mem_filter.mp hfineCell).2
    have h1 : fineCell ∈ wz1PaperActiveCells fineBand hdelta := by
      simpa [activeFineCells] using h_in_active
    have h2 :
        wz1PaperGridCube delta fineCell ⊆
          wz1PaperGridCube rho cell := by
      rw [← h_parent_eq]
      exact h_coarseParent_containment fineCell h_in_active
    exact ⟨h1, h2⟩
  have h_exact_main :
      Nonempty
        (WZ2PaperExactCellBalancingData
          (rho := rho) fineBand finalCoarseCells
          availableFinalFineCells) :=
    wz2_prop_sticky_exact_cell_balancing hdelta hrho fineBand
      hfineBand_cubical finalCoarseCells
      h_finalCoarseCells_nonempty availableFinalFineCells
      h_available_nonempty h_available_ready
  rcases h_exact_main with ⟨exact⟩
  have h_retained_coarse_subset :
      exact.retainedCoarseCells ⊆ restriction.selectedCells := by
    intro cell hcell
    have h1 : cell ∈ finalCoarseCells :=
      exact.retainedCoarseCells_subset hcell
    rcases Finset.mem_image.mp h1 with
      ⟨fineCell, hfineCell, rfl⟩
    exact h_coarseParent_selected fineCell hfineCell
  let U := wz2RetainedCellsUnion delta exact.retainedFineCells
  have h_exact_refined_union_inter :
      exact.refined.union = fineBand.union ∩ U := by
    ext point
    simp only [Kakeya.Streamlined.Shading.union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨index, hpoint⟩
      have hcar :
          exact.refined.carrier index =
            fineBand.carrier index ∩ U :=
        exact.refined_carrier_eq index
      rw [hcar] at hpoint
      exact ⟨⟨index, hpoint.1⟩, hpoint.2⟩
    · rintro ⟨⟨index, h1⟩, h2⟩
      refine ⟨index, ?_⟩
      have hcar :
          exact.refined.carrier index =
            fineBand.carrier index ∩ U :=
        exact.refined_carrier_eq index
      rw [hcar]
      exact ⟨h1, h2⟩
  have h_exact_multiplicity_band :
      ∀ point ∈ exact.refined.union,
        (2 ^ fineLevel : ENNReal) ≤
            (exact.refined.pointMultiplicity point : ENNReal) ∧
          (exact.refined.pointMultiplicity point : ENNReal) <
            (2 ^ (fineLevel + 1) : ENNReal) := by
    intro point hpoint
    have h_eq :
        exact.refined.pointMultiplicity point =
          fineBand.pointMultiplicity point :=
      wholeCellRestriction_pointMultiplicity_eq
        exact.refined_carrier_eq hpoint
    rw [h_eq]
    have h_in_fineBand : point ∈ fineBand.union := by
      rw [h_exact_refined_union_inter] at hpoint
      exact hpoint.1
    exact hfineBand_multiplicity point h_in_fineBand
  let N : ℕ :=
    ∑ cell ∈ finalCoarseCells,
      (availableFinalFineCells cell).card
  have h_fineBand_const :
      fineBand.HasConstantMultiplicity
        (2 ^ fineLevel) (2 * (2 ^ fineLevel)) := by
    intro point hpoint
    have h := hfineBand_multiplicity point hpoint
    constructor
    · exact_mod_cast h.1
    · have h_upper :
          (fineBand.pointMultiplicity point : ENNReal) <
            (2 ^ (fineLevel + 1) : ENNReal) := h.2
      have h_eq :
          (2 ^ (fineLevel + 1) : ENNReal) =
            (2 * (2 ^ fineLevel) : ENNReal) := by
        simp [pow_succ] <;> ring
      rw [h_eq] at h_upper
      exact_mod_cast h_upper.le
  have h_exact_active_eq :
      wz1PaperActiveCells exact.refined hdelta =
        exact.retainedFineCells := by
    ext cell
    simp only [mem_wz1PaperActiveCells]
    constructor
    · rintro ⟨hwindow, hnonempty⟩
      rcases hnonempty with ⟨p, hp_union, hp_cube⟩
      rw [exact.refined_union_eq] at hp_union
      rcases Set.mem_iUnion₂.mp hp_union with ⟨g, hg, hpg⟩
      have h_eq : cell = g := by
        have h1 : wz1PaperGridIndex delta p = cell :=
          (mem_wz1PaperGridCube _ _ _).mp hp_cube
        have h2 : wz1PaperGridIndex delta p = g :=
          (mem_wz1PaperGridCube _ _ _).mp hpg
        exact h1.symm.trans h2
      rw [h_eq]
      exact hg
    · intro hcell
      have h_in_active : cell ∈ activeFineCells := by
        rw [exact.retainedFineCells_eq] at hcell
        rcases Finset.mem_biUnion.mp hcell with
          ⟨c, hc, hsel⟩
        have h_in_avail :
            cell ∈ availableFinalFineCells c :=
          exact.selectedFineCells_subset c hc hsel
        exact (Finset.mem_filter.mp h_in_avail).1
      have hwindow :
          cell ∈ wz1PaperGridIndicesInWindow delta hdelta :=
        (mem_wz1PaperActiveCells fineBand hdelta cell).mp
          h_in_active |>.1
      have hnonempty :
          (exact.refined.union ∩
            wz1PaperGridCube delta cell).Nonempty := by
        rw [exact.refined_union_eq]
        exact
          ⟨cellCorner delta cell,
            Set.mem_iUnion₂.mpr
              ⟨cell, hcell, cellCorner_mem_gridCube hdelta cell⟩,
            cellCorner_mem_gridCube hdelta cell⟩
      exact ⟨hwindow, hnonempty⟩
  have h_N_eq : N = activeFineCells.card := by
    dsimp only [N, availableFinalFineCells]
    have h_filter_eq :
        activeFineCells.filter
            (fun i => coarseParent i ∈ finalCoarseCells) =
          activeFineCells := by
      apply Finset.filter_true_of_mem
      intro i hi
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    rw [Finset.sum_card_fiberwise_eq_card_filter, h_filter_eq]
  have h_count_nat :
      N ≤
        2 * (Nat.log 2 N + 1) *
          exact.retainedFineCells.card :=
    exact.retainedFineCells_count
  have h_count :
      (activeFineCells.card : ENNReal) ≤
        ((2 * (Nat.log 2 N + 1 : ℕ) : ENNReal)) *
          (exact.retainedFineCells.card : ENNReal) := by
    have h_eq :
        (activeFineCells.card : ENNReal) = (N : ENNReal) := by
      exact_mod_cast h_N_eq.symm
    rw [h_eq]
    exact_mod_cast h_count_nat
  have h_count' :
      (wz1PaperActiveCells fineBand hdelta).card ≤
        ((2 * (Nat.log 2 N + 1 : ℕ) : ENNReal)) *
          (wz1PaperActiveCells exact.refined hdelta).card := by
    rw [h_exact_active_eq]
    have h_let :
        wz1PaperActiveCells fineBand hdelta = activeFineCells := by rfl
    rw [h_let]
    have h_log :
        Nat.log 2 N = Nat.log 2 activeFineCells.card := by
      rw [h_N_eq]
    simpa [h_log] using h_count
  have h_exact_const :
      exact.refined.HasConstantMultiplicity
        (2 ^ fineLevel) (2 * (2 ^ fineLevel)) := by
    intro point hpoint
    have h_eq :
        exact.refined.pointMultiplicity point =
          fineBand.pointMultiplicity point :=
      wholeCellRestriction_pointMultiplicity_eq
        exact.refined_carrier_eq hpoint
    rw [h_eq]
    have h_in_fineBand : point ∈ fineBand.union := by
      rw [h_exact_refined_union_inter] at hpoint
      exact hpoint.1
    exact h_fineBand_const point h_in_fineBand
  have h_exact_mass_retention_raw :
      fineBand.mass ≤
        2 * ((2 * (Nat.log 2 N + 1 : ℕ) : ENNReal)) *
          exact.refined.mass :=
    cubical_mass_retention_from_cell_count
      fineBand exact.refined hfineBand_cubical exact.refined_cubical
      hdelta (2 ^ fineLevel) h_fineBand_const h_exact_const
      ((2 * (Nat.log 2 N + 1 : ℕ) : ENNReal)) h_count'
  have h_exact_mass_retention :
      fineBand.mass ≤
        (4 * ((Nat.log 2 N + 1 : ℕ) : ENNReal)) *
          exact.refined.mass := by
    have h_eq :
        2 * ((2 * (Nat.log 2 N + 1 : ℕ) : ENNReal)) =
          (4 * ((Nat.log 2 N + 1 : ℕ) : ENNReal)) := by
      norm_cast <;> ring
    rw [h_eq] at h_exact_mass_retention_raw
    exact h_exact_mass_retention_raw
  have h_fiber_multiplicity_band :
      ∀ parent point,
        point ∈
            (restrictPaperShading
              (cover.fullFiberSubfamily parent)
              exact.refined).union →
          (2 ^ fiberBand.level : ENNReal) ≤
              ((restrictPaperShading
                (cover.fullFiberSubfamily parent)
                exact.refined).pointMultiplicity point : ENNReal) ∧
          ((restrictPaperShading
            (cover.fullFiberSubfamily parent)
            exact.refined).pointMultiplicity point : ENNReal) <
            (2 ^ (fiberBand.level + 1) : ENNReal) := by
    intro parent point hpoint
    let selected := cover.fullFiberSubfamily parent
    let fiberExact :=
      restrictPaperShading selected exact.refined
    let fiberFineBand :=
      restrictPaperShading selected fineBand
    let fiberRestriction :=
      restrictPaperShading selected restriction.refined
    have h1 :
        fiberExact.pointMultiplicity point =
          fiberFineBand.pointMultiplicity point :=
      wholeCellRestriction_fiberPointMultiplicity_eq
        exact.refined_carrier_eq selected hpoint
    have hpoint' : point ∈ fiberFineBand.union := by
      rcases hpoint with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have h :
          exact.refined.carrier (selected.embedding i) ⊆
            fineBand.carrier (selected.embedding i) := by
        rw [exact.refined_carrier_eq]
        exact Set.inter_subset_left
      exact h hi
    have h2 :
        fiberFineBand.pointMultiplicity point =
          fiberRestriction.pointMultiplicity point :=
      dyadicBandSubshading_fiberPointMultiplicity_eq
        selected hpoint'
    rw [h1, h2]
    have h_in_fiberRestriction :
        point ∈ fiberRestriction.union := by
      rcases hpoint' with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have h :
          fineBand.carrier (selected.embedding i) ⊆
            restriction.refined.carrier (selected.embedding i) :=
        Set.inter_subset_left
      exact h hi
    exact
      restriction.fiber_multiplicity_band parent point
        h_in_fiberRestriction
  refine' ⟨
    fineLevel, fineBand, (by intro; rfl), hfineBand_cubical,
    hfineBand_multiplicity, hfineBand_mass_retention,
    activeFineCells, rfl, h_activeFineCells_nonempty,
    coarseParent, h_activeFineCell_contained,
    finalCoarseCells, rfl, h_finalCoarseCells_nonempty,
    availableFinalFineCells, (by intro cell; rfl),
    h_available_nonempty, h_available_ready,
    exact, h_retained_coarse_subset, h_exact_multiplicity_band,
    h_exact_mass_retention, h_fiber_multiplicity_band
  ⟩

end Kakeya.Assouad

end
