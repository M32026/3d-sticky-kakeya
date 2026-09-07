import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantParentCellsStatements

/-! # Dominant parent contribution in each balanced cell -/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem wz2_paper_dominant_parent_cells :
    WZ2PaperDominantParentCellsStatement := by
  intro delta rho hdelta hrho fine coarse cover sourceShading coarseCells
    availableFineCells balancing coarseData active multiplicityLevel degree
  have h_coarse_card_pos : 0 < coarse.card := by
    rcases balancing.retainedCoarseCells_nonempty with ⟨cell, hcell⟩
    rcases active.activeParents_nonempty cell hcell with ⟨parent, _⟩
    exact Fin.pos_iff_nonempty.mpr ⟨parent⟩
  let defaultParent : Fin coarse.card := ⟨0, h_coarse_card_pos⟩
  let dominantParent : WZ2PaperCellIndex → Fin coarse.card := fun cell =>
    if h : cell ∈ balancing.retainedCoarseCells then
      Classical.choose
        (Finset.exists_max_image
          (active.activeParents cell)
          (fun parent =>
            wz2PaperParentCellMass
              cover balancing.refined (cell, parent))
          (active.activeParents_nonempty cell h))
    else defaultParent
  let dominantMass : WZ2PaperCellIndex → ENNReal := fun cell =>
    wz2PaperParentCellMass
      cover balancing.refined (cell, dominantParent cell)
  have h_dominantParent_mem :
      ∀ cell ∈ balancing.retainedCoarseCells,
        dominantParent cell ∈ active.activeParents cell := by
    intro cell hcell
    have h :
        dominantParent cell =
          Classical.choose
            (Finset.exists_max_image
              (active.activeParents cell)
              (fun parent =>
                wz2PaperParentCellMass
                  cover balancing.refined (cell, parent))
              (active.activeParents_nonempty cell hcell)) := by
      simp [dominantParent, hcell]
    rw [h]
    exact
      (Classical.choose_spec
        (Finset.exists_max_image
          (active.activeParents cell)
          (fun parent =>
            wz2PaperParentCellMass
              cover balancing.refined (cell, parent))
          (active.activeParents_nonempty cell hcell))).1
  have h_dominant_max :
      ∀ cell ∈ balancing.retainedCoarseCells,
        ∀ parent ∈ active.activeParents cell,
          wz2PaperParentCellMass
              cover balancing.refined (cell, parent) ≤
            dominantMass cell := by
    intro cell hcell parent hparent
    have h :
        dominantParent cell =
          Classical.choose
            (Finset.exists_max_image
              (active.activeParents cell)
              (fun candidate =>
                wz2PaperParentCellMass
                  cover balancing.refined (cell, candidate))
              (active.activeParents_nonempty cell hcell)) := by
      simp [dominantParent, hcell]
    have hmain :
        wz2PaperParentCellMass
              cover balancing.refined (cell, parent) ≤
          wz2PaperParentCellMass
            cover balancing.refined
            (cell,
              Classical.choose
                (Finset.exists_max_image
                  (active.activeParents cell)
                  (fun candidate =>
                    wz2PaperParentCellMass
                      cover balancing.refined (cell, candidate))
                  (active.activeParents_nonempty cell hcell))) :=
      (Classical.choose_spec
        (Finset.exists_max_image
          (active.activeParents cell)
          (fun candidate =>
            wz2PaperParentCellMass
              cover balancing.refined (cell, candidate))
          (active.activeParents_nonempty cell hcell))).2
        parent hparent
    simpa [dominantMass, h] using hmain
  have h_dominant_lower :
      ∀ cell ∈ balancing.retainedCoarseCells,
        balancing.cellMass ≤
          (2 * wz2PaperBalancedParentDegreeCap
              balancing multiplicityLevel : ENNReal) *
            dominantMass cell := by
    intro cell hcell
    have h1 :
        balancing.cellMass ≤
          ∑ parent ∈ active.activeParents cell,
            wz2PaperParentCellMass
              cover balancing.refined (cell, parent) :=
      active.cell_mass_le_sum_parent cell hcell
    have h2 :
        (∑ parent ∈ active.activeParents cell,
            wz2PaperParentCellMass
              cover balancing.refined (cell, parent)) ≤
          ((active.activeParents cell).card : ENNReal) *
            dominantMass cell := by
      calc
        (∑ parent ∈ active.activeParents cell,
            wz2PaperParentCellMass
              cover balancing.refined (cell, parent)) ≤
            ∑ _parent ∈ active.activeParents cell,
              dominantMass cell := by
          apply Finset.sum_le_sum
          intro parent hparent
          exact h_dominant_max cell hcell parent hparent
        _ =
            ((active.activeParents cell).card : ENNReal) *
              dominantMass cell := by
          simp [Finset.sum_const]
    have h4 :
        (active.activeParents cell).card ≤
          2 * wz2PaperBalancedParentDegreeCap
            balancing multiplicityLevel :=
      degree.active_parent_degree cell hcell
    have h5 :
        ((active.activeParents cell).card : ENNReal) *
              dominantMass cell ≤
          (2 * wz2PaperBalancedParentDegreeCap
              balancing multiplicityLevel : ENNReal) *
            dominantMass cell := by
      gcongr
      exact_mod_cast h4
    exact h1.trans (h2.trans h5)
  have h_dominant_pos :
      ∀ cell ∈ balancing.retainedCoarseCells,
        0 < dominantMass cell := by
    intro cell hcell
    let parent := dominantParent cell
    have hparent : parent ∈ active.activeParents cell :=
      h_dominantParent_mem cell hcell
    let restricted :=
      restrictPaperShading
        (cover.fullFiberSubfamily parent) balancing.refined
    have h_union_inter :
        restricted.union ∩ wz1PaperGridCube rho cell =
          ⋃ source :
              Fin (cover.fullFiberSubfamily parent).family.card,
            restricted.carrier source ∩
              wz1PaperGridCube rho cell := by
      ext point
      simp [Set.mem_iUnion]
      tauto
    have h_subadd :
        volume
            (restricted.union ∩ wz1PaperGridCube rho cell) ≤
          dominantMass cell := by
      rw [h_union_inter]
      have h :
          volume
              (⋃ source ∈
                    (Finset.univ :
                      Finset
                        (Fin
                          (cover.fullFiberSubfamily parent).family.card)),
                restricted.carrier source ∩
                  wz1PaperGridCube rho cell) ≤
            ∑ source ∈
                (Finset.univ :
                  Finset
                    (Fin
                      (cover.fullFiberSubfamily parent).family.card)),
              volume
                (restricted.carrier source ∩
                  wz1PaperGridCube rho cell) :=
        MeasureTheory.measure_biUnion_finset_le
          Finset.univ
          (fun source =>
            restricted.carrier source ∩
              wz1PaperGridCube rho cell)
      have h_univ_eq :
          (⋃ source ∈
                (Finset.univ :
                  Finset
                    (Fin
                      (cover.fullFiberSubfamily parent).family.card)),
              restricted.carrier source ∩
                wz1PaperGridCube rho cell) =
            ⋃ source :
                Fin (cover.fullFiberSubfamily parent).family.card,
              restricted.carrier source ∩
                wz1PaperGridCube rho cell := by
        ext point
        simp [Set.mem_iUnion]
      rw [h_univ_eq] at h
      simpa [dominantMass, wz2PaperParentCellMass] using h
    have h_lower :
        active.fiberCellMass ≤
          volume
            (restricted.union ∩ wz1PaperGridCube rho cell) :=
      active.fiber_cell_mass_lower cell hcell parent hparent
    exact
      active.fiberCellMass_pos.trans_le
        (h_lower.trans h_subadd)
  have h_dominant_ne_top :
      ∀ cell ∈ balancing.retainedCoarseCells,
        dominantMass cell ≠ ⊤ := by
    intro cell hcell
    let f : Fin coarse.card → ENNReal := fun parent =>
      wz2PaperParentCellMass
        cover balancing.refined (cell, parent)
    have hmem :
        dominantParent cell ∈ active.activeParents cell :=
      h_dominantParent_mem cell hcell
    have h1 :
        f (dominantParent cell) ≤
          ∑ parent ∈ active.activeParents cell, f parent :=
      Finset.single_le_sum (fun _ _ => by positivity) hmem
    have h3 :
        (∑ parent ∈ active.activeParents cell, f parent) =
          wz2PaperCellIncidenceMass
            (rho := rho) balancing.refined cell :=
      active.sum_parent_mass_eq_cell_incidence cell hcell
    rw [h3] at h1
    have h4 :
        wz2PaperCellIncidenceMass
            (rho := rho) balancing.refined cell ≤
          (2 ^ (multiplicityLevel + 1) : ENNReal) *
            balancing.cellMass :=
      degree.cell_incidence_upper cell hcell
    have h5 :
        (2 ^ (multiplicityLevel + 1) : ENNReal) *
              balancing.cellMass ≠
            ⊤ :=
      ENNReal.mul_ne_top (by simp) balancing.cellMass_ne_top
    exact ne_top_of_le_ne_top h5 (h1.trans h4)
  let Cell := {cell // cell ∈ balancing.retainedCoarseCells}
  let weight : Cell → ENNReal := fun index => dominantMass index.val
  let total : ENNReal := ∑ index : Cell, weight index
  have h_total_eq :
      total =
        ∑ cell ∈ balancing.retainedCoarseCells,
          dominantMass cell := by
    dsimp only [total, weight]
    exact
      Finset.sum_coe_sort balancing.retainedCoarseCells
        (fun cell => dominantMass cell)
  have h_total_ne_top : total ≠ ⊤ := by
    rw [h_total_eq]
    exact
      ENNReal.sum_ne_top.mpr
        (fun cell hcell => h_dominant_ne_top cell hcell)
  have h_total_pos : 0 < total := by
    rw [h_total_eq]
    rcases balancing.retainedCoarseCells_nonempty with ⟨cell, hcell⟩
    exact
      (h_dominant_pos cell hcell).trans_le
        (Finset.single_le_sum
          (fun _ _ => by positivity) hcell)
  rcases
      ennreal_dyadic_bin weight total rfl h_total_ne_top h_total_pos with
    ⟨bins, selectedSubtype, hbins_eq, hselectedSubtype,
      hmass_retention, _hthreshold, ⟨massLevel, hmassLevelPos, hband⟩⟩
  let selectedCells : Finset WZ2PaperCellIndex :=
    Finset.image (fun index : Cell => index.val) selectedSubtype
  have h_selectedCells_subset :
      selectedCells ⊆ balancing.retainedCoarseCells := by
    intro cell hcell
    rcases Finset.mem_image.mp hcell with ⟨index, _, rfl⟩
    exact index.property
  have h_selectedCells_nonempty : selectedCells.Nonempty := by
    rcases hselectedSubtype with ⟨index, hindex⟩
    exact
      ⟨index.val,
        Finset.mem_image.mpr ⟨index, hindex, rfl⟩⟩
  have h_sum_selected :
      (∑ cell ∈ selectedCells, dominantMass cell) =
        ∑ index ∈ selectedSubtype, weight index := by
    have hinj :
        Set.InjOn (fun index : Cell => index.val) selectedSubtype := by
      intro first _ second _ heq
      exact Subtype.ext heq
    dsimp only [weight]
    rw [← Finset.sum_image hinj]
  have h_bins_eq :
      bins =
        Nat.log 2
            (2 * balancing.retainedCoarseCells.card) +
          1 := by
    simpa [Cell, Fintype.card_subtype] using hbins_eq
  have h_mass_retention' :
      total / (2 * (bins : ENNReal)) ≤
        ∑ index ∈ selectedSubtype, weight index := by
    have h_bins_pos : 0 < bins := by
      rw [h_bins_eq]
      omega
    have h_bins_ne_zero : (bins : ENNReal) ≠ 0 := by
      exact_mod_cast h_bins_pos.ne'
    have h_bins_ne_top : (bins : ENNReal) ≠ ⊤ :=
      ENNReal.coe_ne_top
    let selectedMass : ENNReal :=
      ∑ index ∈ selectedSubtype, weight index
    have h :
        selectedMass * (bins : ENNReal) ≥ total / 2 :=
      hmass_retention
    have h2 :
        selectedMass * (2 * (bins : ENNReal)) ≥ total := by
      have h3 :
          selectedMass * (2 * (bins : ENNReal)) =
            2 * (selectedMass * (bins : ENNReal)) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      rw [h3]
      have h4 :
          2 * (selectedMass * (bins : ENNReal)) ≥
            2 * (total / 2) := by
        gcongr
      have h5 : 2 * (total / 2) = total := by
        have h6 : total / 2 + total / 2 = total :=
          ENNReal.add_halves total
        simpa [two_mul] using h6
      rw [h5] at h4
      exact h4
    have hprodZero : 2 * (bins : ENNReal) ≠ 0 :=
      mul_ne_zero (by norm_num) h_bins_ne_zero
    have hprodTop : 2 * (bins : ENNReal) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) h_bins_ne_top
    calc
      total / (2 * (bins : ENNReal)) =
          total * (2 * (bins : ENNReal))⁻¹ := rfl
      _ ≤ selectedMass * (2 * (bins : ENNReal)) *
            (2 * (bins : ENNReal))⁻¹ := by
        gcongr
      _ = selectedMass := by
        rw [mul_assoc,
          ENNReal.mul_inv_cancel hprodZero hprodTop, mul_one]
  have h_final_retention :
      (∑ cell ∈ balancing.retainedCoarseCells,
          dominantMass cell) /
            (2 *
              (Nat.log 2
                    (2 * balancing.retainedCoarseCells.card) +
                  1 :
                ENNReal)) ≤
        ∑ cell ∈ selectedCells, dominantMass cell := by
    have h_bins_coe :
        (bins : ENNReal) =
          (Nat.log 2
                (2 * balancing.retainedCoarseCells.card) +
              1 :
            ENNReal) := by
      rw [h_bins_eq]
      norm_cast
    rw [h_total_eq] at h_mass_retention'
    rw [h_bins_coe] at h_mass_retention'
    exact h_mass_retention'.trans_eq h_sum_selected.symm
  have h_massLevel_ne_top : massLevel ≠ ⊤ := by
    rcases hselectedSubtype with ⟨index, hindex⟩
    exact
      ne_top_of_le_ne_top
        (h_dominant_ne_top index.val index.property)
        (hband index hindex).1
  have h_mass_band :
      ∀ cell ∈ selectedCells,
        massLevel ≤ dominantMass cell ∧
          dominantMass cell ≤ 2 * massLevel := by
    intro cell hcell
    rcases Finset.mem_image.mp hcell with ⟨index, hindex, rfl⟩
    exact hband index hindex
  exact
    ⟨dominantParent, h_dominantParent_mem, dominantMass,
      fun _ => rfl, h_dominant_max, h_dominant_lower,
      selectedCells, h_selectedCells_subset,
      h_selectedCells_nonempty, massLevel, hmassLevelPos,
      h_massLevel_ne_top, h_mass_band, h_final_retention⟩

end Kakeya.Assouad

end
