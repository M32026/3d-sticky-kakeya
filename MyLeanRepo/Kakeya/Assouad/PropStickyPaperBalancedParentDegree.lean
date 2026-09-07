import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedParentDegreeStatements

/-! # Degree bound for balanced parent-cell incidence -/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem wz2_paper_balanced_parent_degree :
    WZ2PaperBalancedParentDegreeStatement := by
  intro delta rho hdelta hrho fine coarse cover sourceShading coarseCells
    availableFineCells balancing coarseData active multiplicityLevel h_mult
  let Y := balancing.refined
  let C : ENNReal := 2 ^ (multiplicityLevel + 1)
  have hY_measurable : MeasurableSet Y.union :=
    measurableSet_shading_union Y
  have h_cell_incidence_upper :
      ∀ cell ∈ balancing.retainedCoarseCells,
        wz2PaperCellIncidenceMass (rho := rho) Y cell ≤
          C * balancing.cellMass := by
    intro cell hcell
    let s := wz1PaperGridCube rho cell
    have hs : MeasurableSet s := wz1PaperGridCube_measurable cell
    let t := s ∩ Y.union
    have ht : MeasurableSet t := hs.inter hY_measurable
    have h_carrier_subset_union : ∀ index, Y.carrier index ⊆ Y.union := by
      intro index point hpoint
      exact ⟨index, hpoint⟩
    have h_inter_eq : ∀ index, Y.carrier index ∩ s = Y.carrier index ∩ t := by
      intro index
      have h : Y.carrier index ∩ t = Y.carrier index ∩ s := by
        ext point
        simp only [t, Set.mem_inter_iff]
        constructor
        · rintro ⟨hcarrier, hcell, _⟩
          exact ⟨hcarrier, hcell⟩
        · rintro ⟨hcarrier, hcell⟩
          exact ⟨hcarrier, hcell, h_carrier_subset_union index hcarrier⟩
      exact h.symm
    have h_fubini :
        wz2PaperCellIncidenceMass (rho := rho) Y cell =
          ∫⁻ point in t, (Y.pointMultiplicity point : ENNReal) := by
      rw [wz2PaperCellIncidenceMass]
      have h_sum :
          ∑ index : Fin fine.card, volume (Y.carrier index ∩ s) =
            ∑ index : Fin fine.card, volume (Y.carrier index ∩ t) := by
        apply Finset.sum_congr rfl
        intro index _
        rw [h_inter_eq index]
      rw [h_sum]
      exact sum_volume_inter_eq_setLIntegral_pointMultiplicity Y ht
    rw [h_fubini]
    have hM : ∀ point ∈ t, (Y.pointMultiplicity point : ENNReal) ≤ C := by
      intro point hpoint
      exact (h_mult point hpoint.2).le
    have h_main :
        (∫⁻ point in t, (Y.pointMultiplicity point : ENNReal)) ≤
          C * volume t := by
      have h :
          (∫⁻ point in t, (Y.pointMultiplicity point : ENNReal)) ≤
            ∫⁻ _point in t, C :=
        setLIntegral_mono' ht hM
      rw [setLIntegral_const] at h
      exact h
    have h_t_eq : t = Y.union ∩ s := by
      ext point
      simp [t, Set.inter_comm]
    have h_cell_mass :
        volume (Y.union ∩ s) = balancing.cellMass :=
      balancing.fine_cell_mass cell hcell
    have h_volume_t : volume t = balancing.cellMass := by
      rw [h_t_eq, h_cell_mass]
    rw [h_volume_t] at h_main
    exact h_main
  have h_parent_lower :
      ∀ cell ∈ balancing.retainedCoarseCells,
        ∀ parent ∈ active.activeParents cell,
          active.fiberCellMass ≤
            wz2PaperParentCellMass cover Y (cell, parent) := by
    intro cell hcell parent hparent
    let s := wz1PaperGridCube rho cell
    have hs : MeasurableSet s := wz1PaperGridCube_measurable cell
    let restricted :=
      restrictPaperShading (cover.fullFiberSubfamily parent) Y
    have h1 :
        active.fiberCellMass ≤ volume (restricted.union ∩ s) :=
      active.fiber_cell_mass_lower cell hcell parent hparent
    let indexType := Fin (cover.fullFiberSubfamily parent).family.card
    have h_union_eq :
        restricted.union ∩ s =
          ⋃ source : indexType, restricted.carrier source ∩ s := by
      ext point
      simp only [restricted, restrictPaperShading, Set.mem_inter_iff,
        Set.mem_iUnion]
      constructor
      · rintro ⟨⟨source, hsource⟩, hs2⟩
        exact ⟨source, hsource, hs2⟩
      · rintro ⟨source, hsource, hs2⟩
        exact ⟨⟨source, hsource⟩, hs2⟩
    have h2 :
        volume (restricted.union ∩ s) ≤
          ∑ source : indexType,
            volume (restricted.carrier source ∩ s) := by
      rw [h_union_eq]
      have h3 :
          volume (⋃ source : indexType, restricted.carrier source ∩ s) ≤
            ∑' source : indexType,
              volume (restricted.carrier source ∩ s) :=
        measure_iUnion_le fun source : indexType =>
          restricted.carrier source ∩ s
      have h4 :
          (∑' source : indexType,
              volume (restricted.carrier source ∩ s)) =
            ∑ source : indexType,
              volume (restricted.carrier source ∩ s) :=
        tsum_fintype _
      rw [h4] at h3
      exact h3
    exact h1.trans h2
  have h_degree :
      ∀ cell ∈ balancing.retainedCoarseCells,
        (active.activeParents cell).card ≤
          2 * wz2PaperBalancedParentDegreeCap balancing multiplicityLevel := by
    intro cell hcell
    have h_sum_lower :
        ((active.activeParents cell).card : ENNReal) *
              active.fiberCellMass ≤
          ∑ parent ∈ active.activeParents cell,
            wz2PaperParentCellMass cover Y (cell, parent) := by
      calc
        ((active.activeParents cell).card : ENNReal) *
              active.fiberCellMass =
            ∑ _parent ∈ active.activeParents cell,
              active.fiberCellMass := by
          rw [Finset.sum_const]
          ring
        _ ≤ ∑ parent ∈ active.activeParents cell,
              wz2PaperParentCellMass cover Y (cell, parent) := by
          apply Finset.sum_le_sum
          intro parent hparent
          exact h_parent_lower cell hcell parent hparent
    have h_sum_eq :
        (∑ parent ∈ active.activeParents cell,
            wz2PaperParentCellMass cover Y (cell, parent)) =
          wz2PaperCellIncidenceMass (rho := rho) Y cell :=
      active.sum_parent_mass_eq_cell_incidence cell hcell
    have h_incidence_upper :
        wz2PaperCellIncidenceMass (rho := rho) Y cell ≤
          C * balancing.cellMass :=
      h_cell_incidence_upper cell hcell
    have h_cellMass_eq :
        balancing.cellMass =
          (2 ^ balancing.level : ENNReal) * active.fiberCellMass := by
      rw [balancing.cellMass_eq, active.fiberCellMass_eq]
      norm_cast
    have h_final :
        ((active.activeParents cell).card : ENNReal) *
              active.fiberCellMass ≤
          (C * (2 ^ balancing.level : ENNReal)) *
            active.fiberCellMass := by
      calc
        ((active.activeParents cell).card : ENNReal) *
              active.fiberCellMass ≤
            ∑ parent ∈ active.activeParents cell,
              wz2PaperParentCellMass cover Y (cell, parent) :=
          h_sum_lower
        _ = wz2PaperCellIncidenceMass (rho := rho) Y cell := h_sum_eq
        _ ≤ C * balancing.cellMass := h_incidence_upper
        _ = C * ((2 ^ balancing.level : ENNReal) *
              active.fiberCellMass) := by
          rw [h_cellMass_eq]
        _ = (C * (2 ^ balancing.level : ENNReal)) *
              active.fiberCellMass := by ring
    have h_cancel :
        ((active.activeParents cell).card : ENNReal) ≤
          C * (2 ^ balancing.level : ENNReal) := by
      exact
        (ENNReal.mul_le_mul_iff_left
          active.fiberCellMass_pos.ne'
          active.fiberCellMass_ne_top).mp h_final
    have h_C_eq :
        C * (2 ^ balancing.level : ENNReal) =
          (2 * wz2PaperBalancedParentDegreeCap
            balancing multiplicityLevel : ENNReal) := by
      simp [C, wz2PaperBalancedParentDegreeCap, pow_succ]
      ring
    rw [h_C_eq] at h_cancel
    exact_mod_cast h_cancel
  have h_cell_mass_upper :
      balancing.cellMass ≤
        2 * (wz2PaperBalancedParentDegreeCap
              balancing multiplicityLevel : ENNReal) *
          active.fiberCellMass := by
    have h1 :
        balancing.cellMass =
          (2 ^ balancing.level : ENNReal) * active.fiberCellMass := by
      rw [balancing.cellMass_eq, active.fiberCellMass_eq]
      norm_cast
    rw [h1]
    have h2 : (1 : ENNReal) ≤ (2 ^ multiplicityLevel : ENNReal) := by
      exact_mod_cast Nat.one_le_pow multiplicityLevel 2 (by norm_num)
    have h4 :
        (2 ^ balancing.level : ENNReal) * active.fiberCellMass ≤
          2 * (2 ^ balancing.level : ENNReal) *
            (2 ^ multiplicityLevel : ENNReal) *
              active.fiberCellMass := by
      have h5 : (1 : ENNReal) ≤ 2 * (2 ^ multiplicityLevel : ENNReal) := by
        exact h2.trans (by
          have h6 :
              (2 ^ multiplicityLevel : ENNReal) ≤
                (2 ^ multiplicityLevel : ENNReal) +
                  (2 ^ multiplicityLevel : ENNReal) :=
            le_self_add
          simpa [two_mul] using h6)
      calc
        (2 ^ balancing.level : ENNReal) * active.fiberCellMass =
            (2 ^ balancing.level : ENNReal) * 1 *
              active.fiberCellMass := by ring
        _ ≤ (2 ^ balancing.level : ENNReal) *
              (2 * (2 ^ multiplicityLevel : ENNReal)) *
                active.fiberCellMass := by
          gcongr
        _ = 2 * (2 ^ balancing.level : ENNReal) *
              (2 ^ multiplicityLevel : ENNReal) *
                active.fiberCellMass := by ring
    simpa [wz2PaperBalancedParentDegreeCap, mul_assoc] using h4
  have h_cap_pos :
      0 < wz2PaperBalancedParentDegreeCap balancing multiplicityLevel := by
    simp [wz2PaperBalancedParentDegreeCap]
  exact
    ⟨h_cap_pos, h_degree, h_cell_incidence_upper,
      h_cell_mass_upper⟩

end Kakeya.Assouad

end
