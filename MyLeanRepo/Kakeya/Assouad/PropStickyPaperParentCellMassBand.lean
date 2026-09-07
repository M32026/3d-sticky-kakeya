import MyLeanRepo.Kakeya.Assouad.PropStickyPaperParentCellMassBandStatements

/-!
# Dyadic regularization of additive parent-cell incidence mass

For `shading := fiberBand.refined`, the sum of parent-cell masses over active
parents equals the cell incidence mass.  The total positive pair mass equals
the refined shading mass.  Dyadic binning then selects a nonempty common band
retaining a logarithmic fraction of that mass.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem wz2_paper_parent_cell_mass_band :
    WZ2PaperParentCellMassBandStatement := by
  intro delta rho hdelta hrho fine coarse cover sourceShading coarseCells
    availableFineCells balancing coarseData active fiberBand
  let shading := fiberBand.refined
  let allPairs := wz2PaperParentCellPairs active
  let positivePairs := wz2PaperPositiveParentCellPairs active shading
  let mass : (WZ2PaperCellIndex × Fin coarse.card) → ENNReal :=
    fun pair => wz2PaperParentCellMass cover shading pair

  have h_parentCellMass_eq : ∀ (cell : WZ2PaperCellIndex) (parent : Fin coarse.card),
      mass (cell, parent) =
        ∑ source ∈ cover.fiberIndices parent,
          volume (shading.carrier source ∩ wz1PaperGridCube rho cell) := by
    intro cell parent
    dsimp only [mass, wz2PaperParentCellMass, restrictPaperShading]
    let indices := wz2PaperFullFiberIndices fine coarse parent
    let equivalence : Fin indices.card ≃ indices :=
      (indices.orderIsoOfFin rfl).toEquiv
    have h_card : (cover.fullFiberSubfamily parent).family.card = indices.card := by
      rfl
    calc
      ∑ index : Fin (cover.fullFiberSubfamily parent).family.card,
          volume (shading.carrier ((cover.fullFiberSubfamily parent).embedding index) ∩
            wz1PaperGridCube rho cell)
        = ∑ source : indices,
            volume (shading.carrier source.val ∩ wz1PaperGridCube rho cell) := by
          exact Fintype.sum_equiv equivalence
            (fun index => volume (shading.carrier ((cover.fullFiberSubfamily parent).embedding index) ∩
              wz1PaperGridCube rho cell))
            (fun source => volume (shading.carrier source.val ∩ wz1PaperGridCube rho cell))
            (fun _ => rfl)
      _ = ∑ source ∈ indices, volume (shading.carrier source ∩ wz1PaperGridCube rho cell) := by
          exact Finset.sum_coe_sort indices (fun source =>
            volume (shading.carrier source ∩ wz1PaperGridCube rho cell))
      _ = ∑ source ∈ cover.fiberIndices parent,
          volume (shading.carrier source ∩ wz1PaperGridCube rho cell) := by
          exact Finset.sum_congr (cover.fullFiberIndices_eq parent) (fun _ _ => rfl)

  have h_inactive_zero : ∀ (cell : WZ2PaperCellIndex) (parent : Fin coarse.card),
      parent ∉ active.activeParents cell → mass (cell, parent) = 0 := by
    intro cell parent hnotactive
    have h_cell_not_in : cell ∉ coarseData.parentCells parent := by
      have h : active.activeParents cell =
          Finset.univ.filter (fun p => cell ∈ coarseData.parentCells p) :=
        active.activeParents_eq cell
      rw [h] at hnotactive
      simpa using hnotactive
    have h_each : ∀ source ∈ cover.fiberIndices parent,
        volume (shading.carrier source ∩ wz1PaperGridCube rho cell) = 0 := by
      intro source hsource
      have h_parent : cover.parent source = parent := by
        simpa [WZ1PaperTubeCover.fiberIndices, Finset.mem_filter, Finset.mem_univ] using hsource
      have h_subset : shading.carrier source ⊆ coarseData.coarseShading.carrier parent := by
        have h1 : shading.carrier source ⊆ balancing.refined.carrier source :=
          fiberBand.refined_subshading source
        have h2 : balancing.refined.carrier source ⊆
            coarseData.coarseShading.carrier (cover.parent source) :=
          coarseData.balancedCover.point_compatibility source
        rw [h_parent] at h2
        exact subset_trans h1 h2
      have h_disjoint : Disjoint (coarseData.coarseShading.carrier parent)
          (wz1PaperGridCube rho cell) := by
        rw [coarseData.coarseShading_carrier_eq parent]
        rw [Set.disjoint_left]
        intro x hx1 hx2
        have h_exists :
            ∃ c, c ∈ coarseData.parentCells parent ∧ x ∈ wz1PaperGridCube rho c := by
          simpa [Set.mem_biUnion] using hx1
        rcases h_exists with ⟨c, hc, hxc⟩
        have hne : c ≠ cell := by
          intro h
          rw [h] at hc
          exact h_cell_not_in hc
        have h_disj : Disjoint (wz1PaperGridCube rho c) (wz1PaperGridCube rho cell) :=
          wz1PaperGridCube_disjoint hne
        rw [Set.disjoint_left] at h_disj
        exact h_disj hxc hx2
      have h_disjoint2 : Disjoint (shading.carrier source) (wz1PaperGridCube rho cell) :=
        h_disjoint.mono_left h_subset
      have h_empty : shading.carrier source ∩ wz1PaperGridCube rho cell = ∅ :=
        Set.disjoint_iff_inter_eq_empty.mp h_disjoint2
      rw [h_empty] <;> simp
    rw [h_parentCellMass_eq cell parent]
    rw [Finset.sum_congr rfl h_each] <;> simp

  have h_general_identity : ∀ cell ∈ balancing.retainedCoarseCells,
      (∑ parent ∈ active.activeParents cell, mass (cell, parent)) =
        wz2PaperCellIncidenceMass (rho := rho) shading cell := by
    intro cell hcell
    have h_all_parents : (∑ parent : Fin coarse.card, mass (cell, parent)) =
        wz2PaperCellIncidenceMass (rho := rho) shading cell := by
      have h1 : ∀ parent, mass (cell, parent) =
          ∑ source ∈ cover.fiberIndices parent,
            volume (shading.carrier source ∩ wz1PaperGridCube rho cell) :=
        fun parent => h_parentCellMass_eq cell parent
      simp_rw [h1]
      have h_fiber_eq : ∀ parent : Fin coarse.card,
          cover.fiberIndices parent =
            Finset.univ.filter (fun source => cover.parent source = parent) := by
        intro parent
        ext source
        simp [WZ1PaperTubeCover.fiberIndices, Finset.mem_filter, Finset.mem_univ]
        <;> tauto
      simp_rw [h_fiber_eq]
      rw [Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ) (t := Finset.univ) (g := cover.parent)
        (fun _ _ => Finset.mem_univ _)]
      <;> rfl
    have h_sum_active : (∑ parent ∈ active.activeParents cell, mass (cell, parent)) =
        ∑ parent : Fin coarse.card, mass (cell, parent) := by
      rw [Finset.sum_subset (Finset.subset_univ (active.activeParents cell))]
      intro parent _ hnot
      exact h_inactive_zero cell parent hnot
    rw [h_sum_active, h_all_parents]

  have h_containment : ∀ source, shading.carrier source ⊆
      ⋃ cell ∈ balancing.retainedCoarseCells, wz1PaperGridCube rho cell := by
    intro source
    have h1 : shading.carrier source ⊆ balancing.refined.carrier source :=
      fiberBand.refined_subshading source
    have h2 : balancing.refined.carrier source ⊆
        coarseData.coarseShading.carrier (cover.parent source) :=
      coarseData.balancedCover.point_compatibility source
    have h3 : coarseData.coarseShading.carrier (cover.parent source) ⊆
        ⋃ cell ∈ balancing.retainedCoarseCells, wz1PaperGridCube rho cell := by
      rw [coarseData.coarseShading_carrier_eq (cover.parent source)]
      intro x hx
      have h_exists :
          ∃ c, c ∈ coarseData.parentCells (cover.parent source) ∧
            x ∈ wz1PaperGridCube rho c := by
        simpa [Set.mem_biUnion] using hx
      rcases h_exists with ⟨c, hc, hxc⟩
      have h4 : c ∈ balancing.retainedCoarseCells :=
        coarseData.parentCells_subset (cover.parent source) hc
      exact Set.mem_biUnion h4 hxc
    exact subset_trans h1 (subset_trans h2 h3)

  have h_vol_decomp : ∀ source, volume (shading.carrier source) =
      ∑ cell ∈ balancing.retainedCoarseCells,
        volume (shading.carrier source ∩ wz1PaperGridCube rho cell) := by
    intro source
    let A := shading.carrier source
    have hA_subset : A ⊆
        ⋃ cell ∈ balancing.retainedCoarseCells, wz1PaperGridCube rho cell :=
      h_containment source
    have h_disj : ∀ c1 ∈ balancing.retainedCoarseCells,
        ∀ c2 ∈ balancing.retainedCoarseCells,
          c1 ≠ c2 →
            Disjoint (A ∩ wz1PaperGridCube rho c1) (A ∩ wz1PaperGridCube rho c2) := by
      intro c1 _ c2 _ hne
      have h : Disjoint (wz1PaperGridCube rho c1) (wz1PaperGridCube rho c2) :=
        wz1PaperGridCube_disjoint hne
      exact h.mono (fun x hx => hx.2) (fun x hx => hx.2)
    have h_inter_union :
        A ∩ (⋃ cell ∈ balancing.retainedCoarseCells, wz1PaperGridCube rho cell) =
          ⋃ cell ∈ balancing.retainedCoarseCells,
            (A ∩ wz1PaperGridCube rho cell) := by
      ext x
      simp [Set.mem_biUnion]
      <;> tauto
    have h_eq :
        A = ⋃ cell ∈ balancing.retainedCoarseCells,
          (A ∩ wz1PaperGridCube rho cell) := by
      have h' :
          A ∩ (⋃ cell ∈ balancing.retainedCoarseCells, wz1PaperGridCube rho cell) =
            A := by
        rw [Set.inter_eq_left.mpr hA_subset]
      rw [h_inter_union] at h'
      exact h'.symm
    have h_eq' :
        volume A =
          volume (⋃ cell ∈ balancing.retainedCoarseCells,
            (A ∩ wz1PaperGridCube rho cell)) :=
      congr_arg volume h_eq
    have h_vol : volume A =
        ∑ cell ∈ balancing.retainedCoarseCells,
          volume (A ∩ wz1PaperGridCube rho cell) := by
      rw [h_eq']
      exact MeasureTheory.measure_biUnion_finset h_disj
        (fun _ _ =>
          shading.measurable_carrier source |>.inter
            (wz1PaperGridCube_measurable _))
    simpa [A] using h_vol

  have h_total_eq_mass :
      (∑ cell ∈ balancing.retainedCoarseCells,
          wz2PaperCellIncidenceMass (rho := rho) shading cell) =
        shading.mass := by
    dsimp only [wz2PaperCellIncidenceMass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro source _
    exact (h_vol_decomp source).symm

  have h1 :
      (∑ pair ∈ positivePairs, mass pair) =
        ∑ pair ∈ allPairs, mass pair := by
    have h_positivePairs_def :
        positivePairs = allPairs.filter (fun pair => mass pair ≠ 0) := by
      rfl
    rw [h_positivePairs_def, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro pair _
    by_cases h : mass pair ≠ 0
    · simp [h]
    · have h' : mass pair = 0 := by simpa using h
      simp [h']

  have h_allPairs_eq :
      allPairs = balancing.retainedCoarseCells.biUnion (fun cell =>
        (active.activeParents cell).image (fun parent => (cell, parent))) := by
    rfl

  have h2 : (∑ pair ∈ allPairs, mass pair) =
      ∑ cell ∈ balancing.retainedCoarseCells,
        ∑ parent ∈ active.activeParents cell, mass (cell, parent) := by
    rw [h_allPairs_eq]
    have h_disj : ∀ cell1 ∈ balancing.retainedCoarseCells,
        ∀ cell2 ∈ balancing.retainedCoarseCells, cell1 ≠ cell2 →
          Disjoint
            ((active.activeParents cell1).image (fun parent => (cell1, parent)))
            ((active.activeParents cell2).image (fun parent => (cell2, parent))) := by
      intro cell1 _ cell2 _ hne
      rw [Finset.disjoint_left]
      intro pair h1 h2
      rcases Finset.mem_image.mp h1 with ⟨p1, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨p2, _, h_eq⟩
      injection h_eq with h_cell _
      exact hne h_cell.symm
    rw [Finset.sum_biUnion h_disj]
    apply Finset.sum_congr rfl
    intro cell _
    rw [Finset.sum_image]
    <;> intro x y _ _ h <;> injection h <;> tauto

  have h_total_eq : (∑ pair ∈ positivePairs, mass pair) =
      ∑ cell ∈ balancing.retainedCoarseCells,
        wz2PaperCellIncidenceMass (rho := rho) shading cell := by
    rw [h1, h2]
    apply Finset.sum_congr rfl
    intro cell hcell
    exact h_general_identity cell hcell

  have h_balancing_mass_pos : 0 < balancing.refined.mass := by
    rcases balancing.retainedCoarseCells_nonempty with ⟨cell, hcell⟩
    have h4 : balancing.cellMass ≤
        ∑ parent ∈ active.activeParents cell,
          wz2PaperParentCellMass cover balancing.refined (cell, parent) :=
      active.cell_mass_le_sum_parent cell hcell
    have h5 : 0 < balancing.cellMass := balancing.cellMass_pos
    have h6 : 0 < ∑ parent ∈ active.activeParents cell,
        wz2PaperParentCellMass cover balancing.refined (cell, parent) :=
      lt_of_lt_of_le h5 h4
    have h7 :
        (∑ parent ∈ active.activeParents cell,
            wz2PaperParentCellMass cover balancing.refined (cell, parent)) ≤
          balancing.refined.mass := by
      rw [active.sum_parent_mass_eq_cell_incidence cell hcell]
      dsimp only [wz2PaperCellIncidenceMass]
      apply Finset.sum_le_sum
      intro source _
      have h_sub :
          (balancing.refined.carrier source ∩ wz1PaperGridCube rho cell) ⊆
            balancing.refined.carrier source := by
        intro x hx
        exact hx.1
      exact measure_mono h_sub
    exact lt_of_lt_of_le h6 h7

  have h_shading_mass_pos : 0 < shading.mass := by
    have h_ret :
        balancing.refined.mass /
            ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) ≤
          shading.mass :=
      fiberBand.retained_mass
    have h_pos :
        0 < balancing.refined.mass /
          ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) :=
      ENNReal.div_pos h_balancing_mass_pos.ne' ENNReal.coe_ne_top
    exact lt_of_lt_of_le h_pos h_ret

  have h_pos : 0 < ∑ pair ∈ positivePairs, mass pair := by
    rw [h_total_eq, h_total_eq_mass]
    exact h_shading_mass_pos

  have h_finite_each : ∀ pair ∈ allPairs, mass pair ≠ ⊤ := by
    intro pair _
    rw [h_parentCellMass_eq pair.1 pair.2]
    exact ENNReal.sum_ne_top.mpr (fun source _ =>
      ne_top_of_le_ne_top (wz1PaperGridCube_volume_ne_top hrho pair.1)
        (measure_mono (by intro x hx; exact hx.2)))

  have h_finite : (∑ pair ∈ positivePairs, mass pair) ≠ ⊤ := by
    have h_sub : positivePairs ⊆ allPairs := Finset.filter_subset _ _
    have h_le :
        (∑ pair ∈ positivePairs, mass pair) ≤
          ∑ pair ∈ allPairs, mass pair :=
      Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => by positivity)
    have h_all_finite : (∑ pair ∈ allPairs, mass pair) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr h_finite_each
    exact ne_top_of_le_ne_top h_all_finite h_le

  let α := {p // p ∈ positivePairs}
  let w : α → ENNReal := fun p => mass p.val
  let total : ENNReal := ∑ pair ∈ positivePairs, mass pair
  have htotal : total = ∑ i : α, w i := by
    have h : (∑ i : α, w i) =
        ∑ pair ∈ positivePairs, mass pair := by
      have h2 :
          Finset.image (Subtype.val : α → _) (Finset.univ : Finset α) =
            positivePairs := by
        ext x
        simp [α]
        <;> tauto
      have h3 : (∑ i : α, w i) =
          ∑ pair ∈ Finset.image (Subtype.val : α → _)
            (Finset.univ : Finset α), mass pair := by
        rw [Finset.sum_image]
        <;> intro x y _ _ h <;> exact Subtype.ext h
      rw [h3, h2]
    exact h.symm
  have h_main := ennreal_dyadic_bin w total htotal h_finite h_pos
  rcases h_main with
    ⟨bins, S, hbins_eq, hS_nonempty, h_mass, _hthreshold, h_c⟩
  rcases h_c with ⟨c, hc_pos, hc_band⟩

  let retainedPairs : Finset (WZ2PaperCellIndex × Fin coarse.card) :=
    Finset.image Subtype.val S
  have h_inj : Set.InjOn (Subtype.val : α → _) S := by
    intro x _ y _ hxy
    exact Subtype.ext hxy
  have h_sum_image :
      (∑ pair ∈ retainedPairs, mass pair) = ∑ i ∈ S, w i := by
    rw [Finset.sum_image h_inj] <;> rfl
  have h_card_alpha : Fintype.card α = positivePairs.card := by
    simp [α, Fintype.card_subtype]
  have h_bins_eq2 : (bins : ENNReal) =
      (Nat.log 2 (2 * positivePairs.card) + 1 : ENNReal) := by
    rw [hbins_eq, h_card_alpha] <;> norm_cast
  have hbins_pos : 0 < bins := by
    rw [hbins_eq] <;> simp <;> omega
  have hbins_ne_zero : (bins : ENNReal) ≠ 0 := by
    exact_mod_cast hbins_pos.ne'
  have hbins_ne_top : (bins : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top

  have h_retained_mass :
      total / (2 * (bins : ENNReal)) ≤ ∑ i ∈ S, w i := by
    have h : (∑ i ∈ S, w i) * (bins : ENNReal) ≥ total / 2 := h_mass
    have h2 :
        (∑ i ∈ S, w i) * (bins : ENNReal) * (bins : ENNReal)⁻¹ ≥
          (total / 2) * (bins : ENNReal)⁻¹ :=
      mul_le_mul_of_nonneg_right h (by positivity)
    have h3 :
        (∑ i ∈ S, w i) * (bins : ENNReal) * (bins : ENNReal)⁻¹ =
          ∑ i ∈ S, w i := by
      rw [mul_assoc,
        ENNReal.mul_inv_cancel hbins_ne_zero hbins_ne_top, mul_one]
    have h4 :
        (total / 2) * (bins : ENNReal)⁻¹ =
          total / (2 * (bins : ENNReal)) := by
      simp only [div_eq_mul_inv]
      rw [mul_assoc]
      congr 1
      have h5 :
          ((2 : ENNReal)⁻¹ * (bins : ENNReal)⁻¹) =
            ((2 : ENNReal) * (bins : ENNReal))⁻¹ := by
        exact (ENNReal.mul_inv (by norm_num) (by norm_num)).symm
      exact h5
    rw [h3, h4] at h2
    exact h2

  refine' ⟨0, retainedPairs, _, _, _, _, _, c, _, _, _, _⟩
  · intro pair hpair
    rcases Finset.mem_image.mp hpair with ⟨p, hp, rfl⟩
    exact p.prop
  · exact hS_nonempty.image _
  · exact h_total_eq
  · exact h_pos
  · exact h_finite
  · exact hc_pos
  · rcases hS_nonempty with ⟨i, hi⟩
    have h2 : c ≤ w i := (hc_band i hi).1
    have h_i_in_all : i.val ∈ allPairs :=
      Finset.filter_subset _ _ i.prop
    have h3 : w i ≠ ⊤ := h_finite_each i.val h_i_in_all
    exact ne_top_of_le_ne_top h3 h2
  · intro pair hpair
    rcases Finset.mem_image.mp hpair with ⟨p, hp, rfl⟩
    exact hc_band p hp
  · have h_goal1 :
        (∑ pair ∈
            wz2PaperPositiveParentCellPairs active fiberBand.refined,
            wz2PaperParentCellMass cover fiberBand.refined pair) =
          total := by
      rfl
    have h_goal2 :
        ((Nat.log 2
            (2 *
              (wz2PaperPositiveParentCellPairs
                active fiberBand.refined).card) + 1 : ENNReal)) =
          (bins : ENNReal) := by
      exact h_bins_eq2.symm
    have h_sum_image2 :
        (∑ pair ∈ retainedPairs,
            wz2PaperParentCellMass cover fiberBand.refined pair) =
          ∑ i ∈ S, w i := by
      exact h_sum_image
    rw [h_goal1, h_goal2, h_sum_image2]
    exact h_retained_mass

end Kakeya.Assouad

end
