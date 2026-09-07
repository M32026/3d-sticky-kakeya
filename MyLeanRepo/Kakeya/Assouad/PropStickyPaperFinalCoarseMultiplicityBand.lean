import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalCoarseMultiplicityBandStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers

/-!
# Proof of final coarse multiplicity band

Dyadically pigeonhole the point multiplicity of the induced coarse shading,
weighted by final fine shaded mass.  Restrict both shadings by the same whole
rho-cells and preserve exact balance and the fine fiber band.
-/

noncomputable section

namespace Kakeya.Assouad

open Finset MeasureTheory

attribute [local instance] Classical.propDecidable

private lemma restrict_mult_eq
    {scale : ℝ} {family : Kakeya.Streamlined.TubeFamily scale}
    (R : Set Point3) (original selected : WZ1PaperTubeShading family)
    (hcarrier : ∀ source, selected.carrier source = original.carrier source ∩ R)
    {point : Point3} (hpoint : point ∈ R) :
    selected.pointMultiplicity point = original.pointMultiplicity point := by
  classical
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  apply Finset.filter_congr
  intro source _
  rw [hcarrier source]
  simp [hpoint]

private lemma restrict_union_eq
    {scale : ℝ} {family : Kakeya.Streamlined.TubeFamily scale}
    (R : Set Point3) (original selected : WZ1PaperTubeShading family)
    (hcarrier : ∀ source, selected.carrier source = original.carrier source ∩ R) :
    selected.union = original.union ∩ R := by
  ext point
  simp only [Kakeya.Streamlined.Shading.union, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨source, hpoint⟩
    rw [hcarrier source] at hpoint
    exact ⟨⟨source, hpoint.1⟩, hpoint.2⟩
  · rintro ⟨⟨source, h1⟩, h2⟩
    refine ⟨source, ?_⟩
    rw [hcarrier source]
    exact ⟨h1, h2⟩

private lemma fiber_restrict_mult_eq
    {delta rho : ℝ} {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (R : Set Point3) (original selected : WZ1PaperTubeShading fine)
    (hcarrier : ∀ source, selected.carrier source = original.carrier source ∩ R)
    (parent : Fin coarse.card) {point : Point3} (hpoint : point ∈ R) :
    (restrictPaperShading (cover.fullFiberSubfamily parent) selected).pointMultiplicity point =
    (restrictPaperShading (cover.fullFiberSubfamily parent) original).pointMultiplicity point := by
  let subfamily := cover.fullFiberSubfamily parent
  have h : ∀ (index : Fin subfamily.family.card),
      (restrictPaperShading subfamily selected).carrier index =
      (restrictPaperShading subfamily original).carrier index ∩ R := by
    intro index
    simpa [restrictPaperShading] using hcarrier (subfamily.embedding index)
  exact restrict_mult_eq R (restrictPaperShading subfamily original)
    (restrictPaperShading subfamily selected) h hpoint

theorem wz2_paper_final_coarse_multiplicity_band :
    WZ2PaperFinalCoarseMultiplicityBandStatement := by
  intro delta rho hdelta hrho fine coarse cover sourceShading coarseCells
    availableFineCells balancing coarseData active fiberBand pairBand
    restriction finalFine induced

  let refined := finalFine.exact.refined
  let retainedCells := finalFine.exact.retainedCoarseCells
  let N : ℕ := Nat.log 2 coarse.card + 1

  let m (cell : WZ2PaperCellIndex) : ℕ := (induced.activeParents cell).card

  let l (cell : WZ2PaperCellIndex) : ℕ := Nat.log 2 (m cell)

  let cellsAtLevel (k : ℕ) : Finset WZ2PaperCellIndex :=
    retainedCells.filter (fun cell => l cell = k)

  let massInCell (cell : WZ2PaperCellIndex) : ENNReal :=
    ∑ source : Fin fine.card,
      volume (refined.carrier source ∩ wz1PaperGridCube rho cell)

  let massAtLevel (k : ℕ) : ENNReal :=
    ∑ cell ∈ cellsAtLevel k, massInCell cell

  have hN_pos : 0 < N := by
    dsimp only [N]
    exact Nat.succ_pos _

  have h_m_pos : ∀ cell ∈ retainedCells, 0 < m cell := by
    intro cell hcell
    have h1 : (induced.activeParents cell).Nonempty :=
      induced.activeParents_nonempty cell hcell
    exact Finset.card_pos.mpr h1

  have h_m_le : ∀ cell ∈ retainedCells, m cell ≤ coarse.card := by
    intro cell _
    have h : (induced.activeParents cell).card ≤
        (Finset.univ : Finset (Fin coarse.card)).card :=
      Finset.card_le_univ _
    have h2 : (Finset.univ : Finset (Fin coarse.card)).card = coarse.card := by simp
    rw [h2] at h
    exact h

  have h_l_range : ∀ cell ∈ retainedCells, l cell ∈ Finset.range N := by
    intro cell hcell
    have h1 : m cell ≤ coarse.card := h_m_le cell hcell
    have h2 : l cell ≤ Nat.log 2 coarse.card := Nat.log_mono_right h1
    simp only [Finset.mem_range, N] <;> omega

  have h_partition : ∀ cell ∈ retainedCells, cell ∈ cellsAtLevel (l cell) := by
    intro cell hcell
    apply Finset.mem_filter.mpr
    exact ⟨hcell, by rfl⟩

  have h_disjoint_levels : ∀ k1 ∈ Finset.range N, ∀ k2 ∈ Finset.range N,
      k1 ≠ k2 → Disjoint (cellsAtLevel k1) (cellsAtLevel k2) := by
    intro k1 _ k2 _ hne
    simp only [cellsAtLevel, Finset.disjoint_left]
    intro cell h1 h2
    have h3 : l cell = k1 := (Finset.mem_filter.mp h1).2
    have h4 : l cell = k2 := (Finset.mem_filter.mp h2).2
    have h5 : k1 = k2 := h3.symm.trans h4
    exact hne h5

  have h_union_levels :
      (Finset.biUnion (Finset.range N) cellsAtLevel) = retainedCells := by
    ext cell
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨k, _, hk⟩
      exact (Finset.mem_filter.mp hk).1
    · intro hcell
      exact ⟨l cell, h_l_range cell hcell, h_partition cell hcell⟩

  have h_fine_containment :
      ∀ fineCell ∈ finalFine.exact.retainedFineCells,
        ∃ coarseCell ∈ retainedCells,
          wz1PaperGridCube delta fineCell ⊆ wz1PaperGridCube rho coarseCell := by
    intro fineCell hfineCell
    have h_eq : finalFine.exact.retainedFineCells =
        retainedCells.biUnion finalFine.exact.selectedFineCells :=
      finalFine.exact.retainedFineCells_eq
    have h_in_biUnion :
        fineCell ∈ retainedCells.biUnion finalFine.exact.selectedFineCells := by
      rw [← h_eq] <;> exact hfineCell
    rcases Finset.mem_biUnion.mp h_in_biUnion with
      ⟨coarseCell, hcoarseCell, hsel⟩
    have h1 : fineCell ∈ finalFine.availableFinalFineCells coarseCell :=
      finalFine.exact.selectedFineCells_subset coarseCell hcoarseCell hsel
    have h2 : coarseCell ∈ finalFine.finalCoarseCells :=
      finalFine.exact.retainedCoarseCells_subset hcoarseCell
    have h3 : wz1PaperGridCube delta fineCell ⊆
        wz1PaperGridCube rho coarseCell :=
      (finalFine.availableFinalFineCells_ready coarseCell h2 fineCell h1).2
    exact ⟨coarseCell, hcoarseCell, h3⟩

  have h_refined_union_subset :
      refined.union ⊆ ⋃ cell ∈ retainedCells, wz1PaperGridCube rho cell := by
    rw [finalFine.exact.refined_union_eq]
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨fineCell, hfineCell, hpointCell⟩
    rcases h_fine_containment fineCell hfineCell with
      ⟨coarseCell, hcoarseCell, hcont⟩
    exact Set.mem_iUnion₂.mpr ⟨coarseCell, hcoarseCell, hcont hpointCell⟩

  have h_delta_cell_in_rho_cell :
      ∀ point ∈ refined.union,
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          wz1PaperGridCube rho (wz1PaperGridIndex rho point) := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp (finalFine.exact.refined_union_eq ▸ hpoint)
      with ⟨fineCell, hfineCell, hpointCell⟩
    have h_index1 : wz1PaperGridIndex delta point = fineCell :=
      (mem_wz1PaperGridCube delta fineCell point).mp hpointCell
    rcases h_fine_containment fineCell hfineCell with
      ⟨coarseCell, hcoarseCell, hcont⟩
    have h_point_in_rho : point ∈ wz1PaperGridCube rho coarseCell :=
      hcont hpointCell
    have h_index2 : wz1PaperGridIndex rho point = coarseCell :=
      (mem_wz1PaperGridCube rho coarseCell point).mp h_point_in_rho
    rw [h_index1, h_index2]
    exact hcont

  have h_mass_decomp :
      refined.mass = ∑ cell ∈ retainedCells, massInCell cell := by
    have hcarrier : ∀ (source : Fin fine.card),
        refined.carrier source ⊆
          ⋃ cell ∈ retainedCells, wz1PaperGridCube rho cell := by
      intro source x hx
      exact h_refined_union_subset ⟨source, hx⟩
    have hper_source : ∀ (source : Fin fine.card),
        volume (refined.carrier source) =
          ∑ cell ∈ retainedCells,
            volume (refined.carrier source ∩ wz1PaperGridCube rho cell) := by
      intro source
      let pieces : WZ2PaperCellIndex → Set Point3 := fun cell =>
        refined.carrier source ∩ wz1PaperGridCube rho cell
      have hdisj' : Set.PairwiseDisjoint (↑retainedCells) pieces := by
        intro i _ j _ hne
        have h : Disjoint (wz1PaperGridCube rho i) (wz1PaperGridCube rho j) :=
          wz1PaperGridCube_disjoint hne
        exact h.mono Set.inter_subset_right Set.inter_subset_right
      have hmeas' : ∀ cell ∈ retainedCells, MeasurableSet (pieces cell) := by
        intro cell _
        exact (refined.measurable_carrier source).inter
          (wz1PaperGridCube_measurable cell)
      have hpartition :
          refined.carrier source = ⋃ cell ∈ retainedCells, pieces cell := by
        ext x
        simp only [pieces, Set.mem_iUnion, Set.mem_inter_iff]
        constructor
        · intro hx
          have hcov :
              x ∈ (⋃ cell ∈ retainedCells, wz1PaperGridCube rho cell) :=
            hcarrier source hx
          simp only [Set.mem_iUnion] at hcov
          rcases hcov with ⟨cell, hcell, hxi⟩
          exact ⟨cell, hcell, hx, hxi⟩
        · rintro ⟨cell, _, hx, _⟩
          exact hx
      calc
        volume (refined.carrier source)
          = volume (⋃ cell ∈ retainedCells, pieces cell) := by rw [hpartition]
        _ = ∑ cell ∈ retainedCells, volume (pieces cell) :=
          MeasureTheory.measure_biUnion_finset hdisj' hmeas'
    calc
      refined.mass
        = ∑ source : Fin fine.card, volume (refined.carrier source) := rfl
      _ = ∑ source : Fin fine.card,
            ∑ cell ∈ retainedCells,
              volume (refined.carrier source ∩
                wz1PaperGridCube rho cell) := by
          apply Finset.sum_congr rfl
          intro source _
          exact hper_source source
      _ = ∑ cell ∈ retainedCells,
            ∑ source : Fin fine.card,
              volume (refined.carrier source ∩
                wz1PaperGridCube rho cell) := by
          rw [Finset.sum_comm]
      _ = ∑ cell ∈ retainedCells, massInCell cell := by rfl

  have h_sum_levels :
      ∑ k ∈ Finset.range N, massAtLevel k = refined.mass := by
    have h : ∑ k ∈ Finset.range N, massAtLevel k =
        ∑ cell ∈ (Finset.biUnion (Finset.range N) cellsAtLevel),
          massInCell cell := by
      rw [Finset.sum_biUnion h_disjoint_levels] <;> rfl
    rw [h, h_union_levels, h_mass_decomp]

  have h_pigeonhole : ∃ k ∈ Finset.range N,
      (N : ENNReal) * massAtLevel k ≥ refined.mass := by
    have h_nonempty : (Finset.range N).Nonempty :=
      Finset.nonempty_range_iff.mpr (ne_of_gt hN_pos)
    have h_max : ∃ k ∈ Finset.range N,
        ∀ l ∈ Finset.range N, massAtLevel l ≤ massAtLevel k :=
      Finset.exists_max_image (Finset.range N) massAtLevel h_nonempty
    rcases h_max with ⟨k, hk, hmax⟩
    have h_le : ∑ l ∈ Finset.range N, massAtLevel l ≤
        (Finset.range N).card * massAtLevel k := by
      calc
        ∑ l ∈ Finset.range N, massAtLevel l
          ≤ ∑ l ∈ Finset.range N, massAtLevel k := by
            apply Finset.sum_le_sum
            intro l hl
            exact hmax l hl
        _ = (Finset.range N).card * massAtLevel k := by
          simp [Finset.sum_const]
    have h_card : (Finset.range N).card = N := by simp
    rw [h_card] at h_le
    rw [h_sum_levels] at h_le
    exact ⟨k, hk, h_le⟩

  rcases h_pigeonhole with ⟨level, hlevel_range, hge⟩

  let selectedCells := cellsAtLevel level
  let selectedRegion : Set Point3 :=
    ⋃ cell ∈ selectedCells, wz1PaperGridCube rho cell

  have h_selected_subset : selectedCells ⊆ retainedCells :=
    Finset.filter_subset _ _

  have h_refined_mass_pos : 0 < refined.mass := by
    rcases finalFine.exact.retainedCoarseCells_nonempty with ⟨cell, hcell⟩
    have h_cell_mass :
        volume (refined.union ∩ wz1PaperGridCube rho cell) =
          finalFine.exact.cellMass :=
      finalFine.exact.fine_cell_mass cell hcell
    have h_pos :
        0 < volume (refined.union ∩ wz1PaperGridCube rho cell) := by
      rw [h_cell_mass] <;> exact finalFine.exact.cellMass_pos
    have h_union_bound :
        volume (refined.union ∩ wz1PaperGridCube rho cell) ≤
          massInCell cell := by
      have h_eq :
          refined.union ∩ wz1PaperGridCube rho cell =
            ⋃ source : Fin fine.card,
              (refined.carrier source ∩ wz1PaperGridCube rho cell) := by
        ext point
        simp [Kakeya.Streamlined.Shading.union, Set.mem_inter_iff] <;> tauto
      rw [h_eq]
      let f : Fin fine.card → Set Point3 := fun source =>
        refined.carrier source ∩ wz1PaperGridCube rho cell
      have h_bound :
          volume (⋃ source ∈ (Finset.univ : Finset (Fin fine.card)),
              f source) ≤
            ∑ source ∈ (Finset.univ : Finset (Fin fine.card)),
              volume (f source) :=
        MeasureTheory.measure_biUnion_finset_le
          (I := (Finset.univ)) (s := f)
      simpa [f, massInCell] using h_bound
    have h_mass_in_cell_pos : 0 < massInCell cell :=
      h_pos.trans_le h_union_bound
    have h : massInCell cell ≤ refined.mass := by
      rw [h_mass_decomp]
      exact Finset.single_le_sum (fun _ _ => by positivity) hcell
    exact h_mass_in_cell_pos.trans_le h

  have h_selected_nonempty : selectedCells.Nonempty := by
    by_contra h
    have h_empty : selectedCells = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using h
    have h_mass_zero : massAtLevel level = 0 := by
      have h9 : cellsAtLevel level = ∅ := by
        simpa [selectedCells] using h_empty
      simp [massAtLevel, h9]
    rw [h_mass_zero] at hge
    have h_contra : refined.mass ≤ 0 := by simpa [mul_zero] using hge
    exact not_le.mpr h_refined_mass_pos h_contra

  have h_band : ∀ cell ∈ selectedCells,
      (2 ^ level : ℕ) ≤ m cell ∧ m cell < (2 ^ (level + 1) : ℕ) := by
    intro cell hcell
    have h1 : l cell = level := (Finset.mem_filter.mp hcell).2
    have h2 : 0 < m cell := h_m_pos cell (h_selected_subset hcell)
    have h3 : (2 ^ level : ℕ) ≤ m cell := by
      rw [← h1]
      exact Nat.pow_log_le_self 2 h2.ne'
    have h4 : m cell < (2 ^ (level + 1) : ℕ) := by
      rw [← h1]
      exact Nat.lt_pow_succ_log_self (by norm_num) (m cell)
    exact ⟨h3, h4⟩

  let selectedCoarseShading : WZ1PaperTubeShading coarse :=
    wz2RefinedShading induced.coarseShading selectedCells

  let selectedFineShading : WZ1PaperTubeShading fine :=
    { carrier := fun source => refined.carrier source ∩ selectedRegion
      measurable_carrier := fun source =>
        (refined.measurable_carrier source).inter
          (MeasurableSet.iUnion fun _ =>
            MeasurableSet.iUnion fun _ => wz1PaperGridCube_measurable _)
      subset_body := fun source =>
        Set.inter_subset_left.trans (refined.subset_body source) }

  have h_coarse_carrier : ∀ parent,
      selectedCoarseShading.carrier parent =
        induced.coarseShading.carrier parent ∩ selectedRegion := by
    intro parent
    rfl

  have h_coarse_cubical :
      WZ1PaperIsCubicalShading selectedCoarseShading :=
    wz2RefinedShading_cubical induced.coarse_cubical

  have h_coarse_union :
      selectedCoarseShading.union = selectedRegion := by
    have h1 : selectedCoarseShading.union =
        induced.coarseShading.union ∩ selectedRegion :=
      wz2RefinedShading_union_inter
    rw [h1]
    have h_subset : selectedRegion ⊆ induced.coarseShading.union := by
      rw [induced.coarse_union_eq]
      intro point hpoint
      rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, _⟩
      exact Set.mem_iUnion₂.mpr
        ⟨cell, h_selected_subset hcell, ‹_›⟩
    rw [Set.inter_eq_right.mpr h_subset]

  have h_coarse_mult_eq :
      ∀ (cell : WZ2PaperCellIndex), cell ∈ retainedCells →
        ∀ point ∈ wz1PaperGridCube rho cell,
          induced.coarseShading.pointMultiplicity point = m cell := by
    intro cell hcell point hpoint
    have h_rep_in_cell :
        induced.representative cell ∈ wz1PaperGridCube rho cell :=
      induced.representative_mem cell
    have h_same :
        wz1PaperGridIndex rho point =
          wz1PaperGridIndex rho (induced.representative cell) := by
      have h1 : wz1PaperGridIndex rho point = cell :=
        (mem_wz1PaperGridCube rho cell point).mp hpoint
      have h2 :
          wz1PaperGridIndex rho (induced.representative cell) = cell :=
        (mem_wz1PaperGridCube rho cell
          (induced.representative cell)).mp h_rep_in_cell
      exact h1.trans h2.symm
    have h_mult_eq :
        induced.coarseShading.pointMultiplicity point =
          induced.coarseShading.pointMultiplicity
            (induced.representative cell) :=
      induced.coarse_cubical.pointMultiplicity_eq_of_same_cell h_same
    have h_card_eq :
        induced.coarseShading.pointMultiplicity
            (induced.representative cell) =
          m cell :=
      (induced.activeParents_card_eq cell hcell).symm
    rw [h_mult_eq, h_card_eq]

  have h_coarse_band : ∀ point ∈ selectedRegion,
      (2 ^ level : ENNReal) ≤
          (selectedCoarseShading.pointMultiplicity point : ENNReal) ∧
        (selectedCoarseShading.pointMultiplicity point : ENNReal) <
          (2 ^ (level + 1) : ENNReal) := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨cell, hcell, hpointCell⟩
    have h_mult1 :
        selectedCoarseShading.pointMultiplicity point =
          induced.coarseShading.pointMultiplicity point :=
      restrict_mult_eq selectedRegion induced.coarseShading
        selectedCoarseShading h_coarse_carrier hpoint
    rw [h_mult1]
    have h_mult2 :
        induced.coarseShading.pointMultiplicity point = m cell :=
      h_coarse_mult_eq cell (h_selected_subset hcell) point hpointCell
    rw [h_mult2]
    have h_band' := h_band cell hcell
    constructor
    · exact_mod_cast h_band'.1
    · exact_mod_cast h_band'.2

  have h_fine_carrier : ∀ source,
      selectedFineShading.carrier source =
        refined.carrier source ∩ selectedRegion := by
    intro source
    rfl

  have h_fine_cubical :
      WZ1PaperIsCubicalShading selectedFineShading := by
    intro source point hpoint
    have h1 : point ∈ refined.carrier source := hpoint.1
    have h2 : point ∈ selectedRegion := hpoint.2
    have h3 :
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          refined.carrier source :=
      finalFine.exact.refined_cubical source point h1
    have h4 : point ∈ refined.union := ⟨source, h1⟩
    have h5 :
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          selectedRegion := by
      have h6 :
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho (wz1PaperGridIndex rho point) :=
        h_delta_cell_in_rho_cell point h4
      rcases Set.mem_iUnion₂.mp h2 with
        ⟨cell, hcell, hpointCell⟩
      have h7 : wz1PaperGridIndex rho point = cell :=
        (mem_wz1PaperGridCube rho cell point).mp hpointCell
      rw [h7] at h6
      intro x hx
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, h6 hx⟩
    intro y hy
    exact ⟨h3 hy, h5 hy⟩

  have h_fine_union :
      selectedFineShading.union = refined.union ∩ selectedRegion :=
    restrict_union_eq selectedRegion refined selectedFineShading
      h_fine_carrier

  have h_point_compat : ∀ source point,
      point ∈ selectedFineShading.carrier source →
        point ∈ selectedCoarseShading.carrier (cover.parent source) := by
    intro source point hpoint
    have h1 : point ∈ refined.carrier source := hpoint.1
    have h2 : point ∈ selectedRegion := hpoint.2
    have h3 :
        point ∈ induced.coarseShading.carrier (cover.parent source) :=
      induced.point_compatibility source point h1
    exact ⟨h3, h2⟩

  have h_selected_fine_union_subset :
      selectedFineShading.union ⊆
        ⋃ cell ∈ selectedCells, wz1PaperGridCube rho cell := by
    rw [h_fine_union] <;> exact Set.inter_subset_right
  have h_carrier_intersect_eq :
      ∀ (source : Fin fine.card), ∀ cell ∈ selectedCells,
        volume
            (selectedFineShading.carrier source ∩
              wz1PaperGridCube rho cell) =
          volume
            (refined.carrier source ∩ wz1PaperGridCube rho cell) := by
    intro source cell hcell
    have h_cell_subset :
        wz1PaperGridCube rho cell ⊆ selectedRegion := by
      intro x hx
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hx⟩
    have h_eq :
        selectedFineShading.carrier source ∩
            wz1PaperGridCube rho cell =
          refined.carrier source ∩ wz1PaperGridCube rho cell := by
      rw [h_fine_carrier source]
      rw [Set.inter_assoc]
      have h :
          selectedRegion ∩ wz1PaperGridCube rho cell =
            wz1PaperGridCube rho cell := by
        rw [Set.inter_eq_right.mpr h_cell_subset]
      rw [h] <;> rfl
    rw [h_eq]
  have h_fine_mass :
      selectedFineShading.mass = massAtLevel level := by
    have hcarrier : ∀ (source : Fin fine.card),
        selectedFineShading.carrier source ⊆
          ⋃ cell ∈ selectedCells, wz1PaperGridCube rho cell := by
      intro source x hx
      exact h_selected_fine_union_subset ⟨source, hx⟩
    have hper_source : ∀ (source : Fin fine.card),
        volume (selectedFineShading.carrier source) =
          ∑ cell ∈ selectedCells,
            volume
              (selectedFineShading.carrier source ∩
                wz1PaperGridCube rho cell) := by
      intro source
      let pieces : WZ2PaperCellIndex → Set Point3 := fun cell =>
        selectedFineShading.carrier source ∩
          wz1PaperGridCube rho cell
      have hdisj' : Set.PairwiseDisjoint (↑selectedCells) pieces := by
        intro i _ j _ hne
        have h :
            Disjoint (wz1PaperGridCube rho i)
              (wz1PaperGridCube rho j) :=
          wz1PaperGridCube_disjoint hne
        exact h.mono Set.inter_subset_right Set.inter_subset_right
      have hmeas' :
          ∀ cell ∈ selectedCells, MeasurableSet (pieces cell) := by
        intro cell _
        exact (selectedFineShading.measurable_carrier source).inter
          (wz1PaperGridCube_measurable cell)
      have hpartition :
          selectedFineShading.carrier source =
            ⋃ cell ∈ selectedCells, pieces cell := by
        ext x
        simp only [pieces, Set.mem_iUnion, Set.mem_inter_iff]
        constructor
        · intro hx
          have hcov :
              x ∈ (⋃ cell ∈ selectedCells,
                wz1PaperGridCube rho cell) :=
            hcarrier source hx
          simp only [Set.mem_iUnion] at hcov
          rcases hcov with ⟨cell, hcell, hxi⟩
          exact ⟨cell, hcell, hx, hxi⟩
        · rintro ⟨cell, _, hx, _⟩
          exact hx
      calc
        volume (selectedFineShading.carrier source)
          = volume (⋃ cell ∈ selectedCells, pieces cell) := by
              rw [hpartition]
        _ = ∑ cell ∈ selectedCells, volume (pieces cell) :=
          MeasureTheory.measure_biUnion_finset hdisj' hmeas'
    have h_main : selectedFineShading.mass =
        ∑ cell ∈ selectedCells, ∑ source : Fin fine.card,
          volume
            (selectedFineShading.carrier source ∩
              wz1PaperGridCube rho cell) := by
      calc
        selectedFineShading.mass
          = ∑ source : Fin fine.card,
              volume (selectedFineShading.carrier source) := rfl
        _ = ∑ source : Fin fine.card,
              ∑ cell ∈ selectedCells,
                volume
                  (selectedFineShading.carrier source ∩
                    wz1PaperGridCube rho cell) := by
            apply Finset.sum_congr rfl
            intro source _
            exact hper_source source
        _ = ∑ cell ∈ selectedCells, ∑ source : Fin fine.card,
              volume
                (selectedFineShading.carrier source ∩
                  wz1PaperGridCube rho cell) := by
            rw [Finset.sum_comm]
    rw [h_main]
    apply Finset.sum_congr rfl
    intro cell hcell
    apply Finset.sum_congr rfl
    intro source _
    exact h_carrier_intersect_eq source cell hcell

  have h_mass_retention :
      refined.mass / ((N : ENNReal)) ≤ selectedFineShading.mass := by
    rw [h_fine_mass]
    have h : refined.mass ≤ (N : ENNReal) * massAtLevel level := hge
    have hdiv :
        refined.mass / (N : ENNReal) ≤ massAtLevel level := by
      have h9 :
          refined.mass ≤ (N : ENNReal) * massAtLevel level := hge
      by_cases htop : massAtLevel level = ⊤
      · rw [htop] <;> simp
      · have hN_ne_zero : (N : ENNReal) ≠ 0 := by positivity
        have hN_ne_top : (N : ENNReal) ≠ ⊤ := by simp
        have h1 : (N : ENNReal) * (N : ENNReal)⁻¹ = 1 :=
          ENNReal.mul_inv_cancel hN_ne_zero hN_ne_top
        have h_cancel :
            ((N : ENNReal) * massAtLevel level) / (N : ENNReal) =
              massAtLevel level := by
          calc
            ((N : ENNReal) * massAtLevel level) / (N : ENNReal)
              = ((N : ENNReal) * massAtLevel level) *
                  (N : ENNReal)⁻¹ := by rfl
            _ = (N : ENNReal) *
                  (massAtLevel level * (N : ENNReal)⁻¹) := by
              rw [mul_assoc]
            _ = (N : ENNReal) *
                  ((N : ENNReal)⁻¹ * massAtLevel level) := by
              rw [mul_comm (massAtLevel level) (N : ENNReal)⁻¹]
            _ = ((N : ENNReal) * (N : ENNReal)⁻¹) *
                  massAtLevel level := by
              rw [← mul_assoc]
            _ = 1 * massAtLevel level := by rw [h1]
            _ = massAtLevel level := by simp
        have h10 :
            refined.mass / (N : ENNReal) ≤
              ((N : ENNReal) * massAtLevel level) /
                (N : ENNReal) := by
          gcongr
        rw [h_cancel] at h10
        exact h10
    exact hdiv

  have h_selected_cell_mass : ∀ cell ∈ selectedCells,
      volume
          (selectedFineShading.union ∩ wz1PaperGridCube rho cell) =
        finalFine.exact.cellMass := by
    intro cell hcell
    have h_cell_subset :
        wz1PaperGridCube rho cell ⊆ selectedRegion := by
      intro x hx
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hx⟩
    have h_eq :
        selectedFineShading.union ∩ wz1PaperGridCube rho cell =
          refined.union ∩ wz1PaperGridCube rho cell := by
      rw [h_fine_union]
      rw [Set.inter_assoc]
      have h :
          selectedRegion ∩ wz1PaperGridCube rho cell =
            wz1PaperGridCube rho cell := by
        rw [Set.inter_eq_right.mpr h_cell_subset]
      rw [h] <;> rfl
    rw [h_eq]
    exact finalFine.exact.fine_cell_mass cell
      (h_selected_subset hcell)

  have h_fiber_band : ∀ parent point,
      point ∈
          (restrictPaperShading
            (cover.fullFiberSubfamily parent)
            selectedFineShading).union →
        (2 ^ fiberBand.level : ENNReal) ≤
            ((restrictPaperShading
              (cover.fullFiberSubfamily parent)
              selectedFineShading).pointMultiplicity point : ENNReal) ∧
          ((restrictPaperShading
            (cover.fullFiberSubfamily parent)
            selectedFineShading).pointMultiplicity point : ENNReal) <
            (2 ^ (fiberBand.level + 1) : ENNReal) := by
    intro parent point hpoint
    have h_in_selected : point ∈ selectedRegion := by
      rcases hpoint with ⟨index, hpoint⟩
      exact hpoint.2
    have h_mult_eq :
        (restrictPaperShading
            (cover.fullFiberSubfamily parent)
            selectedFineShading).pointMultiplicity point =
          (restrictPaperShading
            (cover.fullFiberSubfamily parent)
            refined).pointMultiplicity point :=
      fiber_restrict_mult_eq cover selectedRegion refined
        selectedFineShading h_fine_carrier parent h_in_selected
    rw [h_mult_eq]
    have h_in_refined_union :
        point ∈
          (restrictPaperShading
            (cover.fullFiberSubfamily parent) refined).union := by
      rcases hpoint with ⟨index, hpoint⟩
      exact ⟨index, hpoint.1⟩
    exact finalFine.fiber_multiplicity_band parent point
      h_in_refined_union

  refine' ⟨_⟩
  exact
    { level := level
      selectedCells := selectedCells
      selectedCells_subset := h_selected_subset
      selectedCells_nonempty := h_selected_nonempty
      selectedRegion := selectedRegion
      selectedRegion_eq := rfl
      selectedCoarseShading := selectedCoarseShading
      selectedCoarse_carrier_eq := h_coarse_carrier
      selectedCoarse_cubical := h_coarse_cubical
      selectedCoarse_union_eq := h_coarse_union
      coarse_multiplicity_band := h_coarse_band
      selectedFineShading := selectedFineShading
      selectedFine_carrier_eq := h_fine_carrier
      selectedFine_subshading := fun _ => Set.inter_subset_left
      selectedFine_cubical := h_fine_cubical
      selectedFine_union_eq := h_fine_union
      point_compatibility := h_point_compat
      selectedFine_mass_retention := h_mass_retention
      selected_cell_mass := h_selected_cell_mass
      fiber_multiplicity_band := h_fiber_band }

end Kakeya.Assouad

end
