import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers

/-!
WZ2 Section 6 `prop: sticky`: exact whole-cell balancing after boundary
pruning.

Dyadically select coarse cells by the number of surviving literal
`delta`-cells, retain the same number of whole fine cells in every selected
literal `rho`-cell, and prove the resulting exact cell-mass identity.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Finset

attribute [local instance] Classical.propDecidable

theorem wz2_prop_sticky_exact_cell_balancing :
    WZ2PropStickyExactCellBalancingStatement := by
  dsimp only [WZ2PropStickyExactCellBalancingStatement]
  intro delta rho hdelta hrho fine shading hcubical coarseCells hcoarse_nonempty
    availableFineCells havailable_nonempty hcontainment_active
  let f : WZ2PaperCellIndex → ℕ := fun c => (availableFineCells c).card
  let N : ℕ := ∑ c ∈ coarseCells, f c
  have hN_pos : 0 < N := Finset.sum_pos (fun c hc => (havailable_nonempty c hc).card_pos) hcoarse_nonempty
  have hpos : ∀ c ∈ coarseCells, 0 < f c := fun c hc => (havailable_nonempty c hc).card_pos
  rcases dyadic_band_pigeonhole coarseCells f hcoarse_nonempty hpos with
    ⟨level, retainedCoarseCells, hret_nonempty, hret_subset, hband, hpigeon⟩
  have hselect_exists : ∀ c ∈ retainedCoarseCells,
      ∃ (s : Finset WZ2PaperCellIndex), s ⊆ availableFineCells c ∧ s.card = 2 ^ level := by
    intro c hc
    have h1 : 2 ^ level ≤ (availableFineCells c).card := (hband c hc).1
    exact Finset.exists_subset_card_eq h1
  choose selectedFineCells hsel_subset hsel_card using hselect_exists
  let selectedFineCells' : WZ2PaperCellIndex → Finset WZ2PaperCellIndex := fun c =>
    if h : c ∈ retainedCoarseCells then selectedFineCells c h else ∅
  have hsel'_subset : ∀ c ∈ retainedCoarseCells,
      selectedFineCells' c ⊆ availableFineCells c := by
    intro c hc
    simp [selectedFineCells', hc]
    exact hsel_subset c hc
  have hsel'_card : ∀ c ∈ retainedCoarseCells,
      (selectedFineCells' c).card = 2 ^ level := by
    intro c hc
    simp [selectedFineCells', hc]
    exact hsel_card c hc
  have hsel_disjoint : ∀ c1 ∈ retainedCoarseCells, ∀ c2 ∈ retainedCoarseCells,
      c1 ≠ c2 → Disjoint (selectedFineCells' c1) (selectedFineCells' c2) := by
    intro c1 _ c2 _ hne
    simp only [Finset.disjoint_left]
    intro f hf1 hf2
    have h1 : f ∈ availableFineCells c1 := hsel'_subset c1 (by assumption) hf1
    have h2 : f ∈ availableFineCells c2 := hsel'_subset c2 (by assumption) hf2
    have hcont1 : wz1PaperGridCube delta f ⊆ wz1PaperGridCube rho c1 :=
      (hcontainment_active c1 (hret_subset (by assumption)) f h1).2
    have hcont2 : wz1PaperGridCube delta f ⊆ wz1PaperGridCube rho c2 :=
      (hcontainment_active c2 (hret_subset (by assumption)) f h2).2
    have hvol_pos : 0 < volume (wz1PaperGridCube delta f) :=
      wz1PaperGridCube_volume_pos hdelta f
    have hnonempty : (wz1PaperGridCube delta f).Nonempty := by
      by_contra h
      have h_empty : wz1PaperGridCube delta f = ∅ := by
        simpa [Set.not_nonempty_iff_eq_empty] using h
      rw [h_empty] at hvol_pos
      simp at hvol_pos
    rcases hnonempty with ⟨point, hpoint⟩
    have h_in1 : point ∈ wz1PaperGridCube rho c1 := hcont1 hpoint
    have h_in2 : point ∈ wz1PaperGridCube rho c2 := hcont2 hpoint
    have h_eq : c1 = c2 := by
      have hi : wz1PaperGridIndex rho point = c1 := (mem_wz1PaperGridCube rho c1 point).mp h_in1
      have hj : wz1PaperGridIndex rho point = c2 := (mem_wz1PaperGridCube rho c2 point).mp h_in2
      exact hi.symm.trans hj
    exact hne h_eq
  let retainedFineCells := retainedCoarseCells.biUnion selectedFineCells'
  have hretained_eq : retainedFineCells = retainedCoarseCells.biUnion selectedFineCells' := rfl
  have hcard_biUnion : retainedFineCells.card = ∑ c ∈ retainedCoarseCells, (selectedFineCells' c).card := by
    rw [Finset.card_biUnion]
    intro c1 _ c2 _ hne
    exact hsel_disjoint c1 (by assumption) c2 (by assumption) hne
  have hcard : retainedFineCells.card = ∑ c ∈ retainedCoarseCells, 2 ^ level := by
    rw [hcard_biUnion]
    apply Finset.sum_congr rfl
    intro c hc
    exact hsel'_card c hc
  let S : ℕ := ∑ c ∈ retainedCoarseCells, (availableFineCells c).card
  have hS_le : S ≤ 2 * retainedFineCells.card := by
    have h1 : ∀ c ∈ retainedCoarseCells, (availableFineCells c).card < 2 * 2 ^ level := by
      intro c hc
      have h2 : (availableFineCells c).card < 2 ^ (level + 1) := (hband c hc).2
      have h3 : 2 ^ (level + 1) = 2 * 2 ^ level := by ring
      rw [h3] at h2
      exact h2
    have h4 : S ≤ ∑ c ∈ retainedCoarseCells, 2 * 2 ^ level := by
      apply Finset.sum_le_sum
      intro c hc
      exact (h1 c hc).le
    have h5 : ∑ c ∈ retainedCoarseCells, 2 * 2 ^ level = 2 * retainedFineCells.card := by
      rw [hcard]
      <;> simp [Finset.mul_sum]
      <;> ring
    rw [h5] at h4
    exact h4
  have hcount : N ≤ (Nat.log 2 N + 1) * S := hpigeon
  have hfinal_count : N ≤ 2 * (Nat.log 2 N + 1) * retainedFineCells.card := by
    calc N ≤ (Nat.log 2 N + 1) * S := hcount
      _ ≤ (Nat.log 2 N + 1) * (2 * retainedFineCells.card) := by gcongr
      _ = 2 * (Nat.log 2 N + 1) * retainedFineCells.card := by ring
  let refined := wz2RefinedShading shading retainedFineCells
  have hactive : ∀ fineCell ∈ retainedFineCells,
      fineCell ∈ wz1PaperActiveCells shading hdelta := by
    intro fineCell hfine
    rcases Finset.mem_biUnion.mp hfine with ⟨c, hc, hf⟩
    have h_in_avail : fineCell ∈ availableFineCells c := hsel'_subset c hc hf
    exact (hcontainment_active c (hret_subset hc) fineCell h_in_avail).1
  have h_containment : ∀ c ∈ retainedCoarseCells,
      ∀ f ∈ selectedFineCells' c, wz1PaperGridCube delta f ⊆ wz1PaperGridCube rho c := by
    intro c hc f hf
    have h_in_avail : f ∈ availableFineCells c := hsel'_subset c hc hf
    exact (hcontainment_active c (hret_subset hc) f h_in_avail).2
  let cellMass : ENNReal := (2 ^ level : ENNReal) * volume (wz1PaperGridCube delta (0, 0, 0))
  have hcellMass_pos : 0 < cellMass := by
    have h1 : (0 : ENNReal) < (2 ^ level : ENNReal) := by positivity
    have h2 : 0 < volume (wz1PaperGridCube delta (0, 0, 0)) :=
      wz1PaperGridCube_volume_pos hdelta (0, 0, 0)
    positivity
  have hcellMass_ne_top : cellMass ≠ ⊤ := by
    have h1 : volume (wz1PaperGridCube delta (0, 0, 0)) ≠ ⊤ :=
      wz1PaperGridCube_volume_ne_top hdelta (0, 0, 0)
    simp [cellMass, h1]
    <;> exact ENNReal.mul_ne_top (by simp) h1
  refine' ⟨
    level,
    retainedCoarseCells,
    hret_subset,
    hret_nonempty,
    selectedFineCells',
    hsel'_subset,
    hsel'_card,
    hband,
    retainedFineCells,
    hretained_eq,
    hfinal_count,
    refined,
    _
    ,
    _
    ,
    _
    ,
    _
    ,
    cellMass,
    by simp [cellMass],
    hcellMass_pos,
    hcellMass_ne_top,
    _,
    _
  ⟩
  ·
    intro index
    simp [refined, wz2RefinedShading_carrier, wz2RetainedCellsUnion]
    <;> rfl
  ·
    exact wz2RefinedShading_subshading
  ·
    exact wz2RefinedShading_cubical hcubical
  ·
    exact wz2RefinedShading_union_eq hcubical hdelta hactive
  ·
    intro coarseCell hcoarse
    have h_union_eq : refined.union = wz2RetainedCellsUnion delta retainedFineCells :=
      wz2RefinedShading_union_eq hcubical hdelta hactive
    have h_set_eq : (refined.union ∩ wz1PaperGridCube rho coarseCell) =
        ⋃ f ∈ selectedFineCells' coarseCell, wz1PaperGridCube delta f := by
      rw [h_union_eq]
      exact wz2RefinedUnion_inter_coarseCube hretained_eq h_containment hcoarse
    rw [h_set_eq]
    have h_vol : volume (⋃ f ∈ selectedFineCells' coarseCell, wz1PaperGridCube delta f) =
        ((selectedFineCells' coarseCell).card : ENNReal) * volume (wz1PaperGridCube delta (0, 0, 0)) :=
      wz1PaperGridCube_volume_biUnion hdelta (selectedFineCells' coarseCell)
    rw [h_vol, hsel'_card coarseCell hcoarse]
    <;> simp [cellMass]
  · exact h_containment

end Kakeya.Assouad
