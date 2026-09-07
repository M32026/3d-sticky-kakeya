import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCellPartition
import MyLeanRepo.Kakeya.Assouad.WZ1.NeighborPackingBound
import MyLeanRepo.Kakeya.Assouad.WZ1.ExactInducedCoarseShading
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.Floor

/-!
# Balanced cell construction for WZ1

One-cell fiber restriction strategy:
1. Find a grid cell with positive refined volume.
2. Find a coarse fiber with positive volume in that cell.
3. Restrict refined to that fiber within the cell.
4. Restrict coarseShading to that coarse tube within the cell.
5. Pick a representative from the chosen fiber.

This guarantees representative_associated because every point in
coarseShading belongs to the unique coarse tube whose fiber contains
the representative.

All other properties (diameter, fine witness, cell balance, neighbor bound)
follow from the single-cell construction.
-/

noncomputable section

open MeasureTheory Metric Finset

namespace Kakeya.Assouad

/-- Bounded set of grid indices that can intersect the radius-`R` ball. -/
def gridIndicesInRadius (R rho : ℝ) (hrho : 0 < rho) :
    Finset (ℤ × ℤ × ℤ) :=
  let s := gridSide rho
  let b : ℤ := ⌈R / s⌉ + 1
  (Finset.Icc (-b) b).product ((Finset.Icc (-b) b).product (Finset.Icc (-b) b))

/-- Compatibility name for the radius-one grid universe. -/
def gridIndicesInBall (rho : ℝ) (hrho : 0 < rho) : Finset (ℤ × ℤ × ℤ) :=
  gridIndicesInRadius 1 rho hrho

/-- Any point in a radius-`R` ball has an index in the radius-`R` universe. -/
lemma gridIndex_inRadius {R rho : ℝ} (hR : 0 ≤ R) (hrho : 0 < rho)
    {p : Point3} (hp : ‖p‖ ≤ R) :
    rhoGridIndex rho p ∈ gridIndicesInRadius R rho hrho := by
  set s : ℝ := gridSide rho with hs
  set b : ℤ := ⌈R / s⌉ + 1 with hb
  have hs_pos : 0 < s := by
    simp only [hs, gridSide] <;> positivity
  have h_ceil : (R / s : ℝ) ≤ ↑⌈R / s⌉ := Int.le_ceil _
  have h_coord : ∀ (k : Fin 3),
      -b ≤ ⌊(p k) / s⌋ ∧ ⌊(p k) / s⌋ ≤ b := by
    intro k
    have hpk : |p k| ≤ R :=
      (PiLp.norm_apply_le p k).trans hp
    have hupper : p k / s ≤ R / s := by
      gcongr
      exact (abs_le.mp hpk).2
    have hlower : -(R / s) ≤ p k / s := by
      have h : (-R) / s ≤ p k / s := by
        gcongr
        exact (abs_le.mp hpk).1
      simpa only [neg_div] using h
    constructor
    · have hfloor : ⌊-(R / s)⌋ ≤ ⌊p k / s⌋ :=
        Int.floor_mono hlower
      rw [Int.floor_neg] at hfloor
      dsimp only [b]
      omega
    · have hfloor : ⌊p k / s⌋ ≤ ⌊R / s⌋ :=
        Int.floor_mono hupper
      exact hfloor.trans
        (Int.floor_le_ceil (R / s) |>.trans (by omega))
  have h0 : ⌊p 0 / s⌋ ∈ Finset.Icc (-b) b :=
    Finset.mem_Icc.mpr (h_coord 0)
  have h1 : ⌊p 1 / s⌋ ∈ Finset.Icc (-b) b :=
    Finset.mem_Icc.mpr (h_coord 1)
  have h2 : ⌊p 2 / s⌋ ∈ Finset.Icc (-b) b :=
    Finset.mem_Icc.mpr (h_coord 2)
  change
    (⌊p 0 / gridSide rho⌋,
      ⌊p 1 / gridSide rho⌋, ⌊p 2 / gridSide rho⌋) ∈
        gridIndicesInRadius R rho hrho
  have hinner :
      (⌊p 1 / s⌋, ⌊p 2 / s⌋) ∈
        (Finset.Icc (-b) b).product (Finset.Icc (-b) b) :=
    Finset.mem_product.mpr ⟨h1, h2⟩
  have houter :
      (⌊p 0 / s⌋, (⌊p 1 / s⌋, ⌊p 2 / s⌋)) ∈
        (Finset.Icc (-b) b).product
          ((Finset.Icc (-b) b).product (Finset.Icc (-b) b)) :=
    Finset.mem_product.mpr ⟨h0, hinner⟩
  simpa [gridIndicesInRadius, hs, hb] using houter

/-- Any point in the unit ball has grid index in `gridIndicesInBall`. -/
lemma gridIndex_inBall {rho : ℝ} (hrho : 0 < rho) {p : Point3} (hp : ‖p‖ ≤ 1) :
    rhoGridIndex rho p ∈ gridIndicesInBall rho hrho := by
  exact gridIndex_inRadius (R := 1) (by norm_num) hrho hp

/--
Package of results from the balanced cell construction.
-/
structure BalancedCellResult
    {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (refined0 : Kakeya.Streamlined.TubeShading F) where
  refined : Kakeya.Streamlined.TubeShading F
  coarseShading : Kakeya.Streamlined.TubeShading (U.coarse rho)
  h_subshading : IsSubshading refined refined0
  h_induced : (U.cover rho).toFactoring.IsInducedSubshading refined coarseShading rho.1
  h_point_comp : ∀ i p, p ∈ refined.carrier i → p ∈ coarseShading.carrier ((U.cover rho).parent i)
  h_coarse_nonempty : coarseShading.union.Nonempty
  cell : Point3 → Fin 1
  hcell_meas : Measurable cell
  representative : Fin 1 → Point3
  cellMass : ENNReal
  hcellMass_pos : 0 < cellMass
  hcellMass_ne_top : cellMass ≠ ⊤
  neighborBound : ℕ
  hneighborBound_pos : 0 < neighborBound
  hneighborBound_le : neighborBound ≤ 10000
  h_diameter : ∀ p ∈ coarseShading.union, ∀ q ∈ coarseShading.union, cell p = cell q → dist p q ≤ 2 * rho.1
  h_fine_witness : ∀ p ∈ coarseShading.union, representative (cell p) ∈ refined.union ∧ cell (representative (cell p)) = cell p
  h_rep_associated : ∀ j p, p ∈ coarseShading.carrier j → ∃ i, (U.cover rho).parent i = j ∧ representative (cell p) ∈ refined.carrier i
  h_nearby : ∀ c : Fin 1, {p | p ∈ coarseShading.union ∧ cell p = c}.Nonempty → wz1NearbyActiveCellCount coarseShading cell representative c ≤ neighborBound
  h_cell_balance : ∀ c : Fin 1, {p | p ∈ coarseShading.union ∧ cell p = c}.Nonempty → cellMass ≤ volume (refined.union ∩ {p | cell p = c}) ∧ volume (refined.union ∩ {p | cell p = c}) ≤ 2 * cellMass
  h_coarse_multiplicity_le_one : ∀ p, coarseShading.pointMultiplicity p ≤ 1

/--
Balanced cell construction using one-cell fiber restriction.

Finds a single grid cell with positive volume in one coarse fiber,
restricts both refined and coarseShading to that cell/fiber, and
produces all cell-related fields with cellCount = 1.
-/
def balanced_cell_construction
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (refined0 : Kakeya.Streamlined.TubeShading F)
    (h_refined0_nonempty : refined0.union.Nonempty)
    (hrho_pos : 0 < rho.1)
    (h_refined0_in_ball : refined0.union ⊆ {p | ‖p‖ ≤ 1})
    (h_refined0_volume_pos : 0 < MeasureTheory.volume refined0.union) :
    BalancedCellResult F U rho refined0 := by
  classical
  set s : ℝ := gridSide rho.1 with hs
  let cover := U.cover rho
  let coarse := U.coarse rho
  let cellSet (idx : ℤ × ℤ × ℤ) : Set Point3 :=
    {p | rhoGridIndex rho.1 p = idx}

  -- Measurability of rhoGridIndex
  have h_meas_floor : Measurable (Int.floor : ℝ → ℤ) := Int.measurable_floor
  have h_coord_cont : ∀ (k : Fin 3), Continuous (fun p : Point3 => p k) := by
    intro k
    fun_prop
  have h1m : Measurable (fun p : Point3 => p 0) := (h_coord_cont 0).measurable
  have h2m : Measurable (fun p : Point3 => p 1) := (h_coord_cont 1).measurable
  have h3m : Measurable (fun p : Point3 => p 2) := (h_coord_cont 2).measurable
  have h4 : Measurable (fun p : Point3 => ⌊(p 0) / s⌋) := h_meas_floor.comp (h1m.div_const s)
  have h5 : Measurable (fun p : Point3 => ⌊(p 1) / s⌋) := h_meas_floor.comp (h2m.div_const s)
  have h6 : Measurable (fun p : Point3 => ⌊(p 2) / s⌋) := h_meas_floor.comp (h3m.div_const s)
  have h_meas_grid : Measurable (rhoGridIndex rho.1) := by
    have h7 : rhoGridIndex rho.1 = fun p => (⌊(p 0) / s⌋, ⌊(p 1) / s⌋, ⌊(p 2) / s⌋) := by
      funext p
      simp [rhoGridIndex, gridIndex]
      <;> aesop
    rw [h7]
    exact Measurable.prod h4 (Measurable.prod h5 h6)

  have h_cellSet_meas : ∀ idx, MeasurableSet (cellSet idx) := by
    intro idx
    exact h_meas_grid (MeasurableSet.singleton idx)

  have h_refined0_union_meas : MeasurableSet refined0.union := by
    have h1 : refined0.union = ⋃ i : Fin F.card, refined0.carrier i := by
      ext p; simp [Kakeya.Streamlined.Shading.union] <;> rfl
    rw [h1]
    exact MeasurableSet.iUnion (fun i => refined0.measurable_carrier i)

  -- General helper: finite union of null measurable sets is null
  have h_null_union : ∀ {α : Type} (s : Finset α) (f : α → Set Point3),
      (∀ i ∈ s, volume (f i) = 0) → volume (⋃ i ∈ s, f i) = 0 := by
    intro α s f hnull
    have h_iff : (volume (⋃ i ∈ s, f i) = 0) ↔ (∀ i ∈ s, volume (f i) = 0) :=
      measure_biUnion_null_iff (Finset.countable_toSet s)
    exact h_iff.mpr hnull

  -- All grid cells intersecting refined0.union
  let allIndices : Finset (ℤ × ℤ × ℤ) :=
    (gridIndicesInBall rho.1 hrho_pos).filter
      (fun idx => (refined0.union ∩ cellSet idx).Nonempty)

  have h_allIndices_nonempty : allIndices.Nonempty := by
    rcases h_refined0_nonempty with ⟨p, hp⟩
    have hidx : rhoGridIndex rho.1 p ∈ allIndices := by
      apply Finset.mem_filter.mpr
      constructor
      · exact gridIndex_inBall hrho_pos (h_refined0_in_ball hp)
      · exact ⟨p, ⟨hp, rfl⟩⟩
    exact ⟨rhoGridIndex rho.1 p, hidx⟩

  -- Cover refined0.union by cells
  have h_cover : refined0.union ⊆ ⋃ idx ∈ allIndices, cellSet idx := by
    intro p hp
    have h1 : ‖p‖ ≤ 1 := h_refined0_in_ball hp
    have h2 : rhoGridIndex rho.1 p ∈ allIndices := by
      apply Finset.mem_filter.mpr
      constructor
      · exact gridIndex_inBall hrho_pos h1
      · exact ⟨p, ⟨hp, rfl⟩⟩
    exact Set.mem_iUnion₂.mpr ⟨rhoGridIndex rho.1 p, h2, rfl⟩

  have h_eq_union : refined0.union = ⋃ idx ∈ allIndices, (refined0.union ∩ cellSet idx) := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hp
      have h3 := h_cover hp
      rcases Set.mem_iUnion₂.mp h3 with ⟨idx, hidx, h4⟩
      exact ⟨idx, hidx, hp, h4⟩
    · rintro ⟨idx, _, hp, _⟩
      exact hp

  -- Positive volume cells
  let posIndices := allIndices.filter (fun idx => 0 < volume (refined0.union ∩ cellSet idx))

  have h_posIndices_nonempty : posIndices.Nonempty := by
    by_contra h
    have h' : posIndices = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have h_all_zero : ∀ idx ∈ allIndices, volume (refined0.union ∩ cellSet idx) = 0 := by
      intro idx hidx
      by_cases hpos : 0 < volume (refined0.union ∩ cellSet idx)
      · have h_in : idx ∈ posIndices := by
          rw [Finset.mem_filter] <;> exact ⟨hidx, hpos⟩
        rw [h'] at h_in <;> simp at h_in
      · have hle : volume (refined0.union ∩ cellSet idx) ≤ 0 := by simpa using hpos
        exact le_antisymm hle (by positivity)
    have h_meas_sets : ∀ idx ∈ allIndices, MeasurableSet (refined0.union ∩ cellSet idx) := by
      intro idx _
      exact h_refined0_union_meas.inter (h_cellSet_meas idx)
    have h_vol_zero : volume refined0.union = 0 := by
      rw [h_eq_union]
      exact h_null_union allIndices (fun idx => refined0.union ∩ cellSet idx) (fun idx hidx => h_all_zero idx hidx)
    rw [h_vol_zero] at h_refined0_volume_pos
    exact lt_irrefl 0 h_refined0_volume_pos

  -- Pick one positive-volume cell
  have h_exists_idx : ∃ x, x ∈ posIndices := h_posIndices_nonempty
  let idx : ℤ × ℤ × ℤ := Classical.choose h_exists_idx
  have h_idx_in_pos : idx ∈ posIndices := Classical.choose_spec h_exists_idx
  have h_idx_in_all : idx ∈ allIndices := (Finset.mem_filter.mp h_idx_in_pos).1
  have h_vol_pos : 0 < volume (refined0.union ∩ cellSet idx) :=
    (Finset.mem_filter.mp h_idx_in_pos).2

  -- Fiber for coarse tube j
  let fiber (j : Fin coarse.card) : Set Point3 :=
    {p | ∃ i : Fin F.card, cover.parent i = j ∧ p ∈ refined0.carrier i}

  have h_fiber_meas : ∀ j : Fin coarse.card, MeasurableSet (fiber j) := by
    intro j
    have h1 : fiber j = ⋃ i ∈ (Finset.univ.filter (fun i => cover.parent i = j)), refined0.carrier i := by
      ext p
      simp [fiber, Finset.mem_filter]
      <;> tauto
    rw [h1]
    exact Finset.measurableSet_biUnion _ (fun i _ => refined0.measurable_carrier i)

  have h_fiber_union : refined0.union = ⋃ j : Fin coarse.card, fiber j := by
    ext p
    simp only [Kakeya.Streamlined.Shading.union, fiber, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨cover.parent i, i, rfl, hi⟩
    · rintro ⟨j, i, rfl, hi⟩
      exact ⟨i, hi⟩

  have h_cover2 : refined0.union ∩ cellSet idx = ⋃ j : Fin coarse.card, (fiber j ∩ cellSet idx) := by
    rw [h_fiber_union]
    rw [Set.iUnion_inter]

  -- Find coarse tube j with positive fiber volume in this cell
  have h_exists_j : ∃ j : Fin coarse.card, 0 < volume (fiber j ∩ cellSet idx) := by
    by_contra h
    push Not at h
    have h_all_zero : ∀ j : Fin coarse.card, volume (fiber j ∩ cellSet idx) = 0 := by
      intro j
      have h' : volume (fiber j ∩ cellSet idx) ≤ 0 := h j
      exact le_antisymm h' (by positivity)
    have h_meas : ∀ j : Fin coarse.card, MeasurableSet (fiber j ∩ cellSet idx) := by
      intro j
      exact (h_fiber_meas j).inter (h_cellSet_meas idx)
    have h_eq_univ : (⋃ j : Fin coarse.card, (fiber j ∩ cellSet idx)) =
        ⋃ j ∈ (Finset.univ : Finset (Fin coarse.card)), (fiber j ∩ cellSet idx) := by
      ext x; simp
    have h_vol : volume (refined0.union ∩ cellSet idx) = 0 := by
      rw [h_cover2]
      rw [measure_iUnion_null_iff]
      exact fun j => h_all_zero j
    rw [h_vol] at h_vol_pos
    exact lt_irrefl 0 h_vol_pos

  let j : Fin coarse.card := Classical.choose h_exists_j
  have hj_vol_pos : 0 < volume (fiber j ∩ cellSet idx) :=
    Classical.choose_spec h_exists_j

  -- Pick representative from fiber j ∩ cellSet idx
  have h_fiber_nonempty : (fiber j ∩ cellSet idx).Nonempty := by
    by_contra h
    have h' : fiber j ∩ cellSet idx = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h
    rw [h'] at hj_vol_pos
    simp at hj_vol_pos

  let q : Point3 := Classical.choose h_fiber_nonempty
  have hq : q ∈ fiber j ∩ cellSet idx := Classical.choose_spec h_fiber_nonempty
  have hq_fiber : q ∈ fiber j := hq.1
  have hq_cell : q ∈ cellSet idx := hq.2
  have h_exists_i : ∃ (i : Fin F.card), cover.parent i = j ∧ q ∈ refined0.carrier i := hq_fiber
  let i : Fin F.card := Classical.choose h_exists_i
  have hi_parent : cover.parent i = j := (Classical.choose_spec h_exists_i).1
  have hi_q : q ∈ refined0.carrier i := (Classical.choose_spec h_exists_i).2

  -- Balanced region = single cell
  let balancedRegion : Set Point3 := cellSet idx
  have h_balancedRegion_meas : MeasurableSet balancedRegion := h_cellSet_meas idx

  let refined : Kakeya.Streamlined.TubeShading F :=
    { carrier := fun i' => if cover.parent i' = j then refined0.carrier i' ∩ balancedRegion else ∅
      measurable_carrier := by
        intro i'
        split_ifs <;> [exact (refined0.measurable_carrier i').inter h_balancedRegion_meas; exact MeasurableSet.empty]
      subset_body := by
        intro i'
        split_ifs <;> [exact Set.inter_subset_left.trans (refined0.subset_body i'); exact Set.empty_subset _] }

  -- Exact induced coarse shading from refined
  let exactCoarse := exactInducedCoarseShading U rho refined

  -- cell and representative (cellCount = 1)
  let cell : Point3 → Fin 1 := fun _ => 0
  let representative : Fin 1 → Point3 := fun _ => q

  let coarseShading : Kakeya.Streamlined.TubeShading (U.coarse rho) :=
    { carrier := fun j' => if j' = j then exactCoarse.carrier j' ∩ balancedRegion else ∅
      measurable_carrier := by
        intro j'
        split_ifs <;> [exact (exactCoarse.measurable_carrier j').inter h_balancedRegion_meas; exact MeasurableSet.empty]
      subset_body := by
        intro j'
        split_ifs <;> [exact Set.inter_subset_left.trans (exactCoarse.subset_body j'); exact Set.empty_subset _] }

  -- Helper lemmas for carrier equalities
  have h_refined_pos : ∀ (i' : Fin F.card) (h : cover.parent i' = j),
      refined.carrier i' = refined0.carrier i' ∩ balancedRegion := by
    intro i' h
    have h1 : refined.carrier i' = (if cover.parent i' = j then refined0.carrier i' ∩ balancedRegion else ∅) := by rfl
    rw [h1, if_pos h]

  have h_refined_neg : ∀ (i' : Fin F.card) (h : ¬cover.parent i' = j),
      refined.carrier i' = ∅ := by
    intro i' h
    have h1 : refined.carrier i' = (if cover.parent i' = j then refined0.carrier i' ∩ balancedRegion else ∅) := by rfl
    rw [h1, if_neg h]

  have h_coarse_pos : ∀ (j' : Fin (U.coarse rho).card) (h : j' = j),
      coarseShading.carrier j' = exactCoarse.carrier j' ∩ balancedRegion := by
    intro j' h
    have h1 : coarseShading.carrier j' =
        (if j' = j then exactCoarse.carrier j' ∩ balancedRegion else ∅) := by rfl
    rw [h1, if_pos h]

  have h_coarse_neg : ∀ (j' : Fin (U.coarse rho).card) (h : j' ≠ j),
      coarseShading.carrier j' = ∅ := by
    intro j' h
    have h1 : coarseShading.carrier j' =
        (if j' = j then exactCoarse.carrier j' ∩ balancedRegion else ∅) := by rfl
    rw [h1, if_neg h]

  -- Key property: refined.union = fiber j ∩ balancedRegion
  have h_refined_union_eq : refined.union = fiber j ∩ balancedRegion := by
    ext p
    simp only [Kakeya.Streamlined.Shading.union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i', hi'⟩
      have h_parent : cover.parent i' = j := by
        by_cases h : cover.parent i' = j
        · exact h
        · rw [h_refined_neg i' h] at hi' <;> simp at hi'
      have h_p_in : p ∈ refined0.carrier i' ∩ balancedRegion := by
        rw [h_refined_pos i' h_parent] at hi' <;> exact hi'
      exact ⟨⟨i', h_parent, h_p_in.1⟩, h_p_in.2⟩
    · rintro ⟨h1, h2⟩
      rcases h1 with ⟨i', hi_parent, hi_p⟩
      have h11 : p ∈ refined.carrier i' := by
        rw [h_refined_pos i' hi_parent] <;> exact ⟨hi_p, h2⟩
      exact ⟨i', h11⟩

  have h_q_in_refined : q ∈ refined.carrier i := by
    rw [h_refined_pos i hi_parent]
    exact ⟨hi_q, hq_cell⟩

  have h_q_in_refined_union : q ∈ refined.union := ⟨i, h_q_in_refined⟩

  -- h_subshading
  have h_subshading : IsSubshading refined refined0 := by
    intro i'
    by_cases h : cover.parent i' = j
    · rw [h_refined_pos i' h]
      exact Set.inter_subset_left
    · rw [h_refined_neg i' h]
      exact Set.empty_subset _

  -- h_induced
  have h_induced : (U.cover rho).toFactoring.IsInducedSubshading refined coarseShading rho.1 := by
    intro j'
    by_cases h : j' = j
    · rw [h_coarse_pos j' h]
      exact Set.inter_subset_left.trans (exactInducedCoarseShading_isInducedSubshading U rho refined j')
    · rw [h_coarse_neg j' h]
      exact Set.empty_subset _

  -- h_point_comp
  have h_point_comp : ∀ i' p, p ∈ refined.carrier i' →
      p ∈ coarseShading.carrier (cover.parent i') := by
    intro i' p hp
    have h_parent : cover.parent i' = j := by
      by_cases h : cover.parent i' = j
      · exact h
      · rw [h_refined_neg i' h] at hp <;> simp at hp
    have h_p_in : p ∈ refined0.carrier i' ∩ balancedRegion := by
      rw [h_refined_pos i' h_parent] at hp <;> exact hp
    have h_exact : p ∈ exactCoarse.carrier (cover.parent i') :=
      exactInducedCoarseShading_pointCompatibility U rho refined i' p hp
    rw [h_parent] at h_exact
    have h11 : coarseShading.carrier (cover.parent i') = exactCoarse.carrier j ∩ balancedRegion := by
      rw [h_coarse_pos (cover.parent i') h_parent, h_parent]
    rw [h11]
    exact ⟨h_exact, h_p_in.2⟩

  -- h_coarse_nonempty
  have h_coarse_nonempty : coarseShading.union.Nonempty := by
    have h14 : q ∈ coarseShading.carrier (cover.parent i) := h_point_comp i q h_q_in_refined
    refine ⟨q, ?_⟩
    exact ⟨cover.parent i, h14⟩

  -- Helper: any point in coarseShading.union is in balancedRegion
  have h_in_balanced : ∀ p, p ∈ coarseShading.union → p ∈ balancedRegion := by
    intro p hp
    rcases hp with ⟨j', hj'⟩
    by_cases h : j' = j
    · rw [h_coarse_pos j' h] at hj'
      exact hj'.2
    · rw [h_coarse_neg j' h] at hj' <;> simp at hj'

  -- Cell diameter
  have h_diameter : ∀ p ∈ coarseShading.union, ∀ q' ∈ coarseShading.union,
      cell p = cell q' → dist p q' ≤ 2 * rho.1 := by
    intro p hp q' hq' _
    have hp_bal : p ∈ balancedRegion := h_in_balanced p hp
    have hq'_bal : q' ∈ balancedRegion := h_in_balanced q' hq'
    have hp_idx : rhoGridIndex rho.1 p = idx := by simpa [balancedRegion, cellSet] using hp_bal
    have hq'_idx : rhoGridIndex rho.1 q' = idx := by simpa [balancedRegion, cellSet] using hq'_bal
    exact grid_cell_diameter hrho_pos (by rw [hp_idx, hq'_idx])

  -- Cell fine witness
  have h_fine_witness : ∀ p ∈ coarseShading.union,
      representative (cell p) ∈ refined.union ∧ cell (representative (cell p)) = cell p := by
    intro p _
    exact ⟨h_q_in_refined_union, rfl⟩

  -- Representative associated
  have h_rep_associated : ∀ j' p, p ∈ coarseShading.carrier j' →
      ∃ i', cover.parent i' = j' ∧ representative (cell p) ∈ refined.carrier i' := by
    intro j' p hp
    have h_j' : j' = j := by
      by_cases h : j' = j
      · exact h
      · rw [h_coarse_neg j' h] at hp <;> simp at hp
    rw [h_j']
    refine ⟨i, hi_parent, h_q_in_refined⟩

  -- Neighbor bound (trivial with cellCount = 1)
  have h_nearby : ∀ c : Fin 1,
      {p | p ∈ coarseShading.union ∧ cell p = c}.Nonempty →
      wz1NearbyActiveCellCount coarseShading cell representative c ≤ 10000 := by
    intro c _
    have h1 : wz1NearbyActiveCellCount coarseShading cell representative c ≤
        (Finset.univ : Finset (Fin 1)).card := Finset.card_le_univ _
    simpa using h1.trans (by norm_num)

  -- Cell balance
  let cellMass : ENNReal := volume (fiber j ∩ cellSet idx)
  have hcellMass_pos : 0 < cellMass := hj_vol_pos
  have hcellMass_ne_top : cellMass ≠ ⊤ := by
    have h1 : fiber j ∩ cellSet idx ⊆ refined0.union := by
      intro p hp
      have h2 : p ∈ fiber j := hp.1
      rcases h2 with ⟨i', _, hi'⟩
      exact ⟨i', hi'⟩
    have h2 : fiber j ∩ cellSet idx ⊆ Metric.closedBall (0 : Point3) 1 := by
      have h21 : fiber j ∩ cellSet idx ⊆ {p | ‖p‖ ≤ 1} := h1.trans h_refined0_in_ball
      have h22 : {p : Point3 | ‖p‖ ≤ 1} = Metric.closedBall (0 : Point3) 1 := by
        ext p; simp [Metric.mem_closedBall]
      rw [h22] at h21
      exact h21
    have h3 : volume (fiber j ∩ cellSet idx) ≤ volume (Metric.closedBall (0 : Point3) 1) :=
      measure_mono h2
    have h4 : volume (Metric.closedBall (0 : Point3) 1) < ⊤ :=
      measure_closedBall_lt_top
    exact ne_top_of_le_ne_top h4.ne h3

  have h_cell_balance : ∀ c : Fin 1,
      {p | p ∈ coarseShading.union ∧ cell p = c}.Nonempty →
      cellMass ≤ volume (refined.union ∩ {p | cell p = c}) ∧
      volume (refined.union ∩ {p | cell p = c}) ≤ 2 * cellMass := by
    intro c _
    have h5 : {p : Point3 | cell p = c} = Set.univ := by
      ext x
      simp [cell]
      <;> fin_cases c <;> simp
    rw [h5]
    have h6 : volume (refined.union ∩ Set.univ) = volume refined.union := by simp
    rw [h6]
    have h7 : volume refined.union = volume (fiber j ∩ balancedRegion) := by
      rw [h_refined_union_eq]
    rw [h7]
    have h8 : balancedRegion = cellSet idx := rfl
    rw [h8]
    exact ⟨le_refl _, by
      have h9 : cellMass ≤ 2 * cellMass := by
        have h10 : (1 : ENNReal) ≤ 2 := by norm_num
        simpa [two_mul] using add_le_add (le_refl cellMass) (le_refl cellMass)
      exact h9⟩

  exact {
    refined := refined,
    coarseShading := coarseShading,
    h_subshading := h_subshading,
    h_induced := h_induced,
    h_point_comp := h_point_comp,
    h_coarse_nonempty := h_coarse_nonempty,
    cell := cell,
    hcell_meas := by fun_prop,
    representative := representative,
    cellMass := cellMass,
    hcellMass_pos := hcellMass_pos,
    hcellMass_ne_top := hcellMass_ne_top,
    neighborBound := 10000,
    hneighborBound_pos := by norm_num,
    hneighborBound_le := by norm_num,
    h_diameter := h_diameter,
    h_fine_witness := h_fine_witness,
    h_rep_associated := h_rep_associated,
    h_nearby := h_nearby,
    h_cell_balance := h_cell_balance,
    h_coarse_multiplicity_le_one := by
      intro p
      have h1 : ∀ (j' : Fin (U.coarse rho).card), p ∈ coarseShading.carrier j' → j' = j := by
        intro j' hj'
        by_cases h : j' = j
        · exact h
        · rw [h_coarse_neg j' h] at hj' <;> simp at hj'
      have h_main : coarseShading.pointMultiplicity p ≤ 1 := by
        simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
        apply Finset.card_le_one.mpr
        intro j1 hj1 j2 hj2
        have h_j1 : j1 = j := h1 j1 (by simpa [Finset.mem_filter] using hj1)
        have h_j2 : j2 = j := h1 j2 (by simpa [Finset.mem_filter] using hj2)
        rw [h_j1, h_j2]
      exact h_main
  }

/--
Coarse multiplicity upper bound from the one-cell construction.

Since only one coarse tube has a nonempty shading carrier, the point
multiplicity is at most 1.  And since `ρ ≤ 1` and `-σ-ε < 0`, we have
`ρ^(-σ-ε) ≥ 1`, giving the required bound.
-/
lemma coarse_multiplicity_from_one_cell
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {refined0 : Kakeya.Streamlined.TubeShading F}
    (result : BalancedCellResult (F := F) U rho refined0)
    (hdelta_pos : 0 < delta)
    (hsigma_pos : 0 < sigma) (hepsilon_pos : 0 < epsilon) :
    ∀ p : Point3,
      (result.coarseShading.pointMultiplicity p : ENNReal) ≤
        Kakeya.realRpowENN rho.1 (-sigma - epsilon) := by
  have hrho_le_one : rho.1 ≤ 1 := rho.2.2
  have hrho_pos : 0 < rho.1 := by linarith [rho.2.1]
  have hexp_neg : -sigma - epsilon < 0 := by linarith
  have h1 : (1 : ENNReal) ≤ Kakeya.realRpowENN rho.1 (-sigma - epsilon) := by
    have h4 : (rho.1 : ℝ) ^ (-sigma - epsilon) ≥ 1 :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hrho_pos hrho_le_one (by linarith)
    simpa [Kakeya.realRpowENN, ENNReal.ofReal_le_ofReal] using h4
  intro p
  have h5 : result.coarseShading.pointMultiplicity p ≤ 1 :=
    result.h_coarse_multiplicity_le_one p
  have h6 : (result.coarseShading.pointMultiplicity p : ENNReal) ≤ (1 : ENNReal) := by
    exact_mod_cast h5
  exact h6.trans h1

end Kakeya.Assouad
