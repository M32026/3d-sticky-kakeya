import MyLeanRepo.Kakeya.Assouad.PropStickyShiftedGridPruningStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperInfrastructure
import Mathlib.Tactic

/-!
# Helper lemmas for WZ2 exact whole-cell balancing
-/

noncomputable section

namespace Kakeya.Assouad

open Finset MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Dyadic pigeonhole for natural-number values. -/
lemma dyadic_band_pigeonhole
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ)
    (hs : s.Nonempty) (hpos : ∀ i ∈ s, 0 < f i) :
    ∃ (k : ℕ) (t : Finset α),
      t.Nonempty ∧ t ⊆ s ∧
      (∀ i ∈ t, 2^k ≤ f i ∧ f i < 2^(k+1)) ∧
      (Nat.log 2 (∑ i ∈ s, f i) + 1) * (∑ i ∈ t, f i) ≥
        ∑ i ∈ s, f i := by
  let N : ℕ := ∑ i ∈ s, f i
  have hN_pos : 0 < N := by
    rcases hs with ⟨i, hi⟩
    have h1 : 0 < f i := hpos i hi
    have h2 : f i ≤ N := Finset.single_le_sum (fun j _ => by omega) hi
    omega
  let K : ℕ := Nat.log 2 N + 1
  let band : ℕ → Finset α := fun k =>
    s.filter (fun i => 2^k ≤ f i ∧ f i < 2^(k+1))
  have h_cover : ∀ i ∈ s, ∃ k ∈ Finset.range K, i ∈ band k := by
    intro i hi
    let k : ℕ := Nat.log 2 (f i)
    have hfk_pos : 0 < f i := hpos i hi
    have h1 : 2^k ≤ f i := Nat.pow_log_le_self 2 hfk_pos.ne'
    have h2 : f i < 2^(k+1) := Nat.lt_pow_succ_log_self (by norm_num) (f i)
    have hfi_le_N : f i ≤ N := Finset.single_le_sum (fun j _ => by omega) hi
    have hk_le : k ≤ Nat.log 2 N := Nat.log_mono_right hfi_le_N
    have hk_lt_K : k < K := by dsimp only [K]; omega
    have hk_range : k ∈ Finset.range K := by
      simp only [Finset.mem_range]; omega
    have h_in_band : i ∈ band k := by
      simp only [band, Finset.mem_filter]; exact ⟨hi, h1, h2⟩
    exact ⟨k, hk_range, h_in_band⟩
  have h_disjoint : ∀ k ∈ Finset.range K, ∀ l ∈ Finset.range K,
      k ≠ l → Disjoint (band k) (band l) := by
    intro k _ l _ hne
    simp only [band, Finset.disjoint_left]
    intro i hi1 hi2
    have h1 : 2^k ≤ f i := (Finset.mem_filter.mp hi1).2.1
    have h2 : f i < 2^(k+1) := (Finset.mem_filter.mp hi1).2.2
    have h3 : 2^l ≤ f i := (Finset.mem_filter.mp hi2).2.1
    have h4 : f i < 2^(l+1) := (Finset.mem_filter.mp hi2).2.2
    by_cases h : k < l
    · have h5 : k + 1 ≤ l := by omega
      have h6 : 2^(k+1) ≤ 2^l := by gcongr; norm_num
      have h7 : 2^(k+1) ≤ f i := h6.trans h3
      exact not_le.mpr h2 h7
    · have h6 : l < k := by omega
      have h7 : l + 1 ≤ k := by omega
      have h8 : 2^(l+1) ≤ 2^k := by gcongr; norm_num
      have h9 : 2^(l+1) ≤ f i := h8.trans h1
      exact not_le.mpr h4 h9
  have h_union : (Finset.biUnion (Finset.range K) band) = s := by
    ext i
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨k, _, hk⟩
      exact (Finset.mem_filter.mp hk).1
    · intro hi
      exact h_cover i hi
  have h_sum : ∑ k ∈ Finset.range K, ∑ i ∈ band k, f i = N := by
    rw [← Finset.sum_biUnion h_disjoint, h_union]
  have hK_pos : 0 < K := by dsimp only [K]; omega
  have h_nonempty_range : (Finset.range K).Nonempty := by
    exact Finset.nonempty_range_iff.mpr (ne_of_gt hK_pos)
  have h_max : ∃ k ∈ Finset.range K,
      (K : ℕ) * (∑ i ∈ band k, f i) ≥ N := by
    have h : ∃ k ∈ Finset.range K,
        ∀ l ∈ Finset.range K,
          (∑ i ∈ band l, f i) ≤ (∑ i ∈ band k, f i) :=
      Finset.exists_max_image (Finset.range K)
        (fun k => ∑ i ∈ band k, f i) h_nonempty_range
    rcases h with ⟨k, hk, hmax⟩
    have h_le : ∑ l ∈ Finset.range K, (∑ i ∈ band l, f i) ≤
        (Finset.range K).card * (∑ i ∈ band k, f i) := by
      calc
        ∑ l ∈ Finset.range K, (∑ i ∈ band l, f i)
          ≤ ∑ l ∈ Finset.range K, (∑ i ∈ band k, f i) := by
            apply Finset.sum_le_sum
            intro l hl
            exact hmax l hl
        _ = (Finset.range K).card * (∑ i ∈ band k, f i) := by
          simp [Finset.sum_const]
    have h_card : (Finset.range K).card = K := by simp
    rw [h_card] at h_le
    rw [h_sum] at h_le
    exact ⟨k, hk, h_le⟩
  rcases h_max with ⟨k, hk, hge⟩
  let t := band k
  have ht_sub : t ⊆ s := Finset.filter_subset _ _
  have h_band : ∀ i ∈ t, 2^k ≤ f i ∧ f i < 2^(k+1) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have h_sum_t_pos : 0 < ∑ i ∈ t, f i := by
    by_contra h
    have h' : ∑ i ∈ t, f i = 0 := by omega
    rw [h'] at hge
    omega
  have ht_nonempty : t.Nonempty := by
    by_contra h
    have h_empty : t = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using h
    rw [h_empty] at h_sum_t_pos
    simp at h_sum_t_pos
  exact ⟨k, t, ht_nonempty, ht_sub, h_band, hge⟩

/-- The union of grid cubes for a finite set of cell indices. -/
def wz2RetainedCellsUnion
    (delta : ℝ) (retainedFineCells : Finset (ℤ × ℤ × ℤ)) :
    Set Point3 :=
  ⋃ fineCell ∈ retainedFineCells, wz1PaperGridCube delta fineCell

/-- The union of finitely many grid cubes is measurable. -/
theorem wz2RetainedCellsUnion_measurable
    {delta : ℝ} {retainedFineCells : Finset (ℤ × ℤ × ℤ)} :
    MeasurableSet (wz2RetainedCellsUnion delta retainedFineCells) := by
  apply MeasurableSet.iUnion
  intro fineCell
  apply MeasurableSet.iUnion
  intro _
  exact wz1PaperGridCube_measurable fineCell

/-- Construct the refined shading by intersecting each carrier with `U`. -/
def wz2RefinedShading
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (retainedFineCells : Finset (ℤ × ℤ × ℤ)) :
    WZ1PaperTubeShading fine :=
  let U := wz2RetainedCellsUnion delta retainedFineCells
  { carrier := fun i => shading.carrier i ∩ U,
    measurable_carrier := fun i =>
      (shading.measurable_carrier i).inter
        wz2RetainedCellsUnion_measurable,
    subset_body := fun i =>
      Set.inter_subset_left.trans (shading.subset_body i) }

@[simp]
theorem wz2RefinedShading_carrier
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {retainedFineCells : Finset (ℤ × ℤ × ℤ)}
    {index : Fin fine.card} :
    (wz2RefinedShading shading retainedFineCells).carrier index =
      shading.carrier index ∩
        wz2RetainedCellsUnion delta retainedFineCells := by
  rfl

/-- The refined shading is a subshading. -/
theorem wz2RefinedShading_subshading
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {retainedFineCells : Finset (ℤ × ℤ × ℤ)} :
    ∀ index,
      (wz2RefinedShading shading retainedFineCells).carrier index ⊆
        shading.carrier index := by
  intro index
  exact Set.inter_subset_left

/-- If the original shading is cubical, the refined shading is cubical. -/
theorem wz2RefinedShading_cubical
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {retainedFineCells : Finset (ℤ × ℤ × ℤ)}
    (hcubical : WZ1PaperIsCubicalShading shading) :
    WZ1PaperIsCubicalShading
      (wz2RefinedShading shading retainedFineCells) := by
  intro index point hpoint
  have h1 : point ∈ shading.carrier index := hpoint.1
  have h2 : point ∈ wz2RetainedCellsUnion delta retainedFineCells := hpoint.2
  rcases Set.mem_iUnion₂.mp h2 with ⟨fineCell, hfineCell, hpointCell⟩
  have hindex : wz1PaperGridIndex delta point = fineCell :=
    (mem_wz1PaperGridCube delta fineCell point).mp hpointCell
  have hcube_subset :
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        shading.carrier index :=
    hcubical index point h1
  have hcube_in_U :
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        wz2RetainedCellsUnion delta retainedFineCells := by
    rw [hindex]
    intro x hx
    exact Set.mem_iUnion₂.mpr ⟨fineCell, hfineCell, hx⟩
  intro y hy
  exact ⟨hcube_subset hy, hcube_in_U hy⟩

/-- The union of the refined shading equals `shading.union ∩ U`. -/
theorem wz2RefinedShading_union_inter
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {retainedFineCells : Finset (ℤ × ℤ × ℤ)} :
    (wz2RefinedShading shading retainedFineCells).union =
      shading.union ∩ wz2RetainedCellsUnion delta retainedFineCells := by
  ext point
  simp only [Kakeya.Streamlined.Shading.union,
    wz2RefinedShading_carrier, Set.mem_setOf_eq]
  constructor
  · rintro ⟨index, hpoint⟩
    exact ⟨⟨index, hpoint.1⟩, hpoint.2⟩
  · rintro ⟨⟨index, h1⟩, h2⟩
    exact ⟨index, ⟨h1, h2⟩⟩

/-- If every retained fine cell is active, then `U ⊆ shading.union`. -/
theorem wz2RetainedCellsUnion_subset_shadingUnion
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {retainedFineCells : Finset (ℤ × ℤ × ℤ)}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta : 0 < delta)
    (hactive : ∀ fineCell ∈ retainedFineCells,
      fineCell ∈ wz1PaperActiveCells shading hdelta) :
    wz2RetainedCellsUnion delta retainedFineCells ⊆ shading.union := by
  intro point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨fineCell, hfineCell, hpointCell⟩
  have hcell : fineCell ∈ wz1PaperActiveCells shading hdelta :=
    hactive fineCell hfineCell
  have h_eq : shading.union ∩ wz1PaperGridCube delta fineCell =
        wz1PaperGridCube delta fineCell :=
    hcubical.inter_activeCell_eq hdelta hcell
  have h : point ∈ shading.union ∩ wz1PaperGridCube delta fineCell := by
    rw [h_eq]
    exact hpointCell
  exact h.1

/-- If every retained fine cell is active, the refined union equals `U`. -/
theorem wz2RefinedShading_union_eq
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {retainedFineCells : Finset (ℤ × ℤ × ℤ)}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta : 0 < delta)
    (hactive : ∀ fineCell ∈ retainedFineCells,
      fineCell ∈ wz1PaperActiveCells shading hdelta) :
    (wz2RefinedShading shading retainedFineCells).union =
      wz2RetainedCellsUnion delta retainedFineCells := by
  rw [wz2RefinedShading_union_inter]
  have h_subset :
      wz2RetainedCellsUnion delta retainedFineCells ⊆ shading.union :=
    wz2RetainedCellsUnion_subset_shadingUnion hcubical hdelta hactive
  rw [Set.inter_eq_right.mpr h_subset]

/-- Distinct paper grid cubes are disjoint. -/
theorem wz1PaperGridCube_disjoint
    {scale : ℝ} {i j : ℤ × ℤ × ℤ} (h : i ≠ j) :
    Disjoint (wz1PaperGridCube scale i) (wz1PaperGridCube scale j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hi : wz1PaperGridIndex scale x = i :=
    (mem_wz1PaperGridCube scale i x).mp hxi
  have hj : wz1PaperGridIndex scale x = j :=
    (mem_wz1PaperGridCube scale j x).mp hxj
  exact h (hi.symm.trans hj)

/-- Volume of a finite union of pairwise disjoint grid cubes. -/
theorem wz1PaperGridCube_volume_biUnion
    {scale : ℝ} (hscale : 0 < scale)
    (s : Finset (ℤ × ℤ × ℤ)) :
    volume (⋃ i ∈ s, wz1PaperGridCube scale i) =
      (s.card : ENNReal) * volume (wz1PaperGridCube scale (0, 0, 0)) := by
  have h_disj : Set.PairwiseDisjoint (↑s) (fun i => wz1PaperGridCube scale i) := by
    intro i _ j _ hne
    exact wz1PaperGridCube_disjoint hne
  have h_meas : ∀ i ∈ s, MeasurableSet (wz1PaperGridCube scale i) := by
    intro i _
    exact wz1PaperGridCube_measurable i
  rw [MeasureTheory.measure_biUnion_finset h_disj h_meas]
  have h_sum : ∑ i ∈ s, volume (wz1PaperGridCube scale i) =
      (s.card : ENNReal) * volume (wz1PaperGridCube scale (0, 0, 0)) := by
    have h_eq : ∀ i ∈ s, volume (wz1PaperGridCube scale i) =
          volume (wz1PaperGridCube scale (0, 0, 0)) := by
      intro i _
      exact wz1PaperGridCube_volume_eq hscale i (0, 0, 0)
    rw [Finset.sum_congr rfl h_eq]
    simp
  exact h_sum

/-- A paper grid cube has finite volume. -/
lemma wz1PaperGridCube_volume_ne_top {scale : ℝ} (hscale : 0 < scale)
    (cell : ℤ × ℤ × ℤ) :
    volume (wz1PaperGridCube scale cell) ≠ ⊤ := by
  rw [wz1PaperGridCube_eq_translate hscale cell]
  let v := wz1PaperGridCubeTranslation scale cell
  let f : Point3 → Point3 := fun x => x + v
  have h_sub : wz1PaperGridCube scale (0, 0, 0) ⊆
      Metric.closedBall (0 : Point3) (3 * scale) := by
    intro p hp
    have h_idx : wz1PaperGridIndex scale p = (0, 0, 0) :=
      (mem_wz1PaperGridCube _ _ _).mp hp
    have h_floors : ⌊p 0 / scale⌋ = 0 ∧
        ⌊p 1 / scale⌋ = 0 ∧ ⌊p 2 / scale⌋ = 0 := by
      simp [wz1PaperGridIndex, gridIndex, Prod.ext_iff] at h_idx ⊢
      exact h_idx
    have h_coords : ∀ (i : Fin 3), 0 ≤ p i ∧ p i < scale := by
      intro i
      have h_floor : ⌊p i / scale⌋ = 0 := by
        fin_cases i <;> simp [h_floors] <;> rfl
      have h1 : 0 ≤ p i / scale := (Int.floor_eq_zero_iff.mp h_floor).1
      have h2 : p i / scale < 1 := (Int.floor_eq_zero_iff.mp h_floor).2
      have h3 : 0 ≤ p i := by
        have h4 : 0 ≤ (p i / scale) * scale := mul_nonneg h1 hscale.le
        have h5 : (p i / scale) * scale = p i := by
          field_simp [hscale.ne'] <;> ring
        rw [h5] at h4
        exact h4
      have h6 : p i < scale := by
        have h7 : (p i / scale) * scale < 1 * scale :=
          mul_lt_mul_of_pos_right h2 hscale
        have h8 : (p i / scale) * scale = p i := by
          field_simp [hscale.ne'] <;> ring
        rw [h8] at h7
        simpa using h7
      exact ⟨h3, h6⟩
    have h_norm2 : ‖p‖ ^ 2 ≤ 3 * scale ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq p]
      have h_sum : ∑ i : Fin 3, (p i) ^ 2 ≤ ∑ i : Fin 3, scale ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h3 : (p i) ^ 2 ≤ scale ^ 2 := by
          have h4 : 0 ≤ p i := (h_coords i).1
          have h5 : p i < scale := (h_coords i).2
          nlinarith
        exact h3
      simpa using h_sum
    have h_norm : ‖p‖ ≤ 3 * scale := by
      nlinarith [norm_nonneg p, hscale]
    simpa [Metric.mem_closedBall, dist_zero_right] using h_norm
  have h0 : Bornology.IsBounded (wz1PaperGridCube scale (0, 0, 0)) :=
    Metric.isBounded_closedBall.subset h_sub
  have h1 : f '' wz1PaperGridCube scale (0, 0, 0) ⊆
      Metric.closedBall v (3 * scale) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h2 : x ∈ Metric.closedBall (0 : Point3) (3 * scale) := h_sub hx
    have h3 : dist (x + v) v ≤ 3 * scale := by
      have h4 : dist (x + v) v = dist x 0 := by
        simp [dist_eq_norm]
        <;> abel
      rw [h4]
      simpa [Metric.mem_closedBall, dist_zero_right] using h2
    exact h3
  have h_image_bdd : Bornology.IsBounded (f '' wz1PaperGridCube scale (0, 0, 0)) :=
    Metric.isBounded_closedBall.subset h1
  have h_lt_top : volume (f '' wz1PaperGridCube scale (0, 0, 0)) < ⊤ :=
    h_image_bdd.measure_lt_top
  exact h_lt_top.ne

/-- Intersection of retained-cell union with a coarse rho-cube. -/
theorem wz2RefinedUnion_inter_coarseCube
    {delta rho : ℝ}
    {retainedCoarseCells : Finset (ℤ × ℤ × ℤ)}
    {selectedFineCells : (ℤ × ℤ × ℤ) → Finset (ℤ × ℤ × ℤ)}
    {retainedFineCells : Finset (ℤ × ℤ × ℤ)}
    (h_retained :
      retainedFineCells =
        retainedCoarseCells.biUnion selectedFineCells)
    (h_containment :
      ∀ coarseCell ∈ retainedCoarseCells,
        ∀ fineCell ∈ selectedFineCells coarseCell,
          wz1PaperGridCube delta fineCell ⊆
            wz1PaperGridCube rho coarseCell)
    {coarseCell : ℤ × ℤ × ℤ}
    (hcoarse : coarseCell ∈ retainedCoarseCells) :
    (wz2RetainedCellsUnion delta retainedFineCells) ∩
      wz1PaperGridCube rho coarseCell =
    ⋃ fineCell ∈ selectedFineCells coarseCell,
      wz1PaperGridCube delta fineCell := by
  rw [h_retained]
  ext point
  have h_iff1 : point ∈ wz2RetainedCellsUnion delta
        (retainedCoarseCells.biUnion selectedFineCells) ↔
      ∃ (c : ℤ × ℤ × ℤ), c ∈ retainedCoarseCells ∧
        ∃ (f : ℤ × ℤ × ℤ), f ∈ selectedFineCells c ∧
          point ∈ wz1PaperGridCube delta f := by
    simp [wz2RetainedCellsUnion, Finset.mem_biUnion]
  constructor
  · intro h
    have hpointRho : point ∈ wz1PaperGridCube rho coarseCell := h.2
    have h1 := h_iff1.mp h.1
    rcases h1 with ⟨c, hc, f, hf, hpoint⟩
    have h_cont : wz1PaperGridCube delta f ⊆
          wz1PaperGridCube rho c :=
      h_containment c hc f hf
    have h_in_rho_c : point ∈ wz1PaperGridCube rho c :=
      h_cont hpoint
    have h_index_eq : c = coarseCell := by
      have hi : wz1PaperGridIndex rho point = c :=
        (mem_wz1PaperGridCube rho c point).mp h_in_rho_c
      have hj : wz1PaperGridIndex rho point = coarseCell :=
        (mem_wz1PaperGridCube rho coarseCell point).mp hpointRho
      exact hi.symm.trans hj
    subst h_index_eq
    exact Set.mem_iUnion₂.mpr ⟨f, hf, hpoint⟩
  · intro h
    rcases Set.mem_iUnion₂.mp h with ⟨f, hf, hpoint⟩
    have h_cont : wz1PaperGridCube delta f ⊆
          wz1PaperGridCube rho coarseCell :=
      h_containment coarseCell hcoarse f hf
    have h1 : point ∈ wz2RetainedCellsUnion delta
          (retainedCoarseCells.biUnion selectedFineCells) := by
      rw [h_iff1]
      exact ⟨coarseCell, hcoarse, f, hf, hpoint⟩
    exact ⟨h1, h_cont hpoint⟩

/-- Distinct shifted paper grid cubes are disjoint. -/
theorem wz2PaperShiftedGridCube_disjoint
    {rho : ℝ} {choice : WZ2PaperGridShiftChoice}
    {i j : WZ2PaperCellIndex} (h : i ≠ j) :
    Disjoint (wz2PaperShiftedGridCube rho choice i)
      (wz2PaperShiftedGridCube rho choice j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hi : wz2PaperShiftedGridIndex rho choice x = i := hxi
  have hj : wz2PaperShiftedGridIndex rho choice x = j := hxj
  exact h (hi.symm.trans hj)

/-- Intersection of retained-cell union with a shifted coarse rho-cube. -/
theorem wz2RefinedUnion_inter_shiftedCoarseCube
    {delta rho : ℝ}
    {choice : WZ2PaperGridShiftChoice}
    {retainedCoarseCells : Finset WZ2PaperCellIndex}
    {selectedFineCells : WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {retainedFineCells : Finset WZ2PaperCellIndex}
    (h_retained :
      retainedFineCells =
        retainedCoarseCells.biUnion selectedFineCells)
    (h_containment :
      ∀ coarseCell ∈ retainedCoarseCells,
        ∀ fineCell ∈ selectedFineCells coarseCell,
          wz1PaperGridCube delta fineCell ⊆
            wz2PaperShiftedGridCube rho choice coarseCell)
    {coarseCell : WZ2PaperCellIndex}
    (hcoarse : coarseCell ∈ retainedCoarseCells) :
    (wz2RetainedCellsUnion delta retainedFineCells) ∩
      wz2PaperShiftedGridCube rho choice coarseCell =
    ⋃ fineCell ∈ selectedFineCells coarseCell,
      wz1PaperGridCube delta fineCell := by
  rw [h_retained]
  ext point
  have h_iff1 : point ∈ wz2RetainedCellsUnion delta
        (retainedCoarseCells.biUnion selectedFineCells) ↔
      ∃ (c : WZ2PaperCellIndex), c ∈ retainedCoarseCells ∧
        ∃ (f : WZ2PaperCellIndex), f ∈ selectedFineCells c ∧
          point ∈ wz1PaperGridCube delta f := by
    simp [wz2RetainedCellsUnion, Finset.mem_biUnion]
  constructor
  · intro h
    have hpointRho : point ∈ wz2PaperShiftedGridCube rho choice coarseCell := h.2
    have h1 := h_iff1.mp h.1
    rcases h1 with ⟨c, hc, f, hf, hpoint⟩
    have h_cont : wz1PaperGridCube delta f ⊆
          wz2PaperShiftedGridCube rho choice c :=
      h_containment c hc f hf
    have h_in_rho_c : point ∈ wz2PaperShiftedGridCube rho choice c :=
      h_cont hpoint
    have h_index_eq : c = coarseCell := by
      have hi : wz2PaperShiftedGridIndex rho choice point = c := h_in_rho_c
      have hj : wz2PaperShiftedGridIndex rho choice point = coarseCell := hpointRho
      exact hi.symm.trans hj
    subst h_index_eq
    exact Set.mem_iUnion₂.mpr ⟨f, hf, hpoint⟩
  · intro h
    rcases Set.mem_iUnion₂.mp h with ⟨f, hf, hpoint⟩
    have h_cont : wz1PaperGridCube delta f ⊆
          wz2PaperShiftedGridCube rho choice coarseCell :=
      h_containment coarseCell hcoarse f hf
    have h1 : point ∈ wz2RetainedCellsUnion delta
          (retainedCoarseCells.biUnion selectedFineCells) := by
      rw [h_iff1]
      exact ⟨coarseCell, hcoarse, f, hf, hpoint⟩
    exact ⟨h1, h_cont hpoint⟩

end Kakeya.Assouad
