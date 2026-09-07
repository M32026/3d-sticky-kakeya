import MyLeanRepo.Kakeya.Assouad.WZ1.Statements
import MyLeanRepo.Kakeya.Assouad.WZ1.GreedyColoring
import MyLeanRepo.Kakeya.Assouad.WZ1.Helpers
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCovering
import Mathlib.Tactic

/-!
# WZ1 Lemma 15: finest-scale exact-cell plane-map refinement

In each active measurable `delta`-cell, retain one directed plane-map cap of
radius `delta / 2`; then color the nearby-cell graph and keep one color class so
any retained points at distance at most `delta` lie in the same cell.
-/

namespace Kakeya.Assouad

open MeasureTheory Set Finset SimpleGraph

theorem wz1_finest_cell_plane_map :
    WZ1FinestCellPlaneMapStatement := by
  intro delta hdelta F Y cellCount cell hcell representative
    neighborBound hnbound hnearby hrep planeMap hplane hunit
  classical

  by_cases h0 : cellCount = 0
  · subst h0
    exact False.elim (Fin.elim0 (cell (0 : Point3)))

  let N : ℕ := Nat.ceil (4 * Real.sqrt 3 / delta) + 1
  have hN1 : 1 ≤ N := by
    dsimp only [N]
    exact Nat.succ_pos _
  have hN_gt : (4 * Real.sqrt 3 / delta : ℝ) < (N : ℝ) := by
    dsimp only [N]
    have h1 : (4 * Real.sqrt 3 / delta : ℝ) ≤
        ↑(Nat.ceil (4 * Real.sqrt 3 / delta)) := Nat.le_ceil _
    have h2 : (↑(Nat.ceil (4 * Real.sqrt 3 / delta)) : ℝ) < (N : ℝ) := by
      simp [N] <;> linarith
    linarith
  have hdiam : Real.sqrt 3 * (2 * (1 : ℝ) / N) ≤ delta / 2 := by
    have h15 : 0 < delta := hdelta
    have h16 : (4 * Real.sqrt 3 / delta : ℝ) < (N : ℝ) := hN_gt
    have h17 : 4 * Real.sqrt 3 < (N : ℝ) * delta := by
      calc
        4 * Real.sqrt 3 = (4 * Real.sqrt 3 / delta) * delta := by
          field_simp [h15.ne'] <;> ring
        _ < (N : ℝ) * delta := by gcongr
    have h18 : Real.sqrt 3 * (2 * (1 : ℝ) / N) =
        2 * Real.sqrt 3 / (N : ℝ) := by ring
    rw [h18]
    have h19 : 2 * Real.sqrt 3 / (N : ℝ) < delta / 2 := by
      have hpos : 0 < (2 * (N : ℝ)) := by positivity
      have h : 2 * Real.sqrt 3 / (N : ℝ) <
          ((N : ℝ) * delta) / (2 * (N : ℝ)) := by
        calc
          2 * Real.sqrt 3 / (N : ℝ) =
              (4 * Real.sqrt 3) / (2 * (N : ℝ)) := by ring
          _ < ((N : ℝ) * delta) / (2 * (N : ℝ)) := by gcongr
      have h2 : ((N : ℝ) * delta) / (2 * (N : ℝ)) = delta / 2 := by
        field_simp [hN1] <;> ring
      rw [h2] at h
      exact h
    exact h19.le

  let capCount1 : ℕ := 2 * N ^ 3
  have hcapCount1 : wz1FinestPlaneMapCapCount delta = capCount1 := by
    have h_eq : 2 * Real.sqrt 3 * (1 : ℝ) / (delta / 2) =
        4 * Real.sqrt 3 / delta := by
      field_simp [hdelta.ne'] <;> ring
    dsimp only [wz1FinestPlaneMapCapCount, wz1OrientationCapCount, capCount1, N]
    rw [h_eq]
    <;> rfl

  obtain ⟨C, hC_meas, hC_cover, hC_diam⟩ :=
    grid_covering_cover (0 : Point3) 1 (delta / 2) (by norm_num) N hN1
      (by linarith) hdiam

  let Idx := Fin 3 → Fin N
  let CapIdx := Fin 2 × Idx

  let defaultUnit : Point3 :=
    WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)
  have hdefaultUnit_norm : ‖defaultUnit‖ = 1 := by
    simp [defaultUnit, PiLp.norm_eq_of_L2, Fin.sum_univ_succ]
    <;> norm_num

  let v (k : Idx) : Point3 :=
    if h : (C k ∩ Metric.sphere 0 1).Nonempty then
      Classical.choose h
    else
      defaultUnit
  have hv_norm : ∀ k : Idx, ‖v k‖ = 1 := by
    intro k
    dsimp only [v]
    by_cases h : (C k ∩ Metric.sphere 0 1).Nonempty
    · rw [dif_pos h]
      have h2 : Classical.choose h ∈ C k ∩ Metric.sphere 0 1 :=
        Classical.choose_spec h
      have h3 : Classical.choose h ∈ Metric.sphere 0 1 := h2.2
      simpa [Metric.mem_sphere] using h3
    · rw [dif_neg h]
      exact hdefaultUnit_norm

  let capCenter : CapIdx → Point3 := fun idx => v idx.2
  have hcapCenter_norm : ∀ idx : CapIdx, ‖capCenter idx‖ = 1 := by
    intro idx
    exact hv_norm idx.2

  have hsphere_cover : ∀ (x : Point3), ‖x‖ = 1 →
      ∃ idx : CapIdx, Dist.dist x (capCenter idx) ≤ delta / 2 := by
    intro x hx
    have hdist0 : Dist.dist x (0 : Point3) ≤ 1 := by
      have h1 : Dist.dist x (0 : Point3) = ‖x‖ := by
        simp [dist_eq_norm]
      rw [h1, hx] <;> norm_num
    rcases hC_cover x hdist0 with ⟨k, hk⟩
    have h_inter : (C k ∩ Metric.sphere 0 1).Nonempty := by
      refine ⟨x, hk, ?_⟩
      simpa [Metric.mem_sphere] using hx
    have hv_in : v k ∈ C k := by
      dsimp only [v]
      rw [dif_pos h_inter]
      exact (Classical.choose_spec h_inter).1
    let idx : CapIdx := (0, k)
    have hidx : capCenter idx = v k := by
      simp [capCenter, idx] <;> rfl
    refine ⟨idx, ?_⟩
    rw [hidx]
    exact hC_diam k x (v k) hk hv_in

  let capSet (c : Fin cellCount) (idx : CapIdx) : Set Point3 :=
    {p | cell p = c ∧ p ∈ Y.union ∧
      dist (planeMap p) (capCenter idx) ≤ delta / 2}

  have hcapSet_meas : ∀ c idx, MeasurableSet (capSet c idx) := by
    intro c idx
    have h1 : MeasurableSet {p : Point3 | cell p = c} :=
      hcell (measurableSet_singleton c)
    have h2 : MeasurableSet
        {p | dist (planeMap p) (capCenter idx) ≤ delta / 2} := by
      have h : Measurable
          (fun p : Point3 => dist (planeMap p) (capCenter idx)) := by
        fun_prop
      exact measurableSet_le h measurable_const
    have hYunion_meas : MeasurableSet Y.union := by
      have h : Y.union = ⋃ i : Fin F.card, Y.carrier i := by
        ext x
        simp [Kakeya.Streamlined.Shading.union] <;> aesop
      rw [h]
      exact MeasurableSet.iUnion (fun i => Y.measurable_carrier i)
    have h4 : capSet c idx =
        {p | cell p = c} ∩ Y.union ∩
          {p | dist (planeMap p) (capCenter idx) ≤ delta / 2} := by
      ext x
      simp [capSet] <;> tauto
    rw [h4]
    exact h1.inter hYunion_meas |>.inter h2

  have hcap_subset_cell : ∀ c idx, capSet c idx ⊆ {p | cell p = c} := by
    intro c idx p hp
    exact hp.1

  have hcap_cover : ∀ c,
      {p | cell p = c ∧ p ∈ Y.union} ⊆ ⋃ idx : CapIdx, capSet c idx := by
    intro c p hp
    have hcell_p : cell p = c := hp.1
    have hY_p : p ∈ Y.union := hp.2
    have hunit_p : ‖planeMap p‖ = 1 := hunit p hY_p
    rcases hsphere_cover (planeMap p) hunit_p with ⟨idx, hidx⟩
    have hmem : p ∈ capSet c idx := by
      exact ⟨hcell_p, hY_p, hidx⟩
    exact Set.mem_iUnion.mpr ⟨idx, hmem⟩

  let cellSlice (c : Fin cellCount) : Set Point3 := {p | cell p = c}
  let massCell (c : Fin cellCount) : ENNReal :=
    ∑ i : Fin F.card, volume (Y.carrier i ∩ cellSlice c)
  let massCellCap (c : Fin cellCount) (idx : CapIdx) : ENNReal :=
    ∑ i : Fin F.card, volume (Y.carrier i ∩ capSet c idx)

  have hsub : ∀ (i : Fin F.card) (c : Fin cellCount),
      volume (Y.carrier i ∩ cellSlice c) ≤
        ∑ idx : CapIdx, volume (Y.carrier i ∩ capSet c idx) := by
    intro i c
    have hYsub : Y.carrier i ⊆ Y.union := by
      intro x hx
      exact ⟨i, hx⟩
    have hcover : Y.carrier i ∩ cellSlice c ⊆
        ⋃ idx : CapIdx, Y.carrier i ∩ capSet c idx := by
      intro x hx
      have hxi : x ∈ Y.carrier i := hx.1
      have hxcell : x ∈ cellSlice c := hx.2
      have h3 : x ∈ Y.union := hYsub hxi
      have h4 : x ∈ {p | cell p = c ∧ p ∈ Y.union} := ⟨hxcell, h3⟩
      have h5 : x ∈ ⋃ idx : CapIdx, capSet c idx := hcap_cover c h4
      rcases Set.mem_iUnion.mp h5 with ⟨idx, h6⟩
      exact Set.mem_iUnion.mpr ⟨idx, ⟨hxi, h6⟩⟩
    have h_mono : volume (Y.carrier i ∩ cellSlice c) ≤
        volume (⋃ idx : CapIdx, Y.carrier i ∩ capSet c idx) :=
      measure_mono hcover
    have h_subadd :
        volume (⋃ idx : CapIdx, Y.carrier i ∩ capSet c idx) ≤
          ∑ idx : CapIdx, volume (Y.carrier i ∩ capSet c idx) := by
      have h_tsum :
          volume (⋃ idx : CapIdx, Y.carrier i ∩ capSet c idx) ≤
            ∑' idx : CapIdx, volume (Y.carrier i ∩ capSet c idx) :=
        measure_iUnion_le (fun idx : CapIdx => Y.carrier i ∩ capSet c idx)
      simpa only [tsum_fintype] using h_tsum
    exact h_mono.trans h_subadd

  have hmass_cell_le : ∀ c,
      massCell c ≤ ∑ idx : CapIdx, massCellCap c idx := by
    intro c
    dsimp only [massCell, massCellCap]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i _
    exact hsub i c

  letI : Nonempty CapIdx :=
    ⟨(0, fun _ => ⟨0, by omega⟩)⟩

  choose idx_c h_idx_c using
    fun c : Fin cellCount =>
      exists_ge_average (f := fun idx : CapIdx => massCellCap c idx)

  have hcard : Fintype.card CapIdx = capCount1 := by
    have h1 : Fintype.card CapIdx =
        Fintype.card (Fin 2) * Fintype.card Idx := by
      simp [CapIdx, Fintype.card_prod] <;> rfl
    rw [h1]
    have h2 : Fintype.card (Fin 2) = 2 := by decide
    have h3 : Fintype.card Idx = N ^ 3 := by
      have h4 : Fintype.card Idx = Fintype.card (Fin 3 → Fin N) := by
        simp [Idx]
      rw [h4]
      simp [Fintype.card_fun, Fintype.card_fin] <;> ring
    rw [h2, h3] <;> rfl

  have hpigeon : ∀ c,
      massCell c ≤ (capCount1 : ENNReal) * massCellCap c (idx_c c) := by
    intro c
    have h : (Fintype.card CapIdx : ENNReal) *
        massCellCap c (idx_c c) ≥
          ∑ idx : CapIdx, massCellCap c idx := h_idx_c c
    have h' : massCell c ≤ ∑ idx : CapIdx, massCellCap c idx :=
      hmass_cell_le c
    rw [hcard] at h
    exact h'.trans h

  let selectedSet1 : Set Point3 := ⋃ c : Fin cellCount, capSet c (idx_c c)

  have hselectedSet1_meas : MeasurableSet selectedSet1 := by
    dsimp only [selectedSet1]
    exact MeasurableSet.iUnion (fun c => hcapSet_meas c (idx_c c))

  let shading1 : Kakeya.Streamlined.TubeShading F :=
    { carrier := fun i => Y.carrier i ∩ selectedSet1
      measurable_carrier := fun i =>
        (Y.measurable_carrier i).inter hselectedSet1_meas
      subset_body := fun i =>
        Set.Subset.trans Set.inter_subset_left (Y.subset_body i) }

  have hcells_disjoint : ∀ c1 c2 : Fin cellCount,
      c1 ≠ c2 → Disjoint (cellSlice c1) (cellSlice c2) := by
    intro c1 c2 hne
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have h1 : cell x = c1 := hx1
    have h2 : cell x = c2 := hx2
    rw [h1] at h2
    exact hne h2

  have hmass1_shading : ∀ i,
      volume (shading1.carrier i) =
        ∑ c : Fin cellCount,
          volume (Y.carrier i ∩ capSet c (idx_c c)) := by
    intro i
    have h2 : shading1.carrier i =
        ⋃ c : Fin cellCount, Y.carrier i ∩ capSet c (idx_c c) := by
      ext x
      simp [shading1, selectedSet1, Set.mem_iUnion] <;> aesop
    rw [h2]
    have hdisj : Set.PairwiseDisjoint
        (Finset.univ : Finset (Fin cellCount))
        (fun c => Y.carrier i ∩ capSet c (idx_c c)) := by
      intro c1 _ c2 _ hne
      have h4 : Disjoint
          (capSet c1 (idx_c c1)) (capSet c2 (idx_c c2)) :=
        (hcells_disjoint c1 c2 hne).mono
          (hcap_subset_cell c1 (idx_c c1))
          (hcap_subset_cell c2 (idx_c c2))
      exact h4.mono Set.inter_subset_right Set.inter_subset_right
    have hmeas : ∀ c ∈ (Finset.univ : Finset (Fin cellCount)),
        MeasurableSet (Y.carrier i ∩ capSet c (idx_c c)) := by
      intro c _
      exact (Y.measurable_carrier i).inter (hcapSet_meas c (idx_c c))
    have h_eq :
        volume (⋃ c ∈ (Finset.univ : Finset (Fin cellCount)),
          Y.carrier i ∩ capSet c (idx_c c)) =
            ∑ c ∈ (Finset.univ : Finset (Fin cellCount)),
              volume (Y.carrier i ∩ capSet c (idx_c c)) :=
      measure_biUnion_finset hdisj hmeas
    simpa [Set.biUnion_univ, Finset.mem_univ] using h_eq

  have hmass2 :
      shading1.mass = ∑ c : Fin cellCount, massCellCap c (idx_c c) := by
    change ∑ i : Fin F.card, volume (shading1.carrier i) =
        ∑ c : Fin cellCount, massCellCap c (idx_c c)
    calc
      ∑ i : Fin F.card, volume (shading1.carrier i) =
          ∑ i : Fin F.card, ∑ c : Fin cellCount,
            volume (Y.carrier i ∩ capSet c (idx_c c)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hmass1_shading i
      _ = ∑ c : Fin cellCount, ∑ i : Fin F.card,
            volume (Y.carrier i ∩ capSet c (idx_c c)) := by
        rw [Finset.sum_comm]
      _ = ∑ c : Fin cellCount, massCellCap c (idx_c c) := by rfl

  have htotal_mass : ∑ c : Fin cellCount, massCell c = Y.mass := by
    dsimp only [massCell, Kakeya.Streamlined.Shading.mass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have hfiber_meas :
        ∀ c : Fin cellCount, MeasurableSet (cellSlice c) := by
      intro c
      exact hcell (measurableSet_singleton c)
    let pieces : Fin cellCount → Set Point3 :=
      fun c => Y.carrier i ∩ cellSlice c
    have hdisj : Set.PairwiseDisjoint
        (Finset.univ : Finset (Fin cellCount)) pieces := by
      intro c1 _ c2 _ hne
      exact (hcells_disjoint c1 c2 hne).mono
        Set.inter_subset_right Set.inter_subset_right
    have hmeas : ∀ c ∈ (Finset.univ : Finset (Fin cellCount)),
        MeasurableSet (pieces c) := by
      intro c _
      exact (Y.measurable_carrier i).inter (hfiber_meas c)
    have hcover : Y.carrier i = ⋃ c : Fin cellCount, pieces c := by
      ext x
      simp only [pieces, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro hxi
        exact ⟨cell x, hxi, rfl⟩
      · rintro ⟨c, hxi, _⟩
        exact hxi
    have h_eq : volume (⋃ c : Fin cellCount, pieces c) =
        ∑ c : Fin cellCount, volume (pieces c) := by
      have h :
          volume (⋃ c ∈ (Finset.univ : Finset (Fin cellCount)), pieces c) =
            ∑ c ∈ (Finset.univ : Finset (Fin cellCount)),
              volume (pieces c) :=
        measure_biUnion_finset hdisj hmeas
      simpa [Set.biUnion_univ, Finset.mem_univ] using h
    have h9 :
        volume (Y.carrier i) =
          volume (⋃ c : Fin cellCount, pieces c) := by
      rw [hcover]
    rw [h9, h_eq] <;> rfl

  have hmass_lower1 :
      Y.mass ≤ (capCount1 : ENNReal) * shading1.mass := by
    rw [htotal_mass.symm, hmass2]
    calc
      ∑ c : Fin cellCount, massCell c ≤
          ∑ c : Fin cellCount,
            (capCount1 : ENNReal) * massCellCap c (idx_c c) := by
        apply Finset.sum_le_sum
        intro c _
        exact hpigeon c
      _ = (capCount1 : ENNReal) *
          ∑ c : Fin cellCount, massCellCap c (idx_c c) := by
        rw [Finset.mul_sum]

  let representativeMap : Point3 → Point3 :=
    fun p => capCenter (idx_c (cell p))

  have h_fintype_meas :
      ∀ (f : Fin cellCount → Point3), Measurable f := by
    intro f
    intro s _
    have hfin : Set.Finite (f ⁻¹' s) := Set.toFinite _
    exact hfin.measurableSet
  have hrepMap_meas : Measurable representativeMap :=
    (h_fintype_meas (capCenter ∘ idx_c)).comp hcell

  have hrepMap_unit :
      ∀ p ∈ shading1.union, ‖representativeMap p‖ = 1 := by
    intro p _
    exact hcapCenter_norm (idx_c (cell p))

  have hrepMap_close : ∀ p ∈ shading1.union,
      dist (representativeMap p) (planeMap p) ≤ delta / 2 := by
    intro p hp
    rcases hp with ⟨i, hi⟩
    have hp_sel : p ∈ selectedSet1 := hi.2
    rcases Set.mem_iUnion.mp hp_sel with ⟨c, hc⟩
    have hc1 : cell p = c := hcap_subset_cell c (idx_c c) hc
    have hdist :
        dist (planeMap p) (capCenter (idx_c c)) ≤ delta / 2 := hc.2.2
    have hrep : representativeMap p = capCenter (idx_c c) := by
      dsimp only [representativeMap]
      rw [hc1]
      <;> rfl
    rw [hrep]
    rw [_root_.dist_comm]
    exact hdist

  have hconstant_on_cells1 :
      ∀ p ∈ shading1.union, ∀ q ∈ shading1.union,
        cell p = cell q → representativeMap p = representativeMap q := by
    intro p _ q _ h
    dsimp only [representativeMap]
    rw [h]

  let active : Fin cellCount → Prop := fun c =>
    {p | p ∈ Y.union ∧ cell p = c}.Nonempty

  let G : SimpleGraph (Fin cellCount) :=
    { Adj := fun c d =>
        c ≠ d ∧ active c ∧ active d ∧
          Dist.dist (representative c) (representative d) ≤ 6 * delta
      symm := ⟨fun {c d} h =>
        ⟨h.1.symm, h.2.2.1, h.2.1,
          _root_.dist_comm (representative c) (representative d) ▸ h.2.2.2⟩⟩
      loopless := ⟨fun c h => h.1 rfl⟩ }

  have hG : ∀ c d, G.Adj c d ↔
      c ≠ d ∧ active c ∧ active d ∧
        Dist.dist (representative c) (representative d) ≤ 6 * delta := by
    intro c d
    rfl

  have h_count : ∀ c, active c →
      (Finset.univ.filter fun d : Fin cellCount =>
        active d ∧ dist (representative c) (representative d) ≤
          6 * delta).card ≤ neighborBound := by
    intro c hc
    exact hnearby c hc

  have h_deg :
      ∀ c : Fin cellCount, (G.neighborFinset c).card ≤ neighborBound :=
    nearby_cell_graph_degree_le
      active representative delta G hG neighborBound h_count

  have h_deg' : ∀ c : Fin cellCount, G.degree c ≤ neighborBound := by
    intro c
    have h_eq : G.degree c = (G.neighborFinset c).card :=
      SimpleGraph.card_neighborFinset_eq_degree G c
    rw [h_eq]
    exact h_deg c

  have h_colorable : G.Colorable (neighborBound + 1) :=
    SimpleGraph.colorable_of_forall_degree_le h_deg'

  rcases h_colorable with ⟨coloring⟩
  let color : Fin cellCount → Fin (neighborBound + 1) := coloring

  have h_proper : ∀ c d, G.Adj c d → color c ≠ color d := by
    intro c d h
    exact coloring.valid h

  let S : Fin (neighborBound + 1) → Set Point3 := fun k =>
    {p | color (cell p) = k}

  have h_color_meas : Measurable color := by fun_prop

  have hS_meas :
      ∀ k : Fin (neighborBound + 1), MeasurableSet (S k) := by
    intro k
    have h_comp : Measurable (color ∘ cell) :=
      h_color_meas.comp hcell
    have hS_eq :
        S k = (color ∘ cell) ⁻¹' ({k} : Set (Fin (neighborBound + 1))) := by
      ext p
      simp [S, Function.comp_apply] <;> rfl
    rw [hS_eq]
    exact h_comp (by simp)

  have hS_disj :
      ∀ k1 k2 : Fin (neighborBound + 1), k1 ≠ k2 →
        Disjoint (S k1) (S k2) := by
    intro k1 k2 hne
    rw [Set.disjoint_left]
    intro p hp1 hp2
    have h3 : color (cell p) = k1 := hp1
    have h4 : color (cell p) = k2 := hp2
    rw [h3] at h4
    exact hne h4

  have hS_univ :
      (⋃ k : Fin (neighborBound + 1), S k) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    exact Set.mem_iUnion.mpr ⟨color (cell p), rfl⟩

  let shadingK :
      Fin (neighborBound + 1) → Kakeya.Streamlined.TubeShading F :=
    fun k =>
      { carrier := fun i => shading1.carrier i ∩ S k
        measurable_carrier := fun i =>
          (shading1.measurable_carrier i).inter (hS_meas k)
        subset_body := fun i =>
          Set.inter_subset_left.trans (shading1.subset_body i) }

  have h_mass_partition : ∀ i,
      volume (shading1.carrier i) =
        ∑ k : Fin (neighborBound + 1),
          volume (shading1.carrier i ∩ S k) := by
    intro i
    let f : Fin (neighborBound + 1) → Set Point3 :=
      fun k => shading1.carrier i ∩ S k
    have h_union : shading1.carrier i = ⋃ k, f k := by
      calc
        shading1.carrier i =
            shading1.carrier i ∩
              (⋃ k : Fin (neighborBound + 1), S k) := by
          rw [hS_univ] <;> simp
        _ = ⋃ k : Fin (neighborBound + 1), f k := by
          rw [Set.inter_iUnion]
    have h_biUnion : (⋃ k : Fin (neighborBound + 1), f k) =
        ⋃ k ∈ (Finset.univ : Finset (Fin (neighborBound + 1))), f k := by
      ext x
      simp
    have h_meas :
        ∀ k ∈ (Finset.univ : Finset (Fin (neighborBound + 1))),
          MeasurableSet (f k) := by
      intro k _
      exact (shading1.measurable_carrier i).inter (hS_meas k)
    have h_disj : Set.PairwiseDisjoint
        (↑(Finset.univ : Finset (Fin (neighborBound + 1)))) f := by
      intro k1 _ k2 _ hne
      exact (hS_disj k1 k2 hne).mono
        Set.inter_subset_right Set.inter_subset_right
    have h_main :
        volume
            (⋃ k ∈ (Finset.univ : Finset (Fin (neighborBound + 1))),
              f k) =
          ∑ k ∈ (Finset.univ : Finset (Fin (neighborBound + 1))),
            volume (f k) :=
      MeasureTheory.measure_biUnion_finset h_disj h_meas
    calc
      volume (shading1.carrier i) = volume (⋃ k, f k) := by rw [h_union]
      _ = volume
          (⋃ k ∈ (Finset.univ : Finset (Fin (neighborBound + 1))),
            f k) := by
        rw [h_biUnion]
      _ = ∑ k ∈ (Finset.univ : Finset (Fin (neighborBound + 1))),
            volume (f k) := h_main
      _ = ∑ k : Fin (neighborBound + 1), volume (f k) := by simp

  have h_total_mass2 :
      shading1.mass =
        ∑ k : Fin (neighborBound + 1), (shadingK k).mass := by
    calc
      shading1.mass = ∑ i, volume (shading1.carrier i) := by rfl
      _ = ∑ i, ∑ k : Fin (neighborBound + 1),
            volume (shading1.carrier i ∩ S k) := by
          apply Finset.sum_congr rfl
          intro i _
          exact h_mass_partition i
      _ = ∑ k : Fin (neighborBound + 1), ∑ i,
            volume (shading1.carrier i ∩ S k) := by
          rw [Finset.sum_comm]
      _ = ∑ k : Fin (neighborBound + 1), (shadingK k).mass := by rfl

  let s : Finset (Fin (neighborBound + 1)) := Finset.univ
  have hs_nonempty : s.Nonempty := by simp [s]

  obtain ⟨k0, hk0, h_mass_lower2⟩ :
      ∃ k0 ∈ s,
        ((neighborBound + 1 : ℕ) : ENNReal) *
            (shadingK k0).mass ≥ shading1.mass := by
    rcases finset_ennreal_pigeonhole hs_nonempty
        (fun k => (shadingK k).mass) with
      ⟨k0, hk0, hge⟩
    have h_card : s.card = neighborBound + 1 := by simp [s]
    have h_sum :
        ∑ j ∈ s, (shadingK j).mass = shading1.mass := by
      simpa [s] using h_total_mass2.symm
    rw [h_card, h_sum] at hge
    exact ⟨k0, hk0, hge⟩

  let selectedSet : Set Point3 := selectedSet1 ∩ S k0
  let shading : Kakeya.Streamlined.TubeShading F := shadingK k0

  have h_selectedSet_meas : MeasurableSet selectedSet :=
    hselectedSet1_meas.inter (hS_meas k0)

  have h_subshading1 : IsSubshading shading1 Y := by
    intro i
    exact Set.inter_subset_left

  have h_subshading : IsSubshading shading Y := by
    intro i
    exact Set.inter_subset_left.trans (h_subshading1 i)

  have h_carrier_eq :
      ∀ i, shading.carrier i = Y.carrier i ∩ selectedSet := by
    intro i
    have h : shading.carrier i = shading1.carrier i ∩ S k0 := by rfl
    rw [h]
    have h2 : shading1.carrier i = Y.carrier i ∩ selectedSet1 := by rfl
    rw [h2]
    ext x
    simp [selectedSet, Set.mem_inter_iff]
    <;> tauto

  have h_mass_lower_raw : Y.mass ≤
      (↑((neighborBound + 1) * capCount1) : ENNReal) * shading.mass := by
    have h1 :
        Y.mass ≤ (capCount1 : ENNReal) * shading1.mass :=
      hmass_lower1
    have h2 :
        shading1.mass ≤
          (↑(neighborBound + 1) : ENNReal) * shading.mass :=
      h_mass_lower2
    have h3 :
        (capCount1 : ENNReal) * shading1.mass ≤
          (capCount1 : ENNReal) *
            ((↑(neighborBound + 1) : ENNReal) * shading.mass) := by
      gcongr
    have h4 :
        (capCount1 : ENNReal) *
            ((↑(neighborBound + 1) : ENNReal) * shading.mass) =
          (↑((neighborBound + 1) * capCount1) : ENNReal) *
            shading.mass := by
      have h5 :
          (capCount1 : ENNReal) *
              (↑(neighborBound + 1) : ENNReal) =
            (↑((neighborBound + 1) * capCount1) : ENNReal) := by
        rw [←Nat.cast_mul]
        <;> simp [mul_comm]
      calc
        (capCount1 : ENNReal) *
            ((↑(neighborBound + 1) : ENNReal) * shading.mass) =
              (capCount1 : ENNReal) *
                (↑(neighborBound + 1) : ENNReal) * shading.mass := by
          rw [mul_assoc]
        _ = (↑((neighborBound + 1) * capCount1) : ENNReal) *
              shading.mass := by
          rw [h5]
    rw [h4] at h3
    exact h1.trans h3

  have h_union_subset :
      ∀ {Z Y' : Kakeya.Streamlined.TubeShading F},
        IsSubshading Z Y' → Z.union ⊆ Y'.union := by
    intro Z' Y' hZ p hp
    rcases hp with ⟨i, hi⟩
    exact ⟨i, hZ i hi⟩

  have h_nearby_same_cell :
      ∀ p ∈ shading.union, ∀ q ∈ shading.union,
        dist p q ≤ delta → cell p = cell q := by
    intro p hp q hq h_dist
    have hp1 : p ∈ shading1.union :=
      h_union_subset
        (show IsSubshading shading shading1 from
          fun i => Set.inter_subset_left) hp
    have hq1 : q ∈ shading1.union :=
      h_union_subset
        (show IsSubshading shading shading1 from
          fun i => Set.inter_subset_left) hq
    have hpY : p ∈ Y.union := h_union_subset h_subshading1 hp1
    have hqY : q ∈ Y.union := h_union_subset h_subshading1 hq1
    let c := cell p
    let d := cell q
    have hc_active : active c := ⟨p, hpY, rfl⟩
    have hd_active : active d := ⟨q, hqY, rfl⟩
    have hrep_p : dist p (representative c) ≤ 2 * delta :=
      (hrep p hpY).2.2
    have hrep_q : dist q (representative d) ≤ 2 * delta :=
      (hrep q hqY).2.2
    have hdist_reps :
        dist (representative c) (representative d) ≤ 5 * delta := by
      calc
        dist (representative c) (representative d) ≤
            dist (representative c) p + dist p q +
              dist q (representative d) :=
          dist_triangle4 _ _ _ _
        _ ≤ 2 * delta + delta + 2 * delta := by
          rw [dist_comm (representative c) p]
          <;> linarith
        _ = 5 * delta := by ring
    have hdist6 :
        dist (representative c) (representative d) ≤ 6 * delta := by
      linarith
    by_contra h_neq
    have h_adj : G.Adj c d :=
      ⟨h_neq, hc_active, hd_active, hdist6⟩
    have h_color_p : color c = k0 := by
      rcases hp with ⟨i, hi⟩
      exact hi.2
    have h_color_q : color d = k0 := by
      rcases hq with ⟨i, hi⟩
      exact hi.2
    exact (h_proper c d h_adj) (h_color_p.trans h_color_q.symm)

  have hrepMap_unit_final :
      ∀ p ∈ shading.union, ‖representativeMap p‖ = 1 := by
    intro p hp
    have hp1 : p ∈ shading1.union :=
      h_union_subset
        (show IsSubshading shading shading1 from
          fun i => Set.inter_subset_left) hp
    exact hrepMap_unit p hp1

  have hrepMap_close_final : ∀ p ∈ shading.union,
      dist (representativeMap p) (planeMap p) ≤ delta / 2 := by
    intro p hp
    have hp1 : p ∈ shading1.union :=
      h_union_subset
        (show IsSubshading shading shading1 from
          fun i => Set.inter_subset_left) hp
    exact hrepMap_close p hp1

  have hconstant_on_cells_final :
      ∀ p ∈ shading.union, ∀ q ∈ shading.union,
        cell p = cell q → representativeMap p = representativeMap q := by
    intro p hp q hq h
    have hp1 : p ∈ shading1.union :=
      h_union_subset
        (show IsSubshading shading shading1 from
          fun i => Set.inter_subset_left) hp
    have hq1 : q ∈ shading1.union :=
      h_union_subset
        (show IsSubshading shading shading1 from
          fun i => Set.inter_subset_left) hq
    exact hconstant_on_cells1 p hp1 q hq1 h

  have h_mass_lower : Y.mass ≤
      (↑((neighborBound + 1) * wz1FinestPlaneMapCapCount delta) : ENNReal) *
        shading.mass := by
    have h_eq :
        (↑((neighborBound + 1) *
            wz1FinestPlaneMapCapCount delta) : ENNReal) =
          (↑((neighborBound + 1) * capCount1) : ENNReal) := by
      rw [hcapCount1]
      <;> rfl
    rw [h_eq]
    exact h_mass_lower_raw

  exact ⟨
    representativeMap,
    hrepMap_meas,
    selectedSet,
    h_selectedSet_meas,
    shading,
    h_subshading,
    h_carrier_eq,
    h_mass_lower,
    hrepMap_unit_final,
    hrepMap_close_final,
    hconstant_on_cells_final,
    h_nearby_same_cell
  ⟩

end Kakeya.Assouad
