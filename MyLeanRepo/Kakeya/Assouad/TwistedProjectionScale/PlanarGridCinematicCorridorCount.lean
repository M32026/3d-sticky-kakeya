import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.PlanarGridCinematicCorridorCountStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CorridorCountHelpers
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FiberCardBound

/-!
# Linear planar-grid corridor count

Bound the number of occupied planar grid cells meeting one bounded-slope
cinematic corridor by a quantity linear in the inverse mesh.
-/

namespace Kakeya.Assouad

theorem planar_grid_cinematic_corridor_count :
    PlanarGridCinematicCorridorCountStatement := by
  intro A base level slopeBlocks radiusBlocks hbase g hlip r hr hr'
  set N : ℕ := base ^ level with hN
  have hNpos : 0 < N := by positivity
  set C : ℕ := 2 * radiusBlocks + slopeBlocks * (1 + 2 * radiusBlocks) with hC
  let S := planarGridCinematicCorridorCells base level A g r
  let graph := cinematicExtensionGraph g

  classical

  -- Step 1: Pick a witness point for each cell
  have h_witness : ∀ (cell : DiscreteSet 2), cell ∈ S →
      ∃ (p : Point2), p ∈ (cell : Set Point2) ∧ p ∈ Metric.cthickening r graph := by
    intro cell hcell
    have h : ((cell : Set Point2) ∩ Metric.cthickening r graph).Nonempty :=
      (Finset.mem_filter.mp hcell).2
    exact h

  let p : DiscreteSet 2 → Point2 := fun cell =>
    if h : cell ∈ S then Classical.choose (h_witness cell h) else 0
  have hp : ∀ (cell : DiscreteSet 2), cell ∈ S →
      p cell ∈ (cell : Set Point2) ∧ p cell ∈ Metric.cthickening r graph := by
    intro cell hcell
    have hpe : p cell = Classical.choose (h_witness cell hcell) := by
      simp [p, hcell]
    rw [hpe]
    exact Classical.choose_spec (h_witness cell hcell)

  -- Index map: (x-index, y-index) where x = coordinate 1, y = coordinate 0
  let f : DiscreteSet 2 → ℤ × ℤ := fun cell =>
    (⌊p cell 1 * (N : ℝ)⌋, ⌊p cell 0 * (N : ℝ)⌋)

  -- Helper: cell in partition containing q equals planarGridCell A q
  have h_cell_eq : ∀ (cell : DiscreteSet 2), cell ∈ planarGridPartition base level A →
      ∀ (q : Point2), q ∈ (cell : Set Point2) → cell = planarGridCell base level A q := by
    intro cell hcell q hq
    rcases Finset.mem_image.mp hcell with ⟨q0, hq0, rfl⟩
    have hq2 : planarGridIndex base level q = planarGridIndex base level q0 := by
      simpa [planarGridCell, Finset.mem_filter] using (Finset.mem_filter.mp hq).2
    simp [planarGridCell, hq2]

  -- Step 2: f is injective on S
  have h_inj : Set.InjOn f S := by
    intro cell1 hcell1 cell2 hcell2 heq
    have h1 : cell1 ∈ planarGridPartition base level A := (Finset.mem_filter.mp hcell1).1
    have h2 : cell2 ∈ planarGridPartition base level A := (Finset.mem_filter.mp hcell2).1
    have hp1 : p cell1 ∈ (cell1 : Set Point2) := (hp cell1 hcell1).1
    have hp2 : p cell2 ∈ (cell2 : Set Point2) := (hp cell2 hcell2).1
    have h3 : cell1 = planarGridCell base level A (p cell1) := h_cell_eq cell1 h1 (p cell1) hp1
    have h4 : cell2 = planarGridCell base level A (p cell2) := h_cell_eq cell2 h2 (p cell2) hp2
    have h51 : ⌊p cell1 1 * (N : ℝ)⌋ = ⌊p cell2 1 * (N : ℝ)⌋ :=
      (Prod.ext_iff.mp heq).1
    have h52 : ⌊p cell1 0 * (N : ℝ)⌋ = ⌊p cell2 0 * (N : ℝ)⌋ :=
      (Prod.ext_iff.mp heq).2
    have h5 : planarGridIndex base level (p cell1) = planarGridIndex base level (p cell2) := by
      have h51' : ⌊p cell1 1 * (base ^ level : ℝ)⌋ = ⌊p cell2 1 * (base ^ level : ℝ)⌋ := by
        simpa [hN] using h51
      have h52' : ⌊p cell1 0 * (base ^ level : ℝ)⌋ = ⌊p cell2 0 * (base ^ level : ℝ)⌋ := by
        simpa [hN] using h52
      unfold planarGridIndex
      exact Prod.ext h52' h51'
    rw [h3, h4]
    simp [planarGridCell, h5]

  -- Extract witness from cthickening
  have h_extract : ∀ (cell : DiscreteSet 2), cell ∈ S →
      ∃ (q : Point2), q ∈ graph ∧ dist (p cell) q ≤ r := by
    intro cell hcell
    exact cthickening_extract (p cell) g r hr ((hp cell hcell).2)

  -- Reusable bound: r * N ≤ radiusBlocks
  have hr'N : r ≤ (radiusBlocks : ℝ) * (N : ℝ)⁻¹ := by
    simpa [hN] using hr'
  have h_rN : r * (N : ℝ) ≤ (radiusBlocks : ℝ) := by
    have hpos : 0 ≤ (N : ℝ) := by positivity
    have h : r * (N : ℝ) ≤ ((radiusBlocks : ℝ) * (N : ℝ)⁻¹) * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hr'N hpos
    have h2 : ((radiusBlocks : ℝ) * (N : ℝ)⁻¹) * (N : ℝ) = (radiusBlocks : ℝ) := by
      field_simp [hNpos.ne'] <;> ring
    rw [h2] at h
    exact h

  -- Step 3: x-index bound
  let X : Finset ℤ := Finset.Icc (-(radiusBlocks : ℤ)) ((N : ℤ) + radiusBlocks)
  have hX_card : X.card = N + 2 * radiusBlocks + 1 := by
    simp [X, Finset.Icc_eq_empty_of_lt]
    <;> omega

  have h_x_bound : ∀ cell ∈ S, (f cell).1 ∈ X := by
    intro cell hcell
    rcases h_extract cell hcell with ⟨q, hq_graph, hdist⟩
    have hq1 : q 1 ∈ Set.Icc (0 : ℝ) 1 := hq_graph.1
    have h_coord1 : |p cell 1 - q 1| ≤ dist (p cell) q :=
      euclidean_coord_dist (p cell) q 1
    have h6 : |p cell 1 - q 1| ≤ r := by linarith
    have h61 : -r ≤ p cell 1 - q 1 := (abs_le.mp h6).1
    have h62 : p cell 1 - q 1 ≤ r := (abs_le.mp h6).2
    have h7 : -(radiusBlocks : ℝ) ≤ p cell 1 * (N : ℝ) := by
      have h11 : -r ≤ p cell 1 := by linarith [h61, hq1.1]
      nlinarith
    have h8 : p cell 1 * (N : ℝ) ≤ (N : ℝ) + (radiusBlocks : ℝ) := by
      have h12 : p cell 1 ≤ 1 + r := by linarith [h62, hq1.2]
      nlinarith
    have h13 : (-(radiusBlocks : ℤ)) ≤ ⌊p cell 1 * (N : ℝ)⌋ := by
      apply Int.le_floor.mpr
      have h_eq : (↑(-(radiusBlocks : ℤ)) : ℝ) = -(radiusBlocks : ℝ) := by simp
      rw [h_eq]
      exact h7
    have h144 : ((N : ℤ) + radiusBlocks : ℝ) = (N : ℝ) + (radiusBlocks : ℝ) := by simp
    have h14 : ⌊p cell 1 * (N : ℝ)⌋ ≤ ((N : ℤ) + radiusBlocks) := by
      have h141 : (⌊p cell 1 * (N : ℝ)⌋ : ℝ) ≤ p cell 1 * (N : ℝ) := Int.floor_le _
      have h143 : (⌊p cell 1 * (N : ℝ)⌋ : ℝ) ≤ ((N : ℤ) + radiusBlocks : ℝ) := by
        rw [h144]
        linarith [h141, h8]
      exact_mod_cast h143
    exact Finset.mem_Icc.mpr ⟨h13, h14⟩

  -- Step 4: y-index spread for fixed x-index
  have h_y_spread : ∀ (cell1 : DiscreteSet 2), cell1 ∈ S →
      ∀ (cell2 : DiscreteSet 2), cell2 ∈ S →
        (f cell1).1 = (f cell2).1 → |(f cell1).2 - (f cell2).2| ≤ (C + 1 : ℤ) := by
    intro cell1 hcell1 cell2 hcell2 hsame
    rcases h_extract cell1 hcell1 with ⟨q1, hq1_graph, hdist1⟩
    rcases h_extract cell2 hcell2 with ⟨q2, hq2_graph, hdist2⟩
    have hq1_1 : q1 1 ∈ Set.Icc (0 : ℝ) 1 := hq1_graph.1
    have hq2_1 : q2 1 ∈ Set.Icc (0 : ℝ) 1 := hq2_graph.1
    have hq1_0 : q1 0 = g.extension (q1 1) := hq1_graph.2
    have hq2_0 : q2 0 = g.extension (q2 1) := hq2_graph.2

    -- Same x-index implies |p1 1 - p2 1| < 1/N
    have hfloor_eq : ⌊p cell1 1 * (N : ℝ)⌋ = ⌊p cell2 1 * (N : ℝ)⌋ := hsame
    have h15 : |p cell1 1 * (N : ℝ) - p cell2 1 * (N : ℝ)| < 1 :=
      same_floor_close (p cell1 1 * (N : ℝ)) (p cell2 1 * (N : ℝ)) hfloor_eq
    have h17 : |p cell1 1 * (N : ℝ) - p cell2 1 * (N : ℝ)| = |p cell1 1 - p cell2 1| * (N : ℝ) := by
      have h171 : p cell1 1 * (N : ℝ) - p cell2 1 * (N : ℝ) = (p cell1 1 - p cell2 1) * (N : ℝ) := by ring
      rw [h171, abs_mul]
      <;> rw [abs_of_pos (show (0 : ℝ) < (N : ℝ) by exact_mod_cast hNpos)]
    have h16 : |p cell1 1 - p cell2 1| < (N : ℝ)⁻¹ := by
      rw [h17] at h15
      have h18 : |p cell1 1 - p cell2 1| * (N : ℝ) < 1 := h15
      have h19 : 0 < (N : ℝ) := by exact_mod_cast hNpos
      calc |p cell1 1 - p cell2 1|
        = (|p cell1 1 - p cell2 1| * (N : ℝ)) * (N : ℝ)⁻¹ := by field_simp [h19.ne'] <;> ring
        _ < 1 * (N : ℝ)⁻¹ := by gcongr
        _ = (N : ℝ)⁻¹ := by ring

    -- Coordinate distance bounds
    have h_c11 : |p cell1 1 - q1 1| ≤ dist (p cell1) q1 := euclidean_coord_dist (p cell1) q1 1
    have h_c21 : |p cell2 1 - q2 1| ≤ dist (p cell2) q2 := euclidean_coord_dist (p cell2) q2 1
    have h_c10 : |p cell1 0 - q1 0| ≤ dist (p cell1) q1 := euclidean_coord_dist (p cell1) q1 0
    have h_c20 : |p cell2 0 - q2 0| ≤ dist (p cell2) q2 := euclidean_coord_dist (p cell2) q2 0
    have h_sym11 : |q1 1 - p cell1 1| = |p cell1 1 - q1 1| := by rw [abs_sub_comm]
    have h_sym21 : |q2 1 - p cell2 1| = |p cell2 1 - q2 1| := by rw [abs_sub_comm]

    -- |q1 1 - q2 1| ≤ 1/N + 2*r
    have h_tri1 : |q1 1 - q2 1| ≤ |q1 1 - p cell1 1| + |p cell1 1 - q2 1| :=
      abs_sub_le (q1 1) (p cell1 1) (q2 1)
    have h_tri2 : |p cell1 1 - q2 1| ≤ |p cell1 1 - p cell2 1| + |p cell2 1 - q2 1| :=
      abs_sub_le (p cell1 1) (p cell2 1) (q2 1)
    have h20 : |q1 1 - q2 1| ≤ (N : ℝ)⁻¹ + 2 * r := by
      calc |q1 1 - q2 1|
        ≤ |q1 1 - p cell1 1| + |p cell1 1 - q2 1| := h_tri1
        _ ≤ |q1 1 - p cell1 1| + (|p cell1 1 - p cell2 1| + |p cell2 1 - q2 1|) := by gcongr
        _ = |p cell1 1 - q1 1| + |p cell1 1 - p cell2 1| + |p cell2 1 - q2 1| := by rw [h_sym11] <;> ring
        _ ≤ dist (p cell1) q1 + |p cell1 1 - p cell2 1| + dist (p cell2) q2 := by gcongr
        _ ≤ r + |p cell1 1 - p cell2 1| + r := by gcongr <;> linarith
        _ ≤ r + (N : ℝ)⁻¹ + r := by gcongr <;> linarith
        _ = (N : ℝ)⁻¹ + 2 * r := by ring

    -- Lipschitz bound
    have h_lip_dist : dist (g.extension (q1 1)) (g.extension (q2 1)) ≤ (slopeBlocks : ℝ) * dist (q1 1) (q2 1) :=
      hlip.dist_le_mul (q1 1) hq1_1 (q2 1) hq2_1
    have h_lip2 : |g.extension (q1 1) - g.extension (q2 1)| ≤ (slopeBlocks : ℝ) * |q1 1 - q2 1| := by
      simpa [Real.dist_eq] using h_lip_dist

    -- |p1 0 - p2 0| ≤ 2*r + slopeBlocks * (1/N + 2*r)
    have h_tri3 : |p cell1 0 - p cell2 0| ≤ |p cell1 0 - q1 0| + |q1 0 - p cell2 0| :=
      abs_sub_le (p cell1 0) (q1 0) (p cell2 0)
    have h_tri4 : |q1 0 - p cell2 0| ≤ |q1 0 - q2 0| + |q2 0 - p cell2 0| :=
      abs_sub_le (q1 0) (q2 0) (p cell2 0)
    have h_sym10 : |q1 0 - p cell1 0| = |p cell1 0 - q1 0| := by rw [abs_sub_comm]
    have h_slope_nonneg : 0 ≤ (slopeBlocks : ℝ) := by positivity
    have h_middle : |g.extension (q1 1) - g.extension (q2 1)| ≤ (slopeBlocks : ℝ) * |q1 1 - q2 1| := h_lip2
    have h_right : |q2 0 - p cell2 0| ≤ dist (p cell2) q2 := by
      rw [abs_sub_comm] <;> exact h_c20
    have h_step1 : |p cell1 0 - q1 0| + |g.extension (q1 1) - g.extension (q2 1)| + |q2 0 - p cell2 0| ≤
        dist (p cell1) q1 + (slopeBlocks : ℝ) * |q1 1 - q2 1| + dist (p cell2) q2 := by
      have h_a : |p cell1 0 - q1 0| ≤ dist (p cell1) q1 := h_c10
      linarith
    have h_middle2 : (slopeBlocks : ℝ) * |q1 1 - q2 1| ≤ (slopeBlocks : ℝ) * ((N : ℝ)⁻¹ + 2 * r) :=
      mul_le_mul_of_nonneg_left h20 h_slope_nonneg
    have h_step2 : dist (p cell1) q1 + (slopeBlocks : ℝ) * |q1 1 - q2 1| + dist (p cell2) q2 ≤
        r + (slopeBlocks : ℝ) * ((N : ℝ)⁻¹ + 2 * r) + r := by
      linarith [hdist1, hdist2, h_middle2]
    have h22 : |p cell1 0 - p cell2 0| ≤ 2 * r + (slopeBlocks : ℝ) * ((N : ℝ)⁻¹ + 2 * r) := by
      calc |p cell1 0 - p cell2 0|
        ≤ |p cell1 0 - q1 0| + |q1 0 - p cell2 0| := h_tri3
        _ ≤ |p cell1 0 - q1 0| + (|q1 0 - q2 0| + |q2 0 - p cell2 0|) := by gcongr
        _ = |p cell1 0 - q1 0| + |q1 0 - q2 0| + |q2 0 - p cell2 0| := by ring
        _ = |p cell1 0 - q1 0| + |g.extension (q1 1) - g.extension (q2 1)| + |q2 0 - p cell2 0| := by
          rw [hq1_0, hq2_0] <;> rfl
        _ ≤ dist (p cell1) q1 + (slopeBlocks : ℝ) * |q1 1 - q2 1| + dist (p cell2) q2 := h_step1
        _ ≤ r + (slopeBlocks : ℝ) * ((N : ℝ)⁻¹ + 2 * r) + r := h_step2
        _ = 2 * r + (slopeBlocks : ℝ) * ((N : ℝ)⁻¹ + 2 * r) := by ring

    -- Multiply by N
    have h24 : |p cell1 0 * (N : ℝ) - p cell2 0 * (N : ℝ)| = |p cell1 0 - p cell2 0| * (N : ℝ) := by
      have h241 : p cell1 0 * (N : ℝ) - p cell2 0 * (N : ℝ) = (p cell1 0 - p cell2 0) * (N : ℝ) := by ring
      rw [h241, abs_mul]
      <;> rw [abs_of_pos (show (0 : ℝ) < (N : ℝ) by exact_mod_cast hNpos)]
    have h23 : |p cell1 0 * (N : ℝ) - p cell2 0 * (N : ℝ)| ≤ (C : ℝ) := by
      rw [h24]
      calc |p cell1 0 - p cell2 0| * (N : ℝ)
        ≤ (2 * r + (slopeBlocks : ℝ) * ((N : ℝ)⁻¹ + 2 * r)) * (N : ℝ) := by gcongr
        _ = 2 * (r * (N : ℝ)) + (slopeBlocks : ℝ) * (1 + 2 * (r * (N : ℝ))) := by
          field_simp [hNpos.ne'] <;> ring
        _ ≤ 2 * (radiusBlocks : ℝ) + (slopeBlocks : ℝ) * (1 + 2 * (radiusBlocks : ℝ)) := by gcongr
        _ = (C : ℝ) := by simp [hC] <;> ring

    -- Floor difference bound
    have h25 : |(⌊p cell1 0 * (N : ℝ)⌋ : ℝ) - (⌊p cell2 0 * (N : ℝ)⌋ : ℝ)| ≤ (C : ℝ) + 1 :=
      floor_diff_bound h23
    have h26 : |(f cell1).2 - (f cell2).2| ≤ (C + 1 : ℤ) := by
      simpa [f] using by exact_mod_cast h25
    exact h26

  -- Step 5: Cardinality via fiber counting
  let I : Finset (ℤ × ℤ) := S.image f
  have hI_card : I.card = S.card := by
    rw [Finset.card_image_of_injOn h_inj]

  -- First projection image is subset of X
  have h_proj_subset : I.image Prod.fst ⊆ X := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨pair, hpair, rfl⟩
    rcases Finset.mem_image.mp hpair with ⟨cell, hcell, rfl⟩
    exact h_x_bound cell hcell

  have hM : (I.image Prod.fst).card ≤ X.card := Finset.card_le_card h_proj_subset

  -- Fiber bound
  have hK : ∀ (x : ℤ), (I.filter (fun p : ℤ × ℤ => p.1 = x)).card ≤ 2 * C + 7 := by
    intro x
    let fiber := I.filter (fun p : ℤ × ℤ => p.1 = x)
    by_cases h : fiber.Nonempty
    · rcases h with ⟨pair0, hpair0⟩
      rcases Finset.mem_image.mp (Finset.mem_filter.mp hpair0).1 with ⟨cell0, hcell0, rfl⟩
      let y0 := (f cell0).2
      have h_y_inj : Set.InjOn (fun p : ℤ × ℤ => p.2) fiber := by
        intro p1 hp1 p2 hp2 heq
        have h1 : p1.1 = x := (Finset.mem_filter.mp hp1).2
        have h2 : p2.1 = x := (Finset.mem_filter.mp hp2).2
        have h3 : p1 = p2 := by
          ext <;> simp [h1, h2, heq] <;> tauto
        exact h3
      let Y := Finset.Icc (y0 - (C + 1)) (y0 + (C + 1))
      have h_subset : fiber.image (fun p : ℤ × ℤ => p.2) ⊆ Y := by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨pair, hpair, rfl⟩
        rcases Finset.mem_image.mp (Finset.mem_filter.mp hpair).1 with ⟨cell, hcell, rfl⟩
        have hsame : (f cell).1 = (f cell0).1 := by
          have h1 : (f cell).1 = x := (Finset.mem_filter.mp hpair).2
          have h2 : (f cell0).1 = x := (Finset.mem_filter.mp hpair0).2
          simp [h1, h2]
        have h_spread : |(f cell).2 - y0| ≤ (C + 1 : ℤ) :=
          h_y_spread cell hcell cell0 hcell0 hsame
        have h_abs : -(C + 1 : ℤ) ≤ (f cell).2 - y0 := (abs_le.mp h_spread).1
        have h_abs2 : (f cell).2 - y0 ≤ (C + 1 : ℤ) := (abs_le.mp h_spread).2
        simp only [Y, Finset.mem_Icc]
        <;> constructor <;> linarith
      have h_card : fiber.card = (fiber.image (fun p : ℤ × ℤ => p.2)).card := by
        rw [Finset.card_image_of_injOn h_y_inj]
      rw [h_card]
      have h_le : (fiber.image (fun p : ℤ × ℤ => p.2)).card ≤ Y.card :=
        Finset.card_le_card h_subset
      have hY_card : Y.card = 2 * C + 3 := by
        simp [Y, Finset.Icc_eq_empty_of_lt] <;> omega
      rw [hY_card] at h_le
      have h_final : 2 * C + 3 ≤ 2 * C + 7 := by omega
      exact le_trans h_le h_final
    · have h_empty : fiber = ∅ := by
        simpa [Finset.not_nonempty_iff_eq_empty] using h
      have h_goal : (I.filter (fun p : ℤ × ℤ => p.1 = x)).card ≤ 2 * C + 7 := by
        have h_eq : (I.filter (fun p : ℤ × ℤ => p.1 = x)) = fiber := by rfl
        rw [h_eq, h_empty]
        <;> simp <;> omega
      exact h_goal

  have h_main : I.card ≤ X.card * (2 * C + 7) :=
    fiber_card_bound I X.card (2 * C + 7) hM hK

  rw [hI_card] at h_main
  rw [hX_card] at h_main
  have h_factor1 : N + 2 * radiusBlocks + 1 ≤ N + 2 * radiusBlocks + 3 := by omega
  have h_factor2 : 2 * C + 7 = 2 * (2 * radiusBlocks + slopeBlocks * (1 + 2 * radiusBlocks) + 2) + 3 := by
    simp [hC] <;> ring
  rw [h_factor2] at h_main
  have h_final : (N + 2 * radiusBlocks + 1) * (2 * (2 * radiusBlocks + slopeBlocks * (1 + 2 * radiusBlocks) + 2) + 3) ≤
      (N + 2 * radiusBlocks + 3) * (2 * (2 * radiusBlocks + slopeBlocks * (1 + 2 * radiusBlocks) + 2) + 3) := by
    exact Nat.mul_le_mul_right _ h_factor1
  exact h_main.trans h_final

end Kakeya.Assouad
