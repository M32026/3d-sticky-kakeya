import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCellThickeningStatement

/-!
# Thickening one occupied projected-fiber grid cell

Grid-index equalities and the terminal/coarse mesh comparisons place one
retained cell band and its `rho`-thickening in explicit planar balls.
-/

namespace Kakeya.Assouad

lemma planarGridIndex_same_coord_bound
    {base level : ℕ} (hbase : 0 < base)
    {p q : Point2}
    (h : planarGridIndex base level p = planarGridIndex base level q) :
    ∀ i : Fin 2, |p i - q i| < (base ^ level : ℝ)⁻¹ := by
  set B : ℝ := (base ^ level : ℝ) with hB
  have hBpos : 0 < B := by positivity
  have h_pair :
      ⌊p 0 * B⌋ = ⌊q 0 * B⌋ ∧
        ⌊p 1 * B⌋ = ⌊q 1 * B⌋ := by
    simpa [planarGridIndex, Prod.ext_iff] using h
  intro i
  have hi : ⌊p i * B⌋ = ⌊q i * B⌋ := by
    fin_cases i <;> tauto
  set n : ℤ := ⌊p i * B⌋ with hn
  have h2 : (n : ℝ) ≤ p i * B := Int.floor_le (p i * B)
  have h3 : p i * B < (n : ℝ) + 1 :=
    Int.lt_floor_add_one (p i * B)
  have hq_floor : ⌊q i * B⌋ = n := Eq.symm hi
  have h41 : (⌊q i * B⌋ : ℝ) ≤ q i * B :=
    Int.floor_le (q i * B)
  have h4 : (n : ℝ) ≤ q i * B := by
    rw [hq_floor] at h41
    exact h41
  have h51 : q i * B < (⌊q i * B⌋ : ℝ) + 1 :=
    Int.lt_floor_add_one (q i * B)
  have h5 : q i * B < (n : ℝ) + 1 := by
    rw [hq_floor] at h51
    exact h51
  have h6 : |p i * B - q i * B| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have h7 : |p i - q i| * B < 1 := by
    have h8 : p i * B - q i * B = (p i - q i) * B := by
      ring
    rw [h8] at h6
    have h9 :
        |(p i - q i) * B| = |p i - q i| * B := by
      rw [abs_mul, abs_of_nonneg (show 0 ≤ B by linarith)]
    rw [h9] at h6
    exact h6
  have h10 : |p i - q i| < 1 / B := by
    calc
      |p i - q i| = (|p i - q i| * B) / B := by
        field_simp [hBpos.ne']
      _ < 1 / B := by gcongr
  have h11 : (1 / B : ℝ) = B⁻¹ := by simp
  rw [h11] at h10
  exact h10

lemma dist_lt_two_of_coord_lt
    {p q : Point2} {d : ℝ}
    (h : ∀ i : Fin 2, |p i - q i| < d) :
    dist p q < 2 * d := by
  have hdpos : 0 < d := by
    have h0 : 0 ≤ |p 0 - q 0| := abs_nonneg _
    have h1 : |p 0 - q 0| < d := h 0
    linarith
  let x := p - q
  have hx0 : |x 0| < d := by simpa [x] using h 0
  have hx1 : |x 1| < d := by simpa [x] using h 1
  have h_norm_sq : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two]
  have h_abs_sq0 : (x 0) ^ 2 = |x 0| ^ 2 := by
    rw [sq_abs]
  have h_abs_sq1 : (x 1) ^ 2 = |x 1| ^ 2 := by
    rw [sq_abs]
  have h_pos : 0 ≤ |x 0| * |x 1| := by positivity
  have h_sq_le :
      (x 0) ^ 2 + (x 1) ^ 2 ≤ (|x 0| + |x 1|) ^ 2 := by
    rw [h_abs_sq0, h_abs_sq1]
    have h :
        |x 0| ^ 2 + |x 1| ^ 2 +
            2 * (|x 0| * |x 1|) =
          (|x 0| + |x 1|) ^ 2 := by
      ring
    have h2 :
        |x 0| ^ 2 + |x 1| ^ 2 ≤
          |x 0| ^ 2 + |x 1| ^ 2 +
            2 * (|x 0| * |x 1|) := by
      linarith [h_pos]
    rw [h] at h2
    exact h2
  have h1 : ‖x‖ ^ 2 ≤ (|x 0| + |x 1|) ^ 2 := by
    rw [h_norm_sq]
    exact h_sq_le
  have h2 : 0 ≤ ‖x‖ := by positivity
  have h3 : 0 ≤ |x 0| + |x 1| := by positivity
  have h_main : ‖x‖ ≤ |x 0| + |x 1| := by
    nlinarith
  have h4 : dist p q = ‖x‖ := by
    simp [x, dist_eq_norm]
  rw [h4]
  have h5 : ‖x‖ ≤ |x 0| + |x 1| := h_main
  have h6 : |x 0| + |x 1| < 2 * d := by linarith
  exact lt_of_le_of_lt h5 h6

lemma dist_mesh_combination
    {base levels level : ℕ} {q c center : Point2} {rho : ℝ}
    (_hbase : 3 ≤ base) (_hrho : 0 < rho)
    (h1 : dist q c < 2 * (base ^ levels : ℝ)⁻¹)
    (h2 : dist c center < 2 * (base ^ level : ℝ)⁻¹)
    (h_rho1 : (base ^ level : ℝ)⁻¹ ≤ rho)
    (h_rho2 :
      (base ^ levels : ℝ)⁻¹ < (base : ℝ) * rho) :
    dist q center < ((2 * base + 2 : ℕ) : ℝ) * rho := by
  have h_tri : dist q center ≤ dist q c + dist c center :=
    dist_triangle q c center
  have h_term :
      2 * (base ^ levels : ℝ)⁻¹ <
        2 * (base : ℝ) * rho := by
    have h :
        (base ^ levels : ℝ)⁻¹ < (base : ℝ) * rho :=
      h_rho2
    linarith
  have h_coarse :
      2 * (base ^ level : ℝ)⁻¹ ≤ 2 * rho := by
    have h : (base ^ level : ℝ)⁻¹ ≤ rho := h_rho1
    linarith
  have h_sum :
      dist q c + dist c center <
        2 * (base : ℝ) * rho + 2 * rho := by
    linarith
  have h_final :
      dist q center <
        2 * (base : ℝ) * rho + 2 * rho := by
    calc
      dist q center ≤ dist q c + dist c center := h_tri
      _ < 2 * (base : ℝ) * rho + 2 * rho := h_sum
  have h_eq :
      2 * (base : ℝ) * rho + 2 * rho =
        ((2 * base + 2 : ℕ) : ℝ) * rho := by
    simp [Nat.cast_add, Nat.cast_mul]
    ring
  rw [h_eq] at h_final
  exact h_final

theorem projected_fiber_os_cell_thickening :
    ProjectedFiberOSCellThickeningStatement := by
  intro delta F Y f threshold levelCount bandData base levels
    indexBound hbase atomized uniform level hlevel rho hrho
    hmesh_coarse hmesh_fine cell hcell hoccupied
  rcases hoccupied with ⟨center, hcenter⟩
  have hcenter' := Finset.mem_inter.mp hcenter
  have hcenter_in_centers : center ∈ uniform.centers :=
    hcenter'.1
  have hcenter_in_cell : center ∈ cell := hcenter'.2
  have hbase_pos : 0 < base := by linarith
  refine' ⟨center, hcenter, _⟩
  have h_cell_form :
      ∃ (p : Point2), p ∈ atomized.centers ∧
        planarGridCell base level atomized.centers p = cell := by
    have h :
        cell ∈
          atomized.centers.image
            (planarGridCell base level atomized.centers) := by
      simpa [planarGridPartition] using hcell
    rcases Finset.mem_image.mp h with ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩
  rcases h_cell_form with ⟨p, _hp, hcell_eq⟩
  have h_main1 :
      projectedFiberOSCellBand
          Y f bandData base levels uniform.centers cell ⊆
        Metric.closedBall center
          (((2 * base + 2 : ℕ) : ℝ) * rho) := by
    intro q hq
    have hq' :
        q ∈ finiteAtomUnion (uniform.centers ∩ cell)
          (projectedFiberGridAtom bandData.band base levels) := by
      simpa [projectedFiberOSCellBand] using hq
    rcases Set.mem_iUnion₂.mp hq' with ⟨c, hc, hqc⟩
    have hc' := Finset.mem_inter.mp hc
    have hc_in_cell : c ∈ cell := hc'.2
    have h_atom :
        q ∈ projectedFiberGridAtom
          bandData.band base levels c :=
      hqc
    have h_same_terminal :
        planarGridIndex base levels q =
          planarGridIndex base levels c := by
      simpa [projectedFiberGridAtom, Set.mem_inter_iff,
        Set.mem_setOf_eq] using h_atom.2
    have h_c_index :
        planarGridIndex base level c =
          planarGridIndex base level p := by
      have h_in :
          c ∈ planarGridCell base level atomized.centers p := by
        rw [hcell_eq]
        exact hc_in_cell
      exact (Finset.mem_filter.mp h_in).2
    have h_center_index :
        planarGridIndex base level center =
          planarGridIndex base level p := by
      have h_in :
          center ∈ planarGridCell base level atomized.centers p := by
        rw [hcell_eq]
        exact hcenter_in_cell
      exact (Finset.mem_filter.mp h_in).2
    have h_same_coarse :
        planarGridIndex base level c =
          planarGridIndex base level center := by
      rw [h_c_index, h_center_index]
    have h_coord_terminal :
        ∀ i : Fin 2,
          |q i - c i| < (base ^ levels : ℝ)⁻¹ :=
      planarGridIndex_same_coord_bound
        hbase_pos h_same_terminal
    have h_dist_terminal :
        dist q c < 2 * (base ^ levels : ℝ)⁻¹ :=
      dist_lt_two_of_coord_lt h_coord_terminal
    have h_coord_coarse :
        ∀ i : Fin 2,
          |c i - center i| < (base ^ level : ℝ)⁻¹ :=
      planarGridIndex_same_coord_bound hbase_pos h_same_coarse
    have h_dist_coarse :
        dist c center < 2 * (base ^ level : ℝ)⁻¹ :=
      dist_lt_two_of_coord_lt h_coord_coarse
    have h_final :
        dist q center <
          ((2 * base + 2 : ℕ) : ℝ) * rho :=
      dist_mesh_combination hbase hrho h_dist_terminal
        h_dist_coarse hmesh_coarse hmesh_fine
    exact h_final.le
  have h_main2 :
      MeasureTheory.volume
          (Metric.cthickening rho
            (projectedFiberOSCellBand
              Y f bandData base levels uniform.centers cell)) ≤
        ENNReal.ofReal
          ((((2 * base + 3 : ℕ) : ℝ) * rho) ^ 2 *
            Real.pi) := by
    have hthick :
        Metric.cthickening rho
            (projectedFiberOSCellBand
              Y f bandData base levels uniform.centers cell) ⊆
          Metric.closedBall center
            (((2 * base + 3 : ℕ) : ℝ) * rho) := by
      have hsub :
          Metric.cthickening rho
              (projectedFiberOSCellBand
                Y f bandData base levels uniform.centers cell) ⊆
            Metric.cthickening rho
              (Metric.closedBall center
                (((2 * base + 2 : ℕ) : ℝ) * rho)) :=
        Metric.cthickening_subset_of_subset rho h_main1
      have heq :
          Metric.cthickening rho
              (Metric.closedBall center
                (((2 * base + 2 : ℕ) : ℝ) * rho)) =
            Metric.closedBall center
              (rho + (((2 * base + 2 : ℕ) : ℝ) * rho)) :=
        cthickening_closedBall (by positivity) (by positivity) center
      rw [heq] at hsub
      have hsum :
          rho + (((2 * base + 2 : ℕ) : ℝ) * rho) =
            (((2 * base + 3 : ℕ) : ℝ) * rho) := by
        have h :
            ((2 * base + 2 : ℕ) : ℝ) + 1 =
              ((2 * base + 3 : ℕ) : ℝ) := by
          norm_cast
        have h' :
            1 + ((2 * base + 2 : ℕ) : ℝ) =
              ((2 * base + 3 : ℕ) : ℝ) := by
          linarith
        calc
          rho + (((2 * base + 2 : ℕ) : ℝ) * rho) =
              (1 + ((2 * base + 2 : ℕ) : ℝ)) * rho := by
                ring
          _ = (((2 * base + 3 : ℕ) : ℝ) * rho) := by
            rw [h']
      rw [hsum] at hsub
      exact hsub
    have hvol :
        MeasureTheory.volume
            (Metric.closedBall center
              (((2 * base + 3 : ℕ) : ℝ) * rho)) =
          ENNReal.ofReal
            ((((2 * base + 3 : ℕ) : ℝ) * rho) ^ 2 *
              Real.pi) := by
      have h :=
        EuclideanSpace.volume_closedBall_fin_two center
          (((2 * base + 3 : ℕ) : ℝ) * rho)
      rw [h]
      have hpos :
          0 ≤ (((2 * base + 3 : ℕ) : ℝ) * rho) := by
        positivity
      have h5 :
          ENNReal.ofReal
                (((2 * base + 3 : ℕ) : ℝ) * rho) ^ 2 *
              ENNReal.ofReal Real.pi =
            ENNReal.ofReal
              ((((2 * base + 3 : ℕ) : ℝ) * rho) ^ 2 *
                Real.pi) := by
        have h6 :
            ENNReal.ofReal
                  (((2 * base + 3 : ℕ) : ℝ) * rho) ^ 2 =
                ENNReal.ofReal
                  ((((2 * base + 3 : ℕ) : ℝ) * rho) ^ 2) := by
          rw [← ENNReal.ofReal_pow hpos]
        rw [h6]
        rw [← ENNReal.ofReal_mul (by positivity)]
      exact h5
    calc
      MeasureTheory.volume (Metric.cthickening rho _)
          ≤ MeasureTheory.volume
              (Metric.closedBall center
                (((2 * base + 3 : ℕ) : ℝ) * rho)) :=
        MeasureTheory.measure_mono hthick
      _ = ENNReal.ofReal
            ((((2 * base + 3 : ℕ) : ℝ) * rho) ^ 2 *
              Real.pi) :=
        hvol
  exact ⟨h_main1, h_main2⟩

end Kakeya.Assouad
