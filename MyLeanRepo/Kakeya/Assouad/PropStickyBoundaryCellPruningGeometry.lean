import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingStatements

/-!
# Geometric volume bound for boundary-cell pruning

When the literal `delta`- and `rho`-grids are not nested, whole `delta`-cells
that cross a `rho`-grid hyperplane lie in thin slabs around those hyperplanes.
Inside the cropped paper window `[-1,1]^3` the total volume of all such
crossing cells is `O(delta / rho)`.

The constant `1000` is deliberately generous; the actual bound proved here is
`120 * delta / rho`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Coordinate projection for a triple cell index. -/
def tripleCoord (cell : ℤ × ℤ × ℤ) : Fin 3 → ℤ :=
  ![cell.1, cell.2.1, cell.2.2]

lemma cellCorner_coord
    {scale : ℝ} {cell : ℤ × ℤ × ℤ} {c : Fin 3} :
    cellCorner scale cell c =
      (tripleCoord cell c : ℝ) * scale := by
  fin_cases c <;> simp [tripleCoord] <;> rfl

/--
Membership in a literal grid cube iff each coordinate lies in the
half-open interval `[i*scale, (i+1)*scale)`.
-/
lemma mem_gridCube_iff
    {scale : ℝ} (hscale : 0 < scale)
    {cell : ℤ × ℤ × ℤ} {p : Point3} :
    p ∈ wz1PaperGridCube scale cell ↔
      ∀ c : Fin 3,
        (tripleCoord cell c : ℝ) * scale ≤ p c ∧
          p c <
            ((tripleCoord cell c : ℝ) + 1) * scale := by
  have h_floor :
      ∀ c : Fin 3,
        ⌊p c / scale⌋ = tripleCoord cell c ↔
          (tripleCoord cell c : ℝ) * scale ≤ p c ∧
            p c <
              ((tripleCoord cell c : ℝ) + 1) * scale := by
    intro c
    have h :
        ⌊p c / scale⌋ = tripleCoord cell c ↔
          (tripleCoord cell c : ℝ) ≤ p c / scale ∧
            p c / scale <
              ((tripleCoord cell c : ℝ) + 1) :=
      Int.floor_eq_iff
    rw [h]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · calc
          (tripleCoord cell c : ℝ) * scale
              ≤ (p c / scale) * scale := by gcongr
          _ = p c := by field_simp [hscale.ne']
      · calc
          p c = (p c / scale) * scale := by
            field_simp [hscale.ne']
          _ < ((tripleCoord cell c : ℝ) + 1) * scale := by
            gcongr
    · rintro ⟨h1, h2⟩
      constructor
      · calc
          (tripleCoord cell c : ℝ) =
              (tripleCoord cell c : ℝ) * scale / scale := by
                field_simp [hscale.ne']
          _ ≤ p c / scale := by gcongr
      · calc
          p c / scale <
              (((tripleCoord cell c : ℝ) + 1) * scale) /
                scale := by
                  gcongr
          _ = (tripleCoord cell c : ℝ) + 1 := by
            field_simp [hscale.ne']
  have h_main :
      wz1PaperGridIndex scale p = cell ↔
        (⌊p 0 / scale⌋ = cell.1 ∧
          ⌊p 1 / scale⌋ = cell.2.1 ∧
          ⌊p 2 / scale⌋ = cell.2.2) := by
    simp [wz1PaperGridIndex, gridIndex, Prod.ext_iff]
  have h_triple :
      (⌊p 0 / scale⌋ = cell.1 ∧
          ⌊p 1 / scale⌋ = cell.2.1 ∧
          ⌊p 2 / scale⌋ = cell.2.2) ↔
        ∀ c : Fin 3,
          ⌊p c / scale⌋ = tripleCoord cell c := by
    constructor
    · rintro ⟨h0, h1, h2⟩
      intro c
      fin_cases c <;> simp [tripleCoord] at * <;> tauto
    · intro h
      have h0 : ⌊p 0 / scale⌋ = cell.1 := by
        have h' := h 0
        simpa [tripleCoord] using h'
      have h1 : ⌊p 1 / scale⌋ = cell.2.1 := by
        have h' := h 1
        simpa [tripleCoord] using h'
      have h2 : ⌊p 2 / scale⌋ = cell.2.2 := by
        have h' := h 2
        simpa [tripleCoord] using h'
      exact ⟨h0, h1, h2⟩
  rw [mem_wz1PaperGridCube, h_main, h_triple]
  constructor
  · intro h c
    exact (h_floor c).mp (h c)
  · intro h c
    exact (h_floor c).mpr (h c)

/-- The union of a paper shading is contained in the cropped window. -/
lemma shading_union_subset_axisBox
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine} :
    shading.union ⊆ Kakeya.Streamlined.axisBox 2 2 2 := by
  intro p hp
  rcases hp with ⟨i, hi⟩
  have h1 :
      p ∈ wz1PaperTubeCarrier (fine.tube i) :=
    shading.subset_body i hi
  exact h1.2

/-- Every active cell of a cubical shading lies in the cropped window. -/
lemma activeCell_subset_axisBox
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta : 0 < delta)
    {cell : ℤ × ℤ × ℤ}
    (hcell : cell ∈ wz1PaperActiveCells shading hdelta) :
    wz1PaperGridCube delta cell ⊆
      Kakeya.Streamlined.axisBox 2 2 2 := by
  exact wz1PaperActiveCell_subset_axisBox hcubical hdelta hcell

/-- Volume of one coordinate slab inside the cropped window. -/
lemma propSticky_boundary_cell_slab_volume_le
    {delta rho : ℝ} (hdelta : 0 < delta)
    (c : Fin 3) (m : ℤ) :
    volume
        ({p : Point3 |
            |p c - (m : ℝ) * rho| < delta} ∩
          Kakeya.Streamlined.axisBox 2 2 2) ≤
      ENNReal.ofReal (8 * delta) := by
  have h_set :
      ({p : Point3 |
          |p c - (m : ℝ) * rho| < delta} ∩
        Kakeya.Streamlined.axisBox 2 2 2) =
      {p : Point3 |
        p ∈ Kakeya.Streamlined.axisBox 2 2 2 ∧
          |p c - (m : ℝ) * rho| < delta} := by
    ext p
    simp [Set.mem_inter_iff]
    <;> tauto
  rw [h_set]
  exact
    boundary_slab_volume_le
      c ((m : ℝ) * rho) delta hdelta

/--
A crossing cell is contained in a coordinate slab around some `rho`-grid
hyperplane, and that hyperplane lies in the cropped coordinate window.
-/
lemma crossing_cell_slab
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    {cell : ℤ × ℤ × ℤ}
    (hcell : cell ∈ wz1PaperActiveCells shading hdelta)
    (hcross :
      ¬ (wz1PaperGridCube delta cell ⊆
        wz1PaperGridCube rho
          (wz1PaperGridIndex rho
            (cellCorner delta cell)))) :
    ∃ (c : Fin 3) (m : ℤ),
      (wz1PaperGridCube delta cell ⊆
        {p : Point3 |
            |p c - (m : ℝ) * rho| < delta} ∩
          Kakeya.Streamlined.axisBox 2 2 2) ∧
      |(m : ℝ) * rho| ≤ 1 := by
  let parent :=
    wz1PaperGridIndex rho (cellCorner delta cell)
  have hparent :
      ∀ c : Fin 3,
        tripleCoord parent c =
          ⌊(tripleCoord cell c : ℝ) * delta / rho⌋ := by
    intro c
    fin_cases c <;>
      simp [wz1PaperGridIndex, gridIndex, tripleCoord,
        cellCorner_coord] <;> rfl
  have h_floor1 :
      ∀ c : Fin 3,
        (tripleCoord parent c : ℝ) * rho ≤
          (tripleCoord cell c : ℝ) * delta := by
    intro c
    have h :
        (tripleCoord parent c : ℝ) ≤
          (tripleCoord cell c : ℝ) * delta / rho := by
      rw [hparent c]
      exact Int.floor_le _
    calc
      (tripleCoord parent c : ℝ) * rho
          ≤ ((tripleCoord cell c : ℝ) * delta / rho) *
              rho := by
                gcongr
      _ = (tripleCoord cell c : ℝ) * delta := by
        field_simp [hrho.ne'] <;> ring
  have h_floor2 :
      ∀ c : Fin 3,
        (tripleCoord cell c : ℝ) * delta <
          ((tripleCoord parent c : ℝ) + 1) * rho := by
    intro c
    have h :
        (tripleCoord cell c : ℝ) * delta / rho <
          (tripleCoord parent c : ℝ) + 1 := by
      rw [hparent c]
      exact Int.lt_floor_add_one _
    calc
      (tripleCoord cell c : ℝ) * delta =
          ((tripleCoord cell c : ℝ) * delta / rho) *
            rho := by
              field_simp [hrho.ne'] <;> ring
      _ < ((tripleCoord parent c : ℝ) + 1) * rho := by
        gcongr
  by_cases h :
      ∀ c : Fin 3,
        ((tripleCoord cell c : ℝ) + 1) * delta ≤
          ((tripleCoord parent c : ℝ) + 1) * rho
  · have h_contain :
        wz1PaperGridCube delta cell ⊆
          wz1PaperGridCube rho parent := by
      intro p hp
      have hpb := (mem_gridCube_iff hdelta).mp hp
      have hres :
          ∀ c : Fin 3,
            (tripleCoord parent c : ℝ) * rho ≤ p c ∧
              p c <
                ((tripleCoord parent c : ℝ) + 1) * rho := by
        intro c
        have h1 :
            (tripleCoord cell c : ℝ) * delta ≤ p c :=
          (hpb c).1
        have h2 :
            p c <
              ((tripleCoord cell c : ℝ) + 1) * delta :=
          (hpb c).2
        constructor
        · exact (h_floor1 c).trans h1
        · exact h2.trans_le (h c)
      exact (mem_gridCube_iff hrho).mpr hres
    exact False.elim (hcross h_contain)
  · push Not at h
    rcases h with ⟨c, hc⟩
    let m : ℤ := tripleCoord parent c + 1
    have h_bound1 :
        (tripleCoord cell c : ℝ) * delta <
          (m : ℝ) * rho := by
      simpa [m] using h_floor2 c
    have h_bound2 :
        (m : ℝ) * rho <
          ((tripleCoord cell c : ℝ) + 1) * delta := by
      simpa [m] using hc
    have h_in_box :
        wz1PaperGridCube delta cell ⊆
          Kakeya.Streamlined.axisBox 2 2 2 :=
      activeCell_subset_axisBox hcubical hdelta hcell
    have h_slab :
        ∀ p ∈ wz1PaperGridCube delta cell,
          |p c - (m : ℝ) * rho| < delta := by
      intro p hp
      have hpb := (mem_gridCube_iff hdelta).mp hp
      have h1 :
          (tripleCoord cell c : ℝ) * delta ≤ p c :=
        (hpb c).1
      have h2 :
          p c <
            ((tripleCoord cell c : ℝ) + 1) * delta :=
        (hpb c).2
      rw [abs_lt]
      constructor <;> linarith
    let q : Point3 :=
      WithLp.toLp 2
        (fun i =>
          if i = c then
            (m : ℝ) * rho
          else
            (tripleCoord cell i : ℝ) * delta)
    have hq_mem :
        q ∈ wz1PaperGridCube delta cell := by
      rw [mem_gridCube_iff hdelta]
      intro i
      have hqi :
          q i =
            if i = c then
              (m : ℝ) * rho
            else
              (tripleCoord cell i : ℝ) * delta := by
        simp [q] <;> rfl
      rw [hqi]
      by_cases hi : i = c
      · rw [if_pos hi, hi]
        exact ⟨le_of_lt h_bound1, h_bound2⟩
      · rw [if_neg hi]
        exact ⟨by linarith, by linarith⟩
    have hq_box :
        q ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
      h_in_box hq_mem
    have hqc : q c = (m : ℝ) * rho := by
      simp [q] <;> rfl
    have h_all :
        |q 0| ≤ 1 ∧ |q 1| ≤ 1 ∧ |q 2| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hq_box
    have h_qc_abs : |q c| ≤ 1 := by
      fin_cases c <;> tauto
    have h_m_bound : |(m : ℝ) * rho| ≤ 1 := by
      rw [← hqc]
      exact h_qc_abs
    refine ⟨c, m, ?_, h_m_bound⟩
    intro p hp
    exact ⟨h_slab p hp, h_in_box hp⟩

/-- Finite union volume bound. -/
private lemma finset_volume_biUnion_le
    {α : Type _} {s : Finset α} {f : α → Set Point3} :
    volume (⋃ i ∈ s, f i) ≤
      ∑ i ∈ s, volume (f i) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have h1 :
        (⋃ i ∈ insert a s, f i) =
          f a ∪ (⋃ i ∈ s, f i) := by
      ext x
      simp [Finset.mem_insert, ha]
      <;> tauto
    rw [h1, Finset.sum_insert ha]
    exact
      (measure_union_le _ _).trans
        (add_le_add_right ih (volume (f a)))

/--
Volume bound for the union of all crossing `delta`-cells.

The crossing cells are covered by coordinate slabs of width `2*delta` around
`rho`-grid hyperplanes inside `[-1,1]^3`. There are at most `3 * (5/rho)`
such slabs, each of volume at most `8*delta`.
-/
theorem wz2_boundary_cell_pruning_volume_bound
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta : 0 < delta) (hdelta_le_rho : delta ≤ rho)
    (hrho : 0 < rho) (hrho_le_one : rho ≤ 1)
    (crossingFineCells : Finset WZ2PaperCellIndex)
    (h_crossing_subset :
      crossingFineCells ⊆
        wz1PaperActiveCells shading hdelta)
    (h_crossing_def :
      ∀ cell ∈ crossingFineCells,
        ¬ (wz1PaperGridCube delta cell ⊆
          wz1PaperGridCube rho
            (wz1PaperGridIndex rho
              (cellCorner delta cell)))) :
    volume
        (⋃ cell ∈ crossingFineCells,
          wz1PaperGridCube delta cell) ≤
      ENNReal.ofReal (1000 * delta / rho) := by
  let bound : ℤ := ⌈1 / rho⌉
  let relevantM : Finset ℤ := Finset.Icc (-bound) bound
  let slabs : Finset (Fin 3 × ℤ) :=
    (Finset.univ : Finset (Fin 3)).product relevantM
  let slabSet : Fin 3 → ℤ → Set Point3 :=
    fun c m =>
      {p : Point3 |
          |p c - (m : ℝ) * rho| < delta} ∩
        Kakeya.Streamlined.axisBox 2 2 2
  have h_cover :
      ∀ cell ∈ crossingFineCells,
        ∃ cm : Fin 3 × ℤ,
          cm ∈ slabs ∧
            wz1PaperGridCube delta cell ⊆
              slabSet cm.1 cm.2 := by
    intro cell hcell
    have hcell_active :
        cell ∈ wz1PaperActiveCells shading hdelta :=
      h_crossing_subset hcell
    rcases
        crossing_cell_slab hcubical hdelta hrho
          hcell_active (h_crossing_def cell hcell) with
      ⟨c, m, hsub, hm_bound⟩
    have hm_relevant : m ∈ relevantM := by
      simp only [relevantM, Finset.mem_Icc]
      have h1 : |(m : ℝ) * rho| ≤ 1 := hm_bound
      have h21 :
          |(m : ℝ) * rho| = |(m : ℝ)| * rho := by
        rw [abs_mul, abs_of_pos hrho] <;> ring
      have h2 : |(m : ℝ)| ≤ 1 / rho := by
        have h' : |(m : ℝ)| ≤ 1 / rho := by
          calc
            |(m : ℝ)| =
                |(m : ℝ)| * rho / rho := by
                  field_simp [hrho.ne'] <;> ring
            _ ≤ 1 / rho := by
              gcongr
              rwa [← h21]
        exact h'
      have h2' :
          -(1 / rho) ≤ (m : ℝ) ∧
            (m : ℝ) ≤ 1 / rho :=
        abs_le.mp h2
      have h3 : -bound ≤ m := by
        have h41 : -(1 / rho) ≤ (m : ℝ) := h2'.1
        have h42 :
            -(bound : ℝ) ≤ -(1 / rho) := by
          have h43 :
              (bound : ℝ) ≥ 1 / rho :=
            Int.le_ceil (1 / rho)
          linarith
        have h44 : -(bound : ℝ) ≤ (m : ℝ) := by
          linarith
        exact_mod_cast h44
      have h4 : m ≤ bound := by
        have h51 : (m : ℝ) ≤ 1 / rho := h2'.2
        have h52 : (m : ℝ) ≤ (bound : ℝ) := by
          have h53 :
              1 / rho ≤ (bound : ℝ) :=
            Int.le_ceil (1 / rho)
          linarith
        exact_mod_cast h52
      exact ⟨h3, h4⟩
    refine ⟨(c, m), ?_, hsub⟩
    simpa [slabs, Finset.mem_product] using hm_relevant
  have h_union :
      (⋃ cell ∈ crossingFineCells,
          wz1PaperGridCube delta cell) ⊆
        ⋃ cm ∈ slabs, slabSet cm.1 cm.2 := by
    intro p hp
    rcases Set.mem_iUnion₂.mp hp with
      ⟨cell, hcell, hpcell⟩
    rcases h_cover cell hcell with
      ⟨cm, hcm, hsub⟩
    exact
      Set.mem_iUnion₂.mpr
        ⟨cm, hcm, hsub hpcell⟩
  have h_slab_vol :
      ∀ cm : Fin 3 × ℤ, cm ∈ slabs →
        volume (slabSet cm.1 cm.2) ≤
          ENNReal.ofReal (8 * delta) := by
    rintro ⟨c, m⟩ _
    exact propSticky_boundary_cell_slab_volume_le hdelta c m
  calc
    volume
        (⋃ cell ∈ crossingFineCells,
          wz1PaperGridCube delta cell)
        ≤ volume (⋃ cm ∈ slabs, slabSet cm.1 cm.2) :=
      measure_mono h_union
    _ ≤ ∑ cm ∈ slabs, volume (slabSet cm.1 cm.2) :=
      finset_volume_biUnion_le
    _ ≤ ∑ _cm ∈ slabs, ENNReal.ofReal (8 * delta) := by
      exact Finset.sum_le_sum fun cm hcm =>
        h_slab_vol cm hcm
    _ = (slabs.card : ENNReal) *
          ENNReal.ofReal (8 * delta) := by
      simp [Finset.sum_const]
      <;> ring
    _ ≤ ENNReal.ofReal (1000 * delta / rho) := by
      have h_bound_nonneg : 0 ≤ bound := by
        by_cases h : 0 ≤ bound
        · exact h
        · have h' : bound < 0 := by omega
          have h'' : (bound : ℝ) < 0 := by
            exact_mod_cast h'
          have h_pos : (0 : ℝ) < 1 / rho := by
            positivity
          have h3 : (bound : ℝ) ≥ 1 / rho :=
            Int.le_ceil (1 / rho)
          linarith
      let b : ℕ := bound.natAbs
      have hb : (b : ℤ) = bound := by
        simp [b, Int.natAbs_of_nonneg h_bound_nonneg]
        <;> omega
      have h_card1 :
          slabs.card = 3 * relevantM.card := by
        simp [slabs, Finset.card_product]
        <;> decide
      have h_card2 :
          (relevantM.card : ℝ) =
            2 * (bound : ℝ) + 1 := by
        have h_def :
            relevantM = Finset.Icc (-bound) bound := by
          rfl
        rw [h_def]
        have h2 :
            (Finset.Icc (-bound) bound).card =
              2 * b + 1 := by
          rw [
            show (-bound) = -(b : ℤ) by rw [hb],
            show bound = (b : ℤ) from hb.symm]
          simp [Int.toNat_of_nonneg]
          <;> omega
        rw [h2]
        simp [hb]
        <;> norm_cast <;> ring
      have h_bound_le :
          (bound : ℝ) ≤ 1 / rho + 1 := by
        have h_lt :
            (bound : ℝ) < 1 / rho + 1 :=
          Int.ceil_lt_add_one (1 / rho)
        linarith
      have h_one_le_rho_inv :
          (1 : ℝ) ≤ 1 / rho := by
        have h : 1 / rho ≥ 1 / 1 := by
          gcongr
        simpa using h
      have h5 :
          (relevantM.card : ℝ) ≤ 5 / rho := by
        rw [h_card2]
        have h51 :
            2 * (bound : ℝ) + 1 ≤
              2 / rho + 3 := by
          calc
            2 * (bound : ℝ) + 1
                ≤ 2 * (1 / rho + 1) + 1 := by
                  gcongr
            _ = 2 / rho + 3 := by ring
        have h52 : 2 / rho + 3 ≤ 5 / rho := by
          have h53 : (3 : ℝ) ≤ 3 / rho := by
            calc
              (3 : ℝ) = 3 * 1 := by ring
              _ ≤ 3 * (1 / rho) := by gcongr
              _ = 3 / rho := by ring
          have h :
              2 / rho + 3 ≤ 2 / rho + 3 / rho := by
            gcongr
          have h2 : 2 / rho + 3 / rho = 5 / rho := by
            ring
          linarith
        linarith
      have h6 : (slabs.card : ℝ) ≤ 15 / rho := by
        rw [h_card1]
        have h61 :
            (3 : ℝ) * (relevantM.card : ℝ) ≤
              3 * (5 / rho) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
        have h62 : (3 : ℝ) * (5 / rho) = 15 / rho := by
          ring
        rw [h62] at h61
        have h63 :
            ((3 * relevantM.card : ℕ) : ℝ) =
              (3 : ℝ) * (relevantM.card : ℝ) := by
          simp [Nat.cast_mul]
          <;> ring
        rw [h63]
        exact h61
      have h7 :
          (slabs.card : ℝ) * (8 * delta) ≤
            1000 * delta / rho := by
        calc
          (slabs.card : ℝ) * (8 * delta)
              ≤ (15 / rho) * (8 * delta) := by
                gcongr
          _ = 120 * delta / rho := by ring
          _ ≤ 1000 * delta / rho := by
            gcongr <;> norm_num
      have h14 :
          (slabs.card : ENNReal) *
              ENNReal.ofReal (8 * delta) =
            ENNReal.ofReal
              ((slabs.card : ℝ) * (8 * delta)) := by
        rw [show (slabs.card : ENNReal) =
            ENNReal.ofReal (slabs.card : ℝ) by simp]
        exact
          (ENNReal.ofReal_mul
            (by positivity :
              0 ≤ (slabs.card : ℝ))).symm
      rw [h14]
      exact ENNReal.ofReal_le_ofReal h7

end Kakeya.Assouad
