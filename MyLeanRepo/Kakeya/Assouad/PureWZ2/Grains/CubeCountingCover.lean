import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SlabCubeCounting
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalSlabLower

/-!
# Cube counting cover for local AD

Elementary covering-number bound via grid-cube counting.

## Main results

1. `count_cubes_slab_ball`: N_cubes ≤ 1000 * (length + L) * (R + L)^2 / L^3
2. `projection_covering_from_cubes`: covering ≤ N when ρ' ≥ L√3
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Finset
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- If a cube intersects ball(q,R), it is contained in ball(q, R+L√3). -/
lemma cube_intersects_ball_contained
    {L : ℝ} (hL_pos : 0 < L)
    {cell : ℤ × ℤ × ℤ} {q : Point3} {R : ℝ} (hR_nonneg : 0 ≤ R)
    (h_nonempty : (wz1PaperGridCube L cell ∩ Metric.closedBall q R).Nonempty) :
    wz1PaperGridCube L cell ⊆ Metric.closedBall q (R + L * Real.sqrt 3) := by
  rcases h_nonempty with ⟨y, hy_cube, hy_ball⟩
  intro x hx
  have h1 : dist x y ≤ L * Real.sqrt 3 := wz1PaperGridCube_diameter hL_pos cell hx hy_cube
  have h2 : dist y q ≤ R := by simpa [Metric.mem_closedBall] using hy_ball
  have h3 : dist x q ≤ dist x y + dist y q := dist_triangle x y q
  have h4 : dist x q ≤ R + L * Real.sqrt 3 := by linarith
  simpa [Metric.mem_closedBall] using h4

/-- If a cube's projection onto v intersects [a,a+length], the cube is
contained in a slab of half-width length/2 + L√3 around (a+length/2)•v. -/
lemma cube_projection_slab_contained
    {L : ℝ} (hL_pos : 0 < L)
    {cell : ℤ × ℤ × ℤ} {v : Point3} (hv_unit : ‖v‖ = 1)
    {a length : ℝ} (hlen_nonneg : 0 ≤ length)
    (h_nonempty : (scalarProjection v (wz1PaperGridCube L cell) ∩ Set.Icc a (a + length)).Nonempty) :
    wz1PaperGridCube L cell ⊆
      {x : Point3 | |inner ℝ (x - ((a + length / 2) • v)) v| ≤ length / 2 + L * Real.sqrt 3} := by
  rcases h_nonempty with ⟨t, ⟨y, hy_cube, rfl⟩, ht_Icc⟩
  have h_t_in : a ≤ inner ℝ y v ∧ inner ℝ y v ≤ a + length := ht_Icc
  intro x hx
  have h1 : dist x y ≤ L * Real.sqrt 3 := wz1PaperGridCube_diameter hL_pos cell hx hy_cube
  have h2 : |inner ℝ (x - y) v| ≤ ‖x - y‖ * ‖v‖ := abs_real_inner_le_norm _ _
  have h3 : ‖x - y‖ ≤ L * Real.sqrt 3 := by simpa [dist_eq_norm] using h1
  have h2' : |inner ℝ (x - y) v| ≤ L * Real.sqrt 3 := by
    rw [hv_unit] at h2
    have h : ‖x - y‖ * (1 : ℝ) ≤ L * Real.sqrt 3 := by
      simpa using h3
    exact h2.trans h
  have h4 : |inner ℝ x v - inner ℝ y v| ≤ L * Real.sqrt 3 := by
    have h5 : inner ℝ x v - inner ℝ y v = inner ℝ (x - y) v := by
      rw [inner_sub_left] <;> ring
    rw [h5]
    exact h2'
  have h6 : |inner ℝ x v - (a + length / 2)| ≤ length / 2 + L * Real.sqrt 3 := by
    rw [abs_le] at h4 ⊢
    constructor <;> linarith [h_t_in.1, h_t_in.2]
  have h8 : inner ℝ (x - ((a + length / 2) • v)) v =
      inner ℝ x v - inner ℝ (((a + length / 2) • v)) v := by
    exact inner_sub_left x ((a + length / 2) • v) v
  have h9 : inner ℝ (((a + length / 2) • v)) v = (a + length / 2) := by
    have h10 : inner ℝ (((a + length / 2) • v)) v = (a + length / 2) * inner ℝ v v := by
      exact inner_smul_left _ _ _
    have h11 : inner ℝ v v = 1 := by
      have h12 : inner ℝ v v = ‖v‖^2 := real_inner_self_eq_norm_sq v
      rw [h12, hv_unit] <;> norm_num
    rw [h10, h11] <;> ring
  have h7 : inner ℝ (x - ((a + length / 2) • v)) v = inner ℝ x v - (a + length / 2) := by
    rw [h8, h9]
  have h_goal : |inner ℝ (x - ((a + length / 2) • v)) v| ≤ length / 2 + L * Real.sqrt 3 := by
    rw [h7]
    exact h6
  simpa only [Set.mem_setOf_eq] using h_goal

/-- Slab-ball volume bound with arbitrary ball center. -/
lemma slab_ball_volume_any_center
    {v : Point3} (hv_unit : ‖v‖ = 1)
    {q slab_center : Point3} {w R : ℝ} (hw_nonneg : 0 ≤ w) (hR_pos : 0 < R) :
    volume ({x : Point3 | |inner ℝ (x - slab_center) v| ≤ w} ∩ Metric.closedBall q R) ≤
      ENNReal.ofReal (8 * w * R^2) := by
  let S := {x : Point3 | |inner ℝ (x - slab_center) v| ≤ w} ∩ Metric.closedBall q R
  let S' := {y : Point3 | |inner ℝ (y - (slab_center - q)) v| ≤ w} ∩ Metric.closedBall 0 R
  have h_eq : S = (fun x : Point3 => x + q) '' S' := by
    ext x
    simp only [S, S', Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨x - q, ?_, by simp⟩
      constructor
      · have h : inner ℝ ((x - q) - (slab_center - q)) v = inner ℝ (x - slab_center) v := by
          simp [inner_sub_left] <;> ring
        rw [h]; exact h1
      · simpa [Metric.mem_closedBall, dist_eq_norm] using h2
    · rintro ⟨y, hy, rfl⟩
      constructor
      · have h : inner ℝ ((y + q) - slab_center) v = inner ℝ (y - (slab_center - q)) v := by
          have h' : (y + q) - slab_center = y - (slab_center - q) := by
            ext i <;> simp <;> ring
          rw [h']
        rw [h]; exact hy.1
      · simpa [Metric.mem_closedBall, dist_eq_norm] using hy.2
  have h_mp : MeasurePreserving (fun x : Point3 => x + q) volume volume :=
    measurePreserving_add_right volume q
  have h_vol : volume S = volume S' := by
    rw [h_eq]
    let g : Point3 → Point3 := fun x => x - q
    have hg_mp : MeasurePreserving g volume volume := measurePreserving_add_right volume (-q)
    have h_image_eq_preimage : (fun x : Point3 => x + q) '' S' = g ⁻¹' S' := by
      ext z
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [g] using hy
      · intro hz
        refine ⟨z - q, hz, ?_⟩
        ext i <;> simp <;> ring
    rw [h_image_eq_preimage]
    exact hg_mp.measure_preimage (show NullMeasurableSet S' volume from by
      have h1 : MeasurableSet S' := by
        have h2 : MeasurableSet {y : Point3 | |inner ℝ (y - (slab_center - q)) v| ≤ w} := by
          have h1 : Continuous (fun y : Point3 => inner ℝ (y - (slab_center - q)) v) := by
            fun_prop
          have h_cont : Continuous (fun y : Point3 => |inner ℝ (y - (slab_center - q)) v|) :=
            continuous_abs.comp h1
          have h_closed : IsClosed (Set.Iic w) := isClosed_Iic
          exact (h_closed.preimage h_cont).measurableSet
        have h3 : MeasurableSet (Metric.closedBall (0 : Point3) R) :=
          Metric.isClosed_closedBall.measurableSet
        exact h2.inter h3
      exact h1.nullMeasurableSet)
  rw [h_vol]
  exact PureWZ2.slab_ball_volume hv_unit hw_nonneg hR_pos

/-- Main cube counting bound.

Number of cells whose cube intersects ball(q,R) AND whose projection
onto v intersects [a,a+length] is at most 1000*(length+L)*(R+L)^2/L^3. -/
lemma count_cubes_slab_ball
    {L : ℝ} (hL_pos : 0 < L) (hL_le_one : L ≤ 1)
    (v : Point3) (hv_unit : ‖v‖ = 1)
    (q : Point3) (R : ℝ) (hR_pos : 0 < R)
    (a length : ℝ) (hlen_pos : 0 < length)
    (cells : Finset (ℤ × ℤ × ℤ)) :
    let relevant := cells.filter fun cell =>
      (wz1PaperGridCube L cell ∩ Metric.closedBall q R).Nonempty ∧
      (scalarProjection v (wz1PaperGridCube L cell) ∩ Set.Icc a (a + length)).Nonempty
    (relevant.card : ENNReal) ≤
      ENNReal.ofReal (1000 * (length + L) * (R + L)^2 / L^3) := by
  let relevant := cells.filter fun cell =>
      (wz1PaperGridCube L cell ∩ Metric.closedBall q R).Nonempty ∧
      (scalarProjection v (wz1PaperGridCube L cell) ∩ Set.Icc a (a + length)).Nonempty
  let w : ℝ := length / 2 + L * Real.sqrt 3
  let R' : ℝ := R + L * Real.sqrt 3
  let slab_center : Point3 := (a + length / 2) • v
  let E : Set Point3 :=
    {x : Point3 | |inner ℝ (x - slab_center) v| ≤ w} ∩ Metric.closedBall q R'
  have hE_meas : MeasurableSet E := by
    have h1 : Continuous (fun x : Point3 => inner ℝ (x - slab_center) v) := by fun_prop
    have h2 : MeasurableSet {x : Point3 | |inner ℝ (x - slab_center) v| ≤ w} := by
      have h_cont : Continuous (fun x : Point3 => |inner ℝ (x - slab_center) v|) :=
        continuous_abs.comp h1
      have h_closed : IsClosed (Set.Iic w : Set ℝ) := isClosed_Iic
      exact (h_closed.preimage h_cont).measurableSet
    have h3 : MeasurableSet (Metric.closedBall q R') := by
      have h : IsClosed (Metric.closedBall q R') := Metric.isClosed_closedBall
      exact h.measurableSet
    exact MeasurableSet.inter h2 h3
  have h_contained : ∀ cell ∈ relevant, wz1PaperGridCube L cell ⊆ E := by
    intro cell hcell
    have h1 := (Finset.mem_filter.mp hcell).2
    have hball : (wz1PaperGridCube L cell ∩ Metric.closedBall q R).Nonempty := h1.1
    have hproj : (scalarProjection v (wz1PaperGridCube L cell) ∩ Set.Icc a (a + length)).Nonempty := h1.2
    have h2 : wz1PaperGridCube L cell ⊆ Metric.closedBall q R' :=
      cube_intersects_ball_contained hL_pos hR_pos.le hball
    have h3 : wz1PaperGridCube L cell ⊆ {x | |inner ℝ (x - slab_center) v| ≤ w} :=
      cube_projection_slab_contained hL_pos hv_unit hlen_pos.le hproj
    intro x hx
    exact ⟨h3 hx, h2 hx⟩
  have h_count : (relevant.card : ENNReal) * ENNReal.ofReal (L^3) ≤ volume E :=
    PureWZ2.grid_cubes_contained_count hL_pos hE_meas h_contained
  have h_volume : volume E ≤ ENNReal.ofReal (8 * w * R'^2) :=
    slab_ball_volume_any_center hv_unit (by positivity) (by positivity)
  have h_pos3 : 0 < L^3 := by positivity
  have h_arith : 8 * w * R'^2 ≤ 1000 * (length + L) * (R + L)^2 := by
    dsimp only [w, R']
    have hsqrt3 : Real.sqrt 3 < 2 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h1 : length / 2 + L * Real.sqrt 3 ≤ 2 * (length + L) := by
      have h2 : 0 ≤ length := by linarith
      have h3 : 0 ≤ L := by linarith
      nlinarith
    have h2 : R + L * Real.sqrt 3 ≤ 2 * (R + L) := by
      have h3 : 0 ≤ R := by linarith
      have h4 : 0 ≤ L := by linarith
      nlinarith
    calc
      8 * (length / 2 + L * Real.sqrt 3) * (R + L * Real.sqrt 3)^2
        ≤ 8 * (2 * (length + L)) * (2 * (R + L))^2 := by gcongr
      _ = 64 * (length + L) * (R + L)^2 := by ring
      _ ≤ 1000 * (length + L) * (R + L)^2 := by
        have h3 : 0 ≤ (length + L) * (R + L)^2 := by positivity
        gcongr <;> norm_num
  have h4 : (relevant.card : ENNReal) * ENNReal.ofReal (L^3) ≤
      ENNReal.ofReal (1000 * (length + L) * (R + L)^2) :=
    h_count.trans (h_volume.trans (ENNReal.ofReal_le_ofReal h_arith))
  have h5 : ENNReal.ofReal (L^3) ≠ 0 := by
    have h : 0 < L^3 := h_pos3
    have h' : ENNReal.ofReal (L^3) = 0 ↔ L^3 ≤ 0 := ENNReal.ofReal_eq_zero
    intro h_eq
    have h'' : L^3 ≤ 0 := h'.mp h_eq
    linarith
  have h5' : ENNReal.ofReal (L^3) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h6 : (relevant.card : ENNReal) ≤
      ENNReal.ofReal (1000 * (length + L) * (R + L)^2) / ENNReal.ofReal (L^3) := by
    let b := ENNReal.ofReal (L^3)
    have hb0 : b ≠ 0 := h5
    have hbt : b ≠ ⊤ := h5'
    have hbinv : b * b⁻¹ = 1 := ENNReal.mul_inv_cancel hb0 hbt
    calc (relevant.card : ENNReal)
      = (relevant.card : ENNReal) * (b * b⁻¹) := by rw [hbinv] <;> simp
      _ = ((relevant.card : ENNReal) * b) * b⁻¹ := by rw [mul_assoc]
      _ ≤ ENNReal.ofReal (1000 * (length + L) * (R + L)^2) * b⁻¹ := by gcongr
      _ = ENNReal.ofReal (1000 * (length + L) * (R + L)^2) / b := by rfl
  have h_pos1 : 0 ≤ 1000 * (length + L) * (R + L)^2 := by positivity
  have h7 : ENNReal.ofReal (1000 * (length + L) * (R + L)^2) / ENNReal.ofReal (L^3) =
      ENNReal.ofReal (1000 * (length + L) * (R + L)^2 / L^3) := by
    have hdiv : ENNReal.ofReal (1000 * (length + L) * (R + L)^2) / ENNReal.ofReal (L^3) =
        ENNReal.ofReal (1000 * (length + L) * (R + L)^2) * (ENNReal.ofReal (L^3))⁻¹ := by rfl
    rw [hdiv]
    have hinv : (ENNReal.ofReal (L^3))⁻¹ = ENNReal.ofReal ((L^3)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos h_pos3]
    rw [hinv]
    have hmul : ENNReal.ofReal (1000 * (length + L) * (R + L)^2) * ENNReal.ofReal ((L^3)⁻¹) =
        ENNReal.ofReal ((1000 * (length + L) * (R + L)^2) * (L^3)⁻¹) := by
      rw [← ENNReal.ofReal_mul h_pos1]
      <;> ring_nf
    rw [hmul]
    <;> ring_nf
  rw [h7] at h6
  exact h6

/-- Projection of a grid cube onto a unit direction fits in an interval
of half-width L*√3. -/
lemma cube_projection_interval
    {L : ℝ} (hL_pos : 0 < L)
    (cell : ℤ × ℤ × ℤ) (v : Point3) (hv_unit : ‖v‖ = 1) :
    ∃ (c : ℝ), scalarProjection v (wz1PaperGridCube L cell) ⊆
      Set.Icc (c - L * Real.sqrt 3) (c + L * Real.sqrt 3) := by
  let x0 := cellCorner L cell
  have h_x0_in : x0 ∈ wz1PaperGridCube L cell := cellCorner_mem_gridCube hL_pos cell
  refine ⟨inner ℝ x0 v, ?_⟩
  intro t ht
  rcases ht with ⟨x, hx, rfl⟩
  have hdist : dist x x0 ≤ L * Real.sqrt 3 :=
    wz1PaperGridCube_diameter hL_pos cell hx h_x0_in
  have h_eq : inner ℝ x v - inner ℝ x0 v = inner ℝ (x - x0) v := by
    rw [inner_sub_left] <;> ring
  have h1 : |inner ℝ (x - x0) v| ≤ ‖x - x0‖ * ‖v‖ := abs_real_inner_le_norm (x - x0) v
  have h1' : |inner ℝ x v - inner ℝ x0 v| ≤ ‖x - x0‖ := by
    rw [h_eq]
    rw [hv_unit] at h1
    simpa [mul_one] using h1
  have h2 : |inner ℝ x v - inner ℝ x0 v| ≤ L * Real.sqrt 3 := by
    have h3 : ‖x - x0‖ ≤ L * Real.sqrt 3 := by simpa [dist_eq_norm] using hdist
    exact h1'.trans h3
  have h4 : inner ℝ x0 v - L * Real.sqrt 3 ≤ inner ℝ x v := by
    linarith [abs_le.mp h2]
  have h5 : inner ℝ x v ≤ inner ℝ x0 v + L * Real.sqrt 3 := by
    linarith [abs_le.mp h2]
  exact ⟨h4, h5⟩

/-- Covering number bound for the projection of a union of grid cubes.

If ρ' ≥ L√3, each cube's projection fits in one ball of radius ρ'. -/
lemma projection_covering_from_cubes
    {L rho' : ℝ} (hL_pos : 0 < L) (hrho'_pos : 0 < rho') (hL_sqrt3_le_rho' : L * Real.sqrt 3 ≤ rho')
    (v : Point3) (hv_unit : ‖v‖ = 1)
    (cells : Finset (ℤ × ℤ × ℤ))
    (E : Set ℝ)
    (hE_sub : E ⊆ scalarProjection v (⋃ cell ∈ (cells : Set (ℤ × ℤ × ℤ)), wz1PaperGridCube L cell))
    (a length : ℝ) (hlen_pos : 0 < length) :
    (↑(Metric.externalCoveringNumber ⟨rho', hrho'_pos.le⟩ (E ∩ Set.Icc a (a + length))) : ENNReal) ≤
      (cells.card : ENNReal) := by
  let relevant := cells.filter fun cell =>
    (scalarProjection v (wz1PaperGridCube L cell) ∩ Set.Icc a (a + length)).Nonempty
  have h1 : E ∩ Set.Icc a (a + length) ⊆
      scalarProjection v (⋃ cell ∈ (relevant : Set (ℤ × ℤ × ℤ)), wz1PaperGridCube L cell) := by
    intro t ht
    have h_t_in_E : t ∈ E := ht.1
    have h_t_in_I : t ∈ Set.Icc a (a + length) := ht.2
    rcases hE_sub h_t_in_E with ⟨x, hx, rfl⟩
    have hx' := Set.mem_iUnion₂.mp hx
    rcases hx' with ⟨cell, hcell, hxcell⟩
    have h_rel : cell ∈ relevant := by
      simp only [relevant, Finset.mem_filter]
      exact ⟨hcell, ⟨inner ℝ x v, ⟨x, hxcell, rfl⟩, h_t_in_I⟩⟩
    exact ⟨x, Set.mem_iUnion₂.mpr ⟨cell, h_rel, hxcell⟩, rfl⟩
  have h2 : ∀ (cell : ℤ × ℤ × ℤ), cell ∈ relevant → ∃ (c : ℝ),
      scalarProjection v (wz1PaperGridCube L cell) ⊆ Metric.closedBall c rho' := by
    intro cell _
    rcases cube_projection_interval hL_pos cell v hv_unit with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro t ht
    have h3 : t ∈ Set.Icc (c - L * Real.sqrt 3) (c + L * Real.sqrt 3) := hc ht
    have h4 : |t - c| ≤ L * Real.sqrt 3 := by
      rw [abs_sub_le_iff] <;> constructor <;> linarith [h3.1, h3.2]
    have h5 : dist t c ≤ rho' := by
      simpa [Real.dist_eq] using h4.trans hL_sqrt3_le_rho'
    simpa [Metric.mem_closedBall] using h5
  classical
  let f : (ℤ × ℤ × ℤ) → ℝ := fun cell =>
    if h : cell ∈ relevant then Classical.choose (h2 cell h) else 0
  let centers : Finset ℝ := Finset.image f relevant
  have hc_spec : ∀ cell ∈ relevant,
      scalarProjection v (wz1PaperGridCube L cell) ⊆ Metric.closedBall (f cell) rho' := by
    intro cell hcell
    have h3 : f cell = Classical.choose (h2 cell hcell) := by
      simp [f, hcell]
    rw [h3]
    exact Classical.choose_spec (h2 cell hcell)
  let ε : NNReal := ⟨rho', hrho'_pos.le⟩
  have hcover : Metric.IsCover ε (E ∩ Set.Icc a (a + length)) (centers : Set ℝ) := by
    intro t ht
    rcases h1 ht with ⟨x, hx, rfl⟩
    have hx' := Set.mem_iUnion₂.mp hx
    rcases hx' with ⟨cell, hcell, hxcell⟩
    have h_c_in : f cell ∈ (centers : Set ℝ) := by
      simp only [centers, Finset.mem_coe, Finset.mem_image]
      exact ⟨cell, hcell, rfl⟩
    have h5 : inner ℝ x v ∈ scalarProjection v (wz1PaperGridCube L cell) := ⟨x, hxcell, rfl⟩
    have h6 : dist (inner ℝ x v) (f cell) ≤ rho' := by
      simpa [Metric.mem_closedBall] using hc_spec cell hcell h5
    have h7 : edist (inner ℝ x v) (f cell) ≤ ↑ε := by
      have h8 : edist (inner ℝ x v) (f cell) ≤ ENNReal.ofReal rho' :=
        (edist_le_ofReal hrho'_pos.le).mpr h6
      have h9 : (↑ε : ENNReal) = ENNReal.ofReal rho' := by
        have h10 : (ε : ℝ) = rho' := by
          simp [ε]
          <;> rfl
        have h11 : (↑ε : ENNReal) = ENNReal.ofReal (↑ε : ℝ) := ENNReal.coe_nnreal_eq ε
        rw [h11, h10]
      rw [h9]
      exact h8
    exact ⟨f cell, h_c_in, h7⟩
  have h3 : (Metric.externalCoveringNumber ε (E ∩ Set.Icc a (a + length)) : ENNReal) ≤
      (centers : Set ℝ).encard := by
    exact_mod_cast hcover.externalCoveringNumber_le_encard
  have h4 : (centers : Set ℝ).encard = (centers.card : ENNReal) := by simp
  have h5 : centers.card ≤ relevant.card := Finset.card_image_le
  have h6 : relevant.card ≤ cells.card := Finset.card_le_card (Finset.filter_subset _ _)
  calc
    (Metric.externalCoveringNumber ε (E ∩ Set.Icc a (a + length)) : ENNReal)
      ≤ (centers : Set ℝ).encard := h3
    _ = (centers.card : ENNReal) := h4
    _ ≤ (relevant.card : ENNReal) := by exact_mod_cast h5
    _ ≤ (cells.card : ENNReal) := by exact_mod_cast h6

/-- Covering number of a union of sets, each contained in an interval of length `W`.

If each `A i` is contained in some interval of length `W`, then the covering
number of the union at scale `r` is at most `s.card * (W/r + 2)`. -/
lemma covering_number_union_intervals
    {r W : ℝ} (hr_pos : 0 < r) (hW_nonneg : 0 ≤ W)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) {A : ι → Set ℝ}
    (hA : ∀ i ∈ s, ∃ (left : ℝ), A i ⊆ Set.Icc left (left + W)) :
    (↑(Metric.externalCoveringNumber ⟨r, hr_pos.le⟩ (⋃ i ∈ s, A i)) : ENNReal) ≤
      (s.card : ENNReal) * (ENNReal.ofReal (W / r) + 2) := by
  classical
  let ε : NNReal := ⟨r, hr_pos.le⟩
  let left : ι → ℝ := fun i =>
    if h : i ∈ s then Classical.choose (hA i h) else 0
  have hA' : ∀ i ∈ s, A i ⊆ Set.Icc (left i) (left i + W) := by
    intro i hi
    have hleft : left i = Classical.choose (hA i hi) := by
      simp [left, hi]
    rw [hleft]
    exact Classical.choose_spec (hA i hi)
  let n : ℕ := Nat.ceil (W / r)
  let centers_i : ι → Finset ℝ := fun i =>
    Finset.image (fun k : ℕ => left i + (k : ℝ) * r) (Finset.range (n + 1))
  have h_cover_i : ∀ i ∈ s, Metric.IsCover ε (A i) ((centers_i i : Set ℝ)) := by
    intro i hi
    intro t ht
    have h_t_in : t ∈ Set.Icc (left i) (left i + W) := hA' i hi ht
    have h1 : left i ≤ t := h_t_in.1
    have h2 : t ≤ left i + W := h_t_in.2
    let k : ℕ := Nat.ceil ((t - left i) / r)
    have hk1 : (k : ℝ) ≥ (t - left i) / r := Nat.le_ceil _
    have hk_ceil_lt : (k : ℝ) < (t - left i) / r + 1 := by
      exact Nat.ceil_lt_add_one (ha := by positivity)
    have hk_le_n : k ≤ n := by
      have h' : t - left i ≤ W := by linarith
      have h : (t - left i) / r ≤ W / r := by gcongr
      exact Nat.ceil_mono h
    have hk_range : k ∈ Finset.range (n + 1) := by
      simp only [Finset.mem_range]
      omega
    let c : ℝ := left i + (k : ℝ) * r
    have h_c_in : c ∈ (centers_i i : Set ℝ) := by
      simp only [centers_i, Finset.mem_coe, Finset.mem_image]
      exact ⟨k, hk_range, rfl⟩
    have h_dist : dist t c ≤ r := by
      have h3 : t ≤ c := by
        have h4 : (k : ℝ) * r ≥ t - left i := by
          have h5 : (k : ℝ) ≥ (t - left i) / r := hk1
          have h6 : (k : ℝ) * r ≥ ((t - left i) / r) * r := by gcongr
          have h7 : ((t - left i) / r) * r = t - left i := by
            field_simp [hr_pos.ne'] <;> ring
          linarith
        simpa [c] using show t ≤ left i + (k : ℝ) * r from by linarith
      have h4 : c < t + r := by
        have h5 : (k : ℝ) * r < t - left i + r := by
          have h6 : (k : ℝ) < (t - left i) / r + 1 := hk_ceil_lt
          have h7 : (k : ℝ) * r < ((t - left i) / r + 1) * r := by gcongr
          have h8 : ((t - left i) / r + 1) * r = t - left i + r := by
            field_simp [hr_pos.ne'] <;> ring
          linarith
        simpa [c] using show left i + (k : ℝ) * r < t + r from by linarith
      simp only [Real.dist_eq, abs_le]
      constructor <;> linarith
    have h_edist : edist t c ≤ (↑ε : ENNReal) := by
      rw [edist_dist]
      have h_coe : (↑ε : ENNReal) = ENNReal.ofReal r :=
        ENNReal.coe_nnreal_eq ε
      rw [h_coe]
      exact ENNReal.ofReal_le_ofReal h_dist
    exact ⟨c, h_c_in, h_edist⟩
  let all_centers : Finset ℝ := s.biUnion centers_i
  have h_cover : Metric.IsCover ε (⋃ i ∈ s, A i) (all_centers : Set ℝ) := by
    intro t ht
    rcases Set.mem_iUnion₂.mp ht with ⟨i, hi, hti⟩
    have h := h_cover_i i hi hti
    rcases h with ⟨c, hc_in, hc_dist⟩
    have h_c_in_all : c ∈ (all_centers : Set ℝ) := by
      simp only [all_centers, Finset.mem_coe, Finset.mem_biUnion]
      exact ⟨i, hi, hc_in⟩
    exact ⟨c, h_c_in_all, hc_dist⟩
  have h1 : (Metric.externalCoveringNumber ε (⋃ i ∈ s, A i) : ENNReal) ≤
      (all_centers : Set ℝ).encard := by
    exact_mod_cast h_cover.externalCoveringNumber_le_encard
  have h2 : (all_centers : Set ℝ).encard = (all_centers.card : ENNReal) := by simp
  have h3 : all_centers.card ≤ ∑ i ∈ s, (centers_i i).card := Finset.card_biUnion_le
  have h4 : ∀ i ∈ s, (centers_i i).card ≤ n + 1 := by
    intro i _
    have h : (centers_i i).card ≤ (Finset.range (n + 1)).card := Finset.card_image_le
    simpa [centers_i] using h
  have h5 : ∑ i ∈ s, (centers_i i).card ≤ s.card * (n + 1) := by
    calc ∑ i ∈ s, (centers_i i).card
      ≤ ∑ _i ∈ s, (n + 1) := Finset.sum_le_sum h4
    _ = s.card * (n + 1) := by simp [Finset.sum_const] <;> ring
  have h6 : (n : ℝ) ≤ W / r + 1 := by
    have h : (n : ℝ) < W / r + 1 := by
      exact Nat.ceil_lt_add_one (ha := by positivity)
    linarith
  have h7 : ((n + 1 : ℕ) : ENNReal) ≤ ENNReal.ofReal (W / r) + 2 := by
    have h8 : ((n + 1 : ℕ) : ℝ) ≤ W / r + 2 := by
      have h9 : (n : ℝ) ≤ W / r + 1 := h6
      have h10 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
      rw [h10]
      linarith
    have h10 : ENNReal.ofReal (W / r + 2) = ENNReal.ofReal (W / r) + 2 := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num)] <;> simp
    have h11 : ((n + 1 : ℕ) : ENNReal) = ENNReal.ofReal ((n + 1 : ℕ) : ℝ) := by
      norm_cast
    rw [h11]
    have h12 : ENNReal.ofReal ((n + 1 : ℕ) : ℝ) ≤ ENNReal.ofReal (W / r + 2) := ENNReal.ofReal_le_ofReal h8
    rw [h10] at h12
    exact h12
  calc
    (Metric.externalCoveringNumber ε (⋃ i ∈ s, A i) : ENNReal)
      ≤ (all_centers : Set ℝ).encard := h1
    _ = (all_centers.card : ENNReal) := h2
    _ ≤ (∑ i ∈ s, (centers_i i).card : ENNReal) := by exact_mod_cast h3
    _ ≤ (s.card * (n + 1) : ENNReal) := by exact_mod_cast h5
    _ = (s.card : ENNReal) * ((n + 1 : ℕ) : ENNReal) := by
      simp [Nat.cast_mul]
    _ ≤ (s.card : ENNReal) * (ENNReal.ofReal (W / r) + 2) := by gcongr

end Kakeya.Assouad

end
