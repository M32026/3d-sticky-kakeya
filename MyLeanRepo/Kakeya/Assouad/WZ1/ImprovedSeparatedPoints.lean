import MyLeanRepo.Kakeya.Assouad.WZ1.Statements
import MyLeanRepo.Kakeya.Assouad.WZ1.CubeCountGeometry
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Improved separated points extraction using slab/projection method

Partition the tube into slabs perpendicular to its direction. Each slab
intersects the tube in volume at most `4 * δ² * w` (via three-diameters bound).
By selecting slabs sufficiently far apart, we extract separated points with
constant better than the ball-packing method.
-/

namespace Kakeya.Assouad

open MeasureTheory Metric

/--
Volume bound for a `δ`-tube intersected with a slab perpendicular to its
direction axis. The slab is `a ≤ inner(x - base, direction) ≤ a + w`.

After aligning the tube with the first coordinate axis, the intersection has
coordinate diameters `w`, `2δ`, `2δ`, giving volume `4 * δ² * w`.
-/
lemma deltaTube_inter_axis_slab_volume_le
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (T : Kakeya.DeltaTube delta)
    (a w : ℝ) (hw_nonneg : 0 ≤ w) :
    volume (T.carrier ∩ {x | a ≤ inner ℝ (x - T.base) T.direction ∧
        inner ℝ (x - T.base) T.direction ≤ a + w})
      ≤ ENNReal.ofReal (4 * delta^2 * w) := by
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  have he0 : ‖e0‖ = 1 := by simp [e0]
  have hnorm : ‖T.direction‖ = ‖e0‖ := by rw [T.direction_unit, he0]
  let A : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (T.direction - e0))ᗮ
  have hA_dir : A T.direction = e0 := Submodule.reflection_sub hnorm
  let c : Point3 := A T.base
  let E : Set Point3 := T.carrier ∩
    {x | a ≤ inner ℝ (x - T.base) T.direction ∧
          inner ℝ (x - T.base) T.direction ≤ a + w}

  have h_segment_compact : IsCompact (Kakeya.unitSegment T.base T.direction) := by
    apply IsCompact.image isCompact_Icc
    fun_prop
  have h_carrier_closed : IsClosed T.carrier := by
    have h : T.carrier = Metric.cthickening delta (Kakeya.unitSegment T.base T.direction) := rfl
    rw [h]
    exact h_segment_compact.cthickening.isClosed
  have h_cont : Continuous (fun x : Point3 => inner ℝ (x - T.base) T.direction) :=
    Continuous.inner (continuous_id.sub continuous_const) continuous_const
  have h_slab_closed : IsClosed {x : Point3 | a ≤ inner ℝ (x - T.base) T.direction ∧
        inner ℝ (x - T.base) T.direction ≤ a + w} := by
    apply IsClosed.inter
    · exact isClosed_le continuous_const h_cont
    · exact isClosed_le h_cont continuous_const
  have hE_meas : MeasurableSet E :=
    h_carrier_closed.measurableSet.inter h_slab_closed.measurableSet

  have h_inner_eq : ∀ (x : Point3),
      inner ℝ (x - T.base) T.direction = (A x - c) 0 := by
    intro x
    have h : inner ℝ (x - T.base) T.direction =
        inner ℝ (A (x - T.base)) (A T.direction) :=
      (A.inner_map_map _ _).symm
    rw [h]
    have h2 : A (x - T.base) = A x - c := by simp [A.map_sub, c]
    rw [h2, hA_dir]
    simp [e0, inner] <;> rfl

  have h_axis_diam : ∀ x y, x ∈ E → y ∈ E → |(A x) 0 - (A y) 0| ≤ w := by
    intro x y hx hy
    have hx_slab : a ≤ inner ℝ (x - T.base) T.direction ∧
        inner ℝ (x - T.base) T.direction ≤ a + w := hx.2
    have hy_slab : a ≤ inner ℝ (y - T.base) T.direction ∧
        inner ℝ (y - T.base) T.direction ≤ a + w := hy.2
    have hx' : a ≤ (A x - c) 0 ∧ (A x - c) 0 ≤ a + w := by
      have h := h_inner_eq x
      rw [h] at hx_slab
      exact hx_slab
    have hy' : a ≤ (A y - c) 0 ∧ (A y - c) 0 ≤ a + w := by
      have h := h_inner_eq y
      rw [h] at hy_slab
      exact hy_slab
    have h3 : (A x) 0 - (A y) 0 = (A x - c) 0 - (A y - c) 0 := by simp
    rw [h3]
    have h4 : (A x - c) 0 - (A y - c) 0 ≤ w := by linarith
    have h5 : -w ≤ (A x - c) 0 - (A y - c) 0 := by linarith
    rw [abs_le] <;> constructor <;> linarith

  have h_transverse_bound : ∀ (x : Point3), x ∈ T.carrier →
      |(A x) 1 - c 1| ≤ delta ∧ |(A x) 2 - c 2| ≤ delta := by
    intro x hx
    have h_thick : x ∈ Metric.cthickening delta (Kakeya.unitSegment T.base T.direction) := hx
    rw [IsCompact.cthickening_eq_biUnion_closedBall h_segment_compact (by linarith)] at h_thick
    rcases Set.mem_iUnion₂.mp h_thick with ⟨z, hz, hdist⟩
    rcases hz with ⟨t, _ht, rfl⟩
    have h_dist2 : dist (A x) (A (T.base + t • T.direction)) ≤ delta := by
      have h_eq : dist (A x) (A (T.base + t • T.direction)) =
          dist x (T.base + t • T.direction) := A.dist_map _ _
      rw [h_eq]; exact hdist
    have h_Az : A (T.base + t • T.direction) = c + t • e0 := by
      simp [A.map_add, A.map_smul, hA_dir, c]
    rw [h_Az] at h_dist2
    have h1 : |(A x) 1 - (c + t • e0) 1| ≤ delta :=
      (PiLp.dist_apply_le (A x) (c + t • e0) 1).trans h_dist2
    have h2 : |(A x) 2 - (c + t • e0) 2| ≤ delta :=
      (PiLp.dist_apply_le (A x) (c + t • e0) 2).trans h_dist2
    have h3 : (c + t • e0) 1 = c 1 := by simp [e0]
    have h4 : (c + t • e0) 2 = c 2 := by simp [e0]
    rw [h3] at h1; rw [h4] at h2
    exact ⟨h1, h2⟩

  have h1_diam : ∀ x y, x ∈ E → y ∈ E → |(A x) 1 - (A y) 1| ≤ 2 * delta := by
    intro x y hx hy
    have hx' := h_transverse_bound x hx.1
    have hy' := h_transverse_bound y hy.1
    have h_tri : |(A x) 1 - (A y) 1| ≤ |(A x) 1 - c 1| + |c 1 - (A y) 1| := by
      have h : (A x) 1 - (A y) 1 = ((A x) 1 - c 1) + (c 1 - (A y) 1) := by ring
      rw [h]; exact abs_add_le _ _
    have h_comm : |c 1 - (A y) 1| = |(A y) 1 - c 1| := by
      rw [show c 1 - (A y) 1 = -((A y) 1 - c 1) by ring]; rw [abs_neg]
    rw [h_comm] at h_tri
    linarith [hx'.1, hy'.1]

  have h2_diam : ∀ x y, x ∈ E → y ∈ E → |(A x) 2 - (A y) 2| ≤ 2 * delta := by
    intro x y hx hy
    have hx' := h_transverse_bound x hx.1
    have hy' := h_transverse_bound y hy.1
    have h_tri : |(A x) 2 - (A y) 2| ≤ |(A x) 2 - c 2| + |c 2 - (A y) 2| := by
      have h : (A x) 2 - (A y) 2 = ((A x) 2 - c 2) + (c 2 - (A y) 2) := by ring
      rw [h]; exact abs_add_le _ _
    have h_comm : |c 2 - (A y) 2| = |(A y) 2 - c 2| := by
      rw [show c 2 - (A y) 2 = -((A y) 2 - c 2) by ring]; rw [abs_neg]
    rw [h_comm] at h_tri
    linarith [hx'.2, hy'.2]

  have hd0 : 0 ≤ w := by linarith
  have hd1 : 0 ≤ 2 * delta := by positivity
  have hd2 : 0 ≤ 2 * delta := by positivity
  have h_main : volume E ≤ ENNReal.ofReal (w * (2 * delta) * (2 * delta)) :=
    volume_by_three_diameters_public hE_meas A w (2 * delta) (2 * delta)
      hd0 hd1 hd2 h_axis_diam h1_diam h2_diam
  have h_eq : w * (2 * delta) * (2 * delta) = 4 * delta^2 * w := by ring
  rw [h_eq] at h_main
  exact h_main

/-- Helper: `(n : ENNReal) * ENNReal.ofReal x = ENNReal.ofReal ((n : ℝ) * x)`. -/
private lemma enat_mul_ofReal {n : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    (n : ENNReal) * ENNReal.ofReal x = ENNReal.ofReal ((n : ℝ) * x) := by
  have h2 : 0 ≤ (n : ℝ) := by positivity
  simp [h2, hx]
  <;> norm_cast

/-- Sum of a constant over a finite type. -/
lemma sum_const_helper {α : Type*} [Fintype α] (c : ℝ) :
    ∑ r : α, c = (Fintype.card α : ℝ) * c := by
  have h_smul : ∀ (n : ℕ), n • c = (n : ℝ) * c := by
    intro n
    simp [nsmul_eq_mul]
    <;> ring
  have h : ∑ r ∈ (Finset.univ : Finset α), c = (Finset.univ : Finset α).card • c := by
    rw [Finset.sum_const]
  have h2 : ∑ r ∈ (Finset.univ : Finset α), c = ((Finset.univ : Finset α).card : ℝ) * c := by
    rw [h, h_smul]
  have h3 : ((Finset.univ : Finset α).card : ℝ) = (Fintype.card α : ℝ) := by
    norm_cast <;> simp
  rw [h2, h3]

/-- In any additive commutative group, `(a - c) - (b - c) = a - b`. -/
lemma sub_sub_sub_cancel_right {G : Type*} [AddCommGroup G] (a b c : G) :
    (a - c) - (b - c) = a - b := by
  have h : (a - c) - (b - c) = (a - c) + (c - b) := by
    rw [sub_eq_add_neg, neg_sub]
    <;> rfl
  rw [h]
  have h3 : (a - c) + (c - b) = a - b := by
    calc (a - c) + (c - b)
      = (a - c) + c - b := by rw [add_sub_assoc]
    _ = a - b := by rw [sub_add_cancel]
  exact h3

/--
Extract separated points from a set inside a tube using slab partitioning.

Slabs of width `sep_scale / 5` perpendicular to the tube direction are used.
Selecting every 6th nonempty slab gives points separated by `≥ sep_scale`.
The number of points satisfies `k ≥ 5 * V / (24 * delta^2 * sep_scale)`.
-/
lemma separated_points_from_tube_volume_slab
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (T : Kakeya.DeltaTube delta) (q : Point3) (tau : ℝ) (_htau_pos : 0 < tau)
    (S : Set Point3) (_hS_meas : MeasurableSet S)
    (hS_sub : S ⊆ T.carrier ∩ Metric.closedBall q tau)
    (sep_scale : ℝ) (hsep_pos : 0 < sep_scale)
    (V : ℝ) (_hV_pos : 0 < V)
    (h_volume : volume S ≥ ENNReal.ofReal V) :
    ∃ (p : ℕ → Point3) (k : ℕ),
      (k : ℝ) ≥ 5 * V / (24 * delta^2 * sep_scale) ∧
      (∀ m < k, p m ∈ S) ∧
      (∀ m n, m < k → n < k → m ≠ n → dist (p m) (p n) ≥ sep_scale) := by
  classical
  let w : ℝ := sep_scale / 5
  have hw_pos : 0 < w := by positivity
  let m : ℕ := 6
  let π : Point3 → ℝ := fun x => inner ℝ (x - T.base) T.direction
  let slab (j : ℤ) : Set Point3 :=
    {x | (j : ℝ) * w ≤ π x ∧ π x ≤ ((j : ℝ) + 1) * w}

  have hdir_unit : ‖T.direction‖ = 1 := T.direction_unit
  have hB : ∀ x ∈ S, |π x| ≤ tau + |inner ℝ (q - T.base) T.direction| := by
    intro x hx
    have h_ball : dist x q ≤ tau := (hS_sub hx).2
    have h_eq1 : x - T.base = (x - q) + (q - T.base) := by abel
    have h1 : π x = inner ℝ (x - q) T.direction + inner ℝ (q - T.base) T.direction := by
      rw [show π x = inner ℝ (x - T.base) T.direction from rfl, h_eq1]
      rw [inner_add_left]
    have h2 : |inner ℝ (x - q) T.direction| ≤ dist x q := by
      have h21 : |inner ℝ (x - q) T.direction| ≤ ‖x - q‖ * ‖T.direction‖ := by
        exact abs_real_inner_le_norm (x - q) T.direction
      rw [hdir_unit] at h21
      have h22 : ‖x - q‖ = dist x q := by rw [dist_eq_norm]
      rw [h22] at h21
      simpa using h21
    have h_abs : |π x| ≤ |inner ℝ (x - q) T.direction| + |inner ℝ (q - T.base) T.direction| := by
      rw [h1]
      exact abs_add_le _ _
    calc |π x|
      ≤ |inner ℝ (x - q) T.direction| + |inner ℝ (q - T.base) T.direction| := h_abs
    _ ≤ dist x q + |inner ℝ (q - T.base) T.direction| := by gcongr
    _ ≤ tau + |inner ℝ (q - T.base) T.direction| := by gcongr
  let B : ℝ := tau + |inner ℝ (q - T.base) T.direction|
  let N : ℤ := Int.ceil (B / w) + 2
  have hB_pos : 0 < B := by
    dsimp only [B]
    have h : 0 ≤ |inner ℝ (q - T.base) T.direction| := abs_nonneg _
    linarith
  have hBw_pos : 0 < B / w := by positivity
  have h_ceil_pos : (0 : ℝ) ≤ (Int.ceil (B / w) : ℝ) := by
    by_contra h2
    have h3 : (Int.ceil (B / w) : ℝ) < 0 := by linarith
    have h4 : B / w ≤ (Int.ceil (B / w) : ℝ) := Int.le_ceil (B / w)
    linarith [hBw_pos]
  have hN_pos : (0 : ℝ) ≤ (N : ℝ) := by
    have h1 : (N : ℝ) = (Int.ceil (B / w) : ℝ) + 2 := by simp [N]
    rw [h1]
    linarith
  have h_range : ∀ x ∈ S, ∃ j ∈ Finset.Icc (-N) N, x ∈ slab j := by
    intro x hx
    have h4 : |π x| ≤ B := hB x hx
    let j : ℤ := Int.floor (π x / w)
    have h5 : (j : ℝ) * w ≤ π x := by
      have h6 : (j : ℝ) ≤ π x / w := Int.floor_le (π x / w)
      have h7 : 0 < w := hw_pos
      have h : (j : ℝ) * w ≤ (π x / w) * w := by gcongr
      have h9 : (π x / w) * w = π x := by
        field_simp [h7.ne'] <;> ring
      rw [h9] at h
      exact h
    have h8 : π x < ((j : ℝ) + 1) * w := by
      have h9 : π x / w < (j : ℝ) + 1 := Int.lt_floor_add_one (π x / w)
      have h10 : 0 < w := hw_pos
      have h : (π x / w) * w < ((j : ℝ) + 1) * w := by gcongr
      have h11 : (π x / w) * w = π x := by
        field_simp [h10.ne'] <;> ring
      rw [h11] at h
      exact h
    have h_j1 : -N ≤ j := by
      have h11 : -B ≤ π x := by linarith [abs_le.mp h4]
      have h12 : -B / w ≤ π x / w := by gcongr
      have h13 : (j : ℝ) ≥ π x / w - 1 := by
        have h14 : (j : ℝ) = Int.floor (π x / w) := by simp [j]
        rw [h14]
        have h15 : π x / w < (Int.floor (π x / w) : ℝ) + 1 := Int.lt_floor_add_one (π x / w)
        linarith
      have h14 : (j : ℝ) ≥ -B / w - 1 := by linarith
      have h15 : (N : ℝ) ≥ B / w + 1 := by
        have h16 : (Int.ceil (B / w) : ℝ) ≥ B / w := Int.le_ceil (B / w)
        have h17 : (N : ℝ) = (Int.ceil (B / w) : ℝ) + 2 := by simp [N]
        rw [h17]
        linarith
      have h18 : (-N : ℝ) ≤ -B / w - 1 := by
        have h181 : -((N : ℝ)) ≤ -(B / w + 1) := neg_le_neg h15
        have h182 : -(B / w + 1) = -B / w - 1 := by ring
        rw [h182] at h181
        exact h181
      have h19 : (-N : ℝ) ≤ (j : ℝ) := by
        calc (-N : ℝ) ≤ -B / w - 1 := h18
             _ ≤ (j : ℝ) := h14
      exact_mod_cast h19
    have h_j2 : j ≤ N := by
      have h18 : π x ≤ B := by linarith [abs_le.mp h4]
      have h19 : π x / w ≤ B / w := by gcongr
      have h20 : (j : ℝ) ≤ π x / w := Int.floor_le (π x / w)
      have h21 : (j : ℝ) ≤ B / w := by linarith
      have h22 : (N : ℝ) ≥ B / w + 1 := by
        have h23 : (Int.ceil (B / w) : ℝ) ≥ B / w := Int.le_ceil (B / w)
        have h24 : (N : ℝ) = (Int.ceil (B / w) : ℝ) + 2 := by simp [N]
        rw [h24]
        linarith
      have h25 : (j : ℝ) ≤ (N : ℝ) := by
        have h26 : (j : ℝ) < (N : ℝ) := by
          calc (j : ℝ) ≤ B / w := h21
               _ < B / w + 1 := by linarith
               _ ≤ (N : ℝ) := h22
        exact le_of_lt h26
      exact_mod_cast h25
    refine ⟨j, Finset.mem_Icc.mpr ⟨h_j1, h_j2⟩, ?_⟩
    exact ⟨h5, by linarith⟩

  let J_all : Finset ℤ := Finset.Icc (-N) N
  let J : Finset ℤ := J_all.filter (fun j => (S ∩ slab j).Nonempty)
  have hJ_def : ∀ j, j ∈ J ↔ j ∈ J_all ∧ (S ∩ slab j).Nonempty := by
    intro j
    simp [J]
  have h_cover : S ⊆ ⋃ j ∈ J, slab j := by
    intro x hx
    rcases h_range x hx with ⟨j, hj_in, hx_slab⟩
    have h_nonempty : (S ∩ slab j).Nonempty := ⟨x, ⟨hx, hx_slab⟩⟩
    have hjJ : j ∈ J := (hJ_def j).mpr ⟨hj_in, h_nonempty⟩
    exact Set.mem_iUnion₂.mpr ⟨j, hjJ, hx_slab⟩

  have h_vol_bound : ∀ j ∈ J, volume (S ∩ slab j) ≤ ENNReal.ofReal (4 * delta^2 * w) := by
    intro j hj
    have h_nonempty : (S ∩ slab j).Nonempty := (hJ_def j).mp hj |>.2
    have h_sub : S ∩ slab j ⊆ T.carrier ∩ slab j := by
      intro x hx
      exact ⟨(hS_sub hx.1).1, hx.2⟩
    have h_slab_eq : (T.carrier ∩ slab j) =
        T.carrier ∩ {x | (j : ℝ) * w ≤ inner ℝ (x - T.base) T.direction ∧
          inner ℝ (x - T.base) T.direction ≤ (j : ℝ) * w + w} := by
      have h9 : ((j : ℝ) + 1) * w = (j : ℝ) * w + w := by ring
      simp [slab, h9]
      <;> rfl
    rw [h_slab_eq] at h_sub
    exact (measure_mono h_sub).trans
      (deltaTube_inter_axis_slab_volume_le hdelta_pos T ((j : ℝ) * w) w (by linarith))

  have h_union_bound : ∀ (s : Finset ℤ),
      volume (⋃ j ∈ s, (S ∩ slab j)) ≤ ∑ j ∈ s, volume (S ∩ slab j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      have h_eq : (⋃ k ∈ (insert j s), (S ∩ slab k)) =
          (S ∩ slab j) ∪ (⋃ k ∈ s, (S ∩ slab k)) := by ext x; simp
      rw [h_eq, Finset.sum_insert hj]
      have h1 : volume ((S ∩ slab j) ∪ (⋃ k ∈ s, (S ∩ slab k))) ≤
          volume (S ∩ slab j) + volume (⋃ k ∈ s, (S ∩ slab k)) := measure_union_le _ _
      have h2 : volume (⋃ k ∈ s, (S ∩ slab k)) ≤ ∑ k ∈ s, volume (S ∩ slab k) := ih
      have h3 : volume (S ∩ slab j) + volume (⋃ k ∈ s, (S ∩ slab k)) ≤
          volume (S ∩ slab j) + ∑ k ∈ s, volume (S ∩ slab k) := by
        gcongr
      exact h1.trans h3

  have h_eq2 : S = ⋃ j ∈ J, (S ∩ slab j) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      rcases h_range x hx with ⟨j, hj_in, hx_slab⟩
      have h_nonempty : (S ∩ slab j).Nonempty := ⟨x, ⟨hx, hx_slab⟩⟩
      have hjJ : j ∈ J := (hJ_def j).mpr ⟨hj_in, h_nonempty⟩
      exact ⟨j, hjJ, ⟨hx, hx_slab⟩⟩
    · rintro ⟨j, _hj, hx⟩
      exact hx.1

  have h_vol : volume S ≤ (J.card : ENNReal) * ENNReal.ofReal (4 * delta^2 * w) := by
    calc
      volume S = volume (⋃ j ∈ J, (S ∩ slab j)) := by
        exact congr_arg volume h_eq2
      _ ≤ ∑ j ∈ J, volume (S ∩ slab j) := h_union_bound J
      _ ≤ ∑ j ∈ J, ENNReal.ofReal (4 * delta^2 * w) :=
        Finset.sum_le_sum h_vol_bound
      _ = (J.card : ENNReal) * ENNReal.ofReal (4 * delta^2 * w) := by
        simp [Finset.sum_const]

  have h_pos_const : 0 < 4 * delta^2 * w := by positivity
  have h_card_lower : (J.card : ℝ) ≥ V / (4 * delta^2 * w) := by
    have h1 : ENNReal.ofReal V ≤ (J.card : ENNReal) * ENNReal.ofReal (4 * delta^2 * w) :=
      h_volume.trans h_vol
    have h_mul_nonneg : 0 ≤ (J.card : ℝ) * (4 * delta^2 * w) := by
      apply mul_nonneg
      · exact_mod_cast Nat.cast_nonneg J.card
      · positivity
    have h2 : (J.card : ENNReal) * ENNReal.ofReal (4 * delta^2 * w) =
        ENNReal.ofReal ((J.card : ℝ) * (4 * delta^2 * w)) :=
      enat_mul_ofReal (show 0 ≤ 4 * delta^2 * w by positivity)
    rw [h2] at h1
    have hV_nonneg : 0 ≤ V := by linarith [_hV_pos]
    have h4 : V ≤ (J.card : ℝ) * (4 * delta^2 * w) :=
      (ENNReal.ofReal_le_ofReal_iff h_mul_nonneg).mp h1
    have hB : (4 * delta^2 * w) ≠ 0 := by linarith
    have h_eq : ((J.card : ℝ) * (4 * delta^2 * w)) / (4 * delta^2 * w) = (J.card : ℝ) := by
      have h : ((J.card : ℝ) * (4 * delta^2 * w)) / (4 * delta^2 * w) =
          (J.card : ℝ) * ((4 * delta^2 * w) / (4 * delta^2 * w)) := by
        rw [mul_div_assoc]
      rw [h]
      have h2 : (4 * delta^2 * w) / (4 * delta^2 * w) = 1 := div_self hB
      rw [h2] <;> ring
    calc (J.card : ℝ)
      = ((J.card : ℝ) * (4 * delta^2 * w)) / (4 * delta^2 * w) := h_eq.symm
    _ ≥ V / (4 * delta^2 * w) := by gcongr

  let J_r : Fin m → Finset ℤ := fun r =>
    J.filter (fun j => j % (m : ℤ) = (r : ℤ))
  have h_disj : ∀ (r1 r2 : Fin m), r1 ≠ r2 → Disjoint (J_r r1) (J_r r2) := by
    intro r1 r2 hne
    simp only [J_r, Finset.disjoint_left]
    intro j hj1 hj2
    have h1 : j % (m : ℤ) = (r1 : ℤ) := (Finset.mem_filter.mp hj1).2
    have h2 : j % (m : ℤ) = (r2 : ℤ) := (Finset.mem_filter.mp hj2).2
    have h3 : (r1 : ℤ) = (r2 : ℤ) := by rw [←h1, h2]
    have h4 : r1 = r2 := by
      apply Fin.ext
      exact_mod_cast h3
    exact hne h4
  have h_union : J = Finset.biUnion (Finset.univ : Finset (Fin m)) J_r := by
    ext j
    simp only [J_r, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro hj
      have h1 : j ∈ J := hj
      have h_nonneg : 0 ≤ j % (m : ℤ) := by
        apply Int.emod_nonneg
        omega
      have h_lt : j % (m : ℤ) < (m : ℤ) := by
        apply Int.emod_lt
        omega
      let r : Fin m := ⟨(j % (m : ℤ)).toNat, by
        have h5 : ((j % (m : ℤ)).toNat : ℤ) = j % (m : ℤ) := by
          rw [Int.toNat_of_nonneg h_nonneg]
        have h6 : (j % (m : ℤ)).toNat < m := by
          omega
        exact h6⟩
      have hr_val : (r : ℤ) = j % (m : ℤ) := by
        have h5 : ((j % (m : ℤ)).toNat : ℤ) = j % (m : ℤ) := by
          rw [Int.toNat_of_nonneg h_nonneg]
        have h6 : (r : ℤ) = ((j % (m : ℤ)).toNat : ℤ) := by
          simp [r] <;> rfl
        rw [h6, h5]
      refine ⟨r, ?_⟩
      simpa [J_r, hr_val] using h1
    · rintro ⟨r, hr⟩
      exact (Finset.mem_filter.mp hr).1
  have h_sum : (J.card : ℝ) = ∑ r : Fin m, ((J_r r).card : ℝ) := by
    have h_card : J.card = ∑ r : Fin m, (J_r r).card := by
      have h9 : J = Finset.biUnion (Finset.univ : Finset (Fin m)) J_r := h_union
      rw [h9]
      have h_pairwise : ∀ (i : Fin m), i ∈ (Finset.univ : Finset (Fin m)) →
          ∀ (j : Fin m), j ∈ (Finset.univ : Finset (Fin m)) → i ≠ j → Disjoint (J_r i) (J_r j) := by
        intro i _ j _ hne
        exact h_disj i j hne
      exact Finset.card_biUnion h_pairwise
    exact_mod_cast h_card

  have h_exists : ∃ (r : Fin m), ((J_r r).card : ℝ) ≥ (J.card : ℝ) / (m : ℝ) := by
    by_contra h
    push Not at h
    have h_all_lt : ∀ r : Fin m, ((J_r r).card : ℝ) < (J.card : ℝ) / (m : ℝ) := h
    have h_pos : 0 < ∑ r : Fin m, ((J.card : ℝ) / (m : ℝ) - ((J_r r).card : ℝ)) := by
      apply Finset.sum_pos
      · intro r _
        exact sub_pos.mpr (h_all_lt r)
      · refine' ⟨⟨0, by norm_num [m]⟩, Finset.mem_univ _⟩
    have h_sum_diff : ∑ r : Fin m, ((J.card : ℝ) / (m : ℝ) - ((J_r r).card : ℝ)) =
        (∑ r : Fin m, (J.card : ℝ) / (m : ℝ)) - ∑ r : Fin m, ((J_r r).card : ℝ) := by
      rw [Finset.sum_sub_distrib]
    have h_strict : ∑ r : Fin m, ((J_r r).card : ℝ) < ∑ r : Fin m, (J.card : ℝ) / (m : ℝ) := by
      have h_pos2 : (∑ r : Fin m, (J.card : ℝ) / (m : ℝ)) - ∑ r : Fin m, ((J_r r).card : ℝ) > 0 := by
        rw [←h_sum_diff]
        exact h_pos
      exact sub_pos.mp h_pos2
    have h_sum_const : ∑ r : Fin m, (J.card : ℝ) / (m : ℝ) = (J.card : ℝ) := by
      let c : ℝ := (J.card : ℝ) / (m : ℝ)
      have h1 : ∑ r : Fin m, c = (Fintype.card (Fin m) : ℝ) * c := sum_const_helper c
      have h_card : Fintype.card (Fin m) = m := by simp
      have h3 : (m : ℝ) ≠ 0 := by norm_num [m]
      calc ∑ r : Fin m, (J.card : ℝ) / (m : ℝ)
        = (Fintype.card (Fin m) : ℝ) * ((J.card : ℝ) / (m : ℝ)) := h1
      _ = (m : ℝ) * ((J.card : ℝ) / (m : ℝ)) := by rw [show (Fintype.card (Fin m) : ℝ) = (m : ℝ) from by exact_mod_cast h_card]
      _ = (J.card : ℝ) := mul_div_cancel₀ (J.card : ℝ) h3
    rw [h_sum_const] at h_strict
    rw [h_sum] at h_strict
    <;> linarith
  rcases h_exists with ⟨r, hr⟩
  let J' : Finset ℤ := J_r r

  have h_select : ∀ j ∈ J', ∃ (x : Point3), x ∈ S ∩ slab j := by
    intro j hj
    have h1 : j ∈ J := (Finset.mem_filter.mp hj).1
    have h2 : (S ∩ slab j).Nonempty := (hJ_def j).mp h1 |>.2
    exact h2

  choose p_dep hp_dep using h_select
  let p : ℤ → Point3 := fun j => if h : j ∈ J' then p_dep j h else q

  have hp : ∀ (j : ℤ), j ∈ J' → p j ∈ S ∩ slab j := by
    intro j hj
    have hpe : p j = p_dep j hj := by
      change (if h : j ∈ J' then p_dep j h else q) = p_dep j hj
      exact dif_pos hj
    rw [hpe]
    exact hp_dep j hj

  have h_sep : ∀ (j k : ℤ), j ∈ J' → k ∈ J' → j ≠ k →
      dist (p j) (p k) ≥ sep_scale := by
    intro j k hj hk hne
    wlog h_jk : j < k generalizing j k
    · have hklj : k < j := by omega
      have h := this k j hk hj (Ne.symm hne) hklj
      have h_comm : dist (p j) (p k) = dist (p k) (p j) := dist_comm (p j) (p k)
      rw [h_comm]
      exact h
    have h1 : j % (m : ℤ) = (r : ℤ) := (Finset.mem_filter.mp hj).2
    have h2 : k % (m : ℤ) = (r : ℤ) := (Finset.mem_filter.mp hk).2
    have h3 : k - j ≥ (m : ℤ) := by
      have hpos : 0 < (m : ℤ) := by norm_num [m]
      have hdiv : (m : ℤ) ∣ (k - j) := by
        have h : (k - j) % (m : ℤ) = 0 := by
          have h_sub : (k - j) % (m : ℤ) = ((k % (m : ℤ)) - (j % (m : ℤ))) % (m : ℤ) := by
            rw [Int.sub_emod]
          rw [h_sub, h2, h1]
          <;> simp
        have hdiv : (m : ℤ) ∣ (k - j) := by
          rw [Int.dvd_iff_emod_eq_zero]
          exact h
        exact hdiv
      have h4 : 0 < k - j := by omega
      exact Int.le_of_dvd (by omega) hdiv
    have h4 : π (p j) ≤ ((j : ℝ) + 1) * w := (hp j hj).2.2
    have h5 : π (p k) ≥ (k : ℝ) * w := (hp k hk).2.1
    have h6 : π (p k) - π (p j) ≥ ((k : ℝ) - (j : ℝ) - 1) * w := by
      have h61 : π (p k) ≥ (k : ℝ) * w := h5
      have h62 : π (p j) ≤ ((j : ℝ) + 1) * w := h4
      have h63 : π (p k) - π (p j) ≥ (k : ℝ) * w - (((j : ℝ) + 1) * w) := by
        exact sub_le_sub h61 h62
      have h64 : (k : ℝ) * w - (((j : ℝ) + 1) * w) = ((k : ℝ) - (j : ℝ) - 1) * w := by ring
      rw [h64] at h63
      exact h63
    have h7 : ((k : ℝ) - (j : ℝ) - 1) * w ≥ sep_scale := by
      have h8 : (k : ℝ) - (j : ℝ) ≥ 6 := by
        have h81 : (k : ℝ) - (j : ℝ) ≥ ((m : ℤ) : ℝ) := by exact_mod_cast h3
        have h82 : ((m : ℤ) : ℝ) = 6 := by norm_cast <;> norm_num [m]
        rw [h82] at h81 <;> exact h81
      have h9 : (k : ℝ) - (j : ℝ) - 1 ≥ 5 := by linarith
      have h10 : ((k : ℝ) - (j : ℝ) - 1) * w ≥ 5 * w :=
        mul_le_mul_of_nonneg_right h9 (by linarith)
      have h11 : 5 * w = sep_scale := by
        have h12 : w = sep_scale / 5 := by rfl
        rw [h12] <;> ring
      rw [h11] at h10
      exact h10
    have h10 : dist (p j) (p k) ≥ |π (p k) - π (p j)| := by
      have h11 : |inner ℝ (p k - p j) T.direction| ≤ ‖p k - p j‖ * ‖T.direction‖ :=
        abs_real_inner_le_norm (p k - p j) T.direction
      have h12 : π (p k) - π (p j) = inner ℝ (p k - p j) T.direction := by
        dsimp only [π]
        have h_sub : inner ℝ (p k - T.base) T.direction - inner ℝ (p j - T.base) T.direction =
            inner ℝ ((p k - T.base) - (p j - T.base)) T.direction := by
          rw [←inner_sub_left]
        rw [h_sub]
        have h2 : (p k - T.base) - (p j - T.base) = p k - p j :=
          sub_sub_sub_cancel_right (p k) (p j) T.base
        rw [h2]
      have h13 : ‖p k - p j‖ = dist (p j) (p k) := by
        rw [dist_eq_norm, norm_sub_rev]
      have h14 : |inner ℝ (p k - p j) T.direction| ≤ dist (p j) (p k) := by
        calc |inner ℝ (p k - p j) T.direction|
          ≤ ‖p k - p j‖ * ‖T.direction‖ := h11
        _ = ‖p k - p j‖ * 1 := by
          have h_unit : ‖T.direction‖ = 1 := hdir_unit
          congr 1
        _ = ‖p k - p j‖ := by ring
        _ = dist (p j) (p k) := by rw [h13]
      rw [h12]
      exact h14
    have h14 : π (p k) - π (p j) ≥ sep_scale := by linarith
    have h14_pos : 0 < π (p k) - π (p j) := by linarith [hsep_pos]
    have h15 : |π (p k) - π (p j)| ≥ sep_scale := by
      rw [abs_of_pos h14_pos]
      exact h14
    have h16 : dist (p j) (p k) ≥ sep_scale := by
      calc dist (p j) (p k)
        ≥ |π (p k) - π (p j)| := h10
      _ ≥ sep_scale := h15
    exact h16

  have h_card_lower2 : (J'.card : ℝ) ≥ 5 * V / (24 * delta^2 * sep_scale) := by
    have h10 : (J'.card : ℝ) ≥ (J.card : ℝ) / (m : ℝ) := hr
    have h11 : (J.card : ℝ) ≥ V / (4 * delta^2 * w) := h_card_lower
    have h12 : w = sep_scale / 5 := by rfl
    rw [h12] at h11
    have h13 : (m : ℝ) = 6 := by norm_num [m]
    rw [h13] at h10
    calc
      (J'.card : ℝ) ≥ (J.card : ℝ) / 6 := h10
      _ ≥ (V / (4 * delta^2 * (sep_scale / 5))) / 6 := by gcongr
      _ = 5 * V / (24 * delta^2 * sep_scale) := by
        field_simp [hdelta_pos.ne', hsep_pos.ne'] <;> ring

  let e : {x : ℤ // x ∈ J'} ≃ Fin J'.card := Finset.equivFin J'
  let p_seq : ℕ → Point3 := fun n =>
    if h : n < J'.card then p (e.symm ⟨n, h⟩).val else q
  refine ⟨p_seq, J'.card, h_card_lower2, ?_, ?_⟩
  · intro n hn
    have h5 : p_seq n = p (e.symm ⟨n, hn⟩).val := by
      dsimp only [p_seq]
      rw [dif_pos hn]
    rw [h5]
    exact (hp (e.symm ⟨n, hn⟩).val (e.symm ⟨n, hn⟩).property).1
  · intro n1 n2 hn1 hn2 hne
    let j1 : ℤ := (e.symm ⟨n1, hn1⟩).val
    let j2 : ℤ := (e.symm ⟨n2, hn2⟩).val
    have h5 : p_seq n1 = p j1 := by
      dsimp only [p_seq]
      rw [dif_pos hn1]
    have h6 : p_seq n2 = p j2 := by
      dsimp only [p_seq]
      rw [dif_pos hn2]
    rw [h5, h6]
    have h7 : j1 ≠ j2 := by
      intro h
      have h8 : (e.symm ⟨n1, hn1⟩) = (e.symm ⟨n2, hn2⟩) := by
        exact Subtype.ext h
      have h9 : (⟨n1, hn1⟩ : Fin J'.card) = (⟨n2, hn2⟩ : Fin J'.card) := by
        rw [←e.apply_symm_apply ⟨n1, hn1⟩, ←e.apply_symm_apply ⟨n2, hn2⟩, h8]
      have h10 : n1 = n2 := by
        exact congr_arg (fun (x : Fin J'.card) => x.val) h9
      exact hne h10
    exact h_sep j1 j2 (e.symm ⟨n1, hn1⟩).property (e.symm ⟨n2, hn2⟩).property h7

end Kakeya.Assouad
