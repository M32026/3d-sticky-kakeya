import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameters

/-!
# Same-height y-diameter bound for vertical-chart tubes

For any two points in a vertical-chart tube that share the same height
(z-coordinate), their y-coordinates differ by at most `6 * δ`.

This is a port of `tube_y_diameter_bound` from the compact projection-area
target, restated without `coordEquiv3` so it can be used by non-target modules.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- Any coordinate of a Euclidean vector is bounded by its norm. -/
lemma euclidean_coord_le_norm {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    |x k| ≤ ‖x‖ := by
  have h_sum_nonneg : 0 ≤ ∑ i : Fin n, (x i) ^ 2 := by positivity
  have h_norm_sq : ‖x‖ ^ 2 = ∑ i : Fin n, (x i) ^ 2 := by
    have h : ‖x‖ = Real.sqrt (∑ i : Fin n, (x i) ^ 2) := by
      simp [EuclideanSpace.norm_eq]
    rw [h, Real.sq_sqrt h_sum_nonneg]
  have h3 : (x k) ^ 2 ≤ ∑ i : Fin n, (x i) ^ 2 := by
    have h4 : ∀ i ∈ Finset.univ, 0 ≤ (x i) ^ 2 := by
      intro i _
      positivity
    exact Finset.single_le_sum h4 (Finset.mem_univ k)
  have h5 : (x k) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [h_norm_sq] at *
    exact h3
  have h6 : |x k| ^ 2 ≤ ‖x‖ ^ 2 := by
    have h7 : |x k| ^ 2 = (x k) ^ 2 := by rw [sq_abs]
    rw [h7]
    exact h5
  have h7 : 0 ≤ |x k| := by positivity
  have h8 : 0 ≤ ‖x‖ := by positivity
  nlinarith [sq_abs (x k)]

/--
Distance from a tube point at height `z` to the axis point at the same height.

The axis of tube `i` in the vertical chart is
`(a + c*z, b + d*z, z)`. Any point in the tube at height `z` is within
`3 * δ` of this axis point.
-/
lemma tubeCarrier_axisDistance
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (hδ : 0 ≤ δ) (hvert : IsInVerticalChart F) (i : Fin F.card)
    (p : Point3) (hp : p ∈ (F.tube i).carrier)
    (z : ℝ) (hz : p (2 : Fin 3) = z) :
    ‖p - point3 ((tubeParams i).a + (tubeParams i).c * z)
        ((tubeParams i).b + (tubeParams i).d * z) z‖ ≤ 3 * δ := by
  let T := F.tube i
  let base := T.base
  let dir := T.direction
  have hdir_unit : ‖dir‖ = 1 := T.direction_unit
  have hdz : (1 / 2 : ℝ) ≤ |dir (2 : Fin 3)| := hvert i
  have hdir2_ne_zero : dir (2 : Fin 3) ≠ 0 := by
    have hpos : 0 < |dir (2 : Fin 3)| := by linarith
    exact abs_ne_zero.mp hpos.ne'
  have h_seg_compact : IsCompact (unitSegment base dir) := by
    apply IsCompact.image isCompact_Icc
    exact continuous_const.add (continuous_id.smul continuous_const)
  have h1 : ∃ q : Point3, q ∈ unitSegment base dir ∧ dist p q ≤ δ := by
    have h_eq :
        (F.tube i).carrier =
          Metric.cthickening δ (unitSegment base dir) := by
      rfl
    rw [h_eq] at hp
    have h_bunion :
        Metric.cthickening δ (unitSegment base dir) =
          ⋃ x ∈ unitSegment base dir, Metric.closedBall x δ :=
      h_seg_compact.cthickening_eq_biUnion_closedBall hδ
    rw [h_bunion] at hp
    simpa [Set.mem_iUnion, Metric.mem_closedBall] using hp
  rcases h1 with ⟨q, hq_seg, hdist⟩
  have h2 : ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ base + t • dir = q := by
    simpa [unitSegment, Set.mem_image] using hq_seg
  rcases h2 with ⟨t, _ht, hq_eq⟩
  let z_q := q (2 : Fin 3)
  have hq_eq' : q = base + t • dir := hq_eq.symm
  have hz_q : z_q = base (2 : Fin 3) + t * dir (2 : Fin 3) := by
    have h1 : z_q = q (2 : Fin 3) := by rfl
    rw [h1, hq_eq']
    simp
  have h3 : |z - z_q| ≤ δ := by
    have h4 :
        |p (2 : Fin 3) - q (2 : Fin 3)| ≤ ‖p - q‖ :=
      euclidean_coord_le_norm (p - q) (2 : Fin 3)
    have h5 : ‖p - q‖ = dist p q := by rfl
    rw [h5] at h4
    have h6 :
        |z - z_q| = |p (2 : Fin 3) - q (2 : Fin 3)| := by
      rw [hz]
    rw [h6]
    exact h4.trans hdist
  let s := (z - base (2 : Fin 3)) / dir (2 : Fin 3)
  let q_z := base + s • dir
  have hq_z_coord2 : q_z (2 : Fin 3) = z := by
    have h :
        q_z (2 : Fin 3) =
          base (2 : Fin 3) + s * dir (2 : Fin 3) := by
      simp [q_z]
    rw [h]
    dsimp only [s]
    field_simp [hdir2_ne_zero]
    ring
  have hq_z_coord0 :
      q_z (0 : Fin 3) =
        (tubeParams i).a + (tubeParams i).c * z := by
    have h :
        q_z (0 : Fin 3) =
          base (0 : Fin 3) + s * dir (0 : Fin 3) := by
      simp [q_z]
    rw [h]
    have ha :
        (tubeParams i).a =
          base 0 - base 2 * dir 0 / dir 2 := by
      rfl
    have hc : (tubeParams i).c = dir 0 / dir 2 := by
      rfl
    rw [ha, hc]
    dsimp only [s]
    field_simp [hdir2_ne_zero]
    ring
  have hq_z_coord1 :
      q_z (1 : Fin 3) =
        (tubeParams i).b + (tubeParams i).d * z := by
    have h :
        q_z (1 : Fin 3) =
          base (1 : Fin 3) + s * dir (1 : Fin 3) := by
      simp [q_z]
    rw [h]
    have hb :
        (tubeParams i).b =
          base 1 - base 2 * dir 1 / dir 2 := by
      rfl
    have hd : (tubeParams i).d = dir 1 / dir 2 := by
      rfl
    rw [hb, hd]
    dsimp only [s]
    field_simp [hdir2_ne_zero]
    ring
  have hq_z_eq :
      q_z =
        point3 ((tubeParams i).a + (tubeParams i).c * z)
          ((tubeParams i).b + (tubeParams i).d * z) z := by
    ext k
    fin_cases k
    · simpa [point3] using hq_z_coord0
    · simpa [point3] using hq_z_coord1
    · simpa [point3] using hq_z_coord2
  have h_st_diff :
      s - t = (z - z_q) / dir (2 : Fin 3) := by
    dsimp only [s]
    rw [hz_q]
    field_simp [hdir2_ne_zero]
    ring
  have h_qz_q_dist : ‖q_z - q‖ ≤ 2 * δ := by
    have h7 : q_z - q = (s - t) • dir := by
      rw [hq_eq']
      have h9 :
          (base + s • dir) - (base + t • dir) =
            s • dir - t • dir := by
        abel
      rw [h9, ← sub_smul]
    rw [h7]
    have h8 : ‖(s - t) • dir‖ = |s - t| * ‖dir‖ := by
      rw [norm_smul]
      have h9 : ‖s - t‖ = |s - t| := by
        simp [Real.norm_eq_abs]
      rw [h9]
    rw [h8, hdir_unit]
    have h9 :
        |s - t| = |z - z_q| / |dir (2 : Fin 3)| := by
      rw [h_st_diff, abs_div]
    rw [h9]
    have h10 :
        |z - z_q| / |dir (2 : Fin 3)| ≤ δ / (1 / 2 : ℝ) := by
      gcongr
    linarith
  have h13 : ‖p - q_z‖ ≤ dist p q + ‖q_z - q‖ := by
    have h_eq : p - q_z = (p - q) + (q - q_z) := by
      abel
    rw [h_eq]
    have h :
        ‖(p - q) + (q - q_z)‖ ≤ ‖p - q‖ + ‖q - q_z‖ :=
      norm_add_le _ _
    have h2 : ‖q - q_z‖ = ‖q_z - q‖ := norm_sub_rev q q_z
    rw [h2] at h
    exact h
  have h14 : ‖p - q_z‖ ≤ 3 * δ := by
    calc
      ‖p - q_z‖ ≤ dist p q + ‖q_z - q‖ := h13
      _ ≤ δ + 2 * δ := by gcongr
      _ = 3 * δ := by ring
  rw [hq_z_eq] at h14
  exact h14

/--
Same-height y-diameter bound: two points in a vertical-chart tube at the
same height `z` have y-coordinates differing by at most `6 * δ`.
-/
lemma tube_same_height_y_diameter
    {δ : ℝ} (hδ : 0 < δ)
    {F : Kakeya.Streamlined.TubeFamily δ}
    (hvert : IsInVerticalChart F)
    (i : Fin F.card)
    {p1 p2 : Point3}
    (hp1 : p1 ∈ (F.tube i).carrier)
    (hp2 : p2 ∈ (F.tube i).carrier)
    {z : ℝ} (hz1 : p1 (2 : Fin 3) = z)
    (hz2 : p2 (2 : Fin 3) = z) :
    |p1 (1 : Fin 3) - p2 (1 : Fin 3)| ≤ 6 * δ := by
  let axisPoint : Point3 :=
    point3 ((tubeParams i).a + (tubeParams i).c * z)
      ((tubeParams i).b + (tubeParams i).d * z) z
  have hdist1 : ‖p1 - axisPoint‖ ≤ 3 * δ :=
    tubeCarrier_axisDistance hδ.le hvert i p1 hp1 z hz1
  have hdist2 : ‖p2 - axisPoint‖ ≤ 3 * δ :=
    tubeCarrier_axisDistance hδ.le hvert i p2 hp2 z hz2
  have hy1 : |p1 1 - axisPoint 1| ≤ 3 * δ :=
    (euclidean_coord_le_norm (p1 - axisPoint) 1).trans hdist1
  have hy2 : |p2 1 - axisPoint 1| ≤ 3 * δ :=
    (euclidean_coord_le_norm (p2 - axisPoint) 1).trans hdist2
  have h_comm : |axisPoint 1 - p2 1| = |p2 1 - axisPoint 1| := by
    have h : axisPoint 1 - p2 1 = -(p2 1 - axisPoint 1) := by ring
    rw [h, abs_neg]
  calc
    |p1 1 - p2 1|
        = |(p1 1 - axisPoint 1) + (axisPoint 1 - p2 1)| := by ring_nf
    _ ≤ |p1 1 - axisPoint 1| + |axisPoint 1 - p2 1| := abs_add_le _ _
    _ = |p1 1 - axisPoint 1| + |p2 1 - axisPoint 1| := by rw [h_comm]
    _ ≤ 3 * δ + 3 * δ := add_le_add hy1 hy2
    _ = 6 * δ := by ring

end Kakeya.Assouad
