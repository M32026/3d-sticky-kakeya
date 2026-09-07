import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Prism geometry lemmas for LargeSlopeStep4Witness

Geometric core:
1. A tube in the vertical chart has its slab intersection contained in one
   `tubeSegmentCarrier` of length `sqrt(rho)`.
2. The scalar projection of the slab intersection onto any unit direction has
   diameter at most `2*(b-a) + 6*delta`.
3. A set of diameter `< 2*W` meets at most three pairwise-disjoint intervals
   of length `>= W`.
-/

noncomputable section

open Metric Set

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- Coordinate absolute value is bounded by Euclidean norm. -/
lemma coord_abs_le_norm (x : Point3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have h : |inner ℝ x (EuclideanSpace.single i (1 : ℝ))| ≤ ‖x‖ * ‖(EuclideanSpace.single i (1 : ℝ))‖ :=
    abs_real_inner_le_norm x (EuclideanSpace.single i (1 : ℝ))
  have h2 : inner ℝ x (EuclideanSpace.single i (1 : ℝ)) = x i := by
    rw [EuclideanSpace.inner_single_right] <;> simp
  have h3 : ‖(EuclideanSpace.single i (1 : ℝ))‖ = 1 := by
    rw [PiLp.norm_single] <;> norm_num
  rw [h2, h3] at h
  linarith

/-- Extract a parameter witness from tube carrier membership. -/
lemma tube_carrier_witness {delta : ℝ} (hdelta : 0 < delta) {T : Kakeya.DeltaTube delta} {x : Point3}
    (hx : x ∈ T.carrier) :
    ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ dist x (T.base + t • T.direction) ≤ delta := by
  have hseg_compact : IsCompact (unitSegment T.base T.direction) :=
    isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  have hcthick : T.carrier = ⋃ p ∈ unitSegment T.base T.direction, Metric.closedBall p delta :=
    hseg_compact.cthickening_eq_biUnion_closedBall hdelta.le
  rw [hcthick] at hx
  simpa [Set.mem_iUnion, Metric.mem_closedBall, unitSegment, Set.mem_image] using hx

/-- Show membership in tubeSegmentCarrier from a parameter witness. -/
lemma mem_tube_segment {delta start rho : ℝ} {base direction x : Point3} {t : ℝ}
    (ht : t ∈ Set.Icc start (start + Real.sqrt rho))
    (hdist : dist x (base + t • direction) ≤ delta)
    (hdelta : 0 < delta) :
    x ∈ tubeSegmentCarrier delta base direction start rho := by
  have hseg_compact : IsCompact ((fun t : ℝ => base + t • direction) '' Set.Icc start (start + Real.sqrt rho)) :=
    isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  have hcthick : tubeSegmentCarrier delta base direction start rho =
      ⋃ p ∈ ((fun t : ℝ => base + t • direction) '' Set.Icc start (start + Real.sqrt rho)),
        Metric.closedBall p delta :=
    hseg_compact.cthickening_eq_biUnion_closedBall hdelta.le
  rw [hcthick]
  have h_im : (base + t • direction) ∈ (fun t : ℝ => base + t • direction) '' Set.Icc start (start + Real.sqrt rho) :=
    ⟨t, ht, rfl⟩
  exact Set.mem_iUnion₂.mpr ⟨base + t • direction, h_im, by simpa [Metric.mem_closedBall] using hdist⟩

/--
A tube in the vertical chart has its intersection with a horizontal slab
contained in a single `tubeSegmentCarrier` of length `Real.sqrt rho`,
provided `2 * (b - a + 2 * delta) <= Real.sqrt rho`.
-/
lemma tube_slab_in_segment
    {delta a b rho : ℝ}
    (hdelta : 0 < delta) (hab : a < b) (hrho : 0 < rho)
    (h_len : 2 * (b - a + 2 * delta) ≤ Real.sqrt rho)
    {T : Kakeya.DeltaTube delta}
    (hvert : (1 / 2 : ℝ) ≤ |T.direction (2 : Fin 3)|) :
    ∃ start : ℝ,
      T.carrier ∩ horizontalSlab a b ⊆
        tubeSegmentCarrier delta T.base T.direction start rho := by
  set d2 : ℝ := T.direction (2 : Fin 3) with hd2_def
  have h_d2_ne_zero : d2 ≠ 0 := by
    by_contra h
    have h' : |d2| = 0 := by rw [h] <;> simp
    rw [h'] at hvert
    norm_num at hvert

  by_cases hpos : 0 < d2
  · -- Case d2 > 0
    let start := (a - delta - T.base (2 : Fin 3)) / d2
    use start
    intro x hx
    rcases tube_carrier_witness hdelta hx.1 with ⟨t, ht, hdist⟩
    set y := T.base + t • T.direction with hy_def
    have h4 : ‖x - y‖ ≤ delta := by simpa [dist_eq_norm] using hdist
    have h5 : |x (2 : Fin 3) - y (2 : Fin 3)| ≤ delta := by
      have h6 : |x (2 : Fin 3) - y (2 : Fin 3)| ≤ ‖x - y‖ := coord_abs_le_norm (x - y) 2
      linarith
    have h7 : y (2 : Fin 3) = T.base (2 : Fin 3) + t * d2 := by
      simp [hy_def, hd2_def] <;> abel
    have h2 : x (2 : Fin 3) ∈ Set.Icc a b := hx.2
    have h8 : a - delta ≤ y (2 : Fin 3) := by
      rw [h7] <;> linarith [h2.1, abs_le.mp h5]
    have h9 : y (2 : Fin 3) ≤ b + delta := by
      rw [h7] <;> linarith [h2.2, abs_le.mp h5]
    have h10 : start ≤ t := by
      dsimp only [start]
      have h11 : a - delta - T.base (2 : Fin 3) ≤ t * d2 := by
        rw [h7] at h8 <;> linarith
      have h : (a - delta - T.base (2 : Fin 3)) / d2 ≤ (t * d2) / d2 := by
        gcongr
      have h2' : (t * d2) / d2 = t := by
        field_simp [hpos.ne'] <;> ring
      rw [h2'] at h
      exact h
    have h12 : t - start ≤ 2 * (b - a + 2 * delta) := by
      dsimp only [start]
      have h13 : t * d2 - (a - delta - T.base (2 : Fin 3)) ≤ b - a + 2 * delta := by
        rw [h7] at h9 <;> linarith
      have h14 : 0 < d2 := hpos
      have h15 : (t * d2 - (a - delta - T.base (2 : Fin 3))) / d2 ≤ (b - a + 2 * delta) / d2 := by
        gcongr
      have h16 : (t * d2 - (a - delta - T.base (2 : Fin 3))) / d2 = t - start := by
        dsimp only [start]
        field_simp [hpos.ne'] <;> ring
      rw [h16] at h15
      have h17 : (b - a + 2 * delta) / d2 ≤ 2 * (b - a + 2 * delta) := by
        have h18 : 1 / d2 ≤ 2 := by
          have h19 : |d2| = d2 := abs_of_pos hpos
          rw [h19] at hvert
          calc 1 / d2 ≤ 1 / (1 / 2 : ℝ) := by gcongr
            _ = 2 := by norm_num
        have h20 : 0 ≤ b - a + 2 * delta := by linarith
        calc (b - a + 2 * delta) / d2
            = (b - a + 2 * delta) * (1 / d2) := by ring
          _ ≤ (b - a + 2 * delta) * 2 := by gcongr
          _ = 2 * (b - a + 2 * delta) := by ring
      linarith
    have h20 : t ≤ start + Real.sqrt rho := by linarith
    have h21 : t ∈ Set.Icc start (start + Real.sqrt rho) := ⟨h10, h20⟩
    exact mem_tube_segment h21 hdist hdelta

  · -- Case d2 < 0
    have hneg : d2 < 0 := by
      by_contra h
      have : d2 = 0 := by linarith
      exact h_d2_ne_zero this
    let start := (b + delta - T.base (2 : Fin 3)) / d2
    use start
    intro x hx
    rcases tube_carrier_witness hdelta hx.1 with ⟨t, ht, hdist⟩
    set y := T.base + t • T.direction with hy_def
    have h4 : ‖x - y‖ ≤ delta := by simpa [dist_eq_norm] using hdist
    have h5 : |x (2 : Fin 3) - y (2 : Fin 3)| ≤ delta := by
      have h6 : |x (2 : Fin 3) - y (2 : Fin 3)| ≤ ‖x - y‖ := coord_abs_le_norm (x - y) 2
      linarith
    have h7 : y (2 : Fin 3) = T.base (2 : Fin 3) + t * d2 := by
      simp [hy_def, hd2_def] <;> abel
    have h2 : x (2 : Fin 3) ∈ Set.Icc a b := hx.2
    have h8 : a - delta ≤ y (2 : Fin 3) := by
      rw [h7] <;> linarith [h2.1, abs_le.mp h5]
    have h9 : y (2 : Fin 3) ≤ b + delta := by
      rw [h7] <;> linarith [h2.2, abs_le.mp h5]
    have h10 : start ≤ t := by
      dsimp only [start]
      have h11 : t * d2 ≤ b + delta - T.base (2 : Fin 3) := by
        rw [h7] at h9 <;> linarith
      have h : (b + delta - T.base (2 : Fin 3)) / d2 ≤ t := by
        rw [div_le_iff_of_neg hneg]
        <;> linarith
      exact h
    have h_abs : |d2| = -d2 := abs_of_neg hneg
    have h12 : t - start ≤ 2 * (b - a + 2 * delta) := by
      dsimp only [start]
      have h13 : a - delta - T.base (2 : Fin 3) ≤ t * d2 := by
        rw [h7] at h8 <;> linarith
      have h14 : t - start = (-(t * d2 - (b + delta - T.base (2 : Fin 3)))) / |d2| := by
        dsimp only [start]
        rw [h_abs]
        field_simp [hneg.ne] <;> ring
      rw [h14]
      have h15 : -(t * d2 - (b + delta - T.base (2 : Fin 3))) ≤ b - a + 2 * delta := by linarith
      have h16 : 0 ≤ |d2| := by positivity
      have h17 : (-(t * d2 - (b + delta - T.base (2 : Fin 3)))) / |d2| ≤ (b - a + 2 * delta) / |d2| := by
        gcongr
      have h18 : (b - a + 2 * delta) / |d2| ≤ 2 * (b - a + 2 * delta) := by
        have h19 : 1 / |d2| ≤ 2 := by
          calc 1 / |d2| ≤ 1 / (1 / 2 : ℝ) := by gcongr
            _ = 2 := by norm_num
        have h20 : 0 ≤ b - a + 2 * delta := by linarith
        calc (b - a + 2 * delta) / |d2|
            = (b - a + 2 * delta) * (1 / |d2|) := by ring
          _ ≤ (b - a + 2 * delta) * 2 := by gcongr
          _ = 2 * (b - a + 2 * delta) := by ring
      linarith
    have h20 : t ≤ start + Real.sqrt rho := by linarith
    have h21 : t ∈ Set.Icc start (start + Real.sqrt rho) := ⟨h10, h20⟩
    exact mem_tube_segment h21 hdist hdelta

/--
The scalar projection of a tube's slab intersection onto any unit direction
has diameter at most `2 * (b - a) + 6 * delta`.
-/
lemma tube_slab_projection_diam
    {delta a b : ℝ}
    (hdelta : 0 < delta) (hab : a < b)
    {T : Kakeya.DeltaTube delta}
    (hvert : (1 / 2 : ℝ) ≤ |T.direction (2 : Fin 3)|)
    {v : Point3} (hv : ‖v‖ = 1) :
    ∀ (x y : Point3), x ∈ T.carrier ∩ horizontalSlab a b →
      y ∈ T.carrier ∩ horizontalSlab a b →
      |inner ℝ x v - inner ℝ y v| ≤ 2 * (b - a) + 6 * delta := by
  set d2 : ℝ := T.direction (2 : Fin 3) with hd2_def
  have h_d2_ne_zero : d2 ≠ 0 := by
    by_contra h
    have h' : |d2| = 0 := by rw [h] <;> simp
    rw [h'] at hvert
    norm_num at hvert

  intro x y hx hy
  rcases tube_carrier_witness hdelta hx.1 with ⟨tx, _, hdx⟩
  rcases tube_carrier_witness hdelta hy.1 with ⟨ty, _, hdy⟩
  set ax := T.base + tx • T.direction with hax_def
  set ay := T.base + ty • T.direction with hay_def
  have hnx : ‖x - ax‖ ≤ delta := by simpa [dist_eq_norm] using hdx
  have hny : ‖y - ay‖ ≤ delta := by simpa [dist_eq_norm] using hdy
  have h_x2 : x (2 : Fin 3) ∈ Set.Icc a b := hx.2
  have h_y2 : y (2 : Fin 3) ∈ Set.Icc a b := hy.2
  have h_ax2 : |x (2 : Fin 3) - ax (2 : Fin 3)| ≤ delta := by
    have h : |x (2 : Fin 3) - ax (2 : Fin 3)| ≤ ‖x - ax‖ := coord_abs_le_norm (x - ax) 2
    linarith
  have h_ay2 : |y (2 : Fin 3) - ay (2 : Fin 3)| ≤ delta := by
    have h : |y (2 : Fin 3) - ay (2 : Fin 3)| ≤ ‖y - ay‖ := coord_abs_le_norm (y - ay) 2
    linarith
  have h_ax2_val : ax (2 : Fin 3) = T.base (2 : Fin 3) + tx * d2 := by
    simp [hax_def, hd2_def] <;> abel
  have h_ay2_val : ay (2 : Fin 3) = T.base (2 : Fin 3) + ty * d2 := by
    simp [hay_def, hd2_def] <;> abel
  have h_ax_range : ax (2 : Fin 3) ∈ Set.Icc (a - delta) (b + delta) := by
    rw [h_ax2_val] <;> constructor <;> linarith [h_x2.1, h_x2.2, abs_le.mp h_ax2]
  have h_ay_range : ay (2 : Fin 3) ∈ Set.Icc (a - delta) (b + delta) := by
    rw [h_ay2_val] <;> constructor <;> linarith [h_y2.1, h_y2.2, abs_le.mp h_ay2]
  have h_diff : |ax (2 : Fin 3) - ay (2 : Fin 3)| ≤ b - a + 2 * delta := by
    rw [abs_le] <;> constructor <;> linarith [h_ax_range.1, h_ax_range.2, h_ay_range.1, h_ay_range.2]
  have h_diff2 : |(tx - ty) * d2| ≤ b - a + 2 * delta := by
    have h_eq : ax (2 : Fin 3) - ay (2 : Fin 3) = (tx - ty) * d2 := by
      rw [h_ax2_val, h_ay2_val] <;> ring
    rw [h_eq] at h_diff
    exact h_diff
  have h_abs_mul : |(tx - ty) * d2| = |tx - ty| * |d2| := by rw [abs_mul]
  rw [h_abs_mul] at h_diff2
  have h_tx_ty : |tx - ty| ≤ 2 * (b - a + 2 * delta) := by
    have h_pos : 0 < |d2| := abs_pos.mpr h_d2_ne_zero
    have h : |tx - ty| * |d2| ≤ b - a + 2 * delta := h_diff2
    have h2 : |tx - ty| ≤ (b - a + 2 * delta) / |d2| := by
      calc |tx - ty|
          = (|tx - ty| * |d2|) / |d2| := by field_simp [h_pos.ne'] <;> ring
        _ ≤ (b - a + 2 * delta) / |d2| := by gcongr
    have h3 : (b - a + 2 * delta) / |d2| ≤ 2 * (b - a + 2 * delta) := by
      have h4 : 1 / |d2| ≤ 2 := by
        calc 1 / |d2| ≤ 1 / (1 / 2 : ℝ) := by gcongr
          _ = 2 := by norm_num
      have h5 : 0 ≤ b - a + 2 * delta := by linarith
      calc (b - a + 2 * delta) / |d2|
          = (b - a + 2 * delta) * (1 / |d2|) := by ring
        _ ≤ (b - a + 2 * delta) * 2 := by gcongr
        _ = 2 * (b - a + 2 * delta) := by ring
    linarith
  have h_inner1 : |inner ℝ (x - ax) v| ≤ delta := by
    calc |inner ℝ (x - ax) v|
        ≤ ‖x - ax‖ * ‖v‖ := abs_real_inner_le_norm (x - ax) v
      _ = ‖x - ax‖ := by rw [hv] <;> ring
      _ ≤ delta := hnx
  have h_inner2 : |inner ℝ (y - ay) v| ≤ delta := by
    calc |inner ℝ (y - ay) v|
        ≤ ‖y - ay‖ * ‖v‖ := abs_real_inner_le_norm (y - ay) v
      _ = ‖y - ay‖ := by rw [hv] <;> ring
      _ ≤ delta := hny
  have h_inner3 : |inner ℝ (ax - ay) v| ≤ |tx - ty| := by
    have h_eq : ax - ay = (tx - ty) • T.direction := by
      simp [hax_def, hay_def, sub_smul] <;> abel
    rw [h_eq]
    have h : inner ℝ ((tx - ty) • T.direction) v = (tx - ty) * inner ℝ T.direction v := by
      simp [inner_smul_left]
    rw [h]
    have h_dir : |inner ℝ T.direction v| ≤ 1 := by
      calc |inner ℝ T.direction v|
          ≤ ‖T.direction‖ * ‖v‖ := abs_real_inner_le_norm T.direction v
        _ = 1 := by rw [T.direction_unit, hv] <;> ring
    have h_goal : |(tx - ty) * inner ℝ T.direction v| ≤ |tx - ty| := by
      calc |(tx - ty) * inner ℝ T.direction v|
          = |tx - ty| * |inner ℝ T.direction v| := by rw [abs_mul]
        _ ≤ |tx - ty| * 1 := by gcongr
        _ = |tx - ty| := by ring
    exact h_goal
  have h_decomp : inner ℝ x v - inner ℝ y v =
      inner ℝ (x - ax) v + inner ℝ (ax - ay) v - inner ℝ (y - ay) v := by
    have h_eq : x - y = (x - ax) + (ax - ay) + (ay - y) := by abel
    have h1 : inner ℝ x v - inner ℝ y v = inner ℝ (x - y) v := by
      rw [← inner_sub_left] <;> ring
    rw [h1, h_eq]
    have h2 : inner ℝ ((x - ax) + (ax - ay) + (ay - y)) v =
        inner ℝ (x - ax) v + inner ℝ (ax - ay) v + inner ℝ (ay - y) v := by
      have h3 : inner ℝ ((x - ax) + (ax - ay) + (ay - y)) v =
          inner ℝ ((x - ax) + (ax - ay)) v + inner ℝ (ay - y) v := by
        rw [inner_add_left]
      rw [h3]
      have h4 : inner ℝ ((x - ax) + (ax - ay)) v =
          inner ℝ (x - ax) v + inner ℝ (ax - ay) v := by
        rw [inner_add_left]
      rw [h4] <;> ring
    rw [h2]
    have h5 : inner ℝ (ay - y) v = -inner ℝ (y - ay) v := by
      have h6 : inner ℝ (ay - y) v = inner ℝ (-(y - ay)) v := by rw [neg_sub]
      rw [h6, inner_neg_left] <;> ring
    rw [h5] <;> ring
  rw [h_decomp]
  have h_tri : |inner ℝ (x - ax) v + inner ℝ (ax - ay) v - inner ℝ (y - ay) v| ≤
      |inner ℝ (x - ax) v| + |inner ℝ (ax - ay) v| + |inner ℝ (y - ay) v| := by
    have h1 : |inner ℝ (x - ax) v + inner ℝ (ax - ay) v - inner ℝ (y - ay) v| ≤
        |inner ℝ (x - ax) v + inner ℝ (ax - ay) v| + |inner ℝ (y - ay) v| :=
      abs_sub _ _
    have h2 : |inner ℝ (x - ax) v + inner ℝ (ax - ay) v| ≤
        |inner ℝ (x - ax) v| + |inner ℝ (ax - ay) v| := abs_add_le _ _
    linarith
  linarith [h_inner1, h_inner2, h_inner3, h_tx_ty]

/-- Helper: disjoint nonempty intervals cannot share a point. -/
private lemma disjoint_no_point {a b c d : ℝ}
    (h_disj : Disjoint (Set.Icc a b) (Set.Icc c d))
    {x : ℝ} (hx1 : x ∈ Set.Icc a b) (hx2 : x ∈ Set.Icc c d) : False := by
  have h_empty : (Set.Icc a b ∩ Set.Icc c d) = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp h_disj
  have h_nonempty : (Set.Icc a b ∩ Set.Icc c d).Nonempty := ⟨x, hx1, hx2⟩
  rw [h_empty] at h_nonempty
  simpa using h_nonempty

/--
If `a < c` and `Icc a b` is disjoint from `Icc c d`, then `b ≤ c`.
Proof: if `c < b`, then `c` belongs to both intervals.
-/
private lemma disjoint_left_endpoint {a b c d : ℝ}
    (h_ab : a ≤ b) (h_cd : c ≤ d)
    (h_ac : a < c)
    (h_disj : Disjoint (Set.Icc a b) (Set.Icc c d)) :
    b ≤ c := by
  by_contra h
  have h' : c < b := by linarith
  have h1 : c ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  have h2 : c ∈ Set.Icc c d := ⟨by linarith, h_cd⟩
  exact disjoint_no_point h_disj h1 h2

/--
If three pairwise-disjoint closed intervals each have length `≥ W`, and points
`p1,p2,p3` lie in them respectively, then some pair of points is at least `W` apart.
-/
private lemma three_points_diam {W : ℝ} (hW : 0 < W)
    {a1 b1 a2 b2 a3 b3 : ℝ}
    (h_ab1 : a1 ≤ b1) (h_ab2 : a2 ≤ b2) (h_ab3 : a3 ≤ b3)
    (hL1 : b1 - a1 ≥ W) (hL2 : b2 - a2 ≥ W) (hL3 : b3 - a3 ≥ W)
    (h_disj12 : Disjoint (Set.Icc a1 b1) (Set.Icc a2 b2))
    (h_disj13 : Disjoint (Set.Icc a1 b1) (Set.Icc a3 b3))
    (h_disj23 : Disjoint (Set.Icc a2 b2) (Set.Icc a3 b3))
    {p1 p2 p3 : ℝ}
    (hp1 : p1 ∈ Set.Icc a1 b1)
    (hp2 : p2 ∈ Set.Icc a2 b2)
    (hp3 : p3 ∈ Set.Icc a3 b3) :
    W ≤ |p1 - p2| ∨ W ≤ |p1 - p3| ∨ W ≤ |p2 - p3| := by
  have h_ne12 : a1 ≠ a2 := by
    intro h
    have h4 : a1 ∈ Set.Icc a1 b1 := ⟨by linarith, h_ab1⟩
    have h5 : a1 ∈ Set.Icc a2 b2 := by
      have h7 : a2 ≤ a1 := by linarith
      have h8 : a1 ≤ b2 := by linarith
      exact ⟨h7, h8⟩
    exact disjoint_no_point h_disj12 h4 h5
  have h_ne13 : a1 ≠ a3 := by
    intro h
    have h4 : a1 ∈ Set.Icc a1 b1 := ⟨by linarith, h_ab1⟩
    have h5 : a1 ∈ Set.Icc a3 b3 := by
      have h7 : a3 ≤ a1 := by linarith
      have h8 : a1 ≤ b3 := by linarith
      exact ⟨h7, h8⟩
    exact disjoint_no_point h_disj13 h4 h5
  have h_ne23 : a2 ≠ a3 := by
    intro h
    have h4 : a2 ∈ Set.Icc a2 b2 := ⟨by linarith, h_ab2⟩
    have h5 : a2 ∈ Set.Icc a3 b3 := by
      have h7 : a3 ≤ a2 := by linarith
      have h8 : a2 ≤ b3 := by linarith
      exact ⟨h7, h8⟩
    exact disjoint_no_point h_disj23 h4 h5
  have h_cases :
      (a1 < a2 ∧ a2 < a3) ∨ (a1 < a3 ∧ a3 < a2) ∨
      (a2 < a1 ∧ a1 < a3) ∨ (a2 < a3 ∧ a3 < a1) ∨
      (a3 < a1 ∧ a1 < a2) ∨ (a3 < a2 ∧ a2 < a1) := by
    rcases lt_trichotomy a1 a2 with (h12 | h12 | h12) <;>
      rcases lt_trichotomy a1 a3 with (h13 | h13 | h13) <;>
        rcases lt_trichotomy a2 a3 with (h23 | h23 | h23) <;> tauto
  rcases h_cases with (h | h | h | h | h | h)
  · -- a1 < a2 < a3: p1 and p3 are W apart
    have h_b12 : b1 ≤ a2 := disjoint_left_endpoint h_ab1 h_ab2 h.1 h_disj12
    have h_b23 : b2 ≤ a3 := disjoint_left_endpoint h_ab2 h_ab3 h.2 h_disj23
    have h_main : p3 - p1 ≥ W := by
      have h1 : p1 ≤ b1 := hp1.2
      have h2 : b1 ≤ a2 := h_b12
      have h3 : a2 ≤ p2 := hp2.1
      have h4 : p2 ≤ b2 := hp2.2
      have h5 : b2 ≤ a3 := h_b23
      have h6 : a3 ≤ p3 := hp3.1
      linarith [hL2]
    have h_nonneg : 0 ≤ p3 - p1 := by linarith
    have h_abs : |p3 - p1| = p3 - p1 := abs_of_nonneg h_nonneg
    have h_goal : W ≤ |p1 - p3| := by
      have h_eq : |p1 - p3| = |p3 - p1| := by
        have h : p1 - p3 = -(p3 - p1) := by ring
        rw [h, abs_neg]
      rw [h_eq, h_abs] <;> linarith
    exact Or.inr (Or.inl h_goal)
  · -- a1 < a3 < a2: p1 and p2 are W apart
    have h_b13 : b1 ≤ a3 := disjoint_left_endpoint h_ab1 h_ab3 h.1 h_disj13
    have h_b32 : b3 ≤ a2 := disjoint_left_endpoint h_ab3 h_ab2 h.2 h_disj23.symm
    have h_main : p2 - p1 ≥ W := by
      have h1 : p1 ≤ b1 := hp1.2
      have h2 : b1 ≤ a3 := h_b13
      have h3 : a3 ≤ p3 := hp3.1
      have h4 : p3 ≤ b3 := hp3.2
      have h5 : b3 ≤ a2 := h_b32
      have h6 : a2 ≤ p2 := hp2.1
      linarith [hL3]
    have h_nonneg : 0 ≤ p2 - p1 := by linarith
    have h_abs : |p2 - p1| = p2 - p1 := abs_of_nonneg h_nonneg
    have h_goal : W ≤ |p1 - p2| := by
      have h_eq : |p1 - p2| = |p2 - p1| := by
        have h : p1 - p2 = -(p2 - p1) := by ring
        rw [h, abs_neg]
      rw [h_eq, h_abs] <;> linarith
    exact Or.inl h_goal
  · -- a2 < a1 < a3: p2 and p3 are W apart
    have h_b21 : b2 ≤ a1 := disjoint_left_endpoint h_ab2 h_ab1 h.1 h_disj12.symm
    have h_b13 : b1 ≤ a3 := disjoint_left_endpoint h_ab1 h_ab3 h.2 h_disj13
    have h_main : p3 - p2 ≥ W := by
      have h1 : p2 ≤ b2 := hp2.2
      have h2 : b2 ≤ a1 := h_b21
      have h3 : a1 ≤ p1 := hp1.1
      have h4 : p1 ≤ b1 := hp1.2
      have h5 : b1 ≤ a3 := h_b13
      have h6 : a3 ≤ p3 := hp3.1
      linarith [hL1]
    have h_nonneg : 0 ≤ p3 - p2 := by linarith
    have h_abs : |p3 - p2| = p3 - p2 := abs_of_nonneg h_nonneg
    have h_goal0 : W ≤ |p3 - p2| := by rw [h_abs]; linarith
    have h_goal : W ≤ |p2 - p3| := by
      have h_eq : |p2 - p3| = |p3 - p2| := by
        have h : p2 - p3 = -(p3 - p2) := by ring
        rw [h, abs_neg]
      rw [h_eq]; exact h_goal0
    exact Or.inr (Or.inr h_goal)
  · -- a2 < a3 < a1: p1 and p2 are W apart
    have h_b23 : b2 ≤ a3 := disjoint_left_endpoint h_ab2 h_ab3 h.1 h_disj23
    have h_b31 : b3 ≤ a1 := disjoint_left_endpoint h_ab3 h_ab1 h.2 h_disj13.symm
    have h_main : p1 - p2 ≥ W := by
      have h1 : p2 ≤ b2 := hp2.2
      have h2 : b2 ≤ a3 := h_b23
      have h3 : a3 ≤ p3 := hp3.1
      have h4 : p3 ≤ b3 := hp3.2
      have h5 : b3 ≤ a1 := h_b31
      have h6 : a1 ≤ p1 := hp1.1
      linarith [hL3]
    have h_nonneg : 0 ≤ p1 - p2 := by linarith
    have h_abs : |p1 - p2| = p1 - p2 := abs_of_nonneg h_nonneg
    have h_goal : W ≤ |p1 - p2| := by rw [h_abs]; linarith
    exact Or.inl h_goal
  · -- a3 < a1 < a2: p2 and p3 are W apart
    have h_b31 : b3 ≤ a1 := disjoint_left_endpoint h_ab3 h_ab1 h.1 h_disj13.symm
    have h_b12 : b1 ≤ a2 := disjoint_left_endpoint h_ab1 h_ab2 h.2 h_disj12
    have h_main : p2 - p3 ≥ W := by
      have h1 : p3 ≤ b3 := hp3.2
      have h2 : b3 ≤ a1 := h_b31
      have h3 : a1 ≤ p1 := hp1.1
      have h4 : p1 ≤ b1 := hp1.2
      have h5 : b1 ≤ a2 := h_b12
      have h6 : a2 ≤ p2 := hp2.1
      linarith [hL1]
    have h_nonneg : 0 ≤ p2 - p3 := by linarith
    have h_abs : |p2 - p3| = p2 - p3 := abs_of_nonneg h_nonneg
    have h_goal : W ≤ |p2 - p3| := by rw [h_abs]; linarith
    exact Or.inr (Or.inr h_goal)
  · -- a3 < a2 < a1: p1 and p3 are W apart
    have h_b32 : b3 ≤ a2 := disjoint_left_endpoint h_ab3 h_ab2 h.1 h_disj23.symm
    have h_b21 : b2 ≤ a1 := disjoint_left_endpoint h_ab2 h_ab1 h.2 h_disj12.symm
    have h_main : p1 - p3 ≥ W := by
      have h1 : p3 ≤ b3 := hp3.2
      have h2 : b3 ≤ a2 := h_b32
      have h3 : a2 ≤ p2 := hp2.1
      have h4 : p2 ≤ b2 := hp2.2
      have h5 : b2 ≤ a1 := h_b21
      have h6 : a1 ≤ p1 := hp1.1
      linarith [hL2]
    have h_nonneg : 0 ≤ p1 - p3 := by linarith
    have h_abs : |p1 - p3| = p1 - p3 := abs_of_nonneg h_nonneg
    have h_goal : W ≤ |p1 - p3| := by rw [h_abs]; linarith
    exact Or.inr (Or.inl h_goal)

/--
A set of real numbers with diameter `< W` meets at most two
pairwise-disjoint closed intervals each of length `>= W`.
-/
lemma set_meets_at_most_two_intervals
    {W : ℝ} (hW : 0 < W)
    {A : Set ℝ} (hA : ∀ x y, x ∈ A → y ∈ A → |x - y| < W)
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (I : ι → Set ℝ)
    (h_disj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (I i) (I j))
    (h_len : ∀ i ∈ s, ∃ a b : ℝ, I i = Set.Icc a b ∧ b - a ≥ W) :
    (s.filter (fun i => (A ∩ I i).Nonempty)).card ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ (s.filter (fun i => (A ∩ I i).Nonempty)).card := by linarith
  rcases Finset.exists_subset_card_eq h3 with ⟨t, ht_sub, ht_card⟩
  have h_t_s : t ⊆ s := by
    intro i hi
    exact (Finset.mem_filter.mp (ht_sub hi)).1
  have h_t_nonempty : ∀ i ∈ t, (A ∩ I i).Nonempty := by
    intro i hi
    exact (Finset.mem_filter.mp (ht_sub hi)).2
  have h_disj' : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Disjoint (I i) (I j) := by
    intro i hi j hj hne
    exact h_disj i (h_t_s hi) j (h_t_s hj) hne

  rcases Finset.card_eq_three.mp ht_card with ⟨i0, i1, i2, h_ne01, h_ne02, h_ne12, h_t_eq⟩
  have hi0 : i0 ∈ t := by rw [h_t_eq]; simp
  have hi1 : i1 ∈ t := by rw [h_t_eq]; simp
  have hi2 : i2 ∈ t := by rw [h_t_eq]; simp

  rcases h_len i0 (h_t_s hi0) with ⟨a0, b0, hI0, hL0⟩
  rcases h_len i1 (h_t_s hi1) with ⟨a1, b1, hI1, hL1⟩
  rcases h_len i2 (h_t_s hi2) with ⟨a2, b2, hI2, hL2⟩
  rcases h_t_nonempty i0 hi0 with ⟨p0, hp0A, hp0I⟩
  rcases h_t_nonempty i1 hi1 with ⟨p1, hp1A, hp1I⟩
  rcases h_t_nonempty i2 hi2 with ⟨p2, hp2A, hp2I⟩
  have hp0_in : p0 ∈ Set.Icc a0 b0 := by rw [hI0] at hp0I; exact hp0I
  have hp1_in : p1 ∈ Set.Icc a1 b1 := by rw [hI1] at hp1I; exact hp1I
  have hp2_in : p2 ∈ Set.Icc a2 b2 := by rw [hI2] at hp2I; exact hp2I
  have h_ab0 : a0 ≤ b0 := by linarith [hL0]
  have h_ab1 : a1 ≤ b1 := by linarith [hL1]
  have h_ab2 : a2 ≤ b2 := by linarith [hL2]
  have h_disj01 : Disjoint (Set.Icc a0 b0) (Set.Icc a1 b1) := by
    rw [← hI0, ← hI1]; exact h_disj' i0 hi0 i1 hi1 h_ne01
  have h_disj02 : Disjoint (Set.Icc a0 b0) (Set.Icc a2 b2) := by
    rw [← hI0, ← hI2]; exact h_disj' i0 hi0 i2 hi2 h_ne02
  have h_disj12 : Disjoint (Set.Icc a1 b1) (Set.Icc a2 b2) := by
    rw [← hI1, ← hI2]; exact h_disj' i1 hi1 i2 hi2 h_ne12

  have h_main := three_points_diam hW h_ab0 h_ab1 h_ab2 hL0 hL1 hL2
    h_disj01 h_disj02 h_disj12 hp0_in hp1_in hp2_in

  have h01 : |p0 - p1| < W := hA p0 p1 hp0A hp1A
  have h02 : |p0 - p2| < W := hA p0 p2 hp0A hp2A
  have h12 : |p1 - p2| < W := hA p1 p2 hp1A hp2A
  rcases h_main with (h | h | h) <;> linarith

/--
A bounded subset of `ℝ` with diameter at most `rho` is an AD set of any
dimension `α ∈ (0,1]` at scale `rho` with constant `2`.

Proof: at any scale `rho' ≥ rho`, the set has diameter ≤ `rho ≤ rho'`, so it
fits inside a single ball of radius `rho'`.
-/
lemma isADSet1_of_diam_le
    {E : Set ℝ} {rho alpha : ℝ}
    (hrho : 0 < rho) (hrho_le_one : rho ≤ 1)
    (halpha : 0 < alpha) (halpha_one : alpha ≤ 1)
    (hE : E ⊆ Set.Icc (-4 : ℝ) 4)
    (hdiam : ∀ x y, x ∈ E → y ∈ E → |x - y| ≤ rho) :
    IsADSet1 E rho alpha 2 := by
  refine' ⟨hrho, halpha, halpha_one, by norm_num, hE, _⟩
  intro rho' hrho'_nonneg hrho'_le hrho'_one x r hr_le hr_one
  set S : Set ℝ := E ∩ Metric.closedBall x r with hS
  by_cases h_empty : S = ∅
  · rw [h_empty]
    simp
  · have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty
    rcases hS_nonempty with ⟨z, hz⟩
    have hzE : z ∈ E := hz.1
    have h_ediam_real : Metric.ediam S ≤ ENNReal.ofReal rho' := by
      apply Metric.ediam_le
      intro y hy z hz
      have hyE : y ∈ E := hy.1
      have hzE' : z ∈ E := hz.1
      have hdist : dist y z ≤ rho := by
        simpa [dist_eq_norm] using hdiam y z hyE hzE'
      have h : dist y z ≤ rho' := by linarith
      have h' : edist y z = ENNReal.ofReal (dist y z) :=
        edist_dist y z
      rw [h']
      exact ENNReal.ofReal_le_ofReal h
    let eps : NNReal := ⟨rho', hrho'_nonneg⟩
    have h_ediam : Metric.ediam S ≤ (eps : ENNReal) := by
      have hval : (eps : ℝ) = rho' := by
        dsimp only [eps] <;> rfl
      have h_coe : (eps : ENNReal) = ENNReal.ofReal (eps : ℝ) :=
        ENNReal.coe_nnreal_eq eps
      rw [h_coe, hval]
      exact h_ediam_real
    have h1 : Metric.externalCoveringNumber eps S ≤ 1 :=
      Metric.externalCoveringNumber_le_one_of_ediam_le h_ediam
    have h2 : (↑(Metric.externalCoveringNumber eps S) : ENNReal) ≤ 1 := by
      exact_mod_cast h1
    have h5 : 1 ≤ r / rho' := by
      have hpos : 0 < rho' := by linarith
      have h : rho' ≤ r := hr_le
      exact (one_le_div hpos).mpr h
    have h6 : (1 : ENNReal) ≤ Kakeya.realRpowENN (r / rho') alpha := by
      simpa [Kakeya.realRpowENN] using ENNReal.ofReal_le_ofReal
        (Real.one_le_rpow h5 halpha.le)
    have h7 : (1 : ENNReal) ≤ (2 : ENNReal) * Kakeya.realRpowENN (r / rho') alpha := by
      calc (1 : ENNReal)
        ≤ Kakeya.realRpowENN (r / rho') alpha := h6
      _ ≤ (2 : ENNReal) * Kakeya.realRpowENN (r / rho') alpha := by
        exact le_mul_of_one_le_left (by positivity) (by norm_num)
    exact h2.trans h7

/--
A set of real numbers with diameter strictly less than `W` meets at most two
pairwise-disjoint closed intervals each of length at least `W`.

This is the strip-counting corollary: a tube segment whose scalar projection
has diameter `< W` intersects at most two transverse strips of width `≥ W`.
-/
lemma projection_meets_at_most_two_strips
    {W : ℝ} (hW : 0 < W)
    {A : Set ℝ} (hA : ∀ x y, x ∈ A → y ∈ A → |x - y| < W)
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (strips : ι → Set ℝ)
    (h_disj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (strips i) (strips j))
    (h_width : ∀ i ∈ s, ∃ a b : ℝ, strips i = Set.Icc a b ∧ b - a ≥ W) :
    (s.filter (fun i => (A ∩ strips i).Nonempty)).card ≤ 2 :=
  set_meets_at_most_two_intervals hW hA s strips h_disj h_width

/--
Specialized trivial AD lemma: a set of diameter at most `rho` is AD at scale
`rho` with dimension `1 - sigma` and constant `2`.
-/
lemma isADSet1_of_diam_le_rho
    {E : Set ℝ} {rho sigma : ℝ}
    (hrho : 0 < rho) (hrho_le_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hbounded : E ⊆ Set.Icc (-4 : ℝ) 4)
    (hdiam : ∀ x y, x ∈ E → y ∈ E → |x - y| ≤ rho) :
    IsADSet1 E rho (1 - sigma) 2 :=
  isADSet1_of_diam_le hrho hrho_le_one (by linarith) (by linarith) hbounded hdiam

/--
Trivial AD with arbitrary constant `C ≥ 2`.
-/
lemma isADSet1_of_diam_le_rho'
    {E : Set ℝ} {rho sigma : ℝ} {C : ENNReal}
    (hrho : 0 < rho) (hrho_le_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hbounded : E ⊆ Set.Icc (-4 : ℝ) 4)
    (hdiam : ∀ x y, x ∈ E → y ∈ E → |x - y| ≤ rho)
    (hC : (2 : ENNReal) ≤ C) :
    IsADSet1 E rho (1 - sigma) C := by
  have h_base := isADSet1_of_diam_le_rho hrho hrho_le_one hsigma hsigma_one hbounded hdiam
  rcases h_base with ⟨h1, h2, h3, h4, h5, h6⟩
  have h1C : (1 : ENNReal) ≤ C := by
    calc (1 : ENNReal) ≤ 2 := by norm_num
      _ ≤ C := hC
  refine' ⟨h1, h2, h3, h1C, h5, _⟩
  intro rho' hrho'_nonneg hrho'_le hrho'_one x r hr_le hr_one
  have h7 := h6 rho' hrho'_nonneg hrho'_le hrho'_one x r hr_le hr_one
  have h8 : (2 : ENNReal) * Kakeya.realRpowENN (r / rho') (1 - sigma) ≤
      C * Kakeya.realRpowENN (r / rho') (1 - sigma) := by
    gcongr
  exact h7.trans h8

/-! ### PlaneMap strip containment -/

/--
For a single tube in the vertical chart, the scalar projection (onto any unit
direction) of its intersection with the horizontal slab has diameter at most
`2 * (b - a) + 6 * delta`.

When `64 * delta ≤ rho` and `Real.sqrt rho = 8 * (b - a)`, this bound is
`≤ Real.sqrt rho`.
-/
lemma tube_slab_projection_diam_le_sqrt_rho
    {delta a b rho : ℝ}
    {T : Kakeya.DeltaTube delta} {v : Point3} (hv : ‖v‖ = 1)
    (hdelta : 0 < delta) (hab : a < b)
    (hvert : (1 / 2 : ℝ) ≤ |T.direction (2 : Fin 3)|)
    (h64delta : 64 * delta ≤ rho)
    (hrho_le_quarter : rho ≤ 1 / 4)
    (hsqrt_rho : Real.sqrt rho = 8 * (b - a)) :
    ∀ (x y : Point3), x ∈ T.carrier ∩ horizontalSlab a b →
      y ∈ T.carrier ∩ horizontalSlab a b →
      |inner ℝ x v - inner ℝ y v| ≤ Real.sqrt rho := by
  have h1 : ∀ (x y : Point3), x ∈ T.carrier ∩ horizontalSlab a b →
      y ∈ T.carrier ∩ horizontalSlab a b →
      |inner ℝ x v - inner ℝ y v| ≤ 2 * (b - a) + 6 * delta :=
    tube_slab_projection_diam hdelta hab hvert hv
  have hba_small : b - a ≤ 1 / 16 := by
    have hsq : Real.sqrt rho ≤ 1 / 2 := by
      rw [Real.sqrt_le_left] <;> linarith
    linarith [hsqrt_rho]
  have hba_nonneg : 0 ≤ b - a := by linarith
  have h4_eq : rho = 64 * (b - a)^2 := by
    have hsq1 : (Real.sqrt rho)^2 = rho := Real.sq_sqrt (by linarith)
    have h : (Real.sqrt rho)^2 = (8 * (b - a))^2 := by rw [hsqrt_rho]
    linarith
  have h3 : delta ≤ (b - a)^2 := by
    have h : 64 * delta ≤ 64 * (b - a)^2 := by
      calc 64 * delta ≤ rho := h64delta
           _ = 64 * (b - a)^2 := h4_eq
    nlinarith
  have h4 : delta ≤ b - a := by
    calc delta ≤ (b - a)^2 := h3
         _ = (b - a) * (b - a) := by ring
         _ ≤ (b - a) * (1 / 16 : ℝ) := by exact mul_le_mul_of_nonneg_left hba_small hba_nonneg
         _ ≤ b - a := by nlinarith
  have h2 : 2 * (b - a) + 6 * delta ≤ Real.sqrt rho := by
    rw [hsqrt_rho]
    linarith
  intro x y hx hy
  exact (h1 x y hx hy).trans h2

/--
A tube's slab intersection lies in a planeMap-strip of half-width `sqrt rho`,
centered at any reference point `p0` in the same tube's slab intersection.
-/
lemma tube_slab_in_planeMap_strip
    {delta a b rho : ℝ}
    {T : Kakeya.DeltaTube delta} {v : Point3} (hv : ‖v‖ = 1)
    (hdelta : 0 < delta) (hab : a < b)
    (hvert : (1 / 2 : ℝ) ≤ |T.direction (2 : Fin 3)|)
    (h64delta : 64 * delta ≤ rho)
    (hrho_le_quarter : rho ≤ 1 / 4)
    (hsqrt_rho : Real.sqrt rho = 8 * (b - a))
    (p0 : Point3) (hp0 : p0 ∈ T.carrier ∩ horizontalSlab a b) :
    ∀ p ∈ T.carrier ∩ horizontalSlab a b,
      |inner ℝ (p - p0) v| ≤ Real.sqrt rho := by
  intro p hp
  have h : |inner ℝ p v - inner ℝ p0 v| ≤ Real.sqrt rho :=
    tube_slab_projection_diam_le_sqrt_rho hv hdelta hab hvert h64delta hrho_le_quarter hsqrt_rho p p0 hp hp0
  have h' : inner ℝ (p - p0) v = inner ℝ p v - inner ℝ p0 v := by
    rw [← inner_sub_left] <;> ring
  rw [h']
  exact h

/-! ### Tube segment projection diameter -/

/--
Extract a parameter witness from membership in a tube segment carrier.
-/
lemma tube_segment_carrier_witness
    {delta start rho : ℝ} (hdelta : 0 < delta) (hrho : 0 < rho)
    {base direction : Point3} {x : Point3}
    (hx : x ∈ tubeSegmentCarrier delta base direction start rho) :
    ∃ t : ℝ, t ∈ Set.Icc start (start + Real.sqrt rho) ∧
      dist x (base + t • direction) ≤ delta := by
  have hseg_compact : IsCompact ((fun t : ℝ => base + t • direction) '' Set.Icc start (start + Real.sqrt rho)) :=
    isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  have hcthick : tubeSegmentCarrier delta base direction start rho =
      ⋃ p ∈ ((fun t : ℝ => base + t • direction) '' Set.Icc start (start + Real.sqrt rho)),
        Metric.closedBall p delta :=
    hseg_compact.cthickening_eq_biUnion_closedBall hdelta.le
  rw [hcthick] at hx
  simpa [Set.mem_iUnion, Metric.mem_closedBall, Set.mem_image] using hx

/--
The scalar projection of a tube segment carrier onto a unit direction `v`
has diameter at most `K * Real.sqrt rho + 2 * delta`, where
`K = |inner(direction, v)|`.
-/
lemma tube_segment_projection_diam
    {delta rho : ℝ} (hdelta : 0 < delta) (hrho : 0 < rho)
    {base direction : Point3} (hdir : ‖direction‖ = 1)
    {start : ℝ} {v : Point3} (hv : ‖v‖ = 1)
    {K : ℝ} (hK : |inner ℝ direction v| ≤ K)
    {E : Set Point3} (hE : E ⊆ tubeSegmentCarrier delta base direction start rho) :
    ∀ (x y : Point3), x ∈ E → y ∈ E →
      |inner ℝ x v - inner ℝ y v| ≤ K * Real.sqrt rho + 2 * delta := by
  intro x y hx hy
  rcases tube_segment_carrier_witness hdelta hrho (hE hx) with ⟨tx, htx, hdx⟩
  rcases tube_segment_carrier_witness hdelta hrho (hE hy) with ⟨ty, hty, hdy⟩
  set ax := base + tx • direction with hax_def
  set ay := base + ty • direction with hay_def
  have hnx : ‖x - ax‖ ≤ delta := by simpa [dist_eq_norm] using hdx
  have hny : ‖y - ay‖ ≤ delta := by simpa [dist_eq_norm] using hdy
  have h_inner1 : |inner ℝ (x - ax) v| ≤ delta := by
    calc |inner ℝ (x - ax) v|
        ≤ ‖x - ax‖ * ‖v‖ := abs_real_inner_le_norm (x - ax) v
      _ = ‖x - ax‖ := by rw [hv] <;> ring
      _ ≤ delta := hnx
  have h_inner2 : |inner ℝ (y - ay) v| ≤ delta := by
    calc |inner ℝ (y - ay) v|
        ≤ ‖y - ay‖ * ‖v‖ := abs_real_inner_le_norm (y - ay) v
      _ = ‖y - ay‖ := by rw [hv] <;> ring
      _ ≤ delta := hny
  have h_inner3 : |inner ℝ (ax - ay) v| ≤ K * |tx - ty| := by
    have h_eq : ax - ay = (tx - ty) • direction := by
      simp [hax_def, hay_def, sub_smul] <;> abel
    rw [h_eq]
    have h : inner ℝ ((tx - ty) • direction) v = (tx - ty) * inner ℝ direction v := by
      simp [inner_smul_left]
    rw [h]
    have h_goal : |(tx - ty) * inner ℝ direction v| ≤ K * |tx - ty| := by
      have hK_nonneg : 0 ≤ K := by
        have h : 0 ≤ |inner ℝ direction v| := abs_nonneg _
        linarith [hK]
      calc |(tx - ty) * inner ℝ direction v|
          = |tx - ty| * |inner ℝ direction v| := by rw [abs_mul]
        _ ≤ |tx - ty| * K := by gcongr
        _ = K * |tx - ty| := by ring
    exact h_goal
  have h_tx_ty : |tx - ty| ≤ Real.sqrt rho := by
    have h11 : start ≤ tx := htx.1
    have h12 : tx ≤ start + Real.sqrt rho := htx.2
    have h21 : start ≤ ty := hty.1
    have h22 : ty ≤ start + Real.sqrt rho := hty.2
    rw [abs_le] <;> constructor <;> linarith
  have h_decomp : inner ℝ x v - inner ℝ y v =
      inner ℝ (x - ax) v + inner ℝ (ax - ay) v - inner ℝ (y - ay) v := by
    have h_eq : x - y = (x - ax) + (ax - ay) + (ay - y) := by abel
    have h1 : inner ℝ x v - inner ℝ y v = inner ℝ (x - y) v := by
      rw [← inner_sub_left] <;> ring
    rw [h1, h_eq]
    have h2 : inner ℝ ((x - ax) + (ax - ay) + (ay - y)) v =
        inner ℝ (x - ax) v + inner ℝ (ax - ay) v + inner ℝ (ay - y) v := by
      rw [inner_add_left, inner_add_left]
    rw [h2]
    have h3 : inner ℝ (ay - y) v = -inner ℝ (y - ay) v := by
      have h4 : inner ℝ (ay - y) v = inner ℝ (-(y - ay)) v := by rw [neg_sub]
      rw [h4, inner_neg_left] <;> ring
    rw [h3] <;> ring
  rw [h_decomp]
  have h_tri : |inner ℝ (x - ax) v + inner ℝ (ax - ay) v - inner ℝ (y - ay) v| ≤
      |inner ℝ (x - ax) v| + |inner ℝ (ax - ay) v| + |inner ℝ (y - ay) v| := by
    have h1 : |inner ℝ (x - ax) v + inner ℝ (ax - ay) v - inner ℝ (y - ay) v| ≤
        |inner ℝ (x - ax) v + inner ℝ (ax - ay) v| + |inner ℝ (y - ay) v| :=
      abs_sub _ _
    have h2 : |inner ℝ (x - ax) v + inner ℝ (ax - ay) v| ≤
        |inner ℝ (x - ax) v| + |inner ℝ (ax - ay) v| := abs_add_le _ _
    linarith
  have h_main : |inner ℝ (ax - ay) v| ≤ K * Real.sqrt rho := by
    have hK_nonneg : 0 ≤ K := by
      have h : 0 ≤ |inner ℝ direction v| := abs_nonneg _
      linarith [hK]
    calc |inner ℝ (ax - ay) v|
        ≤ K * |tx - ty| := h_inner3
      _ ≤ K * Real.sqrt rho := by
        exact mul_le_mul_of_nonneg_left h_tx_ty hK_nonneg
  linarith

/--
The planeMap-projection of a tube segment piece has diameter at most `rho`.

Uses the incidence bound `|inner(tube_dir, v)| ≤ delta` and the segment length
`sqrt rho`.  Total: `delta * sqrt rho + 2 * delta ≤ 2.5 * delta ≤ rho`,
where the last step uses `64 * delta ≤ rho` and `sqrt rho ≤ 1/2`.
-/
lemma piece_planeMap_diam_le_rho
    {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho_pos : 0 < rho)
    (h64delta : 64 * delta ≤ rho) (hrho_le_quarter : rho ≤ 1 / 4)
    {T : Kakeya.DeltaTube delta} {v : Point3} (hv : ‖v‖ = 1)
    (hinc : |inner ℝ T.direction v| ≤ delta)
    (start : ℝ)
    (S : Set Point3) (hS : S ⊆ tubeSegmentCarrier delta T.base T.direction start rho) :
    ∀ x y, x ∈ S → y ∈ S → |inner ℝ x v - inner ℝ y v| ≤ rho := by
  have hsqrt_le_half : Real.sqrt rho ≤ 1 / 2 := by
    rw [Real.sqrt_le_left] <;> linarith
  have h_bound : delta * Real.sqrt rho + 2 * delta ≤ rho := by
    have h1 : delta * Real.sqrt rho ≤ delta * (1 / 2 : ℝ) := by gcongr
    have h2 : delta * Real.sqrt rho + 2 * delta ≤ (5 / 2 : ℝ) * delta := by linarith
    have h3 : (5 / 2 : ℝ) * delta ≤ rho := by
      calc (5 / 2 : ℝ) * delta
          ≤ (64 / 2 : ℝ) * delta := by gcongr <;> norm_num
        _ = 32 * delta := by ring
        _ ≤ 64 * delta := by linarith
        _ ≤ rho := h64delta
    linarith
  intro x y hx hy
  have h := tube_segment_projection_diam hdelta hrho_pos T.direction_unit hv hinc hS x y hx hy
  exact h.trans h_bound

/--
Local AD for a tube segment piece via trivial diameter bound.

If the piece is contained in a tube segment carrier and the projection direction
`v` satisfies `|inner(tube_dir, v)| ≤ delta`, then the scalar projection has
diameter at most `delta * sqrt rho + 2 * delta ≤ rho` (when `rho ≤ 1/4` and
`64 * delta ≤ rho`), so it is an AD set at scale `rho` with constant `2`.
-/
lemma tube_segment_piece_local_ad
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hrho_le_quarter : rho ≤ 1 / 4)
    (h64delta : 64 * delta ≤ rho)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    {E : Set Point3} {v : Point3} (hv : ‖v‖ = 1)
    {base direction : Point3} (hdir : ‖direction‖ = 1)
    {start : ℝ}
    (hincidence : |inner ℝ direction v| ≤ delta)
    (hE : E ⊆ tubeSegmentCarrier delta base direction start rho)
    (hbounded : scalarProjection v E ⊆ Set.Icc (-4 : ℝ) 4) :
    IsADSet1 (scalarProjection v E) rho (1 - sigma) 2 := by
  have hsqrt_le_half : Real.sqrt rho ≤ 1 / 2 := by
    rw [Real.sqrt_le_left] <;> linarith
  have hdiam_proj : ∀ (x y : ℝ), x ∈ scalarProjection v E → y ∈ scalarProjection v E → |x - y| ≤ rho := by
    intro x y hx hy
    rcases hx with ⟨p, hp, rfl⟩
    rcases hy with ⟨q, hq, rfl⟩
    have h := tube_segment_projection_diam hdelta hrho hdir hv hincidence hE p q hp hq
    have h' : |inner ℝ p v - inner ℝ q v| = |(inner ℝ p v) - (inner ℝ q v)| := by rfl
    rw [h'] at h
    have h_bound : delta * Real.sqrt rho + 2 * delta ≤ rho := by
      have h1 : delta * Real.sqrt rho ≤ delta * (1 / 2 : ℝ) := by gcongr
      have h2 : delta * Real.sqrt rho + 2 * delta ≤ (5 / 2 : ℝ) * delta := by linarith
      have h3 : (5 / 2 : ℝ) * delta ≤ rho := by
        calc (5 / 2 : ℝ) * delta
            ≤ (64 / 2 : ℝ) * delta := by gcongr <;> norm_num
          _ = 32 * delta := by ring
          _ ≤ 64 * delta := by linarith
          _ ≤ rho := h64delta
      linarith
    exact h.trans h_bound
  exact isADSet1_of_diam_le_rho hrho (by linarith) hsigma hsigma_one hbounded hdiam_proj

end Kakeya.Assouad
