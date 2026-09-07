import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44CloseAndLineBounds

/-!
# WZ1 Lemma 44: transverse strip-pair bound

The third case in the bad-pair triple count: a point far from the line through
two `G₁` points forces the associated strips to be transverse, so their
intersection lies in a small ball controlled by the Frostman bound on `G₂`.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal

attribute [local instance] Classical.propDecidable

lemma cross2_add_right (a b w : Point2) :
    cross2 w (a + b) = cross2 w a + cross2 w b := by
  simp [cross2] <;> ring

lemma cross2_smul_right (c : ℝ) (a w : Point2) :
    cross2 w (c • a) = c * cross2 w a := by
  simp [cross2] <;> ring

/-- |cross2 (y-x) (x'-x)| ≥ D * s using base ≥ D and height ≥ s. -/
lemma cross2_area_lower_bound {x x' y : Point2} {D s : ℝ}
    (hD : D ≤ dist x x')
    (hs : s ≤ Metric.infDist y (lineThrough x x' : Set Point2))
    (hne : x ≠ x')
    (hD_nonneg : 0 ≤ D) (hs_nonneg : 0 ≤ s) :
    D * s ≤ |cross2 (y - x) (x' - x)| := by
  set w := x' - x with hw_def
  have hw_ne_zero : w ≠ 0 := by
    intro h
    have h' : x' = x := by simpa [hw_def, sub_eq_zero] using h
    exact hne h'.symm
  let q := projPoint x y w
  have hq_dir : q - x ∈ (ℝ ∙ w : Submodule ℝ Point2) := by
    have h : q - x = (inner ℝ (y - x) w / ‖w‖ ^ 2) • w := by
      dsimp only [q, projPoint] <;> abel
    rw [h]
    exact Submodule.smul_mem (ℝ ∙ w) _ (Submodule.subset_span (by simp))
  have h1 : (lineThrough x x').direction = ℝ ∙ w := by
    simp [lineThrough, AffineSubspace.direction_mk', hw_def] <;> rfl
  have h2 : q - x ∈ (lineThrough x x').direction := by
    rw [h1]; exact hq_dir
  have hq_line : q ∈ (lineThrough x x' : Set Point2) := by
    have h_vadd : (q - x) +ᵥ x = q := by
      simp [vadd_eq_add] <;> abel
    have h : (q - x) +ᵥ x ∈ (lineThrough x x') ↔ (q - x) ∈ (lineThrough x x').direction :=
      AffineSubspace.vadd_mem_iff_mem_direction (q - x) lineThrough_contains_first
    have h' : (q - x) +ᵥ x ∈ (lineThrough x x') := h.mpr h2
    rw [h_vadd] at h'
    exact h'
  have h_norm : ‖y - q‖ = |cross2 (y - x) w| / ‖w‖ :=
    projPoint_norm hw_ne_zero
  set d := Metric.infDist y (lineThrough x x' : Set Point2) with hd_def
  have h_dist : d ≤ dist y q := Metric.infDist_le_dist_of_mem hq_line
  have h_dist_norm : dist y q = ‖y - q‖ := rfl
  have h_dist' : d ≤ ‖y - q‖ := by rw [h_dist_norm] at h_dist; exact h_dist
  have h_base : D ≤ ‖w‖ := by
    have h1 : dist x x' = ‖x - x'‖ := rfl
    have h2 : ‖x - x'‖ = ‖x' - x‖ := by
      rw [show x - x' = -(x' - x) by abel, norm_neg]
    have h3 : ‖x' - x‖ = ‖w‖ := by rfl
    rw [h1, h2, h3] at hD
    exact hD
  have h_pos : 0 ≤ d := Metric.infDist_nonneg
  have hwnorm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne_zero
  have h4 : |cross2 (y - x) w| ≥ d * ‖w‖ := by
    have h5 : d * ‖w‖ ≤ ‖y - q‖ * ‖w‖ :=
      mul_le_mul_of_nonneg_right h_dist' (by positivity)
    have h6 : ‖y - q‖ * ‖w‖ = |cross2 (y - x) w| := by
      rw [h_norm]
      field_simp [hwnorm_pos.ne'] <;> ring
    rw [h6] at h5
    exact h5
  have h7 : d * ‖w‖ ≥ D * s := by
    have h8 : d ≥ s := hs
    have h9 : ‖w‖ ≥ D := h_base
    have h10 : 0 ≤ d := h_pos
    have h11 : 0 ≤ ‖w‖ := by positivity
    have h12 : d * ‖w‖ ≥ s * ‖w‖ := mul_le_mul_of_nonneg_right h8 h11
    have h13 : s * ‖w‖ ≥ s * D := mul_le_mul_of_nonneg_left h9 hs_nonneg
    have h14 : s * D = D * s := by ring
    linarith
  have h15 : D * s ≤ |cross2 (y - x) w| := h7.trans h4
  have h16 : |cross2 (y - x) w| = |cross2 (y - x) (x' - x)| := by
    have h17 : w = x' - x := by simp [hw_def]
    rw [h17]
  rw [h16] at h15
  exact h15

/-- cross2(n1, perp(n2)) = inner(n1, n2). -/
lemma cross2_n1_perp_n2 (n1 n2 : Point2) :
    cross2 n1 (wz1Perp2 n2) = inner ℝ n1 n2 := by
  have h2 := wz1Perp2_coords n2
  simp [cross2, inner2_eq, h2.1, h2.2] <;> ring

/-- cross2(perp(n1), n2) = -inner(n1, n2). -/
lemma cross2_perp_n1_n2 (n1 n2 : Point2) :
    cross2 (wz1Perp2 n1) n2 = -inner ℝ n1 n2 := by
  have h1 := wz1Perp2_coords n1
  simp [cross2, inner2_eq, h1.1, h1.2] <;> ring

/--
Approximate angle lower bound for thickening setting.

Given u, v with |inner(u,n1)| ≤ r, |inner(v,n2)| ≤ r,
and |cross2(u,v)| ≥ D*s, with ‖u‖,‖v‖ ≤ 2 and r ≤ 1,
then ‖n1-n2‖ ≥ (D*s - 4r)/5.
-/
lemma angle_lower_bound_approx
    {u v : Point2} {D s r : ℝ}
    (h_area : D * s ≤ |cross2 u v|)
    (hu_norm : ‖u‖ ≤ 2) (hv_norm : ‖v‖ ≤ 2)
    (n1 n2 : Point2) (hn1 : ‖n1‖ = 1) (hn2 : ‖n2‖ = 1)
    (hε1 : |inner ℝ u n1| ≤ r)
    (hε2 : |inner ℝ v n2| ≤ r)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖n1 - n2‖ ≥ (D * s - 4 * r) / 5 := by
  set ε1 := inner ℝ u n1 with hε1_def
  set ε2 := inner ℝ v n2 with hε2_def
  set a := inner ℝ u (wz1Perp2 n1) with ha_def
  set b := inner ℝ v (wz1Perp2 n2) with hb_def
  have h_decomp1 : u = ε1 • n1 + a • wz1Perp2 n1 := by
    have h := orthonormal_decomp u n1 hn1
    simpa [hε1_def, ha_def] using h
  have h_decomp2 : v = ε2 • n2 + b • wz1Perp2 n2 := by
    have h := orthonormal_decomp v n2 hn2
    simpa [hε2_def, hb_def] using h
  have h_cross : cross2 u v =
      (ε1 * ε2 + a * b) * cross2 n1 n2 +
      (ε1 * b - a * ε2) * inner ℝ n1 n2 := by
    rw [h_decomp1, h_decomp2]
    have h1 : cross2 (ε1 • n1 + a • wz1Perp2 n1) (ε2 • n2 + b • wz1Perp2 n2) =
        cross2 (ε1 • n1) (ε2 • n2) + cross2 (ε1 • n1) (b • wz1Perp2 n2) +
        cross2 (a • wz1Perp2 n1) (ε2 • n2) + cross2 (a • wz1Perp2 n1) (b • wz1Perp2 n2) := by
      rw [cross2_add_left, cross2_add_right, cross2_add_right] <;> ring
    rw [h1]
    have h2 : cross2 (ε1 • n1) (ε2 • n2) = ε1 * ε2 * cross2 n1 n2 := by
      rw [cross2_smul_left, cross2_smul_right] <;> ring
    have h3 : cross2 (ε1 • n1) (b • wz1Perp2 n2) = ε1 * b * inner ℝ n1 n2 := by
      rw [cross2_smul_left, cross2_smul_right, cross2_n1_perp_n2] <;> ring
    have h4 : cross2 (a • wz1Perp2 n1) (ε2 • n2) = a * ε2 * (-inner ℝ n1 n2) := by
      rw [cross2_smul_left, cross2_smul_right, cross2_perp_n1_n2] <;> ring
    have h5 : cross2 (a • wz1Perp2 n1) (b • wz1Perp2 n2) = a * b * cross2 n1 n2 := by
      rw [cross2_smul_left, cross2_smul_right, cross2_perp_perp] <;> ring
    rw [h2, h3, h4, h5] <;> ring
  have h_a_le : |a| ≤ ‖u‖ := by
    have h : |inner ℝ u (wz1Perp2 n1)| ≤ ‖u‖ * ‖wz1Perp2 n1‖ :=
      abs_real_inner_le_norm u (wz1Perp2 n1)
    have hnorm : ‖wz1Perp2 n1‖ = ‖n1‖ := by
      have hpc := wz1Perp2_coords n1
      have h1 : ‖wz1Perp2 n1‖ ^ 2 = ‖n1‖ ^ 2 := by
        rw [norm2_sq (wz1Perp2 n1), norm2_sq n1, hpc.1, hpc.2] <;> ring
      have h2 : 0 ≤ ‖wz1Perp2 n1‖ := by positivity
      have h3 : 0 ≤ ‖n1‖ := by positivity
      nlinarith
    rw [hnorm, hn1] at h
    simpa [ha_def] using h
  have h_b_le : |b| ≤ ‖v‖ := by
    have h : |inner ℝ v (wz1Perp2 n2)| ≤ ‖v‖ * ‖wz1Perp2 n2‖ :=
      abs_real_inner_le_norm v (wz1Perp2 n2)
    have hnorm : ‖wz1Perp2 n2‖ = ‖n2‖ := by
      have hpc := wz1Perp2_coords n2
      have h1 : ‖wz1Perp2 n2‖ ^ 2 = ‖n2‖ ^ 2 := by
        rw [norm2_sq (wz1Perp2 n2), norm2_sq n2, hpc.1, hpc.2] <;> ring
      have h2 : 0 ≤ ‖wz1Perp2 n2‖ := by positivity
      have h3 : 0 ≤ ‖n2‖ := by positivity
      nlinarith
    rw [hnorm, hn2] at h
    simpa [hb_def] using h
  have h_a2 : |a| ≤ 2 := by linarith [h_a_le, hu_norm]
  have h_b2 : |b| ≤ 2 := by linarith [h_b_le, hv_norm]
  have h_bound1 : |ε1 * ε2 + a * b| ≤ r ^ 2 + 4 := by
    calc
      |ε1 * ε2 + a * b| ≤ |ε1 * ε2| + |a * b| := by exact abs_add_le (ε1 * ε2) (a * b)
      _ = |ε1| * |ε2| + |a| * |b| := by simp [abs_mul] <;> ring
      _ ≤ r * r + 2 * 2 := by gcongr <;> linarith
      _ = r ^ 2 + 4 := by ring
  have h_bound2 : |ε1 * b - a * ε2| ≤ 4 * r := by
    calc
      |ε1 * b - a * ε2| ≤ |ε1 * b| + |a * ε2| := by exact abs_sub (ε1 * b) (a * ε2)
      _ = |ε1| * |b| + |a| * |ε2| := by simp [abs_mul] <;> ring
      _ ≤ r * 2 + 2 * r := by gcongr <;> linarith
      _ = 4 * r := by ring
  have h_main : |cross2 u v| ≤ (r ^ 2 + 4) * |cross2 n1 n2| + 4 * r * |inner ℝ n1 n2| := by
    rw [h_cross]
    have h : |(ε1 * ε2 + a * b) * cross2 n1 n2 + (ε1 * b - a * ε2) * inner ℝ n1 n2| ≤
        |(ε1 * ε2 + a * b) * cross2 n1 n2| + |(ε1 * b - a * ε2) * inner ℝ n1 n2| := by
      exact abs_add_le
        ((ε1 * ε2 + a * b) * cross2 n1 n2)
        ((ε1 * b - a * ε2) * inner ℝ n1 n2)
    calc
      |_| ≤ |(ε1 * ε2 + a * b) * cross2 n1 n2| + |(ε1 * b - a * ε2) * inner ℝ n1 n2| := h
      _ = |ε1 * ε2 + a * b| * |cross2 n1 n2| + |ε1 * b - a * ε2| * |inner ℝ n1 n2| := by
        simp [abs_mul] <;> ring
      _ ≤ (r ^ 2 + 4) * |cross2 n1 n2| + 4 * r * |inner ℝ n1 n2| := by gcongr
  have h_cross_le : |cross2 n1 n2| ≤ ‖n1 - n2‖ :=
    abs_cross2_normals_le_dist n1 n2 hn1 hn2
  have h_inner_le : |inner ℝ n1 n2| ≤ 1 := by
    have h : |inner ℝ n1 n2| ≤ ‖n1‖ * ‖n2‖ := abs_real_inner_le_norm n1 n2
    rw [hn1, hn2] at h <;> linarith
  have h_r2_le_one : r ^ 2 ≤ 1 := by nlinarith
  have h_final : D * s ≤ 5 * ‖n1 - n2‖ + 4 * r := by
    calc
      D * s ≤ |cross2 u v| := h_area
      _ ≤ (r ^ 2 + 4) * |cross2 n1 n2| + 4 * r * |inner ℝ n1 n2| := h_main
      _ ≤ (r ^ 2 + 4) * ‖n1 - n2‖ + 4 * r * 1 := by gcongr
      _ ≤ 5 * ‖n1 - n2‖ + 4 * r := by
        have h_nonneg : 0 ≤ ‖n1 - n2‖ := by positivity
        nlinarith
  linarith

/-!
## Case 3: b2 far from line(b1, b1'), strips intersect in a small region
-/

/--
Strip intersection geometry: given two lines with unit normals separated by θ,
their r-thickenings' intersection is contained in a closed ball of radius 6r/θ
around any point c that lies in both strips.

Uses bacon's `strip_intersection_subset_ball` and `thickening_subset_strip`.
The angle hypothesis is essential: without it (parallel lines), the intersection
can be an unbounded strip, so the statement would be false.
-/
lemma stripIntersectionBall {r θ : ℝ} (hr : 0 < r) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    {ℓ1 ℓ2 : AffineSubspace ℝ Point2}
    (hfin1 : Module.finrank ℝ ℓ1.direction = 1)
    (hfin2 : Module.finrank ℝ ℓ2.direction = 1)
    (n1 n2 : Point2) (hn1 : ‖n1‖ = 1) (hn2 : ‖n2‖ = 1)
    (hn1_orth : ∀ v ∈ ℓ1.direction, inner ℝ v n1 = 0)
    (hn2_orth : ∀ v ∈ ℓ2.direction, inner ℝ v n2 = 0)
    (h_angle_lower : θ ≤ ‖n1 - n2‖)
    (h_angle_upper : ‖n1 - n2‖ ≤ Real.sqrt 2)
    {b1 b2 c : Point2}
    (hb1 : b1 ∈ (ℓ1 : Set Point2)) (hb2 : b2 ∈ (ℓ2 : Set Point2))
    (hc1 : |inner ℝ (c - b1) n1| ≤ r)
    (hc2 : |inner ℝ (c - b2) n2| ≤ r) :
    (Metric.thickening r (ℓ1 : Set Point2) ∩
     Metric.thickening r (ℓ2 : Set Point2)) ⊆
    Metric.closedBall c (6 * r / θ) := by
  have h_strip1 : Metric.thickening r (ℓ1 : Set Point2) ⊆
      {p : Point2 | |inner ℝ (p - b1) n1| ≤ r} := by
    have h := thickening_subset_strip hfin1 n1 hn1 hn1_orth b1 hb1 r hr
    intro p hp
    have h' : |inner ℝ p n1 - inner ℝ b1 n1| ≤ r := h hp
    have h_eq : inner ℝ p n1 - inner ℝ b1 n1 = inner ℝ (p - b1) n1 := by
      rw [←inner_sub_left]
    rw [h_eq] at h'
    exact h'
  have h_strip2 : Metric.thickening r (ℓ2 : Set Point2) ⊆
      {p : Point2 | |inner ℝ (p - b2) n2| ≤ r} := by
    have h := thickening_subset_strip hfin2 n2 hn2 hn2_orth b2 hb2 r hr
    intro p hp
    have h' : |inner ℝ p n2 - inner ℝ b2 n2| ≤ r := h hp
    have h_eq : inner ℝ p n2 - inner ℝ b2 n2 = inner ℝ (p - b2) n2 := by
      rw [←inner_sub_left]
    rw [h_eq] at h'
    exact h'
  have h_inter : (Metric.thickening r (ℓ1 : Set Point2) ∩
      Metric.thickening r (ℓ2 : Set Point2)) ⊆
      {p : Point2 | |inner ℝ (p - b1) n1| ≤ r ∧ |inner ℝ (p - b2) n2| ≤ r} := by
    intro p hp
    exact ⟨h_strip1 hp.1, h_strip2 hp.2⟩
  have h_ball := strip_intersection_subset_ball
    hr hθ hθ1 n1 n2 hn1 hn2 h_angle_lower h_angle_upper b1 b2 c hc1 hc2
  exact Set.Subset.trans h_inter h_ball

/--
Per-strip-pair bound for Case 3: for fixed b1, b1', ℓ1, ℓ2, the G2 points
in the intersection of the two r-thickenings that are far from line(b1,b1')
are bounded by Frostman after strip intersection geometry.

Uses approximate angle bound + `stripIntersectionBall` + Frostman on G2.

Requires `8*r ≤ D*s` for a positive angle lower bound.
-/
lemma case3_per_strip_pair {delta r D s : ℝ}
    (hδ : 0 < delta) (hr : delta ≤ r) (hr1 : r ≤ 1)
    (hD : 0 < D) (hs : 0 < s)
    (hDsr : 8 * r ≤ D * s)
    {G2 : DiscreteSet 2} (C_F : ENNReal)
    (hC_F : 1 ≤ C_F)
    (hFrost2 : G2.IsFrostman delta 1 C_F)
    (hG2_ball : G2.IsInUnitBall)
    {b1 b1' : Point2}
    (hb1_ball : ‖b1‖ ≤ 1) (hb1'_ball : ‖b1'‖ ≤ 1)
    (h_dist : D < dist b1 b1')
    {ℓ1 ℓ2 : AffineSubspace ℝ Point2}
    (hfin1 : Module.finrank ℝ ℓ1.direction = 1)
    (hfin2 : Module.finrank ℝ ℓ2.direction = 1)
    (hℓ1 : b1 ∈ (ℓ1 : Set Point2))
    (hℓ2 : b1' ∈ (ℓ2 : Set Point2)) :
    ↑(G2.filter fun b2 =>
      b2 ∉ Metric.thickening s ((lineThrough b1 b1') : Set Point2) ∧
      b2 ∈ Metric.thickening r (ℓ1 : Set Point2) ∧
      b2 ∈ Metric.thickening r (ℓ2 : Set Point2)).card
    ≤ C_F * Kakeya.realRpowENN (60 * r / (D * s)) 1 * G2.enncard := by
  let S : Finset Point2 := G2.filter fun b2 =>
      b2 ∉ Metric.thickening s ((lineThrough b1 b1') : Set Point2) ∧
      b2 ∈ Metric.thickening r (ℓ1 : Set Point2) ∧
      b2 ∈ Metric.thickening r (ℓ2 : Set Point2)
  by_cases hS : S = ∅
  · have h_empty : (↑S.card : ENNReal) = 0 := by
      rw [hS, Finset.card_empty] <;> simp
    rw [h_empty]
    <;> simp
  ·
    have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    rcases hS_nonempty with ⟨b2, hb2⟩
    have hb2_in_G2 : b2 ∈ G2 := (Finset.mem_filter.mp hb2).1
    have hb2_cond := (Finset.mem_filter.mp hb2).2
    have hb2_far : b2 ∉ Metric.thickening s ((lineThrough b1 b1') : Set Point2) := hb2_cond.1
    have hb2_in1 : b2 ∈ Metric.thickening r (ℓ1 : Set Point2) := hb2_cond.2.1
    have hb2_in2 : b2 ∈ Metric.thickening r (ℓ2 : Set Point2) := hb2_cond.2.2
    have hb2_ball : ‖b2‖ ≤ 1 := by
      have h : dist b2 0 ≤ 1 := hG2_ball b2 hb2_in_G2
      simpa [dist_eq_norm] using h
    have hne : b1 ≠ b1' := by
      intro h
      have h' : dist b1 b1' = 0 := by rw [h, dist_self]
      rw [h'] at h_dist
      linarith [hD]
    obtain ⟨n1, hn1, hn1_orth⟩ := exists_unit_normal_of_finrank_one hfin1
    obtain ⟨n2_raw, hn2_raw, hn2_raw_orth⟩ := exists_unit_normal_of_finrank_one hfin2
    have h_choose : ‖n1 - n2_raw‖ ≤ Real.sqrt 2 ∨ ‖n1 + n2_raw‖ ≤ Real.sqrt 2 := by
      by_cases h : ‖n1 - n2_raw‖ ≤ Real.sqrt 2
      · exact Or.inl h
      · have h' : ‖n1 - n2_raw‖ ^ 2 > 2 := by
          have hsqrt : 0 ≤ Real.sqrt 2 := by positivity
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        have h_sum : ‖n1 - n2_raw‖ ^ 2 + ‖n1 + n2_raw‖ ^ 2 = 4 := by
          have h1 : ‖n1 - n2_raw‖ ^ 2 + ‖n1 + n2_raw‖ ^ 2 = 2 * (‖n1‖ ^ 2 + ‖n2_raw‖ ^ 2) := by
            have h2 : ‖n1 - n2_raw‖ ^ 2 = (n1 0 - n2_raw 0) ^ 2 + (n1 1 - n2_raw 1) ^ 2 := by
              rw [norm2_sq (n1 - n2_raw)] <;> simp [Pi.sub_apply] <;> ring
            have h3 : ‖n1 + n2_raw‖ ^ 2 = (n1 0 + n2_raw 0) ^ 2 + (n1 1 + n2_raw 1) ^ 2 := by
              rw [norm2_sq (n1 + n2_raw)] <;> simp [Pi.add_apply] <;> ring
            have h4 : ‖n1‖ ^ 2 = (n1 0) ^ 2 + (n1 1) ^ 2 := norm2_sq n1
            have h5 : ‖n2_raw‖ ^ 2 = (n2_raw 0) ^ 2 + (n2_raw 1) ^ 2 := norm2_sq n2_raw
            rw [h2, h3, h4, h5] <;> ring
          rw [h1, hn1, hn2_raw] <;> norm_num
        have h'' : ‖n1 + n2_raw‖ ^ 2 < 2 := by nlinarith
        have hsqrt : 0 ≤ Real.sqrt 2 := by positivity
        have h3 : ‖n1 + n2_raw‖ ≤ Real.sqrt 2 := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        exact Or.inr h3
    let n2 := if ‖n1 - n2_raw‖ ≤ Real.sqrt 2 then n2_raw else -n2_raw
    have hn2 : ‖n2‖ = 1 := by
      dsimp only [n2]
      split_ifs with h
      · exact hn2_raw
      · rw [norm_neg] <;> exact hn2_raw
    have hn2_orth : ∀ v ∈ ℓ2.direction, inner ℝ v n2 = 0 := by
      dsimp only [n2]
      split_ifs with h
      · exact hn2_raw_orth
      · intro v hv
        have h9 : inner ℝ v (-n2_raw) = -inner ℝ v n2_raw := by
          simp
        rw [h9, hn2_raw_orth v hv] <;> ring
    have h_angle_upper : ‖n1 - n2‖ ≤ Real.sqrt 2 := by
      dsimp only [n2]
      split_ifs with h
      · exact h
      · have h5 : ‖n1 - (-n2_raw)‖ = ‖n1 + n2_raw‖ := by
          have h6 : n1 - (-n2_raw) = n1 + n2_raw := by abel
          rw [h6]
        rw [h5]
        exact h_choose.resolve_left h
    have hr_pos : 0 < r := hδ.trans_le hr
    have hε1 : |inner ℝ (b2 - b1) n1| ≤ r := by
      have h_strip1 : Metric.thickening r (ℓ1 : Set Point2) ⊆
          {p : Point2 | |inner ℝ (p - b1) n1| ≤ r} := by
        have h := thickening_subset_strip hfin1 n1 hn1 hn1_orth b1 hℓ1 r hr_pos
        intro p hp
        have h' : |inner ℝ p n1 - inner ℝ b1 n1| ≤ r := h hp
        have h_eq : inner ℝ p n1 - inner ℝ b1 n1 = inner ℝ (p - b1) n1 := by
          rw [←inner_sub_left]
        rw [h_eq] at h'; exact h'
      exact h_strip1 hb2_in1
    have hε2 : |inner ℝ (b2 - b1') n2| ≤ r := by
      have h_strip2 : Metric.thickening r (ℓ2 : Set Point2) ⊆
          {p : Point2 | |inner ℝ (p - b1') n2| ≤ r} := by
        have h := thickening_subset_strip hfin2 n2 hn2 hn2_orth b1' hℓ2 r hr_pos
        intro p hp
        have h' : |inner ℝ p n2 - inner ℝ b1' n2| ≤ r := h hp
        have h_eq : inner ℝ p n2 - inner ℝ b1' n2 = inner ℝ (p - b1') n2 := by
          rw [←inner_sub_left]
        rw [h_eq] at h'; exact h'
      exact h_strip2 hb2_in2
    have hu_norm : ‖b2 - b1‖ ≤ 2 := by
      calc ‖b2 - b1‖ ≤ ‖b2‖ + ‖b1‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by linarith
        _ = 2 := by norm_num
    have hv_norm : ‖b2 - b1'‖ ≤ 2 := by
      calc ‖b2 - b1'‖ ≤ ‖b2‖ + ‖b1'‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by linarith
        _ = 2 := by norm_num
    have h_dist_line : s ≤ Metric.infDist b2 (lineThrough b1 b1' : Set Point2) := by
      have h_line_nonempty : (lineThrough b1 b1' : Set Point2).Nonempty :=
        ⟨b1, lineThrough_contains_first⟩
      by_contra h
      have h' : Metric.infDist b2 (lineThrough b1 b1' : Set Point2) < s := by linarith
      have h'' : ∃ z ∈ (lineThrough b1 b1' : Set Point2), dist b2 z < s :=
        (Metric.infDist_lt_iff h_line_nonempty).mp h'
      rcases h'' with ⟨z, hz, hlt⟩
      have h3 : b2 ∈ Metric.thickening s ((lineThrough b1 b1') : Set Point2) := by
        rw [Metric.mem_thickening_iff]
        exact ⟨z, hz, hlt⟩
      exact hb2_far h3
    have h_area1 : D * s ≤ |cross2 (b2 - b1) (b1' - b1)| :=
      cross2_area_lower_bound (show D ≤ dist b1 b1' from le_of_lt h_dist) h_dist_line hne (by linarith) (by linarith)
    have h_cross_neg : cross2 (b2 - b1) (b2 - b1') = -cross2 (b2 - b1) (b1' - b1) := by
      simp [cross2] <;> ring
    have h_area : D * s ≤ |cross2 (b2 - b1) (b2 - b1')| := by
      rw [h_cross_neg]
      rw [abs_neg]
      exact h_area1
    set θ : ℝ := (D * s - 4 * r) / 5 with hθ_def
    have hθ_pos : 0 < θ := by
      have h : D * s > 4 * r := by linarith
      linarith
    have hθ_le_one : θ ≤ 1 := by
      have hD2 : D ≤ 2 := by
        calc D ≤ dist b1 b1' := le_of_lt h_dist
          _ = ‖b1 - b1'‖ := rfl
          _ = ‖b1' - b1‖ := by
            have h_eq : b1 - b1' = -(b1' - b1) := by abel
            rw [h_eq, norm_neg]
          _ ≤ ‖b1'‖ + ‖b1‖ := norm_sub_le _ _
          _ ≤ 2 := by linarith
      have hs2 : s ≤ 2 := by
        calc s ≤ Metric.infDist b2 (lineThrough b1 b1' : Set Point2) := h_dist_line
          _ ≤ dist b2 b1 := Metric.infDist_le_dist_of_mem lineThrough_contains_first
          _ = ‖b2 - b1‖ := rfl
          _ ≤ 2 := hu_norm
      have hr_nonneg : 0 ≤ r := by linarith
      have hDs : D * s ≤ 4 := by nlinarith
      rw [hθ_def]
      linarith [hDs]
    have h_angle_lower : θ ≤ ‖n1 - n2‖ :=
      angle_lower_bound_approx h_area hu_norm hv_norm n1 n2 hn1 hn2 hε1 hε2 (by linarith) hr1
    have hc1 : |inner ℝ (b2 - b1) n1| ≤ r := hε1
    have hc2 : |inner ℝ (b2 - b1') n2| ≤ r := hε2
    have h_ball : (Metric.thickening r (ℓ1 : Set Point2) ∩
        Metric.thickening r (ℓ2 : Set Point2)) ⊆
        Metric.closedBall b2 (6 * r / θ) :=
      stripIntersectionBall hr_pos hθ_pos hθ_le_one hfin1 hfin2 n1 n2 hn1 hn2
        hn1_orth hn2_orth h_angle_lower h_angle_upper hℓ1 hℓ2 hc1 hc2
    have hθ_lower : θ ≥ D * s / 10 := by
      rw [hθ_def]
      linarith
    have h_radius : 6 * r / θ ≤ 60 * r / (D * s) := by
      have hpos1 : 0 < θ := hθ_pos
      have hpos2 : 0 < D * s := mul_pos hD hs
      have h : 6 * r / θ ≤ 6 * r / (D * s / 10) := by
        gcongr
        <;> linarith
      have h2 : 6 * r / (D * s / 10) = 60 * r / (D * s) := by
        field_simp [hpos2.ne'] <;> ring
      rw [h2] at h
      exact h
    let R : ℝ := 60 * r / (D * s)
    have hR_pos : 0 < R := by positivity
    have hRδ : delta ≤ R := by
      have hpos : 0 < D * s := mul_pos hD hs
      have h1 : D * s ≤ 4 := by
        have hD2 : D ≤ 2 := by
          calc D ≤ dist b1 b1' := le_of_lt h_dist
            _ = ‖b1 - b1'‖ := rfl
            _ = ‖b1' - b1‖ := by
              have h_eq : b1 - b1' = -(b1' - b1) := by abel
              rw [h_eq, norm_neg]
            _ ≤ ‖b1'‖ + ‖b1‖ := norm_sub_le _ _
            _ ≤ 2 := by
              have hb1'_norm : ‖b1'‖ ≤ 1 := hb1'_ball
              have hb1_norm : ‖b1‖ ≤ 1 := hb1_ball
              linarith
        have hs2 : s ≤ 2 := by
          calc s ≤ Metric.infDist b2 (lineThrough b1 b1' : Set Point2) := h_dist_line
            _ ≤ dist b2 b1 := Metric.infDist_le_dist_of_mem lineThrough_contains_first
            _ = ‖b2 - b1‖ := rfl
            _ ≤ ‖b2‖ + ‖b1‖ := norm_sub_le _ _
            _ ≤ 2 := by
              have hb2_norm : ‖b2‖ ≤ 1 := hb2_ball
              have hb1_norm2 : ‖b1‖ ≤ 1 := hb1_ball
              linarith
        nlinarith
      have h3 : R ≥ 15 * r := by
        dsimp only [R]
        have h4 : 60 * r / (D * s) ≥ 15 * r := by
          have h5 : D * s ≤ 4 := h1
          have h6 : 0 < D * s := hpos
          have h7 : 60 / (D * s) ≥ 15 := by
            calc 60 / (D * s) ≥ 60 / 4 := by gcongr
              _ = 15 := by norm_num
          have h8 : 60 * r / (D * s) = (60 / (D * s)) * r := by
            field_simp [h6.ne'] <;> ring
          rw [h8]
          have h9 : 0 ≤ r := by linarith
          gcongr
        exact h4
      linarith [hr]
    have hS_sub : ∀ y ∈ S, dist y b2 ≤ R := by
      intro y hy
      have hy_cond := (Finset.mem_filter.mp hy).2
      have hy_in1 : y ∈ Metric.thickening r (ℓ1 : Set Point2) := hy_cond.2.1
      have hy_in2 : y ∈ Metric.thickening r (ℓ2 : Set Point2) := hy_cond.2.2
      have h_in_inter : y ∈ (Metric.thickening r (ℓ1 : Set Point2) ∩
          Metric.thickening r (ℓ2 : Set Point2)) := ⟨hy_in1, hy_in2⟩
      have h_in_ball : y ∈ Metric.closedBall b2 (6 * r / θ) := h_ball h_in_inter
      have h_dist_le : dist y b2 ≤ 6 * r / θ := h_in_ball
      linarith
    have hS_card : ↑S.card ≤ G2.ballCount b2 R := by
      have h_sub : S ⊆ G2.filter fun y => dist y b2 ≤ R := by
        intro y hy
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, hS_sub y hy⟩
      have h_card : S.card ≤ (G2.filter fun y => dist y b2 ≤ R).card := Finset.card_le_card h_sub
      have h_goal : (↑S.card : ENNReal) ≤ (↑(G2.filter fun y => dist y b2 ≤ R).card : ENNReal) :=
        Nat.cast_le.mpr h_card
      simpa [DiscreteSet.ballCount] using h_goal
    have h_frost : G2.ballCount b2 R ≤ C_F * Kakeya.realRpowENN R 1 * G2.enncard := by
      by_cases hR1 : R ≤ 1
      · exact hFrost2 b2 R hRδ hR1
      ·
        have hR_gt_one : 1 < R := by linarith
        have h1 : G2.ballCount b2 R ≤ G2.enncard := by
          have h2 : (G2.filter fun y => dist y b2 ≤ R) ⊆ G2 := Finset.filter_subset _ _
          have h3 : (G2.filter fun y => dist y b2 ≤ R).card ≤ G2.card := Finset.card_le_card h2
          have h4 : (↑(G2.filter fun y => dist y b2 ≤ R).card : ENNReal) ≤ (↑G2.card : ENNReal) :=
            Nat.cast_le.mpr h3
          simpa [DiscreteSet.ballCount, DiscreteSet.enncard] using h4
        have h2 : G2.enncard ≤ C_F * Kakeya.realRpowENN R 1 * G2.enncard := by
          by_cases hG2_empty : G2.enncard = 0
          · rw [hG2_empty] <;> simp
          · have h4 : (1 : ENNReal) ≤ C_F * Kakeya.realRpowENN R 1 := by
              have h5 : (1 : ENNReal) ≤ C_F := hC_F
              have h6 : (1 : ENNReal) ≤ Kakeya.realRpowENN R 1 := by
                simp [Kakeya.realRpowENN, hR_gt_one.le] <;> norm_num <;> linarith
              have h7' : Kakeya.realRpowENN R 1 ≤ C_F * Kakeya.realRpowENN R 1 := by
                calc Kakeya.realRpowENN R 1
                  = (1 : ENNReal) * Kakeya.realRpowENN R 1 := by simp
                _ ≤ C_F * Kakeya.realRpowENN R 1 := mul_le_mul' h5 (le_refl _)
              exact le_trans h6 h7'
            have h8 : G2.enncard ≤ C_F * Kakeya.realRpowENN R 1 * G2.enncard := by
              calc G2.enncard
                = (1 : ENNReal) * G2.enncard := by simp
              _ ≤ (C_F * Kakeya.realRpowENN R 1) * G2.enncard := by gcongr
            exact h8
        exact h1.trans h2
    have h_final : ↑S.card ≤ C_F * Kakeya.realRpowENN R 1 * G2.enncard :=
      hS_card.trans h_frost
    simpa [R] using h_final

/-- Case 3 upper bound: union bound over strip pairs, then sum over (b1,b1'). -/
lemma threeCase_case3 {delta lam r D s : ℝ}
    (hδ : 0 < delta) (hlam : 0 < lam)
    (hr : delta ≤ r) (hr1 : r ≤ 1)
    (hD : 0 < D) (hs : 0 < s)
    (hDsr : 8 * r ≤ D * s)
    {G1 G2 : DiscreteSet 2} (C_F : ENNReal)
    (hC_F : 1 ≤ C_F)
    (hFrost2 : G2.IsFrostman delta 1 C_F)
    (hG2_ball : G2.IsInUnitBall)
    (hG1_ball : G1.IsInUnitBall)
    (M : ℕ)
    (badLines : Point2 → Finset (AffineSubspace ℝ Point2))
    (h_lines_through : ∀ b1, ∀ ℓ ∈ badLines b1, b1 ∈ (ℓ : Set Point2))
    (h_fin : ∀ b1, ∀ ℓ ∈ badLines b1, Module.finrank ℝ ℓ.direction = 1)
    (h_max_strips : ∀ b1, (badLines b1).card ≤ M) :
    ∑ b1 ∈ G1, ∑ b1' ∈ G1,
      ((G2.filter fun b2 =>
        (D < dist b1 b1') ∧
        (b2 ∉ Metric.thickening s ((lineThrough b1 b1') : Set Point2)) ∧
        (∃ ℓ1 ∈ badLines b1, b2 ∈ Metric.thickening r (ℓ1 : Set Point2)) ∧
        (∃ ℓ2 ∈ badLines b1', b2 ∈ Metric.thickening r (ℓ2 : Set Point2))).card : ENNReal)
    ≤ C_F * Kakeya.realRpowENN (60 * r / (D * s)) 1 * (M : ENNReal) * (M : ENNReal) *
        G1.enncard * G1.enncard * G2.enncard := by
  set B : ENNReal := C_F * Kakeya.realRpowENN (60 * r / (D * s)) 1 * G2.enncard with hB
  have h_main : ∀ b1 ∈ G1, ∀ b1' ∈ G1,
      ↑(G2.filter fun b2 =>
        (D < dist b1 b1') ∧
        (b2 ∉ Metric.thickening s ((lineThrough b1 b1') : Set Point2)) ∧
        (∃ ℓ1 ∈ badLines b1, b2 ∈ Metric.thickening r (ℓ1 : Set Point2)) ∧
        (∃ ℓ2 ∈ badLines b1', b2 ∈ Metric.thickening r (ℓ2 : Set Point2))).card
      ≤ (M : ENNReal) * (M : ENNReal) * B := by
    intro b1 hb1 b1' hb1'
    by_cases h_dist : D < dist b1 b1'
    ·
      let L1 := badLines b1
      let L2 := badLines b1'
      let f : AffineSubspace ℝ Point2 × AffineSubspace ℝ Point2 → Finset Point2 :=
        fun p => G2.filter fun b2 =>
          b2 ∉ Metric.thickening s ((lineThrough b1 b1') : Set Point2) ∧
          b2 ∈ Metric.thickening r (p.1 : Set Point2) ∧
          b2 ∈ Metric.thickening r (p.2 : Set Point2)
      have h_union : (G2.filter fun b2 =>
          (D < dist b1 b1') ∧
          (b2 ∉ Metric.thickening s ((lineThrough b1 b1') : Set Point2)) ∧
          (∃ ℓ1 ∈ L1, b2 ∈ Metric.thickening r (ℓ1 : Set Point2)) ∧
          (∃ ℓ2 ∈ L2, b2 ∈ Metric.thickening r (ℓ2 : Set Point2))) =
          Finset.biUnion (L1 ×ˢ L2) f := by
        ext b2
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_product]
        <;> aesop
      rw [h_union]
      have h_card_nat : (Finset.biUnion (L1 ×ˢ L2) f).card ≤
          ∑ p ∈ (L1 ×ˢ L2), (f p).card := Finset.card_biUnion_le
      have h_card1 : (↑(Finset.biUnion (L1 ×ˢ L2) f).card : ENNReal) ≤
          (↑(∑ p ∈ (L1 ×ˢ L2), (f p).card) : ENNReal) := by
        exact_mod_cast h_card_nat
      have h_sum_cast : (↑(∑ p ∈ (L1 ×ˢ L2), (f p).card) : ENNReal) =
          ∑ p ∈ (L1 ×ˢ L2), (↑(f p).card : ENNReal) := by
        rw [Nat.cast_sum]
      have h_each : ∀ p ∈ (L1 ×ˢ L2), (↑(f p).card : ENNReal) ≤ B := by
        rintro ⟨ℓ1, ℓ2⟩ hp
        have hℓ1_in : ℓ1 ∈ L1 := (Finset.mem_product.mp hp).1
        have hℓ2_in : ℓ2 ∈ L2 := (Finset.mem_product.mp hp).2
        have h_b1_in : b1 ∈ (ℓ1 : Set Point2) := h_lines_through b1 ℓ1 hℓ1_in
        have h_b1'_in : b1' ∈ (ℓ2 : Set Point2) := h_lines_through b1' ℓ2 hℓ2_in
        have hb1_ball : ‖b1‖ ≤ 1 := by
          have h : dist b1 0 ≤ 1 := hG1_ball b1 hb1
          simpa [dist_eq_norm] using h
        have hb1'_ball : ‖b1'‖ ≤ 1 := by
          have h : dist b1' 0 ≤ 1 := hG1_ball b1' hb1'
          simpa [dist_eq_norm] using h
        have hfin1 : Module.finrank ℝ ℓ1.direction = 1 := h_fin b1 ℓ1 hℓ1_in
        have hfin2 : Module.finrank ℝ ℓ2.direction = 1 := h_fin b1' ℓ2 hℓ2_in
        exact case3_per_strip_pair hδ hr hr1 hD hs hDsr C_F hC_F hFrost2 hG2_ball
          hb1_ball hb1'_ball h_dist hfin1 hfin2 h_b1_in h_b1'_in
      have h_card_prod : (↑((L1 ×ˢ L2).card) : ENNReal) = (↑L1.card : ENNReal) * (↑L2.card : ENNReal) := by
        have h : (L1 ×ˢ L2).card = L1.card * L2.card := Finset.card_product L1 L2
        rw [h] <;> simp [Nat.cast_mul]
      have h_sum3 : ∑ p ∈ (L1 ×ˢ L2), (↑(f p).card : ENNReal) ≤ ↑((L1 ×ˢ L2).card) * B := by
        calc
          ∑ p ∈ (L1 ×ˢ L2), (↑(f p).card : ENNReal)
            ≤ ∑ p ∈ (L1 ×ˢ L2), B := Finset.sum_le_sum h_each
          _ = ↑((L1 ×ˢ L2).card) * B := by
            rw [Finset.sum_const] <;> simp [nsmul_eq_mul]
      have h_sum2 : ∑ p ∈ (L1 ×ˢ L2), (↑(f p).card : ENNReal) ≤ (↑L1.card * ↑L2.card) * B := by
        rw [← h_card_prod]
        exact h_sum3
      have h1 : ↑L1.card ≤ (M : ENNReal) := by exact_mod_cast h_max_strips b1
      have h2 : ↑L2.card ≤ (M : ENNReal) := by exact_mod_cast h_max_strips b1'
      calc
        (↑(Finset.biUnion (L1 ×ˢ L2) f).card : ENNReal)
          ≤ (↑(∑ p ∈ (L1 ×ˢ L2), (f p).card) : ENNReal) := h_card1
        _ = ∑ p ∈ (L1 ×ˢ L2), (↑(f p).card : ENNReal) := h_sum_cast
        _ ≤ (↑L1.card * ↑L2.card) * B := h_sum2
        _ ≤ (M : ENNReal) * (M : ENNReal) * B := by gcongr
    ·
      have h_filter_empty : (G2.filter fun b2 =>
          (D < dist b1 b1') ∧
          (b2 ∉ Metric.thickening s ((lineThrough b1 b1') : Set Point2)) ∧
          (∃ ℓ1 ∈ badLines b1, b2 ∈ Metric.thickening r (ℓ1 : Set Point2)) ∧
          (∃ ℓ2 ∈ badLines b1', b2 ∈ Metric.thickening r (ℓ2 : Set Point2))) = ∅ := by
        simp [h_dist]
      rw [h_filter_empty]
      simp
  have h_inner : ∀ b1 ∈ G1,
      ∑ b1' ∈ G1, ↑(G2.filter fun b2 =>
        (D < dist b1 b1') ∧
        (b2 ∉ Metric.thickening s ((lineThrough b1 b1') : Set Point2)) ∧
        (∃ ℓ1 ∈ badLines b1, b2 ∈ Metric.thickening r (ℓ1 : Set Point2)) ∧
        (∃ ℓ2 ∈ badLines b1', b2 ∈ Metric.thickening r (ℓ2 : Set Point2))).card
      ≤ (M : ENNReal) * (M : ENNReal) * B * G1.enncard := by
    intro b1 hb1
    calc
      ∑ b1' ∈ G1, _
        ≤ ∑ b1' ∈ G1, (M : ENNReal) * (M : ENNReal) * B :=
          Finset.sum_le_sum (fun b1' hb1' => h_main b1 hb1 b1' hb1')
      _ = G1.enncard * ((M : ENNReal) * (M : ENNReal) * B) := by
        rw [Finset.sum_const, DiscreteSet.enncard]
        simp [nsmul_eq_mul]
      _ = (M : ENNReal) * (M : ENNReal) * B * G1.enncard := by
        simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
  have h_sum : ∑ b1 ∈ G1, _ ≤ ∑ b1 ∈ G1, (M : ENNReal) * (M : ENNReal) * B * G1.enncard :=
    Finset.sum_le_sum h_inner
  have h_const : ∑ b1 ∈ G1, (M : ENNReal) * (M : ENNReal) * B * G1.enncard
      = G1.enncard * ((M : ENNReal) * (M : ENNReal) * B * G1.enncard) := by
    rw [Finset.sum_const, DiscreteSet.enncard]
    simp [nsmul_eq_mul]
  rw [h_const] at h_sum
  have h_goal :
      G1.enncard *
          ((M : ENNReal) * (M : ENNReal) * B *
            G1.enncard) =
        C_F *
            Kakeya.realRpowENN
              (60 * r / (D * s)) 1 *
          (M : ENNReal) * (M : ENNReal) *
          G1.enncard * G1.enncard * G2.enncard := by
    rw [hB]
    simp [mul_assoc, mul_comm, mul_left_comm]
  rwa [h_goal] at h_sum

end Kakeya.Assouad
