import MyLeanRepo.Kakeya.Assouad.LargeSlope.XZGridIncidenceStatement

/-!
# Three-prism xz-grid incidence bound

The x-projection of a vertical-chart tube inside a horizontal slab has
diameter strictly less than two grid widths, using the unit-direction
relation between x- and z-components. Hence it meets at most three half-open
grid columns.
-/

noncomputable section

open Metric Set

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

lemma direction_x_bound {delta : ℝ} {T : Kakeya.DeltaTube delta}
    (hvert : (1 / 2 : ℝ) ≤ |T.direction (2 : Fin 3)|) :
    |T.direction (0 : Fin 3)| ≤ Real.sqrt 3 / 2 := by
  have h1 : ‖T.direction‖ ^ 2 = ∑ i : Fin 3, (T.direction i) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq T.direction
  have h2 : ∑ i : Fin 3, (T.direction i) ^ 2 =
      (T.direction 0) ^ 2 + (T.direction 1) ^ 2 +
        (T.direction 2) ^ 2 := by
    simp [Fin.sum_univ_succ] <;> ring
  have h3 : ‖T.direction‖ ^ 2 = 1 := by
    rw [T.direction_unit] <;> norm_num
  have h4 : (T.direction 0) ^ 2 + (T.direction 1) ^ 2 +
      (T.direction 2) ^ 2 = 1 := by
    linarith [h1, h2, h3]
  have h5 : (T.direction 2) ^ 2 ≥ 1 / 4 := by
    have h6 : |T.direction 2| ≥ 1 / 2 := hvert
    have h7 : (T.direction 2) ^ 2 = |T.direction 2| ^ 2 := by
      rw [sq_abs]
    rw [h7]
    nlinarith
  have h8 : (T.direction 0) ^ 2 ≤ 3 / 4 := by
    nlinarith
  have h9 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
    calc
      (Real.sqrt 3 / 2) ^ 2 = (Real.sqrt 3) ^ 2 / 4 := by ring
      _ = 3 / 4 := by
        rw [Real.sq_sqrt (by norm_num)] <;> ring
  have h10 : |T.direction 0| ^ 2 ≤ (Real.sqrt 3 / 2) ^ 2 := by
    have h11 : |T.direction 0| ^ 2 = (T.direction 0) ^ 2 := by
      rw [sq_abs]
    rw [h11, h9]
    exact h8
  have h12 : 0 ≤ |T.direction 0| := abs_nonneg _
  have h13 : 0 ≤ Real.sqrt 3 / 2 := by positivity
  nlinarith

lemma tube_slab_x_diam_refined
    {delta a b : ℝ} (hdelta : 0 < delta) (hab : a < b)
    {T : Kakeya.DeltaTube delta}
    (hvert : (1 / 2 : ℝ) ≤ |T.direction (2 : Fin 3)|) :
    ∀ x y : Point3, x ∈ T.carrier ∩ horizontalSlab a b →
      y ∈ T.carrier ∩ horizontalSlab a b →
      |x (0 : Fin 3) - y (0 : Fin 3)| ≤
        Real.sqrt 3 * (b - a) +
          (2 + 2 * Real.sqrt 3) * delta := by
  set W : ℝ := b - a with hW_def
  have hW : 0 < W := by linarith
  set d0 : ℝ := T.direction (0 : Fin 3) with hd0_def
  set d2 : ℝ := T.direction (2 : Fin 3) with hd2_def
  have h_d0_bound : |d0| ≤ Real.sqrt 3 / 2 :=
    direction_x_bound hvert
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
  have hnx : ‖x - ax‖ ≤ delta := by
    simpa [dist_eq_norm] using hdx
  have hny : ‖y - ay‖ ≤ delta := by
    simpa [dist_eq_norm] using hdy
  have h_x2 : x (2 : Fin 3) ∈ Set.Icc a b := hx.2
  have h_y2 : y (2 : Fin 3) ∈ Set.Icc a b := hy.2
  have h_ax2 : |x (2 : Fin 3) - ax (2 : Fin 3)| ≤ delta := by
    have h : |x (2 : Fin 3) - ax (2 : Fin 3)| ≤ ‖x - ax‖ :=
      coord_abs_le_norm (x - ax) 2
    linarith
  have h_ay2 : |y (2 : Fin 3) - ay (2 : Fin 3)| ≤ delta := by
    have h : |y (2 : Fin 3) - ay (2 : Fin 3)| ≤ ‖y - ay‖ :=
      coord_abs_le_norm (y - ay) 2
    linarith
  have h_ax2_val :
      ax (2 : Fin 3) = T.base (2 : Fin 3) + tx * d2 := by
    simp [hax_def, hd2_def] <;> abel
  have h_ay2_val :
      ay (2 : Fin 3) = T.base (2 : Fin 3) + ty * d2 := by
    simp [hay_def, hd2_def] <;> abel
  have h_ax_range :
      ax (2 : Fin 3) ∈ Set.Icc (a - delta) (b + delta) := by
    rw [h_ax2_val] <;>
      constructor <;>
        linarith [h_x2.1, h_x2.2, abs_le.mp h_ax2]
  have h_ay_range :
      ay (2 : Fin 3) ∈ Set.Icc (a - delta) (b + delta) := by
    rw [h_ay2_val] <;>
      constructor <;>
        linarith [h_y2.1, h_y2.2, abs_le.mp h_ay2]
  have h_diff :
      |ax (2 : Fin 3) - ay (2 : Fin 3)| ≤ W + 2 * delta := by
    rw [abs_le] <;>
      constructor <;>
        linarith [h_ax_range.1, h_ax_range.2,
          h_ay_range.1, h_ay_range.2]
  have h_diff2 : |(tx - ty) * d2| ≤ W + 2 * delta := by
    have h_eq :
        ax (2 : Fin 3) - ay (2 : Fin 3) = (tx - ty) * d2 := by
      rw [h_ax2_val, h_ay2_val] <;> ring
    rw [h_eq] at h_diff
    exact h_diff
  have h_abs_mul : |(tx - ty) * d2| = |tx - ty| * |d2| := by
    rw [abs_mul]
  rw [h_abs_mul] at h_diff2
  have h_tx_ty : |tx - ty| ≤ 2 * (W + 2 * delta) := by
    have h_pos : 0 < |d2| := abs_pos.mpr h_d2_ne_zero
    have h2 : |tx - ty| ≤ (W + 2 * delta) / |d2| := by
      calc
        |tx - ty| = (|tx - ty| * |d2|) / |d2| := by
          field_simp [h_pos.ne'] <;> ring
        _ ≤ (W + 2 * delta) / |d2| := by gcongr
    have h3 :
        (W + 2 * delta) / |d2| ≤ 2 * (W + 2 * delta) := by
      have h4 : 1 / |d2| ≤ 2 := by
        calc
          1 / |d2| ≤ 1 / (1 / 2 : ℝ) := by gcongr
          _ = 2 := by norm_num
      have h5 : 0 ≤ W + 2 * delta := by linarith
      calc
        (W + 2 * delta) / |d2|
            = (W + 2 * delta) * (1 / |d2|) := by ring
        _ ≤ (W + 2 * delta) * 2 := by gcongr
        _ = 2 * (W + 2 * delta) := by ring
    linarith
  have h_ax0_val :
      ax (0 : Fin 3) = T.base (0 : Fin 3) + tx * d0 := by
    simp [hax_def, hd0_def] <;> abel
  have h_ay0_val :
      ay (0 : Fin 3) = T.base (0 : Fin 3) + ty * d0 := by
    simp [hay_def, hd0_def] <;> abel
  have h_ax0_diff :
      ax (0 : Fin 3) - ay (0 : Fin 3) = (tx - ty) * d0 := by
    rw [h_ax0_val, h_ay0_val] <;> ring
  have h_ax0_abs :
      |ax (0 : Fin 3) - ay (0 : Fin 3)| ≤
        |tx - ty| * (Real.sqrt 3 / 2) := by
    rw [h_ax0_diff]
    calc
      |(tx - ty) * d0| = |tx - ty| * |d0| := by rw [abs_mul]
      _ ≤ |tx - ty| * (Real.sqrt 3 / 2) := by gcongr
  have h_x0_ax0 :
      |x (0 : Fin 3) - ax (0 : Fin 3)| ≤ delta := by
    have h : |x (0 : Fin 3) - ax (0 : Fin 3)| ≤ ‖x - ax‖ :=
      coord_abs_le_norm (x - ax) 0
    linarith
  have h_y0_ay0 :
      |y (0 : Fin 3) - ay (0 : Fin 3)| ≤ delta := by
    have h : |y (0 : Fin 3) - ay (0 : Fin 3)| ≤ ‖y - ay‖ :=
      coord_abs_le_norm (y - ay) 0
    linarith
  have h_decomp :
      x (0 : Fin 3) - y (0 : Fin 3) =
        (x (0 : Fin 3) - ax (0 : Fin 3)) +
          (ax (0 : Fin 3) - ay (0 : Fin 3)) -
            (y (0 : Fin 3) - ay (0 : Fin 3)) := by
    abel
  rw [h_decomp]
  have h_tri :
      |(x 0 - ax 0) + (ax 0 - ay 0) - (y 0 - ay 0)| ≤
        |x 0 - ax 0| + |ax 0 - ay 0| + |y 0 - ay 0| := by
    have h1 :
        |(x 0 - ax 0) + (ax 0 - ay 0) - (y 0 - ay 0)| ≤
          |(x 0 - ax 0) + (ax 0 - ay 0)| + |y 0 - ay 0| :=
      abs_sub _ _
    have h2 :
        |(x 0 - ax 0) + (ax 0 - ay 0)| ≤
          |x 0 - ax 0| + |ax 0 - ay 0| :=
      abs_add_le _ _
    linarith
  calc
    _ ≤ |x 0 - ax 0| + |ax 0 - ay 0| + |y 0 - ay 0| := h_tri
    _ ≤ delta + |tx - ty| * (Real.sqrt 3 / 2) + delta := by
      gcongr
    _ ≤ delta + 2 * (W + 2 * delta) * (Real.sqrt 3 / 2) +
        delta := by
      gcongr
    _ = Real.sqrt 3 * W + (2 + 2 * Real.sqrt 3) * delta := by
      ring

lemma refined_diam_lt_two_W {W delta : ℝ}
    (hW : 0 < W) (hdelta : 0 < delta)
    (h : 32 * delta ≤ W) :
    Real.sqrt 3 * W + (2 + 2 * Real.sqrt 3) * delta < 2 * W := by
  have h_sqrt3_lt : Real.sqrt 3 < 31 / 17 := by
    have h1 : (0 : ℝ) ≤ 3 := by norm_num
    have h2pos : (0 : ℝ) ≤ 31 / 17 := by norm_num
    have h3sq : (3 : ℝ) < ((31 / 17 : ℝ)) ^ 2 := by norm_num
    exact (Real.sqrt_lt h1 h2pos).mpr h3sq
  have hdelta_le : delta ≤ W / 32 := by linarith
  calc
    Real.sqrt 3 * W + (2 + 2 * Real.sqrt 3) * delta
        ≤ Real.sqrt 3 * W +
            (2 + 2 * Real.sqrt 3) * (W / 32) := by
      gcongr <;> linarith
    _ = W * (Real.sqrt 3 + (2 + 2 * Real.sqrt 3) / 32) := by
      ring
    _ < W * 2 := by
      have h4 :
          Real.sqrt 3 + (2 + 2 * Real.sqrt 3) / 32 < 2 := by
        linarith [h_sqrt3_lt]
      exact mul_lt_mul_of_pos_left h4 hW
    _ = 2 * W := by ring

lemma grid_meets_at_most_three
    {W : ℝ} (hW : 0 < W) {x₀ : ℝ}
    {A : Set ℝ} (hA : ∀ x y, x ∈ A → y ∈ A → |x - y| < 2 * W)
    (s : Finset ℤ) :
    (s.filter fun k : ℤ =>
      (A ∩ Set.Ico (x₀ + (k : ℝ) * W)
        (x₀ + ((k : ℝ) + 1) * W)).Nonempty).card ≤ 3 := by
  let S : Finset ℤ := s.filter fun k : ℤ =>
    (A ∩ Set.Ico (x₀ + (k : ℝ) * W)
      (x₀ + ((k : ℝ) + 1) * W)).Nonempty
  by_contra h
  have h4 : 4 ≤ S.card := by linarith
  have hS_nonempty : S.Nonempty := Finset.card_pos.mp (by linarith)
  let kmin : ℤ := S.min' hS_nonempty
  let kmax : ℤ := S.max' hS_nonempty
  have hkmin : kmin ∈ S := Finset.min'_mem S hS_nonempty
  have hkmax : kmax ∈ S := Finset.max'_mem S hS_nonempty
  have hdiff : 3 ≤ kmax - kmin := by
    by_contra hdiff'
    have hdiff_le : kmax - kmin ≤ 2 := by linarith
    have hsubset : S ⊆ Finset.Icc kmin (kmin + 2) := by
      intro k hk
      have hkmin_le : kmin ≤ k := Finset.min'_le S k hk
      have hkmax_ge : k ≤ kmax := Finset.le_max' S k hk
      exact Finset.mem_Icc.mpr ⟨hkmin_le, by linarith⟩
    have hcard : S.card ≤ (Finset.Icc kmin (kmin + 2)).card :=
      Finset.card_le_card hsubset
    have hinter :
        Finset.Icc kmin (kmin + 2) = {kmin, kmin + 1, kmin + 2} := by
      ext x
      simp [Finset.mem_Icc] <;> omega
    rw [hinter] at hcard
    simp at hcard
    linarith
  have hmin_nonempty :
      (A ∩ Set.Ico (x₀ + (kmin : ℝ) * W)
        (x₀ + ((kmin : ℝ) + 1) * W)).Nonempty :=
    (Finset.mem_filter.mp hkmin).2
  have hmax_nonempty :
      (A ∩ Set.Ico (x₀ + (kmax : ℝ) * W)
        (x₀ + ((kmax : ℝ) + 1) * W)).Nonempty :=
    (Finset.mem_filter.mp hkmax).2
  rcases hmin_nonempty with ⟨pmin, hpminA, hpminI⟩
  rcases hmax_nonempty with ⟨pmax, hpmaxA, hpmaxI⟩
  have hkmax_ge : (kmin : ℝ) + 3 ≤ (kmax : ℝ) := by
    exact_mod_cast (show kmin + 3 ≤ kmax by linarith)
  have hpmax_ge : pmax ≥ x₀ + ((kmin : ℝ) + 3) * W := by
    calc
      pmax ≥ x₀ + (kmax : ℝ) * W := hpmaxI.1
      _ ≥ x₀ + ((kmin : ℝ) + 3) * W := by gcongr
  have hpmin_lt :
      pmin < x₀ + ((kmin : ℝ) + 1) * W := hpminI.2
  have hmain : pmax - pmin > 2 * W := by linarith
  have habs : |pmax - pmin| = pmax - pmin :=
    abs_of_pos (by linarith)
  have hcontra := hA pmax pmin hpmaxA hpminA
  rw [habs] at hcontra
  linarith

theorem large_slope_xz_grid_three_incidence :
    LargeSlopeXZGridThreeIncidenceStatement := by
  intro delta a b x₀ T s hdelta hab h32delta hvert
  set W : ℝ := b - a with hW_def
  have hW : 0 < W := by linarith
  let v : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  have hv : ‖v‖ = 1 := by
    rw [PiLp.norm_single] <;> norm_num
  let A : Set ℝ :=
    scalarProjection v (T.carrier ∩ horizontalSlab a b)
  have hA_diam :
      ∀ x y : ℝ, x ∈ A → y ∈ A → |x - y| < 2 * W := by
    intro x y hx hy
    rcases hx with ⟨p, hp, rfl⟩
    rcases hy with ⟨q, hq, rfl⟩
    have hinner_p : inner ℝ p v = p (0 : Fin 3) := by
      rw [EuclideanSpace.inner_single_right] <;> simp
    have hinner_q : inner ℝ q v = q (0 : Fin 3) := by
      rw [EuclideanSpace.inner_single_right] <;> simp
    have h_goal : |inner ℝ p v - inner ℝ q v| < 2 * W := by
      rw [hinner_p, hinner_q]
      have hdiam :
          |p (0 : Fin 3) - q (0 : Fin 3)| ≤
            Real.sqrt 3 * W +
              (2 + 2 * Real.sqrt 3) * delta :=
        tube_slab_x_diam_refined hdelta hab hvert p q hp hq
      exact
        hdiam.trans_lt
          (refined_diam_lt_two_W hW hdelta h32delta)
    simpa using h_goal
  have hincidence :
      ∀ k ∈ s, (T.carrier ∩ xzGridPrism x₀ a b k).Nonempty →
        (A ∩ Set.Ico (x₀ + (k : ℝ) * W)
          (x₀ + ((k : ℝ) + 1) * W)).Nonempty := by
    intro k _ hk
    rcases hk with ⟨p, hpT, hpP⟩
    have hp_slab :
        p ∈ T.carrier ∩ horizontalSlab a b := ⟨hpT, hpP.2⟩
    have hinner : inner ℝ p v = p (0 : Fin 3) := by
      rw [EuclideanSpace.inner_single_right] <;> simp
    have hpA : inner ℝ p v ∈ A := ⟨p, hp_slab, rfl⟩
    rw [hinner] at hpA
    exact ⟨p (0 : Fin 3), hpA, hpP.1⟩
  let SA : Finset ℤ := s.filter fun k : ℤ =>
    (A ∩ Set.Ico (x₀ + (k : ℝ) * W)
      (x₀ + ((k : ℝ) + 1) * W)).Nonempty
  let ST : Finset ℤ := s.filter fun k : ℤ =>
    (T.carrier ∩ xzGridPrism x₀ a b k).Nonempty
  have hsubset : ST ⊆ SA := by
    intro k hk
    have hks : k ∈ s := (Finset.mem_filter.mp hk).1
    have hk_nonempty :
        (T.carrier ∩ xzGridPrism x₀ a b k).Nonempty :=
      (Finset.mem_filter.mp hk).2
    exact
      Finset.mem_filter.mpr
        ⟨hks, hincidence k hks hk_nonempty⟩
  exact
    (Finset.card_le_card hsubset).trans
      (grid_meets_at_most_three hW hA_diam s)

end Kakeya.Assouad
