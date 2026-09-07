import MyLeanRepo.Kakeya.Streamlined.Basic
import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.Families
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Position grid in a ball

Constructs a finite `s`-separated grid whose `sqrt 3 / 2 * s` neighborhood
covers a closed ball of radius `R`, with an explicit cubic cardinality bound.
-/

noncomputable section

open MeasureTheory Metric Finset

namespace Kakeya.Streamlined.GeometricLemmas

private def e0 : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
private def e1 : Point3 := EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
private def e2 : Point3 := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)

private def gridPoint (s : ℝ) (i j k : ℤ) : Point3 :=
  ((i : ℝ) * s) • e0 + ((j : ℝ) * s) • e1 + ((k : ℝ) * s) • e2

private def coordOf (q : ℤ × ℤ × ℤ) (idx : Fin 3) : ℤ :=
  match idx with
  | 0 => q.1
  | 1 => q.2.1
  | 2 => q.2.2

private lemma gridPoint_coord (s : ℝ) (i j k : ℤ) (idx : Fin 3) :
    (gridPoint s i j k) idx =
      (match idx with | 0 => (i : ℝ) | 1 => (j : ℝ) | 2 => (k : ℝ)) * s := by
  fin_cases idx <;> simp [gridPoint, e0, e1, e2, Pi.add_apply, Pi.smul_apply] <;> ring

private lemma norm_sq_eq (x : Point3) : ‖x‖ ^ 2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
  have h : ‖x‖ ^ 2 = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm
  rw [h]
  have h2 : inner ℝ x x = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
    simp [inner, Fin.sum_univ_succ] <;> ring
  exact h2

private lemma coord_le_norm (x : Point3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have h_sum2 : ‖x‖^2 = ∑ j : Fin 3, (x j)^2 := by
    have h : ‖x‖^2 = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm
    rw [h]
    have h2 : inner ℝ x x = ∑ j : Fin 3, (x j)^2 := by
      simp [inner, Fin.sum_univ_succ] <;> ring
    exact h2
  have h1 : (x i)^2 ≤ ∑ j : Fin 3, (x j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have h1' : (x i)^2 ≤ ‖x‖^2 := by rw [h_sum2] <;> exact h1
  have h2 : |x i|^2 = (x i)^2 := by rw [sq_abs]
  have h3 : |x i|^2 ≤ ‖x‖^2 := by rw [h2] <;> exact h1'
  have h4 : 0 ≤ |x i| := by positivity
  have h5 : 0 ≤ ‖x‖ := by positivity
  by_contra h6
  have h7 : ‖x‖ < |x i| := by linarith
  have h8 : ‖x‖^2 < |x i|^2 := by nlinarith
  exact not_le.mpr h8 h3

private lemma roundTo_dist (x s : ℝ) (hs : 0 < s) :
    |x - (Int.floor (x / s + 1 / 2) : ℝ) * s| ≤ s / 2 := by
  set i : ℤ := Int.floor (x / s + 1 / 2) with hi
  have h1 : (i : ℝ) ≤ x / s + 1 / 2 := Int.floor_le _
  have h2 : x / s + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : -(1 / 2 : ℝ) ≤ x / s - (i : ℝ) := by linarith
  have h4 : x / s - (i : ℝ) ≤ 1 / 2 := by linarith
  have h5 : |x / s - (i : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨h3, h4⟩
  have h6 : x - (i : ℝ) * s = s * (x / s - (i : ℝ)) := by field_simp [hs.ne']
  rw [h6, abs_mul, abs_of_pos hs]
  have h8 : s * |x / s - (i : ℝ)| ≤ s * (1 / 2 : ℝ) := by gcongr
  linarith

private lemma roundTo_bound_general (x s R : ℝ) (hs : 0 < s) (hR : 0 < R)
    (hx : |x| ≤ R) (N : ℕ) (hN : (N : ℝ) ≥ R / s + 1 / 2) :
    |(Int.floor (x / s + 1 / 2) : ℝ)| ≤ (N : ℝ) := by
  set i : ℤ := Int.floor (x / s + 1 / 2) with hi
  have h_rd : |x - (i : ℝ) * s| ≤ s / 2 := roundTo_dist x s hs
  have h1 : |(i : ℝ) * s| ≤ |x| + s / 2 := by
    have h2 : (i : ℝ) * s = x - (x - (i : ℝ) * s) := by ring
    rw [h2]
    have h3 : |x - (x - (i : ℝ) * s)| ≤ |x| + |x - (i : ℝ) * s| := by
      exact abs_sub x (x - (i : ℝ) * s)
    exact h3.trans (by gcongr)
  have h4 : |(i : ℝ)| * s ≤ |x| + s / 2 := by
    have h5 : |(i : ℝ) * s| = |(i : ℝ)| * s := by rw [abs_mul, abs_of_nonneg hs.le]
    rw [h5] at h1
    exact h1
  have h6 : |(i : ℝ)| ≤ |x| / s + 1 / 2 := by
    calc |(i : ℝ)| = (|(i : ℝ)| * s) / s := by field_simp [hs.ne'] <;> ring
      _ ≤ (|x| + s / 2) / s := by gcongr
      _ = |x| / s + 1 / 2 := by field_simp [hs.ne'] <;> ring
  have h7 : |x| / s ≤ R / s := by gcongr
  have h8 : |(i : ℝ)| ≤ R / s + 1 / 2 := by linarith
  exact le_trans h8 hN

/--
For positive `s` and `R`, a closed ball of radius `R` admits a finite
`s`-separated grid with covering radius `sqrt 3 / 2 * s` and cardinality at
most `64 * (R + s)^3 / s^3`.
-/
lemma position_grid (s : ℝ) (hs : 0 < s) (R : ℝ) (hR : 0 < R) :
    ∃ (points : Finset Point3),
      (∀ m : Point3, ‖m‖ ≤ R → ∃ p ∈ points, ‖m - p‖ ≤ Real.sqrt 3 / 2 * s) ∧
      (∀ p1 ∈ points, ∀ p2 ∈ points, p1 ≠ p2 → ‖p1 - p2‖ ≥ s) ∧
      (points.card : ℝ) ≤ 64 * (R + s)^3 / s^3 := by
  classical
  let N : ℕ := Nat.ceil (R / s + 1 / 2)
  have hN_ge : (N : ℝ) ≥ R / s + 1 / 2 := Nat.le_ceil (R / s + 1 / 2)
  have hN_pos : 0 < N := by
    apply Nat.ceil_pos.mpr
    positivity

  let Z : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let points : Finset Point3 :=
    Finset.image (fun p : ℤ × ℤ × ℤ => gridPoint s p.1 p.2.1 p.2.2) (Z ×ˢ Z ×ˢ Z)

  have hZ_card : Z.card = 2 * N + 1 := by simp [Z] <;> omega
  have hPoints_card : points.card ≤ (Z.card)^3 := by
    have h : points.card ≤ (Z ×ˢ Z ×ˢ Z).card := Finset.card_image_le
    have h2 : (Z ×ˢ Z ×ˢ Z).card = (Z.card)^3 := by
      simp [Finset.card_product] <;> ring
    rw [h2] at h
    exact h

  have hN_bound : (N : ℝ) ≤ R / s + 3 / 2 := by
    have h1 : (N : ℝ) ≤ R / s + 1 / 2 + 1 := Nat.ceil_lt_add_one (by positivity) |>.le
    linarith

  have h_linear : 2 * (N : ℝ) + 1 ≤ 4 * (R + s) / s := by
    have h_one_le : 1 ≤ (R + s) / s := by
      rw [one_le_div hs] <;> linarith
    have h_step : 2 ≤ 2 * ((R + s) / s) := by
      calc 2 = 2 * 1 := by ring
        _ ≤ 2 * ((R + s) / s) := by gcongr
    calc 2 * (N : ℝ) + 1 ≤ 2 * (R / s + 3 / 2) + 1 := by gcongr
      _ = 2 * R / s + 4 := by ring
      _ = 2 * (R + s) / s + 2 := by field_simp [hs.ne'] <;> ring
      _ ≤ 2 * (R + s) / s + 2 * ((R + s) / s) := by
        exact add_le_add_right h_step (2 * (R + s) / s)
      _ = 4 * (R + s) / s := by ring

  have h_card_bound : (points.card : ℝ) ≤ 64 * (R + s)^3 / s^3 := by
    have h1 : (points.card : ℝ) ≤ ((Z.card : ℝ))^3 := by exact_mod_cast hPoints_card
    have h2 : (Z.card : ℝ) = 2 * (N : ℝ) + 1 := by
      rw [hZ_card] <;> norm_cast <;> ring
    rw [h2] at h1
    have h3 : ((2 * (N : ℝ) + 1)^3) ≤ (4 * (R + s) / s)^3 := by gcongr
    have h4 : (4 * (R + s) / s)^3 = 64 * (R + s)^3 / s^3 := by
      field_simp [hs.ne'] <;> ring
    rw [h4] at h3
    exact h1.trans h3

  have h_cover : ∀ m : Point3, ‖m‖ ≤ R →
      ∃ p ∈ points, ‖m - p‖ ≤ Real.sqrt 3 / 2 * s := by
    intro m hm
    let i : ℤ := Int.floor (m 0 / s + 1 / 2)
    let j : ℤ := Int.floor (m 1 / s + 1 / 2)
    let k : ℤ := Int.floor (m 2 / s + 1 / 2)
    have h0b : |m 0| ≤ R := coord_le_norm m 0 |>.trans hm
    have h1b : |m 1| ≤ R := coord_le_norm m 1 |>.trans hm
    have h2b : |m 2| ≤ R := coord_le_norm m 2 |>.trans hm
    have hi_in : i ∈ Z := by
      simp only [Z, Finset.mem_Icc]
      have hb : |(i : ℝ)| ≤ (N : ℝ) := roundTo_bound_general (m 0) s R hs hR h0b N hN_ge
      exact ⟨by exact_mod_cast (abs_le.mp hb).1, by exact_mod_cast (abs_le.mp hb).2⟩
    have hj_in : j ∈ Z := by
      simp only [Z, Finset.mem_Icc]
      have hb : |(j : ℝ)| ≤ (N : ℝ) := roundTo_bound_general (m 1) s R hs hR h1b N hN_ge
      exact ⟨by exact_mod_cast (abs_le.mp hb).1, by exact_mod_cast (abs_le.mp hb).2⟩
    have hk_in : k ∈ Z := by
      simp only [Z, Finset.mem_Icc]
      have hb : |(k : ℝ)| ≤ (N : ℝ) := roundTo_bound_general (m 2) s R hs hR h2b N hN_ge
      exact ⟨by exact_mod_cast (abs_le.mp hb).1, by exact_mod_cast (abs_le.mp hb).2⟩
    let p : Point3 := gridPoint s i j k
    have hp_in : p ∈ points := by
      apply Finset.mem_image.mpr
      exact ⟨(i, j, k), by simp [Z, hi_in, hj_in, hk_in], rfl⟩
    have h0 : |m 0 - p 0| ≤ s / 2 := by
      simp [p, gridPoint_coord] <;> exact roundTo_dist (m 0) s hs
    have h1 : |m 1 - p 1| ≤ s / 2 := by
      simp [p, gridPoint_coord] <;> exact roundTo_dist (m 1) s hs
    have h2 : |m 2 - p 2| ≤ s / 2 := by
      simp [p, gridPoint_coord] <;> exact roundTo_dist (m 2) s hs
    have h3 : (m 0 - p 0)^2 ≤ (s / 2)^2 := by
      have h31 : |m 0 - p 0|^2 ≤ (s / 2)^2 := by gcongr
      have h32 : |m 0 - p 0|^2 = (m 0 - p 0)^2 := by rw [sq_abs]
      exact h32 ▸ h31
    have h4 : (m 1 - p 1)^2 ≤ (s / 2)^2 := by
      have h41 : |m 1 - p 1|^2 ≤ (s / 2)^2 := by gcongr
      have h42 : |m 1 - p 1|^2 = (m 1 - p 1)^2 := by rw [sq_abs]
      exact h42 ▸ h41
    have h5 : (m 2 - p 2)^2 ≤ (s / 2)^2 := by
      have h51 : |m 2 - p 2|^2 ≤ (s / 2)^2 := by gcongr
      have h52 : |m 2 - p 2|^2 = (m 2 - p 2)^2 := by rw [sq_abs]
      exact h52 ▸ h51
    have h_norm2 : ‖m - p‖ ^ 2 =
        (m 0 - p 0)^2 + (m 1 - p 1)^2 + (m 2 - p 2)^2 :=
      norm_sq_eq (m - p)
    have h6 : ‖m - p‖ ^ 2 ≤ 3 * (s / 2)^2 := by rw [h_norm2] <;> linarith
    have h7 : 0 ≤ ‖m - p‖ := by positivity
    have h8 : ‖m - p‖ ≤ Real.sqrt (3 * (s / 2)^2) := by
      rw [← Real.sqrt_sq h7] <;> exact Real.sqrt_le_sqrt h6
    have h9 : Real.sqrt (3 * (s / 2)^2) = Real.sqrt 3 / 2 * s := by
      have h10 : 0 ≤ s := by positivity
      have h11 : 3 * (s / 2)^2 = (Real.sqrt 3 / 2 * s)^2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      rw [h11, Real.sqrt_sq (by positivity)]
    rw [h9] at h8
    exact ⟨p, hp_in, h8⟩

  have h_sep : ∀ p1 ∈ points, ∀ p2 ∈ points, p1 ≠ p2 → ‖p1 - p2‖ ≥ s := by
    intro p1 hp1 p2 hp2 hne
    rcases Finset.mem_image.mp hp1 with ⟨q1, hq1, rfl⟩
    rcases Finset.mem_image.mp hp2 with ⟨q2, hq2, rfl⟩
    have hqne : q1 ≠ q2 := by intro h; apply hne; rw [h]
    have h_coord : q1.1 ≠ q2.1 ∨ q1.2.1 ≠ q2.2.1 ∨ q1.2.2 ≠ q2.2.2 := by
      by_contra h'
      push Not at h'
      have h_eq : q1 = q2 := by
        ext <;> simp [h'] <;> tauto
      exact hqne h_eq
    rcases h_coord with (h | h | h)
    · exact sep_coord s hs 0 q1 q2 h
    · exact sep_coord s hs 1 q1 q2 h
    · exact sep_coord s hs 2 q1 q2 h

  exact ⟨points, h_cover, h_sep, h_card_bound⟩

where
  sep_coord (s : ℝ) (hs : 0 < s) (idx : Fin 3) (q1 q2 : ℤ × ℤ × ℤ)
      (h : coordOf q1 idx ≠ coordOf q2 idx) :
      ‖gridPoint s q1.1 q1.2.1 q1.2.2 -
          gridPoint s q2.1 q2.2.1 q2.2.2‖ ≥ s := by
    set v : Point3 :=
      gridPoint s q1.1 q1.2.1 q1.2.2 - gridPoint s q2.1 q2.2.1 q2.2.2 with hv
    let a : ℤ := coordOf q1 idx - coordOf q2 idx
    have ha_ne : a ≠ 0 := by
      simp only [a, sub_ne_zero]
      exact h
    have hvi : v idx = (a : ℝ) * s := by
      rw [hv]
      fin_cases idx <;> simp [gridPoint_coord, coordOf, Pi.sub_apply, a] <;> ring
    have h_int : 1 ≤ |a| := Int.one_le_abs ha_ne
    have h_cast : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast h_int
    have hdiff : |v idx| ≥ s := by
      rw [hvi, abs_mul]
      have h_pos : 0 ≤ s := by positivity
      rw [abs_of_nonneg h_pos]
      calc |(a : ℝ)| * s ≥ 1 * s := by gcongr
        _ = s := by ring
    have h10 : |v idx| ≤ ‖v‖ := coord_le_norm v idx
    exact le_trans hdiff h10

end Kakeya.Streamlined.GeometricLemmas
