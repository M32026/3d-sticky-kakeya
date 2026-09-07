import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.AssertionD
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeImageGeometry
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.VerticalChartPreservation
import Mathlib.Topology.MetricSpace.Thickening


/-!
# Covering construction for anisotropic tube images

Given a source δ-tube in the vertical chart, construct 3 ρ-tubes whose
union contains the image of the tube intersected with the horizontal slab.
-/

noncomputable section

open Kakeya.Assouad Metric

namespace Kakeya.Assouad

private lemma image_axis_vector_norm_sq_le {g_mid K S : ℝ}
    {dir : Point3} (hd_unit : ‖dir‖ = 1)
    (hg : |g_mid| ≤ 1) (hK : |K| ≤ 1) :
    ‖point3 (dir 0 + g_mid * dir 1) (K * dir 1) (S * dir 2)‖ ^ 2 ≤
      3 * (1 - (dir 2) ^ 2) + S ^ 2 * (dir 2) ^ 2 := by
  set d0 := dir 0 with hd0
  set d1 := dir 1 with hd1
  set d2 := dir 2 with hd2
  set Ad := point3 (d0 + g_mid * d1) (K * d1) (S * d2) with hAd
  have hunit2 : d0^2 + d1^2 + d2^2 = 1 := by
    have h : ‖dir‖^2 = d0^2 + d1^2 + d2^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_succ] <;> ring
    have h' : ‖dir‖^2 = 1 := by rw [hd_unit] <;> norm_num
    linarith
  have hAd2 : ‖Ad‖^2 = (d0 + g_mid * d1)^2 + (K * d1)^2 + (S * d2)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [hAd, Fin.sum_univ_succ, point3] <;> ring
  have h1 : (d0 + g_mid * d1)^2 ≤ 2 * (d0^2 + d1^2) := by
    have hcauchy : (d0 + g_mid * d1)^2 ≤ (1 + g_mid^2) * (d0^2 + d1^2) := by
      nlinarith [sq_nonneg (d0 * g_mid - d1)]
    have hgm2 : g_mid^2 ≤ 1 := by nlinarith [abs_le.mp hg]
    nlinarith
  have h2 : (K * d1)^2 ≤ d1^2 := by
    have hK2 : K^2 ≤ 1 := by nlinarith [abs_le.mp hK]
    nlinarith
  set X := (d0 + g_mid * d1)^2 + (K * d1)^2 with hX
  have hXle : X ≤ 3 * (1 - d2^2) := by
    have h5 : d0^2 + d1^2 = 1 - d2^2 := by linarith
    have h71 : X ≤ 2 * (d0^2 + d1^2) + d1^2 := by
      exact add_le_add h1 h2
    have h72 : 2 * (d0^2 + d1^2) + d1^2 ≤ 3 * (d0^2 + d1^2) := by
      have h73 : 0 ≤ d0^2 := by positivity
      nlinarith
    have h7 : X ≤ 3 * (d0^2 + d1^2) := h71.trans h72
    rw [h5] at h7
    exact h7
  change ‖Ad‖ ^ 2 ≤ 3 * (1 - d2 ^ 2) + S ^ 2 * d2 ^ 2
  rw [hAd2]
  nlinarith

private lemma image_axis_length_sq_gen {g_mid K S : ℝ} {c d W : ℝ}
    (hcd : c < d) (hW : 0 ≤ W)
    {dir : Point3} (hd_unit : ‖dir‖ = 1) (hd_z : 1 / 2 ≤ |dir 2|)
    (hg : |g_mid| ≤ 1) (hK : |K| ≤ 1)
    (hS_eq : S = 2 / (d - c)) :
    ((W / |dir 2|) *
      ‖point3 (dir 0 + g_mid * dir 1) (K * dir 1) (S * dir 2)‖) ^ 2 ≤
        9 * W^2 + (2 * W / (d - c))^2 := by
  set d2 := dir 2 with hd2
  set Ad := point3 (dir 0 + g_mid * dir 1) (K * dir 1) (S * dir 2) with hAd
  have hAd_bound : ‖Ad‖ ^ 2 ≤ 3 * (1 - d2 ^ 2) + S ^ 2 * d2 ^ 2 := by
    simpa [Ad, d2] using image_axis_vector_norm_sq_le hd_unit hg hK
  have hdz2 : d2^2 ≥ 1 / 4 := by
    have h : |d2| ≥ 1 / 2 := hd_z
    have h2 : d2^2 = |d2|^2 := by simp [sq_abs]
    rw [h2] <;> nlinarith
  have h_pos2 : 0 < d2^2 := by positivity
  have h_posdc : 0 < (d - c)^2 := by positivity
  have hS2 : S^2 = 4 / (d - c)^2 := by
    rw [hS_eq]
    field_simp [show (d - c) ≠ 0 by linarith] <;> ring
  have h3 : ((W / |d2|) * ‖Ad‖)^2 = W^2 / d2^2 * ‖Ad‖^2 := by
    calc
      ((W / |d2|) * ‖Ad‖)^2 = W^2 / |d2|^2 * ‖Ad‖^2 := by ring
      _ = W^2 / d2^2 * ‖Ad‖^2 := by rw [sq_abs]
  have hne : d2^2 ≠ 0 := h_pos2.ne'
  have hd2_ne : d2 ≠ 0 := by
    intro hd2
    rw [hd2] at h_pos2
    norm_num at h_pos2
  have h_cancel : W^2 / d2^2 * (S^2 * d2^2) = W^2 * S^2 := by
    have h1 : W^2 / d2^2 * (S^2 * d2^2) =
        (W^2 * S^2) * d2^2 / d2^2 := by
      rw [div_mul_eq_mul_div] <;> ring
    rw [h1]
    exact mul_div_cancel_right₀ (W^2 * S^2) hne
  have hscaled : W^2 / d2^2 * ‖Ad‖^2 ≤
      W^2 / d2^2 * (3 * (1 - d2^2) + S^2 * d2^2) :=
    mul_le_mul_of_nonneg_left hAd_bound (by positivity)
  have htransverse : W^2 / d2^2 * (3 * (1 - d2^2)) ≤ 9 * W^2 := by
    have hratio : 3 * (1 - d2^2) ≤ 9 * d2^2 := by nlinarith
    calc
      W^2 / d2^2 * (3 * (1 - d2^2))
          ≤ W^2 / d2^2 * (9 * d2^2) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 9 * W^2 := by
        field_simp [hd2_ne] <;> ring
  have hS_term : W^2 * S^2 = (2 * W / (d - c))^2 := by
    rw [hS2]
    field_simp [show d - c ≠ 0 by linarith] <;> ring
  rw [h3]
  calc
    W^2 / d2^2 * ‖Ad‖^2
        ≤ W^2 / d2^2 * (3 * (1 - d2^2) + S^2 * d2^2) := hscaled
    _ = W^2 / d2^2 * (3 * (1 - d2^2)) + W^2 * S^2 := by
      rw [mul_add, h_cancel]
    _ ≤ 9 * W^2 + W^2 * S^2 := add_le_add htransverse (le_refl _)
    _ = 9 * W^2 + (2 * W / (d - c))^2 := by rw [hS_term]

/--
Generalized axis image length bound for a z-window of width `W`.

The image of an axis subsegment with z-range `W` has length at most
`sqrt(9 * W^2 + (2*W/(d-c))^2)`.
-/
lemma image_axis_length_gen {g_mid K S : ℝ} {c d W : ℝ}
    (hcd : c < d) (hW : 0 ≤ W)
    {dir : Point3} (hd_unit : ‖dir‖ = 1) (hd_z : 1 / 2 ≤ |dir 2|)
    (hg : |g_mid| ≤ 1) (hK : |K| ≤ 1)
    (hS_eq : S = 2 / (d - c)) :
    (W / |dir 2|) *
      ‖point3 (dir 0 + g_mid * dir 1) (K * dir 1) (S * dir 2)‖ ≤
    Real.sqrt (9 * W^2 + (2 * W / (d - c))^2) := by
  have h_main := image_axis_length_sq_gen hcd hW hd_unit hd_z hg hK hS_eq
  set a := (W / |dir 2|) *
    ‖point3 (dir 0 + g_mid * dir 1) (K * dir 1) (S * dir 2)‖ with ha_def
  have ha_nonneg : 0 ≤ a :=
    mul_nonneg (div_nonneg hW (abs_nonneg (dir 2))) (by simp [norm_nonneg])
  have h_main2 : a^2 ≤ 9 * W^2 + (2 * W / (d - c))^2 := h_main
  have h_pos1 : 0 ≤ 9 * W^2 :=
    mul_nonneg (by norm_num) (sq_nonneg W)
  have h_pos2 : 0 ≤ (2 * W / (d - c))^2 := sq_nonneg _
  have h_pos : 0 ≤ 9 * W^2 + (2 * W / (d - c))^2 :=
    add_nonneg h_pos1 h_pos2
  have h_sqrt : Real.sqrt (a^2) ≤ Real.sqrt (9 * W^2 + (2 * W / (d - c))^2) :=
    Real.sqrt_le_sqrt h_main2
  have h_abs : Real.sqrt (a^2) = a := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ha_nonneg]
  rw [h_abs] at h_sqrt
  exact h_sqrt

/--
The extended image axis length (accounting for δ-thickening at slab boundaries)
is strictly less than 3 under the parameter bounds.
-/
lemma extended_image_axis_lt_3 {g_mid K S : ℝ} {c d delta : ℝ}
    (hdelta : 0 < delta) (hcd : c < d)
    {dir : Point3} (hd_unit : ‖dir‖ = 1) (hd_z : 1 / 2 ≤ |dir 2|)
    (hg : |g_mid| ≤ 1) (hK : |K| ≤ 1)
    (hS_eq : S = 2 / (d - c))
    (h_dc : d - c ≤ 1 / 25)
    (hdelta_small : delta ≤ 1 / 100)
    (hrho_small : 2 * delta / (d - c) ≤ 1 / 4) :
    ((d - c + 2 * delta) / |dir 2|) *
      ‖point3 (dir 0 + g_mid * dir 1) (K * dir 1) (S * dir 2)‖ < 3 := by
  set W := d - c + 2 * delta with hW_def
  have hW_nonneg : 0 ≤ W := by linarith
  have h_bound1 : W ≤ 3 / 50 := by linarith
  have h_rho : 2 * W / (d - c) = 2 + 2 * (2 * delta / (d - c)) := by
    have hpos : 0 < d - c := by linarith
    field_simp [hpos.ne'] <;> ring
  have h_main := image_axis_length_gen hcd hW_nonneg hd_unit hd_z hg hK hS_eq
  have h9 : 9 * W^2 ≤ 81 / 2500 := by
    have h : W ≤ 3 / 50 := h_bound1
    nlinarith
  have h_rho2 : (2 * W / (d - c))^2 ≤ (5 / 2 : ℝ)^2 := by
    rw [h_rho]
    have h : 2 + 2 * (2 * delta / (d - c)) ≤ 5 / 2 := by linarith [hrho_small]
    have h' : 0 ≤ 2 + 2 * (2 * delta / (d - c)) := by positivity
    nlinarith
  have h_total : 9 * W^2 + (2 * W / (d - c))^2 < 9 := by linarith
  have h_sqrt : Real.sqrt (9 * W^2 + (2 * W / (d - c))^2) < 3 := by
    have h_pos : 0 ≤ 9 * W^2 + (2 * W / (d - c))^2 := by positivity
    have h : Real.sqrt (9 * W^2 + (2 * W / (d - c))^2) < 3 := by
      rw [Real.sqrt_lt] <;> linarith
    exact h
  exact h_main.trans_lt h_sqrt

/--
Cover a segment of length `< 3` with three unit segments sharing one direction.
Also certifies the direction is in the vertical chart when `Q-P` is.
-/
lemma cover_segment_three {P Q : Point3} (h : dist P Q < 3)
    (hvert : P = Q ∨ (1 / 2 : ℝ) ≤ |(Q - P) 2| / ‖Q - P‖) :
    ∃ (b1 b2 b3 : Point3) (d : Point3), ‖d‖ = 1 ∧
      (1 / 2 : ℝ) ≤ |d 2| ∧
      ∀ x, (∃ t ∈ Set.Icc (0 : ℝ) 1, x = P + t • (Q - P)) →
        x ∈ Kakeya.unitSegment b1 d ∪ Kakeya.unitSegment b2 d ∪ Kakeya.unitSegment b3 d := by
  by_cases h0 : P = Q
  · let d : Point3 := EuclideanSpace.single 2 1
    have hd_unit : ‖d‖ = 1 := by simp [d] <;> norm_num
    have hd_vert : (1 / 2 : ℝ) ≤ |d 2| := by simp [d] <;> norm_num
    let b : Point3 := P - (1 / 2 : ℝ) • d
    refine' ⟨b, b, b, d, hd_unit, hd_vert, _⟩
    intro x hx
    rcases hx with ⟨t, _, h_eq⟩
    have hQ : Q - P = (0 : Point3) := by rw [h0] <;> simp
    have hPt : P + t • (Q - P) = P := by rw [hQ] <;> simp
    have h_x : x = P := by rw [h_eq, hPt]
    rw [h_x]
    have h_in : P ∈ Kakeya.unitSegment b d := by
      refine' ⟨1 / 2, by norm_num, _⟩
      simp [b] <;> abel
    simpa using h_in
  · let v := Q - P
    let L := ‖v‖
    have h_v_ne : v ≠ 0 := by
      intro hv
      have h_eq : Q = P := by simpa [v, sub_eq_zero] using hv
      exact h0 h_eq.symm
    have hL_pos : 0 < L := norm_pos_iff.mpr h_v_ne
    let d : Point3 := (1 / L) • v
    have hd_unit : ‖d‖ = 1 := by
      have h1 : ‖d‖ = |(1 / L : ℝ)| * ‖v‖ := by
        simpa [d, norm_smul] using rfl
      rw [h1]
      have h2 : |(1 / L : ℝ)| = 1 / L := by apply abs_of_pos; positivity
      rw [h2]
      have h3 : (1 / L) * L = 1 := by field_simp [hL_pos.ne'] <;> ring
      rw [h3] <;> norm_num
    have hL_lt_3 : L < 3 := by
      have h4 : dist P Q = ‖P - Q‖ := dist_eq_norm P Q
      have h5 : ‖P - Q‖ = ‖Q - P‖ := norm_sub_rev P Q
      rw [h4, h5] at h
      exact h
    have hne : P ≠ Q := by tauto
    have hvert' : (1 / 2 : ℝ) ≤ |(Q - P) 2| / ‖Q - P‖ := by
      rcases hvert with (h | h)
      · exfalso; exact hne h
      · exact h
    have hd_vert : (1 / 2 : ℝ) ≤ |d 2| := by
      have h1 : d 2 = (1 / L) * (Q - P) 2 := by
        change ((1 / L : ℝ) • (Q - P)) 2 = (1 / L) * (Q - P) 2
        exact rfl
      rw [h1]
      have h_pos2 : 0 < (1 / L : ℝ) := by positivity
      have h2 : |(1 / L) * (Q - P) 2| = (1 / L) * |(Q - P) 2| := by
        rw [abs_mul, abs_of_pos h_pos2]
      rw [h2]
      have h3 : (1 / L) * |(Q - P) 2| = |(Q - P) 2| / ‖Q - P‖ := by
        have h4 : L = ‖Q - P‖ := by rfl
        rw [h4] <;> ring
      rw [h3]
      exact hvert'
    let centers : ℕ → ℝ := fun i => (2 * (i : ℝ) + 1) / 6 * L
    let M : ℕ → Point3 := fun i => P + (centers i) • d
    let b : ℕ → Point3 := fun i => M i - (1 / 2 : ℝ) • d
    refine' ⟨b 0, b 1, b 2, d, hd_unit, hd_vert, _⟩
    intro x hx
    rcases hx with ⟨t, ht, h_x_eq⟩
    have h_t0 : 0 ≤ t := (Set.mem_Icc.mp ht).1
    have h_t1 : t ≤ 1 := (Set.mem_Icc.mp ht).2
    have h_main : ∃ i : ℕ, i ≤ 2 ∧ |t - (2 * (i : ℝ) + 1) / 6| ≤ 1 / 6 := by
      by_cases h1 : t ≤ 1 / 3
      · refine' ⟨0, by norm_num, _⟩
        rw [abs_le] <;> constructor <;> linarith
      · by_cases h2 : t ≤ 2 / 3
        · refine' ⟨1, by norm_num, _⟩
          rw [abs_le] <;> constructor <;> linarith
        · refine' ⟨2, by norm_num, _⟩
          rw [abs_le] <;> constructor <;> linarith
    rcases h_main with ⟨i, hi, h_i⟩
    have h_i2 : |t - (2 * (i : ℝ) + 1) / 6| * L < 1 / 2 := by
      have h_posL : 0 ≤ L := by positivity
      have h' : |t - (2 * (i : ℝ) + 1) / 6| * L ≤ (1 / 6 : ℝ) * L :=
        mul_le_mul_of_nonneg_right h_i h_posL
      have h'' : (1 / 6 : ℝ) * L < (1 / 6 : ℝ) * 3 :=
        mul_lt_mul_of_pos_left hL_lt_3 (by norm_num)
      linarith
    let s : ℝ := 1 / 2 + (t - (2 * (i : ℝ) + 1) / 6) * L
    have h31 : s - 1 / 2 = (t - (2 * (i : ℝ) + 1) / 6) * L := by
      simp [s] <;> ring
    have h32 : |s - 1 / 2| = |t - (2 * (i : ℝ) + 1) / 6| * L := by
      rw [h31, abs_mul, abs_of_nonneg (show 0 ≤ L by positivity)]
    have h3 : |s - 1 / 2| < 1 / 2 := by
      rw [h32]
      exact h_i2
    have h4 : 0 ≤ s := by linarith [abs_lt.mp h3]
    have h5 : s ≤ 1 := by linarith [abs_lt.mp h3]
    have hs_in : s ∈ Set.Icc (0 : ℝ) 1 := ⟨h4, h5⟩
    have h4 : v = L • d := by
      have h5 : L • d = L • ((1 / L) • v) := by rfl
      rw [h5]
      have h6 : L • ((1 / L) • v) = (L * (1 / L)) • v := by rw [smul_smul]
      rw [h6]
      have h7 : L * (1 / L) = 1 := by field_simp [hL_pos.ne'] <;> ring
      rw [h7] <;> simp
    have h9 : P + t • v = P + (t * L) • d := by
      rw [h4]
      have h10 : t • (L • d) = (t * L) • d := by rw [smul_smul]
      rw [h10]
    have h11 : b i + s • d = P + (t * L) • d := by
      have h12 : b i = P + (centers i) • d - (1 / 2 : ℝ) • d := by
        simp [b, M] <;> abel
      rw [h12]
      have h13 : centers i + (s - 1 / 2 : ℝ) = t * L := by
        simp [centers, s] <;> ring
      have h14 : (P + (centers i) • d - (1 / 2 : ℝ) • d) + s • d =
          P + ((centers i + (s - 1 / 2 : ℝ)) • d) := by
        simp [smul_add, add_smul, sub_smul] <;> abel
      rw [h14, h13]
    have h_eq2 : P + t • (Q - P) = b i + s • d := by
      have h_v : Q - P = v := by rfl
      rw [h_v]
      rw [h9, h11]
    have h5 : P + t • (Q - P) ∈ Kakeya.unitSegment (b i) d := by
      exact ⟨s, hs_in, h_eq2.symm⟩
    have h6 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h6 with (rfl | rfl | rfl)
    · have h7 : x ∈ Kakeya.unitSegment (b 0) d := by
        rw [h_x_eq]; exact h5
      exact Or.inl (Or.inl h7)
    · have h7 : x ∈ Kakeya.unitSegment (b 1) d := by
        rw [h_x_eq]; exact h5
      exact Or.inl (Or.inr h7)
    · have h7 : x ∈ Kakeya.unitSegment (b 2) d := by
        rw [h_x_eq]; exact h5
      exact Or.inr h7

/--
Thickening transport for compact sets: if `dist (f x) (f y) ≤ L * dist x y` and `A` is compact,
then f '' (cthickening δ A) ⊆ cthickening (L*δ) (f '' A).
-/
lemma image_cthickening_bound {X Y : Type _} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {L δ : ℝ} {A : Set X} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hA : IsCompact A)
    (h : ∀ x y, dist (f x) (f y) ≤ L * dist x y) :
    f '' cthickening δ A ⊆ cthickening (L * δ) (f '' A) := by
  have h_eq : cthickening δ A = ⋃ y ∈ A, closedBall y δ :=
    hA.cthickening_eq_biUnion_closedBall hδ
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  rw [h_eq] at hx
  have h_exists : ∃ y, y ∈ A ∧ dist x y ≤ δ := by
    simpa [Set.mem_iUnion, closedBall] using hx
  rcases h_exists with ⟨y, hyA, hdist⟩
  have h2 : dist (f x) (f y) ≤ L * dist x y := h x y
  have h3 : dist (f x) (f y) ≤ L * δ := by
    calc dist (f x) (f y) ≤ L * dist x y := h2
      _ ≤ L * δ := by gcongr
  have h4 : f y ∈ f '' A := ⟨y, hyA, rfl⟩
  exact Metric.mem_cthickening_of_dist_le (f x) (f y) (L * δ) (f '' A) h4 h3

/--
Axis subsegment parameter bounds: the part of a unit segment whose z-coordinate
lies in `[c-δ, d+δ]` is contained in a parameter subinterval `[t1, t2]` with
`(t2-t1) * |dir 2| ≤ d-c+2δ`.
-/
lemma axis_slab_parameter_bounds {base dir : Point3} {c d delta : ℝ}
    (hdelta : 0 ≤ delta) (hcd : c < d)
    (hdir_unit : ‖dir‖ = 1) (hdir_z : 1 / 2 ≤ |dir 2|) :
    ∃ (t1 t2 : ℝ), t1 ≤ t2 ∧
      (∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
        (base + t • dir) 2 ∈ Set.Icc (c - delta) (d + delta) →
        t ∈ Set.Icc t1 t2) ∧
      (t2 - t1) * |dir 2| ≤ d - c + 2 * delta := by
  have hdir2_ne : dir 2 ≠ 0 := by
    intro h
    rw [h] at hdir_z
    norm_num at hdir_z
  let a := (c - delta - base 2) / dir 2
  let b := (d + delta - base 2) / dir 2
  let t1 := min a b
  let t2 := max a b
  have h_t1_le_t2 : t1 ≤ t2 := by
    by_cases h : a ≤ b
    · simp [t1, t2, h]
    · simp [t1, t2, h] <;> linarith
  have h_bounds : ∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
      (base + t • dir) 2 ∈ Set.Icc (c - delta) (d + delta) →
      t ∈ Set.Icc t1 t2 := by
    intro t _ hz
    have h_z1 : c - delta ≤ base 2 + t * dir 2 := hz.1
    have h_z2 : base 2 + t * dir 2 ≤ d + delta := hz.2
    have h_ta : (t - a) * dir 2 ≥ 0 := by
      have h : (t - a) * dir 2 = (base 2 + t * dir 2) - (c - delta) := by
        simp [a] <;> field_simp [hdir2_ne] <;> ring
      rw [h] <;> linarith
    have h_tb : (b - t) * dir 2 ≥ 0 := by
      have h : (b - t) * dir 2 = (d + delta) - (base 2 + t * dir 2) := by
        simp [b] <;> field_simp [hdir2_ne] <;> ring
      rw [h] <;> linarith
    by_cases hpos : 0 < dir 2
    · have ha : a ≤ t := by nlinarith
      have hb : t ≤ b := by nlinarith
      have hab : a ≤ b := by nlinarith
      have hmin : t1 = a := by
        rw [show t1 = min a b from rfl, min_eq_left hab]
      have hmax : t2 = b := by
        rw [show t2 = max a b from rfl, max_eq_right hab]
      rw [hmin, hmax] <;> exact ⟨ha, hb⟩
    · have hneg : dir 2 < 0 := by
        by_cases h : dir 2 < 0
        · exact h
        · have h' : dir 2 = 0 := by linarith
          exact False.elim (hdir2_ne h')
      have hb : b ≤ t := by nlinarith
      have ha : t ≤ a := by nlinarith
      have hba : b ≤ a := by nlinarith
      have hmin : t1 = b := by
        rw [show t1 = min a b from rfl, min_eq_right hba]
      have hmax : t2 = a := by
        rw [show t2 = max a b from rfl, max_eq_left hba]
      rw [hmin, hmax] <;> exact ⟨hb, ha⟩
  have h_width : (t2 - t1) * |dir 2| ≤ d - c + 2 * delta := by
    have h7 : t2 - t1 = |a - b| := by
      by_cases h : a ≤ b
      · have hmin : t1 = a := by rw [show t1 = min a b from rfl, min_eq_left h]
        have hmax : t2 = b := by rw [show t2 = max a b from rfl, max_eq_right h]
        rw [hmin, hmax]
        have h_abs : |a - b| = b - a := by
          rw [abs_of_nonpos (show a - b ≤ 0 by linarith)] <;> linarith
        rw [h_abs] <;> linarith
      · have h' : b ≤ a := by linarith
        have hmin : t1 = b := by rw [show t1 = min a b from rfl, min_eq_right h']
        have hmax : t2 = a := by rw [show t2 = max a b from rfl, max_eq_left h']
        rw [hmin, hmax]
        have h_abs : |a - b| = a - b := by
          rw [abs_of_nonneg (show 0 ≤ a - b by linarith)] <;> linarith
        rw [h_abs] <;> linarith
    rw [h7]
    have h8 : |a - b| = (d - c + 2 * delta) / |dir 2| := by
      have h_ab : a - b = -(d - c + 2 * delta) / dir 2 := by
        simp [a, b] <;> field_simp [hdir2_ne] <;> ring
      rw [h_ab]
      have h9 : |-(d - c + 2 * delta) / dir 2| = (d - c + 2 * delta) / |dir 2| := by
        have h10 : |-(d - c + 2 * delta) / dir 2| = |d - c + 2 * delta| / |dir 2| := by
          rw [abs_div, abs_neg]
        rw [h10]
        have h11 : |d - c + 2 * delta| = d - c + 2 * delta := by
          rw [abs_of_nonneg] <;> linarith
        rw [h11]
      exact h9
    rw [h8]
    have h9 : 0 < |dir 2| := by linarith
    have h10 : ((d - c + 2 * delta) / |dir 2|) * |dir 2| = d - c + 2 * delta := by
      field_simp [h9.ne'] <;> ring
    rw [h10] <;> linarith
  exact ⟨t1, t2, h_t1_le_t2, h_bounds, h_width⟩

/--
Clipped version of `axis_slab_parameter_bounds`.

Both endpoints lie in the source unit-segment parameter interval.  When the
axis misses the extended slab, the degenerate interval `[0,0]` is returned.
-/
lemma axis_slab_parameter_bounds_clipped
    {base dir : Point3} {c d delta : ℝ}
    (hdelta : 0 ≤ delta) (hcd : c < d)
    (hdir_unit : ‖dir‖ = 1) (hdir_z : 1 / 2 ≤ |dir 2|) :
    ∃ t1 t2 : ℝ,
      t1 ∈ Set.Icc (0 : ℝ) 1 ∧
      t2 ∈ Set.Icc (0 : ℝ) 1 ∧
      t1 ≤ t2 ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        (base + t • dir) 2 ∈ Set.Icc (c - delta) (d + delta) →
        t ∈ Set.Icc t1 t2) ∧
      (t2 - t1) * |dir 2| ≤ d - c + 2 * delta := by
  by_cases hmeet :
      ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧
        (base + t • dir) 2 ∈ Set.Icc (c - delta) (d + delta)
  · rcases hmeet with ⟨t, ht, htz⟩
    rcases axis_slab_parameter_bounds hdelta hcd hdir_unit hdir_z with
      ⟨a, b, hab, hbounds, hwidth⟩
    have htab : t ∈ Set.Icc a b := hbounds t ht htz
    let t1 : ℝ := max 0 a
    let t2 : ℝ := min 1 b
    have ht1_t : t1 ≤ t := by
      exact max_le ht.1 htab.1
    have ht_t2 : t ≤ t2 := by
      exact le_min ht.2 htab.2
    have ht1_mem : t1 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact le_max_left _ _
      · exact max_le zero_le_one (htab.1.trans ht.2)
    have ht2_mem : t2 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact le_min zero_le_one (ht.1.trans htab.2)
      · exact min_le_left _ _
    have ht12 : t1 ≤ t2 := ht1_t.trans ht_t2
    have hclipped :
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
          (base + s • dir) 2 ∈ Set.Icc (c - delta) (d + delta) →
          s ∈ Set.Icc t1 t2 := by
      intro s hs hsz
      have hsab : s ∈ Set.Icc a b := hbounds s hs hsz
      exact ⟨max_le hs.1 hsab.1, le_min hs.2 hsab.2⟩
    have hwidth_clipped : t2 - t1 ≤ b - a := by
      have ht2_b : t2 ≤ b := min_le_right _ _
      have ha_t1 : a ≤ t1 := le_max_right _ _
      linarith
    have hmul :
        (t2 - t1) * |dir 2| ≤ (b - a) * |dir 2| :=
      mul_le_mul_of_nonneg_right hwidth_clipped (abs_nonneg _)
    exact
      ⟨t1, t2, ht1_mem, ht2_mem, ht12, hclipped,
        hmul.trans hwidth⟩
  · refine ⟨0, 0, by simp, by simp, le_rfl, ?_, ?_⟩
    · intro t ht htz
      exact False.elim (hmeet ⟨t, ht, htz⟩)
    · have hnonneg : 0 ≤ d - c + 2 * delta := by
        linarith
      simpa using hnonneg

/--
Cover the anisotropic image of an axis-slab intersection with 3 unit segments.

Given a tube axis and extended slab [c-δ, d+δ], the image of the intersection
under the anisotropic linear map is covered by 3 unit segments.
-/
lemma cover_axis_image_three {base dir : Point3} {c d delta g_mid K S : ℝ}
    (hdelta : 0 < delta) (hcd : c < d)
    (hdir_unit : ‖dir‖ = 1) (hdir_z : 1 / 2 ≤ |dir 2|)
    (hg : |g_mid| ≤ 1) (hK : |K| ≤ 1)
    (hS_eq : S = 2 / (d - c))
    (h_dc : d - c ≤ 1 / 25)
    (hdelta_small : delta ≤ 1 / 100)
    (hrho_small : 2 * delta / (d - c) ≤ 1 / 4)
    (hAd_vert : (1 / 2 : ℝ) ≤ |(point3 (dir 0 + g_mid * dir 1) (K * dir 1) (S * dir 2)) 2| / ‖(point3 (dir 0 + g_mid * dir 1) (K * dir 1) (S * dir 2))‖)
    (Φ : Point3 → Point3)
    (hΦ_affine : ∀ (t : ℝ), Φ (base + t • dir) = Φ base + t • (point3 (dir 0 + g_mid * dir 1) (K * dir 1) (S * dir 2))) :
    ∃ (b1 b2 b3 : Point3) (d' : Point3), ‖d'‖ = 1 ∧
      (1 / 2 : ℝ) ≤ |d' 2| ∧
      (Φ '' (Kakeya.unitSegment base dir ∩ horizontalSlab (c - delta) (d + delta)) ⊆
        Kakeya.unitSegment b1 d' ∪ Kakeya.unitSegment b2 d' ∪ Kakeya.unitSegment b3 d') := by
  have hdelta' : 0 ≤ delta := by linarith
  rcases axis_slab_parameter_bounds_clipped
      hdelta' hcd hdir_unit hdir_z with
    ⟨t1, t2, _ht1, _ht2, h_t1_le_t2, h_bounds, h_width⟩
  let Ad := point3 (dir 0 + g_mid * dir 1) (K * dir 1) (S * dir 2)
  let P := Φ (base + t1 • dir)
  let Q := Φ (base + t2 • dir)
  have h11 : Q = Φ base + t2 • Ad := by
    simpa [Q, Ad] using hΦ_affine t2
  have h12 : P = Φ base + t1 • Ad := by
    simpa [P, Ad] using hΦ_affine t1
  have h1 : Q - P = (t2 - t1) • Ad := by
    rw [h11, h12]
    simp [sub_smul, smul_sub] <;> abel
  have h_len : dist P Q < 3 := by
    have h2 : dist P Q = ‖P - Q‖ := by rw [dist_eq_norm]
    have h2' : ‖P - Q‖ = ‖Q - P‖ := norm_sub_rev P Q
    rw [h2, h2', h1]
    have h3 : ‖(t2 - t1) • Ad‖ = |t2 - t1| * ‖Ad‖ := by
      simpa using norm_smul (t2 - t1) Ad
    rw [h3]
    have h4 : |t2 - t1| = t2 - t1 := by
      rw [abs_of_nonneg] <;> linarith
    rw [h4]
    have h8 : 0 < |dir 2| := by linarith [hdir_z]
    have h6 : t2 - t1 ≤ (d - c + 2 * delta) / |dir 2| := by
      have h7 : (t2 - t1) * |dir 2| ≤ d - c + 2 * delta := h_width
      have h9 : t2 - t1 ≤ (d - c + 2 * delta) / |dir 2| := by
        calc
          t2 - t1 = ((t2 - t1) * |dir 2|) / |dir 2| := by
            field_simp [h8.ne'] <;> ring
          _ ≤ (d - c + 2 * delta) / |dir 2| := by gcongr
      exact h9
    have h5 : (t2 - t1) * ‖Ad‖ ≤ ((d - c + 2 * delta) / |dir 2|) * ‖Ad‖ := by
      gcongr <;> positivity
    exact h5.trans_lt (extended_image_axis_lt_3 hdelta hcd hdir_unit hdir_z hg hK hS_eq h_dc hdelta_small hrho_small)
  have hvert : P = Q ∨ (1 / 2 : ℝ) ≤ |(Q - P) 2| / ‖Q - P‖ := by
    by_cases h_eq : t1 = t2
    · have hQP : Q - P = 0 := by
        rw [h1, h_eq, sub_self, zero_smul]
      have hPQ : P = Q := by
        have h : Q - P = 0 := hQP
        have hQ : Q = P := by simpa [sub_eq_zero] using h
        exact hQ.symm
      exact Or.inl hPQ
    · have h_lt : t1 < t2 := by
        by_cases h : t1 < t2
        · exact h
        · have h' : t1 = t2 := by linarith
          exact False.elim (h_eq h')
      have h_pos : 0 < t2 - t1 := by linarith
      have h2 : (Q - P) 2 = (t2 - t1) * Ad 2 := by
        rw [h1] <;> simp
      have h3 : ‖Q - P‖ = (t2 - t1) * ‖Ad‖ := by
        calc ‖Q - P‖
          = ‖(t2 - t1) • Ad‖ := by rw [h1]
        _ = |t2 - t1| * ‖Ad‖ := by simpa [norm_smul] using rfl
        _ = (t2 - t1) * ‖Ad‖ := by rw [abs_of_pos h_pos]
      have h4 : |(Q - P) 2| / ‖Q - P‖ = |Ad 2| / ‖Ad‖ := by
        rw [h2, h3]
        have h5 : |(t2 - t1) * Ad 2| = (t2 - t1) * |Ad 2| := by
          rw [abs_mul, abs_of_pos h_pos]
        rw [h5]
        <;> field_simp [h_pos.ne'] <;> ring
      rw [h4]
      exact Or.inr hAd_vert
  rcases cover_segment_three h_len hvert with ⟨b1, b2, b3, d', hd'_unit, hd'_vert, hcover⟩
  have h_image_subset : Φ '' (Kakeya.unitSegment base dir ∩ horizontalSlab (c - delta) (d + delta)) ⊆
      Kakeya.unitSegment P (Q - P) := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    have hy_axis : y ∈ Kakeya.unitSegment base dir := hy.1
    have hy_slab : y 2 ∈ Set.Icc (c - delta) (d + delta) := hy.2
    rcases hy_axis with ⟨t, ht, rfl⟩
    have h_t_in : t ∈ Set.Icc t1 t2 := h_bounds t ht hy_slab
    by_cases h_eq : t1 = t2
    · have h_t : t = t1 := by
        have h_t1 : t1 ≤ t := h_t_in.1
        have h_t2 : t ≤ t2 := h_t_in.2
        linarith
      have h_goal : Φ (base + t • dir) = P := by
        have h : Φ (base + t • dir) = Φ (base + t1 • dir) := by rw [h_t]
        simpa [P] using h
      rw [h_goal]
      refine' ⟨0, by norm_num, _⟩
      simp [P] <;> abel
    · have h_t1_lt_t2 : t1 < t2 := by
        by_cases h : t1 < t2
        · exact h
        · have h' : t1 = t2 := by linarith
          exact False.elim (h_eq h')
      let s : ℝ := (t - t1) / (t2 - t1)
      have hs_in : s ∈ Set.Icc (0 : ℝ) 1 := by
        have h_pos : 0 < t2 - t1 := by linarith
        have h1 : 0 ≤ s := by
          apply div_nonneg <;> linarith [h_t_in.1]
        have h2 : s ≤ 1 := by
          rw [div_le_one (by linarith)] <;> linarith [h_t_in.2]
        exact ⟨h1, h2⟩
      have h_affine : Φ (base + t • dir) = P + s • (Q - P) := by
        have h13 : Φ (base + t • dir) = Φ base + t • Ad := by
          simpa [Ad] using hΦ_affine t
        have h14 : P + s • (Q - P) = Φ base + t • Ad := by
          rw [h12, h11]
          have h_sub : (Φ base + t2 • Ad) - (Φ base + t1 • Ad) = (t2 - t1) • Ad := by
            simp [sub_smul] <;> abel
          have h_smul : s • ((Φ base + t2 • Ad) - (Φ base + t1 • Ad)) = (s * (t2 - t1)) • Ad := by
            rw [h_sub, smul_smul]
          have h15 : (Φ base + t1 • Ad) + s • ((Φ base + t2 • Ad) - (Φ base + t1 • Ad)) =
              Φ base + (t1 + s * (t2 - t1)) • Ad := by
            rw [h_smul]
            simp [add_smul] <;> abel
          rw [h15]
          have h16 : t1 + s * (t2 - t1) = t := by
            simp [s] <;> field_simp [h_t1_lt_t2.ne'] <;> ring
          rw [h16]
        exact h13.trans h14.symm
      rw [h_affine]
      exact ⟨s, hs_in, rfl⟩
  have h_final : Kakeya.unitSegment P (Q - P) ⊆
      Kakeya.unitSegment b1 d' ∪ Kakeya.unitSegment b2 d' ∪ Kakeya.unitSegment b3 d' := by
    intro x hx
    rcases hx with ⟨t, ht, h_eq⟩
    have h_eq' : x = P + t • (Q - P) := h_eq.symm
    exact hcover x ⟨t, ht, h_eq'⟩
  exact ⟨b1, b2, b3, d', hd'_unit, hd'_vert, h_image_subset.trans h_final⟩

/--
Main covering lemma: the image of a δ-tube slab intersection under the
anisotropic rescaling map is covered by 3 ρ-tubes with ρ = S*δ = 2δ/(d-c).
Also certifies all covering tube directions are in the vertical chart.
-/
lemma cover_tube_image_three_rho_tubes
    {δ c d g_mid K S rho : ℝ}
    (hdelta : 0 < δ) (hcd : c < d)
    (T : Kakeya.DeltaTube δ)
    (hdir_z : 1 / 2 ≤ |T.direction 2|)
    (hg : |g_mid| ≤ 1) (hK : |K| ≤ 1)
    (hS_eq : S = 2 / (d - c))
    (h_dc : d - c ≤ 1 / 25)
    (hdelta_small : δ ≤ 1 / 100)
    (hrho_small : 2 * δ / (d - c) ≤ 1 / 4)
    (hrho_eq : rho = S * δ)
    (g : SlopeFunction) (hg_norm : g.IsNormalized)
    (m : ℝ) (hm_pos : 0 < m) (hm_le_one : m ≤ 1)
    (h_sub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hK_def : K = m * (d - c) / 2)
    (hg_mid_def : g_mid = g (c + (d - c) / 2)) :
    ∃ (T1 T2 T3 : Kakeya.DeltaTube rho),
      (fun p : Point3 =>
        point3 (p 0 + g_mid * p 1) (K * p 1) (S * p 2 - S * c - 1)) ''
        (T.carrier ∩ horizontalSlab c d) ⊆
      T1.carrier ∪ T2.carrier ∪ T3.carrier ∧
      (1 / 2 : ℝ) ≤ |T1.direction 2| ∧
      (1 / 2 : ℝ) ≤ |T2.direction 2| ∧
      (1 / 2 : ℝ) ≤ |T3.direction 2| := by
  let Φ : Point3 → Point3 := fun p =>
    point3 (p 0 + g_mid * p 1) (K * p 1) (S * p 2 - S * c - 1)
  let A : Point3 → Point3 := fun p =>
    point3 (p 0 + g_mid * p 1) (K * p 1) (S * p 2)
  have hS_pos : 0 < S := by
    rw [hS_eq] <;> positivity
  have hS2 : 2 ≤ S := by
    rw [hS_eq]
    have h_pos : 0 < d - c := by linarith [hcd]
    have h_le : d - c ≤ 1 / 25 := h_dc
    have h : 2 / (d - c) ≥ 50 := by
      calc 2 / (d - c) ≥ 2 / (1 / 25 : ℝ) := by gcongr
        _ = 50 := by norm_num
    linarith
  have h_dist_bound : ∀ (x y : Point3), dist (Φ x) (Φ y) ≤ S * dist x y := by
    intro x y
    have h2 : Φ x - Φ y = A (x - y) := by
      ext i
      fin_cases i <;> simp [Φ, A, point3, Fin.sum_univ_succ] <;> ring
    have h3 : dist (Φ x) (Φ y) = ‖Φ x - Φ y‖ := by rw [dist_eq_norm]
    rw [h3, h2]
    have h4 : ‖A (x - y)‖ ≤ S * ‖x - y‖ := anisotropicMap_opNorm_bound hg hK hS2 (x - y)
    have h5 : dist x y = ‖x - y‖ := by rw [dist_eq_norm]
    rw [h5] at *
    exact h4
  let axis := Kakeya.unitSegment T.base T.direction
  let E := axis ∩ horizontalSlab (c - δ) (d + δ)
  have h1 : T.carrier ∩ horizontalSlab c d ⊆ Metric.cthickening δ E := by
    intro x hx
    have hx1 : x ∈ T.carrier := hx.1
    have hx2 : x ∈ horizontalSlab c d := hx.2
    have h_xz : x 2 ∈ Set.Icc c d := hx2
    have h_axis_compact : IsCompact axis := by
      exact isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
    have hTcar : T.carrier = Metric.cthickening δ axis := by rfl
    rw [hTcar] at hx1
    have h_eq : Metric.cthickening δ axis = ⋃ y ∈ axis, closedBall y δ :=
      h_axis_compact.cthickening_eq_biUnion_closedBall (by positivity)
    rw [h_eq] at hx1
    have h_exists : ∃ y, y ∈ axis ∧ dist x y ≤ δ := by
      simpa [Set.mem_iUnion, closedBall] using hx1
    rcases h_exists with ⟨y, hy_axis, hdist⟩
    have h_yz : |y 2 - x 2| ≤ dist y x := by
      let v := y - x
      have h1 : (v 2)^2 ≤ ‖v‖^2 := by
        have h2 : ‖v‖^2 = ∑ i : Fin 3, (v i)^2 := by
          simpa using EuclideanSpace.real_norm_sq_eq v
        rw [h2]
        have h3 : (v 2)^2 ≤ ∑ i : Fin 3, (v i)^2 := by
          have h4 : (2 : Fin 3) ∈ Finset.univ := by simp
          exact Finset.single_le_sum (fun i _ => sq_nonneg (v i)) h4
        exact h3
      have h4 : |v 2| ≤ ‖v‖ := by
        have h5 : (|v 2|)^2 ≤ ‖v‖^2 := by
          rw [sq_abs] <;> exact h1
        have h6 : 0 ≤ |v 2| := abs_nonneg (v 2)
        have h7 : 0 ≤ ‖v‖ := norm_nonneg v
        nlinarith
      have h5 : |y 2 - x 2| = |v 2| := by
        have h6 : v 2 = y 2 - x 2 := by simp [v]
        rw [h6]
      rw [h5]
      simpa [dist_eq_norm, v] using h4
    have h_yz2 : y 2 ∈ Set.Icc (c - δ) (d + δ) := by
      have h_x1 : c ≤ x 2 := h_xz.1
      have h_x2 : x 2 ≤ d := h_xz.2
      have hdist' : dist y x ≤ δ := by rwa [dist_comm] at hdist
      have h : |y 2 - x 2| ≤ δ := by calc
          |y 2 - x 2| ≤ dist y x := h_yz
          _ ≤ δ := hdist'
      rw [abs_le] at h
      exact ⟨by linarith, by linarith⟩
    have hy_E : y ∈ E := ⟨hy_axis, h_yz2⟩
    exact Metric.mem_cthickening_of_dist_le x y δ E hy_E hdist
  have h_axis_compact : IsCompact axis := by
    exact isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  have h_slab_closed : IsClosed (horizontalSlab (c - δ) (d + δ)) := by
    have h_cont : Continuous (fun x : Point3 => x 2) :=
      PiLp.continuous_apply (p := 2) (β := fun (_ : Fin 3) => ℝ) (2 : Fin 3)
    have h_ic : IsClosed (Set.Icc (c - δ) (d + δ)) := isClosed_Icc
    have h_pre : IsClosed ((fun x : Point3 => x 2) ⁻¹' Set.Icc (c - δ) (d + δ)) := h_ic.preimage h_cont
    have h_eq : horizontalSlab (c - δ) (d + δ) = (fun x : Point3 => x 2) ⁻¹' Set.Icc (c - δ) (d + δ) := by
      ext x; simp [horizontalSlab] <;> rfl
    rw [h_eq]
    exact h_pre
  have hE_compact : IsCompact E := h_axis_compact.inter_right h_slab_closed
  have h2 : Φ '' (T.carrier ∩ horizontalSlab c d) ⊆ Metric.cthickening (S * δ) (Φ '' E) := by
    have h21 : Φ '' (T.carrier ∩ horizontalSlab c d) ⊆ Φ '' Metric.cthickening δ E := by
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      exact ⟨w, h1 hw, rfl⟩
    have h22 : Φ '' Metric.cthickening δ E ⊆ Metric.cthickening (S * δ) (Φ '' E) :=
      image_cthickening_bound (by positivity) (by positivity) hE_compact h_dist_bound
    exact h21.trans h22
  let dir := T.direction
  let base := T.base
  have hdir_unit : ‖dir‖ = 1 := T.direction_unit
  have hΦ_affine : ∀ (t : ℝ), Φ (base + t • dir) = Φ base + t • (point3 (dir 0 + g_mid * dir 1) (K * dir 1) (S * dir 2)) := by
    intro t
    ext i
    fin_cases i <;> simp [Φ, point3, smul_add, add_smul] <;> ring
  let Ad := point3 (dir 0 + g_mid * dir 1) (K * dir 1) (S * dir 2)
  have h_dc25 : d - c ≤ 1 / 25 := by linarith
  have hS : S = 2 / (d - c) := hS_eq
  have hAd_vert : (1 / 2 : ℝ) ≤ |Ad 2| / ‖Ad‖ := by
    have h_vert := anisotropicMap_preservesVerticalChart g hg_norm c d m hcd hm_pos hm_le_one h_dc25 h_sub dir hdir_unit hdir_z
    simpa [Ad, hK_def, hg_mid_def, hS] using h_vert
  rcases cover_axis_image_three hdelta hcd hdir_unit hdir_z hg hK hS_eq h_dc hdelta_small hrho_small hAd_vert Φ hΦ_affine
    with ⟨b1, b2, b3, d', hd'_unit, hd'_vert, hcover⟩
  have h5 : Metric.cthickening (S * δ) (Φ '' E) ⊆
      Metric.cthickening (S * δ) (Kakeya.unitSegment b1 d' ∪ Kakeya.unitSegment b2 d' ∪ Kakeya.unitSegment b3 d') :=
    Metric.cthickening_subset_of_subset (S * δ) hcover
  have h6 : Metric.cthickening (S * δ) (Kakeya.unitSegment b1 d' ∪ Kakeya.unitSegment b2 d' ∪ Kakeya.unitSegment b3 d') =
      Metric.cthickening (S * δ) (Kakeya.unitSegment b1 d') ∪
      Metric.cthickening (S * δ) (Kakeya.unitSegment b2 d') ∪
      Metric.cthickening (S * δ) (Kakeya.unitSegment b3 d') := by
    rw [Metric.cthickening_union, Metric.cthickening_union]
  let T1 : Kakeya.DeltaTube rho := ⟨b1, d', hd'_unit⟩
  let T2 : Kakeya.DeltaTube rho := ⟨b2, d', hd'_unit⟩
  let T3 : Kakeya.DeltaTube rho := ⟨b3, d', hd'_unit⟩
  have h7 : S * δ ≤ rho := by rw [hrho_eq]
  have h_radius_mono : ∀ (E : Set Point3), Metric.cthickening (S * δ) E ⊆ Metric.cthickening rho E := by
    intro E x hx
    rw [Metric.cthickening_eq_preimage_infEDist] at hx ⊢
    have h2 : ENNReal.ofReal (S * δ) ≤ ENNReal.ofReal rho := ENNReal.ofReal_le_ofReal h7
    exact hx.trans h2
  have h8 : Metric.cthickening (S * δ) (Kakeya.unitSegment b1 d') ⊆ T1.carrier := by
    have h9 : T1.carrier = Metric.cthickening rho (Kakeya.unitSegment b1 d') := by rfl
    rw [h9]
    exact h_radius_mono (Kakeya.unitSegment b1 d')
  have h9 : Metric.cthickening (S * δ) (Kakeya.unitSegment b2 d') ⊆ T2.carrier := by
    have h10 : T2.carrier = Metric.cthickening rho (Kakeya.unitSegment b2 d') := by rfl
    rw [h10]
    exact h_radius_mono (Kakeya.unitSegment b2 d')
  have h10 : Metric.cthickening (S * δ) (Kakeya.unitSegment b3 d') ⊆ T3.carrier := by
    have h11 : T3.carrier = Metric.cthickening rho (Kakeya.unitSegment b3 d') := by rfl
    rw [h11]
    exact h_radius_mono (Kakeya.unitSegment b3 d')
  have h_final : Φ '' (T.carrier ∩ horizontalSlab c d) ⊆ T1.carrier ∪ T2.carrier ∪ T3.carrier := by
    calc Φ '' (T.carrier ∩ horizontalSlab c d)
      ⊆ Metric.cthickening (S * δ) (Φ '' E) := h2
    _ ⊆ Metric.cthickening (S * δ) (Kakeya.unitSegment b1 d' ∪ Kakeya.unitSegment b2 d' ∪ Kakeya.unitSegment b3 d') := h5
    _ = Metric.cthickening (S * δ) (Kakeya.unitSegment b1 d') ∪ Metric.cthickening (S * δ) (Kakeya.unitSegment b2 d') ∪ Metric.cthickening (S * δ) (Kakeya.unitSegment b3 d') := h6
    _ ⊆ T1.carrier ∪ T2.carrier ∪ T3.carrier := by
      intro z hz
      by_cases h1 : z ∈ Metric.cthickening (S * δ) (Kakeya.unitSegment b1 d')
      · exact Or.inl (Or.inl (h8 h1))
      · by_cases h2 : z ∈ Metric.cthickening (S * δ) (Kakeya.unitSegment b2 d')
        · exact Or.inl (Or.inr (h9 h2))
        · have h3 : z ∈ Metric.cthickening (S * δ) (Kakeya.unitSegment b3 d') := by
            have h4 : z ∈ (Metric.cthickening (S * δ) (Kakeya.unitSegment b1 d') ∪ Metric.cthickening (S * δ) (Kakeya.unitSegment b2 d')) ∪ Metric.cthickening (S * δ) (Kakeya.unitSegment b3 d') := hz
            rcases h4 with (h4 | h4)
            · rcases h4 with (h5 | h5)
              · exact False.elim (h1 h5)
              · exact False.elim (h2 h5)
            · exact h4
          exact Or.inr (h10 h3)
  exact ⟨T1, T2, T3, h_final, hd'_vert, hd'_vert, hd'_vert⟩

end Kakeya.Assouad
