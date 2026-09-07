import MyLeanRepo.Kakeya.Cinematic.Geometry

/-!
# Arithmetic estimates for lens existence

Pure arithmetic lemmas used to verify that the quantitative bounds
in the lens-existence argument are compatible.
-/

namespace Kakeya.Cinematic

open Real

/--
Key arithmetic estimate: with `tangency^50 * delta ≤ t / (1000 * K^2)`,
the sum of the value bound and uniform derivative bound on an interval
of length `sqrt(delta/t)` is strictly less than `d/K`.
-/
lemma lens_existence_arithmetic
    {K tangency delta t d : ℝ}
    (hK : 1 ≤ K)
    (htang : 5 ≤ tangency)
    (hdelta : 0 < delta)
    (ht : 0 < t)
    (hdt : delta ≤ t)
    (hd_ge_2t : 2 * t ≤ d)
    (hd_le_K : d ≤ K)
    (h_small : tangency^50 * delta ≤ t / (1000 * K^2)) :
    2 * tangency * delta + 4 * tangency * sqrt (delta * t) + d * sqrt (delta / t) < d / K := by
  set r := delta / t with hr_def
  have hK_pos : 0 < K := by linarith
  have h_tang_pos : 0 < tangency := by linarith
  have hr_pos : 0 < r := by positivity

  have hr_bound : r ≤ 1 / (1000 * K^2 * tangency^50) := by
    have h_pos1 : 0 < tangency^50 * t := by positivity
    have h : (tangency^50 * delta) / (tangency^50 * t) ≤ (t / (1000 * K^2)) / (tangency^50 * t) := by
      gcongr
    have h2 : (tangency^50 * delta) / (tangency^50 * t) = delta / t := by
      field_simp [h_tang_pos.ne', ht.ne'] <;> ring
    have h3 : (t / (1000 * K^2)) / (tangency^50 * t) = 1 / (1000 * K^2 * tangency^50) := by
      field_simp [hK_pos.ne', h_tang_pos.ne', ht.ne'] <;> ring
    rw [h2, h3] at h
    exact h

  have h_sqrt_bound : sqrt r ≤ 1 / (sqrt 1000 * K * tangency^25) := by
    have h4 : 0 ≤ 1 / (1000 * K^2 * tangency^50) := by positivity
    have h5 : sqrt r ≤ sqrt (1 / (1000 * K^2 * tangency^50)) := Real.sqrt_le_sqrt hr_bound
    have h_pos : 0 ≤ sqrt 1000 * K * tangency^25 := by positivity
    have h_sq : (sqrt 1000 * K * tangency^25)^2 = 1000 * K^2 * tangency^50 := by
      have h7 : (sqrt 1000)^2 = 1000 := Real.sq_sqrt (by norm_num)
      calc (sqrt 1000 * K * tangency^25)^2
        = (sqrt 1000)^2 * K^2 * (tangency^25)^2 := by ring
      _ = 1000 * K^2 * (tangency^25)^2 := by rw [h7]
      _ = 1000 * K^2 * tangency^50 := by ring
    have h9 : 1000 * K^2 * tangency^50 = (sqrt 1000 * K * tangency^25)^2 := h_sq.symm
    have h8 : sqrt (1000 * K^2 * tangency^50) = sqrt 1000 * K * tangency^25 := by
      rw [h9]
      exact Real.sqrt_sq h_pos
    have h_pos' : 0 < sqrt 1000 * K * tangency^25 := by positivity
    have h6 : sqrt (1 / (1000 * K^2 * tangency^50)) = 1 / (sqrt 1000 * K * tangency^25) := by
      have h_div : sqrt (1 / (1000 * K^2 * tangency^50)) = 1 / sqrt (1000 * K^2 * tangency^50) := by
        rw [Real.sqrt_div (by positivity)]
        <;> simp
      rw [h_div, h8]
    rw [h6] at h5
    exact h5

  -- Term 1: 2 * tangency * delta ≤ d / (1000 * K * tangency^49)
  have h_term1 : 2 * tangency * delta ≤ d / (1000 * K * tangency^49) := by
    have h1 : delta ≤ t / (1000 * K^2 * tangency^50) := by
      have h2 : delta = r * t := by
        rw [hr_def] <;> field_simp [ht.ne'] <;> ring
      rw [h2]
      have h3 : r * t ≤ (1 / (1000 * K^2 * tangency^50)) * t := by gcongr
      have h4 : (1 / (1000 * K^2 * tangency^50)) * t = t / (1000 * K^2 * tangency^50) := by ring
      rw [h4] at h3
      exact h3
    have h4 : 2 * tangency * delta ≤ 2 * t / (1000 * K^2 * tangency^49) := by
      calc 2 * tangency * delta
        ≤ 2 * tangency * (t / (1000 * K^2 * tangency^50)) := by gcongr
      _ = 2 * t / (1000 * K^2 * tangency^49) := by
        field_simp [h_tang_pos.ne'] <;> ring
    have h5 : 2 * t ≤ d := by linarith
    have h6 : 2 * t / (1000 * K^2 * tangency^49) ≤ d / (1000 * K * tangency^49) := by
      have h7 : 0 < 1000 * K^2 * tangency^49 := by positivity
      have h8 : 0 < 1000 * K * tangency^49 := by positivity
      have h9 : d / (1000 * K * tangency^49) - 2 * t / (1000 * K^2 * tangency^49) ≥ 0 := by
        have h10 : d * K - 2 * t ≥ 0 := by nlinarith
        have h11 : d / (1000 * K * tangency^49) - 2 * t / (1000 * K^2 * tangency^49)
            = (d * K - 2 * t) / (1000 * K^2 * tangency^49) := by
          field_simp [hK_pos.ne', h_tang_pos.ne'] <;> ring
        rw [h11]
        positivity
      linarith
    linarith

  -- Term 2: 4 * tangency * sqrt(delta * t) ≤ 2 * d / (sqrt 1000 * K * tangency^24)
  have h_term2 : 4 * tangency * sqrt (delta * t) ≤ 2 * d / (sqrt 1000 * K * tangency^24) := by
    have h1 : sqrt (delta * t) = t * sqrt r := by
      have h2 : delta * t = t^2 * r := by
        rw [hr_def] <;> field_simp [ht.ne'] <;> ring
      rw [h2]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)] <;> ring
    rw [h1]
    have h3 : 4 * tangency * (t * sqrt r) ≤ 4 * t / (sqrt 1000 * K * tangency^24) := by
      have h31 : 4 * tangency * t * sqrt r ≤ 4 * tangency * t * (1 / (sqrt 1000 * K * tangency^25)) := by
        gcongr
      have h34 : 4 * tangency * t * (1 / (sqrt 1000 * K * tangency^25)) = 4 * t / (sqrt 1000 * K * tangency^24) := by
        field_simp [hK_pos.ne', h_tang_pos.ne'] <;> ring
      have h35 : 4 * tangency * (t * sqrt r) = 4 * tangency * t * sqrt r := by ring
      rw [h35]
      exact h31.trans_eq h34
    have h4 : 4 * t / (sqrt 1000 * K * tangency^24) ≤ 2 * d / (sqrt 1000 * K * tangency^24) := by
      have h5 : 0 < sqrt 1000 * K * tangency^24 := by positivity
      have h6 : 4 * t ≤ 2 * d := by linarith
      gcongr
    exact h3.trans h4

  -- Term 3: d * sqrt r ≤ d / (sqrt 1000 * K * tangency^25)
  have h_term3 : d * sqrt r ≤ d / (sqrt 1000 * K * tangency^25) := by
    have h_d_pos : 0 < d := by linarith
    have h3 : d * sqrt r ≤ d * (1 / (sqrt 1000 * K * tangency^25)) := by
      gcongr <;> exact h_sqrt_bound
    have h4 : d * (1 / (sqrt 1000 * K * tangency^25)) = d / (sqrt 1000 * K * tangency^25) := by ring
    rw [h4] at h3
    exact h3

  let C_sum : ℝ := 1 / (1000 * tangency^49)
      + 2 / (sqrt 1000 * tangency^24)
      + 1 / (sqrt 1000 * tangency^25)

  -- Sum of coefficients < 1
  have h_tang24_ge100 : tangency^24 ≥ 100 := by
    have h4 : (5 : ℝ)^24 ≤ tangency^24 := by gcongr <;> linarith
    have h5 : (100 : ℝ) ≤ (5 : ℝ)^24 := by norm_num
    exact h5.trans h4
  have h_tang25_ge500 : tangency^25 ≥ 500 := by
    have h4 : (5 : ℝ)^25 ≤ tangency^25 := by gcongr <;> linarith
    have h5 : (500 : ℝ) ≤ (5 : ℝ)^25 := by norm_num
    exact h5.trans h4
  have h_tang49_ge1000 : tangency^49 ≥ 1000 := by
    have h4 : (5 : ℝ)^49 ≤ tangency^49 := by gcongr <;> linarith
    have h5 : (1000 : ℝ) ≤ (5 : ℝ)^49 := by norm_num
    exact h5.trans h4
  have h_sqrt1000_gt30 : (30 : ℝ) < sqrt 1000 := by
    have h : (30 : ℝ)^2 < 1000 := by norm_num
    exact Real.lt_sqrt_of_sq_lt h

  have h_coeff_sum : C_sum < 1 := by
    have h1 : 1 / (1000 * tangency^49) ≤ 1 / 1000000 := by
      have h2 : 1000000 ≤ 1000 * tangency^49 := by
        have h3 : tangency^49 ≥ 1000 := h_tang49_ge1000
        nlinarith
      gcongr
    have h2 : 2 / (sqrt 1000 * tangency^24) ≤ 1 / 1500 := by
      have h_pos : 0 < sqrt 1000 * tangency^24 := by positivity
      have h3 : sqrt 1000 * tangency^24 ≥ 3000 := by
        have h4 : 30 ≤ sqrt 1000 := by linarith
        have h5 : tangency^24 ≥ 100 := h_tang24_ge100
        nlinarith
      have h6 : 2 / (sqrt 1000 * tangency^24) ≤ 2 / 3000 := by gcongr
      have h7 : (2 : ℝ) / 3000 = 1 / 1500 := by norm_num
      rw [h7] at h6
      exact h6
    have h3 : 1 / (sqrt 1000 * tangency^25) ≤ 1 / 15000 := by
      have h_pos : 0 < sqrt 1000 * tangency^25 := by positivity
      have h4 : sqrt 1000 * tangency^25 ≥ 15000 := by
        have h5 : 30 ≤ sqrt 1000 := by linarith
        have h6 : tangency^25 ≥ 500 := h_tang25_ge500
        nlinarith
      have h7 : 1 / (sqrt 1000 * tangency^25) ≤ 1 / 15000 := by gcongr
      exact h7
    simp only [C_sum]
    linarith

  have h_d_pos : 0 < d := by linarith
  have h_sum : 2 * tangency * delta + 4 * tangency * sqrt (delta * t) + d * sqrt r
      ≤ d / K * C_sum := by
    calc
      2 * tangency * delta + 4 * tangency * sqrt (delta * t) + d * sqrt r
        ≤ d / (1000 * K * tangency^49)
            + 2 * d / (sqrt 1000 * K * tangency^24)
            + d / (sqrt 1000 * K * tangency^25) := by
          gcongr <;> linarith
      _ = d / K * C_sum := by
        simp only [C_sum]
        <;> ring_nf
        <;> field_simp [hK_pos.ne'] <;> ring
  have h_dK_pos : 0 < d / K := by positivity
  have h_final : d / K * C_sum < d / K := by
    have h : d / K * C_sum < d / K * 1 := by gcongr
    have h2 : d / K * 1 = d / K := by ring
    rw [h2] at h
    exact h
  exact h_sum.trans_lt h_final

end Kakeya.Cinematic
