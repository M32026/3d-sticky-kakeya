import MyLeanRepo.Kakeya.Cinematic.Section5.SingletonFiberScaleAbsorptionInputs

/-!
# Absorb the singleton-fiber scale loss
-/

namespace Kakeya.Cinematic

theorem singleton_fiber_scale_absorption :
    SingletonFiberScaleAbsorptionStatement := by
  intro K m n T hK hm hn hT
  set s : ℝ := m + n with hs
  have hs_pos : 0 < s := by linarith
  set epsilon : ℝ := T - 3 * s / 2 with hepsilon_def
  have hepsilon_pos : 0 < epsilon := by linarith
  set C : ℝ := (8 * K) ^ m * (16 * K) ^ n with hC_def
  have hC_pos : 0 < C := by positivity
  set D : ℝ := 8 * C with hD_def
  have hD_pos : 0 < D := by positivity
  set delta₀ : ℝ := min 1 (D ^ (-3 / (2 * epsilon))) with hdelta₀_def
  have hdelta₀_pos : 0 < delta₀ := by
    rw [hdelta₀_def]
    positivity
  have hdelta₀_le_one : delta₀ ≤ 1 := by
    rw [hdelta₀_def]
    exact min_le_left _ _
  have hdelta₀_le_D : delta₀ ≤ D ^ (-3 / (2 * epsilon)) := by
    rw [hdelta₀_def]
    exact min_le_right _ _
  have h_absorb : D ^ (3 / 2 : ℝ) * delta₀ ^ epsilon ≤ 1 := by
    have h1 :
        delta₀ ^ epsilon ≤ (D ^ (-3 / (2 * epsilon))) ^ epsilon := by
      gcongr
    have h2 :
        (D ^ (-3 / (2 * epsilon))) ^ epsilon = D ^ (-3 / 2 : ℝ) := by
      rw [← Real.rpow_mul (by positivity)]
      have hmul : (-3 / (2 * epsilon)) * epsilon = -3 / 2 := by
        field_simp [hepsilon_pos.ne']
      rw [hmul]
    have hdelta_power :
        delta₀ ^ epsilon ≤ D ^ (-3 / 2 : ℝ) :=
      h1.trans_eq h2
    have h3 :
        D ^ (3 / 2 : ℝ) * delta₀ ^ epsilon ≤
          D ^ (3 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hdelta_power
        (Real.rpow_nonneg (by positivity) _)
    have h4 :
        D ^ (3 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add (by positivity)]
      norm_num
    rw [h4] at h3
    exact h3
  refine' ⟨delta₀, hdelta₀_pos, hdelta₀_le_one, _⟩
  intro delta t Delta mu hdelta hdelta_le hdelta_Delta hDelta_t ht_K hmu hA
  have ht_pos : 0 < t := by linarith
  have hK8_pos : 0 < 8 * K := by linarith
  have hDelta_pos : 0 < Delta := by linarith
  set A : ℝ :=
    (t / (8 * K)) ^ m * (Delta / (2 * t)) ^ n with hA_def
  have hdelta_t : delta ≤ t := hdelta_Delta.trans hDelta_t
  have h4 : t / (8 * K) ≥ delta / (8 * K) := by
    exact (div_le_div_iff_of_pos_right hK8_pos).2 hdelta_t
  have h51 : Delta / (2 * t) ≥ delta / (2 * t) := by
    gcongr
  have h52 : delta / (2 * t) ≥ delta / (16 * K) := by
    have h_le : 2 * t ≤ 16 * K := by linarith
    have h_div : 1 / (16 * K) ≤ 1 / (2 * t) :=
      one_div_le_one_div_of_le (by positivity) h_le
    have h : delta * (1 / (16 * K)) ≤ delta * (1 / (2 * t)) := by
      gcongr
    have h' : delta / (16 * K) = delta * (1 / (16 * K)) := by ring
    have h'' : delta / (2 * t) = delta * (1 / (2 * t)) := by ring
    rw [h', h'']
    exact h
  have h5 : Delta / (2 * t) ≥ delta / (16 * K) := by
    linarith
  have h61 : (t / (8 * K)) ^ m ≥ (delta / (8 * K)) ^ m := by
    gcongr
  have h62 :
      (Delta / (2 * t)) ^ n ≥ (delta / (16 * K)) ^ n := by
    gcongr
  have h6 :
      A ≥ (delta / (8 * K)) ^ m * (delta / (16 * K)) ^ n := by
    calc
      A = (t / (8 * K)) ^ m * (Delta / (2 * t)) ^ n := rfl
      _ ≥ (delta / (8 * K)) ^ m * (Delta / (2 * t)) ^ n := by
        gcongr
      _ ≥ (delta / (8 * K)) ^ m * (delta / (16 * K)) ^ n := by
        gcongr
  have hdiv1 :
      (delta / (8 * K)) ^ m = delta ^ m / (8 * K) ^ m :=
    Real.div_rpow hdelta.le hK8_pos.le m
  have hdiv2 :
      (delta / (16 * K)) ^ n = delta ^ n / (16 * K) ^ n :=
    Real.div_rpow hdelta.le (by linarith) n
  have h73 : delta ^ m * delta ^ n = delta ^ s := by
    rw [← Real.rpow_add (by linarith), hs]
  have h7 :
      (delta / (8 * K)) ^ m * (delta / (16 * K)) ^ n =
        delta ^ s / C := by
    rw [hdiv1, hdiv2]
    have hprod :
        (delta ^ m / (8 * K) ^ m) * (delta ^ n / (16 * K) ^ n) =
          (delta ^ m * delta ^ n) /
            ((8 * K) ^ m * (16 * K) ^ n) := by
      field_simp
    rw [hprod, h73, hC_def]
  have h8 : A ≥ delta ^ s / C := by
    calc
      A ≥ (delta / (8 * K)) ^ m * (delta / (16 * K)) ^ n := h6
      _ = delta ^ s / C := h7
  have hA_pos : 0 < A := by positivity
  have h9 : (mu : ℝ) < 8 / A := by
    have h91 : A * (mu : ℝ) < 8 := hA
    calc
      (mu : ℝ) = (A * (mu : ℝ)) / A := by
        field_simp [hA_pos.ne']
      _ < 8 / A := by gcongr
  have h101 : 0 < delta ^ s := by positivity
  have h10 : 8 / A ≤ 8 * C / delta ^ s := by
    have h : 8 / A ≤ 8 / (delta ^ s / C) := by
      gcongr
    have h2 : 8 / (delta ^ s / C) = 8 * C / delta ^ s := by
      field_simp [hC_pos.ne', h101.ne']
    rw [h2] at h
    exact h
  have h_rpow_neg_s : delta ^ (-s) = (delta ^ s)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
  have h11 : (mu : ℝ) < D * delta ^ (-s) := by
    have h12 : 8 * C / delta ^ s = D * delta ^ (-s) := by
      rw [hD_def, h_rpow_neg_s]
      field_simp [h101.ne']
    rw [h12] at h10
    linarith
  have hmu_pos : 0 < (mu : ℝ) := by exact_mod_cast hmu
  have h13 :
      (mu : ℝ) ^ (3 / 2 : ℝ) <
        (D * delta ^ (-s)) ^ (3 / 2 : ℝ) := by
    gcongr
  have h14 :
      (D * delta ^ (-s)) ^ (3 / 2 : ℝ) =
        D ^ (3 / 2 : ℝ) * delta ^ (-(3 * s / 2)) := by
    have h141 :
        (D * delta ^ (-s)) ^ (3 / 2 : ℝ) =
          D ^ (3 / 2 : ℝ) * (delta ^ (-s)) ^ (3 / 2 : ℝ) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [h141]
    have h142 :
        (delta ^ (-s)) ^ (3 / 2 : ℝ) =
          delta ^ ((-s) * (3 / 2 : ℝ)) := by
      rw [← Real.rpow_mul (by positivity)]
    rw [h142]
    congr 2
    ring
  rw [h14] at h13
  have h_rpow_add_T :
      delta ^ T * delta ^ (-(3 * s / 2)) = delta ^ epsilon := by
    rw [← Real.rpow_add (by positivity)]
    simp only [hepsilon_def]
    congr 2
  have h15 :
      delta ^ T * (mu : ℝ) ^ (3 / 2 : ℝ) <
        D ^ (3 / 2 : ℝ) * delta ^ epsilon := by
    have h151 :
        delta ^ T * (mu : ℝ) ^ (3 / 2 : ℝ) <
          delta ^ T *
            (D ^ (3 / 2 : ℝ) * delta ^ (-(3 * s / 2))) := by
      gcongr
    have h152 :
        delta ^ T *
            (D ^ (3 / 2 : ℝ) * delta ^ (-(3 * s / 2))) =
          D ^ (3 / 2 : ℝ) * delta ^ epsilon := by
      calc
        delta ^ T *
            (D ^ (3 / 2 : ℝ) * delta ^ (-(3 * s / 2))) =
            D ^ (3 / 2 : ℝ) *
              (delta ^ T * delta ^ (-(3 * s / 2))) := by ring
        _ = D ^ (3 / 2 : ℝ) * delta ^ epsilon := by
          rw [h_rpow_add_T]
    rw [h152] at h151
    exact h151
  have h16 : delta ^ epsilon ≤ delta₀ ^ epsilon := by
    gcongr
  have h17 : delta ^ T * (mu : ℝ) ^ (3 / 2 : ℝ) < 1 := by
    calc
      delta ^ T * (mu : ℝ) ^ (3 / 2 : ℝ)
          < D ^ (3 / 2 : ℝ) * delta ^ epsilon := h15
      _ ≤ D ^ (3 / 2 : ℝ) * delta₀ ^ epsilon := by gcongr
      _ ≤ 1 := h_absorb
  have h18 : 0 < delta ^ T * (mu : ℝ) ^ (3 / 2 : ℝ) := by
    positivity
  have h19 :
      1 < (delta ^ T * (mu : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
    rw [one_lt_inv_iff₀]
    exact ⟨h18, h17⟩
  have h20 :
      (delta ^ T * (mu : ℝ) ^ (3 / 2 : ℝ))⁻¹ =
        delta ^ (-T) * (mu : ℝ) ^ (-3 / 2 : ℝ) := by
    have h21 :
        (delta ^ T * (mu : ℝ) ^ (3 / 2 : ℝ))⁻¹ =
          (delta ^ T)⁻¹ * ((mu : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
      field_simp
    rw [h21]
    have h22 : (delta ^ T)⁻¹ = delta ^ (-T) := by
      rw [← Real.rpow_neg (by positivity)]
    have h23 :
        ((mu : ℝ) ^ (3 / 2 : ℝ))⁻¹ =
          (mu : ℝ) ^ (-3 / 2 : ℝ) := by
      rw [← Real.rpow_neg (by positivity)]
      congr 2
      norm_num
    rw [h22, h23]
  rw [h20] at h19
  exact h19.le

end Kakeya.Cinematic
