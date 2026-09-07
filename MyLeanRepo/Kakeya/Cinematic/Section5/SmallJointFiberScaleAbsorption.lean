import MyLeanRepo.Kakeya.Cinematic.Section5.SmallJointFiberScaleAbsorptionInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulScaleAbsorption

/-!
# Absorb the small joint retained-fiber regime

When `q_fiber < 8 * heavyLogLoss`, the joint representative retention lower
bound controls the original multiplicity and one explicit exponent absorbs
the dyadic logarithmic loss.
-/

namespace Kakeya.Cinematic

theorem small_joint_fiber_scale_absorption :
    SmallJointFiberScaleAbsorptionStatement := by
  intro K m n l T hK hm hn hl hmargin
  set s : ℝ := m + n + l with hs
  have hs_pos : 0 < s := by linarith
  set C : ℝ := (8 * K) ^ m * (16 * K) ^ n with hC_def
  have hC_pos : 0 < C := by positivity
  set B : ℝ := 36 * C with hB_def
  have hB_pos : 0 < B := by positivity
  rcases bounded_multiplicity_scale_absorption s T B hB_pos hmargin with
    ⟨delta₀, hdelta₀_pos, hdelta₀_one, hinner⟩
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta t Delta logLoss mu q hdelta hdelta_le hdelta_Delta hDelta_t ht_K hmu
    hlogLoss_one hlogLoss_bound hq hA
  have ht_pos : 0 < t := by linarith
  have hK8_pos : 0 < 8 * K := by linarith
  have hDelta_pos : 0 < Delta := by linarith
  set A : ℝ := (t / (8 * K)) ^ m * (Delta / (2 * t)) ^ n with hA_def
  have hdelta_t : delta ≤ t := hdelta_Delta.trans hDelta_t
  have h4 : t / (8 * K) ≥ delta / (8 * K) := by
    exact (div_le_div_iff_of_pos_right hK8_pos).2 hdelta_t
  have h5 : Delta / (2 * t) ≥ delta / (16 * K) := by
    have h51 : Delta / (2 * t) ≥ delta / (2 * t) := by gcongr
    have h52 : delta / (2 * t) ≥ delta / (16 * K) := by
      have h_le : 2 * t ≤ 16 * K := by linarith
      have h_div : 1 / (16 * K) ≤ 1 / (2 * t) :=
        one_div_le_one_div_of_le (by positivity) h_le
      have h : delta * (1 / (16 * K)) ≤ delta * (1 / (2 * t)) := by gcongr
      have h' : delta / (16 * K) = delta * (1 / (16 * K)) := by ring
      have h'' : delta / (2 * t) = delta * (1 / (2 * t)) := by ring
      rw [h', h'']
      exact h
    linarith
  have h6 : A ≥ (delta / (8 * K)) ^ m * (delta / (16 * K)) ^ n := by
    calc
      A = (t / (8 * K)) ^ m * (Delta / (2 * t)) ^ n := rfl
      _ ≥ (delta / (8 * K)) ^ m * (Delta / (2 * t)) ^ n := by gcongr
      _ ≥ (delta / (8 * K)) ^ m * (delta / (16 * K)) ^ n := by gcongr
  have hdiv1 : (delta / (8 * K)) ^ m = delta ^ m / (8 * K) ^ m :=
    Real.div_rpow hdelta.le hK8_pos.le m
  have hdiv2 : (delta / (16 * K)) ^ n = delta ^ n / (16 * K) ^ n :=
    Real.div_rpow hdelta.le (by linarith) n
  have h73 : delta ^ m * delta ^ n = delta ^ (m + n) := by
    rw [← Real.rpow_add (by linarith)]
  have h7 : (delta / (8 * K)) ^ m * (delta / (16 * K)) ^ n =
      delta ^ (m + n) / C := by
    rw [hdiv1, hdiv2]
    have hprod : (delta ^ m / (8 * K) ^ m) * (delta ^ n / (16 * K) ^ n) =
        (delta ^ m * delta ^ n) / ((8 * K) ^ m * (16 * K) ^ n) := by field_simp
    rw [hprod, h73, hC_def]
  have h8 : A ≥ delta ^ (m + n) / C := by
    calc
      A ≥ (delta / (8 * K)) ^ m * (delta / (16 * K)) ^ n := h6
      _ = delta ^ (m + n) / C := h7
  have hq1 : (q : ℝ) + 1 ≤ 9 * logLoss := by
    have h1 : (q : ℝ) < 8 * logLoss := hq
    have h2 : (q : ℝ) + 1 < 8 * logLoss + 1 := by linarith
    have h3 : 8 * logLoss + 1 ≤ 9 * logLoss := by linarith [hlogLoss_one]
    linarith
  have hq2 : 4 * ((q : ℝ) + 1) ≤ 36 * logLoss := by linarith
  have hA_pos : 0 < A := by positivity
  have h9 : A * (mu : ℝ) < 36 * logLoss := by
    calc
      A * (mu : ℝ) < 4 * ((q : ℝ) + 1) := hA
      _ ≤ 36 * logLoss := hq2
  have hlogLoss_bound' : logLoss ≤ delta ^ (-l) := by
    simpa using hlogLoss_bound
  have h10 : A * (mu : ℝ) < 36 * delta ^ (-l) := by
    calc
      A * (mu : ℝ) < 36 * logLoss := h9
      _ ≤ 36 * delta ^ (-l) := by
        exact mul_le_mul_of_nonneg_left hlogLoss_bound' (by norm_num)
  have h11 : delta ^ (m + n) * (mu : ℝ) < 36 * C * delta ^ (-l) := by
    have h111 : delta ^ (m + n) / C * (mu : ℝ) ≤ A * (mu : ℝ) := by gcongr
    have h112 : delta ^ (m + n) / C * (mu : ℝ) < 36 * delta ^ (-l) :=
      h111.trans_lt h10
    have h : (delta ^ (m + n) * (mu : ℝ)) / C < 36 * delta ^ (-l) := by
      have h_eq : delta ^ (m + n) / C * (mu : ℝ) =
          (delta ^ (m + n) * (mu : ℝ)) / C := by
        field_simp [hC_pos.ne']
      rw [h_eq] at h112
      exact h112
    calc
      delta ^ (m + n) * (mu : ℝ)
        = ((delta ^ (m + n) * (mu : ℝ)) / C) * C := by
          field_simp [hC_pos.ne']
      _ < (36 * delta ^ (-l)) * C := by gcongr
      _ = 36 * C * delta ^ (-l) := by ring
  have h122 : 0 < delta ^ l := by positivity
  have h12 : delta ^ s * (mu : ℝ) < B := by
    have h121 : delta ^ s = delta ^ (m + n) * delta ^ l := by
      rw [← Real.rpow_add hdelta, hs]
    have hneg : delta ^ (-l) = (delta ^ l)⁻¹ := Real.rpow_neg hdelta.le l
    rw [h121, hB_def]
    rw [hneg] at h11
    calc
      delta ^ (m + n) * delta ^ l * (mu : ℝ)
        = (delta ^ (m + n) * (mu : ℝ)) * delta ^ l := by ring
      _ < (36 * C * (delta ^ l)⁻¹) * delta ^ l := by gcongr
      _ = 36 * C := by
        field_simp [h122.ne']
  exact hinner hdelta hdelta_le hmu h12

end Kakeya.Cinematic
