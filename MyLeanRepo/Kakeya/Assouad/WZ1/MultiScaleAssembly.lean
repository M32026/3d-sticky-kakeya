import MyLeanRepo.Kakeya.Assouad.WZ1.ADScaleRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers
import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Multi-scale IsADSet1 assembly for WZ1 Lemma 19
-/

noncomputable section

open Metric Set

namespace Kakeya.Assouad

lemma multiscale_to_ad_set
    (E : Set ℝ) (rho alpha delta loss outputLoss q : ℝ)
    (N : ℕ) (s : ℕ → NNReal)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hdelta_pos : 0 < delta) (hdelta1 : delta ≤ 1)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hloss_pos : 0 < loss) (houtput_pos : 0 < outputLoss)
    (hq1 : 1 ≤ q)
    (hs0 : (s 0 : ℝ) = rho)
    (hsN : (s N : ℝ) = Real.sqrt rho)
    (hs_pos : ∀ k ≤ N, 0 < (s k : ℝ))
    (hs_mono : ∀ k < N, (s k : ℝ) ≤ (s (k+1) : ℝ))
    (hs_ratio : ∀ k < N, (s (k+1) : ℝ) ≤ q * (s k : ℝ))
    (h_find : ∀ (x : ℝ), rho ≤ x → x ≤ Real.sqrt rho →
      ∃ k < N, (s k : ℝ) ≤ x ∧ x ≤ (s (k+1) : ℝ))
    (h_bound : ∀ k < N, ∀ (r : ℝ), (s k : ℝ) ≤ r → r ≤ Real.sqrt rho → ∀ x : ℝ,
        (Metric.externalCoveringNumber (s k)
            (E ∩ Metric.closedBall x r) : ENNReal) ≤
          ENNReal.ofReal (Real.rpow delta (-loss) * Real.rpow (r / (s k : ℝ)) alpha))
    (h_diam : ∀ y z, y ∈ E → z ∈ E → dist y z ≤ 2 * Real.sqrt rho)
    (h_bounded : E ⊆ Set.Icc (-4 : ℝ) 4)
    (h_absorb3 : (3 : ℝ) * Real.rpow delta (-loss) * q^alpha ≤ Real.rpow delta (-outputLoss)) :
    IsADSet1 E rho alpha (ENNReal.ofReal (Real.rpow delta (-outputLoss))) := by
  let C_target : ENNReal := ENNReal.ofReal (Real.rpow delta (-outputLoss))
  have h1_loss : (1 : ℝ) ≤ Real.rpow delta (-loss) := by
    have h2 : -loss ≤ 0 := by linarith
    have h3 := Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta1 h2
    simpa using h3
  have h1q : (1 : ℝ) ≤ q^alpha := Real.one_le_rpow hq1 (by linarith)
  have h_mul : (1 : ℝ) ≤ Real.rpow delta (-loss) * q^alpha := by
    have h1 : (1 : ℝ) ≤ Real.rpow delta (-loss) := h1_loss
    have h2 : (1 : ℝ) ≤ q^alpha := h1q
    have h3 : 0 ≤ Real.rpow delta (-loss) := by positivity
    nlinarith
  have h_3_le : (3 : ℝ) ≤ Real.rpow delta (-outputLoss) := by
    calc (3 : ℝ) ≤ (3 : ℝ) * (Real.rpow delta (-loss) * q^alpha) := by
          have h4 : (1 : ℝ) ≤ Real.rpow delta (-loss) * q^alpha := h_mul
          have h5 : 0 ≤ (3 : ℝ) := by norm_num
          nlinarith
         _ = (3 : ℝ) * Real.rpow delta (-loss) * q^alpha := by ring
         _ ≤ Real.rpow delta (-outputLoss) := h_absorb3
  have hC_one : (1 : ENNReal) ≤ C_target := by
    have h : (1 : ℝ) ≤ Real.rpow delta (-outputLoss) := by
      have h2 : -outputLoss ≤ 0 := by linarith
      have h3 := Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta1 h2
      simpa using h3
    simpa [C_target] using ENNReal.ofReal_le_ofReal h
  have hC3 : (3 : ENNReal) ≤ C_target := by
    simpa [C_target] using ENNReal.ofReal_le_ofReal h_3_le
  have h_absorb3' : ENNReal.ofReal ((3 : ℝ) * Real.rpow delta (-loss) * q^alpha) ≤ C_target :=
    ENNReal.ofReal_le_ofReal h_absorb3
  have h_absorb1 : Real.rpow delta (-loss) * q^alpha ≤ Real.rpow delta (-outputLoss) := by
    have h : Real.rpow delta (-loss) * q^alpha ≤ (3 : ℝ) * Real.rpow delta (-loss) * q^alpha := by
      have hpos : 0 < Real.rpow delta (-loss) := Real.rpow_pos_of_pos hdelta_pos _
      nlinarith
    exact h.trans h_absorb3
  have h_absorb1' : ENNReal.ofReal (Real.rpow delta (-loss) * q^alpha) ≤ C_target :=
    ENNReal.ofReal_le_ofReal h_absorb1
  have hsqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have hsk_pos : ∀ k, k ≤ N → 0 < (s k : ℝ) := fun k hk => hs_pos k hk
  refine ⟨hrho, halpha, halpha1, hC_one, h_bounded, ?_⟩
  intro t ht_nonneg hrho_le_t ht_one x r ht_le_r hr_le_one
  set A_set : Set ℝ := E ∩ Metric.closedBall x r with hA_def
  have ht_pos : 0 < t := by linarith
  by_cases h_case1 : t ≥ Real.sqrt rho
  · -- Case 1: t ≥ sqrt(rho), 3 balls of radius t
    have h_diam_2t : ∀ a b, a ∈ A_set → b ∈ A_set → dist a b ≤ 2 * t := by
      intro a b ha hb
      have h1 : dist a b ≤ 2 * Real.sqrt rho := h_diam a b ha.1 hb.1
      have h2 : 2 * Real.sqrt rho ≤ 2 * t := by gcongr
      exact h1.trans h2
    rcases real_cover_by_three_balls ht_pos h_diam_2t with ⟨centers, hcard3, hcover3⟩
    have h5 : Metric.IsCover ⟨t, ht_nonneg⟩ A_set (centers : Set ℝ) := by
      intro a ha
      have h6 : a ∈ ⋃ c ∈ centers, closedBall c t := hcover3 ha
      rcases Set.mem_iUnion₂.mp h6 with ⟨c, hc, hball⟩
      refine ⟨c, hc, ?_⟩
      simpa [Set.mem_setOf_eq] using dist_le_coe.mp hball
    have h6 : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤
        (centers.card : ENNReal) := by
      have h_main := h5.externalCoveringNumber_le_encard
      have h7 : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤ ((centers : Set ℝ).encard : ENNReal) := by
        exact_mod_cast h_main
      have h8 : ((centers : Set ℝ).encard : ENNReal) = (centers.card : ENNReal) := by simp
      rw [h8] at h7
      exact h7
    have hcov : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤ (3 : ENNReal) := by
      have h7 : (centers.card : ENNReal) ≤ 3 := by exact_mod_cast hcard3
      exact h6.trans h7
    have h_rt : (1 : ENNReal) ≤ Kakeya.realRpowENN (r / t) alpha := by
      simp only [Kakeya.realRpowENN]
      have h5 : 1 ≤ r / t := by
        calc (1 : ℝ) = t / t := by field_simp [ht_pos.ne']
             _ ≤ r / t := by gcongr
      have h6 : (1 : ℝ) ≤ Real.rpow (r / t) alpha := Real.one_le_rpow h5 (by linarith)
      simpa using ENNReal.ofReal_le_ofReal h6
    have h_final : (3 : ENNReal) ≤ C_target * Kakeya.realRpowENN (r / t) alpha := by
      calc (3 : ENNReal) ≤ C_target := hC3
           _ ≤ C_target * Kakeya.realRpowENN (r / t) alpha := le_mul_of_one_le_right' h_rt
    exact hcov.trans h_final
  · -- t < sqrt(rho)
    have h_t_lt_sqrt : t < Real.sqrt rho := by linarith
    rcases h_find t hrho_le_t (by linarith) with ⟨k, hk_lt_N, h_sk_le_t, h_t_le_sk1⟩
    have hsk_k_pos : 0 < (s k : ℝ) := hs_pos k (by linarith)
    have h_ratio : t / (s k : ℝ) ≤ q := by
      have h1 : t ≤ (s (k+1) : ℝ) := h_t_le_sk1
      have h2 : (s (k+1) : ℝ) ≤ q * (s k : ℝ) := hs_ratio k hk_lt_N
      have h3 : t ≤ q * (s k : ℝ) := h1.trans h2
      have h4 : 0 < (s k : ℝ) := hsk_k_pos
      calc t / (s k : ℝ) ≤ (q * (s k : ℝ)) / (s k : ℝ) := by gcongr
           _ = q := by field_simp [h4.ne'] <;> ring
    by_cases h_r_ge_sqrt : r ≥ Real.sqrt rho
    · -- Case 2: r ≥ sqrt(rho), 3-ball cover at sqrt(rho)
      have h_diam_2sqrt : ∀ a b, a ∈ A_set → b ∈ A_set → dist a b ≤ 2 * Real.sqrt rho := by
        intro a b ha hb; exact h_diam a b ha.1 hb.1
      rcases real_cover_by_three_balls hsqrt_pos h_diam_2sqrt with ⟨centers, hcard3, hcover3⟩
      have h_union : A_set ⊆ ⋃ c ∈ centers, E ∩ Metric.closedBall c (Real.sqrt rho) := by
        intro y hy
        have h6 : y ∈ ⋃ c ∈ centers, closedBall c (Real.sqrt rho) := hcover3 hy
        rcases Set.mem_iUnion₂.mp h6 with ⟨c, hc, hball⟩
        exact Set.mem_iUnion₂.mpr ⟨c, hc, ⟨hy.1, hball⟩⟩
      have h_pieces : ∀ c ∈ centers,
          (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩
            (E ∩ Metric.closedBall c (Real.sqrt rho)) : ENNReal) ≤
          ENNReal.ofReal (Real.rpow delta (-loss) * (Real.sqrt rho / (s k : ℝ))^alpha) := by
        intro c hc
        have h_nn : s k ≤ ⟨t, ht_nonneg⟩ := by
          exact Subtype.mk_le_mk.mpr h_sk_le_t
        have h1 : Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ (E ∩ Metric.closedBall c (Real.sqrt rho)) ≤
            Metric.externalCoveringNumber (s k) (E ∩ Metric.closedBall c (Real.sqrt rho)) :=
          Metric.externalCoveringNumber_anti h_nn
        have h2 := h_bound k hk_lt_N (Real.sqrt rho) (by linarith) (by linarith) c
        have h1' : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ (E ∩ Metric.closedBall c (Real.sqrt rho)) : ENNReal) ≤
            (Metric.externalCoveringNumber (s k) (E ∩ Metric.closedBall c (Real.sqrt rho)) : ENNReal) := by
          exact_mod_cast h1
        exact h1'.trans h2
      have h_bunion : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤
          (centers.card : ENNReal) * ENNReal.ofReal (Real.rpow delta (-loss) * (Real.sqrt rho / (s k : ℝ))^alpha) := by
        have h3 : A_set ⊆ ⋃ c ∈ centers, (E ∩ Metric.closedBall c (Real.sqrt rho)) := h_union
        have h4 := externalCoveringNumber_biUnion_le_card h_pieces
        have h5 : Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set ≤
            Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ (⋃ c ∈ centers, (E ∩ Metric.closedBall c (Real.sqrt rho))) :=
          Metric.externalCoveringNumber_mono_set h3
        have h5' : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤
            (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ (⋃ c ∈ centers, (E ∩ Metric.closedBall c (Real.sqrt rho))) : ENNReal) := by
          exact_mod_cast h5
        exact h5'.trans h4
      have h9 : Real.rpow (Real.sqrt rho / (s k : ℝ)) alpha ≤ q^alpha * Real.rpow (r / t) alpha := by
        have h10 : Real.sqrt rho / (s k : ℝ) = (Real.sqrt rho / t) * (t / (s k : ℝ)) := by
          field_simp [ht_pos.ne', hsk_k_pos.ne'] <;> ring
        rw [h10]
        have h11 : 0 ≤ Real.sqrt rho / t := by positivity
        have h12 : 0 ≤ t / (s k : ℝ) := by positivity
        have h_mul_rpow : Real.rpow ((Real.sqrt rho / t) * (t / (s k : ℝ))) alpha =
            Real.rpow (Real.sqrt rho / t) alpha * Real.rpow (t / (s k : ℝ)) alpha :=
          Real.mul_rpow h11 h12
        rw [h_mul_rpow]
        have h13 : Real.rpow (t / (s k : ℝ)) alpha ≤ q^alpha := Real.rpow_le_rpow (by positivity) h_ratio (by linarith)
        have h14 : Real.sqrt rho / t ≤ r / t := by gcongr
        have h15 : Real.rpow (Real.sqrt rho / t) alpha ≤ Real.rpow (r / t) alpha := Real.rpow_le_rpow (by positivity) h14 (by linarith)
        have h_nonneg1 : 0 ≤ Real.rpow (Real.sqrt rho / t) alpha := Real.rpow_nonneg (by positivity) alpha
        have h_nonneg2 : 0 ≤ Real.rpow (t / (s k : ℝ)) alpha := Real.rpow_nonneg (by positivity) alpha
        have h16 : Real.rpow (Real.sqrt rho / t) alpha * Real.rpow (t / (s k : ℝ)) alpha ≤ q^alpha * Real.rpow (r / t) alpha := by
          calc
            Real.rpow (Real.sqrt rho / t) alpha * Real.rpow (t / (s k : ℝ)) alpha
              ≤ Real.rpow (r / t) alpha * Real.rpow (t / (s k : ℝ)) alpha := by
                exact mul_le_mul_of_nonneg_right h15 h_nonneg2
            _ ≤ Real.rpow (r / t) alpha * q^alpha := by
                have hrt_nonneg : 0 ≤ r / t := by apply div_nonneg <;> linarith
                exact mul_le_mul_of_nonneg_left h13 (Real.rpow_nonneg hrt_nonneg alpha)
            _ = q^alpha * Real.rpow (r / t) alpha := by ring
        exact h16
      have h10 : (centers.card : ENNReal) ≤ (3 : ENNReal) := by exact_mod_cast hcard3
      have h11 : (centers.card : ENNReal) * ENNReal.ofReal (Real.rpow delta (-loss) * (Real.sqrt rho / (s k : ℝ))^alpha) ≤
          (3 : ENNReal) * ENNReal.ofReal (Real.rpow delta (-loss) * q^alpha * (r / t)^alpha) := by
        have h_pos_loss : 0 ≤ Real.rpow delta (-loss) := by positivity
        have h12 : Real.rpow delta (-loss) * Real.rpow (Real.sqrt rho / (s k : ℝ)) alpha ≤
            Real.rpow delta (-loss) * (q^alpha * Real.rpow (r / t) alpha) :=
          mul_le_mul_of_nonneg_left h9 h_pos_loss
        have h13 : Real.rpow delta (-loss) * (q^alpha * Real.rpow (r / t) alpha) =
            Real.rpow delta (-loss) * q^alpha * Real.rpow (r / t) alpha := by ring
        have h14 : ENNReal.ofReal (Real.rpow delta (-loss) * Real.rpow (Real.sqrt rho / (s k : ℝ)) alpha) ≤
            ENNReal.ofReal (Real.rpow delta (-loss) * q^alpha * Real.rpow (r / t) alpha) :=
          ENNReal.ofReal_le_ofReal (h12.trans_eq h13)
        exact mul_le_mul' h10 h14
      have h14 : (3 : ENNReal) * ENNReal.ofReal (Real.rpow delta (-loss) * q^alpha * (r / t)^alpha) =
          ENNReal.ofReal ((3 : ℝ) * Real.rpow delta (-loss) * q^alpha) * Kakeya.realRpowENN (r / t) alpha := by
        simp only [Kakeya.realRpowENN]
        set A : ℝ := (3 : ℝ) * Real.rpow delta (-loss) * q^alpha with hA_def
        set B : ℝ := (r / t)^alpha with hB_def
        have hA_nonneg : 0 ≤ A := by positivity
        have hrt_nonneg : 0 ≤ r / t := by apply div_nonneg <;> linarith
        have hB_nonneg : 0 ≤ B := Real.rpow_nonneg hrt_nonneg alpha
        have h_eq1 : (3 : ENNReal) * ENNReal.ofReal (Real.rpow delta (-loss) * q^alpha * (r / t)^alpha) =
            ENNReal.ofReal (A * B) := by
          have h3_pos : (0 : ℝ) ≤ 3 := by norm_num
          have h_step1 : (3 : ENNReal) * ENNReal.ofReal (Real.rpow delta (-loss) * q^alpha * (r / t)^alpha) =
              ENNReal.ofReal ((3 : ℝ) * (Real.rpow delta (-loss) * q^alpha * (r / t)^alpha)) := by
            have h3_cast : (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) := by simp
            rw [h3_cast]
            rw [← ENNReal.ofReal_mul h3_pos]
            <;> rfl
          rw [h_step1]
          have h_eq2 : (3 : ℝ) * (Real.rpow delta (-loss) * q^alpha * (r / t)^alpha) = A * B := by
            simp [A, B] <;> ring
          rw [h_eq2]
        rw [h_eq1]
        have h3 : ENNReal.ofReal (A * B) = ENNReal.ofReal A * ENNReal.ofReal B := by
          rw [ENNReal.ofReal_mul hA_nonneg]
        rw [h3]
        <;> rfl
      have h15 : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤
          ENNReal.ofReal ((3 : ℝ) * Real.rpow delta (-loss) * q^alpha) * Kakeya.realRpowENN (r / t) alpha :=
        h_bunion.trans (h11.trans (by rw [h14]))
      have h16 : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤
          C_target * Kakeya.realRpowENN (r / t) alpha := by
        calc (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal)
          ≤ ENNReal.ofReal ((3 : ℝ) * Real.rpow delta (-loss) * q^alpha) * Kakeya.realRpowENN (r / t) alpha := h15
        _ ≤ C_target * Kakeya.realRpowENN (r / t) alpha := by gcongr
      exact h16
    · -- Case 3: r < sqrt(rho), continuous bound at scale s_k
      have h_nn : s k ≤ ⟨t, ht_nonneg⟩ := by
        exact Subtype.mk_le_mk.mpr h_sk_le_t
      have h1 : Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set ≤
          Metric.externalCoveringNumber (s k) A_set :=
        Metric.externalCoveringNumber_anti h_nn
      have h2 : Metric.externalCoveringNumber (s k) A_set ≤
          Metric.externalCoveringNumber (s k) (E ∩ Metric.closedBall x r) :=
        Metric.externalCoveringNumber_mono_set (Set.Subset.refl _)
      have h3 := h_bound k hk_lt_N r (by linarith) (by linarith) x
      have h1' : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤
          (Metric.externalCoveringNumber (s k) A_set : ENNReal) := by exact_mod_cast h1
      have h2' : (Metric.externalCoveringNumber (s k) A_set : ENNReal) ≤
          (Metric.externalCoveringNumber (s k) (E ∩ Metric.closedBall x r) : ENNReal) := by exact_mod_cast h2
      have h4 : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤
          ENNReal.ofReal (Real.rpow delta (-loss) * (r / (s k : ℝ))^alpha) :=
        h1'.trans (h2'.trans h3)
      have h6 : Real.rpow (r / (s k : ℝ)) alpha ≤ q^alpha * Real.rpow (r / t) alpha := by
        have h7 : r / (s k : ℝ) = (r / t) * (t / (s k : ℝ)) := by
          field_simp [ht_pos.ne', hsk_k_pos.ne'] <;> ring
        rw [h7]
        have h8 : 0 ≤ r / t := by
          have h81 : 0 ≤ r := by linarith
          exact div_nonneg h81 (by linarith)
        have h9 : 0 ≤ t / (s k : ℝ) := by
          have h91 : 0 ≤ t := by linarith
          exact div_nonneg h91 (by linarith)
        have h10eq : Real.rpow ((r / t) * (t / (s k : ℝ))) alpha =
            Real.rpow (r / t) alpha * Real.rpow (t / (s k : ℝ)) alpha := by
          simpa using Real.mul_rpow h8 h9
        rw [h10eq]
        have h10le : Real.rpow (t / (s k : ℝ)) alpha ≤ q^alpha :=
          Real.rpow_le_rpow h9 h_ratio (by linarith)
        have h11nonneg : 0 ≤ Real.rpow (r / t) alpha := Real.rpow_nonneg h8 alpha
        have h11 : Real.rpow (r / t) alpha * Real.rpow (t / (s k : ℝ)) alpha ≤
            Real.rpow (r / t) alpha * q^alpha :=
          mul_le_mul_of_nonneg_left h10le h11nonneg
        have h12comm : Real.rpow (r / t) alpha * q^alpha = q^alpha * Real.rpow (r / t) alpha := by ring
        rw [h12comm] at h11
        exact h11
      have h_pos_loss : 0 ≤ Real.rpow delta (-loss) := by positivity
      have h12 : Real.rpow delta (-loss) * Real.rpow (r / (s k : ℝ)) alpha ≤
          Real.rpow delta (-loss) * (q^alpha * Real.rpow (r / t) alpha) :=
        mul_le_mul_of_nonneg_left h6 h_pos_loss
      have h13 : Real.rpow delta (-loss) * (q^alpha * Real.rpow (r / t) alpha) =
          Real.rpow delta (-loss) * q^alpha * Real.rpow (r / t) alpha := by ring
      have h14 : ENNReal.ofReal (Real.rpow delta (-loss) * Real.rpow (r / (s k : ℝ)) alpha) ≤
          ENNReal.ofReal (Real.rpow delta (-loss) * q^alpha * Real.rpow (r / t) alpha) :=
        ENNReal.ofReal_le_ofReal (h12.trans_eq h13)
      have h15 : ENNReal.ofReal (Real.rpow delta (-loss) * q^alpha * Real.rpow (r / t) alpha) =
          ENNReal.ofReal (Real.rpow delta (-loss) * q^alpha) * Kakeya.realRpowENN (r / t) alpha := by
        simp only [Kakeya.realRpowENN]
        set A : ℝ := Real.rpow delta (-loss) * q^alpha with hA_def
        set B : ℝ := Real.rpow (r / t) alpha with hB_def
        have hA_nonneg : 0 ≤ A := by positivity
        have hrt_nonneg : 0 ≤ r / t := by apply div_nonneg <;> linarith
        have hB_nonneg : 0 ≤ B := Real.rpow_nonneg hrt_nonneg alpha
        have h3 : ENNReal.ofReal (A * B) = ENNReal.ofReal A * ENNReal.ofReal B := by
          rw [ENNReal.ofReal_mul hA_nonneg]
        exact h3
      have h4' : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤
          ENNReal.ofReal (Real.rpow delta (-loss) * Real.rpow (r / (s k : ℝ)) alpha) := by
        simpa using h4
      have h_final : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤
          C_target * Kakeya.realRpowENN (r / t) alpha := by
        calc (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal)
          ≤ ENNReal.ofReal (Real.rpow delta (-loss) * Real.rpow (r / (s k : ℝ)) alpha) := h4'
        _ ≤ ENNReal.ofReal (Real.rpow delta (-loss) * q^alpha * Real.rpow (r / t) alpha) := h14
        _ = ENNReal.ofReal (Real.rpow delta (-loss) * q^alpha) * Kakeya.realRpowENN (r / t) alpha := h15
        _ ≤ C_target * Kakeya.realRpowENN (r / t) alpha := by gcongr
      exact h_final

end Kakeya.Assouad
