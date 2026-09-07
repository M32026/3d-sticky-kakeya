import MyLeanRepo.Kakeya.Assouad.Subunit.Statements
import MyLeanRepo.Kakeya.Assouad.Subunit.LowDeltaMaxCase
import MyLeanRepo.Kakeya.Assouad.Subunit.HighDeltaMaxThinning
import MyLeanRepo.Kakeya.Assouad.Subunit.FrostmanDeltaMaxBound
import MyLeanRepo.Kakeya.Assouad.Subunit.AsymptoticHelper
import MyLeanRepo.Kakeya.Assouad.Subunit.ExpDomination
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Streamlined.GeneralizedKatzTao.ProbabilisticThinning
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.Proof
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Probabilistic Katz--Tao subfamily

Proof route:
1. Choose input loss `inputEta` and thinning exponent `η'`.
2. Choose `delta₀` small enough for all asymptotic inequalities.
3. For each `δ ≤ delta₀`, obtain the polynomial density-test net.
4. Apply the Frostman global deltaMax bound at scale 1.
5. Case split on `deltaMax ≤ δ^{-η'}`:
   - Low case: identity subfamily works directly.
   - High case: Bernoulli thinning extracts a Katz--Tao subfamily.

Paper: Guth--Wang--Zahl 2026, Sections 3 and 8 plus Appendix A.
-/

noncomputable section

open Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation
open Kakeya.Assouad.Subunit

namespace Kakeya.Assouad

/-- Explicit density-test net with `lossFactor ≤ 10^7` and `card ≤ δ^{-200}`. -/
lemma tube_density_test_net_explicit {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (net : TubeDensityTestNet δ),
      net.lossFactor ≤ (10^7 : ENNReal) ∧
      (net.testSets.card : ℝ) ≤ (1 / δ) ^ 200 := by
  by_cases h_large : δ ≥ 1 / 2
  · let net := large_delta_test_net hδ hδ1 h_large (10^7 : ENNReal)
      (by norm_num) ENNReal.coe_ne_top (by norm_num)
    refine ⟨net, ?_, ?_⟩
    · simpa [net, large_delta_test_net] using le_refl (10^7 : ENNReal)
    · have h1 : (net.testSets.card : ℝ) = 1 := by
        simp [net, large_delta_test_net] <;> norm_num
      rw [h1]
      have h3 : 1 ≤ 1 / δ := by apply one_le_one_div <;> linarith
      have h4 : (1 : ℝ) ≤ (1 / δ) ^ 200 := by
        calc (1 : ℝ) = 1 ^ 200 := by norm_num
          _ ≤ (1 / δ) ^ 200 := by gcongr <;> linarith
      exact h4
  · have h_small : δ < 1 / 2 := by linarith
    let net := small_delta_test_net hδ hδ1 h_small (10^7 : ENNReal)
      (by norm_num) ENNReal.coe_ne_top (by norm_num)
    refine ⟨net, ?_, ?_⟩
    · simpa [net, small_delta_test_net] using le_refl (10^7 : ENNReal)
    · have h_eq : net.testSets = smallDeltaTestSets δ hδ := by rfl
      rw [h_eq]
      exact smallDeltaTestSets_card_bound hδ h_small

/-- The polynomial-size density net contributes at most `1/16` to the
probabilistic union bound. -/
lemma density_net_failure_bound
    {δ η' x : ℝ} {N : ℕ}
    (hx : x = Real.rpow δ (-η'))
    (hN : (N : ℝ) ≤ (1 / δ) ^ (200 : ℕ))
    (hasym :
      (1 / δ) ^ (200 : ℝ) *
          Real.exp (-(11 - Real.exp 1) * δ ^ (-η')) <
        1 / 16) :
    (N : ℝ) * Real.exp (-(11 - Real.exp 1) * x) < 1 / 16 := by
  have hasym' :
      (1 / δ) ^ (200 : ℕ) *
          Real.exp
            (-(11 - Real.exp 1) *
              Real.rpow δ (-η')) <
        1 / 16 := by
    simpa [Real.rpow_natCast] using hasym
  have hle :
      (N : ℝ) * Real.exp (-(11 - Real.exp 1) * x) ≤
        (1 / δ) ^ (200 : ℕ) *
          Real.exp (-(11 - Real.exp 1) * x) := by
    exact mul_le_mul_of_nonneg_right hN (Real.exp_pos _).le
  have hrhs :
      (1 / δ) ^ (200 : ℕ) *
          Real.exp (-(11 - Real.exp 1) * x) <
        1 / 16 := by
    rw [hx]
    exact hasym'
  exact hle.trans_lt hrhs

/-- The Frostman cardinality lower bound and tube-volume upper bound imply
the Bernoulli sampling mass used in the second exponential estimate. -/
lemma thinning_mass_lower_bound
    {δ inputEta η' e6 D V1 Vδ card : ℝ}
    (hδ : 0 < δ)
    (hD : 0 < D) (hV1 : 0 < V1) (hVδ : 0 < Vδ)
    (hcard :
      D * V1 /
          (Real.rpow δ (-inputEta) * Vδ) ≤
        card)
    (hVδ_upper :
      Vδ ≤ (24 : ℝ) * Real.rpow δ 2 * V1)
    (he6 : e6 = inputEta - η' - 2) :
    Real.rpow δ (-η') / D * card ≥
      (1 / 24 : ℝ) * Real.rpow δ e6 := by
  have hrpow_eta : 0 < Real.rpow δ (-η') :=
    Real.rpow_pos_of_pos hδ _
  have hrpow_input : 0 < Real.rpow δ (-inputEta) :=
    Real.rpow_pos_of_pos hδ _
  have h5 :
      Real.rpow δ (-η') / D * card ≥
        Real.rpow δ (-η') / D *
          (D * V1 /
            (Real.rpow δ (-inputEta) * Vδ)) := by
    exact mul_le_mul_of_nonneg_left hcard
      (div_nonneg hrpow_eta.le hD.le)
  have h6 :
      Real.rpow δ (-η') / D *
          (D * V1 /
            (Real.rpow δ (-inputEta) * Vδ)) =
        Real.rpow δ (-η') * V1 /
          (Real.rpow δ (-inputEta) * Vδ) := by
    field_simp [hD.ne', hVδ.ne', hrpow_input.ne']
  rw [h6] at h5
  have h7 :
      Real.rpow δ (-η') * V1 /
          (Real.rpow δ (-inputEta) * Vδ) ≥
        Real.rpow δ (-η') * V1 /
          (Real.rpow δ (-inputEta) *
            ((24 : ℝ) * Real.rpow δ 2 * V1)) := by
    exact div_le_div_of_nonneg_left
      (mul_nonneg hrpow_eta.le hV1.le)
      (mul_pos hrpow_input hVδ)
      (mul_le_mul_of_nonneg_left hVδ_upper hrpow_input.le)
  have h8 :
      Real.rpow δ (-η') * V1 /
          (Real.rpow δ (-inputEta) *
            ((24 : ℝ) * Real.rpow δ 2 * V1)) =
        Real.rpow δ (-η') /
          (Real.rpow δ (-inputEta) * (24 : ℝ) *
            Real.rpow δ 2) := by
    field_simp [hV1.ne', hrpow_input.ne']
  rw [h8] at h7
  have hexp :
      Real.rpow δ (-η') /
          (Real.rpow δ (-inputEta) * (24 : ℝ) *
            Real.rpow δ 2) =
        (1 / 24 : ℝ) * Real.rpow δ e6 := by
    have hadd :
        Real.rpow δ (-inputEta) * Real.rpow δ 2 =
          Real.rpow δ (-inputEta + 2) :=
      (Real.rpow_add hδ (-inputEta) 2).symm
    have hsub :
        Real.rpow δ (-η') /
            Real.rpow δ (-inputEta + 2) =
          Real.rpow δ (-η' - (-inputEta + 2)) :=
      (Real.rpow_sub hδ (-η') (-inputEta + 2)).symm
    calc
      Real.rpow δ (-η') /
          (Real.rpow δ (-inputEta) * (24 : ℝ) *
            Real.rpow δ 2) =
          (1 / 24 : ℝ) *
            (Real.rpow δ (-η') /
              (Real.rpow δ (-inputEta) *
                Real.rpow δ 2)) := by ring
      _ = (1 / 24 : ℝ) *
            (Real.rpow δ (-η') /
              Real.rpow δ (-inputEta + 2)) := by rw [hadd]
      _ = (1 / 24 : ℝ) *
            Real.rpow δ (-η' - (-inputEta + 2)) := by rw [hsub]
      _ = (1 / 24 : ℝ) * Real.rpow δ e6 := by
        rw [he6]
        congr 2
        ring
  rw [hexp] at h7
  exact h7.trans h5

/-- A lower bound on the sampled mass makes the second failure probability
strictly less than `1/16`. -/
lemma thinning_failure_bound
    {δ e6 z : ℝ}
    (hcoeff : 0 < 3 - Real.exp 1)
    (hz : z ≥ (1 / 24 : ℝ) * Real.rpow δ e6)
    (hasym :
      ((3 - Real.exp 1) / 24) * Real.rpow δ e6 >
        Real.log 16) :
    Real.exp (-(3 - Real.exp 1) * z) < 1 / 16 := by
  have hlog :
      (3 - Real.exp 1) * z > Real.log 16 := by
    have hle :
        (3 - Real.exp 1) *
            ((1 / 24 : ℝ) * Real.rpow δ e6) ≤
          (3 - Real.exp 1) * z :=
      mul_le_mul_of_nonneg_left hz hcoeff.le
    have heq :
        (3 - Real.exp 1) *
            ((1 / 24 : ℝ) * Real.rpow δ e6) =
          ((3 - Real.exp 1) / 24) *
            Real.rpow δ e6 := by ring
    rw [heq] at hle
    exact hasym.trans_le hle
  have hstrict :
      Real.exp (-((3 - Real.exp 1) * z)) <
        Real.exp (-Real.log 16) :=
    Real.exp_strictMono (neg_lt_neg hlog)
  have hexp : Real.exp (-Real.log 16) = 1 / 16 := by
    rw [Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 16)]
    field_simp
  rw [hexp] at hstrict
  have harg :
      -(3 - Real.exp 1) * z =
        -((3 - Real.exp 1) * z) := by ring
  rw [harg]
  exact hstrict

theorem probabilistic_katz_tao_subfamily :
    ProbabilisticKatzTaoSubfamilyStatement := by
  intro cardLoss ktEta densityEta hcardLoss hktEta hdensityEta

  let inputEta : ℝ := min (cardLoss / 4) (min (densityEta / 2) (min (ktEta / 3) 1))
  let η' : ℝ := ktEta / 2

  have h_input_pos : 0 < inputEta := by positivity
  have h_eta'_pos : 0 < η' := by positivity
  have h_input_lt_density : inputEta < densityEta := by
    have h1 : inputEta ≤ densityEta / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have h_eta'_lt_kt : η' < ktEta := by
    dsimp only [η']
    linarith
  have h_input_le_card4 : inputEta ≤ cardLoss / 4 := min_le_left _ _
  have h_input_le_one : inputEta ≤ 1 := by
    have h1 : inputEta ≤ min (ktEta / 3) 1 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    exact le_trans h1 (min_le_right _ _)

  set e1 : ℝ := ktEta / 2 with he1_def
  set e2 : ℝ := densityEta - inputEta with he2_def
  set e3 : ℝ := cardLoss - inputEta with he3_def
  set e4 : ℝ := cardLoss - 2 * inputEta + η' with he4_def
  set e5 : ℝ := 2 - 2 * inputEta + η' with he5_def

  have he1_pos : 0 < e1 := by positivity
  have he2_pos : 0 < e2 := by linarith
  have he3_pos : 0 < e3 := by linarith
  have he4_pos : 0 < e4 := by linarith
  have he5_pos : 0 < e5 := by linarith

  rcases Subunit.exists_delta₀_mul_pow_le_one (10^8 : ℝ) (by norm_num) e1 he1_pos with
    ⟨d1, hd1_pos, hd1_le1, h_ineq1⟩
  rcases Subunit.exists_delta₀_mul_pow_le_one (4 : ℝ) (by norm_num) e2 he2_pos with
    ⟨d2, hd2_pos, hd2_le1, h_ineq2⟩
  rcases Subunit.exists_delta₀_mul_pow_le_one (24 : ℝ) (by norm_num) e3 he3_pos with
    ⟨d3, hd3_pos, hd3_le1, h_ineq3⟩
  rcases Subunit.exists_delta₀_mul_pow_le_one (48 : ℝ) (by norm_num) e4 he4_pos with
    ⟨d4, hd4_pos, hd4_le1, h_ineq4⟩
  rcases Subunit.exists_delta₀_mul_pow_le_one (24 : ℝ) (by norm_num) e5 he5_pos with
    ⟨d5, hd5_pos, hd5_le1, h_ineq5⟩

  have h_exp1_lt_3 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have h11_minus_exp_pos : 0 < 11 - Real.exp 1 := by linarith
  have h3_minus_exp_pos : 0 < 3 - Real.exp 1 := by linarith
  set e6 : ℝ := inputEta - η' - 2 with he6_def
  have he6_neg : e6 < 0 := by linarith [h_input_le_one, h_eta'_pos]
  rcases Subunit.union_bound_small_delta (A := 200) (c := 11 - Real.exp 1) (η' := η')
    (by norm_num) h11_minus_exp_pos h_eta'_pos with ⟨d6, hd6_pos, h_ineq6⟩
  rcases Subunit.rpow_negative_tends_to_inf (c := (3 - Real.exp 1) / 24) (e := e6)
    (by positivity) he6_neg with ⟨d7, hd7_pos, h_ineq7⟩

  let delta₀ := min d1 (min d2 (min d3 (min d4 (min d5 (min d6 d7)))))
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_le1 : delta₀ ≤ 1 :=
    le_trans (min_le_left _ _) hd1_le1

  refine ⟨inputEta, delta₀, h_input_pos, hdelta₀_pos, hdelta₀_le1, ?_⟩

  intro δ hδ hδ₀ F hF_nonempty hF_ball hF_distinct U hU_uniformity hFrost Y hY_dense

  have hδ1 : δ ≤ 1 := le_trans hδ₀ hdelta₀_le1

  have hδ_le_d1 : δ ≤ d1 := le_trans hδ₀ (min_le_left _ _)
  have hδ_le_d2 : δ ≤ d2 :=
    le_trans hδ₀ (min_le_right _ _ |>.trans (min_le_left _ _))
  have hδ_le_d3 : δ ≤ d3 :=
    le_trans hδ₀ (min_le_right _ _ |>.trans (min_le_right _ _) |>.trans (min_le_left _ _))
  have hδ_le_d4 : δ ≤ d4 :=
    le_trans hδ₀ (min_le_right _ _ |>.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans (min_le_left _ _))
  have hδ_le_d5 : δ ≤ d5 := by
    have h : delta₀ ≤ d5 := by unfold delta₀; simp [min_le_right, min_le_left]
    exact le_trans hδ₀ h
  have hδ_le_d6 : δ ≤ d6 := by
    have h : delta₀ ≤ d6 := by unfold delta₀; simp [min_le_right, min_le_left]
    exact le_trans hδ₀ h
  have hδ_le_d7 : δ ≤ d7 := by
    have h : delta₀ ≤ d7 := by unfold delta₀; simp [min_le_right, min_le_left]
    exact le_trans hδ₀ h

  have h_asym1 : (10^8 : ℝ) * Real.rpow δ e1 ≤ 1 := h_ineq1 δ hδ hδ_le_d1
  have h_asym2 : (4 : ℝ) * Real.rpow δ e2 ≤ 1 := h_ineq2 δ hδ hδ_le_d2
  have h_asym3 : (24 : ℝ) * Real.rpow δ e3 ≤ 1 := h_ineq3 δ hδ hδ_le_d3
  have h_asym4 : (48 : ℝ) * Real.rpow δ e4 ≤ 1 := h_ineq4 δ hδ hδ_le_d4
  have h_asym5 : (24 : ℝ) * Real.rpow δ e5 ≤ 1 := h_ineq5 δ hδ hδ_le_d5

  -- Real asymptotic bounds using helper lemmas
  have h_kt_real : (10^8 : ℝ) * Real.rpow δ (-η') ≤ Real.rpow δ (-ktEta) := by
    have h : (10^8 : ℝ) * Real.rpow δ (-η') ≤ Real.rpow δ (-η' - e1) :=
      Subunit.mul_rpow_le_rpow_sub (δ := δ) (c := 10^8) (a := -η') (e := e1) hδ (by norm_num) he1_pos h_asym1
    have h_exp : -η' - e1 = -ktEta := by simp [he1_def, η'] <;> ring
    rw [h_exp] at h
    exact h

  have h_density_real : (4 : ℝ) * Real.rpow δ densityEta ≤ Real.rpow δ inputEta := by
    have h : (4 : ℝ) * Real.rpow δ (inputEta + e2) ≤ Real.rpow δ inputEta :=
      Subunit.mul_rpow_le_rpow_add (δ := δ) (c := 4) (a := inputEta) (e := e2) hδ (by norm_num) he2_pos h_asym2
    have h_exp : densityEta = inputEta + e2 := by simp [he2_def] <;> linarith
    rw [h_exp]
    exact h

  have h_low_card_real : Real.rpow δ (-2 + cardLoss) ≤ (1 / 24 : ℝ) * Real.rpow δ (inputEta - 2) := by
    have h : (24 : ℝ) * Real.rpow δ (-2 + cardLoss) ≤ Real.rpow δ (inputEta - 2) := by
      have h_helper := Subunit.mul_rpow_le_rpow_add (δ := δ) (c := 24) (a := inputEta - 2) (e := e3) hδ (by norm_num) he3_pos h_asym3
      have h_eq : inputEta - 2 + e3 = -2 + cardLoss := by simp [he3_def] <;> ring
      rw [h_eq] at h_helper
      exact h_helper
    have hpos : 0 < Real.rpow δ (inputEta - 2) := Real.rpow_pos_of_pos hδ (inputEta - 2)
    have h' : Real.rpow δ (-2 + cardLoss) ≤ (1 / 24 : ℝ) * Real.rpow δ (inputEta - 2) := by
      calc Real.rpow δ (-2 + cardLoss)
        = (1 / 24 : ℝ) * ((24 : ℝ) * Real.rpow δ (-2 + cardLoss)) := by ring
      _ ≤ (1 / 24 : ℝ) * Real.rpow δ (inputEta - 2) := by gcongr
    exact h'

  have h_vol_real : (24 : ℝ) * Real.rpow δ 2 ≤ Real.rpow δ (2 * inputEta - η') := by
    have h : (24 : ℝ) * Real.rpow δ 2 ≤ Real.rpow δ (2 - e5) :=
      Subunit.mul_rpow_le_rpow_sub (δ := δ) (c := 24) (a := 2) (e := e5) hδ (by norm_num) he5_pos h_asym5
    have h_exp : 2 - e5 = 2 * inputEta - η' := by simp [he5_def] <;> ring
    rw [h_exp] at h
    exact h

  have h_high_card_real : Real.rpow δ (-2 + cardLoss) ≤ (1 / 48 : ℝ) * Real.rpow δ (2 * inputEta - η' - 2) := by
    have h : (48 : ℝ) * Real.rpow δ (-2 + cardLoss) ≤ Real.rpow δ (2 * inputEta - η' - 2) := by
      have h_helper := Subunit.mul_rpow_le_rpow_add (δ := δ) (c := 48) (a := 2 * inputEta - η' - 2) (e := e4) hδ (by norm_num) he4_pos h_asym4
      have h_eq : (2 * inputEta - η' - 2) + e4 = -2 + cardLoss := by simp [he4_def] <;> ring
      rw [h_eq] at h_helper
      exact h_helper
    have hpos : 0 < Real.rpow δ (2 * inputEta - η' - 2) := Real.rpow_pos_of_pos hδ (2 * inputEta - η' - 2)
    calc Real.rpow δ (-2 + cardLoss)
      = (1 / 48 : ℝ) * ((48 : ℝ) * Real.rpow δ (-2 + cardLoss)) := by ring
    _ ≤ (1 / 48 : ℝ) * Real.rpow δ (2 * inputEta - η' - 2) := by gcongr


  -- ENNReal conversion of kt bound
  have h_kt_enn : (10^8 : ENNReal) * Kakeya.realRpowENN δ (-η') ≤ Kakeya.realRpowENN δ (-ktEta) := by
    have h5 : ENNReal.ofReal ((10^8 : ℝ) * Real.rpow δ (-η')) ≤ ENNReal.ofReal (Real.rpow δ (-ktEta)) :=
      ENNReal.ofReal_mono h_kt_real
    have h_pos : 0 ≤ (10^8 : ℝ) := by norm_num
    have h6 : ENNReal.ofReal ((10^8 : ℝ) * Real.rpow δ (-η')) =
        (10^8 : ENNReal) * Kakeya.realRpowENN δ (-η') := by
      rw [ENNReal.ofReal_mul h_pos]
      <;> simp [Kakeya.realRpowENN] <;> norm_cast
    rw [h6] at h5
    simpa [Kakeya.realRpowENN] using h5

  -- ENNReal conversion of density bound
  have h_density_enn : (4 : ENNReal) * Kakeya.realRpowENN δ densityEta ≤ Kakeya.realRpowENN δ inputEta :=
    Subunit.natCoe_realRpow_le_realRpow (n := 4) hδ h_density_real

  -- Net
  rcases tube_density_test_net_explicit hδ hδ1 with ⟨net, hloss, hnet_card⟩
  have h_kt_bound : net.lossFactor * (10 : ENNReal) * Kakeya.realRpowENN δ (-η') ≤
      Kakeya.realRpowENN δ (-ktEta) := by
    calc net.lossFactor * (10 : ENNReal) * Kakeya.realRpowENN δ (-η')
      ≤ (10^7 : ENNReal) * (10 : ENNReal) * Kakeya.realRpowENN δ (-η') := by gcongr
    _ = (10^8 : ENNReal) * Kakeya.realRpowENN δ (-η') := by norm_num
    _ ≤ Kakeya.realRpowENN δ (-ktEta) := h_kt_enn

  -- Volume facts
  have hV1_pos : 0 < Kakeya.deltaTubeVolume 1 :=
    (tube_volume_scaling.2.1) 1 (by norm_num) (by norm_num) |>.1
  have hV1_ne_top : Kakeya.deltaTubeVolume 1 ≠ ⊤ :=
    (tube_volume_scaling.2.1) 1 (by norm_num) (by norm_num) |>.2
  have hVδ_pos : 0 < Kakeya.deltaTubeVolume δ :=
    (tube_volume_scaling.2.1) δ hδ hδ1 |>.1
  have hVδ_ne_top : Kakeya.deltaTubeVolume δ ≠ ⊤ :=
    (tube_volume_scaling.2.1) δ hδ hδ1 |>.2
  let canonicalδ : Kakeya.DeltaTube δ :=
    { base := 0, direction := EuclideanSpace.single (0 : Fin 3) 1, direction_unit := by simp <;> norm_num }
  have hVδ_upper : Kakeya.deltaTubeVolume δ ≤
      (24 : ENNReal) * Kakeya.realRpowENN δ 2 * Kakeya.deltaTubeVolume 1 :=
    tube_volume_scaling.2.2 δ hδ hδ1 canonicalδ

  -- Frostman bound at scale 1
  let C := Kakeya.realRpowENN δ (-inputEta)
  have hC_pos : 0 < C := by
    have h : 0 < Real.rpow δ (-inputEta) := Real.rpow_pos_of_pos hδ (-inputEta)
    simpa [C, Kakeya.realRpowENN, ENNReal.ofReal_pos] using h
  have hC_ne_top : C ≠ ⊤ := by
    simp [C, Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top
  have hC_ne_zero : C ≠ 0 := hC_pos.ne'
  have hC_inv : C⁻¹ = Kakeya.realRpowENN δ inputEta := by
    have h_pos : 0 < Real.rpow δ (-inputEta) := Real.rpow_pos_of_pos hδ (-inputEta)
    have h_eq1 : C = ENNReal.ofReal (Real.rpow δ (-inputEta)) := by
      simp [C, Kakeya.realRpowENN] <;> rfl
    rw [h_eq1]
    have h2 : (ENNReal.ofReal (Real.rpow δ (-inputEta)))⁻¹ =
        ENNReal.ofReal ((Real.rpow δ (-inputEta))⁻¹) :=
      (ENNReal.ofReal_inv_of_pos h_pos).symm
    rw [h2]
    have h_pos2 : 0 < Real.rpow δ inputEta := Real.rpow_pos_of_pos hδ inputEta
    have h3 : (Real.rpow δ (-inputEta))⁻¹ = Real.rpow δ inputEta := by
      have h4 : Real.rpow δ (-inputEta) = (Real.rpow δ inputEta)⁻¹ := Real.rpow_neg hδ.le inputEta
      rw [h4]
      field_simp [h_pos2.ne'] <;> ring
    rw [h3]
    <;> simp [Kakeya.realRpowENN] <;> rfl
  let rho : Kakeya.Streamlined.AdmissibleScale δ := ⟨1, by linarith, by norm_num⟩
  have h_frostman_bound : F.toBodyFamily.deltaMax ≤
      C * F.enncard * Kakeya.deltaTubeVolume δ / Kakeya.deltaTubeVolume 1 :=
    frostman_global_deltaMax_bound hδ hδ1 hF_nonempty (hC_ne_top := hC_ne_top) rho hFrost
  have h_deltaMax_ge_one : (1 : ENNReal) ≤ F.toBodyFamily.deltaMax :=
    deltaMax_ge_one hδ hF_nonempty
  have h_deltaMax_ne_top : F.toBodyFamily.deltaMax ≠ ⊤ := by
    have h_rhs_ne_top : (C * F.enncard * Kakeya.deltaTubeVolume δ / Kakeya.deltaTubeVolume 1) ≠ ⊤ := by
      apply ENNReal.div_ne_top
      · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hC_ne_top ENNReal.coe_ne_top) hVδ_ne_top
      · exact hV1_pos.ne'
    exact ne_top_of_le_ne_top h_rhs_ne_top h_frostman_bound

  -- F.enncard ≥ V1 / (C * Vδ)
  have h_card_frostman : F.enncard ≥
      Kakeya.deltaTubeVolume 1 / (C * Kakeya.deltaTubeVolume δ) := by
    set V1 := Kakeya.deltaTubeVolume 1 with hV1_def
    set Vδ := Kakeya.deltaTubeVolume δ with hVδ_def
    have h3 : (1 : ENNReal) ≤ C * F.enncard * Vδ / V1 :=
      le_trans h_deltaMax_ge_one h_frostman_bound
    have h5 : (C * F.enncard * Vδ / V1) * V1 = C * F.enncard * Vδ :=
      ENNReal.div_mul_cancel hV1_pos.ne' hV1_ne_top
    have h6 : (1 : ENNReal) * V1 ≤ (C * F.enncard * Vδ / V1) * V1 := by gcongr
    have h4 : V1 ≤ C * F.enncard * Vδ := by
      rw [h5] at h6
      have h7 : (1 : ENNReal) * V1 = V1 := by simp
      rw [h7] at h6
      exact h6
    have h8 : C * Vδ ≠ 0 := (ENNReal.mul_pos hC_pos.ne' hVδ_pos.ne').ne'
    have h9 : C * Vδ ≠ ⊤ := ENNReal.mul_ne_top hC_ne_top hVδ_ne_top
    have h10 : V1 / (C * Vδ) ≤ F.enncard := by
      rw [ENNReal.div_le_iff h8 h9]
      have h11 : C * F.enncard * Vδ = F.enncard * (C * Vδ) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      have h12 : V1 ≤ F.enncard * (C * Vδ) := by
        rw [←h11]
        exact h4
      exact h12
    exact h10

  -- Real version of Vδ upper bound
  have h_Vδ_upper_real : (Kakeya.deltaTubeVolume δ).toReal ≤
      (24 : ℝ) * Real.rpow δ 2 * (Kakeya.deltaTubeVolume 1).toReal := by
    set V1 := Kakeya.deltaTubeVolume 1 with hV1_def
    set Vδ := Kakeya.deltaTubeVolume δ with hVδ_def
    have h24_ne_top : (24 : ENNReal) * Kakeya.realRpowENN δ 2 ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · exact ENNReal.coe_ne_top
      · simp [Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top
    have hRHS_ne_top : (24 : ENNReal) * Kakeya.realRpowENN δ 2 * V1 ≠ ⊤ :=
      ENNReal.mul_ne_top h24_ne_top hV1_ne_top
    have h4 : Vδ.toReal ≤ ((24 : ENNReal) * Kakeya.realRpowENN δ 2 * V1).toReal :=
      (ENNReal.toReal_le_toReal hVδ_ne_top hRHS_ne_top).mpr hVδ_upper
    have h_nonneg2 : 0 ≤ Real.rpow δ 2 := (Real.rpow_pos_of_pos hδ _).le
    have h51 : ((24 : ENNReal) * Kakeya.realRpowENN δ 2 * V1).toReal =
        ((24 : ENNReal) * Kakeya.realRpowENN δ 2).toReal * V1.toReal := by
      rw [ENNReal.toReal_mul]
    have h52 : ((24 : ENNReal) * Kakeya.realRpowENN δ 2).toReal =
        (24 : ENNReal).toReal * (Kakeya.realRpowENN δ 2).toReal := by
      rw [ENNReal.toReal_mul]
    have h53 : (24 : ENNReal).toReal = (24 : ℝ) := by simp
    have h54 : (Kakeya.realRpowENN δ 2).toReal = Real.rpow δ 2 :=
      Subunit.realRpowENN_toReal hδ
    have h5 : ((24 : ENNReal) * Kakeya.realRpowENN δ 2 * V1).toReal =
        (24 : ℝ) * Real.rpow δ 2 * V1.toReal := by
      rw [h51, h52, h53, h54] <;> ring
    rw [h5] at h4
    exact h4

  -- h_card_ratio_lower via Real conversion
  have h_card_ratio_lower : Kakeya.deltaTubeVolume 1 / (C * Kakeya.deltaTubeVolume δ) ≥
      (1 / 24 : ENNReal) * Kakeya.realRpowENN δ (inputEta - 2) := by
    set V1 := Kakeya.deltaTubeVolume 1 with hV1_def
    set Vδ := Kakeya.deltaTubeVolume δ with hVδ_def
    have h_lhs_top : V1 / (C * Vδ) ≠ ⊤ := by
      apply ENNReal.div_ne_top
      · exact hV1_ne_top
      · exact (ENNReal.mul_pos hC_pos.ne' hVδ_pos.ne').ne'
    have h_rhs_top : (1 / 24 : ENNReal) * Kakeya.realRpowENN δ (inputEta - 2) ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · simp
      · simp [Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top
    have h_nonneg_C : 0 ≤ Real.rpow δ (-inputEta) := (Real.rpow_pos_of_pos hδ (-inputEta)).le
    have hC_real : C.toReal = Real.rpow δ (-inputEta) := by
      have h : C = ENNReal.ofReal (Real.rpow δ (-inputEta)) := by
        simp [C, Kakeya.realRpowENN] <;> rfl
      rw [h]
      rw [ENNReal.toReal_ofReal h_nonneg_C]
    have h_V1_pos_real : 0 < V1.toReal := ENNReal.toReal_pos hV1_pos.ne' hV1_ne_top
    have h_Vδ_pos_real : 0 < Vδ.toReal := ENNReal.toReal_pos hVδ_pos.ne' hVδ_ne_top
    have h_C_pos_real : 0 < C.toReal := by
      rw [hC_real] <;> exact Real.rpow_pos_of_pos hδ (-inputEta)
    have h1 : (V1 / (C * Vδ)).toReal = V1.toReal / (C.toReal * Vδ.toReal) := by
      rw [ENNReal.toReal_div, ENNReal.toReal_mul]
    have h_rhs1 : ((1 / 24 : ENNReal) * Kakeya.realRpowENN δ (inputEta - 2)).toReal =
        (1 / 24 : ℝ) * Real.rpow δ (inputEta - 2) := by
      have h61 : ((1 / 24 : ENNReal) * Kakeya.realRpowENN δ (inputEta - 2)).toReal =
          (1 / 24 : ENNReal).toReal * (Kakeya.realRpowENN δ (inputEta - 2)).toReal := by
        rw [ENNReal.toReal_mul]
      rw [h61]
      have h62 : (1 / 24 : ENNReal).toReal = (1 / 24 : ℝ) := by simp
      have h63 : (Kakeya.realRpowENN δ (inputEta - 2)).toReal = Real.rpow δ (inputEta - 2) :=
        Subunit.realRpowENN_toReal hδ
      rw [h62, h63] <;> ring
    have h_inv : 1 / Real.rpow δ (-inputEta) = Real.rpow δ inputEta := by
      have h_pos2 : 0 < Real.rpow δ inputEta := Real.rpow_pos_of_pos hδ inputEta
      have h4 : Real.rpow δ (-inputEta) = (Real.rpow δ inputEta)⁻¹ := Real.rpow_neg hδ.le inputEta
      rw [h4]
      field_simp [h_pos2.ne'] <;> ring
    have h3 : V1.toReal / (C.toReal * Vδ.toReal) ≥ (1 / 24 : ℝ) * Real.rpow δ (inputEta - 2) := by
      have h_step1 : V1.toReal / (C.toReal * Vδ.toReal) =
          V1.toReal * Real.rpow δ inputEta / Vδ.toReal := by
        rw [hC_real]
        have h_pos_Creal : 0 < Real.rpow δ (-inputEta) := Real.rpow_pos_of_pos hδ (-inputEta)
        have h_Cinv : (Real.rpow δ (-inputEta))⁻¹ = Real.rpow δ inputEta := by
          have h1 : (Real.rpow δ (-inputEta))⁻¹ = 1 / Real.rpow δ (-inputEta) := by simp
          rw [h1, h_inv]
        have h_eq1 : V1.toReal / (Real.rpow δ (-inputEta) * Vδ.toReal) =
            V1.toReal * (Real.rpow δ (-inputEta))⁻¹ / Vδ.toReal := by field_simp [h_pos_Creal.ne', h_Vδ_pos_real.ne'] <;> ring
        have h_eq2 : V1.toReal * (Real.rpow δ (-inputEta))⁻¹ / Vδ.toReal =
            V1.toReal * Real.rpow δ inputEta / Vδ.toReal := by
          rw [h_Cinv]
        rw [h_eq1, h_eq2]
      have h_num_nonneg : 0 ≤ V1.toReal * Real.rpow δ inputEta := by
        apply mul_nonneg
        · exact h_V1_pos_real.le
        · exact (Real.rpow_pos_of_pos hδ inputEta).le
      have h_denom_le : Vδ.toReal ≤ (24 : ℝ) * Real.rpow δ 2 * V1.toReal := h_Vδ_upper_real
      set c2 := V1.toReal * Real.rpow δ inputEta with hc2_def
      set d2 := (24 : ℝ) * Real.rpow δ 2 * V1.toReal with hd2_def
      have hc2_nonneg : 0 ≤ c2 := h_num_nonneg
      have hd2_pos : 0 < d2 := by
        dsimp only [d2]
        have h1 : 0 < (24 : ℝ) := by norm_num
        have h2 : 0 < Real.rpow δ 2 := Real.rpow_pos_of_pos hδ _
        have h3 : 0 < V1.toReal := h_V1_pos_real
        positivity
      have h_step2 : c2 / Vδ.toReal ≥ c2 / d2 := by
        have h9 : c2 / Vδ.toReal - c2 / d2 = c2 * (d2 - Vδ.toReal) / (Vδ.toReal * d2) := by
          field_simp [h_Vδ_pos_real.ne', hd2_pos.ne'] <;> ring
        have h10 : 0 ≤ c2 / Vδ.toReal - c2 / d2 := by
          rw [h9]
          apply div_nonneg
          · exact mul_nonneg hc2_nonneg (sub_nonneg.mpr h_denom_le)
          · exact mul_nonneg h_Vδ_pos_real.le hd2_pos.le
        linarith
      have h4 : Real.rpow δ inputEta / Real.rpow δ 2 = Real.rpow δ (inputEta - 2) :=
        (Real.rpow_sub hδ inputEta 2).symm
      have h_step3 : V1.toReal * Real.rpow δ inputEta / ((24 : ℝ) * Real.rpow δ 2 * V1.toReal) =
          (1 / 24 : ℝ) * Real.rpow δ (inputEta - 2) := by
        have h5 : V1.toReal * Real.rpow δ inputEta / ((24 : ℝ) * Real.rpow δ 2 * V1.toReal) =
            Real.rpow δ inputEta / ((24 : ℝ) * Real.rpow δ 2) := by
          field_simp [h_V1_pos_real.ne'] <;> ring
        rw [h5]
        have h6 : Real.rpow δ inputEta / ((24 : ℝ) * Real.rpow δ 2) =
            (1 / 24 : ℝ) * (Real.rpow δ inputEta / Real.rpow δ 2) := by
          field_simp <;> ring
        rw [h6, h4]
      rw [h_step1]
      have h_c2_def : c2 = V1.toReal * Real.rpow δ inputEta := by rfl
      have h_d2_def : d2 = (24 : ℝ) * Real.rpow δ 2 * V1.toReal := by rfl
      calc V1.toReal * Real.rpow δ inputEta / Vδ.toReal
        = c2 / Vδ.toReal := by rw [h_c2_def]
      _ ≥ c2 / d2 := h_step2
      _ = V1.toReal * Real.rpow δ inputEta / d2 := by rw [h_c2_def]
      _ = V1.toReal * Real.rpow δ inputEta / ((24 : ℝ) * Real.rpow δ 2 * V1.toReal) := by rw [h_d2_def]
      _ = (1 / 24 : ℝ) * Real.rpow δ (inputEta - 2) := h_step3
    have h4 : ((1 / 24 : ENNReal) * Kakeya.realRpowENN δ (inputEta - 2)).toReal ≤
        (V1 / (C * Vδ)).toReal := by
      rw [h_rhs1, h1]
      exact h3
    exact (ENNReal.toReal_le_toReal h_rhs_top h_lhs_top).mp h4

  -- Low case cardinality: δ^(-2+cardLoss) ≤ F.enncard
  have h_card_lower_ennreal : Kakeya.realRpowENN δ (-2 + cardLoss) ≤ F.enncard := by
    have h_pos24 : 0 ≤ (1 / 24 : ℝ) := by norm_num
    have h_cast : (1 / 24 : ENNReal) = ENNReal.ofReal (1 / 24 : ℝ) := by
      simp <;> norm_cast
    have h_conv : (1 / 24 : ENNReal) * Kakeya.realRpowENN δ (inputEta - 2) =
        ENNReal.ofReal ((1 / 24 : ℝ) * Real.rpow δ (inputEta - 2)) := by
      rw [h_cast]
      exact Subunit.coe_realRpowENN_eq_ofReal h_pos24 hδ
    have h9 : (1 / 24 : ENNReal) * Kakeya.realRpowENN δ (inputEta - 2) ≥
        Kakeya.realRpowENN δ (-2 + cardLoss) := by
      rw [h_conv]
      have h_rhs : Kakeya.realRpowENN δ (-2 + cardLoss) = ENNReal.ofReal (Real.rpow δ (-2 + cardLoss)) := by
        simp [Kakeya.realRpowENN] <;> rfl
      rw [h_rhs]
      exact ENNReal.ofReal_mono h_low_card_real
    exact le_trans h9 (le_trans h_card_ratio_lower h_card_frostman)

  -- Case split on deltaMax
  by_cases h_low : F.toBodyFamily.deltaMax ≤ Kakeya.realRpowENN δ (-η')
  · exact low_deltaMax_case hδ hδ1 hF_nonempty hF_ball hF_distinct
      inputEta densityEta cardLoss ktEta η'
      h_input_lt_density h_eta'_lt_kt hY_dense h_low h_card_lower_ennreal

  · -- High deltaMax case
    have h_high : Kakeya.realRpowENN δ (-η') < F.toBodyFamily.deltaMax :=
      lt_of_not_ge h_low
    let D := F.toBodyFamily.deltaMax
    have hD_pos : 0 < D := by
      have h1 : 0 < Kakeya.realRpowENN δ (-η') := by
        simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hδ] <;> positivity
      exact lt_trans h1 h_high
    have hD_ne_zero : D ≠ 0 := hD_pos.ne'
    have hD_ne_top' : D ≠ ⊤ := h_deltaMax_ne_top
    have h_thin : Kakeya.realRpowENN δ (-η') ≤ D := h_high.le

    let A := Kakeya.realRpowENN δ (-η')
    let B := Kakeya.realRpowENN δ inputEta
    let V1 := Kakeya.deltaTubeVolume 1
    let Vδ := Kakeya.deltaTubeVolume δ

    have hA_ne_top : A ≠ ⊤ := by simp [A, Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top
    have hB_ne_top : B ≠ ⊤ := by simp [B, Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top
    have hA_ne_zero : A ≠ 0 := by
      have h : 0 < Real.rpow δ (-η') := Real.rpow_pos_of_pos hδ (-η')
      simpa [A, Kakeya.realRpowENN, ENNReal.ofReal_pos] using h
    have hB_ne_zero : B ≠ 0 := by
      have h : 0 < Real.rpow δ inputEta := Real.rpow_pos_of_pos hδ inputEta
      simpa [B, Kakeya.realRpowENN, ENNReal.ofReal_pos] using h
    have hF_top : F.enncard ≠ ⊤ := by
      simp [Kakeya.Streamlined.TubeFamily.enncard] <;> exact ENNReal.coe_ne_top

    -- F.enncard ≥ D * V1 / (C * Vδ)
    have h_F_card_D : F.enncard ≥ D * V1 / (C * Vδ) := by
      have h5 : (C * F.enncard * Vδ / V1) * V1 = C * F.enncard * Vδ :=
        ENNReal.div_mul_cancel hV1_pos.ne' hV1_ne_top
      have h6 : D * V1 ≤ (C * F.enncard * Vδ / V1) * V1 := by
        exact mul_le_mul_of_nonneg_right h_frostman_bound (by simp)
      have h4 : D * V1 ≤ C * F.enncard * Vδ := by
        rw [h5] at h6
        exact h6
      have h8 : C * Vδ ≠ 0 := (ENNReal.mul_pos hC_pos.ne' hVδ_pos.ne').ne'
      have h9 : C * Vδ ≠ ⊤ := ENNReal.mul_ne_top hC_ne_top hVδ_ne_top
      have h10 : D * V1 / (C * Vδ) ≤ F.enncard := by
        rw [ENNReal.div_le_iff h8 h9]
        have h11 : C * F.enncard * Vδ = F.enncard * (C * Vδ) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
        have h12 : D * V1 ≤ F.enncard * (C * Vδ) := by
          rw [←h11]
          exact h4
        exact h12
      exact h10

    -- h_mu_ge_V via Real conversion
    have h_mu_ge_V : Vδ ≤ (A / D) * Y.mass := by
      by_cases hY_top : Y.mass = ⊤
      · rw [hY_top]
        have hAD_ne_zero : A / D ≠ 0 := by
          simpa [div_eq_mul_inv, hA_ne_zero, hD_ne_top'] using hA_ne_zero
        rw [ENNReal.mul_top hAD_ne_zero]
        exact le_top
      · have hY_ne_top : Y.mass ≠ ⊤ := hY_top
        have h_nonneg_eta : 0 ≤ Real.rpow δ (-η') := (Real.rpow_pos_of_pos hδ _).le
        have hA_real : A.toReal = Real.rpow δ (-η') :=
          Subunit.realRpowENN_toReal hδ
        have h_nonneg_input : 0 ≤ Real.rpow δ inputEta := (Real.rpow_pos_of_pos hδ _).le
        have hB_real : B.toReal = Real.rpow δ inputEta :=
          Subunit.realRpowENN_toReal hδ
        have h_nonneg_C : 0 ≤ Real.rpow δ (-inputEta) := (Real.rpow_pos_of_pos hδ (-inputEta)).le
        have hC_real : C.toReal = Real.rpow δ (-inputEta) :=
          Subunit.realRpowENN_toReal hδ
        have hD_toReal_pos : 0 < D.toReal := ENNReal.toReal_pos hD_pos.ne' hD_ne_top'
        have h_V1_pos_real : 0 < V1.toReal := ENNReal.toReal_pos hV1_pos.ne' hV1_ne_top
        have h_Vδ_pos_real : 0 < Vδ.toReal := ENNReal.toReal_pos hVδ_pos.ne' hVδ_ne_top
        have h_C_pos_real : 0 < C.toReal := by
          rw [hC_real] <;> exact Real.rpow_pos_of_pos hδ (-inputEta)
        have h_mass_eq : F.toBodyFamily.mass = F.enncard * Vδ := tubeFamily_mass_eq_nominal F
        have hY_dense' : Y.mass ≥ B * F.enncard * Vδ := by
          have h : Y.mass ≥ B * F.toBodyFamily.mass := hY_dense
          rw [h_mass_eq] at h
          simpa [mul_assoc] using h
        have h1 : Y.mass.toReal ≥ B.toReal * F.enncard.toReal * Vδ.toReal := by
          have h_rhs_top : B * F.enncard * Vδ ≠ ⊤ := by
            apply ENNReal.mul_ne_top
            · apply ENNReal.mul_ne_top hB_ne_top hF_top
            · exact hVδ_ne_top
          have hY' : Y.mass ≥ B * F.enncard * Vδ := hY_dense'
          have h_le : (B * F.enncard * Vδ).toReal ≤ Y.mass.toReal :=
            (ENNReal.toReal_le_toReal h_rhs_top hY_ne_top).mpr hY'
          have h_eq : (B * F.enncard * Vδ).toReal = B.toReal * F.enncard.toReal * Vδ.toReal := by
            simp [ENNReal.toReal_mul] <;> ring
          rw [h_eq] at h_le
          exact h_le
        have h_rhs_top2 : (D * V1 / (C * Vδ)) ≠ ⊤ := by
          apply ENNReal.div_ne_top
          · exact ENNReal.mul_ne_top hD_ne_top' hV1_ne_top
          · exact mul_ne_zero hC_pos.ne' hVδ_pos.ne'
        have h2 : (D * V1 / (C * Vδ)).toReal ≤ F.enncard.toReal :=
          (ENNReal.toReal_le_toReal h_rhs_top2 hF_top).mpr h_F_card_D
        have h3 : (D * V1 / (C * Vδ)).toReal = D.toReal * V1.toReal / (C.toReal * Vδ.toReal) := by
          simp [ENNReal.toReal_mul, ENNReal.toReal_div]
          <;> ring
        have h_F_card_real : F.enncard.toReal ≥ D.toReal * V1.toReal / (C.toReal * Vδ.toReal) := by
          rw [h3] at h2
          exact h2
        have h4 : Y.mass.toReal ≥ B.toReal * D.toReal * V1.toReal / C.toReal := by
          calc Y.mass.toReal
            ≥ B.toReal * F.enncard.toReal * Vδ.toReal := h1
          _ ≥ B.toReal * (D.toReal * V1.toReal / (C.toReal * Vδ.toReal)) * Vδ.toReal := by gcongr
          _ = B.toReal * D.toReal * V1.toReal / C.toReal := by
            field_simp [h_Vδ_pos_real.ne', h_C_pos_real.ne'] <;> ring
        have h5 : ((A / D) * Y.mass).toReal = (A.toReal / D.toReal) * Y.mass.toReal := by
          simp [ENNReal.toReal_mul, ENNReal.toReal_div]
          <;> ring
        have h6 : ((A / D) * Y.mass).toReal ≥
            (Kakeya.realRpowENN δ (2 * inputEta - η')).toReal * V1.toReal := by
          rw [h5]
          calc (A.toReal / D.toReal) * Y.mass.toReal
            ≥ (A.toReal / D.toReal) * (B.toReal * D.toReal * V1.toReal / C.toReal) := by gcongr
          _ = A.toReal * B.toReal * V1.toReal / C.toReal := by
            rw [hA_real, hB_real, hC_real]
            field_simp [hD_toReal_pos.ne', h_C_pos_real.ne'] <;> ring
          _ = (Kakeya.realRpowENN δ (2 * inputEta - η')).toReal * V1.toReal := by
            have h7 : A.toReal * B.toReal / C.toReal = (Kakeya.realRpowENN δ (2 * inputEta - η')).toReal := by
              rw [hA_real, hB_real, hC_real, Subunit.realRpowENN_toReal hδ]
              have h_add1 : Real.rpow δ (-η') * Real.rpow δ inputEta = Real.rpow δ (inputEta - η') := by
                have h2 : Real.rpow δ (-η' + inputEta) = Real.rpow δ (-η') * Real.rpow δ inputEta :=
                  Real.rpow_add hδ (-η') inputEta
                have h3 : -η' + inputEta = inputEta - η' := by ring
                have h4 : Real.rpow δ (-η' + inputEta) = Real.rpow δ (inputEta - η') :=
                  congr_arg (Real.rpow δ) h3
                exact Eq.trans h2.symm h4
              have h_div : Real.rpow δ (inputEta - η') / Real.rpow δ (-inputEta) =
                  Real.rpow δ (2 * inputEta - η') := by
                have h3 : (inputEta - η') - (-inputEta) = 2 * inputEta - η' := by ring
                have h4 : Real.rpow δ ((inputEta - η') - (-inputEta)) =
                    Real.rpow δ (inputEta - η') / Real.rpow δ (-inputEta) :=
                  Real.rpow_sub hδ (inputEta - η') (-inputEta)
                have h5 : Real.rpow δ ((inputEta - η') - (-inputEta)) = Real.rpow δ (2 * inputEta - η') :=
                  congr_arg (Real.rpow δ) h3
                exact Eq.trans h4.symm h5
              rw [h_add1, h_div]
            have h_assoc : A.toReal * B.toReal * V1.toReal / C.toReal = (A.toReal * B.toReal / C.toReal) * V1.toReal := by
              field_simp [h_C_pos_real.ne'] <;> ring
            rw [h_assoc, h7] <;> ring
        have h_vol_real2 : Vδ.toReal ≤
            (Kakeya.realRpowENN δ (2 * inputEta - η')).toReal * V1.toReal := by
          have h_vol_enn : Vδ ≤ Kakeya.realRpowENN δ (2 * inputEta - η') * V1 := by
            have h1 : (24 : ENNReal) * Kakeya.realRpowENN δ 2 ≤ Kakeya.realRpowENN δ (2 * inputEta - η') := by
              have h_conv : (24 : ENNReal) * Kakeya.realRpowENN δ 2 =
                  ENNReal.ofReal ((24 : ℝ) * Real.rpow δ 2) := by
                have h_cast : (24 : ENNReal) = ENNReal.ofReal (24 : ℝ) := by simp <;> norm_cast
                rw [h_cast]
                exact Subunit.coe_realRpowENN_eq_ofReal (by norm_num) hδ
              rw [h_conv]
              have h_rhs : Kakeya.realRpowENN δ (2 * inputEta - η') =
                  ENNReal.ofReal (Real.rpow δ (2 * inputEta - η')) := by
                simp [Kakeya.realRpowENN] <;> rfl
              rw [h_rhs]
              exact ENNReal.ofReal_mono h_vol_real
            have h2 : (24 : ENNReal) * Kakeya.realRpowENN δ 2 * V1 ≤
                Kakeya.realRpowENN δ (2 * inputEta - η') * V1 := by
              exact mul_le_mul_of_nonneg_right h1 (by simp)
            exact le_trans hVδ_upper h2
          have h_rhs_top : Kakeya.realRpowENN δ (2 * inputEta - η') * V1 ≠ ⊤ :=
            ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top) hV1_ne_top
          have h_result : Vδ.toReal ≤ (Kakeya.realRpowENN δ (2 * inputEta - η') * V1).toReal :=
            (ENNReal.toReal_le_toReal hVδ_ne_top h_rhs_top).mpr h_vol_enn
          simpa [ENNReal.toReal_mul] using h_result
        have h7 : Vδ.toReal ≤ ((A / D) * Y.mass).toReal := le_trans h_vol_real2 h6
        have h_lhs_top : (A / D) * Y.mass ≠ ⊤ := by
          apply ENNReal.mul_ne_top
          · apply ENNReal.div_ne_top
            · exact hA_ne_top
            · exact hD_ne_zero
          · exact hY_ne_top
        exact (ENNReal.toReal_le_toReal hVδ_ne_top h_lhs_top).mp h7

    -- h_card_bound_high via Real conversion
    have h_card_bound_high : Kakeya.realRpowENN δ (-2 + cardLoss) ≤
        (1 / 2 : ENNReal) * (A / D) * B * F.enncard := by
      have h_nonneg_eta : 0 ≤ Real.rpow δ (-η') := (Real.rpow_pos_of_pos hδ _).le
      have hA_real : A.toReal = Real.rpow δ (-η') := by
        have h : A = ENNReal.ofReal (Real.rpow δ (-η')) := by
          simp [A, Kakeya.realRpowENN] <;> rfl
        rw [h]
        rw [ENNReal.toReal_ofReal h_nonneg_eta]
      have h_nonneg_input : 0 ≤ Real.rpow δ inputEta := (Real.rpow_pos_of_pos hδ _).le
      have hB_real : B.toReal = Real.rpow δ inputEta := by
        have h : B = ENNReal.ofReal (Real.rpow δ inputEta) := by
          simp [B, Kakeya.realRpowENN] <;> rfl
        rw [h]
        rw [ENNReal.toReal_ofReal h_nonneg_input]
      have h_nonneg_C : 0 ≤ Real.rpow δ (-inputEta) := (Real.rpow_pos_of_pos hδ (-inputEta)).le
      have hC_real : C.toReal = Real.rpow δ (-inputEta) := by
        have h : C = ENNReal.ofReal (Real.rpow δ (-inputEta)) := by
          simp [C, Kakeya.realRpowENN] <;> rfl
        rw [h]
        rw [ENNReal.toReal_ofReal h_nonneg_C]
      have hD_toReal_pos : 0 < D.toReal := ENNReal.toReal_pos hD_pos.ne' hD_ne_top'
      have h_V1_pos_real : 0 < V1.toReal := ENNReal.toReal_pos hV1_pos.ne' hV1_ne_top
      have h_Vδ_pos_real : 0 < Vδ.toReal := ENNReal.toReal_pos hVδ_pos.ne' hVδ_ne_top
      have h_C_pos_real : 0 < C.toReal := by
        rw [hC_real] <;> exact Real.rpow_pos_of_pos hδ (-inputEta)
      have h_lhs_top : (1 / 2 : ENNReal) * (A / D) * B * F.enncard ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · apply ENNReal.mul_ne_top
            · simp
            · apply ENNReal.div_ne_top
              · exact hA_ne_top
              · exact hD_ne_zero
          · exact hB_ne_top
        · exact hF_top
      have h_expr : ((1 / 2 : ENNReal) * (A / D) * B * F.enncard).toReal =
          (1 / 2 : ℝ) * (A.toReal / D.toReal) * B.toReal * F.enncard.toReal := by
        simp [ENNReal.toReal_mul, ENNReal.toReal_div] <;> ring
      have h1 : ((1 / 2 : ENNReal) * (A / D) * B * F.enncard).toReal ≥
          (1 / 48 : ℝ) * Real.rpow δ (2 * inputEta - η' - 2) := by
        rw [h_expr]
        have h_rhs_top2 : (D * V1 / (C * Vδ)) ≠ ⊤ := by
          apply ENNReal.div_ne_top
          · exact ENNReal.mul_ne_top hD_ne_top' hV1_ne_top
          · exact mul_ne_zero hC_pos.ne' hVδ_pos.ne'
        have h2 : (D * V1 / (C * Vδ)).toReal ≤ F.enncard.toReal :=
          (ENNReal.toReal_le_toReal h_rhs_top2 hF_top).mpr h_F_card_D
        have h3 : (D * V1 / (C * Vδ)).toReal = D.toReal * V1.toReal / (C.toReal * Vδ.toReal) := by
          simp [ENNReal.toReal_mul, ENNReal.toReal_div]
          <;> ring
        have h_F_card_real : F.enncard.toReal ≥ D.toReal * V1.toReal / (C.toReal * Vδ.toReal) := by
          rw [h3] at h2
          exact h2
        have h4 : (1 / 2 : ℝ) * (A.toReal / D.toReal) * B.toReal * F.enncard.toReal ≥
            (1 / 2 : ℝ) * A.toReal * B.toReal * V1.toReal / (C.toReal * Vδ.toReal) := by
          calc (1 / 2 : ℝ) * (A.toReal / D.toReal) * B.toReal * F.enncard.toReal
            ≥ (1 / 2 : ℝ) * (A.toReal / D.toReal) * B.toReal *
                (D.toReal * V1.toReal / (C.toReal * Vδ.toReal)) := by gcongr
          _ = (1 / 2 : ℝ) * A.toReal * B.toReal * V1.toReal / (C.toReal * Vδ.toReal) := by
            field_simp [hD_toReal_pos.ne', h_C_pos_real.ne', h_Vδ_pos_real.ne'] <;> ring
        have h5 : (1 / 2 : ℝ) * A.toReal * B.toReal * V1.toReal / (C.toReal * Vδ.toReal) ≥
            (1 / 48 : ℝ) * Real.rpow δ (2 * inputEta - η' - 2) := by
          rw [hA_real, hB_real, hC_real]
          have h_abc : Real.rpow δ (-η') * Real.rpow δ inputEta / Real.rpow δ (-inputEta) =
              Real.rpow δ (2 * inputEta - η') := by
            have h_add1 : Real.rpow δ (-η') * Real.rpow δ inputEta = Real.rpow δ (inputEta - η') := by
              have h : Real.rpow δ (-η' + inputEta) = Real.rpow δ (-η') * Real.rpow δ inputEta :=
                Real.rpow_add hδ (-η') inputEta
              have h2 : -η' + inputEta = inputEta - η' := by ring
              rw [h2] at h
              exact h.symm
            have h_div : Real.rpow δ (inputEta - η') / Real.rpow δ (-inputEta) =
                Real.rpow δ (2 * inputEta - η') := by
              have h3 : (inputEta - η') - (-inputEta) = 2 * inputEta - η' := by ring
              have h : Real.rpow δ ((inputEta - η') - (-inputEta)) =
                  Real.rpow δ (inputEta - η') / Real.rpow δ (-inputEta) :=
                Real.rpow_sub hδ (inputEta - η') (-inputEta)
              rw [h3] at h
              exact h.symm
            rw [h_add1, h_div]
          set X : ℝ := (1 / 2 : ℝ) * Real.rpow δ (2 * inputEta - η') * V1.toReal with hX_def
          have hX_nonneg : 0 ≤ X := by
            have h1 : 0 ≤ (1 / 2 : ℝ) := by norm_num
            have h2 : 0 ≤ Real.rpow δ (2 * inputEta - η') := (Real.rpow_pos_of_pos hδ _).le
            have h3 : 0 ≤ V1.toReal := h_V1_pos_real.le
            exact mul_nonneg (mul_nonneg h1 h2) h3
          have h_denom_upper : Vδ.toReal ≤ (24 : ℝ) * Real.rpow δ 2 * V1.toReal := h_Vδ_upper_real
          have h_denom_pos : 0 < (24 : ℝ) * Real.rpow δ 2 * V1.toReal := by
            have h1 : 0 < (24 : ℝ) := by norm_num
            have h2 : 0 < Real.rpow δ 2 := Real.rpow_pos_of_pos hδ _
            exact mul_pos (mul_pos h1 h2) h_V1_pos_real
          have h_rearrange : (1 / 2 : ℝ) * Real.rpow δ (-η') * Real.rpow δ inputEta * V1.toReal / (Real.rpow δ (-inputEta) * Vδ.toReal) =
              (1 / 2 : ℝ) * (Real.rpow δ (-η') * Real.rpow δ inputEta / Real.rpow δ (-inputEta)) * V1.toReal / Vδ.toReal := by
            field_simp [h_C_pos_real.ne', h_Vδ_pos_real.ne'] <;> ring
          rw [h_rearrange]
          have h_lhs_eq : (1 / 2 : ℝ) * (Real.rpow δ (-η') * Real.rpow δ inputEta / Real.rpow δ (-inputEta)) * V1.toReal / Vδ.toReal =
              X / Vδ.toReal := by
            rw [h_abc] <;> ring
          rw [h_lhs_eq]
          have h_step : X / ((24 : ℝ) * Real.rpow δ 2 * V1.toReal) ≤ X / Vδ.toReal :=
            div_le_div_of_nonneg_left hX_nonneg h_Vδ_pos_real h_denom_upper
          have h_final : X / ((24 : ℝ) * Real.rpow δ 2 * V1.toReal) =
              (1 / 48 : ℝ) * Real.rpow δ (2 * inputEta - η' - 2) := by
            have h91 : X / ((24 : ℝ) * Real.rpow δ 2 * V1.toReal) =
                (1 / 2 : ℝ) * Real.rpow δ (2 * inputEta - η') / ((24 : ℝ) * Real.rpow δ 2) := by
              simp [hX_def] <;> field_simp [h_V1_pos_real.ne'] <;> ring
            rw [h91]
            have h92 : (1 / 2 : ℝ) * Real.rpow δ (2 * inputEta - η') / ((24 : ℝ) * Real.rpow δ 2) =
                (1 / 48 : ℝ) * (Real.rpow δ (2 * inputEta - η') / Real.rpow δ 2) := by ring
            rw [h92]
            have h93 : Real.rpow δ (2 * inputEta - η') / Real.rpow δ 2 =
                Real.rpow δ (2 * inputEta - η' - 2) := (Real.rpow_sub hδ (2 * inputEta - η') 2).symm
            rw [h93] <;> ring
          rw [h_final] at h_step
          exact h_step
        have h_ineq : (1 / 2 : ℝ) * (A.toReal / D.toReal) * B.toReal * F.enncard.toReal ≥
            (1 / 48 : ℝ) * Real.rpow δ (2 * inputEta - η' - 2) := le_trans h5 h4
        simpa [h_expr] using h_ineq
      have h2 : (Kakeya.realRpowENN δ (-2 + cardLoss)).toReal ≤
          ((1 / 2 : ENNReal) * (A / D) * B * F.enncard).toReal := by
        have h3 : (Kakeya.realRpowENN δ (-2 + cardLoss)).toReal = Real.rpow δ (-2 + cardLoss) :=
          Subunit.realRpowENN_toReal hδ
        rw [h3]
        exact le_trans h_high_card_real h1
      have h_rpow_top : Kakeya.realRpowENN δ (-2 + cardLoss) ≠ ⊤ := by
        simp [Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top
      exact (ENNReal.toReal_le_toReal h_rpow_top h_lhs_top).mp h2

    -- h_union_bound
    have h_union_bound :
        let p := (Kakeya.realRpowENN δ (-η')).toReal / D.toReal
        (net.testSets.card : ℝ) * Real.exp (-(11 - Real.exp 1) * (Kakeya.realRpowENN δ (-η')).toReal) +
        Real.exp (-(3 - Real.exp 1) * p * (F.card : ℝ)) < 1 / 8 := by
      dsimp only
      set x : ℝ := (Kakeya.realRpowENN δ (-η')).toReal with hx_def
      have h_nonneg_x : 0 ≤ Real.rpow δ (-η') := (Real.rpow_pos_of_pos hδ (-η')).le
      have hx_eq : x = Real.rpow δ (-η') := by
        simpa [hx_def] using Subunit.realRpowENN_toReal hδ
      have hx_pos : 0 < x := by
        rw [hx_eq] <;> exact Real.rpow_pos_of_pos hδ (-η')
      set p : ℝ := x / D.toReal with hp_def
      have hD_toReal_pos : 0 < D.toReal := ENNReal.toReal_pos hD_pos.ne' hD_ne_top'
      have h_nonneg_C : 0 ≤ Real.rpow δ (-inputEta) := (Real.rpow_pos_of_pos hδ (-inputEta)).le
      have hC_real : C.toReal = Real.rpow δ (-inputEta) := by
        have hC_def : C = Kakeya.realRpowENN δ (-inputEta) := by simp [C] <;> rfl
        rw [hC_def]
        exact Subunit.realRpowENN_toReal hδ
      have h_V1_pos_real : 0 < V1.toReal := ENNReal.toReal_pos hV1_pos.ne' hV1_ne_top
      have h_Vδ_pos_real : 0 < Vδ.toReal := ENNReal.toReal_pos hVδ_pos.ne' hVδ_ne_top
      have h_C_pos_real : 0 < C.toReal := by
        rw [hC_real] <;> exact Real.rpow_pos_of_pos hδ (-inputEta)
      have h_card_real : (F.card : ℝ) ≥
          D.toReal * V1.toReal / (C.toReal * Vδ.toReal) := by
        have h1 : F.enncard.toReal = (F.card : ℝ) := by
          simp [Kakeya.Streamlined.TubeFamily.enncard] <;> rfl
        have h_rhs_top : (D * V1 / (C * Vδ)) ≠ ⊤ := by
          apply ENNReal.div_ne_top
          · exact ENNReal.mul_ne_top hD_ne_top' hV1_ne_top
          · exact mul_ne_zero hC_pos.ne' hVδ_pos.ne'
        have h2 : (D * V1 / (C * Vδ)).toReal ≤ F.enncard.toReal :=
          (ENNReal.toReal_le_toReal h_rhs_top hF_top).mpr h_F_card_D
        have h3 : (D * V1 / (C * Vδ)).toReal = D.toReal * V1.toReal / (C.toReal * Vδ.toReal) := by
          simp [ENNReal.toReal_mul, ENNReal.toReal_div]
          <;> ring
        rw [h1, h3] at h2
        exact h2
      have h_p_card_lower : p * (F.card : ℝ) ≥ (1 / 24 : ℝ) * Real.rpow δ e6 := by
        have hcard' :
            D.toReal * V1.toReal /
                (Real.rpow δ (-inputEta) * Vδ.toReal) ≤
              (F.card : ℝ) := by
          rwa [hC_real] at h_card_real
        have hmain :=
          thinning_mass_lower_bound hδ hD_toReal_pos
            h_V1_pos_real h_Vδ_pos_real hcard'
            h_Vδ_upper_real he6_def
        simpa [p, hx_eq] using hmain
      have h_term1 : (net.testSets.card : ℝ) * Real.exp (-(11 - Real.exp 1) * x) < 1 / 16 := by
        exact density_net_failure_bound hx_eq hnet_card
          (h_ineq6 δ hδ hδ_le_d6)
      set z : ℝ := p * (F.card : ℝ) with hz_def
      have h_term2 : Real.exp (-(3 - Real.exp 1) * p * (F.card : ℝ)) < 1 / 16 := by
        have hz_lower :
            z ≥ (1 / 24 : ℝ) * Real.rpow δ e6 := by
          simpa [hz_def] using h_p_card_lower
        have hbound :=
          thinning_failure_bound h3_minus_exp_pos hz_lower
            (h_ineq7 δ hδ hδ_le_d7)
        simpa [z, mul_assoc] using hbound
      have h_sum : (net.testSets.card : ℝ) * Real.exp (-(11 - Real.exp 1) * x) +
          Real.exp (-(3 - Real.exp 1) * p * (F.card : ℝ)) < 1 / 8 := by
        have h : (net.testSets.card : ℝ) * Real.exp (-(11 - Real.exp 1) * x) +
            Real.exp (-(3 - Real.exp 1) * p * (F.card : ℝ)) < 1 / 16 + 1 / 16 :=
          add_lt_add h_term1 h_term2
        have h2 : (1 / 16 : ℝ) + 1 / 16 = 1 / 8 := by norm_num
        rw [h2] at h
        exact h
      exact h_sum

    have h_card_bound' : Kakeya.realRpowENN δ (-2 + cardLoss) ≤
        (1/2 : ENNReal) * (Kakeya.realRpowENN δ (-η') / D) *
        Kakeya.realRpowENN δ inputEta * F.enncard := by
      exact h_card_bound_high
    have h_mu_ge_V' : Kakeya.deltaTubeVolume δ ≤
        (Kakeya.realRpowENN δ (-η') / D) * Y.mass := by
      exact h_mu_ge_V
    exact high_deltaMax_thinning (hδ := hδ) (hδ1 := hδ1)
      (hF_nonempty := hF_nonempty) (hF_ball := hF_ball) (hF_distinct := hF_distinct)
      (η' := η') (ktEta := ktEta) (densityEta := densityEta) (cardLoss := cardLoss)
      (inputEta := inputEta) (hη'_pos := h_eta'_pos)
      (D := D) (hD := le_refl D) (hD_ne_top := hD_ne_top') (h_thin := h_thin)
      (hY_dense := hY_dense) (net := net)
      (h_kt_bound := h_kt_bound) (h_density_bound := h_density_enn)
      (h_card_bound := h_card_bound') (h_mu_ge_V := h_mu_ge_V')
      (h_union_bound := h_union_bound)

end Kakeya.Assouad
