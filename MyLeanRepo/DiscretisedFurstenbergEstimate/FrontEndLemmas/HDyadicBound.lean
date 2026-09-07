module

/-
  h_dyadic_bound: cardinality bound for T_Delta_global_dyadic.

  Uses t_delta_card_bound with:
  - T_standard = T_oriented (actual original family)
  - C_move = 17 (10Δ parent movement + 7δ_n Section 9 proximity)
  - coarse_loss = ε/20
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TDeltaGlobalConstruction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.CGlobalCardBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.NcoverEqualities
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas.HDyadicBound

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA.TDeltaGlobal
open DirecretisedFurstenbergEstimate.AppendixA (tubeSlope tubeIntercept)
open DirecretisedFurstenbergEstimate.FrontEndLemmas.CGlobalCardBound
open DyadicCardToNcover (toAffineLine)

/-- Cardinality bound for T_Delta_global_dyadic via coarse failure + packing. -/
lemma h_dyadic_bound
    {n m : ℕ} (hnm : m ≤ n)
    (Δ δ δ_n : ℝ)
    (hΔ_eq : Δ = DiscretisedFurstenbergEstimate.dyadicDelta m)
    (hδ_n_eq : δ_n = Δ ^ 2)
    (hδ_le_D2 : δ ≤ Δ ^ 2)
    (hδ_n_le_4δ : δ_n ≤ 4 * δ)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδ_pos : 0 < δ)
    (s ε εA : ℝ)
    (hs_pos : 0 < s) (hε_pos : 0 < ε)
    (hεA_eq : εA = ε / 50)
    (T_source : Finset AffineLine)
    (T_oriented T_original allTubes : Set AffineLine)
    (h_slope_source : ∀ ℓ ∈ T_source, |tubeSlope ℓ| ≤ 1)
    (h_intercept_source : ∀ ℓ ∈ T_source, |tubeIntercept ℓ| ≤ 3)
    (h_provenance : ∀ U ∈ T_Delta_global_dyadic hnm T_source,
        ∃ (ℓ_orig : AffineLine),
          ℓ_orig ∈ T_oriented ∧
          dist (toAffineLine U) ℓ_orig ≤ 17 * Δ)
    (hNcover_eq : Metric.externalCoveringNumber Δ.toNNReal T_oriented =
        Metric.externalCoveringNumber Δ.toNNReal T_original)
    (hT_original_sub : T_original ⊆ allTubes)
    (h_coarse_failure : Metric.externalCoveringNumber (Real.sqrt δ).toNNReal allTubes ≤
        ENNReal.ofReal (Real.rpow δ (-(s + εA))))
    (h_absorb_4 : Real.rpow 4 (s + εA) ≤ Real.rpow Δ (-ε / 100))
    (h_absorb_Kpack : (kPack 1 17 : ℝ) ≤
        Real.rpow Δ (ε / 20 - 3 * ε)) :
    (T_Delta_global_dyadic hnm T_source).card ≤
      Real.rpow Δ (-(2 * s + 3 * ε)) :=
by
  set coarse_loss : ℝ := ε / 20 with hcoarse_loss
  have hεA_pos : 0 < εA := by linarith [hεA_eq]
  have h_exp_nonneg : 0 ≤ s + εA := by linarith
  have h_exp_pos : 0 < s + εA := by linarith
  have hδ24_pos : 0 < Δ ^ 2 / 4 := by positivity
  have hδ_ge : Δ ^ 2 / 4 ≤ δ := by linarith
  have h_sqrtδ_nonneg : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have h_sqrtδ_le_D : Real.sqrt δ ≤ Δ := by
    have h1 : 0 ≤ Δ := by linarith
    rw [Real.sqrt_le_left h1] <;> linarith
  have h_toNNReal_le : (Real.sqrt δ).toNNReal ≤ Δ.toNNReal :=
    Real.toNNReal_mono h_sqrtδ_le_D

  have h_slope : ∀ U ∈ T_Delta_global_dyadic hnm T_source, |U.slope| ≤ 1 :=
    T_Delta_global_dyadic_slope_bound h_slope_source

  have h_intercept : ∀ U ∈ T_Delta_global_dyadic hnm T_source, |U.intercept| ≤ 3 :=
    T_Delta_global_dyadic_intercept_bound h_intercept_source

  -- Ncover chain steps
  have hNcover2 : Metric.externalCoveringNumber Δ.toNNReal T_original ≤
      Metric.externalCoveringNumber Δ.toNNReal allTubes :=
    Metric.externalCoveringNumber_mono_set hT_original_sub

  have hNcover3 : Metric.externalCoveringNumber Δ.toNNReal allTubes ≤
      Metric.externalCoveringNumber (Real.sqrt δ).toNNReal allTubes :=
    Metric.externalCoveringNumber_anti h_toNNReal_le

  -- δ^{-(s+εA)} ≤ (Δ²/4)^{-(s+εA)}
  have h_rpow1 : Real.rpow δ (-(s + εA)) ≤
      Real.rpow (Δ ^ 2 / 4) (-(s + εA)) := by
    have h1 : Real.rpow (Δ ^ 2 / 4) (s + εA) ≤ Real.rpow δ (s + εA) :=
      Real.rpow_le_rpow (by positivity) hδ_ge h_exp_nonneg
    have h2 : 0 < Real.rpow (Δ ^ 2 / 4) (s + εA) :=
      Real.rpow_pos_of_pos hδ24_pos _
    have h3 : (Real.rpow δ (s + εA))⁻¹ ≤ (Real.rpow (Δ ^ 2 / 4) (s + εA))⁻¹ := by
      simpa using one_div_le_one_div_of_le h2 h1
    have h4 : Real.rpow δ (-(s + εA)) = (Real.rpow δ (s + εA))⁻¹ :=
      Real.rpow_neg (by positivity) _
    have h5 : Real.rpow (Δ ^ 2 / 4) (-(s + εA)) =
        (Real.rpow (Δ ^ 2 / 4) (s + εA))⁻¹ :=
      Real.rpow_neg (by positivity) _
    rw [h4, h5]; exact h3

  -- (Δ²/4)^{-(s+εA)} = 4^{s+εA} · Δ^{-2(s+εA)}
  have h_rpow2 : Real.rpow (Δ ^ 2 / 4) (-(s + εA)) =
      Real.rpow 4 (s + εA) * Real.rpow Δ (-(2 * (s + εA))) := by
    set a : ℝ := s + εA with ha
    have ha_pos : 0 < a := h_exp_pos
    have h1 : Real.rpow (Δ ^ 2 / 4) (-a) = (Real.rpow (Δ ^ 2 / 4) a)⁻¹ :=
      Real.rpow_neg (by positivity) _
    have h2 : Real.rpow (Δ ^ 2 / 4) a = Real.rpow (Δ ^ 2) a / Real.rpow 4 a := by
      have hdiv : ∀ (z : ℝ), Real.rpow ((Δ ^ 2) / 4) z =
          Real.rpow (Δ ^ 2) z / Real.rpow 4 z := by
        intro z
        have h := Real.div_rpow (show (0 : ℝ) ≤ Δ ^ 2 by positivity) (show (0 : ℝ) ≤ 4 by norm_num) z
        simpa using h
      exact hdiv a
    have h3 : Real.rpow (Δ ^ 2) a = Real.rpow Δ (2 * a) := by
      have h_d2 : (Δ ^ 2 : ℝ) = Real.rpow Δ 2 := by simp [Real.rpow_two]
      rw [h_d2]
      exact (Real.rpow_mul (by linarith) 2 a).symm
    rw [h1, h2, h3]
    have h4 : (Real.rpow Δ (2 * a) / Real.rpow 4 a)⁻¹ =
        Real.rpow 4 a / Real.rpow Δ (2 * a) := by
      have hpos1 : 0 < Real.rpow Δ (2 * a) := Real.rpow_pos_of_pos hΔ_pos _
      have hpos2 : 0 < Real.rpow 4 a := Real.rpow_pos_of_pos (by norm_num) _
      field_simp [hpos1.ne', hpos2.ne'] <;> ring
    rw [h4]
    have h5 : Real.rpow Δ (-(2 * a)) = (Real.rpow Δ (2 * a))⁻¹ :=
      Real.rpow_neg (by positivity) _
    rw [h5] <;> ring

  -- 4^{s+εA} · Δ^{-2(s+εA)} ≤ Δ^{-(2s+coarse_loss)}
  have h_rpow3 : Real.rpow 4 (s + εA) * Real.rpow Δ (-(2 * (s + εA))) ≤
      Real.rpow Δ (-(2 * s + coarse_loss)) := by
    have h_goal_exp : (-ε / 100 : ℝ) + (-(2 * (s + εA))) = -(2 * s + coarse_loss) := by
      simp only [hcoarse_loss, hεA_eq] <;> ring
    have h_mul : Real.rpow 4 (s + εA) * Real.rpow Δ (-(2 * (s + εA))) ≤
        Real.rpow Δ (-ε / 100) * Real.rpow Δ (-(2 * (s + εA))) :=
      mul_le_mul_of_nonneg_right h_absorb_4 (Real.rpow_nonneg hΔ_pos.le _)
    have h_add : Real.rpow Δ (-ε / 100) * Real.rpow Δ (-(2 * (s + εA))) =
        Real.rpow Δ ((-ε / 100 : ℝ) + (-(2 * (s + εA)))) :=
      (Real.rpow_add hΔ_pos _ _).symm
    rw [h_add, h_goal_exp] at h_mul
    exact h_mul

  -- Combined real bound
  have h_real_bound : Real.rpow δ (-(s + εA)) ≤
      Real.rpow Δ (-(2 * s + coarse_loss)) :=
    calc Real.rpow δ (-(s + εA))
      ≤ Real.rpow (Δ ^ 2 / 4) (-(s + εA)) := h_rpow1
    _ = Real.rpow 4 (s + εA) * Real.rpow Δ (-(2 * (s + εA))) := h_rpow2
    _ ≤ Real.rpow Δ (-(2 * s + coarse_loss)) := h_rpow3

  -- Ncover chain combined
  have hNcover_coarse : Metric.externalCoveringNumber Δ.toNNReal T_oriented ≤
      ENNReal.ofReal (Real.rpow Δ (-(2 * s + coarse_loss))) := by
    have h1 : (Metric.externalCoveringNumber Δ.toNNReal T_oriented : ENNReal) ≤
        (Metric.externalCoveringNumber (Real.sqrt δ).toNNReal allTubes : ENNReal) := by
      exact_mod_cast calc Metric.externalCoveringNumber Δ.toNNReal T_oriented
        = Metric.externalCoveringNumber Δ.toNNReal T_original := hNcover_eq
      _ ≤ Metric.externalCoveringNumber Δ.toNNReal allTubes := hNcover2
      _ ≤ Metric.externalCoveringNumber (Real.sqrt δ).toNNReal allTubes := hNcover3
    have h2 : (Metric.externalCoveringNumber (Real.sqrt δ).toNNReal allTubes : ENNReal) ≤
        ENNReal.ofReal (Real.rpow δ (-(s + εA))) := by
      exact_mod_cast h_coarse_failure
    have h3 : ENNReal.ofReal (Real.rpow δ (-(s + εA))) ≤
        ENNReal.ofReal (Real.rpow Δ (-(2 * s + coarse_loss))) := by
      gcongr <;> exact h_real_bound
    exact le_trans (le_trans h1 h2) h3

  have h_absorb : (kPack 1 17 : ℝ) ≤ Real.rpow Δ (coarse_loss - 3 * ε) := by
    simpa [hcoarse_loss] using h_absorb_Kpack

  exact t_delta_card_bound
    Δ hΔ_eq hΔ_pos hΔ_lt_one
    s ε hs_pos hε_pos
    T_oriented
    (T_Delta_global_dyadic hnm T_source)
    1 (by norm_num)
    h_slope h_intercept
    17 (by norm_num)
    h_provenance
    coarse_loss
    hNcover_coarse
    h_absorb

end DirecretisedFurstenbergEstimate.FrontEndLemmas.HDyadicBound
