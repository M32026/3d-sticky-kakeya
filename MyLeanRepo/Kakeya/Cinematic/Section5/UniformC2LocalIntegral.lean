import MyLeanRepo.Kakeya.Cinematic.Section5.UniformC2AnalyticInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.LocalAssembly.FinalReduction

/-!
# Uniform absolute-C2 level-set to local-integral reduction

This is the quantifier-preserving version of the closed local analytic
reduction. No family-dependent normalization is selected here.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Cinematic

theorem uniformC2_local_integral_of_level_set
    (hMultiplicity : MultiplicityLevelSelectionStatement)
    (hRestricted : RestrictedWeakTypeReductionStatement)
    (hLevel : WZ2UniformC2LocalLevelSetInput) :
    WZ2UniformC2LocalIntegralInput := by
  intro K D C_KT lambda M hK hD hC_KT hlambda hM epsilon hepsilon
  have hlambda_pos : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambda
  rcases hRestricted hMultiplicity with
    ⟨C_rw, hC_rw, hRestricted_main⟩
  rcases hLevel K D C_KT lambda M hK hD hC_KT hlambda hM
      (epsilon / 2) (by positivity) with
    ⟨delta_level, hdelta_level_pos, hdelta_level_lambda, hlevel⟩
  have hC_log : 0 < C_KT + 1 := by linarith
  rcases localAssembly_logb_absorption_general
      C_rw (C_KT + 1) (epsilon / 2) hC_rw hC_log (by positivity) with
    ⟨delta_log, hdelta_log_pos, hdelta_log_one, hlog⟩
  let delta₀ := min delta_level delta_log
  have hdelta₀_pos : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀_lambda : delta₀ ≤ 1 / lambda :=
    (min_le_left _ _).trans hdelta_level_lambda
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_lambda, ?_⟩
  intro delta hdelta hdelta₀ family hfamily hbound
    F hF_family hF_separated hF_KT c
  have hdelta_level : delta ≤ delta_level :=
    hdelta₀.trans (min_le_left _ _)
  have hdelta_log : delta ≤ delta_log :=
    hdelta₀.trans (min_le_right _ _)
  have hdelta_one : delta ≤ 1 := hdelta_log.trans hdelta_log_one
  let scale := lambda * delta
  have hscale_pos : 0 < scale := by
    dsimp only [scale]
    positivity
  let E : Set (ℝ × ℝ) :=
    Set.Icc 0 1 ×ˢ Set.Icc c (c + 1)
  have hE_meas : MeasurableSet E :=
    measurableSet_Icc.prod measurableSet_Icc
  have hE_finite : volume E < ⊤ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have hcard_plus :
      ((F.card + 1 : ℕ) : ℝ) ≤ (C_KT + 1) / delta := by
    have hcard : (F.card : ℝ) ≤ C_KT / delta := hF_KT.1
    have hone : (1 : ℝ) ≤ 1 / delta := by
      rw [le_div_iff₀ hdelta]
      simpa only [one_mul] using hdelta_one
    norm_num only [Nat.cast_add, Nat.cast_one]
    calc
      (F.card : ℝ) + 1 ≤ C_KT / delta + 1 / delta :=
        add_le_add hcard hone
      _ = (C_KT + 1) / delta := by ring
  have hcard_plus_pos : 0 < ((F.card + 1 : ℕ) : ℝ) := by positivity
  have hC_delta_pos : 0 < (C_KT + 1) / delta := by positivity
  have hlevels :
      (((Nat.log2 (F.card + 1) + 1 : ℕ) : ℝ)) ≤
        Real.logb 2 ((C_KT + 1) / delta) + 1 := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    calc
      (Nat.log2 (F.card + 1) : ℝ) + 1
          ≤ Real.logb 2 ((F.card + 1 : ℕ) : ℝ) + 1 := by
        gcongr
        exact Real.log2_le_logb (F.card + 1)
      _ ≤ Real.logb 2 ((C_KT + 1) / delta) + 1 := by
        simpa [add_comm] using
          add_le_add_right
            ((Real.logb_le_logb (show (1 : ℝ) < 2 by norm_num)
              hcard_plus_pos hC_delta_pos).2 hcard_plus) 1
  have hlevels_nonneg :
      0 ≤ (((Nat.log2 (F.card + 1) + 1 : ℕ) : ℝ)) := by positivity
  have hB_nonneg : 0 ≤ Real.rpow delta (-(epsilon / 2)) :=
    Real.rpow_nonneg hdelta.le _
  have hlevel_bound :
      ∀ mu : ℕ, 0 < mu →
        ∀ E₀ : Set (ℝ × ℝ),
          MeasurableSet E₀ →
          E₀ ⊆ E →
          (∀ p ∈ E₀,
            (mu : ℝ) ≤ multiplicity F scale p ∧
              multiplicity F scale p < 2 * mu) →
          volume E₀ ≤
            ENNReal.ofReal
              (Real.rpow delta (-(epsilon / 2)) *
                Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) := by
    intro mu hmu E₀ hE₀ hE₀_sub hmu_level
    exact hlevel delta hdelta hdelta_level family hfamily hbound
      F hF_family hF_separated hF_KT c mu hmu
      E₀ hE₀ hE₀_sub hmu_level
  have hintegral :=
    hRestricted_main scale (Real.rpow delta (-(epsilon / 2)))
      hscale_pos hB_nonneg F E hE_meas hE_finite hlevel_bound
  have habsorb :
      C_rw * (Real.logb 2 ((C_KT + 1) / delta) + 1) ≤
        Real.rpow delta (-(epsilon / 2)) :=
    hlog delta hdelta hdelta_log
  calc
    (∫ p in Set.Icc 0 1 ×ˢ Set.Icc c (c + 1),
        Real.rpow (multiplicity F (lambda * delta) p) (3 / 2 : ℝ))
        ≤ C_rw *
            (((Nat.log2 (F.card + 1) + 1 : ℕ) : ℝ)) *
              Real.rpow delta (-(epsilon / 2)) := by
          simpa [E, scale] using hintegral
    _ ≤
        (C_rw * (Real.logb 2 ((C_KT + 1) / delta) + 1)) *
          Real.rpow delta (-(epsilon / 2)) := by
      gcongr
    _ ≤
        Real.rpow delta (-(epsilon / 2)) *
          Real.rpow delta (-(epsilon / 2)) := by
      exact mul_le_mul_of_nonneg_right habsorb hB_nonneg
    _ = Real.rpow delta (-epsilon) := by
      have h :=
        Real.rpow_add hdelta (-(epsilon / 2)) (-(epsilon / 2))
      have hexp : -(epsilon / 2) + -(epsilon / 2) = -epsilon := by ring
      rw [hexp] at h
      exact h.symm

end Kakeya.Cinematic
