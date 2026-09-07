import MyLeanRepo.Kakeya.Cinematic.Section5.UniformC2AnalyticInputs
import MyLeanRepo.Kakeya.Cinematic.WZ2Input.Globalization

/-!
# Global uniform absolute-C2 export

This module globalizes the uniform local integral estimate without choosing a
family-dependent value bound. The fixed absolute two-jet bound `M` supplies
the value bound used by strip covering.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Cinematic

theorem wz2_uniformC2_input_of_local
    (hLocal : WZ2UniformC2LocalIntegralInput) :
    WZ2UniformC2Input := by
  intro K D C_KT lambda M hK hD hC_KT hlambda hM epsilon hepsilon
  have hlambda_pos : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambda
  rcases hLocal K D C_KT lambda M hK hD hC_KT hlambda hM
      (epsilon / 2) (by positivity) with
    ⟨delta_local, hdelta_local_pos, hdelta_local_lambda, hlocal⟩
  let A : ℝ := 3 * (2 * M + 5)
  have hA_nonneg : 0 ≤ A := by
    dsimp only [A]
    positivity
  rcases constant_absorption A epsilon hA_nonneg hepsilon with
    ⟨delta_A, hdelta_A_pos, hdelta_A⟩
  let delta₀ : ℝ := min delta_local delta_A
  have hdelta₀_pos : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀_lambda : delta₀ ≤ 1 / lambda :=
    (min_le_left delta_local delta_A).trans hdelta_local_lambda
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_lambda, ?_⟩
  intro delta hdelta_pos hdelta_delta₀ family hfamily hbound
    F hF_family hF_separated hF_KT
  let scale : ℝ := lambda * delta
  have hscale_pos : 0 < scale := by
    dsimp only [scale]
    positivity
  have hdelta_local_bound : delta ≤ delta_local :=
    hdelta_delta₀.trans (min_le_left delta_local delta_A)
  have hdelta_A_bound : delta ≤ delta_A :=
    hdelta_delta₀.trans (min_le_right delta_local delta_A)
  have hscale_one : scale ≤ 1 := by
    dsimp only [scale]
    simpa [mul_comm] using
      (le_div_iff₀ hlambda_pos).mp
        (hdelta_local_bound.trans hdelta_local_lambda)
  have h_strip :
      ∀ c : ℝ,
        (∫ p in (Set.Icc 0 1 ×ˢ Set.Icc c (c + 1)),
          Real.rpow (multiplicity F scale p) (3 / 2 : ℝ)) ≤
            Real.rpow delta (-(epsilon / 2)) := by
    intro c
    exact hlocal delta hdelta_pos hdelta_local_bound family hfamily
      hbound F hF_family hF_separated hF_KT c
  have h_integrable :
      Integrable
        (fun p => Real.rpow (multiplicity F scale p) (3 / 2 : ℝ))
        MeasureTheory.volume :=
    integrable_multiplicity_rpow F scale
  have hA_absorb : A ≤ Real.rpow delta (-epsilon) :=
    hdelta_A delta hdelta_pos hdelta_A_bound
  have h_global :
      (∫ p, Real.rpow (multiplicity F scale p) (3 / 2 : ℝ)) ≤
        Real.rpow delta (-(3 * epsilon / 2)) := by
    have hcover :=
      strip_covering_integral_bound F scale M
        (Real.rpow delta (-(epsilon / 2)))
        hscale_pos hscale_one
        (fun f hf x => hbound.value (hF_family hf) x)
        hM (Real.rpow_nonneg hdelta_pos.le _) h_strip h_integrable
    calc
      (∫ p, Real.rpow (multiplicity F scale p) (3 / 2 : ℝ))
          ≤ 3 * (2 * M + 5) *
              Real.rpow delta (-(epsilon / 2)) := hcover
      _ = A * Real.rpow delta (-(epsilon / 2)) := by rfl
      _ ≤ Real.rpow delta (-epsilon) *
            Real.rpow delta (-(epsilon / 2)) := by
          exact mul_le_mul_of_nonneg_right hA_absorb
            (Real.rpow_nonneg hdelta_pos.le _)
      _ = Real.rpow delta (-(3 * epsilon / 2)) := by
          change delta ^ (-epsilon) * delta ^ (-(epsilon / 2)) =
            delta ^ (-(3 * epsilon / 2))
          rw [← Real.rpow_add hdelta_pos]
          congr 1
          ring
  have hm_nonneg : ∀ p, 0 ≤ multiplicity F scale p := by
    intro p
    dsimp only [multiplicity]
    apply Finset.sum_nonneg
    intro f _
    exact Set.indicator_nonneg (fun _ => by norm_num) _
  have hnorm :=
    integral_to_elpnorm hm_nonneg (measurable_multiplicity F scale)
      Set.univ MeasurableSet.univ (fun _ _ => Set.mem_univ _)
      (Real.rpow delta (-(3 * epsilon / 2)))
      (Real.rpow_nonneg hdelta_pos.le _) h_integrable
      (by simpa using h_global)
  have hfinal_power :
      Real.rpow (Real.rpow delta (-(3 * epsilon / 2))) (2 / 3 : ℝ) =
        Real.rpow delta (-epsilon) := by
    change (delta ^ (-(3 * epsilon / 2))) ^ (2 / 3 : ℝ) =
      delta ^ (-epsilon)
    rw [← Real.rpow_mul hdelta_pos.le]
    congr 1
    ring
  rw [hfinal_power] at hnorm
  exact hnorm

end Kakeya.Cinematic
