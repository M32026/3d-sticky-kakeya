import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.Subunit.ExpDomination
import MyLeanRepo.Kakeya.Assouad.Targets.ProbabilisticKatzTaoSubfamily

/-!
# Small-scale thresholds for the direct pure WZ2 Wolff floor

This module isolates the finite minimum of scalar thresholds used by the
literal complete-full-fiber Node 1 route.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2DirectWolffFloorThresholds
    (coreDelta₀ c inputEta pruneEta coreEta ktEta thinningEta
      cwaDensityGap cardinalityGap sourceGap kappa : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  core :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      delta ≤ coreDelta₀
  rho :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      Real.rpow delta (c - inputEta) ≤ 1 / 4
  target :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      Real.rpow delta (1 - c) ≤ 39 / 80
  coreScale :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      Real.rpow delta (1 - c) ≤ coreDelta₀
  prune :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      2 * Real.rpow delta (pruneEta - inputEta) ≤ 1
  density :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ENNReal.ofReal 12000000 *
          Kakeya.realRpowENN delta
            ((1 - c) * coreEta - pruneEta) ≤
        1
  katzTao :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ENNReal.ofReal 100000000 *
          Kakeya.realRpowENN delta
            ((1 - c) * (ktEta - thinningEta)) ≤
        1
  net :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      Real.rpow (1 / delta) 200 *
          Real.exp (-(11 - Real.exp 1) *
            Real.rpow delta
              (-((1 - c) * thinningEta))) <
        1 / 16
  count :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ((3 - Real.exp 1) / 48000000) *
          Real.rpow delta
            (-(2 * (1 - c) - inputEta - pruneEta)) >
        Real.log 16
  cwa :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ENNReal.ofReal 576000000000000 *
          Kakeya.realRpowENN delta cwaDensityGap ≤
        1
  cardinality :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ENNReal.ofReal
          (2 * 97200000000000001 *
            12000000 ^ 2 * 48000000 : ℝ) *
          Kakeya.realRpowENN delta cardinalityGap ≤
        1
  source :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ENNReal.ofReal (1000000 * kappa)⁻¹ *
          Kakeya.realRpowENN delta sourceGap ≤
        1

theorem pure_wz2_direct_wolff_floor_thresholds
    {coreDelta₀ c inputEta pruneEta coreEta ktEta thinningEta
      cwaDensityGap cardinalityGap sourceGap kappa : ℝ}
    (hcoreDelta₀ : 0 < coreDelta₀)
    (hcoreDelta₀One : coreDelta₀ ≤ 1)
    (hrhoGap : 0 < c - inputEta)
    (hcGap : 0 < 1 - c)
    (hpruneGap : 0 < pruneEta - inputEta)
    (hdensityGap : 0 < (1 - c) * coreEta - pruneEta)
    (hktGap : 0 < (1 - c) * (ktEta - thinningEta))
    (hnetGap : 0 < (1 - c) * thinningEta)
    (hcountGap :
      -(2 * (1 - c) - inputEta - pruneEta) < 0)
    (hcwaDensityGap : 0 < cwaDensityGap)
    (hcardinalityGap : 0 < cardinalityGap)
    (hsourceGap : 0 < sourceGap)
    (hkappa : 0 < kappa) :
    Nonempty
      (PureWZ2DirectWolffFloorThresholds
        coreDelta₀ c inputEta pruneEta coreEta ktEta thinningEta
        cwaDensityGap cardinalityGap sourceGap kappa) := by
  rcases
      pure_wz2_exists_delta₀_rpow_le
        (threshold := 1 / 4)
        (s := c - inputEta)
        (by norm_num) hrhoGap with
    ⟨rhoDelta₀, hrhoDelta₀, _, hrhoSmall⟩
  rcases
      pure_wz2_exists_delta₀_rpow_le
        (threshold := 39 / 80)
        (s := 1 - c)
        (by norm_num) hcGap with
    ⟨targetDelta₀, htargetDelta₀, _, htargetSmall⟩
  rcases
      pure_wz2_exists_delta₀_rpow_le
        (threshold := coreDelta₀)
        (s := 1 - c)
        hcoreDelta₀ hcGap with
    ⟨coreScaleDelta₀, hcoreScaleDelta₀, _,
      hcoreScaleSmall⟩
  rcases
      Subunit.exists_delta₀_mul_pow_le_one
        2 (by norm_num) (pruneEta - inputEta) hpruneGap with
    ⟨pruneDelta₀, hpruneDelta₀, _, hpruneSmall⟩
  rcases
      pure_wz2_exists_delta₀_constant_rpow_le_one
        (constant := 12000000)
        (gap := (1 - c) * coreEta - pruneEta)
        (by norm_num) hdensityGap with
    ⟨densityDelta₀, hdensityDelta₀, _, hdensityAbsorb⟩
  rcases
      pure_wz2_exists_delta₀_constant_rpow_le_one
        (constant := 100000000)
        (gap := (1 - c) * (ktEta - thinningEta))
        (by norm_num) hktGap with
    ⟨ktDelta₀, hktDelta₀, _, hktAbsorb⟩
  rcases
      Subunit.union_bound_small_delta
        (A := 200)
        (c := 11 - Real.exp 1)
        (η' := (1 - c) * thinningEta)
        (by norm_num)
        (by linarith [Real.exp_one_lt_three])
        hnetGap with
    ⟨netDelta₀, hnetDelta₀, hnetFailure⟩
  rcases
      Subunit.rpow_negative_tends_to_inf
        (c := (3 - Real.exp 1) / 48000000)
        (e := -(2 * (1 - c) - inputEta - pruneEta))
        (by positivity [Real.exp_one_lt_three])
        hcountGap with
    ⟨countDelta₀, hcountDelta₀, hcountFailure⟩
  rcases
      pure_wz2_exists_delta₀_constant_rpow_le_one
        (constant := 576000000000000)
        (gap := cwaDensityGap)
        (by norm_num) hcwaDensityGap with
    ⟨cwaDelta₀, hcwaDelta₀, _, hcwaDensityAbsorb⟩
  rcases
      pure_wz2_exists_delta₀_constant_rpow_le_one
        (constant :=
          2 * 97200000000000001 *
            12000000 ^ 2 * 48000000)
        (gap := cardinalityGap)
        (by positivity) hcardinalityGap with
    ⟨cardinalityDelta₀, hcardinalityDelta₀, _,
      hcardinalityAbsorb⟩
  rcases
      pure_wz2_exists_delta₀_constant_rpow_le_one
        (constant := (1000000 * kappa)⁻¹)
        (gap := sourceGap)
        (by positivity) hsourceGap with
    ⟨sourceDelta₀, hsourceDelta₀, _, hsourceAbsorb⟩
  let delta₀ :=
    min coreDelta₀
      (min rhoDelta₀
        (min targetDelta₀
          (min coreScaleDelta₀
            (min pruneDelta₀
              (min densityDelta₀
                (min ktDelta₀
                  (min netDelta₀
                    (min countDelta₀
                      (min cwaDelta₀
                        (min cardinalityDelta₀ sourceDelta₀))))))))))
  have hdelta₀ : 0 < delta₀ := by
    dsimp [delta₀]
    positivity
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans hcoreDelta₀One
  refine ⟨⟨delta₀, hdelta₀, hdelta₀One, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  all_goals
    intro delta hdelta hdeltaBound
  · exact hdeltaBound.trans (by simp [delta₀])
  · exact hrhoSmall delta hdelta
      (hdeltaBound.trans (by simp [delta₀]))
  · exact htargetSmall delta hdelta
      (hdeltaBound.trans (by simp [delta₀]))
  · exact hcoreScaleSmall delta hdelta
      (hdeltaBound.trans (by simp [delta₀]))
  · exact hpruneSmall delta hdelta
      (hdeltaBound.trans (by simp [delta₀]))
  · exact hdensityAbsorb delta hdelta
      (hdeltaBound.trans (by simp [delta₀]))
  · exact hktAbsorb delta hdelta
      (hdeltaBound.trans (by simp [delta₀]))
  · exact hnetFailure delta hdelta
      (hdeltaBound.trans (by simp [delta₀]))
  · exact hcountFailure delta hdelta
      (hdeltaBound.trans (by simp [delta₀]))
  · exact hcwaDensityAbsorb delta hdelta
      (hdeltaBound.trans (by simp [delta₀]))
  · exact hcardinalityAbsorb delta hdelta
      (hdeltaBound.trans (by simp [delta₀]))
  · exact hsourceAbsorb delta hdelta
      (hdeltaBound.trans (by simp [delta₀]))

end Kakeya.Assouad

end
