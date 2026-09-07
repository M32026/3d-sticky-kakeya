import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalAnalyticSchedule

/-!
# Uniform absorption of bounded-grid logarithmic costs

This numerical lemma factors the common core used by the source-horizontal
and exact-terminal pipelines.  The geometry supplies only two logarithmic
cardinality bounds; every remaining step is scale arithmetic.
-/

noncomputable section

namespace Kakeya.Assouad

theorem pureWZ2_boundedGrid_logCost_schedule
    {extraLoss : ℝ} (hextraLoss : 0 < extraLoss) :
    ∃ scale₀ : ℝ, 0 < scale₀ ∧ scale₀ ≤ 1 ∧
      ∀ scale : ℝ, 0 < scale → scale ≤ scale₀ →
        ∀ bins rawLog cost : ℕ,
          (bins : ℝ) ≤
              23 * (Real.log (1 / scale) + 1) →
          (rawLog : ℝ) ≤
              20 * (Real.log (1 / scale) + 1) →
          cost ≤ 2 * bins * rawLog →
            (cost : ℝ) ≤ Real.rpow scale (-extraLoss) := by
  rcases log_poly_decay_general 2000 (extraLoss / 2) (by norm_num)
      (by positivity) with
    ⟨constantScale₀, hconstantScale₀, hconstantScale₀One, hgraphLog⟩
  rcases log_poly_decay_general 1 (extraLoss / 4) (by norm_num)
      (by positivity) with
    ⟨logScale₀, hlogScale₀, hlogScale₀One, hlogPower⟩
  let scale₀ := min constantScale₀ logScale₀
  refine ⟨scale₀, lt_min hconstantScale₀ hlogScale₀,
    (min_le_left _ _).trans hconstantScale₀One, ?_⟩
  intro scale hscale hscaleSmall bins rawLog cost hbins hraw hcost
  have hscaleOne : scale ≤ 1 :=
    hscaleSmall.trans ((min_le_left _ _).trans hconstantScale₀One)
  let L : ℝ := Real.log (1 / scale) + 1
  have hLNonneg : 0 ≤ L := by
    dsimp only [L]
    have hlogNonneg : 0 ≤ Real.log (1 / scale) := by
      apply Real.log_nonneg
      exact one_le_one_div hscale hscaleOne
    linarith
  have hcostReal : (cost : ℝ) ≤ 920 * L ^ 2 := by
    have hcast : (cost : ℝ) ≤ (2 * bins * rawLog : ℕ) := by
      exact_mod_cast hcost
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcast
    calc
      (cost : ℝ) ≤ 2 * (bins : ℝ) * (rawLog : ℝ) := hcast
      _ ≤ 2 * (23 * L) * (20 * L) := by gcongr
      _ = 920 * L ^ 2 := by ring
  have hLsmall : L ≤ Real.rpow scale (-(extraLoss / 4)) := by
    have h := hlogPower scale hscale
      (hscaleSmall.trans (min_le_right _ _))
    simpa [L, one_div, Real.rpow_neg hscale.le] using h
  have hcostLinear :
      (cost : ℝ) ≤ 920 * Real.rpow scale (-(extraLoss / 2)) := by
    calc
      (cost : ℝ) ≤ 920 * L ^ 2 := hcostReal
      _ ≤ 920 * (Real.rpow scale (-(extraLoss / 4))) ^ 2 := by gcongr
      _ = 920 * Real.rpow scale (-(extraLoss / 2)) := by
        rw [pow_two]
        congr 1
        calc
          Real.rpow scale (-(extraLoss / 4)) *
              Real.rpow scale (-(extraLoss / 4)) =
            Real.rpow scale
              (-(extraLoss / 4) + -(extraLoss / 4)) :=
            (Real.rpow_add hscale _ _).symm
          _ = Real.rpow scale (-(extraLoss / 2)) := by
            congr 1
            ring
  have habsorb := hgraphLog scale hscale
    (hscaleSmall.trans (min_le_left _ _))
  have hconstant : 920 ≤ Real.rpow scale (-(extraLoss / 2)) := by
    have hLone : 1 ≤ L := by
      dsimp only [L]
      have hlogNonneg : 0 ≤ Real.log (1 / scale) := by
        apply Real.log_nonneg
        exact one_le_one_div hscale hscaleOne
      linarith
    have h2000 : 2000 ≤ 2000 * L := by nlinarith
    have hpower : 2000 * L ≤ Real.rpow scale (-(extraLoss / 2)) := by
      simpa [L, one_div, Real.rpow_neg hscale.le] using habsorb
    exact (by norm_num : (920 : ℝ) ≤ 2000) |>.trans (h2000.trans hpower)
  calc
    (cost : ℝ) ≤ 920 * Real.rpow scale (-(extraLoss / 2)) :=
      hcostLinear
    _ ≤ Real.rpow scale (-(extraLoss / 2)) *
        Real.rpow scale (-(extraLoss / 2)) := by gcongr
    _ = Real.rpow scale (-extraLoss) := by
      calc
        Real.rpow scale (-(extraLoss / 2)) *
            Real.rpow scale (-(extraLoss / 2)) =
          Real.rpow scale
            (-(extraLoss / 2) + -(extraLoss / 2)) :=
          (Real.rpow_add hscale _ _).symm
        _ = Real.rpow scale (-extraLoss) := by
          congr 1
          ring

end Kakeya.Assouad

end
