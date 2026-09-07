import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63CommonSliceRescaled

/-!
# Proposition 6.3 M9: first-chart trace density cutoff

This family-free cutoff absorbs the fixed geometric constant in the density
estimate used after passing the first-chart source through the canonical
ordinary trace.  It is frozen before the runtime scale and tube family are
chosen.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- A pre-runtime cutoff for the first-chart ordinary-trace density. -/
structure Proposition63M9FirstChartTraceDensityCutoffData
    (sigma stickyLoss inputLoss chartLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  trace_density : ∀ {q : ℝ}, 0 < q → q ≤ delta₀ →
    Kakeya.realRpowENN q chartLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
        ((100 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN q
            ((1 + sigma / 2) * inputLoss) / 2) *
          (((400000000 : ENNReal)⁻¹ *
            Kakeya.realRpowENN q (sigma * stickyLoss)) / 2))

/-- Freeze the first-chart ordinary-trace density absorption before runtime. -/
theorem proposition63_m9_firstChart_trace_density_cutoff
    {sigma stickyLoss inputLoss chartLoss : ℝ}
    (_hsigma : 0 < sigma)
    (_hsigmaOne : sigma < 1)
    (_hinputLoss : 0 < inputLoss)
    (hgap :
      sigma * stickyLoss + (1 + sigma / 2) * inputLoss < chartLoss) :
    Nonempty (Proposition63M9FirstChartTraceDensityCutoffData
      sigma stickyLoss inputLoss chartLoss) := by
  let geometry : ENNReal := 55296 * Kakeya.deltaTubeVolume 1
  let target : ENNReal :=
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
      ((100 : ENNReal)⁻¹ * (1 / 2 : ENNReal) *
        ((400000000 : ENNReal)⁻¹ / 2))
  have targetZero : target ≠ 0 := by
    norm_num [target, ENNReal.ofReal_eq_zero]
  have targetTop : target ≠ ⊤ := by
    dsimp only [target]
    finiteness
  let fixed : ENNReal := target⁻¹ * geometry
  have fixedTop : fixed ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr targetZero)
      (by
        dsimp only [geometry]
        exact ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top)
  let sourcePower : ℝ :=
    (1 + sigma / 2) * inputLoss + sigma * stickyLoss
  let gap : ℝ := chartLoss - sourcePower
  have gapPos : 0 < gap := by
    dsimp only [gap, sourcePower]
    linarith
  rcases exists_delta_realRpowENN_bound fixed fixedTop gapPos with
    ⟨delta₀, delta₀Pos, delta₀One, bound⟩
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := delta₀Pos
    delta₀_le_one := delta₀One
    trace_density := ?_
  }⟩
  intro q hq hqCutoff
  have hsmall : fixed * Kakeya.realRpowENN q gap ≤ 1 := by
    calc
      fixed * Kakeya.realRpowENN q gap ≤
          Kakeya.realRpowENN q (-gap) *
            Kakeya.realRpowENN q gap := by
              gcongr
              exact bound q hq hqCutoff
      _ = 1 := by
        rw [← realRpowENN_add hq]
        simp [Kakeya.realRpowENN]
  have hgeometry :
      geometry * Kakeya.realRpowENN q gap ≤ target := by
    have hquotient :
        (geometry * Kakeya.realRpowENN q gap) / target ≤ 1 := by
      rw [ENNReal.div_eq_inv_mul]
      simpa [fixed, mul_comm, mul_left_comm, mul_assoc] using hsmall
    simpa using (ENNReal.div_le_iff targetZero targetTop).mp hquotient
  have qPower :
      Kakeya.realRpowENN q chartLoss =
        Kakeya.realRpowENN q sourcePower *
          Kakeya.realRpowENN q gap := by
    rw [← realRpowENN_add hq]
    congr 1
    dsimp only [gap]
    ring
  have sourcePowerSplit :
      Kakeya.realRpowENN q sourcePower =
        Kakeya.realRpowENN q ((1 + sigma / 2) * inputLoss) *
          Kakeya.realRpowENN q (sigma * stickyLoss) := by
    rw [← realRpowENN_add hq]
  rw [qPower, sourcePowerSplit]
  dsimp only [geometry, target] at hgeometry ⊢
  calc
    (Kakeya.realRpowENN q ((1 + sigma / 2) * inputLoss) *
          Kakeya.realRpowENN q (sigma * stickyLoss)) *
          Kakeya.realRpowENN q gap *
          (55296 * Kakeya.deltaTubeVolume 1) =
        (Kakeya.realRpowENN q ((1 + sigma / 2) * inputLoss) *
          Kakeya.realRpowENN q (sigma * stickyLoss)) *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN q gap) := by ring
    _ ≤ (Kakeya.realRpowENN q ((1 + sigma / 2) * inputLoss) *
          Kakeya.realRpowENN q (sigma * stickyLoss)) *
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ((100 : ENNReal)⁻¹ * (1 / 2 : ENNReal) *
            ((400000000 : ENNReal)⁻¹ / 2))) :=
      by gcongr
    _ = ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
        ((100 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN q ((1 + sigma / 2) * inputLoss) / 2) *
          (((400000000 : ENNReal)⁻¹ *
            Kakeya.realRpowENN q (sigma * stickyLoss)) / 2)) := by
      simp only [div_eq_mul_inv]
      ring

end Kakeya.Assouad.PureWZ2

end
