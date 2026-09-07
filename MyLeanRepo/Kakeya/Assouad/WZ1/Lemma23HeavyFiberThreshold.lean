import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalProjectionHeavyFiberInSource

/-!
# Heavy-fiber volume threshold for WZ1 Lemma 23

The local AD cover has size

`C * (sqrt rho / rho)^(1 - sigma)`.

If the actual anchor ball has volume at least
`rho^(3/2 + sigma/2 + eta)` and `C ≤ rho^(-eta)`, then the heavy fiber
selected by `Lemma23LocalProjectionHeavyFiber` has volume at least
`rho^(2 + 2*eta)`.
-/

namespace Kakeya.Assouad

noncomputable section

open MeasureTheory

private lemma lemma23_realRpowENN_mul
    {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    Kakeya.realRpowENN x a * Kakeya.realRpowENN x b =
      Kakeya.realRpowENN x (a + b) := by
  simp only [Kakeya.realRpowENN]
  have hnonneg : 0 ≤ Real.rpow x a :=
    Real.rpow_nonneg hx.le _
  rw [← ENNReal.ofReal_mul hnonneg]
  congr 1
  exact (Real.rpow_add hx a b).symm

private lemma lemma23_sqrt_ratio_power
    {rho sigma : ℝ} (hrho : 0 < rho) :
    Kakeya.realRpowENN
        (Real.sqrt rho / rho) (1 - sigma) =
      Kakeya.realRpowENN rho (-(1 - sigma) / 2) := by
  simp only [Kakeya.realRpowENN]
  apply congrArg ENNReal.ofReal
  have hbase :
      Real.sqrt rho / rho =
        Real.rpow rho (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    calc
      Real.rpow rho (1 / 2 : ℝ) / rho =
          Real.rpow rho (1 / 2 : ℝ) /
            Real.rpow rho 1 := by
        simp
      _ =
          Real.rpow rho ((1 / 2 : ℝ) - 1) :=
        (Real.rpow_sub hrho _ _).symm
      _ = Real.rpow rho (-(1 / 2 : ℝ)) := by
        congr 1
        ring
  rw [hbase]
  calc
    Real.rpow (Real.rpow rho (-(1 / 2 : ℝ)))
          (1 - sigma) =
        Real.rpow rho
          (-(1 / 2 : ℝ) * (1 - sigma)) :=
      (Real.rpow_mul hrho.le _ _).symm
    _ = Real.rpow rho (-(1 - sigma) / 2) := by
      congr 1
      ring

/--
The exact power cancellation behind the almost-full local-grain threshold.
-/
lemma wz1_lemma23_heavy_fiber_power_threshold
    {rho sigma eta : ℝ}
    {C sourceMass grainMass : ENNReal}
    (hrho : 0 < rho)
    (hCOne : 1 ≤ C)
    (hCPower :
      C ≤ Kakeya.realRpowENN rho (-eta))
    (hsourceLower :
      Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + eta) ≤
        sourceMass)
    (hretention :
      sourceMass ≤
        (C * Kakeya.realRpowENN
          (Real.sqrt rho / rho) (1 - sigma)) *
            grainMass) :
    Kakeya.realRpowENN rho (2 + 2 * eta) ≤
      grainMass := by
  let factor : ENNReal :=
    C * Kakeya.realRpowENN
      (Real.sqrt rho / rho) (1 - sigma)
  have hratio :
      Kakeya.realRpowENN
          (Real.sqrt rho / rho) (1 - sigma) =
        Kakeya.realRpowENN rho
          (-(1 - sigma) / 2) :=
    lemma23_sqrt_ratio_power hrho
  have hfactorBound :
      factor ≤
        Kakeya.realRpowENN rho (-eta) *
          Kakeya.realRpowENN rho
            (-(1 - sigma) / 2) := by
    dsimp only [factor]
    rw [hratio]
    gcongr
  have hpower :
      (Kakeya.realRpowENN rho (-eta) *
          Kakeya.realRpowENN rho
            (-(1 - sigma) / 2)) *
          Kakeya.realRpowENN rho (2 + 2 * eta) =
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + eta) := by
    rw [lemma23_realRpowENN_mul hrho]
    rw [lemma23_realRpowENN_mul hrho]
    congr 1
    ring
  have hfactorTarget :
      factor *
          Kakeya.realRpowENN rho (2 + 2 * eta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + eta) := by
    calc
      factor *
            Kakeya.realRpowENN rho (2 + 2 * eta) ≤
          (Kakeya.realRpowENN rho (-eta) *
              Kakeya.realRpowENN rho
                (-(1 - sigma) / 2)) *
            Kakeya.realRpowENN rho (2 + 2 * eta) := by
        gcongr
      _ =
          Kakeya.realRpowENN rho
            (3 / 2 + sigma / 2 + eta) :=
        hpower
  have hfactorPos : factor ≠ 0 := by
    have hCPos : C ≠ 0 := by
      exact ne_of_gt (zero_lt_one.trans_le hCOne)
    have hratioPos :
        Kakeya.realRpowENN
            (Real.sqrt rho / rho) (1 - sigma) ≠ 0 := by
      simp [Kakeya.realRpowENN]
      exact Real.rpow_pos_of_pos (by positivity) _
    exact mul_ne_zero hCPos hratioPos
  have hfactorFinite : factor ≠ ⊤ := by
    have hCFinite : C ≠ ⊤ := by
      exact ne_top_of_le_ne_top
        (by simp [Kakeya.realRpowENN]) hCPower
    exact ENNReal.mul_ne_top hCFinite
      (by simp [Kakeya.realRpowENN])
  apply
    (ENNReal.mul_le_mul_iff_right
      hfactorPos hfactorFinite).mp
  calc
    factor *
          Kakeya.realRpowENN rho (2 + 2 * eta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + eta) :=
      hfactorTarget
    _ ≤ sourceMass := hsourceLower
    _ ≤ factor * grainMass := by
      simpa [factor] using hretention

/--
An actual heavy local-projection fiber is almost full once its actual anchor
ball has the paper's popular-cube volume lower bound.
-/
lemma WZ1Lemma23LocalProjectionHeavyFiber.grain_volume_of_source_lower
    {delta sigma rho eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {localGrains : WZ1LocalGrainData Y sigma C}
    {anchor : Point3}
    (fiber :
      WZ1Lemma23LocalProjectionHeavyFiber
        (rho := rho) Y C localGrains anchor)
    (hrho : 0 < rho)
    (hCOne : 1 ≤ C)
    (hCPower :
      C ≤ Kakeya.realRpowENN rho (-eta))
    (hsourceLower :
      Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + eta) ≤
        volume
          (Y.union ∩
            Metric.closedBall anchor (Real.sqrt rho))) :
    Kakeya.realRpowENN rho (2 + 2 * eta) ≤
      volume fiber.grain :=
  wz1_lemma23_heavy_fiber_power_threshold
    hrho hCOne hCPower hsourceLower fiber.mass_retention

/--
The same threshold applied to a heavy fiber inside an explicit actual coarse
source.
-/
lemma WZ1Lemma23LocalProjectionHeavyFiberInSource.grain_volume_of_source_lower
    {delta sigma rho eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {localGrains : WZ1LocalGrainData Y sigma C}
    {anchor : Point3}
    {source : Set Point3}
    (fiber :
      WZ1Lemma23LocalProjectionHeavyFiberInSource
        (rho := rho) Y C localGrains anchor source)
    (hrho : 0 < rho)
    (hCOne : 1 ≤ C)
    (hCPower :
      C ≤ Kakeya.realRpowENN rho (-eta))
    (hsourceLower :
      Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + eta) ≤
        volume source) :
    Kakeya.realRpowENN rho (2 + 2 * eta) ≤
      volume fiber.grain :=
  wz1_lemma23_heavy_fiber_power_threshold
    hrho hCOne hCPower hsourceLower fiber.mass_retention

end

end Kakeya.Assouad
