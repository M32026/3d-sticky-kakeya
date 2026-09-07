import MyLeanRepo.Kakeya.Assouad.WZ1.RpowArithmeticHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointRawBudgetAssembly

/-!
# Power arithmetic for wide endpoint source budgets
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- The ambient-to-active inverse retention is exactly
`4096 * delta^(-eta)`. -/
lemma wideCoarseEndpoint_activeFraction_inv
    {delta eta : ℝ} (hdelta : 0 < delta) :
    (wideCoarseEndpointActiveFraction delta eta)⁻¹ =
      (4096 : ENNReal) *
        Kakeya.realRpowENN delta (-eta) := by
  have hrpowPos :
      0 < Kakeya.realRpowENN delta eta := by
    simp only [Kakeya.realRpowENN, ENNReal.ofReal_pos]
    exact Real.rpow_pos_of_pos hdelta _
  have hactivePos :
      0 < wideCoarseEndpointActiveFraction delta eta := by
    dsimp only [wideCoarseEndpointActiveFraction]
    exact
      ENNReal.div_pos
        (mul_ne_zero (by norm_num) hrpowPos.ne')
        (by norm_num)
  have hleftTop :
      (wideCoarseEndpointActiveFraction delta eta)⁻¹ ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    exact hactivePos.ne'
  have hrightTop :
      (4096 : ENNReal) *
          Kakeya.realRpowENN delta (-eta) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp
    · simp [Kakeya.realRpowENN]
  apply
    (ENNReal.toReal_eq_toReal_iff'
      hleftTop hrightTop).mp
  have hrpowPositive :
      0 < Real.rpow delta eta :=
    Real.rpow_pos_of_pos hdelta _
  have hrpowNegative :
      Real.rpow delta (-eta) =
        (Real.rpow delta eta)⁻¹ :=
    Real.rpow_neg hdelta.le eta
  have htoReal (exponent : ℝ) :
      (Kakeya.realRpowENN delta exponent).toReal =
        Real.rpow delta exponent := by
    simp only [Kakeya.realRpowENN]
    exact ENNReal.toReal_ofReal
      (Real.rpow_nonneg hdelta.le _)
  rw [ENNReal.toReal_inv, ENNReal.toReal_mul,
    wideCoarseEndpointActiveFraction,
    ENNReal.toReal_div, ENNReal.toReal_mul,
    htoReal eta, htoReal (-eta), hrpowNegative]
  norm_num
  field_simp [hrpowPositive.ne']
  norm_num

/-- The active-to-selected inverse retention is a negative coarse-scale
power. -/
lemma wideCoarseEndpoint_rescaleFraction_inv
    {delta width exponent : ℝ}
    (hdelta : 0 < delta) (hwidth : 0 < width) :
    (wideCoarseEndpointRescaleFraction
        delta width exponent)⁻¹ =
      Kakeya.realRpowENN
        (delta / width) (-exponent) := by
  rw [wideCoarseEndpointRescaleFraction]
  exact rpow_enn_inv (div_pos hdelta hwidth)

/-- The supplied raw width cancels the common-strip width at the cost of the
explicit `delta^(-stripEpsilon * zeta)` loss. -/
lemma wideCoarseEndpoint_rawWidth_cancel
    {delta width rawWidth stripEpsilon zeta : ℝ}
    (hdelta : 0 < delta)
    (hwidth : 0 < width)
    (hrawWidth : 0 < rawWidth)
    (hzeta : 0 < zeta)
    (hwidthRaw :
      width ≤ Real.rpow delta (-stripEpsilon) * rawWidth) :
    Kakeya.realRpowENN rawWidth (-zeta) *
        Kakeya.realRpowENN width zeta ≤
      Kakeya.realRpowENN delta (-stripEpsilon * zeta) := by
  have hreal :
      Real.rpow rawWidth (-zeta) *
          Real.rpow width zeta ≤
        Real.rpow delta (-stripEpsilon * zeta) := by
    have hwidthPower :
        Real.rpow width zeta ≤
          Real.rpow
            (Real.rpow delta (-stripEpsilon) * rawWidth)
            zeta :=
      Real.rpow_le_rpow hwidth.le hwidthRaw hzeta.le
    calc
      Real.rpow rawWidth (-zeta) *
            Real.rpow width zeta
          ≤
        Real.rpow rawWidth (-zeta) *
          Real.rpow
            (Real.rpow delta (-stripEpsilon) * rawWidth)
            zeta := by
              exact mul_le_mul_of_nonneg_left
                hwidthPower
                (Real.rpow_nonneg hrawWidth.le _)
      _ =
        Real.rpow rawWidth (-zeta) *
          (Real.rpow
              (Real.rpow delta (-stripEpsilon)) zeta *
            Real.rpow rawWidth zeta) := by
              have hmul :=
                Real.mul_rpow
                  (x := Real.rpow delta (-stripEpsilon))
                  (y := rawWidth) (z := zeta)
                  (Real.rpow_nonneg hdelta.le _)
                  hrawWidth.le
              exact
                congrArg
                  (fun value : ℝ =>
                    Real.rpow rawWidth (-zeta) * value)
                  hmul
      _ =
        Real.rpow
          (Real.rpow delta (-stripEpsilon)) zeta := by
              have hcancel :
                  Real.rpow rawWidth (-zeta) *
                      Real.rpow rawWidth zeta = 1 := by
                have hnegative :
                    Real.rpow rawWidth (-zeta) =
                      (Real.rpow rawWidth zeta)⁻¹ :=
                  Real.rpow_neg hrawWidth.le zeta
                rw [hnegative]
                exact inv_mul_cancel₀
                  (Real.rpow_pos_of_pos hrawWidth _).ne'
              calc
                Real.rpow rawWidth (-zeta) *
                    (Real.rpow
                        (Real.rpow delta (-stripEpsilon)) zeta *
                      Real.rpow rawWidth zeta) =
                  Real.rpow
                      (Real.rpow delta (-stripEpsilon)) zeta *
                    (Real.rpow rawWidth (-zeta) *
                      Real.rpow rawWidth zeta) := by ring
                _ =
                  Real.rpow
                    (Real.rpow delta (-stripEpsilon)) zeta := by
                      rw [hcancel, mul_one]
      _ =
        Real.rpow delta (-stripEpsilon * zeta) := by
              exact
                (Real.rpow_mul
                  hdelta.le (-stripEpsilon) zeta).symm
  simp only [Kakeya.realRpowENN]
  have hofReal :
      ENNReal.ofReal
          (Real.rpow rawWidth (-zeta) *
            Real.rpow width zeta) =
        ENNReal.ofReal (Real.rpow rawWidth (-zeta)) *
          ENNReal.ofReal (Real.rpow width zeta) :=
    ENNReal.ofReal_mul
      (Real.rpow_nonneg hrawWidth.le _)
  rw [← hofReal]
  exact ENNReal.ofReal_mono hreal

/-- Convert a fixed negative `delta` power to the corresponding negative
coarse-scale power using `tau < delta^(epsilon/10)`. -/
lemma wideCoarseEndpoint_delta_loss_to_tau
    {delta tau epsilon loss : ℝ}
    (hdelta : 0 < delta)
    (htau : 0 < tau)
    (hepsilon : 0 < epsilon)
    (hloss : 0 ≤ loss)
    (htauPower :
      tau ≤ Real.rpow delta (epsilon / 10)) :
    Kakeya.realRpowENN delta (-loss) ≤
      Kakeya.realRpowENN tau (-(10 * loss / epsilon)) := by
  have hexponent :
      -(10 * loss / epsilon) ≤ 0 := by
    have hquotient : 0 ≤ 10 * loss / epsilon := by
      positivity
    linarith
  have hbase :
      Real.rpow
          (Real.rpow delta (epsilon / 10))
          (-(10 * loss / epsilon)) ≤
        Real.rpow tau (-(10 * loss / epsilon)) :=
    Real.rpow_le_rpow_of_nonpos
      htau htauPower hexponent
  have hrewrite :
      Real.rpow
          (Real.rpow delta (epsilon / 10))
          (-(10 * loss / epsilon)) =
        Real.rpow delta (-loss) := by
    calc
      Real.rpow
          (Real.rpow delta (epsilon / 10))
          (-(10 * loss / epsilon)) =
        Real.rpow delta
          ((epsilon / 10) * (-(10 * loss / epsilon))) := by
            exact
              (Real.rpow_mul
                hdelta.le
                (epsilon / 10)
                (-(10 * loss / epsilon))).symm
      _ = Real.rpow delta (-loss) := by
            congr 1
            field_simp [hepsilon.ne']
  rw [hrewrite] at hbase
  exact ENNReal.ofReal_mono hbase

/-- Split the target line-nonconcentration coefficient into the coarse-scale
power and radius power. -/
lemma wideCoarseEndpoint_target_power_identity
    {tau radius lambda zeta : ℝ}
    (htau : 0 < tau) (hradius : 0 < radius) :
    Kakeya.realRpowENN
        (Real.rpow tau (-lambda) * radius) zeta =
      Kakeya.realRpowENN tau (-lambda * zeta) *
        Kakeya.realRpowENN radius zeta := by
  have hbase : 0 < Real.rpow tau (-lambda) :=
    Real.rpow_pos_of_pos htau _
  rw [realRpowENN_mul hbase hradius]
  simp only [Kakeya.realRpowENN]
  have hpower :
      Real.rpow (Real.rpow tau (-lambda)) zeta =
        Real.rpow tau (-lambda * zeta) :=
    (Real.rpow_mul htau.le (-lambda) zeta).symm
  rw [hpower]

end Kakeya.Assouad
