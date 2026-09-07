import MyLeanRepo.Kakeya.Assouad.PropStickyPaperActiveCellLogBound
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Family-free logarithmic cost for rho-height uniformization
-/

noncomputable section

namespace Kakeya.Assouad

theorem commonBin_rhoHeight_logarithmicCost_le
    {rho : ℝ}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily rho}
    (shading : WZ1PaperTubeShading family)
    (cellCount : ℕ)
    (hcard :
      cellCount ≤ (wz1PaperActiveCells shading hrho).card) :
    (Nat.log 2 cellCount + 1 : ℝ) ≤
      (5 / Real.log 2) * Real.log (1 / rho) +
        (5 * Real.log 163 / Real.log 2 + 2) := by
  have hlogNat :
      Nat.log 2 cellCount + 1 ≤
        Nat.log 2 (wz1PaperActiveCells shading hrho).card + 1 :=
    Nat.add_le_add_right (Nat.log_mono_right hcard) 1
  have hlogReal :
      (Nat.log 2 cellCount + 1 : ℝ) ≤
        (Nat.log 2 (wz1PaperActiveCells shading hrho).card + 1 : ℝ) := by
    exact_mod_cast hlogNat
  exact hlogReal.trans
    (wz2_paper_active_cell_log_bound hrho hrhoOne shading)

theorem commonBin_rhoHeight_logarithmicCostENN_le
    {rho : ℝ}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily rho}
    (shading : WZ1PaperTubeShading family)
    (cellCount : ℕ)
    (hcard :
      cellCount ≤ (wz1PaperActiveCells shading hrho).card) :
    ((Nat.log 2 cellCount + 1 : ℕ) : ENNReal) ≤
      ENNReal.ofReal
        ((5 / Real.log 2) * Real.log (1 / rho) +
          (5 * Real.log 163 / Real.log 2 + 2)) := by
  have h := ENNReal.ofReal_le_ofReal
    (commonBin_rhoHeight_logarithmicCost_le
      hrho hrhoOne shading cellCount hcard)
  have hleft :
      ENNReal.ofReal ((Nat.log 2 cellCount : ℝ) + 1) =
        (Nat.log 2 cellCount : ENNReal) + 1 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rw [hleft] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The rho-height dyadic cost is bounded by the canonical physical
logarithmic envelope.  This form is convenient for combining it with the
existing family-free one-window height-cost schedule. -/
theorem commonBin_rhoHeight_logarithmicCostBoundaryENN_le
    {rho : ℝ}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily rho}
    (shading : WZ1PaperTubeShading family)
    (cellCount : ℕ)
    (hcard :
      cellCount ≤ (wz1PaperActiveCells shading hrho).card) :
    ((Nat.log 2 cellCount + 1 : ℕ) : ENNReal) ≤
      ENNReal.ofReal
        (wz2PaperBoundaryLogCoefficient *
          (1 + Real.log rho⁻¹)) := by
  have hlog :
      Nat.log 2 cellCount + 1 ≤
        Nat.log 2 (wz1PaperActiveCells shading hrho).card + 1 :=
    Nat.add_le_add_right (Nat.log_mono_right hcard) 1
  have hlogENN :
      ((Nat.log 2 cellCount + 1 : ℕ) : ENNReal) ≤
        ((Nat.log 2 (wz1PaperActiveCells shading hrho).card + 1 : ℕ) :
          ENNReal) := by
    exact_mod_cast hlog
  exact hlogENN.trans
    (wz2_paper_active_cell_log_bound_ennreal hrho hrhoOne shading)

/-- A coarse numerical bound on the canonical logarithmic coefficient. -/
theorem wz2PaperBoundaryLogCoefficient_le_fortyTwo :
    wz2PaperBoundaryLogCoefficient ≤ 42 := by
  have hlogTwo : (1 / 2 : ℝ) < Real.log 2 := by
    have hexp : Real.exp (1 / 2 : ℝ) < 2 := by
      have hexpOne : Real.exp 1 < 3 := Real.exp_one_lt_three
      have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
      have hsq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
        rw [sq, ← Real.exp_add]
        norm_num
      nlinarith
    have hmono := Real.log_lt_log (by positivity) hexp
    simpa using hmono
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog163 : Real.log (163 : ℝ) < 8 * Real.log 2 := by
    have hmono : Real.log (163 : ℝ) < Real.log 256 :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow] at hmono
    simpa using hmono
  have hratio : Real.log 163 / Real.log 2 < 8 := by
    rw [div_lt_iff₀ hlogTwoPos]
    exact hlog163
  have hfirst : 5 * Real.log 163 / Real.log 2 + 2 ≤ 42 := by
    have : 5 * (Real.log 163 / Real.log 2) + 2 < 42 := by
      nlinarith
    simpa [mul_div_assoc] using this.le
  have hsecond : 5 / Real.log 2 ≤ 42 := by
    rw [div_le_iff₀ hlogTwoPos]
    nlinarith
  exact max_le hfirst hsecond

end Kakeya.Assouad

end
