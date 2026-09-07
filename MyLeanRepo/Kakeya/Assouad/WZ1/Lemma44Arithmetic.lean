import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44ENNRealHelpers
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Arithmetic helper lemmas for WZ1 Lemma 44 triple assembly

Real-power and ENNReal coefficient identities, exponent bounds derived from
the scale-separation premises, and parameter range estimates.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Case 1 coefficient:
`delta^(-lambda) * (delta^(lambda+4*alpha))^1 = delta^(4*alpha)`.
-/
lemma case1_coeff {delta lambda alpha : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hlambda : 0 < lambda) (halpha : 0 < alpha) :
    Kakeya.realRpowENN delta (-lambda) *
      Kakeya.realRpowENN (Real.rpow delta (lambda + 4 * alpha)) 1 =
    Kakeya.realRpowENN delta (4 * alpha) := by
  have h1 : Kakeya.realRpowENN (Real.rpow delta (lambda + 4 * alpha)) 1 =
      Kakeya.realRpowENN delta (lambda + 4 * alpha) := by
    simp only [Kakeya.realRpowENN]
    have h2 : Real.rpow (Real.rpow delta (lambda + 4 * alpha)) 1 =
        Real.rpow delta (lambda + 4 * alpha) := by simp
    rw [h2]
  rw [h1]
  have h3 : Kakeya.realRpowENN delta (-lambda) * Kakeya.realRpowENN delta (lambda + 4 * alpha) =
      Kakeya.realRpowENN delta ((-lambda) + (lambda + 4 * alpha)) :=
    lemma44_realRpowENN_mul hdelta
  rw [h3]
  have h4 : (-lambda) + (lambda + 4 * alpha) = 4 * alpha := by ring
  rw [h4]

/--
Case 2 coefficient:
`(delta^(-lambda) * delta^(lambda+4*alpha/zeta))^zeta = delta^(4*alpha)`.
-/
lemma case2_coeff {delta lambda zeta alpha : ℝ} (hdelta : 0 < delta)
    (hlambda : 0 < lambda) (hzeta : 0 < zeta) (halpha : 0 < alpha) :
    Kakeya.realRpowENN
      (Real.rpow delta (-lambda) * Real.rpow delta (lambda + 4 * alpha / zeta)) zeta =
    Kakeya.realRpowENN delta (4 * alpha) := by
  have h_sum : Real.rpow delta (-lambda) * Real.rpow delta (lambda + 4 * alpha / zeta) =
      Real.rpow delta (4 * alpha / zeta) := by
    have h : Real.rpow delta ((-lambda) + (lambda + 4 * alpha / zeta)) =
        Real.rpow delta (-lambda) * Real.rpow delta (lambda + 4 * alpha / zeta) :=
      Real.rpow_add hdelta _ _
    have h5 : (-lambda) + (lambda + 4 * alpha / zeta) = 4 * alpha / zeta := by ring
    rw [h5] at h
    exact h.symm
  simp only [Kakeya.realRpowENN]
  rw [h_sum]
  have h_nonneg_base : 0 ≤ delta := hdelta.le
  have h_mul : Real.rpow (Real.rpow delta (4 * alpha / zeta)) zeta =
      Real.rpow delta ((4 * alpha / zeta) * zeta) := by
    have h := Real.rpow_mul (x := delta) h_nonneg_base (4 * alpha / zeta) zeta
    exact h.symm
  rw [h_mul]
  have h5 : (4 * alpha / zeta) * zeta = 4 * alpha := by
    field_simp [hzeta.ne'] <;> ring
  rw [h5]

/--
From the scale-separation premise, derive the total exponent bound:
`2*lambda + 4*alpha + 4*alpha/zeta < 1`.
-/
lemma exponent_bound {delta lambda zeta alpha scale : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hlambda : 0 < lambda) (hzeta : 0 < zeta) (halpha : 0 < alpha)
    (hscale_pos : 0 < scale) (hdelta_scale : delta ≤ scale)
    (hprem : 8 * (13 * scale) ≤ Real.rpow delta (lambda + 4 * alpha) *
        Real.rpow delta (lambda + 4 * alpha / zeta)) :
    2 * lambda + 4 * alpha + 4 * alpha / zeta < 1 := by
  set E : ℝ := 2 * lambda + 4 * alpha + 4 * alpha / zeta with hE_def
  have h_rpow_sum : Real.rpow delta (lambda + 4 * alpha) *
      Real.rpow delta (lambda + 4 * alpha / zeta) = Real.rpow delta E := by
    have h : Real.rpow delta ((lambda + 4 * alpha) + (lambda + 4 * alpha / zeta)) =
        Real.rpow delta (lambda + 4 * alpha) * Real.rpow delta (lambda + 4 * alpha / zeta) :=
      Real.rpow_add hdelta _ _
    have h_eq : (lambda + 4 * alpha) + (lambda + 4 * alpha / zeta) = E := by
      simp only [hE_def] <;> ring
    rw [h_eq] at h
    exact h.symm
  have h1 : 104 * delta ≤ Real.rpow delta E := by
    calc 104 * delta
      = 8 * (13 * delta) := by ring
    _ ≤ 8 * (13 * scale) := by gcongr
    _ ≤ Real.rpow delta (lambda + 4 * alpha) * Real.rpow delta (lambda + 4 * alpha / zeta) := hprem
    _ = Real.rpow delta E := h_rpow_sum
  by_contra h
  have h2 : E ≥ 1 := by linarith
  have h3 : Real.rpow delta E ≤ Real.rpow delta 1 := by
    exact Real.rpow_le_rpow_of_exponent_ge (hx0 := hdelta) (hx1 := by linarith) (hyz := by linarith)
  have h4 : Real.rpow delta 1 = delta := by simp
  rw [h4] at h3
  linarith

/--
Bounds on `D = delta^(lambda+4*alpha)`: `delta ≤ D ≤ 1`.
-/
lemma D_bounds {delta lambda zeta alpha scale : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hlambda : 0 < lambda) (hzeta : 0 < zeta) (halpha : 0 < alpha)
    (hscale_pos : 0 < scale) (hdelta_scale : delta ≤ scale)
    (hprem : 8 * (13 * scale) ≤ Real.rpow delta (lambda + 4 * alpha) *
        Real.rpow delta (lambda + 4 * alpha / zeta)) :
    delta ≤ Real.rpow delta (lambda + 4 * alpha) ∧
    Real.rpow delta (lambda + 4 * alpha) ≤ 1 := by
  set E : ℝ := 2 * lambda + 4 * alpha + 4 * alpha / zeta with hE_def
  have hE : E < 1 :=
    exponent_bound hdelta hdelta1 hlambda hzeta halpha hscale_pos hdelta_scale hprem
  set e : ℝ := lambda + 4 * alpha with he_def
  have h_pos_extra : 0 < lambda + 4 * alpha / zeta := by positivity
  have h1 : e < 1 := by
    have h11 : e + (lambda + 4 * alpha / zeta) = E := by
      simp only [he_def, hE_def] <;> ring
    have h12 : e < E := by linarith
    linarith [hE]
  have h2 : 0 < e := by positivity
  have h3 : Real.rpow delta 1 < Real.rpow delta e :=
    Real.rpow_lt_rpow_of_exponent_gt hdelta hdelta1 h1
  have h4 : Real.rpow delta e < Real.rpow delta 0 :=
    Real.rpow_lt_rpow_of_exponent_gt hdelta hdelta1 h2
  have h7 : delta < Real.rpow delta e := by
    have h5 : Real.rpow delta 1 = delta := by simp
    rw [h5] at h3
    exact h3
  have h8 : Real.rpow delta e < 1 := by
    have h6 : Real.rpow delta 0 = 1 := by simp
    rw [h6] at h4
    exact h4
  exact ⟨by linarith, by linarith⟩

/--
Bounds on `s = delta^(lambda+4*alpha/zeta)`: `delta ≤ s ≤ 1`.
-/
lemma s_bounds {delta lambda zeta alpha scale : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hlambda : 0 < lambda) (hzeta : 0 < zeta) (halpha : 0 < alpha)
    (hscale_pos : 0 < scale) (hdelta_scale : delta ≤ scale)
    (hprem : 8 * (13 * scale) ≤ Real.rpow delta (lambda + 4 * alpha) *
        Real.rpow delta (lambda + 4 * alpha / zeta)) :
    delta ≤ Real.rpow delta (lambda + 4 * alpha / zeta) ∧
    Real.rpow delta (lambda + 4 * alpha / zeta) ≤ 1 := by
  set E : ℝ := 2 * lambda + 4 * alpha + 4 * alpha / zeta with hE_def
  have hE : E < 1 :=
    exponent_bound hdelta hdelta1 hlambda hzeta halpha hscale_pos hdelta_scale hprem
  set e : ℝ := lambda + 4 * alpha / zeta with he_def
  have h_pos_extra : 0 < lambda + 4 * alpha := by positivity
  have h1 : e < 1 := by
    have h11 : e + (lambda + 4 * alpha) = E := by
      simp only [he_def, hE_def] <;> ring
    have h12 : e < E := by linarith
    linarith [hE]
  have h2 : 0 < e := by positivity
  have h3 : Real.rpow delta 1 < Real.rpow delta e :=
    Real.rpow_lt_rpow_of_exponent_gt hdelta hdelta1 h1
  have h4 : Real.rpow delta e < Real.rpow delta 0 :=
    Real.rpow_lt_rpow_of_exponent_gt hdelta hdelta1 h2
  have h7 : delta < Real.rpow delta e := by
    have h5 : Real.rpow delta 1 = delta := by simp
    rw [h5] at h3
    exact h3
  have h8 : Real.rpow delta e < 1 := by
    have h6 : Real.rpow delta 0 = 1 := by simp
    rw [h6] at h4
    exact h4
  exact ⟨by linarith, by linarith⟩

/--
The Frostman constant `C_F = delta^(-lambda)` satisfies `1 ≤ C_F` in `ENNReal`.
-/
lemma C_F_gt_one {delta lambda : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hlambda : 0 < lambda) :
    (1 : ENNReal) ≤ Kakeya.realRpowENN delta (-lambda) := by
  have h2 : -lambda < 0 := by linarith
  have h3 : Real.rpow delta 0 < Real.rpow delta (-lambda) :=
    Real.rpow_lt_rpow_of_exponent_gt hdelta hdelta1 h2
  have h4 : Real.rpow delta 0 = 1 := by simp
  rw [h4] at h3
  have h5 : (1 : ℝ) ≤ Real.rpow delta (-lambda) := by linarith
  simp only [Kakeya.realRpowENN]
  have h6 : (1 : ENNReal) ≤ ENNReal.ofReal (Real.rpow delta (-lambda)) := by
    have h7 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (Real.rpow delta (-lambda)) :=
      ENNReal.ofReal_le_ofReal h5
    have h8 : ENNReal.ofReal (1 : ℝ) = (1 : ENNReal) := by simp
    rw [h8] at h7
    exact h7
  exact h6

end Kakeya.Assouad
