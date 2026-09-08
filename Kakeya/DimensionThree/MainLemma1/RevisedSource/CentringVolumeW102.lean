module

public import Kakeya.Tube.CylinderApprox
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

universe uE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem volume_cylinder_three_w102 (hdim : Module.finrank Real E = 3)
    {v : E} (hv : ‖v‖ = 1) (p : E) (a b r : Real) :
    volume (cylinder p v a b r) =
      ENNReal.ofReal (b - a) * (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) := by
  have hvne : v ≠ 0 := by intro h; simpa [h] using hv
  have hspan := finrank_span_singleton (K := Real) hvne
  have hsum := Submodule.finrank_add_finrank_orthogonal (Real ∙ v)
  have hperp : Module.finrank Real ((Real ∙ v)ᗮ : Submodule Real E) = 2 := by omega
  letI : Nontrivial ((Real ∙ v)ᗮ : Submodule Real E) :=
    Module.nontrivial_of_finrank_pos (R := Real) (by rw [hperp]; decide)
  rw [volume_cylinder hv, InnerProductSpace.volume_closedBall_of_dim_even
    (k := 1) (by simpa using hperp)]
  simp only [hperp, pow_one, Nat.factorial_one, Nat.cast_one, div_one]

theorem half_radius_carrier_volume_w102 (hdim : Module.finrank Real E = 3)
    {delta : NNReal} (hdsmall : delta <= 1 / 200)
    (T : Tube delta E) (W : Tube (delta / 2) E) :
    volume W.carrier <= (384 : ENNReal) * (1 / 512 : ENNReal) * volume T.carrier := by
  have hlo := measure_mono (μ := volume) (T.cylinder_subset_carrier_self
    (a := -(1 / 2 : Real)) (b := 1 / 2) (r := delta) le_rfl le_rfl le_rfl)
  rw [volume_cylinder_three_w102 hdim T.norm_direction] at hlo
  norm_num only [sub_neg_eq_add, add_halves, ENNReal.ofReal_one, one_mul] at hlo
  have hhi := measure_mono (μ := volume) (W.carrier_subset_cylinder_self (by positivity))
  rw [volume_cylinder_three_w102 hdim W.norm_direction] at hhi
  have hdR : (delta : Real) <= 1 / 200 := by exact_mod_cast hdsmall
  have hlen : ENNReal.ofReal
      ((1 / 2 : Real) + ((delta / 2 : NNReal) : Real) -
        (-(1 / 2 : Real) - ((delta / 2 : NNReal) : Real))) <= 3 := by
    rw [← ENNReal.ofReal_ofNat]
    apply ENNReal.ofReal_le_ofReal
    simp only [NNReal.coe_div, NNReal.coe_ofNat]
    linarith only [hdR]
  have hrad : ENNReal.ofReal (((delta / 2 : NNReal) : Real)) =
      (delta : ENNReal) / 2 := by
    rw [NNReal.coe_div, ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  rw [hrad] at hhi
  calc
    volume W.carrier <=
        3 * (((delta : ENNReal) / 2) ^ 2 * ENNReal.ofReal Real.pi) :=
      hhi.trans (mul_le_mul_right' hlen _)
    _ = (384 : ENNReal) * (1 / 512 : ENNReal) *
        ((delta : ENNReal) ^ 2 * ENNReal.ofReal Real.pi) := by
      rw [ENNReal.div_eq_inv_mul, mul_pow]
      have hc : (3 : ENNReal) * (2⁻¹) ^ 2 = 384 * (1 / 512) := by
        have h := congrArg ((↑) : NNReal -> ENNReal)
          (show (3 : NNReal) * (2⁻¹) ^ 2 = 384 * (1 / 512) by norm_num)
        simpa only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_inv_two,
          ENNReal.coe_div (by norm_num : (512 : NNReal) ≠ 0),
          ENNReal.coe_ofNat, ENNReal.coe_one] using h
      calc
        _ = (3 * (2⁻¹) ^ 2) * ((delta : ENNReal) ^ 2 * ENNReal.ofReal Real.pi) := by ring
        _ = _ := by rw [hc]
    _ <= _ := by simpa using mul_le_mul_left' hlo ((384 : ENNReal) * (1 / 512))

end
end Kakeya.ml1Boot.TrialRestartW94
