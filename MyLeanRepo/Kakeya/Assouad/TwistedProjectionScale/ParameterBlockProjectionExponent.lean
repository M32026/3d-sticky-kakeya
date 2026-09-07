import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockProjectionUniformityStatements

/-!
# Exponent budget for paper Lemma 7.12

The local cinematic lower bound contains the direct spacing loss
`60 * epsilon²` and the global-scale losses
`12 * eta + 3 * pyzLoss`.  The selected-scale inequality converts the latter
to the normalized fine-scale exponent obtained by dividing by `epsilon²`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Effective normalized exponent in the corrected Lemma 7.12 lower bound. -/
def parameterBlockProjectionEffectiveExponent
    (epsilon eta : ℝ) : ℝ :=
  60 * epsilon ^ 2 +
    (12 * eta +
      3 * parameterBlockProjectionPYZLoss epsilon) /
        epsilon ^ 2

/--
The effective local exponent is strictly below the requested one-scale
exponent.
-/
lemma parameterBlockProjection_effectiveExponent_lt
    {epsilon eta : ℝ}
    (hepsilon : 0 < epsilon)
    (hepsilon_small : epsilon < 1 / 100)
    (heta : 0 < eta)
    (heta_small : 1000 * eta < epsilon ^ 3) :
    parameterBlockProjectionEffectiveExponent epsilon eta <
      epsilon := by
  have hepsilon_sq : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  have heta_scaled :
      12 * eta / epsilon ^ 2 <
        12 * epsilon / 1000 := by
    apply (div_lt_iff₀ hepsilon_sq).2
    nlinarith
  have hpyz :
      3 * parameterBlockProjectionPYZLoss epsilon /
          epsilon ^ 2 =
        3 * epsilon / 100 := by
    unfold parameterBlockProjectionPYZLoss
    field_simp [hepsilon.ne']
  have hquadratic :
      60 * epsilon ^ 2 <
        60 * epsilon / 100 := by
    nlinarith
  unfold parameterBlockProjectionEffectiveExponent
  rw [add_div, hpyz]
  nlinarith

/--
The selected block scale converts every positive global `delta`-loss into a
normalized `(delta / blockScale)`-loss divided by `epsilon²`.
-/
lemma parameterBlockProjection_ratio_loss_le_delta_loss
    {delta blockScale epsilon loss : ℝ}
    (hdelta : 0 < delta)
    (hblockScale : 0 < blockScale)
    (hepsilon : 0 < epsilon)
    (hloss : 0 ≤ loss)
    (hseparated :
      Real.rpow delta (1 - epsilon ^ 2) <
        blockScale / 10) :
    Kakeya.realRpowENN
        (delta / blockScale) (loss / epsilon ^ 2) ≤
      Kakeya.realRpowENN delta loss := by
  have hepsilon_sq : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  have hratio : 0 < delta / blockScale := by positivity
  have hdelta_factor :
      delta / blockScale <
        Real.rpow delta (epsilon ^ 2) := by
    have hten :
        10 * Real.rpow delta (1 - epsilon ^ 2) <
          blockScale := by
      linarith
    have hmul :
        delta =
          Real.rpow delta (1 - epsilon ^ 2) *
            Real.rpow delta (epsilon ^ 2) := by
      calc
        delta = Real.rpow delta 1 := (Real.rpow_one delta).symm
        _ = Real.rpow delta
            ((1 - epsilon ^ 2) + epsilon ^ 2) := by
          congr 1
          ring
        _ =
            Real.rpow delta (1 - epsilon ^ 2) *
              Real.rpow delta (epsilon ^ 2) :=
          Real.rpow_add hdelta _ _
    calc
      delta / blockScale <
          delta /
            (10 * Real.rpow delta
              (1 - epsilon ^ 2)) := by
        apply div_lt_div_of_pos_left hdelta
        · exact mul_pos (by norm_num)
            (Real.rpow_pos_of_pos hdelta _)
        · exact hten
      _ =
          Real.rpow delta (epsilon ^ 2) / 10 := by
        have hfirst :
            0 < Real.rpow delta (1 - epsilon ^ 2) :=
          Real.rpow_pos_of_pos hdelta _
        apply
          (div_eq_iff
            (show
              10 * Real.rpow delta
                (1 - epsilon ^ 2) ≠ 0 by
              positivity)).2
        calc
          delta =
              Real.rpow delta (1 - epsilon ^ 2) *
                Real.rpow delta (epsilon ^ 2) := hmul
          _ =
              (Real.rpow delta (epsilon ^ 2) / 10) *
                (10 *
                  Real.rpow delta
                    (1 - epsilon ^ 2)) := by
            field_simp [hfirst.ne']
      _ < Real.rpow delta (epsilon ^ 2) := by
        have hpositive :
            0 < Real.rpow delta (epsilon ^ 2) :=
          Real.rpow_pos_of_pos hdelta _
        linarith
  have hloss_div : 0 ≤ loss / epsilon ^ 2 := by positivity
  have hpowered :
      Real.rpow (delta / blockScale)
          (loss / epsilon ^ 2) ≤
        Real.rpow (Real.rpow delta (epsilon ^ 2))
          (loss / epsilon ^ 2) :=
    Real.rpow_le_rpow hratio.le hdelta_factor.le hloss_div
  have hcollapse :
      Real.rpow (Real.rpow delta (epsilon ^ 2))
          (loss / epsilon ^ 2) =
        Real.rpow delta loss := by
    calc
      Real.rpow (Real.rpow delta (epsilon ^ 2))
          (loss / epsilon ^ 2) =
          Real.rpow delta
            (epsilon ^ 2 * (loss / epsilon ^ 2)) := by
        exact
          (Real.rpow_mul hdelta.le
            (epsilon ^ 2) (loss / epsilon ^ 2)).symm
      _ = Real.rpow delta loss := by
        congr 1
        field_simp [hepsilon.ne']
  simp only [Kakeya.realRpowENN]
  exact ENNReal.ofReal_mono (hpowered.trans_eq hcollapse)

end Kakeya.Assouad
