import MyLeanRepo.Kakeya.Hairbrush.IntersectionSumBound.Preparations
import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import MyLeanRepo.Kakeya.Hairbrush.Basic

/-!
# Uniform intersection volume bound at a fixed angle scale

For two δ-tubes T, U whose acute angle is at least `angleScale`, the volume
of their intersection is at most `8π δ³ / angleScale`.

This follows from the exact angle bound `16δ³/sin θ` together with
`sin θ ≥ 2 angleScale / π` when `angleScale ≤ θ ≤ π/2`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

lemma uniform_intersection_volume_bound
    {δ angleScale : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 1000)
    (h_angleScale_pos : 0 < angleScale)
    (h_angleScale_le_one : angleScale ≤ 1)
    (T U : Kakeya.DeltaTube δ)
    (h_angle : angleScale ≤ hairbrushAcuteAngle T U) :
    volume (T.carrier ∩ U.carrier) ≤
    ENNReal.ofReal (8 * Real.pi * δ ^ 3 / angleScale) := by
  let θ := hairbrushAcuteAngle T U
  have hθ_pos : 0 < θ := by linarith [h_angle]
  have h_eff : Kakeya.Hairbrush.effectiveAngle T U = θ := by rfl
  have hθ_le_pi2 : θ ≤ Real.pi / 2 := by
    have h := Kakeya.Hairbrush.effectiveAngle_le_pi2 T U
    rw [h_eff] at h
    exact h
  have h_main1 : volume (T.carrier ∩ U.carrier) ≤
      ENNReal.ofReal (16 * δ ^ 3 / Real.sin θ) :=
    Kakeya.Hairbrush.intersection_volume_at_angle hδ hδ1 T U θ hθ_pos hθ_le_pi2 h_eff
  have h_angleScale_le_pi2 : angleScale ≤ Real.pi / 2 := by
    have h1 : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
    linarith
  have h_sin1 : Real.sin angleScale ≤ Real.sin θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) hθ_le_pi2 h_angle
  have h_sin2 : Real.sin angleScale ≥ 2 * angleScale / Real.pi :=
    Kakeya.Hairbrush.sin_lower_bound h_angleScale_pos.le h_angleScale_le_pi2
  have h_sinθ_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ_pos (by linarith [Real.pi_pos])
  have h_sin4 : Real.sin θ ≥ 2 * angleScale / Real.pi := by linarith
  have h_ineq : 16 * δ ^ 3 / Real.sin θ ≤ 8 * Real.pi * δ ^ 3 / angleScale := by
    have h5 : 0 < 2 * angleScale / Real.pi := by positivity
    calc
      16 * δ ^ 3 / Real.sin θ
        ≤ 16 * δ ^ 3 / (2 * angleScale / Real.pi) := by
          gcongr
      _ = 8 * Real.pi * δ ^ 3 / angleScale := by
        field_simp [h_angleScale_pos.ne', Real.pi_ne_zero]; ring
  have h_nonneg : 0 ≤ 8 * Real.pi * δ ^ 3 / angleScale := by positivity
  exact h_main1.trans (ENNReal.ofReal_le_ofReal h_ineq)

end Kakeya.Assouad
