import MyLeanRepo.Kakeya.Assouad.PureWZ2.Critical

/-!
# The Wolff ceiling used at the start of Proposition 6.3

The paper begins the grains argument with `0 < σ ≤ 1 / 2`.  Positivity is
stored in `PureWZ2CriticalPackage`; the upper bound follows from the Wolff
volume floor in the subunit package.  This module records that implication
without adding it to the frozen critical-package interface.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad.PureWZ2

/-- A critical exponent compatible with the pure Wolff floor is at most
`1 / 2`.  The proof compares an arbitrarily small critical extremizer with
the Wolff lower bound at the same scale. -/
theorem pure_wz2_critical_sigma_le_half
    {sigma : ℝ}
    (h_subunit : PureWZ2SubunitPackageStatement)
    (critical : PureWZ2CriticalPackage sigma) :
    sigma ≤ 1 / 2 := by
  by_contra hnot
  have hsigmaHalf : 1 / 2 < sigma := lt_of_not_ge hnot
  let epsilon : ℝ := (sigma - 1 / 2) / 4
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  rcases h_subunit.2.2.2.1 epsilon hepsilon with
    ⟨structuralLoss, deltaFloor, hstructuralLoss, hdeltaFloor,
      hdeltaFloorOne, hfloor⟩
  let sourceLoss : ℝ := min (structuralLoss / 2) epsilon
  have hsourceLoss : 0 < sourceLoss := by
    dsimp only [sourceLoss]
    exact lt_min (half_pos hstructuralLoss) hepsilon
  have hsourceLossStructural : sourceLoss ≤ structuralLoss := by
    calc
      sourceLoss ≤ structuralLoss / 2 := min_le_left _ _
      _ ≤ structuralLoss := by linarith
  have hsourceLossEpsilon : sourceLoss ≤ epsilon := min_le_right _ _
  let deltaRequest : ℝ := min deltaFloor (1 / 2)
  have hdeltaRequest : 0 < deltaRequest := by
    dsimp only [deltaRequest]
    positivity
  rcases critical.extremal_sequence sourceLoss deltaRequest
      hsourceLoss hdeltaRequest with
    ⟨delta, hdelta, hdeltaRequestBound, ⟨extremal⟩⟩
  have hdeltaFloorBound : delta ≤ deltaFloor :=
    hdeltaRequestBound.trans (min_le_left _ _)
  have hdeltaHalf : delta ≤ 1 / 2 :=
    hdeltaRequestBound.trans (min_le_right _ _)
  have hdeltaOne : delta < 1 := by linarith
  have hcwa := extremal.extremal.cwa_nearby_scales.mono_loss
    extremal.extremal.delta_pos extremal.extremal.delta_le_one
      hsourceLossStructural
  have hdensityPower :
      Kakeya.realRpowENN delta structuralLoss ≤
        Kakeya.realRpowENN delta sourceLoss := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge
      extremal.extremal.delta_pos extremal.extremal.delta_le_one
        hsourceLossStructural
  have hdense : extremal.shading.IsLambdaDense
      (Kakeya.realRpowENN delta structuralLoss) :=
    (mul_le_mul_right' hdensityPower
      extremal.family.toBodyFamily.mass).trans extremal.extremal.dense
  have hlower :
      Kakeya.realRpowENN delta (1 / 2 + epsilon) ≤
        volume extremal.shading.union :=
    hfloor delta hdelta hdeltaFloorBound extremal.family
      extremal.extremal.nonempty hcwa extremal.shading hdense
  have hexponents : 1 / 2 + epsilon < sigma - sourceLoss := by
    dsimp only [epsilon] at *
    linarith
  have hpower :
      Kakeya.realRpowENN delta (sigma - sourceLoss) <
        Kakeya.realRpowENN delta (1 / 2 + epsilon) := by
    apply ENNReal.ofReal_lt_ofReal_iff
        (Real.rpow_pos_of_pos hdelta (1 / 2 + epsilon)) |>.2
    exact Real.rpow_lt_rpow_of_exponent_gt hdelta hdeltaOne hexponents
  exact (not_lt_of_ge extremal.extremal.volume_upper)
    (hpower.trans_le hlower)

end Kakeya.Assouad.PureWZ2

end
