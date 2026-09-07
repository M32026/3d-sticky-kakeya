import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6FixedScaleOutput

/-!
# Fixed-output preconditioning multiplicity cap

This module isolates the scalar normalization used when a later same-ambient
shading is pointwise dominated by a certified fixed-scale Node-6 refinement.
The only geometric input is the existing fixed-scale multiplicity cap.
-/

noncomputable section

namespace Kakeya.Assouad

lemma node6_fixed_preconditioning_realRpowENN_rpow
    {delta : ℝ} (hdelta : 0 < delta) (power exponent : ℝ) :
    Kakeya.realRpowENN (Real.rpow delta power) exponent =
      Kakeya.realRpowENN delta (power * exponent) := by
  simp only [Kakeya.realRpowENN]
  congr 1
  exact (Real.rpow_mul hdelta.le power exponent).symm

/-- Rewrite the fixed-output relative cap at `rho = delta^power` as one power
of the original fine scale. -/
lemma node6_fixed_preconditioning_ratio_rpow
    {delta power exponent : ℝ}
    (hdelta : 0 < delta) :
    Kakeya.realRpowENN (delta / Real.rpow delta power) exponent =
      Kakeya.realRpowENN delta ((1 - power) * exponent) := by
  have hratio : delta / Real.rpow delta power =
      Real.rpow delta (1 - power) := by
    calc
      delta / Real.rpow delta power =
          Real.rpow delta 1 / Real.rpow delta power := by
        congr 1
        exact (Real.rpow_one delta).symm
      _ = Real.rpow delta (1 - power) :=
        (Real.rpow_sub hdelta 1 power).symm
  rw [hratio]
  exact node6_fixed_preconditioning_realRpowENN_rpow
    hdelta (1 - power) exponent

/-- Split the target preconditioning exponent into the fixed-output cap and
the later power-scale loss. -/
lemma node6_fixed_preconditioning_cap_factor
    {delta sigma power stickyLoss : ℝ}
    (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta (2 - sigma - (1 + power) * stickyLoss) =
      Kakeya.realRpowENN delta (2 - sigma - stickyLoss) *
        Kakeya.realRpowENN (Real.rpow delta power) (-stickyLoss) := by
  calc
    Kakeya.realRpowENN delta (2 - sigma - (1 + power) * stickyLoss) =
        Kakeya.realRpowENN delta
          ((2 - sigma - stickyLoss) + power * (-stickyLoss)) := by
      congr 1
      ring
    _ =
        Kakeya.realRpowENN delta (2 - sigma - stickyLoss) *
          Kakeya.realRpowENN delta (power * (-stickyLoss)) := by
      rw [realRpowENN_add hdelta]
    _ =
        Kakeya.realRpowENN delta (2 - sigma - stickyLoss) *
          Kakeya.realRpowENN (Real.rpow delta power) (-stickyLoss) := by
      rw [node6_fixed_preconditioning_realRpowENN_rpow
        hdelta power (-stickyLoss)]

namespace PureWZ2Node6FixedScaleOutput

/-- A later same-ambient shading inherits a pointwise cap from a certified
fixed-output refinement after rewriting the relative scale `delta / rho` at
`rho = delta^preLoss` and weakening the exponent to the requested sticky-loss
budget. -/
theorem pointMultiplicity_upper_preconditioned
    {delta sigma preLoss stickyLoss power : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {preRho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (pre : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := preLoss)
      sourceShading preRho logExponent)
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading ambient)
    (hpreRho : preRho.1 = Real.rpow delta preLoss)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (_hpreLoss : 0 < preLoss)
    (_hpreLossOne : preLoss ≤ 1)
    (hpointwise : ∀ point,
      (Y.pointMultiplicity point : ENNReal) ≤
        (pre.refined.pointMultiplicity point : ENNReal))
    (hselectedAmbient : pre.selected.family.enncard ≤ ambient.enncard)
    (hexponent :
      2 - sigma - (1 + power) * stickyLoss ≤
        (1 - preLoss) * (2 - sigma - preLoss)) :
    ∀ point,
      (Y.pointMultiplicity point : ENNReal) ≤
        (Kakeya.realRpowENN delta (2 - sigma - stickyLoss) *
          Kakeya.realRpowENN (Real.rpow delta power) (-stickyLoss)) *
            ambient.enncard := by
  intro point
  calc
    (Y.pointMultiplicity point : ENNReal) ≤
        (pre.refined.pointMultiplicity point : ENNReal) :=
      hpointwise point
    _ ≤
        Kakeya.realRpowENN (delta / preRho.1)
            (2 - sigma - preLoss) *
          pre.selected.family.enncard :=
      pre.fine_pointMultiplicity_upper point
    _ =
        Kakeya.realRpowENN delta
            ((1 - preLoss) * (2 - sigma - preLoss)) *
          pre.selected.family.enncard := by
      rw [hpreRho, node6_fixed_preconditioning_ratio_rpow hdelta]
    _ ≤
        Kakeya.realRpowENN delta
            (2 - sigma - (1 + power) * stickyLoss) *
          ambient.enncard := by
      gcongr
      exact pure_wz2_rpowENN_antitone hdelta hdeltaOne hexponent
    _ =
        (Kakeya.realRpowENN delta (2 - sigma - stickyLoss) *
          Kakeya.realRpowENN (Real.rpow delta power) (-stickyLoss)) *
            ambient.enncard := by
      rw [node6_fixed_preconditioning_cap_factor hdelta]

end PureWZ2Node6FixedScaleOutput

end Kakeya.Assouad

end
