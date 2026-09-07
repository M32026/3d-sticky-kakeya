import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.StickyZeroExtensionExtremal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BalancedFinitePlaniness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.OneScaleFiniteCoordinationSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SparseRelativeBandCVPackage

/-!
# Finite planiness on a sticky zero-extension

The retained selected-family shading is first zero-extended to the original
ambient tube family.  Its quantitatively derived extremality then supports the
existing high-multiplicity dense/sparse planiness theorem, including the
variable-`Q` sparse CV gain.  Finally the output is restricted back to the
selected family with exactly the same mass account.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- Run high-multiplicity finite planiness on a quantitatively extremal sticky
zero-extension and restrict the result back to the selected fine family. -/
theorem sticky_zero_extension_finite_planiness
    {delta sigma sourceLoss stickyLoss targetLoss densityLoss
      kappa eta coefficient incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss family sourceShading)
    (hline : WZ1PaperIsLineClass family)
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (hsourceTarget : sourceLoss ≤ targetLoss)
    (hretentionPower :
      Kakeya.realRpowENN delta targetLoss ≤
        wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta sourceLoss)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hsmall : Kakeya.realRpowENN delta targetLoss < 1 / 4)
    (hfixedAbsorb :
      (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * targetLoss))
    (hsparsePackage : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) (extendShading sticky.selected sticky.refined)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * targetLoss)),
        Nonempty (SparseRelativeBandCVPackage
          (extendShading sticky.selected sticky.refined) prepared))
    (hdenseIncidence : eta ≤ incidenceBudget)
    (hsparseIncidence : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) (extendShading sticky.selected sticky.refined)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * targetLoss)),
      ∀ package : SparseRelativeBandCVPackage
        (extendShading sticky.selected sticky.refined) prepared,
        package.tau / kappa ≤ incidenceBudget)
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaPositive : 0 < kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (heta : 0 < eta)
    (hetaHalf : eta ≤ 1 / 2)
    (hcoefficient : 0 < coefficient)
    (hactualSmall : ∀ coordinate, coordinate < 1 →
      ((sticky_zero_extension_extremal sourceExtremal sticky
          hsourceTarget hretentionPower).cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < 1 / 8)
    (hparentKappa : ∀ coordinate, coordinate < 1 →
      8 * ((sticky_zero_extension_extremal sourceExtremal sticky
          hsourceTarget hretentionPower).cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < kappa) :
    Nonempty (BoundedBalancedFinitePlaninessData
      (coefficient := coefficient) sticky.refined incidenceBudget) := by
  let ambient : WZ1PaperTubeShading family :=
    extendShading sticky.selected sticky.refined
  let extremal : WZ2PaperCroppedIsExtremal
      sigma targetLoss family ambient :=
    sticky_zero_extension_extremal sourceExtremal sticky
      hsourceTarget hretentionPower
  have hdelta : 0 < delta := extremal.delta_pos
  rcases high_multiplicity_balanced_direction_dichotomy
      extremal hline hdeltaSmall hdensityLoss htargetLoss hsmall
      hfixedAbsorb with ⟨dichotomy⟩
  rcases high_multiplicity_balanced_weak_finite_lipschitz_coefficient
      extremal.cwa_nearby_scales extremal.nonempty hline
      (by simpa [hdensityLoss] using dichotomy)
      hsparsePackage 1 schedule.requested schedule.spatialScale
      schedule.variationScale schedule.K hkappaNonnegative hkappaPositive
      hkappaHalf hdelta heta hetaHalf hcoefficient hactualSmall hparentKappa
      schedule.spatial_pos schedule.variation_pos schedule.K_pos
      schedule.spatial_aligned schedule.covers with
    ⟨finite⟩
  have hincidence : finite.incidence ≤ incidenceBudget := by
    rcases finite.branch_formula with hdense | hsparse
    · rw [hdense.1]
      exact hdenseIncidence
    · rcases hsparse with
        ⟨prepared, package, hincidence, _hleft, _hright⟩
      rw [hincidence]
      exact hsparseIncidence prepared package
  let bounded : BoundedBalancedFinitePlaninessData
      (coefficient := coefficient) ambient incidenceBudget := {
    data := (finite.toPlaniness hdelta)
    incidence_le := hincidence
  }
  exact ⟨bounded.restrictZeroExtension sticky.selected⟩

end Kakeya.Assouad.PureWZ2

end
