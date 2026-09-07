import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicRepresentativeParent
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicParentQuotientSchedule

/-!
# Finite representative-parent schedule after the final similarity

This is the scale bookkeeping layer for rebuilding nearby-scale CWA after
the final positive isotropic normalization.  It deliberately reuses the
generic representative-parent and maximal-quotient structures: none of those
structures depends on the triangular formula used by the earlier Section 6
rescaling.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Line-diameter loss of one complete source fiber after the positive
similarity. -/
def isotropicRepresentativeLineBound (scale sourceRho : ℝ) : ℝ :=
  4200000 * scale * sourceRho

/-- Radius of the preliminary parent centered on the representative image
line. -/
def isotropicRepresentativeParentScale
    (targetDelta scale sourceRho : ℝ) : ℝ :=
  6300000 * scale * sourceRho + targetDelta

/-- Radius of the public quotient parent.  The factor three leaves the exact
margin required to absorb both the representative-fiber diameter and the
maximal-net displacement. -/
def isotropicQuotientCallerScale
    (targetDelta scale sourceRho : ℝ) : ℝ :=
  12600000 * scale * sourceRho + 2 * targetDelta

/-- Multiplicative requested-scale loss of the final isotropic quotient
construction. -/
def isotropicQuotientScaleWindowConstant
    (scale : ℝ) (sourceScheduleConstant : ENNReal) : ENNReal :=
  ENNReal.ofReal (12600000 * scale) * sourceScheduleConstant + 2

theorem isotropicRepresentativeParentScale_pos
    {targetDelta scale sourceRho : ℝ}
    (htargetDelta : 0 < targetDelta) (hscale : 0 < scale)
    (hsourceRho : 0 < sourceRho) :
    0 < isotropicRepresentativeParentScale
      targetDelta scale sourceRho := by
  unfold isotropicRepresentativeParentScale
  positivity

theorem isotropicRepresentativeParentScale_containment
    (targetDelta scale sourceRho : ℝ) :
    (3 / 2 : ℝ) * isotropicRepresentativeLineBound scale sourceRho +
        targetDelta =
      isotropicRepresentativeParentScale targetDelta scale sourceRho := by
  unfold isotropicRepresentativeLineBound
    isotropicRepresentativeParentScale
  ring

theorem isotropicQuotientCallerScale_pos
    {targetDelta scale sourceRho : ℝ}
    (htargetDelta : 0 < targetDelta) (hscale : 0 < scale)
    (hsourceRho : 0 < sourceRho) :
    0 < isotropicQuotientCallerScale targetDelta scale sourceRho := by
  unfold isotropicQuotientCallerScale
  positivity

theorem isotropicQuotientCallerScale_containment
    {targetDelta scale sourceRho : ℝ}
    (htargetDelta : 0 < targetDelta) (hscale : 0 < scale)
    (hsourceRho : 0 < sourceRho) :
    (3 / 2 : ℝ) *
          (isotropicRepresentativeLineBound scale sourceRho +
            isotropicQuotientCallerScale targetDelta scale sourceRho / 4) +
        targetDelta ≤
      isotropicQuotientCallerScale targetDelta scale sourceRho := by
  unfold isotropicRepresentativeLineBound isotropicQuotientCallerScale
  nlinarith

/-- Apply the isotropic representative-parent construction to every witness
of a finite source nearby-scale schedule. -/
noncomputable def isotropicRepresentativeParentSchedule
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant scheduleConstant : ENNReal}
    {levelCount : ℕ}
    (sourceSchedule : PureWZ2FiniteNearbyScheduleData
      (family := sourceFine) sourceConstant scheduleConstant levelCount)
    (center : Point3) {scale : ℝ}
    (hscale : 1 ≤ scale) (hcenter : |center 2| ≤ 1)
    (htargetDelta : 0 < targetDelta)
    (hsourceNonempty : sourceFine.Nonempty)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (hzero : ∀ (index : Fin sourceFine.card) (coordinate : Fin 2),
      |(pureWZ2IsotropicMap center scale
        (wz1PaperAxisPointAtHeight
          (sourceFine.tube index) (center 2))) coordinate.castSucc| ≤ 1 / 3)
    (htargetDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFine center scale)) :
    PureWZ2FiniteRepresentativeParentScheduleData
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFine center scale)
      (Equiv.refl (Fin sourceFine.card)) sourceConstant
      sourceSchedule.scaleCount where
  sourceRho coordinate := (sourceSchedule.witness coordinate).rho
  targetRho coordinate := isotropicRepresentativeParentScale
    targetDelta scale (sourceSchedule.witness coordinate).rho
  lineBound coordinate := isotropicRepresentativeLineBound
    scale (sourceSchedule.witness coordinate).rho
  sourceScale coordinate := (sourceSchedule.witness coordinate).scaleData
  parentData coordinate := pureWZ2IsotropicRepresentativeParentData
    (sourceSchedule.witness coordinate).scaleData center hscale hcenter
    htargetDelta
    (isotropicRepresentativeParentScale_pos htargetDelta
      (lt_of_lt_of_le (by norm_num) hscale)
      (sourceSchedule.witness coordinate).scaleData.rho_pos)
    hsourceNonempty
    ((sourceSchedule.requested coordinate).2.1.trans
      (sourceSchedule.witness coordinate).requested_le)
    hsourceLine hsourceBase hzero htargetDistinct
    (isotropicRepresentativeParentScale_containment
      targetDelta scale (sourceSchedule.witness coordinate).rho).le

/-- Build all maximal quotient nets for the final similarity schedule. -/
noncomputable def isotropicParentQuotientSchedule
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {scale : ℝ}
    (representativeSchedule : PureWZ2FiniteRepresentativeParentScheduleData
      targetFine sourceEquiv sourceConstant scaleCount)
    (hscale : 0 < scale)
    (hlineBound : ∀ coordinate,
      representativeSchedule.lineBound coordinate =
        isotropicRepresentativeLineBound scale
          (representativeSchedule.sourceRho coordinate)) :
    PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule where
  callerRho coordinate := isotropicQuotientCallerScale targetDelta scale
    (representativeSchedule.sourceRho coordinate)
  quotient coordinate := Classical.choice <|
    pureWZ2_anisotropic_parent_quotient
      (representativeSchedule.parentData coordinate)
      (isotropicQuotientCallerScale_pos
        (representativeSchedule.parentData coordinate).target_delta_pos
        hscale
        (representativeSchedule.sourceScale coordinate).rho_pos)
      (by
        rw [hlineBound coordinate]
        exact isotropicQuotientCallerScale_containment
          (representativeSchedule.parentData coordinate).target_delta_pos
          hscale
          (representativeSchedule.sourceScale coordinate).rho_pos)

end Kakeya.Assouad

end
