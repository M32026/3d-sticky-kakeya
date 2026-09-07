import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalNormalizationCenteredFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicParentQuotientSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicRepresentativeParent

/-!
# Representative-parent schedule for horizontal normalization

The finite schedule and quotient construction do not depend on the formula
for the affine map.  This file exposes the single map-specific estimate they
need: a uniform distortion bound for the paper line metric.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Target line-diameter inherited from one complete source fiber. -/
def horizontalNormalizedRepresentativeLineBound
    (lineFactor sourceRho : ℝ) : ℝ :=
  lineFactor * (600000 * sourceRho)

/-- Radius of the preliminary parent centered on a target representative. -/
def horizontalNormalizedRepresentativeParentScale
    (targetDelta lineFactor sourceRho : ℝ) : ℝ :=
  (3 / 2 : ℝ) *
      horizontalNormalizedRepresentativeLineBound lineFactor sourceRho +
    targetDelta

/-- One source Definition-2.12 scale gives a target representative-parent
cover whenever the target line metric is controlled by a fixed multiple of
the source line metric. -/
theorem pureWZ2HorizontalNormalizedRepresentativeParentData
    {sourceDelta sourceRho targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    (sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant)
    (targetFine : Kakeya.Streamlined.TubeFamily targetDelta)
    (sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card)
    (lineFactor : ℝ) (hlineFactor : 0 ≤ lineFactor)
    (htargetDelta : 0 < targetDelta)
    (hsourceNonempty : sourceFine.Nonempty)
    (hsourceDeltaRho : sourceDelta ≤ sourceRho)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetLine : WZ1PaperIsLineClass targetFine)
    (htargetDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct targetFine)
    (htargetMidpoint : ∀ target,
      ‖wz2PaperTubeMidpoint (targetFine.tube target)‖ ≤ 3)
    (htargetPackingDistinct : WZ1PaperIsEssentiallyDistinct
      (wz2PaperRelabelFamily
        (sourceScale := targetDelta)
        (targetScale := (2 / 3 : ℝ) * targetDelta) targetFine))
    (htargetCarrierSubsetRelabel : ∀ {rho : ℝ}, 0 < rho →
      ∀ first second,
        (3 / 2 : ℝ) * wz1PaperLineDistance
            (targetFine.tube first) (targetFine.tube second) +
          targetDelta ≤ rho →
        (targetFine.tube first).carrier ⊆
          (wz2PaperRelabelTube (targetScale := rho)
            (targetFine.tube second)).carrier)
    (hlineTransport : ∀ first second,
      wz1PaperLineDistance (targetFine.tube first) (targetFine.tube second) ≤
        lineFactor *
          wz1PaperLineDistance
            (sourceFine.tube (sourceEquiv first))
            (sourceFine.tube (sourceEquiv second))) :
    PureWZ2RepresentativeParentCoverData
      (targetRho := horizontalNormalizedRepresentativeParentScale
        targetDelta lineFactor sourceRho)
      (lineBound := horizontalNormalizedRepresentativeLineBound
        lineFactor sourceRho)
      sourceScale targetFine sourceEquiv where
  source_nonempty := hsourceNonempty
  target_delta_pos := htargetDelta
  target_rho_pos := by
    unfold horizontalNormalizedRepresentativeParentScale
      horizontalNormalizedRepresentativeLineBound
    have hsourceRho : 0 < sourceRho := sourceScale.rho_pos
    positivity
  target_line_class := htargetLine
  target_ordinary_distinct := htargetDistinct
  target_midpoint_local := htargetMidpoint
  target_packing_distinct := htargetPackingDistinct
  target_carrier_subset_relabel := htargetCarrierSubsetRelabel
  common_source_parent_lineDistance := by
    intro first second hparent
    have hsourceDistance :=
      wz1PaperLineDistance_le_of_same_source_fiber_base_five sourceScale
        hsourceDeltaRho hsourceLine hsourceBase
          (sourceEquiv first) (sourceEquiv second) hparent
    calc
      wz1PaperLineDistance (targetFine.tube first) (targetFine.tube second)
          ≤ lineFactor *
              wz1PaperLineDistance
                (sourceFine.tube (sourceEquiv first))
                (sourceFine.tube (sourceEquiv second)) :=
            hlineTransport first second
      _ ≤ lineFactor * (600000 * sourceRho) := by gcongr
      _ = horizontalNormalizedRepresentativeLineBound
          lineFactor sourceRho := rfl
  containment_budget := le_rfl

/-- A finite source nearby-scale schedule lifts to preliminary target
representative parents through a single uniform line-metric distortion
factor. -/
noncomputable def pureWZ2HorizontalNormalizedRepresentativeSchedule
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant scheduleConstant : ENNReal} {levelCount : ℕ}
    (sourceSchedule : PureWZ2FiniteNearbyScheduleData
      (family := sourceFine) sourceConstant scheduleConstant levelCount)
    (targetFine : Kakeya.Streamlined.TubeFamily targetDelta)
    (sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card)
    (lineFactor : ℝ) (hlineFactor : 0 ≤ lineFactor)
    (htargetDelta : 0 < targetDelta)
    (hsourceNonempty : sourceFine.Nonempty)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetLine : WZ1PaperIsLineClass targetFine)
    (htargetDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct targetFine)
    (htargetMidpoint : ∀ target,
      ‖wz2PaperTubeMidpoint (targetFine.tube target)‖ ≤ 3)
    (htargetPackingDistinct : WZ1PaperIsEssentiallyDistinct
      (wz2PaperRelabelFamily
        (sourceScale := targetDelta)
        (targetScale := (2 / 3 : ℝ) * targetDelta) targetFine))
    (htargetCarrierSubsetRelabel : ∀ {rho : ℝ}, 0 < rho →
      ∀ first second,
        (3 / 2 : ℝ) * wz1PaperLineDistance
            (targetFine.tube first) (targetFine.tube second) +
          targetDelta ≤ rho →
        (targetFine.tube first).carrier ⊆
          (wz2PaperRelabelTube (targetScale := rho)
            (targetFine.tube second)).carrier)
    (hlineTransport : ∀ first second,
      wz1PaperLineDistance (targetFine.tube first) (targetFine.tube second) ≤
        lineFactor *
          wz1PaperLineDistance
            (sourceFine.tube (sourceEquiv first))
            (sourceFine.tube (sourceEquiv second))) :
    PureWZ2FiniteRepresentativeParentScheduleData
      targetFine sourceEquiv sourceConstant sourceSchedule.scaleCount where
  sourceRho coordinate := (sourceSchedule.witness coordinate).rho
  targetRho coordinate := horizontalNormalizedRepresentativeParentScale
    targetDelta lineFactor (sourceSchedule.witness coordinate).rho
  lineBound coordinate := horizontalNormalizedRepresentativeLineBound
    lineFactor (sourceSchedule.witness coordinate).rho
  sourceScale coordinate := (sourceSchedule.witness coordinate).scaleData
  parentData coordinate :=
    pureWZ2HorizontalNormalizedRepresentativeParentData
      (sourceSchedule.witness coordinate).scaleData targetFine sourceEquiv
        lineFactor hlineFactor htargetDelta hsourceNonempty
        ((sourceSchedule.requested coordinate).2.1.trans
          (sourceSchedule.witness coordinate).requested_le)
        hsourceLine hsourceBase htargetLine htargetDistinct htargetMidpoint
          htargetPackingDistinct htargetCarrierSubsetRelabel hlineTransport

/-- Radius of the public quotient parent after the maximal-net step. -/
def horizontalNormalizedQuotientCallerScale
    (targetDelta lineFactor sourceRho : ℝ) : ℝ :=
  4 *
      horizontalNormalizedRepresentativeLineBound lineFactor sourceRho +
    2 * targetDelta

/-- Multiplicative requested-scale loss of the horizontal quotient
construction. -/
def horizontalNormalizedQuotientScaleWindowConstant
    (lineFactor : ℝ) (sourceScheduleConstant : ENNReal) : ENNReal :=
  ENNReal.ofReal (2400000 * lineFactor) * sourceScheduleConstant + 2

theorem horizontalNormalizedQuotientCallerScale_pos
    {targetDelta lineFactor sourceRho : ℝ}
    (htargetDelta : 0 < targetDelta) (hlineFactor : 0 ≤ lineFactor)
    (hsourceRho : 0 < sourceRho) :
    0 < horizontalNormalizedQuotientCallerScale
      targetDelta lineFactor sourceRho := by
  unfold horizontalNormalizedQuotientCallerScale
    horizontalNormalizedRepresentativeLineBound
  positivity

theorem horizontalNormalizedQuotientCallerScale_containment
    {targetDelta lineFactor sourceRho : ℝ}
    (htargetDelta : 0 < targetDelta)
    (hlineFactor : 0 ≤ lineFactor) (hsourceRho : 0 < sourceRho) :
    (3 / 2 : ℝ) *
          (horizontalNormalizedRepresentativeLineBound lineFactor sourceRho +
            horizontalNormalizedQuotientCallerScale
              targetDelta lineFactor sourceRho / 4) +
        targetDelta ≤
      horizontalNormalizedQuotientCallerScale
        targetDelta lineFactor sourceRho := by
  simp only [horizontalNormalizedQuotientCallerScale,
    horizontalNormalizedRepresentativeLineBound]
  have hproduct : 0 ≤ lineFactor * (600000 * sourceRho) := by positivity
  nlinarith

/-- The quotient caller radius dominates every requested scale represented
by the corresponding source witness. -/
theorem horizontalNormalizedQuotientCallerScale_request_le
    {targetDelta lineFactor sourceRho request : ℝ}
    (htargetDelta : 0 < targetDelta)
    (hlineFactor : 1 ≤ lineFactor)
    (hrequestPos : 0 < request)
    (htarget : targetDelta ≤ request)
    (hrequest : request ≤ sourceRho) :
    request ≤ horizontalNormalizedQuotientCallerScale
      targetDelta lineFactor sourceRho := by
  unfold horizontalNormalizedQuotientCallerScale
    horizontalNormalizedRepresentativeLineBound
  have hsourceRhoPos : 0 < sourceRho := lt_of_lt_of_le hrequestPos hrequest
  have hscaled : request ≤ 2400000 * lineFactor * sourceRho := by
    calc
      request ≤ sourceRho := hrequest
      _ ≤ (2400000 * lineFactor) * sourceRho := by
        exact (show sourceRho ≤ (2400000 * lineFactor) * sourceRho from by
          nlinarith)
  nlinarith

/-- ENNReal scale-window estimate for the horizontal quotient caller. -/
theorem horizontalNormalizedQuotientCallerScale_within
    {targetDelta lineFactor sourceRho request : ℝ}
    {sourceScheduleConstant : ENNReal}
    (hlineFactor : 0 < lineFactor)
    (hsourceRho : 0 < sourceRho) (htargetDelta : 0 < targetDelta)
    (htarget : targetDelta ≤ request)
    (hsource : ENNReal.ofReal sourceRho <
      sourceScheduleConstant * ENNReal.ofReal request) :
    ENNReal.ofReal (horizontalNormalizedQuotientCallerScale
        targetDelta lineFactor sourceRho) <
      horizontalNormalizedQuotientScaleWindowConstant
        lineFactor sourceScheduleConstant * ENNReal.ofReal request := by
  let multiplier : ℝ := 2400000 * lineFactor
  have hmultiplierPos : 0 < multiplier := by
    dsimp only [multiplier]
    positivity
  have hmul : ENNReal.ofReal multiplier * ENNReal.ofReal sourceRho <
      ENNReal.ofReal multiplier *
        (sourceScheduleConstant * ENNReal.ofReal request) := by
    have hright := (ENNReal.mul_lt_mul_iff_right
      (ENNReal.ofReal_pos.mpr hmultiplierPos).ne'
      ENNReal.ofReal_ne_top).2 hsource
    simpa [mul_comm] using hright
  have htargetENN : ENNReal.ofReal targetDelta ≤ ENNReal.ofReal request :=
    ENNReal.ofReal_mono htarget
  have hadd : ENNReal.ofReal multiplier * ENNReal.ofReal sourceRho +
      2 * ENNReal.ofReal targetDelta <
    ENNReal.ofReal multiplier *
        (sourceScheduleConstant * ENNReal.ofReal request) +
      2 * ENNReal.ofReal request :=
    ENNReal.add_lt_add_of_lt_of_le
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      hmul (mul_le_mul_left' htargetENN 2)
  calc
    ENNReal.ofReal (horizontalNormalizedQuotientCallerScale
        targetDelta lineFactor sourceRho) =
      ENNReal.ofReal multiplier * ENNReal.ofReal sourceRho +
        2 * ENNReal.ofReal targetDelta := by
      unfold horizontalNormalizedQuotientCallerScale
        horizontalNormalizedRepresentativeLineBound multiplier
      rw [show 4 * (lineFactor * (600000 * sourceRho)) =
          multiplier * sourceRho by ring,
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul hmultiplierPos.le,
        ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ < ENNReal.ofReal multiplier *
          (sourceScheduleConstant * ENNReal.ofReal request) +
        2 * ENNReal.ofReal request := hadd
    _ = horizontalNormalizedQuotientScaleWindowConstant
        lineFactor sourceScheduleConstant * ENNReal.ofReal request := by
      unfold horizontalNormalizedQuotientScaleWindowConstant multiplier
      ring

/-- Reuse the generic maximal quotient construction for every coordinate of
the horizontal-normalized representative schedule. -/
noncomputable def pureWZ2HorizontalNormalizedParentQuotientSchedule
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    (representativeSchedule : PureWZ2FiniteRepresentativeParentScheduleData
      targetFine sourceEquiv sourceConstant scaleCount)
    (lineFactor : ℝ) (hlineFactor : 0 ≤ lineFactor)
    (hlineBound : ∀ coordinate,
      representativeSchedule.lineBound coordinate =
        horizontalNormalizedRepresentativeLineBound lineFactor
          (representativeSchedule.sourceRho coordinate))
    (_htargetRho : ∀ coordinate,
      representativeSchedule.targetRho coordinate =
        horizontalNormalizedRepresentativeParentScale targetDelta lineFactor
          (representativeSchedule.sourceRho coordinate)) :
    PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule where
  callerRho coordinate := horizontalNormalizedQuotientCallerScale
    targetDelta lineFactor (representativeSchedule.sourceRho coordinate)
  quotient coordinate := Classical.choice <|
    pureWZ2_anisotropic_parent_quotient
      (representativeSchedule.parentData coordinate)
      (horizontalNormalizedQuotientCallerScale_pos
        (representativeSchedule.parentData coordinate).target_delta_pos
        hlineFactor
        (representativeSchedule.sourceScale coordinate).rho_pos)
      (by
        rw [hlineBound coordinate]
        exact horizontalNormalizedQuotientCallerScale_containment
          (representativeSchedule.parentData coordinate).target_delta_pos
          hlineFactor
          (representativeSchedule.sourceScale coordinate).rho_pos)

end Kakeya.Assouad

end
