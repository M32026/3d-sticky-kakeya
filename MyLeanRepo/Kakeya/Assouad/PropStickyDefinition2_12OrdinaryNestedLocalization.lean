import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12LocalizedDoubledFiber
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryNestedScaleProducer

/-!
# Localization input for one ordinary nested scale

The midpoint locality of the target fine family is sufficient for the
localized centered-doubled containment estimate.  No midpoint locality is
required for the target middle parent.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Construct the ordinary nested localization certificate directly from target
line classes and target-fine midpoint locality.
-/
def wz2PaperOrdinaryNestedTargetLocalization_of_targetLocality
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (sourceFine : Kakeya.Streamlined.TubeFamily delta)
    (sourceMiddle : Kakeya.Streamlined.TubeFamily rho)
    (anchor : Kakeya.DeltaTube sigma)
    (htargetFine :
      WZ1PaperIsLineClass
        (wz2PaperLiteralOrdinaryRescaledFamily
          sourceFine anchor hsigma))
    (htargetMiddle :
      WZ1PaperIsLineClass
        (wz2PaperLiteralOrdinaryRescaledFamily
          sourceMiddle anchor hsigma))
    (htargetFineLocal :
      ∀ target,
        ‖wz2PaperTubeMidpoint
          ((wz2PaperLiteralOrdinaryRescaledFamily
            sourceFine anchor hsigma).tube target)‖ ≤ 3) :
    WZ2PaperOrdinaryNestedTargetLocalization
      sourceFine sourceMiddle anchor hsigma where
  centered_doubled_lineDistance_le target parent hcontained := by
    have hlocalized :=
      wz2_paper_localized_centered_doubled_containment_lineDistance_le
        (div_pos hdelta hsigma)
        (div_pos hrho hsigma)
        (htargetFine target)
        (htargetMiddle parent)
        (htargetFineLocal target)
        hcontained
    calc
      wz1PaperLineDistance
          ((wz2PaperLiteralOrdinaryRescaledFamily
            sourceFine anchor hsigma).tube target)
          ((wz2PaperLiteralOrdinaryRescaledFamily
            sourceMiddle anchor hsigma).tube parent) ≤
          wz2PaperLocalizedDoubledFiberLineDistanceConstant *
            (rho / sigma) :=
        hlocalized
      _ ≤ 800 * (rho / sigma) := by
        rw [wz2PaperLocalizedDoubledFiberLineDistanceConstant]
        nlinarith [div_pos hrho hsigma]

/--
Convenience wrapper deriving both target line classes from source line
classes and the common-anchor cover relations.
-/
def wz2PaperOrdinaryNestedTargetLocalization_of_sourceCovers
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma ≤ 1)
    (sourceFine : Kakeya.Streamlined.TubeFamily delta)
    (sourceMiddle : Kakeya.Streamlined.TubeFamily rho)
    (anchor : Kakeya.DeltaTube sigma)
    (hfine : WZ1PaperIsLineClass sourceFine)
    (hmiddle : WZ1PaperIsLineClass sourceMiddle)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hFineAnchor :
      ∀ source,
        WZ1PaperTubeCovers (sourceFine.tube source) anchor)
    (hMiddleAnchor :
      ∀ parent,
        WZ2PaperDilatedTubeCovers 2
          (sourceMiddle.tube parent) anchor)
    (htargetFineLocal :
      ∀ target,
        ‖wz2PaperTubeMidpoint
          ((wz2PaperLiteralOrdinaryRescaledFamily
            sourceFine anchor hsigma).tube target)‖ ≤ 3) :
    WZ2PaperOrdinaryNestedTargetLocalization
      sourceFine sourceMiddle anchor hsigma :=
  wz2PaperOrdinaryNestedTargetLocalization_of_targetLocality
    hdelta hrho hsigma sourceFine sourceMiddle anchor
    (wz2PaperLiteralOrdinaryRescaledFamily_lineClass
      hsigma hsigmaOne sourceFine anchor hfine hanchor
      (fun source => by
        have hstrict := hFineAnchor source
        unfold WZ1PaperTubeCovers at hstrict
        unfold WZ2PaperDilatedTubeCovers
        linarith))
    (wz2PaperLiteralOrdinaryRescaledFamily_lineClass
      hsigma hsigmaOne sourceMiddle anchor
      hmiddle hanchor hMiddleAnchor)
    htargetFineLocal

end Kakeya.Assouad

end
