import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7AnalyticCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7OrdinaryCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7ProjectionUpper

/-!
# Node 7 affine configuration to analytic cleanup

This is the construction boundary between the synchronized affine geometry
and the scale-generic Section 7 cleanup.  The three scalar receipts are kept
explicit; all structural fields come from the same affine package.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

namespace PureWZ2Node7AffineDiagonalPreparationData

variable
    {logExponent : ℕ}
    {sigma epsilon delta analyticLoss : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

theorem toParameterFrostmanPreparation
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (cutoff : PureWZ2Node7AnalyticCleanupCutoffData sigma analyticLoss)
    (hloss : 0 < analyticLoss)
    (hfinalCutoff : data.finalRadius ≤ cutoff.r₀)
    (hcwa : WZ2PaperConvexWolffBound data.ordinaryFamily
      (Kakeya.realRpowENN data.finalRadius (-(analyticLoss / 100))))
    (hdense : data.ordinaryShading.IsLambdaDense
      (Kakeya.realRpowENN data.finalRadius (analyticLoss / 100)))
    (hprojection : volume
        (twistedUnion data.ordinaryShading data.analysisSlope) ≤
      Kakeya.realRpowENN data.finalRadius (sigma - analyticLoss)) :
    Nonempty (PureWZ2ParameterFrostmanPreparationData
      sigma analyticLoss data.finalRadius) := by
  exact cutoff.run data.ordinaryFamily data.ordinaryShading hloss
    data.finalRadius_pos hfinalCutoff data.ordinaryFamily_nonempty
    data.ordinaryFamily_hasBoundedBase data.ordinaryFamily_isInVerticalChart
    data.ordinaryShading_isInSlopeWindow data.ordinaryFamily_line_class
    hcwa hdense data.analysisSlope data.analysisSlope_zero
    data.analysisSlope_nonsingular hprojection

end PureWZ2Node7AffineDiagonalPreparationData

end Kakeya.Assouad

end
