import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12LocalizedEssentialDistinctness
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryNestedScaleProducer
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryRescaledLocality

/-!
# Essential distinctness of one ordinary literal image family

Strong source separation survives the common literal rescaling.  Unit-ball
support localizes the midpoint-centered ordinary targets, so the resulting
line separation rules out centered two-fold containment in both directions.
-/

noncomputable section

namespace Kakeya.Assouad

/--
A strongly separated source family in one strict anchor fiber becomes
essentially distinct in the ordinary centered-dilation sense of Definition
2.12 after the common literal rescaling.
-/
theorem wz2PaperLiteralOrdinaryRescaledFamily_essentiallyDistinct
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hdeltaRho : delta ≤ rho)
    (hrhoOne : rho ≤ 1)
    (source : Kakeya.Streamlined.TubeFamily delta)
    (anchor : Kakeya.DeltaTube rho)
    (hsourceUnit : source.IsInUnitBall)
    (hsourceLine : WZ1PaperIsLineClass source)
    (hanchorLine : WZ1PaperTubeInLineClass anchor)
    (hcover :
      ∀ index,
        WZ1PaperTubeCovers (source.tube index) anchor)
    (hseparated :
      ∀ first second, first ≠ second →
        wz2PaperLiteralSourceSeparationFactor * delta <
          wz1PaperLineDistance
            (source.tube first) (source.tube second)) :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      (wz2PaperLiteralOrdinaryRescaledFamily
        source anchor hrho) := by
  let target :=
    wz2PaperLiteralOrdinaryRescaledFamily source anchor hrho
  have htargetLine : WZ1PaperIsLineClass target :=
    wz2PaperLiteralOrdinaryRescaledFamily_lineClass
      hrho hrhoOne source anchor hsourceLine hanchorLine
      (fun index => by
        have hstrict := hcover index
        unfold WZ1PaperTubeCovers at hstrict
        unfold WZ2PaperDilatedTubeCovers
        linarith)
  have htargetLocal :
      ∀ index,
        ‖wz2PaperTubeMidpoint (target.tube index)‖ ≤ 3 := by
    intro index
    exact
      wz2PaperLiteralOrdinaryRescaledTube_midpoint_norm_le_three
        hdelta hrho hrhoOne
        (source.tube index) anchor
        (hsourceUnit index) (hsourceLine index) (hcover index)
  have htargetSeparated :
      ∀ first second, first ≠ second →
        wz2PaperLocalizedDoubledFiberLineDistanceConstant *
              (delta / rho) <
          wz1PaperLineDistance
            (target.tube first) (target.tube second) := by
    intro first second hne
    have hstrong :
        1600 * (delta / rho) <
          wz1PaperLineDistance
            (target.tube first) (target.tube second) := by
      exact
        wz2_paper_literal_dilated_strong_separation
          hdelta hdeltaRho hrho hrhoOne
          (source.tube first) (source.tube second) anchor
          (hsourceLine first) (hsourceLine second) hanchorLine
          (by
            have hstrict := hcover first
            unfold WZ1PaperTubeCovers at hstrict
            unfold WZ2PaperDilatedTubeCovers
            linarith)
          (by
            have hstrict := hcover second
            unfold WZ1PaperTubeCovers at hstrict
            unfold WZ2PaperDilatedTubeCovers
            linarith)
          (hseparated first second hne)
          (target.tube first) (target.tube second)
          (htargetLine first) (htargetLine second)
          (wz2PaperLiteralOrdinaryRescaledTube_axis
            (source.tube first) anchor hrho)
          (wz2PaperLiteralOrdinaryRescaledTube_axis
            (source.tube second) anchor hrho)
    have hscale : 0 < delta / rho := div_pos hdelta hrho
    dsimp only [wz2PaperLocalizedDoubledFiberLineDistanceConstant]
    linarith
  exact
    wz2_paper_localized_ordinary_isEssentiallyDistinct
      (div_pos hdelta hrho) htargetLine htargetLocal htargetSeparated

end Kakeya.Assouad

end
