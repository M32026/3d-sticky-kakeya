import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiberIsInUnitBall
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryNestedScaleProducer

/-!
# Bounded support for the canonical ordinary rescaled family

The abstract Assouad-to-literal certificate permits arbitrary recentering
along the target axes.  The concrete certificate used by Proposition 6.2 is
more rigid: its public tubes are centered at the transformed source
midpoints.  A fixed source base bound therefore gives unit-ball support for
that canonical public family.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The canonical midpoint-centred public family lies in the unit ball when
the source family has the fixed base bound used by the Node 4 re-entry. -/
theorem
    wz2PaperLiteralOrdinaryRescaledFamilyCertificate_publicFamily_isInUnitBall_of_boundedBase
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hratio : delta / rho ≤ 1 / 24)
    (sourceFamily : Kakeya.Streamlined.TubeFamily delta)
    (anchor : Kakeya.DeltaTube rho)
    (sourceLine : WZ1PaperIsLineClass sourceFamily)
    (sourceBounded : HasBoundedBase sourceFamily 4)
    (anchorLine : WZ1PaperTubeInLineClass anchor)
    (covered : ∀ index,
      WZ1PaperTubeCovers (sourceFamily.tube index) anchor) :
    (wz2PaperLiteralOrdinaryRescaledFamilyCertificate
      hdelta hrho hrhoOne sourceFamily anchor
      sourceLine anchorLine covered).publicFamily.IsInUnitBall := by
  rw [wz2PaperLiteralOrdinaryRescaledFamilyCertificate_publicFamily]
  intro index
  have sourceMidpoint :
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 9 / 2 := by
    calc
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ =
          ‖(sourceFamily.tube index).base +
            (1 / 2 : ℝ) • (sourceFamily.tube index).direction‖ := rfl
      _ ≤ ‖(sourceFamily.tube index).base‖ +
          ‖(1 / 2 : ℝ) • (sourceFamily.tube index).direction‖ :=
        norm_add_le _ _
      _ = ‖(sourceFamily.tube index).base‖ + 1 / 2 := by
        rw [norm_smul, (sourceFamily.tube index).direction_unit]
        norm_num
      _ ≤ 9 / 2 := by
        linarith [sourceBounded index]
  exact wz2PaperLiteralOrdinaryRescaledTube_is_in_unit_ball
    (C := 9 / 2) hdelta hrho hrhoOne (sourceFamily.tube index) anchor
    (sourceLine index) (covered index) sourceMidpoint
    (by norm_num) (div_pos hdelta hrho) (by nlinarith)

end Kakeya.Assouad

end
