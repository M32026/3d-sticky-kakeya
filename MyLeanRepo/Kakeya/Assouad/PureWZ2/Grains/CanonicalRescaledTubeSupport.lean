import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryRescaledLocality
import MyLeanRepo.Kakeya.Assouad.Hairbrush.HomogeneousTwoEndsHelpers

/-!
# Unit-ball support for canonical literal ordinary rescalings

The public ordinary tube used in the Assouad-to-literal bridge is centered at
the transformed source midpoint.  The existing locality estimate places this
midpoint within `7 / 200` of the origin.  At normalized scale at most `1 / 24`,
the whole unit-segment tube therefore lies in the closed unit ball.

This is a geometric property of the concrete canonical tube.  It is kept
separate from `WZ2PaperPureRescaledFullFiberOutput`, whose abstract certificate
does not record that its public family was produced by this construction.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- A tube lies in the unit ball when its midpoint and its radius leave enough
room for the half-unit axis segment. -/
lemma tube_isInUnitBall_of_midpoint_margin
    {delta : ℝ}
    (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta)
    (hmargin :
      ‖wz2PaperTubeMidpoint tube‖ + (1 / 2 + delta) ≤ 1) :
    tube.IsInUnitBall := by
  intro point hpoint
  have hmidpoint :
      tube.base + (1 / 2 : ℝ) • tube.direction =
        wz2PaperTubeMidpoint tube := by
    rfl
  have hpointMidpoint :
      dist point (wz2PaperTubeMidpoint tube) ≤ 1 / 2 + delta := by
    rw [← hmidpoint]
    exact tube_subset_midpoint_closedBall hdelta tube hpoint
  have hmidpointOrigin :
      dist (wz2PaperTubeMidpoint tube) 0 =
        ‖wz2PaperTubeMidpoint tube‖ := by
    simp [dist_eq_norm]
  have hpointOrigin : dist point 0 ≤ 1 := by
    calc
      dist point 0 ≤
          dist point (wz2PaperTubeMidpoint tube) +
            dist (wz2PaperTubeMidpoint tube) 0 :=
        dist_triangle point (wz2PaperTubeMidpoint tube) 0
      _ ≤ (1 / 2 + delta) + ‖wz2PaperTubeMidpoint tube‖ := by
        rw [hmidpointOrigin]
        gcongr
      _ ≤ 1 := by linarith
  simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall] using hpointOrigin

/-- The concrete midpoint-centered ordinary target in the literal rescaling
bridge is supported in the unit ball at normalized scale at most `1 / 24`. -/
theorem wz2PaperLiteralOrdinaryRescaledTube_isInUnitBall
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hratio : delta / rho ≤ 1 / 24)
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hsourceUnit : source.IsInUnitBall)
    (hsourceLine : WZ1PaperTubeInLineClass source)
    (hcover : WZ1PaperTubeCovers source anchor) :
    (wz2PaperLiteralOrdinaryRescaledTube
      source anchor hrho).IsInUnitBall := by
  let target := wz2PaperLiteralOrdinaryRescaledTube source anchor hrho
  have htargetScale : 0 < delta / rho := div_pos hdelta hrho
  have hmidpoint :
      ‖wz2PaperTubeMidpoint target‖ ≤ 7 / 200 := by
    simpa [target] using
      wz2PaperLiteralOrdinaryRescaledTube_midpoint_norm_le_seven_div_two_hundred
        hdelta hrho hrhoOne source anchor hsourceUnit hsourceLine hcover
  apply tube_isInUnitBall_of_midpoint_margin htargetScale target
  calc
    ‖wz2PaperTubeMidpoint target‖ + (1 / 2 + delta / rho) ≤
        7 / 200 + (1 / 2 + 1 / 24) := by
      gcongr
    _ ≤ 1 := by norm_num

end Kakeya.Assouad

end
