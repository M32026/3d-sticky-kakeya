import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryRescaledTube

/-!
# Locality of the midpoint-centered ordinary rescaling

A source tube supported in the unit ball and covered by one anchor has a
uniformly localized midpoint after the literal anisotropic rescaling.  The
bound is independent of the source and anchor scales.
-/

noncomputable section

namespace Kakeya.Assouad

/--
The midpoint of the public ordinary literal target lies in the ball of radius
`7 / 200`.
-/
theorem wz2PaperLiteralOrdinaryRescaledTube_midpoint_norm_le_seven_div_two_hundred
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hsourceUnit :
      source.carrier ⊆ Kakeya.DeltaTube.unitBall)
    (hsourceLine : WZ1PaperTubeInLineClass source)
    (hcover : WZ1PaperTubeCovers source anchor) :
    ‖wz2PaperTubeMidpoint
        (wz2PaperLiteralOrdinaryRescaledTube source anchor hrho)‖ ≤
      7 / 200 := by
  let sourceMid := wz2PaperTubeMidpoint source
  let sourceZero := wz1TubeAxisZeroPoint source
  let anchorZero := wz1TubeAxisZeroPoint anchor
  let parameter : ℝ :=
    source.base (2 : Fin 3) / source.direction (2 : Fin 3) + 1 / 2
  have hmidMem : sourceMid ∈ source.carrier :=
    wz2_paper_tubeMidpoint_mem_carrier source hdelta.le
  have hmidNorm : ‖sourceMid‖ ≤ 1 := by
    have hunit := hsourceUnit hmidMem
    simpa [sourceMid, Kakeya.DeltaTube.unitBall,
      Metric.mem_closedBall, dist_eq_norm] using hunit
  have hzeroTwo : sourceZero (2 : Fin 3) = 0 := by
    exact
      wz1TubeAxisZeroPoint_coord_two source hsourceLine.vertical
  have hmidEq :
      sourceMid =
        sourceZero + parameter • source.direction := by
    dsimp only [sourceMid, sourceZero, parameter,
      wz2PaperTubeMidpoint, wz1TubeAxisZeroPoint]
    module
  have hcoord : |sourceMid (2 : Fin 3)| ≤ 1 :=
    (abs_coord_two_le_norm sourceMid).trans hmidNorm
  have hcoordEq :
      sourceMid (2 : Fin 3) =
        parameter * source.direction (2 : Fin 3) := by
    rw [hmidEq]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      hzeroTwo, zero_add]
  have hproduct :
      |parameter| * |source.direction (2 : Fin 3)| ≤ 1 := by
    calc
      |parameter| * |source.direction (2 : Fin 3)| =
          |parameter * source.direction (2 : Fin 3)| := by
        rw [abs_mul]
      _ = |sourceMid (2 : Fin 3)| := by rw [hcoordEq]
      _ ≤ 1 := hcoord
  have hparameter : |parameter| ≤ 2 := by
    have hlower :
        (1 / 2 : ℝ) * |parameter| ≤
          |parameter| * |source.direction (2 : Fin 3)| := by
      calc
        (1 / 2 : ℝ) * |parameter| =
            |parameter| * (1 / 2 : ℝ) := by ring
        _ ≤ |parameter| * |source.direction (2 : Fin 3)| :=
          mul_le_mul_of_nonneg_left
            hsourceLine.vertical (abs_nonneg parameter)
    linarith
  have hzeroDistance :
      ‖sourceZero - anchorZero‖ ≤ rho / 2 := by
    simpa [sourceZero, anchorZero, dist_eq_norm] using
      hcover.components.1
  have hzeroImage :
      ‖wz2PaperLiteralUnitRescalingLinear anchor
          (sourceZero - anchorZero)‖ ≤
        1 / 200 := by
    calc
      ‖wz2PaperLiteralUnitRescalingLinear anchor
          (sourceZero - anchorZero)‖ ≤
          ‖sourceZero - anchorZero‖ / (100 * rho) :=
        wz2PaperLiteralUnitRescalingLinear_norm_le
          anchor hrho hrhoOne _
      _ ≤ (rho / 2) / (100 * rho) := by
        gcongr
      _ = 1 / 200 := by
        field_simp [hrho.ne']
        ring
  have hdirectionImage :
      ‖wz2PaperLiteralUnitRescalingLinear anchor source.direction‖ ≤
        3 / 200 :=
    wz2PaperLiteralUnitRescalingLinear_sourceDirection_norm_le
      hrho hrhoOne hcover
  have htargetMid :
      wz2PaperTubeMidpoint
          (wz2PaperLiteralOrdinaryRescaledTube source anchor hrho) =
        wz2PaperLiteralUnitRescalingMap anchor hrho sourceMid := by
    dsimp only [sourceMid, wz2PaperTubeMidpoint,
      wz2PaperLiteralOrdinaryRescaledTube]
    module
  have hanchorZeroMap :
      wz2PaperLiteralUnitRescalingMap anchor hrho anchorZero = 0 := by
    dsimp only [anchorZero]
    simp [wz2PaperLiteralUnitRescalingMap, unitRescalingMap]
  have hmapMid :
      wz2PaperLiteralUnitRescalingMap anchor hrho sourceMid =
        wz2PaperLiteralUnitRescalingLinear anchor
          (sourceMid - anchorZero) := by
    have hsub :=
      wz2PaperLiteralUnitRescalingMap_sub
        anchor hrho sourceMid anchorZero
    rw [hanchorZeroMap, sub_zero] at hsub
    exact hsub
  have hdecompose :
      sourceMid - anchorZero =
        (sourceZero - anchorZero) +
          parameter • source.direction := by
    rw [hmidEq]
    abel
  rw [htargetMid, hmapMid, hdecompose, map_add, map_smul]
  calc
    ‖wz2PaperLiteralUnitRescalingLinear anchor
          (sourceZero - anchorZero) +
        parameter •
          wz2PaperLiteralUnitRescalingLinear anchor source.direction‖ ≤
        ‖wz2PaperLiteralUnitRescalingLinear anchor
            (sourceZero - anchorZero)‖ +
          ‖parameter •
            wz2PaperLiteralUnitRescalingLinear anchor
              source.direction‖ :=
      norm_add_le _ _
    _ =
        ‖wz2PaperLiteralUnitRescalingLinear anchor
            (sourceZero - anchorZero)‖ +
          |parameter| *
            ‖wz2PaperLiteralUnitRescalingLinear anchor
              source.direction‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 / 200 + 2 * (3 / 200) := by
      gcongr
    _ = 7 / 200 := by norm_num

/-- The fixed local window used by the ordinary containment bounds. -/
theorem wz2PaperLiteralOrdinaryRescaledTube_midpoint_norm_le_three
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hsourceUnit :
      source.carrier ⊆ Kakeya.DeltaTube.unitBall)
    (hsourceLine : WZ1PaperTubeInLineClass source)
    (hcover : WZ1PaperTubeCovers source anchor) :
    ‖wz2PaperTubeMidpoint
        (wz2PaperLiteralOrdinaryRescaledTube source anchor hrho)‖ ≤
      3 :=
  (wz2PaperLiteralOrdinaryRescaledTube_midpoint_norm_le_seven_div_two_hundred
    hdelta hrho hrhoOne source anchor hsourceUnit hsourceLine hcover).trans
    (by norm_num)

end Kakeya.Assouad

end
