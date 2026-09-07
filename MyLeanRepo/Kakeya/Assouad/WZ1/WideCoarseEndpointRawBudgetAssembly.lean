import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointRawCounting
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointSourceBudget

/-!
# Assemble an endpoint source budget from one scalar raw coefficient bound
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- The scalar loss left by the complete raw-strip counting chain. -/
noncomputable def wideCoarseEndpointRawCoefficient
    {epsilon eta delta : ℝ}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    {F G₁ G₂ ambient active : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    (input :
      WZ1WideCoarseEndpointLineInput
        (ambient := ambient) (active := active)
        parameters data)
    (rawRadius : ℝ) : ENNReal :=
  ((256 : ENNReal) *
      Kakeya.realRpowENN delta (-eta)) *
    Kakeya.realRpowENN input.rawWidth (-parameters.zeta) *
    Kakeya.realRpowENN rawRadius parameters.zeta *
    (wideCoarseEndpointActiveFraction delta eta)⁻¹ *
    (wideCoarseEndpointRescaleFraction
      delta data.width
      (parameters.stripEpsilon * eta / 10))⁻¹ *
    2

/--
Once the explicit raw coefficient is bounded by the target coefficient, the
complete source-strip budget follows mechanically.
-/
lemma wideCoarseEndpoint_sourceBudget_of_rawCoefficient
    {epsilon eta delta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ ambient active : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {input :
      WZ1WideCoarseEndpointLineInput
        (ambient := ambient) (active := active)
        parameters data}
    (hdelta : 0 < delta)
    (normal : Point2) (hnormal : ‖normal‖ = 1)
    (level radius : ℝ)
    (hradius : delta / data.width ≤ radius)
    (hcoefficient :
      let pullback :=
        wideCoarsePhiGPullbackVector
          data.direction data.width normal
      let sourceRadius :=
        (radius + delta / data.width) / ‖pullback‖
      let rawRadius := max delta sourceRadius
      wideCoarseEndpointRawCoefficient
          parameters input rawRadius ≤
        Kakeya.realRpowENN
          (Real.rpow
            (delta / data.width)
            (-(parameters.projectionLambda / 2)) *
            radius)
          parameters.zeta) :
    WZ1WideCoarseEndpointSourceBudget
      (ambient := ambient) (active := active)
      parameters input normal level radius := by
  classical
  let pullback :=
    wideCoarsePhiGPullbackVector
      data.direction data.width normal
  let pullbackNorm := ‖pullback‖
  let sourceNormal := (1 / pullbackNorm) • pullback
  let sourceLevel :=
    (level -
      inner ℝ
        (wideCoarsePhiG
          data.direction data.width data.width_pos
          data.base 0 data.direction_unit 0)
        normal) /
      pullbackNorm
  let sourceRadius :=
    (radius + delta / data.width) / pullbackNorm
  let rawRadius := max delta sourceRadius
  have hradiusNonnegative : 0 ≤ radius :=
    (div_pos hdelta data.width_pos).le.trans hradius
  have hpullback :=
    anisotropic_coarse_strip_card_le_exact_source_strip
      (hwOne := data.width_le_one)
      input.rescale hdelta.le normal hnormal
      level radius hradiusNonnegative
  have hsourceNormal : ‖sourceNormal‖ = 1 := by
    simpa [pullback, pullbackNorm, sourceNormal,
      sourceLevel, sourceRadius] using hpullback.1
  have hraw :=
    wideCoarseEndpoint_selected_strip_card_le_raw_chain
      input hdelta sourceNormal hsourceNormal
      sourceLevel rawRadius (le_max_left _ _)
  have hcoefficient' :
      wideCoarseEndpointRawCoefficient
          parameters input rawRadius ≤
        Kakeya.realRpowENN
          (Real.rpow
            (delta / data.width)
            (-(parameters.projectionLambda / 2)) *
            radius)
          parameters.zeta := by
    simpa [pullback, pullbackNorm, sourceRadius, rawRadius] using
      hcoefficient
  have hscaled :
      wideCoarseEndpointRawCoefficient
            parameters input rawRadius *
          (input.rescale.fiberMultiplicity : ENNReal) *
          input.rescale.coarse.enncard ≤
        (input.rescale.fiberMultiplicity : ENNReal) *
          (Kakeya.realRpowENN
              (Real.rpow
                (delta / data.width)
                (-(parameters.projectionLambda / 2)) *
                radius)
              parameters.zeta *
            input.rescale.coarse.enncard) := by
    calc
      wideCoarseEndpointRawCoefficient
            parameters input rawRadius *
          (input.rescale.fiberMultiplicity : ENNReal) *
          input.rescale.coarse.enncard
          ≤
        Kakeya.realRpowENN
              (Real.rpow
                (delta / data.width)
                (-(parameters.projectionLambda / 2)) *
                radius)
              parameters.zeta *
          (input.rescale.fiberMultiplicity : ENNReal) *
          input.rescale.coarse.enncard := by
            gcongr
      _ =
        (input.rescale.fiberMultiplicity : ENNReal) *
          (Kakeya.realRpowENN
              (Real.rpow
                (delta / data.width)
                (-(parameters.projectionLambda / 2)) *
                radius)
              parameters.zeta *
            input.rescale.coarse.enncard) := by
              ac_rfl
  simpa [WZ1WideCoarseEndpointSourceBudget,
    wideCoarseEndpointRawCoefficient,
    pullback, pullbackNorm, sourceNormal,
    sourceLevel, sourceRadius, rawRadius] using
      hraw.trans hscaled

end Kakeya.Assouad
