import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointLineSplitStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseExactStripPullback

/-!
# Common exact-source-strip budget for wide endpoint line synthesis

Every normal regime uses the same final mechanical step: pull one coarse
strip back exactly, enlarge its source radius to at least `delta`, bound the
resulting selected-source strip, and cancel the positive balanced fiber
multiplicity.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- A budget on the enlarged exact source strip sufficient for one coarse
normal bound. -/
def WZ1WideCoarseEndpointSourceBudget
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
    (normal : Point2) (level radius : ℝ) : Prop :=
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
  ((input.rescale.selected.filter fun point =>
      |inner ℝ point sourceNormal - sourceLevel| ≤
        rawRadius).card : ENNReal) ≤
    (input.rescale.fiberMultiplicity : ENNReal) *
      (Kakeya.realRpowENN
          (Real.rpow
            (delta / data.width)
            (-(parameters.projectionLambda / 2)) *
            radius)
          parameters.zeta *
        input.rescale.coarse.enncard)

/--
If the target strip coefficient is already at least two, the balanced-fiber
upper count proves the source budget without any geometric estimate.
-/
lemma wideCoarseEndpoint_sourceBudget_of_target_ge_two
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
    {normal : Point2} {level radius : ℝ}
    (htarget :
      (2 : ENNReal) ≤
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
  have hfilter :
      ((input.rescale.selected.filter fun point =>
        |inner ℝ point sourceNormal - sourceLevel| ≤
          rawRadius).card : ENNReal) ≤
        input.rescale.selected.enncard := by
    change
      ((input.rescale.selected.filter fun point =>
        |inner ℝ point sourceNormal - sourceLevel| ≤
          rawRadius).card : ENNReal) ≤
        (input.rescale.selected.card : ENNReal)
    exact_mod_cast
      Finset.card_le_card (Finset.filter_subset _ _)
  have hselected :=
    anisotropic_selected_card_le_two_fiber_coarse
      input.rescale
  have hscaled :
      (2 : ENNReal) *
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
      (2 : ENNReal) *
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
    pullback, pullbackNorm, sourceNormal,
    sourceLevel, sourceRadius, rawRadius] using
      hfilter.trans (hselected.trans hscaled)

/-- Exact pullback plus a source-strip budget imply the requested coarse
normal estimate. -/
lemma wideCoarseEndpoint_sourceBudget_normalBound
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
    (hbudget :
      WZ1WideCoarseEndpointSourceBudget
        (ambient := ambient) (active := active)
        parameters input normal level radius) :
    ((input.rescale.coarse.filter fun point =>
      |inner ℝ point normal - level| ≤ radius).card : ENNReal) ≤
      Kakeya.realRpowENN
          (Real.rpow
            (delta / data.width)
            (-(parameters.projectionLambda / 2)) *
            radius)
          parameters.zeta *
        input.rescale.coarse.enncard := by
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
  have hexact :
      (input.rescale.fiberMultiplicity : ENNReal) *
          ((input.rescale.coarse.filter fun point =>
            |inner ℝ point normal - level| ≤ radius).card :
              ENNReal) ≤
        ((input.rescale.selected.filter fun point =>
          |inner ℝ point sourceNormal - sourceLevel| ≤
            sourceRadius).card : ENNReal) := by
    simpa [pullback, pullbackNorm, sourceNormal,
      sourceLevel, sourceRadius] using hpullback.2.2
  have henlarge :
      ((input.rescale.selected.filter fun point =>
          |inner ℝ point sourceNormal - sourceLevel| ≤
            sourceRadius).card : ENNReal) ≤
        ((input.rescale.selected.filter fun point =>
          |inner ℝ point sourceNormal - sourceLevel| ≤
            rawRadius).card : ENNReal) := by
    exact_mod_cast
      Finset.card_le_card
        (show
          input.rescale.selected.filter (fun point =>
              |inner ℝ point sourceNormal - sourceLevel| ≤
                sourceRadius) ⊆
            input.rescale.selected.filter (fun point =>
              |inner ℝ point sourceNormal - sourceLevel| ≤
                rawRadius) by
          intro point hpoint
          have hpointData := Finset.mem_filter.mp hpoint
          exact
            Finset.mem_filter.mpr
              ⟨hpointData.1,
                hpointData.2.trans
                  (le_max_right delta sourceRadius)⟩)
  have hbudget' :
      ((input.rescale.selected.filter fun point =>
          |inner ℝ point sourceNormal - sourceLevel| ≤
            rawRadius).card : ENNReal) ≤
        (input.rescale.fiberMultiplicity : ENNReal) *
          (Kakeya.realRpowENN
              (Real.rpow
                (delta / data.width)
                (-(parameters.projectionLambda / 2)) *
                radius)
              parameters.zeta *
            input.rescale.coarse.enncard) := by
    simpa [WZ1WideCoarseEndpointSourceBudget,
      pullback, pullbackNorm, sourceNormal,
      sourceLevel, sourceRadius, rawRadius] using hbudget
  have hwithMultiplicity :
      (input.rescale.fiberMultiplicity : ENNReal) *
          ((input.rescale.coarse.filter fun point =>
            |inner ℝ point normal - level| ≤ radius).card :
              ENNReal) ≤
        (input.rescale.fiberMultiplicity : ENNReal) *
          (Kakeya.realRpowENN
              (Real.rpow
                (delta / data.width)
                (-(parameters.projectionLambda / 2)) *
                radius)
              parameters.zeta *
            input.rescale.coarse.enncard) :=
    hexact.trans (henlarge.trans hbudget')
  have hmultiplicityZero :
      (input.rescale.fiberMultiplicity : ENNReal) ≠ 0 := by
    exact_mod_cast
      (Nat.ne_of_gt input.rescale.fiberMultiplicity_pos)
  have hmultiplicityTop :
      (input.rescale.fiberMultiplicity : ENNReal) ≠ ⊤ := by
    exact ENNReal.natCast_ne_top _
  have hcancel :=
    mul_le_mul_left'
      hwithMultiplicity
        (input.rescale.fiberMultiplicity : ENNReal)⁻¹
  simpa only [← mul_assoc,
    ENNReal.inv_mul_cancel hmultiplicityZero hmultiplicityTop,
    one_mul] using hcancel

end Kakeya.Assouad
