import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellNormalizationStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.CoveringNumber1D
import MyLeanRepo.Kakeya.Assouad.WZ1.WideSnappedSourceData
import MyLeanRepo.Kakeya.Assouad.WZ1.WideSnappedTransportArithmetic

/-!
PDF Proposition 8.9 wide branch: control the snapped-dot perturbation for
the coherent normalized graph and transport its covering conclusion to the
actual source graph.

This implication explicitly consumes the coarse, fixed-cell, and normalized
core producers; none of those dependent quantifiers may be discharged
vacuously.  Use the two-sided fixed comparison between
`effectiveWidth * scale` and `delta`, then pay the one-dimensional
fixed-scale covering loss caused by `sourceError`.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- Transport one normalized covering bound through the snapped-dot error. -/
lemma wide_snapped_transport_from_core
    {delta epsilon eta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {coarse :
      WZ1Proposition8_9WideCoarseData
        delta epsilon eta parameters F G₁ G₂ H data}
    {fixed : WZ1Proposition8_9WideFixedCellData coarse}
    (core : WZ1Proposition8_9WideNormalizedCoreData fixed)
    (source : WZ1WideSnappedSourceData core)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (heta : 0 < eta)
    (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon < 1)
    (hetaSmall : eta ≤ epsilon / 20)
    (hwidth :
      Real.rpow delta (1 - epsilon / 10) < data.width)
    (hscaleSmall :
      Real.rpow delta (epsilon ^ 2 / 20) ≤
        1 / ((3840201 : ℝ) *
          Real.rpow 38416 (1 - epsilon)))
    (hthinSmall :
      Real.rpow delta (epsilon / 20) ≤ 1 / 25)
    (hcover :
      Kakeya.realRpowENN core.scale (epsilon / 2 - 1) ≤
        (↑(Metric.externalCoveringNumber
          (Real.toNNReal core.scale)
          (wz1DotDifferenceSet core.normalizedH)) :
          ENNReal)) :
    WZ1StripLocalizationLongProjection
      delta epsilon eta H := by
  set width := core.effectiveWidth with hwidthDef
  set scale := core.scale with hscaleDef
  set error := core.sourceError with herrorDef
  set scaledRadius := width * scale with hscaledRadiusDef
  set transferRadius := delta + error with htransferRadiusDef
  set radius := 2 * width + error with hradiusDef
  let coveringLoss : ℕ := 3840201
  let radiusLoss : ℝ := 38416

  have hwidthPos : 0 < width := core.effectiveWidth_pos
  have hscalePos : 0 < scale := core.scale_pos
  have hscaleOne : scale ≤ 1 := by
    have hscale :
        scale = core.scaleFactor * coarse.scale :=
      core.scale_eq
    rw [hscale]
    have hcoarseOne : coarse.scale ≤ 1 := by
      rw [coarse.scale_eq]
      exact
        (div_le_one data.width_pos).mpr
          data.delta_le_width
    have hfactorNonneg : 0 ≤ core.scaleFactor :=
      core.scaleFactor_pos.le
    nlinarith [core.scaleFactor_le_one]
  have herrorNonneg : 0 ≤ error :=
    core.sourceError_nonneg
  have hscaledRadiusPos : 0 < scaledRadius :=
    mul_pos hwidthPos hscalePos

  have herrorBound :
      error ≤ 4800 * width * scale := by
    have hsource :
        error ≤ 1200 * width * coarse.scale :=
      core.sourceError_bound
    have hcoarse :
        coarse.scale = scale / core.scaleFactor := by
      have hscale :
          scale = core.scaleFactor * coarse.scale :=
        core.scale_eq
      field_simp [core.scaleFactor_pos.ne'] at hscale ⊢
      linarith
    rw [hcoarse] at hsource
    have hquotient :
        scale / core.scaleFactor ≤ 4 * scale := by
      have hcompare :
          scale / core.scaleFactor ≤
            scale / (1 / 4 : ℝ) := by
        exact
          div_le_div_of_nonneg_left
            hscalePos.le (by norm_num)
            core.scaleFactor_lower
      have hfour :
          scale / (1 / 4 : ℝ) = 4 * scale := by
        ring
      linarith [core.scaleFactor_lower]
    nlinarith
  have herrorDelta : error ≤ 19200 * delta := by
    calc
      error ≤ 4800 * width * scale := herrorBound
      _ = 4800 * (width * scale) := by ring
      _ ≤ 4800 * (4 * delta) := by
        exact
          mul_le_mul_of_nonneg_left
            core.effectiveWidth_scale_upper
            (by norm_num)
      _ = 19200 * delta := by ring
  have htransferRadius :
      transferRadius ≤ 19201 * delta := by
    linarith
  have hscaledRadiusLower :
      delta / 100 ≤ scaledRadius :=
    core.effectiveWidth_scale_lower
  have hcoveringRatio :
      2 * transferRadius / scaledRadius ≤ 3840200 := by
    calc
      2 * transferRadius / scaledRadius ≤
          2 * (19201 * delta) / scaledRadius := by
        gcongr
      _ = 38402 * delta / scaledRadius := by ring
      _ ≤ 38402 * delta / (delta / 100) := by
        gcongr
      _ = 3840200 := by
        field_simp [hdelta.ne']
        ring

  let normalizedValues :=
    wz1DotDifferenceSet core.normalizedH
  let scaledValues :=
    (fun value : ℝ => width * value) '' normalizedValues
  let sourceValues :=
    wz1DotDifferenceSet source.sourceH

  have happroximation :
      ∀ value ∈ scaledValues,
        ∃ sourceValue ∈ sourceValues,
          dist value sourceValue ≤ error := by
    intro value hvalue
    exact source.approximation value hvalue

  have hscaling :
      Metric.externalCoveringNumber
          (Real.toNNReal scaledRadius) scaledValues =
        Metric.externalCoveringNumber
          (Real.toNNReal scale) normalizedValues :=
    real_covering_number_scaling
      hwidthPos hscalePos.le
  have hcoverScaled :
      Kakeya.realRpowENN scale (epsilon / 2 - 1) ≤
        (↑(Metric.externalCoveringNumber
          (Real.toNNReal scaledRadius) scaledValues) :
          ENNReal) := by
    rw [hscaling]
    exact hcover
  have htransfer :
      Metric.externalCoveringNumber
          (Real.toNNReal transferRadius) scaledValues ≤
        Metric.externalCoveringNumber
          (Real.toNNReal delta) sourceValues := by
    apply
      external_covering_number_approx_transfer1D
        hdelta herrorNonneg
    exact happroximation

  have hcoarsen :
      Kakeya.realRpowENN scale (epsilon / 2 - 1) /
          (coveringLoss : ENNReal) ≤
        (↑(Metric.externalCoveringNumber
          (Real.toNNReal transferRadius) scaledValues) :
          ENNReal) := by
    by_cases hcase : scaledRadius ≤ transferRadius
    · let cellCount : ℕ :=
        Nat.floor
          (2 * transferRadius / scaledRadius) + 1
      have hcellCount : cellCount ≤ coveringLoss := by
        have hfloor :
            Nat.floor
                (2 * transferRadius / scaledRadius) ≤
              Nat.floor (3840200 : ℝ) :=
          Nat.floor_mono hcoveringRatio
        have hfloorConstant :
            Nat.floor (3840200 : ℝ) = 3840200 := by
          simp
        rw [hfloorConstant] at hfloor
        simp [cellCount, coveringLoss] at *
        omega
      have hcoarseNat :
          Metric.externalCoveringNumber
              (Real.toNNReal scaledRadius) scaledValues ≤
            (cellCount : ℕ∞) *
              Metric.externalCoveringNumber
                (Real.toNNReal transferRadius)
                scaledValues :=
        external_covering_number_coarsen1D
          hscaledRadiusPos hcase
      have hcellCountENN :
          (cellCount : ENNReal) ≤
            (coveringLoss : ENNReal) := by
        exact_mod_cast hcellCount
      have hcoarseENN :
          (Metric.externalCoveringNumber
              (Real.toNNReal scaledRadius) scaledValues :
              ENNReal) ≤
            (cellCount : ENNReal) *
              (Metric.externalCoveringNumber
                (Real.toNNReal transferRadius)
                scaledValues : ENNReal) := by
        exact_mod_cast hcoarseNat
      have hcoarseLoss :
          (Metric.externalCoveringNumber
              (Real.toNNReal scaledRadius) scaledValues :
              ENNReal) ≤
            (coveringLoss : ENNReal) *
              (Metric.externalCoveringNumber
                (Real.toNNReal transferRadius)
                scaledValues : ENNReal) := by
        calc
          _ ≤
              (cellCount : ENNReal) *
                (Metric.externalCoveringNumber
                  (Real.toNNReal transferRadius)
                  scaledValues : ENNReal) :=
            hcoarseENN
          _ ≤
              (coveringLoss : ENNReal) *
                (Metric.externalCoveringNumber
                  (Real.toNNReal transferRadius)
                  scaledValues : ENNReal) := by
            gcongr
      have hlossZero :
          (coveringLoss : ENNReal) ≠ 0 := by
        positivity
      have hlossTop :
          (coveringLoss : ENNReal) ≠ ⊤ := by
        simp
      have hdivision :
          (Metric.externalCoveringNumber
              (Real.toNNReal scaledRadius) scaledValues :
              ENNReal) /
                (coveringLoss : ENNReal) ≤
            (Metric.externalCoveringNumber
              (Real.toNNReal transferRadius)
              scaledValues : ENNReal) := by
        apply
          (ENNReal.div_le_iff hlossZero hlossTop).2
        simpa [mul_comm] using hcoarseLoss
      calc
        Kakeya.realRpowENN scale (epsilon / 2 - 1) /
              (coveringLoss : ENNReal) ≤
            (Metric.externalCoveringNumber
              (Real.toNNReal scaledRadius) scaledValues :
              ENNReal) /
                (coveringLoss : ENNReal) := by
          gcongr
        _ ≤
            (Metric.externalCoveringNumber
              (Real.toNNReal transferRadius)
              scaledValues : ENNReal) :=
          hdivision
    · have hstrict : transferRadius < scaledRadius := by
        linarith
      have hmonotone :
          (Metric.externalCoveringNumber
              (Real.toNNReal scaledRadius) scaledValues :
              ENNReal) ≤
            (Metric.externalCoveringNumber
              (Real.toNNReal transferRadius)
              scaledValues : ENNReal) := by
        exact_mod_cast
          Metric.externalCoveringNumber_anti
            (Real.toNNReal_le_toNNReal hstrict.le)
      have hdivision :
          Kakeya.realRpowENN scale (epsilon / 2 - 1) /
              (coveringLoss : ENNReal) ≤
            Kakeya.realRpowENN scale (epsilon / 2 - 1) := by
        apply
          (ENNReal.div_le_iff
            (by positivity :
              (coveringLoss : ENNReal) ≠ 0)
            (by simp :
              (coveringLoss : ENNReal) ≠ ⊤)).2
        calc
          Kakeya.realRpowENN scale (epsilon / 2 - 1) =
              Kakeya.realRpowENN scale
                (epsilon / 2 - 1) * 1 := by
            simp
          _ ≤
              Kakeya.realRpowENN scale
                (epsilon / 2 - 1) *
                  (coveringLoss : ENNReal) := by
            gcongr
            norm_num [coveringLoss]
      calc
        Kakeya.realRpowENN scale (epsilon / 2 - 1) /
              (coveringLoss : ENNReal) ≤
            Kakeya.realRpowENN scale (epsilon / 2 - 1) :=
          hdivision
        _ ≤
            (Metric.externalCoveringNumber
              (Real.toNNReal scaledRadius) scaledValues :
              ENNReal) :=
          hcoverScaled
        _ ≤
            (Metric.externalCoveringNumber
              (Real.toNNReal transferRadius)
              scaledValues : ENNReal) :=
          hmonotone

  have hcoverSource :
      Kakeya.realRpowENN scale (epsilon / 2 - 1) /
          (coveringLoss : ENNReal) ≤
        (↑(Metric.externalCoveringNumber
          (Real.toNNReal delta) sourceValues) : ENNReal) := by
    calc
      _ ≤
          (Metric.externalCoveringNumber
            (Real.toNNReal transferRadius)
            scaledValues : ENNReal) :=
        hcoarsen
      _ ≤
          (Metric.externalCoveringNumber
            (Real.toNNReal delta) sourceValues :
            ENNReal) := by
        exact_mod_cast htransfer

  have hradiusPos : 0 < radius := by positivity
  have hsourceBall :
      ∀ value ∈ sourceValues, |value| ≤ radius := by
    intro value hvalue
    exact source.source_dot_bound value hvalue
  have hsourceSubsetBall :
      sourceValues ⊆ Metric.closedBall (0 : ℝ) radius := by
    intro value hvalue
    have hbound : |value| ≤ radius :=
      hsourceBall value hvalue
    simpa [Metric.mem_closedBall, Real.dist_eq] using hbound
  have hsourceDotSubset :
      sourceValues ⊆ wz1DotDifferenceSet H := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with
      ⟨edge, hedge, rfl⟩
    exact
      Finset.mem_image.mpr
        ⟨edge, source.sourceH_subset hedge, rfl⟩
  have hsourceIntersection :
      sourceValues ⊆
        wz1DotDifferenceSet H ∩
          Metric.closedBall (0 : ℝ) radius := by
    intro value hvalue
    exact
      ⟨hsourceDotSubset hvalue,
        hsourceSubsetBall hvalue⟩
  have hcoverOriginal :
      Kakeya.realRpowENN scale (epsilon / 2 - 1) /
          (coveringLoss : ENNReal) ≤
        (↑(Metric.externalCoveringNumber
          (Real.toNNReal delta)
          (wz1DotDifferenceSet H ∩
            Metric.closedBall (0 : ℝ) radius)) :
          ENNReal) := by
    calc
      _ ≤
          (Metric.externalCoveringNumber
            (Real.toNNReal delta) sourceValues :
            ENNReal) :=
        hcoverSource
      _ ≤
          (Metric.externalCoveringNumber
            (Real.toNNReal delta)
            (wz1DotDifferenceSet H ∩
              Metric.closedBall (0 : ℝ) radius) :
            ENNReal) := by
        exact_mod_cast
          Metric.externalCoveringNumber_mono_set
            hsourceIntersection

  have hradiusRatio :
      2 * radius / delta ≤ radiusLoss / scale := by
    simpa [radiusLoss] using
      wide_snapped_radius_ratio_bound
        hdelta hwidthPos hscalePos hscaleOne herrorBound
        core.effectiveWidth_scale_upper rfl
  have hscaleUpper :
      scale ≤ Real.rpow delta (epsilon / 10) := by
    have hcoarse :
        coarse.scale < Real.rpow delta (epsilon / 10) := by
      rw [coarse.scale_eq]
      have hdenominatorPos :
          0 < Real.rpow delta (1 - epsilon / 10) :=
        Real.rpow_pos_of_pos hdelta _
      have hdivision :
          delta / data.width <
            delta /
              Real.rpow delta (1 - epsilon / 10) := by
        gcongr
      have hequality :
          delta /
              Real.rpow delta (1 - epsilon / 10) =
            Real.rpow delta (epsilon / 10) := by
        have hsub :=
          Real.rpow_sub hdelta 1 (1 - epsilon / 10)
        calc
          delta /
                Real.rpow delta (1 - epsilon / 10) =
              Real.rpow delta 1 /
                Real.rpow delta (1 - epsilon / 10) := by
            simp
          _ =
              Real.rpow delta
                (1 - (1 - epsilon / 10)) :=
            hsub.symm
          _ = Real.rpow delta (epsilon / 10) := by
            congr 1
            ring
      linarith
    calc
      scale = core.scaleFactor * coarse.scale :=
        core.scale_eq
      _ ≤ 1 * coarse.scale := by
        exact
          mul_le_mul_of_nonneg_right
            core.scaleFactor_le_one coarse.scale_pos.le
      _ = coarse.scale := by ring
      _ ≤ Real.rpow delta (epsilon / 10) :=
        hcoarse.le
  have hexponent :
      Kakeya.realRpowENN
          (radiusLoss / scale) (1 - epsilon) ≤
        Kakeya.realRpowENN scale (epsilon / 2 - 1) /
          (coveringLoss : ENNReal) := by
    simpa [radiusLoss, coveringLoss] using
      wide_snapped_covering_exponent_bound
        hdelta hscalePos hepsilon
        (show (0 : ℝ) < 38416 by norm_num)
        (show (0 : ℕ) < 3840201 by norm_num)
        hscaleUpper hscaleSmall
  have hradiusExponent :
      Kakeya.realRpowENN
          (2 * radius / delta) (1 - epsilon) ≤
        Kakeya.realRpowENN
          (radiusLoss / scale) (1 - epsilon) := by
    have hleft : 0 ≤ 2 * radius / delta := by positivity
    have hexponentNonneg : 0 ≤ 1 - epsilon := by
      linarith
    have hreal :
        Real.rpow (2 * radius / delta) (1 - epsilon) ≤
          Real.rpow (radiusLoss / scale)
            (1 - epsilon) :=
      Real.rpow_le_rpow
        hleft hradiusRatio hexponentNonneg
    simpa [Kakeya.realRpowENN] using
      ENNReal.ofReal_mono hreal
  have hcoverFinal :
      Kakeya.realRpowENN
          (2 * radius / delta) (1 - epsilon) ≤
        (↑(Metric.externalCoveringNumber
          (Real.toNNReal delta)
          (wz1DotDifferenceSet H ∩
            Metric.closedBall (0 : ℝ) radius)) :
          ENNReal) := by
    calc
      _ ≤
          Kakeya.realRpowENN
            (radiusLoss / scale) (1 - epsilon) :=
        hradiusExponent
      _ ≤
          Kakeya.realRpowENN scale (epsilon / 2 - 1) /
            (coveringLoss : ENNReal) :=
        hexponent
      _ ≤ _ := hcoverOriginal

  have hthinPower :
      Real.rpow delta (1 - eta) ≤
        Real.rpow delta (1 - epsilon / 10) / 25 := by
    have hexponent :
        1 - epsilon / 10 ≤ 1 - eta := by
      linarith
    have hsmallExponent :
        epsilon / 20 ≤ epsilon / 10 - eta := by
      linarith
    have hsmall :
        Real.rpow delta (epsilon / 10 - eta) ≤
          1 / 25 := by
      exact
        (Real.rpow_le_rpow_of_exponent_ge
          hdelta hdeltaOne hsmallExponent).trans
          hthinSmall
    have hfactor :
        Real.rpow delta (1 - eta) =
          Real.rpow delta (1 - epsilon / 10) *
            Real.rpow delta (epsilon / 10 - eta) := by
      have hsum :
          1 - eta =
            (1 - epsilon / 10) +
              (epsilon / 10 - eta) := by
        ring
      rw [hsum]
      exact Real.rpow_add hdelta _ _
    rw [hfactor]
    have hnonneg :
        0 ≤ Real.rpow delta (1 - epsilon / 10) :=
      Real.rpow_nonneg hdelta.le _
    nlinarith
  have hthinRadius :
      Real.rpow delta (1 - epsilon / 10) / 25 <
        2 * radius := by
    have hwidthLower : data.width / 100 ≤ width :=
      core.effectiveWidth_lower
    have hradiusLower : 4 * width ≤ 2 * radius := by
      rw [hradiusDef]
      linarith
    have hwidthCompare :
        data.width / 25 ≤ 4 * width := by
      linarith
    have hpowerCompare :
        Real.rpow delta (1 - epsilon / 10) / 25 <
          data.width / 25 := by
      gcongr
    linarith
  have hthin :
      Real.rpow delta (-eta) * delta ≤ 2 * radius := by
    have hpower :
        Real.rpow delta (-eta) * delta =
          Real.rpow delta (1 - eta) := by
      calc
        Real.rpow delta (-eta) * delta =
            Real.rpow delta (-eta) *
              Real.rpow delta 1 := by
          simp
        _ = Real.rpow delta (-eta + 1) :=
          (Real.rpow_add hdelta _ _).symm
        _ = Real.rpow delta (1 - eta) := by
          congr 1
          ring
    rw [hpower]
    linarith [hthinPower, hthinRadius]

  exact
    ⟨delta, 0, radius, by linarith, hdeltaOne,
      hradiusPos, hthin, hcoverFinal⟩

/--
Assemble the repaired wide snapped-covering producer from the coarse,
fixed-cell, and normalized-core producers.
-/
theorem wz1_wide_snapped_covering_transport :
    WZ1Proposition8_9WideSnappedCoveringTransportStatement := by
  intro hCoarseProducer hFixedProducer hCoreProducer
  intro hHypergraph hRescaling
  intro epsilon parameters hepsilon hepsilonOne
  rcases
      hCoarseProducer hHypergraph hRescaling
        epsilon parameters hepsilon hepsilonOne with
    ⟨coarseEtaCap, hcoarseEtaCap, hCoarseAt⟩
  rcases
      hFixedProducer epsilon parameters hepsilon hepsilonOne with
    ⟨fixedEtaCap, hfixedEtaCap, hFixedAt⟩
  rcases
      hCoreProducer epsilon parameters hepsilon hepsilonOne with
    ⟨coreEtaCap, hcoreEtaCap, hCoreAt⟩
  let etaCap :=
    min coarseEtaCap
      (min fixedEtaCap (min coreEtaCap (epsilon / 20)))
  have hetaCap : 0 < etaCap := by
    have hepsilonTwenty : 0 < epsilon / 20 := by
      positivity
    positivity
  refine ⟨etaCap, hetaCap, fun eta heta hetaBound => ?_⟩
  have hetaSmall : eta ≤ epsilon / 20 := by
    exact hetaBound.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  have hetaCoarse : eta ≤ coarseEtaCap :=
    hetaBound.trans (min_le_left _ _)
  have hetaFixed : eta ≤ fixedEtaCap :=
    hetaBound.trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hetaCore : eta ≤ coreEtaCap :=
    hetaBound.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  rcases hCoarseAt eta heta hetaCoarse with
    ⟨coarseScale, hcoarseScale,
      hcoarseScaleOne, hCoarseData⟩
  rcases hFixedAt eta heta hetaFixed with
    ⟨fixedScale, hfixedScale,
      hfixedScaleOne, hFixedData⟩
  rcases hCoreAt eta heta hetaCore with
    ⟨coreScale, hcoreScale, hcoreScaleOne, hCoreData⟩
  rcases
      wide_snapped_transport_small_scales
        epsilon hepsilon hepsilonOne with
    ⟨transportScale, htransportScale,
      htransportScaleOne, hTransportSmall⟩
  let delta₀ :=
    min coarseScale
      (min fixedScale (min coreScale transportScale))
  have hdelta₀ : 0 < delta₀ := by positivity
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans hcoarseScaleOne
  refine
    ⟨delta₀, hdelta₀, hdelta₀One,
      fun {delta F G₁ G₂ H}
        hdelta hdeltaBound data hwidth => ?_⟩
  have hdeltaOne : delta ≤ 1 :=
    hdeltaBound.trans hdelta₀One
  have hdeltaTransport : delta ≤ transportScale :=
    hdeltaBound.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  have hsmall :=
    hTransportSmall delta hdelta hdeltaTransport
  have hdeltaCoarse : delta ≤ coarseScale :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaFixed : delta ≤ fixedScale :=
    hdeltaBound.trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaCore : delta ≤ coreScale :=
    hdeltaBound.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  rcases
      hCoarseData hdelta hdeltaCoarse data hwidth with
    ⟨coarse⟩
  rcases
      hFixedData hdelta hdeltaFixed data hwidth coarse with
    ⟨fixed⟩
  rcases
      hCoreData hdelta hdeltaCore data hwidth coarse fixed with
    ⟨core⟩
  rcases wz1_wide_snapped_source_data core with ⟨source⟩
  let normalizedData :
      WZ1Proposition8_9WideNormalizedData
        delta epsilon eta parameters F G₁ G₂ H :=
    { scale := core.scale
      scale_pos := core.scale_pos
      scale_le_projectionDelta₀ :=
        core.scale_le_projectionDelta₀
      normalizedF := core.normalizedF
      normalizedG₁ := core.normalizedG₁
      normalizedG₂ := core.normalizedG₂
      normalizedH := core.normalizedH
      normalizedF_nonempty := core.normalizedF_nonempty
      normalizedG₁_nonempty := core.normalizedG₁_nonempty
      normalizedG₂_nonempty := core.normalizedG₂_nonempty
      normalizedF_ball := core.normalizedF_ball
      normalizedG₁_ball := core.normalizedG₁_ball
      normalizedG₂_ball := core.normalizedG₂_ball
      normalizedF_separated := core.normalizedF_separated
      normalizedG₁_separated := core.normalizedG₁_separated
      normalizedG₂_separated := core.normalizedG₂_separated
      normalizedF_frostman := core.normalizedF_frostman
      normalizedG₁_frostman := core.normalizedG₁_frostman
      normalizedG₂_frostman := core.normalizedG₂_frostman
      standardSeparation := core.standardSeparation
      first_line_nonconcentration :=
        core.first_line_nonconcentration
      second_line_nonconcentration :=
        core.second_line_nonconcentration
      uniform := core.uniform
      transport := fun hcover =>
        wide_snapped_transport_from_core
          core source hdelta hdeltaOne heta
          hepsilon hepsilonOne hetaSmall hwidth
          hsmall.1 hsmall.2 hcover }
  exact ⟨normalizedData⟩

end Kakeya.Assouad
