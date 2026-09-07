import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalResidueShading

/-!
# Fixed-line localization on the retained whole-cell shading

The selected exact-slice representatives lie within `9 * rho` of one
horizontal global-grain line.  Every retained point lies in the same
side-`sqrt rho` parent as one of those representatives.  The spatial cube
diameter in each coordinate and the one-Lipschitz slope therefore extend the
fixed-line localization to the entire retained carrier, with only an absolute
constant loss.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The complete retained carrier lies in a `14 * sqrt rho` global strip. -/
theorem PureWZ2SourceHorizontalFixedBinResidueShadingData.fixed_line_localizationFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue) :
    ∀ point ∈ retained.shading.union,
      |inner ℝ point
          (globalGrainDirection
            (source.globalGrains.slope
              (point (2 : Fin 3)))) -
        line.lineLevel| ≤
      14 * twoScale.sqrtRequested.1 := by
  let scale := rho
  let root := twoScale.sqrtRequested.1
  have hscale : 0 < scale := line.rho_pos
  have hdeltaScale : delta ≤ scale := by
    dsimp only [scale]
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1
  have hscaleOne : scale ≤ 1 := by
    dsimp only [scale]
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hroot : 0 < root := twoScale.fine.coarse_extremal.delta_pos
  have hscaleRoot : scale ≤ root := by
    have hsqrt : root = Real.sqrt scale := by
      calc
        root = Real.sqrt rho := twoScale.sqrtRequested_eq
        _ = Real.sqrt scale := rfl
    rw [hsqrt]
    nlinarith [Real.sqrt_nonneg scale, Real.sq_sqrt hscale.le]
  intro point hpoint
  have hselected : point ∈ retained.selectedRegion := by
    rw [retained.union_eq] at hpoint
    exact hpoint.2
  rw [retained.selectedRegion_eq] at hselected
  rcases Set.mem_iUnion₂.mp hselected with
    ⟨selectedCell, hselectedCell, hpointCell⟩
  rw [retained.selectedCells_eq] at hselectedCell
  have hselectedData := Finset.mem_filter.mp hselectedCell
  let parent := retained.cellParent selectedCell
  have hparentSelected : parent ∈ residue.selected := hselectedData.2
  have hpointParent :
      point ∈ wz1PaperGridCube root parent :=
    retained.cell_parent selectedCell hselectedData.1 hpointCell
  have hparentInSelection := residue.selected_subset hparentSelected
  rcases selection.selected_hit parent hparentInSelection with
    ⟨cell, hcell, hcellParent⟩
  let representative := line.representative cell
  have hrepresentativeParent :
      representative ∈ wz1PaperGridCube root parent := by
    have hmem := parents.representative_mem_parent cell hcell
    rwa [hcellParent] at hmem
  rw [wz1PaperGridCube_eq_Ico hroot parent] at hpointParent
  rw [wz1PaperGridCube_eq_Ico hroot parent] at hrepresentativeParent
  rcases hpointParent with
    ⟨hpoint0Lower, hpoint0Upper, hpoint1Lower, hpoint1Upper,
      hpoint2Lower, hpoint2Upper⟩
  rcases hrepresentativeParent with
    ⟨hrep0Lower, hrep0Upper, hrep1Lower, hrep1Upper,
      hrep2Lower, hrep2Upper⟩
  have hcoord0 : |point 0 - representative 0| ≤ root := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hcoord1 : |point 1 - representative 1| ≤ root := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hcoord2 : |point 2 - representative 2| ≤ root := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hpointSource : point ∈ source.shading.union :=
    retained.subshading.union_subset hpoint
  have hpointBox := shading_union_subset_axisBox hpointSource
  have hpoint1 : |point 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpointBox.2.1
  have hpointHeight : point (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := by
    have h := hpointBox.2.2
    simpa [Kakeya.Streamlined.axisBox, abs_le] using h
  have hrepresentativeHeight : representative (2 : Fin 3) = line.lineHeight :=
    line.representative_height cell hcell
  have hslopeDifference :
      |source.globalGrains.slope (point (2 : Fin 3)) -
          source.globalGrains.slope line.lineHeight| ≤ root := by
    have hlip :=
      source.globalGrains.slope_lipschitz.dist_le_mul
        (point (2 : Fin 3)) hpointHeight
        line.lineHeight line.lineHeight_mem
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    exact hlip.trans (by
      rw [← hrepresentativeHeight]
      exact hcoord2)
  have hslopeLine :
      |source.globalGrains.slope line.lineHeight| ≤ 3 :=
    source.globalGrains.slope_bound
      line.lineHeight line.lineHeight_mem
  have hprojectionDifference :
      |inner ℝ point
            (globalGrainDirection
              (source.globalGrains.slope
                (point (2 : Fin 3)))) -
          inner ℝ representative
            (globalGrainDirection
              (source.globalGrains.slope line.lineHeight))| ≤
        5 * root := by
    have hformula :
        inner ℝ point
              (globalGrainDirection
                (source.globalGrains.slope
                  (point (2 : Fin 3)))) -
            inner ℝ representative
              (globalGrainDirection
                (source.globalGrains.slope line.lineHeight)) =
          (point 0 - representative 0) +
            source.globalGrains.slope line.lineHeight *
              (point 1 - representative 1) +
            (source.globalGrains.slope (point (2 : Fin 3)) -
              source.globalGrains.slope line.lineHeight) *
              point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      ring
    rw [hformula]
    calc
      |(point 0 - representative 0) +
          source.globalGrains.slope line.lineHeight *
            (point 1 - representative 1) +
          (source.globalGrains.slope (point (2 : Fin 3)) -
            source.globalGrains.slope line.lineHeight) * point 1|
          ≤ |point 0 - representative 0| +
              |source.globalGrains.slope line.lineHeight| *
                |point 1 - representative 1| +
              |source.globalGrains.slope (point (2 : Fin 3)) -
                source.globalGrains.slope line.lineHeight| *
                |point 1| := by
            calc
              _ ≤ |(point 0 - representative 0) +
                    source.globalGrains.slope line.lineHeight *
                      (point 1 - representative 1)| +
                    |(source.globalGrains.slope
                        (point (2 : Fin 3)) -
                      source.globalGrains.slope line.lineHeight) *
                      point 1| := abs_add_le _ _
              _ ≤ (|point 0 - representative 0| +
                    |source.globalGrains.slope line.lineHeight *
                      (point 1 - representative 1)|) +
                    |(source.globalGrains.slope
                        (point (2 : Fin 3)) -
                      source.globalGrains.slope line.lineHeight) *
                      point 1| := by
                    gcongr
                    exact abs_add_le _ _
              _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ root + 3 * root + root * 1 := by gcongr
      _ = 5 * root := by ring
  have hrepresentativeNear :=
    line.heavy_representative_near_line cell hcell
  calc
    |inner ℝ point
          (globalGrainDirection
            (source.globalGrains.slope
              (point (2 : Fin 3)))) -
        line.lineLevel|
        ≤ |inner ℝ point
              (globalGrainDirection
                (source.globalGrains.slope
                  (point (2 : Fin 3)))) -
            inner ℝ representative
              (globalGrainDirection
                (source.globalGrains.slope line.lineHeight))| +
          |inner ℝ representative
              (globalGrainDirection
                (source.globalGrains.slope line.lineHeight)) -
            line.lineLevel| := by
              have := abs_add_le
                (inner ℝ point
                    (globalGrainDirection
                      (source.globalGrains.slope
                        (point (2 : Fin 3)))) -
                  inner ℝ representative
                    (globalGrainDirection
                      (source.globalGrains.slope line.lineHeight)))
                (inner ℝ representative
                    (globalGrainDirection
                      (source.globalGrains.slope line.lineHeight)) -
                  line.lineLevel)
              simpa only [sub_add_sub_cancel] using this
    _ ≤ 5 * root + 9 * delta := by gcongr
    _ ≤ 5 * root + 9 * scale := by gcongr
    _ ≤ 14 * root := by linarith

/-- Every exact horizontal slice has global projection in the same fixed ball. -/
theorem PureWZ2SourceHorizontalFixedBinResidueShadingData.exact_slice_localizationFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue)
    (height : ℝ) :
    scalarProjection
        (globalGrainDirection
          (source.globalGrains.slope height))
        (horizontalSlice retained.shading.union height) ⊆
      Metric.closedBall line.lineLevel
        (14 * twoScale.sqrtRequested.1) := by
  rintro value ⟨point, hpoint, rfl⟩
  have hbound := retained.fixed_line_localizationFixedBin point hpoint.1
  rw [hpoint.2] at hbound
  simpa [Metric.mem_closedBall, Real.dist_eq] using hbound

/-- Compatibility name for maximal-bin fixed-line localization. -/
theorem PureWZ2SourceHorizontalResidueShadingData.fixed_line_localization
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (retained : PureWZ2SourceHorizontalResidueShadingData residue) :
    ∀ point ∈ retained.shading.union,
      |inner ℝ point
          (globalGrainDirection
            (source.globalGrains.slope (point (2 : Fin 3)))) -
        line.lineLevel| ≤ 14 * twoScale.sqrtRequested.1 :=
  retained.fixed_line_localizationFixedBin

/-- Compatibility name for maximal-bin exact-slice localization. -/
theorem PureWZ2SourceHorizontalResidueShadingData.exact_slice_localization
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (retained : PureWZ2SourceHorizontalResidueShadingData residue)
    (height : ℝ) :
    scalarProjection
        (globalGrainDirection (source.globalGrains.slope height))
        (horizontalSlice retained.shading.union height) ⊆
      Metric.closedBall line.lineLevel (14 * twoScale.sqrtRequested.1) :=
  retained.exact_slice_localizationFixedBin height

end Kakeya.Assouad
