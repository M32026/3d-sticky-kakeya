import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularRestrictedParentSelection

/-!
# Exact outer-popular carrier on the post-line selected parents

This is a common spatial restriction of the pre-line parent-weight carrier.
It retains only genuine outer-popular points.  In particular, it is not the
complete sticky shading inside the selected parents.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalPopularSelectedParentCarrierData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
    (selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents) where
  shading : WZ1PaperTubeShading source.family
  carrier_eq : ∀ index, shading.carrier index =
    restricted.shading.carrier index ∩ selection.selectedRegion
  subshading_restricted :
    PureWZ2PaperIsSubshading shading restricted.shading
  subshading_source : PureWZ2PaperIsSubshading shading source.shading
  union_eq : shading.union =
    restricted.shading.union ∩ selection.selectedRegion
  union_eq_popular : shading.union =
    carrier.shading.union ∩ selection.selectedRegion
  volume_eq : volume shading.union =
    ∑ parent ∈ selection.selected,
      pureWZ2TerminalPopularParentWeight carrier parent
  volume_pos : 0 < volume shading.union
  height_region : shading.union ⊆ heightData.popular.heightRegion
  constant_multiplicity : shading.HasConstantMultiplicity
    terminalSource.multiplicity (2 * terminalSource.multiplicity)
  union_height : ∀ point ∈ shading.union,
    point (2 : Fin 3) ∈ Set.Ico
      ((selection.commonParentHeight : ℝ) * terminal.sqrtRequested.1)
      (((selection.commonParentHeight : ℝ) + 1) *
        terminal.sqrtRequested.1)

noncomputable def PureWZ2TerminalPopularRestrictedParentSelectionData.toCarrier
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
    (selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents) :
    PureWZ2TerminalPopularSelectedParentCarrierData selection := by
  let shading : WZ1PaperTubeShading source.family :=
    { carrier := fun index =>
        restricted.shading.carrier index ∩ selection.selectedRegion
      measurable_carrier := fun index =>
        (restricted.shading.measurable_carrier index).inter
          selection.selectedRegion_measurable
      subset_body := fun index => Set.inter_subset_left.trans
        (restricted.shading.subset_body index) }
  have hunion : shading.union =
      restricted.shading.union ∩ selection.selectedRegion := by
    ext point
    constructor
    · rintro ⟨index, hrestricted, hregion⟩
      exact ⟨⟨index, hrestricted⟩, hregion⟩
    · rintro ⟨⟨index, hrestricted⟩, hregion⟩
      exact ⟨index, hrestricted, hregion⟩
  have hselectedRegionSubset : selection.selectedRegion ⊆
      weightClass.selectedRegion := by
    intro point hpoint
    rw [selection.selectedRegion_eq] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨parent, hparent, hpointParent⟩
    rw [weightClass.selectedRegion_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨parent, selection.selected_subset_weightClass hparent, hpointParent⟩
  have hunionPopular : shading.union =
      carrier.shading.union ∩ selection.selectedRegion := by
    rw [hunion, restricted.union_eq]
    ext point
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨hcarrier, _hweightRegion⟩, hselectedRegion⟩
      exact ⟨hcarrier, hselectedRegion⟩
    · rintro ⟨hcarrier, hselectedRegion⟩
      exact ⟨⟨hcarrier, hselectedRegionSubset hselectedRegion⟩, hselectedRegion⟩
  have hsubRestricted :
      PureWZ2PaperIsSubshading shading restricted.shading :=
    fun _ => Set.inter_subset_left
  have hsubSource : PureWZ2PaperIsSubshading shading source.shading :=
    fun index => (hsubRestricted index).trans
      (restricted.subshading_source index)
  have hconstant : shading.HasConstantMultiplicity
      terminalSource.multiplicity (2 * terminalSource.multiplicity) := by
    intro point hpoint
    have hmultiplicity : shading.pointMultiplicity point =
        restricted.shading.pointMultiplicity point := by
      unfold Kakeya.Streamlined.Shading.pointMultiplicity
      congr 1
      ext index
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.1
      · intro hrestricted
        have hregion : point ∈ selection.selectedRegion := by
          have hset : point ∈ restricted.shading.union ∩
              selection.selectedRegion := by
            rw [← hunion]
            exact hpoint
          exact hset.2
        exact ⟨hrestricted, hregion⟩
    rw [hmultiplicity]
    exact restricted.constant_multiplicity point
      (hsubRestricted.union_subset hpoint)
  have hvolume : volume shading.union =
      ∑ parent ∈ selection.selected,
        pureWZ2TerminalPopularParentWeight carrier parent := by
    rw [hunionPopular, ← selection.selected_weight_eq]
  have hroot : 0 < terminal.sqrtRequested.1 :=
    terminal.sticky.coarse_extremal.delta_pos
  exact {
    shading := shading
    carrier_eq := fun _ => rfl
    subshading_restricted := hsubRestricted
    subshading_source := hsubSource
    union_eq := hunion
    union_eq_popular := hunionPopular
    volume_eq := hvolume
    volume_pos := by rw [hvolume]; exact selection.selected_weight_pos
    height_region :=
      hsubRestricted.union_subset.trans
        (restricted.subshading_carrier.union_subset.trans carrier.height_region)
    constant_multiplicity := hconstant
    union_height := by
      intro point hpoint
      have hregion : point ∈ selection.selectedRegion := by
        rw [hunion] at hpoint
        exact hpoint.2
      rw [selection.selectedRegion_eq] at hregion
      rcases Set.mem_iUnion₂.mp hregion with
        ⟨parent, hparent, hpointParent⟩
      rw [wz1PaperGridCube_eq_Ico hroot parent] at hpointParent
      rw [← selection.parent_height_eq parent hparent]
      exact ⟨hpointParent.2.2.2.2.1, hpointParent.2.2.2.2.2⟩
  }

/-- Every point of the original source lying in one selected official parent
is close to the fixed line chosen on the outer-popular slice.  This is the
paper-order bridge which permits the subsequent Lemma-23 carrier to return to
the complete intermediate source without changing the chosen line. -/
theorem PureWZ2TerminalPopularRestrictedParentSelectionData.fixed_line_localization_of_mem_parent
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
    (selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents)
    (parent : ℤ × ℤ × ℤ) (hparent : parent ∈ selection.selected)
    (point : Point3) (hpointSource : point ∈ source.shading.union)
    (hpointParent : point ∈
      wz1PaperGridCube terminal.sqrtRequested.1 parent) :
    |inner ℝ point
          (globalGrainDirection
            (source.globalGrains.slope (point (2 : Fin 3)))) -
        line.lineLevel| ≤ 14 * terminal.sqrtRequested.1 := by
  let root := terminal.sqrtRequested.1
  have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
  have hdeltaRoot : delta ≤ root := by
    rw [show root = Real.sqrt delta by exact terminal.sqrtRequested_eq]
    nlinarith [Real.sqrt_nonneg delta,
      Real.sq_sqrt source.extremal.delta_pos.le,
      source.extremal.delta_le_one]
  rcases parents.parent_hit parent
      (selection.onePerY_subset (selection.selected_subset hparent)) with
    ⟨cell, hcell, hcellParent⟩
  let representative := line.representative cell
  have hrepresentativeParent : representative ∈
      wz1PaperGridCube root parent := by
    have hmem := parents.representative_mem_parent cell hcell
    rwa [hcellParent] at hmem
  rw [wz1PaperGridCube_eq_Ico hroot parent] at hpointParent
  rw [wz1PaperGridCube_eq_Ico hroot parent] at hrepresentativeParent
  have hcoord0 : |point 0 - representative 0| ≤ root := by
    rw [abs_le]
    exact ⟨by linarith [hpointParent.1, hrepresentativeParent.2.1],
      by linarith [hrepresentativeParent.1, hpointParent.2.1]⟩
  have hcoord1 : |point 1 - representative 1| ≤ root := by
    rw [abs_le]
    exact ⟨by linarith [hpointParent.2.2.1,
      hrepresentativeParent.2.2.2.1],
      by linarith [hrepresentativeParent.2.2.1,
        hpointParent.2.2.2.1]⟩
  have hcoord2 : |point 2 - representative 2| ≤ root := by
    rw [abs_le]
    exact ⟨by linarith [hpointParent.2.2.2.2.1,
      hrepresentativeParent.2.2.2.2.2],
      by linarith [hrepresentativeParent.2.2.2.2.1,
        hpointParent.2.2.2.2.2]⟩
  have hpointBox := shading_union_subset_axisBox hpointSource
  have hpoint1 : |point 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpointBox.2.1
  have hpointHeight : point (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa [Kakeya.Streamlined.axisBox, abs_le] using hpointBox.2.2
  have hrepresentativeHeight : representative (2 : Fin 3) =
      line.lineHeight := line.representative_height cell hcell
  have hslopeDifference :
      |source.globalGrains.slope (point (2 : Fin 3)) -
          source.globalGrains.slope line.lineHeight| ≤ root := by
    have hlip := source.globalGrains.slope_lipschitz.dist_le_mul
      (point (2 : Fin 3)) hpointHeight line.lineHeight line.lineHeight_mem
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    exact hlip.trans (by rw [← hrepresentativeHeight]; exact hcoord2)
  have hslopeLine : |source.globalGrains.slope line.lineHeight| ≤ 3 :=
    source.globalGrains.slope_bound line.lineHeight line.lineHeight_mem
  have hprojectionDifference :
      |inner ℝ point
            (globalGrainDirection
              (source.globalGrains.slope (point (2 : Fin 3)))) -
          inner ℝ representative
            (globalGrainDirection
              (source.globalGrains.slope line.lineHeight))| ≤ 5 * root := by
    have hformula :
        inner ℝ point
              (globalGrainDirection
                (source.globalGrains.slope (point (2 : Fin 3)))) -
            inner ℝ representative
              (globalGrainDirection
                (source.globalGrains.slope line.lineHeight)) =
          (point 0 - representative 0) +
            source.globalGrains.slope line.lineHeight *
              (point 1 - representative 1) +
            (source.globalGrains.slope (point (2 : Fin 3)) -
              source.globalGrains.slope line.lineHeight) * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      ring
    rw [hformula]
    calc
      _ ≤ |point 0 - representative 0| +
          |source.globalGrains.slope line.lineHeight| *
            |point 1 - representative 1| +
          |source.globalGrains.slope (point (2 : Fin 3)) -
            source.globalGrains.slope line.lineHeight| * |point 1| := by
        calc
          _ ≤ |(point 0 - representative 0) +
                source.globalGrains.slope line.lineHeight *
                  (point 1 - representative 1)| +
              |(source.globalGrains.slope (point (2 : Fin 3)) -
                source.globalGrains.slope line.lineHeight) * point 1| :=
            abs_add_le _ _
          _ ≤ (|point 0 - representative 0| +
                |source.globalGrains.slope line.lineHeight *
                  (point 1 - representative 1)|) +
              |(source.globalGrains.slope (point (2 : Fin 3)) -
                source.globalGrains.slope line.lineHeight) * point 1| := by
            gcongr
            exact abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ root + 3 * root + root * 1 := by gcongr
      _ = 5 * root := by ring
  have hrepresentativeLine := line.heavy_representative_near_line cell hcell
  have htriangle := abs_sub_le
    (inner ℝ point
      (globalGrainDirection
        (source.globalGrains.slope (point (2 : Fin 3)))))
    (inner ℝ representative
      (globalGrainDirection (source.globalGrains.slope line.lineHeight)))
    line.lineLevel
  have hrepresentativeLineRoot :
      |inner ℝ representative
          (globalGrainDirection (source.globalGrains.slope line.lineHeight)) -
        line.lineLevel| ≤ 9 * root := by
    have hdeltaLine : |inner ℝ representative
          (globalGrainDirection (source.globalGrains.slope line.lineHeight)) -
        line.lineLevel| ≤ 9 * delta := by
      simpa only [representative] using hrepresentativeLine
    exact hdeltaLine.trans (by
      calc
        9 * delta ≤ 9 * root :=
          mul_le_mul_of_nonneg_left hdeltaRoot (by norm_num))
  calc
    _ ≤ |inner ℝ point
            (globalGrainDirection
              (source.globalGrains.slope (point (2 : Fin 3)))) -
          inner ℝ representative
            (globalGrainDirection
              (source.globalGrains.slope line.lineHeight))| +
        |inner ℝ representative
            (globalGrainDirection
              (source.globalGrains.slope line.lineHeight)) -
          line.lineLevel| := htriangle
    _ ≤ 5 * root + 9 * root :=
      add_le_add hprojectionDifference hrepresentativeLineRoot
    _ = 14 * root := by ring

/-- The post-line selected outer-popular carrier remains close to the same
fixed global-grain line. -/
theorem PureWZ2TerminalPopularSelectedParentCarrierData.fixed_line_localization
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
    {selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents}
    (selectedCarrier :
      PureWZ2TerminalPopularSelectedParentCarrierData selection) :
    ∀ point ∈ selectedCarrier.shading.union,
      |inner ℝ point
          (globalGrainDirection
            (source.globalGrains.slope (point (2 : Fin 3)))) -
        line.lineLevel| ≤ 14 * terminal.sqrtRequested.1 := by
  let root := terminal.sqrtRequested.1
  have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
  have hdeltaRoot : delta ≤ root := by
    rw [show root = Real.sqrt delta by exact terminal.sqrtRequested_eq]
    nlinarith [Real.sqrt_nonneg delta,
      Real.sq_sqrt source.extremal.delta_pos.le,
      source.extremal.delta_le_one]
  intro point hpoint
  have hregion : point ∈ selection.selectedRegion := by
    rw [selectedCarrier.union_eq] at hpoint
    exact hpoint.2
  rw [selection.selectedRegion_eq] at hregion
  rcases Set.mem_iUnion₂.mp hregion with
    ⟨parent, hparent, hpointParent⟩
  rcases parents.parent_hit parent
      (selection.onePerY_subset (selection.selected_subset hparent)) with
    ⟨cell, hcell, hcellParent⟩
  let representative := line.representative cell
  have hrepresentativeParent : representative ∈
      wz1PaperGridCube root parent := by
    have hmem := parents.representative_mem_parent cell hcell
    rwa [hcellParent] at hmem
  rw [wz1PaperGridCube_eq_Ico hroot parent] at hpointParent
  rw [wz1PaperGridCube_eq_Ico hroot parent] at hrepresentativeParent
  have hcoord0 : |point 0 - representative 0| ≤ root := by
    rw [abs_le]
    exact ⟨by linarith [hpointParent.1, hrepresentativeParent.2.1],
      by linarith [hrepresentativeParent.1, hpointParent.2.1]⟩
  have hcoord1 : |point 1 - representative 1| ≤ root := by
    rw [abs_le]
    exact ⟨by linarith [hpointParent.2.2.1, hrepresentativeParent.2.2.2.1],
      by linarith [hrepresentativeParent.2.2.1, hpointParent.2.2.2.1]⟩
  have hcoord2 : |point 2 - representative 2| ≤ root := by
    rw [abs_le]
    exact ⟨by linarith [hpointParent.2.2.2.2.1,
      hrepresentativeParent.2.2.2.2.2],
      by linarith [hrepresentativeParent.2.2.2.2.1,
        hpointParent.2.2.2.2.2]⟩
  have hpointSource : point ∈ source.shading.union :=
    selectedCarrier.subshading_source.union_subset hpoint
  have hpointBox := shading_union_subset_axisBox hpointSource
  have hpoint1 : |point 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpointBox.2.1
  have hpointHeight : point (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa [Kakeya.Streamlined.axisBox, abs_le] using hpointBox.2.2
  have hrepresentativeHeight : representative (2 : Fin 3) =
      line.lineHeight := line.representative_height cell hcell
  have hslopeDifference :
      |source.globalGrains.slope (point (2 : Fin 3)) -
          source.globalGrains.slope line.lineHeight| ≤ root := by
    have hlip := source.globalGrains.slope_lipschitz.dist_le_mul
      (point (2 : Fin 3)) hpointHeight line.lineHeight line.lineHeight_mem
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    exact hlip.trans (by rw [← hrepresentativeHeight]; exact hcoord2)
  have hslopeLine : |source.globalGrains.slope line.lineHeight| ≤ 3 :=
    source.globalGrains.slope_bound line.lineHeight line.lineHeight_mem
  have hprojectionDifference :
      |inner ℝ point
            (globalGrainDirection
              (source.globalGrains.slope (point (2 : Fin 3)))) -
          inner ℝ representative
            (globalGrainDirection
              (source.globalGrains.slope line.lineHeight))| ≤ 5 * root := by
    have hformula :
        inner ℝ point
              (globalGrainDirection
                (source.globalGrains.slope (point (2 : Fin 3)))) -
            inner ℝ representative
              (globalGrainDirection
                (source.globalGrains.slope line.lineHeight)) =
          (point 0 - representative 0) +
            source.globalGrains.slope line.lineHeight *
              (point 1 - representative 1) +
            (source.globalGrains.slope (point (2 : Fin 3)) -
              source.globalGrains.slope line.lineHeight) * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      ring
    rw [hformula]
    have hsum := abs_add_le
      ((point 0 - representative 0) +
        source.globalGrains.slope line.lineHeight *
          (point 1 - representative 1))
      ((source.globalGrains.slope (point (2 : Fin 3)) -
        source.globalGrains.slope line.lineHeight) * point 1)
    have hfirst := abs_add_le (point 0 - representative 0)
      (source.globalGrains.slope line.lineHeight *
        (point 1 - representative 1))
    calc
      _ ≤ |(point 0 - representative 0) +
            source.globalGrains.slope line.lineHeight *
              (point 1 - representative 1)| +
          |(source.globalGrains.slope (point (2 : Fin 3)) -
            source.globalGrains.slope line.lineHeight) * point 1| := hsum
      _ ≤ |point 0 - representative 0| +
          |source.globalGrains.slope line.lineHeight| *
            |point 1 - representative 1| +
          |source.globalGrains.slope (point (2 : Fin 3)) -
            source.globalGrains.slope line.lineHeight| * |point 1| := by
        calc
          _ ≤ (|point 0 - representative 0| +
                |source.globalGrains.slope line.lineHeight *
                  (point 1 - representative 1)|) +
              |(source.globalGrains.slope (point (2 : Fin 3)) -
                source.globalGrains.slope line.lineHeight) * point 1| :=
            by
              simpa only [add_assoc, add_left_comm, add_comm] using
                add_le_add_right hfirst
                  |(source.globalGrains.slope (point (2 : Fin 3)) -
                    source.globalGrains.slope line.lineHeight) * point 1|
          _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ root + 3 * root + root * 1 := by gcongr
      _ = 5 * root := by ring
  have hrepresentativeLine := line.heavy_representative_near_line cell hcell
  have htriangle := abs_sub_le
    (inner ℝ point (globalGrainDirection
      (source.globalGrains.slope (point (2 : Fin 3)))))
    (inner ℝ representative (globalGrainDirection
      (source.globalGrains.slope line.lineHeight))) line.lineLevel
  exact htriangle.trans (by linarith [hprojectionDifference,
    hrepresentativeLine, hroot])

end Kakeya.Assouad

end
