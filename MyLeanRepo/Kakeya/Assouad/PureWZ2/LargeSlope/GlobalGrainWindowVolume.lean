import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CommonYSlice
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CroppedPopularGlobalGrains

/-!
# Volume of a popular global grain over a y-window

This is the measure estimate used in WZ2 Section 6, Refinement 2.  A
constant-`4` literal global grain has every exact y-slice bounded by
`64 * delta^2`; Fubini therefore controls the part of the grain over any
measurable exceptional set of y-values.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- Literal global grains are measurable. -/
theorem measurableSet_pureWZ2GlobalGrain
    (slope : ℝ → ℝ) (delta : ℝ) (anchor : Point3) :
    MeasurableSet (pureWZ2GlobalGrain slope delta anchor) := by
  simp only [pureWZ2GlobalGrain, pureWZ2GlobalGrainWithConstant, one_mul]
  apply MeasurableSet.inter
  · have hcontinuous : Continuous
        (fun point : Point3 =>
          |point (2 : Fin 3) - anchor (2 : Fin 3)|) := by
      fun_prop
    exact (isClosed_Iic.preimage hcontinuous).measurableSet
  · have hcontinuous : Continuous
        (fun point : Point3 =>
          |inner ℝ point
                (globalGrainDirection (slope (anchor (2 : Fin 3)))) -
              inner ℝ anchor
                (globalGrainDirection (slope (anchor (2 : Fin 3))))|) := by
      fun_prop
    exact (isClosed_Iic.preimage hcontinuous).measurableSet

/-- The spatial lift of a measurable set of y-values is measurable. -/
theorem measurableSet_pureWZ2YWindow
    {window : Set ℝ} (hwindow : MeasurableSet window) :
    MeasurableSet {point : Point3 | point (1 : Fin 3) ∈ window} := by
  exact hwindow.preimage (by fun_prop)

/-- Taking genuine y-slices is monotone in the spatial set. -/
theorem pureWZ2YSlice_mono
    {first second : Set Point3} (hsubset : first ⊆ second) (y : ℝ) :
    pureWZ2YSlice first y ⊆ pureWZ2YSlice second y := by
  intro point hpoint
  apply pureWZ2_mem_ySlice_iff.mpr
  exact hsubset (pureWZ2_mem_ySlice_iff.mp hpoint)

/--
The part of a constant-`4` global grain above a measurable y-window has
volume at most `64 * delta^2` times the length of the window.
-/
theorem pureWZ2_globalGrainWithConstant_four_window_volume_upper
    (slope : ℝ → ℝ) {delta : ℝ} (hdelta : 0 ≤ delta)
    (anchor : Point3) {window : Set ℝ}
    (hwindow : MeasurableSet window) :
    volume
        (pureWZ2GlobalGrainWithConstant 4 slope delta anchor ∩
          {point : Point3 | point (1 : Fin 3) ∈ window}) ≤
      ENNReal.ofReal (64 * delta ^ 2) * volume window := by
  let grain : Set Point3 := pureWZ2GlobalGrain slope (4 * delta) anchor
  let yWindow : Set Point3 :=
    {point : Point3 | point (1 : Fin 3) ∈ window}
  let restricted : Set Point3 := grain ∩ yWindow
  have hgrain : MeasurableSet grain :=
    measurableSet_pureWZ2GlobalGrain slope (4 * delta) anchor
  have hyWindow : MeasurableSet yWindow :=
    measurableSet_pureWZ2YWindow hwindow
  have hrestricted : MeasurableSet restricted := hgrain.inter hyWindow
  have hslice_bound : ∀ y : ℝ,
      volume (pureWZ2YSlice restricted y) ≤
        ENNReal.ofReal (64 * delta ^ 2) := by
    intro y
    calc
      volume (pureWZ2YSlice restricted y)
          ≤ volume (pureWZ2YSlice grain y) := by
            apply measure_mono
            exact pureWZ2YSlice_mono Set.inter_subset_left y
      _ ≤ ENNReal.ofReal (4 * (4 * delta) ^ 2) :=
        pureWZ2_ySlice_globalGrain_volume_upper slope
          (mul_nonneg (by norm_num) hdelta) y anchor
      _ = ENNReal.ofReal (64 * delta ^ 2) := by
        congr 1
        ring
  have houtside : ∀ y ∉ window,
      volume (pureWZ2YSlice restricted y) = 0 := by
    intro y hy
    have hempty : pureWZ2YSlice restricted y = ∅ := by
      ext point
      simp only [pureWZ2_mem_ySlice_iff, Set.notMem_empty, iff_false]
      intro hpoint
      apply hy
      simpa [yWindow, point3] using hpoint.2
    rw [hempty, measure_empty]
  have hfull :
      (∫⁻ y : ℝ, volume (pureWZ2YSlice restricted y)) =
        ∫⁻ y in window, volume (pureWZ2YSlice restricted y) := by
    rw [← lintegral_indicator hwindow]
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ window
    · simp [hy]
    · simp [hy, houtside y hy]
  have hrestrictedTarget :
      pureWZ2GlobalGrainWithConstant 4 slope delta anchor ∩
          {point : Point3 | point (1 : Fin 3) ∈ window} = restricted := by
    ext point
    simp [restricted, grain, yWindow, pureWZ2GlobalGrain,
      pureWZ2GlobalGrainWithConstant]
  rw [hrestrictedTarget]
  rw [pureWZ2_volume_eq_lintegral_ySlice restricted hrestricted, hfull]
  calc
    (∫⁻ y in window, volume (pureWZ2YSlice restricted y))
        ≤ ∫⁻ _y in window, ENNReal.ofReal (64 * delta ^ 2) := by
          exact setLIntegral_mono' hwindow (fun y _ => hslice_bound y)
    _ = ENNReal.ofReal (64 * delta ^ 2) * volume window := by
      rw [setLIntegral_const]

/--
The part of the whole popular refinement above an arbitrary measurable
y-window is controlled by the number of popular global-grain labels.
-/
theorem pureWZ2_popularF1_window_volume_upper
    {sigma loss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData
      cfg.shading sigma loss scale)
    (popular : PureWZ2PopularGlobalGrainData cfg scale scaleData)
    {window : Set ℝ} (hwindow : MeasurableSet window) :
    volume (popular.F1.union ∩
        {point : Point3 | point (1 : Fin 3) ∈ window}) ≤
      (popular.popular.keptLabels.card : ENNReal) *
        ENNReal.ofReal (64 * delta ^ 2) * volume window := by
  let yWindow : Set Point3 :=
    {point : Point3 | point (1 : Fin 3) ∈ window}
  let labels : Finset
      {label : ℤ × ℤ // label ∈ popular.popular.keptLabels} :=
    Finset.univ
  let grain
      (label : {label : ℤ × ℤ //
        label ∈ popular.popular.keptLabels}) : Set Point3 :=
    pureWZ2GlobalGrainWithConstant 4 cfg.globalGrains.slope delta
      (pureWZ2PaperCellCenter delta
        (popular.label_anchor label label.property)) ∩ yWindow
  have hactive : ∀ cell ∈ popular.activeCells,
      cell ∈ wz1PaperActiveCells popular.multiplicityBand.band
        cfg.extremal.delta_pos := by
    intro cell hcell
    simpa [popular.activeCells_eq] using hcell
  have hsubset : popular.F1.union ∩ yWindow ⊆
      ⋃ label ∈ labels, grain label := by
    intro point hpoint
    have hpointF1 : point ∈ popular.F1.union := hpoint.1
    rw [popular.F1_eq] at hpointF1
    rw [popular.popular.refined_union_eq cfg.extremal.delta_pos
      popular.multiplicityBand.band_cubical hactive] at hpointF1
    rcases Set.mem_iUnion₂.mp hpointF1 with
      ⟨cell, hcell, hpointCell⟩
    rw [popular.popular.retained_eq] at hcell
    rcases Finset.mem_biUnion.mp hcell with
      ⟨label, hlabel, hcellFiber⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨⟨label, hlabel⟩, Finset.mem_univ _, ?_⟩
    exact ⟨popular.label_grain_containment label hlabel
      (Set.mem_iUnion₂.mpr ⟨cell, hcellFiber, hpointCell⟩), hpoint.2⟩
  calc
    volume (popular.F1.union ∩
        {point : Point3 | point (1 : Fin 3) ∈ window})
        ≤ volume (⋃ label ∈ labels,
          grain label) := by
            exact measure_mono hsubset
    _ ≤ ∑ label ∈ labels,
          volume (grain label) :=
      MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ _label ∈ labels,
          ENNReal.ofReal (64 * delta ^ 2) * volume window := by
      apply Finset.sum_le_sum
      intro label _hlabel
      exact pureWZ2_globalGrainWithConstant_four_window_volume_upper
        cfg.globalGrains.slope cfg.extremal.delta_pos.le
        (pureWZ2PaperCellCenter delta
          (popular.label_anchor label label.property)) hwindow
    _ = (popular.popular.keptLabels.card : ENNReal) *
          ENNReal.ofReal (64 * delta ^ 2) * volume window := by
      simp [labels, Finset.sum_const]
      ring

end Kakeya.Assouad

end
