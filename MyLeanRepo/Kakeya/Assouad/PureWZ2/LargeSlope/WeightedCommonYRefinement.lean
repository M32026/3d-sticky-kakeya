import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.WeightedPopularGlobalGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GlobalGrainWindowVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ParametricCoverSliceSelection
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Common-y refinement for incidence-mass popular grains

Every retained global label has a quantitative spatial-volume floor.  A
single small exceptional set of y-values therefore removes at most half of
every retained label region simultaneously.  Fubini then selects one genuine
common y-plane, and the labels met by that slice are expanded back to complete
whole-cell fibers.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- Complete spatial region of one weighted popular label. -/
def pureWZ2WeightedLabelRegion
    {sigma grainLoss slabLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (label : ℤ × ℤ) : Set Point3 :=
  ⋃ cell ∈ pureWZ2GlobalGrainFiber
      cfg.globalGrains.slope delta popular.activeCells label,
    wz1PaperGridCube delta cell

theorem measurableSet_pureWZ2WeightedLabelRegion
    {sigma grainLoss slabLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (label : ℤ × ℤ) :
    MeasurableSet (pureWZ2WeightedLabelRegion popular label) := by
  exact Finset.measurableSet_biUnion _ fun cell _ =>
    wz1PaperGridCube_measurable cell

/-- Labels whose good-y part meets one genuine common y-slice. -/
def pureWZ2WeightedLabelsMeetingGoodSlice
    {sigma loss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma loss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma loss scale}
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (goodY : Set ℝ) (y : ℝ) : Finset (ℤ × ℤ) :=
  popular.keptLabels.filter fun label =>
    (pureWZ2YSlice
      (pureWZ2WeightedLabelRegion popular label ∩
        {point : Point3 | point (1 : Fin 3) ∈ goodY}) y).Nonempty

/-- Stable output of the weighted common-y refinement. -/
structure PureWZ2WeightedCommonYData
    {sigma loss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData cfg.shading sigma loss scale)
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData) where
  coverCenters : Finset Point3
  cover_card : (coverCenters.card : ENNReal) ≤
    Kakeya.realRpowENN delta (-loss) *
      Kakeya.realRpowENN scale.1 (-2 + sigma)
  goodY : Set ℝ
  goodY_measurable : MeasurableSet goodY
  goodY_subset : goodY ⊆ Set.Icc (-1 : ℝ) 1
  goodY_ne_zero : volume goodY ≠ 0
  badY_volume : volume (Set.Icc (-1 : ℝ) 1 \ goodY) ≤
    2 * Kakeya.realRpowENN delta (4 * loss)
  cover_count : ∀ y ∈ goodY,
    ((coverCenters.filter fun center =>
      |center (1 : Fin 3) - y| ≤ scale.1).card : ENNReal) ≤
      Kakeya.realRpowENN delta (-(4 * loss)) *
        ENNReal.ofReal scale.1 * (coverCenters.card : ENNReal)
  every_label_good_half : ∀ label ∈ popular.keptLabels,
    (1 / 2 : ENNReal) *
        volume (pureWZ2WeightedLabelRegion popular label) ≤
      volume (pureWZ2WeightedLabelRegion popular label ∩
        {point : Point3 | point (1 : Fin 3) ∈ goodY})
  goodRegion : Set Point3
  goodRegion_eq : goodRegion =
    (⋃ label ∈ popular.keptLabels,
      pureWZ2WeightedLabelRegion popular label) ∩
        {point : Point3 | point (1 : Fin 3) ∈ goodY}
  goodRegion_measurable : MeasurableSet goodRegion
  goodRegion_ne_zero : volume goodRegion ≠ 0
  y0 : ℝ
  y0_mem : y0 ∈ goodY
  common_slice_average : volume goodRegion / volume goodY ≤
    volume (pureWZ2YSlice goodRegion y0)
  selectedLabels : Finset (ℤ × ℤ)
  selectedLabels_eq : selectedLabels =
    pureWZ2WeightedLabelsMeetingGoodSlice popular goodY y0
  selectedLabels_subset : selectedLabels ⊆ popular.keptLabels
  selectedLabels_nonempty : selectedLabels.Nonempty
  selectedCells : Finset (ℤ × ℤ × ℤ)
  selectedCells_eq : selectedCells = selectedLabels.biUnion
    (pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta popular.activeCells)
  selectedCells_subset : selectedCells ⊆ popular.retainedCells
  F2 : WZ1PaperTubeShading cfg.family
  F2_eq : F2 = wz2RefinedShading scaleData.slabShading selectedCells
  F2_cubical : WZ1PaperIsCubicalShading F2
  F2_in_slab : ∀ index, F2.carrier index ⊆
    horizontalSlab scaleData.slabLeft scaleData.slabRight
  F2_union_eq : F2.union = wz2RetainedCellsUnion delta selectedCells
  common_slice_subset_F2 : pureWZ2YSlice goodRegion y0 ⊆
    pureWZ2YSlice F2.union y0

/-- Abstract half-volume retention after deleting a bad coordinate set. -/
theorem volume_inter_coordinate_good_half
    (E : Set Point3)
    (hEWindow : ∀ point ∈ E, point (1 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1)
    (hEFinite : volume E ≠ ⊤)
    {good : Set ℝ}
    (hbad : volume (E ∩
        {point : Point3 | point (1 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 \ good}) ≤
      (1 / 2 : ENNReal) * volume E) :
    (1 / 2 : ENNReal) * volume E ≤
      volume (E ∩ {point : Point3 | point (1 : Fin 3) ∈ good}) := by
  let goodPart := E ∩ {point : Point3 | point (1 : Fin 3) ∈ good}
  let badPart := E ∩
    {point : Point3 | point (1 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 \ good}
  have hcover : E ⊆ goodPart ∪ badPart := by
    intro point hpoint
    by_cases hgood : point (1 : Fin 3) ∈ good
    · exact Or.inl ⟨hpoint, hgood⟩
    · exact Or.inr ⟨hpoint, hEWindow point hpoint, hgood⟩
  have hmeasure : volume E ≤ volume goodPart + volume badPart :=
    (measure_mono hcover).trans (measure_union_le _ _)
  have hhalfTop : (1 / 2 : ENNReal) * volume E ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hEFinite
  have hhalfAdd :
      (1 / 2 : ENNReal) * volume E + (1 / 2 : ENNReal) * volume E =
        volume E := by
    rw [← add_mul]
    have hhalf : (1 / 2 : ENNReal) + (1 / 2 : ENNReal) = 1 := by
      rw [← two_mul, div_eq_mul_inv, one_mul]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    rw [hhalf, one_mul]
  have hadd :
      (1 / 2 : ENNReal) * volume E + (1 / 2 : ENNReal) * volume E ≤
        (1 / 2 : ENNReal) * volume E + volume goodPart := by
    calc
      _ = volume E := hhalfAdd
      _ ≤ volume goodPart + volume badPart := hmeasure
      _ ≤ volume goodPart + (1 / 2 : ENNReal) * volume E := by gcongr
      _ = (1 / 2 : ENNReal) * volume E + volume goodPart := by rw [add_comm]
  exact (ENNReal.add_le_add_iff_left hhalfTop).mp hadd

/-- Construct weighted Refinement 2 from the explicit single-grain budget. -/
theorem pureWZ2_weightedCommonYRefinement
    {sigma loss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData cfg.shading sigma loss scale)
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (hloss : 0 < loss) (hdeltaLtOne : delta < 1)
    (hbadBudget :
      ENNReal.ofReal (64 * delta ^ 2) *
          (2 * Kakeya.realRpowENN delta (4 * loss)) ≤
        (1 / 2 : ENNReal) *
          (popular.labelThreshold /
            (Kakeya.realRpowENN (delta / scale.1) (2 - sigma - loss) *
              cfg.family.enncard))) :
    Nonempty (PureWZ2WeightedCommonYData cfg scale scaleData popular) := by
  rcases scaleData.slab_cover with ⟨coverCenters, hcoverCard, hcover⟩
  let K := Kakeya.realRpowENN delta (-(4 * loss))
  have hKZero : K ≠ 0 := by
    simp [K, Kakeya.realRpowENN, Real.rpow_pos_of_pos cfg.extremal.delta_pos]
  have hKTop : K ≠ ⊤ := by simp [K, Kakeya.realRpowENN]
  rcases exists_parametric_cover_slice_good_set
      (W := scale.1) (cfg.extremal.delta_pos.trans_le scale.2.1)
      (K := K) hKZero hKTop coverCenters with
    ⟨goodY, hgoodY, hgoodYSubset, hbadRaw, hcoverCount⟩
  have hKInv : 2 / K = 2 * Kakeya.realRpowENN delta (4 * loss) := by
    have hmul : K * Kakeya.realRpowENN delta (4 * loss) = 1 := by
      dsimp only [K]
      rw [← realRpowENN_add cfg.extremal.delta_pos]
      have hexp : -(4 * loss) + 4 * loss = 0 := by ring
      rw [hexp]
      simp [Kakeya.realRpowENN]
    have hinv : K⁻¹ = Kakeya.realRpowENN delta (4 * loss) :=
      (ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hmul)).symm
    rw [div_eq_mul_inv, hinv]
  have hbadY : volume (Set.Icc (-1 : ℝ) 1 \ goodY) ≤
      2 * Kakeya.realRpowENN delta (4 * loss) := by
    rwa [hKInv] at hbadRaw
  have hgoodYNeZero : volume goodY ≠ 0 := by
    have hpower : Kakeya.realRpowENN delta (4 * loss) < 1 := by
      apply ENNReal.ofReal_lt_one.mpr
      exact Real.rpow_lt_one cfg.extremal.delta_pos.le hdeltaLtOne (by positivity)
    have hbadSmall : volume (Set.Icc (-1 : ℝ) 1 \ goodY) < 2 :=
      hbadY.trans_lt (by
        simpa [mul_comm] using ENNReal.mul_lt_mul_left
          (show (2 : ENNReal) ≠ 0 by norm_num)
          (show (2 : ENNReal) ≠ ⊤ by norm_num) hpower)
    intro hzero
    have hgoodTop : volume goodY ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp [Real.volume_Icc] :
        volume (Set.Icc (-1 : ℝ) 1) ≠ ⊤)
        (measure_mono hgoodYSubset)
    rw [measure_sdiff hgoodYSubset hgoodY.nullMeasurableSet hgoodTop, hzero] at hbadSmall
    have hinterval : volume (Set.Icc (-1 : ℝ) 1) = 2 := by
      rw [Real.volume_Icc]; norm_num
    rw [hinterval] at hbadSmall
    simpa using hbadSmall
  have heveryHalf : ∀ label ∈ popular.keptLabels,
      (1 / 2 : ENNReal) * volume (pureWZ2WeightedLabelRegion popular label) ≤
        volume (pureWZ2WeightedLabelRegion popular label ∩
          {point : Point3 | point (1 : Fin 3) ∈ goodY}) := by
    intro label hlabel
    let region := pureWZ2WeightedLabelRegion popular label
    have hregionWindow : ∀ point ∈ region,
        point (1 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := by
      intro point hpoint
      rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
      have hactive := (mem_pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta
        popular.activeCells label cell).mp hcell |>.1
      have hcellActive : cell ∈ wz1PaperActiveCells scaleData.slabShading
          cfg.extremal.delta_pos := by simpa [popular.activeCells_eq] using hactive
      have hcellSub := Set.inter_eq_right.mp
        (scaleData.slab_cubical.inter_activeCell_eq
          cfg.extremal.delta_pos hcellActive) hpointCell
      rcases hcellSub with ⟨index, hcarrier⟩
      have hbox := scaleData.slabShading.subset_body index hcarrier |>.2
      simpa [Set.mem_Icc, abs_le] using hbox.2.1
    have hregionFinite : volume region ≠ ⊤ := by
      change volume (⋃ cell ∈ pureWZ2GlobalGrainFiber
          cfg.globalGrains.slope delta popular.activeCells label,
        wz1PaperGridCube delta cell) ≠ ⊤
      rw [popular.label_volume label hlabel]
      exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
    have hbadRegion : volume (region ∩
        {point : Point3 | point (1 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 \ goodY}) ≤
        (1 / 2 : ENNReal) * volume region := by
      calc
        _ ≤ volume (pureWZ2GlobalGrainWithConstant 4
            cfg.globalGrains.slope delta
            (pureWZ2PaperCellCenter delta (popular.label_anchor label hlabel)) ∩
              {point : Point3 | point (1 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 \ goodY}) := by
          apply measure_mono
          intro point hpoint
          exact ⟨popular.label_grain_containment label hlabel hpoint.1, hpoint.2⟩
        _ ≤ ENNReal.ofReal (64 * delta ^ 2) *
            volume (Set.Icc (-1 : ℝ) 1 \ goodY) :=
          pureWZ2_globalGrainWithConstant_four_window_volume_upper
            cfg.globalGrains.slope cfg.extremal.delta_pos.le _
              (measurableSet_Icc.diff hgoodY)
        _ ≤ ENNReal.ofReal (64 * delta ^ 2) *
            (2 * Kakeya.realRpowENN delta (4 * loss)) := by gcongr
        _ ≤ (1 / 2 : ENNReal) *
            (popular.labelThreshold /
              (Kakeya.realRpowENN (delta / scale.1) (2 - sigma - loss) * cfg.family.enncard)) := hbadBudget
        _ ≤ (1 / 2 : ENNReal) * volume region := by
          gcongr
          exact popular.label_volume_lower label hlabel
    exact volume_inter_coordinate_good_half region hregionWindow hregionFinite hbadRegion
  let goodRegion := (⋃ label ∈ popular.keptLabels,
      pureWZ2WeightedLabelRegion popular label) ∩
    {point : Point3 | point (1 : Fin 3) ∈ goodY}
  have hgoodRegionMeasurable : MeasurableSet goodRegion := by
    apply (Finset.measurableSet_biUnion popular.keptLabels fun label _ =>
      measurableSet_pureWZ2WeightedLabelRegion popular label).inter
    exact measurableSet_pureWZ2YWindow hgoodY
  have hgoodRegionNeZero : volume goodRegion ≠ 0 := by
    rcases popular.keptLabels_nonempty with ⟨label, hlabel⟩
    have hregionPos : volume (pureWZ2WeightedLabelRegion popular label) ≠ 0 := by
      change volume (⋃ cell ∈ pureWZ2GlobalGrainFiber
          cfg.globalGrains.slope delta popular.activeCells label,
        wz1PaperGridCube delta cell) ≠ 0
      rw [popular.label_volume label hlabel]
      have hfiber : (pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta
          popular.activeCells label).Nonempty := by
        rcases popular.label_anchor_mem label hlabel with hmem
        exact ⟨_, hmem⟩
      exact mul_ne_zero (by exact_mod_cast hfiber.card_pos.ne')
        ((ENNReal.ofReal_pos.mpr (pow_pos cfg.extremal.delta_pos 3)).ne')
    have hgoodPartPos : volume (pureWZ2WeightedLabelRegion popular label ∩
        {point : Point3 | point (1 : Fin 3) ∈ goodY}) ≠ 0 := by
      intro hzero
      have hhalfZero := le_zero_iff.mp ((heveryHalf label hlabel).trans_eq hzero)
      exact (mul_ne_zero (by norm_num) hregionPos) hhalfZero
    intro hzero
    apply hgoodPartPos
    apply measure_mono_null _ hzero
    intro point hpoint
    exact ⟨Set.mem_iUnion₂.mpr ⟨label, hlabel, hpoint.1⟩, hpoint.2⟩
  have hgoodRegionFinite : volume goodRegion ≠ ⊤ := by
    have hsubset : goodRegion ⊆ Kakeya.Streamlined.axisBox 2 2 2 := by
      intro point hpoint
      rcases Set.mem_iUnion₂.mp hpoint.1 with ⟨label, _, hregion⟩
      rcases Set.mem_iUnion₂.mp hregion with ⟨cell, hcell, hpointCell⟩
      have hactive := (mem_pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta
        popular.activeCells label cell).mp hcell |>.1
      have hcellActive : cell ∈ wz1PaperActiveCells scaleData.slabShading
          cfg.extremal.delta_pos := by simpa [popular.activeCells_eq] using hactive
      have hcellSub := Set.inter_eq_right.mp
        (scaleData.slab_cubical.inter_activeCell_eq cfg.extremal.delta_pos hcellActive)
      rcases (show point ∈ scaleData.slabShading.union from
          hcellSub hpointCell) with ⟨index, hcarrier⟩
      exact (scaleData.slabShading.subset_body index hcarrier).2
    exact ne_top_of_le_ne_top
      (show volume (Kakeya.Streamlined.axisBox 2 2 2) ≠ ⊤ by
        rw [Kakeya.Streamlined.volume_axisBox 2 2 2]
        · exact ENNReal.ofReal_ne_top
        all_goals norm_num) (measure_mono hsubset)
  have hgoodSupport : ∀ point ∈ goodRegion, point (1 : Fin 3) ∈ goodY :=
    fun _ h => h.2
  rcases pureWZ2_exists_ySlice_average_on hgoodRegionMeasurable hgoodRegionFinite
      hgoodY hgoodYNeZero hgoodSupport with ⟨y0, hy0, hy0Average⟩
  let selectedLabels := pureWZ2WeightedLabelsMeetingGoodSlice popular goodY y0
  have hsliceNeZero : volume (pureWZ2YSlice goodRegion y0) ≠ 0 := by
    have hquot : volume goodRegion / volume goodY ≠ 0 :=
      ENNReal.div_ne_zero.mpr ⟨hgoodRegionNeZero,
        ne_top_of_le_ne_top (by simp [Real.volume_Icc] :
          volume (Set.Icc (-1 : ℝ) 1) ≠ ⊤) (measure_mono hgoodYSubset)⟩
    intro hzero
    exact hquot (le_zero_iff.mp (hy0Average.trans_eq hzero))
  have hselectedNonempty : selectedLabels.Nonempty := by
    rcases nonempty_of_measure_ne_zero hsliceNeZero with ⟨point, hpoint⟩
    have hp3 := pureWZ2_mem_ySlice_iff.mp hpoint
    have hpGood : point3 (point 0) y0 (point 1) ∈ goodRegion := hp3
    rcases Set.mem_iUnion₂.mp hpGood.1 with ⟨label, hlabel, hregion⟩
    refine ⟨label, Finset.mem_filter.mpr ⟨hlabel, ⟨point, ?_⟩⟩⟩
    apply pureWZ2_mem_ySlice_iff.mpr
    exact ⟨hregion, hpGood.2⟩
  have hselectedSubset : selectedLabels ⊆ popular.keptLabels := Finset.filter_subset _ _
  let selectedCells := selectedLabels.biUnion
    (pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta popular.activeCells)
  have hselectedCellsSubset : selectedCells ⊆ popular.retainedCells := by
    intro cell hcell
    rcases Finset.mem_biUnion.mp hcell with ⟨label, hlabel, hfiber⟩
    rw [popular.retainedCells_eq]
    exact Finset.mem_biUnion.mpr ⟨label, hselectedSubset hlabel, hfiber⟩
  let F2 := wz2RefinedShading scaleData.slabShading selectedCells
  have hactiveSelected : ∀ cell ∈ selectedCells,
      cell ∈ wz1PaperActiveCells scaleData.slabShading cfg.extremal.delta_pos := by
    intro cell hcell
    have : cell ∈ popular.activeCells := popular.retainedCells_subset
      (hselectedCellsSubset hcell)
    simpa [popular.activeCells_eq] using this
  have hF2Union : F2.union = wz2RetainedCellsUnion delta selectedCells :=
    wz2RefinedShading_union_eq scaleData.slab_cubical cfg.extremal.delta_pos
      hactiveSelected
  have hcommonSubset : pureWZ2YSlice goodRegion y0 ⊆ pureWZ2YSlice F2.union y0 := by
    intro point hpoint
    have hp3 := pureWZ2_mem_ySlice_iff.mp hpoint
    have hpGood : point3 (point 0) y0 (point 1) ∈ goodRegion := hp3
    rcases Set.mem_iUnion₂.mp hpGood.1 with ⟨label, hlabel, hregion⟩
    rcases Set.mem_iUnion₂.mp hregion with ⟨cell, hfiber, hcell⟩
    have hlabelSelected : label ∈ selectedLabels :=
      Finset.mem_filter.mpr ⟨hlabel, ⟨point, pureWZ2_mem_ySlice_iff.mpr
        ⟨hregion, hpGood.2⟩⟩⟩
    apply pureWZ2_mem_ySlice_iff.mpr
    rw [hF2Union]
    exact Set.mem_iUnion₂.mpr ⟨cell, Finset.mem_biUnion.mpr
      ⟨label, hlabelSelected, hfiber⟩, hcell⟩
  exact ⟨{
    coverCenters := coverCenters
    cover_card := hcoverCard
    goodY := goodY
    goodY_measurable := hgoodY
    goodY_subset := hgoodYSubset
    goodY_ne_zero := hgoodYNeZero
    badY_volume := hbadY
    cover_count := hcoverCount
    every_label_good_half := heveryHalf
    goodRegion := goodRegion
    goodRegion_eq := rfl
    goodRegion_measurable := hgoodRegionMeasurable
    goodRegion_ne_zero := hgoodRegionNeZero
    y0 := y0
    y0_mem := hy0
    common_slice_average := hy0Average
    selectedLabels := selectedLabels
    selectedLabels_eq := rfl
    selectedLabels_subset := hselectedSubset
    selectedLabels_nonempty := hselectedNonempty
    selectedCells := selectedCells
    selectedCells_eq := rfl
    selectedCells_subset := hselectedCellsSubset
    F2 := F2
    F2_eq := rfl
    F2_cubical := wz2RefinedShading_cubical scaleData.slab_cubical
    F2_in_slab := fun index =>
      (wz2RefinedShading_subshading index).trans (scaleData.slab_in_slab index)
    F2_union_eq := hF2Union
    common_slice_subset_F2 := hcommonSubset
  }⟩

end Kakeya.Assouad

end
