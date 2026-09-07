import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CroppedPopularGlobalGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6ScaleData
import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicPieceVolumeRefinementInputs
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume

/-!
# Incidence-mass popular global grains

This is the logarithm-free version of Section 6, Refinement 1.  Instead of
first pigeonholing the point multiplicity and then the label cardinality, it
partitions the actual slab incidence mass by global-grain labels and discards
labels below the average threshold.  At least half of the incidence mass is
retained, while every retained label has a uniform incidence-mass floor.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- Incidence mass carried by the complete cells of one global label. -/
def pureWZ2GlobalLabelIncidenceMass
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (slope : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (label : ℤ × ℤ) : ENNReal :=
  ∑ cell ∈ pureWZ2GlobalGrainFiber slope delta cells label,
    ∑ index : Fin family.card,
      volume (shading.carrier index ∩ wz1PaperGridCube delta cell)

/-- The active global labels partition the full incidence mass. -/
theorem pureWZ2_sum_globalLabelIncidenceMass
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (slope : ℝ → ℝ)
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta : 0 < delta) :
    (∑ label ∈ pureWZ2GlobalGrainLabels
          slope delta (wz1PaperActiveCells shading hdelta),
        pureWZ2GlobalLabelIncidenceMass shading slope
          (wz1PaperActiveCells shading hdelta) label) =
      shading.mass := by
  let cells := wz1PaperActiveCells shading hdelta
  let labels := pureWZ2GlobalGrainLabels slope delta cells
  let fiber := pureWZ2GlobalGrainFiber slope delta cells
  let cellMass : (ℤ × ℤ × ℤ) → ENNReal := fun cell =>
    ∑ index : Fin family.card,
      volume (shading.carrier index ∩ wz1PaperGridCube delta cell)
  have hdisjoint : ∀ first ∈ labels, ∀ second ∈ labels,
      first ≠ second → Disjoint (fiber first) (fiber second) := by
    intro first _ second _ hne
    exact pureWZ2GlobalGrainFiber_disjoint slope delta cells hne
  have hunion : labels.biUnion fiber = cells :=
    pureWZ2GlobalGrainFiber_biUnion slope delta cells
  have hsumCells :
      (∑ label ∈ labels, ∑ cell ∈ fiber label, cellMass cell) =
        ∑ cell ∈ cells, cellMass cell := by
    rw [← Finset.sum_biUnion hdisjoint, hunion]
  have hmassCells :
      (∑ cell ∈ cells, cellMass cell) = shading.mass := by
    rw [← wz2RefinedShading_mass_eq_sum_cells shading cells]
    have hactive : ∀ cell ∈ cells,
        cell ∈ wz1PaperActiveCells shading hdelta := fun _ h => h
    have hunionCells := wz2RefinedShading_union_eq
      hcubical hdelta hactive
    have hcarrier : ∀ index,
        (wz2RefinedShading shading cells).carrier index =
          shading.carrier index := by
      intro index
      apply Set.Subset.antisymm Set.inter_subset_left
      intro point hpoint
      refine ⟨hpoint, ?_⟩
      have hpointUnion : point ∈ shading.union := ⟨index, hpoint⟩
      rw [hcubical.union_eq_activeCells hdelta] at hpointUnion
      exact hpointUnion
    change (wz2RefinedShading shading cells).mass = shading.mass
    apply Finset.sum_congr rfl
    intro index _
    rw [hcarrier index]
  exact hsumCells.trans hmassCells

/-- Heavy elements above the average-half threshold retain half the weight. -/
theorem finite_sum_le_two_mul_heavy_sum
    {α : Type*} [DecidableEq α]
    (elements : Finset α) (weight : α → ENNReal)
    (threshold : ENNReal) (hthresholdTop : threshold ≠ ⊤)
    (hcutoff :
      2 * ((elements.card : ENNReal) * threshold) ≤
        ∑ element ∈ elements, weight element) :
    (∑ element ∈ elements, weight element) ≤
      2 * ∑ element ∈
        (elements.filter fun element => threshold ≤ weight element),
          weight element := by
  let retained := elements.filter fun element => threshold ≤ weight element
  let tiny := elements.filter fun element => ¬ threshold ≤ weight element
  have hpartition :
      (∑ element ∈ retained, weight element) +
          (∑ element ∈ tiny, weight element) =
        ∑ element ∈ elements, weight element := by
    simpa [retained, tiny] using
      Finset.sum_filter_add_sum_filter_not
        elements (fun element => threshold ≤ weight element) weight
  have htiny : (∑ element ∈ tiny, weight element) ≤
      (elements.card : ENNReal) * threshold := by
    calc
      (∑ element ∈ tiny, weight element)
          ≤ tiny.card • threshold := by
            apply Finset.sum_le_card_nsmul
            intro element helement
            exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp helement).2)
      _ = (tiny.card : ENNReal) * threshold := by
        simp [nsmul_eq_mul]
      _ ≤ (elements.card : ENNReal) * threshold := by
        gcongr
        exact Finset.filter_subset _ _
  have htinyTop : (∑ element ∈ tiny, weight element) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (by simp) hthresholdTop) htiny
  have htinyRetained :
      (∑ element ∈ tiny, weight element) ≤
        ∑ element ∈ retained, weight element := by
    apply (ENNReal.add_le_add_iff_right htinyTop).mp
    calc
      (∑ element ∈ tiny, weight element) +
          (∑ element ∈ tiny, weight element)
          = 2 * (∑ element ∈ tiny, weight element) := by ring
      _ ≤ 2 * ((elements.card : ENNReal) * threshold) := by gcongr
      _ ≤ ∑ element ∈ elements, weight element := hcutoff
      _ = (∑ element ∈ retained, weight element) +
          (∑ element ∈ tiny, weight element) := hpartition.symm
  calc
    (∑ element ∈ elements, weight element) =
        (∑ element ∈ retained, weight element) +
          (∑ element ∈ tiny, weight element) := hpartition.symm
    _ ≤ (∑ element ∈ retained, weight element) +
          (∑ element ∈ retained, weight element) := by gcongr
    _ = 2 * ∑ element ∈ retained, weight element := by ring
    _ = 2 * ∑ element ∈
        (elements.filter fun element => threshold ≤ weight element),
          weight element := rfl

/-- Stable logarithm-free output of Refinement 1. -/
structure PureWZ2WeightedPopularGlobalGrainData
    {sigma grainLoss slabLoss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData
      cfg.shading sigma slabLoss scale) where
  activeCells : Finset (ℤ × ℤ × ℤ)
  activeCells_eq :
    activeCells = wz1PaperActiveCells
      scaleData.slabShading cfg.extremal.delta_pos
  labels : Finset (ℤ × ℤ)
  labels_eq : labels = pureWZ2GlobalGrainLabels
    cfg.globalGrains.slope delta activeCells
  labelThreshold : ENNReal
  labelThreshold_pos : 0 < labelThreshold
  labelThreshold_identity :
    2 * ((labels.card : ENNReal) * labelThreshold) =
      scaleData.slabShading.mass
  keptLabels : Finset (ℤ × ℤ)
  keptLabels_eq : keptLabels = labels.filter fun label =>
    labelThreshold ≤ pureWZ2GlobalLabelIncidenceMass
      scaleData.slabShading cfg.globalGrains.slope activeCells label
  keptLabels_nonempty : keptLabels.Nonempty
  label_mass_lower : ∀ label ∈ keptLabels,
    labelThreshold ≤ pureWZ2GlobalLabelIncidenceMass
      scaleData.slabShading cfg.globalGrains.slope activeCells label
  retainedCells : Finset (ℤ × ℤ × ℤ)
  retainedCells_eq : retainedCells = keptLabels.biUnion
    (pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta activeCells)
  retainedCells_subset : retainedCells ⊆ activeCells
  F1 : WZ1PaperTubeShading cfg.family
  F1_eq : F1 = wz2RefinedShading scaleData.slabShading retainedCells
  F1_cubical : WZ1PaperIsCubicalShading F1
  F1_in_slab : ∀ index, F1.carrier index ⊆
    horizontalSlab scaleData.slabLeft scaleData.slabRight
  F1_mass_eq : F1.mass = ∑ label ∈ keptLabels,
    pureWZ2GlobalLabelIncidenceMass
      scaleData.slabShading cfg.globalGrains.slope activeCells label
  F1_mass_retention : scaleData.slabShading.mass ≤ 2 * F1.mass
  total_label_bound : (labels.card : ENNReal) ≤
    ENNReal.ofReal (scale.1 / delta + 2) *
      (24 * Kakeya.realRpowENN delta (-grainLoss) *
        Kakeya.realRpowENN (1 / delta) (1 - sigma))
  label_anchor : ∀ label, label ∈ keptLabels → ℤ × ℤ × ℤ
  label_anchor_mem : ∀ label (hlabel : label ∈ keptLabels),
    label_anchor label hlabel ∈ pureWZ2GlobalGrainFiber
      cfg.globalGrains.slope delta activeCells label
  label_grain_containment : ∀ label (hlabel : label ∈ keptLabels),
    ⋃ cell ∈ pureWZ2GlobalGrainFiber
        cfg.globalGrains.slope delta activeCells label,
      wz1PaperGridCube delta cell ⊆
    pureWZ2GlobalGrainWithConstant 4 cfg.globalGrains.slope delta
      (pureWZ2PaperCellCenter delta (label_anchor label hlabel))
  label_volume : ∀ label ∈ keptLabels,
    volume (⋃ cell ∈ pureWZ2GlobalGrainFiber
        cfg.globalGrains.slope delta activeCells label,
      wz1PaperGridCube delta cell) =
      ((pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta
        activeCells label).card : ENNReal) * ENNReal.ofReal (delta ^ 3)
  label_incidence_mass_upper : ∀ label ∈ keptLabels,
    pureWZ2GlobalLabelIncidenceMass scaleData.slabShading
        cfg.globalGrains.slope activeCells label ≤
      (Kakeya.realRpowENN (delta / scale.1)
          (2 - sigma - slabLoss) *
        cfg.family.enncard) *
        volume (⋃ cell ∈ pureWZ2GlobalGrainFiber
            cfg.globalGrains.slope delta activeCells label,
          wz1PaperGridCube delta cell)
  label_volume_lower : ∀ label ∈ keptLabels,
    labelThreshold /
        (Kakeya.realRpowENN (delta / scale.1)
          (2 - sigma - slabLoss) *
          cfg.family.enncard) ≤
      volume (⋃ cell ∈ pureWZ2GlobalGrainFiber
          cfg.globalGrains.slope delta activeCells label,
        wz1PaperGridCube delta cell)

/-- Any pointwise multiplicity cap for the slab shading bounds the incidence
mass of each popular global label by cap times spatial volume. -/
theorem PureWZ2WeightedPopularGlobalGrainData.label_incidence_mass_upper_of_cap
    {sigma grainLoss slabLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    {cap : ENNReal}
    (hcap : ∀ point,
      (scaleData.slabShading.pointMultiplicity point : ENNReal) ≤ cap)
    (label : ℤ × ℤ) (hlabel : label ∈ popular.keptLabels) :
    pureWZ2GlobalLabelIncidenceMass scaleData.slabShading
        cfg.globalGrains.slope popular.activeCells label ≤
      cap * volume (⋃ cell ∈ pureWZ2GlobalGrainFiber
          cfg.globalGrains.slope delta popular.activeCells label,
        wz1PaperGridCube delta cell) := by
  let region : Set Point3 :=
    ⋃ cell ∈ pureWZ2GlobalGrainFiber
        cfg.globalGrains.slope delta popular.activeCells label,
      wz1PaperGridCube delta cell
  let labelShading : WZ1PaperTubeShading cfg.family :=
    wz2RefinedShading scaleData.slabShading
      (pureWZ2GlobalGrainFiber
        cfg.globalGrains.slope delta popular.activeCells label)
  have hweightMass :
      pureWZ2GlobalLabelIncidenceMass scaleData.slabShading
          cfg.globalGrains.slope popular.activeCells label =
        labelShading.mass := by
    rw [wz2RefinedShading_mass_eq_sum_cells]
    rfl
  have hlabelActive : ∀ cell ∈ pureWZ2GlobalGrainFiber
      cfg.globalGrains.slope delta popular.activeCells label,
      cell ∈ wz1PaperActiveCells scaleData.slabShading
        cfg.extremal.delta_pos := by
    intro cell hcell
    have hactive := (mem_pureWZ2GlobalGrainFiber
      cfg.globalGrains.slope delta popular.activeCells label cell).mp hcell |>.1
    simpa [popular.activeCells_eq] using hactive
  have hlabelUnion : labelShading.union = region :=
    wz2RefinedShading_union_eq scaleData.slab_cubical
      cfg.extremal.delta_pos hlabelActive
  have hlabelCap : ∀ point ∈ labelShading.union,
      (labelShading.pointMultiplicity point : ENNReal) ≤ cap := by
    intro point _
    have hnat : labelShading.pointMultiplicity point ≤
        scaleData.slabShading.pointMultiplicity point := by
      apply Finset.card_le_card
      intro index hindex
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hindex).2.1⟩
    have hnatENN : (labelShading.pointMultiplicity point : ENNReal) ≤
        (scaleData.slabShading.pointMultiplicity point : ENNReal) := by
      exact_mod_cast hnat
    exact hnatENN.trans (hcap point)
  rw [hweightMass]
  calc
    labelShading.mass ≤ cap * volume labelShading.union :=
      mass_le_of_pointMultiplicity_le hlabelCap
    _ = cap * volume region := by rw [hlabelUnion]
    _ = _ := rfl

/-- A popular label is spatially large under any finite nonzero pointwise
multiplicity cap. -/
theorem PureWZ2WeightedPopularGlobalGrainData.label_volume_lower_of_cap
    {sigma grainLoss slabLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    {cap : ENNReal} (hcapZero : cap ≠ 0) (hcapTop : cap ≠ ⊤)
    (hcap : ∀ point,
      (scaleData.slabShading.pointMultiplicity point : ENNReal) ≤ cap)
    (label : ℤ × ℤ) (hlabel : label ∈ popular.keptLabels) :
    popular.labelThreshold / cap ≤
      volume (⋃ cell ∈ pureWZ2GlobalGrainFiber
          cfg.globalGrains.slope delta popular.activeCells label,
        wz1PaperGridCube delta cell) := by
  apply (ENNReal.div_le_iff hcapZero hcapTop).mpr
  have hthreshold := popular.label_mass_lower label hlabel
  have hupper := popular.label_incidence_mass_upper_of_cap hcap label hlabel
  simpa [mul_comm] using hthreshold.trans hupper

/-- Assemble the logarithm-free incidence-mass popularity refinement. -/
theorem pureWZ2_weightedPopularGlobalGrains
    {sigma grainLoss slabLoss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData
      cfg.shading sigma slabLoss scale) :
    Nonempty (PureWZ2WeightedPopularGlobalGrainData
      cfg scale scaleData) := by
  let activeCells := wz1PaperActiveCells
    scaleData.slabShading cfg.extremal.delta_pos
  let labels := pureWZ2GlobalGrainLabels
    cfg.globalGrains.slope delta activeCells
  let weight := pureWZ2GlobalLabelIncidenceMass
    scaleData.slabShading cfg.globalGrains.slope activeCells
  have hsourceMass : scaleData.slabShading.mass ≠ 0 := by
    have hleft :
        0 < ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (slabLoss + 2) *
            cfg.family.enncard * ENNReal.ofReal scale.1 := by
      have hpi : 0 < ENNReal.ofReal (Real.pi / 4) :=
        ENNReal.ofReal_pos.mpr (by positivity)
      have hrpow : 0 < Kakeya.realRpowENN delta (slabLoss + 2) := by
        simp [Kakeya.realRpowENN,
          Real.rpow_pos_of_pos cfg.extremal.delta_pos]
      have hfamily : 0 < cfg.family.enncard := by
        rw [show cfg.family.enncard = (cfg.family.card : ENNReal) by rfl]
        exact_mod_cast cfg.extremal.nonempty
      have hscale : 0 < ENNReal.ofReal scale.1 :=
        ENNReal.ofReal_pos.mpr
          (cfg.extremal.delta_pos.trans_le scale.2.1)
      positivity
    exact (hleft.trans_le scaleData.slab_mass).ne'
  have hlabelsNonempty : labels.Nonempty := by
    by_contra hlabels
    have hlabelsEmpty : labels = ∅ := Finset.not_nonempty_iff_eq_empty.mp hlabels
    have hsum := pureWZ2_sum_globalLabelIncidenceMass
      scaleData.slabShading cfg.globalGrains.slope
      scaleData.slab_cubical cfg.extremal.delta_pos
    rw [show pureWZ2GlobalGrainLabels cfg.globalGrains.slope delta
        (wz1PaperActiveCells scaleData.slabShading
          cfg.extremal.delta_pos) = labels by rfl,
      hlabelsEmpty] at hsum
    simp at hsum
    exact hsourceMass hsum.symm
  have hsourceTop : scaleData.slabShading.mass ≠ ⊤ := by
    have hcarrierTop : ∀ index,
        volume (scaleData.slabShading.carrier index) ≠ ⊤ := by
      intro index
      have hsubset : scaleData.slabShading.carrier index ⊆
          Kakeya.Streamlined.axisBox 2 2 2 :=
        (scaleData.slabShading.subset_body index).trans fun _ h => h.2
      exact ne_top_of_le_ne_top
        (show volume (Kakeya.Streamlined.axisBox 2 2 2) ≠ ⊤ by
          rw [Kakeya.Streamlined.volume_axisBox 2 2 2]
          · exact ENNReal.ofReal_ne_top
          all_goals norm_num)
        (measure_mono hsubset)
    exact ENNReal.sum_ne_top.2 fun index _ => hcarrierTop index
  let denominator : ENNReal := ((2 * labels.card : ℕ) : ENNReal)
  have hdenominatorZero : denominator ≠ 0 := by
    simp [denominator, hlabelsNonempty.card_pos.ne']
  have hdenominatorTop : denominator ≠ ⊤ := by
    exact ENNReal.natCast_ne_top _
  let labelThreshold : ENNReal := scaleData.slabShading.mass / denominator
  have hthresholdPos : 0 < labelThreshold :=
    ENNReal.div_pos hsourceMass hdenominatorTop
  have hthresholdTop : labelThreshold ≠ ⊤ :=
    ENNReal.div_ne_top hsourceTop hdenominatorZero
  have hthresholdIdentity :
      2 * ((labels.card : ENNReal) * labelThreshold) =
        scaleData.slabShading.mass := by
    have hfactor : 2 * (labels.card : ENNReal) = denominator := by
      simp [denominator]
    calc
      2 * ((labels.card : ENNReal) * labelThreshold) =
          denominator * labelThreshold := by rw [← hfactor]; ring
      _ = scaleData.slabShading.mass := by
        exact ENNReal.mul_div_cancel hdenominatorZero hdenominatorTop
  let keptLabels := labels.filter fun label => labelThreshold ≤ weight label
  have hsumWeight : (∑ label ∈ labels, weight label) =
      scaleData.slabShading.mass := by
    simpa [labels, weight, activeCells] using
      pureWZ2_sum_globalLabelIncidenceMass
        scaleData.slabShading cfg.globalGrains.slope
        scaleData.slab_cubical cfg.extremal.delta_pos
  have hretainedMass : scaleData.slabShading.mass ≤
      2 * ∑ label ∈ keptLabels, weight label := by
    rw [← hsumWeight]
    exact finite_sum_le_two_mul_heavy_sum labels weight labelThreshold
      hthresholdTop (by rw [hthresholdIdentity, hsumWeight])
  have hkeptNonempty : keptLabels.Nonempty := by
    by_contra h
    have hempty : keptLabels = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hempty] at hretainedMass
    simp at hretainedMass
    exact hsourceMass hretainedMass
  let retainedCells := keptLabels.biUnion
    (pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta activeCells)
  have hretainedSubset : retainedCells ⊆ activeCells := by
    intro cell hcell
    rcases Finset.mem_biUnion.mp hcell with ⟨label, _, hfiber⟩
    exact (mem_pureWZ2GlobalGrainFiber
      cfg.globalGrains.slope delta activeCells label cell).mp hfiber |>.1
  let F1 := wz2RefinedShading scaleData.slabShading retainedCells
  have hF1Cubical : WZ1PaperIsCubicalShading F1 :=
    wz2RefinedShading_cubical scaleData.slab_cubical
  have hF1InSlab : ∀ index, F1.carrier index ⊆
      horizontalSlab scaleData.slabLeft scaleData.slabRight := by
    intro index
    exact (wz2RefinedShading_subshading index).trans
      (scaleData.slab_in_slab index)
  have hF1Mass : F1.mass = ∑ label ∈ keptLabels, weight label := by
    rw [show F1 = wz2RefinedShading
        scaleData.slabShading retainedCells by rfl,
      wz2RefinedShading_mass_eq_sum_cells]
    change (∑ cell ∈ retainedCells,
      ∑ index : Fin cfg.family.card,
        volume (scaleData.slabShading.carrier index ∩
          wz1PaperGridCube delta cell)) = _
    rw [show retainedCells = keptLabels.biUnion
      (pureWZ2GlobalGrainFiber
        cfg.globalGrains.slope delta activeCells) by rfl]
    rw [Finset.sum_biUnion]
    · rfl
    · intro first hfirst second hsecond hne
      exact pureWZ2GlobalGrainFiber_disjoint
        cfg.globalGrains.slope delta activeCells hne
  have hheightBound := pureWZ2_globalGrainHeights_card_bound
    cfg.extremal.delta_pos activeCells (fun _ h => h)
    scaleData.slab_ordered scaleData.slab_in_slab
  have hbinBound : ∀ heightIndex ∈ pureWZ2GlobalGrainHeights activeCells,
      (((activeCells.filter fun cell => cell.2.2 = heightIndex).image
        fun cell => (pureWZ2GlobalGrainLabel
          cfg.globalGrains.slope delta cell).2).card : ENNReal) ≤
        24 * Kakeya.realRpowENN delta (-grainLoss) *
          Kakeya.realRpowENN (1 / delta) (1 - sigma) := by
    intro heightIndex hheightIndex
    rcases Finset.mem_image.mp hheightIndex with ⟨cell, hcell, hcellHeight⟩
    have hcenterUnion := pureWZ2_activeCellCenter_mem_union
      cfg.extremal.delta_pos scaleData.slab_cubical hcell
    rcases hcenterUnion with ⟨index, hcarrier⟩
    have hslab := scaleData.slab_in_slab index hcarrier
    have hheight : ((heightIndex : ℝ) + 1 / 2) * delta ∈
        Set.Icc (-1 : ℝ) 1 := by
      have hcenterEq : (pureWZ2PaperCellCenter delta cell) 2 =
          ((heightIndex : ℝ) + 1 / 2) * delta := by simp [hcellHeight]
      rw [← hcenterEq]
      exact ⟨scaleData.slabLeft_mem.trans hslab.1,
        hslab.2.trans scaleData.slabRight_mem⟩
    exact pureWZ2_globalBinsAtHeight_card_bound cfg
      scaleData.slab_cubical scaleData.slab_subshading
      activeCells (fun _ h => h) heightIndex hheight
  have hlabelBoundBase := pureWZ2_globalLabels_enncard_le_height_mul_bins
    cfg.globalGrains.slope delta activeCells
    (24 * Kakeya.realRpowENN delta (-grainLoss) *
      Kakeya.realRpowENN (1 / delta) (1 - sigma)) hbinBound
  have hlabelBound : (labels.card : ENNReal) ≤
      ENNReal.ofReal (scale.1 / delta + 2) *
        (24 * Kakeya.realRpowENN delta (-grainLoss) *
          Kakeya.realRpowENN (1 / delta) (1 - sigma)) := by
    have hheightENN :
        ((pureWZ2GlobalGrainHeights activeCells).card : ENNReal) ≤
          ENNReal.ofReal (scale.1 / delta + 2) := by
      rw [← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_mono
      rw [scaleData.slab_width] at hheightBound
      exact hheightBound
    exact hlabelBoundBase.trans (mul_le_mul_right' hheightENN _)
  have hfiberNonempty : ∀ label ∈ keptLabels,
      (pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta
        activeCells label).Nonempty := by
    intro label hlabel
    have hoccupied : label ∈ labels := (Finset.mem_filter.mp hlabel).1
    rcases (mem_pureWZ2GlobalGrainLabels
      cfg.globalGrains.slope delta activeCells label).mp hoccupied with
      ⟨cell, hcell, hlabelCell⟩
    exact ⟨cell, (mem_pureWZ2GlobalGrainFiber
      cfg.globalGrains.slope delta activeCells label cell).mpr
        ⟨hcell, hlabelCell⟩⟩
  choose labelAnchor hlabelAnchor using hfiberNonempty
  have hanchorHeight : ∀ label (hlabel : label ∈ keptLabels),
      (pureWZ2PaperCellCenter delta (labelAnchor label hlabel)) 2 ∈
        Set.Icc (-1 : ℝ) 1 := by
    intro label hlabel
    have hactive := (mem_pureWZ2GlobalGrainFiber
      cfg.globalGrains.slope delta activeCells label
      (labelAnchor label hlabel)).mp (hlabelAnchor label hlabel) |>.1
    have hcenterUnion := pureWZ2_activeCellCenter_mem_union
      cfg.extremal.delta_pos scaleData.slab_cubical hactive
    rcases hcenterUnion with ⟨index, hcarrier⟩
    have hslab := scaleData.slab_in_slab index hcarrier
    exact ⟨scaleData.slabLeft_mem.trans hslab.1,
      hslab.2.trans scaleData.slabRight_mem⟩
  have hcontainment : ∀ label (hlabel : label ∈ keptLabels),
      ⋃ cell ∈ pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta
          activeCells label, wz1PaperGridCube delta cell ⊆
        pureWZ2GlobalGrainWithConstant 4 cfg.globalGrains.slope delta
          (pureWZ2PaperCellCenter delta (labelAnchor label hlabel)) := by
    intro label hlabel point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
    have hcellLabel := (mem_pureWZ2GlobalGrainFiber
      cfg.globalGrains.slope delta activeCells label cell).mp hcell |>.2
    have hanchorLabel := (mem_pureWZ2GlobalGrainFiber
      cfg.globalGrains.slope delta activeCells label
      (labelAnchor label hlabel)).mp (hlabelAnchor label hlabel) |>.2
    exact pureWZ2_same_label_cell_subset_globalGrain
      cfg.extremal.delta_pos cfg.globalGrains.slope
      cfg.globalGrains.slope_normalized (hanchorHeight label hlabel)
      (hcellLabel.trans hanchorLabel.symm) hpointCell
  have hlabelVolume : ∀ label ∈ keptLabels,
      volume (⋃ cell ∈ pureWZ2GlobalGrainFiber
          cfg.globalGrains.slope delta activeCells label,
        wz1PaperGridCube delta cell) =
      ((pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta activeCells
        label).card : ENNReal) * ENNReal.ofReal (delta ^ 3) := by
    intro label _
    rw [wz1PaperGridCube_volume_biUnion cfg.extremal.delta_pos,
      wz1PaperGridCube_volume_exact cfg.extremal.delta_pos]
  have hlabelVolumeLower : ∀ label ∈ keptLabels,
      labelThreshold /
          (Kakeya.realRpowENN (delta / scale.1)
              (2 - sigma - slabLoss) *
            cfg.family.enncard) ≤
        volume (⋃ cell ∈ pureWZ2GlobalGrainFiber
            cfg.globalGrains.slope delta activeCells label,
          wz1PaperGridCube delta cell) := by
    intro label hlabel
    let region : Set Point3 :=
      ⋃ cell ∈ pureWZ2GlobalGrainFiber
          cfg.globalGrains.slope delta activeCells label,
        wz1PaperGridCube delta cell
    let labelShading : WZ1PaperTubeShading cfg.family :=
      wz2RefinedShading scaleData.slabShading
        (pureWZ2GlobalGrainFiber
          cfg.globalGrains.slope delta activeCells label)
    have hweightMass : weight label = labelShading.mass := by
      rw [wz2RefinedShading_mass_eq_sum_cells]
      rfl
    have hlabelActive : ∀ cell ∈ pureWZ2GlobalGrainFiber
        cfg.globalGrains.slope delta activeCells label,
        cell ∈ wz1PaperActiveCells scaleData.slabShading
          cfg.extremal.delta_pos := by
      intro cell hcell
      exact (mem_pureWZ2GlobalGrainFiber
        cfg.globalGrains.slope delta activeCells label cell).mp hcell |>.1
    have hlabelUnion : labelShading.union = region :=
      wz2RefinedShading_union_eq scaleData.slab_cubical
        cfg.extremal.delta_pos hlabelActive
    have hcap : ∀ point ∈ labelShading.union,
        (labelShading.pointMultiplicity point : ENNReal) ≤
          Kakeya.realRpowENN (delta / scale.1)
              (2 - sigma - slabLoss) *
            cfg.family.enncard := by
      intro point _
      have hnatLabel : labelShading.pointMultiplicity point ≤
          scaleData.slabShading.pointMultiplicity point := by
        apply Finset.card_le_card
        intro index hindex
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hindex).2.1⟩
      have hnatENN : (labelShading.pointMultiplicity point : ENNReal) ≤
          (scaleData.slabShading.pointMultiplicity point : ENNReal) := by
        exact_mod_cast hnatLabel
      exact hnatENN.trans (scaleData.slab_pointMultiplicity_upper point)
    have hmassUpper : weight label ≤
        (Kakeya.realRpowENN (delta / scale.1)
            (2 - sigma - slabLoss) *
          cfg.family.enncard) * volume region := by
      rw [hweightMass, ← hlabelUnion]
      exact mass_le_of_pointMultiplicity_le hcap
    have hthresholdMass : labelThreshold ≤ weight label :=
      (Finset.mem_filter.mp hlabel).2
    have hdenZero :
        Kakeya.realRpowENN (delta / scale.1)
            (2 - sigma - slabLoss) *
            cfg.family.enncard ≠ 0 := by
      have hpower : Kakeya.realRpowENN (delta / scale.1)
          (2 - sigma - slabLoss) ≠ 0 := by
        simp [Kakeya.realRpowENN,
          Real.rpow_pos_of_pos (div_pos cfg.extremal.delta_pos
            (cfg.extremal.delta_pos.trans_le scale.2.1))]
      have hfamily : cfg.family.enncard ≠ 0 := by
        rw [show cfg.family.enncard = (cfg.family.card : ENNReal) by rfl]
        exact_mod_cast cfg.extremal.nonempty.ne'
      exact mul_ne_zero hpower hfamily
    have hdenTop :
        Kakeya.realRpowENN (delta / scale.1)
            (2 - sigma - slabLoss) *
            cfg.family.enncard ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN]) (by
        rw [show cfg.family.enncard = (cfg.family.card : ENNReal) by rfl]
        exact ENNReal.natCast_ne_top _)
    apply (ENNReal.div_le_iff hdenZero hdenTop).mpr
    simpa [region, mul_comm] using hthresholdMass.trans hmassUpper
  have hlabelMassUpper : ∀ label ∈ keptLabels,
      weight label ≤
        (Kakeya.realRpowENN (delta / scale.1)
            (2 - sigma - slabLoss) *
          cfg.family.enncard) *
          volume (⋃ cell ∈ pureWZ2GlobalGrainFiber
              cfg.globalGrains.slope delta activeCells label,
            wz1PaperGridCube delta cell) := by
    intro label hlabel
    let region : Set Point3 :=
      ⋃ cell ∈ pureWZ2GlobalGrainFiber
          cfg.globalGrains.slope delta activeCells label,
        wz1PaperGridCube delta cell
    let labelShading : WZ1PaperTubeShading cfg.family :=
      wz2RefinedShading scaleData.slabShading
        (pureWZ2GlobalGrainFiber
          cfg.globalGrains.slope delta activeCells label)
    have hweightMass : weight label = labelShading.mass := by
      rw [wz2RefinedShading_mass_eq_sum_cells]
      rfl
    have hlabelActive : ∀ cell ∈ pureWZ2GlobalGrainFiber
        cfg.globalGrains.slope delta activeCells label,
        cell ∈ wz1PaperActiveCells scaleData.slabShading
          cfg.extremal.delta_pos := by
      intro cell hcell
      exact (mem_pureWZ2GlobalGrainFiber
        cfg.globalGrains.slope delta activeCells label cell).mp hcell |>.1
    have hlabelUnion : labelShading.union = region :=
      wz2RefinedShading_union_eq scaleData.slab_cubical
        cfg.extremal.delta_pos hlabelActive
    have hcap : ∀ point ∈ labelShading.union,
        (labelShading.pointMultiplicity point : ENNReal) ≤
          Kakeya.realRpowENN (delta / scale.1)
              (2 - sigma - slabLoss) *
            cfg.family.enncard := by
      intro point _
      have hnatLabel : labelShading.pointMultiplicity point ≤
          scaleData.slabShading.pointMultiplicity point := by
        apply Finset.card_le_card
        intro index hindex
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hindex).2.1⟩
      have hnatENN : (labelShading.pointMultiplicity point : ENNReal) ≤
          (scaleData.slabShading.pointMultiplicity point : ENNReal) := by
        exact_mod_cast hnatLabel
      exact hnatENN.trans (scaleData.slab_pointMultiplicity_upper point)
    rw [hweightMass]
    calc
      labelShading.mass ≤
          (Kakeya.realRpowENN (delta / scale.1)
              (2 - sigma - slabLoss) *
            cfg.family.enncard) * volume labelShading.union :=
        mass_le_of_pointMultiplicity_le hcap
      _ = _ := by rw [hlabelUnion]
  exact ⟨{
    activeCells := activeCells
    activeCells_eq := rfl
    labels := labels
    labels_eq := rfl
    labelThreshold := labelThreshold
    labelThreshold_pos := hthresholdPos
    labelThreshold_identity := hthresholdIdentity
    keptLabels := keptLabels
    keptLabels_eq := rfl
    keptLabels_nonempty := hkeptNonempty
    label_mass_lower := fun label hlabel => (Finset.mem_filter.mp hlabel).2
    retainedCells := retainedCells
    retainedCells_eq := rfl
    retainedCells_subset := hretainedSubset
    F1 := F1
    F1_eq := rfl
    F1_cubical := hF1Cubical
    F1_in_slab := hF1InSlab
    F1_mass_eq := hF1Mass
    F1_mass_retention := by simpa [hF1Mass] using hretainedMass
    total_label_bound := hlabelBound
    label_anchor := labelAnchor
    label_anchor_mem := hlabelAnchor
    label_grain_containment := hcontainment
    label_volume := hlabelVolume
    label_incidence_mass_upper := hlabelMassUpper
    label_volume_lower := hlabelVolumeLower
  }⟩

end Kakeya.Assouad

end
