import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularRichHeightVolume

/-!
# Refill interior outer-popular rich heights on the original selected family

The outer-popular slice selects the fixed line and official parent indices.
The auxiliary graph is built on localized pieces of that same measured
carrier, while complete terminal parents supply only heterogeneous local-normal
witnesses.  Before returning to the whole terminal selected family, at most
the two snapped height slabs crossing the endpoints of the common parent core
are discarded.  This is the discrete form of the paper's `Z_lin subset Z_S`
refill and avoids imposing the selected-parent region on the final source
mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

def pureWZ2TerminalPopularRichFloor
    (delta outputLoss : ℝ) : ENNReal :=
  Kakeya.realRpowENN
    (wz1Lemma23Theorem22Scale (delta / 625)) (outputLoss - 1)

/-- The refined Katz--Tao threshold makes the rich-height floor large enough
to absorb deletion of the two snapped slabs crossing the exact core. -/
theorem pureWZ2_terminalPopular_richFloor_four
    {delta epsilon theoremEta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hepsilonTheorem : epsilon + theoremEta ≤ 1)
    (hkatz : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale (delta / 625)) (-theoremEta)) :
    (4 : ENNReal) ≤ pureWZ2TerminalPopularRichFloor delta epsilon := by
  let graphScale := wz1Lemma23Theorem22Scale (delta / 625)
  have hgraphPos : 0 < graphScale := by
    dsimp only [graphScale, wz1Lemma23Theorem22Scale]
    positivity
  have hgraphOne : graphScale ≤ 1 := by
    dsimp only [graphScale, wz1Lemma23Theorem22Scale]
    have hdenom : 1 ≤ 5 * Real.sqrt 3 := by
      have hsqrt : 1 ≤ Real.sqrt 3 := Real.one_le_sqrt.mpr (by norm_num)
      nlinarith
    have hquot : delta / 625 ≤ 1 := by nlinarith
    exact (div_le_self (Real.sqrt_nonneg (delta / 625)) hdenom).trans
      (Real.sqrt_le_one.mpr hquot)
  calc
    (4 : ENNReal) ≤ Kakeya.realRpowENN graphScale (-theoremEta) := by
      simpa [graphScale] using hkatz
    _ ≤ Kakeya.realRpowENN graphScale (epsilon - 1) := by
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge hgraphPos
        hgraphOne (by linarith)
    _ = pureWZ2TerminalPopularRichFloor delta epsilon := by
      rfl

/-- Among equal-grid height intervals meeting one fixed core interval, at most
two fail to lie inside the core: one may cross each endpoint. -/
private theorem pureWZ2_heightInterval_boundary_card
    {delta left right : ℝ} (hdelta : 0 < delta)
    (heights : Finset ℤ)
    (hinter : ∀ heightIndex ∈ heights,
      (wz1Lemma23HeightInterval delta heightIndex ∩
        Set.Icc left right).Nonempty) :
    (heights.filter (fun heightIndex =>
      ¬ (wz1Lemma23HeightInterval delta heightIndex ⊆
        Set.Icc left right))).card ≤ 2 := by
  let boundary := heights.filter fun heightIndex =>
    ¬ (wz1Lemma23HeightInterval delta heightIndex ⊆ Set.Icc left right)
  let crossesLeft := boundary.filter (fun heightIndex : ℤ =>
    (heightIndex : ℝ) * gridSide (delta / 2) < left)
  let crossesRight := boundary.filter (fun heightIndex : ℤ =>
    ¬ (heightIndex : ℝ) * gridSide (delta / 2) < left)
  have hleftCard : crossesLeft.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro first second hfirst hsecond
    have hfirst' := Finset.mem_filter.mp hfirst
    have hsecond' := Finset.mem_filter.mp hsecond
    have hfirstBoundary := Finset.mem_filter.mp hfirst'.1
    have hsecondBoundary := Finset.mem_filter.mp hsecond'.1
    rcases hinter first hfirstBoundary.1 with ⟨firstPoint,
      hfirstInterval, hfirstCore⟩
    rcases hinter second hsecondBoundary.1 with ⟨secondPoint,
      hsecondInterval, hsecondCore⟩
    have hleftFirst : left ∈ wz1Lemma23HeightInterval delta first := by
      change (first : ℝ) * gridSide (delta / 2) ≤ left ∧
        left < ((first : ℝ) + 1) * gridSide (delta / 2)
      change (first : ℝ) * gridSide (delta / 2) ≤ firstPoint ∧
        firstPoint < ((first : ℝ) + 1) * gridSide (delta / 2) at hfirstInterval
      exact ⟨hfirst'.2.le, lt_of_le_of_lt hfirstCore.1 hfirstInterval.2⟩
    have hleftSecond : left ∈ wz1Lemma23HeightInterval delta second := by
      change (second : ℝ) * gridSide (delta / 2) ≤ left ∧
        left < ((second : ℝ) + 1) * gridSide (delta / 2)
      change (second : ℝ) * gridSide (delta / 2) ≤ secondPoint ∧
        secondPoint < ((second : ℝ) + 1) * gridSide (delta / 2) at hsecondInterval
      exact ⟨hsecond'.2.le, lt_of_le_of_lt hsecondCore.1 hsecondInterval.2⟩
    let point : Point3 := point3 0 0 left
    have hfirstSlab : point ∈ wz1Lemma23HeightSlab delta first := by
      simpa [point, point3, wz1Lemma23HeightSlab] using hleftFirst
    have hsecondSlab : point ∈ wz1Lemma23HeightSlab delta second := by
      simpa [point, point3, wz1Lemma23HeightSlab] using hleftSecond
    have hfirstFloor :=
      (wz1Lemma23_mem_heightSlab_iff hdelta first point).mp hfirstSlab
    have hsecondFloor :=
      (wz1Lemma23_mem_heightSlab_iff hdelta second point).mp hsecondSlab
    exact hfirstFloor.symm.trans hsecondFloor
  have hrightCard : crossesRight.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro first second hfirst hsecond
    have hfirst' := Finset.mem_filter.mp hfirst
    have hsecond' := Finset.mem_filter.mp hsecond
    have hfirstBoundary := Finset.mem_filter.mp hfirst'.1
    have hsecondBoundary := Finset.mem_filter.mp hsecond'.1
    rcases hinter first hfirstBoundary.1 with ⟨firstPoint,
      hfirstInterval, hfirstCore⟩
    rcases hinter second hsecondBoundary.1 with ⟨secondPoint,
      hsecondInterval, hsecondCore⟩
    have hrightFirst : right ∈ wz1Lemma23HeightInterval delta first := by
      change (first : ℝ) * gridSide (delta / 2) ≤ right ∧
        right < ((first : ℝ) + 1) * gridSide (delta / 2)
      change (first : ℝ) * gridSide (delta / 2) ≤ firstPoint ∧
        firstPoint < ((first : ℝ) + 1) * gridSide (delta / 2) at hfirstInterval
      have hleftLower : left ≤
          (first : ℝ) * gridSide (delta / 2) := le_of_not_gt hfirst'.2
      have hrightUpper : right <
          ((first : ℝ) + 1) * gridSide (delta / 2) := by
        by_contra hnot
        apply hfirstBoundary.2
        intro value hvalue
        change (first : ℝ) * gridSide (delta / 2) ≤ value ∧
          value < ((first : ℝ) + 1) * gridSide (delta / 2) at hvalue
        exact ⟨hleftLower.trans hvalue.1,
          hvalue.2.le.trans (le_of_not_gt hnot)⟩
      exact ⟨hfirstInterval.1.trans hfirstCore.2, hrightUpper⟩
    have hrightSecond : right ∈ wz1Lemma23HeightInterval delta second := by
      change (second : ℝ) * gridSide (delta / 2) ≤ right ∧
        right < ((second : ℝ) + 1) * gridSide (delta / 2)
      change (second : ℝ) * gridSide (delta / 2) ≤ secondPoint ∧
        secondPoint < ((second : ℝ) + 1) * gridSide (delta / 2) at hsecondInterval
      have hleftLower : left ≤
          (second : ℝ) * gridSide (delta / 2) := le_of_not_gt hsecond'.2
      have hrightUpper : right <
          ((second : ℝ) + 1) * gridSide (delta / 2) := by
        by_contra hnot
        apply hsecondBoundary.2
        intro value hvalue
        change (second : ℝ) * gridSide (delta / 2) ≤ value ∧
          value < ((second : ℝ) + 1) * gridSide (delta / 2) at hvalue
        exact ⟨hleftLower.trans hvalue.1,
          hvalue.2.le.trans (le_of_not_gt hnot)⟩
      exact ⟨hsecondInterval.1.trans hsecondCore.2, hrightUpper⟩
    let point : Point3 := point3 0 0 right
    have hfirstSlab : point ∈ wz1Lemma23HeightSlab delta first := by
      simpa [point, point3, wz1Lemma23HeightSlab] using hrightFirst
    have hsecondSlab : point ∈ wz1Lemma23HeightSlab delta second := by
      simpa [point, point3, wz1Lemma23HeightSlab] using hrightSecond
    have hfirstFloor :=
      (wz1Lemma23_mem_heightSlab_iff hdelta first point).mp hfirstSlab
    have hsecondFloor :=
      (wz1Lemma23_mem_heightSlab_iff hdelta second point).mp hsecondSlab
    exact hfirstFloor.symm.trans hsecondFloor
  have hsplit : crossesLeft.card + crossesRight.card = boundary.card := by
    simpa [crossesLeft, crossesRight] using
      (Finset.card_filter_add_card_filter_not
        (s := boundary)
        (p := fun heightIndex =>
          (heightIndex : ℝ) * gridSide (delta / 2) < left))
  change boundary.card ≤ 2
  omega

structure PureWZ2TerminalPopularOuterHeightLift
    {sigma inputLoss delta stickyLoss eta theoremEta epsilon : ℝ}
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
    {selectedCarrier :
      PureWZ2TerminalPopularSelectedParentCarrierData selection}
    {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    {graphParents : PureWZ2TerminalPopularGraphParentData prep}
    {localCells : PureWZ2TerminalPopularLocalCellData
      (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells}
    {sharp : PureWZ2TerminalPopularSharpGeometry preparedGraph}
    {first : PureWZ2TerminalPopularReadyGraph
      (theoremEta := theoremEta) sharp}
    {ready : PureWZ2CommonRefinedReadyGraph
      delta theoremEta first.common first.ready}
    (rich : PureWZ2TerminalPopularAlternativeAHeightData ready epsilon) where
  heightIndices_subset_graphPopular :
    rich.heightIndices ⊆ preparedGraph.heightPopular.heightIndices
  heightIndices_subset_outerPopular :
    rich.heightIndices ⊆ heightData.popular.heightIndices
  innerHeightIndices : Finset ℤ := rich.heightIndices.filter fun heightIndex =>
    wz1Lemma23HeightInterval delta heightIndex ⊆ Set.Icc
      ((selection.commonParentHeight : ℝ) * terminal.sqrtRequested.1)
      (((selection.commonParentHeight : ℝ) + 1) *
        terminal.sqrtRequested.1)
  innerHeightIndices_eq : innerHeightIndices =
    rich.heightIndices.filter fun heightIndex =>
      wz1Lemma23HeightInterval delta heightIndex ⊆ Set.Icc
        ((selection.commonParentHeight : ℝ) * terminal.sqrtRequested.1)
        (((selection.commonParentHeight : ℝ) + 1) *
          terminal.sqrtRequested.1)
  innerHeightIndices_subset : innerHeightIndices ⊆ rich.heightIndices
  boundary_height_card :
    (rich.heightIndices.filter fun heightIndex =>
      ¬ (wz1Lemma23HeightInterval delta heightIndex ⊆ Set.Icc
        ((selection.commonParentHeight : ℝ) * terminal.sqrtRequested.1)
        (((selection.commonParentHeight : ℝ) + 1) *
          terminal.sqrtRequested.1))).card ≤ 2
  richRegion : Set Point3 :=
    ⋃ heightIndex ∈ innerHeightIndices,
      wz1Lemma23HeightSlab delta heightIndex
  richRegion_eq : richRegion =
    ⋃ heightIndex ∈ innerHeightIndices,
      wz1Lemma23HeightSlab delta heightIndex
  richRegion_measurable : MeasurableSet richRegion
  region : Set Point3 := richRegion
  region_eq : region = richRegion
  shading : WZ1PaperTubeShading terminal.sticky.selected.family
  carrier_eq : ∀ index, shading.carrier index =
    terminalSource.shading.carrier index ∩ region
  subshading : PureWZ2PaperIsSubshading shading terminalSource.shading
  union_eq : shading.union = terminalSource.shading.union ∩ region
  union_height : ∀ point ∈ shading.union,
    point (2 : Fin 3) ∈ Set.Icc
      ((selection.commonParentHeight : ℝ) * terminal.sqrtRequested.1)
      (((selection.commonParentHeight : ℝ) + 1) *
        terminal.sqrtRequested.1)
  constant_multiplicity : shading.HasConstantMultiplicity
    terminalSource.multiplicity (2 * terminalSource.multiplicity)
  volume_lower :
    (innerHeightIndices.card : ENNReal) *
        heightData.popular.layerMass ≤ volume shading.union
  multiplicity_mass_lower :
    (terminalSource.multiplicity : ENNReal) * volume shading.union ≤
      shading.mass

theorem PureWZ2TerminalPopularAlternativeAHeightData.toOuterHeightLift
    {sigma inputLoss delta stickyLoss eta theoremEta epsilon : ℝ}
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
    {selectedCarrier :
      PureWZ2TerminalPopularSelectedParentCarrierData selection}
    {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    {graphParents : PureWZ2TerminalPopularGraphParentData prep}
    {localCells : PureWZ2TerminalPopularLocalCellData
      (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells}
    {sharp : PureWZ2TerminalPopularSharpGeometry preparedGraph}
    {first : PureWZ2TerminalPopularReadyGraph
      (theoremEta := theoremEta) sharp}
    {ready : PureWZ2CommonRefinedReadyGraph
      delta theoremEta first.common first.ready}
    (rich : PureWZ2TerminalPopularAlternativeAHeightData ready epsilon) :
    Nonempty (PureWZ2TerminalPopularOuterHeightLift rich) := by
  rcases rich.toRichHeightVolume with ⟨richVolume⟩
  let core : Set ℝ := Set.Icc
    ((selection.commonParentHeight : ℝ) * terminal.sqrtRequested.1)
    (((selection.commonParentHeight : ℝ) + 1) * terminal.sqrtRequested.1)
  let innerHeightIndices := rich.heightIndices.filter fun heightIndex =>
    wz1Lemma23HeightInterval delta heightIndex ⊆ core
  have hinnerSubset : innerHeightIndices ⊆ rich.heightIndices :=
    Finset.filter_subset _ _
  have hboundaryCard :
      (rich.heightIndices.filter fun heightIndex =>
        ¬ wz1Lemma23HeightInterval delta heightIndex ⊆ core).card ≤ 2 := by
    apply pureWZ2_heightInterval_boundary_card source.extremal.delta_pos
    intro heightIndex hheightIndex
    simpa [core] using
      richVolume.heightSlab_inter_commonCore heightIndex hheightIndex
  let richRegion : Set Point3 :=
    ⋃ heightIndex ∈ innerHeightIndices,
      wz1Lemma23HeightSlab delta heightIndex
  have hregionMeas : MeasurableSet richRegion :=
    MeasurableSet.biUnion innerHeightIndices.finite_toSet.countable
      (fun heightIndex _ => by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval delta heightIndex)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  let region := richRegion
  let shading : WZ1PaperTubeShading terminal.sticky.selected.family := {
    carrier := fun index => terminalSource.shading.carrier index ∩ region
    measurable_carrier := fun index =>
      (terminalSource.shading.measurable_carrier index).inter
        hregionMeas
    subset_body := fun index => Set.inter_subset_left.trans
      (terminalSource.shading.subset_body index)
  }
  have hsub : PureWZ2PaperIsSubshading shading terminalSource.shading :=
    fun _ => Set.inter_subset_left
  have hunion : shading.union = terminalSource.shading.union ∩ region := by
    ext point
    constructor
    · rintro ⟨index, hsource, hregion⟩
      exact ⟨⟨index, hsource⟩, hregion⟩
    · rintro ⟨⟨index, hsource⟩, hregion⟩
      exact ⟨index, hsource, hregion⟩
  have hconstant : shading.HasConstantMultiplicity
      terminalSource.multiplicity (2 * terminalSource.multiplicity) := by
    intro point hpoint
    have hmultiplicity : shading.pointMultiplicity point =
        terminalSource.shading.pointMultiplicity point := by
      unfold Kakeya.Streamlined.Shading.pointMultiplicity
      congr 1
      ext index
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, by
          have hunionPoint : point ∈
              terminalSource.shading.union ∩ region := by
            rw [← hunion]
            exact hpoint
          exact hunionPoint.2⟩
    rw [hmultiplicity]
    exact terminalSource.constant_multiplicity point
      (hsub.union_subset hpoint)
  have hvolumeLower :
      (innerHeightIndices.card : ENNReal) *
          heightData.popular.layerMass ≤ volume shading.union := by
    rw [hunion]
    have hpartition : terminalSource.shading.union ∩ richRegion =
        ⋃ heightIndex ∈ innerHeightIndices,
          terminalSource.shading.union ∩
            wz1Lemma23HeightSlab delta heightIndex := by
      ext point
      simp [richRegion]
    rw [hpartition]
    rw [MeasureTheory.measure_biUnion_finset]
    · calc
        (innerHeightIndices.card : ENNReal) *
            heightData.popular.layerMass =
          ∑ _heightIndex ∈ innerHeightIndices,
            heightData.popular.layerMass := by simp [Finset.sum_const]
        _ ≤ ∑ heightIndex ∈ innerHeightIndices,
            volume (terminalSource.shading.union ∩
              wz1Lemma23HeightSlab delta heightIndex) := by
          apply Finset.sum_le_sum
          intro heightIndex hheightIndex
          have houter := richVolume.heightIndices_subset_outerPopular
            (hinnerSubset hheightIndex)
          exact (heightData.popular.layer_volume_band heightIndex houter).1.trans
            (measure_mono <| by
              intro point hpoint
              refine ⟨?_, hpoint.2⟩
              have hprepared := window.subshading.union_subset hpoint.1
              rwa [prepared.shadow_union] at hprepared)
    · intro first _ second _ hne
      exact (wz1Lemma23_heightSlab_disjoint
        source.extremal.delta_pos hne).mono
          Set.inter_subset_right Set.inter_subset_right
    · intro heightIndex _
      exact (measurableSet_shading_union terminalSource.shading).inter (by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval delta heightIndex)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  have hunionHeight : ∀ point ∈ shading.union,
      point (2 : Fin 3) ∈ Set.Icc
        ((selection.commonParentHeight : ℝ) * terminal.sqrtRequested.1)
        (((selection.commonParentHeight : ℝ) + 1) *
          terminal.sqrtRequested.1) := by
    intro point hpoint
    rw [hunion] at hpoint
    have hregion : point ∈ richRegion := by simpa [region] using hpoint.2
    rw [show richRegion = ⋃ heightIndex ∈ innerHeightIndices,
        wz1Lemma23HeightSlab delta heightIndex by rfl] at hregion
    rcases Set.mem_iUnion₂.mp hregion with
      ⟨heightIndex, hheightIndex, hpointSlab⟩
    have hinside := (Finset.mem_filter.mp hheightIndex).2
    exact hinside hpointSlab
  exact ⟨{
    heightIndices_subset_graphPopular := richVolume.heightIndices_subset
    heightIndices_subset_outerPopular :=
      richVolume.heightIndices_subset_outerPopular
    innerHeightIndices := innerHeightIndices
    innerHeightIndices_eq := rfl
    innerHeightIndices_subset := hinnerSubset
    boundary_height_card := by simpa [core] using hboundaryCard
    richRegion := richRegion
    richRegion_eq := rfl
    richRegion_measurable := hregionMeas
    region := region
    region_eq := rfl
    shading := shading
    carrier_eq := fun _ => rfl
    subshading := hsub
    union_eq := hunion
    union_height := hunionHeight
    constant_multiplicity := hconstant
    volume_lower := hvolumeLower
    multiplicity_mass_lower :=
      (constant_multiplicity_mass_volume_generic hconstant).1 }⟩

theorem PureWZ2TerminalPopularOuterHeightLift.source_window_volume_retention
    {sigma inputLoss delta stickyLoss eta theoremEta epsilon localMassLoss : ℝ}
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
    {selectedCarrier :
      PureWZ2TerminalPopularSelectedParentCarrierData selection}
    {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    {graphParents : PureWZ2TerminalPopularGraphParentData prep}
    {localCells : PureWZ2TerminalPopularLocalCellData
      (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells}
    {sharp : PureWZ2TerminalPopularSharpGeometry preparedGraph}
    {first : PureWZ2TerminalPopularReadyGraph
      (theoremEta := theoremEta) sharp}
    {ready : PureWZ2CommonRefinedReadyGraph
      delta theoremEta first.common first.ready}
    {rich : PureWZ2TerminalPopularAlternativeAHeightData ready epsilon}
    (heightLift : PureWZ2TerminalPopularOuterHeightLift rich)
    (hfloorFour : (4 : ENNReal) ≤
      pureWZ2TerminalPopularRichFloor delta epsilon)
    (hscalar :
      16 * Kakeya.realRpowENN delta localMassLoss *
          (heightData.popular.bins : ENNReal) *
          (heightData.popular.heightIndices.card : ENNReal) ≤
        pureWZ2TerminalPopularRichFloor delta epsilon) :
    2 * Kakeya.realRpowENN delta localMassLoss *
        volume window.shading.union ≤ volume heightLift.shading.union := by
  let layerMass := heightData.popular.layerMass
  let floor := pureWZ2TerminalPopularRichFloor delta epsilon
  have hpopularVolume : volume heightData.popular.shading.union ≤
      2 * (heightData.popular.heightIndices.card : ENNReal) *
        layerMass := by
    rw [heightData.popular.volume_eq_sum]
    calc
      (∑ heightIndex ∈ heightData.popular.heightIndices,
          volume (window.shading.union ∩
            wz1Lemma23HeightSlab delta heightIndex)) ≤
        ∑ _heightIndex ∈ heightData.popular.heightIndices,
          2 * layerMass := by
        exact Finset.sum_le_sum fun heightIndex hheight =>
          (heightData.popular.layer_volume_band
            heightIndex hheight).2
      _ = 2 *
          (heightData.popular.heightIndices.card : ENNReal) *
          layerMass := by simp [Finset.sum_const]; ring
  have hwindow : volume window.shading.union ≤
      4 * (heightData.popular.bins : ENNReal) *
        (heightData.popular.heightIndices.card : ENNReal) *
          layerMass := by
    calc
      volume window.shading.union ≤
          2 * (heightData.popular.bins : ENNReal) *
            volume heightData.popular.shading.union := by
        simpa [heightData.graphWindow_supply] using
          heightData.source_volume_retention
      _ ≤ (2 * (heightData.popular.bins : ENNReal)) *
          (2 *
            (heightData.popular.heightIndices.card : ENNReal) *
            layerMass) := by gcongr
      _ = 4 * (heightData.popular.bins : ENNReal) *
          (heightData.popular.heightIndices.card : ENNReal) *
            layerMass := by
        ring
  have hfloor : floor ≤ (rich.heightIndices.card : ENNReal) := by
    have hfloorEq : floor = Kakeya.realRpowENN
        ready.ready.deltaGraph (epsilon - 1) := by
      dsimp only [floor, pureWZ2TerminalPopularRichFloor]
      rw [ready.ready.deltaGraph_eq]
    rw [hfloorEq]
    simpa [rich.heightIndices_card] using rich.richF_card
  let boundary := rich.heightIndices.filter fun heightIndex =>
    ¬ wz1Lemma23HeightInterval delta heightIndex ⊆ Set.Icc
      ((selection.commonParentHeight : ℝ) * terminal.sqrtRequested.1)
      (((selection.commonParentHeight : ℝ) + 1) *
        terminal.sqrtRequested.1)
  have hcardSplit : heightLift.innerHeightIndices.card + boundary.card =
      rich.heightIndices.card := by
    rw [heightLift.innerHeightIndices_eq]
    simpa [boundary] using
      (Finset.card_filter_add_card_filter_not
        (s := rich.heightIndices)
        (p := fun heightIndex =>
          wz1Lemma23HeightInterval delta heightIndex ⊆ Set.Icc
            ((selection.commonParentHeight : ℝ) *
              terminal.sqrtRequested.1)
            (((selection.commonParentHeight : ℝ) + 1) *
              terminal.sqrtRequested.1)))
  have hrichCard : rich.heightIndices.card ≤
      heightLift.innerHeightIndices.card + 2 := by
    have hboundary := heightLift.boundary_height_card
    change boundary.card ≤ 2 at hboundary
    omega
  have hfloorInner : floor ≤
      2 * (heightLift.innerHeightIndices.card : ENNReal) := by
    have hfloorTop : floor ≠ ⊤ := by
      simp [floor, pureWZ2TerminalPopularRichFloor, Kakeya.realRpowENN]
    apply (ENNReal.toReal_le_toReal hfloorTop
      (ENNReal.mul_ne_top (by norm_num) (by simp))).mp
    have hfloorReal : floor.toReal ≤ (rich.heightIndices.card : ℝ) := by
      simpa using (ENNReal.toReal_le_toReal hfloorTop (by simp)).mpr hfloor
    have hfloorFourReal : (4 : ℝ) ≤ floor.toReal := by
      simpa using (ENNReal.toReal_le_toReal (by norm_num) hfloorTop).mpr
        (show (4 : ENNReal) ≤ floor by simpa [floor] using hfloorFour)
    have hrichCardReal : (rich.heightIndices.card : ℝ) ≤
        (heightLift.innerHeightIndices.card : ℝ) + 2 := by
      exact_mod_cast hrichCard
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
    nlinarith
  apply (ENNReal.mul_le_mul_iff_right (show (2 : ENNReal) ≠ 0 by norm_num)
    (show (2 : ENNReal) ≠ ⊤ by norm_num)).mp
  calc
    2 * (2 * Kakeya.realRpowENN delta localMassLoss *
          volume window.shading.union) ≤
        2 * (2 * Kakeya.realRpowENN delta localMassLoss *
          (4 * (heightData.popular.bins : ENNReal) *
            (heightData.popular.heightIndices.card : ENNReal) *
              layerMass)) := by gcongr
    _ = (16 * Kakeya.realRpowENN delta localMassLoss *
          (heightData.popular.bins : ENNReal) *
          (heightData.popular.heightIndices.card : ENNReal)) *
        layerMass := by ring
    _ ≤ floor * layerMass := by gcongr
    _ ≤ (2 * (heightLift.innerHeightIndices.card : ENNReal)) * layerMass := by
      gcongr
    _ = 2 * ((heightLift.innerHeightIndices.card : ENNReal) * layerMass) := by
      ring
    _ ≤ 2 * volume heightLift.shading.union :=
      mul_le_mul_left' heightLift.volume_lower 2

end Kakeya.Assouad
