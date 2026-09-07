import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularPaperOrderChain

/-!
# Exact terminal trapezoid for the heterogeneous popular chain

The carrier is the rich-height refill on the complete terminal selected
family.  Its vertical core is the common official parent-height interval; the
affine approximation is extracted from the rich heights of the outer-popular
graph.  Complete parents supplied only the graph's local-normal witnesses.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalPopularExactTrapezoid
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
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
    {rich : PureWZ2TerminalPopularAlternativeAHeightData ready outputLoss}
    (heightLift : PureWZ2TerminalPopularOuterHeightLift rich) where
  trapezoid : WZ1VerticalTrapezoid
  height_eq : trapezoid.height = delta
  core_eq : trapezoid.core = Set.Icc
    ((selection.commonParentHeight : ℝ) * terminal.sqrtRequested.1)
    (((selection.commonParentHeight : ℝ) + 1) *
      terminal.sqrtRequested.1)
  slope_bound : |trapezoid.slope| ≤ 2
  length_bounds :
    Real.rpow delta (1 / 2 + outputLoss) ≤ trapezoid.length ∧
      trapezoid.length ≤ Real.sqrt delta
  active_height_coverage :
    ∀ z, horizontalSlice heightLift.shading.union z ≠ ∅ →
      z ∈ trapezoid.core
  slope_approximation :
    ∀ z ∈ trapezoid.core,
      horizontalSlice heightLift.shading.union z ≠ ∅ →
        |source.globalGrains.slope z - trapezoid.affine z| ≤ delta
  rich_height_approximation :
    ∀ heightIndex ∈ rich.heightIndices,
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        |z - wz1Lemma23SnappedBaseHeight delta heightIndex| ≤
            delta / (2 * Real.sqrt 3) →
          |source.globalGrains.slope z - trapezoid.affine z| ≤ delta

theorem PureWZ2TerminalPopularOuterHeightLift.toExactTrapezoid
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
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
    {rich : PureWZ2TerminalPopularAlternativeAHeightData ready outputLoss}
    (heightLift : PureWZ2TerminalPopularOuterHeightLift rich)
    (houtputLoss : 0 < outputLoss) :
    Nonempty (PureWZ2TerminalPopularExactTrapezoid heightLift) := by
  let root := terminal.sqrtRequested.1
  let left := (selection.commonParentHeight : ℝ) * root
  let right := ((selection.commonParentHeight : ℝ) + 1) * root
  let baseHeight := wz1Lemma23SnappedBaseHeight delta
    sharp.sharp.baseHeightIndex
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
  have hrootEq : root = Real.sqrt delta := terminal.sqrtRequested_eq
  have hlength : right - left = Real.sqrt delta := by
    dsimp only [right, left]
    rw [hrootEq]
    ring
  have hlengthLower :
      Real.rpow delta (1 / 2 + outputLoss) ≤ Real.sqrt delta := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hdelta
      source.extremal.delta_le_one (by linarith)
  have hextendedLip : ∀ firstHeight secondHeight,
      |prep.windowed.global.extendedSlope firstHeight -
          prep.windowed.global.extendedSlope secondHeight| ≤
        |firstHeight - secondHeight| := by
    intro firstHeight secondHeight
    simpa [Real.dist_eq] using
      prep.windowed.global.extendedSlope_lipschitz.dist_le_mul
        firstHeight (by simp) secondHeight (by simp)
  have hheightDomain : ∀ z,
      horizontalSlice heightLift.shading.union z ≠ ∅ →
        z ∈ Set.Icc (-1 : ℝ) 1 := by
    intro z hslice
    rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint, hheight⟩
    have hterminal : point ∈ terminalSource.shading.union :=
      heightLift.subshading.union_subset hpoint
    rcases hterminal with ⟨index, hindex⟩
    have hsourcePoint : point ∈ source.shading.union :=
      ⟨terminal.sticky.selected.embedding index,
        terminal.sticky.subshading index
          ((congrArg (fun shading => point ∈ shading.carrier index)
            terminalSource.shading_eq).mp hindex)⟩
    have hbox := shading_union_subset_axisBox hsourcePoint
    rw [← hheight]
    have habs : |point 2| ≤ 1 := by
      convert hbox.2.2 using 1 <;> norm_num
    exact abs_le.mp habs
  have hsourceEq : ∀ z, horizontalSlice heightLift.shading.union z ≠ ∅ →
      prep.windowed.global.extendedSlope z = source.globalGrains.slope z := by
    intro z hslice
    have hz := hheightDomain z hslice
    rw [prep.windowed.global.extendedSlope_eq z hz, prep.sourceSlope_eq]
  have hrichCenterFor : ∀ z,
      horizontalSlice heightLift.shading.union z ≠ ∅ →
        ∃ richPoint ∈ rich.richF,
          let center := (wz1Lemma23CellCenter delta
            (rich.pathFor richPoint).2.1) 2
          |z - center| ≤ delta / (2 * Real.sqrt 3) := by
    intro z hslice
    rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint, hheight⟩
    have hregion : point ∈ heightLift.richRegion := by
      rw [heightLift.union_eq, heightLift.region_eq] at hpoint
      exact hpoint.2
    rw [heightLift.richRegion_eq] at hregion
    rcases Set.mem_iUnion₂.mp hregion with
      ⟨heightIndex, hheightIndex, hslab⟩
    have hheightRich := heightLift.innerHeightIndices_subset hheightIndex
    rw [rich.heightIndices_eq] at hheightRich
    rcases Finset.mem_image.mp hheightRich with
      ⟨richPoint, hrichPoint, hheightEq⟩
    refine ⟨richPoint, hrichPoint, ?_⟩
    have hcenterEq :
        (wz1Lemma23CellCenter delta (rich.pathFor richPoint).2.1) 2 =
          ((heightIndex : ℝ) + 1 / 2) * gridSide (delta / 2) := by
      simp [wz1Lemma23CellCenter, point3, ← hheightEq,
        rich.heightIndex_eq richPoint hrichPoint]
    change point 2 ∈ wz1Lemma23HeightInterval delta heightIndex at hslab
    rw [wz1Lemma23HeightInterval] at hslab
    have hside : gridSide (delta / 2) = delta / Real.sqrt 3 := by
      simp [gridSide]
      ring
    have hhalf :
        |point 2 - ((heightIndex : ℝ) + 1 / 2) *
            gridSide (delta / 2)| ≤ gridSide (delta / 2) / 2 := by
      rw [abs_le]
      constructor <;> linarith [hslab.1, hslab.2]
    dsimp only
    rw [← hheight, hcenterEq]
    calc
      _ ≤ gridSide (delta / 2) / 2 := hhalf
      _ = delta / (2 * Real.sqrt 3) := by rw [hside]; ring
  have hcoreCoverage : ∀ z,
      horizontalSlice heightLift.shading.union z ≠ ∅ →
        z ∈ Set.Icc left right := by
    intro z hslice
    rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint, hheight⟩
    have hz := heightLift.union_height point hpoint
    rw [hheight] at hz
    exact hz
  by_cases hnonvertical :
      pureWZ2TerminalDirectionCutoff ≤ |rich.direction 1|
  · let slope := -(rich.direction 0 / rich.direction 1)
    let intercept :=
      prep.windowed.global.extendedSlope baseHeight - slope * baseHeight
    let trapezoid : WZ1VerticalTrapezoid :=
      { left := left
        right := right
        left_lt_right := by dsimp only [left, right]; linarith
        slope := slope
        intercept := intercept
        height := delta
        height_pos := hdelta }
    have hslope : |slope| ≤ 5 / 3 := by
      dsimp only [slope]
      exact pureWZ2_terminal_slope_bound rich.direction
        rich.direction_unit hnonvertical
    have hrichHeightApprox :
        ∀ heightIndex ∈ rich.heightIndices,
          ∀ z ∈ Set.Icc (-1 : ℝ) 1,
            |z - wz1Lemma23SnappedBaseHeight delta heightIndex| ≤
                delta / (2 * Real.sqrt 3) →
              |source.globalGrains.slope z - trapezoid.affine z| ≤ delta := by
      intro heightIndex hheightIndex z hz hclose
      rw [rich.heightIndices_eq] at hheightIndex
      rcases Finset.mem_image.mp hheightIndex with
        ⟨richPoint, hrichPoint, hheightEq⟩
      let center := (wz1Lemma23CellCenter delta
        (rich.pathFor richPoint).2.1) 2
      let centered := center - baseHeight
      have hcenterEq :
          center = wz1Lemma23SnappedBaseHeight delta heightIndex := by
        simp [center, wz1Lemma23SnappedBaseHeight,
          wz1Lemma23CellCenter, point3, ← hheightEq,
          rich.heightIndex_eq richPoint hrichPoint]
      have hcloseCenter : |z - center| ≤
          delta / (2 * Real.sqrt 3) := by rwa [hcenterEq]
      have hstrip := rich.centered_strip richPoint hrichPoint
      have hcenterApprox :
          |wz1Lemma23CenteredSlope baseHeight
              prep.windowed.global.extendedSlope centered -
            slope * centered| ≤
              5 * delta / (13 * Real.sqrt 3) := by
        apply pureWZ2_terminal_strip_affine_sharp rich.direction delta hdelta
          (wz1Lemma23CenteredSlope baseHeight
            prep.windowed.global.extendedSlope) centered hnonvertical
        simpa [baseHeight, center, centered, slope,
          wz1Lemma23SnappedPoint, wz1Lemma23CellCenter] using hstrip
      have hextendedClose :
          |prep.windowed.global.extendedSlope z -
            prep.windowed.global.extendedSlope center| ≤
              delta / (2 * Real.sqrt 3) :=
        (hextendedLip z center).trans hcloseCenter
      have hslopeClose : |slope * (z - center)| ≤
          (5 / 3) * (delta / (2 * Real.sqrt 3)) := by
        rw [abs_mul]
        exact mul_le_mul hslope hcloseCenter (abs_nonneg _) (by norm_num)
      have hsourceAt : prep.windowed.global.extendedSlope z =
          source.globalGrains.slope z := by
        rw [prep.windowed.global.extendedSlope_eq z hz, prep.sourceSlope_eq]
      rw [← hsourceAt]
      change |prep.windowed.global.extendedSlope z -
        (slope * z + intercept)| ≤ delta
      dsimp only [intercept]
      have htriangle :
          |prep.windowed.global.extendedSlope z -
              (slope * z +
                (prep.windowed.global.extendedSlope baseHeight -
                  slope * baseHeight))| ≤
            |prep.windowed.global.extendedSlope z -
              prep.windowed.global.extendedSlope center| +
            |wz1Lemma23CenteredSlope baseHeight
                prep.windowed.global.extendedSlope centered -
              slope * centered| +
            |slope * (z - center)| := by
        dsimp only [wz1Lemma23CenteredSlope, centered]
        rw [show center - baseHeight + baseHeight = center by ring]
        calc
          _ = |(prep.windowed.global.extendedSlope z -
                  prep.windowed.global.extendedSlope center) +
                (prep.windowed.global.extendedSlope center -
                  prep.windowed.global.extendedSlope baseHeight -
                  slope * (center - baseHeight)) +
                (-(slope * (z - center)))| := by ring_nf
          _ ≤ |(prep.windowed.global.extendedSlope z -
                  prep.windowed.global.extendedSlope center) +
                (prep.windowed.global.extendedSlope center -
                  prep.windowed.global.extendedSlope baseHeight -
                  slope * (center - baseHeight))| +
                |-(slope * (z - center))| := abs_add_le _ _
          _ ≤ (|prep.windowed.global.extendedSlope z -
                  prep.windowed.global.extendedSlope center| +
                |prep.windowed.global.extendedSlope center -
                  prep.windowed.global.extendedSlope baseHeight -
                  slope * (center - baseHeight)|) +
                |slope * (z - center)| := by
            rw [abs_neg]
            gcongr
            exact abs_add_le _ _
          _ = _ := by ring
      calc
        _ ≤ |prep.windowed.global.extendedSlope z -
                prep.windowed.global.extendedSlope center| +
              |wz1Lemma23CenteredSlope baseHeight
                  prep.windowed.global.extendedSlope centered -
                slope * centered| +
              |slope * (z - center)| := htriangle
        _ ≤ delta / (2 * Real.sqrt 3) +
              5 * delta / (13 * Real.sqrt 3) +
              (5 / 3) * (delta / (2 * Real.sqrt 3)) := by gcongr
        _ ≤ delta := by
          have hsqrtPos : 0 < Real.sqrt (3 : ℝ) := by positivity
          have hconstant :
              (1 / 2 + 5 / 13 + (5 / 3) * (1 / 2 : ℝ)) /
                  Real.sqrt 3 < 1 := by
            rw [div_lt_one hsqrtPos]
            norm_num
            exact pureWZ2_sqrt_three_gt_sixty_seven_over_thirty_nine
          have heq :
              delta / (2 * Real.sqrt 3) +
                  5 * delta / (13 * Real.sqrt 3) +
                  (5 / 3) * (delta / (2 * Real.sqrt 3)) =
                delta * ((1 / 2 + 5 / 13 + (5 / 3) * (1 / 2 : ℝ)) /
                  Real.sqrt 3) := by ring
          rw [heq]
          exact (mul_lt_of_lt_one_right hdelta hconstant).le
    have happrox : ∀ z ∈ trapezoid.core,
        horizontalSlice heightLift.shading.union z ≠ ∅ →
          |source.globalGrains.slope z - trapezoid.affine z| ≤ delta := by
      intro z _hz hslice
      rcases hrichCenterFor z hslice with
        ⟨richPoint, hrichPoint, hclose⟩
      exact hrichHeightApprox (rich.heightIndex richPoint) (by
        rw [rich.heightIndices_eq]
        exact Finset.mem_image.mpr ⟨richPoint, hrichPoint, rfl⟩) z
        (hheightDomain z hslice) (by
            simpa [wz1Lemma23SnappedBaseHeight, wz1Lemma23CellCenter, point3,
              rich.heightIndex_eq richPoint hrichPoint] using hclose)
    exact ⟨{
      trapezoid := trapezoid
      height_eq := rfl
      core_eq := rfl
      slope_bound := hslope.trans (by norm_num)
      length_bounds := by
        dsimp only [trapezoid, WZ1VerticalTrapezoid.length]
        rw [hlength]
        exact ⟨hlengthLower, le_rfl⟩
      active_height_coverage := by
        intro z hslice
        simpa [trapezoid, WZ1VerticalTrapezoid.core] using
          hcoreCoverage z hslice
      slope_approximation := happrox
      rich_height_approximation := hrichHeightApprox }⟩
  · have hvertical :
        |rich.direction 1| < pureWZ2TerminalDirectionCutoff :=
      lt_of_not_ge hnonvertical
    let basePoint := Classical.choose rich.richF_nonempty
    have hbasePoint : basePoint ∈ rich.richF :=
      Classical.choose_spec rich.richF_nonempty
    let baseCenter := (wz1Lemma23CellCenter delta
      (rich.pathFor basePoint).2.1) 2
    let intercept := prep.windowed.global.extendedSlope baseCenter
    let trapezoid : WZ1VerticalTrapezoid :=
      { left := left
        right := right
        left_lt_right := by dsimp only [left, right]; linarith
        slope := 0
        intercept := intercept
        height := delta
        height_pos := hdelta }
    have hcenterApprox : ∀ point ∈ rich.richF,
        let center := (wz1Lemma23CellCenter delta
          (rich.pathFor point).2.1) 2
        |prep.windowed.global.extendedSlope center -
          prep.windowed.global.extendedSlope baseCenter| ≤
            6 * delta / (5 * Real.sqrt 3) := by
      intro point hpoint
      let center := (wz1Lemma23CellCenter delta
        (rich.pathFor point).2.1) 2
      let centered := center - baseHeight
      let baseCentered := baseCenter - baseHeight
      have hstrip := rich.centered_strip point hpoint
      have hbaseStrip := rich.centered_strip basePoint hbasePoint
      have hgap : (1 / 3 : ℝ) ≤
          |rich.direction 0| - |rich.direction 1| :=
        pureWZ2_terminal_near_vertical_gap rich.direction
          rich.direction_unit hvertical
      have hheight := height_range_bound_of_strip rich.direction delta
        (1 / (5 * Real.sqrt 3)) (1 / 3) hdelta (by norm_num)
        (wz1Lemma23CenteredSlope baseHeight
          prep.windowed.global.extendedSlope)
        (fun firstHeight secondHeight => by
          dsimp only [wz1Lemma23CenteredSlope]
          have h := hextendedLip
            (firstHeight + baseHeight) (secondHeight + baseHeight)
          convert h using 1 <;> ring)
        hgap centered baseCentered (by
          simpa [baseHeight, center, centered, mul_comm, div_eq_mul_inv]
            using hstrip) (by
          simpa [baseHeight, baseCenter, baseCentered, mul_comm,
            div_eq_mul_inv] using hbaseStrip)
      have hcenterDistance :
          |center - baseCenter| ≤ 6 * delta / (5 * Real.sqrt 3) := by
        convert hheight using 1 <;>
          dsimp only [centered, baseCentered] <;> ring
      exact (hextendedLip center baseCenter).trans hcenterDistance
    have hrichHeightApprox :
        ∀ heightIndex ∈ rich.heightIndices,
          ∀ z ∈ Set.Icc (-1 : ℝ) 1,
            |z - wz1Lemma23SnappedBaseHeight delta heightIndex| ≤
                delta / (2 * Real.sqrt 3) →
              |source.globalGrains.slope z - trapezoid.affine z| ≤ delta := by
      intro heightIndex hheightIndex z hz hclose
      rw [rich.heightIndices_eq] at hheightIndex
      rcases Finset.mem_image.mp hheightIndex with
        ⟨richPoint, hrichPoint, hheightEq⟩
      let center := (wz1Lemma23CellCenter delta
        (rich.pathFor richPoint).2.1) 2
      have hcenterEq :
          center = wz1Lemma23SnappedBaseHeight delta heightIndex := by
        simp [center, wz1Lemma23SnappedBaseHeight,
          wz1Lemma23CellCenter, point3, ← hheightEq,
          rich.heightIndex_eq richPoint hrichPoint]
      have hcloseCenter : |z - center| ≤
          delta / (2 * Real.sqrt 3) := by rwa [hcenterEq]
      have hcenter := hcenterApprox richPoint hrichPoint
      have hextendedClose :
          |prep.windowed.global.extendedSlope z -
            prep.windowed.global.extendedSlope center| ≤
              delta / (2 * Real.sqrt 3) :=
        (hextendedLip z center).trans hcloseCenter
      have hsourceAt : prep.windowed.global.extendedSlope z =
          source.globalGrains.slope z := by
        rw [prep.windowed.global.extendedSlope_eq z hz, prep.sourceSlope_eq]
      rw [← hsourceAt]
      change |prep.windowed.global.extendedSlope z -
        (0 * z + intercept)| ≤ delta
      simp only [zero_mul, zero_add]
      dsimp only [intercept]
      calc
        |prep.windowed.global.extendedSlope z -
            prep.windowed.global.extendedSlope baseCenter| ≤
          |prep.windowed.global.extendedSlope z -
              prep.windowed.global.extendedSlope center| +
            |prep.windowed.global.extendedSlope center -
              prep.windowed.global.extendedSlope baseCenter| :=
          abs_sub_le _ _ _
        _ ≤ delta / (2 * Real.sqrt 3) +
              6 * delta / (5 * Real.sqrt 3) := by gcongr
        _ ≤ delta := by
          have hsqrtPos : 0 < Real.sqrt (3 : ℝ) := by positivity
          have hconstant : (17 / 10 : ℝ) / Real.sqrt 3 < 1 := by
            rw [div_lt_one hsqrtPos]
            exact pureWZ2_sqrt_three_gt_seventeen_over_ten
          have heq : delta / (2 * Real.sqrt 3) +
                6 * delta / (5 * Real.sqrt 3) =
              delta * ((17 / 10 : ℝ) / Real.sqrt 3) := by ring
          rw [heq]
          exact (mul_lt_of_lt_one_right hdelta hconstant).le
    have happrox : ∀ z ∈ trapezoid.core,
        horizontalSlice heightLift.shading.union z ≠ ∅ →
          |source.globalGrains.slope z - trapezoid.affine z| ≤ delta := by
      intro z _hz hslice
      rcases hrichCenterFor z hslice with
        ⟨richPoint, hrichPoint, hclose⟩
      exact hrichHeightApprox (rich.heightIndex richPoint) (by
        rw [rich.heightIndices_eq]
        exact Finset.mem_image.mpr ⟨richPoint, hrichPoint, rfl⟩) z
        (hheightDomain z hslice) (by
            simpa [wz1Lemma23SnappedBaseHeight, wz1Lemma23CellCenter, point3,
              rich.heightIndex_eq richPoint hrichPoint] using hclose)
    exact ⟨{
      trapezoid := trapezoid
      height_eq := rfl
      core_eq := rfl
      slope_bound := by simp [trapezoid]
      length_bounds := by
        dsimp only [trapezoid, WZ1VerticalTrapezoid.length]
        rw [hlength]
        exact ⟨hlengthLower, le_rfl⟩
      active_height_coverage := by
        intro z hslice
        simpa [trapezoid, WZ1VerticalTrapezoid.core] using
          hcoreCoverage z hslice
      slope_approximation := happrox
      rich_height_approximation := hrichHeightApprox }⟩

/-- The exact core remains in the block window that selected its parents. -/
theorem PureWZ2TerminalPopularExactTrapezoid.core_height_window
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
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
    {rich : PureWZ2TerminalPopularAlternativeAHeightData ready outputLoss}
    {heightLift : PureWZ2TerminalPopularOuterHeightLift rich}
    (data : PureWZ2TerminalPopularExactTrapezoid heightLift)
    {z : ℝ} (hz : z ∈ data.trapezoid.core) :
    z ∈ Set.Icc (window.left - 2 * Real.sqrt delta)
      (window.left + 3 * Real.sqrt delta) := by
  let root := terminal.sqrtRequested.1
  have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
  have hrootEq : root = Real.sqrt delta := terminal.sqrtRequested_eq
  rcases selection.selected_nonempty with ⟨parent, hparent⟩
  have hparentInParents : parent ∈ parents.parents :=
    selection.onePerY_subset (selection.selected_subset hparent)
  rcases parents.parent_hit parent hparentInParents with
    ⟨cell, hcell, hcellParent⟩
  have hrepresentativeParent := parents.representative_mem_parent cell hcell
  rw [hcellParent, wz1PaperGridCube_eq_Ico hroot parent]
    at hrepresentativeParent
  have hparentHeight := selection.parent_height_eq parent hparent
  rw [hparentHeight] at hrepresentativeParent
  have hlineHeight := line.representative_height cell hcell
  have hlineWindow := restrictedPrepared.union_height_window
    (line.representative cell) (line.representative_mem cell hcell)
  rw [hlineHeight, heightData.graphWindow_left] at hlineWindow
  rw [data.core_eq] at hz
  have hdeltaRoot : delta ≤ root := by
    rw [hrootEq]
    nlinarith [Real.sqrt_nonneg delta,
      Real.sq_sqrt source.extremal.delta_pos.le,
      source.extremal.delta_le_one]
  constructor
  · rw [← hrootEq]
    nlinarith [hz.1, hrepresentativeParent.2.2.2.2.2, hlineWindow.1]
  · rw [← hrootEq]
    nlinarith [hz.2, hrepresentativeParent.2.2.2.2.1, hlineWindow.2]

structure PureWZ2TerminalPopularExactWindowOutput
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (window : PureWZ2TerminalWindow prepared) where
  chain : PureWZ2TerminalPopularPaperOrderChain
    (eta := eta) (theoremEta := theoremEta)
    (outputLoss := outputLoss) window
  exactTrapezoid :
    PureWZ2TerminalPopularExactTrapezoid chain.outerHeightLift

/-- Run the heterogeneous paper-order chain from a prescribed pre-line
height/carrier/parent-class prefix. -/
theorem pureWZ2_terminalPopular_exactWindow_of_prefix_and_certificates
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss
      volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (window : PureWZ2TerminalWindow prepared)
    (preline : PureWZ2TerminalPopularPrefixData window)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (houtputLoss : 0 < outputLoss)
    (houtputTheorem : outputLoss + theoremEta ≤ 1)
    (hCpower : 10 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-eta))
    (hPlanarSmall : 32 * Real.rpow delta eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt delta ≤ 1)
    (hlocalization : Real.rpow delta (1 - 4 * eta / sigma) ≤
      Real.sqrt delta / 14)
    (htransferSmall : 1000 * Real.sqrt delta ≤ 1)
    (hsourceVolume :
      (512 : ENNReal) * Kakeya.realRpowENN delta
          (3 / 2 + sigma / 2 + eta) ≤
        terminal.sticky.balanced.cellMass)
    (hGraphCOne : (1 : ENNReal) ≤
      pureWZ2TerminalPopularGraphConstant delta inputLoss)
    (hGraphCpower :
      (pureWZ2TerminalPopularGraphConstant delta inputLoss).toReal ≤
        Real.rpow delta (-constantLoss))
    (hvolume : ∀
      {restricted : PureWZ2TerminalPopularParentRestrictionData
        preline.weightClass}
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
      (_prep : PureWZ2TerminalPopularGraphPreparation localized),
        pureWZ2TerminalPopularLocalizedPieceCost *
            Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) ≤
          (localized.selectedParents.card : ENNReal) *
            preline.weightClass.weightFloor)
    (hextra : ∀
      {restricted : PureWZ2TerminalPopularParentRestrictionData
        preline.weightClass}
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
      (preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells),
        (preparedGraph.graph.residue.extraCost : ℝ) ≤
          Real.rpow delta (-extraLoss))
    (hedge :
      Real.rpow (wz1Lemma23Theorem22Scale delta) (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow delta
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hrefinedEdge :
      Real.rpow (wz1Lemma23Theorem22Scale (delta / 625))
          (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow delta
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hkatz : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale delta) (-theoremEta))
    (hrefinedKatz : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale (delta / 625)) (-theoremEta))
    (alternativeA : ∀
      {restricted : PureWZ2TerminalPopularParentRestrictionData
        preline.weightClass}
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
      (ready : PureWZ2CommonRefinedReadyGraph
        delta theoremEta first.common first.ready),
        WZ1Proposition8_9AlternativeAUnion
          ready.ready.deltaGraph outputLoss
          ready.common.F ready.common.G₁ ready.common.G₁) :
    Nonempty (PureWZ2TerminalPopularExactWindowOutput
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) window) := by
  rcases pureWZ2_terminalPopular_paperOrderChain_of_certificates
      (volumeLoss := volumeLoss) (constantLoss := constantLoss)
      (extraLoss := extraLoss) window preline
      hbridge hsigma hsigmaOne heta hetaSigma houtputTheorem hCpower hPlanarSmall
      hrootSmall20 hlocalization htransferSmall hsourceVolume hGraphCOne
      hGraphCpower
      (by
        intro restricted restrictedPrepared line parents selection
          selectedCarrier sources localized prep
        exact hvolume prep)
      (by
        intro restricted restrictedPrepared line parents selection
          selectedCarrier sources localized prep graphParents localCells
          preparedGraph
        exact hextra preparedGraph)
      hedge hrefinedEdge hkatz hrefinedKatz
      (by
        intro restricted restrictedPrepared line parents selection
          selectedCarrier sources localized prep graphParents localCells
          preparedGraph sharp first ready
        exact alternativeA ready) with ⟨chain⟩
  rcases chain.outerHeightLift.toExactTrapezoid houtputLoss with
    ⟨exactTrapezoid⟩
  exact ⟨{ chain := chain, exactTrapezoid := exactTrapezoid }⟩

/-- Run the heterogeneous paper-order chain and attach its exact terminal
trapezoid without changing any of the dependent witnesses. -/
theorem pureWZ2_terminalPopular_exactWindow_of_certificates
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss
      volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (window : PureWZ2TerminalWindow prepared)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (houtputLoss : 0 < outputLoss)
    (houtputTheorem : outputLoss + theoremEta ≤ 1)
    (hCpower : 10 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-eta))
    (hPlanarSmall : 32 * Real.rpow delta eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt delta ≤ 1)
    (hlocalization : Real.rpow delta (1 - 4 * eta / sigma) ≤
      Real.sqrt delta / 14)
    (htransferSmall : 1000 * Real.sqrt delta ≤ 1)
    (hsourceVolume :
      (512 : ENNReal) * Kakeya.realRpowENN delta
          (3 / 2 + sigma / 2 + eta) ≤
        terminal.sticky.balanced.cellMass)
    (hGraphCOne : (1 : ENNReal) ≤
      pureWZ2TerminalPopularGraphConstant delta inputLoss)
    (hGraphCpower :
      (pureWZ2TerminalPopularGraphConstant delta inputLoss).toReal ≤
        Real.rpow delta (-constantLoss))
    (hvolume : ∀
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
      (_prep : PureWZ2TerminalPopularGraphPreparation localized),
        pureWZ2TerminalPopularLocalizedPieceCost *
            Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) ≤
          (localized.selectedParents.card : ENNReal) *
            weightClass.weightFloor)
    (hextra : ∀
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
      (preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells),
        (preparedGraph.graph.residue.extraCost : ℝ) ≤
          Real.rpow delta (-extraLoss))
    (hedge :
      Real.rpow (wz1Lemma23Theorem22Scale delta) (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow delta
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hrefinedEdge :
      Real.rpow (wz1Lemma23Theorem22Scale (delta / 625))
          (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow delta
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hkatz : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale delta) (-theoremEta))
    (hrefinedKatz : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale (delta / 625)) (-theoremEta))
    (alternativeA : ∀
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
      (ready : PureWZ2CommonRefinedReadyGraph
        delta theoremEta first.common first.ready),
        WZ1Proposition8_9AlternativeAUnion
          ready.ready.deltaGraph outputLoss
          ready.common.F ready.common.G₁ ready.common.G₁) :
    Nonempty (PureWZ2TerminalPopularExactWindowOutput
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) window) := by
  rcases window.popularPrefix with ⟨preline⟩
  exact pureWZ2_terminalPopular_exactWindow_of_prefix_and_certificates
      window preline
      hbridge hsigma hsigmaOne heta hetaSigma houtputLoss houtputTheorem
      hCpower hPlanarSmall
      hrootSmall20 hlocalization htransferSmall hsourceVolume hGraphCOne
      hGraphCpower hvolume hextra hedge hrefinedEdge hkatz hrefinedKatz alternativeA

end Kakeya.Assouad

end
