import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineRichShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalTrapezoidGeometry

/-!
# One faithful trapezoid on the rich whole-cell coarse shading
-/

noncomputable section

namespace Kakeya.Assouad

open Set

attribute [local instance] Classical.propDecidable

structure PureWZ2HorizontalAlternativeARichTrapezoid
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading : PureWZ2HorizontalFixedLineResidueShadingData residue}
    {prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading}
    {graphParents : PureWZ2HorizontalFixedLineGraphParentData prep}
    {sources : PureWZ2HorizontalFixedLineResidueSourceFamily residueShading}
    {fullGrains : PureWZ2HorizontalFixedLineResidueFullGrainFamily
      (eta := eta) sources prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2HorizontalFixedLineSharpGeometry graph}
    {ready : PureWZ2HorizontalFixedLineReadyGraph
      (eta := eta) (theoremEta := theoremEta)
      (graphParents := graphParents) (sources := sources)
      (fullGrains := fullGrains) sharp}
    {rich : PureWZ2HorizontalAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2HorizontalAlternativeARichCells
      (graphParents := graphParents) rich}
    (richShading : PureWZ2HorizontalAlternativeARichShading richCells) where
  scale : ℝ := 5 * prep.graphScale
  scale_eq : scale = 5 * prep.graphScale
  scale_pos : 0 < scale
  scale_le_one : scale ≤ 1
  trapezoid : WZ1VerticalTrapezoid
  height_eq : trapezoid.height = scale
  slope_bound : |trapezoid.slope| ≤ 2
  length_bounds :
    Real.rpow scale (1 / 2 + finalLoss) ≤ trapezoid.length ∧
      trapezoid.length ≤ Real.sqrt scale
  core_height_window :
    ∀ z ∈ trapezoid.core,
      z ∈ Set.Icc
        (windowed.left - 2 * Real.sqrt rho)
        (windowed.left + 3 * Real.sqrt rho)
  active_height_coverage :
    ∀ z, horizontalSlice richShading.shading.union z ≠ ∅ →
      z ∈ trapezoid.core
  slope_approximation :
    ∀ z ∈ trapezoid.core,
      horizontalSlice richShading.shading.union z ≠ ∅ →
        |twoScale.coarseGrains.globalGrains.slope z -
          trapezoid.affine z| ≤ scale

theorem PureWZ2HorizontalAlternativeARichShading.toRichTrapezoid
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading : PureWZ2HorizontalFixedLineResidueShadingData residue}
    {prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading}
    {graphParents : PureWZ2HorizontalFixedLineGraphParentData prep}
    {sources : PureWZ2HorizontalFixedLineResidueSourceFamily residueShading}
    {fullGrains : PureWZ2HorizontalFixedLineResidueFullGrainFamily
      (eta := eta) sources prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2HorizontalFixedLineSharpGeometry graph}
    {ready : PureWZ2HorizontalFixedLineReadyGraph
      (eta := eta) (theoremEta := theoremEta)
      (graphParents := graphParents) (sources := sources)
      (fullGrains := fullGrains) sharp}
    {rich : PureWZ2HorizontalAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2HorizontalAlternativeARichCells
      (graphParents := graphParents) rich}
    (richShading : PureWZ2HorizontalAlternativeARichShading richCells)
    (hscaleOne : 5 * prep.graphScale ≤ 1)
    (hlengthLower :
      Real.rpow (5 * prep.graphScale) (1 / 2 + finalLoss) ≤
        twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2HorizontalAlternativeARichTrapezoid richShading) := by
  let scale := 5 * prep.graphScale
  let baseHeight := wz1Lemma23SnappedBaseHeight prep.graphScale
    sharp.sharp.baseHeightIndex
  let left := (residueShading.commonParentHeight : ℝ) *
    twoScale.sqrtRequested.1
  let right := ((residueShading.commonParentHeight : ℝ) + 1) *
    twoScale.sqrtRequested.1
  have hroot : 0 < twoScale.sqrtRequested.1 :=
    twoScale.fine.coarse_extremal.delta_pos
  have hscale : 0 < scale := by
    dsimp only [scale]
    exact mul_pos (by norm_num) prep.graphScale_pos
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hcore : ∀ z, horizontalSlice richShading.shading.union z ≠ ∅ →
      z ∈ Set.Icc left right := by
    intro z hslice
    rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint, hheight⟩
    have hretained : point ∈ residueShading.shading.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, (richShading.carrier_eq index ▸ hindex).1⟩
    have hz := residueShading.union_height point hretained
    rw [hheight] at hz
    exact ⟨hz.1, hz.2.le⟩
  have hlength : right - left = twoScale.sqrtRequested.1 := by
    dsimp only [left, right]
    ring
  have hlengthUpper : twoScale.sqrtRequested.1 ≤ Real.sqrt scale := by
    have hrhoScale : rho ≤ scale := by
      dsimp only [scale]
      rw [prep.graphScale_eq, twoScale.rhoRequested_eq]
      nlinarith [hrho]
    have hrootEq : twoScale.sqrtRequested.1 = Real.sqrt rho :=
      twoScale.sqrtRequested_eq
    rw [hrootEq]
    exact Real.sqrt_le_sqrt hrhoScale
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hlineWindow : line.lineHeight ∈ Set.Ico
      (windowed.left - rho) (windowed.left + Real.sqrt rho + rho) := by
    have hraw :=
      windowed.union_height_window line.lineAnchor line.lineAnchor_mem
    rw [line.lineAnchor_height] at hraw
    simpa only [twoScale.rhoRequested_eq] using hraw
  have hlineParent : line.lineHeight ∈ Set.Ico left right := by
    rcases residue.selected_nonempty with ⟨parent, hparent⟩
    rcases selection.selected_hit parent (residue.selected_subset hparent) with
      ⟨cell, hcell, hcellParent⟩
    have hpointParent := parents.representative_mem_parent cell hcell
    rw [hcellParent, wz1PaperGridCube_eq_Ico hroot parent] at hpointParent
    have hheight := line.representative_height cell hcell
    have hparentHeight := residueShading.parent_height_eq parent hparent
    dsimp only [left, right]
    rw [hparentHeight] at hpointParent
    have hzParent : (line.representative cell) (2 : Fin 3) ∈ Set.Ico
        ((residueShading.commonParentHeight : ℝ) * twoScale.sqrtRequested.1)
        (((residueShading.commonParentHeight : ℝ) + 1) *
          twoScale.sqrtRequested.1) :=
      ⟨hpointParent.2.2.2.2.1, hpointParent.2.2.2.2.2⟩
    rwa [hheight] at hzParent
  have hsqrtRho : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have hrhoRoot : rho ≤ Real.sqrt rho := by
    nlinarith [Real.sq_sqrt hrho.le]
  have hcoreWindow : ∀ z ∈ Set.Icc left right,
      z ∈ Set.Icc
        (windowed.left - 2 * Real.sqrt rho)
        (windowed.left + 3 * Real.sqrt rho) := by
    intro z hz
    have hrootEq : twoScale.sqrtRequested.1 = Real.sqrt rho :=
      twoScale.sqrtRequested_eq
    have hleftGap : line.lineHeight - Real.sqrt rho ≤ z := by
      rw [← hrootEq]
      dsimp only [left, right] at hlineParent hz
      nlinarith [hlineParent.2, hz.1]
    have hrightGap : z ≤ line.lineHeight + Real.sqrt rho := by
      rw [← hrootEq]
      dsimp only [left, right] at hlineParent hz
      nlinarith [hlineParent.1, hz.2]
    constructor <;> nlinarith [hlineWindow.1, hlineWindow.2]
  have hsourceEq : ∀ z, horizontalSlice richShading.shading.union z ≠ ∅ →
      prep.windowed.global.extendedSlope z = twoScale.coarseGrains.globalGrains.slope z := by
    intro z hslice
    rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint, hheight⟩
    have hsourcePoint : point ∈ twoScale.coarseGrains.shading.union :=
      richShading.subshading.union_subset hpoint
    have hbox := shading_union_subset_axisBox hsourcePoint
    have hz : z ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [← hheight]
      have habs : |point 2| ≤ 1 := by
        convert hbox.2.2 using 1 <;> norm_num
      exact abs_le.mp habs
    rw [prep.windowed.global.extendedSlope_eq z hz, prep.sourceSlope_eq]
  have hcenterFor : ∀ z, horizontalSlice richShading.shading.union z ≠ ∅ →
      ∃ richPoint ∈ rich.richF,
        let cell := (rich.pathFor richPoint).2.1
        |z - (wz1Lemma23CellCenter prep.graphScale cell) 2| ≤
          prep.graphScale := by
    intro z hslice
    rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint, hheight⟩
    have hregion : point ∈ richShading.region := by
      rw [richShading.union_eq] at hpoint
      exact hpoint
    rw [richShading.region_eq] at hregion
    rcases Set.mem_iUnion₂.mp hregion with ⟨rhoCell, hrhoCell, hpointRho⟩
    rw [richCells.cells_eq] at hrhoCell
    rcases Finset.mem_image.mp hrhoCell with
      ⟨graphCell, hgraphCell, hcellEq⟩
    have hrichHeight := richCells.graphCells_height graphCell hgraphCell
    rw [rich.heightIndices_eq] at hrichHeight
    rcases Finset.mem_image.mp hrichHeight with
      ⟨richPoint, hrichPoint, hheightIndex⟩
    refine ⟨richPoint, hrichPoint, ?_⟩
    have hrepRho := graphParents.representative_mem_rhoCell graphCell
      (graph.residue.cells_subset (richCells.graphCells_subset hgraphCell))
    rw [hcellEq] at hrepRho
    have hzClose :
        |point 2 - graphParents.representative graphCell 2| < rho := by
      rw [wz1PaperGridCube_eq_Ico hrho rhoCell] at hpointRho
      rw [wz1PaperGridCube_eq_Ico hrho rhoCell] at hrepRho
      rw [abs_lt]
      constructor <;>
        linarith [hpointRho.2.2.2.2.1, hpointRho.2.2.2.2.2,
          hrepRho.2.2.2.2.1, hrepRho.2.2.2.2.2]
    have hgraphMem : graphCell ∈ prep.windowed.global.cells :=
      graph.residue.cells_subset (richCells.graphCells_subset hgraphCell)
    have hrepIndex := graphParents.representative_index graphCell hgraphMem
    have hrepCenter :=
      ((wz1_lemma23_snapped_cell_geometry prep.graphScale
        prep.graphScale_pos prep.graphScale_one).2.1
        graphCell (graphParents.representative graphCell) hrepIndex).1 (2 : Fin 3)
    have htriangle :
        |point 2 - (wz1Lemma23CellCenter prep.graphScale graphCell) 2| ≤
          |point 2 - graphParents.representative graphCell 2| +
            |graphParents.representative graphCell 2 -
              (wz1Lemma23CellCenter prep.graphScale graphCell) 2| := by
      simpa using abs_sub_le (point 2)
        (graphParents.representative graphCell 2)
        ((wz1Lemma23CellCenter prep.graphScale graphCell) 2)
    rw [hheight] at htriangle
    have hrhoGraph : rho ≤ prep.graphScale / 2 := by
      rw [prep.graphScale_eq, twoScale.rhoRequested_eq]
      nlinarith [hrho]
    rw [hheight] at hzClose
    have hsumBound :
        |z - graphParents.representative graphCell 2| +
            |graphParents.representative graphCell 2 -
              (wz1Lemma23CellCenter prep.graphScale graphCell) 2| ≤
          prep.graphScale := by
      have hzLe : |z - graphParents.representative graphCell 2| ≤ rho :=
        hzClose.le
      linarith
    have hcloseGraph := htriangle.trans hsumBound
    have hcenterEq :
        (wz1Lemma23CellCenter prep.graphScale graphCell) 2 =
          (wz1Lemma23CellCenter prep.graphScale
            (rich.pathFor richPoint).2.1) 2 := by
      have hindexEq : graphCell.2.2 = (rich.pathFor richPoint).2.1.2.2 := by
        rw [← rich.heightIndex_eq richPoint hrichPoint]
        exact hheightIndex.symm
      simp [wz1Lemma23CellCenter, point3, hindexEq]
    dsimp only
    rw [← hcenterEq]
    exact hcloseGraph
  have hextendedLip : ∀ first second,
      |prep.windowed.global.extendedSlope first -
          prep.windowed.global.extendedSlope second| ≤ |first - second| := by
    intro first second
    simpa [Real.dist_eq] using
      prep.windowed.global.extendedSlope_lipschitz.dist_le_mul
        first (by simp) second (by simp)
  by_cases hnonvertical : 1 / Real.sqrt 5 ≤ |rich.direction 1|
  · let slope := -(rich.direction 0 / rich.direction 1)
    let intercept :=
      prep.windowed.global.extendedSlope baseHeight - slope * baseHeight
    let trapezoid : WZ1VerticalTrapezoid :=
      { left := left
        right := right
        left_lt_right := by dsimp only [left, right]; nlinarith
        slope := slope
        intercept := intercept
        height := scale
        height_pos := hscale }
    have hslope : |slope| ≤ 2 := by
      dsimp only [slope]
      have h :=
        slope_bound_from_direction rich.direction rich.direction_unit hnonvertical
      convert h using 1 <;> ring
    have hslopeApprox : ∀ z ∈ trapezoid.core,
        horizontalSlice richShading.shading.union z ≠ ∅ →
          |twoScale.coarseGrains.globalGrains.slope z - trapezoid.affine z| ≤ scale := by
      intro z _hz hslice
      rcases hcenterFor z hslice with ⟨richPoint, hrichPoint, hclose⟩
      let graphCell := (rich.pathFor richPoint).2.1
      let center := (wz1Lemma23CellCenter prep.graphScale graphCell) 2
      let centered := center - baseHeight
      have hstrip := rich.centered_strip richPoint hrichPoint
      have hcenterApprox :
          |wz1Lemma23CenteredSlope baseHeight
              prep.windowed.global.extendedSlope centered -
            slope * centered| ≤ 2 * prep.graphScale := by
        apply pureWZ2_nonvertical_centered_approximation
          rich.direction prep.graphScale prep.graphScale_pos
          (wz1Lemma23CenteredSlope baseHeight
            prep.windowed.global.extendedSlope) centered hnonvertical
        simpa [baseHeight, graphCell, center, centered, slope] using hstrip
      have hextendedClose :
          |prep.windowed.global.extendedSlope z -
            prep.windowed.global.extendedSlope center| ≤ prep.graphScale :=
        (hextendedLip z center).trans hclose
      have hslopeClose : |slope * (z - center)| ≤ 2 * prep.graphScale := by
        rw [abs_mul]
        exact mul_le_mul hslope hclose (abs_nonneg _) (by norm_num)
      have hsource := hsourceEq z hslice
      rw [← hsource]
      change |prep.windowed.global.extendedSlope z -
        (slope * z + intercept)| ≤ scale
      dsimp only [intercept]
      have htriangle :
          |prep.windowed.global.extendedSlope z - (slope * z +
              (prep.windowed.global.extendedSlope baseHeight - slope * baseHeight))| ≤
            |prep.windowed.global.extendedSlope z -
              prep.windowed.global.extendedSlope center| +
            |wz1Lemma23CenteredSlope baseHeight
                prep.windowed.global.extendedSlope centered - slope * centered| +
            |slope * (z - center)| := by
        dsimp only [wz1Lemma23CenteredSlope, centered]
        have heq : center - baseHeight + baseHeight = center := by ring
        rw [heq]
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
          _ = |prep.windowed.global.extendedSlope z -
                  prep.windowed.global.extendedSlope center| +
                |prep.windowed.global.extendedSlope center -
                  prep.windowed.global.extendedSlope baseHeight -
                  slope * (center - baseHeight)| +
                |slope * (z - center)| := by ring
      dsimp only [scale]
      linarith
    exact ⟨{
      scale := scale
      scale_eq := rfl
      scale_pos := hscale
      scale_le_one := hscaleOne
      trapezoid := trapezoid
      height_eq := rfl
      slope_bound := hslope
      length_bounds := by
        dsimp only [trapezoid, WZ1VerticalTrapezoid.length]
        rw [hlength]
        exact ⟨hlengthLower, hlengthUpper⟩
      core_height_window := by
        intro z hz
        exact hcoreWindow z (by
          simpa [trapezoid, WZ1VerticalTrapezoid.core] using hz)
      active_height_coverage := by
        intro z hslice
        simpa [trapezoid, WZ1VerticalTrapezoid.core] using hcore z hslice
      slope_approximation := hslopeApprox
    }⟩
  · have hvertical : |rich.direction 1| < 1 / Real.sqrt 5 :=
      lt_of_not_ge hnonvertical
    let basePoint := Classical.choose rich.richF_nonempty
    have hbasePoint : basePoint ∈ rich.richF :=
      Classical.choose_spec rich.richF_nonempty
    let baseCell := (rich.pathFor basePoint).2.1
    let baseCenter := (wz1Lemma23CellCenter prep.graphScale baseCell) 2
    let intercept := prep.windowed.global.extendedSlope baseCenter
    let trapezoid : WZ1VerticalTrapezoid :=
      { left := left
        right := right
        left_lt_right := by dsimp only [left, right]; nlinarith
        slope := 0
        intercept := intercept
        height := scale
        height_pos := hscale }
    have hslopeApprox : ∀ z ∈ trapezoid.core,
        horizontalSlice richShading.shading.union z ≠ ∅ →
          |twoScale.coarseGrains.globalGrains.slope z - trapezoid.affine z| ≤ scale := by
      intro z _hz hslice
      rcases hcenterFor z hslice with ⟨richPoint, hrichPoint, hclose⟩
      let graphCell := (rich.pathFor richPoint).2.1
      let center := (wz1Lemma23CellCenter prep.graphScale graphCell) 2
      let centered := center - baseHeight
      let baseCentered := baseCenter - baseHeight
      have hstrip := rich.centered_strip richPoint hrichPoint
      have hbaseStrip := rich.centered_strip basePoint hbasePoint
      have hcenterApprox :
          |wz1Lemma23CenteredSlope baseHeight
                prep.windowed.global.extendedSlope centered -
            wz1Lemma23CenteredSlope baseHeight
                prep.windowed.global.extendedSlope baseCentered| ≤
              3 * prep.graphScale := by
        apply pureWZ2_near_vertical_centered_approximation
          rich.direction rich.direction_unit prep.graphScale prep.graphScale_pos
          (wz1Lemma23CenteredSlope baseHeight
            prep.windowed.global.extendedSlope)
          (fun first second => by
            dsimp only [wz1Lemma23CenteredSlope]
            have h := hextendedLip (first + baseHeight) (second + baseHeight)
            convert h using 1 <;> ring)
          hvertical centered baseCentered
        · simpa [baseHeight, graphCell, center, centered] using hstrip
        · simpa [baseHeight, baseCell, baseCenter, baseCentered] using hbaseStrip
      have hextendedClose :
          |prep.windowed.global.extendedSlope z -
            prep.windowed.global.extendedSlope center| ≤ prep.graphScale :=
        (hextendedLip z center).trans hclose
      have hsource := hsourceEq z hslice
      rw [← hsource]
      change |prep.windowed.global.extendedSlope z - (0 * z + intercept)| ≤ scale
      simp only [zero_mul, zero_add]
      dsimp only [intercept]
      have hcenterEq :
          |wz1Lemma23CenteredSlope baseHeight
                prep.windowed.global.extendedSlope centered -
            wz1Lemma23CenteredSlope baseHeight
                prep.windowed.global.extendedSlope baseCentered| =
            |prep.windowed.global.extendedSlope center -
              prep.windowed.global.extendedSlope baseCenter| := by
        dsimp only [wz1Lemma23CenteredSlope, centered, baseCentered]
        rw [show center - baseHeight + baseHeight = center by ring,
          show baseCenter - baseHeight + baseHeight = baseCenter by ring]
        ring_nf
      rw [hcenterEq] at hcenterApprox
      calc
        |prep.windowed.global.extendedSlope z -
            prep.windowed.global.extendedSlope baseCenter| ≤
            |prep.windowed.global.extendedSlope z -
              prep.windowed.global.extendedSlope center| +
            |prep.windowed.global.extendedSlope center -
              prep.windowed.global.extendedSlope baseCenter| :=
          abs_sub_le _ _ _
        _ ≤ prep.graphScale + 3 * prep.graphScale := by gcongr
        _ ≤ scale := by dsimp only [scale]; linarith [prep.graphScale_pos]
    exact ⟨{
      scale := scale
      scale_eq := rfl
      scale_pos := hscale
      scale_le_one := hscaleOne
      trapezoid := trapezoid
      height_eq := rfl
      slope_bound := by simp [trapezoid]
      length_bounds := by
        dsimp only [trapezoid, WZ1VerticalTrapezoid.length]
        rw [hlength]
        exact ⟨hlengthLower, hlengthUpper⟩
      core_height_window := by
        intro z hz
        exact hcoreWindow z (by
          simpa [trapezoid, WZ1VerticalTrapezoid.core] using hz)
      active_height_coverage := by
        intro z hslice
        simpa [trapezoid, WZ1VerticalTrapezoid.core] using hcore z hslice
      slope_approximation := hslopeApprox
    }⟩

end Kakeya.Assouad
