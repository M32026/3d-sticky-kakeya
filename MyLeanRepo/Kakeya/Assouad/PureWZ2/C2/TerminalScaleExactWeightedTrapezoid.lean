import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactRichHeightCells
import MyLeanRepo.Kakeya.Assouad.WZ1.LocallyLinearOneScale.AlternativeAToTrapezoids

/-!
# Fixed-constant terminal trapezoid on the weighted whole-cell shading

This is the terminal geometric certificate used by the mass-retaining route.
The final carrier is the original-family whole-cell shading constructed from
the genuine rich-height union volume.  The fixed loss remains explicit as
`6 * delta`.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalExactWeightedTrapezoid
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    {retained : PureWZ2TerminalBinRetainedShadingData residue}
    {sources : PureWZ2TerminalBinSourceFamily retained}
    {band : PureWZ2TerminalBinFixedBandSelection sources}
    {phase : PureWZ2TerminalBinHeightPhaseSelection band}
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    {graphParents : PureWZ2TerminalExactGraphParentData prep}
    {localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    {first : PureWZ2TerminalExactReadyGraph
      (theoremEta := theoremEta) sharp}
    {ready : PureWZ2TerminalExactRefinedReadyGraph first}
    {rich : PureWZ2TerminalExactAlternativeAHeightData ready outputLoss}
    (weighted : PureWZ2TerminalExactRichHeightCellData rich) where
  scale : ℝ := 6 * delta
  scale_eq : scale = 6 * delta
  scale_pos : 0 < scale
  scale_le_one : scale ≤ 1
  trapezoid : WZ1VerticalTrapezoid
  height_eq : trapezoid.height = scale
  slope_bound : |trapezoid.slope| ≤ 2
  length_bounds :
    Real.rpow scale (1 / 2 + outputLoss) ≤ trapezoid.length ∧
      trapezoid.length ≤ Real.sqrt scale
  core_eq : trapezoid.core = Set.Icc
    ((retained.commonParentHeight : ℝ) * terminal.sqrtRequested.1)
    (((retained.commonParentHeight : ℝ) + 1) * terminal.sqrtRequested.1)
  active_height_coverage :
    ∀ z, horizontalSlice weighted.shading.union z ≠ ∅ →
      z ∈ trapezoid.core
  slope_approximation :
    ∀ z ∈ trapezoid.core,
      horizontalSlice weighted.shading.union z ≠ ∅ →
        |source.globalGrains.slope z - trapezoid.affine z| ≤ scale

/-- The affine intercept is uniformly bounded on every genuine terminal
weighted trapezoid.  The proof uses an occupied source height; it is not a
formal consequence of the slope bound alone. -/
theorem PureWZ2TerminalExactWeightedTrapezoid.intercept_bound
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    {retained : PureWZ2TerminalBinRetainedShadingData residue}
    {sources : PureWZ2TerminalBinSourceFamily retained}
    {band : PureWZ2TerminalBinFixedBandSelection sources}
    {phase : PureWZ2TerminalBinHeightPhaseSelection band}
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    {graphParents : PureWZ2TerminalExactGraphParentData prep}
    {localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    {first : PureWZ2TerminalExactReadyGraph
      (theoremEta := theoremEta) sharp}
    {ready : PureWZ2TerminalExactRefinedReadyGraph first}
    {rich : PureWZ2TerminalExactAlternativeAHeightData ready outputLoss}
    {weighted : PureWZ2TerminalExactRichHeightCellData rich}
    (data : PureWZ2TerminalExactWeightedTrapezoid weighted) :
    |data.trapezoid.intercept| ≤ 6 := by
  rcases weighted.cells_nonempty with ⟨cell, hcell⟩
  rcases weighted.cells_meet cell hcell with
    ⟨point, ⟨hpointRich, _hpointCell⟩⟩
  have hpointWeighted : point ∈ weighted.shading.union := by
    rw [weighted.union_eq]
    exact weighted.richSet_subset_region hpointRich
  let z := point 2
  have hslice : horizontalSlice weighted.shading.union z ≠ ∅ := by
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨point, hpointWeighted, rfl⟩
  have hzCore : z ∈ data.trapezoid.core :=
    data.active_height_coverage z hslice
  have hpointSource : point ∈ source.shading.union :=
    retained.subshading.union_subset
      (weighted.subshading.union_subset hpointWeighted)
  have hpointBox := shading_union_subset_axisBox hpointSource
  have hz : z ∈ Set.Icc (-1 : ℝ) 1 := by
    have habs : |point 2| ≤ 1 := by
      convert hpointBox.2.2 using 1 <;> norm_num
    simpa [z] using abs_le.mp habs
  have hsource : |source.globalGrains.slope z| ≤ 3 :=
    source.globalGrains.slope_bound z hz
  have happrox :
      |source.globalGrains.slope z - data.trapezoid.affine z| ≤ 1 :=
    (data.slope_approximation z hzCore hslice).trans data.scale_le_one
  have haffine : |data.trapezoid.affine z| ≤ 4 := by
    calc
      |data.trapezoid.affine z| ≤
          |source.globalGrains.slope z| +
            |source.globalGrains.slope z - data.trapezoid.affine z| := by
        have h :=
          abs_sub_le (data.trapezoid.affine z)
            (source.globalGrains.slope z) 0
        simpa [abs_sub_comm, add_comm] using h
      _ ≤ 3 + 1 := by gcongr
      _ = 4 := by norm_num
  have hslopez : |data.trapezoid.slope * z| ≤ 2 := by
    rw [abs_mul]
    have hzAbs : |z| ≤ 1 := abs_le.mpr hz
    calc
      |data.trapezoid.slope| * |z| ≤ 2 * 1 := by
        gcongr
        exact data.slope_bound
      _ = 2 := by norm_num
  have hintercept :
      data.trapezoid.intercept =
        data.trapezoid.affine z - data.trapezoid.slope * z := by
    simp [WZ1VerticalTrapezoid.affine]
  rw [hintercept]
  calc
    |data.trapezoid.affine z - data.trapezoid.slope * z| ≤
        |data.trapezoid.affine z| + |data.trapezoid.slope * z| := by
      have h := abs_sub_le (data.trapezoid.affine z) 0
        (data.trapezoid.slope * z)
      simpa using h
    _ ≤ 4 + 2 := add_le_add haffine hslopez
    _ = 6 := by norm_num

theorem PureWZ2TerminalExactRichHeightCellData.toWeightedTrapezoid
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    {retained : PureWZ2TerminalBinRetainedShadingData residue}
    {sources : PureWZ2TerminalBinSourceFamily retained}
    {band : PureWZ2TerminalBinFixedBandSelection sources}
    {phase : PureWZ2TerminalBinHeightPhaseSelection band}
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    {graphParents : PureWZ2TerminalExactGraphParentData prep}
    {localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    {first : PureWZ2TerminalExactReadyGraph
      (theoremEta := theoremEta) sharp}
    {ready : PureWZ2TerminalExactRefinedReadyGraph first}
    {rich : PureWZ2TerminalExactAlternativeAHeightData ready outputLoss}
    (weighted : PureWZ2TerminalExactRichHeightCellData rich)
    (hscaleOne : 6 * delta ≤ 1)
    (hlengthLower :
      Real.rpow (6 * delta) (1 / 2 + outputLoss) ≤ Real.sqrt delta) :
    Nonempty (PureWZ2TerminalExactWeightedTrapezoid weighted) := by
  let scale := 6 * delta
  let root := terminal.sqrtRequested.1
  let left := (retained.commonParentHeight : ℝ) * root
  let right := ((retained.commonParentHeight : ℝ) + 1) * root
  let baseHeight := wz1Lemma23SnappedBaseHeight delta
    sharp.sharp.baseHeightIndex
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
  have hrootEq : root = Real.sqrt delta := terminal.sqrtRequested_eq
  have hscale : 0 < scale := by dsimp only [scale]; positivity
  have hlength : right - left = Real.sqrt delta := by
    dsimp only [right, left]
    rw [hrootEq]
    ring
  have hlengthUpper : Real.sqrt delta ≤ Real.sqrt scale := by
    apply Real.sqrt_le_sqrt
    dsimp only [scale]
    linarith
  have hextendedLip : ∀ firstHeight secondHeight,
      |prep.windowed.global.extendedSlope firstHeight -
          prep.windowed.global.extendedSlope secondHeight| ≤
        |firstHeight - secondHeight| := by
    intro firstHeight secondHeight
    simpa [Real.dist_eq] using
      prep.windowed.global.extendedSlope_lipschitz.dist_le_mul
        firstHeight (by simp) secondHeight (by simp)
  have hsourceEq : ∀ z, horizontalSlice weighted.shading.union z ≠ ∅ →
      prep.windowed.global.extendedSlope z = source.globalGrains.slope z := by
    intro z hslice
    rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint, hheight⟩
    have hsourcePoint : point ∈ source.shading.union :=
      retained.subshading.union_subset
        (weighted.subshading.union_subset hpoint)
    have hbox := shading_union_subset_axisBox hsourcePoint
    have hz : z ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [← hheight]
      have habs : |point 2| ≤ 1 := by
        convert hbox.2.2 using 1 <;> norm_num
      exact abs_le.mp habs
    rw [prep.windowed.global.extendedSlope_eq z hz, prep.sourceSlope_eq]
  have hcenterFor : ∀ z, horizontalSlice weighted.shading.union z ≠ ∅ →
      ∃ richPoint ∈ rich.richF,
        let cell := (rich.pathFor richPoint).2.1
        |z - (wz1Lemma23CellCenter delta cell) 2| < 3 * delta / 2 := by
    intro z hslice
    rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint, hheight⟩
    rcases weighted.point_near_rich_height point hpoint with
      ⟨richPoint, hrichPoint, hclose⟩
    refine ⟨richPoint, hrichPoint, ?_⟩
    rwa [hheight] at hclose
  have hcoreCoverage : ∀ z, horizontalSlice weighted.shading.union z ≠ ∅ →
      z ∈ Set.Icc left right := by
    intro z hslice
    rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint, hheight⟩
    have hretained := weighted.subshading.union_subset hpoint
    have hz := retained.union_height point hretained
    rw [hheight] at hz
    exact ⟨hz.1, hz.2.le⟩
  by_cases hnonvertical : 1 / Real.sqrt 5 ≤ |rich.direction 1|
  · let slope := -(rich.direction 0 / rich.direction 1)
    let intercept :=
      prep.windowed.global.extendedSlope baseHeight - slope * baseHeight
    let trapezoid : WZ1VerticalTrapezoid :=
      { left := left
        right := right
        left_lt_right := by dsimp only [left, right]; linarith
        slope := slope
        intercept := intercept
        height := scale
        height_pos := hscale }
    have hslope : |slope| ≤ 2 := by
      dsimp only [slope]
      have h := slope_bound_from_direction
        rich.direction rich.direction_unit hnonvertical
      convert h using 1 <;> ring
    have happrox : ∀ z ∈ trapezoid.core,
        horizontalSlice weighted.shading.union z ≠ ∅ →
          |source.globalGrains.slope z - trapezoid.affine z| ≤ scale := by
      intro z _hz hslice
      rcases hcenterFor z hslice with ⟨richPoint, hrichPoint, hclose⟩
      let center := (wz1Lemma23CellCenter delta
        (rich.pathFor richPoint).2.1) 2
      let centered := center - baseHeight
      have hstrip := rich.centered_strip richPoint hrichPoint
      have hcenterApprox :
          |wz1Lemma23CenteredSlope baseHeight
              prep.windowed.global.extendedSlope centered -
            slope * centered| ≤ delta := by
        apply strip_affine_approximation rich.direction delta hdelta
          (wz1Lemma23CenteredSlope baseHeight
            prep.windowed.global.extendedSlope) centered hnonvertical
        simpa [baseHeight, center, centered, slope,
          wz1Lemma23SnappedPoint, wz1Lemma23CellCenter] using hstrip
      have hextendedClose :
          |prep.windowed.global.extendedSlope z -
            prep.windowed.global.extendedSlope center| ≤ 3 * delta / 2 :=
        (hextendedLip z center).trans hclose.le
      have hslopeClose : |slope * (z - center)| ≤ 3 * delta := by
        rw [abs_mul]
        have hclose' : |z - center| ≤ 3 * delta / 2 := hclose.le
        nlinarith [abs_nonneg slope]
      have hsource := hsourceEq z hslice
      rw [← hsource]
      change |prep.windowed.global.extendedSlope z -
        (slope * z + intercept)| ≤ scale
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
        have heq : center - baseHeight + baseHeight = center := by ring
        rw [heq]
        calc
          _ = |(prep.windowed.global.extendedSlope z -
                  prep.windowed.global.extendedSlope center) +
                (prep.windowed.global.extendedSlope center -
                  prep.windowed.global.extendedSlope baseHeight -
                  slope * (center - baseHeight)) +
                (-(slope * (z - center)))| := by ring_nf
          _ ≤ |prep.windowed.global.extendedSlope z -
                  prep.windowed.global.extendedSlope center| +
                |prep.windowed.global.extendedSlope center -
                  prep.windowed.global.extendedSlope baseHeight -
                  slope * (center - baseHeight)| +
                |slope * (z - center)| := by
            calc
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
      core_eq := by rfl
      active_height_coverage := by
        intro z hslice
        simpa [trapezoid, WZ1VerticalTrapezoid.core] using
          hcoreCoverage z hslice
      slope_approximation := happrox }⟩
  · have hvertical : |rich.direction 1| < 1 / Real.sqrt 5 :=
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
        height := scale
        height_pos := hscale }
    have hcenterApprox : ∀ point ∈ rich.richF,
        let center := (wz1Lemma23CellCenter delta
          (rich.pathFor point).2.1) 2
        |prep.windowed.global.extendedSlope center -
          prep.windowed.global.extendedSlope baseCenter| ≤ delta := by
      intro point hpoint
      let center := (wz1Lemma23CellCenter delta
        (rich.pathFor point).2.1) 2
      let centered := center - baseHeight
      let baseCentered := baseCenter - baseHeight
      have hstrip := rich.centered_strip point hpoint
      have hbaseStrip := rich.centered_strip basePoint hbasePoint
      have hgap := near_vertical_gap rich.direction rich.direction_unit hvertical
      have hconst := near_vertical_const
      have hbaseStrip' :
          |rich.direction 0 * baseCentered +
            rich.direction 1 *
              wz1Lemma23CenteredSlope baseHeight
                prep.windowed.global.extendedSlope baseCentered| ≤
            (1 / (5 * Real.sqrt 3)) * delta := by
        dsimp only [baseCentered, baseCenter]
        convert hbaseStrip using 1 <;>
          simp only [wz1Lemma23SnappedPoint] <;> ring
      have hstrip' :
          |rich.direction 0 * centered +
            rich.direction 1 *
              wz1Lemma23CenteredSlope baseHeight
                prep.windowed.global.extendedSlope centered| ≤
            (1 / (5 * Real.sqrt 3)) * delta := by
        dsimp only [centered, center]
        convert hstrip using 1 <;>
          simp only [wz1Lemma23SnappedPoint] <;> ring
      have hraw := constant_approximation_near_vertical rich.direction delta
        (1 / (5 * Real.sqrt 3)) (1 / Real.sqrt 5) hdelta (by positivity)
        (wz1Lemma23CenteredSlope baseHeight
          prep.windowed.global.extendedSlope)
        (fun firstHeight secondHeight => by
          dsimp only [wz1Lemma23CenteredSlope]
          have h := hextendedLip
            (firstHeight + baseHeight) (secondHeight + baseHeight)
          convert h using 1 <;> ring)
        hgap hconst baseCentered centered hbaseStrip' hstrip'
      dsimp only [wz1Lemma23CenteredSlope, centered, baseCentered] at hraw
      rw [show center - baseHeight + baseHeight = center by ring,
        show baseCenter - baseHeight + baseHeight = baseCenter by ring] at hraw
      have heq :
          prep.windowed.global.extendedSlope center -
              prep.windowed.global.extendedSlope baseHeight -
                (prep.windowed.global.extendedSlope baseCenter -
                  prep.windowed.global.extendedSlope baseHeight) =
            prep.windowed.global.extendedSlope center -
              prep.windowed.global.extendedSlope baseCenter := by ring
      rw [heq] at hraw
      exact hraw
    have happrox : ∀ z ∈ trapezoid.core,
        horizontalSlice weighted.shading.union z ≠ ∅ →
          |source.globalGrains.slope z - trapezoid.affine z| ≤ scale := by
      intro z _hz hslice
      rcases hcenterFor z hslice with ⟨richPoint, hrichPoint, hclose⟩
      let center := (wz1Lemma23CellCenter delta
        (rich.pathFor richPoint).2.1) 2
      have hcenter := hcenterApprox richPoint hrichPoint
      have hextendedClose :
          |prep.windowed.global.extendedSlope z -
            prep.windowed.global.extendedSlope center| ≤ 3 * delta / 2 :=
        (hextendedLip z center).trans hclose.le
      have hsource := hsourceEq z hslice
      rw [← hsource]
      change |prep.windowed.global.extendedSlope z - (0 * z + intercept)| ≤ scale
      simp only [zero_mul, zero_add]
      dsimp only [intercept, scale]
      calc
        |prep.windowed.global.extendedSlope z -
            prep.windowed.global.extendedSlope baseCenter| ≤
          |prep.windowed.global.extendedSlope z -
              prep.windowed.global.extendedSlope center| +
            |prep.windowed.global.extendedSlope center -
              prep.windowed.global.extendedSlope baseCenter| :=
          abs_sub_le _ _ _
        _ ≤ 3 * delta / 2 + delta := by gcongr
        _ ≤ 6 * delta := by linarith
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
      core_eq := by rfl
      active_height_coverage := by
        intro z hslice
        simpa [trapezoid, WZ1VerticalTrapezoid.core] using
          hcoreCoverage z hslice
      slope_approximation := happrox }⟩

end Kakeya.Assouad
