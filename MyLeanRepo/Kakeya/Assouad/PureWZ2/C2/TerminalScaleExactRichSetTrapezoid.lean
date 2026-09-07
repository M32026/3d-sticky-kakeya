import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactWeightedTrapezoid
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.GenericHierarchyAlgorithms

/-!
# Exact terminal trapezoid on the unexpanded rich carrier

The whole-cell enlargement in `TerminalScaleExactRichHeightCells` is needed
while the terminal output is still used as an extremal input.  It also moves a
height by a fixed multiple of `delta`, so its honest approximation scale is
`6 * delta`.  At the last Corollary-5.6 level the paper instead only needs the
final retained shading.  We therefore return to the genuine rich set before
the whole-cell enlargement, restrict every source carrier by that common
spatial set, and prove the exact `delta` graph containment there.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The slightly narrower nonvertical cutoff used to keep all three terminal
errors inside one exact `delta`. -/
def pureWZ2TerminalDirectionCutoff : ℝ := 13 / 25

lemma pureWZ2_sqrt_three_gt_sixty_seven_over_thirty_nine :
    (67 / 39 : ℝ) < Real.sqrt 3 := by
  have hsqrt : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
  have hsquare : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  nlinarith [sq_nonneg (Real.sqrt (3 : ℝ) - 67 / 39)]

lemma pureWZ2_sqrt_three_gt_seventeen_over_ten :
    (17 / 10 : ℝ) < Real.sqrt 3 := by
  have hsqrt : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
  have hsquare : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  nlinarith [sq_nonneg (Real.sqrt (3 : ℝ) - 17 / 10)]

/-- A unit direction whose second coordinate is at least `13/25` gives an
affine slope bounded by `5/3`. -/
lemma pureWZ2_terminal_slope_bound
    (direction : Point2) (hdirection : ‖direction‖ = 1)
    (hnonvertical : pureWZ2TerminalDirectionCutoff ≤ |direction 1|) :
    |-(direction 0 / direction 1)| ≤ 5 / 3 := by
  let d₀ := direction 0
  let d₁ := direction 1
  have hnorm : d₀ ^ 2 + d₁ ^ 2 = 1 := by
    simpa [d₀, d₁, EuclideanSpace.norm_eq] using hdirection
  have hcutoff : (13 / 25 : ℝ) ≤ |d₁| := by
    simpa [pureWZ2TerminalDirectionCutoff, d₁] using hnonvertical
  have hd₁pos : 0 < |d₁| := (by norm_num : (0 : ℝ) < 13 / 25) |>.trans_le hcutoff
  have hd₁ne : d₁ ≠ 0 := by simpa [abs_pos] using hd₁pos
  have hd₁sq : (169 / 625 : ℝ) ≤ d₁ ^ 2 := by
    have hsq : (13 / 25 : ℝ) ^ 2 ≤ |d₁| ^ 2 := by gcongr
    norm_num at hsq ⊢
    simpa [sq_abs] using hsq
  have hratioSq : d₀ ^ 2 ≤ (25 / 9 : ℝ) * d₁ ^ 2 := by
    nlinarith
  have hratioAbs : |d₀ / d₁| ≤ 5 / 3 := by
    have hsq : |d₀ / d₁| ^ 2 ≤ (5 / 3 : ℝ) ^ 2 := by
      calc
        |d₀ / d₁| ^ 2 = d₀ ^ 2 / d₁ ^ 2 := by
          simp [sq_abs]
          ring
        _ ≤ ((25 / 9 : ℝ) * d₁ ^ 2) / d₁ ^ 2 := by
          exact div_le_div_of_nonneg_right hratioSq (sq_nonneg d₁)
        _ = (5 / 3 : ℝ) ^ 2 := by
          field_simp [hd₁ne]
          ring
    nlinarith [abs_nonneg (d₀ / d₁)]
  simpa [abs_neg] using hratioAbs

/-- In the complementary direction case the first coordinate dominates by a
fixed rational amount. -/
lemma pureWZ2_terminal_near_vertical_gap
    (direction : Point2) (hdirection : ‖direction‖ = 1)
    (hvertical : |direction 1| < pureWZ2TerminalDirectionCutoff) :
    (1 / 3 : ℝ) ≤ |direction 0| - |direction 1| := by
  let d₀ := direction 0
  let d₁ := direction 1
  have hnorm : d₀ ^ 2 + d₁ ^ 2 = 1 := by
    simpa [d₀, d₁, EuclideanSpace.norm_eq] using hdirection
  have hd₁ : |d₁| < (13 / 25 : ℝ) := by
    simpa [pureWZ2TerminalDirectionCutoff, d₁] using hvertical
  have hd₁sq : d₁ ^ 2 < (169 / 625 : ℝ) := by
    have hsq : |d₁| ^ 2 < (13 / 25 : ℝ) ^ 2 := by
      nlinarith [abs_nonneg d₁]
    norm_num at hsq ⊢
    simpa [sq_abs] using hsq
  have hd₀sq : (456 / 625 : ℝ) < d₀ ^ 2 := by nlinarith
  have hd₀ : (64 / 75 : ℝ) < |d₀| := by
    have htarget : (64 / 75 : ℝ) ^ 2 < d₀ ^ 2 := by
      norm_num at hd₀sq ⊢
      nlinarith
    nlinarith [abs_nonneg d₀, sq_abs d₀]
  dsimp only [d₀, d₁] at hd₀ hd₁ ⊢
  nlinarith

/-- The exact strip width gives a sharper affine error at a selected rich
height than the generic `rho`-rounded helper. -/
lemma pureWZ2_terminal_strip_affine_sharp
    (direction : Point2) (delta : ℝ) (hdelta : 0 < delta)
    (f : ℝ → ℝ) (z : ℝ)
    (hnonvertical : pureWZ2TerminalDirectionCutoff ≤ |direction 1|)
    (hstrip : |direction 0 * z + direction 1 * f z| ≤
      delta / (5 * Real.sqrt 3)) :
    |f z - (-(direction 0 / direction 1)) * z| ≤
      5 * delta / (13 * Real.sqrt 3) := by
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hcutoffPos : 0 < pureWZ2TerminalDirectionCutoff := by
    norm_num [pureWZ2TerminalDirectionCutoff]
  have hdirectionPos : 0 < |direction 1| :=
    hcutoffPos.trans_le hnonvertical
  have hdirectionNe : direction 1 ≠ 0 := by
    simpa [abs_pos] using hdirectionPos
  have hformula :
      |f z - (-(direction 0 / direction 1)) * z| =
        |direction 0 * z + direction 1 * f z| / |direction 1| := by
    have heq :
        f z - (-(direction 0 / direction 1)) * z =
          (direction 0 * z + direction 1 * f z) / direction 1 := by
      field_simp [hdirectionNe]
      ring
    rw [heq, abs_div]
  rw [hformula]
  calc
    |direction 0 * z + direction 1 * f z| / |direction 1| ≤
        (delta / (5 * Real.sqrt 3)) / |direction 1| :=
      div_le_div_of_nonneg_right hstrip (abs_nonneg _)
    _ ≤ (delta / (5 * Real.sqrt 3)) /
        pureWZ2TerminalDirectionCutoff := by
      exact div_le_div_of_nonneg_left (by positivity) hcutoffPos hnonvertical
    _ = 5 * delta / (13 * Real.sqrt 3) := by
      simp [pureWZ2TerminalDirectionCutoff]
      field_simp [hsqrt.ne']
      ring

/-- The actual rich-set shading and one exact-`delta` terminal trapezoid.
Unlike the temporary whole-cell enlargement, this final shading is not
claimed to be cubical. -/
structure PureWZ2TerminalExactRichSetTrapezoid
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
  shading : WZ1PaperTubeShading source.family
  carrier_eq : ∀ index, shading.carrier index =
    retained.shading.carrier index ∩ weighted.richSet
  subshading : PureWZ2PaperIsSubshading shading retained.shading
  union_eq : shading.union = weighted.richSet
  constant_multiplicity :
    shading.HasConstantMultiplicity
      terminalSource.multiplicity (2 * terminalSource.multiplicity)
  volume_lower :
    (rich.heightIndices.card : ENNReal) *
        preparedGraph.heightPopular.layerMass ≤ volume shading.union
  multiplicity_mass_lower :
    (terminalSource.multiplicity : ENNReal) * volume shading.union ≤
      shading.mass
  trapezoid : WZ1VerticalTrapezoid
  height_eq : trapezoid.height = delta
  core_eq : trapezoid.core = Set.Icc
    ((retained.commonParentHeight : ℝ) * terminal.sqrtRequested.1)
    (((retained.commonParentHeight : ℝ) + 1) * terminal.sqrtRequested.1)
  slope_bound : |trapezoid.slope| ≤ 2
  length_bounds :
    Real.rpow delta (1 / 2 + outputLoss) ≤ trapezoid.length ∧
      trapezoid.length ≤ Real.sqrt delta
  active_height_coverage :
    ∀ z, horizontalSlice shading.union z ≠ ∅ → z ∈ trapezoid.core
  slope_approximation :
    ∀ z ∈ trapezoid.core,
      horizontalSlice shading.union z ≠ ∅ →
        |source.globalGrains.slope z - trapezoid.affine z| ≤ delta
  /-- The affine approximation is attached to the rich heights themselves,
  not to the auxiliary fixed-line carrier.  This is the certificate used when
  the proof returns from the Lemma-23 graph to the full source shading over
  the selected height set, as in the proof of Corollary 5.6. -/
  rich_height_approximation :
    ∀ heightIndex ∈ rich.heightIndices,
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        |z - wz1Lemma23SnappedBaseHeight delta heightIndex| ≤
            delta / (2 * Real.sqrt 3) →
          |source.globalGrains.slope z - trapezoid.affine z| ≤ delta

theorem PureWZ2TerminalExactRichHeightCellData.toExactRichSetTrapezoid
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
    (houtputLoss : 0 < outputLoss) :
    Nonempty (PureWZ2TerminalExactRichSetTrapezoid weighted) := by
  let shading : WZ1PaperTubeShading source.family :=
    { carrier := fun index => retained.shading.carrier index ∩ weighted.richSet
      measurable_carrier := fun index =>
        (retained.shading.measurable_carrier index).inter
          weighted.richSet_measurable
      subset_body := fun index => Set.inter_subset_left.trans
        (retained.shading.subset_body index) }
  have hrichRetained : weighted.richSet ⊆ retained.shading.union := by
    intro point hpoint
    have hshadow : point ∈ prep.shadow.union := by
      rw [weighted.richSet_eq] at hpoint
      exact hpoint.1
    have hambient := prep.subshading.union_subset hshadow
    rwa [prep.ambient_union] at hambient
  have hsub : PureWZ2PaperIsSubshading shading retained.shading := by
    intro index point hpoint
    exact hpoint.1
  have hunion : shading.union = weighted.richSet := by
    apply Set.Subset.antisymm
    · rintro point ⟨index, hpoint⟩
      exact hpoint.2
    · intro point hpoint
      rcases hrichRetained hpoint with ⟨index, hindex⟩
      exact ⟨index, hindex, hpoint⟩
  have hconstant : shading.HasConstantMultiplicity
      terminalSource.multiplicity (2 * terminalSource.multiplicity) := by
    have hambientMultiplicity :
        retained.zeroExtension.ambientShading.HasConstantMultiplicity
          terminalSource.multiplicity (2 * terminalSource.multiplicity) :=
      retained.zeroExtension.constantMultiplicity (by
        rw [← terminalSource.shading_eq]
        exact terminalSource.constant_multiplicity)
    have hretainedMultiplicity :
        retained.shading.HasConstantMultiplicity
          terminalSource.multiplicity (2 * terminalSource.multiplicity) := by
      intro retainedPoint hretainedPoint
      have hmultiplicity := wholeCellRestriction_pointMultiplicity_eq
        (fun index => retained.carrier_eq index) hretainedPoint
      rw [hmultiplicity]
      exact hambientMultiplicity retainedPoint (by
        rcases hretainedPoint with ⟨index, hindex⟩
        rw [retained.carrier_eq] at hindex
        exact ⟨index, hindex.1⟩)
    intro point hpoint
    have hmultiplicity : shading.pointMultiplicity point =
        retained.shading.pointMultiplicity point := by
      unfold Kakeya.Streamlined.Shading.pointMultiplicity
      congr 1
      ext index
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.1
      · intro hretained
        exact ⟨hretained, by rw [← hunion]; exact hpoint⟩
    rw [hmultiplicity]
    exact hretainedMultiplicity point (hsub.union_subset hpoint)
  let root := terminal.sqrtRequested.1
  let left := (retained.commonParentHeight : ℝ) * root
  let right := ((retained.commonParentHeight : ℝ) + 1) * root
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
  have hsourceEq : ∀ z, horizontalSlice shading.union z ≠ ∅ →
      prep.windowed.global.extendedSlope z = source.globalGrains.slope z := by
    intro z hslice
    rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint, hheight⟩
    have hsourcePoint : point ∈ source.shading.union :=
      retained.subshading.union_subset (hsub.union_subset hpoint)
    have hbox := shading_union_subset_axisBox hsourcePoint
    have hz : z ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [← hheight]
      have habs : |point 2| ≤ 1 := by
        convert hbox.2.2 using 1 <;> norm_num
      exact abs_le.mp habs
    rw [prep.windowed.global.extendedSlope_eq z hz, prep.sourceSlope_eq]
  have hrichCenterFor : ∀ z, horizontalSlice shading.union z ≠ ∅ →
      ∃ richPoint ∈ rich.richF,
        let center := (wz1Lemma23CellCenter delta
          (rich.pathFor richPoint).2.1) 2
        |z - center| ≤ delta / (2 * Real.sqrt 3) := by
    intro z hslice
    rcases Set.nonempty_iff_ne_empty.mpr hslice with
      ⟨point, hpoint, hheight⟩
    have hrichSet : point ∈ weighted.richSet := by
      rw [← hunion]
      exact hpoint
    rw [weighted.richSet_eq, weighted.richRegion_eq] at hrichSet
    rcases Set.mem_iUnion₂.mp hrichSet.2 with
      ⟨heightIndex, hheightIndex, hslab⟩
    rw [rich.heightIndices_eq] at hheightIndex
    rcases Finset.mem_image.mp hheightIndex with
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
  have hcoreCoverage : ∀ z, horizontalSlice shading.union z ≠ ∅ →
      z ∈ Set.Icc left right := by
    intro z hslice
    rcases Set.nonempty_iff_ne_empty.mpr hslice with
      ⟨point, hpoint, hheight⟩
    have hretained := hsub.union_subset hpoint
    have hz := retained.union_height point hretained
    rw [hheight] at hz
    exact ⟨hz.1, hz.2.le⟩
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
    have happrox : ∀ z ∈ trapezoid.core,
        horizontalSlice shading.union z ≠ ∅ →
          |source.globalGrains.slope z - trapezoid.affine z| ≤ delta := by
      intro z _hz hslice
      rcases hrichCenterFor z hslice with
        ⟨richPoint, hrichPoint, hclose⟩
      let center := (wz1Lemma23CellCenter delta
        (rich.pathFor richPoint).2.1) 2
      let centered := center - baseHeight
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
        (hextendedLip z center).trans hclose
      have hslopeClose : |slope * (z - center)| ≤
          (5 / 3) * (delta / (2 * Real.sqrt 3)) := by
        rw [abs_mul]
        exact mul_le_mul hslope hclose (abs_nonneg _) (by norm_num)
      have hsource := hsourceEq z hslice
      rw [← hsource]
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
      have hcloseCenter : |z - center| ≤ delta / (2 * Real.sqrt 3) := by
        rwa [hcenterEq]
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
    exact ⟨{
      shading := shading
      carrier_eq := fun _ => rfl
      subshading := hsub
      union_eq := hunion
      constant_multiplicity := hconstant
      volume_lower := by
        rw [hunion]
        exact weighted.richSet_volume_lower
      multiplicity_mass_lower :=
        (constant_multiplicity_mass_volume_generic hconstant).1
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
    have happrox : ∀ z ∈ trapezoid.core,
        horizontalSlice shading.union z ≠ ∅ →
          |source.globalGrains.slope z - trapezoid.affine z| ≤ delta := by
      intro z _hz hslice
      rcases hrichCenterFor z hslice with
        ⟨richPoint, hrichPoint, hclose⟩
      let center := (wz1Lemma23CellCenter delta
        (rich.pathFor richPoint).2.1) 2
      have hcenter := hcenterApprox richPoint hrichPoint
      have hextendedClose :
          |prep.windowed.global.extendedSlope z -
            prep.windowed.global.extendedSlope center| ≤
              delta / (2 * Real.sqrt 3) :=
        (hextendedLip z center).trans hclose
      have hsource := hsourceEq z hslice
      rw [← hsource]
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
      have hcloseCenter : |z - center| ≤ delta / (2 * Real.sqrt 3) := by
        rwa [hcenterEq]
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
    exact ⟨{
      shading := shading
      carrier_eq := fun _ => rfl
      subshading := hsub
      union_eq := hunion
      constant_multiplicity := hconstant
      volume_lower := by
        rw [hunion]
        exact weighted.richSet_volume_lower
      multiplicity_mass_lower :=
        (constant_multiplicity_mass_volume_generic hconstant).1
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

/-! ## Terminal level for the Corollary-5.6 hierarchy

The terminal level is never used as the source of another Lemma-24 call.  It
therefore carries the final exact rich-set shading and its inherited grain
data, but deliberately has no cubical or extremality field.
-/

structure PureWZ2ExactTerminalLevelData
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (outputLoss : ℝ) where
  shading : WZ1PaperTubeShading source.family
  subshading : PureWZ2PaperIsSubshading shading source.shading
  volume_lower :
    Kakeya.realRpowENN delta (sigma + outputLoss) ≤ volume shading.union
  localGrains : PureWZ2LocalGrainData shading sigma
    (Kakeya.realRpowENN delta (-outputLoss))
  planeMap_vertical_bound :
    ∀ point : {point : Point3 // point ∈ shading.union},
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  sourceGlobalGrains : PureWZ2BoundedLipschitzGlobalGrainData shading sigma
    (Kakeya.realRpowENN delta (-outputLoss))
  source_slope_eq : sourceGlobalGrains.slope = source.globalGrains.slope
  trapezoids : Finset WZ1VerticalTrapezoid
  trapezoids_nonempty : trapezoids.Nonempty
  height_eq : ∀ trapezoid ∈ trapezoids, trapezoid.height = delta
  slope_bound : ∀ trapezoid ∈ trapezoids, |trapezoid.slope| ≤ 2
  length_bounds : ∀ trapezoid ∈ trapezoids,
    Real.rpow delta (1 / 2 + outputLoss) ≤ trapezoid.length ∧
      trapezoid.length ≤ Real.sqrt delta
  separated_cores : ∀ trapezoid ∈ trapezoids,
    ∀ other ∈ trapezoids, trapezoid ≠ other →
      ∀ z ∈ trapezoid.core, ∀ w ∈ other.core,
        Real.sqrt delta ≤ |z - w|
  slope_approximation : ∀ trapezoid ∈ trapezoids,
    ∀ z ∈ trapezoid.core,
      horizontalSlice shading.union z ≠ ∅ →
        |sourceGlobalGrains.slope z - trapezoid.affine z| ≤ delta
  active_height_coverage : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    horizontalSlice shading.union z ≠ ∅ →
      ∃ trapezoid ∈ trapezoids, z ∈ trapezoid.core

/-- Package the exact rich-set geometry as the final hierarchy level once the
outer numerical schedule has paid its volume loss. -/
theorem PureWZ2TerminalExactRichSetTrapezoid.toExactTerminalLevel
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
    (data : PureWZ2TerminalExactRichSetTrapezoid weighted)
    (hinputOutput : inputLoss ≤ outputLoss)
    (hvolume : Kakeya.realRpowENN delta (sigma + outputLoss) ≤
      (rich.heightIndices.card : ENNReal) *
        preparedGraph.heightPopular.layerMass) :
    Nonempty (PureWZ2ExactTerminalLevelData source outputLoss) := by
  have hsubSource : PureWZ2PaperIsSubshading data.shading source.shading :=
    fun index => (data.subshading index).trans (retained.subshading index)
  have hconstant : Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-outputLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one hinputOutput
  have hconstantTop : Kakeya.realRpowENN delta (-outputLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := source.localGrains.restrictWithConstant
    hsubSource hconstant hconstantTop
  let globalGrains := source.globalGrains.restrict
    hsubSource hconstant hconstantTop
  let trapezoids : Finset WZ1VerticalTrapezoid := {data.trapezoid}
  exact ⟨{
    shading := data.shading
    subshading := hsubSource
    volume_lower := hvolume.trans data.volume_lower
    localGrains := localGrains
    planeMap_vertical_bound := by
      intro point
      exact source.planeMap_vertical_bound
        ⟨point, hsubSource.union_subset point.property⟩
    sourceGlobalGrains := globalGrains
    source_slope_eq := rfl
    trapezoids := trapezoids
    trapezoids_nonempty := by simp [trapezoids]
    height_eq := by
      intro candidate hcandidate
      simp only [trapezoids, Finset.mem_singleton] at hcandidate
      subst candidate
      exact data.height_eq
    slope_bound := by
      intro candidate hcandidate
      simp only [trapezoids, Finset.mem_singleton] at hcandidate
      subst candidate
      exact data.slope_bound
    length_bounds := by
      intro candidate hcandidate
      simp only [trapezoids, Finset.mem_singleton] at hcandidate
      subst candidate
      exact data.length_bounds
    separated_cores := by
      intro firstCandidate hfirst secondCandidate hsecond hne
      simp only [trapezoids, Finset.mem_singleton] at hfirst hsecond
      exact False.elim (hne (hfirst.trans hsecond.symm))
    slope_approximation := by
      intro candidate hcandidate z hz hslice
      simp only [trapezoids, Finset.mem_singleton] at hcandidate
      subst candidate
      exact data.slope_approximation z hz hslice
    active_height_coverage := by
      intro z _hz hslice
      exact ⟨data.trapezoid, by simp [trapezoids],
        data.active_height_coverage z hslice⟩ }⟩

/-- The exact terminal core remains in a fixed enlargement of the height
window from which it was constructed. This is the geometric input for the
final residue-class separation of terminal windows. -/
theorem PureWZ2TerminalExactRichSetTrapezoid.core_height_window
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
    (data : PureWZ2TerminalExactRichSetTrapezoid weighted)
    {z : ℝ} (hz : z ∈ data.trapezoid.core) :
    z ∈ Set.Icc (window.left - 2 * Real.sqrt delta)
      (window.left + 3 * Real.sqrt delta) := by
  let root := terminal.sqrtRequested.1
  have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
  have hrootEq : root = Real.sqrt delta := terminal.sqrtRequested_eq
  rcases residue.selected_nonempty with ⟨parent, hparent⟩
  rcases selection.selected_hit parent (residue.selected_subset hparent) with
    ⟨cell, hcell, hcellParent⟩
  have hrepresentativeParent := parents.representative_mem_parent cell hcell
  rw [hcellParent, wz1PaperGridCube_eq_Ico hroot parent] at hrepresentativeParent
  have hparentHeight := retained.parent_height_eq parent hparent
  rw [hparentHeight] at hrepresentativeParent
  have hlineHeight := line.representative_height cell hcell
  have hlineWindow := window.union_height_window
    (line.representative cell) (line.representative_mem cell hcell)
  rw [hlineHeight] at hlineWindow
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

end Kakeya.Assouad

end
