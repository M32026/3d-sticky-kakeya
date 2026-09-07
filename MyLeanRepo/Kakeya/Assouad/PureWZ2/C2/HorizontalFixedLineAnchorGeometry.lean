import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineGraphParents

/-!
# Actual anchor geometry for the fixed-line Lemma-23 graph

The graph-cell representative, the paper parent, and the maximal
self-centered source use three independent choices.  This module keeps those
choices distinct and proves the metric incidences needed by the generalized
Lemma-23 family.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The actual maximal-source anchor attached to one genuine graph cell. -/
def PureWZ2HorizontalFixedLineGraphParentData.anchorFor
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading :
      PureWZ2HorizontalFixedLineResidueShadingData residue}
    {prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading}
    (graphParents : PureWZ2HorizontalFixedLineGraphParentData prep)
    (sources : PureWZ2HorizontalFixedLineResidueSourceFamily residueShading)
    (cell : ℤ × ℤ × ℤ)
    (hcell : cell ∈ prep.windowed.global.cells) : Point3 :=
  (sources.sourceFor (graphParents.parentOf cell)
    (graphParents.parent_mem cell hcell)).anchor

lemma PureWZ2HorizontalFixedLineGraphParentData.anchorFor_mem_shadow
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading :
      PureWZ2HorizontalFixedLineResidueShadingData residue}
    {prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading}
    (graphParents : PureWZ2HorizontalFixedLineGraphParentData prep)
    (sources : PureWZ2HorizontalFixedLineResidueSourceFamily residueShading)
    (cell : ℤ × ℤ × ℤ)
    (hcell : cell ∈ prep.windowed.global.cells) :
    graphParents.anchorFor sources cell hcell ∈ prep.shadow.union := by
  rw [prep.shadow_union]
  exact sources.anchor_mem _ _

/-- The WZ1 canonical representative lies in the graph-scale ball of the
actual maximal-source anchor. -/
lemma PureWZ2HorizontalFixedLineGraphParentData.canonical_rep_dist_anchor
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading :
      PureWZ2HorizontalFixedLineResidueShadingData residue}
    {prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading}
    (graphParents : PureWZ2HorizontalFixedLineGraphParentData prep)
    (sources : PureWZ2HorizontalFixedLineResidueSourceFamily residueShading)
    (cell : ℤ × ℤ × ℤ)
    (hcell : cell ∈ prep.windowed.global.cells) :
    dist
        (wz1Lemma23CellRepresentative prep.shadow prep.graphScale_pos
          ⟨cell, prep.windowed.global.cells_active hcell⟩)
        (graphParents.anchorFor sources cell hcell) ≤
      Real.sqrt prep.graphScale := by
  let genuine := graphParents.representative cell
  let anchor := graphParents.anchorFor sources cell hcell
  have hsame :
      dist
          (wz1Lemma23CellRepresentative prep.shadow prep.graphScale_pos
            ⟨cell, prep.windowed.global.cells_active hcell⟩)
          genuine ≤ prep.graphScale := by
    apply wz1Lemma23_same_cell_dist prep.graphScale_pos
    rw [wz1Lemma23CellRepresentative_index]
    exact (graphParents.representative_index cell hcell).symm
  have hpaperGenuine := graphParents.representative_mem_parent cell hcell
  have hpaperAnchor := sources.anchor_mem_parent
    (graphParents.parentOf cell) (graphParents.parent_mem cell hcell)
  have hparent : dist genuine anchor <
      2 * twoScale.sqrtRequested.1 :=
    wz1_paper_grid_cube_diameter_lt_two_rho
      twoScale.fine.coarse_extremal.delta_pos
      hpaperGenuine hpaperAnchor
  calc
    dist
        (wz1Lemma23CellRepresentative prep.shadow prep.graphScale_pos
          ⟨cell, prep.windowed.global.cells_active hcell⟩)
        anchor
        ≤ dist
            (wz1Lemma23CellRepresentative prep.shadow prep.graphScale_pos
              ⟨cell, prep.windowed.global.cells_active hcell⟩)
            genuine + dist genuine anchor :=
          dist_triangle _ _ _
    _ ≤ prep.graphScale + 2 * twoScale.sqrtRequested.1 := by
      linarith
    _ ≤ Real.sqrt prep.graphScale := by
      rw [prep.graphScale_sqrt]
      exact prep.graphScale_two_root_bound

/-- Actual source anchors vary at most four times the snapped graph-y
separation.  The proof uses the common paper height, the fixed global line,
and the 512-separated actual parent residue. -/
lemma PureWZ2HorizontalFixedLineGraphParentData.anchorFor_dist
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading :
      PureWZ2HorizontalFixedLineResidueShadingData residue}
    {prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading}
    (graphParents : PureWZ2HorizontalFixedLineGraphParentData prep)
    (sources : PureWZ2HorizontalFixedLineResidueSourceFamily residueShading)
    (first : ℤ × ℤ × ℤ)
    (hfirst : first ∈ prep.windowed.global.cells)
    (second : ℤ × ℤ × ℤ)
    (hsecond : second ∈ prep.windowed.global.cells) :
    dist
        (graphParents.anchorFor sources first hfirst)
        (graphParents.anchorFor sources second hsecond) ≤
      4 *
        |wz1Lemma23SnappedYValue prep.graphScale first.2.1 -
          wz1Lemma23SnappedYValue prep.graphScale second.2.1| := by
  let firstParent := graphParents.parentOf first
  let secondParent := graphParents.parentOf second
  by_cases hparent : firstParent = secondParent
  · have hanchor :
        graphParents.anchorFor sources first hfirst =
          graphParents.anchorFor sources second hsecond := by
      have hparent' :
          graphParents.parentOf first = graphParents.parentOf second := by
        simpa [firstParent, secondParent] using hparent
      simp only [PureWZ2HorizontalFixedLineGraphParentData.anchorFor, hparent']
    rw [hanchor, dist_self]
    positivity
  · let firstRep := graphParents.representative first
    let secondRep := graphParents.representative second
    let firstAnchor := graphParents.anchorFor sources first hfirst
    let secondAnchor := graphParents.anchorFor sources second hsecond
    let root := twoScale.sqrtRequested.1
    let y₁ := wz1Lemma23SnappedYValue prep.graphScale first.2.1
    let y₂ := wz1Lemma23SnappedYValue prep.graphScale second.2.1
    let d := |y₁ - y₂|
    have hroot : 0 < root := twoScale.fine.coarse_extremal.delta_pos
    have hfirstCenter :=
      ((wz1_lemma23_snapped_cell_geometry prep.graphScale
          prep.graphScale_pos prep.graphScale_one).2.1
        first firstRep (graphParents.representative_index first hfirst)).1
          (1 : Fin 3)
    have hsecondCenter :=
      ((wz1_lemma23_snapped_cell_geometry prep.graphScale
          prep.graphScale_pos prep.graphScale_one).2.1
        second secondRep (graphParents.representative_index second hsecond)).1
          (1 : Fin 3)
    have hfirstY : |firstRep 1 - y₁| ≤ prep.graphScale / 2 := by
      simpa [y₁, wz1Lemma23SnappedYValue, wz1Lemma23CellCenter, point3]
        using hfirstCenter
    have hsecondY : |secondRep 1 - y₂| ≤ prep.graphScale / 2 := by
      simpa [y₂, wz1Lemma23SnappedYValue, wz1Lemma23CellCenter, point3]
        using hsecondCenter
    have hrepYUpper : |firstRep 1 - secondRep 1| ≤
        d + prep.graphScale := by
      calc
        |firstRep 1 - secondRep 1| =
            |(firstRep 1 - y₁) + (y₁ - y₂) +
              (y₂ - secondRep 1)| := by ring_nf
        _ ≤ |firstRep 1 - y₁| + |y₁ - y₂| +
              |y₂ - secondRep 1| := by
          calc
            _ ≤ |(firstRep 1 - y₁) + (y₁ - y₂)| +
                  |y₂ - secondRep 1| := abs_add_le _ _
            _ ≤ (|firstRep 1 - y₁| + |y₁ - y₂|) +
                  |y₂ - secondRep 1| := by
              gcongr
              exact abs_add_le _ _
        _ ≤ d + prep.graphScale := by
          rw [abs_sub_comm y₂ (secondRep 1)]
          dsimp only [d]
          linarith
    have hfar := graphParents.different_parent_y_far
      first hfirst second hsecond hparent
    have hgraphSmall : prep.graphScale ≤ 14 * root := by
      linarith [prep.graphScale_two_root_bound]
    have hseparation : 497 * root < d := by
      linarith [hfar, hrepYUpper]
    have hfirstPaper := sources.anchor_mem_parent firstParent
      (graphParents.parent_mem first hfirst)
    have hsecondPaper := sources.anchor_mem_parent secondParent
      (graphParents.parent_mem second hsecond)
    have hfirstRepPaper := graphParents.representative_mem_parent first hfirst
    have hsecondRepPaper := graphParents.representative_mem_parent second hsecond
    have hfirstAnchorRep : dist firstAnchor firstRep < 2 * root := by
      exact wz1_paper_grid_cube_diameter_lt_two_rho hroot
        hfirstPaper hfirstRepPaper
    have hsecondAnchorRep : dist secondAnchor secondRep < 2 * root := by
      exact wz1_paper_grid_cube_diameter_lt_two_rho hroot
        hsecondPaper hsecondRepPaper
    have hsecondRepAnchor : dist secondRep secondAnchor < 2 * root := by
      simpa [dist_comm] using hsecondAnchorRep
    have hy : |firstAnchor 1 - secondAnchor 1| ≤ d + 18 * root := by
      have hfirstCoord := abs_coord_sub_le_dist
        (x := firstAnchor) (y := firstRep) (1 : Fin 3)
      have hsecondCoord := abs_coord_sub_le_dist
        (x := secondRep) (y := secondAnchor) (1 : Fin 3)
      calc
        |firstAnchor 1 - secondAnchor 1| =
            |(firstAnchor 1 - firstRep 1) +
              (firstRep 1 - secondRep 1) +
              (secondRep 1 - secondAnchor 1)| := by ring_nf
        _ ≤ |firstAnchor 1 - firstRep 1| +
              |firstRep 1 - secondRep 1| +
              |secondRep 1 - secondAnchor 1| := by
          calc
            _ ≤ |(firstAnchor 1 - firstRep 1) +
                    (firstRep 1 - secondRep 1)| +
                  |secondRep 1 - secondAnchor 1| := abs_add_le _ _
            _ ≤ (|firstAnchor 1 - firstRep 1| +
                    |firstRep 1 - secondRep 1|) +
                  |secondRep 1 - secondAnchor 1| := by
              gcongr
              exact abs_add_le _ _
        _ ≤ d + 18 * root := by
          linarith [hfirstCoord, hsecondCoord, hfirstAnchorRep,
            hsecondRepAnchor, hrepYUpper, hgraphSmall]
    have hfirstBox := hfirstPaper
    have hsecondBox := hsecondPaper
    rw [wz1PaperGridCube_eq_Ico hroot firstParent] at hfirstBox
    rw [wz1PaperGridCube_eq_Ico hroot secondParent] at hsecondBox
    have hparentHeightFirst := residueShading.parent_height_eq firstParent
      (graphParents.parent_mem first hfirst)
    have hparentHeightSecond := residueShading.parent_height_eq secondParent
      (graphParents.parent_mem second hsecond)
    have hz : |firstAnchor 2 - secondAnchor 2| ≤ root := by
      rw [abs_le]
      have hfirstLower := hfirstBox.2.2.2.2.1
      have hfirstUpper := hfirstBox.2.2.2.2.2
      have hsecondLower := hsecondBox.2.2.2.2.1
      have hsecondUpper := hsecondBox.2.2.2.2.2
      rw [hparentHeightFirst] at hfirstLower hfirstUpper
      rw [hparentHeightSecond] at hsecondLower hsecondUpper
      change (residueShading.commonParentHeight : ℝ) * root ≤
        firstAnchor 2 at hfirstLower
      change firstAnchor 2 <
        ((residueShading.commonParentHeight : ℝ) + 1) * root at hfirstUpper
      change (residueShading.commonParentHeight : ℝ) * root ≤
        secondAnchor 2 at hsecondLower
      change secondAnchor 2 <
        ((residueShading.commonParentHeight : ℝ) + 1) * root at hsecondUpper
      constructor <;> linarith
    have hfirstShadow := graphParents.anchorFor_mem_shadow sources first hfirst
    have hsecondShadow := graphParents.anchorFor_mem_shadow sources second hsecond
    have hfirstLine := prep.fixed_line_localization firstAnchor hfirstShadow
    have hsecondLine := prep.fixed_line_localization secondAnchor hsecondShadow
    have hfirstPaperUnion : firstAnchor ∈ residueShading.shading.union := by
      rwa [prep.shadow_union] at hfirstShadow
    have hsecondPaperUnion : secondAnchor ∈ residueShading.shading.union := by
      rwa [prep.shadow_union] at hsecondShadow
    have hfirstAxis := shading_union_subset_axisBox hfirstPaperUnion
    have hsecondAxis := shading_union_subset_axisBox hsecondPaperUnion
    have hfirstHeight : firstAnchor 2 ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Kakeya.Streamlined.axisBox, abs_le] using hfirstAxis.2.2
    have hsecondHeight : secondAnchor 2 ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Kakeya.Streamlined.axisBox, abs_le] using hsecondAxis.2.2
    have hsecondYBound : |secondAnchor 1| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hsecondAxis.2.1
    have hslopeFirst :
        |prep.windowed.global.sourceSlope (firstAnchor 2)| ≤ 3 := by
      rw [prep.sourceSlope_eq]
      exact twoScale.coarseGrains_slope_bound
        (firstAnchor 2) hfirstHeight
    have hslopeDiff :
        |prep.windowed.global.sourceSlope (firstAnchor 2) -
            prep.windowed.global.sourceSlope (secondAnchor 2)| ≤ root := by
      rw [prep.sourceSlope_eq]
      have hlip := twoScale.coarseGrains.globalGrains.slope_lipschitz.dist_le_mul
        (firstAnchor 2) hfirstHeight (secondAnchor 2) hsecondHeight
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
      exact hlip.trans hz
    have hprojection :
        |(firstAnchor 0 +
              prep.windowed.global.sourceSlope (firstAnchor 2) * firstAnchor 1) -
            (secondAnchor 0 +
              prep.windowed.global.sourceSlope (secondAnchor 2) * secondAnchor 1)| ≤
          28 * root := by
      have hfirstInner :
          inner ℝ firstAnchor
              (globalGrainDirection
                (prep.windowed.global.sourceSlope (firstAnchor 2))) =
            firstAnchor 0 +
              prep.windowed.global.sourceSlope (firstAnchor 2) * firstAnchor 1 := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      have hsecondInner :
          inner ℝ secondAnchor
              (globalGrainDirection
                (prep.windowed.global.sourceSlope (secondAnchor 2))) =
            secondAnchor 0 +
              prep.windowed.global.sourceSlope (secondAnchor 2) * secondAnchor 1 := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      rw [hfirstInner] at hfirstLine
      rw [hsecondInner] at hsecondLine
      have htriangle := abs_sub
        ((firstAnchor 0 +
            prep.windowed.global.sourceSlope (firstAnchor 2) * firstAnchor 1) -
          line.lineLevel)
        ((secondAnchor 0 +
            prep.windowed.global.sourceSlope (secondAnchor 2) * secondAnchor 1) -
          line.lineLevel)
      have hrearrange :
          ((firstAnchor 0 +
              prep.windowed.global.sourceSlope (firstAnchor 2) * firstAnchor 1) -
            line.lineLevel) -
          ((secondAnchor 0 +
              prep.windowed.global.sourceSlope (secondAnchor 2) * secondAnchor 1) -
            line.lineLevel) =
          (firstAnchor 0 +
              prep.windowed.global.sourceSlope (firstAnchor 2) * firstAnchor 1) -
            (secondAnchor 0 +
              prep.windowed.global.sourceSlope (secondAnchor 2) * secondAnchor 1) := by
        ring
      rw [hrearrange] at htriangle
      exact htriangle.trans (by linarith [hfirstLine, hsecondLine])
    have hslopeProduct :
        |prep.windowed.global.sourceSlope (firstAnchor 2) * firstAnchor 1 -
            prep.windowed.global.sourceSlope (secondAnchor 2) * secondAnchor 1| ≤
          3 * |firstAnchor 1 - secondAnchor 1| + root := by
      have hrearrange :
          prep.windowed.global.sourceSlope (firstAnchor 2) * firstAnchor 1 -
              prep.windowed.global.sourceSlope (secondAnchor 2) * secondAnchor 1 =
            prep.windowed.global.sourceSlope (firstAnchor 2) *
                (firstAnchor 1 - secondAnchor 1) +
              (prep.windowed.global.sourceSlope (firstAnchor 2) -
                prep.windowed.global.sourceSlope (secondAnchor 2)) *
                secondAnchor 1 := by ring
      rw [hrearrange]
      calc
        _ ≤ |prep.windowed.global.sourceSlope (firstAnchor 2)| *
              |firstAnchor 1 - secondAnchor 1| +
            |prep.windowed.global.sourceSlope (firstAnchor 2) -
              prep.windowed.global.sourceSlope (secondAnchor 2)| *
              |secondAnchor 1| := by
          simpa [abs_mul] using abs_add_le
            (prep.windowed.global.sourceSlope (firstAnchor 2) *
              (firstAnchor 1 - secondAnchor 1))
            ((prep.windowed.global.sourceSlope (firstAnchor 2) -
                prep.windowed.global.sourceSlope (secondAnchor 2)) *
              secondAnchor 1)
        _ ≤ 3 * |firstAnchor 1 - secondAnchor 1| + root := by
          have hyNonneg := abs_nonneg (firstAnchor 1 - secondAnchor 1)
          nlinarith [mul_le_mul_of_nonneg_right hslopeFirst hyNonneg,
            mul_le_mul hslopeDiff hsecondYBound (abs_nonneg _) (by positivity)]
    have hx : |firstAnchor 0 - secondAnchor 0| ≤ 3 * d + 83 * root := by
      have hsolve := abs_sub
        ((firstAnchor 0 +
            prep.windowed.global.sourceSlope (firstAnchor 2) * firstAnchor 1) -
          (secondAnchor 0 +
            prep.windowed.global.sourceSlope (secondAnchor 2) * secondAnchor 1))
        (prep.windowed.global.sourceSlope (firstAnchor 2) * firstAnchor 1 -
          prep.windowed.global.sourceSlope (secondAnchor 2) * secondAnchor 1)
      have hrearrange :
          ((firstAnchor 0 +
              prep.windowed.global.sourceSlope (firstAnchor 2) * firstAnchor 1) -
            (secondAnchor 0 +
              prep.windowed.global.sourceSlope (secondAnchor 2) * secondAnchor 1)) -
          (prep.windowed.global.sourceSlope (firstAnchor 2) * firstAnchor 1 -
            prep.windowed.global.sourceSlope (secondAnchor 2) * secondAnchor 1) =
          firstAnchor 0 - secondAnchor 0 := by ring
      rw [hrearrange] at hsolve
      linarith [hprojection, hslopeProduct, hy]
    have hdNonneg : 0 ≤ d := abs_nonneg _
    have hx' : |firstAnchor 0 - secondAnchor 0| ≤ 13 * d / 4 := by
      linarith [hx, hseparation]
    have hy' : |firstAnchor 1 - secondAnchor 1| ≤ 21 * d / 20 := by
      linarith [hy, hseparation]
    have hz' : |firstAnchor 2 - secondAnchor 2| ≤ d / 400 := by
      linarith [hz, hseparation]
    have hxSq : (firstAnchor 0 - secondAnchor 0) ^ 2 ≤ (13 * d / 4) ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg (by positivity : 0 ≤ 13 * d / 4)] using hx'
    have hySq : (firstAnchor 1 - secondAnchor 1) ^ 2 ≤ (21 * d / 20) ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg (by positivity : 0 ≤ 21 * d / 20)] using hy'
    have hzSq : (firstAnchor 2 - secondAnchor 2) ^ 2 ≤ (d / 400) ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg (by positivity : 0 ≤ d / 400)] using hz'
    have hcoeff :
        (13 * d / 4) ^ 2 + (21 * d / 20) ^ 2 + (d / 400) ^ 2 ≤
          (4 * d) ^ 2 := by
      nlinarith [sq_nonneg d]
    have hdistSq : dist firstAnchor secondAnchor ^ 2 ≤ (4 * d) ^ 2 := by
      rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
      simpa [Real.dist_eq, sq_abs] using
        (add_le_add (add_le_add hxSq hySq) hzSq).trans hcoeff
    have hdistNonneg : 0 ≤ dist firstAnchor secondAnchor := dist_nonneg
    have htargetNonneg : 0 ≤ 4 * d := by positivity
    exact (sq_le_sq₀ hdistNonneg htargetNonneg).mp hdistSq

end Kakeya.Assouad
