import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightFullGrains

/-!
# Anchor geometry for the joint-height local graph

Selected parent anchors stay in one fixed global strip, are mod-512 separated
in their y-coordinate, and have controlled Euclidean distortion relative to
the final graph y-coordinate.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

namespace PureWZ2Node05V4RichJointFullGrainData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {volumePopular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex}
    {B₀ threshold : ENNReal}
    {block : volumePopular.JointHeightCommonBinData B₀ threshold}
    {oneParent : block.JointOneParentPerYData}
    {separated : PureWZ2Node05V4RichJointSeparatedParentData oneParent}
    (grains : PureWZ2Node05V4RichJointFullGrainData
      (eta := eta) separated)

def parentY
    (_grains : PureWZ2Node05V4RichJointFullGrainData
      (eta := eta) separated)
    (parent : WZ2PaperCellIndex) : ℝ :=
  ((parent.2.1 : ℝ) + 1 / 2) * Real.sqrt rho

theorem anchor_near_line
    {parent : WZ2PaperCellIndex}
    (hparent : parent ∈ separated.selectedParents) :
    |inner ℝ (grains.anchorFor parent)
          (globalGrainDirection
            (current.grain.globalGrains.slope block.referenceHeight)) -
        (block.bin : ℝ) * Real.sqrt rho| ≤ Real.sqrt rho := by
  have hfixed := grains.anchorFor_mem_fixed parent hparent
  have hlabel := hfixed.1.2
  change Int.floor
      (inner ℝ (grains.anchorFor parent)
        (globalGrainDirection
          (current.grain.globalGrains.slope block.referenceHeight)) /
        Real.sqrt rho) = block.bin at hlabel
  rw [Int.floor_eq_iff] at hlabel
  have hroot : 0 < Real.sqrt rho := by
    rw [← pullback.rhoRequested_eq]
    exact Real.sqrt_pos.mpr
      twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hlower :
      (block.bin : ℝ) * Real.sqrt rho ≤
        inner ℝ (grains.anchorFor parent)
          (globalGrainDirection
            (current.grain.globalGrains.slope block.referenceHeight)) := by
    exact (le_div_iff₀ hroot).mp (by simpa [mul_comm] using hlabel.1)
  have hupper :
      inner ℝ (grains.anchorFor parent)
          (globalGrainDirection
            (current.grain.globalGrains.slope block.referenceHeight)) <
        (block.bin : ℝ) * Real.sqrt rho + Real.sqrt rho := by
    have hraw := (div_lt_iff₀ hroot).mp (by simpa using hlabel.2)
    linarith
  rw [abs_le]
  constructor <;> linarith

theorem selectedParent_y_separation
    {first second : WZ2PaperCellIndex}
    (hfirst : first ∈ separated.selectedParents)
    (hsecond : second ∈ separated.selectedParents)
    (hne : first ≠ second) :
    512 * Real.sqrt rho ≤
      |grains.parentY first - grains.parentY second| := by
  have hyNe : first.2.1 ≠ second.2.1 :=
    fun hy => hne
      (separated.selectedParents_y_injective hfirst hsecond hy)
  have hfirstImage :
      first ∈ separated.selectedCells.image pullback.standardSecondParent := by
    rwa [← separated.selectedParents_eq]
  have hsecondImage :
      second ∈ separated.selectedCells.image pullback.standardSecondParent := by
    rwa [← separated.selectedParents_eq]
  rcases Finset.mem_image.mp hfirstImage with
    ⟨firstCell, hfirstCell, hfirstParent⟩
  rcases Finset.mem_image.mp hsecondImage with
    ⟨secondCell, hsecondCell, hsecondParent⟩
  have hfirstResidue := separated.parent_y_residue firstCell hfirstCell
  have hsecondResidue := separated.parent_y_residue secondCell hsecondCell
  rw [hfirstParent] at hfirstResidue
  rw [hsecondParent] at hsecondResidue
  have hmod :
      (first.2.1 - second.2.1) % (512 : ℤ) = 0 := by
    rw [Int.sub_emod, hfirstResidue, hsecondResidue]
    simp
  have hgap : (512 : ℤ) ≤ |first.2.1 - second.2.1| :=
    Int.le_abs_of_dvd (sub_ne_zero.mpr hyNe)
      (by rwa [Int.dvd_iff_emod_eq_zero])
  have hroot : 0 < Real.sqrt rho := by
    rw [← pullback.rhoRequested_eq]
    exact Real.sqrt_pos.mpr
      twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hgapReal :
      (512 : ℝ) ≤ |(first.2.1 : ℝ) - (second.2.1 : ℝ)| := by
    exact_mod_cast hgap
  unfold parentY
  have heq :
      (((first.2.1 : ℝ) + 1 / 2) * Real.sqrt rho -
        ((second.2.1 : ℝ) + 1 / 2) * Real.sqrt rho) =
      ((first.2.1 : ℝ) - (second.2.1 : ℝ)) * Real.sqrt rho := by ring
  rw [heq, abs_mul, abs_of_pos hroot]
  nlinarith

theorem anchor_dist_strong
    (first : WZ2PaperCellIndex)
    (hfirst : first ∈ separated.selectedParents)
    (second : WZ2PaperCellIndex)
    (hsecond : second ∈ separated.selectedParents) :
    dist (grains.anchorFor first) (grains.anchorFor second) ≤
      (33 / 10 : ℝ) * |grains.parentY first - grains.parentY second| := by
  by_cases heq : first = second
  · subst second
    simp
  let firstPoint := grains.anchorFor first
  let secondPoint := grains.anchorFor second
  let root := Real.sqrt rho
  let d := |grains.parentY first - grains.parentY second|
  have hroot : 0 < root := by
    dsimp only [root]
    rw [← pullback.rhoRequested_eq]
    exact Real.sqrt_pos.mpr
      twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hseparation : 512 * root ≤ d := by
    simpa [root, d] using
      grains.selectedParent_y_separation hfirst hsecond heq
  have hfirstCube := grains.anchorFor_mem_parent first hfirst
  have hsecondCube := grains.anchorFor_mem_parent second hsecond
  rw [wz1PaperGridCube_eq_Ico
    twoScale.secondSticky.coarse_extremal.delta_pos] at hfirstCube hsecondCube
  rw [twoScale.sqrtRequested_eq, pullback.rhoRequested_eq] at hfirstCube hsecondCube
  have hfirstY :
      |firstPoint 1 - grains.parentY first| ≤ root / 2 := by
    dsimp only [firstPoint, parentY, root]
    rw [abs_le]
    constructor <;> linarith [hfirstCube.2.2.1, hfirstCube.2.2.2.1]
  have hsecondY :
      |secondPoint 1 - grains.parentY second| ≤ root / 2 := by
    dsimp only [secondPoint, parentY, root]
    rw [abs_le]
    constructor <;> linarith [hsecondCube.2.2.1, hsecondCube.2.2.2.1]
  have hy : |firstPoint 1 - secondPoint 1| ≤ d + root := by
    calc
      _ = |(firstPoint 1 - grains.parentY first) +
            (grains.parentY first - grains.parentY second) +
            (grains.parentY second - secondPoint 1)| := by ring_nf
      _ ≤ |firstPoint 1 - grains.parentY first| +
            |grains.parentY first - grains.parentY second| +
            |grains.parentY second - secondPoint 1| :=
        abs_add_three _ _ _
      _ ≤ d + root := by
        rw [abs_sub_comm (grains.parentY second) (secondPoint 1)]
        dsimp only [d]
        linarith
  have hprojection :
      |(firstPoint 0 +
            current.grain.globalGrains.slope block.referenceHeight *
              firstPoint 1) -
          (secondPoint 0 +
            current.grain.globalGrains.slope block.referenceHeight *
              secondPoint 1)| ≤
        2 * root := by
    have hfirstLine := grains.anchor_near_line hfirst
    have hsecondLine := grains.anchor_near_line hsecond
    have hfirstInner :
        inner ℝ firstPoint
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight)) =
          firstPoint 0 +
            current.grain.globalGrains.slope block.referenceHeight *
              firstPoint 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    have hsecondInner :
        inner ℝ secondPoint
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight)) =
          secondPoint 0 +
            current.grain.globalGrains.slope block.referenceHeight *
              secondPoint 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    rw [hfirstInner] at hfirstLine
    rw [hsecondInner] at hsecondLine
    have htriangle := abs_sub
      ((firstPoint 0 +
          current.grain.globalGrains.slope block.referenceHeight *
            firstPoint 1) - (block.bin : ℝ) * root)
      ((secondPoint 0 +
          current.grain.globalGrains.slope block.referenceHeight *
            secondPoint 1) - (block.bin : ℝ) * root)
    have hrearrange :
        ((firstPoint 0 +
            current.grain.globalGrains.slope block.referenceHeight *
              firstPoint 1) - (block.bin : ℝ) * root) -
          ((secondPoint 0 +
            current.grain.globalGrains.slope block.referenceHeight *
              secondPoint 1) - (block.bin : ℝ) * root) =
        (firstPoint 0 +
            current.grain.globalGrains.slope block.referenceHeight *
              firstPoint 1) -
          (secondPoint 0 +
            current.grain.globalGrains.slope block.referenceHeight *
              secondPoint 1) := by ring
    rw [hrearrange] at htriangle
    exact htriangle.trans (by linarith)
  have hslope :
      |current.grain.globalGrains.slope block.referenceHeight| ≤ 3 :=
    current.grain.globalGrains.slope_bound block.referenceHeight
      (volumePopular.jointPopularHeight_mem_paperRange
        block.referenceHeight_mem)
  have hx : |firstPoint 0 - secondPoint 0| ≤ 3 * d + 5 * root := by
    have hsolve := abs_sub
      ((firstPoint 0 +
          current.grain.globalGrains.slope block.referenceHeight *
            firstPoint 1) -
        (secondPoint 0 +
          current.grain.globalGrains.slope block.referenceHeight *
            secondPoint 1))
      (current.grain.globalGrains.slope block.referenceHeight *
        (firstPoint 1 - secondPoint 1))
    have hrearrange :
        ((firstPoint 0 +
            current.grain.globalGrains.slope block.referenceHeight *
              firstPoint 1) -
          (secondPoint 0 +
            current.grain.globalGrains.slope block.referenceHeight *
              secondPoint 1)) -
          current.grain.globalGrains.slope block.referenceHeight *
            (firstPoint 1 - secondPoint 1) =
        firstPoint 0 - secondPoint 0 := by ring
    rw [hrearrange] at hsolve
    have hproduct :
        |current.grain.globalGrains.slope block.referenceHeight *
            (firstPoint 1 - secondPoint 1)| ≤ 3 * (d + root) := by
      rw [abs_mul]
      exact mul_le_mul hslope hy (abs_nonneg _) (by positivity)
    calc
      _ ≤ _ := hsolve
      _ ≤ 2 * root + 3 * (d + root) := by gcongr
      _ = 3 * d + 5 * root := by ring
  have hfirstHeight := volumePopular.jointSourceSet_height
    (grains.anchorFor first)
    (by
      have hfixed := grains.anchorFor_mem_fixed first hfirst
      exact hfixed.1.1)
  have hsecondHeight := volumePopular.jointSourceSet_height
    (grains.anchorFor second)
    (by
      have hfixed := grains.anchorFor_mem_fixed second hsecond
      exact hfixed.1.1)
  have hz : |firstPoint 2 - secondPoint 2| ≤ root := by
    dsimp only [firstPoint, secondPoint, root]
    rw [abs_le]
    constructor <;>
      linarith [hfirstHeight.1, hfirstHeight.2,
        hsecondHeight.1, hsecondHeight.2]
  have hdNonneg : 0 ≤ d := abs_nonneg _
  have hx' : |firstPoint 0 - secondPoint 0| ≤ 301 * d / 100 := by
    linarith [hx, hseparation]
  have hy' : |firstPoint 1 - secondPoint 1| ≤ 501 * d / 500 := by
    linarith [hy, hseparation]
  have hz' : |firstPoint 2 - secondPoint 2| ≤ d / 512 := by
    linarith [hz, hseparation]
  have hxSq :
      (firstPoint 0 - secondPoint 0) ^ 2 ≤ (301 * d / 100) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg (by positivity : 0 ≤ 301 * d / 100)] using hx'
  have hySq :
      (firstPoint 1 - secondPoint 1) ^ 2 ≤ (501 * d / 500) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg (by positivity : 0 ≤ 501 * d / 500)] using hy'
  have hzSq :
      (firstPoint 2 - secondPoint 2) ^ 2 ≤ (d / 512) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg (by positivity : 0 ≤ d / 512)] using hz'
  have hcoeff :
      (301 * d / 100) ^ 2 + (501 * d / 500) ^ 2 + (d / 512) ^ 2 ≤
        ((33 / 10 : ℝ) * d) ^ 2 := by
    nlinarith [sq_nonneg d]
  have hdistSq :
      dist firstPoint secondPoint ^ 2 ≤ ((33 / 10 : ℝ) * d) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
    simpa [Real.dist_eq, sq_abs] using
      (add_le_add (add_le_add hxSq hySq) hzSq).trans hcoeff
  exact (sq_le_sq₀ dist_nonneg
    (by positivity : 0 ≤ (33 / 10 : ℝ) * d)).mp hdistSq

/-- Constant-four distortion from canonical parent anchors to final graph
y-coordinates. -/
theorem anchor_dist_graph
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : separated.graphScale ≤ 1}
    {prep : PureWZ2AnchoredGraphPreparationData
      (separated.graphInput hbridge hgraphOne)}
    (parents : PureWZ2Node05V4RichJointGraphParentData prep)
    (hheightAbsorb :
      separated.graphScale + 2 * Real.sqrt rho ≤ 16 * Real.sqrt rho)
    (first : WZ2PaperCellIndex)
    (hfirst : first ∈ prep.windowed.global.cells)
    (second : WZ2PaperCellIndex)
    (hsecond : second ∈ prep.windowed.global.cells) :
    dist (grains.anchorFor (parents.parentCell first))
        (grains.anchorFor (parents.parentCell second)) ≤
      4 * |wz1Lemma23SnappedYValue separated.graphScale first.2.1 -
        wz1Lemma23SnappedYValue separated.graphScale second.2.1| := by
  by_cases hparent : parents.parentCell first = parents.parentCell second
  · rw [hparent, dist_self]
    positivity
  let root := Real.sqrt rho
  let parentDistance :=
    |grains.parentY (parents.parentCell first) -
      grains.parentY (parents.parentCell second)|
  let graphDistance :=
    |wz1Lemma23SnappedYValue separated.graphScale first.2.1 -
      wz1Lemma23SnappedYValue separated.graphScale second.2.1|
  have hroot : 0 < root := by
    dsimp only [root]
    rw [← pullback.rhoRequested_eq]
    exact Real.sqrt_pos.mpr
      twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hparentSeparation : 512 * root ≤ parentDistance := by
    simpa [root, parentDistance] using
      grains.selectedParent_y_separation
        (parents.parentCell_selected first hfirst)
        (parents.parentCell_selected second hsecond) hparent
  have hfirstParent := parents.representative_mem_parent first hfirst
  have hsecondParent := parents.representative_mem_parent second hsecond
  rw [wz1PaperGridCube_eq_Ico
    twoScale.secondSticky.coarse_extremal.delta_pos] at hfirstParent hsecondParent
  rw [twoScale.sqrtRequested_eq, pullback.rhoRequested_eq] at hfirstParent hsecondParent
  have hfirstParentClose :
      |parents.representative first 1 -
          grains.parentY (parents.parentCell first)| ≤ root / 2 := by
    dsimp only [parentY, root]
    rw [abs_le]
    constructor <;> linarith
      [hfirstParent.2.2.1, hfirstParent.2.2.2.1]
  have hsecondParentClose :
      |parents.representative second 1 -
          grains.parentY (parents.parentCell second)| ≤ root / 2 := by
    dsimp only [parentY, root]
    rw [abs_le]
    constructor <;> linarith
      [hsecondParent.2.2.1, hsecondParent.2.2.2.1]
  have hfirstGraph :=
    ((wz1_lemma23_snapped_cell_geometry separated.graphScale
      separated.graphScale_pos hgraphOne).2.1 first
      (parents.representative first)
      (parents.representative_index first hfirst)).1 (1 : Fin 3)
  have hsecondGraph :=
    ((wz1_lemma23_snapped_cell_geometry separated.graphScale
      separated.graphScale_pos hgraphOne).2.1 second
      (parents.representative second)
      (parents.representative_index second hsecond)).1 (1 : Fin 3)
  have hfirstGraphClose :
      |parents.representative first 1 -
          wz1Lemma23SnappedYValue separated.graphScale first.2.1| ≤
        separated.graphScale / 2 := by
    simpa [wz1Lemma23SnappedYValue, wz1Lemma23CellCenter, point3]
      using hfirstGraph
  have hsecondGraphClose :
      |parents.representative second 1 -
          wz1Lemma23SnappedYValue separated.graphScale second.2.1| ≤
        separated.graphScale / 2 := by
    simpa [wz1Lemma23SnappedYValue, wz1Lemma23CellCenter, point3]
      using hsecondGraph
  have hrepresentativeToGraph :
      |parents.representative first 1 - parents.representative second 1| ≤
        graphDistance + separated.graphScale := by
    calc
      _ = |(parents.representative first 1 -
            wz1Lemma23SnappedYValue separated.graphScale first.2.1) +
          (wz1Lemma23SnappedYValue separated.graphScale first.2.1 -
            wz1Lemma23SnappedYValue separated.graphScale second.2.1) +
          (wz1Lemma23SnappedYValue separated.graphScale second.2.1 -
            parents.representative second 1)| := by ring_nf
      _ ≤ |parents.representative first 1 -
            wz1Lemma23SnappedYValue separated.graphScale first.2.1| +
          graphDistance +
          |wz1Lemma23SnappedYValue separated.graphScale second.2.1 -
            parents.representative second 1| := by
        simpa [graphDistance] using abs_add_three
          (parents.representative first 1 -
            wz1Lemma23SnappedYValue separated.graphScale first.2.1)
          (wz1Lemma23SnappedYValue separated.graphScale first.2.1 -
            wz1Lemma23SnappedYValue separated.graphScale second.2.1)
          (wz1Lemma23SnappedYValue separated.graphScale second.2.1 -
            parents.representative second 1)
      _ ≤ graphDistance + separated.graphScale := by
        have hsecondGraphClose' :
            |wz1Lemma23SnappedYValue separated.graphScale second.2.1 -
              parents.representative second 1| ≤
                separated.graphScale / 2 := by
          simpa [abs_sub_comm] using hsecondGraphClose
        linarith
  have hparentToGraph :
      parentDistance ≤ graphDistance + separated.graphScale + root := by
    calc
      parentDistance =
          |(grains.parentY (parents.parentCell first) -
              parents.representative first 1) +
            (parents.representative first 1 -
              parents.representative second 1) +
            (parents.representative second 1 -
              grains.parentY (parents.parentCell second))| := by
        dsimp only [parentDistance]
        ring_nf
      _ ≤ |grains.parentY (parents.parentCell first) -
              parents.representative first 1| +
            |parents.representative first 1 -
              parents.representative second 1| +
            |parents.representative second 1 -
              grains.parentY (parents.parentCell second)| :=
        abs_add_three _ _ _
      _ ≤ graphDistance + separated.graphScale + root := by
        have hfirstParentClose' :
            |grains.parentY (parents.parentCell first) -
              parents.representative first 1| ≤ root / 2 := by
          simpa [abs_sub_comm] using hfirstParentClose
        linarith
  have hrootBound : root ≤ parentDistance / 512 := by
    linarith
  have hgraphSmall : separated.graphScale ≤ 14 * root := by
    dsimp only [root] at hheightAbsorb ⊢
    linarith
  have hparentGraph :
      parentDistance ≤ (512 / 497 : ℝ) * graphDistance := by
    nlinarith
  have hanchor := grains.anchor_dist_strong
    (parents.parentCell first) (parents.parentCell_selected first hfirst)
    (parents.parentCell second) (parents.parentCell_selected second hsecond)
  dsimp only [parentDistance, graphDistance] at hparentGraph
  exact hanchor.trans <| by
    nlinarith [abs_nonneg
      (wz1Lemma23SnappedYValue separated.graphScale first.2.1 -
        wz1Lemma23SnappedYValue separated.graphScale second.2.1)]

end PureWZ2Node05V4RichJointFullGrainData

end Kakeya.Assouad

end
