import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactGraphParents

/-!
# Metric geometry of exact-scale terminal anchors
-/

noncomputable section

namespace Kakeya.Assouad

open Set

lemma PureWZ2TerminalExactGraphParentData.anchorFor_mem_parent
    {sigma inputLoss delta stickyLoss : ℝ} {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    {retained : PureWZ2TerminalBinRetainedShadingData residue}
    {sources : PureWZ2TerminalBinSourceFamily retained}
    {band : PureWZ2TerminalBinFixedBandSelection sources}
    {phase : PureWZ2TerminalBinHeightPhaseSelection band}
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    (data : PureWZ2TerminalExactGraphParentData prep)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ prep.windowed.global.cells) :
    data.anchorFor cell hcell ∈
      wz1PaperGridCube terminal.sqrtRequested.1 (data.parentOf cell) := by
  have hphase := anchored.anchor_mem (data.parentOf cell) (data.parent_mem cell hcell)
  have hband := phase.piece_subset _ _ hphase
  have hcoarse := band.piece_subset _ _ hband
  have hparent := band.selected_subset (phase.selected_subset (data.parent_mem cell hcell))
  rw [(sources.sourceFor (data.parentOf cell) hparent).coarseSource_eq,
    (sources.sourceFor (data.parentOf cell) hparent).fullSource_eq] at hcoarse
  change anchored.anchor (data.parentOf cell) (data.parent_mem cell hcell) ∈
    wz1PaperGridCube terminal.sqrtRequested.1 (data.parentOf cell)
  simpa only [sources.sourceFor_cell _ hparent] using hcoarse.1.2

lemma PureWZ2TerminalExactGraphParentData.anchorFor_localized
    {sigma inputLoss delta stickyLoss : ℝ} {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    {retained : PureWZ2TerminalBinRetainedShadingData residue}
    {sources : PureWZ2TerminalBinSourceFamily retained}
    {band : PureWZ2TerminalBinFixedBandSelection sources}
    {phase : PureWZ2TerminalBinHeightPhaseSelection band}
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    (data : PureWZ2TerminalExactGraphParentData prep)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ prep.windowed.global.cells) :
    |inner ℝ (data.anchorFor cell hcell)
          (globalGrainDirection
            (source.globalGrains.slope ((data.anchorFor cell hcell) 2))) -
        band.center| ≤ terminal.sqrtRequested.1 / 2 := by
  exact anchored.piece_localized _ (data.parent_mem cell hcell) _ (by
    rw [anchored.piece_eq]
    exact ⟨anchored.anchor_mem _ _,
      Metric.mem_closedBall_self terminal.sticky.coarse_extremal.delta_pos.le⟩)

lemma PureWZ2TerminalExactGraphParentData.anchorFor_dist
    {sigma inputLoss delta stickyLoss : ℝ} {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    {retained : PureWZ2TerminalBinRetainedShadingData residue}
    {sources : PureWZ2TerminalBinSourceFamily retained}
    {band : PureWZ2TerminalBinFixedBandSelection sources}
    {phase : PureWZ2TerminalBinHeightPhaseSelection band}
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    (data : PureWZ2TerminalExactGraphParentData prep)
    (first : ℤ × ℤ × ℤ) (hfirst : first ∈ prep.windowed.global.cells)
    (second : ℤ × ℤ × ℤ) (hsecond : second ∈ prep.windowed.global.cells) :
    dist (data.anchorFor first hfirst) (data.anchorFor second hsecond) ≤
      4 * |wz1Lemma23SnappedYValue delta first.2.1 -
        wz1Lemma23SnappedYValue delta second.2.1| := by
  by_cases hparent : data.parentOf first = data.parentOf second
  · have hanchor : data.anchorFor first hfirst = data.anchorFor second hsecond := by
      simp only [PureWZ2TerminalExactGraphParentData.anchorFor, hparent]
    rw [hanchor, dist_self]
    positivity
  · let firstRep := data.representative first
    let secondRep := data.representative second
    let firstAnchor := data.anchorFor first hfirst
    let secondAnchor := data.anchorFor second hsecond
    let root := terminal.sqrtRequested.1
    let y₁ := wz1Lemma23SnappedYValue delta first.2.1
    let y₂ := wz1Lemma23SnappedYValue delta second.2.1
    let d := |y₁ - y₂|
    have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
    have hdelta : 0 < delta := source.extremal.delta_pos
    have hdeltaRoot : delta ≤ root := by
      rw [show root = Real.sqrt delta by exact terminal.sqrtRequested_eq]
      nlinarith [Real.sqrt_nonneg delta, Real.sq_sqrt hdelta.le,
        source.extremal.delta_le_one]
    have hfirstCenter := ((wz1_lemma23_snapped_cell_geometry delta hdelta
      source.extremal.delta_le_one).2.1 first firstRep
      (data.representative_index first hfirst)).1 1
    have hsecondCenter := ((wz1_lemma23_snapped_cell_geometry delta hdelta
      source.extremal.delta_le_one).2.1 second secondRep
      (data.representative_index second hsecond)).1 1
    have hfirstY : |firstRep 1 - y₁| ≤ delta / 2 := by
      simpa [y₁, wz1Lemma23SnappedYValue, wz1Lemma23CellCenter, point3]
        using hfirstCenter
    have hsecondY : |secondRep 1 - y₂| ≤ delta / 2 := by
      simpa [y₂, wz1Lemma23SnappedYValue, wz1Lemma23CellCenter, point3]
        using hsecondCenter
    have hrepYUpper : |firstRep 1 - secondRep 1| ≤ d + delta := by
      calc
        _ = |(firstRep 1 - y₁) + (y₁ - y₂) + (y₂ - secondRep 1)| := by ring_nf
        _ ≤ |firstRep 1 - y₁| + |y₁ - y₂| + |y₂ - secondRep 1| := by
          calc
            _ ≤ |(firstRep 1 - y₁) + (y₁ - y₂)| + |y₂ - secondRep 1| :=
              abs_add_le _ _
            _ ≤ (|firstRep 1 - y₁| + |y₁ - y₂|) + |y₂ - secondRep 1| := by
              gcongr; exact abs_add_le _ _
        _ ≤ d + delta := by
          rw [abs_sub_comm y₂ (secondRep 1)]
          dsimp only [d]
          linarith
    have hfar := data.different_parent_y_far first hfirst second hsecond hparent
    have hseparation : 510 * root < d := by
      linarith
    have hfirstAnchorRep : dist firstAnchor firstRep ≤ root := by
      rw [show firstRep = wz1Lemma23CellRepresentative prep.shadow
        source.extremal.delta_pos
        ⟨first, prep.windowed.global.cells_active hfirst⟩ by
          exact data.representative_eq first hfirst]
      rw [show root = Real.sqrt delta by exact terminal.sqrtRequested_eq]
      simpa [firstAnchor, dist_comm] using
        data.canonical_rep_dist_anchor first hfirst
    have hsecondRepAnchor : dist secondRep secondAnchor ≤ root := by
      rw [show secondRep = wz1Lemma23CellRepresentative prep.shadow
        source.extremal.delta_pos
        ⟨second, prep.windowed.global.cells_active hsecond⟩ by
          exact data.representative_eq second hsecond]
      rw [show root = Real.sqrt delta by exact terminal.sqrtRequested_eq]
      simpa [secondAnchor] using data.canonical_rep_dist_anchor second hsecond
    have hy : |firstAnchor 1 - secondAnchor 1| ≤ d + 3 * root := by
      have hfirstCoord := abs_coord_sub_le_dist
        (x := firstAnchor) (y := firstRep) (1 : Fin 3)
      have hsecondCoord := abs_coord_sub_le_dist
        (x := secondRep) (y := secondAnchor) (1 : Fin 3)
      calc
        _ = |(firstAnchor 1 - firstRep 1) +
            (firstRep 1 - secondRep 1) +
            (secondRep 1 - secondAnchor 1)| := by ring_nf
        _ ≤ |firstAnchor 1 - firstRep 1| + |firstRep 1 - secondRep 1| +
            |secondRep 1 - secondAnchor 1| := by
          calc
            _ ≤ |(firstAnchor 1 - firstRep 1) +
                  (firstRep 1 - secondRep 1)| +
                |secondRep 1 - secondAnchor 1| := abs_add_le _ _
            _ ≤ (|firstAnchor 1 - firstRep 1| +
                  |firstRep 1 - secondRep 1|) +
                |secondRep 1 - secondAnchor 1| := by
              gcongr; exact abs_add_le _ _
        _ ≤ d + 3 * root := by
          have hrepBound : |firstRep 1 - secondRep 1| ≤ d + root :=
            hrepYUpper.trans (by linarith)
          have hfirstCoordRoot : |firstAnchor 1 - firstRep 1| ≤ root :=
            hfirstCoord.trans hfirstAnchorRep
          have hsecondCoordRoot : |secondRep 1 - secondAnchor 1| ≤ root :=
            hsecondCoord.trans hsecondRepAnchor
          linarith
    have hfirstBox := data.anchorFor_mem_parent first hfirst
    have hsecondBox := data.anchorFor_mem_parent second hsecond
    rw [wz1PaperGridCube_eq_Ico hroot (data.parentOf first)] at hfirstBox
    rw [wz1PaperGridCube_eq_Ico hroot (data.parentOf second)] at hsecondBox
    have hfirstParentResidue := band.selected_subset
      (phase.selected_subset (data.parent_mem first hfirst))
    have hsecondParentResidue := band.selected_subset
      (phase.selected_subset (data.parent_mem second hsecond))
    have hparentHeightFirst := retained.parent_height_eq _ hfirstParentResidue
    have hparentHeightSecond := retained.parent_height_eq _ hsecondParentResidue
    have hz : |firstAnchor 2 - secondAnchor 2| ≤ root := by
      rw [abs_le]
      rw [hparentHeightFirst] at hfirstBox
      rw [hparentHeightSecond] at hsecondBox
      constructor
      · linarith [hfirstBox.2.2.2.2.1, hsecondBox.2.2.2.2.2.le]
      · linarith [hsecondBox.2.2.2.2.1, hfirstBox.2.2.2.2.2.le]
    have hfirstShadow := data.anchorFor_mem_shadow first hfirst
    have hsecondShadow := data.anchorFor_mem_shadow second hsecond
    have hfirstPaper : firstAnchor ∈ retained.shading.union := by
      have := prep.subshading.union_subset hfirstShadow
      rwa [prep.ambient_union] at this
    have hsecondPaper : secondAnchor ∈ retained.shading.union := by
      have := prep.subshading.union_subset hsecondShadow
      rwa [prep.ambient_union] at this
    have hfirstAxis := shading_union_subset_axisBox hfirstPaper
    have hsecondAxis := shading_union_subset_axisBox hsecondPaper
    have hfirstHeight : firstAnchor 2 ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Kakeya.Streamlined.axisBox, abs_le] using hfirstAxis.2.2
    have hsecondHeight : secondAnchor 2 ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Kakeya.Streamlined.axisBox, abs_le] using hsecondAxis.2.2
    have hsecondYBound : |secondAnchor 1| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hsecondAxis.2.1
    have hslopeFirst : |source.globalGrains.slope (firstAnchor 2)| ≤ 3 :=
      source.globalGrains.slope_bound _ hfirstHeight
    have hslopeDiff : |source.globalGrains.slope (firstAnchor 2) -
        source.globalGrains.slope (secondAnchor 2)| ≤ root := by
      have hlip := source.globalGrains.slope_lipschitz.dist_le_mul
        (firstAnchor 2) hfirstHeight (secondAnchor 2) hsecondHeight
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
      exact hlip.trans hz
    have hprojection :
        |(firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) * firstAnchor 1) -
          (secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) * secondAnchor 1)| ≤
          root := by
      have hfirstLine := data.anchorFor_localized first hfirst
      have hsecondLine := data.anchorFor_localized second hsecond
      have hfirstInner : inner ℝ firstAnchor
            (globalGrainDirection (source.globalGrains.slope (firstAnchor 2))) =
          firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) * firstAnchor 1 := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      have hsecondInner : inner ℝ secondAnchor
            (globalGrainDirection (source.globalGrains.slope (secondAnchor 2))) =
          secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) * secondAnchor 1 := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      rw [hfirstInner] at hfirstLine
      rw [hsecondInner] at hsecondLine
      have htriangle := abs_sub
        ((firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) * firstAnchor 1) -
          band.center)
        ((secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) * secondAnchor 1) -
          band.center)
      have hrearrange :
          ((firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) * firstAnchor 1) - band.center) -
          ((secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) * secondAnchor 1) - band.center) =
          (firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) * firstAnchor 1) -
          (secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) * secondAnchor 1) := by ring
      rw [hrearrange] at htriangle
      linarith
    have hslopeProduct :
        |source.globalGrains.slope (firstAnchor 2) * firstAnchor 1 -
          source.globalGrains.slope (secondAnchor 2) * secondAnchor 1| ≤
          3 * |firstAnchor 1 - secondAnchor 1| + root := by
      have hrearrange :
          source.globalGrains.slope (firstAnchor 2) * firstAnchor 1 -
            source.globalGrains.slope (secondAnchor 2) * secondAnchor 1 =
          source.globalGrains.slope (firstAnchor 2) *
              (firstAnchor 1 - secondAnchor 1) +
            (source.globalGrains.slope (firstAnchor 2) -
              source.globalGrains.slope (secondAnchor 2)) * secondAnchor 1 := by ring
      rw [hrearrange]
      calc
        _ ≤ |source.globalGrains.slope (firstAnchor 2)| *
              |firstAnchor 1 - secondAnchor 1| +
            |source.globalGrains.slope (firstAnchor 2) -
              source.globalGrains.slope (secondAnchor 2)| * |secondAnchor 1| := by
          simpa [abs_mul] using abs_add_le
            (source.globalGrains.slope (firstAnchor 2) *
              (firstAnchor 1 - secondAnchor 1))
            ((source.globalGrains.slope (firstAnchor 2) -
              source.globalGrains.slope (secondAnchor 2)) * secondAnchor 1)
        _ ≤ 3 * |firstAnchor 1 - secondAnchor 1| + root := by
          have hyNonneg := abs_nonneg (firstAnchor 1 - secondAnchor 1)
          nlinarith [mul_le_mul_of_nonneg_right hslopeFirst hyNonneg,
            mul_le_mul hslopeDiff hsecondYBound (abs_nonneg _) (by positivity)]
    have hx : |firstAnchor 0 - secondAnchor 0| ≤ 3 * d + 11 * root := by
      have hsolve := abs_sub
        ((firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) * firstAnchor 1) -
          (secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) * secondAnchor 1))
        (source.globalGrains.slope (firstAnchor 2) * firstAnchor 1 -
          source.globalGrains.slope (secondAnchor 2) * secondAnchor 1)
      have hrearrange :
          ((firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) * firstAnchor 1) -
            (secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) * secondAnchor 1)) -
          (source.globalGrains.slope (firstAnchor 2) * firstAnchor 1 -
            source.globalGrains.slope (secondAnchor 2) * secondAnchor 1) =
          firstAnchor 0 - secondAnchor 0 := by ring
      rw [hrearrange] at hsolve
      linarith
    have hx' : |firstAnchor 0 - secondAnchor 0| ≤ 31 * d / 10 := by
      linarith
    have hy' : |firstAnchor 1 - secondAnchor 1| ≤ 101 * d / 100 := by
      linarith
    have hz' : |firstAnchor 2 - secondAnchor 2| ≤ d / 100 := by
      linarith
    have hxSq : (firstAnchor 0 - secondAnchor 0)^2 ≤ (31*d/10)^2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg (by positivity : 0 ≤ 31*d/10)] using hx'
    have hySq : (firstAnchor 1 - secondAnchor 1)^2 ≤ (101*d/100)^2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg (by positivity : 0 ≤ 101*d/100)] using hy'
    have hzSq : (firstAnchor 2 - secondAnchor 2)^2 ≤ (d/100)^2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg (by positivity : 0 ≤ d/100)] using hz'
    have hcoeff : (31*d/10)^2 + (101*d/100)^2 + (d/100)^2 ≤ (4*d)^2 := by
      nlinarith [sq_nonneg d]
    have hdistSq : dist firstAnchor secondAnchor ^ 2 ≤ (4*d)^2 := by
      rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
      simpa [Real.dist_eq, sq_abs] using
        (add_le_add (add_le_add hxSq hySq) hzSq).trans hcoeff
    exact (sq_le_sq₀ dist_nonneg (by positivity : 0 ≤ 4*d)).mp hdistSq

end Kakeya.Assouad
