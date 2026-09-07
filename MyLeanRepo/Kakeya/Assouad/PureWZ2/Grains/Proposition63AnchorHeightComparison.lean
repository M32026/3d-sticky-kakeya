import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63IntervalLocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperTubeHeightDistance
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DirectionAlignment

/-!
# Compare the parent axial coordinate with the distinguished-tube height
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set

lemma proposition63_paper_height_parent_error
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    (data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity)
    (hDelta : 0 < Delta)
    {point : Point3} (hpoint : point ∈ input.selectedFiber.union) :
    |paperTubeHeight data.anchorTube point -
      100 * proposition63AxialCoordinate
        (coarse.tube input.parent) hrho point| ≤ 4 * rho := by
  have hcover : WZ1PaperTubeCovers data.anchorTube
      (coarse.tube input.parent) := by
    rw [Proposition63CommonSliceRescaledData.anchorTube,
      input.fiberFamily.tube_eq]
    apply (mem_wz2PaperFullFiberIndices_iff input.parent
      (input.fiberFamily.embedding data.commonSlice.distinguished)).mp
    change (Finset.orderEmbOfFin
      (wz2PaperFullFiberIndices fine coarse input.parent) rfl
      data.commonSlice.distinguished) ∈
        wz2PaperFullFiberIndices fine coarse input.parent
    exact Finset.orderEmbOfFin_mem _ _ _
  have hzero : dist (wz1TubeAxisZeroPoint data.anchorTube)
      (wz1TubeAxisZeroPoint (coarse.tube input.parent)) ≤ rho / 2 :=
    hcover.components.1
  have hdirection : ‖wz1PaperDirection data.anchorTube -
      wz1PaperDirection (coarse.tube input.parent)‖ ≤ rho / 2 :=
    paper_cover_direction_alignment hcover
  have hpointNorm : ‖point‖ ≤ 3 := by
    rcases hpoint with ⟨tube, htube⟩
    exact paperShadingPoint_norm_le_three
      (shading := input.selectedFiber) ⟨tube, htube⟩
  have hparentZeroNorm :
      ‖wz1TubeAxisZeroPoint (coarse.tube input.parent)‖ ≤ 1 :=
    paperAxisZeroPoint_norm_le_one (cover.coarse_line_class input.parent)
  have hfirst :
      |inner ℝ
        (point - wz1TubeAxisZeroPoint data.anchorTube)
        (wz1PaperDirection data.anchorTube) -
       inner ℝ
        (point - wz1TubeAxisZeroPoint (coarse.tube input.parent))
        (wz1PaperDirection (coarse.tube input.parent))| ≤ 4 * rho := by
    have hdecomp :
        inner ℝ (point - wz1TubeAxisZeroPoint data.anchorTube)
            (wz1PaperDirection data.anchorTube) -
          inner ℝ (point - wz1TubeAxisZeroPoint (coarse.tube input.parent))
            (wz1PaperDirection (coarse.tube input.parent)) =
        inner ℝ (point - wz1TubeAxisZeroPoint (coarse.tube input.parent))
          (wz1PaperDirection data.anchorTube -
            wz1PaperDirection (coarse.tube input.parent)) +
        inner ℝ (wz1TubeAxisZeroPoint (coarse.tube input.parent) -
          wz1TubeAxisZeroPoint data.anchorTube)
          (wz1PaperDirection data.anchorTube) := by
      have hpointDecomp :
          point - wz1TubeAxisZeroPoint data.anchorTube =
          (point - wz1TubeAxisZeroPoint (coarse.tube input.parent)) +
          (wz1TubeAxisZeroPoint (coarse.tube input.parent) -
            wz1TubeAxisZeroPoint data.anchorTube) := by abel
      rw [hpointDecomp, inner_add_left, inner_sub_right]
      ring
    rw [hdecomp]
    calc
      |inner ℝ (point - wz1TubeAxisZeroPoint (coarse.tube input.parent))
          (wz1PaperDirection data.anchorTube -
            wz1PaperDirection (coarse.tube input.parent)) +
        inner ℝ (wz1TubeAxisZeroPoint (coarse.tube input.parent) -
          wz1TubeAxisZeroPoint data.anchorTube)
          (wz1PaperDirection data.anchorTube)| ≤
        |inner ℝ (point - wz1TubeAxisZeroPoint (coarse.tube input.parent))
          (wz1PaperDirection data.anchorTube -
            wz1PaperDirection (coarse.tube input.parent))| +
        |inner ℝ (wz1TubeAxisZeroPoint (coarse.tube input.parent) -
          wz1TubeAxisZeroPoint data.anchorTube)
          (wz1PaperDirection data.anchorTube)| := abs_add_le _ _
      _ ≤ ‖point - wz1TubeAxisZeroPoint (coarse.tube input.parent)‖ *
            ‖wz1PaperDirection data.anchorTube -
              wz1PaperDirection (coarse.tube input.parent)‖ +
          ‖wz1TubeAxisZeroPoint (coarse.tube input.parent) -
            wz1TubeAxisZeroPoint data.anchorTube‖ *
            ‖wz1PaperDirection data.anchorTube‖ := by
          gcongr <;> exact abs_real_inner_le_norm _ _
      _ ≤ (3 + 1) * (rho / 2) + (rho / 2) * 1 := by
          rw [wz1PaperDirection_norm]
          gcongr
          · exact norm_sub_le _ _ |>.trans (add_le_add hpointNorm hparentZeroNorm)
          · simpa [dist_eq_norm, norm_sub_rev] using hzero
      _ ≤ 4 * rho := by linarith
  rw [proposition63AxialCoordinate_eq]
  change |paperTubeHeight data.anchorTube point -
    100 * ((1 / 100 : ℝ) * inner ℝ
      (point - wz1TubeAxisZeroPoint (coarse.tube input.parent))
      (wz1PaperDirection (coarse.tube input.parent)))| ≤ 4 * rho
  have hhundred : (100 : ℝ) * (1 / 100) = 1 := by norm_num
  have hscaled :
      100 * ((1 / 100 : ℝ) * inner ℝ
        (point - wz1TubeAxisZeroPoint (coarse.tube input.parent))
        (wz1PaperDirection (coarse.tube input.parent))) =
      inner ℝ (point - wz1TubeAxisZeroPoint (coarse.tube input.parent))
        (wz1PaperDirection (coarse.tube input.parent)) := by
    rw [← mul_assoc, hhundred, one_mul]
  rw [hscaled]
  exact hfirst

end Kakeya.Assouad.PureWZ2

end
