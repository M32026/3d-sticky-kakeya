import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalTubeParameters
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.TubeParameterLineDistance
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLinePackingCardinality
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CommonContainerTargetTubeParameterClusterBaseFive

/-!
# Forward stability of affine-diagonal line parameters

The fixed horizontal rotation and diagonal dilation send one coordinatewise
source parameter box to another parameter box.  The estimate is deliberately
coarse but uniform in the common frame and height anchor.
-/

noncomputable section

namespace Kakeya.Assouad

private theorem pureWZ2_affineDiagonalTubeParams_sub_le
    (frameSlope anchor heightScale transverseScale width : ℝ)
    (hframe : |frameSlope| ≤ 1)
    (hanchor : |anchor| ≤ 1)
    (hheight : 1 ≤ heightScale)
    (htransverse : 0 ≤ transverseScale)
    (htransverseOne : transverseScale ≤ 1)
    (hwidth : 0 ≤ width)
    (first second : TubeParams)
    (ha : |first.a - second.a| ≤ width)
    (hb : |first.b - second.b| ≤ width)
    (hc : |first.c - second.c| ≤ width)
    (hd : |first.d - second.d| ≤ width) :
    let firstTarget := pureWZ2AffineDiagonalTubeParams frameSlope anchor
      heightScale transverseScale first
    let secondTarget := pureWZ2AffineDiagonalTubeParams frameSlope anchor
      heightScale transverseScale second
    |firstTarget.a - secondTarget.a| ≤ 4 * width ∧
      |firstTarget.b - secondTarget.b| ≤ 4 * width ∧
      |firstTarget.c - secondTarget.c| ≤ 4 * width ∧
      |firstTarget.d - secondTarget.d| ≤ 4 * width := by
  dsimp only [pureWZ2AffineDiagonalTubeParams]
  have hnormPos : 0 < pureWZ2HorizontalNorm frameSlope :=
    pureWZ2HorizontalNorm_pos frameSlope
  have hnormOne : 1 ≤ pureWZ2HorizontalNorm frameSlope :=
    Real.one_le_sqrt.mpr (by nlinarith)
  have hheightPos : 0 < heightScale := by linarith
  have hdenomPos :
      0 < pureWZ2HorizontalNorm frameSlope * heightScale :=
    mul_pos hnormPos hheightPos
  have hdenomOne :
      1 ≤ pureWZ2HorizontalNorm frameSlope * heightScale := by
    nlinarith
  have haNumerator :
      |(first.a + frameSlope * first.b +
          anchor * (first.c + frameSlope * first.d)) -
        (second.a + frameSlope * second.b +
          anchor * (second.c + frameSlope * second.d))| ≤
        4 * width := by
    rw [show
      (first.a + frameSlope * first.b +
          anchor * (first.c + frameSlope * first.d)) -
        (second.a + frameSlope * second.b +
          anchor * (second.c + frameSlope * second.d)) =
        (first.a - second.a) +
          frameSlope * (first.b - second.b) +
          anchor * ((first.c - second.c) +
            frameSlope * (first.d - second.d)) by ring]
    calc
      |(first.a - second.a) +
          frameSlope * (first.b - second.b) +
          anchor * ((first.c - second.c) +
            frameSlope * (first.d - second.d))|
          ≤ |first.a - second.a| +
              |frameSlope * (first.b - second.b)| +
              |anchor * ((first.c - second.c) +
                frameSlope * (first.d - second.d))| := by
            exact (abs_add_le _ _).trans <| by
              gcongr
              exact abs_add_le _ _
      _ = |first.a - second.a| +
            |frameSlope| * |first.b - second.b| +
            |anchor| * |(first.c - second.c) +
              frameSlope * (first.d - second.d)| := by
            rw [abs_mul, abs_mul]
      _ ≤ |first.a - second.a| +
            |frameSlope| * |first.b - second.b| +
            |anchor| * (|first.c - second.c| +
              |frameSlope| * |first.d - second.d|) := by
            gcongr
            simpa [abs_mul] using abs_add_le
              (first.c - second.c)
              (frameSlope * (first.d - second.d))
      _ ≤ width + 1 * width + 1 * (width + 1 * width) := by
            gcongr
      _ = 4 * width := by ring
  have hbNumerator :
      |(-frameSlope * first.a + first.b +
          anchor * (-frameSlope * first.c + first.d)) -
        (-frameSlope * second.a + second.b +
          anchor * (-frameSlope * second.c + second.d))| ≤
        4 * width := by
    rw [show
      (-frameSlope * first.a + first.b +
          anchor * (-frameSlope * first.c + first.d)) -
        (-frameSlope * second.a + second.b +
          anchor * (-frameSlope * second.c + second.d)) =
        (-frameSlope) * (first.a - second.a) +
          (first.b - second.b) +
          anchor * ((-frameSlope) * (first.c - second.c) +
            (first.d - second.d)) by ring]
    calc
      |(-frameSlope) * (first.a - second.a) +
          (first.b - second.b) +
          anchor * ((-frameSlope) * (first.c - second.c) +
            (first.d - second.d))|
          ≤ |(-frameSlope) * (first.a - second.a)| +
              |first.b - second.b| +
              |anchor * ((-frameSlope) * (first.c - second.c) +
                (first.d - second.d))| := by
            exact (abs_add_le _ _).trans <| by
              gcongr
              exact abs_add_le _ _
      _ = |frameSlope| * |first.a - second.a| +
            |first.b - second.b| +
            |anchor| * |(-frameSlope) * (first.c - second.c) +
              (first.d - second.d)| := by
            rw [abs_mul, abs_mul, abs_neg]
      _ ≤ |frameSlope| * |first.a - second.a| +
            |first.b - second.b| +
            |anchor| * (|frameSlope| * |first.c - second.c| +
              |first.d - second.d|) := by
            gcongr
            simpa [abs_mul, abs_neg] using abs_add_le
              ((-frameSlope) * (first.c - second.c))
              (first.d - second.d)
      _ ≤ 1 * width + width + 1 * (1 * width + width) := by
            gcongr
      _ = 4 * width := by ring
  have hcNumerator :
      |(first.c + frameSlope * first.d) -
        (second.c + frameSlope * second.d)| ≤ 2 * width := by
    rw [show
      (first.c + frameSlope * first.d) -
          (second.c + frameSlope * second.d) =
        (first.c - second.c) +
          frameSlope * (first.d - second.d) by ring]
    calc
      |(first.c - second.c) + frameSlope * (first.d - second.d)|
          ≤ |first.c - second.c| +
              |frameSlope * (first.d - second.d)| := abs_add_le _ _
      _ = |first.c - second.c| +
            |frameSlope| * |first.d - second.d| := by rw [abs_mul]
      _ ≤ width + 1 * width := by gcongr
      _ = 2 * width := by ring
  have hdNumerator :
      |(-frameSlope * first.c + first.d) -
        (-frameSlope * second.c + second.d)| ≤ 2 * width := by
    rw [show
      (-frameSlope * first.c + first.d) -
          (-frameSlope * second.c + second.d) =
        (-frameSlope) * (first.c - second.c) +
          (first.d - second.d) by ring]
    calc
      |(-frameSlope) * (first.c - second.c) +
          (first.d - second.d)|
          ≤ |(-frameSlope) * (first.c - second.c)| +
              |first.d - second.d| := abs_add_le _ _
      _ = |frameSlope| * |first.c - second.c| +
            |first.d - second.d| := by rw [abs_mul, abs_neg]
      _ ≤ 1 * width + width := by gcongr
      _ = 2 * width := by ring
  constructor
  · rw [show
      (first.a + frameSlope * first.b +
          anchor * (first.c + frameSlope * first.d)) /
            pureWZ2HorizontalNorm frameSlope -
        (second.a + frameSlope * second.b +
          anchor * (second.c + frameSlope * second.d)) /
            pureWZ2HorizontalNorm frameSlope =
        ((first.a + frameSlope * first.b +
          anchor * (first.c + frameSlope * first.d)) -
        (second.a + frameSlope * second.b +
          anchor * (second.c + frameSlope * second.d))) /
            pureWZ2HorizontalNorm frameSlope by ring,
        abs_div, abs_of_pos hnormPos]
    apply (div_le_iff₀ hnormPos).2
    exact haNumerator.trans (by nlinarith)
  constructor
  · rw [show
      transverseScale *
          (-frameSlope * first.a + first.b +
            anchor * (-frameSlope * first.c + first.d)) /
            pureWZ2HorizontalNorm frameSlope -
        transverseScale *
          (-frameSlope * second.a + second.b +
            anchor * (-frameSlope * second.c + second.d)) /
            pureWZ2HorizontalNorm frameSlope =
        transverseScale *
          ((-frameSlope * first.a + first.b +
            anchor * (-frameSlope * first.c + first.d)) -
           (-frameSlope * second.a + second.b +
            anchor * (-frameSlope * second.c + second.d))) /
            pureWZ2HorizontalNorm frameSlope by ring,
        abs_div, abs_mul, abs_of_nonneg htransverse,
        abs_of_pos hnormPos]
    apply (div_le_iff₀ hnormPos).2
    calc
      transverseScale *
          |(-frameSlope * first.a + first.b +
            anchor * (-frameSlope * first.c + first.d)) -
           (-frameSlope * second.a + second.b +
            anchor * (-frameSlope * second.c + second.d))|
          ≤ 1 * (4 * width) := by gcongr
      _ ≤ (4 * width) * pureWZ2HorizontalNorm frameSlope := by
        nlinarith
  constructor
  · rw [show
      (first.c + frameSlope * first.d) /
          (pureWZ2HorizontalNorm frameSlope * heightScale) -
        (second.c + frameSlope * second.d) /
          (pureWZ2HorizontalNorm frameSlope * heightScale) =
        ((first.c + frameSlope * first.d) -
          (second.c + frameSlope * second.d)) /
            (pureWZ2HorizontalNorm frameSlope * heightScale) by ring,
        abs_div, abs_of_pos hdenomPos]
    apply (div_le_iff₀ hdenomPos).2
    exact hcNumerator.trans (by nlinarith)
  · rw [show
      transverseScale * (-frameSlope * first.c + first.d) /
          (pureWZ2HorizontalNorm frameSlope * heightScale) -
        transverseScale * (-frameSlope * second.c + second.d) /
          (pureWZ2HorizontalNorm frameSlope * heightScale) =
        transverseScale *
          ((-frameSlope * first.c + first.d) -
            (-frameSlope * second.c + second.d)) /
          (pureWZ2HorizontalNorm frameSlope * heightScale) by ring,
        abs_div, abs_mul, abs_of_nonneg htransverse,
        abs_of_pos hdenomPos]
    apply (div_le_iff₀ hdenomPos).2
    calc
      transverseScale *
          |(-frameSlope * first.c + first.d) -
            (-frameSlope * second.c + second.d)|
          ≤ 1 * (2 * width) := by gcongr
      _ ≤ (4 * width) *
          (pureWZ2HorizontalNorm frameSlope * heightScale) := by
        nlinarith

/-- The fully centered map has the same pairwise parameter differences as the
anchor-only formula, hence the same forward box bound. -/
theorem pureWZ2_affineDiagonalCenteredTubeParams_sub_le
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale width : ℝ)
    (hframe : |frameSlope| ≤ 1)
    (hanchor : |center 2| ≤ 1)
    (hheight : 1 ≤ heightScale)
    (htransverse : 0 ≤ transverseScale)
    (htransverseOne : transverseScale ≤ 1)
    (hwidth : 0 ≤ width)
    (first second : TubeParams)
    (ha : |first.a - second.a| ≤ width)
    (hb : |first.b - second.b| ≤ width)
    (hc : |first.c - second.c| ≤ width)
    (hd : |first.d - second.d| ≤ width) :
    let firstTarget := pureWZ2AffineDiagonalCenteredTubeParams frameSlope
      center heightScale transverseScale first
    let secondTarget := pureWZ2AffineDiagonalCenteredTubeParams frameSlope
      center heightScale transverseScale second
    |firstTarget.a - secondTarget.a| ≤ 4 * width ∧
      |firstTarget.b - secondTarget.b| ≤ 4 * width ∧
      |firstTarget.c - secondTarget.c| ≤ 4 * width ∧
      |firstTarget.d - secondTarget.d| ≤ 4 * width := by
  dsimp only
  have hanchored := pureWZ2_affineDiagonalTubeParams_sub_le
    frameSlope (center 2) heightScale transverseScale width
    hframe hanchor hheight htransverse htransverseOne hwidth
    first second ha hb hc hd
  have hdiff := pureWZ2AffineDiagonalCenteredTubeParams_sub_eq
    frameSlope center heightScale transverseScale first second
  exact ⟨by rw [hdiff.1]; exact hanchored.1,
    by rw [hdiff.2.1]; exact hanchored.2.1,
    by rw [hdiff.2.2.1]; exact hanchored.2.2.1,
    by rw [hdiff.2.2.2]; exact hanchored.2.2.2⟩

/-- Two source tubes in one small ordinary parent remain close in the paper
line metric after the common fixed affine diagonal map.  Only the source
children and target representatives are required to lie in the vertical
chart; the common source parent itself may be arbitrary. -/
theorem pureWZ2_affineDiagonal_lineDistance_le_of_common_container
    {sourceDelta parentScale targetDelta : ℝ}
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hframe : |frameSlope| ≤ 1)
    (hanchor : |center 2| ≤ 1)
    (hheight : 1 ≤ heightScale)
    (htransverse : 0 < transverseScale)
    (htransverseOne : transverseScale ≤ 1)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceParent : sourceDelta ≤ parentScale)
    (hparentSmall : parentScale ≤ 1 / 10000)
    (first second : Kakeya.DeltaTube sourceDelta)
    (parent : Kakeya.DeltaTube parentScale)
    (hfirstLine : WZ1PaperTubeInLineClass first)
    (hsecondLine : WZ1PaperTubeInLineClass second)
    (hfirstBase : ‖first.base‖ ≤ 5)
    (hsecondBase : ‖second.base‖ ≤ 5)
    (hfirstContained : first.carrier ⊆ parent.carrier)
    (hsecondContained : second.carrier ⊆ parent.carrier)
    (firstTarget secondTarget : Kakeya.DeltaTube targetDelta)
    (hfirstTargetLine : WZ1PaperTubeInLineClass firstTarget)
    (hsecondTargetLine : WZ1PaperTubeInLineClass secondTarget)
    (hfirstVertical : first.direction (2 : Fin 3) ≠ 0)
    (hsecondVertical : second.direction (2 : Fin 3) ≠ 0)
    (hfirstTargetVertical : firstTarget.direction (2 : Fin 3) ≠ 0)
    (hsecondTargetVertical : secondTarget.direction (2 : Fin 3) ≠ 0)
    (hfirstAxis : tubeAxisLine firstTarget =
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale 1 '' tubeAxisLine first)
    (hsecondAxis : tubeAxisLine secondTarget =
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale 1 '' tubeAxisLine second) :
    wz1PaperLineDistance firstTarget secondTarget ≤
      2400000 * parentScale := by
  have hsourceCluster := common_container_target_tube_parameter_cluster_base_five
    sourceDelta parentScale hsourceDelta hsourceParent hparentSmall
    first second hfirstLine.vertical hsecondLine.vertical
    hfirstBase hsecondBase parent hfirstContained hsecondContained
  have hheightNe : heightScale ≠ 0 := by linarith
  have hparentNonneg : 0 ≤ parentScale :=
    hsourceDelta.le.trans hsourceParent
  have hfirstParams :=
    tubeParamsOfTube_eq_pureWZ2AffineDiagonalCentered_of_axis_image
      frameSlope center heightScale transverseScale hheightNe
      htransverse.ne' first hfirstVertical firstTarget
      hfirstTargetVertical hfirstAxis
  have hsecondParams :=
    tubeParamsOfTube_eq_pureWZ2AffineDiagonalCentered_of_axis_image
      frameSlope center heightScale transverseScale hheightNe
      htransverse.ne' second hsecondVertical secondTarget
      hsecondTargetVertical hsecondAxis
  have htargetCluster :=
    pureWZ2_affineDiagonalCenteredTubeParams_sub_le
      frameSlope center heightScale transverseScale
      (100000 * parentScale) hframe hanchor hheight
      htransverse.le htransverseOne (by positivity)
      (tubeParamsOfTube first) (tubeParamsOfTube second)
      hsourceCluster.1 hsourceCluster.2.1
      hsourceCluster.2.2.1 hsourceCluster.2.2.2
  have htargetCluster' :
      |(tubeParamsOfTube firstTarget).a -
          (tubeParamsOfTube secondTarget).a| ≤
            4 * (100000 * parentScale) ∧
        |(tubeParamsOfTube firstTarget).b -
          (tubeParamsOfTube secondTarget).b| ≤
            4 * (100000 * parentScale) ∧
        |(tubeParamsOfTube firstTarget).c -
          (tubeParamsOfTube secondTarget).c| ≤
            4 * (100000 * parentScale) ∧
        |(tubeParamsOfTube firstTarget).d -
          (tubeParamsOfTube secondTarget).d| ≤
            4 * (100000 * parentScale) := by
    rw [hfirstParams, hsecondParams]
    exact htargetCluster
  have hraw := wz1PaperLineDistance_le_of_tubeParams_close
    hfirstTargetLine hsecondTargetLine
    (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hparentNonneg))
    htargetCluster'.1 htargetCluster'.2.1
    htargetCluster'.2.2.1 htargetCluster'.2.2.2
  convert hraw using 1 <;> ring

/-- Two synchronized affine-diagonal target tubes lying over one complete
source strict fiber have target paper-line distance at most an absolute
multiple of the actual source parent scale. -/
theorem pureWZ2_affineDiagonal_lineDistance_le_of_same_source_fiber
    {sourceDelta sourceRho targetDelta : ℝ}
    {sourceConstant : ENNReal}
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hframe : |frameSlope| ≤ 1)
    (hanchor : |center 2| ≤ 1)
    (hheight : 1 ≤ heightScale)
    (htransverse : 0 < transverseScale)
    (htransverseOne : transverseScale ≤ 1)
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant)
    (hsourceDeltaRho : sourceDelta ≤ sourceRho)
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    (sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetLine : WZ1PaperIsLineClass targetFine)
    (htargetAxis : ∀ target,
      tubeAxisLine (targetFine.tube target) =
        pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale 1 ''
            tubeAxisLine (sourceFine.tube (sourceEquiv target)))
    (first second : Fin targetFine.card)
    (hsameParent :
      sourceScale.cover.parent (sourceEquiv first) =
        sourceScale.cover.parent (sourceEquiv second)) :
    wz1PaperLineDistance (targetFine.tube first) (targetFine.tube second) ≤
      2400000 * sourceRho := by
  by_cases hsourceRhoSmall : sourceRho ≤ 1 / 10000
  swap
  · have haxis :
        dist (wz1TubeAxisZeroPoint (targetFine.tube first))
            (wz1TubeAxisZeroPoint (targetFine.tube second)) < 1 := by
      simpa [dist_comm] using paper_axis_dist_lt_one htargetLine second first
    have hangle := InnerProductGeometry.angle_le_pi
      (wz1PaperDirection (targetFine.tube first))
      (wz1PaperDirection (targetFine.tube second))
    have hpi := Real.pi_lt_four
    dsimp only [wz1PaperLineDistance]
    have hrho : 1 / 10000 < sourceRho := lt_of_not_ge hsourceRhoSmall
    nlinarith
  let parent := sourceScale.coarse.tube
    (sourceScale.cover.parent (sourceEquiv first))
  have hfirstContained :
      (sourceFine.tube (sourceEquiv first)).carrier ⊆ parent.carrier := by
    exact (mem_wz2PaperOrdinaryFullFiberIndices_iff _ _).mp
      (sourceScale.cover.parent_mem_fullFiber (sourceEquiv first))
  have hsecondContained :
      (sourceFine.tube (sourceEquiv second)).carrier ⊆ parent.carrier := by
    have hmem := sourceScale.cover.parent_mem_fullFiber (sourceEquiv second)
    have hcontain :=
      (mem_wz2PaperOrdinaryFullFiberIndices_iff _ _).mp hmem
    dsimp only [parent]
    rw [hsameParent]
    exact hcontain
  apply pureWZ2_affineDiagonal_lineDistance_le_of_common_container
      frameSlope center heightScale transverseScale hframe hanchor hheight
      htransverse htransverseOne sourceScale.delta_pos hsourceDeltaRho
      hsourceRhoSmall (sourceFine.tube (sourceEquiv first))
      (sourceFine.tube (sourceEquiv second)) parent
      (hsourceLine _) (hsourceLine _) (hsourceBase _) (hsourceBase _)
      hfirstContained hsecondContained (targetFine.tube first)
      (targetFine.tube second) (htargetLine _) (htargetLine _)
  · intro hzero
    have hvertical := (hsourceLine (sourceEquiv first)).vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  · intro hzero
    have hvertical := (hsourceLine (sourceEquiv second)).vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  · intro hzero
    have hvertical := (htargetLine first).vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  · intro hzero
    have hvertical := (htargetLine second).vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  · exact htargetAxis first
  · exact htargetAxis second

end Kakeya.Assouad

end
