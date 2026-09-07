import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicCenteredMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.TubeParameterLineDistance
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CommonContainerTargetTubeParameterClusterBaseFive
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLinePackingCardinality

/-!
# Forward parameter control for the exact triangular map

Two source tubes lying in one arbitrary ordinary parent form a source
parameter cluster.  The exact triangular formulas send that cluster to a
target parameter cluster with only an absolute loss.  The common parent is
not required to lie in the vertical chart.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Pairwise parameter differences under the centered exact triangular map. -/
theorem anisotropicCenteredTubeParams_sub_le
    (g : SlopeFunction) (c d m : ℝ) (center : Point3) (width : ℝ)
    (hcd : c < d) (hdc : d - c ≤ 1)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
    (hmid : |c + (d - c) / 2| ≤ 1)
    (hwidth : 0 ≤ width)
    (first second : TubeParams)
    (ha : |first.a - second.a| ≤ width)
    (hb : |first.b - second.b| ≤ width)
    (hc : |first.c - second.c| ≤ width)
    (hd : |first.d - second.d| ≤ width) :
    let firstTarget := anisotropicCenteredTubeParams
      g c d m center first
    let secondTarget := anisotropicCenteredTubeParams
      g c d m center second
    |firstTarget.a - secondTarget.a| ≤ 4 * width ∧
      |firstTarget.b - secondTarget.b| ≤ 4 * width ∧
      |firstTarget.c - secondTarget.c| ≤ 4 * width ∧
      |firstTarget.d - secondTarget.d| ≤ 4 * width := by
  dsimp only
  have hlength : 0 < d - c := sub_pos.mpr hcd
  have hlengthNonneg : 0 ≤ d - c := hlength.le
  have hK : 0 ≤ m * (d - c) / 2 := by positivity
  have hKOne : m * (d - c) / 2 ≤ 1 := by nlinarith
  have hLHalf : 0 ≤ (d - c) / 2 := by positivity
  have hLHalfOne : (d - c) / 2 ≤ 1 := by linarith
  have hMLSq : 0 ≤ m * (d - c) ^ 2 / 4 := by positivity
  have hMLSqOne : m * (d - c) ^ 2 / 4 ≤ 1 := by
    nlinarith [sq_nonneg (d - c),
      mul_nonneg hm.le (sq_nonneg (d - c))]
  have hrawA :
      |(anisotropicTubeParams g c d m first).a -
          (anisotropicTubeParams g c d m second).a| ≤ 4 * width := by
    dsimp only [anisotropicTubeParams]
    have hdecomp :
        (first.a + g (c + (d - c) / 2) * first.b +
              (c + (d - c) / 2) *
                (first.c + g (c + (d - c) / 2) * first.d)) -
            (second.a + g (c + (d - c) / 2) * second.b +
              (c + (d - c) / 2) *
                (second.c + g (c + (d - c) / 2) * second.d)) =
          (first.a - second.a) +
            g (c + (d - c) / 2) * (first.b - second.b) +
            (c + (d - c) / 2) *
              ((first.c - second.c) +
                g (c + (d - c) / 2) * (first.d - second.d)) := by
      ring
    rw [hdecomp]
    calc
      |(first.a - second.a) +
          g (c + (d - c) / 2) * (first.b - second.b) +
          (c + (d - c) / 2) *
            ((first.c - second.c) +
              g (c + (d - c) / 2) * (first.d - second.d))| ≤
        |first.a - second.a| +
          |g (c + (d - c) / 2)| * |first.b - second.b| +
          |c + (d - c) / 2| *
            (|first.c - second.c| +
              |g (c + (d - c) / 2)| * |first.d - second.d|) := by
        calc
          |_ + _ + _| ≤ |(first.a - second.a) +
              g (c + (d - c) / 2) * (first.b - second.b)| +
              |(c + (d - c) / 2) *
                ((first.c - second.c) +
                  g (c + (d - c) / 2) * (first.d - second.d))| :=
            abs_add_le _ _
          _ ≤ (|first.a - second.a| +
                |g (c + (d - c) / 2) * (first.b - second.b)|) +
              |c + (d - c) / 2| *
                |(first.c - second.c) +
                  g (c + (d - c) / 2) * (first.d - second.d)| := by
            rw [abs_mul]
            gcongr
            exact abs_add_le _ _
          _ ≤ _ := by
            gcongr
            · rw [abs_mul]
            · simpa only [abs_mul] using
                (abs_add_le (first.c - second.c)
                  (g (c + (d - c) / 2) *
                    (first.d - second.d)))
      _ ≤ width + 1 * width + 1 * (width + 1 * width) := by gcongr
      _ = 4 * width := by ring
  have hrawB :
      |(anisotropicTubeParams g c d m first).b -
          (anisotropicTubeParams g c d m second).b| ≤ 4 * width := by
    dsimp only [anisotropicTubeParams]
    have heq :
        m * (d - c) / 2 * (first.b +
            (c + (d - c) / 2) * first.d) -
          m * (d - c) / 2 * (second.b +
            (c + (d - c) / 2) * second.d) =
        (m * (d - c) / 2) *
          ((first.b - second.b) +
            (c + (d - c) / 2) * (first.d - second.d)) := by ring
    rw [heq, abs_mul, abs_of_nonneg hK]
    calc
      (m * (d - c) / 2) *
          |(first.b - second.b) +
            (c + (d - c) / 2) * (first.d - second.d)| ≤
        1 * (|first.b - second.b| +
          |c + (d - c) / 2| * |first.d - second.d|) := by
            exact mul_le_mul hKOne
              (by simpa only [abs_mul] using
                (abs_add_le (first.b - second.b)
                  ((c + (d - c) / 2) * (first.d - second.d))))
              (abs_nonneg _) (by norm_num)
      _ ≤ 1 * (width + 1 * width) := by gcongr
      _ ≤ 4 * width := by nlinarith
  have hrawC :
      |(anisotropicTubeParams g c d m first).c -
          (anisotropicTubeParams g c d m second).c| ≤ 4 * width := by
    dsimp only [anisotropicTubeParams]
    have heq :
        (d - c) / 2 *
            (first.c + g (c + (d - c) / 2) * first.d) -
          (d - c) / 2 *
            (second.c + g (c + (d - c) / 2) * second.d) =
        ((d - c) / 2) *
          ((first.c - second.c) +
            g (c + (d - c) / 2) * (first.d - second.d)) := by ring
    rw [heq, abs_mul, abs_of_nonneg hLHalf]
    calc
      (d - c) / 2 *
          |(first.c - second.c) +
            g (c + (d - c) / 2) * (first.d - second.d)| ≤
        1 * (|first.c - second.c| +
          |g (c + (d - c) / 2)| * |first.d - second.d|) := by
            exact mul_le_mul hLHalfOne
              (by simpa only [abs_mul] using
                (abs_add_le (first.c - second.c)
                  (g (c + (d - c) / 2) * (first.d - second.d))))
              (abs_nonneg _) (by norm_num)
      _ ≤ 1 * (width + 1 * width) := by gcongr
      _ ≤ 4 * width := by nlinarith
  have hrawD :
      |(anisotropicTubeParams g c d m first).d -
          (anisotropicTubeParams g c d m second).d| ≤ 4 * width := by
    dsimp only [anisotropicTubeParams]
    have heq :
        m * (d - c) ^ 2 / 4 * first.d -
          m * (d - c) ^ 2 / 4 * second.d =
        (m * (d - c) ^ 2 / 4) * (first.d - second.d) := by ring
    rw [heq, abs_mul, abs_of_nonneg hMLSq]
    calc
      m * (d - c) ^ 2 / 4 * |first.d - second.d| ≤
          1 * width := by gcongr
      _ ≤ 4 * width := by nlinarith
  have hdiff := anisotropicCenteredTubeParams_sub_eq
    g c d m center first second
  exact ⟨by rw [hdiff.1]; exact hrawA,
    by rw [hdiff.2.1]; exact hrawB,
    by rw [hdiff.2.2.1]; exact hrawC,
    by rw [hdiff.2.2.2]; exact hrawD⟩

/-- Two exact triangular target tubes whose source tubes lie in a common
ordinary parent remain close in the paper line metric. -/
theorem anisotropic_recentered_lineDistance_le_of_common_container
    {sourceDelta parentScale targetDelta : ℝ}
    (g : SlopeFunction) (c d m : ℝ) (center : Point3)
    (hcd : c < d) (hdc : d - c ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
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
    (hfirstVertical : first.direction 2 ≠ 0)
    (hsecondVertical : second.direction 2 ≠ 0)
    (hfirstTargetVertical : firstTarget.direction 2 ≠ 0)
    (hsecondTargetVertical : secondTarget.direction 2 ≠ 0)
    (hfirstAxis : tubeAxisLine firstTarget =
      anisotropicCenteredRescalingMap g c d m center ''
        tubeAxisLine first)
    (hsecondAxis : tubeAxisLine secondTarget =
      anisotropicCenteredRescalingMap g c d m center ''
        tubeAxisLine second) :
    wz1PaperLineDistance firstTarget secondTarget ≤
      2400000 * parentScale := by
  have hsourceCluster := common_container_target_tube_parameter_cluster_base_five
    sourceDelta parentScale hsourceDelta hsourceParent hparentSmall
    first second hfirstLine.vertical hsecondLine.vertical
    hfirstBase hsecondBase parent hfirstContained hsecondContained
  have hmid : c + (d - c) / 2 ∈ Set.Icc (-1 : ℝ) 1 :=
    hsub ⟨by linarith, by linarith⟩
  have hmidAbs : |c + (d - c) / 2| ≤ 1 := abs_le.mpr hmid
  have hfirstParams := tubeParamsOfTube_eq_anisotropicCentered_of_axis_image
    g hcd center first hfirstVertical firstTarget hfirstTargetVertical hfirstAxis
  have hsecondParams := tubeParamsOfTube_eq_anisotropicCentered_of_axis_image
    g hcd center second hsecondVertical secondTarget hsecondTargetVertical
      hsecondAxis
  have hparentNonnegative : 0 ≤ parentScale :=
    hsourceDelta.le.trans hsourceParent
  have htargetCluster := anisotropicCenteredTubeParams_sub_le
    g c d m center (100000 * parentScale) hcd hdc hm hmOne
      hgmid hmidAbs (by positivity)
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
    (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hparentNonnegative))
    htargetCluster'.1 htargetCluster'.2.1
    htargetCluster'.2.2.1 htargetCluster'.2.2.2
  convert hraw using 1 <;> ring

/-- Two synchronized exact-triangular target tubes lying over one complete
source strict fiber have target paper-line distance at most an absolute
multiple of the actual source parent scale.  This is the one-scale bridge
used by the representative-axis parent construction. -/
theorem anisotropic_recentered_lineDistance_le_of_same_source_fiber
    {sourceDelta sourceRho targetDelta : ℝ}
    {sourceConstant : ENNReal}
    (g : SlopeFunction) (c d m : ℝ) (center : Point3)
    (hg : g.IsNormalized) (hcd : c < d) (hdc : d - c ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hm : 0 < m) (hmOne : m ≤ 1)
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
        anisotropicCenteredRescalingMap g c d m center ''
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
  let parent :=
    sourceScale.coarse.tube
      (sourceScale.cover.parent (sourceEquiv first))
  have hgmid : |g (c + (d - c) / 2)| ≤ 1 :=
    (hg _ (hsub ⟨by linarith, by linarith⟩)).1
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
  apply anisotropic_recentered_lineDistance_le_of_common_container
      g c d m center hcd hdc hsub hm hmOne hgmid
      sourceScale.delta_pos hsourceDeltaRho hsourceRhoSmall
      (sourceFine.tube (sourceEquiv first))
      (sourceFine.tube (sourceEquiv second)) parent
      (hsourceLine _) (hsourceLine _) (hsourceBase _) (hsourceBase _)
      hfirstContained hsecondContained
      (targetFine.tube first) (targetFine.tube second)
      (htargetLine _) (htargetLine _)
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
