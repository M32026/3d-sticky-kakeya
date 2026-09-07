import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64QuantitativeVerticalMatchedSourceCovers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64PaperConflictDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.TubeParameterLineDistance
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CommonContainerTargetTubeParameterClusterBaseFive
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLinePackingCardinality

/-!
# One-way carrier transport for quantitative Proposition 6.4

Only the forward direction is developed here.  Source line closeness is
transported through the exact Proposition 6.4 parameter map and the final
isotropic retubing; no doubled-fiber reflection is asserted.
-/

noncomputable section

namespace Kakeya.Assouad

/-- If an ordinary paper-line representative is already centred at height
zero, canonical centring changes at most its orientation and hence preserves
its ordinary carrier. -/
theorem pureWZ2PaperCenteredTube_carrier_eq_of_midpoint_height_zero
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube)
    (hmidpoint : wz2PaperTubeMidpoint tube (2 : Fin 3) = 0) :
    (pureWZ2PaperCenteredTube tube).carrier = tube.carrier := by
  by_cases hdirection : 0 ≤ tube.direction (2 : Fin 3)
  · rw [pureWZ2PaperCenteredTube_eq_self tube hline hdirection hmidpoint]
  · have hzero :
        wz1TubeAxisZeroPoint tube = wz2PaperTubeMidpoint tube := by
      apply wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
        hline.vertical
      · exact ⟨1 / 2, rfl⟩
      · exact hmidpoint
    have hpaperDirection :
        wz1PaperDirection tube = -tube.direction := by
      unfold wz1PaperDirection
      rw [if_neg hdirection]
    have hreverse :
        pureWZ2PaperCenteredTube tube = reverseTube tube := by
      rw [Kakeya.DeltaTube.mk.injEq]
      constructor
      · change
          wz1TubeAxisZeroPoint tube -
              (1 / 2 : ℝ) • wz1PaperDirection tube =
            tube.base + tube.direction
        rw [hzero, hpaperDirection]
        dsimp only [wz2PaperTubeMidpoint]
        module
      · exact hpaperDirection
    rw [hreverse, reverseTube_carrier]

/-- The combined exact-image/isotropic map is quantitatively Lipschitz on the
four vertical line parameters.  The deliberately loose factor `120` absorbs
the common-window shear and avoids using any inverse/reflection statement. -/
theorem pureWZ2Proposition64_combinedTubeParams_forward_cluster
    (anchorSlope slabCenter halfHeight normalization : ℝ)
    (translation center : Point3) (scale radius : ℝ)
    (hanchorSlope : |anchorSlope| ≤ 8)
    (hslabCenter : |slabCenter| ≤ 1)
    (hhalfHeight : 0 < halfHeight) (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 9 ≤ normalization)
    (hcenter : |center 2| ≤ 1)
    (hscale : 1 ≤ scale) (hradius : 0 ≤ radius)
    (first second : TubeParams)
    (ha : |first.a - second.a| ≤ radius)
    (hb : |first.b - second.b| ≤ radius)
    (hc : |first.c - second.c| ≤ 6 * radius)
    (hd : |first.d - second.d| ≤ 6 * radius) :
    let transform := fun params =>
      pureWZ2Proposition64IsotropicTubeParams center scale
        (pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
          halfHeight normalization translation params)
    |(transform first).a - (transform second).a| ≤ 120 * scale * radius ∧
      |(transform first).b - (transform second).b| ≤ 120 * scale * radius ∧
      |(transform first).c - (transform second).c| ≤ 120 * scale * radius ∧
      |(transform first).d - (transform second).d| ≤ 120 * scale * radius := by
  dsimp only
  have hnormalizationPos : 0 < normalization := by linarith
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  let exactFirst := pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
    halfHeight normalization translation first
  let exactSecond := pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
    halfHeight normalization translation second
  have exactA : |exactFirst.a - exactSecond.a| ≤ 63 * radius := by
    have hrewrite : exactFirst.a - exactSecond.a =
        (((first.a - second.a) + slabCenter * (first.c - second.c)) +
          anchorSlope *
            ((first.b - second.b) + slabCenter * (first.d - second.d))) /
          normalization := by
      simp [exactFirst, exactSecond, pureWZ2Proposition64ExactTubeParams]
      ring
    rw [hrewrite, abs_div, abs_of_pos hnormalizationPos]
    apply (div_le_iff₀ hnormalizationPos).2
    calc
      |(first.a - second.a) + slabCenter * (first.c - second.c) +
          anchorSlope *
            ((first.b - second.b) + slabCenter * (first.d - second.d))| ≤
          |first.a - second.a| +
            |slabCenter| * |first.c - second.c| +
            |anchorSlope| *
              (|first.b - second.b| +
                |slabCenter| * |first.d - second.d|) := by
          calc
            _ ≤ |(first.a - second.a) +
                    slabCenter * (first.c - second.c)| +
                  |anchorSlope *
                    ((first.b - second.b) +
                      slabCenter * (first.d - second.d))| := abs_add_le _ _
            _ ≤ (|first.a - second.a| +
                    |slabCenter * (first.c - second.c)|) +
                  |anchorSlope| *
                    (|first.b - second.b| +
                      |slabCenter * (first.d - second.d)|) := by
                rw [abs_mul]
                apply add_le_add
                · exact abs_add_le _ _
                · apply mul_le_mul_of_nonneg_left
                  · exact abs_add_le _ _
                  · exact abs_nonneg _
            _ = _ := by simp only [abs_mul]
      _ ≤ 63 * radius := by
        have hsc : |slabCenter| * |first.c - second.c| ≤ 6 * radius := by
          calc
            _ ≤ 1 * (6 * radius) := by gcongr
            _ = 6 * radius := one_mul _
        have hsd : |slabCenter| * |first.d - second.d| ≤ 6 * radius := by
          calc
            _ ≤ 1 * (6 * radius) := by gcongr
            _ = 6 * radius := one_mul _
        have hleft := add_le_add ha hsc
        have hinner := add_le_add hb hsd
        have hright :
            |anchorSlope| *
                (|first.b - second.b| +
                  |slabCenter| * |first.d - second.d|) ≤
              8 * (7 * radius) :=
          mul_le_mul hanchorSlope
            (hinner.trans_eq (by ring))
            (add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
            (by norm_num)
        nlinarith
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 63) hradius]
  have exactB : |exactFirst.b - exactSecond.b| ≤ 7 * radius := by
    have hrewrite : exactFirst.b - exactSecond.b =
        (first.b - second.b) + slabCenter * (first.d - second.d) := by
      simp [exactFirst, exactSecond, pureWZ2Proposition64ExactTubeParams]
      ring
    rw [hrewrite]
    calc
      _ ≤ |first.b - second.b| +
          |slabCenter| * |first.d - second.d| := by
        simpa [abs_mul] using
          (abs_add_le (first.b - second.b)
            (slabCenter * (first.d - second.d)))
      _ ≤ 7 * radius := by
        have hsd : |slabCenter| * |first.d - second.d| ≤ 6 * radius := by
          calc
            _ ≤ 1 * (6 * radius) := by gcongr
            _ = 6 * radius := one_mul _
        nlinarith
  have exactC : |exactFirst.c - exactSecond.c| ≤ 54 * radius := by
    have hrewrite : exactFirst.c - exactSecond.c =
        halfHeight *
          ((first.c - second.c) +
            anchorSlope * (first.d - second.d)) / normalization := by
      simp [exactFirst, exactSecond, pureWZ2Proposition64ExactTubeParams]
      ring
    rw [hrewrite, abs_div, abs_mul, abs_of_pos hhalfHeight,
      abs_of_pos hnormalizationPos]
    apply (div_le_iff₀ hnormalizationPos).2
    have hsum :
        |(first.c - second.c) +
            anchorSlope * (first.d - second.d)| ≤ 54 * radius := by
      calc
        _ ≤ |first.c - second.c| +
            |anchorSlope| * |first.d - second.d| := by
          simpa [abs_mul] using
            (abs_add_le (first.c - second.c)
              (anchorSlope * (first.d - second.d)))
        _ ≤ 6 * radius + 8 * (6 * radius) := by gcongr
        _ = 54 * radius := by ring
    calc
      halfHeight *
          |(first.c - second.c) +
            anchorSlope * (first.d - second.d)| ≤
          1 * (54 * radius) := by gcongr
      _ ≤ 54 * radius * normalization := by
        nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 54) hradius]
  have exactD : |exactFirst.d - exactSecond.d| ≤ 6 * radius := by
    have hrewrite : exactFirst.d - exactSecond.d =
        halfHeight * (first.d - second.d) := by
      simp [exactFirst, exactSecond, pureWZ2Proposition64ExactTubeParams]
      ring
    rw [hrewrite, abs_mul, abs_of_pos hhalfHeight]
    calc
      halfHeight * |first.d - second.d| ≤ 1 * (6 * radius) := by gcongr
      _ = 6 * radius := one_mul _
  let targetFirst := pureWZ2Proposition64IsotropicTubeParams
    center scale exactFirst
  let targetSecond := pureWZ2Proposition64IsotropicTubeParams
    center scale exactSecond
  have targetA : |targetFirst.a - targetSecond.a| ≤
      120 * scale * radius := by
    have hrewrite : targetFirst.a - targetSecond.a =
        scale * ((exactFirst.a - exactSecond.a) +
          center 2 * (exactFirst.c - exactSecond.c)) := by
      simp [targetFirst, targetSecond,
        pureWZ2Proposition64IsotropicTubeParams]
      ring
    rw [hrewrite, abs_mul, abs_of_pos hscalePos]
    calc
      scale *
          |(exactFirst.a - exactSecond.a) +
            center 2 * (exactFirst.c - exactSecond.c)| ≤
          scale * (|exactFirst.a - exactSecond.a| +
            |center 2| * |exactFirst.c - exactSecond.c|) := by
        gcongr
        simpa [abs_mul] using abs_add_le
          (exactFirst.a - exactSecond.a)
          (center 2 * (exactFirst.c - exactSecond.c))
      _ ≤ scale * (63 * radius + 1 * (54 * radius)) := by gcongr
      _ ≤ 120 * scale * radius := by
        nlinarith [mul_nonneg (le_trans (by norm_num) hscale) hradius]
  have targetB : |targetFirst.b - targetSecond.b| ≤
      120 * scale * radius := by
    have hrewrite : targetFirst.b - targetSecond.b =
        scale * ((exactFirst.b - exactSecond.b) +
          center 2 * (exactFirst.d - exactSecond.d)) := by
      simp [targetFirst, targetSecond,
        pureWZ2Proposition64IsotropicTubeParams]
      ring
    rw [hrewrite, abs_mul, abs_of_pos hscalePos]
    calc
      scale *
          |(exactFirst.b - exactSecond.b) +
            center 2 * (exactFirst.d - exactSecond.d)| ≤
          scale * (|exactFirst.b - exactSecond.b| +
            |center 2| * |exactFirst.d - exactSecond.d|) := by
        gcongr
        simpa [abs_mul] using abs_add_le
          (exactFirst.b - exactSecond.b)
          (center 2 * (exactFirst.d - exactSecond.d))
      _ ≤ scale * (7 * radius + 1 * (6 * radius)) := by gcongr
      _ ≤ 120 * scale * radius := by
        nlinarith [mul_nonneg (le_trans (by norm_num) hscale) hradius]
  have targetC : |targetFirst.c - targetSecond.c| ≤
      120 * scale * radius := by
    simpa [targetFirst, targetSecond,
      pureWZ2Proposition64IsotropicTubeParams] using
      exactC.trans (by
        nlinarith [mul_nonneg (le_trans (by norm_num) hscale) hradius])
  have targetD : |targetFirst.d - targetSecond.d| ≤
      120 * scale * radius := by
    simpa [targetFirst, targetSecond,
      pureWZ2Proposition64IsotropicTubeParams] using
      exactD.trans (by
        nlinarith [mul_nonneg (le_trans (by norm_num) hscale) hradius])
  exact ⟨targetA, targetB, targetC, targetD⟩

/-- Once the two target axes are identified with the combined transform,
source line distance controls target line distance in the forward direction. -/
theorem pureWZ2Proposition64_combined_lineDistance_le
    {firstSourceDelta secondSourceDelta firstTargetDelta secondTargetDelta : ℝ}
    (anchorSlope slabCenter halfHeight normalization : ℝ)
    (translation center : Point3) (scale radius : ℝ)
    (sourceFirst : Kakeya.DeltaTube firstSourceDelta)
    (sourceSecond : Kakeya.DeltaTube secondSourceDelta)
    (targetFirst : Kakeya.DeltaTube firstTargetDelta)
    (targetSecond : Kakeya.DeltaTube secondTargetDelta)
    (hsourceFirst : WZ1PaperTubeInLineClass sourceFirst)
    (hsourceSecond : WZ1PaperTubeInLineClass sourceSecond)
    (htargetFirst : WZ1PaperTubeInLineClass targetFirst)
    (htargetSecond : WZ1PaperTubeInLineClass targetSecond)
    (hanchorSlope : |anchorSlope| ≤ 8)
    (hslabCenter : |slabCenter| ≤ 1)
    (hhalfHeight : 0 < halfHeight) (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 9 ≤ normalization)
    (hcenter : |center 2| ≤ 1)
    (hscale : 1 ≤ scale)
    (hsourceDistance : wz1PaperLineDistance sourceFirst sourceSecond ≤ radius)
    (hfirstParams : tubeParamsOfTube targetFirst =
      pureWZ2Proposition64IsotropicTubeParams center scale
        (pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
          halfHeight normalization translation (tubeParamsOfTube sourceFirst)))
    (hsecondParams : tubeParamsOfTube targetSecond =
      pureWZ2Proposition64IsotropicTubeParams center scale
        (pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
          halfHeight normalization translation (tubeParamsOfTube sourceSecond))) :
    wz1PaperLineDistance targetFirst targetSecond ≤ 720 * scale * radius := by
  have hradius : 0 ≤ radius :=
    (add_nonneg dist_nonneg
      (InnerProductGeometry.angle_nonneg _ _)).trans hsourceDistance
  have sourceCluster :=
    pureWZ2_tubeParams_cluster_of_paperLineDistance sourceFirst sourceSecond
      hsourceFirst hsourceSecond hsourceDistance
  have targetCluster :=
    pureWZ2Proposition64_combinedTubeParams_forward_cluster
      anchorSlope slabCenter halfHeight normalization translation center
      scale radius hanchorSlope hslabCenter hhalfHeight hhalfHeightOne
      hnormalization hcenter hscale hradius
      (tubeParamsOfTube sourceFirst) (tubeParamsOfTube sourceSecond)
      sourceCluster.1 sourceCluster.2.1 sourceCluster.2.2.1 sourceCluster.2.2.2
  calc
    wz1PaperLineDistance targetFirst targetSecond ≤
        6 * (120 * scale * radius) := by
      apply wz1PaperLineDistance_le_of_tubeParams_close
        htargetFirst htargetSecond
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (le_trans (by norm_num) hscale)) hradius)
      all_goals rw [hfirstParams, hsecondParams]
      · exact targetCluster.1
      · exact targetCluster.2.1
      · exact targetCluster.2.2.1
      · exact targetCluster.2.2.2
    _ = 720 * scale * radius := by ring

/-- Derive the parameter identity used above directly from the composed
axis provenance.  This is the bridge from `finalSourceEmbedding` provenance:
it does not assume carrier covariance or a target cover. -/
theorem tubeParamsOfTube_eq_proposition64Combined_of_axis_image
    {sourceDelta targetDelta : ℝ} (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation center : Point3) (scale : ℝ)
    (htranslationHeight : translation 2 = 0)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (hscalePos : 0 < scale)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceVertical : sourceTube.direction 2 ≠ 0)
    (targetTube : Kakeya.DeltaTube targetDelta)
    (htargetVertical : targetTube.direction 2 ≠ 0)
    (hexactVertical :
      (pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight hnormalization
        sourceTube).direction 2 ≠ 0)
    (haxis : tubeAxisLine targetTube =
      pureWZ2Proposition64IsotropicMap center scale ''
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation '' tubeAxisLine sourceTube)) :
    tubeParamsOfTube targetTube =
      pureWZ2Proposition64IsotropicTubeParams center scale
        (pureWZ2Proposition64ExactTubeParams (g anchorHeight) slabCenter
          halfHeight normalization translation (tubeParamsOfTube sourceTube)) := by
  let exactTube :=
    pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
      halfHeight normalization translation hhalfHeight hnormalization sourceTube
  let finalTube :=
    pureWZ2Proposition64IsotropicRebasedPaperTube
      (targetDelta := targetDelta) center scale exactTube
  have hfinalVertical : finalTube.direction 2 ≠ 0 := by
    simpa [finalTube, pureWZ2Proposition64IsotropicRebasedPaperTube,
      pureWZ2Proposition64IsotropicPaperTube] using hexactVertical
  have hfinalAxis : tubeAxisLine finalTube =
      pureWZ2Proposition64IsotropicMap center scale ''
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation '' tubeAxisLine sourceTube) := by
    rw [pureWZ2Proposition64IsotropicRebasedPaperTube_axis center hscalePos]
    congr 1
    exact pureWZ2Proposition64ImageTube_axisLine targetDelta g slabCenter
      anchorHeight translation hhalfHeight hnormalization sourceTube
  calc
    tubeParamsOfTube targetTube = tubeParamsOfTube finalTube :=
      tubeParamsOfTube_eq_of_axis_eq finalTube targetTube hfinalVertical
        htargetVertical (haxis.trans hfinalAxis.symm)
    _ = pureWZ2Proposition64IsotropicTubeParams center scale
        (tubeParamsOfTube exactTube) :=
      tubeParamsOfTube_isotropicRebasedPaperTube center scale exactTube
        hexactVertical
    _ = pureWZ2Proposition64IsotropicTubeParams center scale
        (pureWZ2Proposition64ExactTubeParams (g anchorHeight) slabCenter
          halfHeight normalization translation (tubeParamsOfTube sourceTube)) := by
      congr 1
      exact tubeParamsOfTube_eq_proposition64Exact_of_axis_image g slabCenter
        anchorHeight halfHeight normalization translation htranslationHeight
        hhalfHeight sourceTube hsourceVertical exactTube hexactVertical
        (pureWZ2Proposition64ImageTube_axisLine targetDelta g slabCenter
          anchorHeight translation hhalfHeight hnormalization sourceTube)

/-- Honest transported parent radius.  The `432000` term is
`(3/2) * 720 * 400`: source carrier containment gives source line distance
`≤ 400 rho`, the combined map costs `720 * scale`, and centered retubing
costs the final factor `3/2`. -/
def pureWZ2Proposition64TransportedParentScale
    (targetDelta scale sourceRho : ℝ) : ℝ :=
  432000 * scale * sourceRho + targetDelta

/-- One-way carrier transport from a literal source Definition-2.12 parent
to the relabelled target representative.  This theorem uses no target cover
and asserts no reverse/doubled-fiber implication. -/
theorem pureWZ2Proposition64_combined_carrier_subset_relabel
    {sourceDelta sourceRho targetDelta : ℝ}
    (anchorSlope slabCenter halfHeight normalization : ℝ)
    (translation center : Point3) (scale : ℝ)
    (sourceFine : Kakeya.DeltaTube sourceDelta)
    (sourceParent : Kakeya.DeltaTube sourceRho)
    (targetFine targetRepresentative : Kakeya.DeltaTube targetDelta)
    (hsourceDelta : 0 < sourceDelta) (hsourceRho : 0 < sourceRho)
    (htargetDelta : 0 < targetDelta)
    (hsourceFineLine : WZ1PaperTubeInLineClass sourceFine)
    (hsourceParentLine : WZ1PaperTubeInLineClass sourceParent)
    (htargetFineLine : WZ1PaperTubeInLineClass targetFine)
    (htargetRepresentativeLine :
      WZ1PaperTubeInLineClass targetRepresentative)
    (hsourceCover : WZ2PaperTubeCarrierCovers sourceFine sourceParent)
    (hanchorSlope : |anchorSlope| ≤ 8)
    (hslabCenter : |slabCenter| ≤ 1)
    (hhalfHeight : 0 < halfHeight) (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 9 ≤ normalization)
    (hcenter : |center 2| ≤ 1)
    (hscale : 1 ≤ scale)
    (hfineParams : tubeParamsOfTube targetFine =
      pureWZ2Proposition64IsotropicTubeParams center scale
        (pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
          halfHeight normalization translation (tubeParamsOfTube sourceFine)))
    (hrepresentativeParams : tubeParamsOfTube targetRepresentative =
      pureWZ2Proposition64IsotropicTubeParams center scale
        (pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
          halfHeight normalization translation
            (tubeParamsOfTube sourceParent)))
    (hfineCentered : pureWZ2PaperCenteredTube targetFine = targetFine)
    (hrepresentativeCentered :
      pureWZ2PaperCenteredTube targetRepresentative = targetRepresentative) :
    targetFine.carrier ⊆
      (wz2PaperRelabelTube
        (targetScale := pureWZ2Proposition64TransportedParentScale
          targetDelta scale sourceRho)
        targetRepresentative).carrier := by
  have hsourceDistance :
      wz1PaperLineDistance sourceFine sourceParent ≤ 400 * sourceRho :=
    wz2_paper_carrier_containment_lineDistance_le
      hsourceDelta hsourceRho hsourceFineLine hsourceParentLine hsourceCover
  have htargetDistance :
      wz1PaperLineDistance targetFine targetRepresentative ≤
        720 * scale * (400 * sourceRho) :=
    pureWZ2Proposition64_combined_lineDistance_le
      anchorSlope slabCenter halfHeight normalization translation center
      scale (400 * sourceRho) sourceFine sourceParent targetFine
      targetRepresentative hsourceFineLine hsourceParentLine htargetFineLine
      htargetRepresentativeLine hanchorSlope hslabCenter hhalfHeight
      hhalfHeightOne hnormalization hcenter hscale hsourceDistance
      hfineParams hrepresentativeParams
  have hparentPos :
      0 < pureWZ2Proposition64TransportedParentScale
        targetDelta scale sourceRho := by
    unfold pureWZ2Proposition64TransportedParentScale
    positivity
  have hbudget :
      (3 / 2 : ℝ) *
          wz1PaperLineDistance targetFine targetRepresentative +
          targetDelta ≤
        pureWZ2Proposition64TransportedParentScale
          targetDelta scale sourceRho := by
    unfold pureWZ2Proposition64TransportedParentScale
    nlinarith
  have hcontain :=
    pureWZ2_centered_carrier_subset_relabel_of_lineDistance
      htargetDelta hparentPos targetFine targetRepresentative hbudget
  simpa only [hfineCentered, hrepresentativeCentered] using hcontain

/-- Transport scale when the target parent is built from an occupied fine
representative of a source Definition-2.12 fiber. -/
def pureWZ2Proposition64RepresentativeTransportScale
    (targetDelta scale sourceRho : ℝ) : ℝ :=
  648000000 * scale * sourceRho + targetDelta

theorem quantitativeVertical_sourceLineDistance_le_of_same_parent
    {sourceDelta sourceRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    (sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant)
    (hsourceDeltaRho : sourceDelta ≤ sourceRho)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (first second : Fin sourceFine.card)
    (hsameParent : sourceScale.cover.parent first =
      sourceScale.cover.parent second) :
    wz1PaperLineDistance (sourceFine.tube first) (sourceFine.tube second) ≤
      600000 * sourceRho := by
  by_cases hsourceRhoSmall : sourceRho ≤ 1 / 10000
  swap
  · have haxis :
        dist (wz1TubeAxisZeroPoint (sourceFine.tube first))
            (wz1TubeAxisZeroPoint (sourceFine.tube second)) < 1 := by
      simpa [dist_comm] using paper_axis_dist_lt_one hsourceLine second first
    have hangle := InnerProductGeometry.angle_le_pi
      (wz1PaperDirection (sourceFine.tube first))
      (wz1PaperDirection (sourceFine.tube second))
    have hpi := Real.pi_lt_four
    dsimp only [wz1PaperLineDistance]
    have hrho : 1 / 10000 < sourceRho := lt_of_not_ge hsourceRhoSmall
    nlinarith
  let parent := sourceScale.coarse.tube
    (sourceScale.cover.parent first)
  have hfirstContained :
      (sourceFine.tube first).carrier ⊆ parent.carrier := by
    exact (mem_wz2PaperOrdinaryFullFiberIndices_iff _ _).mp
      (sourceScale.cover.parent_mem_fullFiber first)
  have hsecondContained :
      (sourceFine.tube second).carrier ⊆ parent.carrier := by
    have hmem := sourceScale.cover.parent_mem_fullFiber second
    have hcontain :=
      (mem_wz2PaperOrdinaryFullFiberIndices_iff _ _).mp hmem
    dsimp only [parent]
    rw [hsameParent]
    exact hcontain
  have hcluster := common_container_target_tube_parameter_cluster_base_five
    sourceDelta sourceRho sourceScale.delta_pos hsourceDeltaRho
    hsourceRhoSmall
    (sourceFine.tube first) (sourceFine.tube second)
    (hsourceLine first).vertical (hsourceLine second).vertical
    (hsourceBase first) (hsourceBase second) parent
    hfirstContained hsecondContained
  have hrhoNonnegative : 0 ≤ sourceRho := sourceScale.rho_pos.le
  have hresult := wz1PaperLineDistance_le_of_tubeParams_close
    (hsourceLine first) (hsourceLine second)
    (mul_nonneg (by norm_num) hrhoNonnegative)
    hcluster.1 hcluster.2.1 hcluster.2.2.1 hcluster.2.2.2
  convert hresult using 1 <;> ring

/-- Exact line-distance loss for two final tubes whose source indices lie in
one Definition-2.12 source fibre. -/
theorem pureWZ2Proposition64_combined_lineDistance_le_representative
    {sourceDelta sourceRho targetDelta : ℝ}
    {C : ENNReal}
    (anchorSlope slabCenter halfHeight normalization : ℝ)
    (translation center : Point3) (scale : ℝ)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceScale : WZ2PaperPureScaleCoverData sourceFamily sourceRho C)
    (first second : Fin sourceFamily.card)
    (targetFirst targetSecond : Kakeya.DeltaTube targetDelta)
    (hsourceDeltaRho : sourceDelta ≤ sourceRho)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hsourceBase : ∀ source, ‖(sourceFamily.tube source).base‖ ≤ 5)
    (hsameParent :
      sourceScale.cover.parent first = sourceScale.cover.parent second)
    (htargetFirstLine : WZ1PaperTubeInLineClass targetFirst)
    (htargetSecondLine : WZ1PaperTubeInLineClass targetSecond)
    (hanchorSlope : |anchorSlope| ≤ 8)
    (hslabCenter : |slabCenter| ≤ 1)
    (hhalfHeight : 0 < halfHeight) (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 9 ≤ normalization)
    (hcenter : |center 2| ≤ 1)
    (hscale : 1 ≤ scale)
    (hfirstParams : tubeParamsOfTube targetFirst =
      pureWZ2Proposition64IsotropicTubeParams center scale
        (pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
          halfHeight normalization translation
            (tubeParamsOfTube (sourceFamily.tube first))))
    (hsecondParams : tubeParamsOfTube targetSecond =
      pureWZ2Proposition64IsotropicTubeParams center scale
        (pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
          halfHeight normalization translation
            (tubeParamsOfTube (sourceFamily.tube second)))) :
    wz1PaperLineDistance targetFirst targetSecond ≤
      432000000 * scale * sourceRho := by
  have hsourceDistance :
      wz1PaperLineDistance (sourceFamily.tube first)
          (sourceFamily.tube second) ≤ 600000 * sourceRho :=
    quantitativeVertical_sourceLineDistance_le_of_same_parent
      sourceScale hsourceDeltaRho hsourceLine hsourceBase first second hsameParent
  have htargetDistance :
      wz1PaperLineDistance targetFirst targetSecond ≤
        720 * scale * (600000 * sourceRho) :=
    pureWZ2Proposition64_combined_lineDistance_le
      anchorSlope slabCenter halfHeight normalization translation center
      scale (600000 * sourceRho) (sourceFamily.tube first)
      (sourceFamily.tube second) targetFirst targetSecond
      (hsourceLine first) (hsourceLine second) htargetFirstLine htargetSecondLine
      hanchorSlope hslabCenter hhalfHeight hhalfHeightOne hnormalization
      hcenter hscale hsourceDistance hfirstParams hsecondParams
  convert htargetDistance using 1 <;> ring

/-- The form used by the raw-parent construction: two exact source-packet
indices with the same restricted-cover parent are transported to target
tubes, and the first target carrier is covered by a relabel of the second.
The source coarse tube itself is never transformed, so no line-class
assumption on Definition-2.12 coarse parents is needed. -/
theorem pureWZ2Proposition64_combined_carrier_subset_representative
    {sourceDelta sourceRho targetDelta : ℝ}
    {C : ENNReal}
    (anchorSlope slabCenter halfHeight normalization : ℝ)
    (translation center : Point3) (scale : ℝ)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceScale : WZ2PaperPureScaleCoverData sourceFamily sourceRho C)
    (first second : Fin sourceFamily.card)
    (targetFirst targetSecond : Kakeya.DeltaTube targetDelta)
    (hsourceDeltaRho : sourceDelta ≤ sourceRho)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hsourceBase : ∀ source, ‖(sourceFamily.tube source).base‖ ≤ 5)
    (hsameParent :
      sourceScale.cover.parent first = sourceScale.cover.parent second)
    (htargetDelta : 0 < targetDelta)
    (htargetFirstLine : WZ1PaperTubeInLineClass targetFirst)
    (htargetSecondLine : WZ1PaperTubeInLineClass targetSecond)
    (hanchorSlope : |anchorSlope| ≤ 8)
    (hslabCenter : |slabCenter| ≤ 1)
    (hhalfHeight : 0 < halfHeight) (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 9 ≤ normalization)
    (hcenter : |center 2| ≤ 1)
    (hscale : 1 ≤ scale)
    (hfirstParams : tubeParamsOfTube targetFirst =
      pureWZ2Proposition64IsotropicTubeParams center scale
        (pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
          halfHeight normalization translation
            (tubeParamsOfTube (sourceFamily.tube first))))
    (hsecondParams : tubeParamsOfTube targetSecond =
      pureWZ2Proposition64IsotropicTubeParams center scale
        (pureWZ2Proposition64ExactTubeParams anchorSlope slabCenter
          halfHeight normalization translation
            (tubeParamsOfTube (sourceFamily.tube second))))
    (hfirstCentered : pureWZ2PaperCenteredTube targetFirst = targetFirst)
    (hsecondCentered : pureWZ2PaperCenteredTube targetSecond = targetSecond) :
    targetFirst.carrier ⊆
      (wz2PaperRelabelTube
        (targetScale := pureWZ2Proposition64RepresentativeTransportScale
          targetDelta scale sourceRho)
        targetSecond).carrier := by
  have htargetDistance :
      wz1PaperLineDistance targetFirst targetSecond ≤
        432000000 * scale * sourceRho :=
    pureWZ2Proposition64_combined_lineDistance_le_representative
      anchorSlope slabCenter halfHeight normalization translation center
      scale sourceFamily sourceScale first second targetFirst targetSecond
      hsourceDeltaRho hsourceLine hsourceBase hsameParent
      htargetFirstLine htargetSecondLine hanchorSlope hslabCenter hhalfHeight
      hhalfHeightOne hnormalization hcenter hscale hfirstParams hsecondParams
  have hsourceRhoPos : 0 < sourceRho := sourceScale.rho_pos
  have hparentPos :
      0 < pureWZ2Proposition64RepresentativeTransportScale
        targetDelta scale sourceRho := by
    unfold pureWZ2Proposition64RepresentativeTransportScale
    positivity
  have hbudget :
      (3 / 2 : ℝ) * wz1PaperLineDistance targetFirst targetSecond +
          targetDelta ≤
        pureWZ2Proposition64RepresentativeTransportScale
          targetDelta scale sourceRho := by
    unfold pureWZ2Proposition64RepresentativeTransportScale
    nlinarith
  have hcontain :=
    pureWZ2_centered_carrier_subset_relabel_of_lineDistance
      htargetDelta hparentPos targetFirst targetSecond hbudget
  simpa only [hfirstCentered, hsecondCentered] using hcontain

end Kakeya.Assouad

end
