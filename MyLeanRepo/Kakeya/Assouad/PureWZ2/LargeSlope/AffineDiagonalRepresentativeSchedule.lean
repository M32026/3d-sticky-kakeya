import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalCleanupSourceReregularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalTubeParameterForward
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicParentQuotientSchedule

/-!
# Representative-parent schedule for the fixed affine-diagonal map

This is the map-specific bridge from the twice-regularized Section-6 source
family to the generic finite representative/quotient CWA machinery.
-/

noncomputable section

namespace Kakeya.Assouad

open PureWZ2ExternalWeightRegularizationData

/-- Absolute target parent radius attached to a source nearby scale. -/
def affineDiagonalRepresentativeParentScale
    (targetDelta sourceRho : ℝ) : ℝ :=
  3600000 * sourceRho + targetDelta

/-- Exact source-fiber line-distance budget for the affine-diagonal map. -/
def affineDiagonalRepresentativeLineBound (sourceRho : ℝ) : ℝ :=
  2400000 * sourceRho

/-- Radius of the public quotient parent after the maximal-net step. -/
def affineDiagonalQuotientCallerScale
    (targetDelta sourceRho : ℝ) : ℝ :=
  6000000 * sourceRho + 2 * targetDelta

/-- Multiplicative requested-scale loss of the affine-diagonal quotient. -/
def affineDiagonalQuotientScaleWindowConstant
    (sourceScheduleConstant : ENNReal) : ENNReal :=
  6000000 * sourceScheduleConstant + 2

theorem affineDiagonalQuotientCallerScale_pos
    {targetDelta sourceRho : ℝ}
    (htargetDelta : 0 < targetDelta) (hsourceRho : 0 < sourceRho) :
    0 < affineDiagonalQuotientCallerScale targetDelta sourceRho := by
  unfold affineDiagonalQuotientCallerScale
  positivity

theorem affineDiagonalQuotientCallerScale_containment
    {targetDelta sourceRho : ℝ}
    (htargetDelta : 0 < targetDelta) (hsourceRho : 0 < sourceRho) :
    (3 / 2 : ℝ) *
          (affineDiagonalRepresentativeLineBound sourceRho +
            affineDiagonalQuotientCallerScale targetDelta sourceRho / 4) +
        targetDelta ≤
      affineDiagonalQuotientCallerScale targetDelta sourceRho := by
  unfold affineDiagonalRepresentativeLineBound
    affineDiagonalQuotientCallerScale
  nlinarith

/-- The quotient caller radius dominates every requested scale represented
by the corresponding source witness. -/
theorem affineDiagonalQuotientCallerScale_request_le
    {targetDelta sourceRho request : ℝ}
    (htargetDelta : 0 < targetDelta)
    (hrequestPos : 0 < request)
    (htarget : targetDelta ≤ request)
    (hrequest : request ≤ sourceRho) :
    request ≤ affineDiagonalQuotientCallerScale targetDelta sourceRho := by
  unfold affineDiagonalQuotientCallerScale
  have hsourceRhoPos : 0 < sourceRho := lt_of_lt_of_le hrequestPos hrequest
  have hscaled : request ≤ 6000000 * sourceRho := by
    calc
      request ≤ sourceRho := hrequest
      _ ≤ 6000000 * sourceRho := by nlinarith
  nlinarith

/-- ENNReal scale-window estimate for the affine quotient caller. -/
theorem affineDiagonalQuotientCallerScale_within
    {targetDelta sourceRho request : ℝ}
    {sourceScheduleConstant : ENNReal}
    (hsourceRho : 0 < sourceRho)
    (htargetDelta : 0 < targetDelta)
    (htarget : targetDelta ≤ request)
    (hsource : ENNReal.ofReal sourceRho <
      sourceScheduleConstant * ENNReal.ofReal request) :
    ENNReal.ofReal
        (affineDiagonalQuotientCallerScale targetDelta sourceRho) <
      affineDiagonalQuotientScaleWindowConstant sourceScheduleConstant *
        ENNReal.ofReal request := by
  have hmul : (6000000 : ENNReal) * ENNReal.ofReal sourceRho <
      6000000 * (sourceScheduleConstant * ENNReal.ofReal request) := by
    have hright := (ENNReal.mul_lt_mul_iff_right
      (by norm_num : (6000000 : ENNReal) ≠ 0)
      (by norm_num : (6000000 : ENNReal) ≠ ⊤)).2 hsource
    simpa [mul_comm] using hright
  have htargetENN : ENNReal.ofReal targetDelta ≤ ENNReal.ofReal request :=
    ENNReal.ofReal_mono htarget
  have hadd : (6000000 : ENNReal) * ENNReal.ofReal sourceRho +
      2 * ENNReal.ofReal targetDelta <
    6000000 * (sourceScheduleConstant * ENNReal.ofReal request) +
      2 * ENNReal.ofReal request :=
    ENNReal.add_lt_add_of_lt_of_le
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      hmul (mul_le_mul_left' htargetENN 2)
  calc
    ENNReal.ofReal
        (affineDiagonalQuotientCallerScale targetDelta sourceRho) =
      (6000000 : ENNReal) * ENNReal.ofReal sourceRho +
        2 * ENNReal.ofReal targetDelta := by
      unfold affineDiagonalQuotientCallerScale
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ < 6000000 * (sourceScheduleConstant * ENNReal.ofReal request) +
          2 * ENNReal.ofReal request := hadd
    _ = affineDiagonalQuotientScaleWindowConstant sourceScheduleConstant *
        ENNReal.ofReal request := by
      unfold affineDiagonalQuotientScaleWindowConstant
      ring

/-- One source public scale produces one preliminary affine-diagonal target
parent cover on the synchronized source and target families. -/
noncomputable def affineDiagonalRepresentativeParentData
    {sigma epsilon delta sourceRho : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount)
    {sourceScaleConstant : ENNReal}
    (sourceScale : WZ2PaperPureScaleCoverData
      data.selected.family sourceRho sourceScaleConstant)
    (hsourceDeltaRho : delta ≤ sourceRho) :
    PureWZ2RepresentativeParentCoverData
      (targetRho := affineDiagonalRepresentativeParentScale
        affineScale.targetDelta sourceRho)
      (lineBound := affineDiagonalRepresentativeLineBound sourceRho)
      sourceScale (cleanupTargetSubfamily (cleanup := cleanup) data).family
      (Equiv.refl (Fin data.selected.family.card)) := by
  let targetFine := (cleanupTargetSubfamily (cleanup := cleanup) data).family
  have hsourceLine : WZ1PaperIsLineClass data.selected.family :=
    (band.lemma31.data.cfg.line_class.subfamily regularized.selected)
      |>.subfamily data.selected
  have hsourceBase : ∀ source,
      ‖(data.selected.family.tube source).base‖ ≤ 5 := by
    intro source
    rw [data.selected.tube_eq, regularized.selected.tube_eq]
    exact band.lemma31.data.cfg.bounded_base _ |>.trans (by norm_num)
  have htargetLine : WZ1PaperIsLineClass targetFine :=
    cleanupTarget_line_class (cleanup := cleanup) data
  refine
    { source_nonempty := data.selected_nonempty
      target_delta_pos := affineScale.targetDelta_pos
      target_rho_pos := ?_
      target_line_class := htargetLine
      target_ordinary_distinct := cleanupTarget_distinct
        (cleanup := cleanup) data
      target_midpoint_local := ?_
      target_packing_distinct := ?_
      target_carrier_subset_relabel := ?_
      common_source_parent_lineDistance := ?_
      containment_budget := ?_ }
  · unfold affineDiagonalRepresentativeParentScale
    exact add_pos (mul_pos (by norm_num) sourceScale.rho_pos)
      affineScale.targetDelta_pos
  · intro target
    change ‖wz2PaperTubeMidpoint
      (cleanup.finalFamily.tube
        (cleanupTargetEmbedding (cleanup := cleanup) data target))‖ ≤ 3
    exact cleanup.final_midpoint_le_three
      (cleanupTargetEmbedding (cleanup := cleanup) data target)
  · intro first second hne
    change (2 / 3 : ℝ) * affineScale.targetDelta <
      wz1PaperLineDistance
        (wz2PaperRelabelTube (targetFine.tube first))
        (wz2PaperRelabelTube (targetFine.tube second))
    rw [wz2PaperRelabelTube_lineDistance_both]
    have hdistinct := cleanupTarget_paper_essentially_distinct
      (cleanup := cleanup) data first second hne
    nlinarith [affineScale.targetDelta_pos]
  · intro rho hrho first second hbudget
    have hdistance :
        wz1PaperLineDistance (targetFine.tube first)
              (targetFine.tube second) + affineScale.targetDelta ≤ rho := by
      have hnonneg : 0 ≤ wz1PaperLineDistance
          (targetFine.tube first) (targetFine.tube second) := by
        unfold wz1PaperLineDistance
        exact add_nonneg dist_nonneg
          (InnerProductGeometry.angle_nonneg _ _)
      nlinarith
    have hcontain := pureWZ2_zeroBased_carrier_subset_relabel_of_lineDistance
      affineScale.targetDelta_pos hrho (targetFine.tube first)
      (targetFine.tube second) (htargetLine first) (htargetLine second)
      hdistance
    have hfixed : pureWZ2PaperZeroBasedTube (targetFine.tube first) =
        targetFine.tube first := by
      change pureWZ2PaperZeroBasedTube
          (cleanup.finalFamily.tube
            (cleanupTargetEmbedding (cleanup := cleanup) data first)) =
        cleanup.finalFamily.tube
          (cleanupTargetEmbedding (cleanup := cleanup) data first)
      exact cleanup.final_zeroBased
        (cleanupTargetEmbedding (cleanup := cleanup) data first)
    have hsecond : pureWZ2PaperZeroBasedTube (targetFine.tube second) =
        targetFine.tube second := by
      change pureWZ2PaperZeroBasedTube
          (cleanup.finalFamily.tube
            (cleanupTargetEmbedding (cleanup := cleanup) data second)) =
        cleanup.finalFamily.tube
          (cleanupTargetEmbedding (cleanup := cleanup) data second)
      exact cleanup.final_zeroBased
        (cleanupTargetEmbedding (cleanup := cleanup) data second)
    rwa [hfixed, hsecond] at hcontain
  · intro first second hparent
    change wz1PaperLineDistance
        (targetFine.tube first) (targetFine.tube second) ≤
      affineDiagonalRepresentativeLineBound sourceRho
    unfold affineDiagonalRepresentativeLineBound
    exact pureWZ2_affineDiagonal_lineDistance_le_of_same_source_fiber
      (sourceFine := data.selected.family) (targetFine := targetFine)
      affineScale.slopeData.frameSlope cleanup.raw.center
      affineScale.slopeData.heightScale affineScale.slopeData.transverseScale
      affineScale.slopeData.frameSlope_bound
      (by
        have hcenterHeight : cleanup.raw.center 2 =
            affineScale.slopeData.anchor := by
          rw [cleanup.raw.center_eq]
          simp [pureWZ2AffineDiagonalCommonCenter, point3]
        rw [hcenterHeight, abs_le]
        exact ⟨band.lemma31.data.scaleData.slabLeft_mem.trans
            (band.left_mem.trans <| subband.left_mem.trans
              affineScale.slope_anchor_mem.1),
          affineScale.slope_anchor_mem.2.trans <| subband.right_mem.trans <|
            band.right_mem.trans
            band.lemma31.data.scaleData.slabRight_mem⟩)
      ((show (1 : ℝ) ≤ 100 by norm_num).trans affineScale.height_lower)
      affineScale.transverse_pos
      (affineScale.transverse_le.trans (by norm_num))
      sourceScale hsourceDeltaRho
      (Equiv.refl _) hsourceLine hsourceBase htargetLine
      (cleanupTarget_axis_source (cleanup := cleanup) data)
      first second hparent
  · unfold affineDiagonalRepresentativeParentScale
      affineDiagonalRepresentativeLineBound
    linarith

/-- Package every finite source nearby-scale witness as a preliminary
representative-axis affine target cover. -/
noncomputable def affineDiagonalRepresentativeParentSchedule
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount)
    (sourceSchedule : PureWZ2FiniteNearbyScheduleData
      (family := data.selected.family) data.outputConstant
        sourceScheduleConstant parentLevelCount) :
    PureWZ2FiniteRepresentativeParentScheduleData
      (cleanupTargetSubfamily (cleanup := cleanup) data).family
      (Equiv.refl (Fin data.selected.family.card)) data.outputConstant
        sourceSchedule.scaleCount where
  sourceRho coordinate := (sourceSchedule.witness coordinate).rho
  targetRho coordinate := affineDiagonalRepresentativeParentScale
    affineScale.targetDelta (sourceSchedule.witness coordinate).rho
  lineBound coordinate := affineDiagonalRepresentativeLineBound
    (sourceSchedule.witness coordinate).rho
  sourceScale coordinate := (sourceSchedule.witness coordinate).scaleData
  parentData coordinate := affineDiagonalRepresentativeParentData data
    (sourceSchedule.witness coordinate).scaleData
      ((sourceSchedule.requested coordinate).2.1.trans
        (sourceSchedule.witness coordinate).requested_le)

/-- Build the generic quotient schedule for the affine-diagonal target. -/
noncomputable def affineDiagonalParentQuotientSchedule
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    (representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount)
    (hlineBound : ∀ coordinate,
      representativeSchedule.lineBound coordinate =
        affineDiagonalRepresentativeLineBound
          (representativeSchedule.sourceRho coordinate)) :
    PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule where
  callerRho coordinate := affineDiagonalQuotientCallerScale targetDelta
    (representativeSchedule.sourceRho coordinate)
  quotient coordinate := Classical.choice <|
    pureWZ2_anisotropic_parent_quotient
      (representativeSchedule.parentData coordinate)
      (affineDiagonalQuotientCallerScale_pos
        (representativeSchedule.parentData coordinate).target_delta_pos
        (representativeSchedule.sourceScale coordinate).rho_pos)
      (by
        rw [hlineBound coordinate]
        exact affineDiagonalQuotientCallerScale_containment
          (representativeSchedule.parentData coordinate).target_delta_pos
          (representativeSchedule.sourceScale coordinate).rho_pos)

end Kakeya.Assouad

end
