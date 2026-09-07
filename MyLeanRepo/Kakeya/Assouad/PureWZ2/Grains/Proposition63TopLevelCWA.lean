import MyLeanRepo.Kakeya.Assouad.PropStickyPaperIndexedConvexWolffTransfer
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageCarrier
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingJacobian
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationCWATransport.Basic
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63NearbyCover
import MyLeanRepo.Kakeya.Assouad.PropStickyConvexWolffSubfamilyTransfer
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCardinalityRetention

/-!
# Top-level Convex--Wolff transport for Proposition 6.3

The literal unit rescaling is a single affine equivalence on a complete
metric fibre.  Pulling a convex test set back through this map costs at most
`100^3`: the exact inverse Jacobian is `100^3 * rho^2`, and `rho <= 1`.
The image of every source paper carrier lies in the corresponding literal
target paper carrier, so the generic indexed CWA transport applies without
any unit-ball support assumption.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- A complete literal unit rescaling transports cropped top-level CWA with
the fixed loss `100^3`.  No ordinary-carrier support hypothesis is used. -/
theorem wz2_paper_literal_unit_rescaled_top_level_cwa
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hratio : delta / rho ≤ 1 / 24)
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    {anchor : Kakeya.DeltaTube rho}
    (hanchorLine : WZ1PaperTubeInLineClass anchor)
    (hcovered : ∀ source,
      WZ1PaperTubeCovers (sourceFamily.tube source) anchor)
    (literal : WZ2PaperLiteralUnitRescaledFamilyData
      sourceFamily anchor hrho)
    {C : ENNReal}
    (hsourceCWA : WZ2PaperConvexWolffBound sourceFamily C) :
    WZ2PaperConvexWolffBound literal.targetFamily
      ((1000000 : ENNReal) * C) := by
  let indexEquiv :
      Fin literal.targetFamily.card ≃ Fin sourceFamily.card :=
    Equiv.ofBijective literal.sourceIndex literal.sourceIndex_bijective
  let rescaling := wz2PaperLiteralUnitRescalingAffineEquiv anchor hrho
  apply wz2_paper_indexed_convex_wolff_transfer
      (sourceFamily := sourceFamily)
      (targetFamily := literal.targetFamily)
      (C := C) (envelopeConstant := (1000000 : ENNReal))
      indexEquiv
  · intro targetConvexSet htargetConvex
    let sourceConvexSet : Set Point3 := rescaling.symm '' targetConvexSet
    refine ⟨sourceConvexSet, ?_, ?_, ?_⟩
    · exact Convex.affine_image rescaling.symm.toAffineMap htargetConvex
    · rw [show sourceConvexSet = rescaling.symm '' targetConvexSet by rfl,
        wz2PaperAffineEquiv_volume_image_eq]
      have hdet :
          |LinearMap.det
              (rescaling.symm.linear : Point3 →ₗ[ℝ] Point3)| =
            1000000 * rho ^ 2 := by
        have hlinear :
            rescaling.symm.linear = rescaling.linear.symm := rfl
        rw [hlinear, LinearEquiv.det_coe_symm, abs_inv]
        have hforward :=
          wz2PaperLiteralUnitRescalingAffineEquiv_abs_det anchor hrho
        change
          |LinearMap.det
              ((wz2PaperLiteralUnitRescalingAffineEquiv anchor hrho).linear :
                Point3 →ₗ[ℝ] Point3)| = _ at hforward
        rw [hforward]
        field_simp [hrho.ne']
        ring
      rw [hdet]
      have hrhoSq : rho ^ 2 ≤ 1 := by nlinarith
      have hfactor :
          ENNReal.ofReal (1000000 * rho ^ 2) ≤
            (1000000 : ENNReal) := by
        calc
          ENNReal.ofReal (1000000 * rho ^ 2) ≤
              ENNReal.ofReal (1000000 : ℝ) :=
            ENNReal.ofReal_mono (by nlinarith)
          _ = (1000000 : ENNReal) := by norm_num
      gcongr
    · intro target htargetCarrier
      let source := sourceFamily.tube (indexEquiv target)
      have hsourceIndex : literal.sourceIndex target = indexEquiv target := rfl
      have himage :
          wz2PaperLiteralUnitRescalingMap anchor hrho ''
              wz1PaperTubeCarrier source ⊆
            wz1PaperTubeCarrier (literal.targetFamily.tube target) := by
        have hsaturation :=
          wz2_paper_literal_image_carrier
            hdelta hrho hrhoOne hratio source anchor
            (literal.targetFamily.tube target)
            (hsourceLine (indexEquiv target)) hanchorLine
            (literal.target_line_class target)
            (hcovered (indexEquiv target))
            (by simpa [source, hsourceIndex] using literal.target_axis target)
            (wz1PaperTubeCarrier source) (Set.Subset.rfl)
        intro imagePoint himagePoint
        apply hsaturation
        exact ⟨imagePoint, himagePoint, rfl⟩
      intro point hpoint
      have htarget : rescaling point ∈ targetConvexSet := by
        apply htargetCarrier
        apply himage
        exact ⟨point, hpoint, by
          exact (wz2PaperLiteralUnitRescalingAffineEquiv_apply
            anchor hrho point).symm⟩
      refine ⟨rescaling point, htarget, ?_⟩
      exact rescaling.symm_apply_apply point
  · exact hsourceCWA

/-- Recentring unit segments along the same indexed axes does not alter the
cropped full-line carriers, so top-level CWA reindexes from the literal
family to the public family with no further loss. -/
theorem WZ2PaperAssouadToLiteralRescalingCertificate.public_top_level_cwa
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {normalization : WZ2PaperAssouadUnitRescalingData anchor}
    {literal : WZ2PaperLiteralUnitRescaledFamilyData
      sourceFamily anchor hrho}
    {jacobianConstant C : ENNReal}
    (certificate : WZ2PaperAssouadToLiteralRescalingCertificate
      hrho normalization literal jacobianConstant)
    (hliteral : WZ2PaperConvexWolffBound literal.targetFamily C) :
    WZ2PaperConvexWolffBound certificate.publicFamily C := by
  simpa only [one_mul] using
    (wz2_paper_indexed_convex_wolff_transfer
      (sourceFamily := literal.targetFamily)
      (targetFamily := certificate.publicFamily)
      (C := C) (envelopeConstant := 1)
      certificate.section6Index.symm) (by

    intro targetConvexSet htargetConvex
    refine ⟨targetConvexSet, htargetConvex, by simp, ?_⟩
    intro publicIndex hpublic
    have haxis :
        tubeAxisLine (certificate.publicFamily.tube publicIndex) =
          tubeAxisLine
            (literal.targetFamily.tube
              (certificate.section6Index.symm publicIndex)) := by
      calc
        tubeAxisLine (certificate.publicFamily.tube publicIndex) =
            tubeAxisLine
              (certificate.publicFamily.tube
                (certificate.section6Index
                  (certificate.section6Index.symm publicIndex))) := by
          rw [certificate.section6Index.apply_symm_apply]
        _ = tubeAxisLine
              (literal.targetFamily.tube
                (certificate.section6Index.symm publicIndex)) :=
          certificate.same_axis
            (certificate.section6Index.symm publicIndex)
    simpa only [wz1PaperTubeCarrier, haxis] using hpublic) hliteral

/-- Complete source-to-public cropped CWA transport used by Proposition 6.3.
The only loss is the fixed inverse Jacobian of the literal map. -/
theorem wz2_paper_literal_public_top_level_cwa
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hratio : delta / rho ≤ 1 / 24)
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    {anchor : Kakeya.DeltaTube rho}
    (hanchorLine : WZ1PaperTubeInLineClass anchor)
    (hcovered : ∀ source,
      WZ1PaperTubeCovers (sourceFamily.tube source) anchor)
    (literal : WZ2PaperLiteralUnitRescaledFamilyData
      sourceFamily anchor hrho)
    {normalization : WZ2PaperAssouadUnitRescalingData anchor}
    {jacobianConstant C : ENNReal}
    (certificate : WZ2PaperAssouadToLiteralRescalingCertificate
      hrho normalization literal jacobianConstant)
    (hsourceCWA : WZ2PaperConvexWolffBound sourceFamily C) :
    WZ2PaperConvexWolffBound certificate.publicFamily
      ((1000000 : ENNReal) * C) :=
  certificate.public_top_level_cwa <|
    wz2_paper_literal_unit_rescaled_top_level_cwa
      hdelta hrho hrhoOne hratio hsourceLine hanchorLine hcovered
      literal hsourceCWA

/-- A mass-retaining subfamily inherits the ambient cropped CWA with an
explicit weighted-cardinality loss.  This general lemma is useful whenever
the caller has a genuine ambient-to-selected mass comparison; Proposition
6.3's selected complete fibre does not obtain such a comparison merely from
its per-tube density lower bound. -/
theorem wz2_paper_metric_fiber_top_level_cwa
    {delta : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hline : WZ1PaperIsLineClass ambient)
    (sourceShading : WZ1PaperTubeShading ambient)
    (selected : Kakeya.Streamlined.TubeSubfamily ambient)
    (sourceDensity massLoss C : ENNReal)
    (hsourceDensity : sourceDensity * ambient.enncard *
        Kakeya.realRpowENN delta 2 ≤ sourceShading.mass)
    (hretained : sourceShading.mass ≤
      massLoss * (restrictPaperShading selected sourceShading).mass)
    (hsourceDensityZero : sourceDensity ≠ 0)
    (hsourceDensityTop : sourceDensity ≠ ⊤)
    (hsourceCWA : WZ2PaperConvexWolffBound ambient C) :
    WZ2PaperConvexWolffBound selected.family
      (((sourceDensity⁻¹ *
          (massLoss * (55296 * Kakeya.deltaTubeVolume 1))) * C)) := by
  have hcardinality :
      sourceDensity * ambient.enncard ≤
        (massLoss * (55296 * Kakeya.deltaTubeVolume 1)) *
          selected.family.enncard :=
    wz2PaperWeightedCardinality_retained_from_subfamily_mass
      hdelta hdeltaSmall hline sourceShading selected sourceDensity
      massLoss hsourceDensity hretained
  exact hsourceCWA.subfamily_of_weighted_cardinality selected
    hsourceDensityZero hsourceDensityTop hcardinality

namespace PureWZ2.Proposition63MetricFiberInputData

variable
    {delta rho sigma stickyLoss localLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PureWZ2.PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : PureWZ2.Proposition63InitialRebalancedData
      original initial hdelta}
    {hrho : 0 < rho}

/-- The mass-maximal metric fibre inherits the ambient cropped top-level CWA.
The loss is exactly the inverse selected density, the number of coarse
parents, and the fixed paper-carrier volume constant. -/
theorem fiber_top_level_cwa
    (input : PureWZ2.Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hsourceDensityZero : input.sourceDensity ≠ 0)
    (hsourceDensityTop : input.sourceDensity ≠ ⊤)
    {C : ENNReal}
    (hsourceCWA : WZ2PaperConvexWolffBound fine C) :
    WZ2PaperConvexWolffBound input.fiberFamily.family
      (((input.sourceDensity⁻¹ *
          (coarse.enncard * (55296 * Kakeya.deltaTubeVolume 1))) * C)) := by
  apply wz2_paper_metric_fiber_top_level_cwa
      hdelta hdeltaSmall cover.fine_line_class rebalanced.shading
      input.fiberFamily input.sourceDensity coarse.enncard C
      input.ambient_density
  · change rebalanced.shading.mass ≤ coarse.enncard *
      (PureWZ2.proposition63MetricSelectedFiber
        (coarse := coarse) rebalanced.shading input.parent).mass
    exact input.ambient_mass_retained
  · exact hsourceDensityZero
  · exact hsourceDensityTop
  · exact hsourceCWA

end PureWZ2.Proposition63MetricFiberInputData

/-- Cropped top-level CWA is invariant under a rigid affine isometry whenever
the chosen cropped-carrier convention commutes with that isometry. -/
theorem WZ2PaperConvexWolffBound.image_affineIsometry_of_carrier_eq
    (e : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hcarrier : ∀ index,
      wz1PaperTubeCarrier ((imageTubeFamily e family).tube index) =
        e '' wz1PaperTubeCarrier (family.tube index))
    (hsource : WZ2PaperConvexWolffBound family C) :
    WZ2PaperConvexWolffBound (imageTubeFamily e family) C := by
  simpa only [one_mul] using
    (wz2_paper_indexed_convex_wolff_transfer
      (sourceFamily := family)
      (targetFamily := imageTubeFamily e family)
      (C := C) (envelopeConstant := 1)
      (Equiv.refl (Fin family.card))) (by
        intro targetConvexSet htargetConvex
        refine ⟨e.symm '' targetConvexSet,
          Convex.affine_image
            (affineIsometryToEquiv e.symm).toAffineMap htargetConvex,
          ?_, ?_⟩
        · simpa only [one_mul] using
            (isometry_volume_image e.symm targetConvexSet).le
        · intro targetIndex htargetCarrier point hpoint
          have himage : e point ∈
              wz1PaperTubeCarrier
                ((imageTubeFamily e family).tube targetIndex) := by
            rw [hcarrier targetIndex]
            exact ⟨point, hpoint, rfl⟩
          have htarget : e point ∈ targetConvexSet :=
            htargetCarrier himage
          exact ⟨e point, htarget, e.symm_apply_apply point⟩) hsource

namespace PureWZ2.Proposition63ChartSelectionData

variable
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PureWZ2.PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : PureWZ2.Proposition63InitialRebalancedData
      original initial hdelta}
    {hrho : 0 < rho}
    {input : PureWZ2.Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    {data : PureWZ2.Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity}
    {hDelta : 0 < Delta} {hDeltaSmall : Delta ≤ 1 / 200}
    {hdeltaDelta : delta ≤ Delta ^ 2}
    {hdeltaRatio : delta / Delta ≤ 1 / 4}

/-- Top-level CWA on the chart-normalized family, conditional only on the
complete source fibre's already-paid top-level CWA. -/
theorem normalized_top_level_cwa
    (selection : PureWZ2.Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {outputLoss : ℝ}
    (rescaled : PureWZ2.Proposition63ChartRescaledData selection outputLoss)
    (hrhoOne : rho ≤ 1)
    (hratio : delta / rho ≤ 1 / 24)
    {C : ENNReal}
    (hsourceCWA : WZ2PaperConvexWolffBound input.fiberFamily.family C) :
    WZ2PaperConvexWolffBound (selection.normalizedFamily rescaled)
      ((1000000 : ENNReal) * C) := by
  have hsourceLine : WZ1PaperIsLineClass input.fiberFamily.family :=
    cover.fine_line_class.subfamily input.fiberFamily
  have hanchorLine : WZ1PaperTubeInLineClass (coarse.tube input.parent) :=
    cover.coarse_line_class input.parent
  have hcovered : ∀ source : Fin input.fiberFamily.family.card,
      WZ1PaperTubeCovers (input.fiberFamily.family.tube source)
        (coarse.tube input.parent) := by
    intro source
    rw [input.fiberFamily.tube_eq source]
    exact (mem_wz2PaperFullFiberIndices_iff input.parent
      (input.fiberFamily.embedding source)).mp
      (Finset.orderEmbOfFin_mem
        (wz2PaperFullFiberIndices fine coarse input.parent) rfl source)
  have hpublic : WZ2PaperConvexWolffBound
      input.frozenRescaled.rescalingCertificate.publicFamily
      ((1000000 : ENNReal) * C) :=
    wz2_paper_literal_public_top_level_cwa
      hdelta hrho hrhoOne hratio hsourceLine hanchorLine hcovered
      input.frozenRescaled.familyData
      input.frozenRescaled.rescalingCertificate hsourceCWA
  apply hpublic.image_affineIsometry_of_carrier_eq
      selection.chartLabel.chart.affineIsometry
  intro index
  exact (selection.chartLabel.chart.image_paperTubeCarrier
    (input.frozenRescaled.rescalingCertificate.publicFamily.tube index)).symm

/-- Complete Proposition 6.3 top-level CWA transport from the ambient sticky
fine family to the chart-normalized complete metric fibre.  The selected
parent is the mass-maximal parent stored in `input`, so the first restriction
is justified by its explicit global mass-retention certificate.  All finite
losses are exposed in `habsorb`; no CWA is inherited by an arbitrary
subfamily. -/
theorem normalized_top_level_cwa_of_ambient
    (selection : PureWZ2.Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {outputLoss : ℝ}
    (rescaled : PureWZ2.Proposition63ChartRescaledData selection outputLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrhoOne : rho ≤ 1)
    (hratio : delta / rho ≤ 1 / 24)
    (hsourceDensityZero : input.sourceDensity ≠ 0)
    (hsourceDensityTop : input.sourceDensity ≠ ⊤)
    {C : ENNReal}
    (hsourceCWA : WZ2PaperConvexWolffBound fine C)
    (habsorb :
      (1000000 : ENNReal) *
          ((input.sourceDensity⁻¹ *
              (coarse.enncard *
                (55296 * Kakeya.deltaTubeVolume 1))) * C) ≤
        Kakeya.realRpowENN (delta / rho) (-outputLoss)) :
    WZ2PaperConvexWolffBound (selection.normalizedFamily rescaled)
      (Kakeya.realRpowENN (delta / rho) (-outputLoss)) := by
  have hfiber : WZ2PaperConvexWolffBound input.fiberFamily.family
      ((input.sourceDensity⁻¹ *
          (coarse.enncard * (55296 * Kakeya.deltaTubeVolume 1))) * C) :=
    input.fiber_top_level_cwa hdeltaSmall hsourceDensityZero
      hsourceDensityTop hsourceCWA
  have hnormalized : WZ2PaperConvexWolffBound
      (selection.normalizedFamily rescaled)
      ((1000000 : ENNReal) *
        ((input.sourceDensity⁻¹ *
          (coarse.enncard * (55296 * Kakeya.deltaTubeVolume 1))) * C)) :=
    selection.normalized_top_level_cwa rescaled hrhoOne hratio hfiber
  exact weaken_convex_wolff_bound hnormalized habsorb

end PureWZ2.Proposition63ChartSelectionData

end Kakeya.Assouad

end
