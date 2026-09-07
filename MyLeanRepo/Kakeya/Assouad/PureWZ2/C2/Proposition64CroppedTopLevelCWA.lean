import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.AffineTubeHomotheticEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64ActualJohnPacketCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureNearbyTopLevel
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationOrdinaryPaperCWABridge
import MyLeanRepo.Kakeya.Assouad.PropStickyConvexWolffSubfamilyTransfer
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.RoundingLemma

/-!
# Cropped top-level CWA transport for Proposition 6.4

This is the inexpensive top-level alternative to transporting each actual-
John packet.  First restrict the source paper CWA to the source packet named
by the target indices.  The combined Proposition-6.4 affine map sends every
cropped source carrier into one explicit homothety of the centered target
ordinary carrier.  The generic body-CWA envelope theorem then transports the
count, and the standard crop-box bridge returns to paper carriers.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- The source packet indexed by the final target family. -/
def pureWZ2Proposition64SourcePacket
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (targetFamily : Kakeya.Streamlined.TubeFamily targetDelta)
    (sourceIndex : Fin targetFamily.card ↪ Fin sourceFamily.card) :
    Kakeya.Streamlined.TubeSubfamily sourceFamily where
  family :=
    { card := targetFamily.card
      tube := fun index => sourceFamily.tube (sourceIndex index) }
  embedding := sourceIndex
  tube_eq _ := rfl

/-- Transport a weighted-cardinality restriction of source paper CWA through
the physical combined Proposition-6.4 map.  The conclusion is a paper CWA on
the centered target family, with every geometric and Jacobian loss explicit. -/
theorem pureWZ2Proposition64_croppedTopLevelCWA_of_combined_image
    {sourceDelta targetDelta halfHeight normalization scale factor : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFamily : Kakeya.Streamlined.TubeFamily targetDelta}
    (sourceIndex : Fin targetFamily.card ↪ Fin sourceFamily.card)
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    (translation isotropicCenter : Point3)
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 10)
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 1 ≤ normalization)
    (hscale : 0 < scale)
    (htranslationHeight : translation 2 = 0)
    (hslabCenter : |slabCenter| ≤ 1)
    (hisotropicCenter : |isotropicCenter 2| ≤ 1)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (htargetLine : WZ1PaperIsLineClass targetFamily)
    (htargetCentered : ∀ index,
      wz2PaperTubeMidpoint (targetFamily.tube index) =
        wz1TubeAxisZeroPoint (targetFamily.tube index))
    (haxis : ∀ index,
      tubeAxisLine (targetFamily.tube index) =
        pureWZ2Proposition64IsotropicMap isotropicCenter scale ''
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation ''
              tubeAxisLine (sourceFamily.tube (sourceIndex index))))
    (hfactorOne : 1 ≤ factor)
    (hfactorAxial : 12 * scale / halfHeight ≤ factor)
    (hfactorTransverse :
      180 * scale * sourceDelta ≤ factor * targetDelta)
    {sourceConstant weight retentionConstant : ENNReal}
    (hsourceCWA : WZ2PaperConvexWolffBound sourceFamily sourceConstant)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hcardinality :
      weight * sourceFamily.enncard ≤
        retentionConstant * targetFamily.enncard) :
    WZ2PaperConvexWolffBound targetFamily
      ((ENNReal.ofReal (normalization * halfHeight / scale ^ 3) *
          ENNReal.ofReal (27 * (2 * factor - 1) ^ 3)) *
        ((weight⁻¹ * retentionConstant) * sourceConstant)) := by
  let selected := pureWZ2Proposition64SourcePacket
    sourceFamily targetFamily sourceIndex
  have hselectedCWA : WZ2PaperConvexWolffBound selected.family
      ((weight⁻¹ * retentionConstant) * sourceConstant) := by
    apply hsourceCWA.subfamily_of_weighted_cardinality selected
      hweightZero hweightTop
    simpa [selected, pureWZ2Proposition64SourcePacket,
      Kakeya.Streamlined.TubeFamily.enncard] using hcardinality
  let equivalence := pureWZ2Proposition64CombinedAffineEquiv g slabCenter
    anchorHeight halfHeight normalization translation isotropicCenter scale
      hhalfHeight (lt_of_lt_of_le zero_lt_one hnormalization) hscale
  have hordinary : WZ2PaperBodyConvexWolffBound targetFamily.toBodyFamily
      ((ENNReal.ofReal (normalization * halfHeight / scale ^ 3) *
          ENNReal.ofReal (27 * (2 * factor - 1) ^ 3)) *
        ((weight⁻¹ * retentionConstant) * sourceConstant)) := by
    exact
      pureWZ2Proposition64_bodyCWA_of_affine_homothetic_envelope_of_compact_bound
        (source := wz1PaperBodyFamily selected.family)
        (target := targetFamily.toBodyFamily)
        (equivalence := equivalence)
        (indexEquiv := Equiv.refl (Fin targetFamily.card))
        (factor := factor) (boundingSet :=
          Kakeya.Streamlined.axisBox 2 2 2)
        (center := fun index =>
          wz2PaperTubeMidpoint (targetFamily.tube index))
        (inverseVolumeConstant :=
          ENNReal.ofReal (normalization * halfHeight / scale ^ 3))
        (factor_one := hfactorOne)
        (hboundingCompact := Kakeya.Streamlined.isCompact_axisBox
          2 2 2 (by norm_num) (by norm_num) (by norm_num))
        (hboundingConvex := Kakeya.Streamlined.convex_axisBox 2 2 2)
        (htargetBody := fun index =>
          wz2_paper_ordinary_tube_isConvexBody
            (targetFamily.tube index) htargetDelta)
        (htargetBound := by
          intro index point hpoint
          exact (pureWZ2Proposition64_centeredOrdinaryCarrier_subset_cropped
            htargetDelta htargetDeltaSmall (targetFamily.tube index)
            (htargetLine index) (htargetCentered index) hpoint).2)
        (center_mem := fun index =>
          wz2_paper_tubeMidpoint_mem_carrier
            (targetFamily.tube index) htargetDelta.le)
        (carrier_envelope := by
          intro index
          rintro point ⟨sourcePoint, hsourcePoint, rfl⟩
          have hcontained :=
            pureWZ2Proposition64_combined_paperCarrier_subset_homothety
              hsourceDelta htargetDelta g slabCenter anchorHeight translation
              isotropicCenter htranslationHeight hslabCenter hisotropicCenter
              hhalfHeight hhalfHeightOne hnormalization hanchorSlope hscale
              (sourceFamily.tube (sourceIndex index))
              (targetFamily.tube index) (hsourceLine (sourceIndex index))
              (htargetLine index) (htargetCentered index) (haxis index)
              hfactorOne hfactorAxial hfactorTransverse
          apply hcontained
          refine ⟨pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
              halfHeight normalization translation sourcePoint,
            ⟨sourcePoint, hsourcePoint, rfl⟩, ?_⟩
          simp [equivalence])
        (inverse_volume := by
          intro targetSet
          rw [pureWZ2Proposition64CombinedAffineEquiv_inverse_volume_eq])
        (sourceCWA := hselectedCWA)
  apply ordinary_topLevelCWA_to_paper_of_axisBox
    htargetDelta _ hordinary
  intro index point hpoint
  exact (pureWZ2Proposition64_centeredOrdinaryCarrier_subset_cropped
    htargetDelta htargetDeltaSmall (targetFamily.tube index)
    (htargetLine index) (htargetCentered index) hpoint).2

end Kakeya.Assouad

end
