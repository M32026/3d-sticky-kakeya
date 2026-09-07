import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.AffineScaleTransport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64CombinedAffineEquiv
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64GeometricTopLevelCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64QuantitativeVerticalOfReceipts

/-!
# Proposition 6.4: the same-`Phi` nearby-CWA boundary

The source of every scale witness in this file is the single quantitative
hierarchy configuration.  The final family is the canonical paper-ED
subfamily selected from the same geometric prefix.  The physical map is the
one combined translated-`Phi`/isotropic affine equivalence already used by
the final provenance theorem.

The theorems below close the currently available, assumption-free part of the
transport:

* every source scale cover is selected from
  `source.extremal.cwa_nearby_scales`;
* the final ED index has one injective source parent;
* the final axis and final shaded carrier use the same combined affine map.

There is deliberately no theorem claiming final nearby CWA here.  The
remaining gap is not a scalar inequality: the current paper-ED record only
retains an injective fine source map.  It does not retain, for each source
scale witness, a restricted source coarse family, a partitioning cover whose
full fibres are the selected source fibres, or an equivalence between those
fibres and the final fibres.  These are precisely the fields required to
construct `PureWZ2AffineScaleTransportData`; accepting that data (or a target
cover/degree receipt) as an argument would reintroduce the rejected
arbitrary-final-cover route.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

namespace PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

variable
    {sigma workLoss sourceDelta targetDelta₀ : ℝ}
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    (frostman : SelectedSourceFrostmanReceipt geometry)

/-- The exact combined affine map used by the canonical Proposition 6.4
output.  This is the translated `Phi` followed by the one fixed isotropic
cleanup; it is independent of the requested CWA scale. -/
noncomputable abbrev affineNearbyPhi : Point3 ≃ᵃ[ℝ] Point3 :=
  pureWZ2Proposition64CombinedAffineEquiv
    quantitativeOutput.normalized.prepared.restrictedRaw.slope
    quantitativeOutput.normalized.prepared.slab.center
    quantitativeOutput.normalized.prepared.slab.anchorHeight
    quantitativeOutput.normalized.prepared.slab.halfHeight
    quantitativeOutput.normalized.prepared.normalization
    geometry.common.translation geometry.cleanup.popular.center
    pureWZ2Proposition64Lemma35Scale
    quantitativeOutput.normalized.prepared.slab.halfHeight_pos
    quantitativeOutput.normalized.prepared.normalized.normalization_pos
    pureWZ2Proposition64Lemma35Scale_pos

/-- The source packet indexed by the final canonical paper-ED family.  Its
embedding is literally `finalSourceEmbedding`; no independent source parent
is selected. -/
noncomputable abbrev affineNearbySourcePacket :
    Kakeya.Streamlined.TubeSubfamily
      quantitativeOutput.normalized.source.family :=
  pureWZ2Proposition64SourcePacket
    quantitativeOutput.normalized.source.family
    (quantitativeVerticalPaperED
      quantitativeOutput geometry frostman).subfamily.family
    (geometry.finalSourceEmbedding
      (quantitativeVerticalPaperED quantitativeOutput geometry frostman))

/-- Choose the already-proved full final provenance for the canonical ED
family.  The choice contains no new geometry: `exists_finalProvenance`
deterministically composes the stored ED, cleanup, image, and source maps. -/
noncomputable abbrev affineNearbyFinalProvenance :
    PureWZ2Proposition64FinalProvenanceData
      (normalized := quantitativeOutput.normalized.prepared.normalized)
      (image := geometry.imageData.image)
      (exactCarrier_provenance := geometry.exactCarrier_provenance)
      (cleanup := geometry.cleanup)
      (quantitativeVerticalPaperED quantitativeOutput geometry frostman) :=
  Classical.choice
    (geometry.exists_finalProvenance
      (quantitativeVerticalPaperED quantitativeOutput geometry frostman))

/-- The every-scale source witness is the field of the same quantitative
hierarchy source, not a CWA assumption on the final family. -/
theorem affineNearby_source_cwa :
    WZ2PaperPureCWAAtNearbyScales
      quantitativeOutput.normalized.source.family
      (Kakeya.realRpowENN sourceDelta
        (-quantitativeOutput.normalized.inputLoss)) :=
  quantitativeOutput.normalized.source.extremal.cwa_nearby_scales

/-- Consequently every requested source scale selects its actual cover from
that one hierarchy witness. -/
theorem affineNearby_source_scale
    (requested : WZ2PaperRequestedScale sourceDelta) :
    Nonempty
      (WZ2PaperPureNearbyScaleCoverData
        quantitativeOutput.normalized.source.family requested
        (Kakeya.realRpowENN sourceDelta
          (-quantitativeOutput.normalized.inputLoss))) :=
  (affineNearby_source_cwa quantitativeOutput).2.2.2 requested

/-- The packet tube at a final index is definitionally the tube named by the
one final source embedding. -/
@[simp] theorem affineNearbySourcePacket_tube
    (index : Fin
      (quantitativeVerticalPaperED
        quantitativeOutput geometry frostman).subfamily.family.card) :
    (affineNearbySourcePacket
        quantitativeOutput geometry frostman).family.tube index =
      quantitativeOutput.normalized.source.family.tube
        (geometry.finalSourceEmbedding
          (quantitativeVerticalPaperED
            quantitativeOutput geometry frostman) index) :=
  rfl

/-- `finalSourceEmbedding` and the composed provenance record name the same
original source tube. -/
theorem finalSourceEmbedding_eq_affineNearbyFinalProvenance
    (index : Fin
      (quantitativeVerticalPaperED
        quantitativeOutput geometry frostman).subfamily.family.card) :
    geometry.finalSourceEmbedding
        (quantitativeVerticalPaperED
          quantitativeOutput geometry frostman) index =
      (affineNearbyFinalProvenance
        quantitativeOutput geometry frostman).sourceParent index := by
  rw [(affineNearbyFinalProvenance
    quantitativeOutput geometry frostman).sourceParent_eq]
  rfl

/-- Exact same-`Phi` axis provenance for the final canonical ED family,
expressed against the source packet indexed by that family. -/
theorem affineNearby_final_axis
    (index : Fin
      (quantitativeVerticalPaperED
        quantitativeOutput geometry frostman).subfamily.family.card) :
    tubeAxisLine
        ((quantitativeVerticalPaperED
          quantitativeOutput geometry frostman).subfamily.family.tube index) =
      affineNearbyPhi quantitativeOutput geometry ''
        tubeAxisLine
          ((affineNearbySourcePacket
            quantitativeOutput geometry frostman).family.tube index) := by
  let provenance :=
    affineNearbyFinalProvenance quantitativeOutput geometry frostman
  have hparent :
      geometry.finalSourceEmbedding
          (quantitativeVerticalPaperED
            quantitativeOutput geometry frostman) index =
        provenance.sourceParent index :=
    finalSourceEmbedding_eq_affineNearbyFinalProvenance
      quantitativeOutput geometry frostman index
  rw [affineNearbySourcePacket_tube, hparent, provenance.axis_provenance]
  ext point
  simp [affineNearbyPhi]

/-- The final shaded carrier has the same source parent and the same physical
map.  The `6 * finalDelta` thickening is exactly the stored rediscretization
loss; this statement intentionally concerns the shading, not the whole source
tube carrier required by `PureWZ2AffineScaleTransportData.fine_image_subset`.
-/
theorem affineNearby_final_carrier
    (index : Fin
      (quantitativeVerticalPaperED
        quantitativeOutput geometry frostman).subfamily.family.card) :
    (quantitativeVerticalPaperED
        quantitativeOutput geometry frostman).finalShading.carrier index ⊆
      Metric.cthickening
        (6 * pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        (affineNearbyPhi quantitativeOutput geometry ''
          quantitativeOutput.normalized.prepared.slab.shading.carrier
            (geometry.finalSourceEmbedding
              (quantitativeVerticalPaperED
                quantitativeOutput geometry frostman) index)) := by
  let provenance :=
    affineNearbyFinalProvenance quantitativeOutput geometry frostman
  have hparent :
      geometry.finalSourceEmbedding
          (quantitativeVerticalPaperED
            quantitativeOutput geometry frostman) index =
        provenance.sourceParent index :=
    finalSourceEmbedding_eq_affineNearbyFinalProvenance
      quantitativeOutput geometry frostman index
  intro point hpoint
  have hcarrier := provenance.carrier_provenance index hpoint
  rw [← hparent] at hcarrier
  have himage :
      affineNearbyPhi quantitativeOutput geometry ''
          quantitativeOutput.normalized.prepared.slab.shading.carrier
            (geometry.finalSourceEmbedding
              (quantitativeVerticalPaperED
                quantitativeOutput geometry frostman) index) =
        pureWZ2Proposition64IsotropicMap geometry.cleanup.popular.center
            pureWZ2Proposition64Lemma35Scale ''
          (pureWZ2Proposition64TranslatedMap
              quantitativeOutput.normalized.prepared.restrictedRaw.slope
              quantitativeOutput.normalized.prepared.slab.center
              quantitativeOutput.normalized.prepared.slab.anchorHeight
              quantitativeOutput.normalized.prepared.slab.halfHeight
              quantitativeOutput.normalized.prepared.normalization
              geometry.common.translation ''
            quantitativeOutput.normalized.prepared.slab.shading.carrier
              (geometry.finalSourceEmbedding
                (quantitativeVerticalPaperED
                  quantitativeOutput geometry frostman) index)) := by
    ext targetPoint
    simp only [Set.mem_image]
    constructor
    · rintro ⟨sourcePoint, hsourcePoint, rfl⟩
      refine
        ⟨pureWZ2Proposition64TranslatedMap
            quantitativeOutput.normalized.prepared.restrictedRaw.slope
            quantitativeOutput.normalized.prepared.slab.center
            quantitativeOutput.normalized.prepared.slab.anchorHeight
            quantitativeOutput.normalized.prepared.slab.halfHeight
            quantitativeOutput.normalized.prepared.normalization
            geometry.common.translation sourcePoint,
          ⟨sourcePoint, hsourcePoint, rfl⟩, ?_⟩
      simp [affineNearbyPhi]
    · rintro ⟨translatedPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
      refine ⟨sourcePoint, hsourcePoint, ?_⟩
      simp [affineNearbyPhi]
  rw [himage]
  exact hcarrier

/-!
## Exact remaining statement

The production continuation must prove, without an extra family-valued
argument, the following two-stage statement.

1. For every final requested scale, choose a `sourceRequested` and
   `sourceNearby := Classical.choice
   (affineNearby_source_scale quantitativeOutput sourceRequested)`.  Restrict
   `sourceNearby.scaleData` along `finalSourceEmbedding` to a
   `WZ2PaperPureScaleCoverData` on `affineNearbySourcePacket`, retaining:
   the source cover parent, partitioning containment, selected complete
   full-fibre indices, and the source `rescaledFiber` CWA.
2. From that restricted source scale construct
   `PureWZ2AffineScaleTransportData` with
   `affine = affineNearbyPhi`, `targetFine` equal to the canonical paper-ED
   family, `fineIndex = Equiv.refl _`, and a transported coarse family.  Its
   actual target radius must satisfy the two scalar window inequalities
   required by `nearbyCWA_of_affine_transports`.

The currently available source fields are exactly
`sourceNearby.scaleData.cover`,
`sourceNearby.scaleData.full_fiber_uniform`, and
`sourceNearby.scaleData.rescaledFiber`.  The final record supplies only
`finalSourceEmbedding`, `sourceParent`, `axis_provenance`, and
`carrier_provenance`.

These fields do not prove Stage 1: an arbitrary ED subfamily need not be a
union of complete source-cover fibres.  They also do not prove the
`fine_image_subset` field of Stage 2: `affineNearby_final_carrier` controls
the transported *restricted shading* up to `6 * finalDelta`, whereas
`PureWZ2AffineScaleTransportData.fine_image_subset` asks for the image of the
entire cropped source tube carrier inside the target tube carrier.  The
existing homothetic-envelope theorem is the appropriate geometry but has a
nontrivial factor.  Thus the missing production lemma must synchronize the
ED refinement with source fibres and use a factor-paying affine scale
transport; neither conclusion follows from the present provenance API alone.
-/

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end
