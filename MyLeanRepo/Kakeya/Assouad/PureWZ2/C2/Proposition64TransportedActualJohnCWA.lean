import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64TransportedSelectedCovers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64ExactChildOwnerBlockCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64QuantitativeVerticalActualJohnPackets

/-!
# Actual-John fibre CWA for transported source-parent covers

The source cover, target cover, source indices, and physical affine map are
the literal objects produced along the one Proposition 6.4 witness.  The
owner blocks use the common selection's pair-degree bound and its
source-owner fanout-one theorem.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

namespace PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

variable
    {sigma workLoss sourceDelta targetDelta₀ outputLoss : ℝ}
    {Grid : Type*} [PureWZ2Proposition64TargetGrid Grid]
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    (frostman : SelectedSourceFrostmanReceipt geometry)
    (floor : Grid)

private noncomputable abbrev initialED :=
  quantitativeVerticalPaperED quantitativeOutput geometry frostman

private noncomputable abbrev schedule :=
  quantitativeVerticalRequestedScaleScheduleFor quantitativeOutput geometry floor

namespace QuantitativeVerticalTransportedSourceParentQuotientData

namespace QuantitativeVerticalTransportedCombinedSelectionData

noncomputable def sourceIndex
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data) :
    Fin selected.selected.family.card ↪
      Fin quantitativeOutput.normalized.source.family.card :=
  selected.selected.embedding.trans
    (geometry.finalSourceEmbedding
      (initialED quantitativeOutput geometry frostman))

theorem source_mem
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (source : Fin selected.selected.family.card) :
    selected.sourceIndex quantitativeOutput geometry frostman floor source ∈
      wz2PaperOrdinaryFullFiberIndices
        quantitativeOutput.normalized.source.family
        (quantitativeVerticalMatchedSourceNearby quantitativeOutput geometry
          floor coordinate).scaleData.coarse
        (selected.sourceOwner coordinate source) := by
  have hmem := (quantitativeVerticalMatchedSourceNearby quantitativeOutput geometry
    floor coordinate).scaleData.cover.parent_mem_fullFiber
      ((quantitativeVerticalExactSourcePacket quantitativeOutput geometry frostman
        ).embedding (selected.selected.embedding source))
  rw [selected.sourceOwner_eq coordinate source]
  change
    (quantitativeVerticalExactSourcePacket quantitativeOutput geometry frostman
      ).embedding (selected.selected.embedding source) ∈ _
  exact hmem

noncomputable def finalED
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data) :
    PureWZ2Proposition64PaperEDCleanupData geometry.cleanup.finalShading
      ((quantitativeVerticalPaperEDLoss quantitativeOutput geometry + 1) *
        selected.retentionConstant) :=
  (initialED quantitativeOutput geometry frostman).restrictFurther
    selected.selected.toTubeSubfamily selected.retained_mass

/-- Source-to-final cardinality loss with the canonical joint ED weight band
cancelled before the combined-selection retention is charged. -/
noncomputable def globalRetentionConstant
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data) : ENNReal :=
  2 *
    pureWZ2Proposition64TopRetention
      (sourceDelta := sourceDelta)
      (quantitativeVerticalPaperEDLoss quantitativeOutput geometry) *
    selected.retentionConstant

theorem global_cardinality_retention
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data) :
    pureWZ2Proposition64TopWeight
        (quantitativeOutput := quantitativeOutput) *
        quantitativeOutput.normalized.source.family.enncard ≤
      selected.globalRetentionConstant quantitativeOutput geometry frostman
          floor *
        selected.selected.family.enncard := by
  have hinitial := geometry.paperED_weighted_cardinality_retention
    (quantitativeOutput := quantitativeOutput)
    (initialED quantitativeOutput geometry frostman)
  have hselected :=
    selected.initial_cardinality_le_selected quantitativeOutput geometry
      frostman floor
  calc
    pureWZ2Proposition64TopWeight
          (quantitativeOutput := quantitativeOutput) *
        quantitativeOutput.normalized.source.family.enncard ≤
      pureWZ2Proposition64TopRetention
          (sourceDelta := sourceDelta)
          (quantitativeVerticalPaperEDLoss quantitativeOutput geometry) *
        (initialED quantitativeOutput geometry frostman).subfamily.family.enncard :=
      hinitial
    _ ≤ pureWZ2Proposition64TopRetention
          (sourceDelta := sourceDelta)
          (quantitativeVerticalPaperEDLoss quantitativeOutput geometry) *
        (2 * selected.retentionConstant *
          selected.selected.family.enncard) := by
      exact mul_le_mul_left' hselected _
    _ = selected.globalRetentionConstant quantitativeOutput geometry frostman
          floor *
        selected.selected.family.enncard := by
      unfold globalRetentionConstant
      ring

noncomputable def factor
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (_selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data)
    (_coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    ℝ :=
  max 1 (40 * pureWZ2Proposition64Lemma35Scale /
    quantitativeOutput.normalized.prepared.slab.halfHeight)

theorem factor_one
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    1 ≤ selected.factor quantitativeOutput geometry frostman floor coordinate :=
  le_max_left _ _

theorem factor_axial
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    40 * pureWZ2Proposition64Lemma35Scale /
        quantitativeOutput.normalized.prepared.slab.halfHeight ≤
      selected.factor quantitativeOutput geometry frostman floor coordinate :=
  le_max_right _ _

theorem factor_le_one_add_axial
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    selected.factor quantitativeOutput geometry frostman floor coordinate ≤
      1 + 40 * pureWZ2Proposition64Lemma35Scale /
        quantitativeOutput.normalized.prepared.slab.halfHeight := by
  unfold factor
  apply max_le
  · exact le_add_of_nonneg_right <|
      div_nonneg
        (mul_nonneg (by norm_num) pureWZ2Proposition64Lemma35Scale_pos.le)
        quantitativeOutput.normalized.prepared.slab.halfHeight_pos.le
  · exact le_add_of_nonneg_left (by norm_num)

theorem factor_transverse
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    20 * pureWZ2Proposition64Lemma35Scale * sourceDelta ≤
      selected.factor quantitativeOutput geometry frostman floor coordinate *
        pureWZ2Proposition64Lemma35FinalDelta sourceDelta := by
  have hscale := pureWZ2Proposition64Lemma35Scale_pos
  have hsource := quantitativeOutput.normalized.source.extremal.delta_pos
  have hbase :
      20 * pureWZ2Proposition64Lemma35Scale * sourceDelta ≤
        pureWZ2Proposition64Lemma35FinalDelta sourceDelta := by
    unfold pureWZ2Proposition64Lemma35FinalDelta
    nlinarith [mul_pos hscale hsource]
  exact hbase.trans <| by
    calc
      pureWZ2Proposition64Lemma35FinalDelta sourceDelta =
          1 * pureWZ2Proposition64Lemma35FinalDelta sourceDelta := by ring
      _ ≤ selected.factor quantitativeOutput geometry frostman floor coordinate *
          pureWZ2Proposition64Lemma35FinalDelta sourceDelta := by
        exact mul_le_mul_of_nonneg_right
          (selected.factor_one quantitativeOutput geometry frostman floor
            coordinate) geometry.scales.finalDelta_pos.le

noncomputable def inverseVolumeConstant
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (_selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    ENNReal :=
  432 * Kakeya.realRpowENN
      (quantitativeVerticalTransportedQuotientScale quantitativeOutput geometry
        floor coordinate) 2 *
    ENNReal.ofReal (1 + 2 *
      quantitativeVerticalTransportedQuotientScale quantitativeOutput geometry
        floor coordinate) *
    ENNReal.ofReal
      (quantitativeOutput.normalized.prepared.normalization *
        quantitativeOutput.normalized.prepared.slab.halfHeight /
        (pureWZ2Proposition64Lemma35Scale ^ 3 *
          (quantitativeVerticalMatchedSourceNearby quantitativeOutput geometry
            floor coordinate).rho ^ 2))

noncomputable def rawActualJohnConstant
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    ENNReal :=
  (selected.inverseVolumeConstant quantitativeOutput geometry frostman floor
      coordinate *
      ENNReal.ofReal
        (27 * (2 * selected.factor quantitativeOutput geometry frostman floor
          coordinate - 1) ^ 3)) *
    (((pureWZ2Proposition64TopWeight
        (quantitativeOutput := quantitativeOutput))⁻¹ *
      (Kakeya.realRpowENN sourceDelta
          (-quantitativeOutput.normalized.inputLoss) *
        selected.globalRetentionConstant quantitativeOutput geometry frostman
          floor * 1 * selected.degreeConstant)) *
      Kakeya.realRpowENN sourceDelta
        (-quantitativeOutput.normalized.inputLoss))

noncomputable def scaleConstant
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    ENNReal := max selected.degreeConstant
      (selected.rawActualJohnConstant quantitativeOutput geometry frostman floor
        coordinate)

theorem rawActualJohnFiberCWA
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data)
    (sourceBoundedBase :
      HasBoundedBase quantitativeOutput.normalized.source.family 4)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (targetParent : Fin (selected.targetParents coordinate).family.card) :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := selected.selected.family)
        (coarse := (selected.targetParents coordinate).family) targetParent
        (WZ2PaperAssouadUnitRescalingData.ofTube
          ((selected.targetParents coordinate).family.tube targetParent)
          (data.quotientScale_pos quantitativeOutput geometry frostman floor
            coordinate)))
      (selected.rawActualJohnConstant quantitativeOutput geometry frostman floor
        coordinate) := by
  let sourceScale :=
    (quantitativeVerticalMatchedSourceNearby quantitativeOutput geometry floor
      coordinate).scaleData
  let targetJohn := WZ2PaperAssouadUnitRescalingData.ofTube
    ((selected.targetParents coordinate).family.tube targetParent)
    (data.quotientScale_pos quantitativeOutput geometry frostman floor coordinate)
  have htargetLine : WZ1PaperIsLineClass selected.selected.family :=
    geometry.paperED_lineClass
      (selected.finalED quantitativeOutput geometry frostman floor)
  have htargetCentered : ∀ index,
      wz2PaperTubeMidpoint (selected.selected.family.tube index) =
        wz1TubeAxisZeroPoint (selected.selected.family.tube index) := by
    intro index
    have hvertical := (htargetLine index).vertical
    rw [selected.selected.tube_eq index] at hvertical ⊢
    rw [(initialED quantitativeOutput geometry frostman).tube_provenance
      (selected.selected.embedding index)] at hvertical ⊢
    apply pureWZ2Proposition64IsotropicRebasedPaperTube_midpoint
    simpa [pureWZ2Proposition64IsotropicPaperFamily,
      pureWZ2Proposition64IsotropicRebasedPaperTube,
      pureWZ2Proposition64IsotropicPaperTube] using hvertical
  have haxis : ∀ index,
      tubeAxisLine (selected.selected.family.tube index) =
        pureWZ2Proposition64IsotropicMap geometry.cleanup.popular.center
            pureWZ2Proposition64Lemma35Scale ''
          (pureWZ2Proposition64TranslatedMap
              quantitativeOutput.normalized.prepared.restrictedRaw.slope
              quantitativeOutput.normalized.prepared.slab.center
              quantitativeOutput.normalized.prepared.slab.anchorHeight
              quantitativeOutput.normalized.prepared.slab.halfHeight
              quantitativeOutput.normalized.prepared.normalization
              geometry.common.translation ''
            tubeAxisLine
              (quantitativeOutput.normalized.source.family.tube
                (selected.sourceIndex quantitativeOutput geometry frostman
                  floor index))) := by
    intro index
    have hraw := affineNearby_final_axis quantitativeOutput geometry frostman
      (selected.selected.embedding index)
    rw [selected.selected.tube_eq index]
    calc
      tubeAxisLine
          ((initialED quantitativeOutput geometry frostman).subfamily.family.tube
            (selected.selected.embedding index)) =
        affineNearbyPhi quantitativeOutput geometry ''
          tubeAxisLine
            ((affineNearbySourcePacket quantitativeOutput geometry frostman
              ).family.tube (selected.selected.embedding index)) := hraw
      _ = _ := by
        rw [affineNearbySourcePacket_tube]
        ext point
        simp [affineNearbyPhi, sourceIndex]
  have hslabCenter :
      |quantitativeOutput.normalized.prepared.slab.center| ≤ 1 := by
    have hcenter :=
      quantitativeOutput.normalized.prepared.slab.source_window 0 (by norm_num)
    rw [mul_zero, add_zero] at hcenter
    exact abs_le.mpr hcenter
  apply pureWZ2Proposition64_actualJohnFiber_cwa_of_exactChildOwnerBlocks
    sourceScale
    (by
      have hsource : 0 < quantitativeOutput.normalized.source.family.card :=
        quantitativeOutput.normalized.source.extremal.nonempty
      have hcover := sourceScale.cover.covers (⟨0, hsource⟩)
      rcases hcover with ⟨parent, _⟩
      exact Fin.pos_iff_nonempty.mpr ⟨parent⟩)
    (selected.targetCover coordinate)
    (selected.sourceIndex quantitativeOutput geometry frostman floor)
    (selected.sourceIndex quantitativeOutput geometry frostman floor).injective
    (selected.sourceOwner coordinate) targetParent
    (fun index => selected.source_mem quantitativeOutput geometry frostman floor
      coordinate _)
    (pureWZ2Proposition64TopWeight_ne_zero
      (quantitativeOutput := quantitativeOutput))
    (pureWZ2Proposition64TopWeight_ne_top
      (quantitativeOutput := quantitativeOutput))
    (selected.global_cardinality_retention quantitativeOutput geometry frostman
      floor)
    (selected.pair_degree_uniform coordinate)
    (selected.localFanout coordinate) targetJohn
    quantitativeOutput.normalized.prepared.restrictedRaw.slope
    quantitativeOutput.normalized.prepared.slab.center
    quantitativeOutput.normalized.prepared.slab.anchorHeight
    geometry.common.translation geometry.cleanup.popular.center
    quantitativeOutput.normalized.source.extremal.delta_pos
    quantitativeOutput.normalized.source.extremal.delta_le_one
    geometry.scales.finalDelta_pos
    (data.quotientScale_pos quantitativeOutput geometry frostman floor
      coordinate).le
    quantitativeOutput.normalized.prepared.slab.halfHeight_pos
    quantitativeOutput.normalized.prepared.slab.halfHeight_le_one
    quantitativeOutput.normalized.prepared.normalization_one
    pureWZ2Proposition64Lemma35Scale_pos
    geometry.common.translation_height hslabCenter
    (geometry.cleanup.popular.center_mem 2)
    quantitativeOutput.normalized.prepared.normalized.anchor_value_bound
    sourceBoundedBase
    quantitativeOutput.normalized.source.line_class
    htargetLine htargetCentered haxis
    (selected.factor_one quantitativeOutput geometry frostman floor coordinate)
    (selected.factor_axial quantitativeOutput geometry frostman floor coordinate)
    (selected.factor_transverse quantitativeOutput geometry frostman floor
      coordinate)
    (fun owner => pureWZ2Proposition64ActualJohnCoordinateChange_inverse_det_le
      sourceScale.rho_pos
      (data.quotientScale_pos quantitativeOutput geometry frostman floor
        coordinate)
      (sourceScale.coarse.tube owner)
      ((selected.targetParents coordinate).family.tube targetParent)
      (Classical.choice (sourceScale.rescaledFiber owner)).normalization
      targetJohn
      quantitativeOutput.normalized.prepared.restrictedRaw.slope
      quantitativeOutput.normalized.prepared.slab.center
      quantitativeOutput.normalized.prepared.slab.anchorHeight
      quantitativeOutput.normalized.prepared.slab.halfHeight
      quantitativeOutput.normalized.prepared.normalization
      geometry.common.translation geometry.cleanup.popular.center
      quantitativeOutput.normalized.prepared.slab.halfHeight_pos
    (by linarith [quantitativeOutput.normalized.normalization_nine])
    (by linarith [geometry.scales.scale_one]))

noncomputable def rawScaleData
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data)
    (sourceBoundedBase :
      HasBoundedBase quantitativeOutput.normalized.source.family 4)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    WZ2PaperPureScaleCoverData selected.selected.family
      (quantitativeVerticalTransportedQuotientScale quantitativeOutput geometry
        floor coordinate)
      (selected.scaleConstant quantitativeOutput geometry frostman floor
        coordinate) where
  delta_pos := geometry.scales.finalDelta_pos
  rho_pos := data.quotientScale_pos quantitativeOutput geometry frostman floor
    coordinate
  coarse := (selected.targetParents coordinate).family
  cover := selected.targetCover coordinate
  full_fiber_uniform := fun first second =>
    (selected.fullFiberUniform coordinate first second).trans
      (by
        gcongr
        exact le_max_left _ _)
  rescaledFiber := fun targetParent => ⟨{
    normalization := WZ2PaperAssouadUnitRescalingData.ofTube
      ((selected.targetParents coordinate).family.tube targetParent)
      (data.quotientScale_pos quantitativeOutput geometry frostman floor
        coordinate)
    convex_wolff := fun convexSet hconvex =>
      (selected.rawActualJohnFiberCWA quantitativeOutput geometry frostman floor
        sourceBoundedBase coordinate targetParent convexSet hconvex).trans (by
          gcongr
          exact le_max_right _ _) }⟩

/-- The only scalar input left after exact-child geometry and positive-gap
rounding: every actual-John scale constant fits the final nearby loss. -/
structure NearbyScaleAbsorptionReceipt
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data)
    (nearbyLoss : ℝ) : Prop where
  scaleConstant_le :
    ∀ coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount,
      selected.scaleConstant quantitativeOutput geometry frostman floor
          coordinate ≤
        Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-nearbyLoss)

/-- Assemble nearby CWA on the exact combined-selected final ED.  Covers,
owners, fibres, and rounding all use the same dependent witness. -/
theorem nearbyCWA
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (selected : QuantitativeVerticalTransportedCombinedSelectionData
      quantitativeOutput geometry frostman floor data)
    (sourceBoundedBase :
      HasBoundedBase quantitativeOutput.normalized.source.family 4)
    {nearbyLoss : ℝ}
    (hnearbyLoss : 0 < nearbyLoss)
    (absorption : selected.NearbyScaleAbsorptionReceipt
      quantitativeOutput geometry frostman floor nearbyLoss)
    (rounding :
      ∀ requested : WZ2PaperRequestedScale
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta),
        ∃ coordinate :
            Fin (schedule quantitativeOutput geometry floor).levelCount,
          requested.1 ≤
              quantitativeVerticalTransportedQuotientScale
                quantitativeOutput geometry floor coordinate ∧
            ENNReal.ofReal
                (quantitativeVerticalTransportedQuotientScale
                  quantitativeOutput geometry floor coordinate) <
              Kakeya.realRpowENN
                  (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
                  (-nearbyLoss) *
                ENNReal.ofReal requested.1) :
    WZ2PaperPureCWAAtNearbyScales
      (selected.finalED quantitativeOutput geometry frostman floor
        ).subfamily.family
      (Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        (-nearbyLoss)) := by
  change WZ2PaperPureCWAAtNearbyScales selected.selected.family _
  let outputConstant :=
    Kakeya.realRpowENN
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
      (-nearbyLoss)
  have outputOne : 1 ≤ outputConstant := by
    dsimp only [outputConstant]
    rw [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      geometry.scales.finalDelta_pos
      (geometry.scales.finalDelta_le_one_ninety_six.trans (by norm_num))
      (by linarith)
  have outputTop : outputConstant ≠ ⊤ := by
    simp [outputConstant, Kakeya.realRpowENN]
  apply pureWZ2_nearby_from_finite_witnesses
    geometry.scales.finalDelta_pos outputOne outputTop
    (by
      change WZ2PaperOrdinaryIsEssentiallyDistinct
        (selected.finalED quantitativeOutput geometry frostman floor
          ).subfamily.family
      exact (selected.finalED quantitativeOutput geometry frostman floor
        ).essentially_distinct)
    (schedule quantitativeOutput geometry floor).levelCount
    (schedule quantitativeOutput geometry floor).levelCount_pos
    (fun coordinate => ⟨
      quantitativeVerticalTransportedQuotientScale
        quantitativeOutput geometry floor coordinate,
      (selected.rawScaleData quantitativeOutput geometry frostman floor
        sourceBoundedBase coordinate).mono
          (absorption.scaleConstant_le coordinate)⟩)
    rounding

end QuantitativeVerticalTransportedCombinedSelectionData

end QuantitativeVerticalTransportedSourceParentQuotientData

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end
