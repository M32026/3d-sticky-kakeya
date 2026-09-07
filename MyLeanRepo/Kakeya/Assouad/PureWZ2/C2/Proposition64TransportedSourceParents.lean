import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64AffineNearbyCWATransport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64QuantitativeVerticalMatchedSourceCovers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64QuantitativeVerticalCarrierTransport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalizedRelabelParent
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalizedAssignedParentCover

/-!
# Proposition 6.4 transported source parents

At every coordinate of the fixed target scale schedule, use the matched
Definition 2.12 source cover.  Its hit parents are represented by tubes from
the exact source packet, and those representative lines are transported by
the same combined affine map as the final paper-ED family.  Relabelling the
transported lines at the honest enlarged radius gives a raw target cover and
an explicit source-owner synchronization.

This is deliberately the pre-selection layer.  It asserts neither target
packing nor doubled-fibre disjointness; those belong to the subsequent
bounded-conflict selection.
-/

noncomputable section

namespace Kakeya.Assouad

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

private noncomputable abbrev sourcePacket :=
  quantitativeVerticalExactSourcePacket quantitativeOutput geometry frostman

private noncomputable abbrev sourceNearby
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :=
  quantitativeVerticalMatchedSourceNearby
    quantitativeOutput geometry floor coordinate

private noncomputable abbrev sourceParents
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :=
  (sourceNearby quantitativeOutput geometry floor coordinate).scaleData.cover
    |>.hitParentSubfamily
      (sourcePacket quantitativeOutput geometry frostman)

/-- The exact target radius paid by transporting all final tubes with one
fixed source parent. -/
def quantitativeVerticalTransportedSourceParentScale
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    ℝ :=
  pureWZ2Proposition64RepresentativeTransportScale
    (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
    pureWZ2Proposition64Lemma35Scale
    (sourceNearby quantitativeOutput geometry floor coordinate).rho

/-- Canonical representative in the exact final packet of one hit source
parent. -/
noncomputable def quantitativeVerticalSourceParentRepresentative
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (parent : Fin (sourceParents quantitativeOutput geometry frostman floor
      coordinate).family.card) :
    Fin (initialED quantitativeOutput geometry frostman).subfamily.family.card :=
  Classical.choose <|
    (sourceNearby quantitativeOutput geometry floor coordinate).scaleData.cover
      |>.hitParent_surjective
        (sourcePacket quantitativeOutput geometry frostman) parent

theorem quantitativeVerticalSourceParentRepresentative_hitParent
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (parent : Fin (sourceParents quantitativeOutput geometry frostman floor
      coordinate).family.card) :
    (sourceNearby quantitativeOutput geometry floor coordinate).scaleData.cover.hitParent
        (sourcePacket quantitativeOutput geometry frostman)
        (quantitativeVerticalSourceParentRepresentative
          quantitativeOutput geometry frostman floor coordinate parent) =
      parent :=
  Classical.choose_spec <|
    (sourceNearby quantitativeOutput geometry floor coordinate).scaleData.cover
      |>.hitParent_surjective
        (sourcePacket quantitativeOutput geometry frostman) parent

/-- The target parent family obtained by applying the same exact `Phi` line
transport as the final family, canonically centring, and relabelling at the
honest enlarged radius. -/
noncomputable def quantitativeVerticalTransportedSourceParents
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    Kakeya.Streamlined.TubeFamily
      (quantitativeVerticalTransportedSourceParentScale
        quantitativeOutput geometry floor coordinate) where
  card := (sourceParents quantitativeOutput geometry frostman floor
    coordinate).family.card
  tube parent := wz2PaperRelabelTube
    (targetScale := quantitativeVerticalTransportedSourceParentScale
      quantitativeOutput geometry floor coordinate)
    (pureWZ2PaperCenteredTube
      ((initialED quantitativeOutput geometry frostman).subfamily.family.tube
        (quantitativeVerticalSourceParentRepresentative
          quantitativeOutput geometry frostman floor coordinate parent)))

/-- The target owner is literally the hit-parent map of the restricted
source Definition 2.12 cover. -/
noncomputable def quantitativeVerticalTransportedSourceParent
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    Fin (initialED quantitativeOutput geometry frostman).subfamily.family.card →
      Fin (quantitativeVerticalTransportedSourceParents
        quantitativeOutput geometry frostman floor coordinate).card :=
  (sourceNearby quantitativeOutput geometry floor coordinate).scaleData.cover
    |>.hitParent (sourcePacket quantitativeOutput geometry frostman)

/-- Raw exact-`Phi` source-parent transport over the whole finite schedule.
It deliberately contains no target packing or doubled-fibre disjointness. -/
structure QuantitativeVerticalTransportedSourceParentScheduleData : Prop where
  target_carrier :
    ∀ (coordinate :
        Fin (schedule quantitativeOutput geometry floor).levelCount)
      (source : Fin
        (initialED quantitativeOutput geometry frostman).subfamily.family.card),
      ((initialED quantitativeOutput geometry frostman).subfamily.family.tube
          source).carrier ⊆
        ((quantitativeVerticalTransportedSourceParents
            quantitativeOutput geometry frostman floor coordinate).tube
          (quantitativeVerticalTransportedSourceParent
            quantitativeOutput geometry frostman floor coordinate source)).carrier
  source_parent_synchronized :
    ∀ (coordinate :
        Fin (schedule quantitativeOutput geometry floor).levelCount)
      (source : Fin
        (initialED quantitativeOutput geometry frostman).subfamily.family.card),
      (sourceParents quantitativeOutput geometry frostman floor coordinate).embedding
          (quantitativeVerticalTransportedSourceParent
            quantitativeOutput geometry frostman floor coordinate source) =
        (sourceNearby quantitativeOutput geometry floor coordinate).scaleData.cover.parent
          ((sourcePacket quantitativeOutput geometry frostman).embedding source)

namespace QuantitativeVerticalTransportedSourceParentScheduleData

theorem targetCoarse_lineClass
    (data : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    WZ1PaperIsLineClass
      (quantitativeVerticalTransportedSourceParents
        quantitativeOutput geometry frostman floor coordinate) := by
  intro parent
  exact wz2PaperRelabelTube_lineClass <|
    pureWZ2PaperCenteredTube_lineClass <|
      geometry.paperED_lineClass
        (initialED quantitativeOutput geometry frostman)
        (quantitativeVerticalSourceParentRepresentative
          quantitativeOutput geometry frostman floor coordinate parent)

theorem targetFine_midpoint_local
    (data : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor) :
    ∀ index, ‖wz2PaperTubeMidpoint
      ((initialED quantitativeOutput geometry frostman).subfamily.family.tube
        index)‖ ≤ 3 := by
  intro index
  let ed := initialED quantitativeOutput geometry frostman
  have hcentered :
      wz2PaperTubeMidpoint (ed.subfamily.family.tube index) =
        wz1TubeAxisZeroPoint (ed.subfamily.family.tube index) := by
    have hvertical := (geometry.paperED_lineClass ed index).vertical
    rw [ed.tube_provenance index] at hvertical
    rw [ed.tube_provenance index]
    apply pureWZ2Proposition64IsotropicRebasedPaperTube_midpoint
    simpa [pureWZ2Proposition64IsotropicPaperFamily,
      pureWZ2Proposition64IsotropicRebasedPaperTube,
      pureWZ2Proposition64IsotropicPaperTube] using hvertical
  rw [hcentered]
  have hzeroTwo :
      wz1TubeAxisZeroPoint (ed.subfamily.family.tube index) (2 : Fin 3) = 0 :=
    wz1TubeAxisZeroPoint_coord_two _
      (geometry.paperED_lineClass ed index).vertical
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  constructor
  · positivity
  · simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three, hzeroTwo]
    have hzero := sq_le_sq₀
      (abs_nonneg (wz1TubeAxisZeroPoint (ed.subfamily.family.tube index) 0))
      (by norm_num : 0 ≤ (1 / 3 : ℝ)) |>.2
        (geometry.paperED_lineClass ed index).2.1
    have hone := sq_le_sq₀
      (abs_nonneg (wz1TubeAxisZeroPoint (ed.subfamily.family.tube index) 1))
      (by norm_num : 0 ≤ (1 / 3 : ℝ)) |>.2
        (geometry.paperED_lineClass ed index).2.2
    rw [sq_abs] at hzero hone
    nlinarith

theorem targetParent_surjective
    (data : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    Function.Surjective
      (quantitativeVerticalTransportedSourceParent
        quantitativeOutput geometry frostman floor coordinate) := by
  change Function.Surjective
    ((sourceNearby quantitativeOutput geometry floor coordinate).scaleData.cover
      |>.hitParent (sourcePacket quantitativeOutput geometry frostman))
  exact
    (sourceNearby quantitativeOutput geometry floor coordinate).scaleData.cover
      |>.hitParent_surjective
        (sourcePacket quantitativeOutput geometry frostman)

/-- View one raw transported coordinate through the repository's generic
pre-assigned-cover interface. -/
noncomputable def toPreAssignedParentCover
    (data : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    PureWZ2LocalizedPreAssignedParentCoverData
      (initialED quantitativeOutput geometry frostman).subfamily.family
      (quantitativeVerticalTransportedSourceParents
        quantitativeOutput geometry frostman floor coordinate) where
  delta_pos := geometry.scales.finalDelta_pos
  rho_pos := by
    unfold quantitativeVerticalTransportedSourceParentScale
      pureWZ2Proposition64RepresentativeTransportScale
    have hsourceRho :=
      (sourceNearby quantitativeOutput geometry floor coordinate).scaleData.rho_pos
    have hscale := pureWZ2Proposition64Lemma35Scale_pos
    have hfinal := geometry.scales.finalDelta_pos
    nlinarith
  fine_line_class := geometry.paperED_lineClass
    (initialED quantitativeOutput geometry frostman)
  coarse_line_class := data.targetCoarse_lineClass
    quantitativeOutput geometry frostman floor coordinate
  fine_midpoint_local := data.targetFine_midpoint_local
  assignedParent := quantitativeVerticalTransportedSourceParent
    quantitativeOutput geometry frostman floor coordinate
  assigned_containment := data.target_carrier coordinate

end QuantitativeVerticalTransportedSourceParentScheduleData

private theorem quantitativeVertical_final_tubeParams
    (index : Fin
      (initialED quantitativeOutput geometry frostman).subfamily.family.card) :
    tubeParamsOfTube
        ((initialED quantitativeOutput geometry frostman).subfamily.family.tube
          index) =
      pureWZ2Proposition64IsotropicTubeParams
        geometry.cleanup.popular.center pureWZ2Proposition64Lemma35Scale
        (pureWZ2Proposition64ExactTubeParams
          (quantitativeOutput.normalized.prepared.restrictedRaw.slope
            quantitativeOutput.normalized.prepared.slab.anchorHeight)
          quantitativeOutput.normalized.prepared.slab.center
          quantitativeOutput.normalized.prepared.slab.halfHeight
          quantitativeOutput.normalized.prepared.normalization
          geometry.common.translation
          (tubeParamsOfTube
            (quantitativeOutput.normalized.source.family.tube
              (geometry.finalSourceEmbedding
                (initialED quantitativeOutput geometry frostman) index)))) := by
  let sourceTube := quantitativeOutput.normalized.source.family.tube
    (geometry.finalSourceEmbedding
      (initialED quantitativeOutput geometry frostman) index)
  let targetTube :=
    (initialED quantitativeOutput geometry frostman).subfamily.family.tube index
  have hsourceLine : WZ1PaperTubeInLineClass sourceTube :=
    quantitativeOutput.normalized.source.line_class _
  have htargetLine : WZ1PaperTubeInLineClass targetTube :=
    geometry.paperED_lineClass
      (initialED quantitativeOutput geometry frostman) index
  have hexactVertical :
      (pureWZ2Proposition64ImageTube
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        quantitativeOutput.normalized.prepared.restrictedRaw.slope
        quantitativeOutput.normalized.prepared.slab.center
        quantitativeOutput.normalized.prepared.slab.anchorHeight
        quantitativeOutput.normalized.prepared.slab.halfHeight
        quantitativeOutput.normalized.prepared.normalization
        geometry.common.translation
        quantitativeOutput.normalized.prepared.slab.halfHeight_pos
        quantitativeOutput.normalized.prepared.normalized.normalization_pos
        sourceTube).direction 2 ≠ 0 := by
    have hvertical := pureWZ2Proposition64ImageTube_vertical
      (targetDelta := pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
      quantitativeOutput.normalized.prepared.restrictedRaw.slope
      quantitativeOutput.normalized.prepared.slab.center
      quantitativeOutput.normalized.prepared.slab.anchorHeight
      geometry.common.translation
      quantitativeOutput.normalized.prepared.slab.halfHeight_pos
      quantitativeOutput.normalized.halfHeight_small
      quantitativeOutput.normalized.prepared.normalization_one
      quantitativeOutput.normalized.prepared.normalized.anchor_value_bound
      sourceTube hsourceLine.vertical
    exact abs_pos.mp <| lt_of_lt_of_le
      (show (0 : ℝ) < 1 / 2 by norm_num) hvertical
  apply tubeParamsOfTube_eq_proposition64Combined_of_axis_image
    quantitativeOutput.normalized.prepared.restrictedRaw.slope
    quantitativeOutput.normalized.prepared.slab.center
    quantitativeOutput.normalized.prepared.slab.anchorHeight
    quantitativeOutput.normalized.prepared.slab.halfHeight
    quantitativeOutput.normalized.prepared.normalization
    geometry.common.translation geometry.cleanup.popular.center
    pureWZ2Proposition64Lemma35Scale geometry.common.translation_height
    quantitativeOutput.normalized.prepared.slab.halfHeight_pos
    quantitativeOutput.normalized.prepared.normalized.normalization_pos
    pureWZ2Proposition64Lemma35Scale_pos sourceTube
    (abs_pos.mp <| lt_of_lt_of_le
      (show (0 : ℝ) < 1 / 2 by norm_num) hsourceLine.vertical)
    targetTube
    (abs_pos.mp <| lt_of_lt_of_le
      (show (0 : ℝ) < 1 / 2 by norm_num) htargetLine.vertical)
    hexactVertical
  have haxis := affineNearby_final_axis
    quantitativeOutput geometry frostman index
  rw [affineNearbySourcePacket_tube] at haxis
  calc
    tubeAxisLine targetTube =
        affineNearbyPhi quantitativeOutput geometry ''
          tubeAxisLine sourceTube := haxis
    _ = pureWZ2Proposition64IsotropicMap geometry.cleanup.popular.center
          pureWZ2Proposition64Lemma35Scale ''
        (pureWZ2Proposition64TranslatedMap
          quantitativeOutput.normalized.prepared.restrictedRaw.slope
          quantitativeOutput.normalized.prepared.slab.center
          quantitativeOutput.normalized.prepared.slab.anchorHeight
          quantitativeOutput.normalized.prepared.slab.halfHeight
          quantitativeOutput.normalized.prepared.normalization
          geometry.common.translation '' tubeAxisLine sourceTube) := by
      ext point
      simp only [Set.mem_image]
      constructor
      · rintro ⟨sourcePoint, hsourcePoint, rfl⟩
        refine ⟨pureWZ2Proposition64TranslatedMap
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

/-- Construct the raw transported-parent schedule from the exact source
packet.  The bounded-base input is the production re-entry certificate, not a
new geometric assumption. -/
theorem exists_quantitativeVerticalTransportedSourceParents
    (sourceBoundedBase :
      HasBoundedBase quantitativeOutput.normalized.source.family 4) :
    Nonempty (QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor) := by
  refine ⟨{
    target_carrier := ?_
    source_parent_synchronized := ?_ }⟩
  · intro coordinate source
    let ed := initialED quantitativeOutput geometry frostman
    let nearby := sourceNearby quantitativeOutput geometry floor coordinate
    let packet := sourcePacket quantitativeOutput geometry frostman
    let parent := quantitativeVerticalTransportedSourceParent
      quantitativeOutput geometry frostman floor coordinate source
    let sourceRepresentative := quantitativeVerticalSourceParentRepresentative
      quantitativeOutput geometry frostman floor coordinate parent
    let targetFirst := pureWZ2PaperCenteredTube
      (ed.subfamily.family.tube source)
    let targetSecond := pureWZ2PaperCenteredTube
      (ed.subfamily.family.tube sourceRepresentative)
    have hsourceDeltaRho : sourceDelta ≤ nearby.rho :=
      (quantitativeVerticalMatchedSourceRequested
        quantitativeOutput geometry floor coordinate).2.1.trans
        nearby.requested_le
    have hsameParent :
        nearby.scaleData.cover.parent
            (geometry.finalSourceEmbedding ed source) =
          nearby.scaleData.cover.parent
            (geometry.finalSourceEmbedding ed sourceRepresentative) := by
      have hsource := nearby.scaleData.cover.hitParent_ambient packet source
      have hrepresentative := nearby.scaleData.cover.hitParent_ambient
        packet sourceRepresentative
      have hchosen :
          nearby.scaleData.cover.hitParent packet sourceRepresentative =
            parent :=
        Classical.choose_spec <|
          nearby.scaleData.cover.hitParent_surjective packet parent
      rw [hchosen] at hrepresentative
      exact hsource.symm.trans hrepresentative
    have hfirstLine : WZ1PaperTubeInLineClass targetFirst :=
      pureWZ2PaperCenteredTube_lineClass
        (geometry.paperED_lineClass ed source)
    have hsecondLine : WZ1PaperTubeInLineClass targetSecond :=
      pureWZ2PaperCenteredTube_lineClass
        (geometry.paperED_lineClass ed sourceRepresentative)
    have hfirstParams : tubeParamsOfTube targetFirst =
        pureWZ2Proposition64IsotropicTubeParams
          geometry.cleanup.popular.center pureWZ2Proposition64Lemma35Scale
          (pureWZ2Proposition64ExactTubeParams
            (quantitativeOutput.normalized.prepared.restrictedRaw.slope
              quantitativeOutput.normalized.prepared.slab.anchorHeight)
            quantitativeOutput.normalized.prepared.slab.center
            quantitativeOutput.normalized.prepared.slab.halfHeight
            quantitativeOutput.normalized.prepared.normalization
            geometry.common.translation
            (tubeParamsOfTube
              (quantitativeOutput.normalized.source.family.tube
                (geometry.finalSourceEmbedding ed source)))) := by
      calc
        tubeParamsOfTube targetFirst =
            tubeParamsOfTube (ed.subfamily.family.tube source) :=
          tubeParamsOfTube_eq_of_axis_eq
            (ed.subfamily.family.tube source) targetFirst
            (abs_pos.mp <| lt_of_lt_of_le
              (show (0 : ℝ) < 1 / 2 by norm_num)
              (geometry.paperED_lineClass ed source).vertical)
            (abs_pos.mp <| lt_of_lt_of_le
              (show (0 : ℝ) < 1 / 2 by norm_num) hfirstLine.vertical)
            (pureWZ2PaperCenteredTube_axis _)
        _ = _ := quantitativeVertical_final_tubeParams
          quantitativeOutput geometry frostman source
    have hsecondParams : tubeParamsOfTube targetSecond =
        pureWZ2Proposition64IsotropicTubeParams
          geometry.cleanup.popular.center pureWZ2Proposition64Lemma35Scale
          (pureWZ2Proposition64ExactTubeParams
            (quantitativeOutput.normalized.prepared.restrictedRaw.slope
              quantitativeOutput.normalized.prepared.slab.anchorHeight)
            quantitativeOutput.normalized.prepared.slab.center
            quantitativeOutput.normalized.prepared.slab.halfHeight
            quantitativeOutput.normalized.prepared.normalization
            geometry.common.translation
            (tubeParamsOfTube
              (quantitativeOutput.normalized.source.family.tube
                (geometry.finalSourceEmbedding ed sourceRepresentative)))) := by
      calc
        tubeParamsOfTube targetSecond =
            tubeParamsOfTube (ed.subfamily.family.tube sourceRepresentative) :=
          tubeParamsOfTube_eq_of_axis_eq
            (ed.subfamily.family.tube sourceRepresentative) targetSecond
            (abs_pos.mp <| lt_of_lt_of_le
              (show (0 : ℝ) < 1 / 2 by norm_num)
              (geometry.paperED_lineClass ed sourceRepresentative).vertical)
            (abs_pos.mp <| lt_of_lt_of_le
              (show (0 : ℝ) < 1 / 2 by norm_num) hsecondLine.vertical)
            (pureWZ2PaperCenteredTube_axis _)
        _ = _ := quantitativeVertical_final_tubeParams
          quantitativeOutput geometry frostman sourceRepresentative
    have hfirstCentered : pureWZ2PaperCenteredTube targetFirst = targetFirst := by
      apply pureWZ2PaperCenteredTube_eq_self targetFirst hfirstLine
      · change 0 ≤ wz1PaperDirection (ed.subfamily.family.tube source) 2
        linarith [(geometry.paperED_lineClass ed source).1]
      · dsimp only [targetFirst]
        rw [pureWZ2PaperCenteredTube_midpoint]
        exact wz1TubeAxisZeroPoint_coord_two _
          (geometry.paperED_lineClass ed source).vertical
    have hsecondCentered :
        pureWZ2PaperCenteredTube targetSecond = targetSecond := by
      apply pureWZ2PaperCenteredTube_eq_self targetSecond hsecondLine
      · change 0 ≤
          wz1PaperDirection (ed.subfamily.family.tube sourceRepresentative) 2
        linarith [(geometry.paperED_lineClass ed sourceRepresentative).1]
      · dsimp only [targetSecond]
        rw [pureWZ2PaperCenteredTube_midpoint]
        exact wz1TubeAxisZeroPoint_coord_two _
          (geometry.paperED_lineClass ed sourceRepresentative).vertical
    have hcontain := pureWZ2Proposition64_combined_carrier_subset_representative
      (anchorSlope :=
        quantitativeOutput.normalized.prepared.restrictedRaw.slope
          quantitativeOutput.normalized.prepared.slab.anchorHeight)
      (slabCenter := quantitativeOutput.normalized.prepared.slab.center)
      (halfHeight := quantitativeOutput.normalized.prepared.slab.halfHeight)
      (normalization := quantitativeOutput.normalized.prepared.normalization)
      (translation := geometry.common.translation)
      (center := geometry.cleanup.popular.center)
      (scale := pureWZ2Proposition64Lemma35Scale)
      (sourceFamily := quantitativeOutput.normalized.source.family)
      (sourceScale := nearby.scaleData)
      (first := geometry.finalSourceEmbedding ed source)
      (second := geometry.finalSourceEmbedding ed sourceRepresentative)
      (targetFirst := targetFirst) (targetSecond := targetSecond)
      hsourceDeltaRho quantitativeOutput.normalized.source.line_class
      (fun index => (sourceBoundedBase index).trans (by norm_num))
      hsameParent geometry.scales.finalDelta_pos hfirstLine hsecondLine
      quantitativeOutput.normalized.prepared.normalized.anchor_value_bound
      (by
        have hcenter :=
          quantitativeOutput.normalized.prepared.slab.source_window 0 (by norm_num)
        rw [mul_zero, add_zero] at hcenter
        exact abs_le.mpr hcenter)
      quantitativeOutput.normalized.prepared.slab.halfHeight_pos
      quantitativeOutput.normalized.prepared.slab.halfHeight_le_one
      quantitativeOutput.normalized.normalization_nine
      (geometry.cleanup.popular.center_mem 2)
      geometry.scales.scale_one hfirstParams hsecondParams
      hfirstCentered hsecondCentered
    have hfinalMidpoint :
        wz2PaperTubeMidpoint (ed.subfamily.family.tube source) =
          wz1TubeAxisZeroPoint (ed.subfamily.family.tube source) := by
      have hvertical := (geometry.paperED_lineClass ed source).vertical
      rw [ed.tube_provenance source] at hvertical
      rw [ed.tube_provenance source]
      apply pureWZ2Proposition64IsotropicRebasedPaperTube_midpoint
      simpa [pureWZ2Proposition64IsotropicPaperFamily,
        pureWZ2Proposition64IsotropicRebasedPaperTube,
        pureWZ2Proposition64IsotropicPaperTube] using hvertical
    have hfinalMidpointZero :
        wz2PaperTubeMidpoint (ed.subfamily.family.tube source) 2 = 0 := by
      rw [hfinalMidpoint]
      exact wz1TubeAxisZeroPoint_coord_two _
        (geometry.paperED_lineClass ed source).vertical
    rw [show
      (ed.subfamily.family.tube source).carrier = targetFirst.carrier by
        exact (pureWZ2PaperCenteredTube_carrier_eq_of_midpoint_height_zero
          (ed.subfamily.family.tube source)
          (geometry.paperED_lineClass ed source) hfinalMidpointZero).symm]
    change targetFirst.carrier ⊆
      (wz2PaperRelabelTube
        (targetScale := quantitativeVerticalTransportedSourceParentScale
          quantitativeOutput geometry floor coordinate) targetSecond).carrier
    simpa only [quantitativeVerticalTransportedSourceParentScale] using hcontain
  · intro coordinate source
    change
      (sourceParents quantitativeOutput geometry frostman floor coordinate).embedding
          (quantitativeVerticalTransportedSourceParent
            quantitativeOutput geometry frostman floor coordinate source) = _
    exact (sourceNearby quantitativeOutput geometry floor coordinate).scaleData.cover
      |>.hitParent_ambient
        (sourcePacket quantitativeOutput geometry frostman) source

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end
