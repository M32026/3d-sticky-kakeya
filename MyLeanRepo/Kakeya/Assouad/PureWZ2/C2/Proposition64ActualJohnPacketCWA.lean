import MyLeanRepo.Kakeya.Assouad.PureWZ2.BodyCWASubfamilyTransfer
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12BodyReindex
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64VariableJohnEnvelope
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingBridge
import Mathlib.Analysis.Convex.Measure

/-!
# Proposition 6.4 actual-John packet CWA

This is the map-independent packet kernel for the final nearby-CWA
construction.  A target packet injects into one complete source actual-John
fiber and pays an explicit weighted cardinality ratio.  One common affine
map and a fixed factor-100 carrier envelope then transfer its body CWA to the
target packet.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

attribute [local instance] Classical.propDecidable

/-- The source actual-John bodies indexed by one target packet. -/
noncomputable def pureWZ2Proposition64ActualJohnSourcePacket
    {sourceDelta sourceRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    (sourceParent : Fin sourceCoarse.card)
    (sourceNormalization : WZ2PaperAssouadUnitRescalingData
      (sourceCoarse.tube sourceParent))
    (targetBodies : Kakeya.Streamlined.BodyFamily)
    (sourceIndex : Fin targetBodies.card → Fin sourceFine.card)
    (source_mem : ∀ index, sourceIndex index ∈
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent) :
    Kakeya.Streamlined.BodyFamily where
  card := targetBodies.card
  body index :=
    (wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := sourceFine) (coarse := sourceCoarse)
      sourceParent sourceNormalization).body
        ((wz2PaperOrdinaryFullFiberIndexEquiv sourceParent).symm
          ⟨sourceIndex index, source_mem index⟩)

/-- Restrict one complete source actual-John fiber to a target-indexed packet,
paying the displayed weighted cardinality ratio. -/
theorem pureWZ2Proposition64_actualJohnSourcePacket_cwa
    {sourceDelta sourceRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    (sourceParent : Fin sourceCoarse.card)
    {sourceConstant : ENNReal}
    (sourceFiber : WZ2PaperPureUnitRescaledFullFiberData
      (fine := sourceFine) (coarse := sourceCoarse)
      sourceParent sourceConstant)
    (targetBodies : Kakeya.Streamlined.BodyFamily)
    (sourceIndex : Fin targetBodies.card → Fin sourceFine.card)
    (sourceIndex_injective : Function.Injective sourceIndex)
    (source_mem : ∀ index, sourceIndex index ∈
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent)
    (weight retentionConstant : ENNReal)
    (weight_ne_zero : weight ≠ 0)
    (weight_ne_top : weight ≠ ⊤)
    (cardinality_retention :
      weight *
          ((wz2PaperOrdinaryFullFiberIndices
            sourceFine sourceCoarse sourceParent).card : ENNReal) ≤
        retentionConstant * targetBodies.enncard) :
    WZ2PaperBodyConvexWolffBound
      (pureWZ2Proposition64ActualJohnSourcePacket
        sourceParent sourceFiber.normalization targetBodies
          sourceIndex source_mem)
      ((weight⁻¹ * retentionConstant) * sourceConstant) := by
  let sourceBodies := wz2PaperPureUnitRescaledFullFiberBodyFamily
    (fine := sourceFine) (coarse := sourceCoarse)
    sourceParent sourceFiber.normalization
  let packet := pureWZ2Proposition64ActualJohnSourcePacket
    sourceParent sourceFiber.normalization targetBodies sourceIndex source_mem
  let sourceBodyIndex : Fin packet.card → Fin sourceBodies.card :=
    fun index =>
      (wz2PaperOrdinaryFullFiberIndexEquiv sourceParent).symm
        ⟨sourceIndex index, source_mem index⟩
  let embedding : Fin packet.card ↪ Fin sourceBodies.card :=
    { toFun := sourceBodyIndex
      inj' := by
        intro first second equality
        apply sourceIndex_injective
        have hsub :
            (⟨sourceIndex first, source_mem first⟩ :
              wz2PaperOrdinaryFullFiberIndices
                sourceFine sourceCoarse sourceParent) =
            ⟨sourceIndex second, source_mem second⟩ :=
          (wz2PaperOrdinaryFullFiberIndexEquiv sourceParent).symm.injective
            equality
        exact congrArg Subtype.val hsub }
  let selected : Kakeya.Streamlined.Subfamily sourceBodies :=
    { family := packet
      embedding := embedding
      carrier_eq := fun _ => rfl }
  apply sourceFiber.convex_wolff.subfamily_of_weighted_cardinality
    selected weight_ne_zero weight_ne_top
  change weight *
      ((wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent).card : ENNReal) ≤
    retentionConstant * (targetBodies.card : ENNReal)
  exact cardinality_retention

/-- Transfer body CWA through one common affine map when every transformed
source packet body lies in the displayed homothety of its target body. -/
theorem pureWZ2Proposition64_bodyCWA_of_affine_homothetic_envelope_of_compact_bound
    {source target : Kakeya.Streamlined.BodyFamily}
    (equivalence : Point3 ≃ᵃ[ℝ] Point3)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (factor : ℝ)
    (factor_one : 1 ≤ factor)
    (boundingSet : Set Point3)
    (hboundingCompact : IsCompact boundingSet)
    (hboundingConvex : Convex ℝ boundingSet)
    (htargetBody : ∀ index,
      JohnEllipsoid.IsConvexBody (target.body index).carrier)
    (htargetBound : ∀ index,
      (target.body index).carrier ⊆ boundingSet)
    (center : Fin target.card → Point3)
    (center_mem : ∀ index,
      center index ∈ (target.body index).carrier)
    (carrier_envelope : ∀ index,
      equivalence '' (source.body (indexEquiv index)).carrier ⊆
        AffineMap.homothety (center index) factor ''
          (target.body index).carrier)
    (inverseVolumeConstant : ENNReal)
    (inverse_volume : ∀ targetSet : Set Point3,
      volume (equivalence.symm '' targetSet) ≤
        inverseVolumeConstant * volume targetSet)
    {sourceConstant : ENNReal}
    (sourceCWA : WZ2PaperBodyConvexWolffBound source sourceConstant) :
    WZ2PaperBodyConvexWolffBound target
      ((inverseVolumeConstant *
          ENNReal.ofReal (27 * (2 * factor - 1) ^ 3)) *
        sourceConstant) := by
  apply wz2PaperBodyConvexWolffBound_of_indexed_envelope indexEquiv
  · intro targetSet htargetConvex
    by_cases heligible : ∃ index : Fin target.card,
        (target.body index).carrier ⊆ targetSet
    · rcases heligible with ⟨eligible, heligible⟩
      let body := closure (targetSet ∩ boundingSet)
      have hbodyConvex : Convex ℝ body :=
        (htargetConvex.inter hboundingConvex).closure
      have hbodyCompact : IsCompact body := by
        apply Metric.isCompact_of_isClosed_isBounded isClosed_closure
        exact (hboundingCompact.isBounded.subset fun point hpoint =>
          closure_minimal (fun _ h => h.2) hboundingCompact.isClosed hpoint)
      have heligibleBody : (target.body eligible).carrier ⊆ body := by
        intro point hpoint
        exact subset_closure ⟨heligible hpoint, htargetBound eligible hpoint⟩
      have hbodyInterior : (interior body).Nonempty := by
        rcases (htargetBody eligible).2.2 with ⟨point, hpoint⟩
        exact ⟨point, interior_mono heligibleBody hpoint⟩
      have hbody : JohnEllipsoid.IsConvexBody body :=
        ⟨hbodyConvex, hbodyCompact, hbodyInterior⟩
      rcases pureWZ2Proposition64_variable_john_homothetic_envelope
          factor factor_one body hbody with
        ⟨targetEnvelope, htargetEnvelopeConvex, htargetEnvelopeVolume,
          htargetEnvelope⟩
      let sourceEnvelope := equivalence.symm '' targetEnvelope
      refine ⟨sourceEnvelope,
        Convex.affine_image equivalence.symm.toAffineMap
          htargetEnvelopeConvex, ?_, ?_⟩
      · calc
          volume sourceEnvelope ≤
              inverseVolumeConstant * volume targetEnvelope :=
            inverse_volume targetEnvelope
          _ ≤ inverseVolumeConstant *
              (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
                volume body) := by gcongr
          _ ≤ inverseVolumeConstant *
              (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
                volume targetSet) := by
            have hbodySubset : body ⊆ closure targetSet :=
              closure_mono fun _ hpoint => hpoint.1
            have hfrontier : volume (frontier targetSet) = 0 :=
              Convex.addHaar_frontier volume htargetConvex
            have hbodyVolume : volume body ≤ volume targetSet := by
              calc
                volume body ≤ volume (closure targetSet) :=
                  measure_mono hbodySubset
                _ = volume targetSet :=
                  measure_closure_of_null_frontier hfrontier
            exact mul_le_mul_left'
              (mul_le_mul_left' hbodyVolume
                (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3)))
              inverseVolumeConstant
          _ = (inverseVolumeConstant *
                ENNReal.ofReal (27 * (2 * factor - 1) ^ 3)) *
              volume targetSet := by ring
      · intro targetIndex htargetContained sourcePoint hsourcePoint
        have htargetBodySubset :
            (target.body targetIndex).carrier ⊆ body := by
          intro point hpoint
          exact subset_closure
            ⟨htargetContained hpoint, htargetBound targetIndex hpoint⟩
        have hcenterBody : center targetIndex ∈ body :=
          htargetBodySubset (center_mem targetIndex)
        have himageHomothetic : equivalence sourcePoint ∈
            AffineMap.homothety (center targetIndex) factor '' body :=
          Set.image_mono htargetBodySubset
            (carrier_envelope targetIndex ⟨sourcePoint, hsourcePoint, rfl⟩)
        have himage : equivalence sourcePoint ∈ targetEnvelope :=
          htargetEnvelope (center targetIndex) hcenterBody himageHomothetic
        exact ⟨equivalence sourcePoint, himage,
          equivalence.symm_apply_apply sourcePoint⟩
    · refine ⟨(∅ : Set Point3), convex_empty, by simp, ?_⟩
      intro targetIndex htarget
      exact (heligible ⟨targetIndex, htarget⟩).elim
  · exact sourceCWA

/-- Unit-ball specialization of the compact-bound affine homothetic CWA
transport. -/
theorem pureWZ2Proposition64_bodyCWA_of_affine_homothetic_envelope
    {source target : Kakeya.Streamlined.BodyFamily}
    (equivalence : Point3 ≃ᵃ[ℝ] Point3)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (factor : ℝ)
    (factor_one : 1 ≤ factor)
    (htargetBody : ∀ index,
      JohnEllipsoid.IsConvexBody (target.body index).carrier)
    (htargetBound : ∀ index,
      (target.body index).carrier ⊆ Metric.closedBall (0 : Point3) 1)
    (center : Fin target.card → Point3)
    (center_mem : ∀ index,
      center index ∈ (target.body index).carrier)
    (carrier_envelope : ∀ index,
      equivalence '' (source.body (indexEquiv index)).carrier ⊆
        AffineMap.homothety (center index) factor ''
          (target.body index).carrier)
    (inverseVolumeConstant : ENNReal)
    (inverse_volume : ∀ targetSet : Set Point3,
      volume (equivalence.symm '' targetSet) ≤
        inverseVolumeConstant * volume targetSet)
    {sourceConstant : ENNReal}
    (sourceCWA : WZ2PaperBodyConvexWolffBound source sourceConstant) :
    WZ2PaperBodyConvexWolffBound target
      ((inverseVolumeConstant *
          ENNReal.ofReal (27 * (2 * factor - 1) ^ 3)) *
        sourceConstant) := by
  exact
    pureWZ2Proposition64_bodyCWA_of_affine_homothetic_envelope_of_compact_bound
      equivalence indexEquiv factor factor_one
      (Metric.closedBall (0 : Point3) 1)
      (isCompact_closedBall (0 : Point3) 1)
      (convex_closedBall (0 : Point3) 1)
      htargetBody htargetBound center center_mem carrier_envelope
      inverseVolumeConstant inverse_volume sourceCWA

/-- Complete packet CWA: restrict a source actual-John fiber with an explicit
weighted cardinality receipt, then transport that packet through one affine
homothetic carrier envelope. -/
theorem pureWZ2Proposition64_actualJohnPacket_cwa
    {sourceDelta sourceRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    (sourceParent : Fin sourceCoarse.card)
    {sourceConstant : ENNReal}
    (sourceFiber : WZ2PaperPureUnitRescaledFullFiberData
      (fine := sourceFine) (coarse := sourceCoarse)
      sourceParent sourceConstant)
    (targetBodies : Kakeya.Streamlined.BodyFamily)
    (sourceIndex : Fin targetBodies.card → Fin sourceFine.card)
    (sourceIndex_injective : Function.Injective sourceIndex)
    (source_mem : ∀ index, sourceIndex index ∈
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent)
    (weight retentionConstant : ENNReal)
    (weight_ne_zero : weight ≠ 0)
    (weight_ne_top : weight ≠ ⊤)
    (cardinality_retention :
      weight *
          ((wz2PaperOrdinaryFullFiberIndices
            sourceFine sourceCoarse sourceParent).card : ENNReal) ≤
        retentionConstant * targetBodies.enncard)
    (equivalence : Point3 ≃ᵃ[ℝ] Point3)
    (factor : ℝ)
    (factor_one : 1 ≤ factor)
    (htargetBody : ∀ index,
      JohnEllipsoid.IsConvexBody (targetBodies.body index).carrier)
    (htargetBound : ∀ index,
      (targetBodies.body index).carrier ⊆ Metric.closedBall (0 : Point3) 1)
    (center : Fin targetBodies.card → Point3)
    (center_mem : ∀ index,
      center index ∈ (targetBodies.body index).carrier)
    (carrier_envelope : ∀ index,
      equivalence ''
          ((pureWZ2Proposition64ActualJohnSourcePacket
            sourceParent sourceFiber.normalization targetBodies
              sourceIndex source_mem).body index).carrier ⊆
        AffineMap.homothety (center index) factor ''
          (targetBodies.body index).carrier)
    (inverseVolumeConstant : ENNReal)
    (inverse_volume : ∀ targetSet : Set Point3,
      volume (equivalence.symm '' targetSet) ≤
        inverseVolumeConstant * volume targetSet) :
    WZ2PaperBodyConvexWolffBound targetBodies
      ((inverseVolumeConstant *
          ENNReal.ofReal (27 * (2 * factor - 1) ^ 3)) *
        ((weight⁻¹ * retentionConstant) * sourceConstant)) := by
  let packet := pureWZ2Proposition64ActualJohnSourcePacket
    sourceParent sourceFiber.normalization targetBodies sourceIndex source_mem
  apply pureWZ2Proposition64_bodyCWA_of_affine_homothetic_envelope
    (source := packet) (target := targetBodies)
    equivalence (Equiv.refl _) factor factor_one htargetBody htargetBound center center_mem
      carrier_envelope inverseVolumeConstant inverse_volume
  exact pureWZ2Proposition64_actualJohnSourcePacket_cwa
    sourceParent sourceFiber targetBodies sourceIndex sourceIndex_injective
      source_mem weight retentionConstant weight_ne_zero weight_ne_top
      cardinality_retention

end Kakeya.Assouad

end
