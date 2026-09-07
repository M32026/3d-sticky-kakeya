import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.VariableJohnHomotheticEnvelope
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12BodyReindex
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingBridge
import Mathlib.Analysis.Convex.Measure

/-!
# Actual-body CWA through an affine homothetic envelope

This is the body-level counterpart of the cropped top-level affine transfer.
The target bodies are the genuine bodies used by the public actual-John fiber.
No ordinary carrier is replaced by a cropped full-line carrier.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

attribute [local instance] Classical.propDecidable

/-- Transfer normalized body CWA through one affine map when every transformed
source body lies in a controlled homothety of its corresponding target body.

The uniform ball bound is used only to replace a possibly unbounded test
convex set by a compact convex body before applying the outer-John envelope.
-/
theorem pureWZ2_bodyCWA_of_affine_homothetic_envelope
    {source target : Kakeya.Streamlined.BodyFamily}
    (equivalence : Point3 ≃ᵃ[ℝ] Point3)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (factor radius : ℝ)
    (hfactor : 1 ≤ factor)
    (hradius : 0 ≤ radius)
    (htargetBody : ∀ index,
      JohnEllipsoid.IsConvexBody (target.body index).carrier)
    (htargetBound : ∀ index,
      (target.body index).carrier ⊆ Metric.closedBall (0 : Point3) radius)
    (center : Fin target.card → Point3)
    (hcenter : ∀ index, center index ∈ (target.body index).carrier)
    (hcarrier : ∀ index,
      equivalence '' (source.body (indexEquiv index)).carrier ⊆
        AffineMap.homothety (center index) factor ''
          (target.body index).carrier)
    {sourceConstant : ENNReal}
    (hsource : WZ2PaperBodyConvexWolffBound source sourceConstant) :
    WZ2PaperBodyConvexWolffBound target
      (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
        ENNReal.ofReal
          |LinearMap.det
            (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)| *
        sourceConstant) := by
  apply wz2PaperBodyConvexWolffBound_of_indexed_envelope indexEquiv
  · intro targetSet htargetConvex
    by_cases heligible : ∃ index : Fin target.card,
        (target.body index).carrier ⊆ targetSet
    · rcases heligible with ⟨eligible, heligible⟩
      let boundedTarget :=
        targetSet ∩ Metric.closedBall (0 : Point3) radius
      let body := closure boundedTarget
      have hballConvex :
          Convex ℝ (Metric.closedBall (0 : Point3) radius) :=
        convex_closedBall (0 : Point3) radius
      have hboundedConvex : Convex ℝ boundedTarget :=
        htargetConvex.inter hballConvex
      have hbodyConvex : Convex ℝ body := hboundedConvex.closure
      have hbodyCompact : IsCompact body := by
        apply Metric.isCompact_of_isClosed_isBounded isClosed_closure
        exact (Metric.isBounded_closedBall.subset fun point hpoint =>
          closure_minimal (fun _ h => h.2) Metric.isClosed_closedBall hpoint)
      have heligibleBody : (target.body eligible).carrier ⊆ body := by
        intro point hpoint
        exact subset_closure ⟨heligible hpoint, htargetBound eligible hpoint⟩
      have hbodyInterior : (interior body).Nonempty := by
        rcases (htargetBody eligible).2.2 with ⟨point, hpoint⟩
        exact ⟨point, interior_mono heligibleBody hpoint⟩
      have hbody : JohnEllipsoid.IsConvexBody body :=
        ⟨hbodyConvex, hbodyCompact, hbodyInterior⟩
      rcases pureWZ2_variable_john_homothetic_envelope
          factor hfactor body hbody with
        ⟨targetEnvelope, htargetEnvelopeConvex, htargetEnvelopeVolume,
          htargetEnvelope⟩
      let sourceEnvelope := equivalence.symm '' targetEnvelope
      have hsourceEnvelopeConvex : Convex ℝ sourceEnvelope :=
        Convex.affine_image equivalence.symm.toAffineMap
          htargetEnvelopeConvex
      have hsourceEnvelopeVolume : volume sourceEnvelope ≤
          (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
            ENNReal.ofReal
              |LinearMap.det
                (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)|) *
            volume targetSet := by
        rw [wz2PaperAffineEquiv_volume_image_eq]
        have hbodyVolume : volume body ≤ volume targetSet := by
          have hbodySubset : body ⊆ closure targetSet :=
            closure_mono fun _ hpoint => hpoint.1
          have hfrontier : volume (frontier targetSet) = 0 :=
            Convex.addHaar_frontier volume htargetConvex
          calc
            volume body ≤ volume (closure targetSet) := measure_mono hbodySubset
            _ = volume targetSet := measure_closure_of_null_frontier hfrontier
        calc
          ENNReal.ofReal
                |LinearMap.det
                  (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)| *
              volume targetEnvelope ≤
            ENNReal.ofReal
                |LinearMap.det
                  (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)| *
              (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
                volume body) := by gcongr
          _ ≤ ENNReal.ofReal
                |LinearMap.det
                  (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)| *
              (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
                volume targetSet) := by gcongr
          _ = (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
                ENNReal.ofReal
                  |LinearMap.det
                    (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)|) *
              volume targetSet := by ring
      refine ⟨sourceEnvelope, hsourceEnvelopeConvex,
        hsourceEnvelopeVolume, ?_⟩
      intro targetIndex htargetContained sourcePoint hsourcePoint
      have htargetBodySubset :
          (target.body targetIndex).carrier ⊆ body := by
        intro point hpoint
        exact subset_closure
          ⟨htargetContained hpoint, htargetBound targetIndex hpoint⟩
      have hcenterBody : center targetIndex ∈ body :=
        htargetBodySubset (hcenter targetIndex)
      have himageHomothetic : equivalence sourcePoint ∈
          AffineMap.homothety (center targetIndex) factor '' body :=
        Set.image_mono htargetBodySubset
          (hcarrier targetIndex ⟨sourcePoint, hsourcePoint, rfl⟩)
      have himage : equivalence sourcePoint ∈ targetEnvelope :=
        htargetEnvelope (center targetIndex) hcenterBody himageHomothetic
      exact ⟨equivalence sourcePoint, himage,
        equivalence.symm_apply_apply sourcePoint⟩
    · refine ⟨(∅ : Set Point3), convex_empty, by simp, ?_⟩
      intro targetIndex htarget
      exact (heligible ⟨targetIndex, htarget⟩).elim
  · exact hsource

end Kakeya.Assouad

end
