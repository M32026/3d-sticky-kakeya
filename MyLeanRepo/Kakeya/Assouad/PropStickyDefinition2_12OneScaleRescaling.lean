import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingProducer
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescaledFamily
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# One-scale bridge from actual Assouad images to public ordinary targets

For one pure Definition 2.12 scale witness and one parent:

1. enumerate the complete strict full fiber as a genuine source `TubeFamily`;
2. build the Section 6 literal target family on exactly those indices;
3. identify its source-indexed actual outer-John bodies with the canonical
   `BodyFamily` stored by Definition 2.12;
4. apply the proved Assouad-to-WZ rescaling certificate;
5. obtain an ordinary public target family satisfying Convex-Wolff counting.

No subfiber is selected.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The complete strict ordinary full fiber as a tube family. -/
def wz2PaperPureFullFiberSubfamily
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) :
    Kakeya.Streamlined.TubeSubfamily fine :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset fine
    (wz2PaperOrdinaryFullFiberIndices fine coarse parent)

@[simp] theorem wz2PaperPureFullFiberSubfamily_card
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) :
    (wz2PaperPureFullFiberSubfamily fine coarse parent).family.card =
      (wz2PaperOrdinaryFullFiberIndices fine coarse parent).card :=
  rfl

@[simp] theorem wz2PaperPureFullFiberSubfamily_embedding
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card)
    (source :
      Fin (wz2PaperPureFullFiberSubfamily fine coarse parent).family.card) :
    (wz2PaperPureFullFiberSubfamily fine coarse parent).embedding source =
      ((wz2PaperOrdinaryFullFiberIndexEquiv parent) source).1 := by
  rfl

theorem WZ2PaperAssouadUnitRescalingData.unique
    {rho : ℝ} {parent : Kakeya.DeltaTube rho}
    (first second : WZ2PaperAssouadUnitRescalingData parent) :
    first = second := by
  cases first
  cases second
  congr

/-- One literal target family, its synchronized ordinary public enlargement,
and the public CWA inherited from the canonical actual John images. -/
structure WZ2PaperPureOneScaleRescalingBridge
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (hrho : 0 < rho)
    (C : ENNReal) where
  literal :
    WZ2PaperLiteralUnitRescaledFamilyData
      (wz2PaperPureFullFiberSubfamily fine coarse parent).family
      (coarse.tube parent) hrho
  bridge :
    WZ2PaperAssouadToLiteralRescalingCertificate
      hrho
      (WZ2PaperAssouadUnitRescalingData.ofTube
        (coarse.tube parent) hrho)
      literal 4000000
  public_convex_wolff :
    WZ2PaperBodyConvexWolffBound
      bridge.publicFamily.toBodyFamily
      ((4000000 : ENNReal) * C)

/-- Construct the one-scale public target from one pure scale witness. -/
noncomputable def WZ2PaperPureUnitRescaledFullFiberData.toPublicOneScale
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {parent : Fin coarse.card}
    {C : ENNReal}
    (data :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := coarse) parent C)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hfineLine : WZ1PaperIsLineClass fine)
    (hcoarseLine : WZ1PaperIsLineClass coarse)
    (hlineCover :
      ∀ source :
          Fin (wz2PaperPureFullFiberSubfamily
            fine coarse parent).family.card,
        WZ1PaperTubeCovers
          ((wz2PaperPureFullFiberSubfamily
            fine coarse parent).family.tube source)
          (coarse.tube parent)) :
    WZ2PaperPureOneScaleRescalingBridge
      (fine := fine) (coarse := coarse) parent hrho C := by
  let sourceFamily :=
    (wz2PaperPureFullFiberSubfamily fine coarse parent).family
  have hsourceLine : WZ1PaperIsLineClass sourceFamily :=
    hfineLine.subfamily
      (wz2PaperPureFullFiberSubfamily fine coarse parent)
  let literal :=
    Classical.choice
      (wz2_paper_literal_unit_rescaled_family
        wz2_paper_literal_canonical_unit_rescaled_tube
        hrho hrhoOne sourceFamily
        hsourceLine
        (coarse.tube parent)
        (hcoarseLine parent)
        hlineCover)
  let bridge :=
    wz2PaperAssouadToLiteralRescalingFixed
      hdelta hrho hrhoOne sourceFamily
      (coarse.tube parent) hlineCover literal
  have hnormalization :
      data.normalization =
        WZ2PaperAssouadUnitRescalingData.ofTube
          (coarse.tube parent) hrho :=
    data.normalization.unique _
  have hcanonicalCWA :
      WZ2PaperBodyConvexWolffBound
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := fine) (coarse := coarse) parent
          (WZ2PaperAssouadUnitRescalingData.ofTube
            (coarse.tube parent) hrho))
        C := by
    simpa only [hnormalization] using data.convex_wolff
  let indexEquiv :
      Fin literal.targetFamily.card ≃
        Fin
          (wz2PaperPureUnitRescaledFullFiberBodyFamily
            (fine := fine) (coarse := coarse) parent
            (WZ2PaperAssouadUnitRescalingData.ofTube
              (coarse.tube parent) hrho)).card :=
    Equiv.ofBijective
      literal.sourceIndex literal.sourceIndex_bijective
  have hbody :
      wz2PaperLiteralIndexedAssouadBodyFamily
          (WZ2PaperAssouadUnitRescalingData.ofTube
            (coarse.tube parent) hrho)
          literal =
        wz2PaperReindexedBodyFamily
          (wz2PaperPureUnitRescaledFullFiberBodyFamily
            (fine := fine) (coarse := coarse) parent
            (WZ2PaperAssouadUnitRescalingData.ofTube
              (coarse.tube parent) hrho))
          indexEquiv := by
    rfl
  refine
    {
      literal := literal
      bridge := bridge
      public_convex_wolff := ?_
    }
  apply bridge.public_convexWolff
  rw [hbody]
  exact
    (wz2PaperReindexedBodyFamily.convexWolffBound_iff
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := fine) (coarse := coarse) parent
        (WZ2PaperAssouadUnitRescalingData.ofTube
          (coarse.tube parent) hrho))
      indexEquiv C).2 hcanonicalCWA

end Kakeya.Assouad

end
