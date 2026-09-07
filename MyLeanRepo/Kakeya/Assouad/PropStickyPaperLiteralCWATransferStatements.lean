import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralMapRelationStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyStatements

/-!
# Transfer normalized CWA to the literal-paper target family

The historical and literal target families are indexed by the same source
fiber.  Their axes differ only by the fixed longitudinal compression.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/--
Generic normalized Convex-Wolff transport through an index equivalence and
one common convex envelope for each target test set.
-/
def WZ2PaperIndexedConvexWolffTransferStatement : Prop :=
  ∀ {sourceScale targetScale : ℝ},
    ∀ {sourceFamily :
        Kakeya.Streamlined.TubeFamily sourceScale},
      ∀ {targetFamily :
          Kakeya.Streamlined.TubeFamily targetScale},
        ∀ {C envelopeConstant : ENNReal},
          ∀ (indexEquiv :
              Fin targetFamily.card ≃ Fin sourceFamily.card),
            (∀ targetConvexSet : Set Point3,
              Convex ℝ targetConvexSet →
              ∃ sourceConvexSet : Set Point3,
                Convex ℝ sourceConvexSet ∧
                volume sourceConvexSet ≤
                  envelopeConstant * volume targetConvexSet ∧
                ∀ target,
                  wz1PaperTubeCarrier
                        (targetFamily.tube target) ⊆
                      targetConvexSet →
                    wz1PaperTubeCarrier
                        (sourceFamily.tube (indexEquiv target)) ⊆
                      sourceConvexSet) →
            WZ2PaperConvexWolffBound sourceFamily C →
              WZ2PaperConvexWolffBound targetFamily
                (envelopeConstant * C)

/--
Longitudinal compression supplies a common old-family convex envelope with
fixed volume loss `100`.
-/
def WZ2PaperLongitudinalCompressionEnvelopeStatement : Prop :=
  ∀ {scale : ℝ},
    0 < scale →
    ∀ {historicalFamily :
        Kakeya.Streamlined.TubeFamily scale},
      ∀ {literalFamily :
          Kakeya.Streamlined.TubeFamily scale},
        ∀ (indexEquiv :
            Fin literalFamily.card ≃ Fin historicalFamily.card),
          (∀ target,
            tubeAxisLine (literalFamily.tube target) =
              wz2PaperLongitudinalCompression ''
                tubeAxisLine
                  (historicalFamily.tube (indexEquiv target))) →
          ∀ literalConvexSet : Set Point3,
            Convex ℝ literalConvexSet →
            ∃ historicalConvexSet : Set Point3,
              Convex ℝ historicalConvexSet ∧
              volume historicalConvexSet ≤
                (100 : ENNReal) * volume literalConvexSet ∧
              ∀ target,
                wz1PaperTubeCarrier
                      (literalFamily.tube target) ⊆
                    literalConvexSet →
                  wz1PaperTubeCarrier
                      (historicalFamily.tube (indexEquiv target)) ⊆
                    historicalConvexSet

/-- Conditional assembly of the two independent transfer leaves. -/
def WZ2PaperHistoricalToLiteralCWAStatement : Prop :=
  WZ2PaperIndexedConvexWolffTransferStatement →
    WZ2PaperLongitudinalCompressionEnvelopeStatement →
      ∀ {scale : ℝ},
        0 < scale →
        ∀ {historicalFamily :
            Kakeya.Streamlined.TubeFamily scale},
          ∀ {literalFamily :
              Kakeya.Streamlined.TubeFamily scale},
            ∀ (indexEquiv :
                Fin literalFamily.card ≃ Fin historicalFamily.card),
              (∀ target,
                tubeAxisLine (literalFamily.tube target) =
                  wz2PaperLongitudinalCompression ''
                    tubeAxisLine
                      (historicalFamily.tube
                        (indexEquiv target))) →
              ∀ {C : ENNReal},
                WZ2PaperConvexWolffBound historicalFamily C →
                  WZ2PaperConvexWolffBound literalFamily
                    ((100 : ENNReal) * C)

end Kakeya.Assouad

end
