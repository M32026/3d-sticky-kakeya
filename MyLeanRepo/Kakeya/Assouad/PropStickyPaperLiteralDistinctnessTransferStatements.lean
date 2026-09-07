import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralHistoricalCorrespondenceStatements

/-!
# Essential distinctness under the literal-paper longitudinal compression

WZ Definition 5 uses the fixed map

> `(x₁, ..., xₙ) ↦ (c x₁ / rho, ..., c xₙ₋₁ / rho, c xₙ)`.

Relative to the historical target family already used by the stable CWA
infrastructure, the literal target family is obtained by compressing only the
third coordinate by `1 / 100`. The compression fixes the intersection of
every line with `z = 0`. On the actual `L₃` cone, its induced slope dilation
does not decrease the angle between positively oriented directions.

The two leaves below isolate that geometry and its finite-family consequence.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Longitudinal compression does not decrease the paper line metric when both
the source and image axes are represented by tubes in the fixed line class.
-/
def WZ2PaperLongitudinalCompressionLineDistanceStatement : Prop :=
  ∀ {historicalScale literalScale : ℝ},
    ∀ (historicalFirst historicalSecond :
        Kakeya.DeltaTube historicalScale),
      ∀ (literalFirst literalSecond :
          Kakeya.DeltaTube literalScale),
        WZ1PaperTubeInLineClass historicalFirst →
        WZ1PaperTubeInLineClass historicalSecond →
        WZ1PaperTubeInLineClass literalFirst →
        WZ1PaperTubeInLineClass literalSecond →
        tubeAxisLine literalFirst =
            wz2PaperLongitudinalCompression ''
              tubeAxisLine historicalFirst →
        tubeAxisLine literalSecond =
            wz2PaperLongitudinalCompression ''
              tubeAxisLine historicalSecond →
          wz1PaperLineDistance historicalFirst historicalSecond ≤
            wz1PaperLineDistance literalFirst literalSecond

/--
Transfer paper essential distinctness through an index equivalence and the
literal/historical axis correspondence.
-/
def WZ2PaperLiteralEssentialDistinctnessTransferStatement : Prop :=
  WZ2PaperLongitudinalCompressionLineDistanceStatement →
    ∀ {scale : ℝ},
      ∀ {historicalFamily :
          Kakeya.Streamlined.TubeFamily scale},
        ∀ {literalFamily :
            Kakeya.Streamlined.TubeFamily scale},
          ∀ (indexEquiv :
              Fin literalFamily.card ≃ Fin historicalFamily.card),
            WZ1PaperIsLineClass historicalFamily →
            WZ1PaperIsLineClass literalFamily →
            (∀ target,
              tubeAxisLine (literalFamily.tube target) =
                wz2PaperLongitudinalCompression ''
                  tubeAxisLine
                    (historicalFamily.tube (indexEquiv target))) →
            WZ1PaperIsEssentiallyDistinct historicalFamily →
              WZ1PaperIsEssentiallyDistinct literalFamily

end Kakeya.Assouad

end
