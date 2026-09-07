import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralDistinctnessTransferStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLongitudinalCompressionLineDistanceHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLongitudinalCompressionLineDistanceAxisHelpers

/-! # Line-distance monotonicity under literal longitudinal compression -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_longitudinal_compression_lineDistance :
    WZ2PaperLongitudinalCompressionLineDistanceStatement := by
  intro historicalScale literalScale historicalFirst historicalSecond
    literalFirst literalSecond hHistoricalFirst hHistoricalSecond
    hLiteralFirst hLiteralSecond haxisFirst haxisSecond
  have hpositionFirst :
      wz1TubeAxisZeroPoint literalFirst =
        wz1TubeAxisZeroPoint historicalFirst :=
    longitudinalCompression_zeroPoint_eq
      hHistoricalFirst hLiteralFirst haxisFirst
  have hpositionSecond :
      wz1TubeAxisZeroPoint literalSecond =
        wz1TubeAxisZeroPoint historicalSecond :=
    longitudinalCompression_zeroPoint_eq
      hHistoricalSecond hLiteralSecond haxisSecond
  have hdistance :
      dist
          (wz1TubeAxisZeroPoint literalFirst)
          (wz1TubeAxisZeroPoint literalSecond) =
        dist
          (wz1TubeAxisZeroPoint historicalFirst)
          (wz1TubeAxisZeroPoint historicalSecond) := by
    rw [hpositionFirst, hpositionSecond]
  have hdirectionFirst :
      wz1PaperDirection literalFirst =
        NormedSpace.normalize
          (wz2PaperLongitudinalCompression
            (wz1PaperDirection historicalFirst)) :=
    longitudinalCompression_direction_eq
      hHistoricalFirst hLiteralFirst haxisFirst
  have hdirectionSecond :
      wz1PaperDirection literalSecond =
        NormedSpace.normalize
          (wz2PaperLongitudinalCompression
            (wz1PaperDirection historicalSecond)) :=
    longitudinalCompression_direction_eq
      hHistoricalSecond hLiteralSecond haxisSecond
  have hboundFirst :
      ‖transversePart
          (wz1PaperProjectiveDirection
            (wz1PaperDirection historicalFirst))‖ ^ 2 ≤
        3 / 10000 :=
    longitudinalCompression_transverseBound
      hHistoricalFirst hLiteralFirst hdirectionFirst
  have hboundSecond :
      ‖transversePart
          (wz1PaperProjectiveDirection
            (wz1PaperDirection historicalSecond))‖ ^ 2 ≤
        3 / 10000 :=
    longitudinalCompression_transverseBound
      hHistoricalSecond hLiteralSecond hdirectionSecond
  let historicalDirectionFirst :=
    wz1PaperDirection historicalFirst
  let historicalDirectionSecond :=
    wz1PaperDirection historicalSecond
  let literalDirectionFirst :=
    wz1PaperDirection literalFirst
  let literalDirectionSecond :=
    wz1PaperDirection literalSecond
  have hHistoricalFirst_norm :
      ‖historicalDirectionFirst‖ = 1 :=
    wz1PaperDirection_norm historicalFirst
  have hHistoricalSecond_norm :
      ‖historicalDirectionSecond‖ = 1 :=
    wz1PaperDirection_norm historicalSecond
  have hHistoricalFirst_two :
      0 < historicalDirectionFirst 2 := by
    linarith [hHistoricalFirst.1]
  have hHistoricalSecond_two :
      0 < historicalDirectionSecond 2 := by
    linarith [hHistoricalSecond.1]
  have hLiteralFirst_two :
      0 < literalDirectionFirst 2 := by
    linarith [hLiteralFirst.1]
  have hLiteralSecond_two :
      0 < literalDirectionSecond 2 := by
    linarith [hLiteralSecond.1]
  have hangle :
      InnerProductGeometry.angle
          historicalDirectionFirst historicalDirectionSecond ≤
        InnerProductGeometry.angle
          literalDirectionFirst literalDirectionSecond :=
    longitudinalCompression_angleChain
      hHistoricalFirst_norm hHistoricalSecond_norm
      hHistoricalFirst_two hHistoricalSecond_two
      hLiteralFirst_two hLiteralSecond_two
      hdirectionFirst hdirectionSecond
      hboundFirst hboundSecond
  dsimp only [wz1PaperLineDistance]
  linarith [hdistance, hangle]

end Kakeya.Assouad

end
