import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions

/-!
# Final C2 grain normalization boundary

This lightweight module isolates the WZ1 Proposition 21 normalization
statement from the CV-dependent planiness statements.
-/

namespace Kakeya.Assouad

/--
Final mild-rescaling and normalization step in WZ1 Proposition 21.

For a requested output scale threshold, choose a sufficiently small source
threshold. Every raw Proposition 27 output below that source threshold can
then be transported to a final WZ1 package below the requested threshold.

The source slope is only known to have power-size value and first/second
derivative bounds.  This theorem performs the paper's vertical rescaling and
is the first place where `SlopeFunction.IsNormalized` may be concluded.
-/
def WZ1C2GrainNormalizationStatement : Prop :=
  ∀ sigma outputLoss targetDelta₀ : ℝ,
    0 < sigma → sigma < 1 →
    0 < outputLoss → 0 < targetDelta₀ →
      ∃ sourceDelta₀ : ℝ, 0 < sourceDelta₀ ∧
        ∀ {delta inputLoss A : ℝ},
          0 < delta → delta ≤ sourceDelta₀ →
          ∀ source :
              WZ1PlaninessGraininessPackage
                sigma inputLoss delta,
            ∀ nested :
                WZ1MultiscaleSlopeCorrectionPackage
                  source outputLoss,
              ∀ raw :
                  WZ1RawGlobalGrainData
                    nested.shading sigma source.constant
                    nested.rawLoss A,
                ∃ finalDelta : ℝ,
                  0 < finalDelta ∧ finalDelta ≤ targetDelta₀ ∧
                    Nonempty
                      (WZ1C2GrainPackage
                        sigma outputLoss finalDelta)

end Kakeya.Assouad
