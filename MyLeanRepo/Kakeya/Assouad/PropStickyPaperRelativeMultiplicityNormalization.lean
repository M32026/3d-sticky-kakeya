import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRelativeMultiplicityNormalizationStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyMultiplicityNormalization

/-! # Relative-scale multiplicity normalization -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_relative_multiplicity_normalization :
    WZ2PaperRelativeMultiplicityNormalizationStatement := by
  intro targetScale sigma strongLoss outputLoss hscale hscaleOne
    hStrongLoss hBudget sourceScale family shading hCap point
  have hLoss : strongLoss ≤ outputLoss := by
    linarith
  calc
    (shading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN targetScale
              (2 - sigma - strongLoss) *
            family.enncard :=
      hCap point
    _ ≤
        Kakeya.realRpowENN targetScale
              (2 - sigma - outputLoss) *
            family.enncard := by
      gcongr
      apply ENNReal.ofReal_mono
      exact
        Real.rpow_le_rpow_of_exponent_ge
          hscale hscaleOne (by linarith)

end Kakeya.Assouad

end
