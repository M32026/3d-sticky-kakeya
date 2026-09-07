import MyLeanRepo.Kakeya.Assouad.PropStickyStatements

/-! # Pure exponent normalization for paper multiplicity bounds -/

noncomputable section

namespace Kakeya.Assouad

def WZ2PropStickyPaperMultiplicityNormalizationStatement : Prop :=
  ∀ {delta sigma strongLoss outputLoss : ℝ},
    0 < delta → delta ≤ 1 →
    0 ≤ strongLoss →
    3 * strongLoss ≤ outputLoss →
    ∀ {family : Kakeya.Streamlined.TubeFamily delta},
      ∀ {shading : WZ1PaperTubeShading family},
        (∀ point,
          (shading.pointMultiplicity point : ENNReal) ≤
            Kakeya.realRpowENN delta
                (2 - sigma - strongLoss) *
              family.enncard) →
        ∀ point,
          (shading.pointMultiplicity point : ENNReal) ≤
            Kakeya.realRpowENN delta
                (2 - sigma - outputLoss) *
              family.enncard

end Kakeya.Assouad

end
