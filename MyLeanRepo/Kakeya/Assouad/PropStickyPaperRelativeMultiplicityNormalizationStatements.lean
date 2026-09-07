import MyLeanRepo.Kakeya.Assouad.PropStickyStatements

/-!
# Relative-scale multiplicity normalization

For item (iv) of `prop: sticky`, the source fiber is still a family of
`delta`-tubes, while its relative multiplicity exponent is measured at the
dimensionless target scale `delta / rho`.  This scale must therefore be an
explicit argument rather than inferred from the source family's native tube
radius.
-/

noncomputable section

namespace Kakeya.Assouad

def WZ2PaperRelativeMultiplicityNormalizationStatement : Prop :=
  ∀ {targetScale sigma strongLoss outputLoss : ℝ},
    0 < targetScale →
    targetScale ≤ 1 →
    0 ≤ strongLoss →
    3 * strongLoss ≤ outputLoss →
    ∀ {sourceScale : ℝ},
      ∀ {family : Kakeya.Streamlined.TubeFamily sourceScale},
        ∀ {shading : WZ1PaperTubeShading family},
          (∀ point,
            (shading.pointMultiplicity point : ENNReal) ≤
              Kakeya.realRpowENN targetScale
                  (2 - sigma - strongLoss) *
                family.enncard) →
          ∀ point,
            (shading.pointMultiplicity point : ENNReal) ≤
              Kakeya.realRpowENN targetScale
                  (2 - sigma - outputLoss) *
                family.enncard

end Kakeya.Assouad

end
