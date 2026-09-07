import Comparator.Statements.Definition2_12

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

def PureWZ2Theorem5_2Statement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ family : Kakeya.Streamlined.TubeFamily delta,
          family.Nonempty →
          WZ2PaperPureCWAAtNearbyScales family
            (Kakeya.realRpowENN delta (-eta)) →
          ∀ shading : Kakeya.Streamlined.TubeShading family,
            shading.IsLambdaDense
              (Kakeya.realRpowENN delta eta) →
            Kakeya.realRpowENN delta epsilon ≤
              volume shading.union

end Kakeya.Assouad
