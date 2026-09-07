import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Extremal

/-!
# Pure WZ2 core statements

This module fixes the public form of WZ2 Theorem 5.2 and the critical-exponent
predicate used in its contradiction proof.  The theorem itself has no support
ball hypothesis.  The bounded Section 6 model is reached by a proved
localization and model-conversion step.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
The normalized, paper-facing WZ2 Theorem 5.2.

The all-scale hypothesis is literal Assouad Definition 2.12.  The theorem has
no historical uniform structure, assigned parent, or external proof input.
-/
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

/--
An exponent is admissible for the pure WZ2 contradiction when normalized
counterexamples with volume at most `delta ^ sigma` occur at arbitrarily
small scales and every requested structural loss.
-/
def PureWZ2Admissible (sigma : ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∀ delta₀ : ℝ, 0 < delta₀ →
      ∃ delta : ℝ,
        0 < delta ∧ delta ≤ delta₀ ∧ delta ≤ 1 ∧
        ∃ family : Kakeya.Streamlined.TubeFamily delta,
          ∃ shading : Kakeya.Streamlined.TubeShading family,
            family.Nonempty ∧
            WZ2PaperPureCWAAtNearbyScales family
              (Kakeya.realRpowENN delta (-eta)) ∧
            shading.IsLambdaDense
              (Kakeya.realRpowENN delta eta) ∧
            volume shading.union ≤
              Kakeya.realRpowENN delta sigma

/--
The pure Wolff lower bound needed to place the critical exponent below one.

This is the only mathematical conclusion of the Subunit/hairbrush route that
the pure WZ2 critical argument consumes.
-/
def PureWZ2WolffVolumeFloor : Prop :=
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
            Kakeya.realRpowENN delta (1 / 2 + epsilon) ≤
              volume shading.union

end Kakeya.Assouad

end
