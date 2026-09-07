import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredTaylorQuadraticTransportInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredTaylorUniformFiniteGraphTransportInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.GlobalizationInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.UniformC2ShortCurveInput

/-!
# Uniform absolute-C2 globalization boundary

The centered-sixteenth estimate is applied after transporting every physical
cover interval to one fixed controlled interval.  The absolute two-jet bound
must therefore precede the common scale threshold and every transported
family.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Cinematic

/--
Uniform absolute-`C²` version of the full-unit-interval dyadic level-set
estimate.

This is the globalization output needed before the already-closed
level-set-to-integral and strip-covering arguments can produce
`WZ2UniformC2Input`.
-/
def WZ2UniformC2LocalLevelSetInput : Prop :=
  ∀ K D C_KT lambda M : ℝ,
    1 ≤ K → 1 ≤ D → 1 ≤ C_KT → 1 ≤ lambda → 0 ≤ M →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta₀ : ℝ, 0 < delta₀ ∧
        delta₀ ≤ 1 / lambda ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ family : Set C2Function,
            IsCinematicFamily family K D →
            HasUniformC2Bound family M →
            ∀ F : FiniteFunctionFamily,
              F.carrier ⊆ family →
              F.IsDeltaSeparated delta →
              F.HasKatzTaoBound delta C_KT →
              ∀ c : ℝ,
                ∀ mu : ℕ, 0 < mu →
                  ∀ E₀ : Set (ℝ × ℝ),
                    MeasurableSet E₀ →
                    E₀ ⊆ Set.Icc 0 1 ×ˢ Set.Icc c (c + 1) →
                    (∀ p ∈ E₀,
                      (mu : ℝ) ≤ multiplicity F (lambda * delta) p ∧
                        multiplicity F (lambda * delta) p < 2 * mu) →
                    volume E₀ ≤
                      ENNReal.ofReal
                        (Real.rpow delta (-epsilon) *
                          Real.rpow (mu : ℝ) (-3 / 2 : ℝ))

/--
Globalize the uniform short-curve estimate by the faithful centered Taylor
route.

The finite transport premise still consumes the strengthened quadratic
transport proposition explicitly.  This prevents the proof from selecting
one witness for graph transport and a different witness for the absolute
two-jet bound.  The endpoint hypotheses are kept explicit because the
existing absorption theorem is a caller of the two lower horizontal-stub
lemmas.
-/
def WZ2UniformC2LocalLevelSetFromTaylorGlobalizationStatement : Prop :=
  CenteredSixteenthIntervalCoverStatement →
    HorizontalGraphNeighborhoodVolumeStatement →
    HorizontalStubMultiplicityVolumeStatement →
    HorizontalStubLevelSetAbsorptionStatement →
    CenteredTaylorQuadraticCinematicTransportStatement →
    CenteredTaylorUniformFiniteGraphTransportStatement →
    WZ2UniformC2ShortCurveLevelSetInput →
    WZ2UniformC2LocalLevelSetInput

end Kakeya.Cinematic
