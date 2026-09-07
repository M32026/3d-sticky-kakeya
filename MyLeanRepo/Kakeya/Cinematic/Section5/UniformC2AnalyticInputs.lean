import MyLeanRepo.Kakeya.Cinematic.Section5.UniformC2GlobalizationInputs
import MyLeanRepo.Kakeya.Cinematic.WZ2UniformC2Input

/-!
# Uniform absolute-C2 analytic interfaces

These propositions retain the absolute two-jet bound before the common scale
threshold while separating the full-interval level-set estimate from its
purely analytic integral and global-norm consequences.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Cinematic

/--
Uniform absolute-`C²` local integral estimate.

The concrete family is quantified only after the common threshold. This is
the integral counterpart of `WZ2UniformC2LocalLevelSetInput`.
-/
def WZ2UniformC2LocalIntegralInput : Prop :=
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
                (∫ p in (Set.Icc 0 1 ×ˢ Set.Icc c (c + 1)),
                  Real.rpow (multiplicity F (lambda * delta) p)
                    (3 / 2 : ℝ)) ≤
                  Real.rpow delta (-epsilon)

end Kakeya.Cinematic
