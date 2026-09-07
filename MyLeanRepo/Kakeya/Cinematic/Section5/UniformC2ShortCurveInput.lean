import MyLeanRepo.Kakeya.Cinematic.WZ2Input

/-!
# Uniform absolute-C2 short-curve interface

The family-dependent short-curve theorem chooses its scale threshold only
after the concrete family.  Taylor globalization instead creates a new family
for every later physical scale and cover interval.  The corrected interface
therefore fixes an absolute two-jet bound before the threshold and quantifies
over the concrete family afterwards.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Cinematic

/--
Uniform version of the centered-sixteenth level-set estimate from PYZ
Lemma 39.

The absolute bound `M` is fixed before `epsilon`, the small-scale threshold,
and the concrete family.  This is the quantifier order needed by centered
Taylor globalization.
-/
def WZ2UniformC2ShortCurveLevelSetInput : Prop :=
  ∀ K D C_KT lambda M : ℝ,
    1 ≤ K → 1 ≤ D → 1 ≤ C_KT → 1 ≤ lambda → 0 ≤ M →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta₀ : ℝ, 0 < delta₀ ∧
        delta₀ ≤ 1 / lambda ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ family : Set C2Function,
            IsCinematicFamily family K D →
            HasUniformC2Bound family M →
            ∀ I : ParameterInterval, I.IsControlled K →
              ∀ F : FiniteFunctionFamily,
                F.carrier ⊆ family →
                F.IsDeltaSeparated delta →
                F.HasKatzTaoBound delta C_KT →
                ∀ c : ℝ,
                  ∀ mu : ℕ, 0 < mu →
                    ∀ E₀ : Set (ℝ × ℝ),
                      MeasurableSet E₀ →
                      E₀ ⊆
                        I.realCenteredCarrier (1 / 16) ×ˢ
                          Set.Icc c (c + 1) →
                      (∀ p ∈ E₀,
                        (mu : ℝ) ≤ multiplicity F (lambda * delta) p ∧
                          multiplicity F (lambda * delta) p < 2 * mu) →
                      volume E₀ ≤
                        ENNReal.ofReal
                          (Real.rpow delta (-epsilon) *
                            Real.rpow (mu : ℝ) (-3 / 2 : ℝ))

end Kakeya.Cinematic
