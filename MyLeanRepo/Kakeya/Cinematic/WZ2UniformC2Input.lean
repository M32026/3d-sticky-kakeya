import MyLeanRepo.Kakeya.Cinematic.Definitions
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Absolute-two-jet-uniform PYZ export for WZ2

This is the corrected WZ2-facing boundary after the raw family-uniform
Theorem 1.7 API was disproved. The absolute jet bound is fixed before the
small-scale threshold and before the concrete family.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Cinematic

/--
The uniform cinematic maximal estimate consumed by the WZ2 workstream.

The constants `C_KT`, `lambda`, and `M` respectively control the fixed
Katz--Tao loss, graph-neighborhood dilation, and absolute two-jet
normalization. Their placement before `epsilon`, `delta₀`, and `family`
matches the application-level normalization available in WZ2.
-/
def WZ2UniformC2Input : Prop :=
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
              eLpNorm
                  (multiplicity F (lambda * delta))
                  (3 / 2 : ENNReal) MeasureTheory.volume ≤
                ENNReal.ofReal (Real.rpow delta (-epsilon))

end Kakeya.Cinematic
