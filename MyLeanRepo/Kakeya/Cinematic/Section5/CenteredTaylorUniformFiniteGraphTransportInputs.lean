import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredTaylorFiniteGraphTransportInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredTaylorQuadraticTransportInputs

/-!
# Uniform finite centered Taylor transport input

This proposition freezes the same-witness bridge needed by uniform-`C²`
globalization.  The quadratic-certified Taylor witness must carry both the
established finite graph-transport package and the transported absolute
two-jet bound.
-/

noncomputable section

namespace Kakeya.Cinematic

def CenteredTaylorUniformFiniteGraphTransportStatement : Prop :=
  CenteredTaylorQuadraticCinematicTransportStatement →
    ∀ K D C_KT lambda M : ℝ,
      1 ≤ K →
      1 ≤ D →
      1 ≤ C_KT →
      1 ≤ lambda →
      0 ≤ M →
      ∀ family : Set C2Function,
        IsCinematicFamily family K D →
        HasUniformC2Bound family M →
        ∀ I : ParameterInterval,
          0 < I.length →
          I.IsShort (12 * K) →
          ∀ delta : ℝ,
            0 < delta →
            4 * (lambda * delta) ≤ I.length →
            ∀ F : FiniteFunctionFamily,
              F.carrier ⊆ family →
              F.IsDeltaSeparated delta →
              F.HasKatzTaoBound delta C_KT →
              ∃ transport : C2Function → C2Function,
                CenteredTaylorFiniteGraphTransportData
                    K D C_KT lambda family I delta F transport ∧
                  HasUniformC2Bound (transport '' family) (2 * M) ∧
                  ∀ f ∈ family,
                    IsCenteredQuadraticJetExtension I f (transport f)

end Kakeya.Cinematic
