import MyLeanRepo.Kakeya.Assouad.CriticalInputs
import MyLeanRepo.Kakeya.Cinematic.Definitions
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Explicit black-box inputs for WZ2 Theorem 5.2

These propositions mark the boundary between WZ2's internal reduction and
results imported from WZ1/CV/OSW/PYZ.  They are ordinary hypotheses, not
axioms.
-/

namespace Kakeya.Assouad

/-- Pairwise separation in the genuine cinematic `C²` metric. -/
public def IsCinematicDeltaSeparated
    (F : Kakeya.Cinematic.FiniteFunctionFamily) (delta : ℝ) : Prop :=
  ∀ ⦃f⦄, f ∈ F.carrier →
    ∀ ⦃g⦄, g ∈ F.carrier → f ≠ g → delta ≤ dist f g

/--
The fixed-constant Katz--Tao condition produced by the WZ2 Section 7
extraction, including the global cardinality bound needed above scale one.
-/
public def HasCinematicKatzTaoBound
    (F : Kakeya.Cinematic.FiniteFunctionFamily)
    (delta C : ℝ) : Prop :=
  (F.card : ℝ) ≤ C / delta ∧
    ∀ center : Kakeya.Cinematic.C2Function,
      ∀ r : ℝ, delta ≤ r → r ≤ 1 →
        ((F.carrier ∩ Kakeya.Cinematic.c2Ball center r).ncard : ℝ) ≤
          C * (r / delta)

/--
The current PYZ maximal estimate consumed in WZ2 Section 7.

The fixed constants `C_KT`, `lambda`, and `M` respectively absorb the
Katz--Tao extraction loss, graph-neighborhood dilation, and the absolute
two-jet normalization required by the paper theorem.  The value part of this
normalization also supplies the vertical range needed to globalize the strip
estimate.  The small-scale threshold is chosen from these uniform constants
before the concrete family.  The interface is frozen locally so WZ2 does not
import a moving or unproved PYZ target.
-/
def PYZInput : Prop :=
  ∀ K D C_KT lambda M : ℝ,
    1 ≤ K → 1 ≤ D → 1 ≤ C_KT → 1 ≤ lambda → 0 ≤ M →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta₀ : ℝ, 0 < delta₀ ∧
        delta₀ ≤ 1 / lambda ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ family : Set Kakeya.Cinematic.C2Function,
            Kakeya.Cinematic.IsCinematicFamily family K D →
            (∀ g ∈ family, ∀ x : Kakeya.Cinematic.UnitPoint,
              |g x| ≤ M ∧
                |g.firstDeriv x| ≤ M ∧
                |g.secondDeriv x| ≤ M) →
            ∀ F : Kakeya.Cinematic.FiniteFunctionFamily,
              F.carrier ⊆ family →
              IsCinematicDeltaSeparated F delta →
              HasCinematicKatzTaoBound F delta C_KT →
              MeasureTheory.eLpNorm
                  (Kakeya.Cinematic.multiplicity F (lambda * delta))
                  (3 / 2 : ENNReal) MeasureTheory.volume ≤
                ENNReal.ofReal (Real.rpow delta (-epsilon))

end Kakeya.Assouad
