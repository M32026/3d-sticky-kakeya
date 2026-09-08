import MyLeanRepo.Kakeya.Streamlined.RhoTubeMultiplicity.InducedShading
import MyLeanRepo.Kakeya.Streamlined.Section5CubicalRepair.DilatedFullFiberFactoringAdapter

/-!
# Thickened fiber mass for actual dilated parent bodies

This is the paper-facing geometric core behind the lower-multiplicity witness
in the full-containment Section 5 argument.  The coarse bodies are the actual
fixed dilations of geometric `rho`-tubes; they are not reinterpreted as strict
unit-length `rho`-tube carriers.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/--
For an exact induced shading over actual dilated `rho`-tube parents, the sum
of the full `rho`-thickenings of all fiber shaded unions is controlled by the
induced coarse shading mass.
-/
def DilatedExactInducedThickenedFiberMassStatement : Prop :=
  ∀ {A : ℝ}, 1 ≤ A →
    ∀ {rho : ℝ}, 0 < rho →
      ∀ {fine coarse : BodyFamily},
        ∀ (P : Factoring fine coarse),
          ∀ (Y : Shading fine),
            ∀ (Z : Shading coarse),
              (∀ j, ∃ T : Kakeya.DeltaTube rho,
                (coarse.body j).carrier = dilatedTubeCarrier A T) →
              P.IsExactInducedShading Y Z rho →
                (∑ j : Fin coarse.card,
                    volume
                      (Metric.cthickening rho
                        (P.fiberShadedUnion Y j))) ≤
                  4096 * Z.mass

end Kakeya.Streamlined
