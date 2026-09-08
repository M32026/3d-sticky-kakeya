import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.DilatedCommonChildGeometry
import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverGeometry

/-!
# Fixed-loss composition of surjective dilated tube covers

Suppose a fine family is assigned to a middle family through an
`A`-dilated cover, and the middle family is assigned to a coarser carried
family through an `E`-dilated cover.  Direct transitivity is unavailable
because the two homotheties have different centers.

The assigned fine tube is a common child witnessing both containments.
Common-child geometry therefore places its middle parent inside one fixed
dilation of the carried parent.  Enlarging once more absorbs the original
`A`-dilation of the middle parent.

The resulting cover is surjective with the composed parent map, and its
dilation depends only on `A` and `E`, not on runtime scales or families.
-/

noncomputable section

namespace Kakeya.Streamlined

/--
Two surjective dilated covers at ordered scales compose with one fixed
geometric dilation loss.
-/
def SurjectiveDilatedCoverCompositionStatement : Prop :=
  ∀ A E : ℝ, 1 ≤ A → 1 ≤ E →
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ {delta rho sigma : ℝ},
        0 < delta →
        delta ≤ rho →
        rho ≤ sigma →
        sigma ≤ 1 →
        ∀ {fine : TubeFamily delta},
          fine.IsInUnitBall →
        ∀ {middle : TubeFamily rho},
        ∀ {coarse : TubeFamily sigma},
        ∀ inner : DilatedTubeCover A fine middle,
        ∀ outer : DilatedTubeCover E middle coarse,
          Nonempty (DilatedTubeCover D fine coarse)

end Kakeya.Streamlined
