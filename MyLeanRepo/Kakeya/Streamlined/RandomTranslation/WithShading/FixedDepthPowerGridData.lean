import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.ScaleInterpolation
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.GridLabelMaps
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.FixedDepthPowerGrid

/-!
# Fixed-depth power-grid production data

GWZ Theorem 7.3 first fixes a finite depth `N` and only then chooses the
small scale.  The grid is `rho_k = delta^(k/N)`, not a dyadic chain whose
length grows like `log(1/delta)`.

The dependency-light numerical structure lives in `FixedDepthPowerGrid`.
This compatibility module adds the exact `MultiscaleShiftData` and
`GridLabelMaps` package used by the historical strict-input construction.
-/

noncomputable section

open Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/--
After fixing `N`, sufficiently small `delta` admits the paper power grid and
a positive suffix-summable tail schedule.  Arbitrary shifts bounded by that
schedule then produce the exact flat multiscale data and production label
maps.
-/
def FixedDepthPowerGridDataStatement : Prop :=
  ∀ N : ℕ, 0 < N →
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ < 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∃ grid : FixedDepthPowerGrid delta N,
          ∀ {F : TubeFamily delta},
          ∀ {U : UniformTubeStructure F},
          ∀ {Y : TubeShading F},
          ∀ J : Fin N → ℕ,
            (∀ k, 0 < J k) →
          ∀ shiftAt : (k : Fin N) → Fin (J k) → Point3,
            (∀ k j, ‖shiftAt k j‖ ≤ grid.radius k) →
            ∃ (data : MultiscaleShiftData delta N)
              (gm : GridLabelMaps U Y data),
              data.sigma = grid.fineScale ∧
              data.J = J ∧
              HEq data.shiftAt shiftAt ∧
              data.radius = grid.radius ∧
              gm.fineScale = grid.fineScale ∧
              gm.coarseScale = grid.coarseScale

end Kakeya.Streamlined.RandomTranslation.WithShading

end
