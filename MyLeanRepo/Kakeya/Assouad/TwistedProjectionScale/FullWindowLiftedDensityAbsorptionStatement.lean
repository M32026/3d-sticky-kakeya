import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SelectedScaleStatements

/-!
# Two-sided window clipping and density absorption

For an iterable Section 7 state the source shading lies in the full slope
window `z ∈ [-1,1]`.  Its `rho`-thickening may leave that window through both
boundary slabs:

* `[-1-rho,-1]`;
* `[1,1+rho]`.

A vertical radius-`rho` tube contributes at most `100 rho^3` in each slab.
Thus clipping costs at most `200 rho^3` per indexed lifted tube, and the
budget `ofReal (400 rho) * L ≤ lambda` leaves half of the raw density.
-/

namespace Kakeya.Assouad

/--
Clip an arbitrary lifted shading back to the full slope window and absorb the
two boundary caps into a genuine density on the same lifted family.
-/
def FullWindowLiftedDensityAbsorptionStatement : Prop :=
  ∀ {delta rho : ℝ},
    0 < rho →
    rho ≤ 1 / 8 →
    ∀ fine : Kakeya.Streamlined.TubeFamily delta,
      ∀ Y : Kakeya.Streamlined.TubeShading fine,
        IsInSlopeWindow Y →
        ∀ lifted : Kakeya.Streamlined.TubeFamily rho,
          IsInVerticalChart lifted →
          ∀ Z : Kakeya.Streamlined.TubeShading lifted,
            Z.union ⊆ Metric.cthickening rho Y.union →
            ∀ lambda L : ENNReal,
              lambda ≠ ⊤ →
              L ≠ 0 →
              L ≠ ⊤ →
              lambda * lifted.toBodyFamily.mass ≤ L * Z.mass →
              ENNReal.ofReal (400 * rho) * L ≤ lambda →
                let W := slabRestriction Z (-1) 1
                IsSubshading W Z ∧
                  IsInSlopeWindow W ∧
                  W.IsLambdaDense ((2 * L)⁻¹ * lambda) ∧
                  W.union ⊆ Metric.cthickening rho Y.union

end Kakeya.Assouad
