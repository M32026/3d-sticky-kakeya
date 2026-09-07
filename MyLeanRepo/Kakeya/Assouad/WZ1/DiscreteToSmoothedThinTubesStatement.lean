import MyLeanRepo.Kakeya.Assouad.WZ1.DiscreteThinTubes
import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothedMeasure.Basic

/-!
# Discrete exceptional relations as all-scale thin tubes

This is the finite-point replacement for thickening the paper's unions of
`delta`-squares before applying the OSW radial bootstrap.
-/

namespace Kakeya.Assouad

/--
Promote a discrete thin-tubes witness to an all-scale thin-tubes witness for
the corresponding smoothed probability measures.

The smoothing radius is `delta / 10`.  Delta separation makes the smoothing
cells disjoint, so the discrete good-pair fraction is retained without
changing `c`.  At radii below `delta`, the planar strip fraction inside one
smoothing ball supplies the missing factor of `r / delta`; for
`0 <= beta <= 1` this is bounded by `(r / delta)^beta`.  The absolute factor
`100` absorbs the cell geometry and the displacement of both source points.
-/
def WZ1DiscreteToSmoothedThinTubesStatement : Prop :=
  ∀ {delta beta K c : ℝ}
      (G₁ G₂ : DiscreteSet 2)
      (hG₁ : G₁.Nonempty) (hG₂ : G₂.Nonempty),
    ∀ hdelta : 0 < delta,
    beta ≤ 1 →
    G₁.IsDeltaSeparated delta →
    G₂.IsDeltaSeparated delta →
    HasDiscreteThinTubes delta beta K c G₁ G₂ →
      HasMeasureThinTubes beta (100 * K) c
        (smoothMeasure G₁ hG₁ (delta / 10) (by linarith))
        (smoothMeasure G₂ hG₂ (delta / 10) (by linarith))

end Kakeya.Assouad
