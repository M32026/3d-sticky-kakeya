import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberBand
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberBandParameterSelection
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridAtomization
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridParameterSelection
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberAtomizationToOS
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCellAreaUniformity
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCellMassUniformity
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSDensityAbsorption
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.Section7ProjectionRectangleGridCover

/-!
# Prepare the same-family projected-fiber OS refinement

This is the closed producer immediately before the local cinematic
globalization.  It selects the projected-fiber band and the large planar-grid
base, atomizes the band, applies weighted OS pruning, absorbs every loss into
the shading density, and retains the exact same-level planar cell-area data.
-/

noncomputable section

namespace Kakeya.Assouad

/--
The complete same-family projected refinement used by the local cinematic
continuation.

The global shading remains indexed by the original tube family.  The exact
support identity and all terminal-grid data are retained; in particular this
does not discard the OS uniformity after proving only a density statement.
-/
structure ProjectedFiberOSPreparationData
    {delta eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction) where
  base : ℕ
  base_ge_three : 3 ≤ base
  levels : ℕ
  mesh_lower :
    delta ≤ ((base ^ levels : ℝ)⁻¹)
  mesh_upper :
    ((base ^ levels : ℝ)⁻¹) <
      (base : ℝ) * delta
  atomic_mesh_lt :
    ((base ^ (levels + 1) : ℝ)⁻¹) < delta
  threshold : ENNReal
  levelCount : ℕ
  threshold_ne_zero : threshold ≠ 0
  threshold_ne_top : threshold ≠ ⊤
  bandData :
    ProjectedFiberBandData Y f threshold levelCount
  atomized :
    ProjectedFiberGridAtomizationData
      Y f bandData base levels
        (section7GridIndexBound base levels)
  uniform :
    ProjectedFiberOSUniformData
      Y f bandData base levels
        (section7GridIndexBound base levels) atomized
  density :
    ProjectedFiberOSDensityData
      (eta := eta) Y f bandData base levels
        (section7GridIndexBound base levels) atomized uniform
  cellMass :
    ProjectedFiberOSCellMassUniformityData
      Y f bandData base levels
        (section7GridIndexBound base levels) atomized uniform
  cellArea :
    ProjectedFiberOSCellAreaUniformityData
      Y f bandData base levels
        (section7GridIndexBound base levels) atomized uniform
  global_twisted_eq :
    twistedUnion density.globalShading f = uniform.retainedBand

/--
Assemble every completed projected-fiber leaf into the exact global
same-family preparation consumed by projection globalization.

The grid base is chosen after `eta` but before the fine scale `delta`.
This quantifier order is essential: the later Lemma 7.12 arithmetic absorbs
constants depending on the fixed grid base by shrinking the common
small-scale threshold.  The threshold, terminal depth, and concrete data are
still chosen only after the indexed family and shading are known.
-/
def ProjectedFiberOSPreparationStatement : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∃ base : ℕ,
      3 ≤ base ∧
      ∃ delta₀ : ℝ,
        0 < delta₀ ∧ delta₀ < 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            F.Nonempty →
            IsInVerticalChart F →
            (∀ i : Fin F.card,
              |(tubeParams i).a| ≤ 12 ∧
                |(tubeParams i).b| ≤ 12 ∧
                |(tubeParams i).c| ≤ 2 ∧
                |(tubeParams i).d| ≤ 2) →
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              Y.IsLambdaDense
                (Kakeya.realRpowENN delta eta) →
              Y.union ⊆ horizontalSlab 0 1 →
              ∀ f : SlopeFunction,
                f.IsNonsingular →
                f 0 = 0 →
                ∃ prepared :
                    ProjectedFiberOSPreparationData
                      (eta := eta) Y f,
                  prepared.base = base

end Kakeya.Assouad
