import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberBandMeasureAreaComparisonStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCellMassUniformityStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberPullbackSupportStatement

/-!
# Planar cell-area uniformity after projected-fiber OS branching

The retained projected-fiber density lies in one dyadic factor-two band.
Combining this density comparison with factor-two uniformity of projected
cell masses gives factor-four uniformity of the actual planar cell areas.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
The exact planar support and same-level area comparison consumed by the
local-to-global cinematic continuation.
-/
structure ProjectedFiberOSCellAreaUniformityData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    {threshold : ENNReal}
    {levelCount : ℕ}
    (bandData : ProjectedFiberBandData Y f threshold levelCount)
    (base levels indexBound : ℕ)
    (atomized :
      ProjectedFiberGridAtomizationData
        Y f bandData base levels indexBound)
    (uniform :
      ProjectedFiberOSUniformData
        Y f bandData base levels indexBound atomized) where
  twisted_eq :
    twistedUnion uniform.shading f = uniform.retainedBand
  cellBand_area_nonzero :
    ∀ level : ℕ, level ≤ levels + 1 →
      ∀ cell ∈ planarGridPartition base level atomized.centers,
        (uniform.centers ∩ cell).Nonempty →
          volume
              (projectedFiberOSCellBand
                Y f bandData base levels uniform.centers cell) ≠ 0
  cellBand_area_ne_top :
    ∀ level : ℕ, level ≤ levels + 1 →
      ∀ cell ∈ planarGridPartition base level atomized.centers,
        volume
            (projectedFiberOSCellBand
              Y f bandData base levels uniform.centers cell) ≠ ⊤
  cell_area_comparable :
    ∀ level : ℕ, level ≤ levels + 1 →
      ∀ cell₁ ∈ planarGridPartition base level atomized.centers,
        (uniform.centers ∩ cell₁).Nonempty →
          ∀ cell₂ ∈ planarGridPartition base level atomized.centers,
            (uniform.centers ∩ cell₂).Nonempty →
              volume
                  (projectedFiberOSCellBand
                    Y f bandData base levels uniform.centers cell₁) ≤
                4 *
                  volume
                    (projectedFiberOSCellBand
                      Y f bandData base levels uniform.centers cell₂)

/--
Convert projected cell-mass uniformity into actual planar cell-area
uniformity and identify the retained planar set with the final twisted union.

No new pruning is performed.  The factor four is exactly the product of the
factor-two terminal density band and the factor-two projected cell-mass
comparison.
-/
def ProjectedFiberOSCellAreaUniformityStatement : Prop :=
  ProjectedFiberPullbackSupportStatement →
    ProjectedFiberBandMeasureAreaComparisonStatement →
      ∀ {delta : ℝ},
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            ∀ f : SlopeFunction,
              ∀ {threshold : ENNReal},
                threshold ≠ 0 →
                threshold ≠ ⊤ →
                  ∀ {levelCount : ℕ},
                    ∀ bandData :
                        ProjectedFiberBandData
                          Y f threshold levelCount,
                      ∀ base levels indexBound : ℕ,
                        ∀ atomized :
                            ProjectedFiberGridAtomizationData
                              Y f bandData base levels indexBound,
                          ∀ uniform :
                              ProjectedFiberOSUniformData
                                Y f bandData
                                base levels indexBound atomized,
                            ∀ cellMass :
                                ProjectedFiberOSCellMassUniformityData
                                  Y f bandData
                                  base levels indexBound atomized uniform,
                              Nonempty
                                (ProjectedFiberOSCellAreaUniformityData
                                  Y f bandData
                                  base levels indexBound atomized uniform)

end Kakeya.Assouad
