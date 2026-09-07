import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingCellCardinalityStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberAtomizationToOSStatement

/-!
# Projected cell-mass uniformity after OS branching

Exact branching makes the number of retained terminal atoms below every
occupied cell independent of the cell at a fixed level.  Since terminal atom
masses were already pigeonholed into one factor-two band, the projected
measure of any two occupied cells at that level is comparable within factor
two.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Retained terminal atoms whose centers lie in one planar partition cell. -/
def projectedFiberOSCellBand
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    {threshold : ENNReal}
    {levelCount : ℕ}
    (bandData : ProjectedFiberBandData Y f threshold levelCount)
    (base levels : ℕ)
    (centers cell : DiscreteSet 2) : Set Point2 :=
  finiteAtomUnion (centers ∩ cell)
    (projectedFiberGridAtom bandData.band base levels)

/--
The cell-mass uniformity package consumed by projection globalization.

The measure is the fiber-integrated projected measure, so these are actual
same-family shaded masses after pullback, not cardinality surrogates.
-/
structure ProjectedFiberOSCellMassUniformityData
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
  cellBand_measurable :
    ∀ level : ℕ, level ≤ levels + 1 →
      ∀ cell ∈ planarGridPartition base level atomized.centers,
        MeasurableSet
          (projectedFiberOSCellBand
            Y f bandData base levels uniform.centers cell)
  cellBand_subset :
    ∀ level : ℕ, level ≤ levels + 1 →
      ∀ cell ∈ planarGridPartition base level atomized.centers,
        projectedFiberOSCellBand
            Y f bandData base levels uniform.centers cell ⊆
          uniform.retainedBand
  cellBand_nonzero :
    ∀ level : ℕ, level ≤ levels + 1 →
      ∀ cell ∈ planarGridPartition base level atomized.centers,
        (uniform.centers ∩ cell).Nonempty →
          projectedFiberMeasure Y f
              (projectedFiberOSCellBand
                Y f bandData base levels uniform.centers cell) ≠ 0
  cellBand_ne_top :
    ∀ level : ℕ, level ≤ levels + 1 →
      ∀ cell ∈ planarGridPartition base level atomized.centers,
        projectedFiberMeasure Y f
            (projectedFiberOSCellBand
              Y f bandData base levels uniform.centers cell) ≠ ⊤
  cell_mass_comparable :
    ∀ level : ℕ, level ≤ levels + 1 →
      ∀ cell₁ ∈ planarGridPartition base level atomized.centers,
        (uniform.centers ∩ cell₁).Nonempty →
          ∀ cell₂ ∈ planarGridPartition base level atomized.centers,
            (uniform.centers ∩ cell₂).Nonempty →
              projectedFiberMeasure Y f
                  (projectedFiberOSCellBand
                    Y f bandData base levels uniform.centers cell₁) ≤
                2 *
                  projectedFiberMeasure Y f
                    (projectedFiberOSCellBand
                      Y f bandData base levels uniform.centers cell₂)

/--
Upgrade the exact OS branching output to genuine same-level projected
cell-mass comparability.

No additional pruning or loss is allowed here.  The proof combines equal
retained leaf cardinalities with the already stored terminal atom
measurability, disjointness, positivity, finiteness, and factor-two mass
comparison.
-/
def ProjectedFiberOSCellMassUniformityStatement : Prop :=
  OSBranchingCellCardinalityStatement →
    ∀ {delta : ℝ},
      ∀ F : Kakeya.Streamlined.TubeFamily delta,
        ∀ Y : Kakeya.Streamlined.TubeShading F,
          ∀ f : SlopeFunction,
            ∀ {threshold : ENNReal},
              ∀ {levelCount : ℕ},
                ∀ bandData :
                    ProjectedFiberBandData
                      Y f threshold levelCount,
                  ∀ base levels indexBound : ℕ,
                    3 ≤ base →
                      ∀ atomized :
                          ProjectedFiberGridAtomizationData
                            Y f bandData base levels indexBound,
                        ∀ uniform :
                            ProjectedFiberOSUniformData
                              Y f bandData
                              base levels indexBound atomized,
                          Nonempty
                            (ProjectedFiberOSCellMassUniformityData
                              Y f bandData
                              base levels indexBound atomized uniform)

end Kakeya.Assouad
