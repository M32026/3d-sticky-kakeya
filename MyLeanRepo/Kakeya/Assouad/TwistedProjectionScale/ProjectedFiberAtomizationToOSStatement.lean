import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridAtomizationStatement

/-!
# From projected-fiber grid atoms to a locally uniform subtree

The atomization producer supplies comparable terminal atom masses and a
separated set of their grid centers.  Using one additional planar grid level
makes the terminal partition atomic with the strict mesh inequality required
by `PlanarGridPartitionTreeStatement`.  The weighted OS theorem can then prune
the center tree while retaining a genuine same-family pullback shading.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
The final projected-fiber refinement after exact local branching pruning.

The branching tree has `levels + 1` levels.  Its terminal mesh is one factor
`base` finer than the atom grid, which turns the atomization separation
`base^(-levels)` into the strict atomicity margin.
-/
structure ProjectedFiberOSUniformData
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
        Y f bandData base levels indexBound) where
  centers : DiscreteSet 2
  centers_nonempty : centers.Nonempty
  centers_subset : centers ⊆ atomized.centers
  retainedBand : Set Point2
  retainedBand_eq :
    retainedBand =
      finiteAtomUnion centers
        (projectedFiberGridAtom bandData.band base levels)
  retainedBand_measurable : MeasurableSet retainedBand
  retainedBand_subset :
    retainedBand ⊆ atomized.retainedBand
  shading : Kakeya.Streamlined.TubeShading F
  shading_eq :
    shading =
      projectionPullbackShading
        Y f retainedBand retainedBand_measurable
  subshading : IsSubshading shading atomized.shading
  mass_identity :
    shading.mass =
      projectedFiberMeasure Y f retainedBand
  os_mass_retention :
    atomized.shading.mass ≤
      (2 : ENNReal) *
          ((((2 *
              (Nat.log 2 ((base + 1) ^ 2) + 1)) ^
            (levels + 1) : ℕ)) : ENNReal) *
        shading.mass
  total_mass_retention :
    bandData.shading.mass ≤
      ((2 *
          (Nat.log 2
            (2 *
              (boundedPlanarGridCenters
                base levels indexBound).card) +
            1) : ℕ) : ENNReal) *
        ((2 : ENNReal) *
          ((((2 *
              (Nat.log 2 ((base + 1) ^ 2) + 1)) ^
            (levels + 1) : ℕ)) : ENNReal)) *
        shading.mass
  twisted_subset :
    twistedUnion shading f ⊆ retainedBand
  branchExponent : Fin (levels + 1) → ℕ
  branch_bound :
    ∀ level : Fin (levels + 1),
      2 ^ branchExponent level ≤ (base + 1) ^ 2
  exact_branching :
    ∀ level : Fin (levels + 1),
      ∀ parent ∈ planarGridPartition base level atomized.centers,
        (centers ∩ parent).Nonempty →
          (occupiedPartitionChildren
            centers
            (fun k => planarGridPartition base k atomized.centers)
            level parent).card =
              2 ^ branchExponent level

/--
Compose terminal projected-fiber atomization with the locally bounded planar
partition tree and the measure-weighted OS pruning theorem.

No new analytic input is assumed.  The only scale condition is `3 ≤ base`,
which supplies both the planar child bound and the strict terminal atomicity
margin at level `levels + 1`.
-/
def ProjectedFiberAtomizationToOSStatement : Prop :=
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
                    Nonempty
                      (ProjectedFiberOSUniformData
                        Y f bandData
                        base levels indexBound atomized)

end Kakeya.Assouad
