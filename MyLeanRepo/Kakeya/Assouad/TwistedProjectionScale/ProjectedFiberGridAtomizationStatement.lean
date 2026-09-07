import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.PlanarGridPartitionTreeStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberBandStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.WeightedOSBranchingUniformRefinementStatement

/-!
# Terminal planar-grid atoms for a projected-fiber band

The continuous projected-fiber band is first cut into terminal planar grid
cells.  A single dyadic mass pigeonhole retains cells whose fiber-measure
masses are within a factor two.  Their centers form a separated finite set,
so the locally bounded planar partition tree and weighted OS refinement can
be applied in the next assembly step.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Center of the planar `base^(-level)` cell with integer index `idx`. -/
def planarGridCenter
    (base level : ℕ)
    (idx : ℤ × ℤ) : Point2 :=
  ((((idx.1 : ℝ) + 1 / 2) / (base ^ level : ℝ)) •
      EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
    ((((idx.2 : ℝ) + 1 / 2) / (base ^ level : ℝ)) •
      EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

/-- A finite box of candidate terminal grid centers. -/
def boundedPlanarGridCenters
    (base level indexBound : ℕ) : DiscreteSet 2 :=
  ((Finset.Icc (-(indexBound : ℤ)) (indexBound : ℤ)).product
      (Finset.Icc (-(indexBound : ℤ)) (indexBound : ℤ))).image
    (planarGridCenter base level)

/-- Portion of `band` in the terminal grid cell represented by `center`. -/
def projectedFiberGridAtom
    (band : Set Point2)
    (base level : ℕ)
    (center : Point2) : Set Point2 :=
  band ∩
    {q |
      planarGridIndex base level q =
        planarGridIndex base level center}

/-- Measure on the projection plane with density equal to fiber multiplicity. -/
def projectedFiberMeasure
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction) : Measure Point2 :=
  volume.withDensity (projectedFiberMultiplicity Y f)

/--
One terminal-grid atomization of a projected-fiber band.

The retained planar set is pulled back to the original indexed tube family.
The mass comparison is therefore a statement about the actual shaded mass,
not only about planar Lebesgue area or a point-sampling surrogate.
-/
structure ProjectedFiberGridAtomizationData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    {threshold : ENNReal}
    {levelCount : ℕ}
    (bandData : ProjectedFiberBandData Y f threshold levelCount)
    (base levels indexBound : ℕ) where
  centers : DiscreteSet 2
  centers_nonempty : centers.Nonempty
  centers_subset :
    centers ⊆ boundedPlanarGridCenters base levels indexBound
  centers_separated :
    centers.IsDeltaSeparated
      ((base ^ levels : ℝ)⁻¹)
  atom_measurable :
    ∀ center ∈ centers,
      MeasurableSet
        (projectedFiberGridAtom
          bandData.band base levels center)
  atom_disjoint :
    ∀ center₁ ∈ centers, ∀ center₂ ∈ centers,
      center₁ ≠ center₂ →
        Disjoint
          (projectedFiberGridAtom
            bandData.band base levels center₁)
          (projectedFiberGridAtom
            bandData.band base levels center₂)
  atom_mass_pos :
    ∀ center ∈ centers,
      projectedFiberMeasure Y f
        (projectedFiberGridAtom
          bandData.band base levels center) ≠ 0
  atom_mass_ne_top :
    ∀ center ∈ centers,
      projectedFiberMeasure Y f
        (projectedFiberGridAtom
          bandData.band base levels center) ≠ ⊤
  atom_mass_comparable :
    ∀ center₁ ∈ centers, ∀ center₂ ∈ centers,
      projectedFiberMeasure Y f
          (projectedFiberGridAtom
            bandData.band base levels center₁) ≤
        2 *
          projectedFiberMeasure Y f
            (projectedFiberGridAtom
              bandData.band base levels center₂)
  retainedBand : Set Point2
  retainedBand_eq :
    retainedBand =
      finiteAtomUnion centers
        (projectedFiberGridAtom bandData.band base levels)
  retainedBand_measurable : MeasurableSet retainedBand
  retainedBand_subset : retainedBand ⊆ bandData.band
  shading : Kakeya.Streamlined.TubeShading F
  shading_eq :
    shading =
      projectionPullbackShading
        Y f retainedBand retainedBand_measurable
  subshading : IsSubshading shading bandData.shading
  mass_identity :
    shading.mass =
      projectedFiberMeasure Y f retainedBand
  mass_retention :
    bandData.shading.mass ≤
      ((2 *
          (Nat.log 2
            (2 *
              (boundedPlanarGridCenters
                base levels indexBound).card) +
            1) : ℕ) : ENNReal) *
        shading.mass
  twisted_subset :
    twistedUnion shading f ⊆ retainedBand

/--
Atomize a projected-fiber band inside a finite terminal-grid box.

The explicit cover premise is the geometric boundary: a later closed lemma
will instantiate `indexBound` from
`bandData.band_subset_rectangle`.  This target performs the nontrivial
measure pigeonholing and same-family pullback, but does not assume the
weighted OS theorem or any open target.
-/
def ProjectedFiberGridAtomizationStatement : Prop :=
  ProjectedFiberMassStatement →
    ProjectedFiberPullbackMassStatement →
      ∀ {delta : ℝ},
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            ∀ f : SlopeFunction,
              ∀ {threshold : ENNReal},
                ∀ {levelCount : ℕ},
                  ∀ bandData :
                      ProjectedFiberBandData
                        Y f threshold levelCount,
                    bandData.shading.mass ≠ 0 →
                    bandData.shading.mass ≠ ⊤ →
                    ∀ base levels indexBound : ℕ,
                      3 ≤ base →
                      bandData.band ⊆
                        finiteAtomUnion
                          (boundedPlanarGridCenters
                            base levels indexBound)
                          (projectedFiberGridAtom
                            bandData.band base levels) →
                      Nonempty
                        (ProjectedFiberGridAtomizationData
                          Y f bandData base levels indexBound)

end Kakeya.Assouad
