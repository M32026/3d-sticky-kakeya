import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains

/-!
# Quantitative construction data behind the paper-facing grain statement

Proposition 6.3 only states the global/local grain conclusions.  Its proof,
and the Proposition 6.4 iteration which consumes it, retain three additional
facts on the same configuration: the critical volume floor, the vertical
component bound for the chosen plane map, and the chart bound for the chosen
global slope.  They are construction provenance rather than extra conjuncts
of the public Proposition 6.3 statement, so they live in this dependent
wrapper.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The chart-normalized global grain used internally by Proposition 6.4.
The parent is exactly the paper-facing Proposition 6.3 global grain; the
extra field records the bounded chart representative constructed in its
proof. -/
structure PureWZ2BoundedLipschitzGlobalGrainData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (sigma : ℝ) (C : ENNReal) extends
      PureWZ2LipschitzGlobalGrainData shading sigma C where
  f_bound : ∀ z : PureWZ2UnitInterval, |f z| ≤ 3

namespace PureWZ2BoundedLipschitzGlobalGrainData

/-- Attach a construction-level chart bound to an existing paper-facing
global grain without changing its slope or AD witness. -/
noncomputable def ofSlopeBound
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (data : PureWZ2LipschitzGlobalGrainData shading sigma C)
    (slope_bound : ∀ z : ℝ, z ∈ Set.Icc (-1 : ℝ) 1 →
      |data.slope z| ≤ 3) :
    PureWZ2BoundedLipschitzGlobalGrainData shading sigma C where
  toPureWZ2LipschitzGlobalGrainData := data
  f_bound := by
    intro z
    simpa [PureWZ2LipschitzGlobalGrainData.slope_eq_f]
      using slope_bound z.1 z.2

/-- Ambient form of the chart bound, using the same clamped extension as the
paper-facing global grain. -/
theorem slope_global_bound
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (data : PureWZ2BoundedLipschitzGlobalGrainData shading sigma C) :
    ∀ z : ℝ, |data.slope z| ≤ 3 := by
  intro z
  exact data.f_bound (PureWZ2LipschitzGlobalGrainData.clampHeight z)

theorem slope_bound
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (data : PureWZ2BoundedLipschitzGlobalGrainData shading sigma C)
    (z : ℝ) (_hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    |data.slope z| ≤ 3 :=
  data.slope_global_bound z

end PureWZ2BoundedLipschitzGlobalGrainData

instance {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal} :
    Coe (PureWZ2BoundedLipschitzGlobalGrainData shading sigma C)
      (PureWZ2LipschitzGlobalGrainData shading sigma C) :=
  ⟨PureWZ2BoundedLipschitzGlobalGrainData.toPureWZ2LipschitzGlobalGrainData⟩

/-- A paper-facing grain configuration together with the quantitative
certificates used internally by the Proposition 6.4 hierarchy.  All fields
share literal dependent indices; this is not part of the public Node 4 ABI. -/
structure PureWZ2QuantitativeGrainConfiguration
    (sigma loss delta : ℝ) where
  family : Kakeya.Streamlined.TubeFamily delta
  shading : WZ1PaperTubeShading family
  line_class : WZ1PaperIsLineClass family
  cubical : WZ1PaperIsCubicalShading shading
  extremal : WZ2PaperCroppedIsExtremal sigma loss family shading
  top_level_cwa : WZ2PaperConvexWolffBound family
    (Kakeya.realRpowENN delta (-loss))
  volume_lower :
    Kakeya.realRpowENN delta (sigma + loss) ≤ volume shading.union
  globalGrains : PureWZ2BoundedLipschitzGlobalGrainData shading sigma
    (Kakeya.realRpowENN delta (-loss))
  localGrains : PureWZ2LocalGrainData shading sigma
    (Kakeya.realRpowENN delta (-loss))
  planeMap_vertical_bound :
    ∀ point : {point : Point3 // point ∈ shading.union},
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2

namespace PureWZ2QuantitativeGrainConfiguration

/-- Explicit paper-facing projection. -/
abbrev grain {sigma loss delta : ℝ}
    (data : PureWZ2QuantitativeGrainConfiguration sigma loss delta) :
    PureWZ2GrainConfiguration sigma loss delta := {
  family := data.family
  shading := data.shading
  line_class := data.line_class
  cubical := data.cubical
  extremal := data.extremal
  top_level_cwa := data.top_level_cwa
  globalGrains := data.globalGrains.toPureWZ2LipschitzGlobalGrainData
  localGrains := data.localGrains
}

end PureWZ2QuantitativeGrainConfiguration

instance {sigma loss delta : ℝ} :
    Coe (PureWZ2QuantitativeGrainConfiguration sigma loss delta)
      (PureWZ2GrainConfiguration sigma loss delta) :=
  ⟨PureWZ2QuantitativeGrainConfiguration.grain⟩

namespace PureWZ2GrainConfiguration

/-- Attach Node-5-private quantitative certificates to an unchanged
paper-facing grain configuration. -/
noncomputable def toQuantitativeGrainConfiguration
    {sigma loss delta : ℝ}
    (data : PureWZ2GrainConfiguration sigma loss delta)
    (volume_lower :
      Kakeya.realRpowENN delta (sigma + loss) ≤ volume data.shading.union)
    (slope_bound : ∀ z : ℝ, z ∈ Set.Icc (-1 : ℝ) 1 →
      |data.globalGrains.slope z| ≤ 3)
    (planeMap_vertical_bound :
      ∀ point : {point : Point3 // point ∈ data.shading.union},
        |data.localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2) :
    PureWZ2QuantitativeGrainConfiguration sigma loss delta where
  family := data.family
  shading := data.shading
  line_class := data.line_class
  cubical := data.cubical
  extremal := data.extremal
  top_level_cwa := data.top_level_cwa
  volume_lower := volume_lower
  globalGrains := PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound
    data.globalGrains slope_bound
  localGrains := data.localGrains
  planeMap_vertical_bound := planeMap_vertical_bound

end PureWZ2GrainConfiguration

namespace PureWZ2GrainRefinementData

/-- Forget the source-subshading proof while retaining the quantitative
certificates used by the C2 iteration.  The slope bound is supplied
separately because it belongs to the chart construction, not to the public
global-grain record. -/
noncomputable def toQuantitativeGrainConfiguration
    {delta sigma outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    (data : PureWZ2GrainRefinementData sourceShading sigma outputLoss)
    (slope_bound : ∀ z : ℝ, z ∈ Set.Icc (-1 : ℝ) 1 →
      |data.globalGrains.slope z| ≤ 3) :
    PureWZ2QuantitativeGrainConfiguration sigma outputLoss delta where
  family := family
  shading := data.shading
  line_class := data.line_class
  cubical := data.cubical
  extremal := data.extremal
  top_level_cwa := data.top_level_cwa
  volume_lower := data.volume_lower
  globalGrains :=
    PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound
      data.globalGrains slope_bound
  localGrains := data.localGrains
  planeMap_vertical_bound := data.planeMap_vertical_bound

end PureWZ2GrainRefinementData

end Kakeya.Assouad

end
