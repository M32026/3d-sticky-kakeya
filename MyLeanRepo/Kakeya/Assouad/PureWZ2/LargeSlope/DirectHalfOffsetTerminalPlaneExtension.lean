import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ProjectiveChartSaturationExtension

/-!
# Extend the direct projective plane map to the actual cubical terminal

The extension preserves the projective middle coordinate before unit
normalization, avoiding the opaque finite-dimensional extension loss.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

/-- The unnormalized projective-chart representative on the exact terminal
image. -/
def halfOffsetTerminalExactChartMap
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :
    {point : Point3 // point ∈
      commonSource.halfOffsetTerminalExactSet retubing box
        (lambda := pureWZ2DirectHalfOffsetTerminalLambda)} → Point3 :=
  fun point =>
    let source := commonSource.halfOffsetAssembly.horizontalSource
    let b := source.m * (source.d - source.c) / 2
    let S := 2 / (source.d - source.c)
    pureWZ2OffsetProjectiveTotalNormal b S
      pureWZ2FixedProjectiveNormalLambda
      (pureWZ2OffsetShearProjectiveNormal
        (PureWZ2HalfOffsetHorizontalSourceData.offset source)
        (source.sourceLocalGrains.planeMap
          (commonSource.halfOffsetTerminalSourcePoint retubing box
            pureWZ2DirectHalfOffsetTerminalLambda_pos point)))

theorem halfOffsetTerminalExactChartMap_coord_one
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth)
    (point) :
    commonSource.halfOffsetTerminalExactChartMap retubing box point 1 = 1 := by
  simp [halfOffsetTerminalExactChartMap,
    pureWZ2OffsetProjectiveTotalNormal, point3]

theorem halfOffsetTerminalExactChartMap_lipschitz
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :
    LipschitzWith (1 / 2 : NNReal)
      (commonSource.halfOffsetTerminalExactChartMap retubing box) := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let b := source.m * (source.d - source.c) / 2
  let S := 2 / (source.d - source.c)
  let preimage := commonSource.halfOffsetTerminalSourcePoint retubing box
    pureWZ2DirectHalfOffsetTerminalLambda_pos
  have hlengthPos : 0 < source.d - source.c := sub_pos.mpr source.ordered
  have hb : 0 < b := by
    dsimp only [b]
    exact div_pos (mul_pos source.slopeScale_pos hlengthPos) (by norm_num)
  have hS : 1 ≤ S := by
    dsimp only [S]
    have hlengthUpper : source.d - source.c ≤ 2 := by
      linarith [source.left_mem, source.right_mem]
    exact (le_div_iff₀ hlengthPos).2 (by simpa using hlengthUpper)
  exact pureWZ2FixedProjectiveNormal_exactImage_chart_lipschitz
    (b := b) (S := S) (preimage := preimage)
    (field := fun sourcePoint => pureWZ2OffsetShearProjectiveNormal
      (PureWZ2HalfOffsetHorizontalSourceData.offset source)
      (source.sourceLocalGrains.planeMap sourcePoint))
    hb hS
    (commonSource.halfOffsetTerminalSourcePoint_scaled_dist_le retubing box
      pureWZ2DirectHalfOffsetTerminalLambda_one_le)
    (PureWZ2HalfOffsetHorizontalSourceData.projectiveNormal_lipschitz_restrict
      source commonSource.halfOffsetAssembly_compatibility)
    (PureWZ2HalfOffsetHorizontalSourceData.projectiveNormal_coord_one_restrict
      source commonSource.halfOffsetAssembly_compatibility)

theorem halfOffsetTerminalExactChartMap_coord_two_lipschitz
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :
    LipschitzWith (1 / 100 : NNReal)
      (fun point =>
        commonSource.halfOffsetTerminalExactChartMap retubing box point 2) := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let b := source.m * (source.d - source.c) / 2
  let S := 2 / (source.d - source.c)
  let preimage := commonSource.halfOffsetTerminalSourcePoint retubing box
    pureWZ2DirectHalfOffsetTerminalLambda_pos
  have hlengthPos : 0 < source.d - source.c := sub_pos.mpr source.ordered
  have hb : 0 < b := by
    dsimp only [b]
    exact div_pos (mul_pos source.slopeScale_pos hlengthPos) (by norm_num)
  have hlengthUpper : source.d - source.c ≤ 1 / 25 := by
    rw [source.length_eq, commonSource.halfOffsetAssembly.horizontalSource_scale]
    linarith [commonSource.halfOffsetAssembly.rho_tiny]
  have hS : 50 ≤ S := by
    dsimp only [S]
    exact (le_div_iff₀ hlengthPos).2 (by nlinarith [hlengthUpper])
  exact pureWZ2FixedProjectiveNormal_exactImage_chart_coord_two_lipschitz
    (b := b) (S := S) (preimage := preimage)
    (field := fun sourcePoint => pureWZ2OffsetShearProjectiveNormal
      (PureWZ2HalfOffsetHorizontalSourceData.offset source)
      (source.sourceLocalGrains.planeMap sourcePoint))
    hb hS
    (commonSource.halfOffsetTerminalSourcePoint_scaled_dist_le retubing box
      pureWZ2DirectHalfOffsetTerminalLambda_one_le)
    (PureWZ2HalfOffsetHorizontalSourceData.projectiveNormal_lipschitz_restrict
      source commonSource.halfOffsetAssembly_compatibility)

theorem halfOffsetTerminalExactPlaneMap_eq_normalize_chart
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :
    commonSource.halfOffsetTerminalExactPlaneMap retubing box =
      fun point => NormedSpace.normalize
        (commonSource.halfOffsetTerminalExactChartMap retubing box point) := by
  rfl

namespace TerminalGeometry

/-- Reinterpret an actual exact-shading point in the canonical exact-image
set.  Only the membership proof changes. -/
def exactSetPoint (terminal : commonSource.TerminalGeometry) :
    {point : Point3 // point ∈ terminal.exactShading.union} →
      {point : Point3 // point ∈
        commonSource.halfOffsetTerminalExactSet terminal.retubing terminal.box
          (lambda := pureWZ2DirectHalfOffsetTerminalLambda)} :=
  fun point => ⟨point, by rw [← terminal.exact_union]; exact point.property⟩

def exactChartMap (terminal : commonSource.TerminalGeometry) :
    {point : Point3 // point ∈ terminal.exactShading.union} → Point3 :=
  fun point => commonSource.halfOffsetTerminalExactChartMap terminal.retubing
    terminal.box (exactSetPoint commonSource terminal point)

def exactPlaneMap (terminal : commonSource.TerminalGeometry) :
    {point : Point3 // point ∈ terminal.exactShading.union} → Point3 :=
  fun point => commonSource.halfOffsetTerminalExactPlaneMap terminal.retubing
    terminal.box (exactSetPoint commonSource terminal point)

theorem exactChartMap_lipschitz (terminal : commonSource.TerminalGeometry) :
    LipschitzWith (1 / 2 : NNReal) (exactChartMap commonSource terminal) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  simpa [exactChartMap, exactSetPoint, Subtype.dist_eq] using
    (commonSource.halfOffsetTerminalExactChartMap_lipschitz
      terminal.retubing terminal.box).dist_le_mul
        (exactSetPoint commonSource terminal first)
        (exactSetPoint commonSource terminal second)

theorem exactChartMap_coord_one (terminal : commonSource.TerminalGeometry)
    (point) : exactChartMap commonSource terminal point 1 = 1 :=
  commonSource.halfOffsetTerminalExactChartMap_coord_one terminal.retubing
    terminal.box (exactSetPoint commonSource terminal point)

theorem exactChartMap_coord_two_lipschitz
    (terminal : commonSource.TerminalGeometry) :
    LipschitzWith (1 / 100 : NNReal)
      (fun point => exactChartMap commonSource terminal point 2) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  simpa [exactChartMap, exactSetPoint, Subtype.dist_eq] using
    (commonSource.halfOffsetTerminalExactChartMap_coord_two_lipschitz
      terminal.retubing terminal.box).dist_le_mul
        (exactSetPoint commonSource terminal first)
        (exactSetPoint commonSource terminal second)

theorem exactPlaneMap_eq_normalize_chart
    (terminal : commonSource.TerminalGeometry) :
    exactPlaneMap commonSource terminal = fun point =>
      NormedSpace.normalize (exactChartMap commonSource terminal point) := by
  rfl

end TerminalGeometry

/-- A genuine one-Lipschitz unit plane-map core on the actual cubical
terminal, with same-cell exact provenance and error one cube diagonal. -/
theorem toHalfOffsetTerminalSaturationPlaneMapCore
    (terminal : commonSource.TerminalGeometry) :
    Nonempty (PureWZ2SaturationPlaneMapCoreData
      terminal.exactShading.union terminal.cubicalShading.union
      (TerminalGeometry.exactPlaneMap commonSource terminal)
      (terminal.targetDelta * Real.sqrt 3)
      ((51 / 100 : ℝ) *
        (terminal.targetDelta * Real.sqrt 3))) := by
  rw [TerminalGeometry.exactPlaneMap_eq_normalize_chart commonSource terminal]
  apply pureWZ2_extend_halfLipschitz_projective_chart_to_saturation_core
    (hrawLipschitz :=
      TerminalGeometry.exactChartMap_lipschitz commonSource terminal)
    (hrawCoordTwo :=
      TerminalGeometry.exactChartMap_coord_two_lipschitz commonSource terminal)
    (hcoord :=
      TerminalGeometry.exactChartMap_coord_one commonSource terminal)
    (hwitnessRadius := mul_nonneg
      commonSource.halfOffsetLineClassTargetDelta_pos.le
      (Real.sqrt_nonneg 3))
    (targetWitness := by
      intro point
      rcases commonSource.halfOffsetLineClassActualCubicalShading_targetWitness
          terminal.retubing terminal.box point with ⟨source, hdist⟩
      refine ⟨⟨source, ?_⟩, hdist⟩
      rw [terminal.exact_union]
      exact source.property)

namespace TerminalGeometry

/-- The chart-preserving extension retains the literal tube-direction
incidence on every carrier of the actual cubical terminal. -/
theorem saturationPlaneMap_incidence
    (terminal : commonSource.TerminalGeometry)
    (core : PureWZ2SaturationPlaneMapCoreData
      terminal.exactShading.union terminal.cubicalShading.union
      (exactPlaneMap commonSource terminal)
      (terminal.targetDelta * Real.sqrt 3)
      ((51 / 100 : ℝ) * (terminal.targetDelta * Real.sqrt 3))) :
    ∀ index point,
      ∀ hpoint : point ∈ terminal.cubicalShading.carrier index,
        |inner ℝ (terminal.family.tube index).direction
          (core.planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤
            terminal.targetDelta := by
  intro index point hpoint
  let targetPoint : {point : Point3 // point ∈ terminal.cubicalShading.union} :=
    ⟨point, ⟨index, hpoint⟩⟩
  have hsaturation : point ∈
      wz1PaperCubicalSaturation terminal.targetDelta
        (pureWZ2LineClassNormalizationMap terminal.box.center
          pureWZ2DirectHalfOffsetTerminalLambda ''
          (commonSource.halfOffsetLineClassTerminalSourceShading
            terminal.retubing terminal.box).carrier index) := hpoint
  rcases wz1PaperCubicalSaturation_exists_source_dist_le
      commonSource.halfOffsetLineClassTargetDelta_pos _ hsaturation with
    ⟨imagePoint, ⟨sourcePoint, hsourcePoint, rfl⟩, hdist⟩
  let exactPoint : {point : Point3 // point ∈ terminal.exactShading.union} :=
    ⟨pureWZ2LineClassNormalizationMap terminal.box.center
        pureWZ2DirectHalfOffsetTerminalLambda sourcePoint,
      ⟨index, ⟨sourcePoint, hsourcePoint, rfl⟩⟩⟩
  have hexact : |inner ℝ (terminal.family.tube index).direction
      (exactPlaneMap commonSource terminal exactPoint)| ≤ delta := by
    have hraw :=
      commonSource.halfOffsetLineClassTerminal_tube_mappedPoint_incidence
        terminal.retubing terminal.box terminal.targetDelta index sourcePoint
        hsourcePoint
    simpa [exactPlaneMap, exactSetPoint, exactPoint] using hraw
  exact core.incidence_of_nearby_exact
    (terminal.family.tube index).direction_unit targetPoint exactPoint
    (by simpa [targetPoint, exactPoint] using hdist) hexact
    commonSource.halfOffsetLineClass_incidence_budget

end TerminalGeometry

/-- The actual terminal geometry together with one chart-preserving cubical
plane-map extension on that same output. -/
structure TerminalPlaneData where
  geometry : commonSource.TerminalGeometry
  core : PureWZ2SaturationPlaneMapCoreData
    geometry.exactShading.union geometry.cubicalShading.union
    (TerminalGeometry.exactPlaneMap commonSource geometry)
    (geometry.targetDelta * Real.sqrt 3)
    ((51 / 100 : ℝ) * (geometry.targetDelta * Real.sqrt 3))

theorem toTerminalPlaneData : Nonempty commonSource.TerminalPlaneData := by
  rcases commonSource.toTerminalGeometry with ⟨geometry⟩
  rcases commonSource.toHalfOffsetTerminalSaturationPlaneMapCore geometry with
    ⟨core⟩
  exact ⟨⟨geometry, core⟩⟩

namespace TerminalPlaneData

abbrev family (data : commonSource.TerminalPlaneData) := data.geometry.family

abbrev shading (data : commonSource.TerminalPlaneData) :=
  data.geometry.cubicalShading

abbrev planeMap (data : commonSource.TerminalPlaneData) := data.core.planeMap

theorem planeMap_lipschitz (data : commonSource.TerminalPlaneData) :
    LipschitzWith 1 (planeMap commonSource data) :=
  data.core.planeMap_lipschitz

theorem planeMap_unit (data : commonSource.TerminalPlaneData) :
    ∀ point, ‖planeMap commonSource data point‖ = 1 :=
  data.core.planeMap_unit

theorem planeMap_incidence (data : commonSource.TerminalPlaneData) :
    ∀ index point,
      ∀ hpoint : point ∈ data.shading.carrier index,
        |inner ℝ (data.family.tube index).direction
          (planeMap commonSource data
            (⟨point, ⟨index, hpoint⟩⟩ :
              {point : Point3 // point ∈ data.shading.union}))| ≤
            data.geometry.targetDelta :=
  TerminalGeometry.saturationPlaneMap_incidence commonSource data.geometry
    data.core

end TerminalPlaneData

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
