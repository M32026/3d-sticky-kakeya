import MyLeanRepo.Kakeya.Assouad.WZ1.GridCellPruning
import MyLeanRepo.Kakeya.Assouad.WZ1.UnitRescaling
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# WZ1 Proposition 3.2

This module freezes the single-scale statement of Proposition 3.2 from the
published WZ1 paper.

The output chooses its own coarse family and fine-to-coarse cover.  It is not
forced to use an arbitrary caller-supplied `U.coarse rho`, and it contains no
finite schedule, recursive coarse uniform structure, or later Section 4
associated-cell data.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/--
The repository-normalized version of a paper `rho`-cube.

The paper uses `6 * rho`-thick tubes, while `DeltaTube rho` has carrier radius
`rho`.  We therefore use the existing grid cell of diameter at most `rho / 2`.
This fixed-dimensional normalization leaves room for the transformed source
tube radius and changes no exponent in Proposition 3.2.
-/
def wz1StandardGridCube
    (rho : ℝ) (cell : ℤ × ℤ × ℤ) : Set Point3 :=
  gridCell (rho / 2) cell

/-- Grid index corresponding to `wz1StandardGridCube`. -/
def wz1StandardGridIndex
    (rho : ℝ) (point : Point3) : ℤ × ℤ × ℤ :=
  rhoGridIndex (rho / 4) point

@[simp] theorem mem_wz1StandardGridCube
    (rho : ℝ) (cell : ℤ × ℤ × ℤ) (point : Point3) :
    point ∈ wz1StandardGridCube rho cell ↔
      wz1StandardGridIndex rho point = cell := by
  simp only [wz1StandardGridCube, gridCell, wz1StandardGridIndex,
    Set.mem_setOf_eq]
  congr 2
  ring_nf

/-- The union of all standard `rho`-cubes that meet `source`. -/
def wz1CubicalSaturation
    (rho : ℝ) (source : Set Point3) : Set Point3 :=
  {point |
    ∃ sourcePoint ∈ source,
      wz1StandardGridIndex rho point =
        wz1StandardGridIndex rho sourcePoint}

@[simp] theorem mem_wz1CubicalSaturation
    (rho : ℝ) (source : Set Point3) (point : Point3) :
    point ∈ wz1CubicalSaturation rho source ↔
      ∃ sourcePoint ∈ source,
        wz1StandardGridIndex rho point =
          wz1StandardGridIndex rho sourcePoint := by
  rfl

theorem subset_wz1CubicalSaturation
    (rho : ℝ) (source : Set Point3) :
    source ⊆ wz1CubicalSaturation rho source := by
  intro point hpoint
  exact ⟨point, hpoint, rfl⟩

theorem wz1CubicalSaturation_isCubical
    (rho : ℝ) (source : Set Point3) :
    ∀ point ∈ wz1CubicalSaturation rho source,
      wz1StandardGridCube rho (wz1StandardGridIndex rho point) ⊆
        wz1CubicalSaturation rho source := by
  rintro point ⟨sourcePoint, hsourcePoint, hpoint⟩
    other hother
  exact
    ⟨sourcePoint, hsourcePoint,
      (mem_wz1StandardGridCube _ _ _).mp hother |>.trans hpoint⟩

/-- The point where the supporting axis of `tube` meets the plane `z = 0`. -/
def wz1TubeAxisZeroPoint
    {rho : ℝ} (tube : Kakeya.DeltaTube rho) : Point3 :=
  tube.base -
    (tube.base (2 : Fin 3) / tube.direction (2 : Fin 3)) •
      tube.direction

theorem wz1TubeAxisZeroPoint_coord_two
    {rho : ℝ} (tube : Kakeya.DeltaTube rho)
    (hvertical :
      (1 / 2 : ℝ) ≤ |tube.direction (2 : Fin 3)|) :
    wz1TubeAxisZeroPoint tube (2 : Fin 3) = 0 := by
  have hne : tube.direction (2 : Fin 3) ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  simp only [wz1TubeAxisZeroPoint, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul]
  field_simp [hne]
  ring

/--
The unit-rescaling map from WZ1 Definition 3.1, relative to one coarse tube.

It sends the supporting-axis point at height zero to the origin, sends the
coarse direction to the vertical axis, and applies the fixed transverse
dilation `1 / (100 * rho)`.  Thus the harmless dimensional constant in the
paper is frozen as `c(3) = 1 / 100`.
-/
def wz1CoarseUnitRescalingMap
    {rho : ℝ} (coarse : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (_hvertical :
      (1 / 2 : ℝ) ≤ |coarse.direction (2 : Fin 3)|)
    (point : Point3) : Point3 :=
  unitRescalingMap
    (wz1TubeAxisZeroPoint coarse)
    coarse.direction coarse.direction_unit
    (100 * rho) (by positivity)
    point

/--
The vertical-chart part of the paper's line class at every selected scale.

The absolute value in `IsInVerticalChart` forgets the arbitrary orientation
of the formal unit segment.  This is the repository counterpart of requiring
every supporting line to belong to the fixed class `L_3`.
-/
def WZ1VerticalUniformTubeStructure
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (uniform :
      Kakeya.Streamlined.UniformTubeStructure family) : Prop :=
  IsInVerticalChart family ∧
    ∀ scale, IsInVerticalChart (uniform.coarse scale)

/-- A shading made from whole standard cubes of side length `rho`. -/
def WZ1IsCubicalShading
    {rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily rho}
    (shading : Kakeya.Streamlined.TubeShading family) : Prop :=
  ∀ index point, point ∈ shading.carrier index →
    wz1StandardGridCube rho (wz1StandardGridIndex rho point) ⊆
      shading.carrier index

/--
Item (i): the selected coarse configuration is `epsilon`-extremal.

The coarse family is exactly the `rho` coordinate of the output fine
`UniformTubeStructure`.  Thus the balanced cover below uses the same GWZ
every-scale witness rather than an unrelated existential cover.
-/
structure WZ1Proposition3_2CoarseExtremalData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (fineUniform : Kakeya.Streamlined.UniformTubeStructure fine)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (sigma epsilon : ℝ) where
  uniform :
    Kakeya.Streamlined.UniformTubeStructure
      (fineUniform.coarse rho)
  shading :
    Kakeya.Streamlined.TubeShading
      (fineUniform.coarse rho)
  extremal :
    WZ1ExtremalPair sigma epsilon
      (fineUniform.coarse rho) uniform shading
  vertical :
    WZ1VerticalUniformTubeStructure uniform

/--
The paper's balanced-cover condition at one scale.

The cover is the GWZ `TubeCover` convention used throughout this repository.
The coarse shading is explicitly cubical, its union is represented by the
finite set of active standard `rho`-cubes, and every such cube contains a
comparable amount of the final fine shaded union.  The factor-two band is the
literal quantitative content of the dyadic pigeonholing called “the same” in
the paper.
-/
structure WZ1Proposition3_2BalancedCoverData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : Kakeya.Streamlined.TubeCover fine coarse)
    (refined : Kakeya.Streamlined.TubeShading fine)
    (coarseShading : Kakeya.Streamlined.TubeShading coarse) where
  point_compatibility :
    ∀ source point, point ∈ refined.carrier source →
      point ∈ coarseShading.carrier (cover.parent source)
  coarse_cubical :
    WZ1IsCubicalShading coarseShading
  activeCells : Finset (ℤ × ℤ × ℤ)
  coarse_union_eq :
    coarseShading.union =
      ⋃ cell ∈ activeCells, wz1StandardGridCube rho cell
  cellMass : ENNReal
  cellMass_pos : 0 < cellMass
  cellMass_ne_top : cellMass ≠ ⊤
  fine_cell_balance :
    ∀ cell ∈ activeCells,
      cellMass ≤
          volume
            (refined.union ∩ wz1StandardGridCube rho cell) ∧
        volume
            (refined.union ∩ wz1StandardGridCube rho cell) ≤
          2 * cellMass

/-- Items (iii) and (iv), tied to the same concrete balanced cover. -/
structure WZ1Proposition3_2MultiplicityData
    {delta rho sigma epsilon : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : Kakeya.Streamlined.TubeCover fine coarse)
    (refined : Kakeya.Streamlined.TubeShading fine)
    (coarseShading : Kakeya.Streamlined.TubeShading coarse) where
  coarse_multiplicity_upper :
    ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN rho (-sigma - epsilon)
  fiber_multiplicity_upper :
    ∀ parent point,
      (cover.toFactoring.fiberPointMultiplicity
          refined parent point : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
          (-sigma - epsilon)

/-- The extremal target configuration produced by one unit rescaling. -/
structure WZ1UnitRescaledTargetData
    (targetDelta sigma epsilon : ℝ) where
  family :
    Kakeya.Streamlined.TubeFamily targetDelta
  uniform :
    Kakeya.Streamlined.UniformTubeStructure family
  shading :
    Kakeya.Streamlined.TubeShading family
  extremal :
    WZ1ExtremalPair sigma epsilon
      family uniform shading
  vertical :
    WZ1VerticalUniformTubeStructure uniform

/--
Item (ii): the unit rescaling of the whole final fine fiber over one coarse
tube is extremal at radius `delta / rho`.

The affine normalization is anchored on the coarse tube, not on an unrelated
fine tube.  A paper tube is clipped from a full supporting line, whereas a
repository tube thickens one unit segment.  The transformed shading of one
source tube may therefore be split among finitely many coaxial target tubes.
`sourceIndex` records the source of each target piece and
`sourcePiece_cover` includes the entire final shading of every source tube in
the parent fiber.  Each target shading is exactly the union of standard
`delta / rho`-cubes meeting its transformed source piece.
-/
structure WZ1UnitRescaledParentFiberData
    {delta rho sigma epsilon : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : Kakeya.Streamlined.TubeCover fine coarse)
    (refined : Kakeya.Streamlined.TubeShading fine)
    (parent : Fin coarse.card)
    (hrho : 0 < rho)
    (coarseVertical : IsInVerticalChart coarse) where
  target :
    WZ1UnitRescaledTargetData
      (delta / rho) sigma epsilon
  sourceIndex : Fin target.family.card → Fin fine.card
  sourceIndex_parent :
    ∀ targetIndex,
      cover.parent (sourceIndex targetIndex) = parent
  sourceIndex_surjective :
    ∀ source, cover.parent source = parent →
      (refined.carrier source).Nonempty →
        ∃ targetIndex, sourceIndex targetIndex = source
  sourcePiece : Fin target.family.card → Set Point3
  sourcePiece_measurable :
    ∀ targetIndex, MeasurableSet (sourcePiece targetIndex)
  sourcePiece_subset :
    ∀ targetIndex,
      sourcePiece targetIndex ⊆
        refined.carrier (sourceIndex targetIndex)
  sourcePiece_cover :
    ∀ source,
      cover.parent source = parent →
        refined.carrier source ⊆
          ⋃ targetIndex : Fin target.family.card,
            if sourceIndex targetIndex = source then
              sourcePiece targetIndex
            else ∅
  target_axis :
    ∀ targetIndex,
      tubeAxisLine (target.family.tube targetIndex) =
        wz1CoarseUnitRescalingMap
            (coarse.tube parent) hrho
            (coarseVertical parent) ''
          tubeAxisLine (fine.tube (sourceIndex targetIndex))
  target_carrier_eq :
    ∀ targetIndex,
      target.shading.carrier targetIndex =
        wz1CubicalSaturation (delta / rho)
          (wz1CoarseUnitRescalingMap
              (coarse.tube parent) hrho
              (coarseVertical parent) ''
            sourcePiece targetIndex)

/--
The single-scale output of WZ1 Proposition 3.2.

The four numbered conclusions all refer to this one concrete refinement and
one concrete balanced cover.  No finite schedule, recursive coarse hierarchy,
or later Section 4 associated-cell data appears in this package.
-/
structure WZ1Proposition3_2Data
    {delta sigma epsilon : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) where
  selected : Kakeya.Streamlined.TubeSubfamily source
  refined :
    Kakeya.Streamlined.TubeShading selected.family
  subshading :
    ∀ index,
      refined.carrier index ⊆
        shading.carrier (selected.embedding index)
  refined_cubical :
    WZ1IsCubicalShading refined
  retained_mass :
    Kakeya.realRpowENN delta epsilon * shading.mass ≤ refined.mass
  fineUniform :
    Kakeya.Streamlined.UniformTubeStructure selected.family
  refined_extremal :
    WZ1ExtremalPair sigma epsilon
      selected.family fineUniform refined
  fine_vertical :
    WZ1VerticalUniformTubeStructure fineUniform
  coarse :
    WZ1Proposition3_2CoarseExtremalData
      fineUniform rho sigma epsilon
  balanced :
    WZ1Proposition3_2BalancedCoverData
      (fineUniform.cover rho) refined coarse.shading
  rescaledFiber :
    ∀ parent : Fin (fineUniform.coarse rho).card,
      coarse.shading.carrier parent ≠ ∅ →
      Nonempty
        (WZ1UnitRescaledParentFiberData
          (sigma := sigma) (epsilon := epsilon)
          (fineUniform.cover rho) refined parent
          (lt_of_lt_of_le refined_extremal.1 rho.2.1)
          coarse.vertical.1)
  multiplicity :
    WZ1Proposition3_2MultiplicityData
      (sigma := sigma) (epsilon := epsilon)
      (fineUniform.cover rho) refined coarse.shading

/--
WZ1 Proposition 3.2 in the repository's cropped-window conventions.

The explicit `HasWZ1CriticalVolumeFloor` premise is the already-separated
pre-Proposition-3.2 lower-volume input for cropped formal tube carriers.  This
statement does not revive the invalid global normalization from arbitrary
full formal carriers.
-/
def WZ1Proposition3_2Statement : Prop :=
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
    HasWZ1CriticalVolumeFloor sigma →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ eta delta₀ : ℝ,
          0 < eta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ fine : Kakeya.Streamlined.TubeFamily delta,
              ∀ fineUniform :
                  Kakeya.Streamlined.UniformTubeStructure fine,
                ∀ shading : Kakeya.Streamlined.TubeShading fine,
                  WZ1ExtremalPair sigma eta
                    fine fineUniform shading →
                  WZ1VerticalUniformTubeStructure fineUniform →
                  WZ1IsCubicalShading shading →
                  ∀ rho :
                      Kakeya.Streamlined.AdmissibleScale delta,
                    Real.rpow delta (1 - epsilon) ≤ rho.1 →
                    rho.1 ≤ Real.rpow delta epsilon →
                      Nonempty
                        (WZ1Proposition3_2Data
                          (sigma := sigma) (epsilon := epsilon)
                          shading rho)

end Kakeya.Assouad
