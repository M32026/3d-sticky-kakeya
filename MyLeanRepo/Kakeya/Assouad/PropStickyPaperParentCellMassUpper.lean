import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSourceDirectionalFiberCardinality
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedActiveParentCellsStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.CubeCountGeometry

/-!
# Parent--cell incidence mass upper bound in WZ2 `prop: sticky`

This closes the estimate labelled `upperBdWeightOfQ` in the paper.  One
paper `delta`-tube contributes at most `288 * delta^2 * rho` inside one
literal `rho`-cell.  The source directional-covering condition bounds the
number of tubes in one caller fiber by
`300 * (rho / delta)^2 * delta^(-loss)`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

attribute [local instance] Classical.propDecidable

private lemma abs_inner_sub_le_dist
    (first second direction : Point3)
    (hdirection : ‖direction‖ = 1) :
    |inner ℝ (first - second) direction| ≤ dist first second := by
  have h :=
    abs_real_inner_le_norm (first - second) direction
  rw [hdirection, mul_one] at h
  simpa [dist_eq_norm] using h

/--
One cropped paper tube contributes `O(delta^2 * rho)` volume inside one
literal `rho`-cell.
-/
lemma wz2_paper_tube_cell_intersection_volume
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (tube : Kakeya.DeltaTube delta)
    (cell : WZ2PaperCellIndex) :
    volume
        (wz1PaperTubeCarrier tube ∩
          wz1PaperGridCube rho cell) ≤
      ENNReal.ofReal (288 * delta ^ 2 * rho) := by
  let e0 : Point3 :=
    EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let e1 : Point3 :=
    EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
  let e2 : Point3 :=
    EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  let direction := tube.direction
  let rotation : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (direction - e0))ᗮ
  have hrotationDirection :
      rotation direction = e0 := by
    exact
      Submodule.reflection_sub
        (by rw [tube.direction_unit]; simp [e0])
  let transverseOne : Point3 := rotation.symm e1
  let transverseTwo : Point3 := rotation.symm e2
  have htransverseOneNorm : ‖transverseOne‖ = 1 := by
    rw [rotation.symm.norm_map]
    simp [transverseOne, e1]
  have htransverseTwoNorm : ‖transverseTwo‖ = 1 := by
    rw [rotation.symm.norm_map]
    simp [transverseTwo, e2]
  have htransverseOnePerp :
      inner ℝ direction transverseOne = 0 := by
    have hmap :
        inner ℝ direction transverseOne =
          inner ℝ (rotation direction)
            (rotation transverseOne) :=
      (rotation.inner_map_map direction transverseOne).symm
    rw [hmap, hrotationDirection]
    have htransverseMap : rotation transverseOne = e1 := by
      simp [transverseOne]
    rw [htransverseMap]
    simp [e0, e1, EuclideanSpace.inner_single_right]
  have htransverseTwoPerp :
      inner ℝ direction transverseTwo = 0 := by
    have hmap :
        inner ℝ direction transverseTwo =
          inner ℝ (rotation direction)
            (rotation transverseTwo) :=
      (rotation.inner_map_map direction transverseTwo).symm
    rw [hmap, hrotationDirection]
    have htransverseMap : rotation transverseTwo = e2 := by
      simp [transverseTwo]
    rw [htransverseMap]
    simp [e0, e2, EuclideanSpace.inner_single_right]
  have hcoordinateZero :
      ∀ point : Point3,
        (rotation point) 0 =
          inner ℝ point direction := by
    intro point
    have hcoord :
        (rotation point) 0 =
          inner ℝ (rotation point) e0 := by
      simp [e0, EuclideanSpace.inner_single_right]
    rw [hcoord]
    have hmap :=
      rotation.inner_map_map point direction
    rw [hrotationDirection] at hmap
    exact hmap
  have hcoordinateOne :
      ∀ point : Point3,
        (rotation point) 1 =
          inner ℝ point transverseOne := by
    intro point
    have hcoord :
        (rotation point) 1 =
          inner ℝ (rotation point) e1 := by
      simp [e1, EuclideanSpace.inner_single_right]
    rw [hcoord]
    have hmap :=
      rotation.inner_map_map point transverseOne
    have htransverseMap : rotation transverseOne = e1 := by
      simp [transverseOne]
    rw [htransverseMap] at hmap
    exact hmap
  have hcoordinateTwo :
      ∀ point : Point3,
        (rotation point) 2 =
          inner ℝ point transverseTwo := by
    intro point
    have hcoord :
        (rotation point) 2 =
          inner ℝ (rotation point) e2 := by
      simp [e2, EuclideanSpace.inner_single_right]
    rw [hcoord]
    have hmap :=
      rotation.inner_map_map point transverseTwo
    have htransverseMap : rotation transverseTwo = e2 := by
      simp [transverseTwo]
    rw [htransverseMap] at hmap
    exact hmap
  let piece : Set Point3 :=
    wz1PaperTubeCarrier tube ∩
      wz1PaperGridCube rho cell
  have hpieceMeasurable : MeasurableSet piece :=
    ((Metric.isClosed_cthickening).measurableSet.inter
      (Kakeya.Streamlined.measurableSet_axisBox 2 2 2)).inter
        (wz1PaperGridCube_measurable cell)
  have haxial :
      ∀ first second, first ∈ piece → second ∈ piece →
        |(rotation first) 0 - (rotation second) 0| ≤
          2 * rho := by
    intro first second hfirst hsecond
    rw [hcoordinateZero first, hcoordinateZero second]
    have hinner :
        |inner ℝ first direction -
            inner ℝ second direction| =
          |inner ℝ (first - second) direction| := by
      rw [inner_sub_left]
    rw [hinner]
    have hdist :
        dist first second < 2 * rho :=
      wz1_paper_grid_cube_diameter_lt_two_rho
        hrho hfirst.2 hsecond.2
    exact
      (abs_inner_sub_le_dist
        first second direction tube.direction_unit).trans
        hdist.le
  have htransverse :
      ∀ transverse : Point3,
        ‖transverse‖ = 1 →
        inner ℝ direction transverse = 0 →
        ∀ first second, first ∈ piece → second ∈ piece →
          |inner ℝ (first - second) transverse| ≤
            12 * delta := by
    intro transverse htransverseNorm hperp
      first second hfirst hsecond
    rcases
        exists_dist_le_of_mem_cthickening_closed
          (isClosed_tubeAxisLine tube)
          (by positivity) hfirst.1.1 with
      ⟨firstAxis, hfirstAxis, hfirstDistance⟩
    rcases
        exists_dist_le_of_mem_cthickening_closed
          (isClosed_tubeAxisLine tube)
          (by positivity) hsecond.1.1 with
      ⟨secondAxis, hsecondAxis, hsecondDistance⟩
    rcases hfirstAxis with ⟨firstParameter, hfirstAxisEq⟩
    rcases hsecondAxis with ⟨secondParameter, hsecondAxisEq⟩
    have haxis :
        inner ℝ (firstAxis - secondAxis) transverse = 0 := by
      have haxisDifference :
          firstAxis - secondAxis =
            (firstParameter - secondParameter) • direction := by
        rw [hfirstAxisEq, hsecondAxisEq]
        simp only [direction]
        module
      rw [haxisDifference, inner_smul_left, hperp]
      simp
    have hdecompose :
        first - second =
          (first - firstAxis) +
            (firstAxis - secondAxis) +
              (secondAxis - second) := by
      module
    rw [hdecompose, inner_add_left, inner_add_left, haxis,
      add_zero]
    calc
      |inner ℝ (first - firstAxis) transverse +
          inner ℝ (secondAxis - second) transverse| ≤
        |inner ℝ (first - firstAxis) transverse| +
          |inner ℝ (secondAxis - second) transverse| :=
        abs_add_le _ _
      _ ≤ dist first firstAxis + dist secondAxis second := by
        gcongr
        · exact
            abs_inner_sub_le_dist
              first firstAxis transverse htransverseNorm
        · exact
            abs_inner_sub_le_dist
              secondAxis second transverse htransverseNorm
      _ ≤ 12 * delta := by
        rw [dist_comm secondAxis second]
        linarith
  have hone :
      ∀ first second, first ∈ piece → second ∈ piece →
        |(rotation first) 1 - (rotation second) 1| ≤
          12 * delta := by
    intro first second hfirst hsecond
    rw [hcoordinateOne first, hcoordinateOne second,
      ← inner_sub_left]
    exact
      htransverse transverseOne htransverseOneNorm
        htransverseOnePerp first second hfirst hsecond
  have htwo :
      ∀ first second, first ∈ piece → second ∈ piece →
        |(rotation first) 2 - (rotation second) 2| ≤
          12 * delta := by
    intro first second hfirst hsecond
    rw [hcoordinateTwo first, hcoordinateTwo second,
      ← inner_sub_left]
    exact
      htransverse transverseTwo htransverseTwoNorm
        htransverseTwoPerp first second hfirst hsecond
  have hvolume :=
    volume_by_three_diameters_public
      hpieceMeasurable rotation
      (2 * rho) (12 * delta) (12 * delta)
      (by positivity) (by positivity) (by positivity)
      haxial hone htwo
  have hcoefficient :
      (2 * rho) * (12 * delta) * (12 * delta) =
        288 * delta ^ 2 * rho := by ring
  rw [hcoefficient] at hvolume
  exact hvolume

/--
Paper `upperBdWeightOfQ`: the shaded incidence mass of one parent inside one
literal `rho`-cell is at most
`86400 * delta^(-loss) * rho^3`.
-/
theorem wz2_paper_source_parent_cell_mass_upper
    {delta rho sigma loss : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambient}
    (source :
      WZ2PaperExactScaleExtremal
        sigma loss ambient ambientShading)
    (selected : Kakeya.Streamlined.TubeSubfamily ambient)
    (shading : WZ1PaperTubeShading selected.family)
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover selected.family coarse)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (hdeltaRho : delta ≤ rho)
    (hrhoHalf : rho ≤ 1 / 2)
    (parent : Fin coarse.card)
    (cell : WZ2PaperCellIndex) :
    wz2PaperParentCellMass cover shading (cell, parent) ≤
      ENNReal.ofReal (86400 * rho ^ 3) *
        Kakeya.realRpowENN delta (-loss) := by
  have hrho : 0 < rho :=
    source.delta_pos.trans_le hdeltaRho
  have hfiber :=
    wz2_paper_source_directional_full_fiber_cardinality
      source selected cover coarseLine hdeltaRho hrhoHalf parent
  let fiber := cover.fullFiberSubfamily parent
  let restricted :=
    restrictPaperShading fiber shading
  have hterm :
      ∀ index : Fin fiber.family.card,
        volume
            (restricted.carrier index ∩
              wz1PaperGridCube rho cell) ≤
          ENNReal.ofReal (288 * delta ^ 2 * rho) := by
    intro index
    have hsubset :
        restricted.carrier index ⊆
          wz1PaperTubeCarrier (fiber.family.tube index) :=
      restricted.subset_body index
    exact
      (measure_mono
        (Set.inter_subset_inter hsubset Set.Subset.rfl)).trans
        (wz2_paper_tube_cell_intersection_volume
          source.delta_pos hrho (fiber.family.tube index) cell)
  have hsum :
      wz2PaperParentCellMass cover shading (cell, parent) ≤
        fiber.family.enncard *
          ENNReal.ofReal (288 * delta ^ 2 * rho) := by
    calc
      wz2PaperParentCellMass cover shading (cell, parent) =
          ∑ index : Fin fiber.family.card,
            volume
              (restricted.carrier index ∩
                wz1PaperGridCube rho cell) := rfl
      _ ≤
          ∑ _index : Fin fiber.family.card,
            ENNReal.ofReal (288 * delta ^ 2 * rho) :=
        Finset.sum_le_sum fun index _ => hterm index
      _ =
          fiber.family.enncard *
            ENNReal.ofReal (288 * delta ^ 2 * rho) := by
        simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hfiber' :
      fiber.family.enncard ≤
        ENNReal.ofReal (300 * (rho / delta) ^ 2) *
          Kakeya.realRpowENN delta (-loss) := by
    change
      ((wz2PaperFullFiberIndices
        selected.family coarse parent).card : ENNReal) ≤
        ENNReal.ofReal (300 * (rho / delta) ^ 2) *
          Kakeya.realRpowENN delta (-loss)
    exact hfiber
  calc
    wz2PaperParentCellMass cover shading (cell, parent) ≤
        fiber.family.enncard *
          ENNReal.ofReal (288 * delta ^ 2 * rho) := hsum
    _ ≤
        (ENNReal.ofReal (300 * (rho / delta) ^ 2) *
            Kakeya.realRpowENN delta (-loss)) *
          ENNReal.ofReal (288 * delta ^ 2 * rho) := by
      gcongr
    _ =
        ENNReal.ofReal (86400 * rho ^ 3) *
          Kakeya.realRpowENN delta (-loss) := by
      have hfirstNonnegative :
          0 ≤ 300 * (rho / delta) ^ 2 := by positivity
      have hsecondNonnegative :
          0 ≤ 288 * delta ^ 2 * rho := by positivity
      have hreal :
          (300 * (rho / delta) ^ 2) *
              (288 * delta ^ 2 * rho) =
            86400 * rho ^ 3 := by
        field_simp [source.delta_pos.ne']
        ring
      calc
        (ENNReal.ofReal (300 * (rho / delta) ^ 2) *
              Kakeya.realRpowENN delta (-loss)) *
            ENNReal.ofReal (288 * delta ^ 2 * rho) =
          (ENNReal.ofReal (300 * (rho / delta) ^ 2) *
              ENNReal.ofReal (288 * delta ^ 2 * rho)) *
            Kakeya.realRpowENN delta (-loss) := by ring
        _ =
          ENNReal.ofReal
              ((300 * (rho / delta) ^ 2) *
                (288 * delta ^ 2 * rho)) *
            Kakeya.realRpowENN delta (-loss) := by
          rw [ENNReal.ofReal_mul hfirstNonnegative]
        _ =
          ENNReal.ofReal (86400 * rho ^ 3) *
            Kakeya.realRpowENN delta (-loss) := by rw [hreal]

end Kakeya.Assouad

end
