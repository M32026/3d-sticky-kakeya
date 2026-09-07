import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometry
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperConvexWolffCardinalityCore
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPeriodicBoundaryVolume

/-!
# Slow-coordinate tubes meeting one coarse-grid boundary

If a cropped paper tube meets a boundary hyperplane and its coordinate speed
is at most `speed`, then its whole carrier lies in a common coordinate strip
of width `O(speed + delta)`.  The strip is convex, so top-level CWA bounds the
number and hence total shaded mass of all such tubes.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def wz2PaperSlowBoundaryTubeIndices
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (coordinate : Fin 3)
    (boundary speed : ℝ) : Finset (Fin family.card) :=
  Finset.univ.filter fun index =>
    |wz1PaperDirection (family.tube index) coordinate| ≤ speed ∧
      (wz1PaperTubeCarrier (family.tube index) ∩
        coordinateSlab coordinate (boundary - delta) (boundary + delta)
      ).Nonempty

def wz2PaperBoundaryContainer
    (coordinate : Fin 3)
    (boundary width : ℝ) : Set Point3 :=
  Kakeya.Streamlined.axisBox 2 2 2 ∩
    coordinateSlab coordinate (boundary - width) (boundary + width)

theorem convex_wz2PaperBoundaryContainer
    (coordinate : Fin 3)
    (boundary width : ℝ) :
    Convex ℝ (wz2PaperBoundaryContainer coordinate boundary width) := by
  have hbox :
      Convex ℝ (Kakeya.Streamlined.axisBox 2 2 2) :=
    Kakeya.Streamlined.convex_axisBox 2 2 2
  let projection : Point3 →ₗ[ℝ] ℝ :=
    { toFun := fun point => point coordinate
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hslab :
      Convex ℝ (coordinateSlab coordinate
        (boundary - width) (boundary + width)) := by
    change Convex ℝ
      (projection ⁻¹' Set.Icc (boundary - width) (boundary + width))
    exact (convex_Icc _ _).linear_preimage projection
  exact hbox.inter hslab

theorem volume_wz2PaperBoundaryContainer_le
    (coordinate : Fin 3)
    (boundary width : ℝ)
    (hwidth : 0 < width) :
    volume (wz2PaperBoundaryContainer coordinate boundary width) ≤
      ENNReal.ofReal (16 * width) := by
  have hsubset :
      wz2PaperBoundaryContainer coordinate boundary width ⊆
        {point : Point3 |
          point ∈ Kakeya.Streamlined.axisBox 2 2 2 ∧
            |point coordinate - boundary| < 2 * width} := by
    intro point hpoint
    refine ⟨hpoint.1, ?_⟩
    change point ∈
      (Kakeya.Streamlined.axisBox 2 2 2 ∩
        coordinateSlab coordinate
          (boundary - width) (boundary + width)) at hpoint
    have hpointSlab :
        point ∈ coordinateSlab coordinate
          (boundary - width) (boundary + width) :=
      hpoint.2
    change point ∈ coordinateSlab coordinate
      (boundary - width) (boundary + width) at hpointSlab
    change
      boundary - width ≤ point coordinate ∧
        point coordinate ≤ boundary + width at hpointSlab
    rw [abs_lt]
    constructor <;> linarith
  exact
    (measure_mono hsubset).trans
      (boundary_slab_volume_le coordinate boundary
        (2 * width) (by positivity))
      |>.trans (by
        apply ENNReal.ofReal_mono
        ring_nf
        exact le_rfl)

theorem wz2_paper_slow_boundary_tube_contained
    {delta speed boundary : ℝ}
    (hdelta : 0 < delta)
    (hspeed : 0 ≤ speed)
    (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube)
    (coordinate : Fin 3)
    (hslow :
      |wz1PaperDirection tube coordinate| ≤ speed)
    (hmeets :
      (wz1PaperTubeCarrier tube ∩
        coordinateSlab coordinate
          (boundary - delta) (boundary + delta)).Nonempty) :
    wz1PaperTubeCarrier tube ⊆
      wz2PaperBoundaryContainer coordinate boundary
        (4 * speed + 49 * delta) := by
  rcases hmeets with ⟨witness, hwitnessTube, hwitnessSlab⟩
  have hgeometry :=
    wz2_paper_tube_carrier_geometry hdelta tube hline
  have hwitnessCore :
      ∃ axisWitness ∈ wz2PaperAxisCoreSegment tube,
        dist witness axisWitness ≤ 24 * delta := by
    exact
      exists_dist_le_of_mem_cthickening_closed
        (wz2PaperAxisCoreSegment_compact tube).isClosed
        (by positivity) (hgeometry.2 hwitnessTube)
  rcases hwitnessCore with
    ⟨axisWitness, haxisWitness, hwitnessAxisDist⟩
  rw [wz2PaperAxisCoreSegment_eq] at haxisWitness
  rcases haxisWitness with
    ⟨witnessParameter, hwitnessParameter, haxisWitnessEq⟩
  intro point hpoint
  refine ⟨hpoint.2, ?_⟩
  have hpointCore :
      ∃ axisPoint ∈ wz2PaperAxisCoreSegment tube,
        dist point axisPoint ≤ 24 * delta := by
    exact
      exists_dist_le_of_mem_cthickening_closed
        (wz2PaperAxisCoreSegment_compact tube).isClosed
        (by positivity) (hgeometry.2 hpoint)
  rcases hpointCore with
    ⟨axisPoint, haxisPoint, hpointAxisDist⟩
  rw [wz2PaperAxisCoreSegment_eq] at haxisPoint
  rcases haxisPoint with
    ⟨pointParameter, hpointParameter, haxisPointEq⟩
  have hpointCoordinate :
      |point coordinate - boundary| ≤
        4 * speed + 49 * delta := by
    have hpointAxisCoordinate :
        |point coordinate - axisPoint coordinate| ≤
          24 * delta :=
      (abs_coord_sub_le_dist coordinate).trans hpointAxisDist
    have hwitnessAxisCoordinate :
        |witness coordinate - axisWitness coordinate| ≤
          24 * delta :=
      (abs_coord_sub_le_dist coordinate).trans hwitnessAxisDist
    have hwitnessBoundary :
        |witness coordinate - boundary| ≤ delta := by
      change boundary - delta ≤ witness coordinate ∧
        witness coordinate ≤ boundary + delta at hwitnessSlab
      rw [abs_le]
      constructor <;> linarith
    have haxisDifference :
        |axisPoint coordinate - axisWitness coordinate| ≤
          4 * speed := by
      rw [haxisPointEq, haxisWitnessEq]
      have heq :
          (wz1TubeAxisZeroPoint tube +
                pointParameter • wz1PaperDirection tube) coordinate -
              (wz1TubeAxisZeroPoint tube +
                witnessParameter • wz1PaperDirection tube) coordinate =
            (pointParameter - witnessParameter) *
              wz1PaperDirection tube coordinate := by
        simp
        ring
      rw [heq, abs_mul]
      have hparameterDifference :
          |pointParameter - witnessParameter| ≤ 4 := by
        rw [abs_le]
        constructor <;>
          linarith [hpointParameter.1, hpointParameter.2,
            hwitnessParameter.1, hwitnessParameter.2]
      gcongr
    have hsum :
        |point coordinate - boundary| ≤
          |point coordinate - axisPoint coordinate| +
            |axisPoint coordinate - axisWitness coordinate| +
            |axisWitness coordinate - witness coordinate| +
            |witness coordinate - boundary| := by
      have heq :
          point coordinate - boundary =
            (point coordinate - axisPoint coordinate) +
              (axisPoint coordinate - axisWitness coordinate) +
              (axisWitness coordinate - witness coordinate) +
              (witness coordinate - boundary) := by ring
      rw [heq]
      calc
        |(point coordinate - axisPoint coordinate) +
              (axisPoint coordinate - axisWitness coordinate) +
              (axisWitness coordinate - witness coordinate) +
              (witness coordinate - boundary)|
            ≤
          |(point coordinate - axisPoint coordinate) +
              (axisPoint coordinate - axisWitness coordinate) +
              (axisWitness coordinate - witness coordinate)| +
            |witness coordinate - boundary| := abs_add_le _ _
        _ ≤
          (|(point coordinate - axisPoint coordinate) +
                (axisPoint coordinate - axisWitness coordinate)| +
              |axisWitness coordinate - witness coordinate|) +
            |witness coordinate - boundary| := by
              gcongr
              exact abs_add_le _ _
        _ ≤
          ((|point coordinate - axisPoint coordinate| +
                |axisPoint coordinate - axisWitness coordinate|) +
              |axisWitness coordinate - witness coordinate|) +
            |witness coordinate - boundary| := by
              gcongr
              exact abs_add_le _ _
    have hwitnessAxisCoordinate' :
        |axisWitness coordinate - witness coordinate| ≤
          24 * delta := by
      simpa [abs_sub_comm] using hwitnessAxisCoordinate
    linarith [hpointAxisCoordinate, haxisDifference,
      hwitnessAxisCoordinate', hwitnessBoundary]
  change
    boundary - (4 * speed + 49 * delta) ≤ point coordinate ∧
      point coordinate ≤ boundary + (4 * speed + 49 * delta)
  rw [abs_le] at hpointCoordinate
  constructor <;> linarith

theorem wz2_paper_slow_boundary_shading_mass
    {delta speed boundary : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hspeed : 0 < speed)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (coordinate : Fin 3)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    let slow :=
      wz2PaperSlowBoundaryTubeIndices
        family coordinate boundary speed
    (∑ index ∈ slow,
        volume (shading.carrier index)) ≤
      (C *
          ENNReal.ofReal
            (16 * (4 * speed + 49 * delta)) *
          family.enncard) *
        (55296 * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta 2) := by
  dsimp only
  let slow :=
    wz2PaperSlowBoundaryTubeIndices
      family coordinate boundary speed
  let container :=
    wz2PaperBoundaryContainer coordinate boundary
      (4 * speed + 49 * delta)
  have hwidth :
      0 < 4 * speed + 49 * delta := by positivity
  have hcontained :
      ∀ index ∈ slow,
        wz1PaperTubeCarrier (family.tube index) ⊆
          container := by
    intro index hindex
    have hdata := Finset.mem_filter.mp hindex
    exact
      wz2_paper_slow_boundary_tube_contained
        hdelta hspeed.le (family.tube index)
        (hline index) coordinate hdata.2.1 hdata.2.2
  have hslowCard :
      (slow.card : ENNReal) ≤
        C * volume container * family.enncard := by
    have h := hcwa container
      (convex_wz2PaperBoundaryContainer coordinate boundary
        (4 * speed + 49 * delta))
    change
      (((Finset.univ :
          Finset (Fin family.card)).filter fun index =>
        wz1PaperTubeCarrier (family.tube index) ⊆
          container).card : ENNReal) ≤
        C * volume container * family.enncard at h
    have hsubset :
        slow ⊆
          (Finset.univ :
            Finset (Fin family.card)).filter fun index =>
              wz1PaperTubeCarrier (family.tube index) ⊆
                container := by
      intro index hindex
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hcontained index hindex⟩
    have hcardNat :
        slow.card ≤
          ((Finset.univ :
            Finset (Fin family.card)).filter fun index =>
              wz1PaperTubeCarrier (family.tube index) ⊆
                container).card :=
      Finset.card_le_card hsubset
    have hcardENN :
        (slow.card : ENNReal) ≤
          (((Finset.univ :
            Finset (Fin family.card)).filter fun index =>
              wz1PaperTubeCarrier (family.tube index) ⊆
                container).card : ENNReal) := by
      exact_mod_cast hcardNat
    exact hcardENN.trans h
  have hcontainerVolume :
      volume container ≤
        ENNReal.ofReal
          (16 * (4 * speed + 49 * delta)) :=
    volume_wz2PaperBoundaryContainer_le coordinate boundary
      (4 * speed + 49 * delta) hwidth
  have hslowCard' :
      (slow.card : ENNReal) ≤
        C *
          ENNReal.ofReal
            (16 * (4 * speed + 49 * delta)) *
          family.enncard := by
    calc
      (slow.card : ENNReal) ≤
          C * volume container * family.enncard := hslowCard
      _ ≤
          C *
            ENNReal.ofReal
              (16 * (4 * speed + 49 * delta)) *
            family.enncard := by
        gcongr
  let tubeUpper : ENNReal :=
    55296 * Kakeya.deltaTubeVolume 1 *
      Kakeya.realRpowENN delta 2
  have hterm :
      ∀ index,
        volume (shading.carrier index) ≤ tubeUpper := by
    intro index
    exact
      (measure_mono (shading.subset_body index)).trans
        (wz2PaperTubeCarrier_convex_and_volume_quadratic
          wz2_paper_tube_carrier_geometry
          hdelta hdeltaSmall (family.tube index)
          (hline index)).2
  calc
    (∑ index ∈ slow,
        volume (shading.carrier index))
        ≤ ∑ _index ∈ slow, tubeUpper := by
      exact Finset.sum_le_sum fun index _ => hterm index
    _ = (slow.card : ENNReal) * tubeUpper := by
      simp [Finset.sum_const]
    _ ≤
        (C *
            ENNReal.ofReal
              (16 * (4 * speed + 49 * delta)) *
            family.enncard) *
          tubeUpper := by
      gcongr
    _ =
        (C *
            ENNReal.ofReal
              (16 * (4 * speed + 49 * delta)) *
            family.enncard) *
          (55296 * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2) := rfl

end Kakeya.Assouad

end
