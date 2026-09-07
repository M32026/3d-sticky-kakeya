import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoordinateSlabVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSubfamilyZeroExtension
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCropBoundaryGeometry

/-!
# Aggregate shaded mass near the cropped paper boundary

For each of the six crop faces, split tubes by one coordinate speed.  Slow
tubes meeting the face lie in one common convex strip and are counted by the
ambient normalized Convex-Wolff bound.  Fast tubes contribute only a short
slab segment.  The selected-subfamily version is obtained by zero extension
to the ambient family, not by a false hereditary CWA assertion.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

private def wz2PaperCropFace
    (rho boundary : ℝ) (coordinate : Fin 3) : Set Point3 :=
  Kakeya.Streamlined.axisBox 2 2 2 ∩
    coordinateSlab coordinate (boundary - rho) (boundary + rho)

private def wz2PaperCropSlowIndices
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (rho boundary speed : ℝ)
    (coordinate : Fin 3) : Finset (Fin family.card) :=
  Finset.univ.filter fun index =>
    |wz1PaperDirection (family.tube index) coordinate| ≤ speed ∧
      (wz1PaperTubeCarrier (family.tube index) ∩
        coordinateSlab coordinate (boundary - rho) (boundary + rho)
      ).Nonempty

private def wz2PaperCropSlowContainer
    (delta rho boundary speed : ℝ)
    (coordinate : Fin 3) : Set Point3 :=
  Kakeya.Streamlined.axisBox 2 2 2 ∩
    coordinateSlab coordinate
      (boundary - (4 * speed + 48 * delta + rho))
      (boundary + (4 * speed + 48 * delta + rho))

private theorem convex_wz2PaperCropSlowContainer
    (delta rho boundary speed : ℝ)
    (coordinate : Fin 3) :
    Convex ℝ
      (wz2PaperCropSlowContainer
        delta rho boundary speed coordinate) := by
  apply (Kakeya.Streamlined.convex_axisBox 2 2 2).inter
  let projection : Point3 →ₗ[ℝ] ℝ :=
    { toFun := fun point => point coordinate
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change Convex ℝ
    (projection ⁻¹'
      Set.Icc
        (boundary - (4 * speed + 48 * delta + rho))
        (boundary + (4 * speed + 48 * delta + rho)))
  exact (convex_Icc _ _).linear_preimage projection

private theorem volume_wz2PaperCropSlowContainer_le
    {delta rho speed boundary : ℝ}
    (hwidth : 0 < 4 * speed + 48 * delta + rho)
    (coordinate : Fin 3) :
    volume
        (wz2PaperCropSlowContainer
          delta rho boundary speed coordinate) ≤
      ENNReal.ofReal
        (16 * (4 * speed + 48 * delta + rho)) := by
  let width := 4 * speed + 48 * delta + rho
  have hsubset :
      wz2PaperCropSlowContainer
          delta rho boundary speed coordinate ⊆
        {point : Point3 |
          point ∈ Kakeya.Streamlined.axisBox 2 2 2 ∧
            |point coordinate - boundary| < 2 * width} := by
    intro point hpoint
    refine ⟨hpoint.1, ?_⟩
    have hslab := hpoint.2
    change
      boundary - width ≤ point coordinate ∧
        point coordinate ≤ boundary + width at hslab
    rw [abs_lt]
    constructor <;> linarith [hslab.1, hslab.2]
  exact
    (measure_mono hsubset).trans
      (boundary_slab_volume_le coordinate boundary
        (2 * width) (by positivity))
      |>.trans (by
        apply ENNReal.ofReal_mono
        dsimp only [width]
        ring_nf
        exact le_rfl)

private theorem wz2_paper_crop_slow_tube_contained
    {delta rho speed boundary : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 ≤ rho)
    (hspeed : 0 ≤ speed)
    (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube)
    (coordinate : Fin 3)
    (hslow :
      |wz1PaperDirection tube coordinate| ≤ speed)
    (hmeets :
      (wz1PaperTubeCarrier tube ∩
        coordinateSlab coordinate
          (boundary - rho) (boundary + rho)).Nonempty) :
    wz1PaperTubeCarrier tube ⊆
      wz2PaperCropSlowContainer
        delta rho boundary speed coordinate := by
  rcases hmeets with ⟨witness, hwitnessTube, hwitnessSlab⟩
  have hgeometry :=
    wz2_paper_tube_carrier_geometry hdelta tube hline
  have hwitnessCore :
      ∃ axisWitness ∈ wz2PaperAxisCoreSegment tube,
        dist witness axisWitness ≤ 24 * delta :=
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
        dist point axisPoint ≤ 24 * delta :=
    exists_dist_le_of_mem_cthickening_closed
      (wz2PaperAxisCoreSegment_compact tube).isClosed
      (by positivity) (hgeometry.2 hpoint)
  rcases hpointCore with
    ⟨axisPoint, haxisPoint, hpointAxisDist⟩
  rw [wz2PaperAxisCoreSegment_eq] at haxisPoint
  rcases haxisPoint with
    ⟨pointParameter, hpointParameter, haxisPointEq⟩
  have hpointAxisCoordinate :
      |point coordinate - axisPoint coordinate| ≤ 24 * delta :=
    (abs_coord_sub_le_dist coordinate).trans hpointAxisDist
  have hwitnessAxisCoordinate :
      |axisWitness coordinate - witness coordinate| ≤ 24 * delta := by
    simpa [abs_sub_comm] using
      (abs_coord_sub_le_dist coordinate).trans hwitnessAxisDist
  have hwitnessBoundary :
      |witness coordinate - boundary| ≤ rho := by
    change
      boundary - rho ≤ witness coordinate ∧
        witness coordinate ≤ boundary + rho at hwitnessSlab
    rw [abs_le]
    constructor <;> linarith [hwitnessSlab.1, hwitnessSlab.2]
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
  have htotal :
      |point coordinate - boundary| ≤
        4 * speed + 48 * delta + rho := by
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
        |point coordinate - axisPoint coordinate| +
          |axisPoint coordinate - axisWitness coordinate| +
          |axisWitness coordinate - witness coordinate| +
          |witness coordinate - boundary| := by
        calc
          |(point coordinate - axisPoint coordinate) +
                (axisPoint coordinate - axisWitness coordinate) +
                (axisWitness coordinate - witness coordinate) +
                (witness coordinate - boundary)|
              ≤
            |(point coordinate - axisPoint coordinate) +
                (axisPoint coordinate - axisWitness coordinate) +
                (axisWitness coordinate - witness coordinate)| +
              |witness coordinate - boundary| :=
            abs_add_le _ _
          _ ≤
            (|(point coordinate - axisPoint coordinate) +
                (axisPoint coordinate - axisWitness coordinate)| +
              |axisWitness coordinate - witness coordinate|) +
              |witness coordinate - boundary| := by
            gcongr
            exact abs_add_le _ _
          _ ≤
            (|point coordinate - axisPoint coordinate| +
              |axisPoint coordinate - axisWitness coordinate| +
              |axisWitness coordinate - witness coordinate|) +
              |witness coordinate - boundary| := by
            gcongr
            exact abs_add_le _ _
      _ ≤
          24 * delta + 4 * speed + 24 * delta + rho := by
        gcongr
      _ = 4 * speed + 48 * delta + rho := by ring
  change
    boundary - (4 * speed + 48 * delta + rho) ≤
        point coordinate ∧
      point coordinate ≤
        boundary + (4 * speed + 48 * delta + rho)
  rw [abs_le] at htotal
  constructor <;> linarith [htotal.1, htotal.2]

private theorem wz2_paper_crop_slow_face_mass
    {delta rho speed boundary : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hspeed : 0 < speed)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (coordinate : Fin 3)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    let slow :=
      wz2PaperCropSlowIndices
        family rho boundary speed coordinate
    (∑ index ∈ slow,
        volume (shading.carrier index)) ≤
      (C *
          ENNReal.ofReal
            (16 * (4 * speed + 48 * delta + rho)) *
          family.enncard) *
        (55296 * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta 2) := by
  dsimp only
  let slow :=
    wz2PaperCropSlowIndices
      family rho boundary speed coordinate
  let container :=
    wz2PaperCropSlowContainer delta rho boundary speed coordinate
  have hwidth : 0 < 4 * speed + 48 * delta + rho := by positivity
  have hcontained :
      ∀ index ∈ slow,
        wz1PaperTubeCarrier (family.tube index) ⊆ container := by
    intro index hindex
    have hdata := Finset.mem_filter.mp hindex
    exact
      wz2_paper_crop_slow_tube_contained
        hdelta hrho.le hspeed.le (family.tube index)
        (hline index) coordinate hdata.2.1 hdata.2.2
  have hslowCard :
      (slow.card : ENNReal) ≤
        C * volume container * family.enncard := by
    have h :=
      hcwa container
        (convex_wz2PaperCropSlowContainer
          delta rho boundary speed coordinate)
    change
      (((Finset.univ : Finset (Fin family.card)).filter fun index =>
        wz1PaperTubeCarrier (family.tube index) ⊆
          container).card : ENNReal) ≤
        C * volume container * family.enncard at h
    exact
      (show (slow.card : ENNReal) ≤
          (((Finset.univ : Finset (Fin family.card)).filter fun index =>
            wz1PaperTubeCarrier (family.tube index) ⊆
              container).card : ENNReal) by
        exact_mod_cast Finset.card_le_card <| by
          intro index hindex
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hcontained index hindex⟩).trans h
  have hcontainerVolume :
      volume container ≤
        ENNReal.ofReal
          (16 * (4 * speed + 48 * delta + rho)) :=
    volume_wz2PaperCropSlowContainer_le hwidth coordinate
  let tubeUpper : ENNReal :=
    55296 * Kakeya.deltaTubeVolume 1 *
      Kakeya.realRpowENN delta 2
  calc
    (∑ index ∈ slow, volume (shading.carrier index))
        ≤ ∑ _index ∈ slow, tubeUpper := by
      exact Finset.sum_le_sum fun index _ =>
        (measure_mono (shading.subset_body index)).trans
          (wz2PaperTubeCarrier_convex_and_volume_quadratic
            wz2_paper_tube_carrier_geometry
            hdelta hdeltaSmall (family.tube index)
            (hline index)).2
    _ = (slow.card : ENNReal) * tubeUpper := by
      simp [Finset.sum_const]
    _ ≤
        (C *
            ENNReal.ofReal
              (16 * (4 * speed + 48 * delta + rho)) *
            family.enncard) *
          tubeUpper := by
      gcongr
      exact hslowCard.trans (by gcongr)
    _ =
        (C *
            ENNReal.ofReal
              (16 * (4 * speed + 48 * delta + rho)) *
            family.enncard) *
          (55296 * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2) := rfl

private theorem wz2_paper_crop_fast_face_mass
    {delta rho speed boundary : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hspeed : 0 < speed)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (coordinate : Fin 3) :
    let fast :=
      (Finset.univ : Finset (Fin family.card)).filter fun index =>
        speed ≤
          |wz1PaperDirection (family.tube index) coordinate|
    (∑ index ∈ fast,
        volume
          (shading.carrier index ∩
            coordinateSlab coordinate
              (boundary - rho) (boundary + rho))) ≤
      family.enncard *
        (4 *
          ENNReal.ofReal
            (Real.pi * (24 * delta) ^ 2 *
              ((2 * rho + 2 * (24 * delta)) / speed +
                2 * (24 * delta)))) := by
  dsimp only
  let fast :=
    (Finset.univ : Finset (Fin family.card)).filter fun index =>
      speed ≤
        |wz1PaperDirection (family.tube index) coordinate|
  calc
    (∑ index ∈ fast,
        volume
          (shading.carrier index ∩
            coordinateSlab coordinate
              (boundary - rho) (boundary + rho)))
        ≤
      ∑ _index ∈ fast,
        4 *
          ENNReal.ofReal
            (Real.pi * (24 * delta) ^ 2 *
              ((2 * rho + 2 * (24 * delta)) / speed +
                2 * (24 * delta))) := by
      apply Finset.sum_le_sum
      intro index hindex
      have hSubset :
          shading.carrier index ∩
              coordinateSlab coordinate
                (boundary - rho) (boundary + rho) ⊆
            wz1PaperTubeCarrier (family.tube index) ∩
              coordinateSlab coordinate
                (boundary - rho) (boundary + rho) := by
        intro point hpoint
        exact ⟨shading.subset_body index hpoint.1, hpoint.2⟩
      have hRaw :
          volume
              (wz1PaperTubeCarrier (family.tube index) ∩
                coordinateSlab coordinate
                  (boundary - rho) (boundary + rho)) ≤
            4 *
              ENNReal.ofReal
                (Real.pi * (24 * delta) ^ 2 *
                  (((boundary + rho) - (boundary - rho) +
                        2 * (24 * delta)) /
                      speed +
                    2 * (24 * delta))) :=
        wz2_paper_tube_coordinate_slab_volume
          hdelta hdeltaSmall (by linarith) hspeed
          (family.tube index) (hline index) coordinate
          (Finset.mem_filter.mp hindex).2
      refine (measure_mono hSubset).trans ?_
      have hWidth :
          boundary + rho - (boundary - rho) = 2 * rho := by
        ring
      rw [hWidth] at hRaw
      exact hRaw
    _ =
      (fast.card : ENNReal) *
        (4 *
          ENNReal.ofReal
            (Real.pi * (24 * delta) ^ 2 *
              ((2 * rho + 2 * (24 * delta)) / speed +
                2 * (24 * delta)))) := by
      simp [Finset.sum_const]
    _ ≤
      family.enncard *
        (4 *
          ENNReal.ofReal
            (Real.pi * (24 * delta) ^ 2 *
              ((2 * rho + 2 * (24 * delta)) / speed +
                2 * (24 * delta)))) := by
      gcongr
      change (fast.card : ENNReal) ≤ (family.card : ENNReal)
      exact_mod_cast (by
        simpa [Fintype.card_fin] using Finset.card_le_univ fast)

private theorem wz2_paper_crop_face_mass
    {delta rho speed boundary : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hspeed : 0 < speed)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (coordinate : Fin 3)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            coordinateSlab coordinate
              (boundary - rho) (boundary + rho))) ≤
      (C *
          ENNReal.ofReal
            (16 * (4 * speed + 48 * delta + rho)) *
          family.enncard) *
        (55296 * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta 2) +
        family.enncard *
          (4 *
            ENNReal.ofReal
              (Real.pi * (24 * delta) ^ 2 *
                ((2 * rho + 2 * (24 * delta)) / speed +
                  2 * (24 * delta)))) := by
  let weight : Fin family.card → ENNReal := fun index =>
    volume
      (shading.carrier index ∩
        coordinateSlab coordinate
          (boundary - rho) (boundary + rho))
  let slow :=
    (Finset.univ : Finset (Fin family.card)).filter fun index =>
      |wz1PaperDirection (family.tube index) coordinate| ≤ speed
  let notSlow :=
    (Finset.univ : Finset (Fin family.card)).filter fun index =>
      ¬ |wz1PaperDirection (family.tube index) coordinate| ≤ speed
  let meetingSlow :=
    wz2PaperCropSlowIndices
      family rho boundary speed coordinate
  let fast :=
    (Finset.univ : Finset (Fin family.card)).filter fun index =>
      speed ≤ |wz1PaperDirection (family.tube index) coordinate|
  have hPartition :
      (∑ index : Fin family.card, weight index) =
        (∑ index ∈ slow, weight index) +
          ∑ index ∈ notSlow, weight index := by
    simpa [slow, notSlow] using
      (Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset (Fin family.card))
        (fun index =>
          |wz1PaperDirection (family.tube index) coordinate| ≤ speed)
        weight).symm
  have hSlow :
      (∑ index ∈ slow, weight index) ≤
        ∑ index ∈ meetingSlow,
          volume (shading.carrier index) := by
    let activeSlow :=
      slow.filter fun index =>
        (wz1PaperTubeCarrier (family.tube index) ∩
          coordinateSlab coordinate
            (boundary - rho) (boundary + rho)).Nonempty
    have hActiveSubset : activeSlow ⊆ meetingSlow := by
      intro index hindex
      have hdata := Finset.mem_filter.mp hindex
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hdata.1).2, hdata.2⟩
    calc
      (∑ index ∈ slow, weight index) =
          ∑ index ∈ activeSlow, weight index := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro index hindex hnot
        have hNoMeet :
            ¬ (wz1PaperTubeCarrier (family.tube index) ∩
              coordinateSlab coordinate
                (boundary - rho) (boundary + rho)).Nonempty := by
          intro hmeet
          exact hnot (Finset.mem_filter.mpr ⟨hindex, hmeet⟩)
        have hEmpty :
            shading.carrier index ∩
                coordinateSlab coordinate
                  (boundary - rho) (boundary + rho) = ∅ := by
          apply Set.not_nonempty_iff_eq_empty.mp
          intro hnonempty
          rcases hnonempty with ⟨point, hpointShade, hpointSlab⟩
          exact hNoMeet
            ⟨point, shading.subset_body index hpointShade, hpointSlab⟩
        dsimp only [weight]
        rw [hEmpty]
        simp
      _ ≤
          ∑ index ∈ activeSlow,
            volume (shading.carrier index) := by
        exact Finset.sum_le_sum fun index _ =>
          measure_mono Set.inter_subset_left
      _ ≤
          ∑ index ∈ meetingSlow,
            volume (shading.carrier index) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          hActiveSubset (fun _ _ _ => bot_le)
  have hNotSlowSubset : notSlow ⊆ fast := by
    intro index hindex
    have hnot := (Finset.mem_filter.mp hindex).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, le_of_not_ge hnot⟩
  have hNotSlow :
      (∑ index ∈ notSlow, weight index) ≤
        ∑ index ∈ fast, weight index := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      hNotSlowSubset (fun _ _ _ => bot_le)
  have hSlowBound :=
    wz2_paper_crop_slow_face_mass
      hdelta hdeltaSmall hrho hspeed hline shading
      coordinate hcwa (boundary := boundary)
  have hFastBound :=
    wz2_paper_crop_fast_face_mass
      hdelta hdeltaSmall hrho hspeed hline shading coordinate
      (boundary := boundary)
  change (∑ index : Fin family.card, weight index) ≤ _
  calc
    (∑ index : Fin family.card, weight index) =
        (∑ index ∈ slow, weight index) +
          ∑ index ∈ notSlow, weight index := hPartition
    _ ≤
        (∑ index ∈ meetingSlow,
            volume (shading.carrier index)) +
          ∑ index ∈ fast, weight index :=
      add_le_add hSlow hNotSlow
    _ ≤
        (C *
            ENNReal.ofReal
              (16 * (4 * speed + 48 * delta + rho)) *
            family.enncard) *
          (55296 * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2) +
          family.enncard *
            (4 *
              ENNReal.ofReal
                (Real.pi * (24 * delta) ^ 2 *
                  ((2 * rho + 2 * (24 * delta)) / speed +
                    2 * (24 * delta)))) := by
      exact add_le_add hSlowBound hFastBound

theorem wz2_paper_crop_boundary_mass
    {delta rho speed : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hspeed : 0 < speed)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            wz2PaperCropBoundaryRegion rho)) ≤
      6 *
        ((C *
            ENNReal.ofReal
              (16 * (4 * speed + 48 * delta + rho)) *
            family.enncard) *
          (55296 * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2) +
          family.enncard *
            (4 *
              ENNReal.ofReal
                (Real.pi * (24 * delta) ^ 2 *
                  ((2 * rho + 2 * (24 * delta)) / speed +
                    2 * (24 * delta))))) := by
  let faceBound : ENNReal :=
    (C *
        ENNReal.ofReal
          (16 * (4 * speed + 48 * delta + rho)) *
        family.enncard) *
      (55296 * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2) +
      family.enncard *
        (4 *
          ENNReal.ofReal
            (Real.pi * (24 * delta) ^ 2 *
              ((2 * rho + 2 * (24 * delta)) / speed +
                2 * (24 * delta))))
  let positiveFace : Fin 3 → Set Point3 := fun coordinate =>
    coordinateSlab coordinate (1 - rho) (1 + rho)
  let negativeFace : Fin 3 → Set Point3 := fun coordinate =>
    coordinateSlab coordinate (-1 - rho) (-1 + rho)
  have hCropSubset :
      wz2PaperCropBoundaryRegion rho ⊆
        (⋃ coordinate : Fin 3, positiveFace coordinate) ∪
          ⋃ coordinate : Fin 3, negativeFace coordinate := by
    intro point hpoint
    rcases hpoint with ⟨hbox, coordinate, hboundary⟩
    have hcoordinate : |point coordinate| ≤ 1 := by
      have h := hbox
      simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at h
      norm_num at h
      fin_cases coordinate <;> tauto
    by_cases hnonnegative : 0 ≤ point coordinate
    · apply Or.inl
      apply Set.mem_iUnion.mpr
      refine ⟨coordinate, ?_⟩
      change
        1 - rho ≤ point coordinate ∧
          point coordinate ≤ 1 + rho
      rw [abs_of_nonneg hnonnegative] at hboundary hcoordinate
      constructor <;> linarith
    · apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨coordinate, ?_⟩
      change
        -1 - rho ≤ point coordinate ∧
          point coordinate ≤ -1 + rho
      have hnegative : point coordinate < 0 :=
        lt_of_not_ge hnonnegative
      rw [abs_of_neg hnegative] at hboundary hcoordinate
      constructor <;> linarith
  have hPointwise :
      ∀ index : Fin family.card,
        volume
            (shading.carrier index ∩
              wz2PaperCropBoundaryRegion rho) ≤
          (∑ coordinate : Fin 3,
              volume
                (shading.carrier index ∩
                  positiveFace coordinate)) +
            ∑ coordinate : Fin 3,
              volume
                (shading.carrier index ∩
                  negativeFace coordinate) := by
    intro index
    have hsubset :
        shading.carrier index ∩
            wz2PaperCropBoundaryRegion rho ⊆
          (⋃ coordinate : Fin 3,
              shading.carrier index ∩ positiveFace coordinate) ∪
            ⋃ coordinate : Fin 3,
              shading.carrier index ∩ negativeFace coordinate := by
      intro point hpoint
      rcases hCropSubset hpoint.2 with hpositive | hnegative
      · rcases Set.mem_iUnion.mp hpositive with
          ⟨coordinate, hcoordinate⟩
        exact Or.inl <| Set.mem_iUnion.mpr
          ⟨coordinate, hpoint.1, hcoordinate⟩
      · rcases Set.mem_iUnion.mp hnegative with
          ⟨coordinate, hcoordinate⟩
        exact Or.inr <| Set.mem_iUnion.mpr
          ⟨coordinate, hpoint.1, hcoordinate⟩
    calc
      volume
          (shading.carrier index ∩
            wz2PaperCropBoundaryRegion rho) ≤
        volume
          ((⋃ coordinate : Fin 3,
              shading.carrier index ∩ positiveFace coordinate) ∪
            ⋃ coordinate : Fin 3,
              shading.carrier index ∩ negativeFace coordinate) :=
        measure_mono hsubset
      _ ≤
          volume
              (⋃ coordinate : Fin 3,
                shading.carrier index ∩ positiveFace coordinate) +
            volume
              (⋃ coordinate : Fin 3,
                shading.carrier index ∩ negativeFace coordinate) :=
        measure_union_le _ _
      _ ≤
          (∑ coordinate : Fin 3,
              volume
                (shading.carrier index ∩
                  positiveFace coordinate)) +
            ∑ coordinate : Fin 3,
              volume
                (shading.carrier index ∩
                  negativeFace coordinate) := by
        gcongr
        · exact MeasureTheory.measure_iUnion_fintype_le _ _
        · exact MeasureTheory.measure_iUnion_fintype_le _ _
  have hPositive :
      ∀ coordinate : Fin 3,
        (∑ index : Fin family.card,
            volume
              (shading.carrier index ∩
                positiveFace coordinate)) ≤ faceBound := by
    intro coordinate
    simpa [positiveFace, faceBound] using
      wz2_paper_crop_face_mass
        hdelta hdeltaSmall hrho hspeed hline shading
        coordinate hcwa (boundary := 1)
  have hNegative :
      ∀ coordinate : Fin 3,
        (∑ index : Fin family.card,
            volume
              (shading.carrier index ∩
                negativeFace coordinate)) ≤ faceBound := by
    intro coordinate
    simpa [negativeFace, faceBound] using
      wz2_paper_crop_face_mass
        hdelta hdeltaSmall hrho hspeed hline shading
        coordinate hcwa (boundary := -1)
  calc
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            wz2PaperCropBoundaryRegion rho)) ≤
      ∑ index : Fin family.card,
        ((∑ coordinate : Fin 3,
            volume
              (shading.carrier index ∩
                positiveFace coordinate)) +
          ∑ coordinate : Fin 3,
            volume
              (shading.carrier index ∩
                negativeFace coordinate)) := by
      exact Finset.sum_le_sum fun index _ => hPointwise index
    _ =
      (∑ coordinate : Fin 3,
          ∑ index : Fin family.card,
            volume
              (shading.carrier index ∩
                positiveFace coordinate)) +
        ∑ coordinate : Fin 3,
          ∑ index : Fin family.card,
            volume
              (shading.carrier index ∩
                negativeFace coordinate) := by
      rw [Finset.sum_add_distrib]
      congr 1 <;> exact Finset.sum_comm
    _ ≤
        (∑ _coordinate : Fin 3, faceBound) +
          ∑ _coordinate : Fin 3, faceBound := by
      gcongr
      · exact hPositive _
      · exact hNegative _
    _ = 6 * faceBound := by
      simp [Finset.sum_const]
      ring
    _ =
      6 *
        ((C *
            ENNReal.ofReal
              (16 * (4 * speed + 48 * delta + rho)) *
            family.enncard) *
          (55296 * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2) +
          family.enncard *
            (4 *
              ENNReal.ofReal
                (Real.pi * (24 * delta) ^ 2 *
                  ((2 * rho + 2 * (24 * delta)) / speed +
                    2 * (24 * delta))))) := rfl

theorem wz2_paper_subfamily_crop_boundary_mass
    {delta rho speed : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hspeed : 0 < speed)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (shading : WZ1PaperTubeShading selected.family)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    (∑ index : Fin selected.family.card,
        volume
          (shading.carrier index ∩
            wz2PaperCropBoundaryRegion rho)) ≤
      6 *
        ((C *
            ENNReal.ofReal
              (16 * (4 * speed + 48 * delta + rho)) *
            family.enncard) *
          (55296 * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2) +
          family.enncard *
            (4 *
              ENNReal.ofReal
                (Real.pi * (24 * delta) ^ 2 *
                  ((2 * rho + 2 * (24 * delta)) / speed +
                    2 * (24 * delta))))) := by
  rcases
      wz2_paper_subfamily_zero_extension selected shading with
    ⟨zeroExtension⟩
  have hAmbient :=
    wz2_paper_crop_boundary_mass
      hdelta hdeltaSmall hrho hspeed hline
      zeroExtension.ambientShading hcwa
  have hBoundaryEq :
      (∑ index : Fin family.card,
          volume
            (zeroExtension.ambientShading.carrier index ∩
              wz2PaperCropBoundaryRegion rho)) =
        ∑ index : Fin selected.family.card,
          volume
            (shading.carrier index ∩
              wz2PaperCropBoundaryRegion rho) := by
    let selectedImage : Finset (Fin family.card) :=
      Finset.image selected.embedding Finset.univ
    calc
      (∑ index : Fin family.card,
          volume
            (zeroExtension.ambientShading.carrier index ∩
              wz2PaperCropBoundaryRegion rho)) =
          ∑ index ∈ selectedImage,
            volume
              (zeroExtension.ambientShading.carrier index ∩
                wz2PaperCropBoundaryRegion rho) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro index _ hindex
        have hEmpty :
            zeroExtension.ambientShading.carrier index = ∅ := by
          apply Set.not_nonempty_iff_eq_empty.mp
          intro hnonempty
          rcases hnonempty with ⟨point, hpoint⟩
          rcases zeroExtension.carrier_support index point hpoint with
            ⟨sourceIndex, hsource, _⟩
          exact hindex <|
            Finset.mem_image.mpr
              ⟨sourceIndex, Finset.mem_univ _, hsource⟩
        rw [hEmpty]
        simp
      _ =
          ∑ sourceIndex : Fin selected.family.card,
            volume
              (zeroExtension.ambientShading.carrier
                  (selected.embedding sourceIndex) ∩
                wz2PaperCropBoundaryRegion rho) := by
        rw [Finset.sum_image]
        intro first _ second _ h
        exact selected.embedding.injective h
      _ =
          ∑ sourceIndex : Fin selected.family.card,
            volume
              (shading.carrier sourceIndex ∩
                wz2PaperCropBoundaryRegion rho) := by
        apply Finset.sum_congr rfl
        intro sourceIndex _
        rw [zeroExtension.carrier_embedding sourceIndex]
  rw [← hBoundaryEq]
  exact hAmbient

end Kakeya.Assouad

end
