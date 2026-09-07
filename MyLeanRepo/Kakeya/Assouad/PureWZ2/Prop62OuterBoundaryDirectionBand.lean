import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FixedGridDyadicSum

/-!
# Proposition 6.2 outer boundary: one direction band

This is the one-face analogue of the direction-band estimate in
`WZ2_prop62.tex`, Lemma `prop62-fixed-grid`, with slab half-width `rho`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def pureWZ2Prop62OuterBoundaryContainer
    (delta rho boundary speed : ℝ)
    (coordinate : Fin 3) : Set Point3 :=
  Kakeya.Streamlined.axisBox 2 2 2 ∩
    coordinateSlab coordinate
      (boundary - (4 * speed + 48 * delta + rho))
      (boundary + (4 * speed + 48 * delta + rho))

theorem convex_pureWZ2Prop62OuterBoundaryContainer
    (delta rho boundary speed : ℝ)
    (coordinate : Fin 3) :
    Convex ℝ
      (pureWZ2Prop62OuterBoundaryContainer
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

theorem volume_pureWZ2Prop62OuterBoundaryContainer_le
    {delta rho boundary speed : ℝ}
    (hwidth : 0 < 4 * speed + 48 * delta + rho)
    (coordinate : Fin 3) :
    volume
        (pureWZ2Prop62OuterBoundaryContainer
          delta rho boundary speed coordinate) ≤
      ENNReal.ofReal
        (16 * (4 * speed + 48 * delta + rho)) := by
  let width := 4 * speed + 48 * delta + rho
  have hsubset :
      pureWZ2Prop62OuterBoundaryContainer
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

theorem pureWZ2_prop62_outer_slow_tube_contained
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
      pureWZ2Prop62OuterBoundaryContainer
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

def pureWZ2Prop62OuterDirectionBandIndices
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (coordinate : Fin 3)
    (boundary rho scale : ℝ) : Finset (Fin family.card) :=
  Finset.univ.filter fun index =>
    scale ≤ |wz1PaperDirection (family.tube index) coordinate| ∧
      |wz1PaperDirection (family.tube index) coordinate| ≤ 2 * scale ∧
      (wz1PaperTubeCarrier (family.tube index) ∩
        coordinateSlab coordinate
          (boundary - rho) (boundary + rho)).Nonempty

theorem pureWZ2_prop62_outer_direction_band_boundary_mass
    {delta rho scale boundary : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hscale : 0 < scale)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (coordinate : Fin 3)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    let band :=
      pureWZ2Prop62OuterDirectionBandIndices
        family coordinate boundary rho scale
    (∑ index ∈ band,
        volume
          (shading.carrier index ∩
            coordinateSlab coordinate
              (boundary - rho) (boundary + rho))) ≤
      (C *
          ENNReal.ofReal
            (16 * (8 * scale + 48 * delta + rho)) *
          family.enncard) *
        (4 *
          ENNReal.ofReal
            (Real.pi * (24 * delta) ^ 2 *
              ((2 * rho + 48 * delta) / scale +
                48 * delta))) := by
  dsimp only
  let band :=
    pureWZ2Prop62OuterDirectionBandIndices
      family coordinate boundary rho scale
  let container :=
    pureWZ2Prop62OuterBoundaryContainer
      delta rho boundary (2 * scale) coordinate
  have hwidthPos :
      0 < 8 * scale + 48 * delta + rho := by positivity
  have hcontained :
      ∀ index ∈ band,
        wz1PaperTubeCarrier (family.tube index) ⊆ container := by
    intro index hindex
    have hdata :=
      (Finset.mem_filter.mp hindex).2
    have hraw :=
      pureWZ2_prop62_outer_slow_tube_contained
        hdelta hrho.le (by positivity : 0 ≤ 2 * scale)
        (family.tube index) (hline index) coordinate
        hdata.2.1 hdata.2.2
    change
      wz1PaperTubeCarrier (family.tube index) ⊆
        pureWZ2Prop62OuterBoundaryContainer
          delta rho boundary (2 * scale) coordinate
    exact hraw
  have hbandCard :
      (band.card : ENNReal) ≤
        C *
          ENNReal.ofReal
            (16 * (8 * scale + 48 * delta + rho)) *
          family.enncard := by
    have hcount :=
      hcwa container
        (convex_pureWZ2Prop62OuterBoundaryContainer
          delta rho boundary (2 * scale) coordinate)
    have hsubset :
        band ⊆
          (Finset.univ : Finset (Fin family.card)).filter fun index =>
            wz1PaperTubeCarrier (family.tube index) ⊆ container := by
      intro index hindex
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hcontained index hindex⟩
    have hcard :
        (band.card : ENNReal) ≤
          (((Finset.univ : Finset (Fin family.card)).filter fun index =>
            wz1PaperTubeCarrier (family.tube index) ⊆ container).card :
              ENNReal) := by
      exact_mod_cast Finset.card_le_card hsubset
    have hvolume :
        volume container ≤
          ENNReal.ofReal
            (16 * (8 * scale + 48 * delta + rho)) := by
      simpa only [container, show
        4 * (2 * scale) + 48 * delta + rho =
          8 * scale + 48 * delta + rho by ring] using
        volume_pureWZ2Prop62OuterBoundaryContainer_le
          (delta := delta) (rho := rho) (boundary := boundary)
          (speed := 2 * scale) (by positivity) coordinate
    exact hcard.trans <| hcount.trans <| by
      gcongr
  let tubeBound : ENNReal :=
    4 *
      ENNReal.ofReal
        (Real.pi * (24 * delta) ^ 2 *
          ((2 * rho + 48 * delta) / scale + 48 * delta))
  have htube :
      ∀ index ∈ band,
        volume
            (shading.carrier index ∩
              coordinateSlab coordinate
                (boundary - rho) (boundary + rho)) ≤
          tubeBound := by
    intro index hindex
    have hdirection :
        scale ≤
          |wz1PaperDirection (family.tube index) coordinate| :=
      ((Finset.mem_filter.mp hindex).2).1
    have hsubset :
        shading.carrier index ∩
            coordinateSlab coordinate
              (boundary - rho) (boundary + rho) ⊆
          wz1PaperTubeCarrier (family.tube index) ∩
            coordinateSlab coordinate
              (boundary - rho) (boundary + rho) := by
      intro point hpoint
      exact ⟨shading.subset_body index hpoint.1, hpoint.2⟩
    have hslab :=
      wz2_paper_tube_coordinate_slab_volume
        hdelta hdeltaSmall (by linarith) hscale
        (family.tube index) (hline index) coordinate hdirection
        (a := boundary - rho) (b := boundary + rho)
    have hlength :
        (boundary + rho - (boundary - rho) +
              2 * (24 * delta)) /
              scale +
            2 * (24 * delta) =
          (2 * rho + 48 * delta) / scale + 48 * delta := by
      field_simp [hscale.ne']
      ring
    rw [hlength] at hslab
    exact (measure_mono hsubset).trans <| by
      simpa only [tubeBound] using hslab
  calc
    (∑ index ∈ band,
        volume
          (shading.carrier index ∩
            coordinateSlab coordinate
              (boundary - rho) (boundary + rho))) ≤
      ∑ _index ∈ band, tubeBound := by
        exact Finset.sum_le_sum fun index hindex =>
          htube index hindex
    _ = (band.card : ENNReal) * tubeBound := by
      simp [Finset.sum_const]
    _ ≤
        (C *
            ENNReal.ofReal
              (16 * (8 * scale + 48 * delta + rho)) *
            family.enncard) *
          tubeBound := by
      gcongr
    _ =
        (C *
            ENNReal.ofReal
              (16 * (8 * scale + 48 * delta + rho)) *
            family.enncard) *
          (4 *
            ENNReal.ofReal
              (Real.pi * (24 * delta) ^ 2 *
                ((2 * rho + 48 * delta) / scale +
                  48 * delta))) := rfl

end Kakeya.Assouad

end
