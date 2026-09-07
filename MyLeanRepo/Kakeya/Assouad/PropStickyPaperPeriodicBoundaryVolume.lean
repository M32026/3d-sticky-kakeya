import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoordinateSlabVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruningGeometry

/-!
# One paper tube against the periodic coarse-grid boundary

For one coordinate, only the coarse-grid hyperplanes met by the cropped tube
can contribute.  The axis parameter lies in `[-2,2]`, so the number of
relevant hyperplanes is controlled by the coordinate speed divided by the
coarse scale.  Summing the explicit-speed slab estimate cancels this speed.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

def wz2PaperRelevantBoundaryIndices
    {delta rho : ℝ}
    (tube : Kakeya.DeltaTube delta)
    (coordinate : Fin 3) : Finset ℤ :=
  let zero := wz1TubeAxisZeroPoint tube coordinate
  let speed := |wz1PaperDirection tube coordinate|
  Finset.Icc
    ⌊(zero - 2 * speed - 25 * delta) / rho⌋
    ⌊(zero + 2 * speed + 25 * delta) / rho⌋

def wz2PaperPeriodicBoundaryRegion
    (delta rho : ℝ)
    (coordinate : Fin 3)
    (indices : Finset ℤ) : Set Point3 :=
  ⋃ boundary ∈ indices,
    coordinateSlab coordinate
      ((boundary : ℝ) * rho - delta)
      ((boundary : ℝ) * rho + delta)

theorem wz2_paper_relevant_boundary_card
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (tube : Kakeya.DeltaTube delta)
    (coordinate : Fin 3) :
    let speed := |wz1PaperDirection tube coordinate|
    ((wz2PaperRelevantBoundaryIndices
      (rho := rho) tube coordinate).card : ℝ) ≤
      (4 * speed + 50 * delta) / rho + 2 := by
  dsimp only
  let zero := wz1TubeAxisZeroPoint tube coordinate
  let speed := |wz1PaperDirection tube coordinate|
  let lo := (zero - 2 * speed - 25 * delta) / rho
  let hi := (zero + 2 * speed + 25 * delta) / rho
  have hlohi : lo ≤ hi := by
    dsimp only [lo, hi]
    have hspeed : 0 ≤ speed := abs_nonneg _
    gcongr
    linarith
  have hcardInt :
      ((Finset.Icc ⌊lo⌋ ⌊hi⌋).card : ℤ) =
        ⌊hi⌋ + 1 - ⌊lo⌋ := by
    exact Int.card_Icc_of_le ⌊lo⌋ ⌊hi⌋
      ((Int.floor_mono hlohi).trans (by omega))
  have hfloorHi : (⌊hi⌋ : ℝ) ≤ hi :=
    Int.floor_le hi
  have hfloorLo : lo < (⌊lo⌋ : ℝ) + 1 :=
    Int.lt_floor_add_one lo
  have hcardReal :
      ((Finset.Icc ⌊lo⌋ ⌊hi⌋).card : ℝ) ≤
        hi - lo + 2 := by
    have hcast :
        ((Finset.Icc ⌊lo⌋ ⌊hi⌋).card : ℝ) =
          (⌊hi⌋ : ℝ) + 1 - (⌊lo⌋ : ℝ) := by
      exact_mod_cast hcardInt
    rw [hcast]
    linarith
  have hdiff :
      hi - lo = (4 * speed + 50 * delta) / rho := by
    dsimp only [hi, lo]
    field_simp [hrho.ne']
    ring
  simpa [wz2PaperRelevantBoundaryIndices, zero, speed, lo, hi,
    hdiff] using hcardReal

theorem wz2_paper_boundary_index_mem_relevant
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube)
    (coordinate : Fin 3)
    (boundary : ℤ)
    {point : Point3}
    (hpoint : point ∈ wz1PaperTubeCarrier tube)
    (hslab :
      point ∈ coordinateSlab coordinate
        ((boundary : ℝ) * rho - delta)
        ((boundary : ℝ) * rho + delta)) :
    boundary ∈
      wz2PaperRelevantBoundaryIndices
        (rho := rho) tube coordinate := by
  have hgeometry :=
    wz2_paper_tube_carrier_geometry hdelta tube hline
  have hcore :
      ∃ axisPoint ∈ wz2PaperAxisCoreSegment tube,
        dist point axisPoint ≤ 24 * delta := by
    exact
      exists_dist_le_of_mem_cthickening_closed
        (wz2PaperAxisCoreSegment_compact tube).isClosed
        (by positivity) (hgeometry.2 hpoint)
  rcases hcore with
    ⟨axisPoint, haxisPoint, hpointAxis⟩
  rw [wz2PaperAxisCoreSegment_eq] at haxisPoint
  rcases haxisPoint with
    ⟨parameter, hparameter, haxisPointEq⟩
  let zero := wz1TubeAxisZeroPoint tube coordinate
  let speed := |wz1PaperDirection tube coordinate|
  have hpointAxisCoordinate :
      |point coordinate - axisPoint coordinate| ≤
        24 * delta :=
    (abs_coord_sub_le_dist coordinate).trans hpointAxis
  have hpointBoundary :
      |point coordinate - (boundary : ℝ) * rho| ≤ delta := by
    change
      (boundary : ℝ) * rho - delta ≤ point coordinate ∧
        point coordinate ≤ (boundary : ℝ) * rho + delta at hslab
    rw [abs_le]
    constructor <;> linarith
  have haxisCoordinate :
      axisPoint coordinate =
        zero +
          parameter * wz1PaperDirection tube coordinate := by
    rw [haxisPointEq]
    simp [zero]
  have hparameterDirection :
      |parameter * wz1PaperDirection tube coordinate| ≤
        2 * speed := by
    rw [abs_mul]
    have hparameterAbs : |parameter| ≤ 2 := by
      rw [abs_le]
      exact hparameter
    gcongr
  have hboundaryRange :
      zero - 2 * speed - 25 * delta ≤
          (boundary : ℝ) * rho ∧
        (boundary : ℝ) * rho ≤
          zero + 2 * speed + 25 * delta := by
    have htotal :
        |(boundary : ℝ) * rho - zero| ≤
          2 * speed + 25 * delta := by
      have heq :
          (boundary : ℝ) * rho - zero =
            ((boundary : ℝ) * rho - point coordinate) +
              (point coordinate - axisPoint coordinate) +
              (axisPoint coordinate - zero) := by ring
      rw [heq]
      calc
        |((boundary : ℝ) * rho - point coordinate) +
              (point coordinate - axisPoint coordinate) +
              (axisPoint coordinate - zero)|
            ≤
          |(boundary : ℝ) * rho - point coordinate +
              (point coordinate - axisPoint coordinate)| +
            |axisPoint coordinate - zero| := abs_add_le _ _
        _ ≤
          (|(boundary : ℝ) * rho - point coordinate| +
              |point coordinate - axisPoint coordinate|) +
            |axisPoint coordinate - zero| := by
              gcongr
              exact abs_add_le _ _
        _ ≤ delta + 24 * delta +
            |parameter *
              wz1PaperDirection tube coordinate| := by
          have hlast :
              |axisPoint coordinate - zero| =
                |parameter *
                  wz1PaperDirection tube coordinate| := by
            rw [haxisCoordinate]
            simp
          rw [hlast]
          gcongr
          simpa [abs_sub_comm] using hpointBoundary
        _ ≤ delta + 24 * delta + 2 * speed := by
          gcongr
        _ = 2 * speed + 25 * delta := by ring
    rw [abs_le] at htotal
    constructor <;> linarith
  simp only [wz2PaperRelevantBoundaryIndices, Finset.mem_Icc]
  constructor
  · have hlower :
        (zero - 2 * speed - 25 * delta) / rho ≤
          (boundary : ℝ) := by
      rw [div_le_iff₀ hrho]
      exact hboundaryRange.1
    have hfloor :
        (⌊(zero - 2 * speed - 25 * delta) / rho⌋ : ℝ) ≤
          (boundary : ℝ) :=
      (Int.floor_le _).trans hlower
    exact_mod_cast hfloor
  · have hupper :
        (boundary : ℝ) ≤
          (zero + 2 * speed + 25 * delta) / rho := by
      rw [le_div_iff₀ hrho]
      exact hboundaryRange.2
    have hfloor :=
      Int.floor_mono hupper
    simpa using hfloor

theorem wz2_paper_tube_periodic_boundary_volume_of_speed
    {delta rho speed : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hdeltaRho : 50 * delta ≤ rho)
    (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube)
    (coordinate : Fin 3)
    (hspeed : 0 < speed)
    (hdirection :
      speed ≤ |wz1PaperDirection tube coordinate|) :
    volume
        (wz1PaperTubeCarrier tube ∩
          wz2PaperPeriodicBoundaryRegion delta rho coordinate
            (wz2PaperRelevantBoundaryIndices
              (rho := rho) tube coordinate)) ≤
      ENNReal.ofReal
        (4000000 * delta ^ 3 *
          ((1 / rho) + (1 / speed))) := by
  let indices :=
    wz2PaperRelevantBoundaryIndices
      (rho := rho) tube coordinate
  have hsubset :
      wz1PaperTubeCarrier tube ∩
          wz2PaperPeriodicBoundaryRegion delta rho coordinate indices ⊆
        ⋃ boundary ∈ indices,
          (wz1PaperTubeCarrier tube ∩
            coordinateSlab coordinate
              ((boundary : ℝ) * rho - delta)
              ((boundary : ℝ) * rho + delta)) := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨boundary, hboundary, hpointSlab⟩
    exact Set.mem_iUnion₂.mpr
      ⟨boundary, hboundary, hpoint.1, hpointSlab⟩
  let oneSlab : ENNReal :=
    4 *
      ENNReal.ofReal
        (Real.pi * (24 * delta) ^ 2 *
          ((2 * delta + 2 * (24 * delta)) /
              |wz1PaperDirection tube coordinate| +
            2 * (24 * delta)))
  have hdirectionPos :
      0 < |wz1PaperDirection tube coordinate| :=
    hspeed.trans_le hdirection
  have hslab :
      ∀ boundary : ℤ,
        volume
            (wz1PaperTubeCarrier tube ∩
              coordinateSlab coordinate
                ((boundary : ℝ) * rho - delta)
                ((boundary : ℝ) * rho + delta)) ≤
          oneSlab := by
    intro boundary
    have h :=
      wz2_paper_tube_coordinate_slab_volume
        (a := (boundary : ℝ) * rho - delta)
        (b := (boundary : ℝ) * rho + delta)
        (speed := |wz1PaperDirection tube coordinate|)
        hdelta hdeltaSmall
        (by linarith) hdirectionPos tube hline coordinate le_rfl
    dsimp only [oneSlab]
    convert h using 1
    ring_nf
  have hsum :
      volume
          (wz1PaperTubeCarrier tube ∩
            wz2PaperPeriodicBoundaryRegion delta rho coordinate indices) ≤
        (indices.card : ENNReal) * oneSlab := by
    calc
      volume
          (wz1PaperTubeCarrier tube ∩
            wz2PaperPeriodicBoundaryRegion delta rho coordinate indices)
          ≤
        volume
          (⋃ boundary ∈ indices,
            (wz1PaperTubeCarrier tube ∩
              coordinateSlab coordinate
                ((boundary : ℝ) * rho - delta)
                ((boundary : ℝ) * rho + delta))) :=
        measure_mono hsubset
      _ ≤
          ∑ boundary ∈ indices,
            volume
              (wz1PaperTubeCarrier tube ∩
                coordinateSlab coordinate
                  ((boundary : ℝ) * rho - delta)
                  ((boundary : ℝ) * rho + delta)) :=
        MeasureTheory.measure_biUnion_finset_le _ _
      _ ≤ ∑ _boundary ∈ indices, oneSlab := by
        exact Finset.sum_le_sum fun boundary _ => hslab boundary
      _ = (indices.card : ENNReal) * oneSlab := by
        simp [Finset.sum_const]
  have hcard :=
    wz2_paper_relevant_boundary_card
      hdelta hrho tube coordinate
  have hspeedNonneg :
      0 ≤ |wz1PaperDirection tube coordinate| := abs_nonneg _
  have hreal :
      (indices.card : ℝ) *
          (4 *
            (Real.pi * (24 * delta) ^ 2 *
              ((2 * delta + 2 * (24 * delta)) /
                  |wz1PaperDirection tube coordinate| +
                2 * (24 * delta)))) ≤
        4000000 * delta ^ 3 *
          ((1 / rho) + (1 / speed)) := by
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    have hspeedDirection :
        speed ≤ |wz1PaperDirection tube coordinate| :=
      hdirection
    have hdirectionOne :
        |wz1PaperDirection tube coordinate| ≤ 1 := by
      calc
        |wz1PaperDirection tube coordinate|
            ≤ ‖wz1PaperDirection tube‖ :=
          coord_abs_le_norm
            (wz1PaperDirection tube) coordinate
        _ = 1 := wz1PaperDirection_norm tube
    have hinner :
        2 * delta + 2 * (24 * delta) =
          50 * delta := by ring
    have hcap :
        2 * (24 * delta) = 48 * delta := by ring
    have hpiTerm :
        Real.pi * (24 * delta) ^ 2 *
              ((2 * delta + 2 * (24 * delta)) /
                  |wz1PaperDirection tube coordinate| +
                2 * (24 * delta)) ≤
          4 * (24 * delta) ^ 2 *
              ((50 * delta) /
                  |wz1PaperDirection tube coordinate| +
                48 * delta) := by
      rw [hinner, hcap]
      gcongr
    have hcountFactor :
        ((4 * |wz1PaperDirection tube coordinate| +
              50 * delta) / rho + 2) ≤
          4 *
            ((|wz1PaperDirection tube coordinate| / rho) + 1) := by
      field_simp [hrho.ne']
      nlinarith
    have hslabFactor :
        4 *
              (4 * (24 * delta) ^ 2 *
                ((50 * delta) /
                    |wz1PaperDirection tube coordinate| +
                  48 * delta)) ≤
          1000000 * delta ^ 3 /
            |wz1PaperDirection tube coordinate| := by
      have hparenthesis :
          (50 * delta) /
                |wz1PaperDirection tube coordinate| +
              48 * delta ≤
            (98 * delta) /
              |wz1PaperDirection tube coordinate| := by
        field_simp [hdirectionPos.ne']
        nlinarith
      calc
        4 *
              (4 * (24 * delta) ^ 2 *
                ((50 * delta) /
                    |wz1PaperDirection tube coordinate| +
                  48 * delta))
            ≤
          4 *
              (4 * (24 * delta) ^ 2 *
                ((98 * delta) /
                  |wz1PaperDirection tube coordinate|)) := by
            gcongr
        _ = 903168 * delta ^ 3 /
              |wz1PaperDirection tube coordinate| := by
          field_simp [hdirectionPos.ne']
          ring
        _ ≤ 1000000 * delta ^ 3 /
              |wz1PaperDirection tube coordinate| := by
          apply div_le_div_of_nonneg_right
          · nlinarith [pow_nonneg hdelta.le 3]
          · exact hdirectionPos.le
    calc
      (indices.card : ℝ) *
            (4 *
              (Real.pi * (24 * delta) ^ 2 *
                ((2 * delta + 2 * (24 * delta)) /
                    |wz1PaperDirection tube coordinate| +
                  2 * (24 * delta))))
          ≤
        ((4 * |wz1PaperDirection tube coordinate| +
              50 * delta) / rho + 2) *
            (4 *
              (4 * (24 * delta) ^ 2 *
                ((50 * delta) /
                    |wz1PaperDirection tube coordinate| +
                  48 * delta))) := by
          gcongr
      _ ≤
        4000000 * delta ^ 3 *
          ((1 / rho) + (1 / speed)) := by
        calc
          ((4 * |wz1PaperDirection tube coordinate| +
                50 * delta) / rho + 2) *
              (4 *
                (4 * (24 * delta) ^ 2 *
                  ((50 * delta) /
                      |wz1PaperDirection tube coordinate| +
                    48 * delta)))
              ≤
            (4 *
              ((|wz1PaperDirection tube coordinate| / rho) + 1)) *
              (1000000 * delta ^ 3 /
                |wz1PaperDirection tube coordinate|) := by
                gcongr
          _ =
            4000000 * delta ^ 3 *
              ((1 / rho) +
                (1 / |wz1PaperDirection tube coordinate|)) := by
            field_simp [hrho.ne', hdirectionPos.ne']
            ring
          _ ≤
            4000000 * delta ^ 3 *
              ((1 / rho) + (1 / speed)) := by
            gcongr
  have hOneSlab :
      oneSlab =
        ENNReal.ofReal
          (4 *
            (Real.pi * (24 * delta) ^ 2 *
              ((2 * delta + 2 * (24 * delta)) /
                  |wz1PaperDirection tube coordinate| +
                2 * (24 * delta)))) := by
    dsimp only [oneSlab]
    rw [← ENNReal.ofReal_ofNat (n := 4),
      ← ENNReal.ofReal_mul (by norm_num)]
  calc
    volume
        (wz1PaperTubeCarrier tube ∩
          wz2PaperPeriodicBoundaryRegion delta rho coordinate indices)
        ≤ (indices.card : ENNReal) * oneSlab := hsum
    _ =
        ENNReal.ofReal
          ((indices.card : ℝ) *
            (4 *
              (Real.pi * (24 * delta) ^ 2 *
                ((2 * delta + 2 * (24 * delta)) /
                    |wz1PaperDirection tube coordinate| +
                  2 * (24 * delta))))) := by
      rw [hOneSlab]
      rw [show (indices.card : ENNReal) =
          ENNReal.ofReal (indices.card : ℝ) by simp]
      exact
        (ENNReal.ofReal_mul
          (by positivity : 0 ≤ (indices.card : ℝ))).symm
    _ ≤
        ENNReal.ofReal
          (4000000 * delta ^ 3 *
            ((1 / rho) + (1 / speed))) :=
      ENNReal.ofReal_mono hreal

end Kakeya.Assouad

end
