import MyLeanRepo.Kakeya.Assouad.PropStickyPaperAxisCoreVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoverCarrierContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryHelpers
import MyLeanRepo.Kakeya.Assouad.Targets.TubeVolumeScaling

/-!
# Uniform lower volume bound for cropped paper tubes

Every `L₃` paper tube contains an ordinary unit-segment tube of the same
radius.  The segment is centered at the paper axis zero-point and lies well
inside the crop box.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The centered unit-segment tube carried by one paper-oriented axis. -/
def wz2PaperInnerTube
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    Kakeya.DeltaTube delta where
  base :=
    wz1TubeAxisZeroPoint tube -
      (1 / 2 : ℝ) • wz1PaperDirection tube
  direction := wz1PaperDirection tube
  direction_unit := wz1PaperDirection_norm tube

theorem wz2PaperInnerTube_segment_subset_axis
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    Kakeya.unitSegment
        (wz2PaperInnerTube tube).base
        (wz2PaperInnerTube tube).direction ⊆
      tubeAxisLine tube := by
  rintro point ⟨parameter, hparameter, rfl⟩
  change
    (wz2PaperInnerTube tube).base +
        parameter • (wz2PaperInnerTube tube).direction ∈
      tubeAxisLine tube
  convert
    wz1TubeAxisZeroPoint_add_smul_paperDirection_mem_axis
      tube (parameter - 1 / 2) using 1
  dsimp only [wz2PaperInnerTube]
  module

theorem wz2PaperInnerTube_carrier_subset
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 12)
    (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube) :
    (wz2PaperInnerTube tube).carrier ⊆
      wz1PaperTubeCarrier tube := by
  intro point hpoint
  let segment :=
    Kakeya.unitSegment
      (wz2PaperInnerTube tube).base
      (wz2PaperInnerTube tube).direction
  have hsegmentCompact : IsCompact segment := by
    exact isCompact_Icc.image
      (continuous_const.add
        (continuous_id.smul continuous_const))
  have hpointThickening :
      point ∈ Metric.cthickening delta segment := by
    simpa [Kakeya.DeltaTube.carrier, segment] using hpoint
  have hdeltaNonnegative : 0 ≤ delta := hdelta.le
  rcases
      exists_dist_le_of_mem_cthickening_closed
        hsegmentCompact.isClosed hdeltaNonnegative hpointThickening
    with ⟨axisPoint, haxisPointSegment, hpointAxis⟩
  have haxisPointLine :
      axisPoint ∈ tubeAxisLine tube :=
    wz2PaperInnerTube_segment_subset_axis tube haxisPointSegment
  have hthickening :
      point ∈
        Metric.cthickening (6 * delta) (tubeAxisLine tube) := by
    apply Metric.mem_cthickening_of_dist_le
      point axisPoint (6 * delta) (tubeAxisLine tube)
      haxisPointLine
    linarith
  have haxisCoordinates :
      ∀ coordinate : Fin 3,
        |axisPoint coordinate| ≤ 5 / 6 := by
    intro coordinate
    rcases haxisPointSegment with
      ⟨parameter, hparameter, haxisPoint⟩
    have haxisPoint' :
        axisPoint =
        (wz1TubeAxisZeroPoint tube -
            (1 / 2 : ℝ) • wz1PaperDirection tube) +
          parameter • wz1PaperDirection tube := by
      rw [← haxisPoint]
      rfl
    have hdirectionCoordinate :
        |wz1PaperDirection tube coordinate| ≤ 1 := by
      calc
        |wz1PaperDirection tube coordinate|
            ≤ ‖wz1PaperDirection tube‖ :=
          by
            simpa [Real.norm_eq_abs] using
              PiLp.norm_apply_le
                (wz1PaperDirection tube) coordinate
        _ = 1 := wz1PaperDirection_norm tube
    have hcoefficient :
        |parameter - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [hparameter.1, hparameter.2]
    have hzero :
        |wz1TubeAxisZeroPoint tube coordinate| ≤ 1 / 3 := by
      fin_cases coordinate
      · simpa using hline.2.1
      · simpa using hline.2.2
      · simp [wz1TubeAxisZeroPoint_coord_two tube hline.vertical]
    have hcoordinate :
        axisPoint coordinate =
          wz1TubeAxisZeroPoint tube coordinate +
            (parameter - 1 / 2) *
              wz1PaperDirection tube coordinate := by
      rw [haxisPoint']
      simp
      ring
    rw [hcoordinate]
    calc
      |wz1TubeAxisZeroPoint tube coordinate +
          (parameter - 1 / 2) *
            wz1PaperDirection tube coordinate|
          ≤ |wz1TubeAxisZeroPoint tube coordinate| +
              |parameter - 1 / 2| *
                |wz1PaperDirection tube coordinate| := by
        simpa [abs_mul] using
          abs_add_le
            (wz1TubeAxisZeroPoint tube coordinate)
            ((parameter - 1 / 2) *
              wz1PaperDirection tube coordinate)
      _ ≤ 1 / 3 + (1 / 2) * 1 := by
        gcongr
      _ = 5 / 6 := by norm_num
  have hpointCoordinates :
      ∀ coordinate : Fin 3, |point coordinate| ≤ 1 := by
    intro coordinate
    have hdifference :
        |point coordinate - axisPoint coordinate| ≤ delta := by
      calc
        |point coordinate - axisPoint coordinate|
            ≤ dist point axisPoint :=
          abs_coord_sub_le_dist coordinate
        _ ≤ delta := hpointAxis
    calc
      |point coordinate|
          = |axisPoint coordinate +
              (point coordinate - axisPoint coordinate)| := by
        congr 1
        ring
      _ ≤ |axisPoint coordinate| +
              |point coordinate - axisPoint coordinate| := by
        exact abs_add_le _ _
      _ ≤ 5 / 6 + delta := by
        exact add_le_add
          (haxisCoordinates coordinate) hdifference
      _ ≤ 1 := by linarith
  have hbox :
      point ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq]
    norm_num
    exact
      ⟨hpointCoordinates 0,
        hpointCoordinates 1,
        hpointCoordinates 2⟩
  exact ⟨hthickening, hbox⟩

theorem wz2PaperTubeCarrier_volume_lower
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 12)
    (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube) :
    Kakeya.deltaTubeVolume delta ≤
      volume (wz1PaperTubeCarrier tube) := by
  rw [← tube_volume_scaling.1 delta (wz2PaperInnerTube tube)]
  exact measure_mono
    (wz2PaperInnerTube_carrier_subset
      hdelta hdeltaSmall tube hline)

end Kakeya.Assouad

end
