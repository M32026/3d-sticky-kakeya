import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometry
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperAxisCoreVolume
import MyLeanRepo.Kakeya.Assouad.TubeVolumeRatio
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume

/-!
# Rigid-normalization paper-body mass ratio

A cropped paper carrier in the fixed line class has volume at most `13824`
times the volume of its ordinary unit-segment tube.

For `delta <= 1 / 24`, the finite-axis-core containment covers the paper
carrier by four radius-`24 * delta` ordinary capsules.  The standard capsule
upper bound and `pi <= 4` give volume at most `27648 * delta^2`.  For larger
`delta`, the crop box has volume eight, which satisfies the same comparison.
The ordinary tube lower bound `2 * delta^2` closes both cases.

Summing the pointwise estimate gives the corresponding indexed body-family
mass comparison.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
One line-class paper carrier has at most `13824` times the volume of its
ordinary tube carrier.
-/
theorem body_mass_ratio
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (_deltaLeOne : delta ≤ 1)
    (tube : Kakeya.DeltaTube delta)
    (lineClass : WZ1PaperTubeInLineClass tube) :
    volume (wz1PaperTubeCarrier tube) ≤
      (13824 : ENNReal) * volume tube.carrier := by
  have ordinaryLower :
      ENNReal.ofReal (2 * delta ^ 2) ≤
        volume tube.carrier := by
    change
      ENNReal.ofReal (2 * delta ^ 2) ≤ tube.volume
    rw [tube_volume_scaling.1 delta tube]
    exact
      Kakeya.Streamlined.tube_volume_ge_two_delta_sq
        delta deltaPos
  by_cases deltaSmall : delta ≤ 1 / 24
  · have radiusPos : 0 < 24 * delta := by positivity
    have radiusUpper :
        Kakeya.deltaTubeVolume (24 * delta) ≤
          ENNReal.ofReal
            (Real.pi * (24 * delta) ^ 2 *
              (1 + 2 * (24 * delta))) :=
      deltaTubeVolume_upper_pi radiusPos
    have realUpper :
        Real.pi * (24 * delta) ^ 2 *
            (1 + 2 * (24 * delta)) ≤
          6912 * delta ^ 2 := by
      calc
        Real.pi * (24 * delta) ^ 2 *
              (1 + 2 * (24 * delta)) =
            576 * delta ^ 2 *
              (Real.pi * (1 + 48 * delta)) := by
          ring
        _ ≤ 576 * delta ^ 2 * (4 * 3) := by
          gcongr
          · exact Real.pi_le_four
          · linarith
        _ = 6912 * delta ^ 2 := by ring
    have paperUpper :
        volume (wz1PaperTubeCarrier tube) ≤
          (4 : ENNReal) *
            ENNReal.ofReal (6912 * delta ^ 2) := by
      calc
        volume (wz1PaperTubeCarrier tube) ≤
            volume
              (Metric.cthickening (24 * delta)
                (wz2PaperAxisCoreSegment tube)) :=
          measure_mono
            (wz2_paper_tube_carrier_geometry
              deltaPos tube lineClass).2
        _ ≤ 4 * Kakeya.deltaTubeVolume (24 * delta) :=
          wz2PaperAxisCoreSegment_thickening_volume_le
            deltaPos tube
        _ ≤
            (4 : ENNReal) *
              ENNReal.ofReal
                (Real.pi * (24 * delta) ^ 2 *
                  (1 + 2 * (24 * delta))) := by
          gcongr
        _ ≤
            (4 : ENNReal) *
              ENNReal.ofReal (6912 * delta ^ 2) := by
          gcongr
    have coefficientIdentity :
        (4 : ENNReal) *
            ENNReal.ofReal (6912 * delta ^ 2) =
          (13824 : ENNReal) *
            ENNReal.ofReal (2 * delta ^ 2) := by
      have split :
          ENNReal.ofReal (6912 * delta ^ 2) =
            (3456 : ENNReal) *
              ENNReal.ofReal (2 * delta ^ 2) := by
        calc
          ENNReal.ofReal (6912 * delta ^ 2) =
              ENNReal.ofReal (3456 * (2 * delta ^ 2)) := by
            congr 1
            ring
          _ =
              ENNReal.ofReal 3456 *
                ENNReal.ofReal (2 * delta ^ 2) := by
            rw [ENNReal.ofReal_mul (by norm_num)]
          _ =
              (3456 : ENNReal) *
                ENNReal.ofReal (2 * delta ^ 2) := by
            norm_num
      rw [split]
      ring
    calc
      volume (wz1PaperTubeCarrier tube) ≤
          (4 : ENNReal) *
            ENNReal.ofReal (6912 * delta ^ 2) :=
        paperUpper
      _ =
          (13824 : ENNReal) *
            ENNReal.ofReal (2 * delta ^ 2) :=
        coefficientIdentity
      _ ≤ (13824 : ENNReal) * volume tube.carrier := by
        gcongr
  · have deltaLarge : 1 / 24 < delta := by
      linarith
    have paperSubsetBox :
        wz1PaperTubeCarrier tube ⊆
          Kakeya.Streamlined.axisBox 2 2 2 :=
      fun _ pointMem => pointMem.2
    have boxVolume :
        volume (Kakeya.Streamlined.axisBox 2 2 2) =
          (8 : ENNReal) := by
      rw [Kakeya.Streamlined.volume_axisBox 2 2 2]
      all_goals norm_num
    have realLower :
        (8 : ℝ) ≤ 13824 * (2 * delta ^ 2) := by
      nlinarith
    have eightLower :
        (8 : ENNReal) ≤
          (13824 : ENNReal) *
            ENNReal.ofReal (2 * delta ^ 2) := by
      calc
        (8 : ENNReal) = ENNReal.ofReal (8 : ℝ) := by
          norm_num
        _ ≤ ENNReal.ofReal (13824 * (2 * delta ^ 2)) :=
          ENNReal.ofReal_mono realLower
        _ =
            ENNReal.ofReal 13824 *
              ENNReal.ofReal (2 * delta ^ 2) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
        _ =
            (13824 : ENNReal) *
              ENNReal.ofReal (2 * delta ^ 2) := by
          norm_num
    calc
      volume (wz1PaperTubeCarrier tube) ≤
          volume (Kakeya.Streamlined.axisBox 2 2 2) :=
        measure_mono paperSubsetBox
      _ = (8 : ENNReal) := boxVolume
      _ ≤
          (13824 : ENNReal) *
            ENNReal.ofReal (2 * delta ^ 2) :=
        eightLower
      _ ≤ (13824 : ENNReal) * volume tube.carrier := by
        gcongr

/--
The indexed paper-body mass is at most `13824` times the indexed ordinary
tube-family mass.
-/
theorem wz2PaperBodyFamily_mass_le_ordinary
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (lineClass : WZ1PaperIsLineClass family) :
    (wz1PaperBodyFamily family).mass ≤
      (13824 : ENNReal) * family.toBodyFamily.mass := by
  change
    (∑ index : Fin family.card,
        volume (wz1PaperTubeCarrier (family.tube index))) ≤
      (13824 : ENNReal) *
        ∑ index : Fin family.card,
          volume (family.tube index).carrier
  rw [Finset.mul_sum]
  exact
    Finset.sum_le_sum fun index _ =>
      body_mass_ratio
        deltaPos deltaLeOne (family.tube index) (lineClass index)

end Kakeya.Assouad

end
