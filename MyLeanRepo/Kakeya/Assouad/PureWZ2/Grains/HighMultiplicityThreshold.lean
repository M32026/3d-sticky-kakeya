import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureCWAToCardinality
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12CroppedExtremal
import MyLeanRepo.Kakeya.Assouad.TubeVolumeRatio
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# A fixed lower threshold for the planiness multiplicity

Pure nearby-scale CWA forces `delta^(2-loss) * #family` to be bounded below.
After spending the positive exponent gap `sigma - 4 * loss`, the density
power used by the dyadic planiness decomposition is therefore at least 12.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- Pure nearby-scale CWA forces the standard coarse cardinality floor.
This is the reusable pre-cancellation form of the estimate used below. -/
theorem cwa_cardinality_weight_floor
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal sigma loss family shading)
    (hdeltaSmall : delta ≤ 1 / 24) :
    1 ≤ ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
      (Kakeya.realRpowENN delta (2 - loss) * family.enncard) := by
  have hcard := pure_cwa_to_cardinality_floor
    extremal.cwa_nearby_scales extremal.delta_pos hdeltaSmall
    extremal.nonempty
  have hvolume := deltaTubeVolume_upper_pi extremal.delta_pos
  have hfactor : 1 + 2 * delta ≤ 3 := by
    linarith [hdeltaSmall]
  have hvolumeThree : Kakeya.deltaTubeVolume delta ≤
      ENNReal.ofReal (3 * Real.pi) *
        Kakeya.realRpowENN delta 2 := by
    have hreal : Real.pi * delta ^ 2 * (1 + 2 * delta) ≤
        (3 * Real.pi) * delta ^ 2 := by
      calc
        Real.pi * delta ^ 2 * (1 + 2 * delta) ≤
            Real.pi * delta ^ 2 * 3 := by
          exact mul_le_mul_of_nonneg_left hfactor
            (mul_nonneg Real.pi_pos.le (sq_nonneg delta))
        _ = (3 * Real.pi) * delta ^ 2 := by ring
    calc
      Kakeya.deltaTubeVolume delta ≤
          ENNReal.ofReal (Real.pi * delta ^ 2 * (1 + 2 * delta)) :=
        hvolume
      _ ≤ ENNReal.ofReal ((3 * Real.pi) * delta ^ 2) :=
        ENNReal.ofReal_mono hreal
      _ = ENNReal.ofReal (3 * Real.pi) *
          Kakeya.realRpowENN delta 2 := by
        rw [ENNReal.ofReal_mul (by positivity)]
        simp [Kakeya.realRpowENN, Real.rpow_two]
  have hthreePi : ENNReal.ofReal (3 * Real.pi) =
      (3 : ENNReal) * ENNReal.ofReal Real.pi := by
    calc
      ENNReal.ofReal (3 * Real.pi) =
          ENNReal.ofReal 3 * ENNReal.ofReal Real.pi := by
        rw [ENNReal.ofReal_mul (by norm_num)]
      _ = (3 : ENNReal) * ENNReal.ofReal Real.pi := by norm_num
  have hpower : Kakeya.realRpowENN delta (-loss) *
      Kakeya.realRpowENN delta 2 =
        Kakeya.realRpowENN delta (2 - loss) := by
    rw [← Kakeya.Assouad.realRpowENN_add extremal.delta_pos]
    congr 1
    ring
  calc
    (1 : ENNReal) ≤
        4 * Kakeya.realRpowENN delta (-loss) *
          Kakeya.deltaTubeVolume delta * family.enncard := hcard
    _ ≤ 4 * Kakeya.realRpowENN delta (-loss) *
        (ENNReal.ofReal (3 * Real.pi) *
          Kakeya.realRpowENN delta 2) * family.enncard := by gcongr
    _ = ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
        (Kakeya.realRpowENN delta (2 - loss) * family.enncard) := by
      rw [hthreePi]
      rw [show 4 * Kakeya.realRpowENN delta (-loss) *
          (3 * ENNReal.ofReal Real.pi * Kakeya.realRpowENN delta 2) *
            family.enncard =
          (12 * ENNReal.ofReal Real.pi) *
            ((Kakeya.realRpowENN delta (-loss) *
              Kakeya.realRpowENN delta 2) * family.enncard) by ring]
      rw [hpower]

/-- The density power in the planiness dyadic band dominates any fixed target
once the corresponding CWA and tube-volume constant has been absorbed. -/
theorem density_power_cardinality_ge_fixed
    {delta sigma loss densityLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal sigma loss family shading)
    (target : ENNReal)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * loss)
    (habsorb :
      (12 * target) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * loss)) :
    target ≤
      Kakeya.realRpowENN delta densityLoss * family.enncard := by
  have hdelta : 0 < delta := extremal.delta_pos
  have hcard := pure_cwa_to_cardinality_floor
    extremal.cwa_nearby_scales hdelta hdeltaSmall extremal.nonempty
  have hvolume := deltaTubeVolume_upper_pi hdelta
  have hfactor : 1 + 2 * delta ≤ 3 := by
    linarith [hdeltaSmall]
  have hvolumeThree : Kakeya.deltaTubeVolume delta ≤
      ENNReal.ofReal (3 * Real.pi) *
        Kakeya.realRpowENN delta 2 := by
    have hreal : Real.pi * delta ^ 2 * (1 + 2 * delta) ≤
        (3 * Real.pi) * delta ^ 2 := by
      calc
        Real.pi * delta ^ 2 * (1 + 2 * delta) ≤
            Real.pi * delta ^ 2 * 3 := by
          exact mul_le_mul_of_nonneg_left hfactor
            (mul_nonneg Real.pi_pos.le (sq_nonneg delta))
        _ = (3 * Real.pi) * delta ^ 2 := by ring
    calc
      Kakeya.deltaTubeVolume delta ≤
          ENNReal.ofReal (Real.pi * delta ^ 2 * (1 + 2 * delta)) :=
        hvolume
      _ ≤ ENNReal.ofReal ((3 * Real.pi) * delta ^ 2) :=
        ENNReal.ofReal_mono hreal
      _ = ENNReal.ofReal (3 * Real.pi) *
          Kakeya.realRpowENN delta 2 := by
        rw [ENNReal.ofReal_mul (by positivity)]
        simp [Kakeya.realRpowENN, Real.rpow_two]
  have hthreePi : ENNReal.ofReal (3 * Real.pi) =
      (3 : ENNReal) * ENNReal.ofReal Real.pi := by
    calc
      ENNReal.ofReal (3 * Real.pi) =
          ENNReal.ofReal 3 * ENNReal.ofReal Real.pi := by
        rw [ENNReal.ofReal_mul (by norm_num)]
      _ = (3 : ENNReal) * ENNReal.ofReal Real.pi := by norm_num
  have hpower : Kakeya.realRpowENN delta (-loss) *
      Kakeya.realRpowENN delta 2 =
        Kakeya.realRpowENN delta (2 - loss) := by
    rw [← Kakeya.Assouad.realRpowENN_add hdelta]
    congr 1
    ring
  have hbase : (1 : ENNReal) ≤
      ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
        (Kakeya.realRpowENN delta (2 - loss) * family.enncard) := by
    calc
      (1 : ENNReal) ≤
          4 * Kakeya.realRpowENN delta (-loss) *
            Kakeya.deltaTubeVolume delta * family.enncard := hcard
      _ ≤ 4 * Kakeya.realRpowENN delta (-loss) *
          (ENNReal.ofReal (3 * Real.pi) *
            Kakeya.realRpowENN delta 2) * family.enncard := by gcongr
      _ = ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
          (Kakeya.realRpowENN delta (2 - loss) * family.enncard) := by
        rw [hthreePi]
        rw [show 4 * Kakeya.realRpowENN delta (-loss) *
            (3 * ENNReal.ofReal Real.pi * Kakeya.realRpowENN delta 2) *
              family.enncard =
            (12 * ENNReal.ofReal Real.pi) *
              ((Kakeya.realRpowENN delta (-loss) *
                Kakeya.realRpowENN delta 2) * family.enncard) by ring]
        rw [hpower]
  have hscaled := mul_le_mul_left' hbase target
  have hscaled' : target ≤
      ((12 * target) * ENNReal.ofReal Real.pi) *
        (Kakeya.realRpowENN delta (2 - loss) * family.enncard) := by
    calc
      target = target * 1 := by simp
      _ ≤ target * (((12 : ENNReal) * ENNReal.ofReal Real.pi) *
          (Kakeya.realRpowENN delta (2 - loss) * family.enncard)) :=
        hscaled
      _ = ((12 * target) * ENNReal.ofReal Real.pi) *
          (Kakeya.realRpowENN delta (2 - loss) * family.enncard) := by ring
  calc
    target ≤
        ((12 * target) * ENNReal.ofReal Real.pi) *
          (Kakeya.realRpowENN delta (2 - loss) * family.enncard) :=
      hscaled'
    _ ≤ Kakeya.realRpowENN delta (-sigma + 4 * loss) *
          (Kakeya.realRpowENN delta (2 - loss) * family.enncard) := by
      gcongr
    _ = Kakeya.realRpowENN delta densityLoss * family.enncard := by
      rw [← mul_assoc, ← Kakeya.Assouad.realRpowENN_add hdelta,
        hdensityLoss]
      congr 1 <;> ring

/-- The density power is at least twelve. -/
theorem density_power_cardinality_ge_twelve
    {delta sigma loss densityLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal sigma loss family shading)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * loss)
    (habsorb :
      (144 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * loss)) :
    (12 : ENNReal) ≤
      Kakeya.realRpowENN delta densityLoss * family.enncard := by
  simpa using density_power_cardinality_ge_fixed extremal
    (12 : ENNReal) hdeltaSmall hdensityLoss (by
      convert habsorb using 1 <;> norm_num)

/-- The density power is at least twenty-four. -/
theorem density_power_cardinality_ge_twenty_four
    {delta sigma loss densityLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal sigma loss family shading)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * loss)
    (habsorb :
      (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * loss)) :
    (24 : ENNReal) ≤
      Kakeya.realRpowENN delta densityLoss * family.enncard := by
  simpa using density_power_cardinality_ge_fixed extremal
    (24 : ENNReal) hdeltaSmall hdensityLoss (by
      convert habsorb using 1 <;> norm_num)

/-- Any natural multiplicity dominating the density power is at least twelve. -/
theorem twelve_le_multiplicity_of_density_power
    {delta sigma loss densityLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {multiplicity : ℕ}
    (extremal : WZ2PaperCroppedIsExtremal sigma loss family shading)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * loss)
    (habsorb :
      (144 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * loss))
    (hdensity : Kakeya.realRpowENN delta densityLoss * family.enncard ≤
      (multiplicity : ENNReal)) :
    12 ≤ multiplicity := by
  exact_mod_cast (density_power_cardinality_ge_twelve
    extremal hdeltaSmall hdensityLoss habsorb).trans hdensity

/-- Any natural multiplicity dominating the density power is at least 24. -/
theorem twenty_four_le_multiplicity_of_density_power
    {delta sigma loss densityLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {multiplicity : ℕ}
    (extremal : WZ2PaperCroppedIsExtremal sigma loss family shading)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * loss)
    (habsorb :
      (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * loss))
    (hdensity : Kakeya.realRpowENN delta densityLoss * family.enncard ≤
      (multiplicity : ENNReal)) :
    24 ≤ multiplicity := by
  exact_mod_cast (density_power_cardinality_ge_twenty_four
    extremal hdeltaSmall hdensityLoss habsorb).trans hdensity

end Kakeya.Assouad.PureWZ2

end
