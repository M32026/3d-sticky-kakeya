import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicADTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ConfigurationWeakening
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12CroppedExtremal
import MyLeanRepo.Kakeya.Assouad.ExtremalHelpers

/-!
# Loss and constant weakening for pure WZ2 configurations

When proving at a smaller loss and transferring to the target loss, every
constant of the form `δ^(-loss)` must be enlarged.  This module provides
monotonicity lemmas for each component and for the full configurations.

## Proof route

1. `WZ2PaperConvexWolffBound`: larger constant directly weakens the upper bound.
2. `PureWZ2LocalGrainData` / `PureWZ2C2GlobalGrainData`: only the AD constant
   changes; use `PureWZ2PaperADSet1.weaken_constant`.
3. Full configurations: combine component-wise using existing
   `WZ2PaperCroppedIsExtremal.mono_loss`.
-/

noncomputable section

namespace Kakeya.Assouad

open ENNReal

/-- Enlarge the AD constant in `PureWZ2C2GlobalGrainData`. -/
def PureWZ2C2GlobalGrainData.weaken_constant
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {sigma : ℝ} {C C' : ENNReal}
    (data : PureWZ2C2GlobalGrainData shading sigma C)
    (hC_le : C ≤ C') (hC'_one : 1 ≤ C') (hC'_top : C' ≠ ⊤) :
    PureWZ2C2GlobalGrainData shading sigma C' := by
  refine ⟨
    data.f,
    data.normalized,
    ?_
  ⟩
  intro z
  exact (data.global_ad z).weaken_constant hC_le hC'_one hC'_top

@[simp] theorem PureWZ2C2GlobalGrainData.slope_weaken_constant
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {sigma : ℝ} {C C' : ENNReal}
    (data : PureWZ2C2GlobalGrainData shading sigma C)
    (hC_le : C ≤ C') (hC'_one : 1 ≤ C') (hC'_top : C' ≠ ⊤) :
    (data.weaken_constant hC_le hC'_one hC'_top).slope = data.slope := by
  rfl

/-- Weaken the loss of a full C2 grain configuration. -/
def PureWZ2C2GrainConfiguration.mono_loss
    {sigma firstLoss secondLoss delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hfirstLoss : 0 ≤ firstLoss)
    (hloss : firstLoss ≤ secondLoss)
    (cfg : PureWZ2C2GrainConfiguration sigma firstLoss delta) :
    PureWZ2C2GrainConfiguration sigma secondLoss delta := by
  set C1 : ENNReal := Kakeya.realRpowENN delta (-firstLoss) with hC1_def
  set C2 : ENNReal := Kakeya.realRpowENN delta (-secondLoss) with hC2_def
  have hC_le : C1 ≤ C2 := realRpowENN_antitone hdelta hdeltaOne (by linarith)
  have hsecondLoss_nonneg : 0 ≤ secondLoss := by linarith
  have hC2_one : 1 ≤ C2 := by
    simp only [hC2_def, Kakeya.realRpowENN]
    rw [ENNReal.one_le_ofReal]
    have h_rpow : delta ^ (0 : ℝ) ≤ delta ^ (-secondLoss) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)
    simpa using h_rpow
  have hC2_top : C2 ≠ ⊤ := by
    simp [hC2_def, Kakeya.realRpowENN]
  exact ⟨
    cfg.family,
    cfg.shading,
    cfg.line_class,
    cfg.bounded_base,
    cfg.cubical,
    cfg.extremal.mono_loss hloss,
    cfg.top_level_cwa.weaken_constant hC_le,
    cfg.globalGrains.weaken_constant hC_le hC2_one hC2_top,
    cfg.localGrains.weaken_constant hC_le hC2_top
  ⟩

@[simp] theorem PureWZ2C2GrainConfiguration.slope_mono_loss
    {sigma firstLoss secondLoss delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hfirstLoss : 0 ≤ firstLoss) (hloss : firstLoss ≤ secondLoss)
    (cfg : PureWZ2C2GrainConfiguration sigma firstLoss delta) :
    (cfg.mono_loss hdelta hdeltaOne hfirstLoss hloss).globalGrains.slope =
      cfg.globalGrains.slope := by
  rfl

/-- The internal global/local compatibility is unchanged by loss weakening. -/
theorem PureWZ2LocalGlobalCompatibility.mono_loss
    {sigma firstLoss secondLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma firstLoss delta}
    (compatibility : PureWZ2LocalGlobalCompatibility cfg)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hfirstLoss : 0 ≤ firstLoss) (hloss : firstLoss ≤ secondLoss) :
    PureWZ2LocalGlobalCompatibility
      (cfg.mono_loss hdelta hdeltaOne hfirstLoss hloss) := by
  refine { tube_base_local := ?_, normal_first := ?_, normal_tilt := ?_ }
  · simpa [PureWZ2C2GrainConfiguration.mono_loss] using
      compatibility.tube_base_local
  · intro point
    simpa [PureWZ2C2GrainConfiguration.mono_loss,
      PureWZ2LocalGrainData.weaken_constant] using
      compatibility.normal_first point
  · intro point
    change |cfg.localGrains.planeMap point 1 -
        (cfg.mono_loss hdelta hdeltaOne hfirstLoss hloss).globalGrains.slope
          (point.1 2) * cfg.localGrains.planeMap point 0| ≤ 1 / 10
    rw [PureWZ2C2GrainConfiguration.slope_mono_loss]
    simpa [PureWZ2C2GrainConfiguration.mono_loss,
      PureWZ2LocalGrainData.weaken_constant] using
      compatibility.normal_tilt point

/-- Weaken the loss of a full large-slope configuration.

The slope and its nonsingularity field are loss-independent. -/
def PureWZ2LargeSlopeConfiguration.mono_loss
    {sigma firstLoss secondLoss delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hfirstLoss : 0 ≤ firstLoss)
    (hloss : firstLoss ≤ secondLoss)
    (cfg : PureWZ2LargeSlopeConfiguration sigma firstLoss delta) :
    PureWZ2LargeSlopeConfiguration sigma secondLoss delta := by
  set C1 : ENNReal := Kakeya.realRpowENN delta (-firstLoss) with hC1_def
  set C2 : ENNReal := Kakeya.realRpowENN delta (-secondLoss) with hC2_def
  have hC_le : C1 ≤ C2 := realRpowENN_antitone hdelta hdeltaOne (by linarith)
  have hsecondLoss_nonneg : 0 ≤ secondLoss := by linarith
  have hC2_one : 1 ≤ C2 := by
    simp only [hC2_def, Kakeya.realRpowENN]
    rw [ENNReal.one_le_ofReal]
    have h_rpow : delta ^ (0 : ℝ) ≤ delta ^ (-secondLoss) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)
    simpa using h_rpow
  have hC2_top : C2 ≠ ⊤ := by
    simp [hC2_def, Kakeya.realRpowENN]
  exact ⟨
    cfg.family,
    cfg.shading,
    cfg.line_class,
    cfg.cubical,
    cfg.extremal.mono_loss hloss,
    cfg.top_level_cwa.weaken_constant hC_le,
    cfg.slope,
    cfg.slope_nonsingular,
    fun z hz => (cfg.global_ad z hz).weaken_constant hC_le hC2_one hC2_top,
    cfg.projection_upper.trans (by
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)),
    cfg.localGrains.weaken_constant hC_le hC2_top
  ⟩

end Kakeya.Assouad

end
