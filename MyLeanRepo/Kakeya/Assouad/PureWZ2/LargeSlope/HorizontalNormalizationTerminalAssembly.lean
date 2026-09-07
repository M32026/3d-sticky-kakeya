import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureNearbyTopLevelCWA

/-!
# Terminal assembly after horizontal normalization

This module is the last proof-neutral boundary in the horizontal route.  It
requires every geometric and analytic field on one literal family and one
literal shading, derives the top-level Convex--Wolff bound from the nearby
pure CWA, and packages the public Proposition-6.5 record.

The global slope used by the transformed family and global-AD certificate is
retained in the public output.
-/

noncomputable section

namespace Kakeya.Assouad

/-- All same-configuration facts needed after the horizontal construction.
The nearby CWA may use a smaller bookkeeping loss than the public output
loss; the explicit absorption field pays for the actual-John pullback when
recovering the top-level paper CWA. -/
structure PureWZ2HorizontalTerminalData
    {sigma nearbyLoss outputLoss targetDelta : ℝ}
    (slope : SlopeFunction)
    (family : Kakeya.Streamlined.TubeFamily targetDelta)
    (shading : WZ1PaperTubeShading family) where
  slope_nonsingular : slope.IsNonsingular
  delta_pos : 0 < targetDelta
  delta_le_one : targetDelta ≤ 1
  output_loss_pos : 0 < outputLoss
  nearby_loss_pos : 0 < nearbyLoss
  nearby_loss_le_one : nearbyLoss ≤ 1
  nearby_loss_le_output : nearbyLoss ≤ outputLoss
  nonempty : family.Nonempty
  line_class : WZ1PaperIsLineClass family
  cubical : WZ1PaperIsCubicalShading shading
  nearby_cwa : WZ2PaperPureCWAAtNearbyScales family
    (Kakeya.realRpowENN targetDelta (-nearbyLoss))
  carrier_subset : ∀ index,
    (family.tube index).carrier ⊆
      wz1PaperTubeCarrier (family.tube index)
  top_level_absorption :
    (4 : ENNReal) *
        Kakeya.realRpowENN targetDelta (outputLoss - 3 * nearbyLoss) ≤
      1
  dense : shading.IsLambdaDense
    (Kakeya.realRpowENN targetDelta outputLoss)
  volume_upper : MeasureTheory.volume shading.union ≤
    Kakeya.realRpowENN targetDelta (sigma - outputLoss)
  projection_upper : MeasureTheory.volume
      (twistedProjection slope '' shading.union) ≤
    Kakeya.realRpowENN targetDelta (sigma - outputLoss)
  global_ad :
    ∀ z : ℝ, ∀ hz : z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (slope z))
          (horizontalSlice shading.union z))
        targetDelta (1 - sigma)
          (Kakeya.realRpowENN targetDelta (-outputLoss))
  local_grains : PureWZ2LocalGrainData
    shading sigma (Kakeya.realRpowENN targetDelta (-outputLoss))

namespace PureWZ2HorizontalTerminalData

/-- Package the horizontal output while retaining the same global slope used
by the transformed family and global-AD certificate. -/
def toLargeSlopeConfiguration
    {sigma nearbyLoss outputLoss targetDelta : ℝ}
    {slope : SlopeFunction}
    {family : Kakeya.Streamlined.TubeFamily targetDelta}
    {shading : WZ1PaperTubeShading family}
    (data : PureWZ2HorizontalTerminalData
      (sigma := sigma) (nearbyLoss := nearbyLoss)
      (outputLoss := outputLoss) slope family shading) :
    PureWZ2LargeSlopeConfiguration sigma outputLoss targetDelta := by
  have hnearbyConstant :
      Kakeya.realRpowENN targetDelta (-nearbyLoss) ≤
        Kakeya.realRpowENN targetDelta (-outputLoss) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge data.delta_pos data.delta_le_one
      (by linarith [data.nearby_loss_le_output])
  have houtputFinite :
      WZ2PaperFiniteErrorConstant
        (Kakeya.realRpowENN targetDelta (-outputLoss)) := by
    constructor
    · rw [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
      have hpow := Real.rpow_le_rpow_of_exponent_ge data.delta_pos
        data.delta_le_one (show -outputLoss ≤ (0 : ℝ) by
          linarith [data.output_loss_pos])
      simpa using hpow
    · simp [Kakeya.realRpowENN]
  exact {
    family := family
    shading := shading
    line_class := data.line_class
    cubical := data.cubical
    extremal := {
      delta_pos := data.delta_pos
      delta_le_one := data.delta_le_one
      nonempty := data.nonempty
      cwa_nearby_scales := data.nearby_cwa.mono
        hnearbyConstant houtputFinite.2
      cubical := data.cubical
      dense := data.dense
      volume_upper := data.volume_upper }
    top_level_cwa :=
      wz2PaperPureNearby_topLevelPaperCWA_of_outputLoss
        data.delta_pos data.delta_le_one data.nearby_loss_pos
        data.nearby_loss_le_one data.nearby_cwa data.carrier_subset
        data.top_level_absorption
    slope := slope
    slope_nonsingular := data.slope_nonsingular
    global_ad := data.global_ad
    projection_upper := data.projection_upper
    localGrains := data.local_grains
  }

end PureWZ2HorizontalTerminalData

end Kakeya.Assouad

end
