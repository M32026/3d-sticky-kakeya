import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TreePureScheduleProducer

/-!
# Proposition 6.2: bounded pure schedule provenance

The canonical metric-parent mass budget needs a fixed upper bound for the
depth of the one simultaneous old schedule.  That bound must come from the
finite schedule selected before caller-rooting, rather than being supplied
independently after the pure schedule has been built.

This module retains exactly that provenance.  The synchronized caller-rooted
schedule has the same number of coordinates as the finite nearby schedule,
whose `scaleCount_le` field gives the required bound.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2Prop62BoundedPureSchedule
    {delta : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (ambientConstant scaleWindow : ENNReal)
    (depthBound : ℕ) where
  schedule :
    PureWZ2Prop62PureSchedule
      fine ambientConstant scaleWindow
  levelCount_le :
    schedule.levelCount ≤ depthBound
  actualScale_le_one :
    ∀ coordinate, schedule.actualScale coordinate ≤ 1

namespace WZ2PaperAlignedPureExactSource

variable
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {outputConstant : ENNReal}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    (aligned :
      WZ2PaperAlignedPureExactSource
        sigma loss family shading)
    (historical :
      WZ2PaperCallerRootedSynchronizedScheduleData
        (Kakeya.realRpowENN delta (-loss))
        outputConstant caller
        aligned.sourceData.internalData.cwa_exact_scales)
    (outputFinite :
      WZ2PaperFiniteErrorConstant outputConstant)

/--
Attach the original finite-schedule depth bound to the pure caller-rooted
schedule.  `historicalCount` is the equality returned by the caller-rooted
synchronized-schedule producer.
-/
noncomputable def prop62BoundedPureSchedule
    {levelCount : ℕ}
    (finiteSchedule :
      WZ2PaperFiniteNearbyScheduleData
        (family := family)
        (Kakeya.realRpowENN delta (-loss))
        outputConstant levelCount)
    (historicalCount :
      historical.nestedSchedule.scaleCount =
        finiteSchedule.scaleCount) :
    PureWZ2Prop62BoundedPureSchedule
      family
      (Kakeya.realRpowENN delta (-loss))
      outputConstant
      (levelCount + 1) where
  schedule :=
    aligned.prop62PureSchedule historical outputFinite
  levelCount_le := by
    rw [aligned.prop62PureSchedule_levelCount historical outputFinite,
      historicalCount]
    exact finiteSchedule.scaleCount_le
  actualScale_le_one := fun coordinate =>
    (historical.nestedSchedule.scale coordinate).2.2

@[simp] theorem prop62BoundedPureSchedule_schedule
    {levelCount : ℕ}
    (finiteSchedule :
      WZ2PaperFiniteNearbyScheduleData
        (family := family)
        (Kakeya.realRpowENN delta (-loss))
        outputConstant levelCount)
    (historicalCount :
      historical.nestedSchedule.scaleCount =
        finiteSchedule.scaleCount) :
    (aligned.prop62BoundedPureSchedule
      historical outputFinite finiteSchedule
        historicalCount).schedule =
      aligned.prop62PureSchedule historical outputFinite := by
  rfl

end WZ2PaperAlignedPureExactSource

end Kakeya.Assouad

end
