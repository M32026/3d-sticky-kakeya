import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains

/-!
# Pure WZ2 large-slope statement

This module freezes the conclusion of WZ2 `prop: large slope` on the same
configuration that carries the `C²` global and local grain data.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The nonsingular `C²` condition for the literal Proposition 6.5 function
on `[-1,1]`.  An ambient representative is used only to state derivatives. -/
def PureWZ2C2SlopeIsNonsingular
    (f : PureWZ2C2SlopeFunction) : Prop :=
  ∃ extension : ℝ → ℝ,
    ContDiffOn ℝ 2 extension (Set.Icc (-1 : ℝ) 1) ∧
      (∀ z : PureWZ2UnitInterval, extension z.1 = f z) ∧
      ∀ z : PureWZ2UnitInterval,
        1 ≤ |deriv extension z.1| ∧
          |deriv extension z.1| ≤ 2 ∧
          |deriv (deriv extension) z.1| ≤ 1 / 100

/-- Restrict an internal globally smooth slope witness to the paper domain. -/
abbrev SlopeFunction.onUnitInterval
    (slope : SlopeFunction) : PureWZ2C2SlopeFunction :=
  fun z => slope z.1

/-- A globally smooth internal nonsingular slope supplies the interval-domain
certificate used by the construction modules. -/
theorem SlopeFunction.nonsingular_onUnitInterval
    (slope : SlopeFunction) (nonsingular : slope.IsNonsingular) :
    PureWZ2C2SlopeIsNonsingular slope.onUnitInterval := by
  refine ⟨slope, slope.contDiff.contDiffOn, ?_, ?_⟩
  · intro z
    rfl
  · intro z
    exact nonsingular z.1 z.2

/-- One same-configuration output of WZ2 `prop: large slope`, together with
the twisted-projection estimate deduced immediately after that proposition
in the paper. -/
structure PureWZ2LargeSlopeConfiguration
    (sigma loss delta : ℝ) where
  family : Kakeya.Streamlined.TubeFamily delta
  shading :
    WZ1PaperTubeShading family
  line_class :
    WZ1PaperIsLineClass family
  cubical :
    WZ1PaperIsCubicalShading shading
  extremal :
    WZ2PaperCroppedIsExtremal
      sigma loss family shading
  top_level_cwa :
    WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-loss))
  slope : SlopeFunction
  slope_nonsingular :
    slope.IsNonsingular
  global_ad :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (slope z))
          (horizontalSlice shading.union z))
        delta (1 - sigma)
          (Kakeya.realRpowENN delta (-loss))
  projection_upper :
    MeasureTheory.volume
        (twistedProjection slope '' shading.union) ≤
      Kakeya.realRpowENN delta (sigma - loss)
  localGrains :
    PureWZ2LocalGrainData
      shading sigma
      (Kakeya.realRpowENN delta (-loss))

/-- The paper conclusion of `prop: large slope` for one critical package. -/
def PureWZ2LargeSlopeFromCriticalStatement : Prop :=
  ∀ sigma : ℝ,
    PureWZ2CriticalPackage sigma →
      ∀ outputLoss delta₀ : ℝ,
        0 < outputLoss → 0 < delta₀ →
          ∃ delta : ℝ,
            0 < delta ∧ delta ≤ delta₀ ∧
            Nonempty
              (PureWZ2LargeSlopeConfiguration
                sigma outputLoss delta)

/-- Node 6 in the serial heavy-task chain. -/
def PureWZ2LargeSlopeStatement : Prop :=
  PureWZ2SubunitPackageStatement →
    PureWZ2CriticalExtractionStatement →
      PureWZ2PropStickyStatement →
        PureWZ2GrainsStatement →
          PureWZ2C2GrainsStatement →
            PureWZ2LargeSlopeFromCriticalStatement

end Kakeya.Assouad

end
