import MyLeanRepo.Kakeya.Assouad.PureWZ2.PostDeletionUniversalInputAssembly
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# Post-deletion universal witness: the missing loss gap

The frozen construction-witness leaf uses the same `outputLoss` in three
places:

* the normalized final extremal CWA constant `delta ^ (-outputLoss)`;
* the smallest possible actual requested scale `delta`;
* the caller lower window `delta ^ (1 - outputLoss)`.

Consequently, `within_factor` gives only
`actual < delta ^ (1 - outputLoss)`.  No smaller uniform scale threshold can
turn this strict upper bound into
`2400000 * actual ≤ delta ^ (1 - outputLoss)`.

The scalar obstruction below occurs before any schedule, rounding,
restriction, balancing, or deletion choice.  The final theorem records the
minimal scale-level repair: the normalized nearby-scale CWA must use an
`internalLoss` strictly smaller than the public `outputLoss`.  A complete
construction witness would still need separate producers for
`cropped_base_bound` and `fixed_balancing_input`, which are not fields of the
frozen normalization record.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The frozen normalized final extremal uses exactly the public output loss. -/
theorem pureWZ2_normalized_final_extremal_uses_output_loss
    {delta sigma outputLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma outputLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := outputLoss) source normalizationExponent) :
    WZ2PaperPureCWAAtNearbyScales
      normalized.croppedFamily
      (Kakeya.realRpowENN delta (-outputLoss)) :=
  normalized.final_extremal.cwa_nearby_scales

/--
At the minimum requested scale, the nearby-scale error constant consumes
exactly the same loss as the caller lower window.
-/
theorem pureWZ2_min_requested_window_identity
    {delta loss : ℝ}
    (deltaPos : 0 < delta) :
    Kakeya.realRpowENN delta (-loss) *
        ENNReal.ofReal delta =
      ENNReal.ofReal (Real.rpow delta (1 - loss)) := by
  rw [Kakeya.realRpowENN]
  rw [← ENNReal.ofReal_mul
    (p := Real.rpow delta (-loss))
    (q := delta)
    (Real.rpow_nonneg deltaPos.le (-loss))]
  congr 1
  calc
    Real.rpow delta (-loss) * delta =
        Real.rpow delta (-loss) * Real.rpow delta 1 := by
      exact
        congrArg
          (fun value : ℝ =>
            Real.rpow delta (-loss) * value)
          (Real.rpow_one delta).symm
    _ = Real.rpow delta ((-loss) + 1) :=
      (Real.rpow_add deltaPos (-loss) 1).symm
    _ = Real.rpow delta (1 - loss) := by
      congr 1
      ring

/--
The scalar data permitted by the same-loss minimum-request window but
forbidden by the quotient-net scale gap.
-/
def PureWZ2SameLossActualToCallerObstruction
    (delta outputLoss : ℝ) : Prop :=
  ∃ (actualRequested callerRequested :
        WZ2PaperRequestedScale delta)
      (actual : ℝ),
    actualRequested.1 = delta ∧
    callerRequested.1 =
      Real.rpow delta (1 - outputLoss) ∧
    actualRequested.1 ≤ actual ∧
    ENNReal.ofReal actual <
      Kakeya.realRpowENN delta (-outputLoss) *
        ENNReal.ofReal actualRequested.1 ∧
    ¬ 2400000 * actual ≤ callerRequested.1

/--
Once `2 * delta ≤ delta ^ (1 - outputLoss)`, half of the caller lower
endpoint is a concrete obstruction.
-/
theorem pureWZ2_same_loss_actual_to_caller_obstruction
    {delta outputLoss : ℝ}
    (deltaPos : 0 < delta)
    (deltaOne : delta ≤ 1)
    (outputLossOne : outputLoss ≤ 1)
    (scaleRoom :
      2 * delta ≤ Real.rpow delta (1 - outputLoss)) :
    PureWZ2SameLossActualToCallerObstruction
      delta outputLoss := by
  let callerScale := Real.rpow delta (1 - outputLoss)
  have callerScalePos : 0 < callerScale := by
    exact Real.rpow_pos_of_pos deltaPos _
  have deltaLeCaller : delta ≤ callerScale := by
    dsimp only [callerScale]
    nlinarith
  have callerScaleOne : callerScale ≤ 1 := by
    dsimp only [callerScale]
    exact
      Real.rpow_le_one deltaPos.le deltaOne (by linarith)
  let actualRequested : WZ2PaperRequestedScale delta :=
    ⟨delta, le_rfl, deltaOne⟩
  let callerRequested : WZ2PaperRequestedScale delta :=
    ⟨callerScale, deltaLeCaller, callerScaleOne⟩
  let actual := callerScale / 2
  have requestedLeActual : actualRequested.1 ≤ actual := by
    dsimp only [actualRequested, actual, callerScale]
    nlinarith
  have actualLtCaller : actual < callerScale := by
    dsimp only [actual]
    nlinarith
  have withinFactor :
      ENNReal.ofReal actual <
        Kakeya.realRpowENN delta (-outputLoss) *
          ENNReal.ofReal actualRequested.1 := by
    dsimp only [actualRequested]
    rw [pureWZ2_min_requested_window_identity deltaPos]
    exact
      (ENNReal.ofReal_lt_ofReal_iff callerScalePos).mpr
        actualLtCaller
  have scaleGapFalse :
      ¬ 2400000 * actual ≤ callerRequested.1 := by
    intro scaleGap
    dsimp only [actual, callerRequested] at scaleGap
    nlinarith
  exact
    ⟨actualRequested, callerRequested, actual, rfl, rfl,
      requestedLeActual, withinFactor, scaleGapFalse⟩

/--
Shrinking a uniform scale threshold cannot recover the missing fixed-factor
gap when the normalized and public losses are equal.
-/
theorem pureWZ2_same_loss_gap_cannot_be_recovered_by_delta_threshold
    {outputLoss : ℝ}
    (outputLossPos : 0 < outputLoss)
    (outputLossOne : outputLoss ≤ 1) :
    ∀ deltaCeiling : ℝ, 0 < deltaCeiling →
      ∃ delta : ℝ,
        0 < delta ∧
        delta ≤ deltaCeiling ∧
        PureWZ2SameLossActualToCallerObstruction
          delta outputLoss := by
  rcases
      exists_delta_mul_rpow_le_rpow
        2 (by norm_num)
        (alpha := 1) (beta := 1 - outputLoss)
        (by linarith)
    with
    ⟨scaleCeiling, scaleCeilingPos, scaleCeilingOne, absorb⟩
  intro deltaCeiling deltaCeilingPos
  let delta := min deltaCeiling scaleCeiling
  have deltaPos : 0 < delta :=
    lt_min deltaCeilingPos scaleCeilingPos
  have deltaLeRequested : delta ≤ deltaCeiling :=
    min_le_left deltaCeiling scaleCeiling
  have deltaLeScale : delta ≤ scaleCeiling :=
    min_le_right deltaCeiling scaleCeiling
  have deltaOne : delta ≤ 1 :=
    deltaLeScale.trans scaleCeilingOne
  have scaleRoom :
      2 * delta ≤ Real.rpow delta (1 - outputLoss) := by
    have absorbed := absorb delta deltaPos deltaLeScale
    simpa using absorbed
  exact
    ⟨delta, deltaPos, deltaLeRequested,
      pureWZ2_same_loss_actual_to_caller_obstruction
        deltaPos deltaOne outputLossOne scaleRoom⟩

/--
The quantifier-correct loss-gap repair of the frozen construction-witness
leaf.

The normalized source and its nearby-scale CWA use `internalLoss`, chosen
strictly before the common scale threshold, while the caller window retains
the public `outputLoss`.  This interface repairs the scalar scale gap only;
proving it still requires source localization for `cropped_base_bound` and a
producer for `fixed_balancing_input`.
-/
def PureWZ2PostDeletionUniversalConstructionWitnessGapLeafAt
    (normalizationExponent deletionExponent : ℕ) : Prop :=
  ∀ sigma : ℝ,
    ∀ _critical : PureWZ2CriticalPackage sigma,
    ∀ outputLoss : ℝ, 0 < outputLoss →
      ∃ internalLoss delta₀ : ℝ,
        0 < internalLoss ∧
        internalLoss < outputLoss ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ source :
              PureWZ2ExtremalConfiguration
                sigma internalLoss delta,
            ∀ normalized :
                PureWZ2CroppedCriticalNormalizationData
                  (outputLoss := internalLoss)
                  source normalizationExponent,
              ∀ rho : WZ2PaperRequestedScale delta,
                Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                rho.1 ≤ Real.rpow delta outputLoss →
                  Nonempty
                    (PureWZ2PostDeletionUniversalConstructionWitness
                      normalized rho deletionExponent)

/--
With `internalLoss < outputLoss`, the exponent gap absorbs the quotient-net
constant uniformly.  This is the scale-level quantifier correction needed by
the construction witness: choose `internalLoss` before the uniform scale
threshold, normalize with that loss, and keep the caller window at the public
`outputLoss`.
-/
theorem pureWZ2_internal_loss_gap_actual_to_caller
    {internalLoss outputLoss : ℝ}
    (lossGap : internalLoss < outputLoss) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta}
          (actualRequested : WZ2PaperRequestedScale delta)
          (actualNearby :
            WZ2PaperPureNearbyScaleCoverData
              fine actualRequested
              (Kakeya.realRpowENN delta (-internalLoss)))
          (callerRequested : WZ2PaperRequestedScale delta),
          actualRequested.1 = delta →
          Real.rpow delta (1 - outputLoss) ≤
              callerRequested.1 →
            2400000 * actualNearby.rho ≤ callerRequested.1 := by
  rcases
      exists_delta_mul_rpow_le_rpow
        2400000 (by norm_num)
        (alpha := 1 - internalLoss)
        (beta := 1 - outputLoss)
        (by linarith)
    with
    ⟨delta₀, delta₀Pos, delta₀One, absorb⟩
  refine ⟨delta₀, delta₀Pos, delta₀One, ?_⟩
  intro delta deltaPos deltaSmall fine actualRequested
    actualNearby callerRequested actualRequestedEq callerLower
  have nearbyWindow :
      ENNReal.ofReal actualNearby.rho <
        ENNReal.ofReal
          (Real.rpow delta (1 - internalLoss)) := by
    calc
      ENNReal.ofReal actualNearby.rho <
          Kakeya.realRpowENN delta (-internalLoss) *
            ENNReal.ofReal actualRequested.1 :=
        actualNearby.within_factor
      _ =
          Kakeya.realRpowENN delta (-internalLoss) *
            ENNReal.ofReal delta := by
        rw [actualRequestedEq]
      _ =
          ENNReal.ofReal
            (Real.rpow delta (1 - internalLoss)) :=
        pureWZ2_min_requested_window_identity deltaPos
  have nearbyUpper :
      actualNearby.rho <
        Real.rpow delta (1 - internalLoss) := by
    exact
      (ENNReal.ofReal_lt_ofReal_iff
        (Real.rpow_pos_of_pos deltaPos _)).mp nearbyWindow
  calc
    2400000 * actualNearby.rho ≤
        2400000 *
          Real.rpow delta (1 - internalLoss) := by
      gcongr
    _ ≤ Real.rpow delta (1 - outputLoss) :=
      absorb delta deltaPos deltaSmall
    _ ≤ callerRequested.1 := callerLower

end Kakeya.Assouad

end
