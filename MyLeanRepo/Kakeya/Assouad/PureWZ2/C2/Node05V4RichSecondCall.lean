import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichFirstCall
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DyadicPropertyThreeMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentLocalVolume

/-!
# Node 5 rich V4 second call

This module implements the second Proposition 6.2 call in the paper order
used by WZ1 Lemma 5.4.  Its input is the exact final coarse `T₆` pair of the
first rich call, and its requested scale is `sqrt rho`.

The two loss schedules are selected before runtime.  At runtime,
`PureWZ2Node05V4RichSecondCallSchedule.run` invokes `runTerminal` directly on
`first.finalCoarseFamily`, `first.finalCoarseShading`, and the loss-only
weakening of `first.canonicalCoarseReentry`.  No family, shading, frame,
certificate, or balancing witness is reselected.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
The two rich schedules in the paper's dependency order.

The underlying closed producer chooses the second kernel first, sets the
first output loss from that kernel's source loss, and only then chooses the
first kernel.  Thus this datum is fixed before either runtime source or scale.
-/
structure PureWZ2Node05V4RichSecondCallSchedule
    (sigma outputLoss : ℝ) where
  calls :
    PureWZ2.Proposition63RichTwoCallScheduleData sigma outputLoss

/-- Select the second-call schedule at P0, before runtime objects and scales. -/
theorem pureWZ2Node05V4RichSecondCallSchedule_nonempty
    (sigma : ℝ)
    (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ)
    (outputLossPos : 0 < outputLoss)
    (outputLossLeOne : outputLoss ≤ 1) :
    Nonempty (PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss) := by
  rcases
      PureWZ2.proposition63_rich_two_call_schedule
        sigma critical outputLoss outputLossPos outputLossLeOne
    with
    ⟨calls⟩
  exact ⟨{ calls := calls }⟩

namespace PureWZ2Node05V4RichSecondCallSchedule

variable
    {sigma outputLoss : ℝ}
    (schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss)

/-- The first-call loss selected only after the second kernel. -/
abbrev firstOutputLoss : ℝ :=
  schedule.calls.firstOutputLoss

/-- The preselected second rich kernel. -/
abbrev secondKernel :
    PureWZ2.Proposition63RichStickyKernelScheduleData sigma outputLoss :=
  schedule.calls.second

/--
The first rich schedule paired with the preselected second kernel.
The public capability contributes no runtime family or shading.
-/
def firstCallSchedule
    (capability : PureWZ2PropStickyCapability) :
    PureWZ2Node05V4RichFirstCallSchedule
      capability sigma schedule.firstOutputLoss where
  kernel := schedule.calls.first

/--
Retarget the first call's canonical coarse re-entry to the losses selected by
the second kernel.  `mono_losses` preserves the exact final `T₆` family,
shading, frame, and provenance definitionally.
-/
noncomputable def kernelReentry
    {capability : PureWZ2PropStickyCapability}
    {inputLoss delta : ℝ}
    {current :
      PureWZ2ReentrantGrainSource
        sigma inputLoss delta capability.normalizationExponent}
    {rho : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    (first :
      PureWZ2Node05V4RichFirstCallData
        (schedule.firstCallSchedule capability) current rho inputLossLe) :
    PureWZ2PropStickyReentryData
      (sigma := sigma) first.finalCoarseShading 0
      schedule.secondKernel.sourceLoss
      schedule.secondKernel.normalizationLoss :=
  first.canonicalCoarseReentry.mono_losses
    (by
      have budget := first.rich.coarseSourceLoss_budget
      linarith [
        budget,
        first.rich.coarseSourceLoss_pos,
        schedule.calls.firstOutputLoss_eq,
        schedule.calls.firstOutputLoss_lt_secondSource])
    (by
      rw [first.rich.coarseNormalizationLoss_eq]
      have budget := first.rich.coarseSourceLoss_budget
      linarith [
        budget,
        schedule.calls.firstOutputLoss_eq,
        schedule.calls.firstOutputLoss_lt_secondSource,
        schedule.secondKernel.sourceLoss_le_half,
        first.rich.coarseSourceLoss_pos,
        schedule.secondKernel.normalizationLoss_pos])
    schedule.secondKernel.sourceLoss_pos
    schedule.secondKernel.normalizationLoss_pos
    schedule.secondKernel.sourceLoss_le_half

end PureWZ2Node05V4RichSecondCallSchedule

/--
The dependent two-call witness.

`first` is the sole first rich invocation, while `second` is the sole second
rich invocation.  The type of `second` fixes its input to the exact final
coarse family and shading projected from `first`.
-/
structure PureWZ2Node05V4RichSecondCallData
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta : ℝ}
    (schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss)
    (current :
      PureWZ2ReentrantGrainSource
        sigma inputLoss delta capability.normalizationExponent)
    (rho : WZ2PaperRequestedScale delta)
    (inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss)
    (sqrtRequested : WZ2PaperRequestedScale rho.1) where
  sqrtRequested_eq : sqrtRequested.1 = Real.sqrt rho.1
  first :
    PureWZ2Node05V4RichFirstCallData
      (schedule.firstCallSchedule capability) current rho inputLossLe
  second :
    PureWZ2.Proposition63RichTerminalStickyData
      (outputLoss := outputLoss)
      first.finalCoarseShading
      (schedule.kernelReentry first)
      sqrtRequested

namespace PureWZ2Node05V4RichSecondCallData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current :
      PureWZ2ReentrantGrainSource
        sigma inputLoss delta capability.normalizationExponent}
    {rho : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rho.1}
    (data :
      PureWZ2Node05V4RichSecondCallData
        schedule current rho inputLossLe sqrtRequested)

/-- The first rich witness retained in the dependent two-call object. -/
abbrev firstRich := data.first.rich

/-- The second rich witness retained in the dependent two-call object. -/
abbrev secondRich := data.second

/-- The exact first `T₆` family used as the second call's input family. -/
abbrev secondInputFamily := data.first.finalCoarseFamily

/-- The exact first `T₆` shading used as the second call's input shading. -/
abbrev secondInputShading := data.first.finalCoarseShading

@[simp] theorem second_input_family_eq :
    data.secondInputFamily = data.first.finalCoarseFamily := rfl

@[simp] theorem second_input_shading_eq :
    data.secondInputShading = data.first.finalCoarseShading := rfl

/-- Type-level receipt that the second rich call is on the first final pair. -/
theorem second_has_exact_first_final_input :
    Nonempty
      (PureWZ2.Proposition63RichTerminalStickyData
        (outputLoss := outputLoss)
        data.first.finalCoarseShading
        (schedule.kernelReentry data.first)
        sqrtRequested) :=
  ⟨data.second⟩

/-- The first level's exact terminal balanced cover. -/
abbrev firstBalancedCover := data.first.fourDegreeBalancedCover

/-- The second level's exact terminal balanced cover. -/
abbrev secondBalancedCover := data.second.terminal.balanced

/-- The first level's canonical complete-fibre outputs. -/
abbrev firstFinalFibres := data.first.canonicalRescaledFiber

/-- The second level's canonical complete-fibre outputs. -/
abbrev secondFinalFibres := data.second.canonical_rescaled_fiber

/-- The final selected fine family of the second V4 producer. -/
abbrev secondFinalFineFamily := data.second.data.selected.family

/-- The final refined fine shading of the second V4 producer. -/
abbrev secondRefinedFineShading := data.second.data.refined

/-- The exact final cover produced by the second V4 call. -/
abbrev secondFinalCover := data.second.data.cover

/-- The final coarse family produced by the second V4 call. -/
abbrev secondFinalCoarseFamily := data.second.data.coarse

/-- The final coarse shading produced by the second V4 call. -/
abbrev secondFinalCoarseShading := data.second.data.croppedCoarseShading

/--
The canonical re-entry for a following call, projected from the same second
rich witness.  The argument is precisely the strict axial premise required by
the frozen rich-output projection; it does not alter the input pair.
-/
noncomputable def secondCanonicalCoarseReentry
    (secondInputAxialWindow :
      ∀ index point,
        point ∈
            (schedule.kernelReentry data.first).geometry.frame ''
              (schedule.kernelReentry data.first).geometry.ordinaryRefined.carrier
                index →
          |point (2 : Fin 3)| ≤ 1 / 8) :
    PureWZ2PropStickyReentryData
      (sigma := sigma) data.secondFinalCoarseShading 0
      data.second.coarseSourceLoss data.second.coarseNormalizationLoss :=
  data.second.coarseReentry secondInputAxialWindow

/-- Final complete-fibre mass at the first `delta → rho` level. -/
theorem first_final_fiber_mass_lower
    (parent : Fin data.first.finalCoarseFamily.card) :
    Kakeya.realRpowENN rho.1 schedule.firstOutputLoss *
          (data.first.fourDegreeReceipts.fiberFloor : ENNReal) *
          Kakeya.realRpowENN delta 2 ≤
      data.first.finalCover.toPaperTubeCover.fiberShadedMass
        data.first.refinedFineShading parent :=
  data.first.final_fiber_mass_lower parent

/-- Final complete-fibre mass at the second `rho → sqrt rho` level. -/
theorem second_final_fiber_mass_lower
    (parent : Fin data.secondFinalCoarseFamily.card) :
    Kakeya.realRpowENN sqrtRequested.1 outputLoss *
          (data.second.terminal.fiberFloor : ENNReal) *
          Kakeya.realRpowENN rho.1 2 ≤
      data.secondFinalCover.toPaperTubeCover.fiberShadedMass
        data.secondRefinedFineShading parent :=
  data.second.terminal_fiber_mass_lower parent

/-- Complete-fibre cardinality at the second level. -/
theorem second_final_fiber_cardinality
    (parent : Fin data.secondFinalCoarseFamily.card) :
    (data.second.terminal.fiberFloor : ENNReal) ≤
          wz2PaperFullFiberCount
            data.secondFinalFineFamily data.secondFinalCoarseFamily parent ∧
      wz2PaperFullFiberCount
            data.secondFinalFineFamily data.secondFinalCoarseFamily parent <
        2 * (data.second.terminal.fiberFloor : ENNReal) :=
  data.second.terminal.fiber_cardinality parent

/-- The second rich fine refinement has the same paper-sized union-volume
floor as its exact first-call coarse input.  The second refinement sits inside
that input, while the first terminal coarse multiplicity band controls both
indexed masses; those two multiplicities cancel. -/
theorem second_refined_volume_lower
    (hrhoSmall : rho.1 ≤ 1 / 12) :
    wz2PaperPureRefinementFraction rho.1 61 *
        Kakeya.realRpowENN rho.1
          (sigma + 2 * schedule.firstOutputLoss) ≤
      (data.first.fourDegreeReceipts.regularity : ENNReal) *
        MeasureTheory.volume data.secondRefinedFineShading.union := by
  let multiplicity : ENNReal :=
    data.first.fourDegreeReceipts.muCoarse
  have hinputVolume :
      Kakeya.realRpowENN rho.1
          (sigma + 2 * schedule.firstOutputLoss) ≤
        MeasureTheory.volume data.first.finalCoarseShading.union :=
    PureWZ2.proposition63_sticky_coarse_union_volume_lower
      data.first.publicSticky hrhoSmall
  have hretained :
      wz2PaperPureRefinementFraction rho.1 61 *
          data.first.finalCoarseShading.mass ≤
        data.secondRefinedFineShading.mass :=
    data.second.data.retained_mass
  have hinputMultiplicityFloor :
      (data.first.fourDegreeReceipts.muCoarse : ENNReal) *
          MeasureTheory.volume data.first.finalCoarseShading.union ≤
        data.first.finalCoarseShading.mass := by
    apply multiplicity_floor_le_mass
    intro point hpoint
    exact (data.first.fourDegreeReceipts.coarse_pointMultiplicity_band hpoint).1
  have houtputMultiplicityCap :
      data.secondRefinedFineShading.mass ≤
        ((data.first.fourDegreeReceipts.regularity : ENNReal) * multiplicity) *
          MeasureTheory.volume data.secondRefinedFineShading.union := by
    apply mass_le_of_pointMultiplicity_le
    intro point _hpoint
    have hsource : point ∈ data.first.finalCoarseShading.union := by
      rcases _hpoint with ⟨index, hmem⟩
      exact ⟨data.second.data.selected.embedding index,
        data.second.data.subshading index hmem⟩
    have hsubNat :=
      PureWZ2.sticky_refined_pointMultiplicity_le_source
        data.second.data point
    have hsub :
        (data.secondRefinedFineShading.pointMultiplicity point : ENNReal) ≤
          (data.first.finalCoarseShading.pointMultiplicity point : ENNReal) := by
      exact_mod_cast hsubNat
    exact hsub.trans <| by
      simpa only [multiplicity, Nat.cast_mul] using
        (data.first.fourDegreeReceipts.coarse_pointMultiplicity_band hsource).2
  have hscaled :
      multiplicity *
          (wz2PaperPureRefinementFraction rho.1 61 *
            Kakeya.realRpowENN rho.1
              (sigma + 2 * schedule.firstOutputLoss)) ≤
        multiplicity *
          ((data.first.fourDegreeReceipts.regularity : ENNReal) *
            MeasureTheory.volume data.secondRefinedFineShading.union) := by
    calc
      multiplicity *
            (wz2PaperPureRefinementFraction rho.1 61 *
              Kakeya.realRpowENN rho.1
                (sigma + 2 * schedule.firstOutputLoss)) ≤
          wz2PaperPureRefinementFraction rho.1 61 *
            data.first.finalCoarseShading.mass := by
        calc
          _ = wz2PaperPureRefinementFraction rho.1 61 *
              (multiplicity *
                Kakeya.realRpowENN rho.1
                  (sigma + 2 * schedule.firstOutputLoss)) := by ring
          _ ≤ wz2PaperPureRefinementFraction rho.1 61 *
              (multiplicity *
                MeasureTheory.volume data.first.finalCoarseShading.union) := by
            gcongr
          _ ≤ wz2PaperPureRefinementFraction rho.1 61 *
              data.first.finalCoarseShading.mass := by gcongr
      _ ≤ data.secondRefinedFineShading.mass := hretained
      _ ≤ ((data.first.fourDegreeReceipts.regularity : ENNReal) *
            multiplicity) *
          MeasureTheory.volume data.secondRefinedFineShading.union :=
        houtputMultiplicityCap
      _ = multiplicity *
          ((data.first.fourDegreeReceipts.regularity : ENNReal) *
            MeasureTheory.volume data.secondRefinedFineShading.union) := by ring
  have hmultiplicityZero : multiplicity ≠ 0 := by
    dsimp only [multiplicity]
    exact_mod_cast data.first.fourDegreeReceipts.muCoarse_pos.ne'
  have hmultiplicityTop : multiplicity ≠ ⊤ := by
    simp [multiplicity]
  apply
    (ENNReal.mul_le_mul_iff_right hmultiplicityZero hmultiplicityTop).mp
  simpa only [mul_comm] using hscaled

/-- Relative union-volume retention of the second direct-rich call on the
exact first `T₆` coarse input.  The first terminal coarse multiplicity floor
and ceiling cancel, leaving one copy of its regularity. -/
theorem second_refined_volume_relative_lower :
    wz2PaperPureRefinementFraction rho.1 61 *
        MeasureTheory.volume data.first.finalCoarseShading.union ≤
      (data.first.fourDegreeReceipts.regularity : ENNReal) *
        MeasureTheory.volume data.secondRefinedFineShading.union := by
  let multiplicity : ENNReal :=
    data.first.fourDegreeReceipts.muCoarse
  have hinputMultiplicityFloor :
      multiplicity *
          MeasureTheory.volume data.first.finalCoarseShading.union ≤
        data.first.finalCoarseShading.mass := by
    apply multiplicity_floor_le_mass
    intro point hpoint
    simpa only [multiplicity] using
      (data.first.fourDegreeReceipts.coarse_pointMultiplicity_band hpoint).1
  have hretained :
      wz2PaperPureRefinementFraction rho.1 61 *
          data.first.finalCoarseShading.mass ≤
        data.secondRefinedFineShading.mass :=
    data.second.data.retained_mass
  have houtputMultiplicityCap :
      data.secondRefinedFineShading.mass ≤
        ((data.first.fourDegreeReceipts.regularity : ENNReal) * multiplicity) *
          MeasureTheory.volume data.secondRefinedFineShading.union := by
    apply mass_le_of_pointMultiplicity_le
    intro point hpoint
    have hsource : point ∈ data.first.finalCoarseShading.union := by
      rcases hpoint with ⟨index, hmem⟩
      exact ⟨data.second.data.selected.embedding index,
        data.second.data.subshading index hmem⟩
    have hsub :
        (data.secondRefinedFineShading.pointMultiplicity point : ENNReal) ≤
          (data.first.finalCoarseShading.pointMultiplicity point : ENNReal) := by
      exact_mod_cast
        (PureWZ2.sticky_refined_pointMultiplicity_le_source
          data.second.data point)
    exact hsub.trans <| by
      simpa only [multiplicity, Nat.cast_mul] using
        (data.first.fourDegreeReceipts.coarse_pointMultiplicity_band hsource).2
  have hscaled :
      multiplicity *
          (wz2PaperPureRefinementFraction rho.1 61 *
            MeasureTheory.volume data.first.finalCoarseShading.union) ≤
        multiplicity *
          ((data.first.fourDegreeReceipts.regularity : ENNReal) *
            MeasureTheory.volume data.secondRefinedFineShading.union) := by
    calc
      _ = wz2PaperPureRefinementFraction rho.1 61 *
          (multiplicity *
            MeasureTheory.volume data.first.finalCoarseShading.union) := by ring
      _ ≤ wz2PaperPureRefinementFraction rho.1 61 *
          data.first.finalCoarseShading.mass := by gcongr
      _ ≤ data.secondRefinedFineShading.mass := hretained
      _ ≤ ((data.first.fourDegreeReceipts.regularity : ENNReal) *
            multiplicity) *
          MeasureTheory.volume data.secondRefinedFineShading.union :=
        houtputMultiplicityCap
      _ = multiplicity *
          ((data.first.fourDegreeReceipts.regularity : ENNReal) *
            MeasureTheory.volume data.secondRefinedFineShading.union) := by ring
  have hmultiplicityZero : multiplicity ≠ 0 := by
    dsimp only [multiplicity]
    exact_mod_cast data.first.fourDegreeReceipts.muCoarse_pos.ne'
  have hmultiplicityTop : multiplicity ≠ ⊤ := by
    simp [multiplicity]
  apply
    (ENNReal.mul_le_mul_iff_right hmultiplicityZero hmultiplicityTop).mp
  simpa only [mul_comm] using hscaled

/-- The first call's terminal balanced-cell mass floor. -/
theorem first_cellMass_power_lower :
    Kakeya.realRpowENN rho.1 3 *
          Kakeya.realRpowENN (delta / rho.1)
            (sigma + 2 * data.first.rich.terminalLoss) ≤
      data.firstBalancedCover.cellMass :=
  data.first.final_cellMass_power_lower

/-- The second call's terminal balanced-cell mass floor, on the exact first
final pair and the requested `sqrt rho` scale. -/
theorem second_cellMass_power_lower :
    Kakeya.realRpowENN sqrtRequested.1 3 *
          Kakeya.realRpowENN (rho.1 / sqrtRequested.1)
            (sigma + 2 * data.second.terminalLoss) ≤
      data.secondBalancedCover.cellMass :=
  data.second.terminal_cellMass_power_lower

/-- Rewrite the second balanced-cell floor at the exact square-root scale.
This is the `rho^(3/2 + sigma/2 + loss)` source mass used in WZ Lemma 5.3. -/
theorem second_cellMass_rho_power_lower :
    Kakeya.realRpowENN rho.1
        (3 / 2 + sigma / 2 + data.second.terminalLoss) ≤
      data.secondBalancedCover.cellMass := by
  have hrho : 0 < rho.1 := data.first.publicSticky.coarse_extremal.delta_pos
  have hratio : rho.1 / Real.sqrt rho.1 = Real.sqrt rho.1 := by
    apply (div_eq_iff (Real.sqrt_pos.2 hrho).ne').2
    nlinarith [Real.sq_sqrt hrho.le]
  have hsqrtPower (exponent : ℝ) :
      Kakeya.realRpowENN (Real.sqrt rho.1) exponent =
        Kakeya.realRpowENN rho.1 (exponent / 2) := by
    simp only [Kakeya.realRpowENN, Real.sqrt_eq_rpow]
    apply congrArg ENNReal.ofReal
    calc
      (Real.rpow rho.1 (1 / 2 : ℝ)).rpow exponent =
          Real.rpow rho.1 ((1 / 2 : ℝ) * exponent) :=
        (Real.rpow_mul hrho.le (1 / 2 : ℝ) exponent).symm
      _ = Real.rpow rho.1 (exponent / 2) := by
        congr 1
        ring
  have hleft :
      Kakeya.realRpowENN sqrtRequested.1 3 *
          Kakeya.realRpowENN (rho.1 / sqrtRequested.1)
            (sigma + 2 * data.second.terminalLoss) =
        Kakeya.realRpowENN rho.1
          (3 / 2 + sigma / 2 + data.second.terminalLoss) := by
    rw [data.sqrtRequested_eq, hratio, hsqrtPower, hsqrtPower,
      ← realRpowENN_add hrho]
    congr 1
    ring
  rw [← hleft]
  exact data.second_cellMass_power_lower

end PureWZ2Node05V4RichSecondCallData

namespace PureWZ2Node05V4RichSecondCallSchedule

variable
    {sigma outputLoss : ℝ}

/--
Execute the second rich V4 call directly on the exact first final `T₆` pair.
The only non-object inputs are the kernel threshold, scale-window, and strict
axial proofs required by the already frozen rich kernel.
-/
theorem run
    (schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss)
    {capability : PureWZ2PropStickyCapability}
    {inputLoss delta : ℝ}
    {current :
      PureWZ2ReentrantGrainSource
        sigma inputLoss delta capability.normalizationExponent}
    {rho : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    (first :
      PureWZ2Node05V4RichFirstCallData
        (schedule.firstCallSchedule capability) current rho inputLossLe)
    (sqrtRequested : WZ2PaperRequestedScale rho.1)
    (sqrtRequestedEq : sqrtRequested.1 = Real.sqrt rho.1)
    (rhoLe : rho.1 ≤ schedule.secondKernel.delta₀)
    (sqrtLower :
      Real.rpow rho.1 (1 - outputLoss) ≤ sqrtRequested.1)
    (sqrtUpper :
      sqrtRequested.1 ≤ Real.rpow rho.1 outputLoss) :
    Nonempty
      (PureWZ2Node05V4RichSecondCallData
        schedule current rho inputLossLe sqrtRequested) := by
  rcases
      schedule.secondKernel.runTerminal
        rho.1 first.publicSticky.coarse_extremal.delta_pos rhoLe
        first.finalCoarseFamily first.finalCoarseShading
        (schedule.kernelReentry first)
        sqrtRequested sqrtLower sqrtUpper
    with
    ⟨second⟩
  exact
    ⟨{
      sqrtRequested_eq := sqrtRequestedEq
      first := first
      second := second
    }⟩

end PureWZ2Node05V4RichSecondCallSchedule

end Kakeya.Assouad

end
