import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4GeometricReceipts
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantSource
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RichStickyKernel

/-!
# Node 5 rich V4 first call

This is the paper-order first Proposition 6.2 call used at an ordinary
Corollary-5.6 scale.  The public `PureWZ2PropStickyCapability.kernel` erases
the terminal four-degree certificate, so this module does not call that
projection and then try to reconstruct its receipts.  Instead, the
pre-runtime companion below selects the already proved rich V4 schedule from
`Proposition63RichStickyKernel`.

At runtime, `PureWZ2Node05V4RichFirstCallSchedule.run` calls that schedule
once on the supplied current re-entry and requested scale.  The resulting
dependent object derives its public re-entrant output, final coarse re-entry,
terminal multiplicity certificate, balanced cover, and fibre receipts from
that one rich witness.  No family, shading, balancing, exactification, or
owner is selected here.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
The minimal rich companion to the public Node-3 capability.

It is a proved companion, not a new mathematical hypothesis: the field is
implemented below by the closed rich V4 producer.  Its only purpose is to
keep selection of the rich schedule before the runtime source and scale.
-/
structure PureWZ2Node05V4RichFirstCallCapability
    (capability : PureWZ2PropStickyCapability) where
  schedule :
    ∀ sigma : ℝ,
      PureWZ2CriticalPackage sigma →
        ∀ outputLoss : ℝ,
          0 < outputLoss →
            outputLoss ≤ 1 →
              Nonempty
                (PureWZ2.Proposition63RichStickyKernelScheduleData
                  sigma outputLoss)

/--
Upgrade the erased public capability with the actual rich V4 producer.
The existing capability is retained as the normalization-exponent owner;
the rich producer itself is the closed producer from
`Proposition63RichStickyKernel`.
-/
theorem PureWZ2PropStickyCapability.toNode05V4RichFirstCallCapability
    (capability : PureWZ2PropStickyCapability) :
    PureWZ2Node05V4RichFirstCallCapability capability where
  schedule := by
    intro sigma critical outputLoss outputLossPos outputLossLeOne
    exact
      PureWZ2.proposition63_rich_sticky_kernel
        sigma critical outputLoss outputLossPos outputLossLeOne

/-- One rich first-call schedule fixed before the runtime source and scale. -/
structure PureWZ2Node05V4RichFirstCallSchedule
    (capability : PureWZ2PropStickyCapability)
    (sigma outputLoss : ℝ) where
  kernel :
    PureWZ2.Proposition63RichStickyKernelScheduleData sigma outputLoss

/-- Select the first-call schedule at P0, before `delta`, `current`, and `rho`. -/
theorem PureWZ2Node05V4RichFirstCallCapability.schedule_nonempty
    {capability : PureWZ2PropStickyCapability}
    (richCapability : PureWZ2Node05V4RichFirstCallCapability capability)
    (sigma : ℝ)
    (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ)
    (outputLossPos : 0 < outputLoss)
    (outputLossLeOne : outputLoss ≤ 1) :
    Nonempty
      (PureWZ2Node05V4RichFirstCallSchedule
        capability sigma outputLoss) := by
  rcases
      richCapability.schedule sigma critical outputLoss
        outputLossPos outputLossLeOne
    with
    ⟨kernel⟩
  exact ⟨{ kernel := kernel }⟩

namespace PureWZ2Node05V4RichFirstCallSchedule

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta : ℝ}
    (schedule :
      PureWZ2Node05V4RichFirstCallSchedule capability sigma outputLoss)

/--
The exact current re-entry weakened to the losses selected by the rich
schedule.  Its family, shading, rigid frame, and normalization exponent are
definitionally unchanged.
-/
noncomputable def kernelReentry
    (current :
      PureWZ2ReentrantGrainSource
        sigma inputLoss delta capability.normalizationExponent)
    (inputLossLe : inputLoss ≤ schedule.kernel.sourceLoss) :
    PureWZ2PropStickyReentryData
      (sigma := sigma)
      current.grain.shading capability.normalizationExponent
      schedule.kernel.sourceLoss schedule.kernel.normalizationLoss := by
  have ordinaryLossLe :
      current.ordinaryLoss ≤ schedule.kernel.sourceLoss := by
    exact current.reentry.sourceLoss_le_half.trans
      ((div_le_self current.reentry.normalizationLoss_pos.le
        (by norm_num)).trans inputLossLe)
  have sourceLeNormalization :
      schedule.kernel.sourceLoss ≤ schedule.kernel.normalizationLoss := by
    linarith [
      schedule.kernel.sourceLoss_le_half,
      schedule.kernel.normalizationLoss_pos]
  exact
    current.reentry.mono_losses
      ordinaryLossLe
      (inputLossLe.trans sourceLeNormalization)
      schedule.kernel.sourceLoss_pos
      schedule.kernel.normalizationLoss_pos
      schedule.kernel.sourceLoss_le_half

end PureWZ2Node05V4RichFirstCallSchedule

/--
One actual rich V4 first call.

The sole stored witness is the output of `runTerminal`; consequently the
public sticky datum and every terminal four-degree receipt exposed below are
projections of this same invocation.
-/
structure PureWZ2Node05V4RichFirstCallData
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta : ℝ}
    (schedule :
      PureWZ2Node05V4RichFirstCallSchedule capability sigma outputLoss)
    (current :
      PureWZ2ReentrantGrainSource
        sigma inputLoss delta capability.normalizationExponent)
    (rho : WZ2PaperRequestedScale delta)
    (inputLossLe : inputLoss ≤ schedule.kernel.sourceLoss) where
  rich :
    PureWZ2.Proposition63RichTerminalStickyData
      (outputLoss := outputLoss)
      current.grain.shading
      (schedule.kernelReentry current inputLossLe)
      rho

namespace PureWZ2Node05V4RichFirstCallData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta : ℝ}
    {schedule :
      PureWZ2Node05V4RichFirstCallSchedule capability sigma outputLoss}
    {current :
      PureWZ2ReentrantGrainSource
        sigma inputLoss delta capability.normalizationExponent}
    {rho : WZ2PaperRequestedScale delta}
    {inputLossLe : inputLoss ≤ schedule.kernel.sourceLoss}
    (data :
      PureWZ2Node05V4RichFirstCallData
        schedule current rho inputLossLe)

/-- The public sticky output from the same rich invocation. -/
abbrev publicSticky := data.rich.data

/-- The final selected fine family (`T₆` fine side) of the V4 producer. -/
abbrev finalFineFamily := data.publicSticky.selected.family

/-- The final refined fine shading retained after the V4 deletion. -/
abbrev refinedFineShading := data.publicSticky.refined

/-- The exact Section-6 cover between the final fine and coarse families. -/
abbrev finalCover := data.publicSticky.cover

/-- The final coarse `T₆` family. -/
abbrev finalCoarseFamily := data.publicSticky.coarse

/-- The final coarse `T₆` shading. -/
abbrev finalCoarseShading := data.publicSticky.croppedCoarseShading

/-- The public balanced cover carried by the same sticky output. -/
abbrev publicBalancedCover := data.publicSticky.balanced

/--
The terminal receipts projected from the actual four-degree certificate.
They remain indexed by `finalCover`, `refinedFineShading`, and
`finalCoarseShading`; no equality transport is involved.
-/
abbrev fourDegreeReceipts := data.rich.terminal

/-- The balanced cover retained by the terminal four-degree receipts. -/
abbrev fourDegreeBalancedCover := data.fourDegreeReceipts.balanced

/--
The complete public re-entrant output of this same rich invocation.
Its coarse re-entry is therefore the canonical next-call re-entry, not an
independently supplied existential witness.
-/
noncomputable def reentrant :
    PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      current.grain.shading rho 0 61 :=
  data.rich.toReentrant current.ordinary_axial_window_eighth

@[simp] theorem reentrant_data_eq :
    data.reentrant.data = data.publicSticky := rfl

/-- The canonical coarse re-entry for the next Proposition 6.2 call. -/
noncomputable def canonicalCoarseReentry :
    PureWZ2PropStickyReentryData
      (sigma := sigma) data.finalCoarseShading 0
      data.rich.coarseSourceLoss data.rich.coarseNormalizationLoss :=
  data.reentrant.coarseReentry

/-- Nearby-scale CWA on the exact final coarse `T₆` family. -/
theorem final_coarse_nearby_cwa :
    WZ2PaperPureCWAAtNearbyScales data.finalCoarseFamily
      (Kakeya.realRpowENN rho.1 (-outputLoss)) :=
  data.publicSticky.coarse_extremal.cwa_nearby_scales

/-- Final complete-fibre shaded mass on the exact terminal cover. -/
theorem final_fiber_mass_lower
    (parent : Fin data.finalCoarseFamily.card) :
    Kakeya.realRpowENN rho.1 outputLoss *
          (data.fourDegreeReceipts.fiberFloor : ENNReal) *
          Kakeya.realRpowENN delta 2 ≤
      data.finalCover.toPaperTubeCover.fiberShadedMass
        data.refinedFineShading parent :=
  data.rich.terminal_fiber_mass_lower parent

/-- Final complete-fibre cardinality band on the exact terminal families. -/
theorem final_fiber_cardinality
    (parent : Fin data.finalCoarseFamily.card) :
    (data.fourDegreeReceipts.fiberFloor : ENNReal) ≤
          wz2PaperFullFiberCount
            data.finalFineFamily data.finalCoarseFamily parent ∧
      wz2PaperFullFiberCount
            data.finalFineFamily data.finalCoarseFamily parent <
        2 * (data.fourDegreeReceipts.fiberFloor : ENNReal) :=
  data.fourDegreeReceipts.fiber_cardinality parent

/-- Exact fine multiplicity on every final parent--fine-cell packet. -/
theorem final_exact_fine_multiplicity
    (edge : Fin data.finalCoarseFamily.card × WZ2PaperCellIndex)
    (edgeMem : edge ∈ data.fourDegreeReceipts.packetCells) :
    ((wz2PaperFullFiberIndices
        data.finalFineFamily data.finalCoarseFamily edge.1).filter
      fun sourceIndex =>
        wz1PaperGridCube delta edge.2 ⊆
          data.refinedFineShading.carrier sourceIndex).card =
      data.fourDegreeReceipts.muFine :=
  data.fourDegreeReceipts.exact_fine_multiplicity edge edgeMem

/-- The coarse multiplicity band from the same terminal certificate. -/
theorem final_coarse_multiplicity
    (cell : WZ2PaperCellIndex)
    (cellMem : cell ∈ data.fourDegreeBalancedCover.activeCells) :
    data.fourDegreeReceipts.muCoarse ≤
          (Finset.univ.filter fun parent =>
            wz1PaperGridCube rho.1 cell ⊆
              data.finalCoarseShading.carrier parent).card ∧
      (Finset.univ.filter fun parent =>
        wz1PaperGridCube rho.1 cell ⊆
          data.finalCoarseShading.carrier parent).card ≤
        data.fourDegreeReceipts.regularity *
          data.fourDegreeReceipts.muCoarse :=
  data.fourDegreeReceipts.coarse_multiplicity cell cellMem

/-- Paper-sized lower bound for the exact terminal balanced-cell mass.  This
is retained by the rich V4 call itself and requires no later owner or
post-processing selection. -/
theorem final_cellMass_power_lower :
    Kakeya.realRpowENN rho.1 3 *
          Kakeya.realRpowENN (delta / rho.1)
            (sigma + 2 * data.rich.terminalLoss) ≤
      data.fourDegreeBalancedCover.cellMass :=
  data.rich.terminal_cellMass_power_lower

/-- The canonical complete-fibre rescaling from the same rich invocation. -/
abbrev canonicalRescaledFiber := data.rich.canonical_rescaled_fiber

end PureWZ2Node05V4RichFirstCallData

namespace PureWZ2Node05V4RichFirstCallSchedule

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta : ℝ}

/--
Execute the first ordinary call on the supplied current source and runtime
scale.  The rich output and its canonical re-entry are constructed internally.
-/
theorem run
    (schedule :
      PureWZ2Node05V4RichFirstCallSchedule capability sigma outputLoss)
    (current :
      PureWZ2ReentrantGrainSource
        sigma inputLoss delta capability.normalizationExponent)
    (inputLossLe : inputLoss ≤ schedule.kernel.sourceLoss)
    (deltaLe : delta ≤ schedule.kernel.delta₀)
    (rho : WZ2PaperRequestedScale delta)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho.1)
    (rhoUpper : rho.1 ≤ Real.rpow delta outputLoss) :
    Nonempty
      (PureWZ2Node05V4RichFirstCallData
        schedule current rho inputLossLe) := by
  rcases
      schedule.kernel.runTerminal
        delta current.grain.extremal.delta_pos deltaLe
        current.grain.family current.grain.shading
        (schedule.kernelReentry current inputLossLe)
        rho rhoLower rhoUpper
    with
    ⟨rich⟩
  exact ⟨{ rich := rich }⟩

end PureWZ2Node05V4RichFirstCallSchedule

end Kakeya.Assouad

end
