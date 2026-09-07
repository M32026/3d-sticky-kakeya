import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4TargetAdapter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4CriticalInputsAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4NormalizedLedgerRouting
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4NormalizedRichProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4PureFinalAssemblyInputs
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4SelectedIncidenceScalar
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4UniversalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4WindowedCoarseTrace
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4FrozenCoarseReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropStickyReentry

/-!
# Direct Proposition 6.2 V4 universal assembly

This module combines the ordinary critical floor, the completed
ordinary-to-cropped normalization, and the synchronized V4 producer.  The
coarse critical witness is obtained from genuine selected parent--cell
incidences, not from a reverse containment between cropped and ordinary
carriers.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open Kakeya.Assouad
open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Internal rich output of one reusable kernel call. -/
structure Prop62V4ReentryKernelOutput
    {delta sigma outputLoss sourceLoss normalizationLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    (croppedShading : WZ1PaperTubeShading croppedFamily)
    (reentry :
      PureWZ2PropStickyReentryData
        (sigma := sigma) croppedShading 0 sourceLoss normalizationLoss)
    (rho : WZ2PaperRequestedScale delta) where
  data :
    PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      croppedShading rho 61
  coarseSourceLoss : ℝ
  coarseNormalizationLoss : ℝ
  coarseSourceLoss_pos : 0 < coarseSourceLoss
  coarseNormalizationLoss_pos : 0 < coarseNormalizationLoss
  coarseSourceLoss_budget : 3 * coarseSourceLoss ≤ outputLoss
  coarseNormalizationLoss_eq :
    coarseNormalizationLoss = (7 / 2 : ℝ) * coarseSourceLoss
  coarseReentry :
    (∀ index point,
      point ∈
          reentry.geometry.frame ''
            reentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8) →
      PureWZ2PropStickyReentryData
        (sigma := sigma)
        data.croppedCoarseShading 0
        coarseSourceLoss coarseNormalizationLoss

namespace Prop62V4ReentryKernelOutput

/-- Retain the rich output at its native loss without rebuilding its data. -/
noncomputable def toReentrantSameLoss
    {delta sigma outputLoss sourceLoss normalizationLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry :
      PureWZ2PropStickyReentryData
        (sigma := sigma) croppedShading 0 sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (core :
      Prop62V4ReentryKernelOutput
        (outputLoss := outputLoss) croppedShading reentry rho)
    (rootAxialWindow :
      ∀ index point,
        point ∈
            reentry.geometry.frame ''
              reentry.geometry.ordinaryRefined.carrier index →
          |point (2 : Fin 3)| ≤ 1 / 8) :
    PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      croppedShading rho 0 61 where
  data := core.data
  coarseSourceLoss := core.coarseSourceLoss
  coarseNormalizationLoss := core.coarseNormalizationLoss
  coarseSourceLoss_pos := core.coarseSourceLoss_pos
  coarseNormalizationLoss_pos := core.coarseNormalizationLoss_pos
  coarseSourceLoss_budget := core.coarseSourceLoss_budget
  coarseNormalizationLoss_eq := core.coarseNormalizationLoss_eq
  coarseReentry := core.coarseReentry rootAxialWindow

/-- Weaken the numerical output loss without changing the exact coarse pair. -/
noncomputable def toReentrant
    {delta sigma firstLoss secondLoss sourceLoss normalizationLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry :
      PureWZ2PropStickyReentryData
        (sigma := sigma) croppedShading 0 sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (core :
      Prop62V4ReentryKernelOutput
        (outputLoss := firstLoss) croppedShading reentry rho)
    (lossLe : firstLoss ≤ secondLoss)
    (rootAxialWindow :
      ∀ index point,
        point ∈
            reentry.geometry.frame ''
              reentry.geometry.ordinaryRefined.carrier index →
          |point (2 : Fin 3)| ≤ 1 / 8) :
    PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := secondLoss)
      croppedShading rho 0 61 where
  data := PureWZ2PropStickyData.mono_loss core.data lossLe
  coarseSourceLoss := core.coarseSourceLoss
  coarseNormalizationLoss := core.coarseNormalizationLoss
  coarseSourceLoss_pos := core.coarseSourceLoss_pos
  coarseNormalizationLoss_pos := core.coarseNormalizationLoss_pos
  coarseSourceLoss_budget :=
    core.coarseSourceLoss_budget.trans lossLe
  coarseNormalizationLoss_eq := core.coarseNormalizationLoss_eq
  coarseReentry := core.coarseReentry rootAxialWindow

end Prop62V4ReentryKernelOutput

/--
The reusable V4 kernel on an exact re-entry pair.

The scalar schedule and uniform threshold are selected before `delta`, the
exact cropped pair, and `rho`.  At runtime the kernel converts the supplied
re-entry object back to the existing normalization input without changing its
cropped family or shading.
-/
theorem pureWZ2_prop_sticky_reentry_v4_core_exact_source
    (hFixedGrid : FixedGridBoundaryRemovalStatement)
    (hTreeCleanup : OnePassTreeCleanupStatement)
    (sigma : ℝ)
    (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ)
    (outputLossPos : 0 < outputLoss)
    (outputLossLeOne : outputLoss ≤ 1) :
    ∃ normalizationLoss delta₀ : ℝ,
      0 < pureWZ2CompleteNormalizationFinalLoss normalizationLoss ∧
      0 < normalizationLoss ∧
      pureWZ2CompleteNormalizationFinalLoss normalizationLoss ≤
        normalizationLoss / 2 ∧
      normalizationLoss < outputLoss ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ (croppedFamily :
            Kakeya.Streamlined.TubeFamily delta),
          ∀ (croppedShading : WZ1PaperTubeShading croppedFamily),
            ∀ reentry :
                PureWZ2PropStickyReentryData
                  (sigma := sigma)
                  croppedShading 0
                  (pureWZ2CompleteNormalizationFinalLoss
                    normalizationLoss)
                  normalizationLoss,
              ∀ rho : WZ2PaperRequestedScale delta,
                Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                rho.1 ≤ Real.rpow delta outputLoss →
                  Nonempty
                    (Prop62V4ReentryKernelOutput
                      (outputLoss := outputLoss)
                      croppedShading reentry rho) := by
  rcases
      Kakeya.Assouad.Prop62PaperAudit.V4.PureWZ2CriticalPackage.prop62V4_pure_scalar_routing
        critical
        10 8 2 51 outputLossPos outputLossLeOne
    with
    ⟨scalarRouting⟩
  let routing := scalarRouting.routing
  let scalar := scalarRouting.scalar
  rcases
      prop62V4_three_loss_routing routing outputLossLeOne
    with
    ⟨three⟩
  rcases three with
    ⟨sourceLoss, normalizationLoss, workingEta,
      sourceLossEq, normalizationLossEq, workingEtaEq,
      sourceLossPos, normalizationLossPos, workingEtaPos,
      sourceLossLeEighth, sourceLossLeHalf, sourceLossLeHierarchy,
      normalizationLossWorking, normalizationLossOutput⟩
  subst workingEta
  subst sourceLoss
  let three : Prop62V4ThreeLossRoutingData routing :=
    {
      sourceLoss :=
        pureWZ2CompleteNormalizationFinalLoss normalizationLoss
      normalizationLoss := normalizationLoss
      workingEta := routing.numerics.hierarchy.stableLoss
      sourceLoss_eq := rfl
      normalizationLoss_eq := normalizationLossEq
      workingEta_eq := rfl
      sourceLoss_pos := sourceLossPos
      normalizationLoss_pos := normalizationLossPos
      workingEta_pos := workingEtaPos
      sourceLoss_le_eighth := sourceLossLeEighth
      sourceLoss_le_half := sourceLossLeHalf
      sourceLoss_le_hierarchy := sourceLossLeHierarchy
      normalizationLoss_lt_workingEta := normalizationLossWorking
      normalizationLoss_output_budget := normalizationLossOutput
    }
  let cleanupOracle : PureWZ2Prop62CleanupOracle :=
    onePassTreeCleanupStatement_to_pureWZ2Prop62CleanupOracle
      hTreeCleanup
  rcases
      prop62V4_normalized_rich_producer
        three hFixedGrid cleanupOracle
    with
    ⟨richReceipt⟩
  rcases
      prop62V4_normalized_ledger_routing routing three
    with
    ⟨ledgerReceipt⟩
  rcases
      prop62V4_selected_incidence_pure_scalar_extension
        10 8 2 51 sigma outputLoss outputLossPos routing scalar
    with
    ⟨incidenceScalar⟩
  let coarseSourceLoss :=
    routing.numerics.hierarchy.finalStrongLoss
  let coarseNormalizationLoss :=
    (7 / 2 : ℝ) * coarseSourceLoss
  rcases
      wz2PaperPureNearby_topLevelPaperCWA_eventually
        (loss := coarseSourceLoss)
        (outputLoss := coarseNormalizationLoss)
        routing.numerics.hierarchy.finalStrongLoss_pos
        (by
          nlinarith [
            routing.numerics.hierarchy.final_output_budget,
            outputLossLeOne])
        (by
          change
            3 * routing.numerics.hierarchy.finalStrongLoss <
              (7 / 2 : ℝ) *
                routing.numerics.hierarchy.finalStrongLoss
          nlinarith [routing.numerics.hierarchy.finalStrongLoss_pos])
    with
    ⟨coarseTopDelta, coarseTopDeltaPos, _coarseTopDeltaOne,
      recoverCoarseTopCWA⟩
  rcases
      pure_wz2_exists_delta₀_rpow_le
        coarseTopDeltaPos
        outputLossPos
    with
    ⟨topScaleDelta, topScaleDeltaPos, _topScaleDeltaOne,
      topScaleSmall⟩
  let delta₀ :=
    min richReceipt.delta₀
      (min ledgerReceipt.delta₀
        (min incidenceScalar.delta₀ topScaleDelta))
  have delta₀Pos : 0 < delta₀ := by
    exact
      lt_min richReceipt.delta₀_pos <|
        lt_min ledgerReceipt.delta₀_pos <|
          lt_min incidenceScalar.delta₀_pos topScaleDeltaPos
  have delta₀LeOne : delta₀ ≤ 1 := by
    exact
      (min_le_left _ _).trans <|
        richReceipt.delta₀_le_one_hundred.trans (by norm_num)
  refine
    ⟨three.normalizationLoss, delta₀,
      three.sourceLoss_pos, three.normalizationLoss_pos,
      three.sourceLoss_le_half,
      by
        nlinarith [three.normalizationLoss_output_budget],
      delta₀Pos, delta₀LeOne, ?_⟩
  intro delta deltaPos deltaLe croppedFamily croppedShading reentry
    rho rhoLower rhoUpper
  let normalized := reentry.toNormalizationData
  have deltaRich : delta ≤ richReceipt.delta₀ :=
    deltaLe.trans (min_le_left _ _)
  have deltaLedger : delta ≤ ledgerReceipt.delta₀ :=
    deltaLe.trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have deltaIncidence : delta ≤ incidenceScalar.delta₀ :=
    deltaLe.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have deltaTopScale : delta ≤ topScaleDelta :=
    deltaLe.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
  have deltaScalar : delta ≤ scalar.delta₀ :=
    deltaIncidence.trans incidenceScalar.delta₀_le_scalar
  rcases
      richReceipt.produce
        deltaPos deltaRich normalized rho rhoLower rhoUpper
    with
    ⟨produced⟩
  let rich := produced.rich
  rcases
      ledgerReceipt.route deltaPos deltaLedger normalized
    with
    ⟨ledger⟩
  have sourceLedger :=
    rich.fixedGridMetric_hierarchySourceMassVolumeLedger
      (deltaLedger.trans ledgerReceipt.delta₀_le_one_twelfth)
      ledger
  let coarseWitness :
      Prop62V4FinalCoarseCriticalWitness
        rich.outputCertificate routing.critical.structuralLoss :=
    rich.finalCoarseCriticalWitness_of_selectedIncidence
      routing.critical incidenceScalar.overlap
      (deltaIncidence.trans incidenceScalar.delta₀_le_overlap)
      rhoUpper
      (scalar.rho_small deltaPos deltaScalar rhoUpper)
      (scalar.ratio_small
        deltaPos deltaScalar produced.metricCertificate.rho_pos rhoLower)
      (by
        simpa [three.workingEta_eq] using
          incidenceScalar.reduced_coarse_density
            deltaPos deltaIncidence
            produced.metricCertificate.rho_pos rhoUpper)
      (by
        simpa [three.workingEta_eq] using
          scalar.parent_cwa
            deltaPos deltaScalar
            produced.metricCertificate.rho_pos rhoUpper)
  let criticalInputs :=
    rich.criticalMultiplicityInputs
      scalar deltaScalar rhoLower rhoUpper
      three.sourceLoss_le_hierarchy three.workingEta_eq coarseWitness
  let productInputs :=
    scalar.productMultiplicityInputs
      rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
      rich.exactification rich.parentDegree rich.core rich.good
      rich.families (output := rich.canonicalOutput)
      deltaScalar rhoLower rhoUpper rich.regularity_bound
      sourceLedger.1 sourceLedger.2
  let componentInputs :=
    scalar.componentMultiplicityFloorInputs
      rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
      rich.exactification rich.parentDegree rich.core rich.good
      rich.families (output := rich.canonicalOutput)
      deltaScalar rhoLower rhoUpper rich.regularity_bound
  let volumeAbsorption :=
    scalar.extremalVolumeAbsorption
      deltaScalar deltaPos produced.metricCertificate.rho_pos
  let sourceFiberConstant : ENNReal :=
    Kakeya.realRpowENN delta (-8 * three.workingEta) / 81000000
  let finalInputs :=
    scalar.finalAssemblyInputs
      rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
      rich.exactification rich.parentDegree rich.core rich.good
      rich.families (output := rich.canonicalOutput)
      deltaScalar rho.2.1 rho.2.2 rhoLower rhoUpper
      rich.regularity_bound
      (by
        simpa [three.workingEta_eq] using rich.parent_constant_bound)
      criticalInputs productInputs componentInputs volumeAbsorption
      sourceFiberConstant rich.terminalRescaling
      (by
        simpa [sourceFiberConstant, three.workingEta_eq] using
          rich.terminal_fiber_constant_bound)
  let assembled :
      PureWZ2PropStickyData
        (sigma := sigma)
        (outputLoss := routing.numerics.hierarchy.finalStrongLoss)
        normalized.croppedRefined rho 61 :=
    rich.assemblePurePropStickySixtyOne
      (Prop62V4CriticalInputsAssembly.criticalForCap
        (routing := routing))
      criticalInputs productInputs componentInputs volumeAbsorption
      finalInputs.toFinalAssemblyInputsData
  let outputData :=
    PureWZ2PropStickyData.mono_loss
      (firstLoss := routing.numerics.hierarchy.finalStrongLoss)
      (secondLoss := outputLoss) assembled <| by
      linarith [
        routing.numerics.hierarchy.final_output_budget,
        routing.numerics.hierarchy.finalStrongLoss_pos]
  refine
    ⟨{
      data := outputData
      coarseSourceLoss := coarseSourceLoss
      coarseNormalizationLoss := coarseNormalizationLoss
      coarseSourceLoss_pos :=
        routing.numerics.hierarchy.finalStrongLoss_pos
      coarseNormalizationLoss_pos := by
        dsimp only [coarseNormalizationLoss, coarseSourceLoss]
        nlinarith [routing.numerics.hierarchy.finalStrongLoss_pos]
      coarseSourceLoss_budget := by
        dsimp only [coarseSourceLoss]
        exact routing.numerics.hierarchy.final_output_budget
      coarseNormalizationLoss_eq := rfl
      coarseReentry := ?_
    }⟩
  intro rootAxialWindow
  let lambda :=
    Kakeya.realRpowENN rho.1
      (routing.critical.structuralLoss / 2)
  have lambdaPos : 0 < lambda := by
    simp [lambda, Kakeya.realRpowENN,
      Real.rpow_pos_of_pos produced.metricCertificate.rho_pos]
  have rhoSmall : rho.1 ≤ 1 / 24 :=
    scalar.rho_small deltaPos deltaScalar rhoUpper
  have ratioSmall : delta / rho.1 ≤ 1 / 24 :=
    scalar.ratio_small
      deltaPos deltaScalar produced.metricCertificate.rho_pos rhoLower
  have rhoTopScale : rho.1 ≤ coarseTopDelta :=
    rhoUpper.trans (topScaleSmall delta deltaPos deltaTopScale)
  have densityScalar :
      PureWZ2Prop62FourDegreeOutputCertificate.SelectedIncidenceDensityScalar
        (densityConstant :=
          Kakeya.realRpowENN delta (2 * three.workingEta))
        lambda := by
    change
      (576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
          lambda ≤
        Kakeya.realRpowENN delta (2 * three.workingEta)
    simpa [lambda, three.workingEta_eq] using
      incidenceScalar.reduced_coarse_density
        deltaPos deltaIncidence
        produced.metricCertificate.rho_pos rhoUpper
  have densityBudget :
      Kakeya.realRpowENN rho.1 coarseSourceLoss / 2 ≤
        (100 : ENNReal)⁻¹ * lambda := by
    have finalLeStructural :
        Kakeya.realRpowENN rho.1 coarseSourceLoss ≤
          Kakeya.realRpowENN rho.1 routing.critical.structuralLoss := by
      apply pure_wz2_rpowENN_antitone
        produced.metricCertificate.rho_pos rho.2.2
      exact scalar.structural_to_final
    have absorbed :=
      incidenceScalar.overlap.overlap_absorption
        deltaPos
        (deltaIncidence.trans incidenceScalar.delta₀_le_overlap)
        produced.metricCertificate.rho_pos rhoUpper
    have structuralLeHalf :
        Kakeya.realRpowENN rho.1 routing.critical.structuralLoss ≤
          (100000 : ENNReal)⁻¹ * lambda := by
      have divided :=
        (ENNReal.mul_le_iff_le_inv
          (by norm_num : (100000 : ENNReal) ≠ 0)
          (by norm_num : (100000 : ENNReal) ≠ ⊤)).mp absorbed
      simpa [lambda] using divided
    calc
      Kakeya.realRpowENN rho.1 coarseSourceLoss / 2 ≤
          Kakeya.realRpowENN rho.1 coarseSourceLoss :=
        by
          rw [ENNReal.div_eq_inv_mul]
          calc
            (2 : ENNReal)⁻¹ *
                  Kakeya.realRpowENN rho.1 coarseSourceLoss ≤
                1 *
                  Kakeya.realRpowENN rho.1 coarseSourceLoss := by
              gcongr
              norm_num
            _ = Kakeya.realRpowENN rho.1 coarseSourceLoss := by simp
      _ ≤
          Kakeya.realRpowENN rho.1 routing.critical.structuralLoss :=
        finalLeStructural
      _ ≤ (100000 : ENNReal)⁻¹ * lambda := structuralLeHalf
      _ ≤ (100 : ENNReal)⁻¹ * lambda := by
        gcongr
        norm_num
  let ordinaryExtremal :
      WZ2PaperPureIsExtremal
        sigma coarseSourceLoss
        rich.outputCertificate.coarse.family
        rich.outputCertificate.finalCoarseOrdinaryTrace :=
    {
      delta_pos := produced.metricCertificate.rho_pos
      delta_le_one := rho.2.2
      nonempty := assembled.coarse_extremal.nonempty
      cwa_nearby_scales := assembled.coarse_extremal.cwa_nearby_scales
      dense := by
        have densityPower :
            Kakeya.realRpowENN rho.1 coarseSourceLoss ≤
              Kakeya.realRpowENN rho.1
                routing.critical.structuralLoss := by
          apply pure_wz2_rpowENN_antitone
            produced.metricCertificate.rho_pos rho.2.2
          exact scalar.structural_to_final
        have dense :=
          rich.finalCoarseOrdinaryTrace_dense_of_selectedIncidence
            routing.critical incidenceScalar.overlap
            (deltaIncidence.trans incidenceScalar.delta₀_le_overlap)
            rhoUpper rhoSmall ratioSmall
            (by
              simpa [three.workingEta_eq] using
                incidenceScalar.reduced_coarse_density
                  deltaPos deltaIncidence
                  produced.metricCertificate.rho_pos rhoUpper)
        rw [Kakeya.Streamlined.Shading.IsLambdaDense] at dense ⊢
        calc
          Kakeya.realRpowENN rho.1 coarseSourceLoss *
                rich.outputCertificate.coarse.family.toBodyFamily.mass ≤
              Kakeya.realRpowENN rho.1
                  routing.critical.structuralLoss *
                rich.outputCertificate.coarse.family.toBodyFamily.mass := by
            gcongr
          _ ≤
              rich.outputCertificate.finalCoarseOrdinaryTrace.mass :=
            dense
      volume_upper := by
        calc
          volume
              rich.outputCertificate.finalCoarseOrdinaryTrace.union ≤
            volume rich.outputCertificate.coarseShading.union :=
              measure_mono
                rich.outputCertificate.finalCoarseOrdinaryTrace_union_subset
          _ ≤
              Kakeya.realRpowENN rho.1 (sigma - coarseSourceLoss) := by
            have assembledVolume :=
              assembled.coarse_extremal.volume_upper
            change
              volume rich.outputCertificate.coarseShading.union ≤
                Kakeya.realRpowENN rho.1
                  (sigma -
                    routing.numerics.hierarchy.finalStrongLoss)
              at assembledVolume
            simpa [coarseSourceLoss] using assembledVolume
    }
  have ordinaryAxialWindow :
      ∀ parent point,
        point ∈
            rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent →
          |point (2 : Fin 3)| ≤ 1 / 4 :=
    rich.finalCoarseOrdinaryTrace_axial_window
      rootAxialWindow rhoSmall
  have finalLeNormalization :
      coarseSourceLoss ≤ coarseNormalizationLoss := by
    dsimp only [coarseNormalizationLoss]
    nlinarith [routing.numerics.hierarchy.finalStrongLoss_pos]
  have topNormalization :
      WZ2PaperConvexWolffBound
        rich.outputCertificate.coarse.family
        (Kakeya.realRpowENN rho.1 (-coarseNormalizationLoss)) := by
    exact
      recoverCoarseTopCWA
        rho.1 produced.metricCertificate.rho_pos rhoTopScale
        rich.outputCertificate.coarse.family
        assembled.coarse_extremal.cwa_nearby_scales
        (rich.finalCoarse_fullOrdinaryCarrier_subset_paper
          rhoSmall)
  let croppedExtremal :=
    assembled.coarse_extremal.mono_loss finalLeNormalization
  exact
    rich.exactCoarseReentryData
      (by rfl) ratioSmall rhoSmall lambda lambdaPos densityScalar
      coarseSourceLoss coarseNormalizationLoss
      routing.numerics.hierarchy.finalStrongLoss_pos
      (by
        dsimp only [coarseNormalizationLoss, coarseSourceLoss]
        nlinarith [routing.numerics.hierarchy.finalStrongLoss_pos])
      (by
        dsimp only [coarseNormalizationLoss, coarseSourceLoss]
        nlinarith [routing.numerics.hierarchy.finalStrongLoss_pos])
      densityBudget ordinaryExtremal ordinaryAxialWindow
      topNormalization croppedExtremal

/-- Forget the optional first-call coarse certificate and retain the reusable kernel. -/
theorem pureWZ2_prop_sticky_reentry_v4_exact_source
    (hFixedGrid : FixedGridBoundaryRemovalStatement)
    (hTreeCleanup : OnePassTreeCleanupStatement)
    (sigma : ℝ)
    (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ)
    (outputLossPos : 0 < outputLoss)
    (outputLossLeOne : outputLoss ≤ 1) :
    ∃ normalizationLoss delta₀ : ℝ,
      0 < pureWZ2CompleteNormalizationFinalLoss normalizationLoss ∧
      0 < normalizationLoss ∧
      pureWZ2CompleteNormalizationFinalLoss normalizationLoss ≤
        normalizationLoss / 2 ∧
      normalizationLoss < outputLoss ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ (croppedFamily :
            Kakeya.Streamlined.TubeFamily delta),
          ∀ (croppedShading : WZ1PaperTubeShading croppedFamily),
            ∀ _reentry :
                PureWZ2PropStickyReentryData
                  (sigma := sigma)
                  croppedShading 0
                  (pureWZ2CompleteNormalizationFinalLoss
                    normalizationLoss)
                  normalizationLoss,
              ∀ rho : WZ2PaperRequestedScale delta,
                Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                rho.1 ≤ Real.rpow delta outputLoss →
                  Nonempty
                    (PureWZ2PropStickyData
                      (sigma := sigma)
                      (outputLoss := outputLoss)
                      croppedShading rho 61) := by
  rcases
      pureWZ2_prop_sticky_reentry_v4_core_exact_source
        hFixedGrid hTreeCleanup sigma critical
        outputLoss outputLossPos outputLossLeOne
    with
    ⟨normalizationLoss, delta₀, sourceLossPos,
      normalizationLossPos, sourceLossLeHalf,
      normalizationLossLt, delta₀Pos, delta₀LeOne, produce⟩
  refine
    ⟨normalizationLoss, delta₀, sourceLossPos,
      normalizationLossPos, sourceLossLeHalf,
      normalizationLossLt, delta₀Pos, delta₀LeOne, ?_⟩
  intro delta deltaPos deltaLe croppedFamily croppedShading _reentry
    rho rhoLower rhoUpper
  rcases
      produce delta deltaPos deltaLe
        croppedFamily croppedShading _reentry rho rhoLower rhoUpper
    with ⟨core⟩
  exact ⟨core.data⟩

/--
Close the fixed-grid and tree-cleanup inputs and expose the reusable V4
kernel as one public Node 3 capability.
-/
theorem pureWZ2_prop_sticky_reentry_kernel_v4
    (hFixedGrid : FixedGridBoundaryRemovalStatement)
    (hTreeCleanup : OnePassTreeCleanupStatement) :
    PureWZ2PropStickyReentryKernelAt 0 61 := by
  intro sigma critical outputLoss outputLossPos outputLossLeOne
  rcases
      pureWZ2_prop_sticky_reentry_v4_core_exact_source
        hFixedGrid hTreeCleanup sigma critical
        outputLoss outputLossPos outputLossLeOne
    with
    ⟨normalizationLoss, delta₀, sourceLossPos,
      normalizationLossPos, sourceLossLeHalf,
      normalizationLossLt, delta₀Pos, delta₀LeOne, produce⟩
  exact
    ⟨{
      sourceLoss :=
        pureWZ2CompleteNormalizationFinalLoss normalizationLoss
      normalizationLoss := normalizationLoss
      delta₀ := delta₀
      sourceLoss_pos := sourceLossPos
      normalizationLoss_pos := normalizationLossPos
      sourceLoss_le_half := sourceLossLeHalf
      normalizationLoss_lt_output := normalizationLossLt
      delta₀_pos := delta₀Pos
      delta₀_le_one := delta₀LeOne
      run := by
        intro delta deltaPos deltaLe croppedFamily croppedShading reentry
          rho rhoLower rhoUpper
        rcases
            produce delta deltaPos deltaLe
              croppedFamily croppedShading reentry rho rhoLower rhoUpper
          with ⟨core⟩
        exact ⟨core.data⟩
      runReentrant := by
        intro delta deltaPos deltaLe croppedFamily croppedShading reentry
          rootAxialWindow rho rhoLower rhoUpper
        rcases
            produce delta deltaPos deltaLe
              croppedFamily croppedShading reentry rho rhoLower rhoUpper
          with ⟨core⟩
        exact ⟨core.toReentrantSameLoss rootAxialWindow⟩
    }⟩

/--
The nonvacuous V4 continuation with its source loss exposed as the exact
public output loss of complete-fiber normalization.
-/
private theorem pureWZ2_cropped_prop_sticky_v4_exact_source_legacy
    (hFixedGrid : FixedGridBoundaryRemovalStatement)
    (hTreeCleanup : OnePassTreeCleanupStatement)
    (sigma : ℝ)
    (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ)
    (outputLossPos : 0 < outputLoss)
    (outputLossLeOne : outputLoss ≤ 1) :
    ∃ normalizationLoss delta₀ : ℝ,
      0 < pureWZ2CompleteNormalizationFinalLoss normalizationLoss ∧
      0 < normalizationLoss ∧
      pureWZ2CompleteNormalizationFinalLoss normalizationLoss ≤
        normalizationLoss / 2 ∧
      normalizationLoss < outputLoss ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ source :
            PureWZ2ExtremalConfiguration
              sigma
              (pureWZ2CompleteNormalizationFinalLoss normalizationLoss)
              delta,
          ∀ normalized :
              PureWZ2CroppedCriticalNormalizationData
                (outputLoss := normalizationLoss)
                source 0,
            ∀ rho : WZ2PaperRequestedScale delta,
              Real.rpow delta (1 - outputLoss) ≤ rho.1 →
              rho.1 ≤ Real.rpow delta outputLoss →
                Nonempty
                  (PureWZ2PropStickyData
                    (sigma := sigma)
                    (outputLoss := outputLoss)
                    normalized.croppedRefined rho 61) := by
  rcases
      pureWZ2_prop_sticky_reentry_v4_exact_source
        hFixedGrid hTreeCleanup sigma critical
        outputLoss outputLossPos outputLossLeOne
    with
    ⟨normalizationLoss, delta₀, sourceLossPos,
      normalizationLossPos, sourceLossLeHalf,
      normalizationLossLt, delta₀Pos, delta₀LeOne, produce⟩
  refine
    ⟨normalizationLoss, delta₀, sourceLossPos,
      normalizationLossPos, sourceLossLeHalf,
      normalizationLossLt, delta₀Pos, delta₀LeOne, ?_⟩
  intro delta deltaPos deltaLe source normalized rho rhoLower rhoUpper
  let reentry :=
    normalized.toPropStickyReentryData
      sourceLossPos normalizationLossPos
  exact
    produce delta deltaPos deltaLe
      normalized.croppedFamily normalized.croppedRefined
      reentry rho rhoLower rhoUpper

/--
Compatibility form of the exact-source continuation, derived from the
re-entry kernel.  The supplied normalization is projected to re-entry data
without changing its exact cropped pair.
-/
theorem pureWZ2_cropped_prop_sticky_v4_exact_source
    (hFixedGrid : FixedGridBoundaryRemovalStatement)
    (hTreeCleanup : OnePassTreeCleanupStatement)
    (sigma : ℝ)
    (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ)
    (outputLossPos : 0 < outputLoss)
    (outputLossLeOne : outputLoss ≤ 1) :
    ∃ normalizationLoss delta₀ : ℝ,
      0 < pureWZ2CompleteNormalizationFinalLoss normalizationLoss ∧
      0 < normalizationLoss ∧
      pureWZ2CompleteNormalizationFinalLoss normalizationLoss ≤
        normalizationLoss / 2 ∧
      normalizationLoss < outputLoss ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ source :
            PureWZ2ExtremalConfiguration
              sigma
              (pureWZ2CompleteNormalizationFinalLoss normalizationLoss)
              delta,
          ∀ normalized :
              PureWZ2CroppedCriticalNormalizationData
                (outputLoss := normalizationLoss)
                source 0,
            ∀ rho : WZ2PaperRequestedScale delta,
              Real.rpow delta (1 - outputLoss) ≤ rho.1 →
              rho.1 ≤ Real.rpow delta outputLoss →
                Nonempty
                  (PureWZ2PropStickyData
                    (sigma := sigma)
                    (outputLoss := outputLoss)
                    normalized.croppedRefined rho 61) := by
  rcases
      pureWZ2_prop_sticky_reentry_v4_exact_source
        hFixedGrid hTreeCleanup sigma critical
        outputLoss outputLossPos outputLossLeOne
    with
    ⟨normalizationLoss, delta₀, sourceLossPos,
      normalizationLossPos, sourceLossLeHalf,
      normalizationLossLt, delta₀Pos, delta₀LeOne, produce⟩
  refine
    ⟨normalizationLoss, delta₀, sourceLossPos,
      normalizationLossPos, sourceLossLeHalf,
      normalizationLossLt, delta₀Pos, delta₀LeOne, ?_⟩
  intro delta deltaPos deltaLe source normalized rho rhoLower rhoUpper
  let reentry :=
    normalized.toPropStickyReentryData
      sourceLossPos normalizationLossPos
  exact
    produce delta deltaPos deltaLe
      normalized.croppedFamily normalized.croppedRefined
      reentry rho rhoLower rhoUpper

/--
The corrected V4 chain proves the universal cropped conclusion at
normalization exponent zero and logarithmic loss `61`.
-/
theorem pureWZ2_cropped_prop_sticky_v4
    (hFixedGrid : FixedGridBoundaryRemovalStatement)
    (hTreeCleanup : OnePassTreeCleanupStatement) :
    PureWZ2CroppedPropStickyAt 0 61 := by
  intro sigma critical outputLoss outputLossPos
  by_cases outputLossLeOne : outputLoss ≤ 1
  · rcases
        pureWZ2_cropped_prop_sticky_v4_exact_source
          hFixedGrid hTreeCleanup sigma critical
          outputLoss outputLossPos outputLossLeOne
      with
      ⟨normalizationLoss, delta₀,
        sourceLossPos, normalizationLossPos, sourceLossLeHalf,
        normalizationLossLt, delta₀Pos, delta₀One, produce⟩
    exact
      ⟨pureWZ2CompleteNormalizationFinalLoss normalizationLoss,
        normalizationLoss, delta₀,
        sourceLossPos, normalizationLossPos, sourceLossLeHalf,
        normalizationLossLt, delta₀Pos, delta₀One, produce⟩
  · have outputLossLarge : 1 < outputLoss :=
      lt_of_not_ge outputLossLeOne
    refine
      ⟨outputLoss / 4, outputLoss / 2, 1 / 2,
        by positivity, by positivity, by
          nlinarith,
        by linarith, by norm_num, by norm_num, ?_⟩
    intro delta deltaPos deltaLe _source _normalized rho rhoLower rhoUpper
    have deltaLtOne : delta < 1 :=
      deltaLe.trans_lt (by norm_num)
    have lowerOne :
        1 ≤ Real.rpow delta (1 - outputLoss) := by
      have bound :=
        Real.rpow_le_rpow_of_exponent_ge
          deltaPos deltaLtOne.le
          (by linarith : 1 - outputLoss ≤ 0)
      simpa using bound
    have lowerEqOne :
        Real.rpow delta (1 - outputLoss) = 1 :=
      le_antisymm (rhoLower.trans rho.2.2) lowerOne
    have upperLtOne :
        Real.rpow delta outputLoss < 1 :=
      Real.rpow_lt_one deltaPos.le deltaLtOne outputLossPos
    have oneLeUpper : 1 ≤ Real.rpow delta outputLoss := by
      calc
        1 = Real.rpow delta (1 - outputLoss) := lowerEqOne.symm
        _ ≤ rho.1 := rhoLower
        _ ≤ Real.rpow delta outputLoss := rhoUpper
    exact (not_le_of_gt upperLtOne oneLeUpper).elim

end Kakeya.Assouad.Prop62PaperAudit.V4

end
