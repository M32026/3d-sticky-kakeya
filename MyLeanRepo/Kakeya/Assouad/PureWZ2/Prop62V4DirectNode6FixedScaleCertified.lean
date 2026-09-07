import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4DirectNode6FixedScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4FineUnionCriticalLower

/-!
# Certified direct Proposition 6.2 fixed-scale provider for Node 6

This file leaves the original arbitrary-`rho` bare provider unchanged and adds
the smallest certified wrapper that exposes a public balanced-cell critical
floor.  The floor is consumable exactly at the paper's square-root scale; the
provider itself still runs at arbitrary requested `rho`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- A Node-6 fixed-scale output together with the public critical balanced-cell
floor that becomes available at the square-root scale. -/
structure PureWZ2Node6FixedScaleCriticalOutput
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading source)
    (rho : WZ2PaperRequestedScale delta)
    (logExponent : ℕ) where
  fixed :
    PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent
  balanced_cellMass_critical_lower_at_sqrt :
    rho.1 = Real.sqrt delta →
      Kakeya.realRpowENN delta
          (3 / 2 + sigma / 2 + outputLoss) ≤
        fixed.balanced.cellMass

/-- Certified fixed-scale provider at one fixed logarithmic exponent. -/
def PureWZ2Node6FixedScaleCriticalAt (logExponent : ℕ) : Prop :=
  ∀ sigma : ℝ,
    ∀ critical : PureWZ2CriticalPackage sigma,
      ∀ outputLoss : ℝ, 0 < outputLoss → outputLoss ≤ 1 →
        ∃ inputLoss delta₀ : ℝ,
          0 < inputLoss ∧
          inputLoss ≤ outputLoss ∧
          0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta,
              ∀ rho : WZ2PaperRequestedScale delta,
                Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                rho.1 ≤ Real.rpow delta outputLoss →
                  Nonempty
                    (PureWZ2Node6FixedScaleCriticalOutput
                      (sigma := sigma) (outputLoss := outputLoss)
                      cfg.shading rho logExponent)

/-- Existential wrapper for the certified fixed-scale Node-6 provider. -/
def PureWZ2Node6FixedScaleCriticalStatement : Prop :=
  ∃ logExponent : ℕ, PureWZ2Node6FixedScaleCriticalAt logExponent

namespace PureWZ2Node6FixedScaleCriticalOutput

/-- Forget the certified cell-mass floor and keep the original bare output. -/
def toFixed
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data :
      PureWZ2Node6FixedScaleCriticalOutput
        (sigma := sigma) (outputLoss := outputLoss)
        sourceShading rho logExponent) :
    PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent :=
  data.fixed

end PureWZ2Node6FixedScaleCriticalOutput

/-- Forgetting the certified floor recovers the original fixed-scale provider
interface at the same logarithmic exponent. -/
theorem PureWZ2Node6FixedScaleCriticalAt.toFixedScaleAt
    {logExponent : ℕ}
    (h :
      PureWZ2Node6FixedScaleCriticalAt logExponent) :
    PureWZ2Node6FixedScaleAt logExponent := by
  intro sigma critical outputLoss houtputLoss houtputLossOne
  rcases h sigma critical outputLoss houtputLoss houtputLossOne with
    ⟨inputLoss, delta₀, inputLossPos, inputLossLeOutput,
      delta₀Pos, delta₀LeOne, produce⟩
  refine ⟨inputLoss, delta₀, inputLossPos, inputLossLeOutput,
    delta₀Pos, delta₀LeOne, ?_⟩
  intro delta hdelta hdeltaLe cfg rho rhoLower rhoUpper
  rcases produce delta hdelta hdeltaLe cfg rho rhoLower rhoUpper with
    ⟨certified⟩
  exact ⟨certified.fixed⟩

/-- Forgetting the certified floor recovers the original bare statement. -/
theorem PureWZ2Node6FixedScaleCriticalStatement.toFixedScaleStatement
    (h : PureWZ2Node6FixedScaleCriticalStatement) :
    PureWZ2Node6FixedScaleStatement := by
  rcases h with ⟨logExponent, hlog⟩
  exact ⟨logExponent, hlog.toFixedScaleAt⟩

end Kakeya.Assouad

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open MeasureTheory
open Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace Prop62V4DirectNode6FixedScaleCertified

/-- Certified arbitrary-`rho` fixed-scale provider.  The public critical cell
mass floor is exposed as a square-root-scale receipt on the returned output. -/
theorem provider
    {sigma outputLoss : ℝ}
    (criticalPackage : PureWZ2CriticalPackage sigma)
    (outputLossPos : 0 < outputLoss)
    (outputLossLeOne : outputLoss ≤ 1) :
    ∃ inputLoss delta₀ : ℝ,
      0 < inputLoss ∧
      inputLoss ≤ outputLoss ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta,
          ∀ rho : WZ2PaperRequestedScale delta,
            Real.rpow delta (1 - outputLoss) ≤ rho.1 →
            rho.1 ≤ Real.rpow delta outputLoss →
              Nonempty
                (PureWZ2Node6FixedScaleCriticalOutput
                  (sigma := sigma) (outputLoss := outputLoss)
                  cfg.shading rho 61) := by
  rcases
      Kakeya.Assouad.Prop62PaperAudit.V4.PureWZ2CriticalPackage.prop62V4_pure_scalar_routing
        criticalPackage
        10 8 2 51 outputLossPos outputLossLeOne
    with ⟨scalarRouting⟩
  let routing := scalarRouting.routing
  let scalar := scalarRouting.scalar
  let inputLoss := routing.numerics.hierarchy.sourceLoss
  rcases Prop62V4DirectNode6FixedScale.provider
      (sigma := sigma) (outputLoss := outputLoss)
      criticalPackage outputLossPos outputLossLeOne
    with
    ⟨bareInputLoss, bareDelta₀, bareInputLossPos, bareInputLossLeOutput,
      bareDelta₀Pos, bareDelta₀LeOne, _bareProvider⟩
  rcases prop62V4_direct_cropped_producer
      (sigma := sigma)
      (outputLoss := outputLoss)
      (sourceLoss := routing.numerics.hierarchy.sourceLoss)
      (workingEta := routing.numerics.hierarchy.stableLoss)
      routing.numerics.hierarchy.sourceLoss_pos outputLossPos
      (by
        rw [routing.numerics.hierarchy.sourceLoss_eq]
        dsimp only [wz2PaperFinalSourceLoss]
        have structuralLe :
            routing.critical.structuralLoss ≤ outputLoss ^ 2 / 1000 :=
          routing.critical.structuralLoss_le.trans (min_le_left _ _)
        have structuralLeOne : routing.critical.structuralLoss ≤ 1 := by
          have structuralLeOutput :
              routing.critical.structuralLoss ≤ outputLoss := by
            calc
              routing.critical.structuralLoss ≤ outputLoss ^ 2 / 1000 :=
                structuralLe
              _ ≤ outputLoss := by nlinarith
          exact structuralLeOutput.trans outputLossLeOne
        have structuralSqLe :
            routing.critical.structuralLoss ^ 2 ≤
              routing.critical.structuralLoss := by
          nlinarith [routing.critical.structuralLoss_pos]
        nlinarith)
      routing.numerics.hierarchy.source_stable
      (routing.numerics.hierarchy.sourceLoss_pos.trans
        routing.numerics.hierarchy.source_stable)
      scalar.metric_loss scalar.packet_loss
      fixed_grid_boundary_removal one_pass_tree_cleanup
    with ⟨producerReceipt⟩
  let delta₀ := min scalar.delta₀ producerReceipt.delta₀
  refine ⟨inputLoss, delta₀,
    routing.numerics.hierarchy.sourceLoss_pos, ?_, ?_, ?_, ?_⟩
  · have sourceLeFinal :
        routing.numerics.hierarchy.sourceLoss ≤
          routing.numerics.hierarchy.finalStrongLoss := by
      rw [routing.numerics.hierarchy.sourceLoss_eq,
        routing.numerics.hierarchy.finalStrongLoss_eq]
      dsimp only [wz2PaperFinalSourceLoss, wz2PaperFinalStrongLoss]
      have structuralLe :
          routing.critical.structuralLoss ≤ outputLoss ^ 2 / 1000 :=
        routing.critical.structuralLoss_le.trans (min_le_left _ _)
      have structuralLeOutput :
          routing.critical.structuralLoss ≤ outputLoss := by
        calc
          routing.critical.structuralLoss ≤ outputLoss ^ 2 / 1000 := structuralLe
          _ ≤ outputLoss := by nlinarith
      have structuralLeOne : routing.critical.structuralLoss ≤ 1 :=
        structuralLeOutput.trans outputLossLeOne
      have structuralSqLe :
          routing.critical.structuralLoss ^ 2 ≤
            routing.critical.structuralLoss := by
        nlinarith [routing.critical.structuralLoss_pos]
      nlinarith
    exact sourceLeFinal.trans <| by
      nlinarith [routing.numerics.hierarchy.final_output_budget]
  · exact lt_min scalar.delta₀_pos producerReceipt.delta₀_pos
  · exact (min_le_left _ _).trans <|
      scalar.delta₀_le_one_hundred.trans (by norm_num)
  · intro delta hdelta hdeltaLe cfg rho rhoLower rhoUpper
    have deltaScalar : delta ≤ scalar.delta₀ :=
      hdeltaLe.trans (min_le_left _ _)
    have deltaProducer : delta ≤ producerReceipt.delta₀ :=
      hdeltaLe.trans (min_le_right _ _)
    rcases producerReceipt.produce hdelta deltaProducer cfg rho
        rhoLower rhoUpper with ⟨produced⟩
    let internal :=
      Prop62V4DirectNode6FixedScale.assemble
        (routing := routing) scalar cfg rho hdelta produced
        deltaScalar outputLossLeOne rhoLower rhoUpper
    have finalLeOutput :
        routing.numerics.hierarchy.finalStrongLoss ≤ outputLoss := by
      have := routing.numerics.hierarchy.final_output_budget
      nlinarith [routing.numerics.hierarchy.finalStrongLoss_pos]
    let fixed := internal.mono_loss hdelta finalLeOutput
    refine ⟨{
      fixed := fixed
      balanced_cellMass_critical_lower_at_sqrt := ?_
    }⟩
    intro hrho
    let parent :
        Fin produced.rich.outputCertificate.coarse.family.card :=
      produced.rich.outputCertificate.cover.toWZ1PaperTubeCover.parent
        ⟨0, produced.rich.outputCertificate.refined_nonempty⟩
    have deltaLeOne : delta ≤ 1 := by
      exact deltaScalar.trans <| scalar.delta₀_le_one_hundred.trans (by norm_num)
    have publicPowerLe :
        Kakeya.realRpowENN delta
            (3 / 2 + sigma / 2 + outputLoss) ≤
          Kakeya.realRpowENN delta
            (3 / 2 + sigma / 2 +
              routing.numerics.hierarchy.finalStrongLoss) := by
      exact pure_wz2_rpowENN_antitone hdelta deltaLeOne <| by
        nlinarith [finalLeOutput]
    have internalFloor :
        Kakeya.realRpowENN delta
            (3 / 2 + sigma / 2 +
              routing.numerics.hierarchy.finalStrongLoss) ≤
          internal.balanced.cellMass := by
      have rawFloor :
          Kakeya.realRpowENN delta
              (3 / 2 + sigma / 2 +
                routing.numerics.hierarchy.finalStrongLoss) ≤
            produced.rich.outputCertificate.balanced.cellMass := by
        exact
          Prop62V4DirectCroppedProducerData.balanced_cellMass_critical_lower_at_sqrt
            (routing := routing) (scalar := scalar)
            (cfg := cfg) (rho := rho) (hdelta := hdelta) (produced := produced)
            deltaScalar rhoLower rhoUpper hrho parent
      change
        Kakeya.realRpowENN delta
            (3 / 2 + sigma / 2 +
              routing.numerics.hierarchy.finalStrongLoss) ≤
          produced.rich.outputCertificate.balanced.cellMass
      exact rawFloor
    calc
      Kakeya.realRpowENN delta
            (3 / 2 + sigma / 2 + outputLoss) ≤
          Kakeya.realRpowENN delta
            (3 / 2 + sigma / 2 +
              routing.numerics.hierarchy.finalStrongLoss) :=
        publicPowerLe
      _ ≤ internal.balanced.cellMass := internalFloor
      _ = fixed.balanced.cellMass := rfl

/-- Certified direct fixed-scale statement at log exponent `61`. -/
theorem fixedScaleStatement :
    PureWZ2Node6FixedScaleCriticalStatement := by
  refine ⟨61, ?_⟩
  intro sigma critical outputLoss houtputLoss houtputLossOne
  exact provider critical houtputLoss houtputLossOne

/-- The certified statement projects back to the original bare statement. -/
theorem fixedScaleStatement_to_bare :
    PureWZ2Node6FixedScaleStatement := by
  exact PureWZ2Node6FixedScaleCriticalStatement.toFixedScaleStatement
    fixedScaleStatement

end Prop62V4DirectNode6FixedScaleCertified

end Kakeya.Assouad.Prop62PaperAudit.V4

end
