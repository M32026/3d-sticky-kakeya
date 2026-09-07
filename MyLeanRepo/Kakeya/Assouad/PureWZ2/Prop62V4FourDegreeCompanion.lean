import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4FourDegreeOutputAdapter

/-!
# Proposition 6.2 V4 four-degree companion

The frozen V4 packet-core output deliberately exposes only the public
four-degree conclusions.  This module packages that output together with the
canonical producer from which it was obtained, so downstream code can use the
dependent terminal objects without trying to recover them from an arbitrary
public witness.

The receipt stops at the genuine Target-4 boundary.  In particular, it does
not include a partitioning cover, a critical-floor selection, or terminal
absorption data, none of which is produced by the canonical four-degree
construction.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Canonical provenance for one frozen V4 four-degree output.

The equality records that the public output is the projection of this exact
producer, rather than an independently chosen witness of the frozen
existential statement.
-/
structure Prop62V4FourDegreeCanonicalReceipt
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {eta : ℝ}
    {packetDensityExponent cwaLossExponent : ℕ}
    (hdelta : 0 < delta)
    (metric :
      MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
          parentConstant fiberConstant)
    (output :
      FourDegreePacketCoreData
        (eta := eta)
        (packetDensityExponent := packetDensityExponent)
        hdelta metric
        (Kakeya.realRpowENN delta
          (-(cwaLossExponent : ℝ) * eta))
        (Kakeya.realRpowENN delta
          (-(cwaLossExponent : ℝ) * eta))) where
  localInput : MetricParentsV4PacketCellLocalInput metric
  ambientConstant : ENNReal
  scaleWindow : ENNReal
  schedule :
    PureWZ2Prop62LaminarPureSchedule
      metric.scaleData.coarse ambientConstant scaleWindow
  producer :
    localInput.toPacketCellInput.CanonicalFourDegreeProducerData
      (schedule := schedule) fiberConstant
      (Kakeya.realRpowENN delta
        ((packetDensityExponent : ℝ) * eta))
  parentConstant_le :
    producer.output.output.parentConstant ≤
      Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta)
  fiberConstant_le :
    fiberConstant ≤
      Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta)
  output_eq :
    output =
      localInput.fourDegreePacketCoreData_of_canonicalProducer
        schedule producer cwaLossExponent
          parentConstant_le fiberConstant_le

/--
The public Target-4 output, its regularity bound, and its exact canonical
provenance.
-/
structure Prop62V4FourDegreeCompanionData
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {eta : ℝ}
    {packetDensityExponent cwaLossExponent polylogExponent : ℕ}
    (hdelta : 0 < delta)
    (metric :
      MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
          parentConstant fiberConstant) where
  output :
    FourDegreePacketCoreData
      (eta := eta)
      (packetDensityExponent := packetDensityExponent)
      hdelta metric
      (Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta))
      (Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta))
  regularity_bound :
    (output.regularity : ENNReal) ≤
      logarithmicLoss delta ^ polylogExponent
  receipt :
    Prop62V4FourDegreeCanonicalReceipt
      hdelta metric output

/--
Project one canonical producer simultaneously to the frozen public output and
to the dependent receipt retained for the tail.
-/
noncomputable def prop62V4FourDegreeCompanion_ofCanonicalProducer
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {eta : ℝ}
    {packetDensityExponent cwaLossExponent polylogExponent : ℕ}
    {metric :
      MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
          parentConstant fiberConstant}
    (localInput : MetricParentsV4PacketCellLocalInput metric)
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        metric.scaleData.coarse ambientConstant scaleWindow)
    (producer :
      localInput.toPacketCellInput.CanonicalFourDegreeProducerData
        (schedule := schedule) fiberConstant
        (Kakeya.realRpowENN delta
          ((packetDensityExponent : ℝ) * eta)))
    (parentConstantLe :
      producer.output.output.parentConstant ≤
        Kakeya.realRpowENN delta
          (-(cwaLossExponent : ℝ) * eta))
    (fiberConstantLe :
      fiberConstant ≤
        Kakeya.realRpowENN delta
          (-(cwaLossExponent : ℝ) * eta))
    (regularityBound :
      (producer.output.output.coarseLoss : ENNReal) ≤
        logarithmicLoss delta ^ polylogExponent) :
    Prop62V4FourDegreeCompanionData
      (eta := eta)
      (packetDensityExponent := packetDensityExponent)
      (cwaLossExponent := cwaLossExponent)
      (polylogExponent := polylogExponent)
      localInput.delta_pos metric := by
  let output :=
    localInput.fourDegreePacketCoreData_of_canonicalProducer
      schedule producer cwaLossExponent parentConstantLe fiberConstantLe
  refine
    {
      output := output
      regularity_bound := ?_
      receipt := {
        localInput := localInput
        ambientConstant := ambientConstant
        scaleWindow := scaleWindow
        schedule := schedule
        producer := producer
        parentConstant_le := parentConstantLe
        fiberConstant_le := fiberConstantLe
        output_eq := rfl
      }
    }
  change
    (producer.output.output.coarseLoss : ENNReal) ≤
      logarithmicLoss delta ^ polylogExponent
  exact regularityBound

end Kakeya.Assouad.Prop62PaperAudit.V4

end
