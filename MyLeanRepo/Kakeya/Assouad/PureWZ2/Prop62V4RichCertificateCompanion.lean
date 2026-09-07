import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4Certificate
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4FourDegreeCompanion

/-!
# Proposition 6.2 V4 rich-certificate companion

The public V4 records intentionally forget the ordinary Definition-2.12
receipts.  This module keeps the original metric-parent certificate and
derives the Target-3 implementation record, the Target-4 pure certificate,
and the public Target-4 output from one chain of witnesses.

No coarse family, terminal fiber, balancing sample, or rescaling certificate
is selected a second time.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62MetricParentsV4Certificate

/-- Deterministic projection of the rich metric-parent certificate to the
ordinary V4 implementation record. -/
noncomputable def toMetricData
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (certificate :
      PureWZ2Prop62MetricParentsV4Certificate
        shading rho fineParentDistanceConstant
          parentConstant fiberConstant) :
    Prop62PaperAudit.V4.MetricParentsAtPrescribedScaleData
      shading rho fineParentDistanceConstant
        parentConstant fiberConstant := by
  rcases certificate with
    ⟨rhoPos, distanceConstantPos, refinement, fine, fineEq,
      refinedNonempty, refinedCubical, coarse, _coarseCentered, section6Cover,
      cover, coverEq, fullFiberUniform, coarseCWA,
      _coarseStronglySeparated, sourceFiberConstant,
      fiberConstantEq, fiberRescaling, fiberPublicCWA,
      metricFiber, fineParentClose⟩
  subst fine
  let scaleData :
      Prop62PaperAudit.V4.MetricParentScaleData
        refinement.selected.family rho rhoPos
          parentConstant fiberConstant :=
    {
      coarse := coarse
      section6Cover := section6Cover
      cover := cover
      cover_eq := coverEq
      full_fiber_uniform := fullFiberUniform
      coarse_cwa := coarseCWA
      rescaledFiber := fun parent =>
        ⟨{
          sourceConstant := sourceFiberConstant
          rescalingInput := fiberRescaling parent
          familyData := (fiberRescaling parent).literal
          familyData_eq := rfl
          rescalingCertificate := (fiberRescaling parent).certificate
          rescalingCertificate_eq := HEq.rfl
          constant_eq := fiberConstantEq
          cwa := fiberPublicCWA parent
        }⟩
    }
  exact
    {
      rho_pos := rhoPos
      fine_parent_distance_constant_pos := distanceConstantPos
      refinement := refinement
      refined_nonempty := refinedNonempty
      refined_cubical := refinedCubical
      scaleData := scaleData
      metric_fiber := metricFiber
      fine_parent_close := fineParentClose
    }

end PureWZ2Prop62MetricParentsV4Certificate

namespace Prop62PaperAudit.V4

/-- The Target-3 implementation record together with the richer certificate
from which it is deterministically projected. -/
structure Prop62V4MetricParentsRichCompanionData
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (fineParentDistanceConstant : ℝ)
    (parentConstant fiberConstant : ENNReal) where
  certificate :
    PureWZ2Prop62MetricParentsV4Certificate
      shading rho fineParentDistanceConstant
        parentConstant fiberConstant

namespace Prop62V4MetricParentsRichCompanionData

variable
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (companion :
      Prop62V4MetricParentsRichCompanionData
        shading rho fineParentDistanceConstant
          parentConstant fiberConstant)

/-- The ordinary Target-3 record, with no existential re-selection. -/
noncomputable def metric :
    MetricParentsAtPrescribedScaleData
      shading rho fineParentDistanceConstant
        parentConstant fiberConstant :=
  companion.certificate.toMetricData

/-- The retained pure nearby-scale CWA of the exact Target-3 coarse family. -/
theorem coarse_pure_cwa :
    WZ2PaperPureCWAAtNearbyScales
      companion.certificate.coarse parentConstant :=
  companion.certificate.coarse_cwa

/-- The exact public rescaling certificate attached to one complete Target-3
fiber. -/
noncomputable def fiber_rescaling_certificate
    (parent : Fin companion.certificate.coarse.card) :
    WZ2PaperAssouadToLiteralRescalingCertificate
      (companion.certificate.fiber_rescaling parent).rho_pos
      (WZ2PaperAssouadUnitRescalingData.ofTube
        (companion.certificate.coarse.tube parent)
        (companion.certificate.fiber_rescaling parent).rho_pos)
      (companion.certificate.fiber_rescaling parent).literal
      4000000 :=
  (companion.certificate.fiber_rescaling parent).certificate

/-- The retained pure nearby-scale CWA of the exact public family attached to
one complete Target-3 fiber. -/
theorem fiber_pure_cwa
    (parent : Fin companion.certificate.coarse.card) :
    WZ2PaperPureCWAAtNearbyScales
      (companion.fiber_rescaling_certificate parent).publicFamily
      fiberConstant :=
  companion.certificate.fiber_public_cwa parent

end Prop62V4MetricParentsRichCompanionData

/--
One rich Target-3 certificate together with the exact canonical producer used
for Target 4.  The Target-4 pure certificate and public packet-core output are
derived definitions below, so this record cannot pair unrelated witnesses.
-/
structure Prop62V4RichCertificateCompanionData
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {eta : ℝ}
    {packetDensityExponent cwaLossExponent polylogExponent : ℕ}
    (hdelta : 0 < delta)
    (metricCompanion :
    Prop62V4MetricParentsRichCompanionData
      sourceShading rho fineParentDistanceConstant
        parentConstant fiberConstant) where
  fourDegree :
    Prop62V4FourDegreeCompanionData
      (eta := eta)
      (packetDensityExponent := packetDensityExponent)
      (cwaLossExponent := cwaLossExponent)
      (polylogExponent := polylogExponent)
      hdelta metricCompanion.metric

namespace Prop62V4RichCertificateCompanionData

variable
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {eta : ℝ}
    {packetDensityExponent cwaLossExponent polylogExponent : ℕ}
    {hdelta : 0 < delta}
    {metricCompanion :
      Prop62V4MetricParentsRichCompanionData
        sourceShading rho fineParentDistanceConstant
          parentConstant fiberConstant}
    (companion :
      Prop62V4RichCertificateCompanionData
        (eta := eta)
        (packetDensityExponent := packetDensityExponent)
        (cwaLossExponent := cwaLossExponent)
        (polylogExponent := polylogExponent)
        hdelta metricCompanion)

/-- The exact metric-local input retained by the canonical Target-4 receipt. -/
abbrev localInput :=
  companion.fourDegree.receipt.localInput

/-- The exact packet-cell input consumed by the canonical Target-4 producer. -/
abbrev packetInput :=
  companion.localInput.toPacketCellInput

/-- The exact schedule retained by the canonical Target-4 receipt. -/
abbrev schedule :=
  companion.fourDegree.receipt.schedule

/-- The canonical Target-4 producer retained by the rich companion. -/
abbrev producer :=
  companion.fourDegree.receipt.producer

/-- The exact fine-multiplicity choice in the canonical producer chain. -/
abbrev multiplicity :=
  companion.producer.initial.multiplicity

/-- The exact parent-class choice dependent on `multiplicity`. -/
abbrev parentClass :=
  companion.producer.initial.parentClass

/-- The exact tree-cleanup receipt dependent on the preceding choices. -/
abbrev treeCleanup :=
  companion.producer.initial.treeCleanup

/-- The exact packet-cell exactification dependent on the cleanup receipt. -/
abbrev exactification :=
  companion.producer.initial.exactification

/-- The exact reference-parent degree data in the canonical producer chain. -/
abbrev parentDegree :=
  companion.producer.initial.parentDegree

/-- The exact four-degree core in the canonical producer chain. -/
abbrev core :=
  companion.producer.core

/-- The exact good balancing sample selected by the canonical producer. -/
abbrev good :=
  companion.producer.output.good

/-- The exact terminal complete families selected by the canonical producer. -/
abbrev families :=
  companion.producer.families

/-- The exact internal four-degree output consumed by the final assembly. -/
abbrev canonicalOutput :=
  companion.producer.output.output

/-- Reindex the exact Target-3 fiber inputs onto the terminal Target-4
complete fibers. -/
noncomputable def terminalRescaling :
    companion.families.TerminalPublicRescalingData
      companion.packetInput
      companion.multiplicity
      companion.parentClass
      companion.treeCleanup
      companion.exactification
      companion.parentDegree
      companion.core
      rho.2.2 (fiberConstant / 81000000) where
  ambient ambientParent _parentMem := by
    let ambientFiber :=
      Classical.choice
        (metricCompanion.metric.scaleData.rescaledFiber ambientParent)
    exact
      (ambientFiber.weakenConstant le_rfl ambientFiber.cwa.2.1
        ).rescalingInput

/-- The exact pure terminal certificate derived from the same canonical
producer as the public Target-4 output. -/
noncomputable def outputCertificate :
    PureWZ2Prop62FourDegreeOutputCertificate
      companion.fourDegree.receipt.localInput.toPacketCellInput
      (Kakeya.realRpowENN delta
        ((packetDensityExponent : ℝ) * eta))
      (Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta))
      (fiberConstant / 81000000) :=
  companion.fourDegree.receipt.localInput.toPacketCellInput
    |>.fourDegreeOutputCertificate_of_canonicalProducer
      companion.fourDegree.receipt.schedule
      companion.fourDegree.receipt.producer
      (by simp [Kakeya.realRpowENN])
      companion.fourDegree.receipt.parentConstant_le
      companion.terminalRescaling

/-- The public Target-4 output projected directly from the same canonical
producer as `outputCertificate`. -/
noncomputable def publicOutput :
    FourDegreePacketCoreData
      (eta := eta)
      (packetDensityExponent := packetDensityExponent)
      hdelta metricCompanion.metric
      (Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta))
      (Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta)) :=
  companion.fourDegree.receipt.localInput
    |>.fourDegreePacketCoreData_of_canonicalProducer
      companion.fourDegree.receipt.schedule
      companion.fourDegree.receipt.producer cwaLossExponent
      companion.fourDegree.receipt.parentConstant_le
      companion.fourDegree.receipt.fiberConstant_le

/-- The stored public output is exactly the deterministic projection of the
retained canonical producer. -/
theorem stored_output_eq_publicOutput :
    companion.fourDegree.output = companion.publicOutput :=
  companion.fourDegree.receipt.output_eq

/-- The public output inherits the recorded regularity bound without changing
the canonical producer. -/
theorem publicOutput_regularity_bound :
    (companion.publicOutput.regularity : ENNReal) ≤
      logarithmicLoss delta ^ polylogExponent :=
  companion.stored_output_eq_publicOutput ▸
    companion.fourDegree.regularity_bound

/-- The regularity bound on the exact internal output used by final
assembly. -/
theorem regularity_bound :
    (companion.canonicalOutput.coarseLoss : ENNReal) ≤
      logarithmicLoss delta ^ polylogExponent := by
  change
    (companion.publicOutput.regularity : ENNReal) ≤
      logarithmicLoss delta ^ polylogExponent
  exact companion.publicOutput_regularity_bound

/-- The parent-CWA constant bound on the exact internal output. -/
theorem parent_constant_bound :
    companion.canonicalOutput.parentConstant ≤
      Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta) :=
  companion.fourDegree.receipt.parentConstant_le

include companion

/-- The source fiber-CWA constant bound retained by the canonical receipt. -/
theorem fiber_constant_bound :
    fiberConstant ≤
      Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta) :=
  companion.fourDegree.receipt.fiberConstant_le

/-- The terminal source-fiber constant bound in the exact shape consumed by
the final assembly. -/
theorem terminal_fiber_constant_bound :
    (81000000 : ENNReal) * (fiberConstant / 81000000) ≤
      Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta) := by
  exact
    (show
      (81000000 : ENNReal) * (fiberConstant / 81000000) ≤
        fiberConstant from
      (ENNReal.mul_div_cancel (by norm_num) (by norm_num)).le
    ).trans (fiber_constant_bound companion)

/-- Pure nearby-scale CWA on the exact final coarse family. -/
theorem final_coarse_pure_cwa :
    WZ2PaperPureCWAAtNearbyScales
      companion.outputCertificate.coarse.family
      (Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta)) :=
  companion.outputCertificate.parent_cwa

/-- Exact Definition-2.12 rescaling input for one final complete fiber. -/
noncomputable def final_fiber_rescaling_input
    (parent : Fin companion.outputCertificate.coarse.family.card) :
    PureWZ2Prop62MetricFiberRescalingInput
      companion.outputCertificate.cover parent
      (fiberConstant / 81000000) :=
  companion.outputCertificate.rescaled_fiber_input parent

/-- Exact Assouad-to-literal certificate attached to one final complete
fiber. -/
noncomputable def final_fiber_rescaling_certificate
    (parent : Fin companion.outputCertificate.coarse.family.card) :
    WZ2PaperAssouadToLiteralRescalingCertificate
      (companion.final_fiber_rescaling_input parent).rho_pos
      (WZ2PaperAssouadUnitRescalingData.ofTube
        (companion.outputCertificate.coarse.family.tube parent)
        (companion.final_fiber_rescaling_input parent).rho_pos)
      (companion.final_fiber_rescaling_input parent).literal
      4000000 :=
  (companion.final_fiber_rescaling_input parent).certificate

/-- Pure nearby-scale CWA on the public ordinary family attached to one exact
final complete fiber, weakened to the public Target-4 output constant. -/
theorem final_fiber_pure_cwa
    (parent : Fin companion.outputCertificate.coarse.family.card) :
    WZ2PaperPureCWAAtNearbyScales
      (companion.final_fiber_rescaling_certificate parent).publicFamily
      (Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta)) := by
  have productLe :
      (81000000 : ENNReal) * (fiberConstant / 81000000) ≤
        Kakeya.realRpowENN delta
          (-(cwaLossExponent : ℝ) * eta) := by
    exact
      (show
        (81000000 : ENNReal) * (fiberConstant / 81000000) ≤
          fiberConstant from
        (ENNReal.mul_div_cancel (by norm_num) (by norm_num)).le
      ).trans companion.fourDegree.receipt.fiberConstant_le
  exact
    (companion.final_fiber_rescaling_input parent).publicPureCWA.mono
      productLe companion.outputCertificate.parent_cwa.2.1.2

end Prop62V4RichCertificateCompanionData

/-- Package an existing rich Target-3 companion and canonical Target-4
companion without changing either witness. -/
noncomputable def prop62V4RichCertificateCompanion
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {eta : ℝ}
    {packetDensityExponent cwaLossExponent polylogExponent : ℕ}
    {hdelta : 0 < delta}
    (metricCompanion :
      Prop62V4MetricParentsRichCompanionData
        sourceShading rho fineParentDistanceConstant
          parentConstant fiberConstant)
    (fourDegree :
      Prop62V4FourDegreeCompanionData
        (eta := eta)
        (packetDensityExponent := packetDensityExponent)
        (cwaLossExponent := cwaLossExponent)
        (polylogExponent := polylogExponent)
        hdelta
        metricCompanion.metric) :
    Prop62V4RichCertificateCompanionData
      (eta := eta)
      (packetDensityExponent := packetDensityExponent)
      (cwaLossExponent := cwaLossExponent)
      (polylogExponent := polylogExponent)
      hdelta metricCompanion where
  fourDegree := fourDegree

end Prop62PaperAudit.V4

end Kakeya.Assouad

end
