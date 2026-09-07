import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperAudit.StatementsV4
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4Certificate
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4CleanupReceiptAdapter

/-!
# Proposition 6.2 V4 target adapters

This is the paper-facing, acyclic conversion layer.  It turns the external
V4 one-pass cleanup hypothesis into the statement-independent cleanup oracle,
and packages a neutral metric-parent certificate into the V4 target data.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open Kakeya.Assouad

attribute [local instance] Classical.propDecidable

def pureWZ2Prop62CleanupOracleDataOfOnePassTreeCleanupData
    {Leaf Node : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Node] [DecidableEq Node]
    {depth : ℕ}
    {tree : PureWZ2Prop62FiniteTree Leaf Node depth}
    {selected : Finset Leaf}
    (data : OnePassTreeCleanupData tree selected) :
    PureWZ2Prop62CleanupOracleData tree selected :=
  pureWZ2Prop62CleanupOracleDataOfFields
    tree selected data.core data.core_subset data.global_retention
      data.node_density data.weighted_retention data.local_cwa_transfer

theorem onePassTreeCleanupStatement_to_pureWZ2Prop62CleanupOracle
    (hTreeCleanup : OnePassTreeCleanupStatement) :
    PureWZ2Prop62CleanupOracle :=
  pureWZ2Prop62CleanupOracleOfData fun
    Leaf Node _ _ _ _ depth tree selected selectedNonempty =>
      Nonempty.map
        pureWZ2Prop62CleanupOracleDataOfOnePassTreeCleanupData
        (hTreeCleanup Leaf Node depth tree selected selectedNonempty)

theorem metricParentsAtPrescribedScaleData_of_certificate
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {c0 : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (certificate :
      PureWZ2Prop62MetricParentsV4Certificate
        shading rho c0 parentConstant fiberConstant) :
    Nonempty
      (MetricParentsAtPrescribedScaleData
        shading rho c0 parentConstant fiberConstant) := by
  rcases certificate with
    ⟨rhoPos, c0Pos, refinement, fine, familyEq,
      refinedNonempty, refinedCubical, coarse, _coarseCentered, section6Cover,
      cover, coverEq, fullFiberUniform, coarseCWA,
      _coarseStronglySeparated,
      sourceFiberConstant, fiberConstantEq, fiberRescaling,
      fiberPublicCWA, metricFiber, fineParentClose⟩
  subst fine
  let scaleData :
      MetricParentScaleData
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
    ⟨{
      rho_pos := rhoPos
      fine_parent_distance_constant_pos := c0Pos
      refinement := refinement
      refined_nonempty := refinedNonempty
      refined_cubical := refinedCubical
      scaleData := scaleData
      metric_fiber := metricFiber
      fine_parent_close := fineParentClose
    }⟩

end Kakeya.Assouad.Prop62PaperAudit.V4

end
