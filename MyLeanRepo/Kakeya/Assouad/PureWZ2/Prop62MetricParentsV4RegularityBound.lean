import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeRegularityBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperAudit.StatementsV4

/-!
# Proposition 6.2 V4 regularity bound

Thin adapters from the reusable four-degree regularity bound to the frozen V4
name `Prop62PaperAudit.V4.logarithmicLoss`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62PacketCellInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover shading)
    (multiplicity : input.FineMultiplicityClassData)
    (parentClass : input.ParentClassData multiplicity)
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        coarse ambientConstant scaleWindow}
    (treeCleanup :
      input.ParentTreeCleanupData
        multiplicity parentClass schedule)
    (exactification :
      input.PacketCellExactificationData
        multiplicity parentClass treeCleanup)
    (parentDegree :
      input.ReferenceParentDegreeData
        multiplicity parentClass treeCleanup exactification)
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}

theorem terminalCoarseMultiplicityLoss_le_logarithmicLoss_pow_ten
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup exactification parentDegree bins
          (input.canonicalPeelingA0
            multiplicity parentClass treeCleanup exactification bins))
    (depthBound : ℕ)
    {logCoefficient : ℝ}
    (small :
      PureWZ2Prop62RegularitySmallData
        depthBound logCoefficient)
    (deltaLe : delta ≤ small.delta0)
    (depthLe : schedule.levelCount ≤ depthBound)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹)) :
    (core.terminalCoarseMultiplicityLoss
        input multiplicity parentClass treeCleanup exactification
          parentDegree : ENNReal) ≤
      Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 := by
  simpa only [Prop62PaperAudit.V4.logarithmicLoss] using
    input.terminalCoarseMultiplicityLoss_le_directionLevelCount_ten
      multiplicity parentClass treeCleanup exactification parentDegree
        core depthBound small deltaLe depthLe boundaryCoefficientLe
        fineLogBound

theorem regularity_le_logarithmicLoss_pow_ten
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup exactification parentDegree bins
          (input.canonicalPeelingA0
            multiplicity parentClass treeCleanup exactification bins))
    {regularity : ℕ}
    (regularityEq :
      regularity =
        core.terminalCoarseMultiplicityLoss
          input multiplicity parentClass treeCleanup exactification
            parentDegree)
    (depthBound : ℕ)
    {logCoefficient : ℝ}
    (small :
      PureWZ2Prop62RegularitySmallData
        depthBound logCoefficient)
    (deltaLe : delta ≤ small.delta0)
    (depthLe : schedule.levelCount ≤ depthBound)
    (boundaryCoefficientLe :
      wz2PaperBoundaryLogCoefficient ≤ logCoefficient)
    (fineLogBound :
      (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
        logCoefficient * (1 + Real.log delta⁻¹)) :
    (regularity : ENNReal) ≤
      Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 := by
  have lossEq :
      (regularity : ENNReal) =
        (core.terminalCoarseMultiplicityLoss
          input multiplicity parentClass treeCleanup exactification
            parentDegree : ENNReal) :=
    congrArg (fun value : ℕ => (value : ENNReal))
      regularityEq
  exact lossEq.trans_le <|
    input.terminalCoarseMultiplicityLoss_le_logarithmicLoss_pow_ten
      multiplicity parentClass treeCleanup exactification parentDegree
        core depthBound small deltaLe depthLe boundaryCoefficientLe
        fineLogBound

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
