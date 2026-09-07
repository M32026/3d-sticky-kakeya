import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FinalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CanonicalRescaledFiberBoundedSupport

/-!
# Canonical terminal-fibre support

This module records the unit-ball support of the concrete public family used
by the terminal Proposition 6.2 rescaling.  It is intentionally a theorem
about `terminalFiberCertificate`, not the abstract rescaled-output record.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62PacketCellInput.FourDegreeLemmaOutputData

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover sourceShading)
    (multiplicity : input.FineMultiplicityClassData)
    (parentClass : input.ParentClassData multiplicity)
    {ambientConstant scaleWindow : ENNReal}
    {schedule : PureWZ2Prop62LaminarPureSchedule
      coarse ambientConstant scaleWindow}
    (treeCleanup : input.ParentTreeCleanupData
      multiplicity parentClass schedule)
    (exactification : input.PacketCellExactificationData
      multiplicity parentClass treeCleanup)
    (parentDegree : input.ReferenceParentDegreeData
      multiplicity parentClass treeCleanup exactification)
    {bins : exactification.incidence.ThreeDegreeBinningData
      exactification.incidence.allEdges}
    {A0 : ℕ}
    (core : input.FourDegreeCoreAssemblyData
      multiplicity parentClass treeCleanup exactification parentDegree bins A0)
    {degreeLoss : ℕ}
    (good : core.ranges.GoodBalancingSampleData degreeLoss)
    (families : input.TerminalCompleteFamiliesData
      multiplicity parentClass treeCleanup exactification core.ranges)
    {fiberConstant densityConstant : ENNReal}
    {logExponent : ℕ}
    (output : input.FourDegreeLemmaOutputData
      multiplicity parentClass treeCleanup exactification parentDegree core
      good families fiberConstant densityConstant logExponent)

/-- Bounded source bases force the concrete midpoint-centred public target of
one terminal complete fibre into the unit ball. -/
theorem terminalFiberCertificate_publicFamily_isInUnitBall
    (rho_le_one : rho ≤ 1)
    (ratio_small : delta / rho ≤ 1 / 24)
    (parent : Fin families.restriction.coarseSelected.family.card)
    (source_bounded : HasBoundedBase
      (families.terminalFiber input multiplicity parentClass treeCleanup
        exactification parentDegree core parent).family 4) :
    (output.terminalFiberCertificate input multiplicity parentClass
      treeCleanup exactification parentDegree core good families
      rho_le_one parent).publicFamily.IsInUnitBall := by
  exact
    wz2PaperLiteralOrdinaryRescaledFamilyCertificate_publicFamily_isInUnitBall_of_boundedBase
      input.delta_pos input.rho_pos rho_le_one ratio_small
      (families.terminalFiber input multiplicity parentClass treeCleanup
        exactification parentDegree core parent).family
      (families.restriction.coarseSelected.family.tube parent)
      (output.terminalFiber_line_class input multiplicity parentClass
        treeCleanup exactification parentDegree core good families parent)
      source_bounded
      (families.restriction.section6Cover.coarse_line_class parent)
      (output.terminalFiber_covered input multiplicity parentClass
        treeCleanup exactification parentDegree core good families parent)

end PureWZ2Prop62PacketCellInput.FourDegreeLemmaOutputData

end Kakeya.Assouad

end
