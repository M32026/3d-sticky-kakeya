import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CanonicalBalancing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeLemmaOutput

/-!
# Proposition 6.2: canonical four-degree output

This module connects the fixed-quota lower-tail argument to the existing
terminal four-degree assembly.  The chosen good sample and every downstream
family, shading, and complete fiber remain in one dependent record.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62PacketCellInput

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
    {A0 : ℕ}
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
        exactification parentDegree bins A0)
    (families :
      input.TerminalCompleteFamiliesData
        multiplicity parentClass treeCleanup exactification
          core.ranges)

namespace FourDegreeCoreAssemblyData

structure CanonicalFourDegreeOutputData
    (fiberConstant densityConstant : ENNReal)
    (logExponent : ℕ) where
  good :
    core.ranges.GoodBalancingSampleData
      (core.balancingDegreeLoss
        input multiplicity parentClass treeCleanup
          exactification parentDegree)
  output :
    input.FourDegreeLemmaOutputData
      multiplicity parentClass treeCleanup exactification
        parentDegree core good families
        fiberConstant densityConstant logExponent

theorem pureWZ2_prop62_canonical_four_degree_output
    {fiberConstant densityConstant : ENNReal}
    {logExponent : ℕ}
    (tailSmall :
      core.BalancingTailSmallData
        input multiplicity parentClass treeCleanup
          exactification parentDegree)
    (packetAbsorption :
      ∀ good :
          core.ranges.GoodBalancingSampleData
            (core.balancingDegreeLoss
              input multiplicity parentClass treeCleanup
                exactification parentDegree),
        TerminalFineShading.PacketDensityAbsorptionData
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good densityConstant)
    (massAbsorption :
      ∀ good :
          core.ranges.GoodBalancingSampleData
            (core.balancingDegreeLoss
              input multiplicity parentClass treeCleanup
                exactification parentDegree),
        input.MassRetentionAbsorptionData
          multiplicity parentClass treeCleanup exactification
            parentDegree core good logExponent) :
    Nonempty
      (core.CanonicalFourDegreeOutputData
        input multiplicity parentClass treeCleanup
          exactification parentDegree families
          fiberConstant densityConstant logExponent) := by
  let good :=
    Classical.choice <|
      core.exists_canonical_good_balancing_sample
        input multiplicity parentClass treeCleanup
          exactification parentDegree tailSmall
  let output :
      input.FourDegreeLemmaOutputData
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          fiberConstant densityConstant logExponent :=
    Classical.choice <|
      input.pureWZ2_prop62_four_degree_lemma_output
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          (fiberConstant := fiberConstant)
          (densityConstant := densityConstant)
          (logExponent := logExponent)
          (packetAbsorption good) (massAbsorption good)
  exact
    ⟨{
      good := good
      output := output
    }⟩

theorem pureWZ2_prop62_canonical_four_degree_output_of_numerical
    {fiberConstant densityConstant : ENNReal}
    {logExponent : ℕ}
    (numerical :
      core.BalancingNumericalSmallData
        input multiplicity parentClass treeCleanup
          exactification parentDegree)
    (packetAbsorption :
      ∀ good :
          core.ranges.GoodBalancingSampleData
            (core.balancingDegreeLoss
              input multiplicity parentClass treeCleanup
                exactification parentDegree),
        TerminalFineShading.PacketDensityAbsorptionData
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good densityConstant)
    (massAbsorption :
      ∀ good :
          core.ranges.GoodBalancingSampleData
            (core.balancingDegreeLoss
              input multiplicity parentClass treeCleanup
                exactification parentDegree),
        input.MassRetentionAbsorptionData
          multiplicity parentClass treeCleanup exactification
            parentDegree core good logExponent) :
    Nonempty
      (core.CanonicalFourDegreeOutputData
        input multiplicity parentClass treeCleanup
          exactification parentDegree families
          fiberConstant densityConstant logExponent) := by
  apply
    core.pureWZ2_prop62_canonical_four_degree_output
      input multiplicity parentClass treeCleanup
        exactification parentDegree families
  · exact
      core.balancingTailSmallData_of_numerical
        input multiplicity parentClass treeCleanup
          exactification parentDegree numerical
  · exact packetAbsorption
  · exact massAbsorption

theorem pureWZ2_prop62_canonical_four_degree_output_of_ambientLog
    {fiberConstant densityConstant : ENNReal}
    {logExponent : ℕ}
    (logSmall :
      core.BalancingAmbientLogSmallData
        input multiplicity parentClass treeCleanup
          exactification parentDegree)
    (packetAbsorption :
      ∀ good :
          core.ranges.GoodBalancingSampleData
            (core.balancingDegreeLoss
              input multiplicity parentClass treeCleanup
                exactification parentDegree),
        TerminalFineShading.PacketDensityAbsorptionData
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good densityConstant)
    (massAbsorption :
      ∀ good :
          core.ranges.GoodBalancingSampleData
            (core.balancingDegreeLoss
              input multiplicity parentClass treeCleanup
                exactification parentDegree),
        input.MassRetentionAbsorptionData
          multiplicity parentClass treeCleanup exactification
            parentDegree core good logExponent) :
    Nonempty
      (core.CanonicalFourDegreeOutputData
        input multiplicity parentClass treeCleanup
          exactification parentDegree families
          fiberConstant densityConstant logExponent) := by
  apply
    core.pureWZ2_prop62_canonical_four_degree_output
      input multiplicity parentClass treeCleanup
        exactification parentDegree families
  · exact
      core.balancingTailSmallData_of_numerical
        input multiplicity parentClass treeCleanup
          exactification parentDegree <|
        core.balancingNumericalSmallData_of_ambientLog
          input multiplicity parentClass treeCleanup
            exactification parentDegree logSmall
  · exact packetAbsorption
  · exact massAbsorption

end FourDegreeCoreAssemblyData

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
