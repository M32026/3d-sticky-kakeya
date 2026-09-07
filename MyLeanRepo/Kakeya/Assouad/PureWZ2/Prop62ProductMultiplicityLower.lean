import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CriticalMultiplicityInputs

/-!
# Proposition 6.2: global multiplicity-product lower bound

This module formalizes the first half of the extremality paragraph.  The
terminal fine shading retains a logarithmic fraction of the source mass, its
union is contained in the source union, and its point multiplicity is bounded
by the frozen coarse loss times `muCoarse * muFine`.

The source density and source volume upper bound are represented by one
explicit scalar certificate.  This keeps the small-parameter absorption
separate from the finite incidence argument.
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
    {degreeLoss : ℕ}
    (good : core.ranges.GoodBalancingSampleData degreeLoss)
    (families :
      input.TerminalCompleteFamiliesData
        multiplicity parentClass treeCleanup exactification
          core.ranges)
    {fiberConstant densityConstant : ENNReal}
    {logExponent : ℕ}
    (output :
      input.FourDegreeLemmaOutputData
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          fiberConstant densityConstant logExponent)

namespace FourDegreeLemmaOutputData

/-- The terminal fine shading is a literal subshading of the source shading. -/
theorem fine_union_subset_source :
    output.fineShading.union ⊆ sourceShading.union := by
  intro point pointMem
  rcases pointMem with ⟨source, sourceMem⟩
  refine
    ⟨families.restriction.fineSelected.embedding source, ?_⟩
  rw [output.fineShading_eq] at sourceMem
  exact
    TerminalFineShading.subshading
      input multiplicity parentClass treeCleanup exactification
        core.ranges good families source sourceMem

/--
The scalar data needed for the paper's lower bound on
`coarseLoss * muCoarse * muFine`.

`massLower` and `volumeUpper` are the source extremality powers after all
earlier fixed-grid losses have been frozen.  The last field is precisely the
small-scale absorption that turns them into `desiredProduct`.
-/
structure ProductMultiplicityInputsData
    (desiredProduct massLower volumeUpper : ENNReal) : Prop where
  mass_lower :
    massLower ≤ sourceShading.mass
  source_volume_upper :
    volume sourceShading.union ≤ volumeUpper
  volume_ne_zero :
    volumeUpper ≠ 0
  volume_ne_top :
    volumeUpper ≠ ⊤
  desired_product_power :
    (desiredProduct *
        families.restriction.fineSelected.family.enncard) *
        volumeUpper ≤
      wz2PaperPureRefinementFraction delta logExponent *
        massLower

/--
The global product lower bound on the same terminal configuration.

No cardinality factorization or fiber uniformity is used here; those enter
only when the product is split into separate fine and coarse floors.
-/
theorem product_multiplicity_lower
    {desiredProduct massLower volumeUpper : ENNReal}
    (productInputs :
      ProductMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families
          (logExponent := logExponent)
          desiredProduct massLower volumeUpper) :
    desiredProduct *
        families.restriction.fineSelected.family.enncard ≤
      (output.coarseLoss * output.muCoarse : ENNReal) *
        output.muFine := by
  have retainedMassLower :
      wz2PaperPureRefinementFraction delta logExponent *
          massLower ≤
        output.fineShading.mass := by
    exact
      (mul_le_mul_left'
        productInputs.mass_lower
        (wz2PaperPureRefinementFraction delta logExponent)).trans
        output.retained_mass
  have terminalVolumeUpper :
      volume output.fineShading.union ≤ volumeUpper := by
    exact
      (measure_mono
        (output.fine_union_subset_source
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families)).trans
        productInputs.source_volume_upper
  have terminalMassUpper :
      output.fineShading.mass ≤
        ((output.coarseLoss * output.muCoarse : ENNReal) *
          output.muFine) *
          volume output.fineShading.union := by
    apply mass_le_of_pointMultiplicity_le
    intro point _pointMem
    exact
      output.pointwise_product_upper
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families point
  apply
    (ENNReal.mul_le_mul_iff_right
      productInputs.volume_ne_zero
      productInputs.volume_ne_top).mp
  calc
    volumeUpper *
        (desiredProduct *
          families.restriction.fineSelected.family.enncard) =
      (desiredProduct *
          families.restriction.fineSelected.family.enncard) *
        volumeUpper := by
      ring
    _ ≤
      wz2PaperPureRefinementFraction delta logExponent *
        massLower :=
      productInputs.desired_product_power
    _ ≤ output.fineShading.mass :=
      retainedMassLower
    _ ≤
        ((output.coarseLoss * output.muCoarse : ENNReal) *
          output.muFine) *
          volume output.fineShading.union :=
      terminalMassUpper
    _ ≤
        ((output.coarseLoss * output.muCoarse : ENNReal) *
          output.muFine) *
          volumeUpper := by
      gcongr
    _ =
        volumeUpper *
          ((output.coarseLoss * output.muCoarse : ENNReal) *
            output.muFine) := by
      ring

end FourDegreeLemmaOutputData

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
