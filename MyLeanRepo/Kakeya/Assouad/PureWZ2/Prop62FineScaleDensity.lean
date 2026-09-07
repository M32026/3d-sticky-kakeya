import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PointwiseProductUpper
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryNestedScaleProducer
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescaledShading
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageCarrier
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageMeasure
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescalingVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralAggregateDensity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper

/-!
# Proposition 6.2: density of the rescaled terminal fine fibers

For one terminal metric parent, this module uses the exact same complete fine
fiber and final shading stored by the fourth-lemma output.

The source packet-density lower bound is normalized by the factor-two fiber
cardinality band.  The canonical literal unit-rescaled family and cubical
image shading are then built, and the exact transverse Jacobian gives the
paper's fine-scale density after one scalar absorption.
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

/-- The exact final shading restricted to one terminal complete metric fiber. -/
noncomputable def terminalFiberShading
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    WZ1PaperTubeShading
      (families.terminalFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent).family :=
  restrictPaperShading
    (families.terminalFiber
      input multiplicity parentClass treeCleanup exactification
        parentDegree core parent)
    output.fineShading

theorem terminalFiberShading_mass
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    (output.terminalFiberShading
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent).mass =
      TerminalFineShading.terminalFiberMass
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent := by
  unfold terminalFiberShading
  unfold TerminalCompleteFamiliesData.terminalFiber
  rw [restrictPaperShading_fromFinset_mass, output.fineShading_eq]
  rfl

theorem terminalFiber_line_class
    (_output :
      input.FourDegreeLemmaOutputData
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          fiberConstant densityConstant logExponent)
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    WZ1PaperIsLineClass
      (families.terminalFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent).family :=
  families.restriction.section6Cover.fine_line_class.subfamily
    (families.terminalFiber
      input multiplicity parentClass treeCleanup exactification
        parentDegree core parent)

theorem terminalFiber_covered
    (_output :
      input.FourDegreeLemmaOutputData
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          fiberConstant densityConstant logExponent)
    (parent :
      Fin families.restriction.coarseSelected.family.card)
    (source :
      Fin
        (families.terminalFiber
          input multiplicity parentClass treeCleanup exactification
            parentDegree core parent).family.card) :
    WZ1PaperTubeCovers
      ((families.terminalFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent).family.tube source)
      (families.restriction.coarseSelected.family.tube parent) := by
  rw [
    (families.terminalFiber
      input multiplicity parentClass treeCleanup exactification
        parentDegree core parent).tube_eq
  ]
  have sourceMem :
      (families.terminalFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent).embedding source ∈
        wz2PaperFullFiberIndices
          families.restriction.fineSelected.family
          families.restriction.coarseSelected.family parent :=
    Finset.orderEmbOfFin_mem
      (wz2PaperFullFiberIndices
        families.restriction.fineSelected.family
        families.restriction.coarseSelected.family parent)
      rfl source
  exact
    (mem_wz2PaperFullFiberIndices_iff parent
      ((families.terminalFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent).embedding source)).mp sourceMem

/-- Canonical ordinary literal rescaling of one final complete fiber. -/
noncomputable def terminalFiberLiteral
    (_output :
      input.FourDegreeLemmaOutputData
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          fiberConstant densityConstant logExponent)
    (rho_le_one : rho ≤ 1)
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    WZ2PaperLiteralUnitRescaledFamilyData
      (families.terminalFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent).family
      (families.restriction.coarseSelected.family.tube parent)
      input.rho_pos :=
  wz2PaperLiteralOrdinaryRescaledFamilyLiteralData
    input.rho_pos rho_le_one
    (families.terminalFiber
      input multiplicity parentClass treeCleanup exactification
        parentDegree core parent).family
    (families.restriction.coarseSelected.family.tube parent)
    (_output.terminalFiber_line_class
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent)
    (families.restriction.section6Cover.coarse_line_class parent)
    (_output.terminalFiber_covered
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent)

/-- Canonical cubical shading of the literal unit-rescaled complete fiber. -/
noncomputable def terminalFiberLiteralShading
    (rho_le_one : rho ≤ 1)
    (ratio_small : delta / rho ≤ 1 / 24)
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    WZ2PaperLiteralUnitRescaledShadingData
      (output.terminalFiberLiteral
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families rho_le_one parent)
      (output.terminalFiberShading
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent) :=
  Classical.choice <|
    wz2_paper_literal_unit_rescaled_shading
      wz2_paper_literal_image_carrier
      input.delta_pos input.rho_pos rho_le_one ratio_small
      (output.terminalFiber_line_class
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent)
      (families.restriction.section6Cover.coarse_line_class parent)
      (output.terminalFiber_covered
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent)
      (output.terminalFiberLiteral
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families rho_le_one parent)
      (output.terminalFiberShading
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent)

/-- Exact Jacobian lower bound for the canonical literal image shading. -/
noncomputable def terminalFiberImageMeasure
    (rho_le_one : rho ≤ 1)
    (ratio_small : delta / rho ≤ 1 / 24)
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    WZ2PaperLiteralImageMeasureData
      (output.terminalFiberLiteral
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families rho_le_one parent)
      (output.terminalFiberShading
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent)
      (output.terminalFiberLiteralShading
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families rho_le_one ratio_small parent) :=
  Classical.choice <|
    wz2_paper_literal_image_measure
      wz2_paper_literal_unit_rescaling_volume
      (output.terminalFiberLiteral
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families rho_le_one parent)
      (output.terminalFiberShading
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent)
      (output.terminalFiberLiteralShading
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families rho_le_one ratio_small parent)

/-- The factor-two normalized packet density on one source complete fiber. -/
def terminalFiberSourceDensity
    (_output :
      input.FourDegreeLemmaOutputData
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          fiberConstant densityConstant logExponent) :
    ENNReal :=
  (2 : ENNReal)⁻¹ * densityConstant

theorem terminalFiber_source_mass_lower
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    output.terminalFiberSourceDensity *
          (families.terminalFiber
            input multiplicity parentClass treeCleanup exactification
              parentDegree core parent).family.enncard *
          Kakeya.realRpowENN delta 2 ≤
      (output.terminalFiberShading
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent).mass := by
  have fiberCardUpper :
      ((families.terminalFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent).family.card : ENNReal) ≤
        (2 * output.fiberFloor : ℕ) := by
    exact_mod_cast (output.fiber_cardinality parent).2.le
  rw [output.terminalFiberShading_mass
    input multiplicity parentClass treeCleanup exactification
      parentDegree core good families parent]
  calc
    output.terminalFiberSourceDensity *
          (families.terminalFiber
            input multiplicity parentClass treeCleanup exactification
              parentDegree core parent).family.enncard *
          Kakeya.realRpowENN delta 2 ≤
      output.terminalFiberSourceDensity *
          (2 * output.fiberFloor : ℕ) *
          Kakeya.realRpowENN delta 2 := by
      unfold Kakeya.Streamlined.TubeFamily.enncard
      gcongr
    _ =
      densityConstant * (output.fiberFloor : ENNReal) *
        Kakeya.realRpowENN delta 2 := by
      unfold terminalFiberSourceDensity
      calc
        (2 : ENNReal)⁻¹ * densityConstant *
              (2 * output.fiberFloor : ℕ) *
              Kakeya.realRpowENN delta 2 =
            ((2 : ENNReal)⁻¹ * 2) *
              (densityConstant * (output.fiberFloor : ENNReal) *
                Kakeya.realRpowENN delta 2) := by
          simp only [Nat.cast_mul]
          norm_num only [Nat.cast_ofNat]
          ac_rfl
        _ =
            densityConstant * (output.fiberFloor : ENNReal) *
              Kakeya.realRpowENN delta 2 := by
          rw [ENNReal.inv_mul_cancel] <;> norm_num
    _ ≤
      TerminalFineShading.terminalFiberMass
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent :=
      output.packet_density parent

/-- The one scalar absorption converting source packet density into target
`lambda`-density after the fixed `1/100` normalization. -/
structure FineDensityAbsorptionData
    (output :
      input.FourDegreeLemmaOutputData
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          fiberConstant densityConstant logExponent)
    (lambda : ENNReal) : Prop where
  scalar :
    lambda * (55296 * Kakeya.deltaTubeVolume 1) ≤
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
        output.terminalFiberSourceDensity

theorem terminalFiber_literal_dense
    {lambda : ENNReal}
    (rho_le_one : rho ≤ 1)
    (ratio_small : delta / rho ≤ 1 / 24)
    (absorption :
      FineDensityAbsorptionData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families output lambda)
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    (output.terminalFiberLiteralShading
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families rho_le_one ratio_small parent
      ).targetShading.IsLambdaDense lambda := by
  exact
    wz2_paper_literal_aggregate_density
      wz2_paper_shading_mass_upper
      input.delta_pos input.rho_pos ratio_small
      (output.terminalFiberLiteral
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families rho_le_one parent)
      (output.terminalFiberShading
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent)
      (output.terminalFiberLiteralShading
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families rho_le_one ratio_small parent)
      (output.terminalFiberImageMeasure
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families rho_le_one ratio_small parent)
      output.terminalFiberSourceDensity
      lambda
      (output.terminalFiber_source_mass_lower
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent)
      absorption.scalar

end FourDegreeLemmaOutputData

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
