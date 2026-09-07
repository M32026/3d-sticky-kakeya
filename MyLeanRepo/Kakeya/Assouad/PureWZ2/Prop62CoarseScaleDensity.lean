import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FineScaleDensity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper

/-!
# Proposition 6.2: density of the terminal coarse shading

Every terminal complete metric fiber has the same packet-density lower bound.
Summing over the final parent map gives a global fine-mass lower bound.

The exact fine packet-cell multiplicity is a pointwise fiber cap, so the
standard parent-fiber decomposition transfers this fine mass to the frozen
coarse shading.  The quadratic paper-carrier volume upper bound then proves
coarse density after one scalar absorption.
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

theorem sum_terminalFiberMass_eq_fineMass :
    (∑ parent :
        Fin families.restriction.coarseSelected.family.card,
      TerminalFineShading.terminalFiberMass
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent) =
      output.fineShading.mass := by
  have fiberEq :
      ∀ parent :
          Fin families.restriction.coarseSelected.family.card,
        TerminalFineShading.terminalFiberMass
            input multiplicity parentClass treeCleanup exactification
              parentDegree core good families parent =
          ∑ source ∈
              families.restriction.lineCover.fiberIndices parent,
            volume (output.fineShading.carrier source) := by
    intro parent
    unfold TerminalFineShading.terminalFiberMass
    rw [output.fineShading_eq]
    apply Finset.sum_congr
    · ext source
      exact
        (mem_lineCover_fiberIndices_iff_fullFiber
          input multiplicity parentClass treeCleanup exactification
            parentDegree core families parent source).symm
    · intro source _sourceMem
      rfl
  simp_rw [fiberEq]
  change
    (∑ parent :
        Fin families.restriction.coarseSelected.family.card,
      ∑ source ∈
          families.restriction.lineCover.fiberIndices parent,
        volume (output.fineShading.carrier source)) =
      ∑ source :
          Fin families.restriction.fineSelected.family.card,
        volume (output.fineShading.carrier source)
  have fiberwise :=
    Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ :
        Finset
          (Fin families.restriction.fineSelected.family.card)))
      (t := (Finset.univ :
        Finset
          (Fin families.restriction.coarseSelected.family.card)))
      (g := families.restriction.lineCover.parent)
      (fun _ _ => Finset.mem_univ _)
      (fun source => volume (output.fineShading.carrier source))
  simpa only [
    WZ1PaperTubeCover.fiberIndices,
    Finset.sum_filter
  ] using fiberwise

def terminalCoarseMassLower : ENNReal :=
  densityConstant * (output.fiberFloor : ENNReal) *
    Kakeya.realRpowENN delta 2 *
    families.restriction.coarseSelected.family.enncard

theorem terminalCoarseMassLower_le_fineMass :
    output.terminalCoarseMassLower
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families ≤
      output.fineShading.mass := by
  rw [← output.sum_terminalFiberMass_eq_fineMass
    input multiplicity parentClass treeCleanup exactification
      parentDegree core good families]
  calc
    output.terminalCoarseMassLower
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families =
      ∑ _parent :
          Fin families.restriction.coarseSelected.family.card,
        densityConstant * (output.fiberFloor : ENNReal) *
          Kakeya.realRpowENN delta 2 := by
      unfold terminalCoarseMassLower
      simp [
        Kakeya.Streamlined.TubeFamily.enncard,
        Finset.sum_const,
        nsmul_eq_mul
      ]
      ring
    _ ≤
      ∑ parent :
          Fin families.restriction.coarseSelected.family.card,
        TerminalFineShading.terminalFiberMass
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families parent := by
      exact
        Finset.sum_le_sum fun parent _ =>
          output.packet_density parent

theorem fine_mass_le_muFine_mul_coarse_mass :
    output.fineShading.mass ≤
      (output.muFine : ENNReal) * output.coarseShading.mass := by
  exact
    families.restriction.lineCover
      |>.fine_mass_le_fiberCap_mul_coarse_mass
        output.fineShading output.coarseShading
        (fun source point pointMem =>
          output.balanced.point_compatibility
            source
            (families.restriction.lineCover.parent source)
            (families.restriction.lineCover.parent_covers source)
            point pointMem)
        output.fiber_pointMultiplicity_le

theorem coarse_body_mass_upper
    (_output :
      input.FourDegreeLemmaOutputData
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          fiberConstant densityConstant logExponent)
    (rho_small : rho ≤ 1 / 24) :
    (wz1PaperBodyFamily
      families.restriction.coarseSelected.family).mass ≤
      (55296 * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN rho 2 *
        families.restriction.coarseSelected.family.enncard := by
  let fullShading :
      WZ1PaperTubeShading
        families.restriction.coarseSelected.family :=
    {
      carrier := fun parent =>
        wz1PaperTubeCarrier
          (families.restriction.coarseSelected.family.tube parent)
      measurable_carrier := fun parent =>
        wz1PaperTubeCarrier_measurable
          (families.restriction.coarseSelected.family.tube parent)
      subset_body := fun _ => Set.Subset.rfl
    }
  have upper :=
    wz2_paper_shading_mass_upper
      input.rho_pos rho_small
      families.restriction.section6Cover.coarse_line_class
      fullShading
  change
    (wz1PaperBodyFamily
      families.restriction.coarseSelected.family).mass ≤
      (55296 * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN rho 2 *
        families.restriction.coarseSelected.family.enncard at upper
  exact upper

structure CoarseDensityAbsorptionData
    (output :
      input.FourDegreeLemmaOutputData
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          fiberConstant densityConstant logExponent)
    (lambda : ENNReal) : Prop where
  scalar :
    (output.muFine : ENNReal) *
        (lambda * (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN rho 2) ≤
      densityConstant * (output.fiberFloor : ENNReal) *
        Kakeya.realRpowENN delta 2

theorem terminalCoarse_dense
    {lambda : ENNReal}
    (rho_small : rho ≤ 1 / 24)
    (absorption :
      CoarseDensityAbsorptionData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families output lambda) :
    output.coarseShading.IsLambdaDense lambda := by
  have scaledBody :
      (output.muFine : ENNReal) *
          (lambda *
            (wz1PaperBodyFamily
              families.restriction.coarseSelected.family).mass) ≤
        (output.muFine : ENNReal) * output.coarseShading.mass := by
    calc
      (output.muFine : ENNReal) *
          (lambda *
            (wz1PaperBodyFamily
              families.restriction.coarseSelected.family).mass) ≤
        (output.muFine : ENNReal) *
          (lambda *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN rho 2 *
              families.restriction.coarseSelected.family.enncard)) := by
        gcongr
        exact
          coarse_body_mass_upper
            input multiplicity parentClass treeCleanup exactification
              parentDegree core good families output rho_small
      _ =
        ((output.muFine : ENNReal) *
          (lambda * (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN rho 2)) *
          families.restriction.coarseSelected.family.enncard := by
        ring
      _ ≤
        (densityConstant * (output.fiberFloor : ENNReal) *
          Kakeya.realRpowENN delta 2) *
          families.restriction.coarseSelected.family.enncard := by
        exact
          mul_le_mul_right' absorption.scalar
            families.restriction.coarseSelected.family.enncard
      _ =
        output.terminalCoarseMassLower
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families := by
        rfl
      _ ≤ output.fineShading.mass :=
        output.terminalCoarseMassLower_le_fineMass
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families
      _ ≤
        (output.muFine : ENNReal) *
          output.coarseShading.mass :=
        output.fine_mass_le_muFine_mul_coarse_mass
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families
  have scaledRight :
      (lambda *
        (wz1PaperBodyFamily
          families.restriction.coarseSelected.family).mass) *
          (output.muFine : ENNReal) ≤
        output.coarseShading.mass * (output.muFine : ENNReal) := by
    simpa [mul_comm] using scaledBody
  exact
    (ENNReal.mul_le_mul_iff_left
      (by exact_mod_cast output.muFine_pos.ne')
      (ENNReal.natCast_ne_top output.muFine)).mp scaledRight

end FourDegreeLemmaOutputData

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
