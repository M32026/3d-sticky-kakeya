import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperFinalV4PointwiseProductUpper
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedCoarseDensity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper

/-!
# Proposition 6.2 V4 record-level coarse and fiber density

The packet-density field is already stated on every complete public fiber.
Summing it over the partitioning cover gives the global mass lower bound used
for coarse density.  The factor-two fiber-cardinality band gives the
corresponding density on each unrescaled complete fiber.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open MeasureTheory
open Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PaperFourDegreePacketCoreData

variable
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {eta : ℝ}
    {packetDensityExponent : ℕ}
    {hdelta : 0 < delta}
    {metric :
      PaperMetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
          parentConstant fiberConstant}
    {outputParentConstant outputFiberConstant : ENNReal}
    (output :
      PaperFourDegreePacketCoreData
        (eta := eta)
        (packetDensityExponent := packetDensityExponent)
        hdelta metric outputParentConstant outputFiberConstant)

include output

/-- The global fine-mass floor obtained by summing the packet floor over all
complete terminal fibers. -/
def terminalCoarseMassLower : ENNReal :=
  Kakeya.realRpowENN delta
      ((packetDensityExponent : ℝ) * eta) *
    (output.fiberFloor : ENNReal) *
    Kakeya.realRpowENN delta 2 *
    output.coarse.family.enncard

theorem terminalCoarseMassLower_le_refined_mass :
    output.terminalCoarseMassLower ≤
      output.refinement.refined.mass := by
  rw [← output.cover.sum_fullFiberShading_mass
    output.refinement.refined]
  calc
    output.terminalCoarseMassLower =
        ∑ _parent : Fin output.coarse.family.card,
          Kakeya.realRpowENN delta
              ((packetDensityExponent : ℝ) * eta) *
            (output.fiberFloor : ENNReal) *
            Kakeya.realRpowENN delta 2 := by
      simp [
        terminalCoarseMassLower,
        Kakeya.Streamlined.TubeFamily.enncard,
        Finset.sum_const,
        nsmul_eq_mul
      ]
      ring
    _ ≤
        ∑ parent : Fin output.coarse.family.card,
          (restrictPaperShading
            (output.cover.fullFiberSubfamily parent)
            output.refinement.refined).mass := by
      exact Finset.sum_le_sum fun parent _ =>
        output.packet_density parent

/-- Integrating the record-level fiber cap transfers fine mass to coarse mass. -/
theorem refined_mass_le_muFine_mul_coarse_mass :
    output.refinement.refined.mass ≤
      (output.muFine : ENNReal) * output.coarseShading.mass := by
  exact
    output.cover.toWZ1PaperTubeCover
      |>.fine_mass_le_fiberCap_mul_coarse_mass
        output.refinement.refined output.coarseShading
        output.balanced.point_compatibility
        output.fiber_pointMultiplicity_le

/--
Coarse density at any requested constant whose scalar loss is absorbed by the
record-level global packet-mass floor.
-/
theorem coarse_dense
    {lambda : ENNReal}
    (rhoSmall : rho.1 ≤ 1 / 24)
    (absorption :
      lambda *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN rho.1 2) *
            output.coarse.family.enncard *
            (output.muFine : ENNReal) ≤
        output.terminalCoarseMassLower) :
    output.coarseShading.IsLambdaDense lambda := by
  exact
    wz2_paper_balanced_coarse_density
      metric.rho_pos rhoSmall output.cover
      output.refinement.refined output.coarseShading output.balanced
      output.parent_cwa.2.1
      (output.muFine : ENNReal) output.terminalCoarseMassLower lambda
      (by exact_mod_cast output.muFine_pos.ne')
      (ENNReal.natCast_ne_top output.muFine)
      output.fiber_pointMultiplicity_le
      output.terminalCoarseMassLower_le_refined_mass absorption

/-- The factor-two normalization of the packet-density coefficient. -/
def fullFiberSourceDensity
    (_output :
      PaperFourDegreePacketCoreData
        (eta := eta)
        (packetDensityExponent := packetDensityExponent)
        hdelta metric outputParentConstant outputFiberConstant) :
    ENNReal :=
  (2 : ENNReal)⁻¹ *
    Kakeya.realRpowENN delta
      ((packetDensityExponent : ℝ) * eta)

/-- Every complete terminal fiber has the normalized source-mass lower bound. -/
theorem fullFiber_source_mass_lower
    (parent : Fin output.coarse.family.card) :
    output.fullFiberSourceDensity *
          (output.cover.fullFiberSubfamily parent).family.enncard *
          Kakeya.realRpowENN delta 2 ≤
      (restrictPaperShading
        (output.cover.fullFiberSubfamily parent)
        output.refinement.refined).mass := by
  have fiberCardUpper :
      (output.cover.fullFiberSubfamily parent).family.enncard ≤
        (2 * output.fiberFloor : ℕ) := by
    change
      (wz2PaperFullFiberCount
        output.refinement.selected.family output.coarse.family parent :
          ENNReal) ≤
        (2 * output.fiberFloor : ℕ)
    exact_mod_cast (output.fiber_cardinality parent).2.le
  calc
    output.fullFiberSourceDensity *
          (output.cover.fullFiberSubfamily parent).family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        output.fullFiberSourceDensity *
          (2 * output.fiberFloor : ℕ) *
          Kakeya.realRpowENN delta 2 := by
      gcongr
    _ =
        Kakeya.realRpowENN delta
            ((packetDensityExponent : ℝ) * eta) *
          (output.fiberFloor : ENNReal) *
          Kakeya.realRpowENN delta 2 := by
      unfold fullFiberSourceDensity
      calc
        (2 : ENNReal)⁻¹ *
              Kakeya.realRpowENN delta
                ((packetDensityExponent : ℝ) * eta) *
              (2 * output.fiberFloor : ℕ) *
              Kakeya.realRpowENN delta 2 =
            ((2 : ENNReal)⁻¹ * 2) *
              (Kakeya.realRpowENN delta
                  ((packetDensityExponent : ℝ) * eta) *
                (output.fiberFloor : ENNReal) *
                Kakeya.realRpowENN delta 2) := by
          simp only [Nat.cast_mul]
          norm_num only [Nat.cast_ofNat]
          ac_rfl
        _ =
            Kakeya.realRpowENN delta
                ((packetDensityExponent : ℝ) * eta) *
              (output.fiberFloor : ENNReal) *
              Kakeya.realRpowENN delta 2 := by
          rw [ENNReal.inv_mul_cancel] <;> norm_num
    _ ≤
        (restrictPaperShading
          (output.cover.fullFiberSubfamily parent)
          output.refinement.refined).mass :=
      output.packet_density parent

/--
Density of each complete source fiber before rescaling.  The only additional
input is the scalar absorption selecting the desired density constant.
-/
theorem fullFiber_dense
    (deltaSmall : delta ≤ 1 / 24)
    {lambda : ENNReal}
    (absorption :
      lambda * (55296 * Kakeya.deltaTubeVolume 1) ≤
        output.fullFiberSourceDensity)
    (parent : Fin output.coarse.family.card) :
    (restrictPaperShading
      (output.cover.fullFiberSubfamily parent)
      output.refinement.refined).IsLambdaDense lambda := by
  let fiber := output.cover.fullFiberSubfamily parent
  let fiberShading :=
    restrictPaperShading fiber output.refinement.refined
  let fullShading : WZ1PaperTubeShading fiber.family :=
    {
      carrier := fun index =>
        wz1PaperTubeCarrier (fiber.family.tube index)
      measurable_carrier := fun index =>
        wz1PaperTubeCarrier_measurable (fiber.family.tube index)
      subset_body := fun _ => Set.Subset.rfl
    }
  have bodyMassUpper :
      (wz1PaperBodyFamily fiber.family).mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta 2 *
          fiber.family.enncard := by
    exact
      wz2_paper_shading_mass_upper
        hdelta deltaSmall
        (metric.refined_line_class.subfamily output.refinement.selected
          |>.subfamily fiber)
        fullShading
  calc
    lambda * (wz1PaperBodyFamily fiber.family).mass ≤
        lambda *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN delta 2 *
            fiber.family.enncard) := by
      gcongr
    _ =
        (lambda * (55296 * Kakeya.deltaTubeVolume 1)) *
          fiber.family.enncard *
          Kakeya.realRpowENN delta 2 := by
      ring
    _ ≤
        output.fullFiberSourceDensity *
          fiber.family.enncard *
          Kakeya.realRpowENN delta 2 := by
      gcongr
    _ ≤ fiberShading.mass := by
      exact output.fullFiber_source_mass_lower parent

end PaperFourDegreePacketCoreData

end Kakeya.Assouad.Prop62PaperAudit.V4

end
