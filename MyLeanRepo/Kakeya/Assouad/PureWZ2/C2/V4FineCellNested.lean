import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeOutputCertificate
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4FinalCoarseCriticalWitness
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-!
# Node 5 whole-cell receipt from the exact V4 output

The public Proposition 6.2 record intentionally forgets the internal packet
cells.  The V4 rich certificate still retains them.  This file exports only
the paper whole-cell nesting needed by Node 5, on the exact final fine and
coarse families of that certificate.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The common factor-two V4 fiber band implies the Node 5 relative fiber
uniformity once the eventual small-scale schedule absorbs the factor two.
This lemma deliberately keeps that numerical absorption as an explicit
hypothesis. -/
theorem PureWZ2Prop62FourDegreeOutputCertificate.full_fiber_uniform_of_two_le
    {delta rho loss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {ambientCover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {input : PureWZ2Prop62PacketCellInput ambientCover shading}
    {densityConstant outputParentConstant sourceFiberConstant : ENNReal}
    (output : PureWZ2Prop62FourDegreeOutputCertificate input
      densityConstant outputParentConstant sourceFiberConstant)
    (htwo : (2 : ENNReal) ≤ Kakeya.realRpowENN rho (-loss)) :
    ∀ first second : Fin output.coarse.family.card,
      ((wz2PaperFullFiberIndices
          output.refinement.selected.family output.coarse.family first).card :
        ENNReal) ≤
        Kakeya.realRpowENN rho (-loss) *
          ((wz2PaperFullFiberIndices
            output.refinement.selected.family output.coarse.family second).card :
            ENNReal) := by
  intro first second
  have firstUpper :
      ((wz2PaperFullFiberIndices
          output.refinement.selected.family output.coarse.family first).card :
        ENNReal) ≤
        2 * (output.fiberFloor : ENNReal) := by
    change
      wz2PaperFullFiberCount
          output.refinement.selected.family output.coarse.family first ≤
        2 * (output.fiberFloor : ENNReal)
    exact (output.fiber_cardinality first).2.le
  have secondLower :
      (output.fiberFloor : ENNReal) ≤
        ((wz2PaperFullFiberIndices
          output.refinement.selected.family output.coarse.family second).card :
          ENNReal) := by
    change
      (output.fiberFloor : ENNReal) ≤
        wz2PaperFullFiberCount
          output.refinement.selected.family output.coarse.family second
    exact (output.fiber_cardinality second).1
  calc
    ((wz2PaperFullFiberIndices
        output.refinement.selected.family output.coarse.family first).card :
      ENNReal) ≤ 2 * (output.fiberFloor : ENNReal) := firstUpper
    _ ≤ Kakeya.realRpowENN rho (-loss) *
        (output.fiberFloor : ENNReal) :=
      mul_le_mul_right' htwo _
    _ ≤ Kakeya.realRpowENN rho (-loss) *
        ((wz2PaperFullFiberIndices
          output.refinement.selected.family output.coarse.family second).card :
          ENNReal) :=
      mul_le_mul_left' secondLower _

/-- Transfer the ordinary critical-floor bound on the exact V4 terminal
coarse shading to the (weaker) Node 5 loss exponent.  The witness and scale
cutoff are inputs: this adapter neither reselects the coarse family nor
chooses a new scale. -/
theorem PureWZ2Prop62FourDegreeOutputCertificate.coarse_volume_lower_of_critical
    {delta rho sigma floorLoss structuralBudget outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {ambientCover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {input : PureWZ2Prop62PacketCellInput ambientCover shading}
    {densityConstant outputParentConstant sourceFiberConstant : ENNReal}
    (output : PureWZ2Prop62FourDegreeOutputCertificate input
      densityConstant outputParentConstant sourceFiberConstant)
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss structuralBudget)
    (witness :
      Prop62V4FinalCoarseCriticalWitness
        output critical.structuralLoss)
    (rho_le : rho ≤ critical.delta₀)
    (rho_le_one : rho ≤ 1)
    (floorLoss_le_outputLoss : floorLoss ≤ outputLoss) :
    Kakeya.realRpowENN rho (sigma + outputLoss) ≤
      volume output.coarseShading.union := by
  exact
    (pure_wz2_rpowENN_antitone input.rho_pos rho_le_one
      (by linarith : sigma + floorLoss ≤ sigma + outputLoss)).trans
      (Prop62V4FinalCoarseCriticalWitness.volume_floor
        critical witness rho_le)

end Kakeya.Assouad

end
