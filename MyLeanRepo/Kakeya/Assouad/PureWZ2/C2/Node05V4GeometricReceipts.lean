import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.V4FineCellNested
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05CubicalIncidenceValueBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05IndexedIncidenceRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.StickyRefinementData

/-!
# Node 5 geometric receipts from one exact V4 certificate

The rich Proposition 6.2 V4 certificate already retains the exact final fine
and coarse families, their Section-6 cover, the balanced union-volume data,
the fine-cell ancestry, the full-fiber cardinality band, and the final coarse
critical witness.  This file exposes those facts without reselecting any
family, shading, parent, or cell.

Indexed incidence mass is deliberately separate.  The ordinary balanced
cover stores union volume in each active coarse cell, whereas Node 5 needs the
sum of the individual fine-carrier intersections.  The latter is therefore an
explicit receipt and is never identified with the former.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The exact indexed-incidence enhancement of one already balanced cover. -/
structure PureWZ2Node05IndexedIncidenceReceipt
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    (base : PureWZ2BalancedCoverData cover fineShading coarseShading) where
  incidenceMass : ENNReal
  incidenceMass_pos : 0 < incidenceMass
  incidenceMass_ne_top : incidenceMass ≠ ⊤
  fine_cell_incidence_mass :
    ∀ cell ∈ base.activeCells,
      (∑ source : Fin fine.card,
        volume
          (fineShading.carrier source ∩
            wz1PaperGridCube rho cell)) =
        incidenceMass

/-- Forget the finite-selection ledger after a synchronized restriction has
already installed its retained cells as the balanced cover's active cells. -/
noncomputable def PureWZ2Node05IndexedIncidenceExactificationData.toReceipt
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {activeCells : Finset WZ2PaperCellIndex}
    {valueCount : ℕ}
    (exactification :
      PureWZ2Node05IndexedIncidenceExactificationData
        (rho := rho) fineShading activeCells valueCount)
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    (base : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hactive : base.activeCells = exactification.retainedCells)
    (hmass :
      ∀ cell ∈ exactification.retainedCells,
        wz2PaperCellIncidenceMass (rho := rho) fineShading cell =
          exactification.incidenceMass) :
    PureWZ2Node05IndexedIncidenceReceipt base where
  incidenceMass := exactification.incidenceMass
  incidenceMass_pos := exactification.incidenceMass_pos
  incidenceMass_ne_top := exactification.incidenceMass_ne_top
  fine_cell_incidence_mass := by
    intro cell hcell
    rw [hactive] at hcell
    simpa only [wz2PaperCellIncidenceMass] using hmass cell hcell

namespace PureWZ2Prop62FourDegreeOutputCertificate

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {ambientCover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {input : PureWZ2Prop62PacketCellInput ambientCover shading}
    {densityConstant outputParentConstant sourceFiberConstant : ENNReal}
    (output : PureWZ2Prop62FourDegreeOutputCertificate input
      densityConstant outputParentConstant sourceFiberConstant)

/-- Repackage the V4 balanced cover in the pure public cover type.  The only
non-definitional point is that an arbitrary covering parent equals the
canonical parent by essential distinctness. -/
noncomputable def pureBalanced :
    PureWZ2BalancedCoverData
      output.cover output.refinement.refined output.coarseShading where
  point_compatibility := by
    intro source parent parentCovers point pointMem
    have parentEq :
        parent = output.cover.toWZ1PaperTubeCover.parent source :=
      output.cover.toWZ1PaperTubeCover.parent_unique
        source parent parentCovers
    rw [parentEq]
    exact output.balanced.point_compatibility source point pointMem
  coarse_cubical := output.balanced.coarse_cubical
  activeCells := output.balanced.activeCells
  coarse_union_eq := output.balanced.coarse_union_eq
  cellMass := output.balanced.cellMass
  cellMass_pos := output.balanced.cellMass_pos
  cellMass_ne_top := output.balanced.cellMass_ne_top
  fine_cell_mass := output.balanced.fine_cell_mass

@[simp] theorem pureBalanced_activeCells :
    output.pureBalanced.activeCells = output.balanced.activeCells := rfl

@[simp] theorem pureBalanced_cellMass :
    output.pureBalanced.cellMass = output.balanced.cellMass := rfl

/-- The concrete realized-value cost for the exact V4 balanced cover. -/
abbrev node5IncidenceValueCount : ℕ :=
  output.refinement.selected.family.card *
      (wz1PaperGridIndicesInWindow delta input.delta_pos).card + 1

/-- Exactify the V4 indexed incidence masses using their cubical integer
quantization.  The cost is explicit and depends only on the already selected
finite family and V4 balancing level. -/
noncomputable def node5IndexedIncidenceExactification :
    PureWZ2Node05IndexedIncidenceExactificationData
      (rho := rho) output.refinement.refined
      output.pureBalanced.activeCells output.node5IncidenceValueCount :=
  output.pureBalanced.indexedIncidenceExactification
    output.node5IncidenceValueCount
    (by
      rw [pureBalanced_activeCells, ← output.active_coarse_cells_eq]
      exact output.active_coarse_cells_nonempty)
    (by
      simpa only [pureBalanced_activeCells, node5IncidenceValueCount] using
        pureWZ2Node05_genericCubicalIncidence_valueCard_le
          input.delta_pos output.refined_cubical output.pureBalanced.activeCells
          output.fine_cell_nested)

/-- Run the genuine indexed-incidence exactification on the exact V4 fine
shading and synchronously restrict its coarse shading. -/
noncomputable def node5IndexedIncidenceRestriction :
    PureWZ2Node05IndexedIncidenceRestrictionData
      output.pureBalanced output.fine_cell_nested
        output.node5IndexedIncidenceExactification :=
  pureWZ2Node05_indexedIncidenceRestriction
    output.pureBalanced output.fine_cell_nested
      output.node5IndexedIncidenceExactification

/-- The synchronized incidence restriction is a genuine refinement of the
exact V4 fine shading once the finite value-count cost is absorbed. -/
noncomputable def node5IndexedIncidenceFineRefinement
    (logExponent : ℕ)
    (hscalar :
      wz1PaperRefinementFraction delta logExponent *
          (output.node5IncidenceValueCount : ENNReal) ≤ 1) :
    WZ1PaperRefinement output.refinement.refined logExponent :=
  output.node5IndexedIncidenceRestriction.toFineRefinement hscalar

theorem node5IndexedIncidence_fine_mass_retention :
    output.refinement.refined.mass ≤
      (output.node5IncidenceValueCount : ENNReal) *
        output.node5IndexedIncidenceRestriction.fineRestricted.mass :=
  output.node5IndexedIncidenceRestriction
    |>.fine_mass_le_valueCount_mul_restricted_mass

theorem node5IndexedIncidence_fine_cubical :
    WZ1PaperIsCubicalShading
      output.node5IndexedIncidenceRestriction.fineRestricted :=
  output.node5IndexedIncidenceRestriction
    |>.fineRestricted_cubical output.refined_cubical

/-- The global V4 fine multiplicity band is preserved by the synchronized
coarse-cell restriction. -/
theorem node5IndexedIncidence_fineMultiplicityBand
    {lower upper : ℕ}
    (hconstant :
      output.refinement.refined.HasConstantMultiplicity lower upper) :
    output.node5IndexedIncidenceRestriction.fineRestricted
      |>.HasConstantMultiplicity lower upper :=
  pureWZ2Node05RestrictToCells_constantMultiplicity hconstant

/-- Complete the Node-5 balanced cover from the exact V4 ancestry and an
honest indexed-incidence receipt on that very balanced cover. -/
noncomputable def node5Balanced
    (incidence :
      PureWZ2Node05IndexedIncidenceReceipt output.pureBalanced) :
    PureWZ2Node5BalancedCoverData output.pureBalanced where
  incidenceMass := incidence.incidenceMass
  incidenceMass_pos := incidence.incidenceMass_pos
  incidenceMass_ne_top := incidence.incidenceMass_ne_top
  fine_cell_incidence_mass := incidence.fine_cell_incidence_mass
  fine_cell_nested := output.fine_cell_nested

@[simp] theorem node5Balanced_incidenceMass
    (incidence :
      PureWZ2Node05IndexedIncidenceReceipt output.pureBalanced) :
    (output.node5Balanced incidence).incidenceMass =
      incidence.incidenceMass := rfl

/-- The exact V4 fiber band supplies the Node-5 uniformity inequality once
the scale schedule absorbs the factor two. -/
theorem node5_full_fiber_uniform
    {loss : ℝ}
    (htwo : (2 : ENNReal) ≤ Kakeya.realRpowENN rho (-loss)) :
    ∀ first second : Fin output.coarse.family.card,
      ((wz2PaperFullFiberIndices
          output.refinement.selected.family output.coarse.family first).card :
        ENNReal) ≤
        Kakeya.realRpowENN rho (-loss) *
          ((wz2PaperFullFiberIndices
            output.refinement.selected.family output.coarse.family second).card :
            ENNReal) :=
  output.full_fiber_uniform_of_two_le htwo

/-- The coarse critical-floor witness remains attached to the exact V4
coarse shading; only the loss exponent is weakened. -/
theorem node5_coarse_volume_lower
    {sigma floorLoss structuralBudget outputLoss : ℝ}
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
      volume output.coarseShading.union :=
  output.coarse_volume_lower_of_critical critical witness
    rho_le rho_le_one floorLoss_le_outputLoss

end PureWZ2Prop62FourDegreeOutputCertificate

end Kakeya.Assouad

end
