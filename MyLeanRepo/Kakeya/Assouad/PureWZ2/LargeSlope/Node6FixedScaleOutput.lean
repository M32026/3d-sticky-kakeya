import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperAudit.StatementsV4

/-!
# The fixed-scale Proposition 6.2 data actually used by Node 6

This is the private Node-6 projection of Proposition 6.2 used in the proof of
Proposition 6.5 (`251007_sticky_kakeya_final.tex`, lines 1968--1972).  It keeps
the final fine refinement, the balanced coarse cells, the two volume bounds
used by the slab selection, and the summed fine multiplicity bound.

In particular, this record does not require the final selected fine family to
carry its own every-scale CWA.  Node 6 zero-extends the final shading back to
the original C2 family, whose every-scale CWA is already part of the C2
configuration.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

structure PureWZ2Node6FixedScaleOutput
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading source)
    (rho : WZ2PaperRequestedScale delta)
    (logExponent : ℕ) where
  delta_pos : 0 < delta
  selected : Kakeya.Streamlined.TubeSubfamily source
  selected_nonempty : selected.family.Nonempty
  refined : WZ1PaperTubeShading selected.family
  subshading : ∀ index,
    refined.carrier index ⊆
      sourceShading.carrier (selected.embedding index)
  retained_mass :
    wz2PaperPureRefinementFraction delta logExponent *
        sourceShading.mass ≤
      refined.mass
  refined_cubical : WZ1PaperIsCubicalShading refined
  fine_volume_upper :
    volume refined.union ≤
      Kakeya.realRpowENN delta (sigma - outputLoss)
  coarse : Kakeya.Streamlined.TubeFamily rho.1
  cover : PureWZ2Section6Cover selected.family coarse
  croppedCoarseShading : WZ1PaperTubeShading coarse
  balanced :
    PureWZ2BalancedCoverData cover refined croppedCoarseShading
  coarse_volume_upper :
    volume croppedCoarseShading.union ≤
      Kakeya.realRpowENN rho.1 (sigma - outputLoss)
  fine_pointMultiplicity_upper : ∀ point,
    (refined.pointMultiplicity point : ENNReal) ≤
      Kakeya.realRpowENN (delta / rho.1)
          (2 - sigma - outputLoss) * selected.family.enncard
  /-- Node-6-private actual indexed mass scale of one balanced coarse cell. -/
  cellIndexedMassBase : ENNReal
  cellIndexedMassBase_pos : 0 < cellIndexedMassBase
  cellIndexedMassBase_ne_top : cellIndexedMassBase ≠ ⊤
  /-- Polylogarithmic non-uniformity factor left by the one-pass peeling. -/
  cellIndexedMassRatio : ENNReal
  cellIndexedMassRatio_pos : 0 < cellIndexedMassRatio
  cellIndexedMassRatio_ne_top : cellIndexedMassRatio ≠ ⊤
  cellIndexedMassRatio_le_logarithmicLoss :
    cellIndexedMassRatio ≤
      (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10
  cellIndexedMass : (ℤ × ℤ × ℤ) → ENNReal
  cellIndexedMass_eq : ∀ cell, cellIndexedMass cell =
    ∑ index : Fin selected.family.card,
      volume (refined.carrier index ∩ wz1PaperGridCube rho.1 cell)
  cellIndexedMass_band : ∀ cell ∈ balanced.activeCells,
    cellIndexedMassBase ≤ cellIndexedMass cell ∧
      cellIndexedMass cell ≤ cellIndexedMassRatio * cellIndexedMassBase
  /-- Node-6-private whole-cell provenance.  This follows from the canonical
  V4 packet construction and is not part of the paper's balanced definition. -/
  fine_cell_nested :
    ∀ source point, point ∈ refined.carrier source →
      ∃ cell ∈ balanced.activeCells,
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          wz1PaperGridCube rho.1 cell

/-- The minimal Proposition-6.2 interface actually consumed by Node 6.
Unlike the historical universal sticky interface, its runtime input is the
same C2 configuration supplied by the paper-facing Node-5 theorem. -/
def PureWZ2Node6FixedScaleAt (logExponent : ℕ) : Prop :=
  ∀ sigma : ℝ,
    ∀ critical : PureWZ2CriticalPackage sigma,
      ∀ outputLoss : ℝ, 0 < outputLoss → outputLoss ≤ 1 →
        ∃ inputLoss delta₀ : ℝ,
          0 < inputLoss ∧
          inputLoss ≤ outputLoss ∧
          0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta,
              ∀ rho : WZ2PaperRequestedScale delta,
                Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                rho.1 ≤ Real.rpow delta outputLoss →
                  Nonempty
                    (PureWZ2Node6FixedScaleOutput
                      (sigma := sigma) (outputLoss := outputLoss)
                      cfg.shading rho logExponent)

/-- Existential wrapper for the fixed-scale Node-6 provider. -/
def PureWZ2Node6FixedScaleStatement : Prop :=
  ∃ logExponent : ℕ, PureWZ2Node6FixedScaleAt logExponent

namespace PureWZ2Node6FixedScaleOutput

/-- Weakening the quantitative loss keeps the same fixed-scale witness. -/
noncomputable def mono_loss
    {delta sigma firstLoss secondLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := firstLoss)
      sourceShading rho logExponent)
    (delta_pos : 0 < delta)
    (loss_le : firstLoss ≤ secondLoss) :
    PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := secondLoss)
      sourceShading rho logExponent where
  selected := data.selected
  delta_pos := data.delta_pos
  selected_nonempty := data.selected_nonempty
  refined := data.refined
  subshading := data.subshading
  retained_mass := data.retained_mass
  refined_cubical := data.refined_cubical
  fine_volume_upper := data.fine_volume_upper.trans <|
    pure_wz2_rpowENN_antitone delta_pos
      (rho.2.1.trans rho.2.2) (by linarith)
  coarse := data.coarse
  cover := data.cover
  croppedCoarseShading := data.croppedCoarseShading
  balanced := data.balanced
  coarse_volume_upper := data.coarse_volume_upper.trans <|
    pure_wz2_rpowENN_antitone
      (delta_pos.trans_le rho.2.1) rho.2.2 (by linarith)
  fine_pointMultiplicity_upper := fun point =>
    data.fine_pointMultiplicity_upper point |>.trans <| by
      gcongr
      exact pure_wz2_rpowENN_antitone
        (div_pos delta_pos (delta_pos.trans_le rho.2.1))
        ((div_le_one (delta_pos.trans_le rho.2.1)).mpr rho.2.1)
        (by linarith)
  cellIndexedMassBase := data.cellIndexedMassBase
  cellIndexedMassBase_pos := data.cellIndexedMassBase_pos
  cellIndexedMassBase_ne_top := data.cellIndexedMassBase_ne_top
  cellIndexedMassRatio := data.cellIndexedMassRatio
  cellIndexedMassRatio_pos := data.cellIndexedMassRatio_pos
  cellIndexedMassRatio_ne_top := data.cellIndexedMassRatio_ne_top
  cellIndexedMassRatio_le_logarithmicLoss :=
    data.cellIndexedMassRatio_le_logarithmicLoss
  cellIndexedMass := data.cellIndexedMass
  cellIndexedMass_eq := data.cellIndexedMass_eq
  cellIndexedMass_band := data.cellIndexedMass_band
  fine_cell_nested := data.fine_cell_nested

end PureWZ2Node6FixedScaleOutput

end Kakeya.Assouad

end
