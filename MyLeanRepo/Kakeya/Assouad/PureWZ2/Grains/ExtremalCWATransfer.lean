import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ExtremalTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalAD
import Mathlib.Tactic

/-!
# Transfer extremal and CWA to propertyThree

Uses ExtremalTransfer with K=8 to transfer the cropped extremal from
coarseShading to propertyThree (the high-multiplicity subshading).

The mass retention is ≥ 9/40 > 1/8 (from gridCellPrune argument),
so K=8 works for the ExtremalTransfer.

CWA is a family-level property and transfers automatically.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

/-- Transfer cropped extremal to a mass-retaining subshading with K=8.

Given:
- `extremal1`: cropped extremal at `loss1` for `shading1`
- `hsub`: `shading2` is a subshading of `shading1`
- `hmass`: `shading2` retains ≥ 1/8 of `shading1`'s mass
- `hcubical`: `shading2` is cubical
- `hloss_le`: `loss1 ≤ loss2`
- `hslack`: `8 * δ^loss2 ≤ δ^loss1`

Produces `extremal2`: cropped extremal at `loss2` for `shading2`.
-/
lemma transfer_extremal_to_propertyThree
    {delta sigma loss1 loss2 : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading1 shading2 : WZ1PaperTubeShading family}
    (extremal1 : WZ2PaperCroppedIsExtremal sigma loss1 family shading1)
    (_cwa1 : WZ2PaperConvexWolffBound family (Kakeya.realRpowENN delta (-loss1)))
    (hsub : PaperIsSubshading shading2 shading1)
    (hmass : (1 / 8 : ENNReal) * shading1.mass ≤ shading2.mass)
    (hcubical : WZ1PaperIsCubicalShading shading2)
    (hloss_le : loss1 ≤ loss2)
    (hslack : (8 : ENNReal) * Kakeya.realRpowENN delta loss2 ≤ Kakeya.realRpowENN delta loss1)
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (hloss2_pos : 0 < loss2) :
    WZ2PaperCroppedIsExtremal sigma loss2 family shading2 := by
  have hK_pos : (0 : ENNReal) < (8 : ENNReal) := by norm_num
  have hK_ne_top : (8 : ENNReal) ≠ ⊤ := by norm_num
  have hmass' : ((8 : ENNReal)⁻¹ * shading1.mass) ≤ shading2.mass := by
    have h_inv : (8 : ENNReal)⁻¹ = (1 / 8 : ENNReal) := by norm_num
    rw [h_inv]
    exact hmass
  exact transfer_cropped_extremal_to_subshading
    (K := (8 : ENNReal))
    hK_pos hK_ne_top
    extremal1 hsub hmass' hcubical hloss_le hslack
    hdelta_pos hdelta_le_one hloss2_pos

/-- CWA transfers automatically to any subshading of the same family,
with a larger constant. -/
lemma transfer_cwa_to_subshading
    {delta loss1 loss2 : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {_shading1 _shading2 : WZ1PaperTubeShading family}
    (cwa1 : WZ2PaperConvexWolffBound family (Kakeya.realRpowENN delta (-loss1)))
    (hloss_le : loss1 ≤ loss2)
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1) :
    WZ2PaperConvexWolffBound family (Kakeya.realRpowENN delta (-loss2)) := by
  have hC2_le_C1 : Kakeya.realRpowENN delta (-loss1) ≤ Kakeya.realRpowENN delta (-loss2) := by
    simp only [Kakeya.realRpowENN]
    have h : Real.rpow delta (-loss1) ≤ Real.rpow delta (-loss2) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one (by linarith)
    exact ENNReal.ofReal_le_ofReal h
  intro convexSet hconv
  have h1 := cwa1 convexSet hconv
  have h2 : Kakeya.realRpowENN delta (-loss1) * volume convexSet * family.enncard ≤
      Kakeya.realRpowENN delta (-loss2) * volume convexSet * family.enncard := by
    gcongr
  exact le_trans h1 h2

end Kakeya.Assouad.PureWZ2

end
