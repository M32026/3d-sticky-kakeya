import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.WZ1.CordobaProjectionCoveringGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCellPruning

/-!
# Property-(P) base definitions for PureWZ2

Shared definitions used by both LocalAD and CordobaSlabLower,
extracted to avoid circular imports.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/--
The part of Property-(P) used by the Cordoba slab argument.

The paper's two `tau/2` grid prunings are not, in general, unions of the
original `L`-grid cells.  Cubicality is needed later, when the resulting
point cover is pulled back to a whole-cell current shading, but it is not
used in the Cordoba estimate itself.  Keeping this smaller record prevents
the localization step from asserting a false intermediate cubicality fact.
-/
structure PureWZ2CordobaPropertyPData
    {sigma L tau : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (epsilon₁ epsilon₃ : ℝ) where
  propertyOne : WZ1PaperTubeShading coarse
  propertyOne_sub : PaperIsSubshading propertyOne coarseShading
  propertyThree : WZ1PaperTubeShading coarse
  propertyThree_sub : PaperIsSubshading propertyThree propertyOne
  propertyOne_full :
    ∀ (j : Fin coarse.card) (p : Point3),
      p ∈ propertyOne.carrier j →
        Kakeya.realRpowENN L (2 + 2 * epsilon₁) *
          ENNReal.ofReal tau ≤
        volume (propertyOne.carrier j ∩ Metric.closedBall p tau)
  transverse :
    ∀ p ∈ propertyThree.union,
      ∀ (i : Fin coarse.card),
        p ∈ propertyThree.carrier i →
          ∃ (j : Fin coarse.card),
            p ∈ propertyOne.carrier j ∧
              Real.rpow L epsilon₃ ≤
                ‖wz1Cross
                  (coarse.tube i).direction
                  (coarse.tube j).direction‖

/--
Property-(P) data for the PureWZ2 grain construction.

Consists of two nested paper-tube shadings (propertyOne ⊆ propertyThree ⊆ coarseShading),
constant multiplicity, local fullness, and transverse direction witnesses.
-/
structure PureWZ2PropertyPData
    {sigma L tau : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (epsilon₁ epsilon₃ : ℝ) where
  propertyOne : WZ1PaperTubeShading coarse
  propertyOne_sub : PaperIsSubshading propertyOne coarseShading
  propertyOne_mass :
    (1 / 2 : ENNReal) * coarseShading.mass ≤ propertyOne.mass
  propertyThree : WZ1PaperTubeShading coarse
  propertyThree_sub : PaperIsSubshading propertyThree propertyOne
  propertyThree_common_spatial :
    ∀ parent, propertyThree.carrier parent =
      coarseShading.carrier parent ∩ propertyThree.union
  propertyThree_mass :
    (1 / 2 : ENNReal) * coarseShading.mass ≤ propertyThree.mass
  propertyThree_cubical : WZ1PaperIsCubicalShading propertyThree
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  multiplicity_lower_pointwise :
    ∀ p ∈ propertyOne.union, multiplicity ≤ propertyOne.pointMultiplicity p
  multiplicity_gt_packing :
    (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ENNReal) <
      (multiplicity : ENNReal)
  propertyOne_full :
    ∀ (j : Fin coarse.card) (p : Point3),
      p ∈ propertyOne.carrier j →
        Kakeya.realRpowENN L (2 + 2 * epsilon₁) *
          ENNReal.ofReal tau ≤
        volume (propertyOne.carrier j ∩ Metric.closedBall p tau)
  transverse :
    ∀ p ∈ propertyThree.union,
      ∀ (i : Fin coarse.card),
        p ∈ propertyThree.carrier i →
          ∃ (j : Fin coarse.card),
            p ∈ propertyOne.carrier j ∧
              Real.rpow L epsilon₃ ≤
                ‖wz1Cross
                  (coarse.tube i).direction
                  (coarse.tube j).direction‖

namespace PureWZ2PropertyPData

/-- Forget the mass and whole-cell fields that are not used by Cordoba. -/
def toCordoba
    {sigma L tau : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    {epsilon₁ epsilon₃ : ℝ}
    (data : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := coarseShading)
      (tau := tau) epsilon₁ epsilon₃) :
    PureWZ2CordobaPropertyPData
      (sigma := sigma) (coarseShading := coarseShading)
      (tau := tau) epsilon₁ epsilon₃ where
  propertyOne := data.propertyOne
  propertyOne_sub := data.propertyOne_sub
  propertyThree := data.propertyThree
  propertyThree_sub := data.propertyThree_sub
  propertyOne_full := data.propertyOne_full
  transverse := data.transverse

end PureWZ2PropertyPData

end Kakeya.Assouad

end
