import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WholeCellBalancedRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyPBase

/-!
# Balanced cover induced by analytic Property Three

The analytic Property-Three shading is a common whole-cell restriction of
the original coarse shading.  Pulling the fine shading back to the same cells
therefore preserves the frozen balanced-cover identities exactly.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- Restrict a balanced cover to the analytic Property-Three cells. -/
def PureWZ2PropertyPData.balancedRestriction
    {delta rho sigma tau epsilon₁ epsilon₃ : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (data : PureWZ2PropertyPData
      (sigma := sigma) (tau := tau) (coarseShading := coarseShading)
      epsilon₁ epsilon₃) :
    PureWZ2BalancedCoverData cover
      (propertyThreeFinePullbackShading
        cover fineShading data.propertyThree)
      data.propertyThree :=
  wholeCellBalancedRestriction balanced
    (fun parent =>
      (data.propertyThree_sub parent).trans
        (data.propertyOne_sub parent))
    data.propertyThree_cubical data.propertyThree_common_spatial

end Kakeya.Assouad.PureWZ2

end
