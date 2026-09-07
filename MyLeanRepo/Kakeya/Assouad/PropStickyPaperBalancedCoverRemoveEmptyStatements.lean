import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickySelectedHitCover

/-!
# Remove empty fine carriers from a balanced paper cover

Exact whole-cell balancing can leave some formal fine tubes with empty
shading.  The paper simply discards those tubes and all coarse parents that
are no longer hit.  Because only empty carriers are deleted, the fine shaded
union is unchanged.  Positivity of the balanced cell mass and coarse
cubicality then show that restricting the coarse shading to the hit parents
also leaves its union unchanged.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

def wz2PaperNonemptyCarrierIndices
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine) :
    Finset (Fin fine.card) :=
  Finset.univ.filter fun index =>
    (shading.carrier index).Nonempty

def wz2PaperNonemptyCarrierSubfamily
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine) :
    Kakeya.Streamlined.TubeSubfamily fine :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset
    fine (wz2PaperNonemptyCarrierIndices shading)

def wz2PaperNonemptyCarrierShading
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine) :
    WZ1PaperTubeShading
      (wz2PaperNonemptyCarrierSubfamily shading).family :=
  restrictPaperShading
    (wz2PaperNonemptyCarrierSubfamily shading) shading

structure WZ2PaperBalancedCoverRemoveEmptyData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse)
    (balanced :
      WZ1PaperBalancedCoverData
        cover.toWZ1PaperTubeCover
        fineShading coarseShading) where
  fine_carrier_nonempty :
    ∀ index,
      (wz2PaperNonemptyCarrierShading
        fineShading).carrier index |>.Nonempty
  fine_union_eq :
    (wz2PaperNonemptyCarrierShading fineShading).union =
      fineShading.union
  fine_mass_eq :
    (wz2PaperNonemptyCarrierShading fineShading).mass =
      fineShading.mass
  coarse_union_eq :
    (restrictPaperShading
      (cover.hitParentSubfamily
        (wz2PaperNonemptyCarrierSubfamily fineShading))
      coarseShading).union =
        coarseShading.union
  balanced_restricted :
    WZ1PaperBalancedCoverData
      (cover.restrictToHitParents
        (wz2PaperNonemptyCarrierSubfamily fineShading)
        |>.toWZ1PaperTubeCover)
      (wz2PaperNonemptyCarrierShading fineShading)
      (restrictPaperShading
        (cover.hitParentSubfamily
          (wz2PaperNonemptyCarrierSubfamily fineShading))
        coarseShading)

def WZ2PaperBalancedCoverRemoveEmptyStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ (cover : WZ2PaperPartitioningCover fine coarse),
          ∀ (fineShading : WZ1PaperTubeShading fine),
            ∀ (coarseShading : WZ1PaperTubeShading coarse),
              ∀ (balanced :
                  WZ1PaperBalancedCoverData
                    cover.toWZ1PaperTubeCover
                    fineShading coarseShading),
                Nonempty
                  (WZ2PaperBalancedCoverRemoveEmptyData
                    cover fineShading coarseShading balanced)

end Kakeya.Assouad

end
