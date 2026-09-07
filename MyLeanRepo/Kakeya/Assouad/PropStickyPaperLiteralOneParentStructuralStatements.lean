import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralOneParentStatements

/-!
# Paper-faithful structural output of the one-parent lemma

WZ Lemma 3.3 first constructs a refined unit-rescaled pair with the covering,
density, cardinality, and point-multiplicity conclusions.  The small
union-volume conclusion is obtained only after the global balanced-cover
multiplicity comparison in Proposition 3.2.

This record therefore omits `volume_upper` and extremality.  A separate
completion theorem adds those fields once the final rescaled union-volume
upper bound is available.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperLiteralLemma3_3StructuralData
    {delta rho sigma strongLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (coarse : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (logExponent : ℕ) where
  refinement :
    WZ1PaperRefinement shading logExponent
  refined_cubical :
    WZ1PaperIsCubicalShading refinement.refined
  familyData :
    WZ2PaperLiteralUnitRescaledFamilyData
      refinement.selected.family coarse hrho
  literalShading :
    WZ2PaperLiteralUnitRescaledShadingData
      familyData refinement.refined
  target_scale_pos : 0 < delta / rho
  target_scale_le_one : delta / rho ≤ 1
  strongLoss_pos : 0 < strongLoss
  strongLoss_budget : 3 * strongLoss ≤ outputLoss
  target_nonempty : familyData.targetFamily.Nonempty
  target_cwa_nearby :
    WZ2PaperCWAAtNearbyScales
      familyData.targetFamily
      (Kakeya.realRpowENN (delta / rho) (-strongLoss))
  target_convex_wolff :
    WZ2PaperConvexWolffBound
      familyData.targetFamily
      (Kakeya.realRpowENN (delta / rho) (-strongLoss))
  target_dense :
    literalShading.targetShading.IsLambdaDense
      (Kakeya.realRpowENN (delta / rho) strongLoss)
  target_cardinality_lower :
    Kakeya.realRpowENN (delta / rho)
        (-2 + 2 * strongLoss) ≤
      familyData.targetFamily.enncard
  source_cardinality_eq :
    familyData.targetFamily.enncard =
      refinement.selected.family.enncard
  source_multiplicity_upper_strong :
    ∀ point,
      (refinement.refined.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - strongLoss) *
          refinement.selected.family.enncard
  source_cardinality_lower :
    Kakeya.realRpowENN (delta / rho)
        (-2 + 2 * strongLoss) ≤
      refinement.selected.family.enncard

def WZ2PaperLiteralLemma3_3StructuralCompletionStatement : Prop :=
  ∀ {delta rho sigma strongLoss outputLoss : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ (shading : WZ1PaperTubeShading fine),
        ∀ (coarse : Kakeya.DeltaTube rho),
          ∀ (hrho : 0 < rho),
            ∀ (logExponent : ℕ),
              ∀ (data :
                  WZ2PaperLiteralLemma3_3StructuralData
                    (sigma := sigma)
                    (strongLoss := strongLoss)
                    (outputLoss := outputLoss)
                    shading coarse hrho logExponent),
                (∀ index,
                  (data.refinement.refined.carrier index).Nonempty) →
                MeasureTheory.volume
                    data.literalShading.targetShading.union ≤
                  Kakeya.realRpowENN
                    (delta / rho) (sigma - strongLoss) →
                Nonempty
                  (WZ2PaperLiteralLemma3_3Data
                    (sigma := sigma)
                    (strongLoss := strongLoss)
                    (outputLoss := outputLoss)
                    shading coarse hrho logExponent)

end Kakeya.Assouad

end
