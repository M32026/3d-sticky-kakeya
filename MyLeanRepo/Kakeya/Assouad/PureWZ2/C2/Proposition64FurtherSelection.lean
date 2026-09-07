import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64PaperEDCleanup
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureHitParentRestriction

/-!
# Further synchronized selection after Proposition 6.4 paper ED cleanup

The nearby-CWA construction may make one additional simultaneous tube
selection.  This module repackages that exact selected family as the final
paper-ED output while preserving shading and source provenance and charging
the displayed mass-retention factor.  No CWA inheritance is asserted here.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2Proposition64PaperEDCleanupData

/-- Repackage a further genuine tube selection.  The new degree parameter is
an explicit upper bound for the composite mass loss. -/
noncomputable def restrictFurther
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {K retentionConstant : ENNReal}
    (data : PureWZ2Proposition64PaperEDCleanupData sourceShading K)
    (selected :
      Kakeya.Streamlined.TubeSubfamily data.subfamily.family)
    (retained_mass :
      data.finalShading.mass ≤
        retentionConstant *
          (restrictPaperShading selected data.finalShading).mass) :
    PureWZ2Proposition64PaperEDCleanupData sourceShading
      ((K + 1) * retentionConstant) := by
  let finalSubfamily := data.subfamily.comp selected
  let finalShading := restrictPaperShading selected data.finalShading
  refine
    { subfamily := finalSubfamily
      finalShading := finalShading
      shading_eq := ?_
      essentially_distinct := ?_
      union_subset := ?_
      mass_retention := ?_
      carrier_volume_pos := ?_
      sourceParent := finalSubfamily.embedding
      sourceParent_eq := rfl
      tube_provenance := finalSubfamily.tube_eq }
  · dsimp only [finalShading, finalSubfamily]
    rw [data.shading_eq]
    rfl
  · change WZ2PaperOrdinaryIsEssentiallyDistinct selected.family
    let selectedPure :
        WZ2PaperPureTubeSubfamily data.subfamily.family :=
      { family := selected.family
        embedding := selected.embedding
        tube_eq := selected.tube_eq }
    exact data.essentially_distinct.subfamily selectedPure
  · rintro point ⟨index, hpoint⟩
    exact data.union_subset ⟨selected.embedding index, hpoint⟩
  · calc
      sourceShading.mass ≤ (K + 1) * data.finalShading.mass :=
        data.mass_retention
      _ ≤ (K + 1) *
          (retentionConstant * finalShading.mass) := by
        gcongr
      _ = ((K + 1) * retentionConstant) *
          finalShading.mass := by ring
      _ ≤ (((K + 1) * retentionConstant) + 1) *
          finalShading.mass := by
        gcongr
        exact le_add_right (le_refl ((K + 1) * retentionConstant))
  · intro index
    exact data.carrier_volume_pos (selected.embedding index)

end PureWZ2Proposition64PaperEDCleanupData

end Kakeya.Assouad

end
