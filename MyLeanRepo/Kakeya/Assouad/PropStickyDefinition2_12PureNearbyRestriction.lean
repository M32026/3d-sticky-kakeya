import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureFiberRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureHitParentRestriction

/-!
# Restrict pure nearby-scale CWA with explicit losses

An arbitrary tube subfamily does not inherit normalized Convex-Wolff bounds.
This module gives the exact safe replacement.  At every nearby scale chosen
by the ambient family, the caller supplies:

* a uniform selected-degree bound for the derived strict-fiber parent map;
* one global selected-cardinality retention bound.

The public hit-parent cover then supplies literal cover provenance, while
`WZ2PaperPureScaleCoverData.restrictOfWeightedRetention` pays the actual-John
fiber-cardinality ratio.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Finite error constant after a pure nearby-scale restriction. -/
def wz2PaperPureNearbyRestrictionConstant
    (ambientConstant weight selectedConstant retentionConstant : ENNReal) :
    ENNReal :=
  max ambientConstant
    (max selectedConstant
      ((weight⁻¹ *
          (ambientConstant * retentionConstant * selectedConstant)) *
        ambientConstant))

/--
Restrict pure nearby-scale CWA after proving the exact degree uniformity of
the selected family at every chosen ambient scale.

No arbitrary-subfamily inheritance is used: `selectedDegreeUniform` is the
missing multiscale combinatorial input.
-/
theorem WZ2PaperPureCWAAtNearbyScales.restrictOfWeightedRetention
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant weight selectedConstant retentionConstant : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (selected : WZ2PaperPureTubeSubfamily fine)
    (selectedNonempty : selected.family.Nonempty)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hretentionTop : retentionConstant ≠ ⊤)
    (hselectedTop : selectedConstant ≠ ⊤)
    (hglobalRetention :
      weight * fine.enncard ≤
        retentionConstant * selected.family.enncard)
    (selectedDegreeUniform :
      ∀ requested : WZ2PaperRequestedScale delta,
        let nearby :=
          Classical.choice (ambient.2.2.2 requested)
        ∀ first second : Fin nearby.scaleData.coarse.card,
          0 <
              ((Finset.univ :
                Finset (Fin selected.family.card)).filter fun source =>
                  nearby.scaleData.cover.parent
                      (selected.embedding source) =
                    first).card →
          0 <
              ((Finset.univ :
                Finset (Fin selected.family.card)).filter fun source =>
                  nearby.scaleData.cover.parent
                      (selected.embedding source) =
                    second).card →
          (((Finset.univ :
            Finset (Fin selected.family.card)).filter fun source =>
              nearby.scaleData.cover.parent
                  (selected.embedding source) =
                first).card : ENNReal) ≤
            selectedConstant *
              (((Finset.univ :
                Finset (Fin selected.family.card)).filter fun source =>
                  nearby.scaleData.cover.parent
                      (selected.embedding source) =
                    second).card : ENNReal)) :
    WZ2PaperPureCWAAtNearbyScales
      selected.family
      (wz2PaperPureNearbyRestrictionConstant
        ambientConstant weight selectedConstant retentionConstant) := by
  let outputConstant :=
    wz2PaperPureNearbyRestrictionConstant
      ambientConstant weight selectedConstant retentionConstant
  have hambientTop : ambientConstant ≠ ⊤ :=
    ambient.2.1.2
  have hinverseTop : weight⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr hweightZero
  have hratioTop :
      (weight⁻¹ *
          (ambientConstant * retentionConstant * selectedConstant)) *
        ambientConstant ≠ ⊤ := by
    exact
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hinverseTop
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top hambientTop hretentionTop)
            hselectedTop))
        hambientTop
  have houtputFinite : WZ2PaperFiniteErrorConstant outputConstant := by
    refine
      ⟨ambient.2.1.1.trans ?_,
        max_ne_top hambientTop (max_ne_top hselectedTop hratioTop)⟩
    exact le_max_left _ _
  refine
    ⟨ambient.1,
      houtputFinite,
      ambient.2.2.1.subfamily selected,
      ?_⟩
  intro requested
  let nearby :=
    Classical.choice (ambient.2.2.2 requested)
  let selectedCoarse :=
    nearby.scaleData.cover.hitParentSubfamily selected
  have hselectedCoarseNonempty :
      selectedCoarse.family.Nonempty :=
    nearby.scaleData.cover.hitParentSubfamily_nonempty
      selected selectedNonempty
  let restrictedCover :=
    nearby.scaleData.cover.restrictToHitParents selected
  have hselectedUniform :
      WZ2PaperPureFullFibersAreCUniform
        selected.family selectedCoarse.family selectedConstant :=
    nearby.scaleData.cover
      |>.restrictToHitParents_fullFiber_uniform_of_subfamily
        nearby.scaleData.rho_pos.le selected selectedConstant
        (selectedDegreeUniform requested)
  let rawScale :=
    nearby.scaleData.restrictOfWeightedRetention
      selected selectedCoarse hselectedCoarseNonempty restrictedCover
      hweightZero hweightTop hglobalRetention hselectedUniform
  have hraw :
      max selectedConstant
          ((weight⁻¹ *
              (ambientConstant * retentionConstant * selectedConstant)) *
            ambientConstant) ≤
        outputConstant := by
    exact le_max_right _ _
  exact
    ⟨{
      rho := nearby.rho
      requested_le := nearby.requested_le
      within_factor :=
        nearby.within_factor.trans_le <| by
          gcongr
          exact le_max_left _ _
      scaleData := rawScale.mono hraw
    }⟩

end Kakeya.Assouad

end
