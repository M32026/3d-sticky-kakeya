import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryRescaledTube

/-!
# Produce the Assouad-to-WZ rescaling certificate

The dimension-only comparison constant is `4_000_000`.  For each WZ target
index we use the same source index and construct the recentered ordinary
target tube from the exact literal affine image.  The common coordinate
change and its Jacobian are independent of the source index.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The concrete fixed-constant certificate used by the existential paper
statement and by downstream one-scale adapters. -/
noncomputable def wz2PaperAssouadToLiteralRescalingFixed
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (sourceFamily : Kakeya.Streamlined.TubeFamily delta)
    (anchor : Kakeya.DeltaTube rho)
    (hlineCover :
      ∀ source,
        WZ1PaperTubeCovers
          (sourceFamily.tube source) anchor)
    (literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho) :
    WZ2PaperAssouadToLiteralRescalingCertificate
      hrho
      (WZ2PaperAssouadUnitRescalingData.ofTube anchor hrho)
      literal 4000000 := by
  let normalization :=
    WZ2PaperAssouadUnitRescalingData.ofTube anchor hrho
  let publicFamily :
      Kakeya.Streamlined.TubeFamily (delta / rho) :=
    {
      card := literal.targetFamily.card
      tube := fun target =>
        wz2PaperLiteralOrdinaryRescaledTube
          (sourceFamily.tube (literal.sourceIndex target))
          anchor hrho
    }
  let section6Index :
      Fin literal.targetFamily.card ≃ Fin publicFamily.card :=
    Equiv.refl _
  exact
    {
      publicFamily := publicFamily
      publicSourceIndex := literal.sourceIndex
      publicSourceIndex_bijective :=
        literal.sourceIndex_bijective
      section6Index := section6Index
      sourceIndex_compatibility := by
        intro target
        rfl
      same_axis := by
        intro target
        change
          tubeAxisLine
              (wz2PaperLiteralOrdinaryRescaledTube
                (sourceFamily.tube
                  (literal.sourceIndex target))
                anchor hrho) =
            tubeAxisLine (literal.targetFamily.tube target)
        exact
          wz2PaperLiteralOrdinaryRescaledTube_same_axis
            (sourceFamily.tube (literal.sourceIndex target))
            anchor hrho
            (literal.targetFamily.tube target)
            (literal.target_axis target)
      coordinateChange :=
        wz2PaperJohnToLiteralCoordinateChange
          hrho normalization
      image_eq := by
        intro target
        exact
          wz2PaperJohnToLiteralCoordinateChange_image
            hrho normalization
            (sourceFamily.tube
              (literal.sourceIndex target)).carrier
      literal_image_subset_public := by
        intro target
        change
          wz2PaperLiteralUnitRescalingMap anchor hrho ''
              (sourceFamily.tube
                (literal.sourceIndex target)).carrier ⊆
            (wz2PaperLiteralOrdinaryRescaledTube
              (sourceFamily.tube
                (literal.sourceIndex target))
              anchor hrho).carrier
        exact
          wz2PaperLiteral_image_carrier_subset_ordinary
            hdelta
            (sourceFamily.tube (literal.sourceIndex target))
            anchor hrho hrhoOne
            (hlineCover (literal.sourceIndex target))
      convex_preimage := by
        intro convexSet hconvex
        exact
          Convex.affine_image
            (wz2PaperJohnToLiteralCoordinateChange
              hrho normalization).symm.toAffineMap
            hconvex
      preimage_volume := by
        intro targetSet
        exact
          wz2PaperJohnToLiteralCoordinateChange_inverse_volume
            hrho normalization targetSet
    }

theorem wz2_paper_assouad_to_literal_rescaling :
    WZ2PaperAssouadToLiteralRescalingStatement := by
  refine ⟨4000000, by norm_num, by norm_num, ?_⟩
  intro delta rho hdelta hrho hrhoOne
    sourceFamily anchor hlineCover literal
  exact
    ⟨wz2PaperAssouadToLiteralRescalingFixed
      hdelta hrho hrhoOne sourceFamily anchor
      hlineCover literal⟩

end Kakeya.Assouad

end
