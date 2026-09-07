import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky

/-!
# Dependent two-level Proposition 6.2 cover for Proposition 6.3

The proof of WZ1 Lemma 4.9 first applies the sticky proposition at a scale
`rho`, and then applies it again to the *coarse pair returned by that first
application*.  The second cover is therefore dependent: an independently
chosen cover of the original fine family is not a substitute.

`PureWZ2PropStickyData` records cropped extremality of its coarse pair, while
the universal Node 3 interface accepts an ordinary extremal source together
with a provenance-preserving cropped normalization.  The record below is the
minimal honest bridge between those two interfaces.  It permits the
mass-retaining subfamily/refinement made before the second application, but
stores the exact embedding and carrierwise containment back to the first
coarse pair.  Thus no arbitrary extremizer can be inserted in its place.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- Ordinary provenance needed to apply Proposition 6.2 to the coarse pair
produced by a previous Proposition 6.2 call.

The source and normalization live at the first cover's actual coarse radius.
The embedding and subshading fields state that the normalized pair is a
genuine refinement of the first cover's coarse pair.  They are deliberately
part of the data: cropped extremality alone does not imply an ordinary trace
with the density required by Node 3. -/
structure Proposition63DependentCoarseReentryData
    {delta sigma outerLoss reentryLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho logExponent)
    (normalizationExponent : ℕ) where
  sourceLoss : ℝ
  source :
    PureWZ2ExtremalConfiguration sigma sourceLoss rho.1
  normalization :
    PureWZ2CroppedCriticalNormalizationData
      (outputLoss := reentryLoss) source normalizationExponent
  coarseEmbedding :
    Fin normalization.croppedFamily.card ↪ Fin outer.coarse.card
  coarse_tube_eq :
    ∀ index, normalization.croppedFamily.tube index =
      outer.coarse.tube (coarseEmbedding index)
  normalized_subshading :
    ∀ index, normalization.croppedRefined.carrier index ⊆
      outer.croppedCoarseShading.carrier (coarseEmbedding index)
  retentionFactor : ENNReal
  retentionFactor_pos : 0 < retentionFactor
  retentionFactor_ne_top : retentionFactor ≠ ⊤
  retained_mass :
    retentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
      normalization.croppedRefined.mass

/-- The genuine second Proposition 6.2 output in the Lemma 4.9 chain.  Its
source is definitionally the normalized coarse pair stored by `reentry`; the
HEq in `reentry` relates that pair back to the first cover's coarse shading. -/
structure Proposition63DependentTwoLevelCoverData
    {delta sigma outerLoss reentryLoss innerLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    (reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent)
    (tau : WZ2PaperRequestedScale rho.1) where
  inner : PureWZ2PropStickyData
    (sigma := sigma) (outputLoss := innerLoss)
    reentry.normalization.croppedRefined tau innerLogExponent

namespace Proposition63DependentTwoLevelCoverData

/-- Compose the second cover's fine-family embedding with the stored
embedding into the first cover's coarse family. -/
def outerCoarseEmbedding
    {delta sigma outerLoss reentryLoss innerLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    (data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau) :
    Fin data.inner.selected.family.card ↪ Fin outer.coarse.card :=
  data.inner.selected.embedding.trans reentry.coarseEmbedding

/-- Every tube selected by the second cover is literally a tube of the first
cover's coarse family at the composed index. -/
theorem inner_selected_tube_eq_outer_coarse
    {delta sigma outerLoss reentryLoss innerLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    (data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau)
    (index : Fin data.inner.selected.family.card) :
    data.inner.selected.family.tube index =
      outer.coarse.tube (data.outerCoarseEmbedding index) := by
  rw [data.inner.selected.tube_eq, reentry.coarse_tube_eq]
  rfl

/-- The second cover's actual refined shading remains a carrierwise
subshading of the first cover's coarse shading. -/
theorem inner_refined_sub_outer_coarse
    {delta sigma outerLoss reentryLoss innerLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    (data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau)
    (index : Fin data.inner.selected.family.card) :
    data.inner.refined.carrier index ⊆
      outer.croppedCoarseShading.carrier
        (data.outerCoarseEmbedding index) :=
  fun _ pointMem =>
    reentry.normalized_subshading (data.inner.selected.embedding index)
      (data.inner.subshading index pointMem)

/-- Compose the mass retained by the coarse re-entry with the polylogarithmic
mass retained by the dependent second Proposition 6.2 call. -/
theorem inner_refined_mass_from_outer_coarse
    {delta sigma outerLoss reentryLoss innerLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    (data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau) :
    wz2PaperPureRefinementFraction rho.1 innerLogExponent *
          (reentry.retentionFactor⁻¹ *
            outer.croppedCoarseShading.mass) ≤
      data.inner.refined.mass := by
  calc
    wz2PaperPureRefinementFraction rho.1 innerLogExponent *
          (reentry.retentionFactor⁻¹ *
            outer.croppedCoarseShading.mass) ≤
        wz2PaperPureRefinementFraction rho.1 innerLogExponent *
          reentry.normalization.croppedRefined.mass := by
      gcongr
      exact reentry.retained_mass
    _ ≤ data.inner.refined.mass := data.inner.retained_mass

end Proposition63DependentTwoLevelCoverData

/-- Quantifier-correct dependent second call to Proposition 6.2.

Node 3 first chooses the loss required of its ordinary input.  Only after
that choice does the caller supply an ordinary re-entry of the first cover's
coarse pair.  The requested inner scale `tau` is measured relative to the
actual outer radius `rho`. -/
theorem proposition63_dependent_two_level_cover
    {normalizationExponent innerLogExponent : ℕ}
    (hStickyAt : PureWZ2CroppedPropStickyAt
      normalizationExponent innerLogExponent)
    {sigma : ℝ} (critical : PureWZ2CriticalPackage sigma)
    (innerLoss : ℝ) (hinnerLoss : 0 < innerLoss) :
    ∃ reentrySourceLoss reentryNormalizationLoss innerScaleBound : ℝ,
      0 < reentrySourceLoss ∧
      0 < reentryNormalizationLoss ∧
      reentrySourceLoss ≤ reentryNormalizationLoss / 2 ∧
      reentryNormalizationLoss < innerLoss ∧
      0 < innerScaleBound ∧ innerScaleBound ≤ 1 ∧
      ∀ {delta outerLoss : ℝ},
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
          ∀ {fineShading : WZ1PaperTubeShading fine},
            ∀ {rho : WZ2PaperRequestedScale delta},
            ∀ {outerLogExponent : ℕ},
              ∀ outer : PureWZ2PropStickyData
                (sigma := sigma) (outputLoss := outerLoss)
                fineShading rho outerLogExponent,
                ∀ reentry : Proposition63DependentCoarseReentryData
                  (reentryLoss := reentryNormalizationLoss) outer
                  normalizationExponent,
                  reentry.sourceLoss = reentrySourceLoss →
                  rho.1 ≤ innerScaleBound →
                  ∀ tau : WZ2PaperRequestedScale rho.1,
                    Real.rpow rho.1 (1 - innerLoss) ≤ tau.1 →
                    tau.1 ≤ Real.rpow rho.1 innerLoss →
                      Nonempty
                        (Proposition63DependentTwoLevelCoverData
                          (innerLoss := innerLoss)
                          (innerLogExponent := innerLogExponent)
                          reentry tau) := by
  rcases hStickyAt sigma critical innerLoss hinnerLoss with
    ⟨reentrySourceLoss, reentryNormalizationLoss, innerScaleBound,
      hreentrySourceLoss, hreentryNormalizationLoss, hlossGap,
      hnormalizationBelowInner,
      hinnerScaleBound, hinnerScaleBoundOne, hSticky⟩
  refine ⟨reentrySourceLoss, reentryNormalizationLoss, innerScaleBound,
    hreentrySourceLoss, hreentryNormalizationLoss, hlossGap,
    hnormalizationBelowInner, hinnerScaleBound, hinnerScaleBoundOne, ?_⟩
  intro delta outerLoss fine fineShading rho outerLogExponent outer reentry
    hsourceLoss hrhoBound tau htauLower htauUpper
  subst reentrySourceLoss
  rcases hSticky rho.1 outer.coarse_extremal.delta_pos hrhoBound
      reentry.source reentry.normalization tau htauLower htauUpper with
    ⟨inner⟩
  exact ⟨{ inner := inner }⟩

end Kakeya.Assouad.PureWZ2

end
