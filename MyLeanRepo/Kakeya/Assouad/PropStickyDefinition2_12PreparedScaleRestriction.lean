import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12AlignedExactSource
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureFiberRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyLeafStatements

/-!
# Pure actual-John data on the prepared strict schedule

The historical preparation restricts every canonical exact-scale cover to one
selected fine family and exactly the coarse parents hit by that family.  The
first per-tube pruning may cut ambient fibers, so the actual outer-John CWA is
transported by the explicit weighted cardinality loss proved in
`PropStickyDefinition2_12PureFiberRestriction`.

This module is only a provenance adapter.  It performs no new selection and
does not reconstruct a parent map from an opaque prepared cover.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Forget no data when viewing a historical tube subfamily in the pure
Definition 2.12 layer. -/
def WZ2PaperPureTubeSubfamily.ofTubeSubfamily
    {delta : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily ambient) :
    WZ2PaperPureTubeSubfamily ambient where
  family := selected.family
  embedding := selected.embedding
  tube_eq := selected.tube_eq

/--
Restrict one synchronized actual-John scale witness to a selected fine family
and the internal cover's hit parents.

The explicit coarse equality is the only model-alignment input.  After that
identification, the public restricted cover and public strict-fiber
uniformity are derived from the synchronization certificate.
-/
noncomputable def
    WZ2PaperPureScaleCoverData.restrictToSynchronizedHitParents
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {ambientConstant weight selectedConstant retentionConstant : ENNReal}
    (data :
      WZ2PaperPureScaleCoverData fine rho.1 ambientConstant)
    (coarse : Kakeya.Streamlined.TubeFamily rho.1)
    (coarse_eq : data.coarse = coarse)
    (internalCover : WZ2PaperPartitioningCover fine coarse)
    (synchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine coarse internalCover)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (hitCoarseNonempty :
      (internalCover.hitParentSubfamily selected).family.Nonempty)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hglobalRetention :
      weight * fine.enncard ≤
        retentionConstant * selected.family.enncard)
    (selectedUniform :
      ∀ first second :
          Fin (internalCover.hitParentSubfamily selected).family.card,
        wz2PaperFullFiberCount
            selected.family
            (internalCover.hitParentSubfamily selected).family first ≤
          selectedConstant *
            wz2PaperFullFiberCount
              selected.family
              (internalCover.hitParentSubfamily selected).family second) :
    let fiberRatioConstant :=
      ambientConstant * retentionConstant * selectedConstant
    let selectedToAmbientRatio :=
      weight⁻¹ * fiberRatioConstant
    WZ2PaperPureScaleCoverData
      selected.family rho.1
      (max selectedConstant
        (selectedToAmbientRatio * ambientConstant)) := by
  subst coarse
  let selectedFine :=
    WZ2PaperPureTubeSubfamily.ofTubeSubfamily selected
  let selectedCoarse :=
    WZ2PaperPureTubeSubfamily.ofTubeSubfamily
      (internalCover.hitParentSubfamily selected)
  let restrictedSynchronization :=
    synchronization.restrictToHitParents
      (data.delta_pos.le.trans rho.2.1) selected
  have hselectedUniform :
      WZ2PaperPureFullFibersAreCUniform
        selected.family selectedCoarse.family selectedConstant :=
    restrictedSynchronization.public_full_fiber_uniform
      (data.delta_pos.le.trans rho.2.1) selectedUniform
  exact
    data.restrictOfWeightedRetention
      selectedFine selectedCoarse hitCoarseNonempty
      restrictedSynchronization.publicCover
      hweightZero hweightTop hglobalRetention hselectedUniform

/-- The synchronized restriction retains exactly the internal hit-parent
coarse family, including across the explicit ambient coarse identification. -/
theorem
    WZ2PaperPureScaleCoverData.restrictToSynchronizedHitParents_coarse
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {ambientConstant weight selectedConstant retentionConstant : ENNReal}
    (data :
      WZ2PaperPureScaleCoverData fine rho.1 ambientConstant)
    (coarse : Kakeya.Streamlined.TubeFamily rho.1)
    (coarse_eq : data.coarse = coarse)
    (internalCover : WZ2PaperPartitioningCover fine coarse)
    (synchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine coarse internalCover)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (hitCoarseNonempty :
      (internalCover.hitParentSubfamily selected).family.Nonempty)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hglobalRetention :
      weight * fine.enncard ≤
        retentionConstant * selected.family.enncard)
    (selectedUniform :
      ∀ first second :
          Fin (internalCover.hitParentSubfamily selected).family.card,
        wz2PaperFullFiberCount
            selected.family
            (internalCover.hitParentSubfamily selected).family first ≤
          selectedConstant *
            wz2PaperFullFiberCount
              selected.family
              (internalCover.hitParentSubfamily selected).family second) :
    (data.restrictToSynchronizedHitParents
      coarse coarse_eq internalCover synchronization selected
      hitCoarseNonempty hweightZero hweightTop
      hglobalRetention selectedUniform).coarse =
        (internalCover.hitParentSubfamily selected).family := by
  subst coarse
  rfl

/--
One prepared schedule coordinate equipped with the literal Definition 2.12
actual-John witness, synchronized with the existing Section 6 strict cover.
-/
structure WZ2PaperCallerPreparedPureScaleData
    {delta sigma sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (aligned :
      WZ2PaperAlignedPureExactSource
        sigma sourceLoss source shading)
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (coordinate : Fin prepared.strictScaleCount) where
  pureScale :
    WZ2PaperPureScaleCoverData
      prepared.refinement.selected.family
      (prepared.strictScale coordinate).1
      prepared.structuralConstant
  coarse_eq :
    pureScale.coarse =
      (prepared.strictScaleData coordinate).coarse
  cover_eq :
    HEq pureScale.cover
      (prepared.strict_synchronization
        (fun rho =>
          aligned.sourceData.canonicalScaleSynchronization rho)
        coordinate).publicCover

namespace WZ2PaperAlignedPureExactSource

/-- The canonical internal choices made by two proofs of the same exact-scale
CWA proposition agree. -/
private theorem canonical_choice_eq
    {delta sigma loss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    (aligned :
      WZ2PaperAlignedPureExactSource
        sigma loss source shading)
    (sourceExactCWA :
      WZ2PaperCWAAtEveryScale source
        (Kakeya.realRpowENN delta (-loss)))
    (rho : Kakeya.Streamlined.AdmissibleScale delta) :
    Classical.choice (sourceExactCWA.2.2.2 rho) =
      aligned.sourceData.canonicalScaleData rho := by
  have hproof :
      sourceExactCWA.2.2.2 rho =
        aligned.sourceData.internalData.cwa_exact_scales.2.2.2 rho :=
    Subsingleton.elim _ _
  simpa [WZ2PaperSection6ExactSource.canonicalScaleData] using
    congrArg Classical.choice hproof

/-- Re-express the aligned source synchronization at the canonical choices
stored by a prepared record. -/
noncomputable def canonicalSynchronizationFor
    {delta sigma sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (aligned :
      WZ2PaperAlignedPureExactSource
        sigma sourceLoss source shading)
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) :
    let scaleData :=
      Classical.choice
        (prepared.sourceExactCWA.2.2.2 rho)
    WZ2PaperPureInternalCoverSynchronization
      source scaleData.coarse scaleData.cover := by
  let alignedSynchronization :=
    aligned.sourceData.canonicalScaleSynchronization rho
  exact
    alignedSynchronization.ofScaleDataHEq rfl
      (heq_of_eq
        (aligned.canonical_choice_eq
          prepared.sourceExactCWA rho).symm)

/--
Construct the pure actual-John witness on one prepared strict-scale
coordinate.  All losses are the ones already recorded by preparation.
-/
noncomputable def preparedScaleData
    {delta sigma sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (aligned :
      WZ2PaperAlignedPureExactSource
        sigma sourceLoss source shading)
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (coordinate : Fin prepared.strictScaleCount) :
    WZ2PaperCallerPreparedPureScaleData
      aligned prepared coordinate := by
  let rho := prepared.strictScale coordinate
  let canonicalPure := aligned.canonicalPureScaleData rho
  let ambientInternal := prepared.strictAmbientScaleData coordinate
  have hambientCanonical :
      ambientInternal =
        aligned.sourceData.canonicalScaleData rho := by
    exact eq_of_heq <|
      (prepared.strict_ambient_canonical coordinate).trans
        (heq_of_eq
          (aligned.canonical_choice_eq
            prepared.sourceExactCWA rho))
  have hcoarse :
      canonicalPure.pureScale.coarse =
        ambientInternal.coarse := by
    exact canonicalPure.coarse_eq.trans
      (congrArg (fun scaleData => scaleData.coarse)
        hambientCanonical).symm
  let ambientSynchronization :=
    aligned.canonicalSynchronizationFor prepared rho
      |>.ofScaleDataHEq rfl
        (prepared.strict_ambient_canonical coordinate).symm
  let selected := prepared.refinement.selected
  have hhitCoarseNonempty :
      (ambientInternal.cover.hitParentSubfamily selected).family.Nonempty := by
    let sourceIndex : Fin selected.family.card :=
      ⟨0, prepared.selected_card_pos⟩
    exact
      Fin.pos_iff_nonempty.mpr
        ⟨ambientInternal.cover.hitParent selected sourceIndex⟩
  have hweightZero :
      Kakeya.realRpowENN delta sourceLoss ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos prepared.delta_pos sourceLoss)).ne'
  have hweightTop :
      Kakeya.realRpowENN delta sourceLoss ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let retentionConstant : ENNReal :=
    2 *
      (packingConstant10000 : ENNReal) ^ prepared.strictScaleCount *
      (2 : ENNReal) ^ prepared.strictScaleCount *
      (55296 * Kakeya.deltaTubeVolume 1)
  let rawScale :=
    canonicalPure.pureScale.restrictToSynchronizedHitParents
      ambientInternal.coarse hcoarse ambientInternal.cover
      ambientSynchronization selected hhitCoarseNonempty
      hweightZero hweightTop
      (by
        simpa [retentionConstant] using
          prepared.selected_cardinality_retention)
      (prepared.strict_hit_full_fiber_uniform_tight coordinate)
  let pureScale :
      WZ2PaperPureScaleCoverData
        selected.family rho.1 prepared.structuralConstant :=
    rawScale.mono (by
      simpa only [mul_assoc] using
        prepared.pure_restriction_constant_le)
  refine
    {
      pureScale := pureScale
      coarse_eq := ?_
      cover_eq := ?_
    }
  · exact
      (WZ2PaperPureScaleCoverData.restrictToSynchronizedHitParents_coarse
          canonicalPure.pureScale ambientInternal.coarse hcoarse
          ambientInternal.cover ambientSynchronization selected
          hhitCoarseNonempty hweightZero hweightTop
          (by
            simpa [retentionConstant] using
              prepared.selected_cardinality_retention)
          (prepared.strict_hit_full_fiber_uniform_tight coordinate)).trans
        (prepared.strict_coarse_eq coordinate).symm
  · exact proof_irrel_heq _ _

end WZ2PaperAlignedPureExactSource

end Kakeya.Assouad

end
