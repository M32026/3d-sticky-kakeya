import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RootNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63SequentialReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63AlignedPhase1Candidate

/-!
# Root-driven finite re-entry for Proposition 6.3

This module connects the provenance-correct root normalization to the finite
Lemma 4.11/4.12 iterator.  The root companion supplies every current-shading
ordinary trace; the iterator still asks separately for the paper's one-scale
analytic candidate.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- Fixed numerical data which prepares every current shading in one finite
iteration.  All products are prefixes of the same mass ledger used by the
iterator. -/
structure Proposition63RootFiniteReentryParameters
    {sigma inputLoss normalizationLoss densityLoss currentLoss weightLoss
      reentryLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent N : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (leftFactor rightFactor : ℕ → ENNReal) where
  schedule : WZ2PaperPureFiniteNearbyScheduleData
    (fine := root.normalization.croppedFamily)
    (Kakeya.realRpowENN delta (-normalizationLoss))
    (Kakeya.realRpowENN delta (-reentryLoss))
    (proposition63CanonicalNearbyLevelCount normalizationLoss)
  ambient_two :
    (2 : ENNReal) < Kakeya.realRpowENN delta (-normalizationLoss)
  delta_small : delta ≤ 1 / 24
  normalizationLoss_le_current : normalizationLoss ≤ currentLoss
  currentLoss_le_reentry : currentLoss ≤ reentryLoss
  currentLoss_pos : 0 < currentLoss
  reentryNormalizationLoss : ℝ
  reentryNormalizationLoss_pos : 0 < reentryNormalizationLoss
  reentryLoss_le_half : reentryLoss ≤ reentryNormalizationLoss / 2
  leftFactor_pos : ∀ index, index < N → 0 < leftFactor index
  leftPrefix_pos : ∀ index, index < N →
    0 < ∏ prior ∈ Finset.range index, leftFactor prior
  leftPrefix_ne_top : ∀ index, index < N →
    (∏ prior ∈ Finset.range index, leftFactor prior) ≠ ⊤
  rightPrefix_ne_top : ∀ index, index < N →
    (∏ prior ∈ Finset.range index, rightFactor prior) ≠ ⊤
  mass_loss_absorb : ∀ index, index < N →
    proposition63Lemma43MassLoss
          (∏ prior ∈ Finset.range index, leftFactor prior)
          (∏ prior ∈ Finset.range index, rightFactor prior) *
        Kakeya.realRpowENN delta currentLoss ≤
      Kakeya.realRpowENN delta normalizationLoss
  canonical_weight_absorb :
    proposition63CanonicalReentryWeight delta weightLoss ≤
      (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta densityLoss *
        Kakeya.realRpowENN delta (currentLoss + 2)
  trace_fixed_absorb :
    (96 * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤ 1
  paper_fixed_absorb :
    ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤
      (73 / 100 : ENNReal)
  regularization_absorb :
    let degreeConstant :=
      16 * (schedule.scaleCount : ENNReal) *
        (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
          ENNReal) ^ schedule.scaleCount
    let regularizationLoss :=
      (8 : ENNReal) *
        (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
          ENNReal) ^ (schedule.scaleCount + 1)
    max degreeConstant
        (((proposition63CanonicalReentryWeight delta weightLoss)⁻¹ *
            (Kakeya.realRpowENN delta (-normalizationLoss) *
              (regularizationLoss *
                ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                  Kakeya.realRpowENN delta 2)) *
              degreeConstant)) *
          Kakeya.realRpowENN delta (-normalizationLoss)) ≤
      Kakeya.realRpowENN delta (-reentryLoss)

/-- The fixed root certificate and prefix mass ledger prepare the actual
current shading for its fresh Proposition 6.2 call. -/
theorem Proposition63RootFiniteReentryParameters.prepareWithCanonicalWeight
    {sigma inputLoss normalizationLoss densityLoss currentLoss weightLoss
      reentryLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent N : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss}
    {leftFactor rightFactor : ℕ → ENNReal}
    (parameters : Proposition63RootFiniteReentryParameters
      (currentLoss := currentLoss) (weightLoss := weightLoss)
      (reentryLoss := reentryLoss) (N := N) root leftFactor rightFactor)
    (index : ℕ) (index_lt : index < N)
    (current : WZ1PaperTubeShading root.normalization.croppedFamily)
    (current_sub : PaperIsSubshading current
      root.normalization.croppedRefined)
    (current_cubical : WZ1PaperIsCubicalShading current)
    (_current_multiplicity : ∀ point ∈ current.union,
      current.pointMultiplicity point =
        root.normalization.croppedRefined.pointMultiplicity point)
    (current_mass_ledger :
      (∏ prior ∈ Finset.range index, leftFactor prior) *
          root.normalization.croppedRefined.mass ≤
        (∏ prior ∈ Finset.range index, rightFactor prior) * current.mass)
    (_current_mass_pos : 0 < current.mass) :
    ∃ data : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) root.normalization current,
      data.normalizationWeight =
          proposition63CanonicalReentryWeight delta weightLoss ∧
        data.levelCount =
          proposition63CanonicalNearbyLevelCount normalizationLoss ∧
        data.reentryNormalizationLoss =
          parameters.reentryNormalizationLoss := by
  exact root.currentShadingReentryFromRoot current parameters.schedule
    parameters.ambient_two (parameters.leftPrefix_pos index index_lt)
    (parameters.leftPrefix_ne_top index index_lt)
    (parameters.rightPrefix_ne_top index index_lt) current_mass_ledger
    parameters.normalizationLoss_le_current parameters.currentLoss_le_reentry
    parameters.currentLoss_pos parameters.reentryNormalizationLoss
    parameters.reentryNormalizationLoss_pos parameters.reentryLoss_le_half
    (parameters.mass_loss_absorb index index_lt)
    parameters.canonical_weight_absorb parameters.trace_fixed_absorb
    parameters.paper_fixed_absorb parameters.regularization_absorb
    current_sub current_cubical parameters.delta_small

/-- Compatibility form of `prepareWithCanonicalWeight` for generic iterator
interfaces which only need existence of the prepared re-entry data. -/
theorem Proposition63RootFiniteReentryParameters.prepare
    {sigma inputLoss normalizationLoss densityLoss currentLoss weightLoss
      reentryLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent N : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss}
    {leftFactor rightFactor : ℕ → ENNReal}
    (parameters : Proposition63RootFiniteReentryParameters
      (currentLoss := currentLoss) (weightLoss := weightLoss)
      (reentryLoss := reentryLoss) (N := N) root leftFactor rightFactor)
    (index : ℕ) (index_lt : index < N)
    (current : WZ1PaperTubeShading root.normalization.croppedFamily)
    (current_sub : PaperIsSubshading current
      root.normalization.croppedRefined)
    (current_cubical : WZ1PaperIsCubicalShading current)
    (current_multiplicity : ∀ point ∈ current.union,
      current.pointMultiplicity point =
        root.normalization.croppedRefined.pointMultiplicity point)
    (current_mass_ledger :
      (∏ prior ∈ Finset.range index, leftFactor prior) *
          root.normalization.croppedRefined.mass ≤
        (∏ prior ∈ Finset.range index, rightFactor prior) * current.mass)
    (current_mass_pos : 0 < current.mass) :
    ∃ data : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) root.normalization current,
      data.reentryNormalizationLoss = parameters.reentryNormalizationLoss := by
  rcases parameters.prepareWithCanonicalWeight index index_lt current
      current_sub current_cubical current_multiplicity current_mass_ledger
      current_mass_pos with ⟨data, _, _, hnormalizationLoss⟩
  exact ⟨data, hnormalizationLoss⟩

/-- Run the positive-mass finite Lemma 4.12 iterator with all re-entry
preparations generated from one root companion and one fixed numerical
certificate. -/
theorem proposition63_finite_sequential_reentry_from_root
    {sigma inputLoss normalizationLoss densityLoss currentLoss weightLoss
      reentryLoss stickyLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent logExponent N : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (planeMap : Point3 → Point3)
    (requested : Fin N → WZ2PaperRequestedScale delta)
    (spatialScale localScale variationScale : ℕ → ℝ)
    (constant : ENNReal)
    (leftFactor rightFactor : ℕ → ENNReal)
    (parameters : Proposition63RootFiniteReentryParameters
      (currentLoss := currentLoss) (weightLoss := weightLoss)
      (reentryLoss := reentryLoss) (N := N) root leftFactor rightFactor)
    (hSticky : ∀ reentrySource :
        PureWZ2ExtremalConfiguration sigma reentryLoss delta,
      ∀ reentryNormalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := parameters.reentryNormalizationLoss) reentrySource
          normalizationExponent,
      ∀ rho : WZ2PaperRequestedScale delta,
        Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
        rho.1 ≤ Real.rpow delta stickyLoss →
        Nonempty (PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          reentryNormalized.croppedRefined rho logExponent))
    (requested_lower : ∀ index,
      Real.rpow delta (1 - stickyLoss) ≤ (requested index).1)
    (requested_upper : ∀ index,
      (requested index).1 ≤ Real.rpow delta stickyLoss)
    (candidateStep : ∀ index : ℕ, ∀ index_lt : index < N,
      ∀ current : WZ1PaperTubeShading root.normalization.croppedFamily,
        ∀ current_sub : PaperIsSubshading current
          root.normalization.croppedRefined,
        ∀ current_cubical : WZ1PaperIsCubicalShading current,
        ∀ current_multiplicity : ∀ point ∈ current.union,
          current.pointMultiplicity point =
            root.normalization.croppedRefined.pointMultiplicity point,
        ∀ current_mass_ledger :
          (∏ prior ∈ Finset.range index, leftFactor prior) *
              root.normalization.croppedRefined.mass ≤
            (∏ prior ∈ Finset.range index, rightFactor prior) * current.mass,
        ∀ current_mass_pos : 0 < current.mass,
        ∀ data : Proposition63CurrentShadingReentryData
          (reentryLoss := reentryLoss) root.normalization current,
        ∀ sticky : PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          data.normalization.croppedRefined
          (requested ⟨index, index_lt⟩) logExponent,
          ∃ candidate : WZ1PaperTubeShading
              data.normalization.croppedFamily,
            PaperIsSubshading candidate
                data.normalization.croppedRefined ∧
              WZ1PaperIsCubicalShading candidate ∧
              (∀ first ∈ candidate.union, ∀ second ∈ candidate.union,
                dist first second ≤ spatialScale index →
                  dist (planeMap first) (planeMap second) ≤
                    variationScale index) ∧
              (∀ point ∈ candidate.union,
                IsADSet1
                  (scalarProjection (planeMap point)
                    (candidate.union ∩ Metric.closedBall point
                      (Real.sqrt (localScale index))))
                  (localScale index) (1 - sigma) constant) ∧
              leftFactor index * current.mass ≤
                rightFactor index * candidate.mass) :
    ∃ final : WZ1PaperTubeShading root.normalization.croppedFamily,
      PaperIsSubshading final root.normalization.croppedRefined ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point =
          root.normalization.croppedRefined.pointMultiplicity point) ∧
      (∀ index, index < N → ∀ first ∈ final.union,
        ∀ second ∈ final.union, dist first second ≤ spatialScale index →
          dist (planeMap first) (planeMap second) ≤ variationScale index) ∧
      (∀ index, index < N → ∀ point ∈ final.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (final.union ∩ Metric.closedBall point
              (Real.sqrt (localScale index))))
          (localScale index) (1 - sigma) constant) ∧
      (∏ index ∈ Finset.range N, leftFactor index) *
          root.normalization.croppedRefined.mass ≤
        (∏ index ∈ Finset.range N, rightFactor index) * final.mass ∧
      0 < final.mass := by
  apply proposition63_finite_sequential_reentry_iteration_of_mass_pos
    root.normalization planeMap requested spatialScale localScale
    variationScale constant leftFactor rightFactor parameters.delta_small
    parameters.leftFactor_pos hSticky requested_lower requested_upper
    parameters.prepare
  exact candidateStep

/-- Run the root-driven positive-mass iterator when the analytic leaf first
produces its Property-(P) estimate at the integer-aligned critical scale
`48 * alignedCoarseScale delta queryScale ^ 2`.  The critical output is
refined to the requested finite-grid scale before it enters the iterator; its
shading, mass comparison, and the ambient plane map are unchanged. -/
theorem proposition63_finite_sequential_aligned_oneScale_from_root
    {sigma inputLoss normalizationLoss densityLoss currentLoss weightLoss
      reentryLoss stickyLoss sourceOneScaleLoss targetOneScaleLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent logExponent N : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (planeMap : Point3 → Point3)
    (requested : Fin N → WZ2PaperRequestedScale delta)
    (queryScale spatialScale variationScale : ℕ → ℝ)
    (constant : ENNReal)
    (leftFactor rightFactor : ℕ → ENNReal)
    (parameters : Proposition63RootFiniteReentryParameters
      (currentLoss := currentLoss) (weightLoss := weightLoss)
      (reentryLoss := reentryLoss) (N := N) root leftFactor rightFactor)
    (coefficient : NNReal)
    (planeLipschitz : LipschitzWith coefficient planeMap)
    (variationBudget : ∀ index, index < N →
      (coefficient : ℝ) * spatialScale index ≤ variationScale index)
    (hSticky : ∀ reentrySource :
        PureWZ2ExtremalConfiguration sigma reentryLoss delta,
      ∀ reentryNormalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := parameters.reentryNormalizationLoss) reentrySource
          normalizationExponent,
      ∀ rho : WZ2PaperRequestedScale delta,
        Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
        rho.1 ≤ Real.rpow delta stickyLoss →
        Nonempty (PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          reentryNormalized.croppedRefined rho logExponent))
    (requested_lower : ∀ index,
      Real.rpow delta (1 - stickyLoss) ≤ (requested index).1)
    (requested_upper : ∀ index,
      (requested index).1 ≤ Real.rpow delta stickyLoss)
    (query_pos : ∀ index, index < N → 0 < queryScale index)
    (query_small : ∀ index, index < N → queryScale index ≤ 1 / 4)
    (query_grid_floor : ∀ index, index < N →
      48 * delta ^ 2 ≤ queryScale index)
    (oneScaleLoss_gap : sourceOneScaleLoss < targetOneScaleLoss)
    (oneScaleLoss_absorb : delta ≤ Real.rpow (40 : ℝ)
      (-1 / (targetOneScaleLoss - sourceOneScaleLoss)))
    (criticalStep : ∀ index : ℕ, ∀ index_lt : index < N,
      ∀ current : WZ1PaperTubeShading root.normalization.croppedFamily,
        ∀ current_sub : PaperIsSubshading current
          root.normalization.croppedRefined,
        ∀ current_cubical : WZ1PaperIsCubicalShading current,
        ∀ current_multiplicity : ∀ point ∈ current.union,
          current.pointMultiplicity point =
            root.normalization.croppedRefined.pointMultiplicity point,
        ∀ current_mass_ledger :
          (∏ prior ∈ Finset.range index, leftFactor prior) *
              root.normalization.croppedRefined.mass ≤
            (∏ prior ∈ Finset.range index, rightFactor prior) * current.mass,
        ∀ current_mass_pos : 0 < current.mass,
        ∀ data : Proposition63CurrentShadingReentryData
          (reentryLoss := reentryLoss) root.normalization current,
        data.normalizationWeight =
          proposition63CanonicalReentryWeight delta weightLoss →
        ∀ sticky : PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          data.normalization.croppedRefined
          (requested ⟨index, index_lt⟩) logExponent,
          ∃ critical : PureWZ2OneScaleLocalGrainData
              (sigma := sigma) (outputLoss := sourceOneScaleLoss)
              (rho := 48 *
                alignedCoarseScale delta (queryScale index) ^ 2)
              (Y := data.normalization.croppedRefined)
              (fun point => planeMap point),
            leftFactor index * current.mass ≤
              rightFactor index * critical.shading.mass)
    (target_constant :
      Kakeya.realRpowENN delta (-targetOneScaleLoss) ≤ constant) :
    ∃ final : WZ1PaperTubeShading root.normalization.croppedFamily,
      PaperIsSubshading final root.normalization.croppedRefined ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point =
          root.normalization.croppedRefined.pointMultiplicity point) ∧
      (∀ index, index < N → ∀ first ∈ final.union,
        ∀ second ∈ final.union, dist first second ≤ spatialScale index →
          dist (planeMap first) (planeMap second) ≤ variationScale index) ∧
      (∀ index, index < N → ∀ point ∈ final.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (final.union ∩ Metric.closedBall point
              (Real.sqrt (queryScale index))))
          (queryScale index) (1 - sigma) constant) ∧
      (∏ index ∈ Finset.range N, leftFactor index) *
          root.normalization.croppedRefined.mass ≤
        (∏ index ∈ Finset.range N, rightFactor index) * final.mass ∧
      0 < final.mass := by
  apply joint_finite_variation_local_ad_iteration_of_mass_pos
    root.normalization.croppedRefined root.normalization.cropped_cubical
      (cropped_extremal_shading_mass_pos
        root.normalization.final_extremal root.normalization.line_class
        parameters.delta_small)
      planeMap N spatialScale queryScale variationScale constant
      leftFactor rightFactor parameters.leftFactor_pos
  intro index index_lt current current_sub current_cubical
    current_multiplicity current_mass_ledger current_mass_pos
  rcases parameters.prepareWithCanonicalWeight index index_lt current
      current_sub current_cubical current_multiplicity current_mass_ledger
      current_mass_pos with
    ⟨data, normalization_weight, _levelCount_eq, hnormalizationLoss⟩
  have hStickyData :
      ∀ reentrySource : PureWZ2ExtremalConfiguration sigma reentryLoss delta,
        ∀ reentryNormalized : PureWZ2CroppedCriticalNormalizationData
          (outputLoss := data.reentryNormalizationLoss) reentrySource
            normalizationExponent,
          ∀ rho : WZ2PaperRequestedScale delta,
            Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
            rho.1 ≤ Real.rpow delta stickyLoss →
              Nonempty (PureWZ2PropStickyData
                (sigma := sigma) (outputLoss := stickyLoss)
                reentryNormalized.croppedRefined rho logExponent) := by
    rw [hnormalizationLoss]
    exact hSticky
  rcases proposition63CurrentShadingReentry_sticky data hStickyData
      (requested ⟨index, index_lt⟩) (requested_lower ⟨index, index_lt⟩)
      (requested_upper ⟨index, index_lt⟩) with ⟨sticky⟩
  rcases criticalStep index index_lt current current_sub current_cubical
        current_multiplicity current_mass_ledger current_mass_pos data
        normalization_weight sticky
      with ⟨critical, critical_mass⟩
  let aligned :=
    PureWZ2OneScaleLocalGrainData.atAlignedCoarseQuery critical
      (query_pos index index_lt) (query_small index index_lt)
      (query_grid_floor index index_lt) oneScaleLoss_gap
      oneScaleLoss_absorb
  have aligned_mass : leftFactor index * current.mass ≤
      rightFactor index * aligned.shading.mass := by
    simpa only [aligned, PureWZ2OneScaleLocalGrainData.atAlignedCoarseQuery,
      PureWZ2OneScaleLocalGrainData.refineAlignedQueryScale,
      PureWZ2OneScaleLocalGrainData.refineQueryScale] using critical_mass
  rcases data.oneScaleCandidate planeMap constant
      (leftFactor index) (rightFactor index) (spatialScale index)
      (variationScale index) coefficient planeLipschitz
      (variationBudget index index_lt) aligned target_constant aligned_mass with
    ⟨candidate, candidate_sub, candidate_cubical, candidate_variation,
      candidate_ad, candidate_mass⟩
  exact data.candidate_joint_one_scale candidate planeMap constant
    (leftFactor index) (rightFactor index) candidate_sub candidate_cubical
    candidate_variation candidate_ad candidate_mass

end Kakeya.Assouad.PureWZ2

end
