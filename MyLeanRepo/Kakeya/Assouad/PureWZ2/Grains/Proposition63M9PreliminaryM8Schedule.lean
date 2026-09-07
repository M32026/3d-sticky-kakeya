import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63Lemma412OuterSchedule

/-!
# Independent pre-runtime M8 schedule for the preliminary grains

Proposition 6.3 uses the grain-structure lemma twice.  This schedule belongs
to the first use, before the first exact power-scale rich call.  It is kept
separate from the later M8 schedule used after Lemma 4.7.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

private theorem exists_preliminary_positive_lower_bound
    {α : Type*} [Fintype α] (f : α → ℝ)
    (hf : ∀ index, 0 < f index) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ index, bound < f index := by
  classical
  let values : Finset ℝ := insert 1 (Finset.univ.image f)
  have valuesNonempty : values.Nonempty :=
    ⟨1, Finset.mem_insert_self 1 _⟩
  let lower := values.min' valuesNonempty
  have lowerPos : 0 < lower := by
    have lowerMem : lower ∈ values := Finset.min'_mem values valuesNonempty
    rcases Finset.mem_insert.mp lowerMem with lowerOne | lowerImage
    · simpa [lowerOne]
    · rcases Finset.mem_image.mp lowerImage with ⟨index, _, indexEq⟩
      rw [← indexEq]
      exact hf index
  refine ⟨lower / 2, div_pos lowerPos (by norm_num), ?_⟩
  intro index
  have lowerLe : lower ≤ f index := by
    apply Finset.min'_le values (f index)
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨index, Finset.mem_univ index, rfl⟩)
  linarith

/-- The loss hierarchy, central grid, and terminal interpolation cutoff for
the preliminary application of the grain-structure lemma. -/
structure Proposition63M9PreliminaryM8ScheduleData
    (sigma producerLoss localLoss : ℝ) where
  N : ℕ
  gridLoss : ℝ
  midLoss : ℝ
  schedule : Proposition63Lemma412PreRuntimeScheduleData
    sigma gridLoss midLoss N
  gridLoss_eq : gridLoss = producerLoss / 8
  midLoss_eq : midLoss = producerLoss / 4
  N_ge_nine : 9 ≤ N
  one_over_N_lt_grid : (1 : ℝ) / N < gridLoss
  gridLoss_pos : 0 < gridLoss
  gridLoss_le_half : gridLoss ≤ 1 / 2
  gridLoss_lt_sigma : gridLoss < 2 * sigma / 5
  gridLoss_le_mid : gridLoss ≤ midLoss
  midLoss_pos : 0 < midLoss
  midLoss_le_third : midLoss ≤ 1 / 3
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  scale_small : delta₀ ≤ 1 / 24
  interpolation : ∀ {rho : ℝ}, 0 < rho → rho ≤ delta₀ →
    (100 : ℝ) * Real.rpow rho
        (-gridLoss - midLoss - 1 / (N : ℝ)) ≤
      Real.rpow rho (-localLoss)
  fine : ∀ {rho : ℝ}, 0 < rho → rho ≤ delta₀ →
    (100 : ℝ) * Real.rpow rho
        (-midLoss - 1 / (N : ℝ)) ≤
      Real.rpow rho (-localLoss)

/-- Freeze the preliminary M8 loss schedule and its terminal cutoff before
the runtime coarse family is selected. -/
theorem proposition63_m9_preliminary_m8_schedule
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (producerLoss localLoss : ℝ)
    (hproducerLoss : 0 < producerLoss)
    (hproducerLocal : producerLoss ≤ localLoss)
    (hproducerSigma : producerLoss < sigma / 4) :
    Nonempty (Proposition63M9PreliminaryM8ScheduleData
      sigma producerLoss localLoss) := by
  let gridLoss : ℝ := producerLoss / 8
  let midLoss : ℝ := producerLoss / 4
  have gridLoss_pos : 0 < gridLoss := by
    dsimp only [gridLoss]
    positivity
  have gridLoss_le_half : gridLoss ≤ 1 / 2 := by
    have producerLoss_lt_one : producerLoss < 1 :=
      hproducerSigma.trans (by linarith [critical.sigma_lt_one])
    dsimp only [gridLoss]
    linarith
  have gridLoss_lt_sigma : gridLoss < 2 * sigma / 5 := by
    dsimp only [gridLoss]
    linarith [critical.sigma_pos, hproducerSigma]
  have midLoss_pos : 0 < midLoss := by
    dsimp only [midLoss]
    positivity
  have midLoss_le_third : midLoss ≤ 1 / 3 := by
    have producerLoss_lt_one : producerLoss < 1 :=
      hproducerSigma.trans (by linarith [critical.sigma_lt_one])
    dsimp only [midLoss]
    linarith [hproducerLocal]
  rcases exists_nat_gt (max (9 : ℝ) (1 / gridLoss)) with ⟨N, N_large⟩
  have N_ge_nine : 9 ≤ N := by
    have nine_lt : (9 : ℝ) < N :=
      (le_max_left (9 : ℝ) (1 / gridLoss)).trans_lt N_large
    exact_mod_cast nine_lt.le
  have N_pos : 0 < (N : ℝ) := by positivity
  have one_over_N_lt_grid : (1 : ℝ) / N < gridLoss := by
    have reciprocal_lt : 1 / gridLoss < (N : ℝ) :=
      (le_max_right (9 : ℝ) (1 / gridLoss)).trans_lt N_large
    have scaled : 1 < gridLoss * (N : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ gridLoss_pos).mp reciprocal_lt
    rw [div_lt_iff₀ N_pos]
    simpa [mul_comm] using scaled
  rcases proposition63_lemma412_pre_runtime_schedule sigma critical
      gridLoss gridLoss midLoss N gridLoss_pos gridLoss_le_half
      gridLoss_pos gridLoss_lt_sigma midLoss_pos midLoss_le_third
      N_ge_nine with ⟨schedule⟩
  have interpolationGap :
      -localLoss < -gridLoss - midLoss - 1 / (N : ℝ) := by
    dsimp only [gridLoss, midLoss] at one_over_N_lt_grid ⊢
    linarith [hproducerLocal]
  rcases exists_delta_mul_rpow_le_rpow (100 : ℝ) (by norm_num)
      interpolationGap with
    ⟨interpolationCutoff, interpolationCutoff_pos,
      interpolationCutoff_le_one, interpolationBound⟩
  have fineGap : -localLoss < -midLoss - 1 / (N : ℝ) := by
    dsimp only [gridLoss, midLoss] at one_over_N_lt_grid ⊢
    linarith
  rcases exists_delta_mul_rpow_le_rpow (100 : ℝ) (by norm_num) fineGap with
    ⟨fineCutoff, fineCutoff_pos, fineCutoff_le_one, fineBound⟩
  let delta₀ := min interpolationCutoff (min fineCutoff (1 / 24))
  exact ⟨{
    N := N
    gridLoss := gridLoss
    midLoss := midLoss
    schedule := schedule
    gridLoss_eq := rfl
    midLoss_eq := rfl
    N_ge_nine := N_ge_nine
    one_over_N_lt_grid := one_over_N_lt_grid
    gridLoss_pos := gridLoss_pos
    gridLoss_le_half := gridLoss_le_half
    gridLoss_lt_sigma := gridLoss_lt_sigma
    gridLoss_le_mid := by
      dsimp only [gridLoss, midLoss]
      linarith [hproducerLoss]
    midLoss_pos := midLoss_pos
    midLoss_le_third := midLoss_le_third
    delta₀ := delta₀
    delta₀_pos := lt_min interpolationCutoff_pos <|
      lt_min fineCutoff_pos (by norm_num)
    delta₀_le_one := (min_le_left _ _).trans interpolationCutoff_le_one
    scale_small := (min_le_right _ _).trans <|
      (min_le_right _ _).trans (le_refl _)
    interpolation := by
      intro rho rho_pos rho_le
      exact interpolationBound rho rho_pos (rho_le.trans (min_le_left _ _))
    fine := by
      intro rho rho_pos rho_le
      exact fineBound rho rho_pos <| rho_le.trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  }⟩

/-- Fixed losses before the sampled coarse runtime is exposed.  The first
sticky loss is chosen below every M7 root capacity; the remaining losses are
successive fixed multiples.  Consequently the runtime coarse re-entry can be
retargeted to fixed indices before any current shading is selected. -/
structure Proposition63M9PreliminaryRootLossData
    {sigma producerLoss localLoss : ℝ}
    (preliminary : Proposition63M9PreliminaryM8ScheduleData
      sigma producerLoss localLoss) (nextSourceLoss : ℝ) where
  stickyLoss : ℝ
  ambientSourceLoss : ℝ
  ambientNormalizationLoss : ℝ
  planinessLoss : ℝ
  selectedLoss : ℝ
  currentLoss : ℝ
  densityLoss : ℝ
  weightLoss : ℝ
  reentryLoss : ℝ
  reentryNormalizationLoss : ℝ
  stickyLoss_pos : 0 < stickyLoss
  ambientSourceLoss_eq : ambientSourceLoss = 2 * stickyLoss
  ambientNormalizationLoss_eq : ambientNormalizationLoss = 4 * stickyLoss
  planinessLoss_eq : planinessLoss = 2 * stickyLoss
  selectedLoss_eq : selectedLoss = 8 * stickyLoss
  currentLoss_eq : currentLoss = 16 * stickyLoss
  densityLoss_eq : densityLoss = 32 * stickyLoss
  weightLoss_eq : weightLoss = 64 * stickyLoss
  reentryLoss_eq : reentryLoss = 128 * stickyLoss
  reentryNormalizationLoss_eq : reentryNormalizationLoss = 256 * stickyLoss
  reentry_le_rootSource : ∀ index
    (hindex : index < preliminary.schedule.centralTemplate.count),
      reentryLoss ≤
        (preliminary.schedule.outer.oneQuery index hindex).rootSourceLoss
  reentryNormalization_le_rootNormalization : ∀ index
    (hindex : index < preliminary.schedule.centralTemplate.count),
      reentryNormalizationLoss ≤
        (preliminary.schedule.outer.oneQuery index hindex).backward.rootNormalizationLoss
  reentryNormalization_le_outerInput :
    reentryNormalizationLoss ≤ preliminary.schedule.outer.loss 0
  reentry_lt_grid : reentryLoss < preliminary.gridLoss
  reentryNormalization_lt_producer : reentryNormalizationLoss < producerLoss
  reentryNormalization_lt_nextSource :
    reentryNormalizationLoss < nextSourceLoss
  reentry_lt_nextSource_sixteenth :
    reentryLoss < nextSourceLoss / 16
  currentAbsorption : Proposition63CurrentReentryAbsorptionData
    ambientSourceLoss ambientNormalizationLoss densityLoss currentLoss
    weightLoss reentryLoss
    (proposition63CanonicalNearbyLevelCount ambientNormalizationLoss)
  sampledFirstRichAbsorption : Proposition63CurrentReentryAbsorptionData
    reentryLoss reentryNormalizationLoss (nextSourceLoss / 16)
    (nextSourceLoss / 8) (nextSourceLoss / 2) nextSourceLoss
    (proposition63CanonicalNearbyLevelCount reentryNormalizationLoss)

/-- Choose the complete pre-sampled loss ladder after the preliminary M8
schedule is frozen, but before the runtime scale and family are known. -/
theorem proposition63_m9_preliminary_root_losses
    {sigma producerLoss localLoss : ℝ}
    (preliminary : Proposition63M9PreliminaryM8ScheduleData
      sigma producerLoss localLoss)
    (nextSourceLoss : ℝ) (hnextSourceLoss : 0 < nextSourceLoss) :
    Nonempty (Proposition63M9PreliminaryRootLossData
      preliminary nextSourceLoss) := by
  let Coordinate := Fin preliminary.schedule.centralTemplate.count
  let capacity : Coordinate → ℝ := fun index =>
    min nextSourceLoss <|
      min preliminary.gridLoss <|
      min (preliminary.schedule.outer.loss 0) <|
        min (preliminary.schedule.outer.oneQuery index.val index.isLt).rootSourceLoss
          (Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss
            (preliminary.schedule.outer.oneQuery index.val index.isLt).backward / 2)
  have capacityPos : ∀ index, 0 < capacity index := by
    intro index
    dsimp only [capacity]
    exact lt_min hnextSourceLoss <|
      lt_min preliminary.gridLoss_pos <|
      lt_min (preliminary.schedule.outer.loss_pos 0 (by omega)) <|
      lt_min
        (preliminary.schedule.outer.oneQuery index.val index.isLt
          |>.rootSourceLoss_pos)
        (div_pos
          (preliminary.schedule.outer.oneQuery index.val index.isLt
            |>.rootNormalizationLoss_pos) (by norm_num))
  rcases exists_preliminary_positive_lower_bound capacity capacityPos with
    ⟨capacityFloor, capacityFloorPos, capacityFloorLt⟩
  let stickyLoss := capacityFloor / 8192
  let ambientSourceLoss := 2 * stickyLoss
  let ambientNormalizationLoss := 4 * stickyLoss
  let planinessLoss := 2 * stickyLoss
  let selectedLoss := 8 * stickyLoss
  let currentLoss := 16 * stickyLoss
  let densityLoss := 32 * stickyLoss
  let weightLoss := 64 * stickyLoss
  let reentryLoss := 128 * stickyLoss
  let reentryNormalizationLoss := 256 * stickyLoss
  have stickyLossPos : 0 < stickyLoss := by
    dsimp only [stickyLoss]
    positivity
  have reentryLtCapacity : reentryNormalizationLoss < capacityFloor := by
    dsimp only [reentryNormalizationLoss, stickyLoss]
    linarith [capacityFloorPos]
  have reentryNormalizationLtGrid :
      reentryNormalizationLoss < preliminary.gridLoss := by
    let index : Coordinate := ⟨0, by
      dsimp only [Coordinate, Proposition63Lemma412CentralGridData.count]
      omega⟩
    exact reentryLtCapacity.trans <| (capacityFloorLt index).trans_le <|
      (min_le_right _ _).trans (min_le_left _ _)
  have reentryNormalizationLtNext :
      reentryNormalizationLoss < nextSourceLoss := by
    let index : Coordinate := ⟨0, by
      dsimp only [Coordinate, Proposition63Lemma412CentralGridData.count]
      omega⟩
    exact reentryLtCapacity.trans <| (capacityFloorLt index).trans_le <|
      min_le_left _ _
  have reentryLtNextSixteenth : reentryLoss < nextSourceLoss / 16 := by
    let index : Coordinate := ⟨0, by
      dsimp only [Coordinate, Proposition63Lemma412CentralGridData.count]
      omega⟩
    have floorLtNext : capacityFloor < nextSourceLoss :=
      (capacityFloorLt index).trans_le (min_le_left _ _)
    dsimp only [reentryLoss, stickyLoss]
    linarith
  have ambientSourceDensity : ambientSourceLoss < densityLoss := by
    dsimp only [ambientSourceLoss, densityLoss]
    linarith
  have densityCurrentWeight : densityLoss + currentLoss < weightLoss := by
    dsimp only [densityLoss, currentLoss, weightLoss]
    linarith
  have weightReentry : weightLoss < reentryLoss := by
    dsimp only [weightLoss, reentryLoss]
    linarith
  have regularizationGap :
      0 < reentryLoss - weightLoss - 2 * ambientNormalizationLoss := by
    dsimp only [reentryLoss, weightLoss, ambientNormalizationLoss]
    linarith
  rcases proposition63_current_reentry_absorption ambientSourceLoss
      ambientNormalizationLoss densityLoss currentLoss weightLoss reentryLoss
      (proposition63CanonicalNearbyLevelCount ambientNormalizationLoss)
      ambientSourceDensity (by dsimp only [ambientNormalizationLoss]; positivity)
      densityCurrentWeight weightReentry
      (proposition63CanonicalNearbyLevelCount_pos
        (by dsimp only [ambientNormalizationLoss]; positivity))
      (by dsimp only [reentryLoss]; positivity) regularizationGap with
    ⟨currentAbsorption⟩
  have sampledDensityWeight :
      nextSourceLoss / 16 + nextSourceLoss / 8 < nextSourceLoss / 2 := by
    linarith
  have sampledWeightReentry : nextSourceLoss / 2 < nextSourceLoss := by
    linarith
  have sampledRegularizationGap :
      0 < nextSourceLoss - nextSourceLoss / 2 -
        2 * reentryNormalizationLoss := by
    linarith [reentryNormalizationLtNext]
  rcases proposition63_current_reentry_absorption reentryLoss
      reentryNormalizationLoss (nextSourceLoss / 16)
      (nextSourceLoss / 8) (nextSourceLoss / 2) nextSourceLoss
      (proposition63CanonicalNearbyLevelCount reentryNormalizationLoss)
      reentryLtNextSixteenth
      (by dsimp only [reentryNormalizationLoss, stickyLoss]; positivity)
      sampledDensityWeight sampledWeightReentry
      (proposition63CanonicalNearbyLevelCount_pos
        (by dsimp only [reentryNormalizationLoss, stickyLoss]; positivity))
      hnextSourceLoss sampledRegularizationGap with
    ⟨sampledFirstRichAbsorption⟩
  exact ⟨{
    stickyLoss := stickyLoss
    ambientSourceLoss := ambientSourceLoss
    ambientNormalizationLoss := ambientNormalizationLoss
    planinessLoss := planinessLoss
    selectedLoss := selectedLoss
    currentLoss := currentLoss
    densityLoss := densityLoss
    weightLoss := weightLoss
    reentryLoss := reentryLoss
    reentryNormalizationLoss := reentryNormalizationLoss
    stickyLoss_pos := stickyLossPos
    ambientSourceLoss_eq := rfl
    ambientNormalizationLoss_eq := rfl
    planinessLoss_eq := rfl
    selectedLoss_eq := rfl
    currentLoss_eq := rfl
    densityLoss_eq := rfl
    weightLoss_eq := rfl
    reentryLoss_eq := rfl
    reentryNormalizationLoss_eq := rfl
    reentry_le_rootSource := by
      intro index hindex
      let coordinate : Coordinate := ⟨index, hindex⟩
      have bound := capacityFloorLt coordinate
      have capacityLeSource : capacity coordinate ≤
          (preliminary.schedule.outer.oneQuery index hindex).rootSourceLoss := by
        dsimp only [capacity, coordinate]
        exact (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_left _ _)
      have reentryLtFloor : reentryLoss < capacityFloor := by
        dsimp only [reentryLoss, stickyLoss]
        linarith [capacityFloorPos]
      exact (reentryLtFloor.trans bound).le.trans capacityLeSource
    reentryNormalization_le_rootNormalization := by
      intro index hindex
      let coordinate : Coordinate := ⟨index, hindex⟩
      have bound := capacityFloorLt coordinate
      have capacityLeHalf : capacity coordinate ≤
          Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss
            (preliminary.schedule.outer.oneQuery index hindex).backward / 2 := by
        dsimp only [capacity, coordinate]
        exact (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_right _ _)
      have reentryLeFloor : reentryNormalizationLoss ≤ capacityFloor / 2 := by
        dsimp only [reentryNormalizationLoss, stickyLoss]
        linarith [capacityFloorPos]
      exact reentryLeFloor.trans <| (div_le_div_of_nonneg_right
        (bound.le.trans capacityLeHalf) (by norm_num)).trans <| by
          linarith [
            (preliminary.schedule.outer.oneQuery index hindex)
              |>.rootNormalizationLoss_pos]
    reentryNormalization_le_outerInput := by
      let index : Coordinate := ⟨0, by
        dsimp only [Coordinate, Proposition63Lemma412CentralGridData.count]
        omega⟩
      have bound := capacityFloorLt index
      have capacityLeInput :
          capacity index ≤ preliminary.schedule.outer.loss 0 := by
        dsimp only [capacity, index]
        exact (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
      have reentryLtFloor : reentryNormalizationLoss < capacityFloor := by
        dsimp only [reentryNormalizationLoss, stickyLoss]
        linarith [capacityFloorPos]
      exact (reentryLtFloor.trans bound).le.trans capacityLeInput
    reentry_lt_grid := by
      dsimp only [reentryLoss, reentryNormalizationLoss]
      linarith [reentryNormalizationLtGrid, stickyLossPos]
    reentryNormalization_lt_producer := by
      have producerPos : 0 < producerLoss := by
        have gridPos := preliminary.gridLoss_pos
        rw [preliminary.gridLoss_eq] at gridPos
        linarith [gridPos]
      have gridLtProducer : preliminary.gridLoss < producerLoss := by
        rw [preliminary.gridLoss_eq]
        linarith
      exact reentryNormalizationLtGrid.trans gridLtProducer
    reentryNormalization_lt_nextSource := reentryNormalizationLtNext
    reentry_lt_nextSource_sixteenth := reentryLtNextSixteenth
    currentAbsorption := currentAbsorption
    sampledFirstRichAbsorption := sampledFirstRichAbsorption
  }⟩

/-- Retarget the native coarse re-entry of the preliminary sticky call to the
fixed ambient losses selected by the M8 root ladder.  The sticky call itself
is indexed by `stickyLoss`; hence its native `3 * coarseSourceLoss ≤
stickyLoss` budget has the correct direction for weakening to `2b / 4b`.
No family, shading, frame, or ordinary provenance is changed. -/
noncomputable def Proposition63M9PreliminaryRootLossData.ambientReentry
    {sigma producerLoss localLoss nextSourceLoss delta : ℝ}
    {preliminary : Proposition63M9PreliminaryM8ScheduleData
      sigma producerLoss localLoss}
    (losses : Proposition63M9PreliminaryRootLossData
      preliminary nextSourceLoss)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {requested : WZ2PaperRequestedScale delta}
    {normalizationExponent logExponent : ℕ}
    (sticky : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := losses.stickyLoss)
      sourceShading requested normalizationExponent logExponent) :
    PureWZ2PropStickyReentryData
      (sigma := sigma) sticky.data.croppedCoarseShading normalizationExponent
      losses.ambientSourceLoss losses.ambientNormalizationLoss :=
  sticky.coarseReentry.mono_losses
    (by
      rw [losses.ambientSourceLoss_eq]
      linarith [sticky.coarseSourceLoss_budget,
        sticky.coarseSourceLoss_pos, losses.stickyLoss_pos])
    (by
      rw [losses.ambientNormalizationLoss_eq,
        sticky.coarseNormalizationLoss_eq]
      nlinarith [sticky.coarseSourceLoss_budget,
        sticky.coarseSourceLoss_pos, losses.stickyLoss_pos])
    (by
      rw [losses.ambientSourceLoss_eq]
      linarith [losses.stickyLoss_pos])
    (by
      rw [losses.ambientNormalizationLoss_eq]
      linarith [losses.stickyLoss_pos])
    (by
      rw [losses.ambientSourceLoss_eq,
        losses.ambientNormalizationLoss_eq]
      linarith)

/-- Strict coarse axial provenance is unchanged by the loss-only retargeting
above. -/
theorem Proposition63M9PreliminaryRootLossData.ambientReentry_axialWindow
    {sigma producerLoss localLoss nextSourceLoss delta : ℝ}
    {preliminary : Proposition63M9PreliminaryM8ScheduleData
      sigma producerLoss localLoss}
    (losses : Proposition63M9PreliminaryRootLossData
      preliminary nextSourceLoss)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {requested : WZ2PaperRequestedScale delta}
    {normalizationExponent logExponent : ℕ}
    (sticky : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := losses.stickyLoss)
      sourceShading requested normalizationExponent logExponent)
    (coarseAxialEighth : ∀ tube point,
      point ∈ sticky.coarseReentry.geometry.frame ''
          sticky.coarseReentry.geometry.ordinaryRefined.carrier tube →
        |point (2 : Fin 3)| ≤ 1 / 8) :
    ∀ tube point,
      point ∈ (losses.ambientReentry sticky).geometry.frame ''
          (losses.ambientReentry sticky).geometry.ordinaryRefined.carrier tube →
        |point (2 : Fin 3)| ≤ 1 / 8 := by
  simpa only [Proposition63M9PreliminaryRootLossData.ambientReentry,
    PureWZ2PropStickyReentryData.mono_losses] using coarseAxialEighth

end Kakeya.Assouad.PureWZ2

end
