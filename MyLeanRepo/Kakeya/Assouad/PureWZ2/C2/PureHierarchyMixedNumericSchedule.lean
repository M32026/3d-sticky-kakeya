import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ConditionalAssembly
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26DeltaBudget
import MyLeanRepo.Kakeya.Assouad.WZ1.ActiveCostBoundsHelpers

/-!
# Uniform numerical schedule for the mixed R3 hierarchy

This file chooses every scalar threshold after `N`, `sigma`, and the three
losses have been fixed, but before the runtime mixed hierarchy is known.
The resulting receipt is indexed by that actual construction.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Convert the scalar level-zero absorption into the `ENNReal` inequality
used by mixed popularity. -/
lemma pureWZ2_mixed_level_zero_of_scalar
    {N : ℕ} {delta sigma finalLoss hierarchyLoss : ℝ}
    (hdelta : 0 < delta)
    (hscalar :
      3840 * Real.rpow delta
        (hierarchyLoss / (N : ℝ) - finalLoss -
          hierarchyLoss / (4 * (N : ℝ))) < 1) :
    pureWZ2HierarchySlabConstant delta sigma finalLoss *
        ENNReal.ofReal
          (12 * Real.rpow delta (hierarchyLoss / (N : ℝ))) <
      Kakeya.realRpowENN delta
        (sigma + hierarchyLoss / (4 * (N : ℝ))) := by
  have hreal :
      3840 * Real.rpow delta
          (sigma + hierarchyLoss / (N : ℝ) - finalLoss) <
        Real.rpow delta
          (sigma + hierarchyLoss / (4 * (N : ℝ))) := by
    let base := sigma + hierarchyLoss / (4 * (N : ℝ))
    let gap := hierarchyLoss / (N : ℝ) - finalLoss -
      hierarchyLoss / (4 * (N : ℝ))
    have hsplit :
        Real.rpow delta (sigma + hierarchyLoss / (N : ℝ) - finalLoss) =
          Real.rpow delta base * Real.rpow delta gap := by
      calc
        Real.rpow delta (sigma + hierarchyLoss / (N : ℝ) - finalLoss) =
            Real.rpow delta (base + gap) := by
              congr 1
              dsimp only [base, gap]
              ring
        _ = Real.rpow delta base * Real.rpow delta gap :=
          Real.rpow_add hdelta _ _
    rw [hsplit]
    have hbase : 0 < Real.rpow delta base :=
      Real.rpow_pos_of_pos hdelta _
    nlinarith
  have hlhs :
      pureWZ2HierarchySlabConstant delta sigma finalLoss *
          ENNReal.ofReal
            (12 * Real.rpow delta (hierarchyLoss / (N : ℝ))) =
        (3840 : ENNReal) * Kakeya.realRpowENN delta
          (sigma + hierarchyLoss / (N : ℝ) - finalLoss) := by
    rw [show sigma + hierarchyLoss / (N : ℝ) - finalLoss =
      (-finalLoss) + sigma + hierarchyLoss / (N : ℝ) by ring]
    rw [realRpowENN_add hdelta, realRpowENN_add hdelta]
    unfold pureWZ2HierarchySlabConstant
    simp only [Kakeya.realRpowENN]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12)]
    norm_num
    ring
  rw [hlhs]
  unfold Kakeya.realRpowENN
  rw [← ENNReal.ofReal_ofNat 3840]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3840)]
  exact (ENNReal.ofReal_lt_ofReal_iff
    (Real.rpow_pos_of_pos hdelta _)).mpr hreal

/-- The geometric-series estimate plus the actual mixed volume lower bound
pay the complete popularity-removal budget. -/
lemma pureWZ2_mixed_removed_of_scalar
    {N : ℕ} {delta sigma finalLoss hierarchyLoss : ℝ}
    (hN : 0 < N) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hhierarchy : 0 < hierarchyLoss)
    (hgeometric :
      Real.rpow delta (hierarchyLoss / (N : ℝ)) < 1 / 9)
    (hscalar :
      12960 * Real.rpow delta
        (hierarchyLoss / (N : ℝ) - 2 * finalLoss) ≤ 1)
    {inputLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (mixed : PureWZ2MixedRawHierarchyData
      source finalLoss hierarchyLoss)
    (hlevels : mixed.levelCount = N) :
    pureWZ2HierarchySlabConstant delta sigma finalLoss *
        ENNReal.ofReal
          (12 * ∑ level : Fin mixed.levelCount,
            Real.rpow
              (wz1Corollary26Scale delta mixed.levelCount level)
              hierarchyLoss) ≤
      ENNReal.ofReal (1 / 3) * MeasureTheory.volume mixed.shading.union := by
  have hseries :=
    PureHierarchyGeneric.geometric_series_total_volume_bound
      hN hdelta hdeltaOne hhierarchy hgeometric
  have hseries' :
      ∑ level : Fin mixed.levelCount,
          Real.rpow
            (wz1Corollary26Scale delta mixed.levelCount level)
            hierarchyLoss ≤
        (9 / 8 : ℝ) *
          Real.rpow delta (hierarchyLoss / (N : ℝ)) := by
    rw [hlevels]
    exact hseries.le
  have hleft :
      pureWZ2HierarchySlabConstant delta sigma finalLoss *
          ENNReal.ofReal
            (12 * ∑ level : Fin mixed.levelCount,
              Real.rpow
                (wz1Corollary26Scale delta mixed.levelCount level)
                hierarchyLoss) ≤
        (4320 : ENNReal) * Kakeya.realRpowENN delta
          (sigma - finalLoss + hierarchyLoss / (N : ℝ)) := by
    have hsumCast :
        ENNReal.ofReal
            (12 * ∑ level : Fin mixed.levelCount,
              Real.rpow
                (wz1Corollary26Scale delta mixed.levelCount level)
                hierarchyLoss) ≤
          ENNReal.ofReal
            (12 * ((9 / 8 : ℝ) *
              Real.rpow delta (hierarchyLoss / (N : ℝ)))) :=
      ENNReal.ofReal_mono (mul_le_mul_of_nonneg_left hseries' (by norm_num))
    calc
      pureWZ2HierarchySlabConstant delta sigma finalLoss *
          ENNReal.ofReal
            (12 * ∑ level : Fin mixed.levelCount,
              Real.rpow
                (wz1Corollary26Scale delta mixed.levelCount level)
                hierarchyLoss) ≤
          pureWZ2HierarchySlabConstant delta sigma finalLoss *
            ENNReal.ofReal
              (12 * ((9 / 8 : ℝ) *
                Real.rpow delta (hierarchyLoss / (N : ℝ)))) := by gcongr
      _ ≤ (4320 : ENNReal) * Kakeya.realRpowENN delta
          (sigma - finalLoss + hierarchyLoss / (N : ℝ)) := by
        rw [show sigma - finalLoss + hierarchyLoss / (N : ℝ) =
          (-finalLoss) + sigma + hierarchyLoss / (N : ℝ) by ring]
        rw [realRpowENN_add hdelta, realRpowENN_add hdelta]
        unfold pureWZ2HierarchySlabConstant
        simp only [Kakeya.realRpowENN]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12)]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9 / 8)]
        have hcoefficient :
            (32 : ENNReal) * 10 *
                (12 * ENNReal.ofReal (9 / 8 : ℝ)) ≤ 4320 := by
          rw [← ENNReal.ofReal_ofNat 4320,
            ← ENNReal.ofReal_ofNat 32, ← ENNReal.ofReal_ofNat 10,
            ← ENNReal.ofReal_ofNat 12,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12)]
          rw [mul_assoc, ← ENNReal.ofReal_mul
            (by norm_num : (0 : ℝ) ≤ 10)]
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32)]
          exact ENNReal.ofReal_mono (by norm_num)
        calc
          32 * (10 * ENNReal.ofReal (Real.rpow delta (-finalLoss))) *
                ENNReal.ofReal (Real.rpow delta sigma) *
                (ENNReal.ofReal 12 *
                  (ENNReal.ofReal (9 / 8) *
                    ENNReal.ofReal
                      (Real.rpow delta (hierarchyLoss / (N : ℝ))))) =
              (32 * 10 * (12 * ENNReal.ofReal (9 / 8))) *
                (ENNReal.ofReal (Real.rpow delta (-finalLoss)) *
                  ENNReal.ofReal (Real.rpow delta sigma) *
                  ENNReal.ofReal
                    (Real.rpow delta (hierarchyLoss / (N : ℝ)))) := by
                norm_num only [ENNReal.ofReal_ofNat]
                ring
          _ ≤ 4320 *
                (ENNReal.ofReal (Real.rpow delta (-finalLoss)) *
                  ENNReal.ofReal (Real.rpow delta sigma) *
                  ENNReal.ofReal
                    (Real.rpow delta (hierarchyLoss / (N : ℝ)))) := by gcongr
  have hscalarENN :
      (12960 : ENNReal) * Kakeya.realRpowENN delta
          (hierarchyLoss / (N : ℝ) - 2 * finalLoss) ≤ 1 := by
    unfold Kakeya.realRpowENN
    rw [← ENNReal.ofReal_ofNat 12960]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12960)]
    simpa using ENNReal.ofReal_mono hscalar
  have htarget :
      (4320 : ENNReal) * Kakeya.realRpowENN delta
          (sigma - finalLoss + hierarchyLoss / (N : ℝ)) ≤
        ENNReal.ofReal (1 / 3) *
          Kakeya.realRpowENN delta (sigma + finalLoss) := by
    rw [show sigma - finalLoss + hierarchyLoss / (N : ℝ) =
      (sigma + finalLoss) +
        (hierarchyLoss / (N : ℝ) - 2 * finalLoss) by ring]
    rw [realRpowENN_add hdelta]
    have hthird :
        (4320 : ENNReal) ≤ ENNReal.ofReal (1 / 3) * 12960 := by
      rw [← ENNReal.ofReal_ofNat 4320, ← ENNReal.ofReal_ofNat 12960]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3)]
      exact ENNReal.ofReal_mono (by norm_num)
    calc
      (4320 : ENNReal) *
          (Kakeya.realRpowENN delta (sigma + finalLoss) *
            Kakeya.realRpowENN delta
              (hierarchyLoss / (N : ℝ) - 2 * finalLoss)) ≤
          ENNReal.ofReal (1 / 3) *
            ((12960 : ENNReal) * Kakeya.realRpowENN delta
              (hierarchyLoss / (N : ℝ) - 2 * finalLoss)) *
            Kakeya.realRpowENN delta (sigma + finalLoss) := by
              calc
                _ ≤ (ENNReal.ofReal (1 / 3) * 12960) *
                    (Kakeya.realRpowENN delta (sigma + finalLoss) *
                      Kakeya.realRpowENN delta
                        (hierarchyLoss / (N : ℝ) - 2 * finalLoss)) := by gcongr
                _ = _ := by ring
      _ ≤ ENNReal.ofReal (1 / 3) * 1 *
          Kakeya.realRpowENN delta (sigma + finalLoss) := by gcongr
      _ = ENNReal.ofReal (1 / 3) *
          Kakeya.realRpowENN delta (sigma + finalLoss) := by ring
  exact hleft.trans <| htarget.trans <|
    mul_le_mul_left' mixed.volume_lower (ENNReal.ofReal (1 / 3))

/-- The positive final-loss gap makes the final retained-volume comparison
strict at every sufficiently small scale. -/
lemma pureWZ2_mixed_final_volume_of_half
    {delta sigma finalLoss hierarchyLoss : ℝ}
    (hdelta : 0 < delta)
    (hhalf : Real.rpow delta (hierarchyLoss - finalLoss) ≤ 1 / 2) :
    Kakeya.realRpowENN delta (sigma + hierarchyLoss) <
      ENNReal.ofReal (2 / 3) *
        Kakeya.realRpowENN delta (sigma + finalLoss) := by
  rw [show sigma + hierarchyLoss =
    (sigma + finalLoss) + (hierarchyLoss - finalLoss) by ring]
  rw [realRpowENN_add hdelta]
  have hpower :
      Kakeya.realRpowENN delta (hierarchyLoss - finalLoss) ≤
        ENNReal.ofReal (1 / 2) := by
    exact ENNReal.ofReal_mono hhalf
  have hhalfThird : ENNReal.ofReal (1 / 2) < ENNReal.ofReal (2 / 3) := by
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  calc
    Kakeya.realRpowENN delta (sigma + finalLoss) *
        Kakeya.realRpowENN delta (hierarchyLoss - finalLoss) ≤
      Kakeya.realRpowENN delta (sigma + finalLoss) *
        ENNReal.ofReal (1 / 2) := by gcongr
    _ < Kakeya.realRpowENN delta (sigma + finalLoss) *
        ENNReal.ofReal (2 / 3) := by
      gcongr
      · exact (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos hdelta _)).ne'
      · simp [Kakeya.realRpowENN]
    _ = ENNReal.ofReal (2 / 3) *
        Kakeya.realRpowENN delta (sigma + finalLoss) := by ring

/-- A single source-scale threshold selected before any runtime hierarchy. -/
structure PureWZ2MixedHierarchyNumericSchedule
    (N : ℕ) (sigma finalLoss hierarchyLoss workLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  produce :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ construction : PureWZ2MixedHierarchyConstructionData
        sigma finalLoss hierarchyLoss delta N,
        PureWZ2MixedHierarchyBudgetReceipt construction workLoss

/-- Choose the complete R3 numerical schedule after the finite depth and all
losses are fixed.  No runtime family, shading, or hierarchy occurs in the
choice of `delta₀`. -/
theorem pureWZ2_mixed_hierarchy_numeric_schedule
    {N : ℕ} {sigma finalLoss hierarchyLoss workLoss : ℝ}
    (hN : 4 ≤ N)
    (hfinal : 0 < finalLoss)
    (hhierarchy : 0 < hierarchyLoss)
    (hhierarchyWork : hierarchyLoss ≤ workLoss)
    (hhierarchyUpper : hierarchyLoss ≤ 1 / (N : ℝ))
    (hfinalLevelZero : finalLoss ≤ hierarchyLoss / (4 * (N : ℝ))) :
    Nonempty (PureWZ2MixedHierarchyNumericSchedule
      N sigma finalLoss hierarchyLoss workLoss) := by
  have hNnat : 0 < N := by omega
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNnat
  have hfourN : (1 : ℝ) ≤ 4 * (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNnat
    nlinarith
  have hfourNStrict : (1 : ℝ) < 4 * (N : ℝ) := by
    have hNfour : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have hfinalHierarchy : finalLoss ≤ hierarchyLoss := by
    have hdiv : hierarchyLoss / (4 * (N : ℝ)) ≤ hierarchyLoss := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (N : ℝ))).2
      nlinarith
    exact hfinalLevelZero.trans hdiv
  have hfinalGap : 0 < hierarchyLoss - finalLoss := by
    have hstrict : hierarchyLoss / (4 * (N : ℝ)) < hierarchyLoss := by
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * (N : ℝ))).2
      nlinarith
    linarith
  have hlevelGap :
      0 < 3 * hierarchyLoss / (4 * (N : ℝ)) - finalLoss := by
    have hquarterPos : 0 < hierarchyLoss / (4 * (N : ℝ)) := by positivity
    have hthree : 3 * hierarchyLoss / (4 * (N : ℝ)) =
        3 * (hierarchyLoss / (4 * (N : ℝ))) := by ring
    rw [hthree]
    linarith
  have hremovedGap :
      0 < hierarchyLoss / (N : ℝ) - 2 * finalLoss := by
    have hquarterPos : 0 < hierarchyLoss / (4 * (N : ℝ)) := by positivity
    have hidentity : hierarchyLoss / (N : ℝ) =
        4 * (hierarchyLoss / (4 * (N : ℝ))) := by field_simp
    rw [hidentity]
    linarith
  have hgeometricExp : 0 < hierarchyLoss / (N : ℝ) := by positivity
  rcases exists_delta_rpow_le_single
      (hierarchyLoss / (N : ℝ)) (1 / 10) hgeometricExp
      (by norm_num) (by norm_num) with
    ⟨geometricDelta₀, hgeometricDelta₀, hgeometricDelta₀One, hgeometric⟩
  rcases exists_delta_mul_rpow_le_rpow 7680 (by norm_num) hlevelGap with
    ⟨levelDelta₀, hlevelDelta₀, hlevelDelta₀One, hlevel⟩
  rcases exists_delta_mul_rpow_le_rpow 12960 (by norm_num) hremovedGap with
    ⟨removedDelta₀, hremovedDelta₀, hremovedDelta₀One, hremoved⟩
  rcases exists_delta_rpow_le_single
      (hierarchyLoss - finalLoss) (1 / 2) hfinalGap
      (by norm_num) (by norm_num) with
    ⟨finalDelta₀, hfinalDelta₀, hfinalDelta₀One, hfinalSmall⟩
  rcases exists_delta₀_rpow_neg ((N : ℝ) * 136) (by positivity)
      hierarchyLoss hhierarchy with
    ⟨costDelta₀, hcostDelta₀, hcostDelta₀One, hcost⟩
  rcases pureWZ2Proposition64_hierarchyScaleThreshold hN with
    ⟨hierarchyThreshold⟩
  let delta₀ := min (1 / 2 : ℝ) <|
    min geometricDelta₀ <| min levelDelta₀ <| min removedDelta₀ <|
      min finalDelta₀ <| min costDelta₀ hierarchyThreshold.delta₀
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    exact lt_min (by norm_num) <|
      lt_min hgeometricDelta₀ <| lt_min hlevelDelta₀ <|
        lt_min hremovedDelta₀ <| lt_min hfinalDelta₀ <|
          lt_min hcostDelta₀ hierarchyThreshold.delta₀_pos
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := hdelta₀
    delta₀_le_one := (min_le_left _ _).trans (by norm_num)
    produce := ?_ }⟩
  intro delta hdelta hdeltaSmall construction
  have hdeltaHalf : delta ≤ 1 / 2 :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaStrict : delta < 1 := by linarith
  have hrest := hdeltaSmall.trans (min_le_right _ _)
  have hdeltaGeometric : delta ≤ geometricDelta₀ :=
    hrest.trans (min_le_left _ _)
  have hrest := hrest.trans (min_le_right _ _)
  have hdeltaLevel : delta ≤ levelDelta₀ :=
    hrest.trans (min_le_left _ _)
  have hrest := hrest.trans (min_le_right _ _)
  have hdeltaRemoved : delta ≤ removedDelta₀ :=
    hrest.trans (min_le_left _ _)
  have hrest := hrest.trans (min_le_right _ _)
  have hdeltaFinal : delta ≤ finalDelta₀ :=
    hrest.trans (min_le_left _ _)
  have hrest := hrest.trans (min_le_right _ _)
  have hdeltaCost : delta ≤ costDelta₀ :=
    hrest.trans (min_le_left _ _)
  have hdeltaHierarchy : delta ≤ hierarchyThreshold.delta₀ :=
    hrest.trans (min_le_right _ _)
  have hgeometric' :
      Real.rpow delta (hierarchyLoss / (N : ℝ)) < 1 / 9 :=
    (hgeometric delta hdelta hdeltaGeometric).trans_lt (by norm_num)
  have hlevelRaw :
      7680 * Real.rpow delta
          (3 * hierarchyLoss / (4 * (N : ℝ)) - finalLoss) ≤ 1 := by
    simpa [Real.rpow_zero] using hlevel delta hdelta hdeltaLevel
  have hlevelScalar :
      3840 * Real.rpow delta
          (hierarchyLoss / (N : ℝ) - finalLoss -
            hierarchyLoss / (4 * (N : ℝ))) < 1 := by
    have hpower : 0 < Real.rpow delta
        (3 * hierarchyLoss / (4 * (N : ℝ)) - finalLoss) :=
      Real.rpow_pos_of_pos hdelta _
    have hexponent : hierarchyLoss / (N : ℝ) - finalLoss -
        hierarchyLoss / (4 * (N : ℝ)) =
          3 * hierarchyLoss / (4 * (N : ℝ)) - finalLoss := by ring
    rw [hexponent]
    nlinarith
  have hremovedScalar :
      12960 * Real.rpow delta
          (hierarchyLoss / (N : ℝ) - 2 * finalLoss) ≤ 1 := by
    simpa [Real.rpow_zero] using
      hremoved delta hdelta hdeltaRemoved
  have hfinalSmall' := hfinalSmall delta hdelta hdeltaFinal
  have hcost' := hcost delta hdelta hdeltaCost
  let runtimeThresholdData :
      { threshold : PureWZ2Proposition64HierarchyScaleThreshold
          construction.mixed.levelCount // delta ≤ threshold.delta₀ } := by
    rw [construction.levelCount_eq]
    exact ⟨hierarchyThreshold, hdeltaHierarchy⟩
  let runtimeThreshold := runtimeThresholdData.1
  have hdeltaRuntime : delta ≤ runtimeThreshold.delta₀ :=
    runtimeThresholdData.2
  refine {
    hierarchyLoss_le_workLoss := hhierarchyWork
    finalLoss_le_hierarchy := hfinalHierarchy
    finalLoss_le_level_zero := ?_
    delta_strict := hdeltaStrict
    geometric := ?_
    level_zero := ?_
    removed := ?_
    final_volume := pureWZ2_mixed_final_volume_of_half hdelta hfinalSmall'
    hierarchyLoss_upper := ?_
    cost_absorb := ?_
    threshold := runtimeThreshold
    source_small := ?_ }
  · simpa [construction.levelCount_eq] using hfinalLevelZero
  · simpa [construction.levelCount_eq] using hgeometric'
  · simpa [construction.levelCount_eq] using
      pureWZ2_mixed_level_zero_of_scalar hdelta hlevelScalar
  · exact pureWZ2_mixed_removed_of_scalar hNnat hdelta hdeltaStrict
      hhierarchy hgeometric' hremovedScalar construction.mixed
        construction.levelCount_eq
  · simpa [construction.levelCount_eq] using hhierarchyUpper
  · simpa [construction.levelCount_eq] using hcost'
  · change delta ≤ runtimeThreshold.delta₀
    exact hdeltaRuntime

namespace PureWZ2MixedHierarchyNumericSchedule

/-- Execute the closed R3 hierarchy tail using the receipt produced by this
pre-runtime numerical schedule. -/
theorem toBudgetedHierarchyOutput
    {N : ℕ} {sigma finalLoss hierarchyLoss workLoss delta : ℝ}
    (schedule : PureWZ2MixedHierarchyNumericSchedule
      N sigma finalLoss hierarchyLoss workLoss)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ schedule.delta₀)
    (construction : PureWZ2MixedHierarchyConstructionData
      sigma finalLoss hierarchyLoss delta N)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hhierarchy : 0 < hierarchyLoss) :
    Nonempty (PureWZ2BudgetedHierarchyOutput sigma workLoss delta) :=
  construction.toBudgetedHierarchyOutput hbridge hsigma hsigmaOne
    hhierarchy (schedule.produce hdelta hdeltaSmall construction)

end PureWZ2MixedHierarchyNumericSchedule

end Kakeya.Assouad

end
