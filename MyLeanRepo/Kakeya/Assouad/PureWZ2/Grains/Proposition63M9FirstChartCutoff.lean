import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PowerScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9FirstChartNearbyAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RootNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers

/-!
# The pre-runtime cutoff for the first Proposition 6.3 chart

The small parameter consumed by the first pre-Lemma-4.3 regularization is
the chart ratio `q = delta / firstScale`.  It is not an outer requested
scale.  This file first freezes the finite nearby-scale absorption at `q`,
then pulls its cutoff back to the root scale using the paper lower bound
`delta^(1 - rootExponent) <= firstScale`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- The elementary power pullback behind the first-chart cutoff. -/
theorem proposition63_firstChart_ratio_le_root_power
    {delta firstScale rootExponent : ℝ}
    (delta_pos : 0 < delta)
    (firstScale_pos : 0 < firstScale)
    (firstScale_lower :
      Real.rpow delta (1 - rootExponent) ≤ firstScale) :
    delta / firstScale ≤ Real.rpow delta rootExponent := by
  rw [div_le_iff₀ firstScale_pos]
  calc
    delta = Real.rpow delta 1 := (Real.rpow_one delta).symm
    _ = Real.rpow delta ((1 - rootExponent) + rootExponent) := by
      congr 1
      ring
    _ = Real.rpow delta (1 - rootExponent) *
        Real.rpow delta rootExponent := by
      exact Real.rpow_add delta_pos _ _
    _ ≤ firstScale * Real.rpow delta rootExponent := by
      exact mul_le_mul_of_nonneg_right firstScale_lower
        (Real.rpow_nonneg delta_pos.le rootExponent)
    _ = Real.rpow delta rootExponent * firstScale := mul_comm _ _

/--
The family-free numerical package used before the first chart is known.
`ratioCutoff` is the cutoff returned by finite nearby regularization.  The
separate `rootCutoff` is chosen only so that the paper's lower bound on
`firstScale` implies `delta / firstScale ≤ ratioCutoff`.
-/
structure Proposition63M9FirstChartNearbyCutoffData
    (targetLoss : ℝ) where
  nearbyInputLoss : ℝ
  ratioCutoff : ℝ
  levelCount : ℕ
  nearbyInputLoss_pos : 0 < nearbyInputLoss
  three_nearbyInputLoss_lt : 3 * nearbyInputLoss < targetLoss
  levelCount_pos : 0 < levelCount
  ratioCutoff_pos : 0 < ratioCutoff
  ratioCutoff_le : ratioCutoff ≤ 1 / 24
  nearby_absorption : ∀ q : ℝ, 0 < q → q ≤ ratioCutoff →
      ∀ cardinality : ℕ,
      (cardinality : ℝ) ≤
        (259 : ℝ) ^ 3 * (67 : ℝ) ^ 3 * Real.rpow q (-9 : ℝ) →
      let ambientConstant := Kakeya.realRpowENN q (-nearbyInputLoss)
      let outputConstant := Kakeya.realRpowENN q (-targetLoss)
      let density := Kakeya.realRpowENN q nearbyInputLoss
      let degreeConstant :=
        16 * ((levelCount + 1 : ℕ) : ENNReal) *
          (Nat.log 2 (2 * cardinality) + 1 : ENNReal) ^ (levelCount + 1)
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * cardinality) + 1 : ENNReal) ^ (levelCount + 2)
      let weight := (1 / 2 : ENNReal) * density
      let cardinalityLoss :=
        (2 * regularizationLoss) *
          (55296 * Kakeya.deltaTubeVolume 1)
      2 < ambientConstant ∧
      ambientConstant ≠ ⊤ ∧
      density ≠ 0 ∧
      density ≠ ⊤ ∧
      ENNReal.ofReal (1 / q) ≤ ambientConstant ^ levelCount ∧
      ambientConstant * ambientConstant ≤ outputConstant ∧
      max degreeConstant
          ((weight⁻¹ *
              (ambientConstant * cardinalityLoss * degreeConstant)) *
            ambientConstant) ≤ outputConstant

/-- Bind the already frozen nearby-scale cutoff to the root exponent chosen
after its input loss has been exposed. -/
structure Proposition63M9FirstChartCutoffData
    (targetLoss rootExponent : ℝ)
    extends Proposition63M9FirstChartNearbyCutoffData targetLoss where
  scaleCutoff : ℝ
  scaleCutoff_pos : 0 < scaleCutoff
  scaleCutoff_le_one : scaleCutoff ≤ 1
  scale_absorption : ∀ {q : ℝ}, 0 < q → q ≤ scaleCutoff →
    (96 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN q (targetLoss - nearbyInputLoss) ≤ 1 ∧
      ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN q (targetLoss - nearbyInputLoss) ≤
        (73 / 100 : ENNReal)
  rootCutoff : ℝ
  rootCutoff_pos : 0 < rootCutoff
  rootCutoff_le_one : rootCutoff ≤ 1
  root_power_le_ratioCutoff : ∀ {delta : ℝ},
    0 < delta → delta ≤ rootCutoff →
      Real.rpow delta rootExponent ≤ ratioCutoff
  root_power_le_scaleCutoff : ∀ {delta : ℝ},
    0 < delta → delta ≤ rootCutoff →
      Real.rpow delta rootExponent ≤ scaleCutoff

/-- Freeze finite nearby regularization before choosing the source loss. -/
theorem proposition63_m9_firstChart_nearby_cutoff
    {targetLoss : ℝ}
    (targetLoss_pos : 0 < targetLoss)
    (targetLoss_le_one : targetLoss ≤ 1) :
    Nonempty (Proposition63M9FirstChartNearbyCutoffData targetLoss) := by
  rcases proposition63_m9_firstChart_family_free_nearby_absorption
      targetLoss_pos targetLoss_le_one with
    ⟨nearbyInputLoss, ratioCutoff, levelCount,
      nearbyInputLossPos, threeInputLt, levelCountPos, ratioCutoffPos,
      ratioCutoffLe, nearbyAbsorption⟩
  exact ⟨{
    nearbyInputLoss := nearbyInputLoss
    ratioCutoff := ratioCutoff
    levelCount := levelCount
    nearbyInputLoss_pos := nearbyInputLossPos
    three_nearbyInputLoss_lt := threeInputLt
    levelCount_pos := levelCountPos
    ratioCutoff_pos := ratioCutoffPos
    ratioCutoff_le := ratioCutoffLe
    nearby_absorption := nearbyAbsorption }⟩

/-- After the chart source loss has been chosen below `nearbyInputLoss`,
pull the ratio cutoff back to the outer root scale. -/
theorem Proposition63M9FirstChartNearbyCutoffData.bindRootExponent
    {targetLoss rootExponent : ℝ}
    (nearby : Proposition63M9FirstChartNearbyCutoffData targetLoss)
    (rootExponent_pos : 0 < rootExponent) :
    ∃ cutoff : Proposition63M9FirstChartCutoffData
        targetLoss rootExponent,
      cutoff.toProposition63M9FirstChartNearbyCutoffData = nearby := by
  have lossGap : nearby.nearbyInputLoss < targetLoss := by
    linarith [nearby.nearbyInputLoss_pos,
      nearby.three_nearbyInputLoss_lt]
  rcases exists_delta_proposition63CanonicalReentryWeight_scale_bounds
      lossGap with
    ⟨scaleCutoff, scaleCutoffPos, scaleCutoffOne, scaleAbsorption⟩
  let ratioRootTarget := min nearby.ratioCutoff scaleCutoff
  have ratioRootTargetPos : 0 < ratioRootTarget :=
    lt_min nearby.ratioCutoff_pos scaleCutoffPos
  rcases pure_wz2_exists_delta₀_rpow_le
      ratioRootTargetPos rootExponent_pos with
    ⟨rootCutoff, rootCutoffPos, rootCutoffOne, rootPower⟩
  refine ⟨{
    toProposition63M9FirstChartNearbyCutoffData := nearby
    scaleCutoff := scaleCutoff
    scaleCutoff_pos := scaleCutoffPos
    scaleCutoff_le_one := scaleCutoffOne
    scale_absorption := fun {q} qPos qLe =>
      scaleAbsorption q qPos qLe
    rootCutoff := rootCutoff
    rootCutoff_pos := rootCutoffPos
    rootCutoff_le_one := rootCutoffOne
    root_power_le_ratioCutoff := fun {delta} deltaPos deltaLe =>
      (rootPower delta deltaPos deltaLe).trans (min_le_left _ _)
    root_power_le_scaleCutoff := fun {delta} deltaPos deltaLe =>
      (rootPower delta deltaPos deltaLe).trans (min_le_right _ _)
  }, rfl⟩

/-- Backwards-compatible one-shot constructor. -/
theorem proposition63_m9_firstChart_cutoff
    {targetLoss rootExponent : ℝ}
    (targetLoss_pos : 0 < targetLoss)
    (targetLoss_le_one : targetLoss ≤ 1)
    (rootExponent_pos : 0 < rootExponent) :
    Nonempty (Proposition63M9FirstChartCutoffData
      targetLoss rootExponent) := by
  rcases proposition63_m9_firstChart_nearby_cutoff targetLoss_pos
      targetLoss_le_one with ⟨nearby⟩
  rcases nearby.bindRootExponent rootExponent_pos with ⟨cutoff, _⟩
  exact ⟨cutoff⟩

/-- The explicit root-to-chart pullback.  Notice that the conclusion is a
bound on `delta / firstScale`; no outer `rho` cutoff occurs here. -/
theorem Proposition63M9FirstChartCutoffData.ratio_le_cutoff
    {targetLoss rootExponent delta : ℝ}
    (cutoff : Proposition63M9FirstChartCutoffData
      targetLoss rootExponent)
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ cutoff.rootCutoff)
    (firstScale : WZ2PaperRequestedScale delta)
    (firstScale_lower :
      Real.rpow delta (1 - rootExponent) ≤ firstScale.1) :
    delta / firstScale.1 ≤ cutoff.ratioCutoff := by
  exact (proposition63_firstChart_ratio_le_root_power delta_pos
    (delta_pos.trans_le firstScale.2.1) firstScale_lower).trans
      (cutoff.root_power_le_ratioCutoff delta_pos delta_le)

/-- The chart ratio is positive, as required by every finite-nearby producer. -/
theorem Proposition63M9FirstChartCutoffData.ratio_pos
    {targetLoss rootExponent delta : ℝ}
    (_cutoff : Proposition63M9FirstChartCutoffData
      targetLoss rootExponent)
    (delta_pos : 0 < delta)
    (firstScale : WZ2PaperRequestedScale delta) :
    0 < delta / firstScale.1 :=
  div_pos delta_pos (delta_pos.trans_le firstScale.2.1)

/-- Apply the frozen finite-nearby absorption at the actual first-chart
ratio.  This is the numerical input used by
`proposition63_preLemma43_dense_root_of_firstChart`. -/
theorem Proposition63M9FirstChartCutoffData.absorption_at_ratio
    {targetLoss rootExponent delta : ℝ}
    (cutoff : Proposition63M9FirstChartCutoffData
      targetLoss rootExponent)
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ cutoff.rootCutoff)
    (firstScale : WZ2PaperRequestedScale delta)
    (firstScale_lower :
      Real.rpow delta (1 - rootExponent) ≤ firstScale.1)
    (cardinality : ℕ)
    (cardinality_le : (cardinality : ℝ) ≤
      (259 : ℝ) ^ 3 * (67 : ℝ) ^ 3 *
        Real.rpow (delta / firstScale.1) (-9 : ℝ)) :
    let q := delta / firstScale.1
    let ambientConstant := Kakeya.realRpowENN q (-cutoff.nearbyInputLoss)
    let outputConstant := Kakeya.realRpowENN q (-targetLoss)
    let density := Kakeya.realRpowENN q cutoff.nearbyInputLoss
    let degreeConstant :=
      16 * ((cutoff.levelCount + 1 : ℕ) : ENNReal) *
        (Nat.log 2 (2 * cardinality) + 1 : ENNReal) ^
          (cutoff.levelCount + 1)
    let regularizationLoss :=
      (8 : ENNReal) *
        (Nat.log 2 (2 * cardinality) + 1 : ENNReal) ^
          (cutoff.levelCount + 2)
    let weight := (1 / 2 : ENNReal) * density
    let cardinalityLoss :=
      (2 * regularizationLoss) *
        (55296 * Kakeya.deltaTubeVolume 1)
    2 < ambientConstant ∧
    ambientConstant ≠ ⊤ ∧
    density ≠ 0 ∧
    density ≠ ⊤ ∧
    ENNReal.ofReal (1 / q) ≤ ambientConstant ^ cutoff.levelCount ∧
    ambientConstant * ambientConstant ≤ outputConstant ∧
    max degreeConstant
        ((weight⁻¹ *
            (ambientConstant * cardinalityLoss * degreeConstant)) *
          ambientConstant) ≤ outputConstant := by
  exact cutoff.nearby_absorption (delta / firstScale.1)
    (cutoff.ratio_pos delta_pos firstScale)
    (cutoff.ratio_le_cutoff delta_pos delta_le firstScale firstScale_lower)
    cardinality cardinality_le

/-- The same root pullback also pays the two canonical carrier-scale
absorptions used by the dense first-chart normalization. -/
theorem Proposition63M9FirstChartCutoffData.scale_absorption_at_ratio
    {targetLoss rootExponent delta : ℝ}
    (cutoff : Proposition63M9FirstChartCutoffData
      targetLoss rootExponent)
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ cutoff.rootCutoff)
    (firstScale : WZ2PaperRequestedScale delta)
    (firstScale_lower :
      Real.rpow delta (1 - rootExponent) ≤ firstScale.1) :
    let q := delta / firstScale.1
    (96 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN q
            (targetLoss - cutoff.nearbyInputLoss) ≤ 1 ∧
      ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN q
            (targetLoss - cutoff.nearbyInputLoss) ≤
        (73 / 100 : ENNReal) := by
  exact cutoff.scale_absorption
    (cutoff.ratio_pos delta_pos firstScale)
    ((proposition63_firstChart_ratio_le_root_power delta_pos
      (delta_pos.trans_le firstScale.2.1) firstScale_lower).trans
        (cutoff.root_power_le_scaleCutoff delta_pos delta_le))

end Kakeya.Assouad.PureWZ2

end
