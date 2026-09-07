import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteIntervalGridOneScaleLocalAD

/-!
# Finite iteration of PureWZ2 interval-covering outputs

This is the structure-only recursion used inside the paper's Lemma 4.11.
Each step acts on the actual current shading, restores extremality and CWA
immediately, and proves one new interval-localized covering estimate.  Bounds
from earlier steps survive by subshading monotonicity.

The theorem deliberately does not construct a geometric step.  In
particular, it does not identify the interval window with the square-root
cell scale used by the full-grain selection.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

/-- The finite list of all ordered grid pairs `k < j ≤ N` used by the inner
Lemma 4.11 iteration. -/
def finiteIntervalOrderedPairs (N : ℕ) : List (ℕ × ℕ) :=
  ((Finset.range N).biUnion fun k =>
    (Finset.range (N - k)).image fun offset => (k, k + 1 + offset)).toList

/-- Total indexing function for `finiteIntervalOrderedPairs`.  Only indices
strictly below the list length are used by the iterator. -/
def finiteIntervalOrderedPair (N index : ℕ) : ℕ × ℕ :=
  if hindex : index < (finiteIntervalOrderedPairs N).length then
    (finiteIntervalOrderedPairs N).get ⟨index, hindex⟩
  else
    (0, 0)

theorem finiteIntervalOrderedPair_valid
    {N index : ℕ}
    (hindex : index < (finiteIntervalOrderedPairs N).length) :
    (finiteIntervalOrderedPair N index).1 <
        (finiteIntervalOrderedPair N index).2 ∧
      (finiteIntervalOrderedPair N index).2 ≤ N := by
  have hmem : finiteIntervalOrderedPair N index ∈
      finiteIntervalOrderedPairs N := by
    simpa only [finiteIntervalOrderedPair, dif_pos hindex] using
      List.get_mem (finiteIntervalOrderedPairs N) ⟨index, hindex⟩
  have hfinset : finiteIntervalOrderedPair N index ∈
      (Finset.range N).biUnion (fun k =>
        (Finset.range (N - k)).image fun offset => (k, k + 1 + offset)) := by
    simpa only [finiteIntervalOrderedPairs, Finset.mem_toList] using hmem
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image] at hfinset
  rcases hfinset with ⟨k, hk, offset, hoffset, hpair⟩
  rw [← hpair]
  omega

theorem finiteIntervalOrderedPair_complete
    {N k j : ℕ} (hkj : k < j) (hjN : j ≤ N) :
    ∃ index, index < (finiteIntervalOrderedPairs N).length ∧
      finiteIntervalOrderedPair N index = (k, j) := by
  have hkN : k < N := hkj.trans_le hjN
  let offset := j - k - 1
  have hoffset : offset < N - k := by
    dsimp only [offset]
    omega
  have hpair : (k, j) ∈ (Finset.range N).biUnion (fun first =>
      (Finset.range (N - first)).image fun second =>
        (first, first + 1 + second)) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_range.mpr hkN, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨offset, Finset.mem_range.mpr hoffset, ?_⟩
    simp only [Prod.mk.injEq, true_and]
    dsimp only [offset]
    omega
  have hmem : (k, j) ∈ finiteIntervalOrderedPairs N := by
    simpa only [finiteIntervalOrderedPairs, Finset.mem_toList] using hpair
  rcases List.mem_iff_get.mp hmem with ⟨index, hindex⟩
  refine ⟨index, index.isLt, ?_⟩
  simpa only [finiteIntervalOrderedPair, dif_pos index.isLt] using hindex

/-- Runtime geometric grid for the inner Lemma 4.11 iteration.  The losses
and the grid length are selected before `delta` and `queryScale`; only the
actual powers of `queryScale` are materialized at runtime. -/
structure Proposition63InnerIntervalGridData
    (delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ)
    (gridN : ℕ) where
  scale : ℕ → NNReal
  ratio : ℝ
  query_pos : 0 < queryScale
  query_le_one : queryScale ≤ 1
  interval_loss_pos : 0 < intervalLoss
  output_loss_pos : 0 < outputLoss
  scale_zero : (scale 0 : ℝ) = queryScale
  scale_top : (scale gridN : ℝ) = Real.sqrt queryScale
  scale_pos : ∀ index, index ≤ gridN → 0 < (scale index : ℝ)
  scale_le_one : ∀ index, index ≤ gridN → (scale index : ℝ) ≤ 1
  query_le_scale : ∀ index, index ≤ gridN →
    queryScale ≤ (scale index : ℝ)
  scale_mono : ∀ index, index < gridN →
    (scale index : ℝ) ≤ (scale (index + 1) : ℝ)
  scale_ratio : ∀ index, index < gridN →
    (scale (index + 1) : ℝ) ≤ ratio * (scale index : ℝ)
  ratio_one : 1 ≤ ratio
  scale_covers : ∀ radius : ℝ, queryScale ≤ radius →
    radius ≤ Real.sqrt queryScale →
    ∃ index, index < gridN ∧ (scale index : ℝ) ≤ radius ∧
      radius ≤ (scale (index + 1) : ℝ)
  scale_window : ∀ loss : ℝ, 0 < loss → loss ≤ discreteLoss →
    ∀ index, index ≤ gridN →
      Real.rpow delta (1 - loss) ≤ (scale index : ℝ) ∧
        (scale index : ℝ) ≤ Real.rpow delta loss
  pair_window : ∀ loss : ℝ, 0 < loss → loss ≤ discreteLoss →
    ∀ index, index < (finiteIntervalOrderedPairs gridN).length →
      Real.rpow (scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
          (1 - loss) ≤
          (scale (finiteIntervalOrderedPair gridN index).2 : ℝ) ∧
        (scale (finiteIntervalOrderedPair gridN index).2 : ℝ) ≤
          Real.sqrt
            (scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
  interpolate : Real.rpow delta (-discreteLoss) *
      ratio ^ (1 - sigma) ≤ Real.rpow delta (-intervalLoss)
  absorb : (3 : ℝ) * Real.rpow delta (-intervalLoss) *
      ratio ^ (1 - sigma) ≤ Real.rpow delta (-outputLoss)

/-- All pre-runtime scalar choices for the paper grid from `queryScale` to
`sqrt queryScale`.  In particular, `gridN` and both interpolation losses do
not depend on the runtime extremizer or plane map. -/
structure Proposition63InnerIntervalGridScheduleData
    (sigma outputLoss : ℝ) where
  discreteLoss : ℝ
  intervalLoss : ℝ
  gridN : ℕ
  delta₀ : ℝ
  discrete_loss_pos : 0 < discreteLoss
  discrete_loss_eq : discreteLoss = outputLoss / 4
  discrete_loss_le_output : discreteLoss ≤ outputLoss
  interval_loss_pos : 0 < intervalLoss
  interval_loss_le_output : intervalLoss ≤ outputLoss
  gridN_pos : 0 < gridN
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  run : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    ∀ queryScale : WZ2PaperRequestedScale delta,
      Real.rpow delta (1 - outputLoss) ≤ queryScale.1 →
      queryScale.1 ≤ Real.rpow delta outputLoss →
      Nonempty (Proposition63InnerIntervalGridData delta sigma
        discreteLoss intervalLoss outputLoss queryScale.1 gridN)

/-- The WZ1 Lemma 19 geometric grid, with its interpolation payments, in the
`UniformTubeStructure`-free form consumed by the PureWZ2 inner iterator. -/
theorem proposition63_inner_interval_grid_schedule
    (sigma outputLoss : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtputLoss : 0 < outputLoss) (houtputSmall : outputLoss ≤ 1 / 2) :
    Nonempty (Proposition63InnerIntervalGridScheduleData sigma outputLoss) := by
  let alpha : ℝ := 1 - sigma
  have alphaPos : 0 < alpha := by dsimp only [alpha]; linarith
  have alphaOne : alpha ≤ 1 := by dsimp only [alpha]; linarith
  let discreteLoss : ℝ := outputLoss / 4
  have discretePos : 0 < discreteLoss := by
    dsimp only [discreteLoss]
    positivity
  have discreteOutput : discreteLoss ≤ outputLoss := by
    dsimp only [discreteLoss]
    linarith
  let gridN : ℕ := Nat.floor (2 / outputLoss)
  have gridNLe : (gridN : ℝ) ≤ 2 / outputLoss := by
    exact Nat.floor_le (by positivity)
  have gridNGt : 2 / outputLoss - 1 < (gridN : ℝ) := by
    have raw : (2 / outputLoss : ℝ) <
        ((Nat.floor (2 / outputLoss)).succ : ℕ) :=
      Nat.lt_succ_floor (2 / outputLoss)
    have castSucc : (((Nat.floor (2 / outputLoss)).succ : ℕ) : ℝ) =
        (gridN : ℝ) + 1 := by simp [gridN]
    exact_mod_cast (by rw [castSucc] at raw; linarith :
      2 / outputLoss - 1 < (gridN : ℝ))
  have gridNPos : 0 < gridN := by
    have fourLe : (4 : ℝ) ≤ 2 / outputLoss := by
      calc
        (4 : ℝ) = 2 / (1 / 2 : ℝ) := by norm_num
        _ ≤ 2 / outputLoss := by gcongr
    have threeLt : (3 : ℝ) < gridN := by linarith
    exact_mod_cast (show (0 : ℝ) < gridN by linarith)
  have discreteLeInv : discreteLoss ≤ 1 / (2 * (gridN : ℝ)) := by
    have gridNRealPos : 0 < (gridN : ℝ) := by exact_mod_cast gridNPos
    have denominatorLe : 2 * (gridN : ℝ) ≤ 4 / outputLoss := by
      calc
        2 * (gridN : ℝ) ≤ 2 * (2 / outputLoss) := by gcongr
        _ = 4 / outputLoss := by field_simp [houtputLoss.ne']; ring
    have reciprocal := one_div_le_one_div_of_le
      (show 0 < 2 * (gridN : ℝ) by positivity) denominatorLe
    calc
      discreteLoss = 1 / (4 / outputLoss) := by
        dsimp only [discreteLoss]
        field_simp [houtputLoss.ne']
      _ ≤ 1 / (2 * (gridN : ℝ)) := reciprocal
  have gridAbsorb :
      alpha * (1 - outputLoss) / (gridN : ℝ) <
        3 * outputLoss / 4 := by
    have numeratorLe : alpha * (1 - outputLoss) ≤ 1 := by
      have outputNonnegative : 0 ≤ outputLoss := houtputLoss.le
      nlinarith [alphaOne, alphaPos]
    have first : alpha * (1 - outputLoss) / (gridN : ℝ) ≤
        1 / (gridN : ℝ) := by
      exact div_le_div_of_nonneg_right numeratorLe (by positivity)
    have denominatorPos : 0 < 2 / outputLoss - 1 := by
      have fourLe : (4 : ℝ) ≤ 2 / outputLoss := by
        calc
          (4 : ℝ) = 2 / (1 / 2 : ℝ) := by norm_num
          _ ≤ 2 / outputLoss := by gcongr
      linarith
    have reciprocalLt : 1 / (gridN : ℝ) <
        1 / (2 / outputLoss - 1) := by gcongr
    have rewriteDenominator : 1 / (2 / outputLoss - 1) =
        outputLoss / (2 - outputLoss) := by
      field_simp [houtputLoss.ne', (show 2 - outputLoss ≠ 0 by linarith)]
    have final : outputLoss / (2 - outputLoss) <
        3 * outputLoss / 4 := by
      have denominatorPositive : 0 < 2 - outputLoss := by linarith
      rw [div_lt_iff₀ denominatorPositive]
      nlinarith
    exact first.trans_lt <| reciprocalLt.trans <| by
      rw [rewriteDenominator]
      exact final
  let intervalLoss : ℝ :=
    discreteLoss + alpha * (1 - outputLoss) / (2 * (gridN : ℝ))
  have intervalPos : 0 < intervalLoss := by
    dsimp only [intervalLoss]
    have nonnegative : 0 ≤
        alpha * (1 - outputLoss) / (2 * (gridN : ℝ)) := by
      exact div_nonneg
        (mul_nonneg alphaPos.le (sub_nonneg.mpr (by linarith)))
        (by positivity)
    linarith
  have intervalOutput : intervalLoss ≤ outputLoss := by
    have halfBound : alpha * (1 - outputLoss) / (gridN : ℝ) <
        outputLoss / 2 := by
      have denominatorLower : (2 - outputLoss) / outputLoss <
          (gridN : ℝ) := by
        calc
          (2 - outputLoss) / outputLoss = 2 / outputLoss - 1 := by
            field_simp [houtputLoss.ne']
          _ < (gridN : ℝ) := gridNGt
      have denominatorPositive : 0 < (2 - outputLoss) / outputLoss := by
        exact div_pos (by linarith) houtputLoss
      have numeratorPositive : 0 < alpha * (1 - outputLoss) := by
        exact mul_pos alphaPos (by linarith)
      calc
        alpha * (1 - outputLoss) / (gridN : ℝ) <
            alpha * (1 - outputLoss) / ((2 - outputLoss) / outputLoss) :=
          div_lt_div_of_pos_left numeratorPositive denominatorPositive
            denominatorLower
        _ ≤ outputLoss / 2 := by
          have alphaFactor : alpha * (1 - outputLoss) ≤
              1 - outputLoss := by
            nlinarith [alphaOne, alphaPos, houtputLoss]
          rw [div_le_iff₀ denominatorPositive]
          field_simp [houtputLoss.ne']
          nlinarith
    have quarterBound : alpha * (1 - outputLoss) /
        (2 * (gridN : ℝ)) ≤ outputLoss / 4 := by
      calc
        alpha * (1 - outputLoss) / (2 * (gridN : ℝ)) =
            (alpha * (1 - outputLoss) / (gridN : ℝ)) / 2 := by ring
        _ ≤ outputLoss / 4 := by linarith
    dsimp only [intervalLoss, discreteLoss]
    linarith
  let epsilon : ℝ :=
    3 * outputLoss / 4 - alpha * (1 - outputLoss) / (gridN : ℝ)
  have epsilonPos : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  let delta₀ : ℝ := Real.rpow 3 (-1 / epsilon)
  have delta₀Pos : 0 < delta₀ := Real.rpow_pos_of_pos (by norm_num) _
  have exponentNeg : -1 / epsilon < 0 :=
    div_neg_of_neg_of_pos (by norm_num) epsilonPos
  have delta₀One : delta₀ ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) exponentNeg.le
  refine ⟨{
    discreteLoss := discreteLoss
    intervalLoss := intervalLoss
    gridN := gridN
    delta₀ := delta₀
    discrete_loss_pos := discretePos
    discrete_loss_le_output := discreteOutput
    interval_loss_pos := intervalPos
    interval_loss_le_output := intervalOutput
    gridN_pos := gridNPos
    delta₀_pos := delta₀Pos
    delta₀_le_one := delta₀One
    discrete_loss_eq := rfl
    run := ?_
  }⟩
  intro delta deltaPos deltaLe queryScale queryLower queryUpper
  have deltaOne : delta ≤ 1 := deltaLe.trans delta₀One
  have deltaStrict : delta < 1 := by
    exact deltaLe.trans_lt <|
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) exponentNeg
  have queryPos : 0 < queryScale.1 := deltaPos.trans_le queryScale.2.1
  have queryOne : queryScale.1 ≤ 1 := queryScale.2.2
  let scale : ℕ → NNReal := fun index =>
    ⟨Real.rpow queryScale.1
        (1 - (index : ℝ) / (2 * (gridN : ℝ))),
      Real.rpow_nonneg queryPos.le _⟩
  have scaleEq : ∀ index, (scale index : ℝ) =
      Real.rpow queryScale.1
        (1 - (index : ℝ) / (2 * (gridN : ℝ))) := fun _ => rfl
  have scaleZero : (scale 0 : ℝ) = queryScale.1 := by
    rw [scaleEq]
    simp
  have scaleTop : (scale gridN : ℝ) = Real.sqrt queryScale.1 := by
    rw [scaleEq]
    have exponentEq : 1 - (gridN : ℝ) / (2 * (gridN : ℝ)) =
        1 / 2 := by field_simp [show (gridN : ℝ) ≠ 0 by positivity]; ring
    rw [exponentEq]
    exact (Real.sqrt_eq_rpow queryScale.1).symm
  have scalePos : ∀ index, index ≤ gridN → 0 < (scale index : ℝ) := by
    intro index _
    rw [scaleEq]
    exact Real.rpow_pos_of_pos queryPos _
  have scaleLeOne : ∀ index, index ≤ gridN →
      (scale index : ℝ) ≤ 1 := by
    intro index indexLe
    rw [scaleEq]
    apply Real.rpow_le_one queryPos.le queryOne
    have indexCast : (index : ℝ) ≤ gridN := by exact_mod_cast indexLe
    have denominatorPos : 0 < 2 * (gridN : ℝ) := by positivity
    have fractionLe : (index : ℝ) / (2 * (gridN : ℝ)) ≤ 1 := by
      rw [div_le_one denominatorPos]
      linarith
    linarith
  have queryLeScale : ∀ index, index ≤ gridN →
      queryScale.1 ≤ (scale index : ℝ) := by
    intro index indexLe
    rw [scaleEq]
    have exponentLe :
        1 - (index : ℝ) / (2 * (gridN : ℝ)) ≤ 1 := by
      have fractionNonnegative :
          0 ≤ (index : ℝ) / (2 * (gridN : ℝ)) := by positivity
      linarith
    simpa using Real.rpow_le_rpow_of_exponent_ge queryPos queryOne exponentLe
  have scaleMono : ∀ index, index < gridN →
      (scale index : ℝ) ≤ (scale (index + 1) : ℝ) := by
    intro index indexLt
    rw [scaleEq, scaleEq]
    apply Real.rpow_le_rpow_of_exponent_ge queryPos queryOne
    simp only [Nat.cast_add, Nat.cast_one]
    have denominatorPos : 0 < 2 * (gridN : ℝ) := by positivity
    apply sub_le_sub_left
    exact div_le_div_of_nonneg_right (by norm_num) denominatorPos.le
  let ratio : ℝ := Real.rpow queryScale.1
    (-1 / (2 * (gridN : ℝ)))
  have ratioOne : 1 ≤ ratio := by
    have exponentNonpositive : -1 / (2 * (gridN : ℝ)) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
    dsimp only [ratio]
    simpa using Real.one_le_rpow_of_pos_of_le_one_of_nonpos queryPos
      queryOne exponentNonpositive
  have scaleRatio : ∀ index, index < gridN →
      (scale (index + 1) : ℝ) ≤ ratio * (scale index : ℝ) := by
    intro index indexLt
    rw [scaleEq, scaleEq]
    have exponentEq :
        1 - ((index + 1 : ℕ) : ℝ) / (2 * (gridN : ℝ)) =
          (1 - (index : ℝ) / (2 * (gridN : ℝ))) +
            (-1 / (2 * (gridN : ℝ))) := by
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp [show (gridN : ℝ) ≠ 0 by positivity]
      ring
    rw [exponentEq]
    have powerAdd : Real.rpow queryScale.1
        ((1 - (index : ℝ) / (2 * (gridN : ℝ))) +
          (-1 / (2 * (gridN : ℝ)))) =
        Real.rpow queryScale.1
            (1 - (index : ℝ) / (2 * (gridN : ℝ))) *
          Real.rpow queryScale.1 (-1 / (2 * (gridN : ℝ))) :=
      Real.rpow_add queryPos _ _
    rw [powerAdd]
    dsimp only [ratio]
    rw [mul_comm]
  have scaleMonoGeneral : ∀ first second : ℕ, first ≤ second →
      second ≤ gridN → (scale first : ℝ) ≤ (scale second : ℝ) := by
    intro first second firstLe secondLe
    have inductionStep : ∀ offset : ℕ, first + offset ≤ gridN →
        (scale first : ℝ) ≤ (scale (first + offset) : ℝ) := by
      intro offset
      induction offset with
      | zero => simp
      | succ offset inductionHypothesis =>
          intro sumLe
          exact (inductionHypothesis (by omega)).trans
            (scaleMono (first + offset) (by omega))
    simpa only [Nat.add_sub_of_le firstLe] using
      inductionStep (second - first) (by omega)
  have scaleCovers : ∀ radius : ℝ, queryScale.1 ≤ radius →
      radius ≤ Real.sqrt queryScale.1 →
      ∃ index, index < gridN ∧ (scale index : ℝ) ≤ radius ∧
        radius ≤ (scale (index + 1) : ℝ) := by
    intro radius queryLeRadius radiusLe
    by_cases radiusEq : radius = Real.sqrt queryScale.1
    · subst radius
      refine ⟨gridN - 1, by omega, ?_, ?_⟩
      · exact (scaleMonoGeneral (gridN - 1) gridN (by omega) le_rfl).trans_eq
          scaleTop
      · rw [show gridN - 1 + 1 = gridN by omega, scaleTop]
    · have radiusLt : radius < Real.sqrt queryScale.1 :=
        lt_of_le_of_ne radiusLe radiusEq
      let indices : Finset ℕ :=
        Finset.filter (fun index => (scale index : ℝ) ≤ radius)
          (Finset.Icc 0 gridN)
      have indicesNonempty : indices.Nonempty := by
        refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨le_rfl, gridNPos.le⟩, ?_⟩⟩
        simpa only [scaleZero] using queryLeRadius
      let index : ℕ := indices.max' indicesNonempty
      have indexMem : index ∈ indices := Finset.max'_mem indices indicesNonempty
      have indexRange : index ≤ gridN :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp indexMem).1).2
      have indexScale : (scale index : ℝ) ≤ radius :=
        (Finset.mem_filter.mp indexMem).2
      have indexLt : index < gridN := by
        by_contra notLt
        have indexEq : index = gridN := Nat.le_antisymm indexRange
          (Nat.le_of_not_gt notLt)
        rw [indexEq, scaleTop] at indexScale
        exact (not_le_of_gt radiusLt) indexScale
      have radiusSucc : radius ≤ (scale (index + 1) : ℝ) := by
        by_contra notLe
        have succMem : index + 1 ∈ indices := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
            ⟨by omega, by omega⟩, le_of_not_ge notLe⟩
        exact (Nat.not_succ_le_self index)
          (Finset.le_max' indices (index + 1) succMem)
      exact ⟨index, indexLt, indexScale, radiusSucc⟩
  have scaleWindow : ∀ loss : ℝ, 0 < loss → loss ≤ discreteLoss →
      ∀ index, index ≤ gridN →
        Real.rpow delta (1 - loss) ≤ (scale index : ℝ) ∧
          (scale index : ℝ) ≤ Real.rpow delta loss := by
    intro loss lossPos lossLe index indexLe
    constructor
    · calc
        Real.rpow delta (1 - loss) ≤
            Real.rpow delta (1 - outputLoss) :=
          Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne (by
            linarith [lossLe, discreteOutput])
        _ ≤ queryScale.1 := queryLower
        _ ≤ (scale index : ℝ) := queryLeScale index indexLe
    · calc
        (scale index : ℝ) ≤ (scale gridN : ℝ) :=
          scaleMonoGeneral index gridN indexLe le_rfl
        _ = Real.sqrt queryScale.1 := scaleTop
        _ ≤ Real.rpow delta (outputLoss / 2) := by
          rw [Real.sqrt_eq_rpow]
          calc
            Real.rpow queryScale.1 (1 / 2 : ℝ) ≤
                Real.rpow (Real.rpow delta outputLoss) (1 / 2 : ℝ) :=
              Real.rpow_le_rpow queryPos.le queryUpper (by norm_num)
            _ = Real.rpow delta (outputLoss / 2) := by
              rw [show outputLoss / 2 = outputLoss * (1 / 2 : ℝ) by ring]
              exact (Real.rpow_mul deltaPos.le _ _).symm
        _ ≤ Real.rpow delta loss :=
          Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne (by
            linarith [lossLe, show discreteLoss = outputLoss / 4 from rfl])
  have pairWindow : ∀ loss : ℝ, 0 < loss → loss ≤ discreteLoss →
      ∀ index, index < (finiteIntervalOrderedPairs gridN).length →
        Real.rpow (scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
            (1 - loss) ≤
            (scale (finiteIntervalOrderedPair gridN index).2 : ℝ) ∧
          (scale (finiteIntervalOrderedPair gridN index).2 : ℝ) ≤
            Real.sqrt
              (scale (finiteIntervalOrderedPair gridN index).1 : ℝ) := by
    intro loss lossPos lossLe index indexLt
    obtain ⟨pairLt, pairTop⟩ := finiteIntervalOrderedPair_valid indexLt
    rw [scaleEq, scaleEq]
    let firstExponent : ℝ :=
      1 - ((finiteIntervalOrderedPair gridN index).1 : ℝ) /
        (2 * (gridN : ℝ))
    have firstExponentNonnegative : 0 ≤ firstExponent := by
      have firstLe : (finiteIntervalOrderedPair gridN index).1 ≤ gridN :=
        pairLt.le.trans pairTop
      have firstCast : ((finiteIntervalOrderedPair gridN index).1 : ℝ) ≤
          gridN := by exact_mod_cast firstLe
      dsimp only [firstExponent]
      have denominatorPos : 0 < 2 * (gridN : ℝ) := by positivity
      have fractionLe :
          ((finiteIntervalOrderedPair gridN index).1 : ℝ) /
              (2 * (gridN : ℝ)) ≤ 1 := by
        rw [div_le_one denominatorPos]
        linarith
      linarith
    have firstExponentLeOne : firstExponent ≤ 1 := by
      dsimp only [firstExponent]
      have fractionNonnegative : 0 ≤
          ((finiteIntervalOrderedPair gridN index).1 : ℝ) /
            (2 * (gridN : ℝ)) := by positivity
      linarith
    constructor
    · have nestedPower : Real.rpow
          (Real.rpow queryScale.1 firstExponent) (1 - loss) =
          Real.rpow queryScale.1 ((1 - loss) * firstExponent) := by
          rw [mul_comm]
          exact (Real.rpow_mul queryPos.le _ _).symm
      rw [nestedPower]
      apply Real.rpow_le_rpow_of_exponent_ge queryPos queryOne
      have lossLeInv : loss ≤ 1 / (2 * (gridN : ℝ)) :=
        lossLe.trans discreteLeInv
      have productLe : loss * firstExponent ≤
          1 / (2 * (gridN : ℝ)) := by
        calc
          loss * firstExponent ≤ loss * 1 := by gcongr
          _ = loss := by ring
          _ ≤ 1 / (2 * (gridN : ℝ)) := lossLeInv
      have pairGap :
          ((finiteIntervalOrderedPair gridN index).1 : ℝ) + 1 ≤
            ((finiteIntervalOrderedPair gridN index).2 : ℝ) := by
        exact_mod_cast pairLt
      have denominatorPos : 0 < 2 * (gridN : ℝ) := by positivity
      have predecessorExponent :
          1 - (((finiteIntervalOrderedPair gridN index).1 : ℝ) + 1) /
                (2 * (gridN : ℝ)) =
            firstExponent - 1 / (2 * (gridN : ℝ)) := by
        dsimp only [firstExponent]
        field_simp [show (gridN : ℝ) ≠ 0 by positivity]
        ring
      calc
        1 - ((finiteIntervalOrderedPair gridN index).2 : ℝ) /
              (2 * (gridN : ℝ)) ≤
            1 - (((finiteIntervalOrderedPair gridN index).1 : ℝ) + 1) /
              (2 * (gridN : ℝ)) := by gcongr
        _ = firstExponent - 1 / (2 * (gridN : ℝ)) :=
          predecessorExponent
        _ ≤ (1 - loss) *
            firstExponent := by
          rw [show (1 - loss) * firstExponent =
              firstExponent - loss * firstExponent by ring]
          linarith
    · rw [Real.sqrt_eq_rpow]
      have nestedPower : Real.rpow
          (Real.rpow queryScale.1 firstExponent) (1 / 2 : ℝ) =
          Real.rpow queryScale.1 (firstExponent / 2) := by
        rw [show firstExponent / 2 =
            firstExponent * (1 / 2 : ℝ) by ring]
        exact (Real.rpow_mul queryPos.le _ _).symm
      change Real.rpow queryScale.1
          (1 - ((finiteIntervalOrderedPair gridN index).2 : ℝ) /
            (2 * (gridN : ℝ))) ≤
        Real.rpow (Real.rpow queryScale.1 firstExponent) (1 / 2 : ℝ)
      rw [nestedPower]
      apply Real.rpow_le_rpow_of_exponent_ge queryPos queryOne
      have secondCast : ((finiteIntervalOrderedPair gridN index).2 : ℝ) ≤
          gridN := by exact_mod_cast pairTop
      have denominatorPos : 0 < 2 * (gridN : ℝ) := by positivity
      have numerator :
          0 ≤ 2 * (gridN : ℝ) -
            2 * ((finiteIntervalOrderedPair gridN index).2 : ℝ) +
              ((finiteIntervalOrderedPair gridN index).1 : ℝ) := by
        linarith
      have identity :
          1 - ((finiteIntervalOrderedPair gridN index).2 : ℝ) /
                (2 * (gridN : ℝ)) -
              (1 - ((finiteIntervalOrderedPair gridN index).1 : ℝ) /
                (2 * (gridN : ℝ))) / 2 =
            (2 * (gridN : ℝ) -
                2 * ((finiteIntervalOrderedPair gridN index).2 : ℝ) +
                  ((finiteIntervalOrderedPair gridN index).1 : ℝ)) /
              (2 * (2 * (gridN : ℝ))) := by
        field_simp [show (gridN : ℝ) ≠ 0 by positivity]
        ring
      apply sub_nonneg.mp
      rw [identity]
      exact div_nonneg numerator (by positivity)
  have ratioBound : ratio ≤ Real.rpow delta
      (-(1 - outputLoss) / (2 * (gridN : ℝ))) := by
    let exponent : ℝ := 1 / (2 * (gridN : ℝ))
    have exponentPos : 0 < exponent := by
      dsimp only [exponent]
      positivity
    have powered : Real.rpow (Real.rpow delta (1 - outputLoss)) exponent ≤
        Real.rpow queryScale.1 exponent :=
      Real.rpow_le_rpow (Real.rpow_nonneg deltaPos.le _) queryLower
        exponentPos.le
    have inverse : (Real.rpow queryScale.1 exponent)⁻¹ ≤
        (Real.rpow (Real.rpow delta (1 - outputLoss)) exponent)⁻¹ := by
      exact (inv_le_inv₀ (Real.rpow_pos_of_pos queryPos _)
        (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos deltaPos _) _)).2 powered
    have queryNegative : Real.rpow queryScale.1 (-exponent) =
        (Real.rpow queryScale.1 exponent)⁻¹ :=
      Real.rpow_neg queryPos.le exponent
    have deltaNested : Real.rpow
        (Real.rpow delta (1 - outputLoss)) exponent =
          Real.rpow delta ((1 - outputLoss) * exponent) :=
      (Real.rpow_mul deltaPos.le _ _).symm
    have deltaNegative : Real.rpow delta
        (-((1 - outputLoss) * exponent)) =
          (Real.rpow delta ((1 - outputLoss) * exponent))⁻¹ :=
      Real.rpow_neg deltaPos.le _
    dsimp only [ratio]
    rw [show -1 / (2 * (gridN : ℝ)) = -exponent by
        simp only [exponent]; ring,
      queryNegative]
    calc
      (Real.rpow queryScale.1 exponent)⁻¹ ≤
          (Real.rpow (Real.rpow delta (1 - outputLoss)) exponent)⁻¹ :=
        inverse
      _ = (Real.rpow delta ((1 - outputLoss) * exponent))⁻¹ := by
        rw [deltaNested]
      _ = Real.rpow delta (-((1 - outputLoss) * exponent)) :=
        deltaNegative.symm
      _ = Real.rpow delta
          (-(1 - outputLoss) / (2 * (gridN : ℝ))) := by
        congr 1
        dsimp only [exponent]
        ring
  have interpolate : Real.rpow delta (-discreteLoss) *
      ratio ^ alpha ≤ Real.rpow delta (-intervalLoss) := by
    have ratioPower : ratio ^ alpha ≤ Real.rpow delta
        (-(alpha * (1 - outputLoss) / (2 * (gridN : ℝ)))) := by
      calc
        ratio ^ alpha ≤
            (Real.rpow delta
              (-(1 - outputLoss) / (2 * (gridN : ℝ)))) ^ alpha :=
          Real.rpow_le_rpow (by
            dsimp only [ratio]
            exact Real.rpow_nonneg queryPos.le _) ratioBound alphaPos.le
        _ = Real.rpow delta
            (-(alpha * (1 - outputLoss) / (2 * (gridN : ℝ)))) := by
          change Real.rpow
              (Real.rpow delta
                (-(1 - outputLoss) / (2 * (gridN : ℝ)))) alpha = _
          calc
            _ = Real.rpow delta
                ((-(1 - outputLoss) / (2 * (gridN : ℝ))) * alpha) :=
              (Real.rpow_mul deltaPos.le _ _).symm
            _ = _ := by congr 1; ring
    calc
      Real.rpow delta (-discreteLoss) * ratio ^ alpha ≤
          Real.rpow delta (-discreteLoss) * Real.rpow delta
            (-(alpha * (1 - outputLoss) /
              (2 * (gridN : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left ratioPower
          (Real.rpow_nonneg deltaPos.le _)
      _ = Real.rpow delta
          (-discreteLoss +
            -(alpha * (1 - outputLoss) / (2 * (gridN : ℝ)))) :=
        (Real.rpow_add deltaPos _ _).symm
      _ = Real.rpow delta (-intervalLoss) := by
        congr 1
        dsimp only [intervalLoss]
        ring
  have threeBound : (3 : ℝ) ≤ Real.rpow delta (-epsilon) := by
    have powerLe : Real.rpow delta epsilon ≤ 1 / 3 := by
      calc
        Real.rpow delta epsilon ≤ Real.rpow delta₀ epsilon :=
          Real.rpow_le_rpow deltaPos.le deltaLe epsilonPos.le
        _ = 1 / 3 := by
          have nested : Real.rpow (Real.rpow 3 (-1 / epsilon)) epsilon =
              Real.rpow 3 ((-1 / epsilon) * epsilon) :=
            (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
          rw [show delta₀ = Real.rpow 3 (-1 / epsilon) by rfl, nested]
          have exponentEq : (-1 / epsilon) * epsilon = -1 := by
            field_simp [epsilonPos.ne']
          rw [exponentEq]
          norm_num
    have inverseEq : Real.rpow delta (-epsilon) =
        (Real.rpow delta epsilon)⁻¹ := Real.rpow_neg deltaPos.le epsilon
    rw [inverseEq]
    have inverseLower : (Real.rpow delta epsilon)⁻¹ ≥
        (1 / 3 : ℝ)⁻¹ :=
      (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1 / 3)
        (Real.rpow_pos_of_pos deltaPos epsilon)).2 powerLe
    simpa using inverseLower
  have absorb : (3 : ℝ) * Real.rpow delta (-intervalLoss) *
      ratio ^ alpha ≤ Real.rpow delta (-outputLoss) := by
    have ratioPower : ratio ^ alpha ≤ Real.rpow delta
        (-(alpha * (1 - outputLoss) / (2 * (gridN : ℝ)))) := by
      calc
        ratio ^ alpha ≤
            (Real.rpow delta
              (-(1 - outputLoss) / (2 * (gridN : ℝ)))) ^ alpha :=
          Real.rpow_le_rpow (by
            dsimp only [ratio]
            exact Real.rpow_nonneg queryPos.le _) ratioBound alphaPos.le
        _ = Real.rpow delta
            (-(alpha * (1 - outputLoss) / (2 * (gridN : ℝ)))) := by
          change Real.rpow
              (Real.rpow delta
                (-(1 - outputLoss) / (2 * (gridN : ℝ)))) alpha = _
          calc
            _ = Real.rpow delta
                ((-(1 - outputLoss) / (2 * (gridN : ℝ))) * alpha) :=
              (Real.rpow_mul deltaPos.le _ _).symm
            _ = _ := by congr 1; ring
    calc
      (3 : ℝ) * Real.rpow delta (-intervalLoss) * ratio ^ alpha ≤
          (3 : ℝ) * Real.rpow delta (-intervalLoss) *
            Real.rpow delta (-(alpha * (1 - outputLoss) /
              (2 * (gridN : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left ratioPower
          (mul_nonneg (by norm_num) (Real.rpow_nonneg deltaPos.le _))
      _ ≤ Real.rpow delta (-epsilon) *
            (Real.rpow delta (-intervalLoss) * Real.rpow delta
              (-(alpha * (1 - outputLoss) /
                (2 * (gridN : ℝ))))) := by
        rw [show (3 : ℝ) * Real.rpow delta (-intervalLoss) *
            Real.rpow delta (-(alpha * (1 - outputLoss) /
              (2 * (gridN : ℝ)))) =
            3 * (Real.rpow delta (-intervalLoss) *
              Real.rpow delta (-(alpha * (1 - outputLoss) /
                (2 * (gridN : ℝ))))) by ring]
        exact mul_le_mul_of_nonneg_right threeBound
          (mul_nonneg (Real.rpow_nonneg deltaPos.le _)
            (Real.rpow_nonneg deltaPos.le _))
      _ = Real.rpow delta (-epsilon) *
            Real.rpow delta
              (-intervalLoss - alpha * (1 - outputLoss) /
                (2 * (gridN : ℝ))) := by
        congr 1
        exact (Real.rpow_add deltaPos _ _).symm
      _ = Real.rpow delta
            (-epsilon - intervalLoss - alpha * (1 - outputLoss) /
              (2 * (gridN : ℝ))) := by
        exact (Real.rpow_add deltaPos _ _).symm.trans <| by congr 1 <;> ring
      _ = Real.rpow delta (-outputLoss) := by
        congr 1
        dsimp only [epsilon, intervalLoss, discreteLoss]
        ring
  exact ⟨{
    scale := scale
    ratio := ratio
    query_pos := queryPos
    query_le_one := queryOne
    interval_loss_pos := intervalPos
    output_loss_pos := houtputLoss
    scale_zero := scaleZero
    scale_top := scaleTop
    scale_pos := scalePos
    scale_le_one := scaleLeOne
    query_le_scale := queryLeScale
    scale_mono := scaleMono
    scale_ratio := scaleRatio
    ratio_one := ratioOne
    scale_covers := scaleCovers
    scale_window := scaleWindow
    pair_window := pairWindow
    interpolate := by simpa only [alpha] using interpolate
    absorb := by simpa only [alpha] using absorb
  }⟩

/-- Iterate an interval producer over a finite schedule while preserving the
current-shading provenance, point multiplicity, mass ledger, and the analytic
state needed to re-enter the next step. -/
theorem finite_interval_covering_iteration_of_mass_pos
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (planeMap : Point3 → Point3)
    (spatialQueryScale : ℕ → ℝ)
    (N : ℕ)
    (resolutionScale windowScale : ℕ → NNReal)
    (constant : ℕ → ENNReal)
    (loss : ℕ → ℝ)
    (leftFactor rightFactor : ℕ → ENNReal)
    (hsourceCubical : WZ1PaperIsCubicalShading source)
    (hsourceExtremal :
      WZ2PaperCroppedIsExtremal sigma (loss 0) family source)
    (hsourceCWA : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-(loss 0))))
    (hsourceMass : 0 < source.mass)
    (hleftFactorPos : ∀ index, index < N → 0 < leftFactor index)
    (step : ∀ index : ℕ, index < N →
      ∀ current : WZ1PaperTubeShading family,
        PaperIsSubshading current source →
        WZ1PaperIsCubicalShading current →
        (∀ point ∈ current.union,
          current.pointMultiplicity point = source.pointMultiplicity point) →
        WZ2PaperCroppedIsExtremal sigma (loss index) family current →
        WZ2PaperConvexWolffBound family
          (Kakeya.realRpowENN delta (-(loss index))) →
        (∏ prior ∈ Finset.range index, leftFactor prior) * source.mass ≤
          (∏ prior ∈ Finset.range index, rightFactor prior) * current.mass →
        0 < current.mass →
        ∃ next : WZ1PaperTubeShading family,
          PaperIsSubshading next current ∧
          WZ1PaperIsCubicalShading next ∧
          (∀ point ∈ next.union,
            next.pointMultiplicity point = current.pointMultiplicity point) ∧
          WZ2PaperCroppedIsExtremal sigma (loss (index + 1)) family next ∧
          WZ2PaperConvexWolffBound family
            (Kakeya.realRpowENN delta (-(loss (index + 1)))) ∧
          PureWZ2IntervalCoveringAt next planeMap (spatialQueryScale index)
            (resolutionScale index) (windowScale index) (constant index) ∧
          leftFactor index * current.mass ≤ rightFactor index * next.mass) :
    ∃ final : WZ1PaperTubeShading family,
      PaperIsSubshading final source ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point = source.pointMultiplicity point) ∧
      WZ2PaperCroppedIsExtremal sigma (loss N) family final ∧
      WZ2PaperConvexWolffBound family
        (Kakeya.realRpowENN delta (-(loss N))) ∧
      (∀ index, index < N →
        PureWZ2IntervalCoveringAt final planeMap (spatialQueryScale index)
          (resolutionScale index) (windowScale index) (constant index)) ∧
      (∏ index ∈ Finset.range N, leftFactor index) * source.mass ≤
        (∏ index ∈ Finset.range N, rightFactor index) * final.mass ∧
      0 < final.mass := by
  let P : ℕ → Prop := fun completed =>
    ∃ current : WZ1PaperTubeShading family,
      PaperIsSubshading current source ∧
      WZ1PaperIsCubicalShading current ∧
      (∀ point ∈ current.union,
        current.pointMultiplicity point = source.pointMultiplicity point) ∧
      WZ2PaperCroppedIsExtremal sigma (loss completed) family current ∧
      WZ2PaperConvexWolffBound family
        (Kakeya.realRpowENN delta (-(loss completed))) ∧
      (∀ index, index < completed → index < N →
        PureWZ2IntervalCoveringAt current planeMap (spatialQueryScale index)
          (resolutionScale index) (windowScale index) (constant index)) ∧
      (∏ index ∈ Finset.range completed, leftFactor index) * source.mass ≤
        (∏ index ∈ Finset.range completed, rightFactor index) * current.mass ∧
      0 < current.mass
  have hbase : P 0 := by
    refine ⟨source, fun _ => Set.Subset.rfl, hsourceCubical, ?_,
      hsourceExtremal, hsourceCWA, ?_, ?_, hsourceMass⟩
    · intro point _
      rfl
    · intro index hindex
      omega
    · simp
  have hnext : ∀ completed, completed < N → P completed →
      P (completed + 1) := by
    intro completed hcompleted hP
    rcases hP with
      ⟨current, hcurrentSub, hcurrentCubical, hcurrentMultiplicity,
        hcurrentExtremal, hcurrentCWA, hcurrentCovering,
        hcurrentMassLedger, hcurrentMass⟩
    rcases step completed hcompleted current hcurrentSub hcurrentCubical
        hcurrentMultiplicity hcurrentExtremal hcurrentCWA
        hcurrentMassLedger hcurrentMass with
      ⟨next, hnextSub, hnextCubical, hnextMultiplicityCurrent,
        hnextExtremal, hnextCWA, hnextCovering, hnextMassLedger⟩
    have hnextSubSource : PaperIsSubshading next source := fun index =>
      (hnextSub index).trans (hcurrentSub index)
    have hnextMultiplicity : ∀ point ∈ next.union,
        next.pointMultiplicity point = source.pointMultiplicity point := by
      intro point hpoint
      have hpointCurrent : point ∈ current.union := by
        rcases hpoint with ⟨index, hindex⟩
        exact ⟨index, hnextSub index hindex⟩
      exact (hnextMultiplicityCurrent point hpoint).trans
        (hcurrentMultiplicity point hpointCurrent)
    have hallCovering : ∀ index, index < completed + 1 → index < N →
        PureWZ2IntervalCoveringAt next planeMap (spatialQueryScale index)
          (resolutionScale index) (windowScale index) (constant index) := by
      intro index hindex hindexN
      by_cases hlast : index = completed
      · subst index
        exact hnextCovering
      · have hindexOld : index < completed := by omega
        exact pureWZ2IntervalCoveringAt_mono hnextSub
          (hcurrentCovering index hindexOld hindexN)
    have hmass :
        (∏ index ∈ Finset.range (completed + 1), leftFactor index) *
            source.mass ≤
          (∏ index ∈ Finset.range (completed + 1), rightFactor index) *
            next.mass := by
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      calc
        ((∏ index ∈ Finset.range completed, leftFactor index) *
              leftFactor completed) * source.mass =
            leftFactor completed *
              ((∏ index ∈ Finset.range completed, leftFactor index) *
                source.mass) := by ring
        _ ≤ leftFactor completed *
              ((∏ index ∈ Finset.range completed, rightFactor index) *
                current.mass) := by gcongr
        _ = (∏ index ∈ Finset.range completed, rightFactor index) *
              (leftFactor completed * current.mass) := by ring
        _ ≤ (∏ index ∈ Finset.range completed, rightFactor index) *
              (rightFactor completed * next.mass) := by gcongr
        _ = ((∏ index ∈ Finset.range completed, rightFactor index) *
              rightFactor completed) * next.mass := by ring
    have hleftCurrent : 0 < leftFactor completed * current.mass :=
      ENNReal.mul_pos (hleftFactorPos completed hcompleted).ne'
        hcurrentMass.ne'
    have hrightNext : 0 < rightFactor completed * next.mass :=
      hleftCurrent.trans_le hnextMassLedger
    have hnextMass : 0 < next.mass := by
      by_contra hnot
      have hzero : next.mass = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hnot)
      rw [hzero, mul_zero] at hrightNext
      exact (lt_irrefl 0) hrightNext
    exact ⟨next, hnextSubSource, hnextCubical, hnextMultiplicity,
      hnextExtremal, hnextCWA, hallCovering, hmass, hnextMass⟩
  have hinduction : ∀ completed, completed ≤ N → P completed := by
    intro completed hcompleted
    induction completed with
    | zero => exact hbase
    | succ completed ih =>
        exact hnext completed (by omega) (ih (by omega))
  rcases hinduction N le_rfl with
    ⟨final, hfinalSub, hfinalCubical, hfinalMultiplicity,
      hfinalExtremal, hfinalCWA, hfinalCovering, hfinalMassLedger,
      hfinalMass⟩
  exact ⟨final, hfinalSub, hfinalCubical, hfinalMultiplicity,
    hfinalExtremal, hfinalCWA,
    (fun index hindex => hfinalCovering index hindex hindex),
    hfinalMassLedger, hfinalMass⟩

/-- Run a finite schedule enumerating every ordered grid pair and feed its
final interval bounds directly into the one-scale AD terminal.  This closes
all recursion and interpolation bookkeeping; the caller still has to supply
the genuine geometric `step` at each scheduled pair. -/
theorem finite_interval_covering_iteration_to_one_scale
    {delta sigma discreteLoss intervalLoss outputLoss queryScale ratio : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (planeMap : Point3 → Point3)
    (gridN stepCount : ℕ)
    (scale : ℕ → NNReal)
    (pair : ℕ → ℕ × ℕ)
    (loss : ℕ → ℝ)
    (leftFactor rightFactor : ℕ → ENNReal)
    (hpairComplete : ∀ k j, k < j → j ≤ gridN →
      ∃ index, index < stepCount ∧ pair index = (k, j))
    (hsourceCubical : WZ1PaperIsCubicalShading source)
    (hsourceExtremal :
      WZ2PaperCroppedIsExtremal sigma (loss 0) family source)
    (hsourceCWA : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-(loss 0))))
    (hsourceMass : 0 < source.mass)
    (hleftFactorPos : ∀ index, index < stepCount → 0 < leftFactor index)
    (step : ∀ index : ℕ, index < stepCount →
      ∀ current : WZ1PaperTubeShading family,
        PaperIsSubshading current source →
        WZ1PaperIsCubicalShading current →
        (∀ point ∈ current.union,
          current.pointMultiplicity point = source.pointMultiplicity point) →
        WZ2PaperCroppedIsExtremal sigma (loss index) family current →
        WZ2PaperConvexWolffBound family
          (Kakeya.realRpowENN delta (-(loss index))) →
        (∏ prior ∈ Finset.range index, leftFactor prior) * source.mass ≤
          (∏ prior ∈ Finset.range index, rightFactor prior) * current.mass →
        0 < current.mass →
        ∃ next : WZ1PaperTubeShading family,
          PaperIsSubshading next current ∧
          WZ1PaperIsCubicalShading next ∧
          (∀ point ∈ next.union,
            next.pointMultiplicity point = current.pointMultiplicity point) ∧
          WZ2PaperCroppedIsExtremal sigma (loss (index + 1)) family next ∧
          WZ2PaperConvexWolffBound family
            (Kakeya.realRpowENN delta (-(loss (index + 1)))) ∧
          PureWZ2IntervalCoveringAt next planeMap
            (scale (pair index).1 : ℝ)
            (scale (pair index).1) (scale (pair index).2)
            (ENNReal.ofReal
              (Real.rpow delta (-discreteLoss) *
                Real.rpow
                  ((scale (pair index).2 : ℝ) /
                    (scale (pair index).1 : ℝ))
                  (1 - sigma))) ∧
          leftFactor index * current.mass ≤ rightFactor index * next.mass)
    (hfinalLoss : loss stepCount = outputLoss)
    (hunit : ∀ point ∈ source.union, ‖planeMap point‖ = 1)
    (hquery : 0 < queryScale) (hqueryOne : queryScale ≤ 1)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hintervalLoss : 0 < intervalLoss) (houtputLoss : 0 < outputLoss)
    (hratio : 1 ≤ ratio)
    (hscaleZero : (scale 0 : ℝ) = queryScale)
    (hqueryScale : ∀ index, index ≤ gridN →
      queryScale ≤ (scale index : ℝ))
    (hscaleTop : (scale gridN : ℝ) = Real.sqrt queryScale)
    (hscalePos : ∀ index, index ≤ gridN → 0 < (scale index : ℝ))
    (hscaleMono : ∀ index, index < gridN →
      (scale index : ℝ) ≤ (scale (index + 1) : ℝ))
    (hscaleRatio : ∀ index, index < gridN →
      (scale (index + 1) : ℝ) ≤ ratio * (scale index : ℝ))
    (hscaleCovers : ∀ radius : ℝ, queryScale ≤ radius →
      radius ≤ Real.sqrt queryScale →
      ∃ index, index < gridN ∧ (scale index : ℝ) ≤ radius ∧
        radius ≤ (scale (index + 1) : ℝ))
    (hinterpolate : Real.rpow delta (-discreteLoss) *
      ratio ^ (1 - sigma) ≤ Real.rpow delta (-intervalLoss))
    (habsorb : (3 : ℝ) * Real.rpow delta (-intervalLoss) *
      ratio ^ (1 - sigma) ≤ Real.rpow delta (-outputLoss)) :
    ∃ data : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := outputLoss)
        (rho := queryScale) (Y := source) (fun point => planeMap point),
      (∀ point ∈ data.shading.union,
        data.shading.pointMultiplicity point = source.pointMultiplicity point) ∧
      (∏ index ∈ Finset.range stepCount, leftFactor index) * source.mass ≤
        (∏ index ∈ Finset.range stepCount, rightFactor index) *
          data.shading.mass ∧
      0 < data.shading.mass := by
  let resolution : ℕ → NNReal := fun index => scale (pair index).1
  let window : ℕ → NNReal := fun index => scale (pair index).2
  let spatialQuery : ℕ → ℝ := fun index => (scale (pair index).1 : ℝ)
  let bound : ℕ → ENNReal := fun index =>
    ENNReal.ofReal
      (Real.rpow delta (-discreteLoss) *
        Real.rpow
          ((scale (pair index).2 : ℝ) / (scale (pair index).1 : ℝ))
          (1 - sigma))
  rcases finite_interval_covering_iteration_of_mass_pos source planeMap
      spatialQuery stepCount resolution window bound loss leftFactor rightFactor
      hsourceCubical hsourceExtremal hsourceCWA hsourceMass hleftFactorPos
      step with
    ⟨final, hfinalSub, _hfinalCubical, hfinalMultiplicity,
      hfinalExtremal, hfinalCWA, hfinalCovering, hfinalMassLedger,
      hfinalMass⟩
  have hfinalExtremal' :
      WZ2PaperCroppedIsExtremal sigma outputLoss family final := by
    simpa [hfinalLoss] using hfinalExtremal
  have hfinalCWA' : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-outputLoss)) := by
    simpa [hfinalLoss] using hfinalCWA
  have hdiscrete : ∀ k j, k < j → j ≤ gridN →
      PureWZ2IntervalCoveringAt final planeMap queryScale
        (scale k) (scale j)
        (ENNReal.ofReal
          (Real.rpow delta (-discreteLoss) *
            Real.rpow ((scale j : ℝ) / (scale k : ℝ)) (1 - sigma))) := by
    intro k j hkj hjN
    rcases hpairComplete k j hkj hjN with ⟨index, hindex, hp⟩
    have hcover := hfinalCovering index hindex
    have hcover' : PureWZ2IntervalCoveringAt final planeMap (scale k : ℝ)
        (scale k) (scale j)
        (ENNReal.ofReal
          (Real.rpow delta (-discreteLoss) *
            Real.rpow ((scale j : ℝ) / (scale k : ℝ)) (1 - sigma))) := by
      simpa only [spatialQuery, resolution, window, bound, hp, Prod.fst,
        Prod.snd] using hcover
    exact pureWZ2IntervalCoveringAt_mono_queryScale
      (hqueryScale k (hkj.le.trans hjN)) hcover'
  let data := one_scale_local_grain_of_discrete_interval_pairs planeMap
    hfinalSub hfinalExtremal' hfinalCWA' hunit gridN scale hquery hqueryOne
    hdelta hdeltaOne hsigma hsigmaOne hintervalLoss houtputLoss hratio
    hscaleZero hscaleTop hscalePos hscaleMono hscaleRatio hscaleCovers
    hdiscrete hinterpolate habsorb
  exact ⟨data, by simpa only [data,
      one_scale_local_grain_of_discrete_interval_pairs,
      one_scale_local_grain_of_finite_interval_grid] using hfinalMultiplicity,
    by simpa only [data, one_scale_local_grain_of_discrete_interval_pairs,
        one_scale_local_grain_of_finite_interval_grid] using hfinalMassLedger,
    by simpa only [data, one_scale_local_grain_of_discrete_interval_pairs,
        one_scale_local_grain_of_finite_interval_grid] using hfinalMass⟩

namespace Proposition63InnerIntervalGridData

/-- Execute the already-constructed paper grid using its canonical complete
ordered-pair enumeration.  This adapter removes every remaining grid and
interpolation callback from the one-query terminal; the only input left is
the genuine geometric transition for one enumerated pair. -/
theorem runIteration
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN : ℕ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN)
    (source : WZ1PaperTubeShading family)
    (planeMap : Point3 → Point3)
    (loss : ℕ → ℝ)
    (leftFactor rightFactor : ℕ → ENNReal)
    (hsourceCubical : WZ1PaperIsCubicalShading source)
    (hsourceExtremal : WZ2PaperCroppedIsExtremal sigma (loss 0) family source)
    (hsourceCWA : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-(loss 0))))
    (hsourceMass : 0 < source.mass)
    (hleftFactorPos : ∀ index,
      index < (finiteIntervalOrderedPairs gridN).length →
        0 < leftFactor index)
    (step : ∀ index : ℕ,
      index < (finiteIntervalOrderedPairs gridN).length →
      ∀ current : WZ1PaperTubeShading family,
        PaperIsSubshading current source →
        WZ1PaperIsCubicalShading current →
        (∀ point ∈ current.union,
          current.pointMultiplicity point = source.pointMultiplicity point) →
        WZ2PaperCroppedIsExtremal sigma (loss index) family current →
        WZ2PaperConvexWolffBound family
          (Kakeya.realRpowENN delta (-(loss index))) →
        (∏ prior ∈ Finset.range index, leftFactor prior) * source.mass ≤
          (∏ prior ∈ Finset.range index, rightFactor prior) * current.mass →
        0 < current.mass →
        ∃ next : WZ1PaperTubeShading family,
          PaperIsSubshading next current ∧
          WZ1PaperIsCubicalShading next ∧
          (∀ point ∈ next.union,
            next.pointMultiplicity point = current.pointMultiplicity point) ∧
          WZ2PaperCroppedIsExtremal sigma (loss (index + 1)) family next ∧
          WZ2PaperConvexWolffBound family
            (Kakeya.realRpowENN delta (-(loss (index + 1)))) ∧
          PureWZ2IntervalCoveringAt next planeMap
            (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
            (grid.scale (finiteIntervalOrderedPair gridN index).1)
            (grid.scale (finiteIntervalOrderedPair gridN index).2)
            (ENNReal.ofReal
              (Real.rpow delta (-discreteLoss) *
                Real.rpow
                  ((grid.scale
                      (finiteIntervalOrderedPair gridN index).2 : ℝ) /
                    (grid.scale
                      (finiteIntervalOrderedPair gridN index).1 : ℝ))
                  (1 - sigma))) ∧
          leftFactor index * current.mass ≤ rightFactor index * next.mass)
    (hfinalLoss : loss (finiteIntervalOrderedPairs gridN).length =
      outputLoss)
    (hunit : ∀ point ∈ source.union, ‖planeMap point‖ = 1)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    ∃ data : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := outputLoss)
        (rho := queryScale) (Y := source) (fun point => planeMap point),
      (∀ point ∈ data.shading.union,
        data.shading.pointMultiplicity point = source.pointMultiplicity point) ∧
      (∏ index ∈ Finset.range (finiteIntervalOrderedPairs gridN).length,
          leftFactor index) * source.mass ≤
        (∏ index ∈ Finset.range (finiteIntervalOrderedPairs gridN).length,
          rightFactor index) * data.shading.mass ∧
      0 < data.shading.mass := by
  exact finite_interval_covering_iteration_to_one_scale source planeMap gridN
    (finiteIntervalOrderedPairs gridN).length grid.scale
    (finiteIntervalOrderedPair gridN) loss leftFactor rightFactor
    (fun k j hkj hjN => finiteIntervalOrderedPair_complete hkj hjN)
    hsourceCubical hsourceExtremal hsourceCWA hsourceMass hleftFactorPos step
    hfinalLoss hunit grid.query_pos grid.query_le_one hdelta hdeltaOne
    hsigma hsigmaOne grid.interval_loss_pos
    grid.output_loss_pos
    grid.ratio_one grid.scale_zero grid.query_le_scale grid.scale_top
    grid.scale_pos grid.scale_mono grid.scale_ratio grid.scale_covers
    grid.interpolate grid.absorb

end Proposition63InnerIntervalGridData

end Kakeya.Assouad.PureWZ2

end
