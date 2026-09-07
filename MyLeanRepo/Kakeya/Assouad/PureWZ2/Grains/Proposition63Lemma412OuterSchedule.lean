import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63Lemma411OneQuery
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63Lemma412

/-!
# Outer Lemma 4.12 schedule driven by the one-query producer

This module starts the outer dependent iteration.  The first adapter retains
the one-step mass receipt exported by Lemma 4.11, restricts the fixed weak
plane map to the new shading, and packages the result in the existing
one-scale full-grain interface.  Extremality is taken directly from the local
Lemma 4.11 output; the mass receipt is only an audit ledger.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- A backward-selected finite family of M7 schedules.  Coordinate `index`
starts at `loss index` and terminates at `loss (index + 1)`. -/
structure Proposition63Lemma411OuterScheduleData
    (sigma outputLoss : ℝ) (N : ℕ) where
  loss : ℕ → ℝ
  oneQuery : ∀ index, index < N →
    Proposition63Lemma411ScheduleData sigma (loss (index + 1))
  input_eq : ∀ index (hindex : index < N),
    (oneQuery index hindex).backward.loss 0 = loss index
  loss_mono : ∀ index, loss index ≤ loss (index + 1)
  loss_pos : ∀ index, index ≤ N → 0 < loss index
  loss_le_terminal : ∀ index, index ≤ N → loss index ≤ outputLoss
  final_loss : loss N = outputLoss

/-- Select the outer M7 loss hierarchy backwards.  Each inner grid/loss
schedule is fixed before any runtime root, query, or current shading. -/
theorem proposition63_lemma411_outer_schedule
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (outputLoss floorLoss : ℝ)
    (outputLoss_pos : 0 < outputLoss)
    (outputLoss_le_half : outputLoss ≤ 1 / 2)
    (floorLoss_pos : 0 < floorLoss)
    (outputLoss_lt_sigma : outputLoss < 2 * sigma / 5) :
    ∀ N, Nonempty (Proposition63Lemma411OuterScheduleData
      sigma outputLoss N) := by
  intro N
  induction N with
  | zero =>
      exact ⟨{
        loss := fun _ => outputLoss
        oneQuery := by intro index index_lt; omega
        input_eq := by intro index index_lt; omega
        loss_mono := fun _ => le_rfl
        loss_pos := by intro index index_le; exact outputLoss_pos
        loss_le_terminal := by intro index index_le; exact le_rfl
        final_loss := rfl
      }⟩
  | succ N inductionHypothesis =>
      rcases inductionHypothesis with ⟨tail⟩
      have tail_input_pos : 0 < tail.loss 0 := tail.loss_pos 0 (by omega)
      have tail_input_half : tail.loss 0 ≤ 1 / 2 :=
        (tail.loss_le_terminal 0 (by omega)).trans outputLoss_le_half
      have tail_input_sigma : tail.loss 0 < 2 * sigma / 5 :=
        (tail.loss_le_terminal 0 (by omega)).trans_lt outputLoss_lt_sigma
      let head := Classical.choice <| proposition63_lemma411_schedule sigma
        critical (tail.loss 0) floorLoss tail_input_pos tail_input_half
        floorLoss_pos tail_input_sigma
      let loss : ℕ → ℝ
        | 0 => head.backward.loss 0
        | index + 1 => tail.loss index
      have loss_zero : loss 0 = head.backward.loss 0 := rfl
      have loss_succ : ∀ index, loss (index + 1) = tail.loss index :=
        fun _ => rfl
      let oneQuery : ∀ index, index < N + 1 →
          Proposition63Lemma411ScheduleData sigma (loss (index + 1)) :=
        fun index index_lt => match index with
          | 0 => head
          | index + 1 => tail.oneQuery index (by omega)
      refine ⟨{
        loss := loss
        oneQuery := oneQuery
        input_eq := ?_
        loss_mono := ?_
        loss_pos := ?_
        loss_le_terminal := ?_
        final_loss := ?_
      }⟩
      · intro index index_lt
        rcases index with _ | index
        · rfl
        · exact tail.input_eq index (by omega)
      · intro index
        rcases index with _ | index
        · rw [loss_zero, loss_succ]
          exact head.backward.loss_le_terminal 0 (by omega)
        · rw [loss_succ, loss_succ]
          exact tail.loss_mono index
      · intro index index_le
        rcases index with _ | index
        · rw [loss_zero]
          exact head.backward.loss_pos 0 (by omega)
        · rw [loss_succ]
          exact tail.loss_pos index (by omega)
      · intro index index_le
        rcases index with _ | index
        · rw [loss_zero]
          exact (head.backward.loss_le_terminal 0 (by omega)).trans
            (tail.loss_le_terminal 0 (by omega))
        · rw [loss_succ]
          exact tail.loss_le_terminal index (by omega)
      · rw [loss_succ]
        exact tail.final_loss

/-- The central power-grid interval used by Lemma 4.12.  Only these
coordinates require the expensive Lemma 4.11 producer; interpolation handles
the two query endpoints. -/
structure Proposition63Lemma412CentralGridData
    (delta midLoss : ℝ) (N : ℕ) where
  kMin : ℕ
  kMax : ℕ
  N_pos : 0 < (N : ℝ)
  midLoss_pos : 0 < midLoss
  kMin_eq : kMin = Nat.ceil ((N : ℝ) * midLoss)
  kMin_le_kMax : kMin ≤ kMax
  kMax_lt_N : kMax < N
  kMax_lower : (N : ℝ) * (1 - midLoss) - 1 ≤ (kMax : ℝ)
  kMin_lower : (N : ℝ) * midLoss ≤ (kMin : ℝ)
  kMax_upper : (kMax : ℝ) ≤ (N : ℝ) * (1 - midLoss)
  admissible : ∀ k, kMin ≤ k ∧ k ≤ kMax →
    delta ≤ finiteGridScaleVal delta N k ∧
      finiteGridScaleVal delta N k ≤ 1

/-- Choose the canonical central interval from the paper loss margin. -/
theorem proposition63_lemma412_central_grid
    (delta midLoss : ℝ) (N : ℕ)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hmidLoss : 0 < midLoss) (hmidLossThird : midLoss ≤ 1 / 3)
    (hN : 9 ≤ N) :
    Nonempty (Proposition63Lemma412CentralGridData delta midLoss N) := by
  let kMin : ℕ := Nat.ceil ((N : ℝ) * midLoss)
  let kMax : ℕ := Nat.floor ((N : ℝ) * (1 - midLoss))
  have N_pos : 0 < (N : ℝ) := by positivity
  have one_sub_pos : 0 < 1 - midLoss := by linarith
  have product_nonneg : 0 ≤ (N : ℝ) * (1 - midLoss) := by positivity
  have kMin_lower : (N : ℝ) * midLoss ≤ (kMin : ℝ) :=
    Nat.le_ceil _
  have kMin_upper : (kMin : ℝ) < (N : ℝ) * midLoss + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have kMax_upper : (kMax : ℝ) ≤ (N : ℝ) * (1 - midLoss) :=
    Nat.floor_le product_nonneg
  have kMax_lower : (N : ℝ) * (1 - midLoss) - 1 ≤
      (kMax : ℝ) := by
    have h := Nat.lt_floor_add_one ((N : ℝ) * (1 - midLoss))
    linarith
  have kMin_le_kMax : kMin ≤ kMax := by
    have N_nine : (9 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have middle_gap : (N : ℝ) * midLoss + 1 ≤
        (N : ℝ) * (1 - midLoss) := by nlinarith
    have cast_lt : (kMin : ℝ) < (kMax : ℝ) + 1 := by linarith
    have nat_lt : kMin < kMax + 1 := by exact_mod_cast cast_lt
    omega
  have kMax_lt_N : kMax < N := by
    have product_lt : (N : ℝ) * (1 - midLoss) < (N : ℝ) := by
      nlinarith
    have cast_lt : (kMax : ℝ) < (N : ℝ) := kMax_upper.trans_lt product_lt
    exact_mod_cast cast_lt
  refine ⟨{
    kMin := kMin
    kMax := kMax
    N_pos := N_pos
    midLoss_pos := hmidLoss
    kMin_eq := rfl
    kMin_le_kMax := kMin_le_kMax
    kMax_lt_N := kMax_lt_N
    kMax_lower := kMax_lower
    kMin_lower := kMin_lower
    kMax_upper := kMax_upper
    admissible := ?_
  }⟩
  intro k hk
  have kMin_cast : (kMin : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
  have kMax_cast : (k : ℝ) ≤ (kMax : ℝ) := by exact_mod_cast hk.2
  have exponent_nonneg : 0 ≤ 1 - (k : ℝ) / (N : ℝ) := by
    have quotient_le : (k : ℝ) / (N : ℝ) ≤ 1 - midLoss := by
      calc
        (k : ℝ) / (N : ℝ) ≤ (kMax : ℝ) / (N : ℝ) := by
          exact div_le_div_of_nonneg_right kMax_cast N_pos.le
        _ ≤ ((N : ℝ) * (1 - midLoss)) / (N : ℝ) := by
          exact div_le_div_of_nonneg_right kMax_upper N_pos.le
        _ = 1 - midLoss := by field_simp [ne_of_gt N_pos]
    linarith
  have exponent_le_one : 1 - (k : ℝ) / (N : ℝ) ≤ 1 := by
    have k_nonneg : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have quotient_nonneg : 0 ≤ (k : ℝ) / (N : ℝ) :=
      div_nonneg k_nonneg N_pos.le
    linarith
  constructor
  · change delta ≤ Real.rpow delta (1 - (k : ℝ) / (N : ℝ))
    have h := Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne
      exponent_le_one
    simpa using h
  · change Real.rpow delta (1 - (k : ℝ) / (N : ℝ)) ≤ 1
    have h := Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne
      exponent_nonneg
    simpa using h

/-- Number of genuinely nontrivial outer coordinates. -/
def Proposition63Lemma412CentralGridData.count
    {delta midLoss : ℝ} {N : ℕ}
    (data : Proposition63Lemma412CentralGridData delta midLoss N) : ℕ :=
  data.kMax - data.kMin + 1

/-- Translate a local iteration coordinate to its paper power-grid index. -/
def Proposition63Lemma412CentralGridData.globalIndex
    {delta midLoss : ℝ} {N : ℕ}
    (data : Proposition63Lemma412CentralGridData delta midLoss N)
    (index : ℕ) : ℕ :=
  data.kMin + index

theorem Proposition63Lemma412CentralGridData.globalIndex_range
    {delta midLoss : ℝ} {N : ℕ}
    (data : Proposition63Lemma412CentralGridData delta midLoss N)
    {index : ℕ} (hindex : index < data.count) :
    data.kMin ≤ data.globalIndex index ∧
      data.globalIndex index ≤ data.kMax := by
  dsimp [Proposition63Lemma412CentralGridData.count,
    Proposition63Lemma412CentralGridData.globalIndex] at *
  have hbounds := data.kMin_le_kMax
  omega

theorem Proposition63Lemma412CentralGridData.globalIndex_lt_N
    {delta midLoss : ℝ} {N : ℕ}
    (data : Proposition63Lemma412CentralGridData delta midLoss N)
    {index : ℕ} (hindex : index < data.count) :
    data.globalIndex index < N :=
  (data.globalIndex_range hindex).2.trans_lt data.kMax_lt_N

/-- The canonical requested scale at a central outer coordinate. -/
noncomputable def Proposition63Lemma412CentralGridData.query
    {delta midLoss : ℝ} {N : ℕ}
    (data : Proposition63Lemma412CentralGridData delta midLoss N)
    (index : ℕ) (hindex : index < data.count) :
    WZ2PaperRequestedScale delta :=
  ⟨finiteGridScaleVal delta N (data.globalIndex index),
    data.admissible _ (data.globalIndex_range hindex)⟩

/-- A central power-grid scale lies in every M7 window whose output loss is
at most the central margin. -/
theorem Proposition63Lemma412CentralGridData.query_window
    {delta midLoss loss : ℝ} {N : ℕ}
    (data : Proposition63Lemma412CentralGridData delta midLoss N)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    {index : ℕ} (hindex : index < data.count)
    (hloss : loss ≤ midLoss) :
    Real.rpow delta (1 - loss) ≤ (data.query index hindex).1 ∧
      (data.query index hindex).1 ≤ Real.rpow delta loss := by
  have hkRange := data.globalIndex_range hindex
  have hkMinCast : (data.kMin : ℝ) ≤ (data.globalIndex index : ℝ) := by
    exact_mod_cast hkRange.1
  have hkMaxCast : (data.globalIndex index : ℝ) ≤ (data.kMax : ℝ) := by
    exact_mod_cast hkRange.2
  have hmidLower : midLoss ≤
      (data.globalIndex index : ℝ) / (N : ℝ) := by
    calc
      midLoss = ((N : ℝ) * midLoss) / (N : ℝ) := by
        field_simp [ne_of_gt data.N_pos]
      _ ≤ (data.kMin : ℝ) / (N : ℝ) := by
        exact div_le_div_of_nonneg_right data.kMin_lower data.N_pos.le
      _ ≤ (data.globalIndex index : ℝ) / (N : ℝ) := by
        exact div_le_div_of_nonneg_right hkMinCast data.N_pos.le
  have hmidUpper : (data.globalIndex index : ℝ) / (N : ℝ) ≤
      1 - midLoss := by
    calc
      (data.globalIndex index : ℝ) / (N : ℝ) ≤
          (data.kMax : ℝ) / (N : ℝ) := by
        exact div_le_div_of_nonneg_right hkMaxCast data.N_pos.le
      _ ≤ ((N : ℝ) * (1 - midLoss)) / (N : ℝ) := by
        exact div_le_div_of_nonneg_right data.kMax_upper data.N_pos.le
      _ = 1 - midLoss := by field_simp [ne_of_gt data.N_pos]
  constructor
  · change Real.rpow delta (1 - loss) ≤
      Real.rpow delta (1 - (data.globalIndex index : ℝ) / (N : ℝ))
    exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)
  · change Real.rpow delta
        (1 - (data.globalIndex index : ℝ) / (N : ℝ)) ≤
      Real.rpow delta loss
    exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)

/-- Reuse the already frozen central index interval at a new positive scale.
Only the admissibility proof changes; `kMin`, `kMax`, and therefore `count`
remain definitionally unchanged. -/
def Proposition63Lemma412CentralGridData.rebase
    {baseDelta midLoss : ℝ} {N : ℕ}
    (data : Proposition63Lemma412CentralGridData baseDelta midLoss N)
    (delta : ℝ) (delta_pos : 0 < delta) (delta_le_one : delta ≤ 1) :
    Proposition63Lemma412CentralGridData delta midLoss N where
  kMin := data.kMin
  kMax := data.kMax
  N_pos := data.N_pos
  midLoss_pos := data.midLoss_pos
  kMin_eq := data.kMin_eq
  kMin_le_kMax := data.kMin_le_kMax
  kMax_lt_N := data.kMax_lt_N
  kMax_lower := data.kMax_lower
  kMin_lower := data.kMin_lower
  kMax_upper := data.kMax_upper
  admissible := by
    intro k hk
    have kMax_cast : (k : ℝ) ≤ (data.kMax : ℝ) := by
      exact_mod_cast hk.2
    have exponent_nonneg : 0 ≤ 1 - (k : ℝ) / (N : ℝ) := by
      have quotient_le : (k : ℝ) / (N : ℝ) ≤ 1 - midLoss := by
        calc
          (k : ℝ) / (N : ℝ) ≤ (data.kMax : ℝ) / (N : ℝ) := by
            exact div_le_div_of_nonneg_right kMax_cast data.N_pos.le
          _ ≤ ((N : ℝ) * (1 - midLoss)) / (N : ℝ) := by
            exact div_le_div_of_nonneg_right data.kMax_upper data.N_pos.le
          _ = 1 - midLoss := by field_simp [ne_of_gt data.N_pos]
      linarith [data.midLoss_pos]
    have exponent_le_one : 1 - (k : ℝ) / (N : ℝ) ≤ 1 := by
      have quotient_nonneg : 0 ≤ (k : ℝ) / (N : ℝ) := by positivity
      linarith
    constructor
    · change delta ≤ Real.rpow delta (1 - (k : ℝ) / (N : ℝ))
      simpa using Real.rpow_le_rpow_of_exponent_ge delta_pos delta_le_one
        exponent_le_one
    · change Real.rpow delta (1 - (k : ℝ) / (N : ℝ)) ≤ 1
      simpa using Real.rpow_le_rpow_of_exponent_ge delta_pos delta_le_one
        exponent_nonneg

@[simp] theorem Proposition63Lemma412CentralGridData.rebase_count
    {baseDelta midLoss delta : ℝ} {N : ℕ}
    (data : Proposition63Lemma412CentralGridData baseDelta midLoss N)
    (delta_pos : 0 < delta) (delta_le_one : delta ≤ 1) :
    (data.rebase delta delta_pos delta_le_one).count = data.count := rfl

/-- All discrete choices for M8: the canonical central power-grid interval
and the backward M7 loss hierarchy on exactly that interval. -/
structure Proposition63Lemma412ScheduleData
    (sigma gridLoss delta midLoss : ℝ) (N : ℕ) where
  central : Proposition63Lemma412CentralGridData delta midLoss N
  outer : Proposition63Lemma411OuterScheduleData
    sigma gridLoss central.count

/-- The complete M8 discrete schedule before Node 3 selects the runtime
scale.  A unit-scale template fixes the central indices and hence the exact
number of M7 schedules; `specialize` below only re-establishes their power
grid admissibility at the realized scale. -/
structure Proposition63Lemma412PreRuntimeScheduleData
    (sigma gridLoss midLoss : ℝ) (N : ℕ) where
  centralTemplate : Proposition63Lemma412CentralGridData 1 midLoss N
  outer : Proposition63Lemma411OuterScheduleData
    sigma gridLoss centralTemplate.count

/-- Freeze the M8 central indices and every nested M7 loss schedule before a
runtime fine scale exists. -/
theorem proposition63_lemma412_pre_runtime_schedule
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (gridLoss floorLoss midLoss : ℝ) (N : ℕ)
    (gridLoss_pos : 0 < gridLoss)
    (gridLoss_le_half : gridLoss ≤ 1 / 2)
    (floorLoss_pos : 0 < floorLoss)
    (gridLoss_lt_sigma : gridLoss < 2 * sigma / 5)
    (midLoss_pos : 0 < midLoss) (midLoss_le_third : midLoss ≤ 1 / 3)
    (N_ge_nine : 9 ≤ N) :
    Nonempty (Proposition63Lemma412PreRuntimeScheduleData
      sigma gridLoss midLoss N) := by
  rcases proposition63_lemma412_central_grid 1 midLoss N (by norm_num)
      le_rfl midLoss_pos midLoss_le_third N_ge_nine with ⟨centralTemplate⟩
  rcases proposition63_lemma411_outer_schedule sigma critical gridLoss
      floorLoss gridLoss_pos gridLoss_le_half floorLoss_pos
      gridLoss_lt_sigma centralTemplate.count with ⟨outer⟩
  exact ⟨{ centralTemplate := centralTemplate, outer := outer }⟩

/-- Materialize the frozen M8 index/schedule package at the scale selected by
Node 3. -/
def Proposition63Lemma412PreRuntimeScheduleData.specialize
    {sigma gridLoss midLoss delta : ℝ} {N : ℕ}
    (data : Proposition63Lemma412PreRuntimeScheduleData
      sigma gridLoss midLoss N)
    (delta_pos : 0 < delta) (delta_le_one : delta ≤ 1) :
    Proposition63Lemma412ScheduleData sigma gridLoss delta midLoss N where
  central := data.centralTemplate.rebase delta delta_pos delta_le_one
  outer := data.outer

/-- Freeze the M8 grid interval and every nested M7 loss schedule before any
runtime shading is exposed. -/
theorem proposition63_lemma412_schedule
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (gridLoss floorLoss delta midLoss : ℝ) (N : ℕ)
    (gridLoss_pos : 0 < gridLoss)
    (gridLoss_le_half : gridLoss ≤ 1 / 2)
    (floorLoss_pos : 0 < floorLoss)
    (gridLoss_lt_sigma : gridLoss < 2 * sigma / 5)
    (delta_pos : 0 < delta) (delta_le_one : delta ≤ 1)
    (midLoss_pos : 0 < midLoss) (midLoss_le_third : midLoss ≤ 1 / 3)
    (N_ge_nine : 9 ≤ N) :
    Nonempty (Proposition63Lemma412ScheduleData
      sigma gridLoss delta midLoss N) := by
  rcases proposition63_lemma412_central_grid delta midLoss N delta_pos
      delta_le_one midLoss_pos midLoss_le_third N_ge_nine with ⟨central⟩
  rcases proposition63_lemma411_outer_schedule sigma critical gridLoss
      floorLoss gridLoss_pos gridLoss_le_half floorLoss_pos
      gridLoss_lt_sigma central.count with ⟨outer⟩
  exact ⟨{ central := central, outer := outer }⟩

/-- Canonical ordinary source loss used to retarget one ambient re-entry to
the root normalization required by an M7 schedule. -/
noncomputable def Proposition63Lemma411ScheduleData.rootSourceLoss
    {sigma outputLoss : ℝ}
    (schedule : Proposition63Lemma411ScheduleData sigma outputLoss) : ℝ :=
  schedule.backward.rootNormalizationLoss / 4

theorem Proposition63Lemma411ScheduleData.rootSourceLoss_pos
    {sigma outputLoss : ℝ}
    (schedule : Proposition63Lemma411ScheduleData sigma outputLoss) :
    0 < schedule.rootSourceLoss := by
  dsimp [Proposition63Lemma411ScheduleData.rootSourceLoss,
    Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
  exact div_pos (div_pos schedule.backward.rootBudget_pos (by norm_num))
    (by norm_num)

theorem Proposition63Lemma411ScheduleData.rootNormalizationLoss_pos
    {sigma outputLoss : ℝ}
    (schedule : Proposition63Lemma411ScheduleData sigma outputLoss) :
    0 < schedule.backward.rootNormalizationLoss := by
  dsimp [Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
  exact div_pos schedule.backward.rootBudget_pos (by norm_num)

theorem Proposition63Lemma411ScheduleData.rootSourceLoss_le_half
    {sigma outputLoss : ℝ}
    (schedule : Proposition63Lemma411ScheduleData sigma outputLoss) :
    schedule.rootSourceLoss ≤ schedule.backward.rootNormalizationLoss / 2 := by
  dsimp [Proposition63Lemma411ScheduleData.rootSourceLoss]
  linarith [schedule.rootNormalizationLoss_pos]

/-- Exact scalar receipts needed to retarget a shared ambient re-entry to one
M7 schedule.  The strict `1/8` axial certificate is kept separately because
the generic re-entry record only stores the weaker `1/4` window. -/
structure Proposition63Lemma411OuterRootBindingData
    {sigma outputLoss delta ambientSourceLoss ambientNormalizationLoss : ℝ}
    {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {normalizationExponent : ℕ}
    (schedule : Proposition63Lemma411ScheduleData sigma outputLoss)
    (ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) ambientShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss) where
  ambient_source_le : ambientSourceLoss ≤ schedule.rootSourceLoss
  ambient_normalization_le :
    ambientNormalizationLoss ≤ schedule.backward.rootNormalizationLoss
  density_absorb :
    Kakeya.realRpowENN delta schedule.backward.rootDensityLoss ≤
      Kakeya.realRpowENN delta schedule.rootSourceLoss / 2

noncomputable def Proposition63Lemma411OuterRootBindingData.scheduledReentry
    {sigma outputLoss delta ambientSourceLoss ambientNormalizationLoss : ℝ}
    {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {normalizationExponent : ℕ}
    {schedule : Proposition63Lemma411ScheduleData sigma outputLoss}
    {ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) ambientShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss}
    (data : Proposition63Lemma411OuterRootBindingData schedule
      ambientReentry) :
    PureWZ2PropStickyReentryData (sigma := sigma) ambientShading
      normalizationExponent schedule.rootSourceLoss
        schedule.backward.rootNormalizationLoss :=
  ambientReentry.mono_losses data.ambient_source_le
    data.ambient_normalization_le schedule.rootSourceLoss_pos
    schedule.rootNormalizationLoss_pos schedule.rootSourceLoss_le_half

noncomputable def Proposition63Lemma411OuterRootBindingData.root
    {sigma outputLoss delta ambientSourceLoss ambientNormalizationLoss : ℝ}
    {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {normalizationExponent : ℕ}
    {schedule : Proposition63Lemma411ScheduleData sigma outputLoss}
    {ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) ambientShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss}
    (data : Proposition63Lemma411OuterRootBindingData schedule
      ambientReentry) :
    Proposition63RootNormalizationData
      (outputLoss := schedule.backward.rootNormalizationLoss)
      data.scheduledReentry.ordinarySource normalizationExponent
        schedule.backward.rootDensityLoss :=
  Proposition63RootNormalizationData.ofPropStickyReentry
    data.scheduledReentry data.density_absorb

theorem Proposition63Lemma411OuterRootBindingData.rootInput
    {sigma outputLoss delta ambientSourceLoss ambientNormalizationLoss : ℝ}
    {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {normalizationExponent : ℕ}
    {schedule : Proposition63Lemma411ScheduleData sigma outputLoss}
    {ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) ambientShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss}
    (data : Proposition63Lemma411OuterRootBindingData schedule
      ambientReentry)
    (ambientAxialEighth : ∀ index point,
      point ∈ ambientReentry.geometry.frame ''
          ambientReentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8) :
    Proposition63FourCallRootInput data.root := by
  refine ⟨?_⟩
  intro index point point_mem
  simpa [Proposition63Lemma411OuterRootBindingData.root,
    Proposition63Lemma411OuterRootBindingData.scheduledReentry,
    Proposition63RootNormalizationData.ofPropStickyReentry,
    Proposition63RootNormalizationData.ofNormalization,
    PureWZ2PropStickyReentryData.mono_losses,
    PureWZ2PropStickyReentryData.toNormalizationData] using
      ambientAxialEighth index point point_mem

/-- Promote one receipt-bearing Lemma 4.11 output to the one-scale interface
used by the finite Lemma 4.12 recursion. -/
theorem Proposition63Lemma411OneQueryStepData.toExtremalOneScaleFullGrain
    {delta sigma outputLoss queryScale incidence spatialScale
      variationScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {current : WZ1PaperTubeShading family}
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (coefficient : NNReal)
    (currentLipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ current.union} =>
        currentMap.planeMap point))
    (step : Proposition63Lemma411OneQueryStepData
      (sigma := sigma) (outputLoss := outputLoss)
      (queryScale := queryScale) current
      (fun point => currentMap.planeMap point))
    (variation_budget :
      (coefficient : ℝ) * spatialScale ≤ variationScale) :
    Nonempty (Proposition63ExtremalOneScaleFullGrainData
      (sigma := sigma) current currentMap outputLoss queryScale
        spatialScale variationScale) := by
  let nextMap := paperWeakPlaneMapRestrict currentMap step.oneQuery.subshading
  refine ⟨{
    shading := step.oneQuery.shading
    subshading := step.oneQuery.subshading
    cubical := step.oneQuery.extremal.cubical
    planeMap := nextMap
    same_plane_map := rfl
    variation := ?_
    local_ad := ?_
    massLoss := step.massLoss
    massLoss_pos := step.massLoss_pos
    massLoss_ne_top := step.massLoss_ne_top
    mass_retention := step.mass_retention
    extremal := step.oneQuery.extremal
  }⟩
  · intro first first_mem second second_mem distance_bound
    change dist (currentMap.planeMap first) (currentMap.planeMap second) ≤
      variationScale
    have hlipschitz := currentLipschitz.dist_le_mul
      ⟨first, paperSubshading_union step.oneQuery.subshading first_mem⟩
      ⟨second, paperSubshading_union step.oneQuery.subshading second_mem⟩
    calc
      dist (currentMap.planeMap first) (currentMap.planeMap second) ≤
          (coefficient : ℝ) * dist first second := by
        simpa only [Subtype.dist_eq] using hlipschitz
      _ ≤ (coefficient : ℝ) * spatialScale := by
        exact mul_le_mul_of_nonneg_left distance_bound (by positivity)
      _ ≤ variationScale := variation_budget
  · intro point point_mem
    change IsADSet1
      (scalarProjection (currentMap.planeMap point)
        (step.oneQuery.shading.union ∩
          Metric.closedBall point (Real.sqrt queryScale)))
      queryScale (1 - sigma)
      (Kakeya.realRpowENN delta (-outputLoss))
    exact step.oneQuery.local_ad point point_mem

/-- All pre-current data for one outer coordinate.  The root is the exact
loss-retargeted view of the shared ambient re-entry, while the query and its
M7 smallness receipt are fixed before the active shading is exposed. -/
structure Proposition63Lemma411OuterCoordinateData
    {sigma outputLoss delta ambientSourceLoss ambientNormalizationLoss
      incidence : ℝ}
    {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {normalizationExponent : ℕ}
    {N : ℕ}
    (outer : Proposition63Lemma411OuterScheduleData sigma outputLoss N)
    (ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) ambientShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss)
    (K : ℝ) (sourceCoefficient : NNReal)
    (index : ℕ) (hindex : index < N) where
  rootBinding : Proposition63Lemma411OuterRootBindingData
    (outer.oneQuery index hindex) ambientReentry
  query : WZ2PaperRequestedScale delta
  delta_le_grid :
    delta ≤ (outer.oneQuery index hindex).gridSchedule.delta₀
  query_lower : Real.rpow delta (1 - outer.loss (index + 1)) ≤ query.1
  query_upper : query.1 ≤ Real.rpow delta (outer.loss (index + 1))
  smallness : Proposition63Lemma411UniformSmallnessData (K := K)
    (incidence := incidence) (outer.oneQuery index hindex).backward
    rootBinding.root
    ((outer.oneQuery index hindex).runtimeGrid query
      rootBinding.root.normalization.final_extremal.delta_pos delta_le_grid
      query_lower query_upper) sourceCoefficient

/-- Execute one pre-bound outer coordinate on the actual current shading. -/
theorem Proposition63Lemma411OuterCoordinateData.run
    {sigma outputLoss delta ambientSourceLoss ambientNormalizationLoss
      incidence : ℝ}
    {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading mapShading : WZ1PaperTubeShading ambientFamily}
    {normalizationExponent N : ℕ}
    {outer : Proposition63Lemma411OuterScheduleData sigma outputLoss N}
    {ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) ambientShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss}
    {K : ℝ} {sourceCoefficient : NNReal}
    {index : ℕ} {hindex : index < N}
    (coordinate : Proposition63Lemma411OuterCoordinateData
      (incidence := incidence) outer
      ambientReentry K sourceCoefficient index hindex)
    (ambientAxialEighth : ∀ tube point,
      point ∈ ambientReentry.geometry.frame ''
          ambientReentry.geometry.ordinaryRefined.carrier tube →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (sourceMap : PaperWZ1WeakPlaneMapData mapShading incidence)
    (sourceLipschitz : LipschitzWith sourceCoefficient
      (fun point : {point : Point3 // point ∈ mapShading.union} =>
        sourceMap.planeMap point))
    (active : WZ1PaperTubeShading ambientFamily)
    (active_sub_map : PaperIsSubshading active mapShading)
    (active_sub_ambient : PaperIsSubshading active ambientShading)
    (active_extremal : WZ2PaperCroppedIsExtremal
      sigma (outer.loss index) ambientFamily active)
    (active_cwa : WZ2PaperConvexWolffBound ambientFamily
      (Kakeya.realRpowENN delta (-(outer.loss index))))
    (active_mass_pos : 0 < active.mass) :
    Nonempty (Proposition63Lemma411OneQueryStepData
      (sigma := sigma) (outputLoss := outer.loss (index + 1))
      (queryScale := coordinate.query.1) active
      (fun point => sourceMap.planeMap point)) := by
  let activeMap := paperWeakPlaneMapRestrict sourceMap active_sub_map
  have activeLipschitz : LipschitzWith sourceCoefficient
      (fun point : {point : Point3 // point ∈ active.union} =>
        activeMap.planeMap point) := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    have h := sourceLipschitz.dist_le_mul
      ⟨first, paperSubshading_union active_sub_map first.property⟩
      ⟨second, paperSubshading_union active_sub_map second.property⟩
    simpa only [activeMap, paperWeakPlaneMapRestrict, Subtype.dist_eq] using h
  have active_sub_root : PaperIsSubshading active
      coordinate.rootBinding.root.normalization.croppedRefined := by
    simpa [Proposition63Lemma411OuterRootBindingData.root,
      Proposition63Lemma411OuterRootBindingData.scheduledReentry,
      Proposition63RootNormalizationData.ofPropStickyReentry,
      Proposition63RootNormalizationData.ofNormalization,
      PureWZ2PropStickyReentryData.mono_losses,
      PureWZ2PropStickyReentryData.toNormalizationData] using
        active_sub_ambient
  have active_extremal' : WZ2PaperCroppedIsExtremal sigma
      ((outer.oneQuery index hindex).backward.loss 0)
      coordinate.rootBinding.root.normalization.croppedFamily active := by
    rw [outer.input_eq index hindex]
    simpa [Proposition63Lemma411OuterRootBindingData.root,
      Proposition63Lemma411OuterRootBindingData.scheduledReentry,
      Proposition63RootNormalizationData.ofPropStickyReentry,
      Proposition63RootNormalizationData.ofNormalization,
      PureWZ2PropStickyReentryData.mono_losses,
      PureWZ2PropStickyReentryData.toNormalizationData] using active_extremal
  have active_cwa' : WZ2PaperConvexWolffBound
      coordinate.rootBinding.root.normalization.croppedFamily
      (Kakeya.realRpowENN delta
        (-((outer.oneQuery index hindex).backward.loss 0))) := by
    rw [outer.input_eq index hindex]
    simpa [Proposition63Lemma411OuterRootBindingData.root,
      Proposition63Lemma411OuterRootBindingData.scheduledReentry,
      Proposition63RootNormalizationData.ofPropStickyReentry,
      Proposition63RootNormalizationData.ofNormalization,
      PureWZ2PropStickyReentryData.mono_losses,
      PureWZ2PropStickyReentryData.toNormalizationData] using active_cwa
  have result := (outer.oneQuery index hindex).runWithReceipt K
    coordinate.rootBinding.root
    (coordinate.rootBinding.rootInput ambientAxialEighth) coordinate.query
    coordinate.delta_le_grid coordinate.query_lower coordinate.query_upper
    sourceCoefficient coordinate.smallness active active_sub_root activeMap
    activeLipschitz active_extremal' active_cwa' active_mass_pos
  rcases result with ⟨result⟩
  let oneQuery : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := outer.loss (index + 1))
      (rho := coordinate.query.1) (Y := active)
      (fun point => sourceMap.planeMap point) := {
    shading := result.oneQuery.shading
    subshading := result.oneQuery.subshading
    extremal := result.oneQuery.extremal
    cwa := result.oneQuery.cwa
    local_ad := by
      intro point point_mem
      change IsADSet1
        (scalarProjection (activeMap.planeMap point)
          (result.oneQuery.shading.union ∩
            Metric.closedBall point (Real.sqrt coordinate.query.1)))
        coordinate.query.1 (1 - sigma)
        (Kakeya.realRpowENN delta (-(outer.loss (index + 1))))
      exact result.oneQuery.local_ad point point_mem
  }
  exact ⟨{
    oneQuery := oneQuery
    massLoss := result.massLoss
    massLoss_pos := result.massLoss_pos
    massLoss_ne_top := result.massLoss_ne_top
    mass_retention := result.mass_retention
    shading_mass_pos := result.shading_mass_pos
  }⟩

/-- A finite family of M7 coordinates, all fixed before the outer recursion
exposes its successive current shadings. -/
structure Proposition63Lemma411OuterBindingData
    {sigma outputLoss delta ambientSourceLoss ambientNormalizationLoss
      incidence : ℝ}
    {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {normalizationExponent N : ℕ}
    (outer : Proposition63Lemma411OuterScheduleData sigma outputLoss N)
    (ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) ambientShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss)
    (K : ℝ) (sourceCoefficient : NNReal) where
  coordinate : ∀ index (hindex : index < N),
    Proposition63Lemma411OuterCoordinateData (incidence := incidence) outer
      ambientReentry K sourceCoefficient index hindex

/-- The requested scale of a bound coordinate, extended arbitrarily outside
the finite outer range. -/
noncomputable def Proposition63Lemma411OuterBindingData.queryScale
    {sigma outputLoss delta ambientSourceLoss ambientNormalizationLoss
      incidence : ℝ}
    {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {normalizationExponent N : ℕ}
    {outer : Proposition63Lemma411OuterScheduleData sigma outputLoss N}
    {ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) ambientShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss}
    {K : ℝ} {sourceCoefficient : NNReal}
    (data : Proposition63Lemma411OuterBindingData (incidence := incidence)
      outer ambientReentry K sourceCoefficient) (index : ℕ) : ℝ :=
  if hindex : index < N then (data.coordinate index hindex).query.1 else 1

/-- The genuinely external receipts for the central M7 coordinates.  The
query scales and their two-sided paper windows are not fields: they are
canonically generated from the central power grid below. -/
structure Proposition63Lemma411OuterBindingInputs
    {sigma gridLoss delta midLoss ambientSourceLoss ambientNormalizationLoss
      incidence : ℝ}
    {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {normalizationExponent N : ℕ}
    (central : Proposition63Lemma412CentralGridData delta midLoss N)
    (outer : Proposition63Lemma411OuterScheduleData
      sigma gridLoss central.count)
    (ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) ambientShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss)
    (K : ℝ) (sourceCoefficient : NNReal)
    (hgridLossMid : gridLoss ≤ midLoss) where
  rootBinding : ∀ index (hindex : index < central.count),
    Proposition63Lemma411OuterRootBindingData
      (outer.oneQuery index hindex) ambientReentry
  delta_le_grid : ∀ index (hindex : index < central.count),
    delta ≤ (outer.oneQuery index hindex).gridSchedule.delta₀
  smallness : ∀ index (hindex : index < central.count),
    let loss_le_mid :=
      (outer.loss_le_terminal (index + 1) (by omega)).trans hgridLossMid
    let window := central.query_window
      (rootBinding index hindex).root.normalization.final_extremal.delta_pos
      (rootBinding index hindex).root.normalization.final_extremal.delta_le_one
      hindex loss_le_mid
    Proposition63Lemma411UniformSmallnessData (K := K)
      (incidence := incidence) (outer.oneQuery index hindex).backward
      (rootBinding index hindex).root
      ((outer.oneQuery index hindex).runtimeGrid
        (central.query index hindex)
        (rootBinding index hindex).root.normalization.final_extremal.delta_pos
        (delta_le_grid index hindex) window.1 window.2) sourceCoefficient

/-- A central binding together with the definitional identification of its
queries with the original Lemma 4.12 power grid. -/
structure Proposition63Lemma411CentralBindingData
    {sigma gridLoss delta midLoss ambientSourceLoss ambientNormalizationLoss
      incidence : ℝ}
    {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {normalizationExponent N : ℕ}
    (central : Proposition63Lemma412CentralGridData delta midLoss N)
    (outer : Proposition63Lemma411OuterScheduleData
      sigma gridLoss central.count)
    (ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) ambientShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss)
    (K : ℝ) (sourceCoefficient : NNReal) where
  binding : Proposition63Lemma411OuterBindingData (incidence := incidence)
    outer ambientReentry K sourceCoefficient
  query_eq : ∀ index (_hindex : index < central.count),
    binding.queryScale index =
      finiteGridScaleVal delta N (central.globalIndex index)

/-- Construct every central outer coordinate from the honest cutoff/root
receipts.  In particular the query is chosen here, and both M7 power-window
bounds follow from the central-grid exponent range. -/
theorem proposition63_lemma411_central_binding
    {sigma gridLoss delta midLoss ambientSourceLoss ambientNormalizationLoss
      incidence : ℝ}
    {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {normalizationExponent N : ℕ}
    (central : Proposition63Lemma412CentralGridData delta midLoss N)
    (outer : Proposition63Lemma411OuterScheduleData
      sigma gridLoss central.count)
    (ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) ambientShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss)
    (K : ℝ) (sourceCoefficient : NNReal)
    (hgridLossMid : gridLoss ≤ midLoss)
    (inputs : Proposition63Lemma411OuterBindingInputs (incidence := incidence)
      central outer ambientReentry K sourceCoefficient hgridLossMid) :
    Nonempty (Proposition63Lemma411CentralBindingData (incidence := incidence)
      central outer ambientReentry K sourceCoefficient) := by
  let coordinate : ∀ index (hindex : index < central.count),
      Proposition63Lemma411OuterCoordinateData (incidence := incidence) outer
        ambientReentry K sourceCoefficient index hindex := fun index hindex => by
    let loss_le_mid :=
      (outer.loss_le_terminal (index + 1) (by omega)).trans hgridLossMid
    let window := central.query_window
      (inputs.rootBinding index hindex).root.normalization.final_extremal.delta_pos
      (inputs.rootBinding index hindex).root.normalization.final_extremal.delta_le_one
      hindex loss_le_mid
    exact {
      rootBinding := inputs.rootBinding index hindex
      query := central.query index hindex
      delta_le_grid := inputs.delta_le_grid index hindex
      query_lower := window.1
      query_upper := window.2
      smallness := inputs.smallness index hindex
    }
  let binding : Proposition63Lemma411OuterBindingData (incidence := incidence)
      outer ambientReentry K sourceCoefficient := ⟨coordinate⟩
  refine ⟨{ binding := binding, query_eq := ?_ }⟩
  intro index hindex
  rw [Proposition63Lemma411OuterBindingData.queryScale, dif_pos hindex]
  rfl

/-- Stateful outer recursion for Lemma 4.12.  Each step receives the actual
current shading together with its root ancestry, restored extremality/CWA, and
positive mass.  Earlier one-query AD estimates are transported only through
the genuine subshading returned by the next M7 call. -/
theorem proposition63_lemma411_outer_iteration
    {delta sigma incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading mapShading current : WZ1PaperTubeShading family}
    (sourceMap : PaperWZ1WeakPlaneMapData mapShading incidence)
    (sourceCoefficient : NNReal)
    (sourceLipschitz : LipschitzWith sourceCoefficient
      (fun point : {point : Point3 // point ∈ mapShading.union} =>
        sourceMap.planeMap point))
    (current_sub_map : PaperIsSubshading current mapShading)
    (current_sub_ambient : PaperIsSubshading current ambientShading)
    (loss : ℕ → ℝ) (N : ℕ)
    (queryScale spatialScale variationScale : ℕ → ℝ)
    (loss_mono : ∀ index, loss index ≤ loss (index + 1))
    (current_extremal : WZ2PaperCroppedIsExtremal
      sigma (loss 0) family current)
    (current_cwa : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-(loss 0))))
    (current_mass_pos : 0 < current.mass)
    (step : ∀ index, index < N →
      ∀ active : WZ1PaperTubeShading family,
        PaperIsSubshading active mapShading →
        PaperIsSubshading active ambientShading →
        WZ2PaperCroppedIsExtremal sigma (loss index) family active →
        WZ2PaperConvexWolffBound family
          (Kakeya.realRpowENN delta (-(loss index))) →
        0 < active.mass →
        Nonempty (Proposition63Lemma411OneQueryStepData
          (sigma := sigma) (outputLoss := loss (index + 1))
          (queryScale := queryScale index) active
          (fun point => sourceMap.planeMap point)))
    (variation_budget : ∀ index, index < N →
      (sourceCoefficient : ℝ) * spatialScale index ≤ variationScale index) :
    Nonempty (Proposition63ExtremalFiniteFullGrainData
      (sigma := sigma) current
      (paperWeakPlaneMapRestrict sourceMap current_sub_map)
      loss N queryScale spatialScale variationScale) := by
  let P : ℕ → Prop := fun completed =>
    ∃ active : WZ1PaperTubeShading family,
      PaperIsSubshading active current ∧
      PaperIsSubshading active mapShading ∧
      PaperIsSubshading active ambientShading ∧
      (∀ index, index < completed → ∀ point ∈ active.union,
        IsADSet1
          (scalarProjection (sourceMap.planeMap point)
            (active.union ∩ Metric.closedBall point
              (Real.sqrt (queryScale index))))
          (queryScale index) (1 - sigma)
          (Kakeya.realRpowENN delta (-(loss completed)))) ∧
      (∃ massLoss : ENNReal, 0 < massLoss ∧ massLoss ≠ ⊤ ∧
        massLoss⁻¹ * current.mass ≤ active.mass) ∧
      WZ2PaperCroppedIsExtremal sigma (loss completed) family active ∧
      WZ2PaperConvexWolffBound family
        (Kakeya.realRpowENN delta (-(loss completed))) ∧
      0 < active.mass
  have base : P 0 := by
    exact ⟨current, fun _ => Set.Subset.rfl, current_sub_map,
      current_sub_ambient,
      (by intro index index_lt; omega),
      ⟨1, by norm_num, by norm_num, by simp⟩, current_extremal,
      current_cwa, current_mass_pos⟩
  have advance : ∀ completed, completed < N → P completed →
      P (completed + 1) := by
    intro completed completed_lt state
    rcases state with ⟨active, active_sub_current, active_sub_map,
      active_sub_ambient, active_ad, active_mass, active_extremal, active_cwa,
      active_mass_pos⟩
    rcases active_mass with
      ⟨activeLoss, activeLoss_pos, activeLoss_top, active_retention⟩
    rcases step completed completed_lt active active_sub_map
      active_sub_ambient active_extremal active_cwa active_mass_pos with ⟨next⟩
    let nextLoss := activeLoss * next.massLoss
    have nextLoss_pos : 0 < nextLoss := ENNReal.mul_pos
      activeLoss_pos.ne' next.massLoss_pos.ne'
    have nextLoss_top : nextLoss ≠ ⊤ := ENNReal.mul_ne_top
      activeLoss_top next.massLoss_ne_top
    have next_retention : nextLoss⁻¹ * current.mass ≤
        next.oneQuery.shading.mass := by
      rw [ENNReal.mul_inv (Or.inl activeLoss_pos.ne')
        (Or.inl activeLoss_top)]
      calc
        (activeLoss⁻¹ * next.massLoss⁻¹) * current.mass =
            next.massLoss⁻¹ * (activeLoss⁻¹ * current.mass) := by ring
        _ ≤ next.massLoss⁻¹ * active.mass := by
          exact mul_le_mul_right active_retention _
        _ ≤ next.oneQuery.shading.mass := next.mass_retention
    have next_sub_current : PaperIsSubshading next.oneQuery.shading current :=
      fun tube point point_mem =>
        active_sub_current tube (next.oneQuery.subshading tube point_mem)
    have next_sub_map : PaperIsSubshading
        next.oneQuery.shading mapShading :=
      fun tube point point_mem =>
        active_sub_map tube (next.oneQuery.subshading tube point_mem)
    have next_sub_ambient : PaperIsSubshading
        next.oneQuery.shading ambientShading :=
      fun tube point point_mem =>
        active_sub_ambient tube (next.oneQuery.subshading tube point_mem)
    have constantStep : Kakeya.realRpowENN delta (-(loss completed)) ≤
        Kakeya.realRpowENN delta (-(loss (completed + 1))) := by
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge active_extremal.delta_pos
        active_extremal.delta_le_one (by linarith [loss_mono completed])
    refine ⟨next.oneQuery.shading, next_sub_current, next_sub_map,
      next_sub_ambient, ?_,
      ⟨nextLoss, nextLoss_pos, nextLoss_top, next_retention⟩,
      next.oneQuery.extremal, next.oneQuery.cwa, next.shading_mass_pos⟩
    intro index index_lt point point_mem
    by_cases is_new : index = completed
    · subst index
      exact next.oneQuery.local_ad point point_mem
    · have index_old : index < completed := by omega
      have point_active : point ∈ active.union :=
        paperSubshading_union next.oneQuery.subshading point_mem
      have hset : scalarProjection (sourceMap.planeMap point)
            (next.oneQuery.shading.union ∩ Metric.closedBall point
              (Real.sqrt (queryScale index))) ⊆
          scalarProjection (sourceMap.planeMap point)
            (active.union ∩ Metric.closedBall point
              (Real.sqrt (queryScale index))) := by
        rintro value ⟨other, ⟨other_mem, other_ball⟩, rfl⟩
        exact ⟨other,
          ⟨paperSubshading_union next.oneQuery.subshading other_mem,
            other_ball⟩, rfl⟩
      exact ((active_ad index index_old point point_active).mono hset).mono_constant
        constantStep
  have all : ∀ completed, completed ≤ N → P completed := by
    intro completed completed_le
    induction completed with
    | zero => exact base
    | succ completed inductionHypothesis =>
        exact advance completed (by omega)
          (inductionHypothesis (by omega))
  rcases all N le_rfl with ⟨final, final_sub_current, final_sub_map,
    _final_sub_ambient, final_ad, final_mass, final_extremal, _final_cwa,
    _final_mass_pos⟩
  rcases final_mass with
    ⟨finalLoss, finalLoss_pos, finalLoss_top, final_retention⟩
  let currentMap := paperWeakPlaneMapRestrict sourceMap current_sub_map
  let finalMap := paperWeakPlaneMapRestrict currentMap final_sub_current
  exact ⟨{
    shading := final
    subshading := final_sub_current
    cubical := final_extremal.cubical
    planeMap := finalMap
    same_plane_map := rfl
    variation := by
      intro index index_lt first first_mem second second_mem distance_bound
      change dist (sourceMap.planeMap first) (sourceMap.planeMap second) ≤
        variationScale index
      have hlipschitz := sourceLipschitz.dist_le_mul
        ⟨first, paperSubshading_union final_sub_map first_mem⟩
        ⟨second, paperSubshading_union final_sub_map second_mem⟩
      calc
        dist (sourceMap.planeMap first) (sourceMap.planeMap second) ≤
            (sourceCoefficient : ℝ) * dist first second := by
          simpa only [Subtype.dist_eq] using hlipschitz
        _ ≤ (sourceCoefficient : ℝ) * spatialScale index := by
          exact mul_le_mul_of_nonneg_left distance_bound (by positivity)
        _ ≤ variationScale index := variation_budget index index_lt
    local_ad := by
      intro index index_lt point point_mem
      change IsADSet1
        (scalarProjection (sourceMap.planeMap point)
          (final.union ∩ Metric.closedBall point
            (Real.sqrt (queryScale index))))
        (queryScale index) (1 - sigma)
        (Kakeya.realRpowENN delta (-(loss N)))
      exact final_ad index index_lt point point_mem
    massLoss := finalLoss
    massLoss_pos := finalLoss_pos
    massLoss_ne_top := finalLoss_top
    mass_retention := final_retention
    extremal := final_extremal
  }⟩

/-- Execute all pre-bound M7 coordinates in order.  Each step uses the
extremality, CWA, and positive mass returned by its immediate predecessor. -/
theorem Proposition63Lemma411OuterBindingData.run
    {sigma outputLoss delta ambientSourceLoss ambientNormalizationLoss
      incidence : ℝ}
    {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading mapShading current : WZ1PaperTubeShading ambientFamily}
    {normalizationExponent N : ℕ}
    {outer : Proposition63Lemma411OuterScheduleData sigma outputLoss N}
    {ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) ambientShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss}
    {K : ℝ} {sourceCoefficient : NNReal}
    (data : Proposition63Lemma411OuterBindingData (incidence := incidence)
      outer ambientReentry K sourceCoefficient)
    (ambientAxialEighth : ∀ tube point,
      point ∈ ambientReentry.geometry.frame ''
          ambientReentry.geometry.ordinaryRefined.carrier tube →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (sourceMap : PaperWZ1WeakPlaneMapData mapShading incidence)
    (sourceLipschitz : LipschitzWith sourceCoefficient
      (fun point : {point : Point3 // point ∈ mapShading.union} =>
        sourceMap.planeMap point))
    (current_sub_map : PaperIsSubshading current mapShading)
    (current_sub_ambient : PaperIsSubshading current ambientShading)
    (current_extremal : WZ2PaperCroppedIsExtremal
      sigma (outer.loss 0) ambientFamily current)
    (current_cwa : WZ2PaperConvexWolffBound ambientFamily
      (Kakeya.realRpowENN delta (-(outer.loss 0))))
    (current_mass_pos : 0 < current.mass)
    (spatialScale variationScale : ℕ → ℝ)
    (variation_budget : ∀ index, index < N →
      (sourceCoefficient : ℝ) * spatialScale index ≤ variationScale index) :
    Nonempty (Proposition63ExtremalFiniteFullGrainData
      (sigma := sigma) current
      (paperWeakPlaneMapRestrict sourceMap current_sub_map) outer.loss N
      data.queryScale spatialScale variationScale) := by
  apply proposition63_lemma411_outer_iteration sourceMap sourceCoefficient
    sourceLipschitz current_sub_map current_sub_ambient outer.loss N
    data.queryScale spatialScale variationScale outer.loss_mono
    current_extremal current_cwa current_mass_pos
  · intro index hindex active active_sub_map active_sub_ambient active_extremal
      active_cwa active_mass_pos
    have result := (data.coordinate index hindex).run ambientAxialEighth
      sourceMap sourceLipschitz active active_sub_map active_sub_ambient
      active_extremal active_cwa active_mass_pos
    simpa only [Proposition63Lemma411OuterBindingData.queryScale,
      dif_pos hindex] using result
  · exact variation_budget

/-- Run the M7-driven outer schedule on the actual Lemma 4.7 shading and feed
the resulting finite local-AD family to the existing Lemma 4.12 interpolation
and Lipschitz-selection endpoint. -/
theorem proposition63_lemma412_output_of_lemma411_outer_binding
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss lemma44Loss
      lemma47Loss coefficient gridLoss midLoss outputLoss
      ambientSourceLoss ambientNormalizationLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent normalizationExponent N kMin kMax : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss}
    (lemma47 : Proposition63Lemma47Data lemma44 lemma47Loss coefficient)
    (ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sticky.croppedCoarseShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss)
    (ambientAxialEighth : ∀ tube point,
      point ∈ ambientReentry.geometry.frame ''
          ambientReentry.geometry.ordinaryRefined.carrier tube →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (outer : Proposition63Lemma411OuterScheduleData sigma gridLoss N)
    (K : ℝ)
    (binding : Proposition63Lemma411OuterBindingData (incidence := rho.1)
      outer ambientReentry K (Real.toNNReal coefficient))
    (hlemma47Input : lemma47Loss ≤ outer.loss 0)
    (hrhoSmall : rho.1 ≤ 1 / 24)
    (spatialScale variationScale : ℕ → ℝ)
    (variation_budget : ∀ index, index < N →
      (Real.toNNReal coefficient : ℝ) * spatialScale index ≤
        variationScale index)
    (houtputLossPos : 0 < outputLoss)
    (hlemma47Output : lemma47Loss ≤ outputLoss)
    (hgridOutput : gridLoss ≤ outputLoss)
    (hresidue : 27 * Kakeya.realRpowENN rho.1 outputLoss ≤
      Kakeya.realRpowENN rho.1 gridLoss)
    (hcoefficientPos : 0 < coefficient)
    (hvariationCovers : ∀ d : ℝ, rho.1 < d → d ≤ 4 →
      coefficient * d < 2 →
      ∃ index, index < N ∧ d ≤ spatialScale index ∧
        variationScale index ≤ coefficient * d)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hmidLoss : 0 < midLoss) (hN : 0 < (N : ℝ))
    (hkMin : kMin = Nat.ceil ((N : ℝ) * midLoss))
    (hkMinMax : kMin ≤ kMax) (hkMaxLt : kMax < N)
    (hkMaxLower : (N : ℝ) * (1 - midLoss) - 1 ≤ (kMax : ℝ))
    (hqueryEq : ∀ index, index < N →
      binding.queryScale index = finiteGridScaleVal rho.1 N index)
    (hgridAdmissible : ∀ k, kMin ≤ k ∧ k ≤ kMax →
      rho.1 ≤ finiteGridScaleVal rho.1 N k ∧
        finiteGridScaleVal rho.1 N k ≤ 1)
    (habsorbInterpolation :
      (100 : ℝ) * Real.rpow rho.1
          (-gridLoss - midLoss - 1 / (N : ℝ)) ≤
        Real.rpow rho.1 (-outputLoss))
    (habsorbFine :
      (100 : ℝ) * Real.rpow rho.1
          (-midLoss - 1 / (N : ℝ)) ≤
        Real.rpow rho.1 (-outputLoss)) :
    Nonempty (Proposition63Lemma412OutputData lemma47 outputLoss) := by
  have current_extremal : WZ2PaperCroppedIsExtremal sigma (outer.loss 0)
      sticky.coarse lemma47.shading :=
    lemma47.extremal.mono_loss hlemma47Input
  have current_cwa : WZ2PaperConvexWolffBound sticky.coarse
      (Kakeya.realRpowENN rho.1 (-(outer.loss 0))) := by
    apply weaken_convex_wolff_bound lemma47.top_level_cwa
    exact realRpowENN_antitone lemma47.extremal.delta_pos
      lemma47.extremal.delta_le_one (by linarith)
  have current_sub_ambient : PaperIsSubshading lemma47.shading
      sticky.croppedCoarseShading := fun tube point point_mem =>
    lemma44.coarse_subshading tube (lemma47.subshading tube point_mem)
  have current_mass_pos : 0 < lemma47.shading.mass :=
    cropped_extremal_shading_mass_pos lemma47.extremal
      sticky.cover.coarse_line_class hrhoSmall
  let identitySub : PaperIsSubshading lemma47.shading lemma47.shading :=
    fun _ => Set.Subset.rfl
  rcases binding.run ambientAxialEighth lemma47.planeMap lemma47.lipschitz
      identitySub current_sub_ambient current_extremal current_cwa
      current_mass_pos spatialScale variationScale variation_budget with
    ⟨finiteRestricted⟩
  let finite : Proposition63ExtremalFiniteFullGrainData
      (sigma := sigma) lemma47.shading lemma47.planeMap outer.loss N
      binding.queryScale spatialScale variationScale := {
    shading := finiteRestricted.shading
    subshading := finiteRestricted.subshading
    cubical := finiteRestricted.cubical
    planeMap := finiteRestricted.planeMap
    same_plane_map := by
      simpa only [identitySub, paperWeakPlaneMapRestrict] using
        finiteRestricted.same_plane_map
    variation := by
      intro index index_lt first first_mem second second_mem distance_bound
      exact finiteRestricted.variation index index_lt first first_mem second
        second_mem distance_bound
    local_ad := by
      intro index index_lt point point_mem
      exact finiteRestricted.local_ad index index_lt point point_mem
    massLoss := finiteRestricted.massLoss
    massLoss_pos := finiteRestricted.massLoss_pos
    massLoss_ne_top := finiteRestricted.massLoss_ne_top
    mass_retention := finiteRestricted.mass_retention
    extremal := finiteRestricted.extremal
  }
  exact proposition63_lemma412_output_of_extremal_finite_full_grain lemma47
    outer.loss binding.queryScale spatialScale variationScale finite
    outer.final_loss (by
      rw [← outer.final_loss]
      exact outer.loss_pos N le_rfl) houtputLossPos
    hlemma47Output hgridOutput hresidue hcoefficientPos le_rfl
    hvariationCovers hsigma hsigmaOne
    -- The following finite-grid data are exactly the paper interpolation
    -- receipts supplied by the outer parameter hierarchy.
    hmidLoss hN hkMin hkMinMax hkMaxLt hkMaxLower hqueryEq
    hgridAdmissible habsorbInterpolation habsorbFine

/-- Paper-faithful M8 terminal bridge.  It runs M7 only on the central grid
coordinates and hands the exact central local-AD family to Lemma 4.12.  The
Lipschitz selector may still use all `N` spatial coordinates because those
variation estimates come directly from the fixed Lemma 4.7 map. -/
theorem proposition63_lemma412_output_of_lemma411_central_binding
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss lemma44Loss
      lemma47Loss coefficient gridLoss midLoss outputLoss
      ambientSourceLoss ambientNormalizationLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent normalizationExponent N : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss}
    (lemma47 : Proposition63Lemma47Data lemma44 lemma47Loss coefficient)
    (ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sticky.croppedCoarseShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss)
    (ambientAxialEighth : ∀ tube point,
      point ∈ ambientReentry.geometry.frame ''
          ambientReentry.geometry.ordinaryRefined.carrier tube →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (central : Proposition63Lemma412CentralGridData rho.1 midLoss N)
    (outer : Proposition63Lemma411OuterScheduleData
      sigma gridLoss central.count)
    (K : ℝ)
    (binding : Proposition63Lemma411CentralBindingData
      (incidence := rho.1) central outer ambientReentry K
        (Real.toNNReal coefficient))
    (hlemma47Input : lemma47Loss ≤ outer.loss 0)
    (hrhoSmall : rho.1 ≤ 1 / 24)
    (spatialScale variationScale : ℕ → ℝ)
    (variation_budget : ∀ index, index < N →
      (Real.toNNReal coefficient : ℝ) * spatialScale index ≤
        variationScale index)
    (houtputLossPos : 0 < outputLoss)
    (hlemma47Output : lemma47Loss ≤ outputLoss)
    (hgridOutput : gridLoss ≤ outputLoss)
    (hresidue : 27 * Kakeya.realRpowENN rho.1 outputLoss ≤
      Kakeya.realRpowENN rho.1 gridLoss)
    (hcoefficientPos : 0 < coefficient)
    (hvariationCovers : ∀ d : ℝ, rho.1 < d → d ≤ 4 →
      coefficient * d < 2 →
      ∃ index, index < N ∧ d ≤ spatialScale index ∧
        variationScale index ≤ coefficient * d)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (habsorbInterpolation :
      (100 : ℝ) * Real.rpow rho.1
          (-gridLoss - midLoss - 1 / (N : ℝ)) ≤
        Real.rpow rho.1 (-outputLoss))
    (habsorbFine :
      (100 : ℝ) * Real.rpow rho.1
          (-midLoss - 1 / (N : ℝ)) ≤
        Real.rpow rho.1 (-outputLoss)) :
    Nonempty (Proposition63Lemma412OutputData lemma47 outputLoss) := by
  have current_extremal : WZ2PaperCroppedIsExtremal sigma (outer.loss 0)
      sticky.coarse lemma47.shading :=
    lemma47.extremal.mono_loss hlemma47Input
  have current_cwa : WZ2PaperConvexWolffBound sticky.coarse
      (Kakeya.realRpowENN rho.1 (-(outer.loss 0))) := by
    apply weaken_convex_wolff_bound lemma47.top_level_cwa
    exact realRpowENN_antitone lemma47.extremal.delta_pos
      lemma47.extremal.delta_le_one (by linarith)
  have current_sub_ambient : PaperIsSubshading lemma47.shading
      sticky.croppedCoarseShading := fun tube point point_mem =>
    lemma44.coarse_subshading tube (lemma47.subshading tube point_mem)
  have current_mass_pos : 0 < lemma47.shading.mass :=
    cropped_extremal_shading_mass_pos lemma47.extremal
      sticky.cover.coarse_line_class hrhoSmall
  let identitySub : PaperIsSubshading lemma47.shading lemma47.shading :=
    fun _ => Set.Subset.rfl
  rcases binding.binding.run ambientAxialEighth lemma47.planeMap
      lemma47.lipschitz identitySub current_sub_ambient current_extremal
      current_cwa current_mass_pos
      (fun index => spatialScale (central.globalIndex index))
      (fun index => variationScale (central.globalIndex index))
      (by
        intro index hindex
        exact variation_budget _ (central.globalIndex_lt_N hindex)) with
    ⟨finiteRestricted⟩
  let finite : Proposition63Lemma412FiniteGridData
      (sigma := sigma) (gridLoss := gridLoss) lemma47.shading lemma47.planeMap
        N central.kMin central.kMax spatialScale variationScale := {
    shading := finiteRestricted.shading
    subshading := finiteRestricted.subshading
    cubical := finiteRestricted.cubical
    planeMap := finiteRestricted.planeMap
    same_plane_map := by
      simpa only [identitySub, paperWeakPlaneMapRestrict] using
        finiteRestricted.same_plane_map
    variation := by
      intro index index_lt first first_mem second second_mem distance_bound
      rw [finiteRestricted.same_plane_map]
      change dist (lemma47.planeMap.planeMap first)
        (lemma47.planeMap.planeMap second) ≤ variationScale index
      have hlipschitz := lemma47.lipschitz.dist_le_mul
        ⟨first, paperSubshading_union finiteRestricted.subshading first_mem⟩
        ⟨second, paperSubshading_union finiteRestricted.subshading second_mem⟩
      calc
        dist (lemma47.planeMap.planeMap first)
            (lemma47.planeMap.planeMap second) ≤
            (Real.toNNReal coefficient : ℝ) * dist first second := by
          simpa only [Subtype.dist_eq] using hlipschitz
        _ ≤ (Real.toNNReal coefficient : ℝ) * spatialScale index := by
          exact mul_le_mul_of_nonneg_left distance_bound (by positivity)
        _ ≤ variationScale index := variation_budget index index_lt
    local_ad := by
      intro index index_range point point_mem
      have local_index_lt : index - central.kMin < central.count := by
        dsimp [Proposition63Lemma412CentralGridData.count]
        omega
      have global_index_eq :
          central.globalIndex (index - central.kMin) = index := by
        dsimp [Proposition63Lemma412CentralGridData.globalIndex]
        omega
      have sourceAD := finiteRestricted.local_ad
        (index - central.kMin) local_index_lt point point_mem
      rw [binding.query_eq (index - central.kMin) local_index_lt,
        global_index_eq, outer.final_loss] at sourceAD
      exact sourceAD
    massLoss := finiteRestricted.massLoss
    massLoss_pos := finiteRestricted.massLoss_pos
    massLoss_ne_top := finiteRestricted.massLoss_ne_top
    mass_retention := finiteRestricted.mass_retention
    extremal := by
      simpa only [outer.final_loss] using finiteRestricted.extremal
  }
  exact proposition63_lemma412_output_of_finite_grid_data lemma47
    spatialScale variationScale finite (by
      rw [← outer.final_loss]
      exact outer.loss_pos central.count le_rfl) houtputLossPos
    hlemma47Output hgridOutput hresidue hcoefficientPos
    hvariationCovers hsigma hsigmaOne central.midLoss_pos central.N_pos
    central.kMin_eq central.kMin_le_kMax central.kMax_lower
    central.admissible habsorbInterpolation habsorbFine

/-- Complete M8 entry point.  The caller supplies only the honest pre-runtime
root and cutoff receipts; this theorem constructs the canonical coordinates,
runs their stateful M7 iteration, and closes Lemma 4.12. -/
theorem proposition63_lemma412_output_of_lemma411_outer_inputs
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss lemma44Loss
      lemma47Loss coefficient gridLoss midLoss outputLoss
      ambientSourceLoss ambientNormalizationLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent normalizationExponent N : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss}
    (lemma47 : Proposition63Lemma47Data lemma44 lemma47Loss coefficient)
    (ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sticky.croppedCoarseShading normalizationExponent
        ambientSourceLoss ambientNormalizationLoss)
    (ambientAxialEighth : ∀ tube point,
      point ∈ ambientReentry.geometry.frame ''
          ambientReentry.geometry.ordinaryRefined.carrier tube →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (schedule : Proposition63Lemma412ScheduleData
      sigma gridLoss rho.1 midLoss N)
    (K : ℝ)
    (hgridLossMid : gridLoss ≤ midLoss)
    (inputs : Proposition63Lemma411OuterBindingInputs (incidence := rho.1)
      schedule.central schedule.outer ambientReentry K
        (Real.toNNReal coefficient) hgridLossMid)
    (hlemma47Input : lemma47Loss ≤ schedule.outer.loss 0)
    (hrhoSmall : rho.1 ≤ 1 / 24)
    (spatialScale variationScale : ℕ → ℝ)
    (variation_budget : ∀ index, index < N →
      (Real.toNNReal coefficient : ℝ) * spatialScale index ≤
        variationScale index)
    (houtputLossPos : 0 < outputLoss)
    (hlemma47Output : lemma47Loss ≤ outputLoss)
    (hgridOutput : gridLoss ≤ outputLoss)
    (hresidue : 27 * Kakeya.realRpowENN rho.1 outputLoss ≤
      Kakeya.realRpowENN rho.1 gridLoss)
    (hcoefficientPos : 0 < coefficient)
    (hvariationCovers : ∀ d : ℝ, rho.1 < d → d ≤ 4 →
      coefficient * d < 2 →
      ∃ index, index < N ∧ d ≤ spatialScale index ∧
        variationScale index ≤ coefficient * d)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (habsorbInterpolation :
      (100 : ℝ) * Real.rpow rho.1
          (-gridLoss - midLoss - 1 / (N : ℝ)) ≤
        Real.rpow rho.1 (-outputLoss))
    (habsorbFine :
      (100 : ℝ) * Real.rpow rho.1
          (-midLoss - 1 / (N : ℝ)) ≤
        Real.rpow rho.1 (-outputLoss)) :
    Nonempty (Proposition63Lemma412OutputData lemma47 outputLoss) := by
  rcases proposition63_lemma411_central_binding schedule.central
      schedule.outer ambientReentry K (Real.toNNReal coefficient)
      hgridLossMid inputs with ⟨binding⟩
  exact proposition63_lemma412_output_of_lemma411_central_binding lemma47
    ambientReentry ambientAxialEighth schedule.central schedule.outer K
    binding hlemma47Input hrhoSmall spatialScale variationScale
    variation_budget houtputLossPos hlemma47Output hgridOutput hresidue
    hcoefficientPos hvariationCovers hsigma hsigmaOne
    habsorbInterpolation habsorbFine

end Kakeya.Assouad.PureWZ2
