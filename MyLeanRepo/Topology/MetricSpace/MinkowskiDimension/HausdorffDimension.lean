import MyLeanRepo.Topology.MetricSpace.MinkowskiDimension.Basic
import MyLeanRepo.Topology.MetricSpace.MinkowskiDimension.ExpDecay
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Asymptotics.ExpGrowth

/-!
# Hausdorff dimension ≤ lower Minkowski dimension

This module proves `dimH s ≤ lowerMinkowskiDim s` for arbitrary sets in
pseudo-emetric spaces.

## Proof route

1. Bound `μH[d] s` by `liminf` of dyadic covering sums using minimal covers.
2. If `expGrowthInf u < d * log 2`, pick `b` strictly between and use
   `frequently_le_exp` to get frequent upper bounds on covering numbers.
3. Use `exp_decay_estimate` to show the bounding sequence tends to `0`.
4. Conclude `liminf = 0`, hence `μH[d] s = 0`.
5. Deduce `dimH s ≤ lowerMinkowskiDim s` via `dimH_le`.
-/

noncomputable section

open scoped ENNReal NNReal Topology
open Metric ExpGrowth MeasureTheory Filter Set EReal

namespace MeasureTheory

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

section Helpers

/-- If `x < ↑y` in `EReal` with `y : ℝ`, there exists a real `b` strictly between. -/
private lemma exists_real_between {x : EReal} {y : ℝ} (h : x < ↑y) :
    ∃ (b : ℝ), x < ↑b ∧ b < y := by
  induction x with
  | bot =>
    let b : ℝ := y - 1
    have hne : (↑b : EReal) ≠ ⊥ := EReal.coe_ne_bot b
    exact ⟨b, bot_lt_iff_ne_bot.mpr hne, by linarith⟩
  | coe r =>
    have hrl : r < y := by exact_mod_cast h
    refine ⟨(r + y) / 2, ?_, by linarith⟩
    exact_mod_cast (by linarith)
  | top =>
    simp at h

/-- If `expGrowthInf u < ⊤` and `u` is monotone, then `u n < ⊤` for all `n`. -/
private lemma lt_top_of_expGrowthInf_lt_top {u : ℕ → ENNReal} (h_mono : Monotone u)
    (h : expGrowthInf u < ⊤) : ∀ n, u n < ⊤ := by
  intro n
  by_contra h2
  have h3 : u n = ⊤ := by simpa using h2
  have h_ev : ∀ᶠ m in atTop, u m = ⊤ := by
    filter_upwards [eventually_ge_atTop n] with m hm
    have h4 : u n ≤ u m := h_mono hm
    have h5 : (⊤ : ENNReal) ≤ u m := by
      rw [h3] at h4
      exact h4
    exact le_antisymm le_top h5
  have h_log_ev : ∀ᶠ m in atTop, ENNReal.log (u m) / (m : EReal) = ⊤ := by
    filter_upwards [h_ev, eventually_ge_atTop 1] with m hm1 hm2
    rw [hm1, ENNReal.log_top]
    have hpos : 0 < (m : EReal) := by
      have h3 : 0 < m := by omega
      exact_mod_cast h3
    have hne_top : (m : EReal) ≠ ⊤ := EReal.coe_ne_top (m : ℝ)
    exact EReal.top_div_of_pos_ne_top hpos hne_top
  have h6 : expGrowthInf u = ⊤ := by
    rw [expGrowthInf]
    have h7 : (fun m : ℕ => ENNReal.log (u m) / (m : EReal)) =ᶠ[atTop] (fun _ : ℕ => (⊤ : EReal)) :=
      h_log_ev.mono (fun _ h => h)
    rw [liminf_congr h7]
    simp
  exact h.ne h6

/-- If `x ≤ 0` in `EReal` and `0 ≤ y` in `ℝ`, then `x * ↑y ≤ 0`. -/
private lemma ereal_mul_nonpos_of_nonpos_of_nonneg {x : EReal} {y : ℝ} (hx : x ≤ 0) (hy : 0 ≤ y) :
    x * (↑y : EReal) ≤ 0 := by
  induction x with
  | bot =>
    by_cases hy0 : y = 0
    · rw [hy0]; simp
    · have hne : 0 ≠ y := fun h => hy0 h.symm
      have hy_pos : 0 < y := hy.lt_of_ne hne
      have h : (⊥ : EReal) * (↑y : EReal) = ⊥ :=
        bot_mul_coe_of_pos hy_pos
      rw [h]; exact bot_le
  | coe r =>
    have hr : r ≤ 0 := by exact_mod_cast hx
    have h : (↑r : EReal) * (↑y : EReal) = ↑(r * y) := by norm_cast
    rw [h]
    have h2 : r * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hr hy
    exact_mod_cast h2
  | top => simp at hx

/-- If `x ≠ ⊥` and `x ≠ ⊤`, then `x` is the coercion of some real number. -/
private lemma ereal_exists_coe {x : EReal} (hbot : x ≠ ⊥) (htop : x ≠ ⊤) :
    ∃ (r : ℝ), x = ↑r := by
  induction x with
  | bot => exfalso; exact hbot rfl
  | coe r => exact ⟨r, rfl⟩
  | top => exfalso; exact htop rfl

/-- If a nonnegative sequence is frequently bounded by a sequence tending to `0`,
then its `liminf` is `0`. -/
private lemma liminf_zero_of_frequently_tendsto {f g : ℕ → ENNReal}
    (h_freq : ∃ᶠ n in atTop, f n ≤ g n)
    (h_tendsto : Tendsto g atTop (nhds 0)) :
    liminf f atTop = 0 := by
  have h1 : ∀ (ε : ENNReal), 0 < ε → liminf f atTop ≤ ε := by
    intro ε hε
    have h2 : ∀ᶠ n in atTop, g n < ε := h_tendsto (Iio_mem_nhds hε)
    have h3 : ∃ᶠ n in atTop, f n ≤ ε := by
      have h4 : ∃ᶠ n in atTop, (f n ≤ g n) ∧ (g n < ε) := h_freq.and_eventually h2
      exact h4.mono (fun n hn => hn.1.trans hn.2.le)
    exact liminf_le_of_frequently_le' h3
  have h4 : liminf f atTop ≤ 0 := by
    by_contra h5
    have h6 : 0 < liminf f atTop := Std.not_le.mp h5
    by_cases h7 : liminf f atTop = ⊤
    · have h8 := h1 1 (by norm_num)
      rw [h7] at h8
      <;> simp at h8
    · have h_lt_top : liminf f atTop ≠ ⊤ := h7
      let ε := (liminf f atTop) / 2
      have hε_pos : 0 < ε := ENNReal.half_pos h6.ne'
      have hε_lt : ε < liminf f atTop := ENNReal.half_lt_self h6.ne' h_lt_top
      have h9 := h1 ε hε_pos
      exact lt_irrefl ε (hε_lt.trans_le h9)
  simpa using h4

end Helpers

section CoverLemma

/-- Bound the `d`-dimensional Hausdorff measure by the `liminf` of dyadic
covering numbers times diameter powers. -/
lemma hausdorffMeasure_le_liminf_covering (s : Set X) (d : ℝ) (hd : 0 ≤ d)
    (hfin : ∀ n, Metric.coveringNumber (((2 : NNReal)^n)⁻¹) s ≠ ⊤) :
    μH[d] s ≤ liminf (fun n : ℕ =>
      (Metric.coveringNumber (((2 : NNReal)^n)⁻¹) s : ENNReal) *
      (2 * ↑(((2 : NNReal)^n)⁻¹) : ENNReal)^d) atTop := by
  let εn : ℕ → NNReal := fun n => ((2 : NNReal)^n)⁻¹
  let C : ℕ → Set X := fun n => Metric.minimalCover (εn n) s
  let ι : ℕ → Type _ := fun n => {x // x ∈ C n}
  have hCfin : ∀ n, (C n).Finite := fun _ => Metric.finite_minimalCover
  letI coverFintype (n : ℕ) : Fintype (ι n) := (hCfin n).fintype

  let t : ∀ n, ι n → Set X := fun n i =>
    Metric.closedEBall (i : X) (↑(εn n) : ENNReal)
  let r : ℕ → ENNReal := fun n => 2 * ↑(εn n)

  have h_diam : ∀ n i, ediam (t n i) ≤ r n := by
    intro n i
    exact ediam_closedEBall_le

  have h_cover : ∀ n, s ⊆ ⋃ (i : ι n), t n i := by
    intro n
    have hcov : Metric.IsCover (εn n) s (C n) := Metric.isCover_minimalCover (hfin n)
    have h : s ⊆ ⋃ y ∈ C n, Metric.closedEBall y (↑(εn n) : ENNReal) :=
      Metric.isCover_iff_subset_iUnion_closedEBall.mp hcov
    have h_eq : (⋃ y ∈ C n, Metric.closedEBall y (↑(εn n) : ENNReal)) =
        ⋃ (i : ι n), t n i := by
      ext z
      simp only [t, Set.mem_iUnion]
      <;> aesop
    rw [h_eq] at h
    exact h

  have h_coe : ∀ n, (↑(εn n) : ENNReal) = (((2 : ENNReal)^n)⁻¹) := by
    intro n
    simp [εn]

  have hr_tendsto : Tendsto r atTop (nhds 0) := by
    have h1 : ∀ n, r n = 2 * (((2 : ENNReal)^n)⁻¹) := by
      intro n
      have h2 : r n = 2 * (↑(εn n) : ENNReal) := by rfl
      rw [h2, h_coe n]
    have h1' : r = fun n : ℕ => 2 * (((2 : ENNReal)^n)⁻¹) := by
      funext n
      exact h1 n
    rw [h1']
    have h_half_lt_one : (1 / 2 : ENNReal) < 1 := by norm_num
    have h_pow_half_real : Tendsto (fun x : ℝ => (1 / 2 : ENNReal)^x) atTop (nhds 0) :=
      ENNReal.tendsto_rpow_atTop_of_base_lt_one h_half_lt_one
    have h_pow_half : Tendsto (fun n : ℕ => (1 / 2 : ENNReal)^n) atTop (nhds 0) := by
      simpa using h_pow_half_real.comp tendsto_natCast_atTop_atTop
    have h_eq : ∀ n, (2 : ENNReal) * ((2 : ENNReal)^n)⁻¹ = (2 : ENNReal) * (1 / 2 : ENNReal)^n := by
      intro n
      have h1 : ((2 : ENNReal)^n)⁻¹ = ((2 : ENNReal)⁻¹)^n := by rw [ENNReal.inv_pow]
      rw [h1]
      have h2 : (2 : ENNReal)⁻¹ = (1 / 2 : ENNReal) := by norm_num
      rw [h2]
    have ha : (2 : ENNReal) ≠ 0 ∨ (0 : ENNReal) ≠ ⊤ := Or.inl (by norm_num)
    have hb : (0 : ENNReal) ≠ 0 ∨ (2 : ENNReal) ≠ ⊤ := Or.inr (by norm_num)
    have h_mul : Tendsto (fun n : ℕ => (2 : ENNReal) * (1 / 2 : ENNReal)^n) atTop (nhds 0) := by
      have h := ENNReal.Tendsto.mul tendsto_const_nhds ha h_pow_half hb
      simpa [mul_zero] using h
    exact h_mul.congr (fun n => (h_eq n).symm)

  have h_sum : ∀ n, ∑ (i : ι n), ediam (t n i)^d ≤
      (Metric.coveringNumber (εn n) s : ENNReal) * (r n)^d := by
    intro n
    have h1 : ∀ (i : ι n), ediam (t n i)^d ≤ (r n)^d := by
      intro i
      gcongr <;> exact h_diam n i
    have h2 : ∑ (i : ι n), ediam (t n i)^d ≤ ∑ (i : ι n), (r n)^d := by
      apply Finset.sum_le_sum
      intro i _
      exact h1 i
    have h3 : ∑ (i : ι n), (r n)^d =
        (Fintype.card (ι n) : ENNReal) * (r n)^d := by
      simp [Finset.sum_const, mul_comm]
    rw [h3] at h2
    have h41 : Fintype.card (ι n) = (C n).ncard :=
      Set.fintypeCard_eq_ncard (C n)
    have h42 : ((C n).ncard : ENNReal) = ↑((C n).encard : ENat) := by
      exact_mod_cast Set.coe_ncard_eq_encard (C n)
    have h4 : (Fintype.card (ι n) : ENNReal) = (C n).encard := by
      rw [h41]
      exact h42
    rw [h4, Metric.encard_minimalCover (hfin n)] at h2
    exact h2

  have h_haar := Measure.hausdorffMeasure_le_liminf_sum d s r hr_tendsto t
    (Eventually.of_forall fun n => h_diam n)
    (Eventually.of_forall fun n => h_cover n)

  exact h_haar.trans (liminf_le_liminf (Eventually.of_forall h_sum))

end CoverLemma

section MeasureZero

/-- If the lower exponential growth of dyadic covering numbers is strictly below
`d * log 2`, then the `d`-dimensional Hausdorff measure vanishes. -/
lemma hausdorffMeasure_zero_of_expGrowthInf_lt (s : Set X) {d : ℝ} (hd : 0 < d)
    (h : expGrowthInf (dyadicCoveringSequence s) < (d : EReal) * ENNReal.log 2) :
    μH[d] s = 0 := by
  let u := dyadicCoveringSequence s
  let εn : ℕ → NNReal := fun n => ((2 : NNReal)^n)⁻¹
  let log2 : EReal := ENNReal.log 2

  have hlog2_real : log2 = ↑(Real.log 2) := by
    have h_eq2 : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_num
    have h : ENNReal.log (2 : ENNReal) = ↑(Real.log 2) := by
      rw [h_eq2]
      exact ENNReal.log_ofReal_of_pos (show (0 : ℝ) < 2 by norm_num)
    simpa [log2] using h

  have h_main_hyp : expGrowthInf u < ↑(d * Real.log 2) := by
    have h_eq : (d : EReal) * log2 = ↑(d * Real.log 2) := by
      rw [hlog2_real] <;> norm_cast
    rw [h_eq] at h
    exact h

  -- Choose b : ℝ with expGrowthInf u < ↑b and b < d * Real.log 2
  rcases exists_real_between h_main_hyp with ⟨b, hb1, hb2⟩

  -- Frequently: u n ≤ EReal.exp (b * n)
  have h_freq : ∃ᶠ n in atTop, u n ≤ EReal.exp ((b : EReal) * ↑n) :=
    frequently_le_exp hb1

  -- The bounding sequence tends to 0
  have h_tendsto : Tendsto (fun n : ℕ =>
      EReal.exp ((b : EReal) * ↑n) * (2 * ↑((2 : NNReal)^n)⁻¹ : ENNReal)^d)
      atTop (nhds 0) :=
    Metric.exp_decay_estimate hb2 hd.le

  -- Covering numbers are finite
  have h_mono : Monotone u := dyadicCoveringSequence_monotone s
  have h_lt_top : expGrowthInf u < ⊤ := h_main_hyp.trans_le le_top
  have hfin : ∀ n, u n < ⊤ := lt_top_of_expGrowthInf_lt_top h_mono h_lt_top
  have hfin' : ∀ n, Metric.coveringNumber (εn n) s ≠ ⊤ := by
    intro n
    have h5 : u n = (Metric.coveringNumber (εn n) s : ENNReal) := by
      simpa [u, dyadicCoveringSequence, εn] using rfl
    intro h6
    have h7 : u n = ⊤ := by
      rw [h5, h6] <;> simp
    exact (hfin n).ne h7

  -- Let f n = coveringNumber * (2 * εn n)^d
  let f : ℕ → ENNReal := fun n =>
    (Metric.coveringNumber (εn n) s : ENNReal) * (2 * ↑(εn n) : ENNReal)^d
  let g : ℕ → ENNReal := fun n =>
    EReal.exp ((b : EReal) * ↑n) * (2 * ↑((2 : NNReal)^n)⁻¹ : ENNReal)^d

  have h_u_eq : ∀ n, u n = (Metric.coveringNumber (εn n) s : ENNReal) := by
    intro n
    simpa [u, dyadicCoveringSequence, εn] using rfl

  have h_freq2 : ∃ᶠ n in atTop, f n ≤ g n :=
    h_freq.mono (fun n hn => by
      dsimp only [f, g]
      have h9 : (Metric.coveringNumber (εn n) s : ENNReal) ≤ EReal.exp ((b : EReal) * ↑n) := by
        rw [←h_u_eq n] <;> exact hn
      have h10 : (2 * ↑(εn n) : ENNReal)^d = (2 * ↑((2 : NNReal)^n)⁻¹ : ENNReal)^d := by
        rfl
      rw [h10]
      exact mul_le_mul_of_nonneg_right h9 (by positivity))

  have h_liminf_zero : liminf f atTop = 0 :=
    liminf_zero_of_frequently_tendsto h_freq2 h_tendsto

  have h_cover_bound : μH[d] s ≤ liminf f atTop :=
    hausdorffMeasure_le_liminf_covering s d hd.le hfin'

  rw [h_liminf_zero] at h_cover_bound
  simpa using h_cover_bound

end MeasureZero

section Main

/-- `dimH s ≤ lowerMinkowskiDim s` for any set `s`. -/
theorem dimH_le_lowerMinkowskiDim {X : Type*} [EMetricSpace X] (s : Set X) :
    dimH s ≤ Metric.lowerMinkowskiDim s := by
  borelize X
  by_cases hL_top : Metric.lowerMinkowskiDim s = ⊤
  · rw [hL_top]
    exact le_top
  · set L : ENNReal := Metric.lowerMinkowskiDim s with hL_def
    have hL_ne_top : L ≠ ⊤ := by
      rw [hL_def]
      exact hL_top
    apply dimH_le (d := L)
    intro d' hd'
    by_contra h
    have h_gt : L < (↑d' : ENNReal) := Std.not_le.mp h
    have h_d_pos : 0 < (d' : ℝ) := by
      by_contra h0
      have h1 : (d' : ℝ) ≤ 0 := by linarith
      have h2 : d' = 0 := LE.le.eq_zero h1
      rw [h2] at h_gt
      simp at h_gt
    let u := Metric.dyadicCoveringSequence s
    let log2 : EReal := ENNReal.log 2
    have hlog2_pos : (0 : EReal) < log2 :=
      ENNReal.zero_lt_log_iff.mpr (by norm_num)
    have hlog2_ne_bot : log2 ≠ ⊥ := ne_bot_of_gt hlog2_pos
    have hlog2_ne_top : log2 ≠ ⊤ := by
      simp [log2, ENNReal.log_eq_top_iff] <;> norm_num
    have hlog2_ne_zero : log2 ≠ 0 := hlog2_pos.ne'
    have hlog2_real : log2 = ↑(Real.log 2) := by
      have h_eq2 : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_num
      have h : ENNReal.log (2 : ENNReal) = ↑(Real.log 2) := by
        rw [h_eq2]
        exact ENNReal.log_ofReal_of_pos (show (0 : ℝ) < 2 by norm_num)
      simpa [log2] using h

    let a : EReal := expGrowthInf u / log2
    have hL_eq : a.toENNReal = L := by
      simp [L, Metric.lowerMinkowskiDim, a] <;> rfl

    have h_main : expGrowthInf u < (d' : EReal) * log2 := by
      by_cases h_case : a ≤ 0
      · -- Case a ≤ 0
        have h1 : expGrowthInf u ≤ 0 := by
          have h2 : (expGrowthInf u / log2) * log2 = expGrowthInf u :=
            EReal.div_mul_cancel hlog2_ne_bot hlog2_ne_top hlog2_ne_zero
          have h3 : expGrowthInf u = (expGrowthInf u / log2) * log2 := h2.symm
          rw [h3]
          have h4 : a * log2 ≤ 0 := by
            rw [hlog2_real]
            exact ereal_mul_nonpos_of_nonpos_of_nonneg h_case (Real.log_nonneg (by norm_num))
          exact h4
        have h4 : (0 : EReal) < (d' : EReal) * log2 := by
          rw [show (d' : EReal) * log2 = ↑((d' : ℝ) * Real.log 2) from by
            rw [hlog2_real] <;> norm_cast]
          exact_mod_cast (mul_pos h_d_pos (Real.log_pos (by norm_num)))
        exact h1.trans_lt h4
      · -- Case a > 0
        have h_pos : 0 < a := Std.not_le.mp h_case
        have h_a_lt : a < (↑(d' : ℝ) : EReal) := by
          have h4 : a.toENNReal < (↑d' : ENNReal) := by
            rw [hL_eq] <;> exact h_gt
          have h5 : (a.toENNReal : EReal) < ((↑d' : ENNReal) : EReal) := by
            exact_mod_cast h4
          have h6 : (a.toENNReal : EReal) = a := EReal.coe_toENNReal h_pos.le
          have h7 : ((↑d' : ENNReal) : EReal) = (↑(d' : ℝ) : EReal) := by
            norm_cast
          rw [h6, h7] at h5
          exact h5
        have h_a_ne_bot : a ≠ ⊥ := by
          intro hbot; rw [hbot] at h_pos; simp at h_pos
        have h_a_ne_top : a ≠ ⊤ := by
          intro htop
          have h9 : a.toENNReal = ⊤ := by rw [htop]; simp
          have h10 : L = ⊤ := by
            rw [←hL_eq, h9]
          exact hL_ne_top h10
        rcases ereal_exists_coe h_a_ne_bot h_a_ne_top with ⟨r, hr⟩
        have hr_pos : 0 < r := by exact_mod_cast (hr ▸ h_pos)
        have hr_lt_d' : r < (d' : ℝ) := by
          rw [hr] at h_a_lt
          exact_mod_cast h_a_lt
        have h2 : (expGrowthInf u / log2) * log2 = expGrowthInf u :=
          EReal.div_mul_cancel hlog2_ne_bot hlog2_ne_top hlog2_ne_zero
        have h3 : expGrowthInf u = a * log2 := by
          simpa [a] using h2.symm
        rw [h3]
        have h11 : r * Real.log 2 < (d' : ℝ) * Real.log 2 := by
          gcongr
          <;> linarith [Real.log_pos (by norm_num)]
        have h12 : a * log2 = ↑(r * Real.log 2) := by
          rw [hr, hlog2_real] <;> norm_cast
        have h13 : (d' : EReal) * log2 = ↑((d' : ℝ) * Real.log 2) := by
          rw [hlog2_real] <;> norm_cast
        rw [h12, h13]
        exact_mod_cast h11

    have h_zero : μH[(d' : ℝ)] s = 0 :=
      hausdorffMeasure_zero_of_expGrowthInf_lt s h_d_pos h_main
    rw [h_zero] at hd'
    <;> simp at hd'

end Main

end MeasureTheory
