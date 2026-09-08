/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.MeasureTheory.Integral.Pi
public import Kakeya.Frostman
public import Kakeya.KatzTao
public import Kakeya.Multiplicity

/-!
We formalise [Lemma A.1, GWZ]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω]

private lemma exp_mul_le_of_mem_Icc {M lam X : ℝ} (hM : 0 < M)
    (hX0 : 0 ≤ X) (hXM : X ≤ M) :
    Real.exp (lam * X) ≤ (X / M) * Real.exp (lam * M) + (1 - X / M) := by
  have h := convexOn_exp.2 (Set.mem_univ (lam * M)) (Set.mem_univ (0 : ℝ))
    (div_nonneg hX0 hM.le) (sub_nonneg.mpr ((div_le_one hM).mpr hXM))
    (by ring : X / M + (1 - X / M) = 1)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  rwa [div_mul_eq_mul_div, mul_comm X, mul_right_comm, mul_div_cancel_right₀ _ hM.ne'] at h

private lemma exp_le_one_add_eMinusOne_mul {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp s ≤ 1 + (Real.exp 1 - 1) * s := by
  have h := exp_mul_le_of_mem_Icc (lam := 1) one_pos hs0 hs1
  rw [div_one, one_mul, one_mul] at h
  linarith

private lemma tail_bound_from_mgf {P : Measure Ω} [IsProbabilityMeasure P]
    (N : ℕ) [NeZero N] (X : Fin N → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (M : ℝ)
    (hbound : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω ∧ X i ω ≤ M)
    (hindep : iIndepFun X P) (hident : ∀ i : Fin N, IdentDistrib (X i) (X 0) P P)
    (S lam B : ℝ) (hlam_nn : 0 ≤ lam) (hmgf_bound : mgf (X 0) P lam ≤ B)
    (hB_pow : B ^ N ≤ Real.exp (Real.exp 1 - 1)) :
    (P {ω | ∑ i : Fin N, X i ω > S}).toReal ≤
      Real.exp (-lam * S) * Real.exp (Real.exp 1 - 1) := by
  have hmgfsum : mgf (fun ω => ∑ i, X i ω) P lam ≤ Real.exp (Real.exp 1 - 1) := by
    rw [show (fun ω => ∑ i, X i ω) = ∑ i ∈ (Finset.univ : Finset (Fin N)), X i from
        funext fun ω => (Finset.sum_apply ω _ _).symm,
      mgf_sum_of_identDistrib hmeas hindep (fun i _ j _ => (hident i).trans (hident j).symm)
        (Finset.mem_univ (0 : Fin N)) lam, Finset.card_univ, Fintype.card_fin]
    exact (pow_le_pow_left₀ mgf_nonneg hmgf_bound N).trans hB_pow
  have hint : Integrable (fun ω => Real.exp (lam * ∑ i, X i ω)) P := by
    simpa only [Finset.sum_apply] using hindep.integrable_exp_mul_sum hmeas
      (s := Finset.univ) fun i _ => Integrable.of_bound
        ((hmeas i).const_mul lam).exp.aestronglyMeasurable (Real.exp (lam * M))
        ((hbound i).mono fun ω hω => (Real.norm_of_nonneg (Real.exp_pos _).le).trans_le
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω.2 hlam_nn)))
  exact le_trans (measureReal_mono fun _ hω => (show S < _ from hω).le)
    ((measure_ge_le_exp_mul_mgf (X := fun ω => ∑ i, X i ω) S hlam_nn hint).trans
      (mul_le_mul_of_nonneg_left hmgfsum (Real.exp_pos _).le))

private lemma mgf_le_of_bounded {P : Measure Ω} [IsProbabilityMeasure P]
    (X0 : Ω → ℝ) (hmeas : Measurable X0) (M : ℝ) (hM : 0 < M)
    (m : ℝ) (hmean : ∫ ω, X0 ω ∂P = m)
    (hbound : ∀ᵐ ω ∂P, 0 ≤ X0 ω ∧ X0 ω ≤ M)
    (lam : ℝ) (hlam_nn : 0 ≤ lam) :
    mgf X0 P lam ≤ (m / M) * Real.exp (lam * M) + (1 - m / M) := by
  have hdiv : Integrable (fun ω => X0 ω / M) P :=
    (Integrable.of_bound hmeas.aestronglyMeasurable M (hbound.mono fun ω hω =>
      (Real.norm_of_nonneg hω.1).trans_le hω.2)).div_const M
  have hexp : Integrable (fun ω => Real.exp (lam * X0 ω)) P :=
    Integrable.of_bound ((hmeas.const_mul lam).exp.aestronglyMeasurable)
      (Real.exp (lam * M)) (hbound.mono fun ω hω =>
        (Real.norm_of_nonneg (Real.exp_pos _).le).trans_le
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω.2 hlam_nn)))
  refine (integral_mono_ae hexp (show Integrable
      (fun ω => X0 ω / M * Real.exp (lam * M) + (1 - X0 ω / M)) P from
      (hdiv.mul_const _).add ((integrable_const 1).sub hdiv))
    (hbound.mono fun ω hω => exp_mul_le_of_mem_Icc hM hω.1 hω.2)).trans_eq ?_
  rw [integral_add (hdiv.mul_const _) (g := fun ω => (1 - X0 ω / M : ℝ))
      ((integrable_const (1 : ℝ)).sub hdiv), integral_mul_const,
    integral_sub (integrable_const _) hdiv, integral_const, integral_div, hmean,
    probReal_univ, one_smul]

-- (extracted by Fuse golfer) `(1 + a / n) ^ n ≤ exp a` for `a ≥ 0` and `n ≠ 0`.
private lemma one_add_div_pow_le_exp {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (hn : n ≠ 0) :
    (1 + a / n) ^ n ≤ Real.exp a := by
  refine (pow_le_pow_left₀ (b := Real.exp (a / n)) (add_nonneg zero_le_one
    (div_nonneg ha n.cast_nonneg)) ((add_comm _ _).trans_le (Real.add_one_le_exp _)) n).trans_eq ?_
  rw [← Real.exp_nat_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn)]

-- (extracted by Fuse golfer) Chord estimate for the exponential on `[0, M]`: if `0 ≤ lam * M ≤ 1`
-- then the convex combination bound of `mgf_le_of_bounded` collapses to `1 + (e - 1) * lam * m`.
private lemma chord_exp_bound {m M lam : ℝ} (hm : 0 ≤ m) (hM : 0 < M)
    (hlam0 : 0 ≤ lam) (hlamM : lam * M ≤ 1) :
    m / M * Real.exp (lam * M) + (1 - m / M) ≤ 1 + (Real.exp 1 - 1) * (lam * m) := by
  refine (add_le_add (mul_le_mul_of_nonneg_left (exp_le_one_add_eMinusOne_mul
    (mul_nonneg hlam0 hM.le) hlamM) (div_nonneg hm hM.le)) le_rfl).trans_eq ?_
  linear_combination (Real.exp 1 - 1) * lam * div_mul_cancel₀ m hM.ne'

/-- Tail bound for i.i.d. [0, M]-valued random variables with mean m, case N * m ≥ M:
    P{∑ X i > S} ≤ exp(10 * e - S / (N * m)). -/
theorem lemma_A1_case_ge {P : Measure Ω} [IsProbabilityMeasure P]
    (N : ℕ) [NeZero N] (X : Fin N → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (M : ℝ) (hM : 0 < M)
    (m : ℝ) (hm : 0 ≤ m) (_hmM : m ≤ M)
    (hbound : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω ∧ X i ω ≤ M)
    (hmean : ∫ ω, X 0 ω ∂P = m) (hindep : iIndepFun X P)
    (hident : ∀ i : Fin N, IdentDistrib (X i) (X 0) P P)
    (S : ℝ) (hNm : (N : ℝ) * m ≥ M) :
    (P {ω | ∑ i : Fin N, X i ω > S}).toReal ≤
      Real.exp (10 * Real.exp 1 - S / ((N : ℝ) * m)) := by
  have hNm_pos : 0 < (N : ℝ) * m := hM.trans_le hNm
  obtain ⟨lam, hlam_def⟩ : ∃ x : ℝ, x = 1 / ((N : ℝ) * m) := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := hlam_def ▸ (div_pos one_pos hNm_pos).le
  refine (tail_bound_from_mgf N X hmeas M hbound hindep hident S lam (1 + (Real.exp 1 - 1) / ↑N)
      hlam0 ?_ ?_).trans ?_
  · refine ((mgf_le_of_bounded (X 0) (hmeas 0) M hM m hmean (hbound 0) lam hlam0).trans
      (chord_exp_bound hm hM hlam0 (by
        rw [hlam_def, div_mul_eq_mul_div, one_mul]
        exact (div_le_one hNm_pos).mpr hNm))).trans_eq ?_
    rw [hlam_def, one_div_mul_eq_div, mul_comm (N : ℝ) m, ← div_div,
      div_self (right_ne_zero_of_mul hNm_pos.ne'), mul_one_div]
  · exact one_add_div_pow_le_exp (sub_nonneg.mpr (Real.one_le_exp zero_le_one)) N (NeZero.ne N)
  · rw [← Real.exp_add, show -lam * S + (Real.exp 1 - 1)
      = (Real.exp 1 - 1) - S / ((N : ℝ) * m) from by rw [hlam_def]; ring]
    exact Real.exp_le_exp.mpr (sub_le_sub_right (by linarith only [Real.exp_pos (1 : ℝ)]) _)

/-- Tail bound for i.i.d. [0, M]-valued random variables with mean m, case N * m < M :
    P {∑ X i > S} ≤ exp(10 * e - S / M). -/
theorem lemma_A1_case_lt {P : Measure Ω} [IsProbabilityMeasure P]
    (N : ℕ) [NeZero N] (X : Fin N → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (M : ℝ) (hM : 0 < M)
    (m : ℝ) (hm : 0 ≤ m) (_hmM : m ≤ M)
    (hbound : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω ∧ X i ω ≤ M)
    (hmean : ∫ ω, X 0 ω ∂P = m) (hindep : iIndepFun X P)
    (hident : ∀ i : Fin N, IdentDistrib (X i) (X 0) P P)
    (S : ℝ) (hNm : (N : ℝ) * m < M) :
    (P {ω | ∑ i : Fin N, X i ω > S}).toReal ≤
      Real.exp (10 * Real.exp 1 - S / M) := by
  have he_nn : 0 ≤ Real.exp 1 - 1 := sub_nonneg.mpr (Real.one_le_exp zero_le_one)
  have hpow_bd : (1 + (m / M) * (Real.exp 1 - 1)) ^ N ≤ Real.exp (Real.exp 1 - 1) := by
    refine (pow_le_pow_left₀ (add_nonneg zero_le_one (mul_nonneg (div_nonneg hm hM.le) he_nn))
      ((add_comm _ _).trans_le (Real.add_one_le_exp _)) N).trans ?_
    rw [← Real.exp_nat_mul, ← mul_assoc, mul_div_assoc']
    exact Real.exp_le_exp.mpr (mul_le_of_le_one_left he_nn ((div_le_one hM).mpr hNm.le))
  have hlam : (0 : ℝ) ≤ 1 / M := (div_pos one_pos hM).le
  refine (tail_bound_from_mgf N X hmeas M hbound hindep hident S (1 / M) _ hlam
    ((mgf_le_of_bounded (X 0) (hmeas 0) M hM m hmean (hbound 0) (1 / M) hlam).trans_eq
      (by rw [one_div, inv_mul_cancel₀ hM.ne']; ring)) hpow_bd).trans ?_
  rw [← Real.exp_add, neg_mul, one_div, inv_mul_eq_div]
  exact Real.exp_le_exp.mpr (by linarith only [Real.exp_pos (1 : ℝ)])

namespace Bernoulli

/-- The N-fold product Bernoulli(p) measure on `Fin N → Bool`. Sample interpretation:
each coordinate is independently `true` with probability `p`. -/
noncomputable def bernoulliPi (N : ℕ) (p : ℝ) :
    Measure (Fin N → Bool) :=
  Measure.pi (fun _ : Fin N =>
    ENNReal.ofReal p • Measure.dirac true +
    ENNReal.ofReal (1 - p) • Measure.dirac false)

/-- The single Bernoulli(p) factor measure on `Bool`. -/
noncomputable def bernoulliFactor (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false

instance bernoulliFactor_isProbabilityMeasure {p : ℝ}
    [hp0 : Fact (0 ≤ p)] [hp1 : Fact (p ≤ 1)] :
    IsProbabilityMeasure (bernoulliFactor p) :=
  ⟨by simp [bernoulliFactor, ← ENNReal.ofReal_add hp0.out (sub_nonneg.mpr hp1.out)]⟩

lemma bernoulliPi_eq (N : ℕ) (p : ℝ) :
    bernoulliPi N p = Measure.pi (fun _ : Fin N => bernoulliFactor p) := rfl

/-- `bernoulliPi` is a probability measure. -/
instance bernoulliPi_isProbabilityMeasure (N : ℕ) (p : ℝ)
    [Fact (0 ≤ p)] [Fact (p ≤ 1)] :
    IsProbabilityMeasure (bernoulliPi N p) :=
  bernoulliPi_eq N p ▸ inferInstance

/-- Indicator random variables for the Bernoulli(p) i.i.d. sequence. The `i`-th
coordinate produces `1` if the sample's `i`-th bit is `true`, else `0`.
This is the `Set.indicator` of `{ω | ω i = true}` with constant value `1`. -/
noncomputable def bernoulliIndicator (N : ℕ) (i : Fin N) : (Fin N → Bool) → ℝ :=
  Set.indicator {ω | ω i} 1

lemma bernoulliIndicator_apply (N : ℕ) (i : Fin N) (ω : Fin N → Bool) :
    bernoulliIndicator N i ω = if ω i then (1 : ℝ) else 0 := by
  rw [bernoulliIndicator, Set.indicator_apply]; simp

/-- Each indicator is measurable. -/
lemma bernoulliIndicator_measurable (N : ℕ) (i : Fin N) :
    Measurable (bernoulliIndicator N i) := measurable_of_finite _

lemma bernoulliIndicator_nonneg (N : ℕ) (i : Fin N) (ω : Fin N → Bool) :
    0 ≤ bernoulliIndicator N i ω :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) ω

lemma bernoulliIndicator_le_one (N : ℕ) (i : Fin N) (ω : Fin N → Bool) :
    bernoulliIndicator N i ω ≤ 1 := by
  simp only [bernoulliIndicator_apply]; split_ifs <;> norm_num

lemma bernoulliIndicator_integrable (N : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin N) : Integrable (bernoulliIndicator N i) (bernoulliPi N p) := by
  haveI : Fact (0 ≤ p) := ⟨hp0⟩
  haveI : Fact (p ≤ 1) := ⟨hp1⟩
  exact Integrable.of_finite

/-- The indicator family is jointly independent under `bernoulliPi`. -/
theorem bernoulliIndicator_iIndep (N : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    iIndepFun (bernoulliIndicator N) (bernoulliPi N p) := by
  haveI : Fact (0 ≤ p) := ⟨hp0⟩
  haveI : Fact (p ≤ 1) := ⟨hp1⟩
  have h_eq : bernoulliIndicator N = fun (i : Fin N) ω => if ω i then (1:ℝ) else 0 := by
    funext i ω; exact bernoulliIndicator_apply N i ω
  rw [h_eq, bernoulliPi_eq]
  exact iIndepFun_pi (μ := fun _ : Fin N => bernoulliFactor p)
    (X := fun _ : Fin N => fun b : Bool => if b then (1:ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)

/-- All indicators are identically distributed. -/
theorem bernoulliIndicator_identDistrib (N : ℕ) [NeZero N] (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : Fin N) :
    IdentDistrib (bernoulliIndicator N i) (bernoulliIndicator N 0)
      (bernoulliPi N p) (bernoulliPi N p) := by
  haveI : Fact (0 ≤ p) := ⟨hp0⟩
  haveI : Fact (p ≤ 1) := ⟨hp1⟩
  have hgen : ∀ j : Fin N, bernoulliIndicator N j
      = (fun b : Bool => if b then (1 : ℝ) else 0) ∘ Function.eval j :=
    fun j => funext (bernoulliIndicator_apply N j)
  rw [hgen i, hgen 0]
  refine IdentDistrib.comp ⟨(measurable_pi_apply i).aemeasurable,
    (measurable_pi_apply 0).aemeasurable, ?_⟩ (measurable_of_finite _)
  rw [bernoulliPi_eq, (measurePreserving_eval _ i).map_eq, (measurePreserving_eval _ 0).map_eq]

/-- Each indicator has mean `p`. -/
theorem bernoulliIndicator_integral (N : ℕ) [NeZero N] (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : Fin N) :
    ∫ ω, bernoulliIndicator N i ω ∂(bernoulliPi N p) = p := by
  haveI : Fact (0 ≤ p) := ⟨hp0⟩
  haveI : Fact (p ≤ 1) := ⟨hp1⟩
  rw [bernoulliIndicator, show {ω : Fin N → Bool | ω i} = (fun f => f i) ⁻¹' {true} from rfl,
      integral_indicator_one (measurable_pi_apply i (measurableSet_singleton true)),
      measureReal_def, bernoulliPi_eq,
      (measurePreserving_eval (fun _ : Fin N => bernoulliFactor p) i).measure_preimage
        (measurableSet_singleton true).nullMeasurableSet]
  simp [bernoulliFactor, ENNReal.toReal_ofReal hp0]

end Bernoulli

open Bernoulli

theorem exists_compl_iUnion (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] (A : ι → Set Ω) (_hAm : ∀ i, MeasurableSet (A i))
    (h : ∑ i, (P (A i)).toReal < 1) :
    ∃ ω, ∀ i, ω ∉ A i := by
  by_contra! hcon
  have h1 := measureReal_iUnion_fintype_le (μ := P) A
  simp only [Set.iUnion_eq_univ_iff.mpr hcon, measureReal_def, measure_univ,
    ENNReal.toReal_one] at h1
  linarith

lemma exp_neg_le_quadratic {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
  -- `(1 - t + t²/2) * exp t ≥ (1 - t + t²/2) * (1 + t + t²/2) = 1 + t⁴/4 ≥ 1`.
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos t)]
  linear_combination mul_le_mul_of_nonneg_left (Real.quadratic_le_exp_of_nonneg ht)
    (div_nonneg (add_nonneg (sq_nonneg (t - 1)) zero_le_one) zero_le_two) + sq_nonneg (t ^ 2) / 4

lemma kl_lower_bound {x : ℝ} (hx : 1 ≤ x) :
    (x - 1) ^ 2 / (2 * x) ≤ x * Real.log x - (x - 1) := by
  -- `log x ≥ 2 (x - 1) / (x + 1)` gives `x log x - (x - 1) ≥ (x - 1)² / (x + 1) ≥ (x - 1)² / (2x)`.
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans_le hx
  have h := Real.le_log_one_add_of_nonneg (sub_nonneg.mpr hx)
  rw [show (1 : ℝ) + (x - 1) = x by ring, div_le_iff₀ (by linarith only [hx0])] at h
  refine (div_le_div_of_nonneg_left (sq_nonneg _) (by linarith only [hx0] : (0 : ℝ) < x + 1)
    (by linarith only [hx] : x + 1 ≤ 2 * x)).trans ?_
  rw [div_le_iff₀ (by linarith only [hx0])]
  linarith only [mul_le_mul_of_nonneg_left h hx0.le]

-- (extracted by Fuse golfer) Ratio form of `kl_lower_bound`, used for the Chernoff upper tail.
private lemma kl_div_lower_bound {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    (a - b) ^ 2 / (2 * a) ≤ a * Real.log (a / b) - (a - b) := by
  have ha : a ≠ 0 := (hb.trans_le hab).ne'
  have hb' : b ≠ 0 := hb.ne'
  have h := mul_le_mul_of_nonneg_right (kl_lower_bound ((one_le_div hb).mpr hab)) hb.le
  rwa [show (a / b - 1) ^ 2 / (2 * (a / b)) * b = (a - b) ^ 2 / (2 * a) by field_simp,
    show (a / b * Real.log (a / b) - (a / b - 1)) * b = a * Real.log (a / b) - (a - b) from by
      linear_combination (Real.log (a / b) - 1) * div_mul_cancel₀ a hb'] at h

-- (extracted by Fuse golfer) The weighted indicators are jointly independent.
private lemma iIndepFun_smul_bernoulliIndicator {N : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (c : Fin N → ℝ) :
    iIndepFun (fun i ω => c i * bernoulliIndicator N i ω) (bernoulliPi N p) :=
  (bernoulliIndicator_iIndep N p hp0 hp1).comp (g := fun i (x : ℝ) => c i * x)
    fun _ => measurable_const.mul measurable_id

-- (extracted by Fuse golfer) Moment generating function of a scaled Bernoulli indicator.
private lemma mgf_smul_bernoulliIndicator {N : ℕ} [NeZero N] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin N) (a t : ℝ) :
    mgf (fun ω => a * bernoulliIndicator N i ω) (bernoulliPi N p) t
      = (1 - p) + p * Real.exp (t * a) := by
  haveI : Fact (0 ≤ p) := ⟨hp0⟩
  haveI : Fact (p ≤ 1) := ⟨hp1⟩
  rw [mgf, show (fun ω => Real.exp (t * (a * bernoulliIndicator N i ω)))
      = (fun ω => 1 + bernoulliIndicator N i ω * (Real.exp (t * a) - 1)) from
      funext fun ω => by simp only [bernoulliIndicator_apply]; split_ifs <;> simp,
    integral_add (integrable_const _) ((bernoulliIndicator_integrable N p hp0 hp1 i).mul_const _),
    integral_const, integral_mul_const, bernoulliIndicator_integral N p hp0 hp1 i,
    probReal_univ, smul_eq_mul]
  ring

-- (extracted by Fuse golfer) Chernoff-style bound on the mgf of a weighted Bernoulli sum,
-- valid for every real `t` (used for both tails).
private lemma mgf_sum_smul_bernoulliIndicator_le {N : ℕ} [NeZero N] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (c : Fin N → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    (t : ℝ) :
    mgf (fun ω => ∑ i, c i * bernoulliIndicator N i ω) (bernoulliPi N p) t
      ≤ Real.exp (p * (∑ i, c i) * (Real.exp t - 1)) := by
  haveI : Fact (0 ≤ p) := ⟨hp0⟩
  haveI : Fact (p ≤ 1) := ⟨hp1⟩
  rw [show (fun ω => ∑ i, c i * bernoulliIndicator N i ω)
        = ∑ i ∈ (Finset.univ : Finset (Fin N)), fun ω => c i * bernoulliIndicator N i ω from
      funext fun ω => by simp only [Finset.sum_apply],
    (iIndepFun_smul_bernoulliIndicator hp0 hp1 c).mgf_sum
      (fun i => measurable_const.mul (bernoulliIndicator_measurable N i))
      (Finset.univ : Finset (Fin N)) (t := t)]
  refine (Finset.prod_le_prod (g := fun i => Real.exp (p * c i * (Real.exp t - 1)))
    (fun _ _ => mgf_nonneg) (fun i _ => ?_)).trans_eq
    (by rw [← Real.exp_sum, ← Finset.sum_mul, ← Finset.mul_sum])
  rw [mgf_smul_bernoulliIndicator hp0 hp1 i (c i) t]
  have h := exp_mul_le_of_mem_Icc (lam := t) one_pos (hc0 i) (hc1 i)
  simp only [div_one, mul_one] at h
  linarith only [mul_le_mul_of_nonneg_left h hp0, Real.add_one_le_exp (p * c i * (Real.exp t - 1))]

-- (extracted by Fuse golfer) Raw Chernoff upper-tail estimate at an arbitrary rate `lam ≥ 0`,
-- before optimising over `lam`.
private lemma measure_gt_sum_smul_bernoulliIndicator_le {N : ℕ} [NeZero N] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (c : Fin N → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    (S : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    (bernoulliPi N p {ω | S < ∑ i, c i * bernoulliIndicator N i ω}).toReal ≤
      Real.exp (-lam * S + p * (∑ i, c i) * (Real.exp lam - 1)) := by
  haveI : Fact (0 ≤ p) := ⟨hp0⟩
  haveI : Fact (p ≤ 1) := ⟨hp1⟩
  rw [Real.exp_add]
  exact (measureReal_mono (fun _ (hω : S < _) => hω.le) (measure_ne_top _ _)).trans
    ((measure_ge_le_exp_mul_mgf S hlam Integrable.of_finite).trans
      (mul_le_mul_of_nonneg_left (mgf_sum_smul_bernoulliIndicator_le hp0 hp1 c hc0 hc1 lam)
        (Real.exp_pos _).le))

-- (extracted by Fuse golfer) Choice of Chernoff rate: for `0 ≤ μ ≤ S` there is a rate `lam ≥ 0`
-- whose Chernoff exponent `-lam * S + μ * (exp lam - 1)` is at most `-(S - μ)² / (2 S)`.
-- The optimal rate is `log (S / μ)`; for `μ = 0` any positive rate works.
private lemma exists_chernoff_rate {μ S : ℝ} (hμ0 : 0 ≤ μ) (hSμ : μ ≤ S) :
    ∃ lam : ℝ, 0 ≤ lam ∧
      -lam * S + μ * (Real.exp lam - 1) ≤ -(S - μ) ^ 2 / (2 * S) := by
  rcases hμ0.eq_or_lt with hμ | hμ
  · refine ⟨2⁻¹, by norm_num, ?_⟩
    rcases (hμ0.trans hSμ).eq_or_lt with hS | hS
    · rw [← hμ, ← hS]; norm_num
    · rw [← hμ, le_div_iff₀ (by linarith : (0:ℝ) < 2 * S)]; exact le_of_eq (by ring)
  · refine ⟨Real.log (S / μ), Real.log_nonneg ((one_le_div hμ).mpr hSμ), ?_⟩
    rw [Real.exp_log (div_pos (hμ.trans_le hSμ) hμ), mul_sub, mul_one,
      mul_div_cancel₀ S hμ.ne', neg_div]
    exact (le_of_eq (by ring)).trans (neg_le_neg (kl_div_lower_bound hμ hSμ))

/-- Weighted upper-tail Chernoff bound for the i.i.d. Bernoulli sample.
With weights `c i ∈ [0, 1]` and mean `μ := p · ∑ c i`,
`P[∑ c i · χ_i > S] ≤ exp(-(S - μ)² / (2 S))` for any `S ≥ μ ≥ 0`. -/
theorem chernoff_bernoulli_weighted_upper
    (N : ℕ) [NeZero N] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (c : Fin N → ℝ) (_hc0 : ∀ i, 0 ≤ c i) (_hc1 : ∀ i, c i ≤ 1)
    (S : ℝ) (_hSμ : p * ∑ i, c i ≤ S) :
    (bernoulliPi N p
        {ω | S < ∑ i, c i * bernoulliIndicator N i ω}).toReal ≤
      Real.exp (- (S - p * ∑ i, c i) ^ 2 / (2 * S)) := by
  obtain ⟨lam, hlam0, hlam⟩ := exists_chernoff_rate
    (mul_nonneg hp0 (Finset.sum_nonneg fun i _ => _hc0 i)) _hSμ
  exact (measure_gt_sum_smul_bernoulliIndicator_le hp0 hp1 c _hc0 _hc1 S hlam0).trans
    (Real.exp_le_exp.mpr hlam)

/-- Weighted lower-tail Chernoff bound for the i.i.d. Bernoulli sample.
With weights `c i ∈ [0, 1]` and mean `μ := p · ∑ c i > 0`,
`P[∑ c i · χ_i < S] ≤ exp(-(μ - S)² / (2 μ))` for any `0 ≤ S ≤ μ`. -/
theorem chernoff_bernoulli_weighted_lower
    (N : ℕ) [NeZero N] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (c : Fin N → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    (S : ℝ) (hS0 : 0 ≤ S) (hSμ : S ≤ p * ∑ i, c i) :
    (bernoulliPi N p {ω | (∑ i, c i * bernoulliIndicator N i ω) < S}).toReal ≤
      Real.exp (- (p * ∑ i, c i - S) ^ 2 / (2 * (p * ∑ i, c i))) := by
  haveI : Fact (0 ≤ p) := ⟨hp0⟩
  haveI : Fact (p ≤ 1) := ⟨hp1⟩
  set μ := p * ∑ i, c i
  have hμ0 : 0 ≤ μ := mul_nonneg hp0 (Finset.sum_nonneg fun i _ => hc0 i)
  rcases hμ0.eq_or_lt with hμ | hμ
  · -- Degenerate case: `S = μ = 0`, so the bound is `exp 0 = 1`.
    rw [← hμ, le_antisymm (hSμ.trans_eq hμ.symm) hS0]
    exact measureReal_le_one.trans (Real.one_le_exp (by norm_num))
  -- Optimal rate `lam = (μ - S) / μ`, then the quadratic bound on `exp (-lam)`.
  obtain ⟨lam, hlam_nn, hd⟩ : ∃ x : ℝ, 0 ≤ x ∧ μ * x = μ - S :=
    ⟨(μ - S) / μ, div_nonneg (sub_nonneg.mpr hSμ) hμ.le, mul_div_cancel₀ _ hμ.ne'⟩
  rw [show -(μ - S) ^ 2 / (2 * μ) = -(-lam) * S + μ * (-lam + lam ^ 2 / 2) by
      rw [div_eq_iff (mul_ne_zero two_ne_zero hμ.ne')]
      linear_combination (μ - S - μ * lam) * hd, Real.exp_add]
  refine (measureReal_mono (fun ω (hω : _ < S) => hω.le) (measure_ne_top _ _)).trans
    ((measure_le_le_exp_mul_mgf (X := fun ω => ∑ i, c i * bernoulliIndicator N i ω) S
      (neg_nonpos.mpr hlam_nn) Integrable.of_finite).trans
      (mul_le_mul_of_nonneg_left ((mgf_sum_smul_bernoulliIndicator_le hp0 hp1 c hc0 hc1
        (-lam)).trans (Real.exp_le_exp.mpr ?_)) (Real.exp_pos _).le))
  exact mul_le_mul_of_nonneg_left (by linarith only [exp_neg_le_quadratic hlam_nn]) hμ0

end Probability

namespace Kakeya

open MeasureTheory (volume)

/-! ### Random-subset extraction

The definitions below turn a `{0,1}`-valued sample into a finite subset and relate its
cardinality and weighted sums to the corresponding indicator variables.
-/

/-- The random subset of `s : Finset ι` selected by a `{0,1}`-valued sample function. -/
noncomputable def randomSubset
    {ι : Type*} (s : Finset ι) {Ω : Type*}
    (χ : Fin s.card → Ω → ℝ) (ω : Ω) : Finset ι := by
  classical
  exact {i ∈ (Finset.univ : Finset (Fin s.card)) | χ i ω = 1}.image
    (fun i => ((s.equivFin.symm i) : s).val)

/-- The random subset is contained in `s`. -/
lemma randomSubset_subset
    {ι : Type*} (s : Finset ι) {Ω : Type*}
    (χ : Fin s.card → Ω → ℝ) (ω : Ω) :
    randomSubset s χ ω ⊆ s := by
  classical
  unfold randomSubset
  rw [Finset.image_subset_iff]
  exact fun i _ => (s.equivFin.symm i).2

/-- Sums over the random subset rewrite as weighted sums of indicators on `Fin s.card`. -/
lemma sum_over_randomSubset
    {ι : Type*} (s : Finset ι) {Ω : Type*}
    (χ : Fin s.card → Ω → ℝ) (ω : Ω)
    (hχ : ∀ i, χ i ω = 0 ∨ χ i ω = 1) (f : ι → ℝ) :
    ∑ i ∈ randomSubset s χ ω, f i =
      ∑ i : Fin s.card, χ i ω * f ((s.equivFin.symm i : ↥s).val) := by
  classical
  unfold randomSubset
  rw [Finset.sum_image fun a _ b _ hab =>
      s.equivFin.symm.injective (Subtype.val_injective hab), Finset.sum_filter]
  exact Finset.sum_congr rfl fun i _ => by rcases hχ i with h | h <;> simp [h]

/-- For `{0,1}`-valued samples, the cardinality of the random subset equals the sum of
indicator values. -/
lemma randomSubset_card_eq_sum
    {ι : Type*} (s : Finset ι) {Ω : Type*}
    (χ : Fin s.card → Ω → ℝ) (ω : Ω)
    (hχ : ∀ i, χ i ω = 0 ∨ χ i ω = 1) :
    ((randomSubset s χ ω).card : ℝ) = ∑ i : Fin s.card, χ i ω := by
  simpa only [mul_one, Finset.sum_const, nsmul_eq_mul] using
    sum_over_randomSubset s χ ω hχ fun _ => 1

/-- Comparison of an indicator-weighted sum on `Fin s.card` with a sum over the random
subset: if `c * g j` is dominated termwise by `f`, then `c * S ≤ ∑_{i ∈ s'} f i`. -/
private lemma le_sum_over_randomSubset -- (extracted by Fuse golfer)
    {ι : Type*} (s : Finset ι) {Ω : Type*}
    (χ : Fin s.card → Ω → ℝ) (ω : Ω) (hχ_nn : ∀ j, 0 ≤ χ j ω)
    (hχ : ∀ j, χ j ω = 0 ∨ χ j ω = 1) {f : ι → ℝ} {g : Fin s.card → ℝ} {c S : ℝ}
    (hc : 0 ≤ c) (hg : ∀ j, c * g j ≤ f ((s.equivFin.symm j : ↥s).val))
    (hS : S ≤ ∑ j, g j * χ j ω) :
    c * S ≤ ∑ i ∈ randomSubset s χ ω, f i := by
  refine (mul_le_mul_of_nonneg_left hS hc).trans ?_
  rw [sum_over_randomSubset s χ ω hχ f, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => (mul_assoc c (g j) (χ j ω)).ge.trans
    ((mul_le_mul_of_nonneg_right (hg j) (hχ_nn j)).trans_eq (mul_comm _ _))

/-- A sum over the random subset is at most a uniform termwise bound times the number of
selected indices. -/
private lemma sum_over_randomSubset_le -- (extracted by Fuse golfer)
    {ι : Type*} (s : Finset ι) {Ω : Type*}
    (χ : Fin s.card → Ω → ℝ) (ω : Ω) (hχ_nn : ∀ j, 0 ≤ χ j ω)
    (hχ : ∀ j, χ j ω = 0 ∨ χ j ω = 1) {f : ι → ℝ} {c : ℝ}
    (hf : ∀ j, f ((s.equivFin.symm j : ↥s).val) ≤ c) :
    ∑ i ∈ randomSubset s χ ω, f i ≤ c * ∑ j, χ j ω := by
  rw [sum_over_randomSubset s χ ω hχ f, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    (mul_le_mul_of_nonneg_left (hf j) (hχ_nn j)).trans_eq (mul_comm _ _)

section KatzTaoExistsRandomSubset

universe u

variable
  (E : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Local real-valued multiplicity adapter. -/
noncomputable def multiplicityRLocal
    {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) : ℝ :=
  (ShadedBody.multiplicity s V).toReal

lemma multiplicityRLocal_nonneg
    {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) :
    0 ≤ multiplicityRLocal E s V := ENNReal.toReal_nonneg

lemma multiplicityRLocal_eq_div
    {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) :
    multiplicityRLocal E s V =
      (∑ i ∈ s, MeasureTheory.volume.real (V i).shade) /
        MeasureTheory.volume.real (⋃ i ∈ s, (V i).shade) := by
  unfold multiplicityRLocal ShadedBody.multiplicity
  rw [ENNReal.toReal_div, ENNReal.toReal_sum fun i _ =>
    ne_top_of_le_ne_top (V i).isCompact'.measure_ne_top (measure_mono (V i).shade_subset)]
  rfl

lemma multiplicityRLocal_le_card
    {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) :
    multiplicityRLocal E s V ≤ s.card :=
  ENNReal.toReal_natCast s.card ▸
    ENNReal.toReal_mono (ENNReal.natCast_ne_top _) (ShadedBody.multiplicity_le_card s V)

/-- A singleton family whose shade has positive volume has multiplicity `1`. -/
private lemma multiplicityRLocal_singleton {ι : Type*} (V : ι → ShadedBody E) {i : ι}
    (h : volume.real (V i).shade ≠ 0) : -- (extracted by Fuse golfer)
    multiplicityRLocal E {i} V = 1 := by
  rw [multiplicityRLocal_eq_div, Finset.sum_singleton, Finset.set_biUnion_singleton, div_self h]

/-- The fullness of a singleton family is the shade-to-carrier ratio of its single member,
so a pointwise bound `a * carrier ≤ shade` bounds it from below. -/
private lemma le_fullness_singleton {ι : Type*} (V : ι → ShadedBody E) {i : ι} {a : ℝ}
    (hpos : 0 < volume.real (V i).carrier) -- (extracted by Fuse golfer)
    (h : a * volume.real (V i).carrier ≤ volume.real (V i).shade) :
    a ≤ ((ShadedBody.fullness {i} V : NNReal) : ℝ) :=
  le_of_mul_le_mul_right (h.trans_eq (by simpa only [Finset.sum_singleton] using
    _sum_shade_eq_fullness_mul_sum_carrier E {i} V (by rwa [Finset.sum_singleton]))) hpos

/-- For 2 ≤ A and 0 ≤ μ ≤ 1, -(A-μ)²/(2A) ≤ -A/8. -/
private lemma exists_random_subset_aux2 (A μ : ℝ) (hA : 2 ≤ A)
    (_hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) : -(A - μ) ^ 2 / (2 * A) ≤ -A / 8 := by
  rw [div_le_div_iff₀ (by linarith only [hA] : (0:ℝ) < 2 * A) (by norm_num : (0:ℝ) < 8)]
  linarith only [mul_nonneg (by linarith only [hA, hμ1] : (0:ℝ) ≤ 3 * A - 2 * μ)
    (by linarith only [hA, hμ1] : (0:ℝ) ≤ A - 2 * μ)]

/-- For x ≥ 2, x²/4 ≤ (x-1)². -/
private lemma exists_random_subset_aux1 (x : ℝ) (_hx_pos : 0 < x) (hx_ge_2 : 2 ≤ x) :
    -(x - 1) ^ 2 / (2 * x) ≤ -x / 8 :=
  exists_random_subset_aux2 x 1 hx_ge_2 zero_le_one le_rfl

/-- The smallness condition `2 K² ≤ δ^(-c)` is implied by `4 K⁴ ≤ δ^(-η₁)` when `η₁ < c / 2`. -/
private lemma two_K2_le_rpow_neg_of_four_K4 {δ K η₁ c : ℝ} (hδ_pos : 0 < δ) (hδ1 : δ < 1)
    (hK : 1 ≤ K) (hη₁ : 0 < η₁) (hc : η₁ < c / 2) (hfull : 4 * K ^ 4 ≤ δ ^ (-η₁)) :
    2 * K ^ 2 ≤ δ ^ (-c) := by
  -- `δ^(-η₁) ≤ δ^(-c)` since `δ < 1` and `η₁ < c`, and `2 K² ≤ 4 K⁴`.
  refine (le_trans ?_ hfull).trans (Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ1.le (by linarith))
  linarith only [sq_nonneg K, pow_le_pow_right₀ hK (by norm_num : 2 ≤ 4)]

/-- The `η₁`-shifted exponential smallness condition implies its unshifted counterpart. -/
private lemma exp_neg_rpow_le_of_shift {δ K η₁ c : ℝ} (hδ_pos : 0 < δ) (hδ1 : δ < 1)
    (hK : 1 ≤ K) (hη₁ : 0 < η₁)
    (h : Real.exp (-δ ^ (η₁ - c / 2) / (8 * K ^ 2)) ≤ 1 / 5) :
    Real.exp (-δ ^ (-c / 2) / 8) ≤ 1 / 5 := by
  refine (Real.exp_le_exp.mpr ?_).trans h
  simp only [neg_div, neg_le_neg_iff]
  exact div_le_div₀ (Real.rpow_nonneg hδ_pos.le _) (Real.rpow_le_rpow_of_exponent_ge hδ_pos
    hδ1.le ((sub_le_sub_right hη₁.le (c / 2)).trans_eq' (zero_sub _)))
    (by norm_num) (le_mul_of_one_le_right (by norm_num) (one_le_pow₀ hK))

/-- Reindexing a sum over `Fin s.card` to a sum over `s` via `s.equivFin`. -/
private lemma sum_via_equivFin {ι α : Type*} [AddCommMonoid α] (s : Finset ι) (f : ι → α) :
    ∑ j : Fin s.card, f ((s.equivFin.symm j) : ↥s).val = ∑ i ∈ s, f i :=
  (Equiv.sum_comp s.equivFin.symm fun x : ↥s => f x.val).trans (Finset.sum_coe_sort s f)

-- (extracted by Fuse golfer) The all-ones weight vector on `Fin N` sums to `N`.
private lemma sum_const_one (N : ℕ) : ∑ _i : Fin N, (1 : ℝ) = N := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- Specialized Chernoff upper-tail count bound: for i.i.d. Bernoulli(p) on Fin N,
    `P[∑ χ > S] ≤ exp(-(S - pN)²/(2S))` whenever `pN ≤ S`. -/
private lemma chernoff_count_upper {N : ℕ} [NeZero N] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {S : ℝ} (hμle : p * (N : ℝ) ≤ S) :
    ((Probability.Bernoulli.bernoulliPi N p)
        {ω | S < ∑ i, Probability.Bernoulli.bernoulliIndicator N i ω}).toReal ≤
      Real.exp (- (S - p * (N : ℝ)) ^ 2 / (2 * S)) := by
  simpa only [one_mul, sum_const_one] using Probability.chernoff_bernoulli_weighted_upper N p hp0
    hp1 (fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl) S
    (by simpa only [sum_const_one] using hμle)

/-- Specialized Chernoff lower-tail count bound: for i.i.d. Bernoulli(p) on Fin N,
    `P[∑ χ < S] ≤ exp(-(pN - S)²/(2 pN))` whenever `0 ≤ S ≤ pN`. -/
private lemma chernoff_count_lower {N : ℕ} [NeZero N] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {S : ℝ} (hS_nn : 0 ≤ S) (hS_le : S ≤ p * (N : ℝ)) :
    ((Probability.Bernoulli.bernoulliPi N p)
        {ω | (∑ i, Probability.Bernoulli.bernoulliIndicator N i ω) < S}).toReal ≤
      Real.exp (- (p * (N : ℝ) - S) ^ 2 / (2 * (p * (N : ℝ)))) := by
  simpa only [one_mul, sum_const_one] using Probability.chernoff_bernoulli_weighted_lower N p hp0
    hp1 (fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl) S hS_nn
    (by simpa only [sum_const_one] using hS_le)

/-- The Multiplicity tail of `exists_random_subset`: given a uniform lower bound
    `(∑ i ∈ s, shade i) / (2 Δ K²) ≤ ∑ i ∈ s', shade i` and a smallness assumption
    `2 K² ≤ δ^(-c)`, conclude `multiplicity s ≤ δ^(-c) Δ multiplicity s'`. -/
private lemma multiplicity_upper_bound_helper {ι : Type*} {s s' : Finset ι}
    (V : ι → ShadedBody E) (hs'_sub : s' ⊆ s)
    {Δ K_unif δ c : ℝ} (hΔ_pos : 0 < Δ) (hK_unif_pos : 0 < K_unif) (hδ_pos : 0 < δ)
    (hδ_small_d : 2 * K_unif ^ 2 ≤ δ ^ (-c))
    (h_sum_shade_lb : (∑ i ∈ s, volume.real (V i).shade) / (2 * Δ * K_unif ^ 2)
      ≤ ∑ i ∈ s', volume.real (V i).shade) :
    multiplicityRLocal E s V ≤ δ ^ (-c) * Δ * multiplicityRLocal E s' V := by
  have hC_nn : 0 ≤ δ ^ (-c) * Δ := mul_nonneg (Real.rpow_nonneg hδ_pos.le _) hΔ_pos.le
  have h_sum_shade_nn : 0 ≤ ∑ i ∈ s', volume.real (V i).shade :=
    Finset.sum_nonneg fun _ _ => measureReal_nonneg
  have h_sum_s_le' : ∑ i ∈ s, volume.real (V i).shade ≤
      δ ^ (-c) * Δ * ∑ i ∈ s', volume.real (V i).shade :=
    ((div_le_iff₀' (mul_pos (mul_pos two_pos hΔ_pos) (pow_pos hK_unif_pos 2))).mp
        h_sum_shade_lb).trans
      (mul_le_mul_of_nonneg_right ((mul_right_comm 2 Δ (K_unif ^ 2)).trans_le
        (mul_le_mul_of_nonneg_right hδ_small_d hΔ_pos.le)) h_sum_shade_nn)
  rw [multiplicityRLocal_eq_div, multiplicityRLocal_eq_div, ← mul_div_assoc]
  by_cases hUs'_zero : volume.real (⋃ i ∈ s', (V i).shade) = 0
  · have h_sum_s'_zero : ∑ i ∈ s', volume.real (V i).shade = 0 :=
      Finset.sum_eq_zero fun i hi => le_antisymm
        ((measureReal_mono (Finset.subset_set_biUnion_of_mem (f := fun j => (V j).shade) hi)
          (ShadedBody.volume_iUnion_shade_ne_top s' V)).trans_eq hUs'_zero)
        measureReal_nonneg
    rw [h_sum_s'_zero, mul_zero] at h_sum_s_le'
    rw [le_antisymm h_sum_s_le' (Finset.sum_nonneg fun _ _ => measureReal_nonneg), zero_div]
    exact div_nonneg (mul_nonneg hC_nn h_sum_shade_nn) measureReal_nonneg
  exact div_le_div₀ (mul_nonneg hC_nn h_sum_shade_nn) h_sum_s_le'
    (measureReal_nonneg.lt_of_ne' hUs'_zero)
    (measureReal_mono (Set.iUnion₂_subset fun i hi =>
      Finset.subset_set_biUnion_of_mem (f := fun j => (V j).shade) (hs'_sub hi))
      (ShadedBody.volume_iUnion_shade_ne_top s V))

/-- Real-valued form of `one_le_maxDensity`. -/
private lemma one_le_maxDensity_toReal {ι : Type*} {s : Finset ι} -- (extracted by Fuse golfer)
    {W : ι → ConvexSpaceBody E} (h : ∃ i ∈ s, 0 < volume (W i).carrier) :
    1 ≤ (maxDensity s W).toReal :=
  ENNReal.toReal_one ▸ ENNReal.toReal_mono (maxDensity_ne_top s W) (one_le_maxDensity h)

/-- Real-valued form of `maxDensity_le_card`. -/
private lemma maxDensity_toReal_le_card {ι : Type*} (s : Finset ι) -- (extracted by Fuse golfer)
    (W : ι → ConvexSpaceBody E) : (maxDensity s W).toReal ≤ (s.card : ℝ) :=
  ENNReal.toReal_natCast s.card ▸
    ENNReal.toReal_mono (ENNReal.natCast_ne_top _) (maxDensity_le_card s W)

/-- Small/dense case of `exists_random_subset`: when `s.card / Δ ≤ δ^(-c/2)`, the
singleton `{istar}` (a chosen heavy index) already witnesses all four conclusions. -/
private lemma exists_random_subset_small_case {δ : NNReal} {η₁ c : ℝ} (hη₁ : 0 < η₁)
    (h : η₁ < c / 2) {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E)
    (hδ : 0 < (δ : ℝ)) (hδ1 : (δ : ℝ) < 1)
    (istar : ι) (histar_mem : istar ∈ s)
    (histar_pos : 0 < volume.real (T istar).toShadedBody.carrier)
    (histar_shade : (δ : ℝ) ^ η₁ * volume.real (T istar).toShadedBody.carrier
      ≤ volume.real (T istar).toShadedBody.shade)
    (hcase : (s.card : ℝ) / (maxDensity s (fun i => (T i).toConvexSpaceBody)).toReal
      ≤ (δ : ℝ) ^ (-c / 2)) :
    ∃ s' ⊆ s, s'.Nonempty ∧
      (s'.card : ℝ) ≤ 2 * (s.card : ℝ) *
        ((maxDensity s (fun i ↦ (T i).toConvexSpaceBody)).toReal)⁻¹ ∧
      ConvexSpaceBody.IsKatzTao s' (fun i ↦ (T i).toConvexSpaceBody)
        (ENNReal.ofReal ((δ : ℝ) ^ (-c))) ∧
      (ShadedBody.fullness s' (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (δ : ℝ) ^ (2 * η₁) ∧
      multiplicityRLocal E s (fun i ↦ (T i).toShadedBody) ≤ (δ : ℝ) ^ (-c) *
        (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)).toReal *
        multiplicityRLocal E s' (fun i ↦ (T i).toShadedBody) := by
  have hΔ_pos : 0 < (maxDensity s fun i ↦ (T i).toConvexSpaceBody).toReal := zero_lt_one.trans_le
    (one_le_maxDensity_toReal E ⟨istar, histar_mem, (ENNReal.toReal_pos_iff.mp histar_pos).1⟩)
  have hc_nonpos : -c ≤ 0 := by linarith only [h, hη₁]
  refine ⟨{istar}, Finset.singleton_subset_iff.mpr histar_mem,
    Finset.singleton_nonempty istar, ?_, ?_, ?_, ?_⟩
  · -- `#{istar} = 1 ≤ 2 * #s / Δ`, since `Δ ≤ #s`
    rw [Finset.card_singleton, Nat.cast_one, mul_assoc, ← div_eq_mul_inv]
    exact one_le_two.trans (le_mul_of_one_le_right zero_le_two
      ((one_le_div hΔ_pos).mpr (maxDensity_toReal_le_card E s _)))
  · -- `IsKatzTao {istar} W (ENNReal.ofReal (δ^(-c)))`, since `1 ≤ δ^(-c)`
    refine (maxDensity_le_card {istar} fun i ↦ (T i).toConvexSpaceBody).trans ?_
    rw [Finset.card_singleton, Nat.cast_one]
    exact ENNReal.one_le_ofReal.mpr
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1.le hc_nonpos)
  · -- `δ^(2η₁) ≤ δ^η₁ ≤ fullness {istar} V`, the latter by cancelling the carrier volume
    exact (Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le (le_mul_of_one_le_left hη₁.le
      one_le_two)).trans (le_fullness_singleton E _ histar_pos histar_shade)
  · -- the multiplicity on `{istar}` is `1`, so this is exactly `hcase` weakened
    rw [multiplicityRLocal_singleton E (fun i ↦ (T i).toShadedBody)
      ((mul_pos (Real.rpow_pos_of_pos hδ η₁) histar_pos).trans_le histar_shade).ne', mul_one]
    rw [div_le_iff₀ hΔ_pos] at hcase
    exact (multiplicityRLocal_le_card E s _).trans (hcase.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le
        (by linarith only [hc_nonpos] : -c ≤ -c / 2)) hΔ_pos.le))

/-- Fullness lower-bound step of `exists_random_subset` (random/large case): given
    the carrier upper bound, shade lower bound (via `Sc`), cardinality bound and
    the smallness assumption `4 K^4 ≤ δ^(-η₁)`, conclude `δ^(2η₁) ≤ fullness s' V`. -/
private lemma exists_random_subset_fullness_step {ι : Type*}
    {s s' : Finset ι} (V : ι → ShadedBody E) {δ η₁ Δ K_unif vstar Sc sum_wc : ℝ}
    (hδ_pos : 0 < δ) (_hη₁ : 0 < η₁) (hΔ_pos : 0 < Δ) (hK_unif_pos : 0 < K_unif)
    (hvstar_pos : 0 < vstar) (hδ_small_full : 4 * K_unif ^ 4 ≤ δ ^ (-η₁))
    (h_card_a' : (s'.card : ℝ) ≤ 2 * (s.card : ℝ) * Δ⁻¹)
    (h_sum_carrier_s'_pos : 0 < ∑ i ∈ s', volume.real (V i).carrier)
    (h_sum_carrier_ub : ∑ i ∈ s', volume.real (V i).carrier
      ≤ K_unif * vstar * (s'.card : ℝ))
    (hSc_eq : Sc = sum_wc / (2 * Δ))
    (h_sum_wc_lb : δ ^ η₁ * (s.card : ℝ) / K_unif ^ 2 ≤ sum_wc)
    (h_shade_via_Sc : (vstar / K_unif) * Sc ≤ ∑ i ∈ s', volume.real (V i).shade) :
        δ ^ (2 * η₁) ≤ ((ShadedBody.fullness s' V : NNReal) : ℝ) := by
  have hδη₁ : (0:ℝ) < δ ^ η₁ := Real.rpow_pos_of_pos hδ_pos _
  have h_main_ineq : 4 * δ ^ η₁ * K_unif ^ 4 ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hδ_small_full hδη₁.le
    rwa [← Real.rpow_add hδ_pos, add_neg_cancel, Real.rpow_zero, ← mul_assoc,
      mul_comm (δ ^ η₁) 4] at hh
  -- clear all denominators in the hypotheses
  rw [← div_eq_mul_inv, le_div_iff₀ hΔ_pos] at h_card_a'
  rw [hSc_eq, div_mul_div_comm,
    div_le_iff₀ (mul_pos hK_unif_pos (mul_pos two_pos hΔ_pos))] at h_shade_via_Sc
  rw [div_le_iff₀ (pow_pos hK_unif_pos 2)] at h_sum_wc_lb
  have hshade : (0:ℝ) ≤ ∑ i ∈ s', volume.real (V i).shade :=
    Finset.sum_nonneg fun _ _ => measureReal_nonneg
  refine le_of_mul_le_mul_right ?_ h_sum_carrier_s'_pos
  rw [← _sum_shade_eq_fullness_mul_sum_carrier E s' V h_sum_carrier_s'_pos, two_mul,
    Real.rpow_add hδ_pos]
  refine le_of_mul_le_mul_right ?_ hΔ_pos
  -- the five bounds below telescope into the goal
  linarith only [mul_le_mul_of_nonneg_left h_sum_carrier_ub
      (mul_nonneg (mul_nonneg hδη₁.le hδη₁.le) hΔ_pos.le),
    mul_le_mul_of_nonneg_left h_card_a'
      (mul_nonneg (mul_nonneg (mul_nonneg hδη₁.le hδη₁.le) hK_unif_pos.le) hvstar_pos.le),
    mul_le_mul_of_nonneg_left h_sum_wc_lb
      (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hδη₁.le) hK_unif_pos.le) hvstar_pos.le),
    mul_le_mul_of_nonneg_left h_shade_via_Sc
      (mul_nonneg (mul_nonneg zero_le_two hδη₁.le) (pow_nonneg hK_unif_pos.le 3)),
    mul_le_mul_of_nonneg_left h_main_ineq (mul_nonneg hΔ_pos.le hshade)]

/-- Multiplicity-bound step of `exists_random_subset` (random/large case): given
    that the shade sum on `s'` is lower-bounded by `(vstar/K) * (Σ wc / (2 Δ))`
    and that `Σ shade on s ≤ K * vstar * Σ wc`, conclude the multiplicity bound. -/
private lemma exists_random_subset_multiplicity_step {ι : Type*}
    {s s' : Finset ι} (V : ι → ShadedBody E) (hs'_sub : s' ⊆ s)
    {δ c Δ K_unif vstar sum_wc : ℝ}
    (hδ_pos : 0 < δ) (hΔ_pos : 0 < Δ) (hK_unif_pos : 0 < K_unif)
    (_hvstar_pos : 0 < vstar) (hδ_small_d : 2 * K_unif ^ 2 ≤ δ ^ (-c))
    (h_sum_shade_s_ub : ∑ i ∈ s, volume.real (V i).shade ≤ (K_unif * vstar) * sum_wc)
    (h_sum_shade_s'_via_wc :
      (vstar / K_unif) * (sum_wc / (2 * Δ)) ≤ ∑ i ∈ s', volume.real (V i).shade) :
    multiplicityRLocal E s V ≤ δ ^ (-c) * Δ * multiplicityRLocal E s' V := by
  refine multiplicity_upper_bound_helper E V hs'_sub hΔ_pos hK_unif_pos hδ_pos hδ_small_d
    (le_trans ?_ h_sum_shade_s'_via_wc)
  rw [div_le_iff₀ (mul_pos (mul_pos two_pos hΔ_pos) (pow_pos hK_unif_pos 2))]
  exact h_sum_shade_s_ub.trans_eq (by
    rw [div_mul_div_comm, div_mul_eq_mul_div,
      eq_div_iff (mul_ne_zero hK_unif_pos.ne' (mul_ne_zero two_ne_zero hΔ_pos.ne'))]
    ring)

-- (extracted by Fuse golfer)
open scoped Classical in
/-- Real-valued form of `densityIn`: the total carrier volume of the members of `s`
contained in `K`, divided by the volume of `K`. -/
private lemma densityIn_toReal_eq {ι : Type u} (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) :
    (densityIn s W K).toReal
      = (∑ i ∈ s with W i ≤ K, volume.real (W i).carrier) / volume.real K.carrier := by
  rw [ENNReal.toReal_div, ENNReal.toReal_sum fun i _ => (W i).isCompact'.measure_lt_top.ne]; rfl

-- Density-bound step of `exists_random_subset` (random/large case): given a test
-- convex body `K` together with the indicator-sum bound `Σ wbK_j * χ_j ω ≤ Aval`,
-- deduce `densityIn (randomSubset s χ ω) W K ≤ Aval`. The hypothesis is stated with
-- `wbK` inlined so that callers can use it directly after `set wbK :=...`.
open scoped Classical in
private lemma exists_random_subset_dens_bound {ι : Type u}
    {s : Finset ι} {Ω : Type*} (χ : Fin s.card → Ω → ℝ) (ω : Ω)
    (hχω_zero_one : ∀ j, χ j ω = 0 ∨ χ j ω = 1)
    (W : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E)
    {Aval : ℝ} (hAval_nn : 0 ≤ Aval)
    (h_sum_le_Aval :
      ∑ j : Fin s.card,
        (if W ((s.equivFin.symm j : ↥s).val) ≤ K ∧ 0 < volume.real K.carrier
          then volume.real (W ((s.equivFin.symm j : ↥s).val)).carrier
                / volume.real K.carrier
          else 0) * χ j ω ≤ Aval) :
    (densityIn (randomSubset s χ ω) W K).toReal ≤ Aval := by
  by_cases hKvol_zero : volume.real K.carrier = 0
  · rwa [densityIn_eq_zero_of_volume_eq_zero
      ((measureReal_eq_zero_iff K.isCompact'.measure_lt_top.ne).1 hKvol_zero), ENNReal.toReal_zero]
  have hKvol_pos : 0 < volume.real K.carrier := ENNReal.toReal_nonneg.lt_of_ne' hKvol_zero
  rw [densityIn_toReal_eq, Finset.sum_filter,
    sum_over_randomSubset s χ ω hχω_zero_one
      (fun i => if W i ≤ K then volume.real (W i).carrier else 0),
    Finset.sum_div]
  refine (Finset.sum_congr rfl fun j _ => ?_).trans_le h_sum_le_Aval
  simp only [and_iff_left hKvol_pos, mul_ite, mul_zero, ite_div, zero_div, mul_div_assoc, mul_comm]

-- (extracted by Fuse golfer)
/-- Lower bound for the total shade/carrier ratio over `s`, from a uniform comparison of
carrier volumes and a lower bound on the total shade. -/
private lemma sum_shade_ratio_lb {ι : Type u} {s : Finset ι} (V : ι → ShadedBody E)
    {istar : ι} (histar_pos : 0 < volume.real (V istar).carrier)
    {K_unif A : ℝ} (hK_unif_pos : 0 < K_unif) (hA : 0 ≤ A)
    (hcarrier_in_s_lb : ∀ i ∈ s,
      volume.real (V istar).carrier / K_unif ≤ volume.real (V i).carrier)
    (hSum_shade_ge : A * (∑ i ∈ s, volume.real (V i).carrier)
      ≤ ∑ i ∈ s, volume.real (V i).shade)
    (hcarrier_ub : ∀ j : Fin s.card,
      volume.real (V ((s.equivFin.symm j : ↥s)).val).carrier
        ≤ K_unif * volume.real (V istar).carrier)
    (hcarrier_pos : ∀ j : Fin s.card,
      0 < volume.real (V ((s.equivFin.symm j : ↥s)).val).carrier)
    {wc : Fin s.card → ℝ}
    (hwc_eq : ∀ j : Fin s.card, wc j =
      volume.real (V ((s.equivFin.symm j : ↥s)).val).shade
        / volume.real (V ((s.equivFin.symm j : ↥s)).val).carrier) :
    A * (s.card : ℝ) / K_unif ^ 2 ≤ ∑ j : Fin s.card, wc j := by
  have h_sum_carrier_s_lb : (s.card : ℝ) * (volume.real (V istar).carrier / K_unif)
      ≤ ∑ i ∈ s, volume.real (V i).carrier :=
    (Finset.card_nsmul_le_sum s _ _ hcarrier_in_s_lb).trans_eq' (nsmul_eq_mul _ _)
  have h_sum_wc_ge_div :
      (∑ i ∈ s, volume.real (V i).shade) / (K_unif * volume.real (V istar).carrier)
        ≤ ∑ j : Fin s.card, wc j := by
    rw [← sum_via_equivFin s (fun i => volume.real (V i).shade), Finset.sum_div]
    exact Finset.sum_le_sum fun j _ =>
      (div_le_div_of_nonneg_left measureReal_nonneg (hcarrier_pos j)
        (hcarrier_ub j)).trans_eq (hwc_eq j).symm
  refine le_trans ?_ h_sum_wc_ge_div
  rw [le_div_iff₀ (mul_pos hK_unif_pos histar_pos)]
  refine le_trans (le_of_eq ?_)
    ((mul_le_mul_of_nonneg_left h_sum_carrier_s_lb hA).trans hSum_shade_ge)
  rw [div_mul_eq_mul_div, sq, ← div_div, mul_comm K_unif (volume.real (V istar).carrier),
    ← mul_assoc, mul_div_cancel_right₀ _ hK_unif_pos.ne']; ring

-- (extracted by Fuse golfer)
/-- If the carrier volumes over `s` agree up to the factor `K_unif`, then every member of `s`
is comparable to a fixed member `istar`, both from below and (after reindexing along
`s.equivFin`) from above. -/
private lemma carrier_bounds_of_unif {ι : Type u} {s : Finset ι} (V : ι → ShadedBody E)
    {istar : ι} (histar_mem : istar ∈ s) {K_unif : ℝ} (hK_unif_pos : 0 < K_unif)
    (hT_unif : ∀ i ∈ s, ∀ j ∈ s,
      volume.real (V i).carrier ≤ K_unif * volume.real (V j).carrier) :
    (∀ i ∈ s, volume.real (V istar).carrier / K_unif ≤ volume.real (V i).carrier) ∧
      ∀ j : Fin s.card, volume.real (V ((s.equivFin.symm j : ↥s)).val).carrier
        ≤ K_unif * volume.real (V istar).carrier :=
  ⟨fun i hi => (div_le_iff₀' hK_unif_pos).2 (hT_unif istar histar_mem i hi),
    fun j => hT_unif _ (s.equivFin.symm j).2 istar histar_mem⟩

-- (extracted by Fuse golfer)
/-- The shade/carrier ratios of `s`, reindexed along `s.equivFin`, are weights in `[0, 1]`
that recover each shade from its carrier and, under a uniform comparison of carrier volumes,
have total mass at least `A * #s / K_unif ^ 2`. -/
private lemma exists_shadeRatioWeights {ι : Type u} {s : Finset ι} (V : ι → ShadedBody E)
    {istar : ι} (histar_pos : 0 < volume.real (V istar).carrier)
    {K_unif A : ℝ} (hK_unif_pos : 0 < K_unif) (hA : 0 ≤ A)
    (hcarrier_in_s_lb : ∀ i ∈ s,
      volume.real (V istar).carrier / K_unif ≤ volume.real (V i).carrier)
    (hSum_shade_ge : A * (∑ i ∈ s, volume.real (V i).carrier)
      ≤ ∑ i ∈ s, volume.real (V i).shade)
    (hcarrier_ub : ∀ j : Fin s.card,
      volume.real (V ((s.equivFin.symm j : ↥s)).val).carrier
        ≤ K_unif * volume.real (V istar).carrier) :
    ∃ wc : Fin s.card → ℝ, (∀ j, 0 ≤ wc j) ∧ (∀ j, wc j ≤ 1) ∧
      A * (s.card : ℝ) / K_unif ^ 2 ≤ ∑ j, wc j ∧
      ∀ j : Fin s.card, volume.real (V ((s.equivFin.symm j : ↥s)).val).shade
        = wc j * volume.real (V ((s.equivFin.symm j : ↥s)).val).carrier := by
  have hpos : ∀ j : Fin s.card, 0 < volume.real (V ((s.equivFin.symm j : ↥s)).val).carrier :=
    fun j => (div_pos histar_pos hK_unif_pos).trans_le (hcarrier_in_s_lb _ (s.equivFin.symm j).2)
  exact ⟨fun j => volume.real (V ((s.equivFin.symm j : ↥s)).val).shade
      / volume.real (V ((s.equivFin.symm j : ↥s)).val).carrier,
    fun _ => div_nonneg measureReal_nonneg measureReal_nonneg,
    fun j => (div_le_one (hpos j)).2
      (measureReal_mono (V _).shade_subset (V _).isCompact'.measure_ne_top),
    sum_shade_ratio_lb E V histar_pos hK_unif_pos hA hcarrier_in_s_lb hSum_shade_ge
      hcarrier_ub hpos fun _ => rfl,
    fun j => (div_mul_cancel₀ _ (hpos j).ne').symm⟩

-- (extracted by Fuse golfer)
/-- The reindexed density weights for a test body `K` sum to at most the maximal density. -/
private lemma sum_densityWeights_le_maxDensity {ι : Type u} (s : Finset ι)
    (W : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E)
    (e : Fin s.card → ι) (he : ∀ j, e j = ((s.equivFin.symm j : ↥s)).val)
    (wbK : Fin s.card → ℝ)
    (hwbK : ∀ j, wbK j = if W (e j) ≤ K ∧ 0 < volume.real K.carrier
      then volume.real (W (e j)).carrier / volume.real K.carrier else 0) :
    ∑ j : Fin s.card, wbK j ≤ (maxDensity s W).toReal := by
  by_cases hKvol : volume.real K.carrier = 0
  · exact (Finset.sum_eq_zero fun j _ => by
      rw [hwbK j, if_neg fun hc => hc.2.ne' hKvol]).trans_le ENNReal.toReal_nonneg
  have hKpos : 0 < volume.real K.carrier := ENNReal.toReal_nonneg.lt_of_ne' hKvol
  refine Eq.trans_le ?_
    (ENNReal.toReal_mono (maxDensity_ne_top s W) (le_maxDensity s W K))
  rw [densityIn_toReal_eq, Finset.sum_filter,
    ← sum_via_equivFin s fun i => if W i ≤ K then volume.real (W i).carrier else 0,
    Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by
    simp only [hwbK j, he j, and_iff_left hKpos, ite_div, zero_div]

-- (extracted by Fuse golfer)
/-- The density weights of `s` against a test body `K`, reindexed along `s.equivFin`: they
take values in `[0, 1]` and their total mass is at most the maximal density of `s`. -/
private lemma exists_densityWeights {ι : Type u} (s : Finset ι) (W : ι → ConvexSpaceBody E) :
    ∃ w : ConvexSpaceBody E → Fin s.card → ℝ,
      (∀ K j, 0 ≤ w K j) ∧ (∀ K j, w K j ≤ 1) ∧
      (∀ K, ∑ j, w K j ≤ (maxDensity s W).toReal) ∧
      ∀ K j, w K j = if W ((s.equivFin.symm j : ↥s)).val ≤ K ∧ 0 < volume.real K.carrier
        then volume.real (W ((s.equivFin.symm j : ↥s)).val).carrier / volume.real K.carrier
        else 0 := by
  obtain ⟨w, hw⟩ : ∃ w : ConvexSpaceBody E → Fin s.card → ℝ, ∀ K j, w K j =
      if W ((s.equivFin.symm j : ↥s)).val ≤ K ∧ 0 < volume.real K.carrier
      then volume.real (W ((s.equivFin.symm j : ↥s)).val).carrier / volume.real K.carrier
      else 0 := ⟨_, fun _ _ => rfl⟩
  have h01 : ∀ K j, 0 ≤ w K j ∧ w K j ≤ 1 := fun K j => by
    rw [hw]; split_ifs with h
    exacts [⟨div_nonneg measureReal_nonneg measureReal_nonneg,
      (div_le_one h.2).2 (measureReal_mono h.1 K.isCompact'.measure_ne_top)⟩, ⟨le_rfl, zero_le_one⟩]
  exact ⟨w, fun K j => (h01 K j).1, fun K j => (h01 K j).2,
    fun K => sum_densityWeights_le_maxDensity E s W K _ (fun _ => rfl) (w K) (hw K), hw⟩

/-- An exponential smallness bound `exp (-a / k) ≤ 1/5` transfers to any larger `b ≥ a`. -/
private lemma exp_neg_div_le_one_fifth {a b k : ℝ} (hk : (0 : ℝ) ≤ k) (hab : a ≤ b)
    (h : Real.exp (-a / k) ≤ 1 / 5) : Real.exp (-b / k) ≤ 1 / 5 := -- (extracted by Fuse golfer)
  (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith only [hab]) hk)).trans h

/-- The Chernoff exponent at a deviation equal to half the threshold: if `y = 2 * x` then
`-(y - x)² / (2 * y)` collapses to `-x / 4` (also valid in the degenerate case `x = 0`). -/
private lemma neg_sq_sub_div_two_mul {x y : ℝ} (h : y = 2 * x) :
    -(y - x) ^ 2 / (2 * y) = -x / 4 := by -- (extracted by Fuse golfer)
  rw [h, show 2 * x - x = x by ring, show (2 : ℝ) * (2 * x) = x * 4 by ring, neg_div, neg_div,
    div_mul_eq_div_div, sq, mul_self_div_self]

/-- If `C ≤ δ ^ (-M)` then the Chernoff bound `C * exp (-A / 8)` at the threshold
`A = (8 M + 8) * log (1 / δ)` is at most `δ`. -/
private lemma mul_exp_neg_log_div_eight_le {C M δ : ℝ} (hδ : 0 < δ) (hC : C ≤ δ ^ (-M)) :
    C * Real.exp (-((8 * M + 8) * Real.log (1 / δ)) / 8) ≤ δ := by
  -- (extracted by Fuse golfer)
  rw [show -((8 * M + 8) * Real.log (1 / δ)) / 8 = Real.log δ * (M + 1) by
    rw [one_div, Real.log_inv]; ring, ← Real.rpow_def_of_pos hδ]
  exact (mul_le_mul_of_nonneg_right hC (Real.rpow_pos_of_pos hδ _).le).trans_eq
    (by rw [← Real.rpow_add hδ]; norm_num)

-- (extracted by Fuse golfer)
/-- Combinatorial core of the random/large case of `exists_random_subset`: a single
Bernoulli(`1/Δ`) sample of `Fin N` simultaneously selects at most `Sa` indices, selects at
least one index, has `wc`-weighted sum at least `Sc`, and has `wb`-weighted sum at most
`Aval` against every member of the test family `KTest`.

The four bad events each have probability at most `1/5`, so their union is not everything. -/
private lemma exists_good_sample {N : ℕ} [NeZero N] {α : Type*} (KTest : Finset α)
    (wc : Fin N → ℝ) (wb : α → Fin N → ℝ)
    {p Δ δ c η₁ K_unif Mtest Aval Sa Sc : ℝ}
    (hp_def : p = 1 / Δ) (hΔ_ge_one : 1 ≤ Δ) (hΔ_le_card : Δ ≤ (N : ℝ))
    (hwc0 : ∀ j, 0 ≤ wc j) (hwc1 : ∀ j, wc j ≤ 1)
    (hwb0 : ∀ K j, 0 ≤ wb K j) (hwb1 : ∀ K j, wb K j ≤ 1)
    (hwb_sum : ∀ K ∈ KTest, ∑ j, wb K j ≤ Δ)
    (hδ_pos : 0 < δ) (hK_unif_pos : 0 < K_unif)
    (hSa_def : Sa = 2 * (N : ℝ) / Δ) (hSc_def : Sc = p * (∑ j, wc j) / 2)
    (hAval_def : Aval = (8 * Mtest + 8) * Real.log (1 / δ))
    (hKTest_card : (KTest.card : ℝ) ≤ δ ^ (-Mtest))
    (h_sum_wc_lb : δ ^ η₁ * (N : ℝ) / K_unif ^ 2 ≤ ∑ j, wc j)
    (hδ5_empty : Real.exp (-δ ^ (-c / 2) / 8) ≤ 1 / 5)
    (hδ5_two : 2 ≤ δ ^ (-c / 2))
    (hδ5_a : Real.exp (-δ ^ (-c / 2) / 4) ≤ 1 / 5)
    (hδ5_c : Real.exp (-δ ^ (η₁ - c / 2) / (8 * K_unif ^ 2)) ≤ 1 / 5)
    (hδ5_b : δ ≤ 1 / 5) (hδ5_aval : 2 ≤ Aval)
    (hcase : δ ^ (-c / 2) < (N : ℝ) / Δ) :
    ∃ ω : Fin N → Bool,
      ∑ i, Probability.Bernoulli.bernoulliIndicator N i ω ≤ Sa ∧
      1 ≤ ∑ i, Probability.Bernoulli.bernoulliIndicator N i ω ∧
      Sc ≤ ∑ j, wc j * Probability.Bernoulli.bernoulliIndicator N j ω ∧
      ∀ K ∈ KTest, ∑ j, wb K j * Probability.Bernoulli.bernoulliIndicator N j ω ≤ Aval := by
  have hΔ_pos : 0 < Δ := zero_lt_one.trans_le hΔ_ge_one
  have hN_div_Δ_pos : 0 < (N : ℝ) / Δ := div_pos (Nat.cast_pos.mpr (NeZero.pos N)) hΔ_pos
  have hp0 : 0 ≤ p := (div_pos zero_lt_one hΔ_pos).le.trans hp_def.ge
  have hp1 : p ≤ 1 := hp_def.le.trans ((div_le_one hΔ_pos).mpr hΔ_ge_one)
  haveI : Fact (0 ≤ p) := ⟨hp0⟩; haveI : Fact (p ≤ 1) := ⟨hp1⟩
  have hpN : p * (N : ℝ) = (N : ℝ) / Δ := by rw [hp_def, one_div, inv_mul_eq_div]
  let P : Measure (Fin N → Bool) := Probability.Bernoulli.bernoulliPi N p
  let χ : Fin N → (Fin N → Bool) → ℝ := Probability.Bernoulli.bernoulliIndicator N
  let E_a : Set (Fin N → Bool) := {ω | ∑ i, χ i ω > Sa}
  let E_empty : Set (Fin N → Bool) := {ω | ∑ i, χ i ω < 1}
  let E_c : Set (Fin N → Bool) := {ω | (∑ j, wc j * χ j ω) < Sc}
  let E_b_K : α → Set (Fin N → Bool) := fun K => {ω | Aval < ∑ j, wb K j * χ j ω}
  let E_b : Set (Fin N → Bool) := ⋃ K ∈ KTest, E_b_K K
  -- Each of the four bad events has probability at most `1/5`.
  have hPa : (P E_a).toReal ≤ 1/5 := by
    have hSa_eq : Sa = 2 * ((N : ℝ) / Δ) := by rw [hSa_def, mul_div_assoc]
    refine (chernoff_count_upper (N := N) hp0 hp1 (S := Sa)
      (by rw [hpN, hSa_eq]; exact le_mul_of_one_le_left hN_div_Δ_pos.le one_le_two)).trans ?_
    rw [hpN, neg_sq_sub_div_two_mul hSa_eq]
    exact exp_neg_div_le_one_fifth (Nat.ofNat_nonneg 4) hcase.le hδ5_a
  have hPempty : (P E_empty).toReal ≤ 1/5 := by
    refine (chernoff_count_lower (N := N) hp0 hp1 (S := 1) zero_le_one
      (by rw [hpN]; exact (one_le_div hΔ_pos).mpr hΔ_le_card)).trans ?_
    rw [hpN]
    exact (exp_le_exp.mpr (exists_random_subset_aux1 _ hN_div_Δ_pos (hδ5_two.trans hcase.le))).trans
      (exp_neg_div_le_one_fifth (Nat.ofNat_nonneg 8) hcase.le hδ5_empty)
  have hPc : (P E_c).toReal ≤ 1/5 := by
    have hSc0 : 0 ≤ Sc := hSc_def ▸ div_nonneg
      (mul_nonneg hp0 (Finset.sum_nonneg fun j _ => hwc0 j)) zero_le_two
    have hμc2 : p * ∑ j, wc j = 2 * Sc := by rw [hSc_def, two_mul, add_halves]
    have hμc_lb : δ ^ (η₁ - c/2) / K_unif ^ 2 ≤ p * ∑ j, wc j := by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left h_sum_wc_lb hp0)
      rw [← mul_div_assoc, mul_left_comm, hpN, show η₁ - c/2 = η₁ + -c/2 by ring, rpow_add hδ_pos]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcase.le
        (rpow_pos_of_pos hδ_pos _).le) (pow_pos hK_unif_pos 2).le
    refine (Probability.chernoff_bernoulli_weighted_lower N p hp0 hp1 wc hwc0 hwc1 Sc hSc0
      ((le_mul_of_one_le_left hSc0 one_le_two).trans_eq hμc2.symm)).trans
      ((exp_le_exp.mpr ?_).trans hδ5_c)
    rw [neg_sq_sub_div_two_mul hμc2, neg_div, neg_div, mul_comm (8:ℝ) (K_unif ^ 2), ← div_div]
    exact neg_le_neg ((div_le_div_of_nonneg_right (hμc_lb.trans_eq hμc2)
      (Nat.ofNat_nonneg 8)).trans_eq (by ring))
  have hPb : (P E_b).toReal ≤ 1/5 := by
    have hsum1 : ∀ K ∈ KTest, p * ∑ j, wb K j ≤ 1 := fun K hK => by
      rw [hp_def, div_mul_eq_mul_div, one_mul, div_le_one hΔ_pos]; exact hwb_sum K hK
    refine (measureReal_biUnion_finset_le (μ := P) KTest E_b_K).trans
      ((Finset.sum_le_sum (g := fun _ => Real.exp (-Aval / 8)) fun K hK =>
        (Probability.chernoff_bernoulli_weighted_upper N p hp0 hp1 (wb K) (hwb0 K) (hwb1 K)
          Aval ((hsum1 K hK).trans (one_le_two.trans hδ5_aval))).trans (exp_le_exp.mpr
          (exists_random_subset_aux2 Aval (p * ∑ j, wb K j) hδ5_aval
            (mul_nonneg hp0 (Finset.sum_nonneg fun j _ => hwb0 K j)) (hsum1 K hK)))).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul, hAval_def]
    exact (mul_exp_neg_log_div_eight_le hδ_pos hKTest_card).trans hδ5_b
  obtain ⟨ω, hω⟩ := Probability.exists_compl_iUnion P
    (![E_a, E_empty, E_c, E_b] : Fin 4 → Set (Fin N → Bool)) (fun _ => MeasurableSet.of_discrete)
    (by rw [Fin.sum_univ_four]
        exact (add_le_add (add_le_add (add_le_add hPa hPempty) hPc) hPb).trans_lt (by norm_num))
  exact ⟨ω, not_lt.mp (hω 0), not_lt.mp (hω 1), not_lt.mp (hω 2),
    fun K hK => not_lt.mp fun hcontra => hω 3 (Set.mem_biUnion hK hcontra)⟩

/-- Random/large case of `exists_random_subset`: Bernoulli sampling simultaneously
controls cardinality, emptiness, fullness, Katz-Tao density, and multiplicity. -/
private lemma exists_random_subset_large_case {δ : NNReal} {η₁ c : ℝ}
    (hη₁ : 0 < η₁) {ι : Type u} (s : Finset ι) (hs : s.Nonempty)
    (W : ι → ConvexSpaceBody E) (V : ι → ShadedBody E)
    (hWV : ∀ i, (W i).carrier = (V i).carrier)
    (Δ : ℝ) (hΔ_def : Δ = (maxDensity s W).toReal)
    (hΔ_ne_top : maxDensity s W ≠ ⊤)
    (hSum_shade_ge : (δ : ℝ) ^ η₁ * (∑ i ∈ s, volume.real (V i).carrier) ≤
      ∑ i ∈ s, volume.real (V i).shade)
    (istar : ι) (histar_mem : istar ∈ s) (histar_pos : 0 < volume.real (V istar).carrier)
    (hδR : 0 < (δ : ℝ)) (_hδ1 : (δ : ℝ) < 1)
    (K_unif : ℝ) (hK_unif_pos : 0 < K_unif)
    (hT_unif : ∀ i ∈ s, ∀ j ∈ s,
      volume.real (V i).carrier ≤ K_unif * volume.real (V j).carrier)
    (hδ_small_full : 4 * K_unif ^ 4 ≤ (δ : ℝ) ^ (-η₁))
    (hδ_small_d : 2 * K_unif ^ 2 ≤ (δ : ℝ) ^ (-c))
    (hδ5_empty : Real.exp (-(δ : ℝ) ^ (-c / 2) / 8) ≤ 1 / 5)
    (hδ5_two : 2 ≤ (δ : ℝ) ^ (-c / 2))
    (hδ5_a : Real.exp (-(δ : ℝ) ^ (-c / 2) / 4) ≤ 1 / 5)
    (Mtest Ctest : ℝ) (_hMtest_pos : 0 < Mtest) (hCtest_pos : 0 < Ctest)
    (htest_family : ∃ KTest : Finset (ConvexSpaceBody E),
      (∀ K ∈ KTest,
        K ≤ ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E))) ∧
      (KTest.card : ℝ) ≤ (δ : ℝ) ^ (-Mtest) ∧ ∀ u : Finset ι, u ⊆ s →
      ∃ K ∈ KTest, (maxDensity u W).toReal ≤ Ctest * (densityIn u W K).toReal)
    (hδ_small_b : Ctest * ((8 * Mtest + 8) * Real.log (1 / (δ : ℝ))) ≤
      (δ : ℝ) ^ (-c))
    (hδ5_c : Real.exp (-(δ : ℝ) ^ (η₁ - c / 2) / (8 * K_unif ^ 2)) ≤ 1 / 5)
    (hδ5_b : (δ : ℝ) ≤ 1 / 5)
    (hδ5_aval : 2 ≤ (8 * Mtest + 8) * Real.log (1 / (δ : ℝ)))
    (hcase : (δ : ℝ) ^ (-c / 2) < (s.card : ℝ) / Δ) :
    ∃ s' ⊆ s, s'.Nonempty ∧
      (s'.card : ℝ) ≤ 2 * (s.card : ℝ) * Δ⁻¹ ∧
      ConvexSpaceBody.IsKatzTao s' W (ENNReal.ofReal ((δ : ℝ) ^ (-c))) ∧
      ((ShadedBody.fullness s' V : NNReal) : ℝ) ≥ (δ : ℝ) ^ (2 * η₁) ∧
      multiplicityRLocal E s V ≤ (δ : ℝ) ^ (-c) * Δ * multiplicityRLocal E s' V := by
  have hΔ_ge_one : 1 ≤ Δ := by
    rw [hΔ_def, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hΔ_ne_top (one_le_maxDensity ⟨istar, histar_mem,
      by rw [hWV istar]; exact (ENNReal.toReal_pos_iff.1 histar_pos).1⟩)
  have hΔ_pos : 0 < Δ := zero_lt_one.trans_le hΔ_ge_one
  haveI : NeZero s.card := ⟨(Finset.card_pos.mpr hs).ne'⟩
  obtain ⟨hcarrier_in_s_lb_pre, hcarrier_ub_pre⟩ :=
    carrier_bounds_of_unif E V histar_mem hK_unif_pos hT_unif
  obtain ⟨wc, hwc0, hwc1, h_sum_wc_lb_pre, h_shade_eq_wc⟩ :=
    exists_shadeRatioWeights E V histar_pos hK_unif_pos (Real.rpow_nonneg hδR.le _)
      hcarrier_in_s_lb_pre hSum_shade_ge hcarrier_ub_pre
  obtain ⟨KTest, _, hKTest_card, hKTest_dense⟩ := htest_family
  obtain ⟨wbK, hwbK0, hwbK1, hwbK_sum, hwbK_def⟩ := exists_densityWeights E s W
  obtain ⟨ω, hω_a, hω_empty, hω_c, hω_b⟩ :=
    exists_good_sample (Sc := (∑ j, wc j) / (2 * Δ)) KTest wc wbK rfl hΔ_ge_one
      (hΔ_def.trans_le (maxDensity_toReal_le_card E s W))
      hwc0 hwc1 hwbK0 hwbK1 (fun K _ => (hwbK_sum K).trans_eq hΔ_def.symm)
      hδR hK_unif_pos rfl (by ring) rfl hKTest_card
      h_sum_wc_lb_pre hδ5_empty hδ5_two hδ5_a hδ5_c hδ5_b hδ5_aval hcase
  obtain ⟨χ, hχ_def⟩ : ∃ f : Fin s.card → (Fin s.card → Bool) → ℝ,
      f = Probability.Bernoulli.bernoulliIndicator s.card := ⟨_, rfl⟩
  rw [← hχ_def] at hω_a hω_empty hω_c hω_b
  have hχ_nn : ∀ j, 0 ≤ χ j ω :=
    hχ_def ▸ fun j => Probability.Bernoulli.bernoulliIndicator_nonneg s.card j ω
  have hχω_zero_one : ∀ j, χ j ω = 0 ∨ χ j ω = 1 := fun j => by
    rw [hχ_def, Probability.Bernoulli.bernoulliIndicator_apply]
    exact (ite_eq_or_eq _ _ _).symm
  obtain ⟨s', hs'_def⟩ : ∃ t : Finset ι, t = randomSubset s χ ω := ⟨_, rfl⟩
  have hs'_sub : s' ⊆ s := hs'_def ▸ randomSubset_subset s χ ω
  have hs'_card_eq : (s'.card : ℝ) = ∑ i, χ i ω :=
    hs'_def ▸ randomSubset_card_eq_sum s χ ω hχω_zero_one
  have h_card_a' : (s'.card : ℝ) ≤ 2 * (s.card : ℝ) * Δ⁻¹ :=
    (hs'_card_eq.trans_le hω_a).trans_eq (div_eq_mul_inv _ _)
  have hs'_nonempty : s'.Nonempty :=
    Finset.card_pos.mp (Nat.one_le_cast.mp (hω_empty.trans hs'_card_eq.ge))
  -- The `wc`-weighted shade bound feeding both the fullness and the multiplicity step.
  have h_shade_via_wc : volume.real (V istar).carrier / K_unif * ((∑ j, wc j) / (2 * Δ))
      ≤ ∑ i ∈ s', volume.real (V i).shade := by
    rw [hs'_def]
    refine le_sum_over_randomSubset s χ ω hχ_nn hχω_zero_one
      (div_nonneg histar_pos.le hK_unif_pos.le) (fun j => ?_) hω_c
    rw [h_shade_eq_wc j, mul_comm]
    exact mul_le_mul_of_nonneg_left (hcarrier_in_s_lb_pre _ (s.equivFin.symm j).2) (hwc0 j)
  refine ⟨s', hs'_sub, hs'_nonempty, h_card_a', ?_, ?_, ?_⟩
  · -- IsKatzTao s' W (ENNReal.ofReal (δ^(-c)))
    obtain ⟨K, hK_mem, hK_dense⟩ := hKTest_dense s' hs'_sub
    refine (ENNReal.ofReal_toReal (maxDensity_ne_top s' W)).ge.trans
      (ENNReal.ofReal_le_ofReal (hK_dense.trans
        ((mul_le_mul_of_nonneg_left ?_ hCtest_pos.le).trans hδ_small_b)))
    rw [hs'_def]
    exact exists_random_subset_dens_bound E χ ω hχω_zero_one W K (zero_le_two.trans hδ5_aval)
      ((Finset.sum_congr rfl fun j _ => by rw [hwbK_def]).trans_le (hω_b K hK_mem))
  · -- δ^(2η₁) ≤ fullness s' V (as ℝ via NNReal)
    refine exists_random_subset_fullness_step E V hδR hη₁ hΔ_pos hK_unif_pos
      histar_pos hδ_small_full h_card_a'
      (Finset.sum_pos (fun i hi => (div_pos histar_pos hK_unif_pos).trans_le
        (hcarrier_in_s_lb_pre i (hs'_sub hi))) hs'_nonempty) ?_ rfl h_sum_wc_lb_pre h_shade_via_wc
    rw [hs'_card_eq, hs'_def]
    exact sum_over_randomSubset_le s χ ω hχ_nn hχω_zero_one hcarrier_ub_pre
  · -- multiplicityRLocal E s V ≤ δ^(-c) * Δ * multiplicityRLocal E s' V
    refine exists_random_subset_multiplicity_step E V hs'_sub hδR hΔ_pos hK_unif_pos
      histar_pos hδ_small_d ?_ h_shade_via_wc
    rw [← sum_via_equivFin s (fun i => volume.real (V i).shade), Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => (h_shade_eq_wc j).trans_le
      ((mul_le_mul_of_nonneg_left (hcarrier_ub_pre j) (hwc0 j)).trans_eq (mul_comm _ _))

private lemma one_le_log_five : (1 : ℝ) ≤ Real.log 5 := -- (extracted by Fuse golfer)
  (Real.le_log_iff_exp_le (by norm_num)).2 (Real.exp_one_lt_d9.trans (by norm_num)).le

/-- If `4 K^4 ≤ δ^(-η)` with `1 ≤ K` and `0 < η`, then `δ < 1`. -/
private lemma lt_one_of_four_K4_le_rpow_neg {δ K η : ℝ} (hK : 1 ≤ K) (hη : 0 < η)
    (h : 4 * K ^ 4 ≤ δ ^ (-η)) : δ < 1 := by -- (extracted by Fuse golfer)
  by_contra! hge
  linarith only [h, (one_le_pow₀ hK : (1:ℝ) ≤ K ^ 4),
    Real.rpow_le_one_of_one_le_of_nonpos hge (neg_nonpos.mpr hη.le)]

/-- The exponential decay bound `exp (-x/8) ≤ 1/5` forces `x` to be at least `2`. -/
private lemma two_le_of_exp_neg_div_eight_le {x : ℝ} (h : Real.exp (-x / 8) ≤ 1 / 5) :
    2 ≤ x := by -- (extracted by Fuse golfer)
  -- `-x/8 + 1 ≤ exp (-x/8) ≤ 1/5` already forces `x ≥ 32/5`.
  linarith only [(Real.add_one_le_exp (-x / 8)).trans h]

/-- For `0 < d ≤ 1/5` and `0 < M` one has `2 ≤ (8M + 8) * log (1/d)`. -/
private lemma two_le_mul_log_one_div {M d : ℝ} (hM : 0 < M) (hd : 0 < d) (hd5 : d ≤ 1 / 5) :
    2 ≤ (8 * M + 8) * Real.log (1 / d) := by -- (extracted by Fuse golfer)
  have h1 : (1 : ℝ) ≤ Real.log (1 / d) := one_le_log_five.trans
    (Real.log_le_log (by norm_num) ((le_div_iff₀ hd).2 (by linarith only [hd5])))
  exact le_trans (by linarith only [hM]) (le_mul_of_one_le_right (by linarith only [hM]) h1)

/-- A family whose fullness is positive has carriers of positive total volume. -/
private lemma sum_carrier_pos_of_fullness_pos {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E)
    {f : ℝ} (hf : 0 < f) (hfull : f ≤ ((ShadedBody.fullness s V : NNReal) : ℝ)) :
    0 < ∑ i ∈ s, volume.real (V i).carrier := by -- (extracted by Fuse golfer)
  by_contra! hzero
  -- Each carrier has measure `0`, hence so does each shade, hence the fullness is `0`.
  have hshade : ∑ i ∈ s, volume (V i).shade = 0 :=
    Finset.sum_eq_zero fun i hi => MeasureTheory.measure_mono_null (V i).shade_subset
      ((measureReal_eq_zero_iff (V i).isCompact'.measure_ne_top).1 (le_antisymm
        ((Finset.single_le_sum (f := fun j => volume.real (V j).carrier)
          (fun j _ => measureReal_nonneg) hi).trans hzero) measureReal_nonneg))
  exact absurd hfull (not_le.2 (by simpa only [ShadedBody.fullness, ShadedBody.fullness', hshade,
    ENNReal.zero_div, ENNReal.toNNReal_zero, NNReal.coe_zero] using hf))

/-- Pigeonhole for shadings: if the shades of `s` fill an `f`-fraction of the carriers on
average, then some member with positive carrier volume does so individually. -/
private lemma exists_shade_ge_mul_carrier {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E)
    {f : ℝ} (hsum : f * (∑ i ∈ s, volume.real (V i).carrier)
      ≤ ∑ i ∈ s, volume.real (V i).shade)
    (hpos : 0 < ∑ i ∈ s, volume.real (V i).carrier) :
    ∃ i ∈ s, 0 < volume.real (V i).carrier ∧
      f * volume.real (V i).carrier ≤ volume.real (V i).shade := by
  obtain ⟨istar, hmem, hstar⟩ : ∃ i ∈ s, 0 < volume.real (V i).carrier :=
    Finset.exists_lt_of_sum_lt (by rwa [Finset.sum_const_zero]) -- (extracted by Fuse golfer)
  by_contra! hno
  refine absurd hsum (not_le.2 ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_lt_sum (fun i hi => ?_) ⟨istar, hmem, hno istar hmem hstar⟩
  rcases (measureReal_nonneg : (0 : ℝ) ≤ volume.real (V i).carrier).eq_or_lt with heq | hlt
  · rw [← heq, mul_zero]
    exact (measureReal_mono (V i).shade_subset (V i).isCompact'.measure_ne_top).trans heq.ge
  · exact (hno i hi hlt).le

/-- The random subset used in the proof of Lemma 3.7.
TODO: get rid of use of `volume.real` and other `.toReal`
-/
theorem exists_random_subset {δ : NNReal} {η₁ c : ℝ} (hη₁ : 0 < η₁)
    (h : η₁ < c / 2) {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E)
    (_hB : ∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) (hs : s.Nonempty)
    (hδ : 0 < (δ : ℝ))
    (K_unif : ℝ) (hK_unif_pos : 0 < K_unif)
    (hT_unif : ∀ i ∈ s, ∀ j ∈ s,
       volume.real (T i).carrier ≤ K_unif * volume.real (T j).carrier)
    (hδ_small_full : 4 * K_unif ^ 4 ≤ (δ : ℝ) ^ (-η₁))
    (Mtest Ctest : ℝ) (hMtest_pos : 0 < Mtest) (hCtest_pos : 0 < Ctest)
    (htest_family : ∃ KTest : Finset (ConvexSpaceBody E),
        (∀ K ∈ KTest, K ≤ ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E))) ∧
        (KTest.card : ℝ) ≤ (δ : ℝ) ^ (-Mtest) ∧ ∀ u : Finset ι, u ⊆ s →
        ∃ K ∈ KTest, (maxDensity u (fun i ↦ (T i).toConvexSpaceBody)).toReal ≤
        Ctest * (densityIn u (fun i ↦ (T i).toConvexSpaceBody) K).toReal)
    (hδ_small_b : Ctest * ((8 * Mtest + 8) * Real.log (1/(δ : ℝ))) ≤ (δ : ℝ) ^ (-c))
    (hδ5_c : Real.exp (- (δ : ℝ) ^ (η₁ - c/2) / (8 * K_unif ^ 2)) ≤ 1/5)
    (hδ5_b : (δ : ℝ) ≤ 1/5)
    (hfull : ((ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) : NNReal) : ℝ)
      ≥ (δ : ℝ) ^ η₁) :
    ∃ s' ⊆ s, s'.Nonempty ∧
      (s'.card : ℝ) ≤ 2 * (s.card : ℝ) *
        ((maxDensity s (fun i ↦ (T i).toConvexSpaceBody)).toReal)⁻¹ ∧
      ConvexSpaceBody.IsKatzTao s' (fun i ↦ (T i).toConvexSpaceBody)
        (ENNReal.ofReal ((δ : ℝ) ^ (-c))) ∧
      ((ShadedBody.fullness s' (fun i ↦ (T i).toShadedBody) : NNReal) : ℝ)
        ≥ (δ : ℝ) ^ (2 * η₁) ∧
      multiplicityRLocal E s (fun i ↦ (T i).toShadedBody) ≤ (δ : ℝ) ^ (-c) *
        (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)).toReal *
        multiplicityRLocal E s' (fun i ↦ (T i).toShadedBody) := by
  -- NB: no `set` for the abbreviations `W`, `V`, `Δ`: abstracting them in this large
  -- context costs over a million heartbeats.
  have hSum_carrier_pos : 0 < ∑ i ∈ s, volume.real (T i).toShadedBody.carrier :=
    sum_carrier_pos_of_fullness_pos E s _ (Real.rpow_pos_of_pos hδ η₁) hfull
  have hSum_shade_ge :
      (δ : ℝ) ^ η₁ * (∑ i ∈ s, volume.real (T i).toShadedBody.carrier)
        ≤ ∑ i ∈ s, volume.real (T i).toShadedBody.shade :=
    (mul_le_mul_of_nonneg_right hfull hSum_carrier_pos.le).trans_eq
      (_sum_shade_eq_fullness_mul_sum_carrier E s _ hSum_carrier_pos).symm
  obtain ⟨istar, histar_mem, histar_pos, histar_shade⟩ :=
    exists_shade_ge_mul_carrier E s _ hSum_shade_ge hSum_carrier_pos
  have hK_unif_ge_one : (1 : ℝ) ≤ K_unif :=
    le_of_mul_le_mul_right ((one_mul _).trans_le
      (hT_unif istar histar_mem istar histar_mem)) histar_pos
  have hδ1 : (δ : ℝ) < 1 := lt_one_of_four_K4_le_rpow_neg hK_unif_ge_one hη₁ hδ_small_full
  have hδ5_empty : Real.exp (- (δ : ℝ) ^ (-c/2) / 8) ≤ 1/5 :=
    exp_neg_rpow_le_of_shift hδ hδ1 hK_unif_ge_one hη₁ hδ5_c
  rcases le_or_gt ((s.card : ℝ) / (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)).toReal)
      ((δ : ℝ) ^ (-c/2)) with hcase | hcase
  · exact exists_random_subset_small_case E hη₁ h s T hδ hδ1
      istar histar_mem histar_pos histar_shade hcase
  · exact exists_random_subset_large_case E hη₁ s hs (fun i ↦ (T i).toConvexSpaceBody)
      (fun i ↦ (T i).toShadedBody) (fun _ => rfl) _ rfl (maxDensity_ne_top s _)
      hSum_shade_ge istar histar_mem histar_pos hδ hδ1
      K_unif hK_unif_pos hT_unif hδ_small_full
      (two_K2_le_rpow_neg_of_four_K4 hδ hδ1 hK_unif_ge_one hη₁ h hδ_small_full) hδ5_empty
      (two_le_of_exp_neg_div_eight_le hδ5_empty)
      ((Real.exp_le_exp.mpr (by linarith only [Real.rpow_pos_of_pos hδ (-c / 2)])).trans hδ5_empty)
      Mtest Ctest hMtest_pos hCtest_pos
      htest_family hδ_small_b hδ5_c hδ5_b
      (two_le_mul_log_one_div hMtest_pos hδ hδ5_b) hcase

end KatzTaoExistsRandomSubset

end Kakeya
