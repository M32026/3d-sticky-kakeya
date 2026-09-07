module

/-
# Restriction Frostman Lemma

Extracts a Frostman measure from a probability measure with bounded regularized
energy via Markov restriction. Also provides the pushforward energy comparison
between 1D regularized energy and regularized projected energy.
-/

public import MyLeanRepo.robust_kaufman_projection.EnergyAveraging
public import MyLeanRepo.robust_kaufman_projection.EnergyToDeltaSet.Kernel
public import MyLeanRepo.robust_kaufman_projection.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Metric Set Finset Classical

namespace RobustKaufmanProjection.RestrictionFrostman

noncomputable section

/-! ### Uniform measure -/

def uniformMeasure {X : Type*} [MeasurableSpace X] (S : Finset X) : Measure X :=
  (S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set X)

lemma lintegral_count_restrict_finset {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (S : Finset X) (f : X → ENNReal) :
    ∫⁻ x, f x ∂(Measure.count.restrict (S : Set X)) = ∑ x ∈ S, f x := by
  have h_eq : Measure.count.restrict (S : Set X) =
      Finset.sum S (fun x => Measure.dirac x) := by
    ext A hA
    have h1 : Measure.count.restrict (S : Set X) A = Measure.count (A ∩ (S : Set X)) := by
      rw [Measure.restrict_apply hA]
    have h2 : (Finset.sum S (fun x => Measure.dirac x)) A = ∑ x ∈ S, (Measure.dirac x) A := by
      exact Measure.finsetSum_apply S Measure.dirac A
    have h4 : MeasurableSet (A ∩ (S : Set X)) := hA.inter (Finset.measurableSet S)
    have h5 : Measure.count (A ∩ (S : Set X)) = ↑(S.filter (fun x => x ∈ A)).card := by
      rw [Measure.count_apply h4]
      have h6 : (A ∩ (S : Set X)) = (S.filter (fun x => x ∈ A) : Set X) := by
        ext y; simp [Finset.mem_filter] <;> tauto
      rw [h6]
      exact_mod_cast Set.encard_coe_eq_coe_finsetCard (S.filter (fun x => x ∈ A))
    have h7 : ∑ x ∈ S, (Measure.dirac x) A = ↑(S.filter (fun x => x ∈ A)).card := by
      have h8 : ∀ x ∈ S, (Measure.dirac x) A = if x ∈ A then (1 : ENNReal) else 0 := by
        intro x _
        simp [Measure.dirac_apply, Set.indicator_apply]
        <;> split_ifs <;> simp_all
      rw [Finset.sum_congr rfl h8]
      simp [Finset.sum_ite]
      <;> norm_cast
    rw [h1, h5]
    exact h7.symm.trans h2.symm
  rw [h_eq]
  have h_ind : ∀ (T : Finset X), ∫⁻ x, f x ∂(Finset.sum T (fun x => Measure.dirac x)) =
      ∑ x ∈ T, f x := by
    intro T
    induction T using Finset.induction with
    | empty => simp
    | @insert x T hx ih =>
      rw [Finset.sum_insert hx, lintegral_add_measure, ih, lintegral_dirac, Finset.sum_insert hx] <;> ring
  exact h_ind S

lemma lintegral_uniformMeasure {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (S : Finset X) (f : X → ENNReal) :
    ∫⁻ x, f x ∂(uniformMeasure S) = (S.card : ENNReal)⁻¹ * ∑ x ∈ S, f x := by
  rw [uniformMeasure, lintegral_smul_measure, lintegral_count_restrict_finset, smul_eq_mul]

/-! ### Measurability of kernels -/

lemma regularizedKernel_measurable {s δ : ℝ} (hδ : 0 < δ) :
    Measurable (fun d : ℝ => EnergyToDeltaSet.regularizedKernel s δ d) := by
  have h1 : Continuous (fun d : ℝ => (max |d| δ) ^ (-s)) := by
    have h_pos : ∀ (x : ℝ), 0 < max |x| δ := by intro x; positivity
    have h_cont : Continuous (fun d : ℝ => max |d| δ) :=
      continuous_abs.max continuous_const
    have h_ne_zero : ∀ (x : ℝ), max |x| δ ≠ 0 := by
      intro x
      have h : 0 < max |x| δ := by positivity
      exact ne_of_gt h
    exact h_cont.rpow continuous_const (fun x => Or.inl (h_ne_zero x))
  have h2 : Measurable (fun d : ℝ => (max |d| δ) ^ (-s)) := h1.measurable
  exact ENNReal.measurable_ofReal.comp h2

/-! ### Pushforward energy comparison -/

lemma pushforward_projected_energy
    {δ s : ℝ} {S : Finset EuclideanPlane} {σ : ℝ}
    (hδ : 0 < δ) (hs : 0 < s) (hS_nonempty : S.Nonempty) :
    EnergyToDeltaSet.regularizedEnergy
      (Measure.map (fun p : EuclideanPlane => p 0 - σ * p 1) (uniformMeasure S)) s δ =
    EnergyAveraging.projectedEnergyReg (uniformMeasure S) s δ σ +
    ENNReal.ofReal (δ ^ (-s) / (S.card : ℝ)) := by
  let f : EuclideanPlane → ℝ := fun p => p 0 - σ * p 1
  let μ : Measure EuclideanPlane := uniformMeasure S
  let ν : Measure ℝ := Measure.map f μ
  let c : ENNReal := ENNReal.ofReal (δ ^ (-s))
  have hS_card_pos : 0 < S.card := Finset.card_pos.mpr hS_nonempty
  have h_card_ne_zero : (S.card : ENNReal) ≠ 0 := by
    exact_mod_cast hS_card_pos.ne'
  have hf_meas : Measurable f := by fun_prop
  have h_reg_meas : Measurable (fun d : ℝ => EnergyToDeltaSet.regularizedKernel s δ d) :=
    regularizedKernel_measurable hδ

  -- Pointwise decomposition
  have h_pointwise : ∀ (a b : EuclideanPlane),
      EnergyToDeltaSet.regularizedKernel s δ (f a - f b) =
      EnergyAveraging.projectedKernelReg s δ σ a b + (if a = b then c else 0) := by
    intro a b
    by_cases h : a = b
    · subst h
      have h_max : max (0 : ℝ) δ = δ := by
        rw [max_eq_right] <;> linarith
      have h_eq : EnergyToDeltaSet.regularizedKernel s δ (f a - f a) = c := by
        simp [EnergyToDeltaSet.regularizedKernel, f, c, h_max, hδ]
        <;> norm_num
      rw [h_eq]
      have h_proj : EnergyAveraging.projectedKernelReg s δ σ a a = 0 := by
        rw [EnergyAveraging.projectedKernelReg, if_pos rfl]
      rw [h_proj]
      <;> simp
    · have h3 : EnergyAveraging.projectedKernelReg s δ σ a b =
          ENNReal.ofReal ((max |f a - f b| δ) ^ (-s)) := by
        rw [EnergyAveraging.projectedKernelReg, if_neg h] <;> rfl
      have h4 : EnergyToDeltaSet.regularizedKernel s δ (f a - f b) =
          ENNReal.ofReal ((max |f a - f b| δ) ^ (-s)) := by rfl
      rw [h3, h4, if_neg h] <;> simp

  -- Helper: double integral over uniform measure = normalized double sum
  have h_double_sum : ∀ (K : EuclideanPlane → EuclideanPlane → ENNReal),
      ∫⁻ a, ∫⁻ b, K a b ∂μ ∂μ =
      (S.card : ENNReal)⁻¹ * (S.card : ENNReal)⁻¹ * ∑ a ∈ S, ∑ b ∈ S, K a b := by
    intro K
    have h1 : ∫⁻ a, ∫⁻ b, K a b ∂μ ∂μ =
        (S.card : ENNReal)⁻¹ * ∑ a ∈ S, ∫⁻ b, K a b ∂μ :=
      lintegral_uniformMeasure S (fun a => ∫⁻ b, K a b ∂μ)
    rw [h1]
    have h_term : ∀ a ∈ S, ∫⁻ b, K a b ∂μ = (S.card : ENNReal)⁻¹ * ∑ b ∈ S, K a b := by
      intro a _; exact lintegral_uniformMeasure S (K a)
    have h_sum : ∑ a ∈ S, ∫⁻ b, K a b ∂μ =
        ∑ a ∈ S, ((S.card : ENNReal)⁻¹ * ∑ b ∈ S, K a b) := by
      apply Finset.sum_congr rfl; exact h_term
    have h_sum2 : ∑ a ∈ S, ((S.card : ENNReal)⁻¹ * ∑ b ∈ S, K a b) =
        (S.card : ENNReal)⁻¹ * ∑ a ∈ S, ∑ b ∈ S, K a b := by
      rw [Finset.mul_sum]
    rw [h_sum, h_sum2] <;> ring

  -- Pushforward integral transformation
  have h_inner : ∀ (x : ℝ),
      ∫⁻ y, EnergyToDeltaSet.regularizedKernel s δ (x - y) ∂ν =
      ∫⁻ b, EnergyToDeltaSet.regularizedKernel s δ (x - f b) ∂μ := by
    intro x
    have h_meas : Measurable (fun y : ℝ => EnergyToDeltaSet.regularizedKernel s δ (x - y)) :=
      h_reg_meas.comp (measurable_const.sub measurable_id)
    rw [MeasureTheory.lintegral_map' h_meas.aemeasurable hf_meas.aemeasurable]

  have h_eq_sum : (fun x : ℝ => ∫⁻ b, EnergyToDeltaSet.regularizedKernel s δ (x - f b) ∂μ) =
      (fun x : ℝ => (S.card : ENNReal)⁻¹ * ∑ b ∈ S, EnergyToDeltaSet.regularizedKernel s δ (x - f b)) := by
    funext x
    exact lintegral_uniformMeasure S (fun b => EnergyToDeltaSet.regularizedKernel s δ (x - f b))

  have h_meas2 : Measurable (fun x : ℝ => ∫⁻ b, EnergyToDeltaSet.regularizedKernel s δ (x - f b) ∂μ) := by
    rw [h_eq_sum]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro b _
    exact h_reg_meas.comp (measurable_id.sub measurable_const)

  have h_outer :
      ∫⁻ x, ∫⁻ y, EnergyToDeltaSet.regularizedKernel s δ (x - y) ∂ν ∂ν =
      ∫⁻ a, ∫⁻ b, EnergyToDeltaSet.regularizedKernel s δ (f a - f b) ∂μ ∂μ := by
    rw [lintegral_congr (fun x => h_inner x)]
    rw [MeasureTheory.lintegral_map' h_meas2.aemeasurable hf_meas.aemeasurable]

  have h_pushforward_sum :
      ∫⁻ x, ∫⁻ y, EnergyToDeltaSet.regularizedKernel s δ (x - y) ∂ν ∂ν =
      (S.card : ENNReal)⁻¹ * (S.card : ENNReal)⁻¹ *
      ∑ a ∈ S, ∑ b ∈ S, EnergyToDeltaSet.regularizedKernel s δ (f a - f b) := by
    rw [h_outer]
    exact h_double_sum (fun a b => EnergyToDeltaSet.regularizedKernel s δ (f a - f b))

  have h_projected_sum :
      EnergyAveraging.projectedEnergyReg μ s δ σ =
      (S.card : ENNReal)⁻¹ * (S.card : ENNReal)⁻¹ *
      ∑ a ∈ S, ∑ b ∈ S, EnergyAveraging.projectedKernelReg s δ σ a b := by
    rw [EnergyAveraging.projectedEnergyReg]
    exact h_double_sum (EnergyAveraging.projectedKernelReg s δ σ)

  -- Diagonal sum
  have h_diag_sum : ∑ a ∈ S, ∑ b ∈ S, (if a = b then c else 0) = c * (S.card : ENNReal) := by
    have h1 : ∀ a ∈ S, ∑ b ∈ S, (if a = b then c else 0) = c := by
      intro a ha
      rw [Finset.sum_ite]
      have h3 : S.filter (fun b => a = b) = {a} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hax, h_eq⟩; exact h_eq.symm
        · intro hx
          have h_x_in_S : x ∈ S := by rw [hx] <;> exact ha
          exact ⟨h_x_in_S, hx.symm⟩
      rw [h3] <;> simp
    have h_sum : ∑ a ∈ S, ∑ b ∈ S, (if a = b then c else 0) = ∑ a ∈ S, c := by
      apply Finset.sum_congr rfl
      exact h1
    rw [h_sum]
    simp [Finset.sum_const]
    <;> ring

  -- Decompose the sum
  have h_decomp : ∑ a ∈ S, ∑ b ∈ S, EnergyToDeltaSet.regularizedKernel s δ (f a - f b) =
      (∑ a ∈ S, ∑ b ∈ S, EnergyAveraging.projectedKernelReg s δ σ a b) +
      ∑ a ∈ S, ∑ b ∈ S, (if a = b then c else 0) := by
    have h2 : ∀ a ∈ S, ∑ b ∈ S, EnergyToDeltaSet.regularizedKernel s δ (f a - f b) =
        (∑ b ∈ S, EnergyAveraging.projectedKernelReg s δ σ a b) + ∑ b ∈ S, (if a = b then c else 0) := by
      intro a _
      have h3 : ∀ b ∈ S, EnergyToDeltaSet.regularizedKernel s δ (f a - f b) =
          EnergyAveraging.projectedKernelReg s δ σ a b + (if a = b then c else 0) := by
        intro b _; exact h_pointwise a b
      rw [Finset.sum_congr rfl h3, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib]

  have h9 : c * (S.card : ENNReal)⁻¹ = ENNReal.ofReal (δ ^ (-s) / (S.card : ℝ)) := by
    have h10 : (S.card : ENNReal)⁻¹ = ENNReal.ofReal ((S.card : ℝ)⁻¹) := by
      simp [ENNReal.ofReal_inv_of_pos, hS_card_pos] <;> norm_cast
    have hc : c = ENNReal.ofReal (δ ^ (-s)) := by rfl
    rw [hc, h10]
    rw [← ENNReal.ofReal_mul (by positivity)]
    <;> field_simp [hS_card_pos.ne'] <;> ring

  have h12 : (S.card : ENNReal)⁻¹ * (S.card : ENNReal) = 1 := by
    apply ENNReal.inv_mul_cancel
    · exact h_card_ne_zero
    · exact WithTop.coe_ne_top
  have h11 : (S.card : ENNReal)⁻¹ * (S.card : ENNReal)⁻¹ * (c * (S.card : ENNReal)) =
      c * (S.card : ENNReal)⁻¹ := by
    have h13 : (S.card : ENNReal)⁻¹ * (S.card : ENNReal)⁻¹ * (c * (S.card : ENNReal)) =
        c * ((S.card : ENNReal)⁻¹ * ((S.card : ENNReal)⁻¹ * (S.card : ENNReal))) := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    rw [h13, h12] <;> simp

  calc
    EnergyToDeltaSet.regularizedEnergy ν s δ
      = (S.card : ENNReal)⁻¹ * (S.card : ENNReal)⁻¹ *
          ∑ a ∈ S, ∑ b ∈ S, EnergyToDeltaSet.regularizedKernel s δ (f a - f b) := h_pushforward_sum
    _ = (S.card : ENNReal)⁻¹ * (S.card : ENNReal)⁻¹ *
          ((∑ a ∈ S, ∑ b ∈ S, EnergyAveraging.projectedKernelReg s δ σ a b) +
           ∑ a ∈ S, ∑ b ∈ S, (if a = b then c else 0)) := by rw [h_decomp]
    _ = (S.card : ENNReal)⁻¹ * (S.card : ENNReal)⁻¹ *
          (∑ a ∈ S, ∑ b ∈ S, EnergyAveraging.projectedKernelReg s δ σ a b) +
        (S.card : ENNReal)⁻¹ * (S.card : ENNReal)⁻¹ *
          (∑ a ∈ S, ∑ b ∈ S, (if a = b then c else 0)) := by rw [mul_add] <;> ring
    _ = (S.card : ENNReal)⁻¹ * (S.card : ENNReal)⁻¹ *
          (∑ a ∈ S, ∑ b ∈ S, EnergyAveraging.projectedKernelReg s δ σ a b) +
        c * (S.card : ENNReal)⁻¹ := by rw [h_diag_sum, h11]
    _ = EnergyAveraging.projectedEnergyReg μ s δ σ + ENNReal.ofReal (δ ^ (-s) / (S.card : ℝ)) := by
        rw [h_projected_sum, h9] <;> ring

/-! ### Energy → Frostman via restriction -/

lemma energy_to_frostman_restriction
    {δ s E : ℝ} {ν : Measure ℝ}
    (hδ : 0 < δ) (hs : 0 < s) (hE : 0 < E)
    (hν_prob : ν Set.univ = 1)
    (h_energy : EnergyToDeltaSet.regularizedEnergy ν s δ ≤ ENNReal.ofReal E) :
    ∃ (ν' : Measure ℝ) (m : ℝ),
      m ≥ 1 / 2 ∧
      ν' Set.univ = ENNReal.ofReal m ∧
      (∀ (x : ℝ) (r : ℝ), δ / 2 ≤ r →
        ν' (closedBall x r) ≤ ENNReal.ofReal (2^(2*s+1) * E * r^s)) ∧
      ν'.support ⊆ ν.support := by

  let U : ℝ → ENNReal := fun x =>
    ∫⁻ y, EnergyToDeltaSet.regularizedKernel s δ (x - y) ∂ν

  have h_reg_meas : Measurable (fun d : ℝ => EnergyToDeltaSet.regularizedKernel s δ d) :=
    regularizedKernel_measurable hδ

  haveI : IsProbabilityMeasure ν := ⟨hν_prob⟩
  have hU_meas : Measurable U := by
    have h1 : Measurable (fun p : ℝ × ℝ => EnergyToDeltaSet.regularizedKernel s δ (p.1 - p.2)) :=
      h_reg_meas.comp (measurable_fst.sub measurable_snd)
    exact h1.lintegral_prod_right

  have h1 : ∫⁻ x, U x ∂ν ≤ ENNReal.ofReal E := h_energy

  let A : Set ℝ := {x | U x ≤ ENNReal.ofReal (2 * E)}

  have hA_meas : MeasurableSet A := by
    have h : MeasurableSet (Set.Iic (ENNReal.ofReal (2 * E))) :=
      isClosed_Iic.measurableSet
    exact hU_meas h

  have h2 : ν A ≥ ENNReal.ofReal (1 / 2 : ℝ) :=
    EnergyToDeltaSet.markov_half hE hU_meas hν_prob h1

  let ν' : Measure ℝ := ν.restrict A
  let m : ℝ := (ν' Set.univ).toReal

  have h3 : ν' Set.univ = ν A := by
    simp [ν', Measure.restrict_apply hA_meas] <;> rfl

  have h4 : ν' Set.univ ≠ ⊤ := by
    rw [h3]
    have h5 : ν A ≤ ν Set.univ := measure_mono (subset_univ A)
    rw [hν_prob] at h5
    exact ne_top_of_le_ne_top (by simp) h5

  have h5 : ν' Set.univ = ENNReal.ofReal m := by
    exact (ENNReal.ofReal_toReal h4).symm

  have h6 : m ≥ 1 / 2 := by
    have h7 : ENNReal.ofReal m = ν A := by rw [← h5, h3]
    have h8 : ENNReal.ofReal (1 / 2 : ℝ) ≤ ν A := h2
    have h9 : ENNReal.ofReal (1 / 2 : ℝ) ≤ ENNReal.ofReal m := by rw [h7] <;> exact h8
    have hm_nonneg : 0 ≤ m := by exact ENNReal.toReal_nonneg
    exact (ENNReal.ofReal_le_ofReal_iff hm_nonneg).mp h9

  have h10 : ∀ (x : ℝ), x ∈ A → ∀ (r : ℝ), δ ≤ r →
      ν (closedBall x r) ≤ ENNReal.ofReal (2 * E * r ^ s) := by
    intro x hx r hr
    have hUx : U x ≤ ENNReal.ofReal (2 * E) := hx
    exact EnergyToDeltaSet.potential_frostman_regularized hs hδ hr (by linarith) hUx

  have h11_ge : ∀ (z : ℝ) (r : ℝ), δ ≤ r →
      ν' (closedBall z r) ≤ ENNReal.ofReal (2^(s+1) * E * r^s) := by
    intro z r hr
    by_cases h_nonempty : (closedBall z r ∩ A).Nonempty
    · rcases h_nonempty with ⟨a, ha⟩
      have ha_in_ball : a ∈ closedBall z r := ha.1
      have ha_in_A : a ∈ A := ha.2
      have h14 : closedBall z r ⊆ closedBall a (2 * r) := by
        intro x hx
        have h15 : dist x a ≤ dist x z + dist z a := dist_triangle x z a
        have h16 : dist x z ≤ r := by simpa [closedBall] using hx
        have h17 : dist z a ≤ r := by
          have h17' : dist a z ≤ r := by simpa [closedBall] using ha_in_ball
          rw [dist_comm] at h17' <;> exact h17'
        have h18 : dist x a ≤ 2 * r := by linarith
        simpa [closedBall] using h18
      have h19 : ν' (closedBall z r) ≤ ν (closedBall z r) := by exact Measure.restrict_apply_le A (closedBall z r)
      have h20 : ν (closedBall z r) ≤ ν (closedBall a (2 * r)) := measure_mono h14
      have h21 : δ ≤ 2 * r := by linarith
      have h22 : ν (closedBall a (2 * r)) ≤ ENNReal.ofReal (2 * E * (2 * r) ^ s) :=
        h10 a ha_in_A (2 * r) h21
      have h23 : (2 * E * (2 * r) ^ s) = (2^(s+1) * E * r^s) := by
        have h25 : (2 * r) ^ s = (2 : ℝ)^s * r^s := by
          rw [← Real.mul_rpow (by norm_num) (by linarith)] <;> ring
        have h26 : (2 : ℝ)^(s+1) = 2 * (2 : ℝ)^s := by
          have h261 : (2 : ℝ)^(s+1) = (2 : ℝ)^s * (2 : ℝ)^(1 : ℝ) := by
            rw [← Real.rpow_add (by norm_num)] <;> ring
          rw [h261]
          have h262 : (2 : ℝ)^(1 : ℝ) = 2 := by simp
          rw [h262] <;> ring
        rw [h25, h26] <;> ring
      calc ν' (closedBall z r)
        ≤ ν (closedBall z r) := h19
        _ ≤ ν (closedBall a (2 * r)) := h20
        _ ≤ ENNReal.ofReal (2 * E * (2 * r) ^ s) := h22
        _ = ENNReal.ofReal (2^(s+1) * E * r^s) := by rw [h23]
    · have h_empty : (closedBall z r ∩ A) = ∅ := by
        simpa [Set.nonempty_iff_ne_empty] using h_nonempty
      have h12 : ν' (closedBall z r) = 0 := by
        have h13 : ν' (closedBall z r) = ν ((closedBall z r) ∩ A) := by exact Measure.restrict_apply' hA_meas
        rw [h13, h_empty] <;> simp
      rw [h12] <;> positivity

  have h11 : ∀ (z : ℝ) (r : ℝ), δ / 2 ≤ r →
      ν' (closedBall z r) ≤ ENNReal.ofReal (2^(2*s+1) * E * r^s) := by
    intro z r hr
    by_cases h_ge : δ ≤ r
    · have h_bound : ν' (closedBall z r) ≤ ENNReal.ofReal (2^(s+1) * E * r^s) := h11_ge z r h_ge
      have hr_pos : 0 < r := by linarith
      have h_const : (2^(s+1) * E * r^s) ≤ (2^(2*s+1) * E * r^s) := by
        have h_exp : (2 : ℝ)^(s+1) ≤ (2 : ℝ)^(2*s+1) := by gcongr <;> linarith
        have h : (2 : ℝ)^(s+1) * E * r^s ≤ (2 : ℝ)^(2*s+1) * E * r^s := by
          gcongr <;> linarith
        exact h
      exact h_bound.trans (ENNReal.ofReal_le_ofReal h_const)
    · have h_lt : r < δ := by linarith
      have h_sub : closedBall z r ⊆ closedBall z δ := by
        intro x hx
        have h : dist x z ≤ r := by simpa [closedBall] using hx
        simpa [closedBall] using le_trans h (by linarith)
      have h24 : ν' (closedBall z r) ≤ ν' (closedBall z δ) := measure_mono h_sub
      have h25 : ν' (closedBall z δ) ≤ ENNReal.ofReal (2^(s+1) * E * δ^s) := h11_ge z δ (by linarith)
      have h26 : δ ≤ 2 * r := by linarith
      have h27 : δ^s ≤ (2 * r)^s := by gcongr <;> linarith
      have h28 : (2^(s+1) * E * δ^s) ≤ (2^(2*s+1) * E * r^s) := by
        have h29 : (2 * r)^s = (2 : ℝ)^s * r^s := by
          rw [← Real.mul_rpow (by norm_num) (by linarith)] <;> ring
        calc
          (2^(s+1) * E * δ^s) ≤ 2^(s+1) * E * (2 * r)^s := by gcongr
          _ = 2^(s+1) * E * ((2 : ℝ)^s * r^s) := by rw [h29]
          _ = 2^(2*s+1) * E * r^s := by
            have h30 : (2 : ℝ)^(s+1) * (2 : ℝ)^s = (2 : ℝ)^(2*s+1) := by
              rw [← Real.rpow_add (by norm_num)] <;> ring_nf
            have h31 : (2 : ℝ)^(s+1) * E * ((2 : ℝ)^s * r^s) =
                ((2 : ℝ)^(s+1) * (2 : ℝ)^s) * (E * r^s) := by ring
            rw [h31, h30] <;> ring
      calc ν' (closedBall z r)
        ≤ ν' (closedBall z δ) := h24
        _ ≤ ENNReal.ofReal (2^(s+1) * E * δ^s) := h25
        _ ≤ ENNReal.ofReal (2^(2*s+1) * E * r^s) := ENNReal.ofReal_le_ofReal h28

  have h12 : ν'.support ⊆ ν.support := by
    have h13 := MeasureTheory.Measure.support_restrict_subset (μ := ν) (s := A)
    exact h13.trans (by simp)

  exact ⟨ν', m, h6, h5, h11, h12⟩

end

end RobustKaufmanProjection.RestrictionFrostman
