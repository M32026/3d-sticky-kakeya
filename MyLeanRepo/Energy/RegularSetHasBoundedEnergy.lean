module

/-
# Regular Set Has Bounded Energy

Full proof that a (δ,2s)-regular planar set admits a probability measure
with bounded 2κ-Riesz energy.

## Proof route

1. Construct representative set S (one point per δ-cube meeting P).
2. Convert IsDeltaSCSet to ball-counting bound for S (constant 9C).
3. Apply energy bound with max(dist,δ) regularization.
4. Define normalized counting measure ν on S.
5. Connect finite-sum energy to rieszEnergy integral.

## Dependencies

- `representative_set_construction` (RegularSetRepresentative)
- `delta_sc_set_to_ball_counting` (DeltaSCToBallCounting)
- `energy_max_from_ball_counting` (RegularSetEnergyMain)
- `bounded_energy_measure_from_finset` (packaging lemma below)

## Whiteprint node
KaufmanProjection energy axiom (H3).
-/

public import MyLeanRepo.Energy.RegularSetBoundedEnergy
public import MyLeanRepo.DeltaSCToBallCounting
public import MyLeanRepo.EnergyTransfer
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Finset Set Bornology Classical BigOperators

namespace robust_projection

/-- α-Riesz energy of a measure ν, with diagonal regularized at scale δ.
    The base max(dist x y, δ) is always positive, so this is well-defined for any real α. -/
def rieszEnergy (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {X : Type*} [MeasurableSpace X] [MetricSpace X] (ν : Measure X) : ENNReal :=
  ∫⁻ (x : X), ∫⁻ (y : X),
    ENNReal.ofReal ((max (dist x y) δ) ^ (-α)) ∂ν ∂ν

/-- Combined energy constant from the ball-covering method.
    Factor 9 comes from covering a Euclidean ball with a 3×3 grid of dyadic cubes. -/
def energyBoundConstant (C s κ : ℝ) : ℝ :=
  1 + 9 * C * (1 - (2 : ℝ) ^ (2 * (κ - s)) + (2 : ℝ) ^ (2 * κ)) /
    (1 - (2 : ℝ) ^ (2 * (κ - s)))

/-- Core packaging lemma: given a finset S with an energy bound, construct
    a probability measure ν with bounded rieszEnergy. -/
lemma bounded_energy_measure_from_finset
    {δ κ C_energy : ℝ}
    {S : Finset (EuclideanSpace ℝ (Fin 2))}
    (hδ : 0 < δ)
    (hS_nonempty : S.Nonempty)
    (hC_energy_nonneg : 0 ≤ C_energy)
    (h_sum_bound : ∑ p ∈ S, ∑ q ∈ S, (max (dist p q) δ) ^ (-2 * κ) ≤ C_energy * (S.card : ℝ)^2) :
    ∃ (ν : Measure (EuclideanSpace ℝ (Fin 2))),
      ν Set.univ = 1 ∧
      ν.support ⊆ (S : Set (EuclideanSpace ℝ (Fin 2))) ∧
      rieszEnergy (2 * κ) (hδ := hδ) ν ≤ ENNReal.ofReal C_energy := by
  let c : ENNReal := (S.card : ENNReal)
  have hc_ne_top : c ≠ ⊤ := ENNReal.coe_ne_top
  have hc_ne_zero : c ≠ 0 := by
    intro h
    have h' : (S.card : ENNReal) = 0 := h
    have h'' : S.card = 0 := by simpa [c] using h'
    have h3 : S = ∅ := Finset.card_eq_zero.mp h''
    exact hS_nonempty.ne_empty h3
  let ν : Measure (EuclideanSpace ℝ (Fin 2)) :=
    ∑ p ∈ S, c⁻¹ • Measure.dirac p

  have h_mul_inv : c * c⁻¹ = 1 := ENNReal.mul_inv_cancel hc_ne_zero hc_ne_top
  have h_mul_inv2 : c⁻¹ * c = 1 := by
    rw [mul_comm]; exact h_mul_inv

  have hν_univ : ν Set.univ = 1 := by
    have h1 : ν Set.univ = ∑ p ∈ S, (c⁻¹ • Measure.dirac p) Set.univ := by
      rw [Measure.finsetSum_apply S (fun p => c⁻¹ • Measure.dirac p) Set.univ] <;> rfl
    rw [h1]
    have h2 : ∀ p ∈ S, (c⁻¹ • Measure.dirac p) Set.univ = c⁻¹ := by
      intro p _; simp
    rw [Finset.sum_congr rfl h2]
    have h3 : ∑ _ ∈ S, c⁻¹ = c * c⁻¹ := by
      simp [Finset.sum_const, c] <;> ring
    rw [h3, h_mul_inv]

  have hS_closed : IsClosed (S : Set (EuclideanSpace ℝ (Fin 2))) :=
    Set.Finite.isClosed (Finset.finite_toSet S)

  have h_ν_compl : ν ((S : Set (EuclideanSpace ℝ (Fin 2)))ᶜ) = 0 := by
    have h1 : ν ((S : Set _)ᶜ) = ∑ p ∈ S, (c⁻¹ • Measure.dirac p) ((S : Set _)ᶜ) := by
      rw [Measure.finsetSum_apply S (fun p => c⁻¹ • Measure.dirac p) ((S : Set _)ᶜ)] <;> rfl
    rw [h1]
    have h2 : ∀ p ∈ S, (c⁻¹ • Measure.dirac p) ((S : Set _)ᶜ) = 0 := by
      intro p hp; simp [hp] <;> tauto
    rw [Finset.sum_congr rfl h2] <;> simp

  have h_S_ae : (S : Set (EuclideanSpace ℝ (Fin 2))) ∈ ae ν := by
    rw [MeasureTheory.mem_ae_iff]
    exact h_ν_compl
  have hν_support : ν.support ⊆ (S : Set (EuclideanSpace ℝ (Fin 2))) :=
    Measure.support_subset_of_isClosed hS_closed h_S_ae

  have h_lintegral : ∀ (f : (EuclideanSpace ℝ (Fin 2)) → ENNReal), Measurable f →
      ∫⁻ x, f x ∂ν = c⁻¹ * ∑ x ∈ S, f x := by
    intro f hf
    have h1 : ∫⁻ x, f x ∂ν = ∑ p ∈ S, ∫⁻ x, f x ∂(c⁻¹ • Measure.dirac p) := by
      rw [lintegral_finsetSum_measure S f (fun p => c⁻¹ • Measure.dirac p)] <;> rfl
    rw [h1]
    have h2 : ∀ p ∈ S, ∫⁻ x, f x ∂(c⁻¹ • Measure.dirac p) = c⁻¹ * f p := by
      intro p _
      rw [lintegral_smul_measure c⁻¹ f, lintegral_dirac' p hf] <;> rfl
    rw [Finset.sum_congr rfl h2, Finset.mul_sum] <;> rfl

  let k : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2)) → ENNReal :=
    fun x y => ENNReal.ofReal ((max (dist x y) δ) ^ (-2 * κ))

  have h_k_sym : ∀ (x y : EuclideanSpace ℝ (Fin 2)), k x y = k y x := by
    intro x y
    have h1 : dist x y = dist y x := dist_comm x y
    simp [k, h1]

  have h_k_meas : ∀ (x : EuclideanSpace ℝ (Fin 2)), Measurable (k x) := by
    intro x
    have h1a : Continuous (fun y : EuclideanSpace ℝ (Fin 2) => dist x y) :=
      continuous_const.dist continuous_id
    have h1b : Continuous (fun y => max (dist x y) δ) := h1a.max continuous_const
    have h_cond : ∀ y, max (dist x y) δ ≠ 0 ∨ 0 < (-2 * κ) := by
      intro y; left; have hpos : 0 < max (dist x y) δ := lt_max_of_lt_right hδ; exact ne_of_gt hpos
    have h1c : Continuous (fun y => (max (dist x y) δ) ^ (-2 * κ)) :=
      h1b.rpow continuous_const h_cond
    exact measurable_ofReal.comp h1c.measurable

  have h_k_nonneg : ∀ (x y : EuclideanSpace ℝ (Fin 2)), 0 ≤ (max (dist x y) δ) ^ (-2 * κ) := by
    intro x y
    have hpos : 0 < max (dist x y) δ := by positivity
    positivity

  have h_main_sum : ∑ p ∈ S, ∑ q ∈ S, k p q ≤ ENNReal.ofReal (C_energy * (S.card : ℝ)^2) := by
    have h4 : ∀ (p : EuclideanSpace ℝ (Fin 2)), p ∈ S → ∑ q ∈ S, k p q =
        ENNReal.ofReal (∑ q ∈ S, (max (dist p q) δ) ^ (-2 * κ)) := by
      intro p _
      have h5 : ∀ q ∈ S, 0 ≤ (max (dist p q) δ) ^ (-2 * κ) := by
        intro q _; exact h_k_nonneg p q
      have h6 : ∑ q ∈ S, k p q = ∑ q ∈ S, ENNReal.ofReal ((max (dist p q) δ) ^ (-2 * κ)) := by rfl
      rw [h6, ← ENNReal.ofReal_sum_of_nonneg h5] <;> rfl
    have h3 : ∑ p ∈ S, ∑ q ∈ S, k p q =
        ENNReal.ofReal (∑ p ∈ S, ∑ q ∈ S, (max (dist p q) δ) ^ (-2 * κ)) := by
      rw [Finset.sum_congr rfl h4]
      have h6 : ∀ p ∈ S, 0 ≤ ∑ q ∈ S, (max (dist p q) δ) ^ (-2 * κ) := by
        intro p _; positivity
      rw [← ENNReal.ofReal_sum_of_nonneg h6] <;> rfl
    rw [h3]
    exact ENNReal.ofReal_le_ofReal h_sum_bound

  have h_partial_eq : ∀ (x : EuclideanSpace ℝ (Fin 2)),
      (∫⁻ (y), k x y ∂ν) = c⁻¹ * ∑ q ∈ S, k x q := by
    intro x
    exact h_lintegral (k x) (h_k_meas x)

  have h_partial_meas : Measurable (fun x : EuclideanSpace ℝ (Fin 2) => ∫⁻ (y), k x y ∂ν) := by
    have h_eq : (fun x : EuclideanSpace ℝ (Fin 2) => ∫⁻ (y), k x y ∂ν) =
        fun x => c⁻¹ * ∑ q ∈ S, k x q := by
      funext x
      exact h_partial_eq x
    rw [h_eq]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro q _
    have h_sym : (fun x : EuclideanSpace ℝ (Fin 2) => k x q) = k q := by
      funext x
      exact h_k_sym x q
    rw [h_sym]
    exact h_k_meas q

  have h2 : ∀ p ∈ S, ∫⁻ (y), k p y ∂ν = c⁻¹ * ∑ q ∈ S, k p q := by
    intro p _
    exact h_partial_eq p

  have h_energy : rieszEnergy (2 * κ) (hδ := hδ) ν =
      c⁻¹ ^ 2 * ∑ p ∈ S, ∑ q ∈ S, k p q := by
    dsimp only [rieszEnergy]
    have h_step1 : ∫⁻ (x : EuclideanSpace ℝ (Fin 2)), (∫⁻ (y : EuclideanSpace ℝ (Fin 2)), k x y ∂ν) ∂ν =
        c⁻¹ * ∑ p ∈ S, (∫⁻ (y), k p y ∂ν) :=
      h_lintegral (fun x => ∫⁻ (y), k x y ∂ν) h_partial_meas
    have h_step2 : c⁻¹ * ∑ p ∈ S, (∫⁻ (y), k p y ∂ν) =
        c⁻¹ * ∑ p ∈ S, (c⁻¹ * ∑ q ∈ S, k p q) := by
      rw [Finset.sum_congr rfl h2]
    have h_step3 : c⁻¹ * ∑ p ∈ S, (c⁻¹ * ∑ q ∈ S, k p q) =
        c⁻¹ ^ 2 * ∑ p ∈ S, ∑ q ∈ S, k p q := by
      have h : ∑ p ∈ S, (c⁻¹ * ∑ q ∈ S, k p q) = c⁻¹ * ∑ p ∈ S, ∑ q ∈ S, k p q := by
        rw [Finset.mul_sum] <;> rfl
      rw [h] <;> ring
    have h_goal : ∫⁻ (x : EuclideanSpace ℝ (Fin 2)), (∫⁻ (y : EuclideanSpace ℝ (Fin 2)), k x y ∂ν) ∂ν =
        c⁻¹ ^ 2 * ∑ p ∈ S, ∑ q ∈ S, k p q := by
      calc _ = c⁻¹ * ∑ p ∈ S, (∫⁻ (y), k p y ∂ν) := h_step1
           _ = c⁻¹ * ∑ p ∈ S, (c⁻¹ * ∑ q ∈ S, k p q) := h_step2
           _ = c⁻¹ ^ 2 * ∑ p ∈ S, ∑ q ∈ S, k p q := h_step3
    simpa [rieszEnergy, k] using h_goal

  have h11 : c⁻¹ ^ 2 * c ^ 2 = 1 := by
    have h12 : c⁻¹ ^ 2 * c ^ 2 = (c⁻¹ * c) ^ 2 := by
      rw [← mul_pow] <;> ring
    rw [h12, h_mul_inv2] <;> norm_num

  have h7 : ENNReal.ofReal (C_energy * (S.card : ℝ)^2) =
      ENNReal.ofReal C_energy * c ^ 2 := by
    rw [ENNReal.ofReal_mul hC_energy_nonneg]
    have h9 : ENNReal.ofReal ((S.card : ℝ)^2) = c ^ 2 := by
      simp [c] <;> norm_cast
    rw [h9] <;> ring

  have h_final : rieszEnergy (2 * κ) (hδ := hδ) ν ≤ ENNReal.ofReal C_energy := by
    rw [h_energy]
    have h5 : c⁻¹ ^ 2 * ∑ p ∈ S, ∑ q ∈ S, k p q ≤
        c⁻¹ ^ 2 * ENNReal.ofReal (C_energy * (S.card : ℝ)^2) := by
      gcongr <;> exact h_main_sum
    rw [h7] at h5
    have h10 : c⁻¹ ^ 2 * (ENNReal.ofReal C_energy * c ^ 2) = ENNReal.ofReal C_energy := by
      calc c⁻¹ ^ 2 * (ENNReal.ofReal C_energy * c ^ 2)
          = ENNReal.ofReal C_energy * (c⁻¹ ^ 2 * c ^ 2) := by ring
        _ = ENNReal.ofReal C_energy * 1 := by rw [h11]
        _ = ENNReal.ofReal C_energy := by simp
    rw [h10] at h5
    exact h5

  exact ⟨ν, hν_univ, hν_support, h_final⟩

/-- Strengthened version that also exposes the cardinal equality
    `(S.card : ENNReal) = Nplane δ P` and per-cube uniqueness. -/
theorem regular_set_has_bounded_energy_with_card
    {δ s κ C : ℝ}
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hs : 0 < s) (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hκ_pos : 0 < κ) (hκ_lt_s : κ < s)
    (hP : IsDeltaSCSet δ (2 * s) C P)
    (hP_bdd : Bornology.IsBounded P) (hP_nonempty : P.Nonempty)
    (hP_lower : ENNReal.ofReal (δ ^ (-2*κ)) ≤ Nplane δ P) :
    ∃ (S : Finset (EuclideanSpace ℝ (Fin 2)))
      (ν : Measure (EuclideanSpace ℝ (Fin 2))),
      S.Nonempty ∧
      IsDeltaDense δ S P ∧
      (S.card : ENNReal) = Nplane δ P ∧
      (∀ Q ∈ dyadicCubesMeeting δ P,
        ∃! (p : EuclideanSpace ℝ (Fin 2)), p ∈ S ∧ p ∈ Q ∩ P) ∧
      ν Set.univ = 1 ∧
      ν.support ⊆ P ∧
      (ν = ∑ p ∈ S, (1 / (S.card : ENNReal)) • Measure.dirac p) ∧
      rieszEnergy (2 * κ) (hδ := hδ_pos) ν ≤
        ENNReal.ofReal (energyBoundConstant C s κ) := by
  -- Step 1: Construct representative set S
  rcases representative_set_construction hδ_pos hP_bdd hP_nonempty with
    ⟨S, hS_rep, hS_card, hS_in_P⟩
  have hδ_dyadic : δ ∈ dyadicScales := hP.2.2.2.1

  have hS_lower : ENNReal.ofReal (δ ^ (-2*κ)) ≤ (S.card : ENNReal) := by
    have h1 : (S.card : ENNReal) = Nplane δ P := hS_card
    rw [h1]
    exact hP_lower

  have hS_nonempty : S.Nonempty := by
    have h1 : (S.card : ENNReal) = Nplane δ P := hS_card
    have h2 : 0 < ENNReal.ofReal (δ ^ (-2*κ)) := by positivity
    have h3 : 0 < Nplane δ P := lt_of_lt_of_le h2 hP_lower
    have h4 : (0 : ENNReal) < (S.card : ENNReal) := by
      rw [h1] <;> exact h3
    exact Finset.card_pos.mp (by exact_mod_cast h4)

  -- Step 2: Ball-counting bound for S with constant 9C
  have h_ball : ∀ (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ),
      δ ≤ r → r ≤ 1 → r ∈ dyadicScales →
      (S.filter (fun q => dist p q < r)).card ≤ (9 * C) * (S.card : ℝ) * r ^ (2 * s) := by
    intro p r hδ_le_r hr_le_one hr_dyadic
    exact delta_sc_set_to_ball_counting hP hS_rep hS_card p r hδ_pos hδ_le_r hr_le_one hr_dyadic

  -- Step 3: Energy sum bound with constant energyBoundConstant C s κ
  set C_ball : ℝ := 9 * C with hC_ball_def
  have hC_ball_pos : 0 < C_ball := by
    have hC_pos : 0 < C := hP.2.2.2.2.2.2.2.1
    positivity

  have h_sum_bound : ∑ p ∈ S, ∑ q ∈ S, (max (dist p q) δ) ^ (-2 * κ) ≤
      (1 + C_ball * (1 - (2 : ℝ) ^ (2 * (κ - s)) + (2 : ℝ) ^ (2 * κ)) /
        (1 - (2 : ℝ) ^ (2 * (κ - s)))) * (S.card : ℝ)^2 :=
    energy_max_from_ball_counting hδ_pos hδ_lt_one hδ_dyadic hs hκ_pos hκ_lt_s hC_ball_pos hS_nonempty h_ball

  have h_const_match : (1 + C_ball * (1 - (2 : ℝ) ^ (2 * (κ - s)) + (2 : ℝ) ^ (2 * κ)) /
      (1 - (2 : ℝ) ^ (2 * (κ - s)))) = energyBoundConstant C s κ := by
    simp [energyBoundConstant, hC_ball_def] <;> ring

  rw [h_const_match] at h_sum_bound

  -- Step 4: Construct probability measure ν
  have hC_energy_nonneg : 0 ≤ energyBoundConstant C s κ := by
    have hC_pos : 0 < C := hP.2.2.2.2.2.2.2.1
    have hx_lt_one : (2 : ℝ) ^ (2 * (κ - s)) < 1 := by
      have h1 : 2 * (κ - s) < 0 := by linarith
      have h2 : (2 : ℝ) ^ (2 * (κ - s)) < (2 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
      simpa using h2
    have h_denom_pos : 0 < 1 - (2 : ℝ) ^ (2 * (κ - s)) := by linarith
    have h_num_nonneg : 0 ≤ 1 - (2 : ℝ) ^ (2 * (κ - s)) + (2 : ℝ) ^ (2 * κ) := by positivity
    have h_frac_nonneg : 0 ≤ (9 * C * (1 - (2 : ℝ) ^ (2 * (κ - s)) + (2 : ℝ) ^ (2 * κ))) / (1 - (2 : ℝ) ^ (2 * (κ - s))) := by
      apply div_nonneg
      · positivity
      · linarith
    have h_main : 0 ≤ (1 : ℝ) + (9 * C * (1 - (2 : ℝ) ^ (2 * (κ - s)) + (2 : ℝ) ^ (2 * κ))) / (1 - (2 : ℝ) ^ (2 * (κ - s))) := by linarith
    simpa [energyBoundConstant] using h_main

  -- Step 4: Construct probability measure ν explicitly
  let c : ENNReal := (S.card : ENNReal)
  have hc_ne_zero : c ≠ 0 := by
    have h : 0 < S.card := hS_nonempty.card_pos
    have h' : (0 : ENNReal) < (S.card : ENNReal) := by exact_mod_cast h
    have h'' : (0 : ENNReal) < c := by simpa [c] using h'
    exact ne_of_gt h''
  have hc_ne_top : c ≠ ⊤ := ENNReal.coe_ne_top
  let ν : Measure (EuclideanSpace ℝ (Fin 2)) :=
    ∑ p ∈ S, (1 / c) • Measure.dirac p

  have hν_counting : ν = ∑ p ∈ S, (1 / (S.card : ENNReal)) • Measure.dirac p := by
    rfl

  have h_div : (1 / c) = c⁻¹ := by simp
  have h_mul_inv : c * (1 / c) = 1 := by
    rw [h_div]
    exact ENNReal.mul_inv_cancel hc_ne_zero hc_ne_top
  have hν_univ : ν Set.univ = 1 := by
    have h1 : ν Set.univ = ∑ p ∈ S, ((1 / c) • Measure.dirac p) Set.univ := by
      rw [Measure.finsetSum_apply S (fun p => (1 / c) • Measure.dirac p) Set.univ] <;> rfl
    rw [h1]
    have h2 : ∀ p ∈ S, ((1 / c) • Measure.dirac p) Set.univ = 1 / c := by
      intro p _; simp
    rw [Finset.sum_congr rfl h2]
    have h3 : ∑ _ ∈ S, (1 / c) = c * (1 / c) := by
      simp [Finset.sum_const, c] <;> ring
    rw [h3, h_mul_inv]

  have hS_closed : IsClosed (S : Set (EuclideanSpace ℝ (Fin 2))) :=
    Set.Finite.isClosed (Finset.finite_toSet S)
  have h_ν_compl : ν ((S : Set (EuclideanSpace ℝ (Fin 2)))ᶜ) = 0 := by
    have h1 : ν ((S : Set _)ᶜ) = ∑ p ∈ S, ((1 / c) • Measure.dirac p) ((S : Set _)ᶜ) := by
      rw [Measure.finsetSum_apply S (fun p => (1 / c) • Measure.dirac p) ((S : Set _)ᶜ)] <;> rfl
    rw [h1]
    have h2 : ∀ p ∈ S, ((1 / c) • Measure.dirac p) ((S : Set _)ᶜ) = 0 := by
      intro p hp; simp [hp] <;> tauto
    rw [Finset.sum_congr rfl h2] <;> simp
  have h_S_ae : (S : Set (EuclideanSpace ℝ (Fin 2))) ∈ ae ν := by
    rw [MeasureTheory.mem_ae_iff]; exact h_ν_compl
  have hν_support_S : ν.support ⊆ (S : Set (EuclideanSpace ℝ (Fin 2))) :=
    Measure.support_subset_of_isClosed hS_closed h_S_ae
  have hν_support_P : ν.support ⊆ P := by
    calc ν.support ⊆ (S : Set _) := hν_support_S
         _ ⊆ P := by exact fun x hx => hS_in_P x hx

  -- Step 5: Prove IsDeltaDense δ S P
  have hS_sub_P : (S : Set _) ⊆ P := by exact fun x hx => hS_in_P x hx
  have h_dense : ∀ p ∈ P, ∃ (p_fin : EuclideanSpace ℝ (Fin 2)), p_fin ∈ S ∧ (∀ i : Fin 2, |p i - p_fin i| ≤ δ) := by
    intro p hp
    let k : Fin 2 → ℤ := fun i => ⌊p i / δ⌋
    let Q : Set (EuclideanSpace ℝ (Fin 2)) := dyadicCube δ k
    have hQ_in_cubes : Q ∈ dyadicCubes 2 δ := ⟨k, rfl⟩
    have hp_in_Q : p ∈ Q := by
      dsimp only [Q, dyadicCube, Set.mem_setOf_eq]
      intro i; exact floor_cube_mem (hr := hδ_pos) (x := p i)
    have hQ_meet : Q ∈ dyadicCubesMeeting δ P := ⟨hQ_in_cubes, ⟨p, hp_in_Q, hp⟩⟩
    have h_unique : ∃! (p_fin : EuclideanSpace ℝ (Fin 2)), p_fin ∈ S ∧ p_fin ∈ Q ∩ P := hS_rep Q hQ_meet
    rcases h_unique with ⟨p_fin, h_prop, _⟩
    have hpfin_S : p_fin ∈ S := h_prop.1
    have hpfin_QP : p_fin ∈ Q ∩ P := h_prop.2
    have hpfin_Q : p_fin ∈ Q := hpfin_QP.1
    refine' ⟨p_fin, ⟨hpfin_S, _⟩⟩
    intro i
    have h1 : p i ∈ Set.Ico (δ * (k i : ℝ)) (δ * ((k i : ℝ) + 1)) := hp_in_Q i
    have h2 : p_fin i ∈ Set.Ico (δ * (k i : ℝ)) (δ * ((k i : ℝ) + 1)) := hpfin_Q i
    have h3 : |p i - p_fin i| < δ := by
      rw [Set.mem_Ico] at h1 h2
      have h4 : p i - p_fin i < δ := by linarith
      have h5 : -(δ : ℝ) < p i - p_fin i := by linarith
      rw [abs_lt] <;> constructor <;> linarith
    linarith
  have hS_dense : IsDeltaDense δ S P := ⟨hS_sub_P, h_dense⟩

  -- Step 6: Energy bound (inline calculation from bounded_energy_measure_from_finset)
  let k : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2)) → ENNReal :=
    fun x y => ENNReal.ofReal ((max (dist x y) δ) ^ (-2 * κ))
  have h_k_meas : ∀ (x : EuclideanSpace ℝ (Fin 2)), Measurable (k x) := by
    intro x
    have h1a : Continuous (fun y : EuclideanSpace ℝ (Fin 2) => dist x y) :=
      continuous_const.dist continuous_id
    have h1b : Continuous (fun y => max (dist x y) δ) := h1a.max continuous_const
    have h_cond : ∀ y, max (dist x y) δ ≠ 0 ∨ 0 < (-2 * κ) := by
      intro y; left; have hpos : 0 < max (dist x y) δ := lt_max_of_lt_right hδ_pos; exact ne_of_gt hpos
    have h1c : Continuous (fun y => (max (dist x y) δ) ^ (-2 * κ)) :=
      h1b.rpow continuous_const h_cond
    exact measurable_ofReal.comp h1c.measurable
  have h_k_nonneg : ∀ (x y : EuclideanSpace ℝ (Fin 2)), 0 ≤ (max (dist x y) δ) ^ (-2 * κ) := by
    intro x y
    have hpos : 0 < max (dist x y) δ := by positivity
    exact Real.rpow_nonneg hpos.le _
  have h_lintegral1 : ∀ (f : _ → ENNReal), Measurable f →
      ∫⁻ x, f x ∂ν = (1 / c) * ∑ x ∈ S, f x := by
    intro f hf
    have h1 : ∫⁻ x, f x ∂ν = ∑ p ∈ S, ∫⁻ x, f x ∂((1 / c) • Measure.dirac p) := by
      rw [lintegral_finsetSum_measure S f (fun p => (1 / c) • Measure.dirac p)] <;> rfl
    rw [h1]
    have h2 : ∀ p ∈ S, ∫⁻ x, f x ∂((1 / c) • Measure.dirac p) = (1 / c) * f p := by
      intro p _; rw [lintegral_smul_measure (1 / c) f, lintegral_dirac' p hf] <;> rfl
    rw [Finset.sum_congr rfl h2, Finset.mul_sum] <;> rfl
  have h_partial_meas : Measurable (fun x => ∫⁻ (y), k x y ∂ν) := by
    have h_eq : (fun x => ∫⁻ (y), k x y ∂ν) = fun x => (1 / c) * ∑ q ∈ S, k x q := by
      funext x; exact h_lintegral1 (k x) (h_k_meas x)
    rw [h_eq]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro q _
    have h_sym : (fun x => k x q) = k q := by funext x; simp [k, dist_comm]
    rw [h_sym]; exact h_k_meas q
  have h_energy : rieszEnergy (2 * κ) (hδ := hδ_pos) ν =
      (1 / c) ^ 2 * ∑ p ∈ S, ∑ q ∈ S, k p q := by
    dsimp only [rieszEnergy]
    have h_step1 : ∫⁻ (x), (∫⁻ (y), k x y ∂ν) ∂ν =
        (1 / c) * ∑ p ∈ S, (∫⁻ (y), k p y ∂ν) :=
      h_lintegral1 (fun x => ∫⁻ (y), k x y ∂ν) h_partial_meas
    have h_step2 : (1 / c) * ∑ p ∈ S, (∫⁻ (y), k p y ∂ν) =
        (1 / c) * ∑ p ∈ S, ((1 / c) * ∑ q ∈ S, k p q) := by
      rw [Finset.sum_congr rfl (fun p _ => h_lintegral1 (k p) (h_k_meas p))]
    have h_step3 : (1 / c) * ∑ p ∈ S, ((1 / c) * ∑ q ∈ S, k p q) =
        (1 / c) ^ 2 * ∑ p ∈ S, ∑ q ∈ S, k p q := by
      have h : ∑ p ∈ S, ((1 / c) * ∑ q ∈ S, k p q) = (1 / c) * ∑ p ∈ S, ∑ q ∈ S, k p q := by
        rw [Finset.mul_sum] <;> rfl
      rw [h] <;> ring
    have h_goal : ∫⁻ (x : EuclideanSpace ℝ (Fin 2)), (∫⁻ (y : EuclideanSpace ℝ (Fin 2)), k x y ∂ν) ∂ν =
        (1 / c) ^ 2 * ∑ p ∈ S, ∑ q ∈ S, k p q := by
      exact h_step1.trans (h_step2.trans h_step3)
    simpa [rieszEnergy, k] using h_goal
  have h_main_sum : ∑ p ∈ S, ∑ q ∈ S, k p q ≤
      ENNReal.ofReal (energyBoundConstant C s κ * (S.card : ℝ)^2) := by
    have h4 : ∀ p ∈ S, ∑ q ∈ S, k p q = ENNReal.ofReal (∑ q ∈ S, (max (dist p q) δ) ^ (-2 * κ)) := by
      intro p _
      have h5 : ∀ q ∈ S, 0 ≤ (max (dist p q) δ) ^ (-2 * κ) := by intro q _; exact h_k_nonneg p q
      have h6 : ∑ q ∈ S, k p q = ∑ q ∈ S, ENNReal.ofReal ((max (dist p q) δ) ^ (-2 * κ)) := by rfl
      rw [h6, ← ENNReal.ofReal_sum_of_nonneg h5] <;> rfl
    have h3 : ∑ p ∈ S, ∑ q ∈ S, k p q =
        ENNReal.ofReal (∑ p ∈ S, ∑ q ∈ S, (max (dist p q) δ) ^ (-2 * κ)) := by
      rw [Finset.sum_congr rfl h4]
      have h6 : ∀ p ∈ S, 0 ≤ ∑ q ∈ S, (max (dist p q) δ) ^ (-2 * κ) := by intro p _; positivity
      rw [← ENNReal.ofReal_sum_of_nonneg h6] <;> rfl
    rw [h3]
    exact ENNReal.ofReal_le_ofReal h_sum_bound
  have h_mul_inv2 : (1 / c) * c = 1 := by
    rw [mul_comm]
    exact h_mul_inv
  have h11 : (1 / c) ^ 2 * c ^ 2 = 1 := by
    have h12 : (1 / c) ^ 2 * c ^ 2 = ((1 / c) * c) ^ 2 := by rw [← mul_pow] <;> ring
    rw [h12, h_mul_inv2] <;> norm_num
  have h7 : ENNReal.ofReal (energyBoundConstant C s κ * (S.card : ℝ)^2) =
      ENNReal.ofReal (energyBoundConstant C s κ) * c ^ 2 := by
    rw [ENNReal.ofReal_mul hC_energy_nonneg]
    have h9 : ENNReal.ofReal ((S.card : ℝ)^2) = c ^ 2 := by simp [c] <;> norm_cast
    rw [h9] <;> ring

  -- Diagonal contribution to normalized energy is ≤ 1, using hP_lower
  have h_diag_sum : ∑ p ∈ S, k p p = c * ENNReal.ofReal (δ ^ (-2*κ)) := by
    have h1 : ∀ p ∈ S, k p p = ENNReal.ofReal (δ ^ (-2*κ)) := by
      intro p _
      have h2 : dist p p = 0 := dist_self p
      have h3 : max (dist p p) δ = δ := by
        rw [h2, max_eq_right] <;> linarith
      have h4 : (max (dist p p) δ) ^ (-2 * κ) = δ ^ (-2 * κ) := by rw [h3]
      dsimp only [k]
      rw [h4]
    rw [Finset.sum_congr rfl h1]
    have h_sum_const : ∑ _ ∈ S, ENNReal.ofReal (δ ^ (-2*κ)) =
        c * ENNReal.ofReal (δ ^ (-2*κ)) := by
      simp [Finset.sum_const, c] <;> ring
    exact h_sum_const
  have h_diag_normalized : (1 / c) ^ 2 * (∑ p ∈ S, k p p) ≤ 1 := by
    rw [h_diag_sum]
    have h1 : (1 / c) ^ 2 * (c * ENNReal.ofReal (δ ^ (-2*κ))) =
        (1 / c) * ENNReal.ofReal (δ ^ (-2*κ)) := by
      have h_mul_comm : (1 / c) * c = 1 := by
        rw [mul_comm]
        exact h_mul_inv
      calc (1 / c) ^ 2 * (c * ENNReal.ofReal (δ ^ (-2*κ)))
          = (1 / c) * ((1 / c) * c) * ENNReal.ofReal (δ ^ (-2*κ)) := by ring
        _ = (1 / c) * 1 * ENNReal.ofReal (δ ^ (-2*κ)) := by rw [h_mul_comm]
        _ = (1 / c) * ENNReal.ofReal (δ ^ (-2*κ)) := by ring
    rw [h1]
    have h2 : (1 / c) * ENNReal.ofReal (δ ^ (-2*κ)) ≤ (1 / c) * c := by
      gcongr
      <;> exact hS_lower
    have h_mul_comm2 : (1 / c) * c = 1 := by
      rw [mul_comm]
      exact h_mul_inv
    rw [h_mul_comm2] at h2
    exact h2

  have h_final : rieszEnergy (2 * κ) (hδ := hδ_pos) ν ≤ ENNReal.ofReal (energyBoundConstant C s κ) := by
    rw [h_energy]
    have h5 : (1 / c) ^ 2 * ∑ p ∈ S, ∑ q ∈ S, k p q ≤
        (1 / c) ^ 2 * ENNReal.ofReal (energyBoundConstant C s κ * (S.card : ℝ)^2) := by
      gcongr <;> exact h_main_sum
    rw [h7] at h5
    have h10 : (1 / c) ^ 2 * (ENNReal.ofReal (energyBoundConstant C s κ) * c ^ 2) =
        ENNReal.ofReal (energyBoundConstant C s κ) := by
      calc (1 / c) ^ 2 * (ENNReal.ofReal (energyBoundConstant C s κ) * c ^ 2)
          = ENNReal.ofReal (energyBoundConstant C s κ) * ((1 / c) ^ 2 * c ^ 2) := by ring
        _ = ENNReal.ofReal (energyBoundConstant C s κ) * 1 := by rw [h11]
        _ = ENNReal.ofReal (energyBoundConstant C s κ) := by simp
    rw [h10] at h5; exact h5

  exact ⟨S, ν, hS_nonempty, hS_dense, hS_card, hS_rep, hν_univ, hν_support_P, hν_counting, h_final⟩

/-- A (δ,2s)-regular planar set admits a probability measure with bounded
    2κ-Riesz energy. This is the H3 axiom for Kaufman projection.
    Wrapper around `regular_set_has_bounded_energy_with_card` that discards
    the cardinal equality and per-cube uniqueness. -/
theorem regular_set_has_bounded_energy
    {δ s κ C : ℝ}
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hs : 0 < s) (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hκ_pos : 0 < κ) (hκ_lt_s : κ < s)
    (hP : IsDeltaSCSet δ (2 * s) C P)
    (hP_bdd : Bornology.IsBounded P) (hP_nonempty : P.Nonempty)
    (hP_lower : ENNReal.ofReal (δ ^ (-2*κ)) ≤ Nplane δ P) :
    ∃ (S : Finset (EuclideanSpace ℝ (Fin 2)))
      (ν : Measure (EuclideanSpace ℝ (Fin 2))),
      S.Nonempty ∧
      IsDeltaDense δ S P ∧
      ν Set.univ = 1 ∧
      ν.support ⊆ P ∧
      (ν = ∑ p ∈ S, (1 / (S.card : ENNReal)) • Measure.dirac p) ∧
      rieszEnergy (2 * κ) (hδ := hδ_pos) ν ≤
        ENNReal.ofReal (energyBoundConstant C s κ) := by
  rcases regular_set_has_bounded_energy_with_card hs hδ_pos hδ_lt_one hκ_pos hκ_lt_s hP hP_bdd hP_nonempty hP_lower
    with ⟨S, ν, hS_nonempty, hS_dense, _h_card, _h_rep, hν_univ, hν_support_P, hν_counting, h_final⟩
  exact ⟨S, ν, hS_nonempty, hS_dense, hν_univ, hν_support_P, hν_counting, h_final⟩

/-- The energy bound constant is strictly positive. -/
lemma energyBoundConstant_pos {C s κ : ℝ} (hC_pos : 0 < C)
    (hκ_pos : 0 < κ) (hκ_lt_s : κ < s) :
    0 < energyBoundConstant C s κ := by
  have h1 : κ - s < 0 := by linarith
  have h2 : (2 : ℝ) ^ (2 * (κ - s)) < 1 := by
    have h3 : 2 * (κ - s) < 0 := by linarith
    have h4 : (2 : ℝ) ^ (2 * (κ - s)) < (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h3
    simpa using h4
  have h5 : 0 < 1 - (2 : ℝ) ^ (2 * (κ - s)) := by linarith
  have h6 : 0 < (2 : ℝ) ^ (2 * κ) := by positivity
  have h7 : 0 < 1 - (2 : ℝ) ^ (2 * (κ - s)) + (2 : ℝ) ^ (2 * κ) := by linarith
  have h8 : 0 < 9 * C * (1 - (2 : ℝ) ^ (2 * (κ - s)) + (2 : ℝ) ^ (2 * κ)) /
        (1 - (2 : ℝ) ^ (2 * (κ - s))) := by
    apply div_pos
    · positivity
    · exact h5
  dsimp only [energyBoundConstant]
  linarith

end robust_projection
