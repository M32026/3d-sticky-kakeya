module

public import MyLeanRepo.robust_kaufman_projection.Base
public import MyLeanRepo.robust_kaufman_projection.Helpers
public import MyLeanRepo.OSWPrelude

@[expose] public section

set_option maxHeartbeats 500000

/-!
# Hausdorff Content to δ-Set Extraction (1D)

Provides two key lemmas for the robust Kaufman projection proof:

1. `potential_weighted_frostman`: Bounded regularized energy implies a restricted
   measure with Frostman-type ball growth and mass ≥ 1/2.

2. `frostman_measure_to_deltaset`: Frostman measure on ℝ implies existence
   of a δ-set with IsDeltaSSet constant O(C/m) and Ncover lower bound O(m/(C·δ^s)).

The extraction uses the cumulative distribution function (CDF) of a Frostman
measure on ℝ. If μ(B(x,r)) ≤ C·r^s for r ≥ δ/2, then the CDF
f(x) = μ((-∞,x]) is (C,s)-Hölder for gaps ≥ δ/2. Sampling the inverse CDF at
regular intervals gives a 3δ-separated set with controlled ball growth.

Whiteprint node: hausdorff_content_to_deltaset
Dependencies: basics, kernels_energy
-/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory Metric Set Finset Classical

namespace RobustKaufmanProjection.HausdorffContentToDeltaSet

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! ### Regularized kernel and energy -/

/-- Regularized kernel: K(d) = max(|d|, δ)^(-s). -/
def regularizedKernel (s δ : ℝ) (d : ℝ) : ENNReal :=
  ENNReal.ofReal ((max |d| δ) ^ (-s))

/-- Regularized energy: ∫∫ K(x-y) dν(x) dν(y). -/
def regularizedEnergy (ν : Measure ℝ) (s δ : ℝ) : ENNReal :=
  ∫⁻ x, ∫⁻ y, regularizedKernel s δ (x - y) ∂ν ∂ν

/-! ### CDF-based extraction from Frostman measure on ℝ -/

/-- Extract a 3δ-separated δ-set from a Frostman measure on ℝ using the CDF method.

    Given μ with μ(B(x,r)) ≤ C·r^s for r ≥ δ/2 and μ(univ) = m > 0,
    extract P with:
    - IsDeltaSSet δ s (4 * C * 3^s / m) P
    - Ncover δ P ≥ m / (2 * C * 3^s * δ^s)
    - Ncover δ P = |P| (due to 3δ-separation)
    -/

lemma frostman_measure_to_deltaset
    {δ s C m : ℝ} {μ : Measure ℝ} {X : Set ℝ}
    (hδ : 0 < δ) (hs : 0 < s) (hC : 0 < C) (hm : 0 < m)
    (hX_bdd : X ⊆ Set.Icc (-100 : ℝ) 100)
    (hμ_support : μ.support ⊆ X)
    (hμ_mass : μ Set.univ = ENNReal.ofReal m)
    (h_ball : ∀ (x : ℝ) (r : ℝ), δ / 2 ≤ r →
      μ (closedBall x r) ≤ ENNReal.ofReal (C * r ^ s)) :
    ∃ (P : Set ℝ), P ⊆ X ∧
      IsDeltaSSet δ s (4 * C * 3 ^ s / m) P ∧
      ENNReal.ofReal (m / (2 * C * 3 ^ s * δ ^ s)) ≤ Ncover δ P := by
  have h_ne_top : ∀ (s : Set ℝ), μ s ≠ ⊤ := by
    intro s
    have h : μ s ≤ μ Set.univ := measure_mono (subset_univ _)
    rw [hμ_mass] at h
    exact ne_top_of_le_ne_top (by simp) h
  let f : ℝ → ℝ := fun x => (μ (Set.Iic x)).toReal
  have hf_nondec : Monotone f := by
    intro x y hxy
    have h : μ (Set.Iic x) ≤ μ (Set.Iic y) := measure_mono (Set.Iic_subset_Iic.mpr hxy)
    have h_b_fin : μ (Set.Iic y) ≠ ⊤ := h_ne_top _
    exact ENNReal.toReal_mono h_b_fin h
  have h_support_bounded : μ.support ⊆ Set.Icc (-100 : ℝ) 100 :=
    hμ_support.trans hX_bdd
  have h_disj : ∀ (x y : ℝ), x ≤ y → Disjoint (Set.Iic x) (Set.Ioc x y) := by
    intro x y _
    rw [Set.disjoint_left]
    intro z hz1 hz2
    simp only [Set.mem_Iic, Set.mem_Ioc] at hz1 hz2
    linarith
  have h_union : ∀ (x y : ℝ), x ≤ y → Set.Iic y = Set.Iic x ∪ Set.Ioc x y := by
    intro x y hxy
    ext z
    simp only [Set.mem_Iic, Set.mem_Ioc, Set.mem_union]
    constructor
    · intro h
      by_cases h' : z ≤ x
      · exact Or.inl h'
      · exact Or.inr ⟨by linarith, h⟩
    · rintro (h | h) <;> linarith
  have hf_holder : ∀ x y, x ≤ y → δ / 2 ≤ y - x →
      f y - f x ≤ C * (y - x) ^ s := by
    intro x y hxy hlen
    have h1 : μ (Set.Ioc x y) ≤ μ (closedBall x (y - x)) := by
      apply measure_mono
      intro z hz
      simp only [Set.mem_Ioc] at hz
      simpa [Real.dist_eq, abs_of_nonneg (show 0 ≤ z - x by linarith)] using hz.2
    have h2 : μ (Set.Ioc x y) ≤ ENNReal.ofReal (C * (y - x) ^ s) :=
      h1.trans (h_ball x (y - x) hlen)
    have h4 : μ (Set.Iic y) = μ (Set.Iic x) + μ (Set.Ioc x y) := by
      rw [h_union x y hxy, measure_union (h_disj x y hxy) measurableSet_Ioc]
    have h5 : (μ (Set.Iic y)).toReal = (μ (Set.Iic x)).toReal + (μ (Set.Ioc x y)).toReal := by
      rw [h4, ENNReal.toReal_add (h_ne_top _) (h_ne_top _)]
    have h3 : f y - f x = (μ (Set.Ioc x y)).toReal := by
      dsimp only [f]
      linarith
    rw [h3]
    have h_b_fin : (ENNReal.ofReal (C * (y - x) ^ s)) ≠ ⊤ := by simp
    have h62 : (μ (Set.Ioc x y)).toReal ≤ (ENNReal.ofReal (C * (y - x) ^ s)).toReal :=
      ENNReal.toReal_mono h_b_fin h2
    have h63 : (ENNReal.ofReal (C * (y - x) ^ s)).toReal = C * (y - x) ^ s := by
      simp [show 0 ≤ C * (y - x) ^ s by positivity]
    rw [h63] at h62
    exact h62
  have hf_top : f 100 = m := by
    have h_support_compl_null : μ (μ.supportᶜ) = 0 :=
      MeasureTheory.Measure.measure_compl_support (μ := μ)
    have h_sub : (Set.Iic (100 : ℝ))ᶜ ⊆ μ.supportᶜ := by
      intro x hx
      intro hsup
      have h3 : x ∈ Set.Icc (-100 : ℝ) 100 := h_support_bounded hsup
      have h4 : x ≤ 100 := (Set.mem_Icc.mp h3).2
      simp only [Set.mem_compl_iff, Set.mem_Iic] at hx
      linarith
    have h_compl_null : μ ((Set.Iic (100 : ℝ))ᶜ) = 0 :=
      measure_mono_null h_sub h_support_compl_null
    have h1 : μ Set.univ = μ (Set.Iic (100 : ℝ)) := by
      have h2 : Set.univ = Set.Iic (100 : ℝ) ∪ (Set.Iic (100 : ℝ))ᶜ := by simp
      rw [h2, measure_union disjoint_compl_right measurableSet_Iic.compl, h_compl_null]
      <;> simp
    dsimp only [f]
    rw [← h1, hμ_mass]
    have hm' : 0 ≤ m := by linarith
    simp [hm']
  have hf_bot : f (-101) = 0 := by
    have h_disj2 : Disjoint (Set.Iic (-101)) μ.support := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have h3 : x ∈ Set.Icc (-100 : ℝ) 100 := h_support_bounded hx2
      have h4 : -100 ≤ x := (Set.mem_Icc.mp h3).1
      have h5 : x ≤ -101 := hx1
      linarith
    have h1 : μ (Set.Iic (-101)) = 0 := by
      by_contra h
      have h_pos : 0 < μ (Set.Iic (-101)) := by positivity
      have h_nonempty : (Set.Iic (-101) ∩ μ.support).Nonempty :=
        Measure.nonempty_inter_support_of_pos h_pos
      have h_empty : (Set.Iic (-101) ∩ μ.support) = ∅ :=
        Set.disjoint_iff_inter_eq_empty.mp h_disj2
      rw [h_empty] at h_nonempty
      simp at h_nonempty
    dsimp only [f]
    rw [h1] <;> simp
  let step : ℝ := C * (3 * δ) ^ s
  have hstep_pos : 0 < step := by positivity
  let N : ℕ := Nat.floor (m / step)
  have h_m_step_nonneg : 0 ≤ m / step := by positivity
  have hN_def : (N : ℝ) ≤ m / step := Nat.floor_le h_m_step_nonneg
  have hN_pos' : m / step < (N : ℝ) + 1 := Nat.lt_floor_add_one (m / step)
  by_cases hN_zero : N = 0
  · -- N = 0: m < step. Pick one point from support.
    have h_support_nonempty : μ.support.Nonempty := by
      by_contra h
      have h' : μ.support = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      have h'' : μ = 0 :=
        (MeasureTheory.Measure.support_eq_empty_iff (μ := μ)).mp h'
      rw [h''] at hμ_mass
      simp at hμ_mass <;> linarith
    rcases h_support_nonempty with ⟨x0, hx0⟩
    let P : Set ℝ := {x0}
    have hP_sub : P ⊆ X := by simpa [P] using hμ_support hx0
    have hP_nonempty : P.Nonempty := ⟨x0, by simp [P]⟩
    have h_const_pos : 0 < 4 * C * 3 ^ s / m := by positivity
    have h_m_lt_step : m < step := by
      have h : m / step < 1 := by
        rw [hN_zero] at hN_pos' <;> linarith
      have h' : 0 < step := hstep_pos
      calc m
        = (m / step) * step := by field_simp [h'.ne'] <;> ring
      _ < 1 * step := by gcongr
      _ = step := by ring
    have h_main : IsDeltaSSet δ s (4 * C * 3 ^ s / m) P := by
      refine' ⟨hP_nonempty, hδ, h_const_pos, by linarith, _⟩
      intro z r hr
      let S := P ∩ closedBall z r
      have hS_sub_P : S ⊆ P := Set.inter_subset_left
      have hP_subsingleton : P.Subsingleton := Set.subsingleton_singleton
      have hS_subsingleton : S.Subsingleton := by
        intro x hx y hy
        exact hP_subsingleton (hS_sub_P hx) (hS_sub_P hy)
      have h1 : Ncover δ S ≤ 1 := by
        by_cases h_empty : S = ∅
        · rw [h_empty]; simp [Ncover]
        · have hS_eq : S = P := by
            have h : S.Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty
            rcases h with ⟨x, hx⟩
            have hxP : x ∈ P := hS_sub_P hx
            have h_x_eq : x = x0 := by simpa [P] using hxP
            have hS_single : S = {x0} := by
              ext y
              simp only [Set.mem_singleton_iff]
              constructor
              · intro hy
                have h_y_eq_x : y = x := hS_subsingleton hy hx
                exact h_y_eq_x.trans h_x_eq
              · intro hy
                rw [hy]
                have h_x0_in_S : x0 ∈ S := by
                  rw [← h_x_eq] <;> exact hx
                exact h_x0_in_S
            simpa [P] using hS_single
          rw [hS_eq]
          have h_eq : Ncover δ P = 1 := by
            simpa [P, Ncover] using Metric.externalCoveringNumber_singleton δ.toNNReal x0
          rw [h_eq] <;> norm_num
      have h5 : Ncover δ P = 1 := by
        simpa [P, Ncover] using Metric.externalCoveringNumber_singleton δ.toNNReal x0
      have h7 : 1 ≤ (4 * C * 3 ^ s / m) * r ^ s := by
        have h8 : m < C * (3 * δ) ^ s := by simpa [step] using h_m_lt_step
        have h9 : m ≤ 4 * C * (3 * δ) ^ s := by
          have h10 : 0 < C * (3 * δ) ^ s := by positivity
          linarith
        have h12 : (3 * δ) ^ s = (3 : ℝ) ^ s * δ ^ s := by
          rw [← Real.mul_rpow (by norm_num) (by linarith)] <;> ring
        have h13 : 1 ≤ (4 * C * (3 * δ) ^ s) / m := by
          rw [one_le_div (by positivity)] <;> exact h9
        have h14 : (4 * C * (3 * δ) ^ s) / m = (4 * C * 3 ^ s / m) * δ ^ s := by
          rw [h12] <;> field_simp [hm.ne'] <;> ring
        have h15 : 1 ≤ (4 * C * 3 ^ s / m) * δ ^ s := by
          rw [h14] at h13; exact h13
        have h16 : δ ^ s ≤ r ^ s := by gcongr
        calc 1
          ≤ (4 * C * 3 ^ s / m) * δ ^ s := h15
        _ ≤ (4 * C * 3 ^ s / m) * r ^ s := by gcongr
      have h_pos1 : 0 ≤ (4 * C * 3 ^ s / m) * r ^ s := by positivity
      have h17 : ENNReal.ofReal ((4 * C * 3 ^ s / m) * r ^ s) =
          ENNReal.ofReal (4 * C * 3 ^ s / m) * (ENNReal.ofReal r) ^ s := by
        have h_a : 0 ≤ 4 * C * 3 ^ s / m := by positivity
        have h_b : 0 ≤ r := by linarith
        have h_c : 0 ≤ r ^ s := Real.rpow_nonneg h_b s
        have h171 : ENNReal.ofReal ((4 * C * 3 ^ s / m) * r ^ s) =
            ENNReal.ofReal (4 * C * 3 ^ s / m) * ENNReal.ofReal (r ^ s) :=
          ENNReal.ofReal_mul h_a
        have h172 : ENNReal.ofReal (r ^ s) = (ENNReal.ofReal r) ^ s := by
          have hs' : 0 ≤ s := by linarith
          exact (ENNReal.ofReal_rpow_of_nonneg h_b hs').symm
        rw [h171, h172]
      have h18 : (1 : ENNReal) ≤ ENNReal.ofReal (4 * C * 3 ^ s / m) * (ENNReal.ofReal r) ^ s * Ncover δ P := by
        rw [h5, mul_one]
        rw [← h17]
        have h_one : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
        rw [h_one]
        have h_iff : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal ((4 * C * 3 ^ s / m) * r ^ s) ↔
            (1 : ℝ) ≤ (4 * C * 3 ^ s / m) * r ^ s :=
          ENNReal.ofReal_le_ofReal_iff h_pos1
        exact h_iff.mpr h7
      exact h1.trans h18
    have h_lower : ENNReal.ofReal (m / (2 * C * 3 ^ s * δ ^ s)) ≤ Ncover δ P := by
      have h10 : m < C * (3 * δ) ^ s := by simpa [step] using h_m_lt_step
      have h11 : (3 * δ) ^ s = (3 : ℝ) ^ s * δ ^ s := by
        rw [← Real.mul_rpow (by norm_num) (by linarith)] <;> ring
      have h12 : m ≤ 2 * C * 3 ^ s * δ ^ s := by
        have h121 : m < C * (3 * δ) ^ s := h10
        have h122 : C * (3 * δ) ^ s = C * 3 ^ s * δ ^ s := by rw [h11] <;> ring
        have h123 : m < C * 3 ^ s * δ ^ s := by rw [h122] at h121; exact h121
        have h124 : C * 3 ^ s * δ ^ s ≤ 2 * C * 3 ^ s * δ ^ s := by
          have h2 : (0 : ℝ) ≤ C * 3 ^ s * δ ^ s := by positivity
          linarith
        exact h123.le.trans h124
      have h13 : m / (2 * C * 3 ^ s * δ ^ s) ≤ 1 := by
        rw [div_le_one (by positivity)] <;> exact h12
      have h14 : Ncover δ P = 1 := by
        simpa [P, Ncover] using Metric.externalCoveringNumber_singleton δ.toNNReal x0
      rw [h14]
      have h15 : 0 ≤ m / (2 * C * 3 ^ s * δ ^ s) := by positivity
      have h16 : ENNReal.ofReal (m / (2 * C * 3 ^ s * δ ^ s)) ≤ ENNReal.ofReal (1 : ℝ) := by
        have h_iff : ENNReal.ofReal (m / (2 * C * 3 ^ s * δ ^ s)) ≤ ENNReal.ofReal (1 : ℝ) ↔
            m / (2 * C * 3 ^ s * δ ^ s) ≤ (1 : ℝ) :=
          ENNReal.ofReal_le_ofReal_iff (by norm_num)
        exact h_iff.mpr h13
      have h17 : ENNReal.ofReal (1 : ℝ) = (1 : ENNReal) := by simp
      rw [h17] at h16
      exact h16
    exact ⟨P, hP_sub, h_main, h_lower⟩
  · -- N ≥ 1
    have hN_pos : 0 < N := Nat.pos_of_ne_zero hN_zero
    let pts : ℕ → ℝ := fun i => sInf {x : ℝ | f x ≥ (i + 1 : ℝ) * step}
    have h_pts_def : ∀ i < N, ∃ (x : ℝ), f x ≥ (i + 1 : ℝ) * step := by
      intro i hi
      have h21 : i + 1 ≤ N := Nat.succ_le_iff.mpr hi
      have h22 : (i + 1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h21
      have h1 : (i + 1 : ℝ) * step ≤ m := by
        calc (i + 1 : ℝ) * step
          ≤ (N : ℝ) * step := by gcongr
        _ ≤ m := by
          have h3 : (N : ℝ) ≤ m / step := hN_def
          have h4 : (N : ℝ) * step ≤ m := by
            calc (N : ℝ) * step
              ≤ (m / step) * step := by gcongr
            _ = m := by field_simp [hstep_pos.ne'] <;> ring
          exact h4
      refine' ⟨100, _⟩
      rw [hf_top]
      exact h1
    have h_bounded : ∀ i, i < N → BddBelow {x : ℝ | f x ≥ (i + 1 : ℝ) * step} := by
      intro i _
      refine' ⟨-101, fun x hx => _⟩
      have h5 : f x ≥ (i + 1 : ℝ) * step := by simpa using hx
      by_contra h
      have h' : x ≤ -101 := by linarith
      have h'' : f x ≤ f (-101) := hf_nondec h'
      rw [hf_bot] at h''
      have h4 : 0 < (i + 1 : ℝ) * step := by positivity
      linarith
    have h_above : ∀ i, i < N → ∀ ε : ℝ, 0 < ε →
        f (pts i + ε) ≥ (i + 1 : ℝ) * step := by
      intro i hi ε hε
      let S := {x : ℝ | f x ≥ (i + 1 : ℝ) * step}
      have hS_nonempty : S.Nonempty := h_pts_def i hi
      have h_inf : ∃ x ∈ S, x < pts i + ε := by
        by_contra h
        push Not at h
        have h' : pts i + ε ≤ pts i := le_csInf hS_nonempty h
        linarith
      rcases h_inf with ⟨x, hxS, hx_lt⟩
      have h_x_le : x ≤ pts i + ε := by linarith
      have h : f (pts i + ε) ≥ f x := hf_nondec h_x_le
      have h_result : f (pts i + ε) ≥ (i + 1 : ℝ) * step := by
        calc f (pts i + ε) ≥ f x := h
             _ ≥ (i + 1 : ℝ) * step := hxS
      exact h_result
    have h_below : ∀ i, i < N → ∀ ε : ℝ, 0 < ε →
        f (pts i - ε) < (i + 1 : ℝ) * step := by
      intro i hi ε hε
      let S := {x : ℝ | f x ≥ (i + 1 : ℝ) * step}
      have h_bdd : BddBelow S := h_bounded i hi
      have h : pts i - ε ∉ S := by
        intro h_contra
        have h' : pts i ≤ pts i - ε := csInf_le h_bdd h_contra
        linarith
      simpa [S] using h
    have h_mono_pts : ∀ i j, i ≤ j → i < N → j < N → pts i ≤ pts j := by
      intro i j hij hi hj
      let S_i := {x : ℝ | f x ≥ (i + 1 : ℝ) * step}
      let S_j := {x : ℝ | f x ≥ (j + 1 : ℝ) * step}
      have h_sub : S_j ⊆ S_i := by
        intro x hx
        have h : (i + 1 : ℝ) * step ≤ (j + 1 : ℝ) * step := by gcongr
        exact h.trans hx
      have hSi_nonempty : S_i.Nonempty := h_pts_def i hi
      have hSj_nonempty : S_j.Nonempty := h_pts_def j hj
      have h : pts i ≤ pts j := by
        apply le_csInf hSj_nonempty
        intro x hx
        have h_x_in_Si : x ∈ S_i := h_sub hx
        have h_bdd_i : BddBelow S_i := h_bounded i hi
        exact csInf_le h_bdd_i h_x_in_Si
      exact h
    have h_gap : ∀ i j, i < N → j < N → i < j →
        (j - i : ℝ) * step ≤ C * (pts j - pts i) ^ s := by
      intro i j hi hj hlt
      have h1 : ∀ ε : ℝ, 0 < ε →
          f (pts j + ε) - f (pts i - ε) > (j - i : ℝ) * step := by
        intro ε hε
        have h2 : f (pts j + ε) ≥ (j + 1 : ℝ) * step := h_above j hj ε hε
        have h3 : f (pts i - ε) < (i + 1 : ℝ) * step := h_below i hi ε hε
        linarith
      have h_ge_delta2 : δ / 2 ≤ pts j - pts i := by
        by_contra h
        have h_lt : pts j - pts i < δ / 2 := by linarith
        let ε := (δ / 2 - (pts j - pts i)) / 4
        have hε_pos : 0 < ε := by positivity
        have h_len : pts j - pts i + 2 * ε < δ / 2 := by
          simp [ε] <;> linarith
        have h4 : Set.Ioc (pts i - ε) (pts j + ε) ⊆ closedBall (pts i - ε) (δ / 2) := by
          intro z hz
          simp only [Set.mem_Ioc] at hz
          have h5 : dist z (pts i - ε) ≤ δ / 2 := by
            have h6 : 0 ≤ z - (pts i - ε) := by linarith
            have h8 : z - (pts i - ε) < δ / 2 := by linarith
            have h9 : dist z (pts i - ε) = z - (pts i - ε) := by
              rw [Real.dist_eq, abs_of_nonneg h6]
            rw [h9]
            exact le_of_lt h8
          exact h5
        have h6 : μ (Set.Ioc (pts i - ε) (pts j + ε)) ≤ ENNReal.ofReal (C * (δ / 2) ^ s) :=
          (measure_mono h4).trans (h_ball (pts i - ε) (δ / 2) (by linarith))
        have h7 : f (pts j + ε) - f (pts i - ε) =
            (μ (Set.Ioc (pts i - ε) (pts j + ε))).toReal := by
          have h8 : μ (Set.Iic (pts j + ε)) =
              μ (Set.Iic (pts i - ε)) + μ (Set.Ioc (pts i - ε) (pts j + ε)) := by
            have h_ord : pts i - ε ≤ pts j + ε := by
              have h_mono : pts i ≤ pts j := h_mono_pts i j (by linarith) hi hj
              linarith
            rw [h_union (pts i - ε) (pts j + ε) h_ord,
              measure_union (h_disj (pts i - ε) (pts j + ε) h_ord) measurableSet_Ioc]
          have h9 : (μ (Set.Iic (pts j + ε))).toReal =
              (μ (Set.Iic (pts i - ε))).toReal +
              (μ (Set.Ioc (pts i - ε) (pts j + ε))).toReal := by
            rw [h8, ENNReal.toReal_add (h_ne_top _) (h_ne_top _)]
          dsimp only [f] at *
          <;> linarith
        have h81 : (μ (Set.Ioc (pts i - ε) (pts j + ε))).toReal ≤ (ENNReal.ofReal (C * (δ / 2) ^ s)).toReal :=
          ENNReal.toReal_mono (by simp) h6
        have h82 : (ENNReal.ofReal (C * (δ / 2) ^ s)).toReal = C * (δ / 2) ^ s := by
          rw [ENNReal.toReal_ofReal] <;> positivity
        have h8 : f (pts j + ε) - f (pts i - ε) ≤ C * (δ / 2) ^ s := by
          rw [h7]
          rw [h82] at h81
          exact h81
        have h9 : (j - i : ℝ) ≥ 1 := by
          have h10 : i + 1 ≤ j := by omega
          have h11 : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h10
          have h12 : (j : ℝ) - (i : ℝ) ≥ 1 := by linarith
          exact h12
        have h10 : step ≤ (j - i : ℝ) * step := by
          have h11 : 1 ≤ (j - i : ℝ) := h9
          calc step
            = 1 * step := by ring
          _ ≤ (j - i : ℝ) * step := by gcongr
        have h12 : step ≤ f (pts j + ε) - f (pts i - ε) := by
          calc step
            ≤ (j - i : ℝ) * step := h10
          _ ≤ f (pts j + ε) - f (pts i - ε) := by linarith [h1 ε hε_pos]
        have h11 : C * (δ / 2) ^ s < step := by
          have h12 : (δ / 2) ^ s < (3 * δ) ^ s := by
            apply Real.rpow_lt_rpow
            <;> linarith
          have h13 : C * (δ / 2) ^ s < C * (3 * δ) ^ s := by gcongr
          simpa [step] using h13
        linarith
      have h_main : ∀ ε : ℝ, 0 < ε →
          (j - i : ℝ) * step < C * (pts j - pts i + 2 * ε) ^ s := by
        intro ε hε
        have h_len : δ / 2 ≤ pts j - pts i + 2 * ε := by linarith
        have h5 : pts i - ε ≤ pts j + ε := by
          have h6 : pts i ≤ pts j := h_mono_pts i j (by linarith) hi hj
          linarith
        have h_len' : δ / 2 ≤ pts j + ε - (pts i - ε) := by
          have h_eq : pts j + ε - (pts i - ε) = pts j - pts i + 2 * ε := by ring
          rw [h_eq]
          exact h_len
        have h7 : f (pts j + ε) - f (pts i - ε) ≤
            C * (pts j - pts i + 2 * ε) ^ s := by
          have h71 := hf_holder (pts i - ε) (pts j + ε) h5 h_len'
          have h_eq : (pts j + ε - (pts i - ε)) = pts j - pts i + 2 * ε := by ring
          rw [h_eq] at h71
          exact h71
        have h8 : f (pts j + ε) - f (pts i - ε) > (j - i : ℝ) * step := h1 ε hε
        linarith
      by_contra h9
      have h10 : C * (pts j - pts i) ^ s < (j - i : ℝ) * step := by linarith
      have hs' : 0 ≤ s := by linarith
      have h11 : Continuous (fun ε : ℝ => C * (pts j - pts i + 2 * ε) ^ s) := by
        fun_prop <;> exact hs'
      have h12 : ∃ ε : ℝ, 0 < ε ∧ C * (pts j - pts i + 2 * ε) ^ s < (j - i : ℝ) * step := by
        have h13 : ContinuousAt (fun ε : ℝ => C * (pts j - pts i + 2 * ε) ^ s) 0 := h11.continuousAt
        have h14 : (fun ε : ℝ => C * (pts j - pts i + 2 * ε) ^ s) 0 < (j - i : ℝ) * step := by
          have h15 : (fun ε : ℝ => C * (pts j - pts i + 2 * ε) ^ s) 0 = C * (pts j - pts i) ^ s := by simp
          rw [h15]
          exact h10
        have h15 : ∀ᶠ (x : ℝ) in nhds 0, C * (pts j - pts i + 2 * x) ^ s < (j - i : ℝ) * step :=
          h13.eventually (gt_mem_nhds h14)
        have h15' : ∃ (δ' : ℝ), 0 < δ' ∧ ∀ (x : ℝ), dist x (0 : ℝ) < δ' →
            C * (pts j - pts i + 2 * x) ^ s < (j - i : ℝ) * step := by
          have h_set : {x : ℝ | C * (pts j - pts i + 2 * x) ^ s < (j - i : ℝ) * step} ∈ nhds (0 : ℝ) := h15
          have h2 : ∃ (δ' : ℝ), 0 < δ' ∧ Metric.ball (0 : ℝ) δ' ⊆
              {x : ℝ | C * (pts j - pts i + 2 * x) ^ s < (j - i : ℝ) * step} :=
            Metric.mem_nhds_iff.mp h_set
          rcases h2 with ⟨δ', hδ'_pos, h_sub⟩
          refine' ⟨δ', hδ'_pos, _⟩
          intro x hx
          have h_in : x ∈ {x : ℝ | C * (pts j - pts i + 2 * x) ^ s < (j - i : ℝ) * step} := h_sub hx
          exact h_in
        rcases h15' with ⟨δ', hδ'_pos, h16⟩
        let ε := δ' / 2
        have hε_pos : 0 < ε := by positivity
        have h17 : dist ε 0 < δ' := by
          have h18 : dist ε 0 = |ε| := by simp [Real.dist_eq]
          have h19 : |ε| = ε := abs_of_pos hε_pos
          have h20 : dist ε 0 = ε := by rw [h18, h19]
          rw [h20]
          dsimp only [ε]
          linarith
        have h18 : C * (pts j - pts i + 2 * ε) ^ s < (j - i : ℝ) * step := h16 ε h17
        exact ⟨ε, hε_pos, h18⟩
      rcases h12 with ⟨ε, hε, h13⟩
      have h14 := h_main ε hε
      linarith
    have h_sep : ∀ i j, i < N → j < N → i ≠ j → 3 * δ ≤ |pts i - pts j| := by
      intro i j hi hj hne
      have h_lt_or_gt : i < j ∨ j < i := by omega
      rcases h_lt_or_gt with (h_ij | h_ji)
      · -- i < j
        have h1 : (j - i : ℝ) * step ≤ C * (pts j - pts i) ^ s := h_gap i j hi hj h_ij
        have h2 : (j - i : ℝ) ≥ 1 := by
          have h3 : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr h_ij)
          linarith
        have h3 : step ≤ C * (pts j - pts i) ^ s := by
          calc step
            = 1 * step := by ring
          _ ≤ (j - i : ℝ) * step := by gcongr
          _ ≤ C * (pts j - pts i) ^ s := h1
        have h4 : (3 * δ) ^ s ≤ (pts j - pts i) ^ s := by
          have h5 : C * (3 * δ) ^ s ≤ C * (pts j - pts i) ^ s := by simpa [step] using h3
          have hC_pos : 0 < C := hC
          exact (mul_le_mul_iff_of_pos_left hC_pos).mp h5
        have h5 : 0 ≤ pts j - pts i := by
          have h6 : pts i ≤ pts j := h_mono_pts i j (by linarith) hi hj
          linarith
        have h7 : 3 * δ ≤ pts j - pts i := by
          have h8 : (3 * δ) ^ s ≤ (pts j - pts i) ^ s := h4
          have h9 : 0 ≤ 3 * δ := by positivity
          exact (Real.rpow_le_rpow_iff h9 h5 hs).mp h8
        have h10 : |pts i - pts j| = pts j - pts i := by
          rw [abs_sub_comm, abs_of_nonneg h5]
        rw [h10]
        exact h7
      · -- j < i
        have h1 : (i - j : ℝ) * step ≤ C * (pts i - pts j) ^ s := h_gap j i hj hi h_ji
        have h2 : (i - j : ℝ) ≥ 1 := by
          have h3 : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr h_ji)
          linarith
        have h3 : step ≤ C * (pts i - pts j) ^ s := by
          calc step
            = 1 * step := by ring
          _ ≤ (i - j : ℝ) * step := by gcongr
          _ ≤ C * (pts i - pts j) ^ s := h1
        have h4 : (3 * δ) ^ s ≤ (pts i - pts j) ^ s := by
          have h5 : C * (3 * δ) ^ s ≤ C * (pts i - pts j) ^ s := by simpa [step] using h3
          have hC_pos : 0 < C := hC
          exact (mul_le_mul_iff_of_pos_left hC_pos).mp h5
        have h5 : 0 ≤ pts i - pts j := by
          have h6 : pts j ≤ pts i := h_mono_pts j i (by linarith) hj hi
          linarith
        have h7 : 3 * δ ≤ pts i - pts j := by
          have h8 : (3 * δ) ^ s ≤ (pts i - pts j) ^ s := h4
          have h9 : 0 ≤ 3 * δ := by positivity
          exact (Real.rpow_le_rpow_iff h9 h5 hs).mp h8
        have h10 : |pts i - pts j| = pts i - pts j := by
          rw [abs_of_nonneg h5]
        rw [h10]
        exact h7
    have h_in_support : ∀ i < N, pts i ∈ μ.support := by
      intro i hi
      by_contra h
      have h5 : ∃ ε > 0, μ (closedBall (pts i) ε) = 0 := by
        have h_not_in : pts i ∉ μ.support := h
        have h6 : ∃ (U : Set ℝ), U ∈ nhds (pts i) ∧ μ U = 0 :=
          (MeasureTheory.Measure.notMem_support_iff_exists).mp h_not_in
        rcases h6 with ⟨U, hU_nhds, hU_null⟩
        have h7 : ∃ ε > 0, Metric.ball (pts i) ε ⊆ U := Metric.mem_nhds_iff.mp hU_nhds
        rcases h7 with ⟨ε, hε_pos, h_sub⟩
        let ε' := ε / 2
        have hε'_pos : 0 < ε' := by positivity
        have h8 : closedBall (pts i) ε' ⊆ Metric.ball (pts i) ε := by
          intro z hz
          have h9 : dist z (pts i) ≤ ε' := by simpa [mem_closedBall] using hz
          have h10 : ε' < ε := by simp [ε'] <;> linarith
          have h11 : dist z (pts i) < ε := by linarith
          simpa [Metric.mem_ball] using h11
        have h9 : closedBall (pts i) ε' ⊆ U := h8.trans h_sub
        exact ⟨ε', hε'_pos, measure_mono_null h9 hU_null⟩
      rcases h5 with ⟨ε, hε_pos, hμ_ball⟩
      let ε' := ε / 2
      have hε'_pos : 0 < ε' := by positivity
      have h6 : μ (Set.Ioc (pts i - ε') (pts i + ε')) = 0 := by
        apply measure_mono_null _ hμ_ball
        intro z hz
        have hz' : z ∈ Set.Ioc (pts i - ε') (pts i + ε') := hz
        have h_in : dist z (pts i) ≤ ε' := by
          have h1 : pts i - ε' < z := hz'.1
          have h2 : z ≤ pts i + ε' := hz'.2
          have h3 : |z - pts i| ≤ ε' := by
            rw [abs_le] <;> constructor <;> linarith
          simpa [Real.dist_eq] using h3
        have h4 : ε' ≤ ε := by simp [ε'] <;> linarith
        have h5 : dist z (pts i) ≤ ε := h_in.trans h4
        simpa [mem_closedBall] using h5
      have h7 : f (pts i + ε') = f (pts i - ε') := by
        have h8 : μ (Set.Iic (pts i + ε')) =
            μ (Set.Iic (pts i - ε')) + μ (Set.Ioc (pts i - ε') (pts i + ε')) := by
          rw [h_union (pts i - ε') (pts i + ε') (by linarith),
            measure_union (h_disj (pts i - ε') (pts i + ε') (by linarith)) measurableSet_Ioc]
        dsimp only [f]
        rw [h8, h6] <;> simp
      have h9 : f (pts i + ε') ≥ (i + 1 : ℝ) * step := h_above i hi ε' hε'_pos
      have h10 : f (pts i - ε') < (i + 1 : ℝ) * step := h_below i hi ε' hε'_pos
      rw [h7] at h9
      linarith
    let P : Set ℝ := (Finset.range N : Set ℕ).image pts
    have hP_sub : P ⊆ X := by
      intro y hy
      rcases hy with ⟨i, hi, rfl⟩
      exact hμ_support (h_in_support i (Finset.mem_range.mp hi))
    have hP_finite : P.Finite := (Finset.range N).finite_toSet.image _
    let P' : Finset ℝ := hP_finite.toFinset
    have hP'_eq : (P' : Set ℝ) = P := hP_finite.coe_toFinset
    have hP'_image : P' = Finset.image pts (Finset.range N) := by
      apply Finset.coe_inj.mp
      rw [hP'_eq]
      simp [P, Finset.coe_image]
      <;> rfl
    have h_inj : Set.InjOn pts (Finset.range N : Set ℕ) := by
      intro i hi j hj h
      by_contra hne
      have h5 : 3 * δ ≤ |pts i - pts j| := h_sep i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hne
      have h7 : |pts i - pts j| = 0 := by
        have h6 : pts i = pts j := h
        rw [h6] <;> simp
      rw [h7] at h5
      <;> linarith
    have h_card : P'.card = N := by
      rw [hP'_image, Finset.card_image_of_injOn h_inj]
      <;> simp
    have hP_sep' : ∀ (x : ℝ), x ∈ P → ∀ (y : ℝ), y ∈ P → x ≠ y →
        (2 * δ : ℝ) < dist x y := by
      intro x hx y hy hne
      rcases hx with ⟨i, hi, rfl⟩
      rcases hy with ⟨j, hj, rfl⟩
      have h_ij : i ≠ j := by
        intro h
        apply hne
        rw [h]
      have h5 : 3 * δ ≤ |pts i - pts j| := h_sep i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h_ij
      have h6 : (2 * δ : ℝ) < |pts i - pts j| := by linarith
      simpa [Real.dist_eq] using h6
    let ε : NNReal := δ.toNNReal
    have hε_pos : 0 < ε := by
      have hδ' : 0 ≤ δ := by linarith
      have h_coe : (ε : ℝ) = δ := by
        simp [ε] <;> norm_cast <;> linarith
      have h' : (0 : ℝ) < (ε : ℝ) := by
        rw [h_coe] <;> exact hδ
      exact NNReal.coe_pos.mp h'
    have h_is_sep : Metric.IsSeparated (2 * ε) P := by
      intro x hx y hy hne
      have h : (2 * δ : ℝ) < dist x y := hP_sep' x hx y hy hne
      have h2 : (↑(2 * ε) : ℝ) = 2 * δ := by
        simp [ε, NNReal.coe_mk] <;> norm_cast <;> linarith
      have h' : (↑(2 * ε) : ENNReal) < edist x y := by
        have h3 : (↑(2 * ε) : ENNReal) = ENNReal.ofReal (↑(2 * ε) : ℝ) := by
          rw [← ENNReal.ofReal_coe_nnreal] <;> rfl
        rw [h3, edist_dist]
        have h4 : (↑(2 * ε) : ℝ) = 2 * δ := h2
        rw [h4]
        exact ENNReal.ofReal_lt_ofReal_iff (by linarith) |>.mpr h
      exact h'
    have h_encard : P.encard = ↑N := by
      have h1 : P.encard = ↑(P'.card) := hP_finite.encard_eq_coe_toFinset_card
      have h2 : (↑(P'.card) : ENat) = (↑N : ENat) := by
        rw [h_card]
      rw [h1, h2]
    have h_ncover : Ncover δ P = ↑N := by
      let ε := δ.toNNReal
      have h3 : P.encard ≤ Metric.packingNumber (2 * ε) P :=
        Metric.IsSeparated.encard_le_packingNumber (Set.Subset.refl P) h_is_sep
      have h4 : Metric.packingNumber (2 * ε) P ≤ Metric.externalCoveringNumber ε P :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber ε P
      have h5 : Metric.externalCoveringNumber ε P ≤ P.encard :=
        Metric.externalCoveringNumber_le_encard_self P
      have h6 : Metric.externalCoveringNumber ε P = P.encard :=
        le_antisymm h5 (h3.trans h4)
      have h7 : Metric.externalCoveringNumber ε P = (↑N : ENNReal) := by
        rw [h6, h_encard] <;> simp
      have h_eq : Ncover δ P = Metric.externalCoveringNumber ε P := by rfl
      rw [h_eq]
      exact h7
    have h_step_eq : step = C * 3 ^ s * δ ^ s := by
      have h1 : (3 * δ) ^ s = (3 : ℝ) ^ s * δ ^ s := by
        rw [← Real.mul_rpow (by norm_num) (by linarith)] <;> ring
      simp [step, h1] <;> ring
    have h_N_lower : (m / (2 * C * 3 ^ s * δ ^ s)) ≤ (N : ℝ) := by
      have h_eq1 : m / (2 * C * 3 ^ s * δ ^ s) = (m / step) / 2 := by
        rw [h_step_eq]
        field_simp [hC.ne', hδ.ne'] <;> ring
      rw [h_eq1]
      by_cases h : N = 1
      · -- N = 1
        rw [h]
        have h' : m / step < 2 := by
          rw [h] at hN_pos' <;> linarith
        have h'' : (m / step) / 2 ≤ (1 : ℝ) := by linarith
        exact_mod_cast h''
      · -- N ≠ 1, so N ≥ 2 (since N > 0)
        have hN_ge2 : 2 ≤ N := by omega
        have h_ge2 : 2 ≤ m / step := by
          by_contra h2
          have h3 : m / step < 2 := by linarith
          have h4 : (N : ℝ) < 2 := by linarith [hN_pos']
          have h5 : N < 2 := by exact_mod_cast h4
          omega
        have h_le : (m / step) / 2 ≤ m / step - 1 := by linarith
        have h_lt : m / step - 1 < (N : ℝ) := by linarith [hN_pos']
        have h6 : (m / step) / 2 < (N : ℝ) := lt_of_le_of_lt h_le h_lt
        exact le_of_lt h6
    have h_growth : ∀ (z : ℝ) (r : ℝ), δ ≤ r →
        (P'.filter (fun x => dist x z ≤ r)).card ≤
          (2 : ℝ) * r ^ s / δ ^ s := by
      intro z r hr
      set S : Finset ℝ := P'.filter (fun x => dist x z ≤ r) with hS_def
      have hS_sub : (S : Set ℝ) ⊆ closedBall z r := by
        intro x hx
        have h2 : dist x z ≤ r := (Finset.mem_filter.mp hx).2
        simpa [mem_closedBall] using h2
      by_cases hS_empty : S = ∅
      · have hr_pos : 0 < r := by linarith
        have h_goal : (0 : ℝ) ≤ 2 * r ^ s / δ ^ s := by
          apply div_nonneg
          · positivity
          · positivity
        rw [hS_empty]
        simpa using h_goal
      · have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
        let I : Finset ℕ := (Finset.range N).filter (fun i => pts i ∈ S)
        have hI_sub : I ⊆ Finset.range N := Finset.filter_subset _ _
        have hI_eq : I.image pts = S := by
          ext x
          simp only [Finset.mem_image]
          constructor
          · rintro ⟨i, hi, rfl⟩
            exact (Finset.mem_filter.mp hi).2
          · intro hx
            have h_x_in_P' : x ∈ P' := (Finset.mem_filter.mp hx).1
            have h_x_in_P : x ∈ P := by
              rw [← hP'_eq] <;> exact h_x_in_P'
            rcases h_x_in_P with ⟨i, hi, h_eq⟩
            have h_i_in_I : i ∈ I := by
              rw [Finset.mem_filter]
              have h_pts_in_S : pts i ∈ S := by rw [h_eq] <;> exact hx
              exact ⟨hi, h_pts_in_S⟩
            exact ⟨i, h_i_in_I, h_eq⟩
        have h_inj_I : Set.InjOn pts (I : Set ℕ) := h_inj.mono (Finset.coe_subset.mpr hI_sub)
        have hI_card : I.card = S.card := by
          have h : (I.image pts).card = I.card := Finset.card_image_of_injOn (H := h_inj_I)
          rw [hI_eq] at h
          exact h.symm
        have hI_nonempty : I.Nonempty := by
          rcases hS_nonempty with ⟨x, hx⟩
          have h_x_in_P' : x ∈ P' := (Finset.mem_filter.mp hx).1
          have h_x_in_P : x ∈ P := by
            rw [← hP'_eq] <;> exact h_x_in_P'
          rcases h_x_in_P with ⟨i, hi, h_eq⟩
          have h_i_in_I : i ∈ I := by
            rw [Finset.mem_filter]
            have h_pts_in_S : pts i ∈ S := by rw [h_eq] <;> exact hx
            exact ⟨hi, h_pts_in_S⟩
          exact ⟨i, h_i_in_I⟩
        let i_min := I.min' hI_nonempty
        let i_max := I.max' hI_nonempty
        have h_min_in : i_min ∈ I := Finset.min'_mem I hI_nonempty
        have h_max_in : i_max ∈ I := Finset.max'_mem I hI_nonempty
        have h_min_in_range : i_min ∈ Finset.range N := (Finset.mem_filter.mp h_min_in).1
        have h_max_in_range : i_max ∈ Finset.range N := (Finset.mem_filter.mp h_max_in).1
        have h_pts_min_in : pts i_min ∈ S := (Finset.mem_filter.mp h_min_in).2
        have h_pts_max_in : pts i_max ∈ S := (Finset.mem_filter.mp h_max_in).2
        have h_min_le_max : i_min ≤ i_max := Finset.min'_le I i_max h_max_in
        rcases eq_or_lt_of_le h_min_le_max with (h_eq | h_lt)
        · -- S has exactly 1 point
          have h1 : S.card = 1 := by
            have h2 : I = {i_min} := by
              apply Finset.eq_singleton_iff_unique_mem.mpr
              constructor
              · exact h_min_in
              · intro k hk
                have h3 : i_min ≤ k := Finset.min'_le I k hk
                have h4 : k ≤ i_max := Finset.le_max' I k hk
                have h5 : k ≤ i_min := by
                  have h6 : i_max = i_min := h_eq.symm
                  rw [h6] at h4
                  exact h4
                exact le_antisymm h5 h3
            have h3 : I.card = 1 := by rw [h2] <;> simp
            have h4 : S.card = 1 := by
              rw [← hI_card, h3]
            rw [h4]
          rw [h1]
          have hδs_pos : 0 < δ ^ s := Real.rpow_pos_of_pos hδ s
          have h3 : δ ^ s ≤ r ^ s := by gcongr
          have h4 : 1 ≤ r ^ s / δ ^ s := by
            rw [one_le_div hδs_pos] <;> exact h3
          have h5 : 1 ≤ 2 * (r ^ s / δ ^ s) := by
            have h6 : 0 ≤ r ^ s / δ ^ s := by positivity
            linarith [h4]
          have h5' : 1 ≤ 2 * r ^ s / δ ^ s := by
            have h_eq : 2 * r ^ s / δ ^ s = 2 * (r ^ s / δ ^ s) := by ring
            rw [h_eq]
            exact h5
          exact_mod_cast h5'
        · -- S has at least 2 distinct points
          have h_pos : 0 ≤ pts i_max - pts i_min := by
            have h : pts i_min ≤ pts i_max := h_mono_pts i_min i_max (by omega)
              (Finset.mem_range.mp h_min_in_range) (Finset.mem_range.mp h_max_in_range)
            linarith
          have h_sep_dist : 3 * δ ≤ pts i_max - pts i_min := by
            have h_sep2 : 3 * δ ≤ |pts i_max - pts i_min| :=
              h_sep i_max i_min (Finset.mem_range.mp h_max_in_range)
                (Finset.mem_range.mp h_min_in_range) (by omega)
            simpa [abs_of_nonneg h_pos] using h_sep2
          have h_ge : δ / 2 ≤ pts i_max - pts i_min := by
            have h_goal : δ / 2 ≤ 3 * δ := by linarith [hδ]
            exact h_goal.trans h_sep_dist
          have h1 : ∀ ε : ℝ, 0 < ε →
              f (pts i_max + ε) - f (pts i_min - ε) > (i_max - i_min : ℝ) * step := by
            intro ε hε
            have h2 : f (pts i_max + ε) ≥ (i_max + 1 : ℝ) * step :=
              h_above i_max (Finset.mem_range.mp h_max_in_range) ε hε
            have h3 : f (pts i_min - ε) < (i_min + 1 : ℝ) * step :=
              h_below i_min (Finset.mem_range.mp h_min_in_range) ε hε
            linarith
          have h_main : ∀ ε : ℝ, 0 < ε →
              (i_max - i_min : ℝ) * step < C * (pts i_max - pts i_min + 2 * ε) ^ s := by
            intro ε hε
            have h_len : δ / 2 ≤ pts i_max - pts i_min + 2 * ε := by linarith
            have h5 : pts i_min - ε ≤ pts i_max + ε := by linarith
            have h_len' : δ / 2 ≤ (pts i_max + ε) - (pts i_min - ε) := by
              have h_eq : (pts i_max + ε) - (pts i_min - ε) = pts i_max - pts i_min + 2 * ε := by ring
              rw [h_eq]
              exact h_len
            have h7 : f (pts i_max + ε) - f (pts i_min - ε) ≤
                C * ((pts i_max + ε) - (pts i_min - ε)) ^ s := hf_holder (pts i_min - ε) (pts i_max + ε) h5 h_len'
            have h_eq2 : (pts i_max + ε) - (pts i_min - ε) = pts i_max - pts i_min + 2 * ε := by ring
            rw [h_eq2] at h7
            linarith [h1 ε hε]
          have h_limit : (i_max - i_min : ℝ) * step ≤ C * (pts i_max - pts i_min) ^ s := by
            by_contra h9
            have h10 : C * (pts i_max - pts i_min) ^ s < (i_max - i_min : ℝ) * step := not_le.mp h9
            have h_base_pos : 0 < pts i_max - pts i_min := by linarith [h_sep_dist]
            have h_cont : Continuous (fun ε : ℝ => pts i_max - pts i_min + 2 * ε) := by fun_prop
            have h11 : ContinuousAt (fun ε : ℝ => C * (pts i_max - pts i_min + 2 * ε) ^ s) 0 := by
              have h_rpow : ContinuousAt (fun ε : ℝ => (pts i_max - pts i_min + 2 * ε) ^ s) 0 :=
                h_cont.continuousAt.rpow_const (Or.inr hs.le)
              exact continuousAt_const.mul h_rpow
            have h14 : (fun ε : ℝ => C * (pts i_max - pts i_min + 2 * ε) ^ s) 0 < (i_max - i_min : ℝ) * step := by
              have h15 : (fun ε : ℝ => C * (pts i_max - pts i_min + 2 * ε) ^ s) 0 = C * (pts i_max - pts i_min) ^ s := by simp
              rw [h15]
              exact h10
            have h15 : ∀ᶠ (x : ℝ) in nhds 0, C * (pts i_max - pts i_min + 2 * x) ^ s < (i_max - i_min : ℝ) * step :=
              h11.eventually (gt_mem_nhds h14)
            have h16 : ∃ (δ' : ℝ), 0 < δ' ∧ Metric.ball (0 : ℝ) δ' ⊆ {x : ℝ | C * (pts i_max - pts i_min + 2 * x) ^ s < (i_max - i_min : ℝ) * step} :=
              Metric.mem_nhds_iff.mp h15
            rcases h16 with ⟨δ', hδ'_pos, h_sub⟩
            let ε' := δ' / 2
            have hε'_pos : 0 < ε' := by positivity
            have hε'_ball : ε' ∈ Metric.ball (0 : ℝ) δ' := by
              have h : dist ε' 0 < δ' := by
                have h2 : dist ε' 0 = ε' := by
                  rw [Real.dist_eq]
                  have h3 : |ε' - 0| = ε' := by
                    have h4 : ε' - 0 = ε' := by ring
                    rw [h4, abs_of_pos hε'_pos]
                  exact h3
                rw [h2]
                have h3 : ε' < δ' := by
                  dsimp only [ε']
                  linarith
                exact h3
              exact h
            have hε'_in : C * (pts i_max - pts i_min + 2 * ε') ^ s < (i_max - i_min : ℝ) * step := h_sub hε'_ball
            have h17 : (i_max - i_min : ℝ) * step < C * (pts i_max - pts i_min + 2 * ε') ^ s := h_main ε' hε'_pos
            linarith
          have h_range : pts i_max - pts i_min ≤ 2 * r := by
            have h1 : dist (pts i_min) z ≤ r := by
              simpa [mem_closedBall] using hS_sub h_pts_min_in
            have h2 : dist (pts i_max) z ≤ r := by
              simpa [mem_closedBall] using hS_sub h_pts_max_in
            have h3 : dist (pts i_min) (pts i_max) ≤ dist (pts i_min) z + dist z (pts i_max) := dist_triangle _ _ _
            have h3' : dist z (pts i_max) = dist (pts i_max) z := dist_comm _ _
            rw [h3'] at h3
            have h4 : dist (pts i_min) (pts i_max) = pts i_max - pts i_min := by
              rw [Real.dist_eq]
              have h5 : |pts i_min - pts i_max| = pts i_max - pts i_min := by
                have h6 : pts i_min - pts i_max = -(pts i_max - pts i_min) := by ring
                rw [h6, abs_neg, abs_of_nonneg h_pos]
              exact h5
            rw [h4] at h3
            linarith
          have h_card_bound : (I.card - 1 : ℝ) ≤ (i_max - i_min : ℝ) := by
            have hI_ge2 : 2 ≤ I.card := by
              have h2 : i_min ≠ i_max := by omega
              exact Finset.one_lt_card.mpr ⟨i_min, h_min_in, i_max, h_max_in, h2⟩
            have hI_ge1 : 1 ≤ I.card := by linarith
            have h_sub : I ⊆ Finset.Icc i_min i_max := by
              intro k hk
              simp only [Finset.mem_Icc]
              exact ⟨Finset.min'_le I k hk, Finset.le_max' I k hk⟩
            have h : I.card ≤ (Finset.Icc i_min i_max).card := Finset.card_le_card h_sub
            have h2 : (Finset.Icc i_min i_max).card = i_max - i_min + 1 := by
              have h2' : i_min ≤ i_max := h_min_le_max
              have h3 : (Finset.Icc i_min i_max).card = i_max + 1 - i_min := by
                simp
              rw [h3]
              omega
            have h_cast : (↑(i_max - i_min + 1) : ℝ) = (i_max - i_min : ℝ) + 1 := by
              have h_sub : i_min ≤ i_max := h_min_le_max
              simp [Nat.cast_add, Nat.cast_sub h_sub] <;> omega
            have h3 : (I.card : ℝ) ≤ (i_max - i_min : ℝ) + 1 := by
              have h4 : (I.card : ℝ) ≤ ↑((Finset.Icc i_min i_max).card) := by exact_mod_cast h
              rw [h2] at h4
              rw [h_cast] at h4
              exact h4
            have h6 : (I.card : ℝ) - 1 ≤ (i_max - i_min : ℝ) := by linarith
            exact h6
          have h9 : (i_max - i_min : ℝ) * step ≤ C * (2 * r) ^ s := by
            calc (i_max - i_min : ℝ) * step
              ≤ C * (pts i_max - pts i_min) ^ s := h_limit
            _ ≤ C * (2 * r) ^ s := by
              have h_rpow : (pts i_max - pts i_min) ^ s ≤ (2 * r) ^ s :=
                Real.rpow_le_rpow h_pos h_range hs.le
              exact mul_le_mul_of_nonneg_left h_rpow (by positivity)
          have h10 : (S.card - 1 : ℝ) * step ≤ C * (2 * r) ^ s := by
            calc (S.card - 1 : ℝ) * step
              = (I.card - 1 : ℝ) * step := by rw [hI_card]
            _ ≤ (i_max - i_min : ℝ) * step := by gcongr
            _ ≤ C * (2 * r) ^ s := h9
          have h11 : (S.card : ℝ) ≤ 2 * r ^ s / δ ^ s := by
            have h12 : C * ((S.card - 1 : ℝ) * (3 * δ) ^ s) ≤ C * (2 * r) ^ s := by
              have h12' : (S.card - 1 : ℝ) * step ≤ C * (2 * r) ^ s := h10
              have h_step_eq2 : step = C * (3 * δ) ^ s := by simp [step] <;> ring
              rw [h_step_eq2] at h12'
              have h_assoc : (S.card - 1 : ℝ) * (C * (3 * δ) ^ s) = C * ((S.card - 1 : ℝ) * (3 * δ) ^ s) := by ring
              rw [h_assoc] at h12'
              exact h12'
            have h13 : (S.card - 1 : ℝ) * (3 * δ) ^ s ≤ (2 * r) ^ s := by
              have hC_pos' : 0 < C := hC
              by_contra h_contra
              have h4 : (2 * r) ^ s < (S.card - 1 : ℝ) * (3 * δ) ^ s := by linarith
              have h5 : C * (2 * r) ^ s < C * ((S.card - 1 : ℝ) * (3 * δ) ^ s) := by gcongr
              linarith
            have h14 : (S.card - 1 : ℝ) ≤ (2 * r) ^ s / (3 * δ) ^ s := by
              have h_pos3 : 0 < (3 * δ) ^ s := by positivity
              calc (S.card - 1 : ℝ)
                = ((S.card - 1 : ℝ) * (3 * δ) ^ s) / (3 * δ) ^ s := by field_simp [h_pos3.ne'] <;> ring
              _ ≤ (2 * r) ^ s / (3 * δ) ^ s := by gcongr
            have h15 : (S.card : ℝ) ≤ (2 * r) ^ s / (3 * δ) ^ s + 1 := by
              have h14' : (S.card : ℝ) - 1 ≤ (2 * r) ^ s / (3 * δ) ^ s := h14
              have h15' : (S.card : ℝ) - 1 + 1 ≤ (2 * r) ^ s / (3 * δ) ^ s + 1 := by
                exact add_le_add h14' (show (1 : ℝ) ≤ 1 by norm_num)
              have h16' : (S.card : ℝ) - 1 + 1 = (S.card : ℝ) := by ring
              rw [h16'] at h15'
              exact h15'
            have h16 : 1 ≤ r ^ s / δ ^ s := by
              have h17 : δ ^ s ≤ r ^ s := by gcongr
              rw [one_le_div (by positivity)] <;> exact h17
            calc (S.card : ℝ)
              ≤ (2 * r) ^ s / (3 * δ) ^ s + 1 := h15
            _ = (2 / 3 : ℝ) ^ s * (r ^ s / δ ^ s) + 1 := by
              have hr_pos : 0 < r := by linarith
              have h21 : (2 * r) ^ s = (2 : ℝ) ^ s * r ^ s := by
                rw [← Real.mul_rpow (by norm_num) hr_pos.le]
              have h22 : (3 * δ) ^ s = (3 : ℝ) ^ s * δ ^ s := by
                rw [← Real.mul_rpow (by norm_num) hδ.le]
              have h23 : (2 / 3 : ℝ) ^ s = (2 : ℝ) ^ s / (3 : ℝ) ^ s := by
                rw [Real.div_rpow (by norm_num) (by norm_num)]
              rw [h21, h22, h23]
              <;> field_simp [hδ.ne'] <;> ring
            _ ≤ 2 * (r ^ s / δ ^ s) := by
              have h17 : (2 / 3 : ℝ) ^ s < 1 := by
                have h18 : (2 / 3 : ℝ) < 1 := by norm_num
                have h19 : 0 ≤ (2 / 3 : ℝ) := by norm_num
                exact Real.rpow_lt_one h19 h18 hs
              have h17' : 0 ≤ (2 / 3 : ℝ) ^ s := by positivity
              set x := r ^ s / δ ^ s with hx_def
              have hx_ge1 : 1 ≤ x := h16
              have h21 : 1 ≤ 2 - (2 / 3 : ℝ) ^ s := by
                have h22 : (2 / 3 : ℝ) ^ s < 1 := h17
                linarith
              have h23 : 0 ≤ 2 - (2 / 3 : ℝ) ^ s := by linarith [h17']
              have h20 : (2 / 3 : ℝ) ^ s * x + 1 ≤ 2 * x := by
                have h24 : 1 ≤ (2 - (2 / 3 : ℝ) ^ s) * x := by
                  have h25 : 1 ≤ 2 - (2 / 3 : ℝ) ^ s := h21
                  have h26 : 1 ≤ x := hx_ge1
                  have h27 : 0 ≤ 2 - (2 / 3 : ℝ) ^ s := h23
                  have h28 : (2 - (2 / 3 : ℝ) ^ s) * 1 ≤ (2 - (2 / 3 : ℝ) ^ s) * x :=
                    mul_le_mul_of_nonneg_left h26 h27
                  have h29 : 1 ≤ (2 - (2 / 3 : ℝ) ^ s) * 1 := by
                    have h30 : (2 - (2 / 3 : ℝ) ^ s) * 1 = 2 - (2 / 3 : ℝ) ^ s := by ring
                    rw [h30]
                    exact h25
                  exact le_trans h29 h28
                linarith
              exact h20
            _ = 2 * r ^ s / δ ^ s := by ring
          exact_mod_cast h11
    have h_main_isDelta : IsDeltaSSet δ s (4 * C * 3 ^ s / m) P := by
      have hP_nonempty : P.Nonempty := by
        have h0 : 0 < N := hN_pos
        have h1 : 0 ∈ Finset.range N := Finset.mem_range.mpr h0
        exact ⟨pts 0, ⟨0, h1, rfl⟩⟩
      refine' ⟨hP_nonempty, hδ, by positivity, by linarith, _⟩
      intro z r hr
      let S := P'.filter (fun x => dist x z ≤ r)
      have hS_eq : (S : Set ℝ) = P ∩ closedBall z r := by
        ext x
        simp only [S, Finset.mem_coe, Finset.mem_filter, mem_inter_iff, mem_closedBall]
        constructor
        · rintro ⟨h1, h2⟩
          have h3 : x ∈ P := by rw [← hP'_eq] <;> exact h1
          exact ⟨h3, h2⟩
        · rintro ⟨h1, h2⟩
          have h3 : x ∈ (P' : Set ℝ) := by rw [hP'_eq] <;> exact h1
          exact ⟨h3, h2⟩
      have h1 : Ncover δ (P ∩ closedBall z r) ≤ (↑S.card : ENNReal) := by
        rw [← hS_eq]
        have h2' : Metric.externalCoveringNumber δ.toNNReal (S : Set ℝ) ≤ (S : Set ℝ).encard :=
          Metric.externalCoveringNumber_le_encard_self (ε := δ.toNNReal) (S : Set ℝ)
        have hS_finite : (S : Set ℝ).Finite := S.finite_toSet
        have h3 : (S : Set ℝ).encard = ↑S.card := by
          rw [hS_finite.encard_eq_coe_toFinset_card]
          <;> simp
        have h4 : (Metric.externalCoveringNumber δ.toNNReal (S : Set ℝ) : ENNReal) ≤ (↑S.card : ENNReal) := by
          exact_mod_cast h2'.trans (le_of_eq h3)
        simpa [Ncover] using h4
      have hr_pos : 0 < r := by linarith
      have h3_real : (S.card : ℝ) ≤ 2 * r ^ s / δ ^ s := h_growth z r hr
      have h_pos1 : 0 ≤ (4 * C * 3 ^ s / m) * r ^ s := by positivity
      have h5 : (S.card : ℝ) ≤ (4 * C * 3 ^ s / m) * r ^ s * (N : ℝ) := by
        have h6 : (m / (2 * C * 3 ^ s * δ ^ s)) ≤ (N : ℝ) := h_N_lower
        calc (S.card : ℝ)
          ≤ 2 * r ^ s / δ ^ s := h3_real
        _ = (4 * C * 3 ^ s / m) * r ^ s * (m / (2 * C * 3 ^ s * δ ^ s)) := by
          field_simp [hC.ne', hδ.ne'] <;> ring
        _ ≤ (4 * C * 3 ^ s / m) * r ^ s * (N : ℝ) := by
          exact mul_le_mul_of_nonneg_left h6 h_pos1
      have h_pos2 : 0 ≤ (4 * C * 3 ^ s / m) * r ^ s * (N : ℝ) := by positivity
      have h4 : (↑S.card : ENNReal) ≤ ENNReal.ofReal ((4 * C * 3 ^ s / m) * r ^ s) * (↑N : ENNReal) := by
        have h8 : ENNReal.ofReal (S.card : ℝ) ≤ ENNReal.ofReal ((4 * C * 3 ^ s / m) * r ^ s * (N : ℝ)) :=
          ENNReal.ofReal_le_ofReal h5
        have h9 : ENNReal.ofReal (S.card : ℝ) = (↑S.card : ENNReal) := by simp
        have h10 : ENNReal.ofReal ((4 * C * 3 ^ s / m) * r ^ s * (N : ℝ)) =
            ENNReal.ofReal ((4 * C * 3 ^ s / m) * r ^ s) * ENNReal.ofReal ((N : ℝ)) := by
          rw [ENNReal.ofReal_mul h_pos1]
          <;> simp
        have h11 : ENNReal.ofReal ((N : ℝ)) = (↑N : ENNReal) := by simp
        rw [h9] at h8
        rw [h10, h11] at h8
        exact h8
      have hr_pos' : 0 ≤ r := by linarith
      have h_format : ENNReal.ofReal ((4 * C * 3 ^ s / m) * r ^ s) =
          ENNReal.ofReal (4 * C * 3 ^ s / m) * (ENNReal.ofReal r) ^ s := by
        have h1 : ENNReal.ofReal ((4 * C * 3 ^ s / m) * r ^ s) =
            ENNReal.ofReal (4 * C * 3 ^ s / m) * ENNReal.ofReal (r ^ s) := by
          rw [ENNReal.ofReal_mul (by positivity)]
        rw [h1]
        have h2 : ENNReal.ofReal (r ^ s) = (ENNReal.ofReal r) ^ s := by
          rw [ENNReal.ofReal_rpow_of_nonneg hr_pos' (by linarith)]
        rw [h2]
        <;> ring
      calc Ncover δ (P ∩ closedBall z r)
        ≤ (↑S.card : ENNReal) := h1
      _ ≤ ENNReal.ofReal ((4 * C * 3 ^ s / m) * r ^ s) * (↑N : ENNReal) := h4
      _ = ENNReal.ofReal (4 * C * 3 ^ s / m) * (ENNReal.ofReal r) ^ s * (↑N : ENNReal) := by
        rw [h_format] <;> ring
      _ = ENNReal.ofReal (4 * C * 3 ^ s / m) * (ENNReal.ofReal r) ^ s * Ncover δ P := by
        rw [h_ncover]
    have h_lower : ENNReal.ofReal (m / (2 * C * 3 ^ s * δ ^ s)) ≤ Ncover δ P := by
      rw [h_ncover]
      have h9 : ENNReal.ofReal (m / (2 * C * 3 ^ s * δ ^ s)) ≤ ENNReal.ofReal ((N : ℝ)) :=
        ENNReal.ofReal_le_ofReal h_N_lower
      have h10 : ENNReal.ofReal ((N : ℝ)) = (↑N : ENNReal) := by
        simp
      rw [h10] at h9
      exact h9
    exact ⟨P, hP_sub, h_main_isDelta, h_lower⟩

end RobustKaufmanProjection.HausdorffContentToDeltaSet

end
