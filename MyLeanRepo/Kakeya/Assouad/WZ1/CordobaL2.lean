import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
# Finite Córdoba L2 inequality

A measure-theoretic lemma used in WZ1 Lemma 17.

## Whiteprint node
`Kakeya/WZ1/Lemma17Cordoba/CordobaL2`
-/

namespace Kakeya.Assouad

open Finset MeasureTheory

/-- Auxiliary: `∑ i ∈ Finset.range k, 1/(k-i) = harmonic k`. -/
private lemma sum_range_inv_sub_eq_harmonic (k : ℕ) (hk : 0 < k) :
    ∑ i ∈ Finset.range k, (1 : ℝ) / ((k : ℝ) - (i : ℝ)) = (harmonic k : ℝ) := by
  let g : ℕ → ℕ := fun d => k - d
  have h1 : Finset.image g (Finset.Icc 1 k) = Finset.range k := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc, g]
    constructor
    · rintro ⟨d, ⟨hd1, hdk⟩, rfl⟩
      omega
    · intro hx
      refine ⟨k - x, ?_, ?_⟩
      · omega
      · omega
  have h_inj : Set.InjOn g (Finset.Icc 1 k) := by
    intro d1 _ d2 _ h
    simp_all [g] <;> omega
  have h2 : ∑ i ∈ Finset.range k, (1 : ℝ) / ((k : ℝ) - (i : ℝ)) =
      ∑ d ∈ Finset.Icc 1 k, (1 : ℝ) / ((k : ℝ) - (g d : ℝ)) := by
    rw [← h1, Finset.sum_image h_inj] <;> rfl
  have h3 : ∀ d ∈ Finset.Icc 1 k, (k : ℝ) - (g d : ℝ) = (d : ℝ) := by
    intro d hd
    simp only [g]
    have h4 : d ≤ k := (Finset.mem_Icc.mp hd).2
    have h5 : ↑(k - d) = (k : ℝ) - (d : ℝ) := by
      rw [Nat.cast_sub h4] <;> norm_cast
    rw [h5] <;> ring
  have h4 : ∑ d ∈ Finset.Icc 1 k, (1 : ℝ) / ((k : ℝ) - (g d : ℝ)) =
      ∑ d ∈ Finset.Icc 1 k, (1 : ℝ) / (d : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [h3 d hd]
  rw [h2, h4]
  have h_final : ∑ d ∈ Finset.Icc 1 k, (1 : ℝ) / (d : ℝ) = (harmonic k : ℝ) := by
    have h' : (harmonic k : ℚ) = ∑ d ∈ Finset.Icc 1 k, (↑d)⁻¹ := harmonic_eq_sum_Icc
    have h'' : ((harmonic k : ℝ)) = ∑ d ∈ Finset.Icc 1 k, ((↑d : ℝ)⁻¹) := by
      simpa [Rat.cast_sum] using congr_arg (fun x : ℚ => (x : ℝ)) h'
    have h3 : ∑ d ∈ Finset.Icc 1 k, ((↑d : ℝ)⁻¹) = ∑ d ∈ Finset.Icc 1 k, (1 : ℝ) / (d : ℝ) := by
      apply Finset.sum_congr rfl
      intro d _
      field_simp
    rw [h3] at h''
    exact h''.symm
  exact h_final

/-- Harmonic pairwise sum bound over `Finset.range k`. -/
private lemma harmonic_range_sum_bound :
    ∀ (k : ℕ), 0 < k →
      ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
        (if i ≠ j then (1 : ℝ) / |(i : ℝ) - (j : ℝ)| else 0)
      ≤ 2 * (k : ℝ) * (1 + Real.log (k : ℝ)) := by
  intro k
  induction k with
  | zero =>
    intro h
    exfalso
    linarith
  | succ k ih =>
    intro hk
    by_cases h_k : k = 0
    · subst h_k
      norm_num
    · have h_k_pos : 0 < k := Nat.pos_of_ne_zero h_k
      let f : ℕ → ℕ → ℝ := fun i j =>
        if i ≠ j then 1 / |(i : ℝ) - (j : ℝ)| else 0
      have h_fik : ∀ i ∈ Finset.range k, f i k = 1 / ((k : ℝ) - (i : ℝ)) := by
        intro i hi
        have h_i_lt_k : i < k := Finset.mem_range.mp hi
        have h_ne : i ≠ k := by linarith
        have h_neg : (i : ℝ) - (k : ℝ) < 0 := by
          have h : (i : ℝ) < (k : ℝ) := by exact_mod_cast h_i_lt_k
          linarith
        have h_abs : |(i : ℝ) - (k : ℝ)| = (k : ℝ) - (i : ℝ) := by
          rw [abs_of_neg h_neg] <;> linarith
        have h_main : f i k = 1 / |(i : ℝ) - (k : ℝ)| := by
          unfold f
          rw [if_pos h_ne]
        rw [h_main, h_abs]
      have h_fki : ∀ j ∈ Finset.range k, f k j = 1 / ((k : ℝ) - (j : ℝ)) := by
        intro j hj
        have h_j_lt_k : j < k := Finset.mem_range.mp hj
        have h_ne : k ≠ j := by linarith
        have h_pos : 0 < (k : ℝ) - (j : ℝ) := by
          have h : (j : ℝ) < (k : ℝ) := by exact_mod_cast h_j_lt_k
          linarith
        have h_abs : |(k : ℝ) - (j : ℝ)| = (k : ℝ) - (j : ℝ) := by
          rw [abs_of_pos h_pos]
        have h_main : f k j = 1 / |(k : ℝ) - (j : ℝ)| := by
          unfold f
          rw [if_pos h_ne]
        rw [h_main, h_abs]
      have h_fkk : f k k = 0 := by
        unfold f
        have h : ¬(k ≠ k) := by simp
        rw [if_neg h] <;> rfl
      have h_sum : ∑ i ∈ Finset.range k, (1 : ℝ) / ((k : ℝ) - (i : ℝ)) = (harmonic k : ℝ) :=
        sum_range_inv_sub_eq_harmonic k h_k_pos
      have h_step1 : ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), f i j =
          (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range (k + 1), f i j) + ∑ j ∈ Finset.range (k + 1), f k j := by
        rw [Finset.sum_range_succ]
      have h_step2 : ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range (k + 1), f i j =
          (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k, f i j) + ∑ i ∈ Finset.range k, f i k := by
        have h : ∀ i ∈ Finset.range k, ∑ j ∈ Finset.range (k + 1), f i j =
            (∑ j ∈ Finset.range k, f i j) + f i k := by
          intro i _
          rw [Finset.sum_range_succ]
        have h' : ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range (k + 1), f i j =
            ∑ i ∈ Finset.range k, ((∑ j ∈ Finset.range k, f i j) + f i k) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact h i hi
        rw [h', Finset.sum_add_distrib]
      have h_step3 : ∑ j ∈ Finset.range (k + 1), f k j =
          (∑ j ∈ Finset.range k, f k j) + f k k := by
        rw [Finset.sum_range_succ]
      have h_step4 : ∑ i ∈ Finset.range k, f i k =
          ∑ i ∈ Finset.range k, (1 : ℝ) / ((k : ℝ) - (i : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact h_fik i hi
      have h_step5 : ∑ j ∈ Finset.range k, f k j =
          ∑ j ∈ Finset.range k, (1 : ℝ) / ((k : ℝ) - (j : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact h_fki j hj
      have h_decomp : ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), f i j =
          (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k, f i j) + 2 * (harmonic k : ℝ) := by
        rw [h_step1, h_step2, h_step3, h_step4, h_step5]
        rw [h_fkk, h_sum] <;> ring
      rw [h_decomp]
      have h_harm : (harmonic k : ℝ) ≤ 1 + Real.log (k : ℝ) := harmonic_le_one_add_log k
      have h_ih := ih h_k_pos
      have h_log : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) := by
        apply Real.log_le_log <;> norm_cast <;> linarith
      calc
        (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k, f i j) + 2 * (harmonic k : ℝ)
          ≤ 2 * (k : ℝ) * (1 + Real.log (k : ℝ)) + 2 * (1 + Real.log (k : ℝ)) := by gcongr
        _ = 2 * ((k + 1 : ℕ) : ℝ) * (1 + Real.log (k : ℝ)) := by
            simp [Nat.cast_add] <;> ring
        _ ≤ 2 * ((k + 1 : ℕ) : ℝ) * (1 + Real.log ((k + 1 : ℕ) : ℝ)) := by
            gcongr <;> linarith

/-- Harmonic pairwise sum bound: for `k > 0`,
    `∑_{i≠j : Fin k} 1/|i-j| ≤ 2 * k * (1 + log k)`. -/
lemma harmonic_pairwise_sum_bound (k : ℕ) (hk : 0 < k) :
    (∑ i : Fin k, ∑ j : Fin k,
      (if i ≠ j then (1 : ℝ) / |(i : ℝ) - (j : ℝ)| else (0 : ℝ)))
    ≤ 2 * (k : ℝ) * (1 + Real.log (k : ℝ)) := by
  let H : ℕ → ℕ → ℝ := fun i j =>
    if i ≠ j then (1 : ℝ) / |(i : ℝ) - (j : ℝ)| else 0
  have h_eq : ∀ (i j : Fin k),
      (if i ≠ j then (1 : ℝ) / |(i : ℝ) - (j : ℝ)| else 0) = H (i.val) (j.val) := by
    intro i j
    by_cases h : i ≠ j
    · have h' : i.val ≠ j.val := by
        intro h''
        apply h
        exact Fin.val_injective h''
      have h4 : (i : ℝ) = (i.val : ℝ) := by simp
      have h5 : (j : ℝ) = (j.val : ℝ) := by simp
      have h6 : |(i : ℝ) - (j : ℝ)| = |(i.val : ℝ) - (j.val : ℝ)| := by
        rw [h4, h5]
      have hF : H (i.val) (j.val) = (1 : ℝ) / |(i.val : ℝ) - (j.val : ℝ)| := by
        unfold H
        rw [if_pos h']
      rw [if_pos h, hF, h6]
    · have h' : i = j := by tauto
      have h'' : i.val = j.val := by rw [h']
      have hF : H (i.val) (j.val) = 0 := by
        unfold H
        rw [if_neg (show ¬(i.val ≠ j.val) from by simp [h''])]
      rw [if_neg h, hF]
  have h_sum1 : ∑ i : Fin k, ∑ j : Fin k,
        (if i ≠ j then (1 : ℝ) / |(i : ℝ) - (j : ℝ)| else 0) =
      ∑ i : Fin k, ∑ j : Fin k, H (i.val) (j.val) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact h_eq i j
  have h_sum_image1 : ∀ (g : ℕ → ℝ),
      ∑ i : Fin k, g (i.val) = ∑ i ∈ Finset.range k, g i := by
    intro g
    have h_inj : Set.InjOn (fun i : Fin k => i.val) (Finset.univ : Finset (Fin k)) := by
      intro a _ b _ h
      exact Fin.val_injective h
    have h_image : Finset.image (fun i : Fin k => i.val) (Finset.univ : Finset (Fin k)) = Finset.range k := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      · rintro ⟨i, _, rfl⟩
        exact i.is_lt
      · intro hx
        have h_exists : ∃ (i : Fin k), i.val = x := ⟨⟨x, hx⟩, by simp⟩
        rcases h_exists with ⟨i, hi⟩
        exact ⟨i, hi⟩
    calc
      ∑ i : Fin k, g (i.val)
        = ∑ y ∈ Finset.image (fun i : Fin k => i.val) (Finset.univ : Finset (Fin k)), g y := by
          rw [Finset.sum_image h_inj] <;> rfl
      _ = ∑ y ∈ Finset.range k, g y := by rw [h_image]
  have h_sum2 : ∑ i : Fin k, ∑ j : Fin k, H (i.val) (j.val) =
      ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k, H i j := by
    rw [h_sum_image1 (fun i => ∑ j : Fin k, H i (j.val))]
    apply Finset.sum_congr rfl
    intro i _
    exact h_sum_image1 (fun j => H i j)
  rw [h_sum1, h_sum2]
  exact harmonic_range_sum_bound k hk

/-- Finite Córdoba L2 inequality. -/
lemma finite_cordoba_l2
    {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    {k : ℕ} (hk_pos : 0 < k)
    (A : Fin k → Set X) (hA_meas : ∀ i, MeasurableSet (A i))
    (V V' C : ℝ) (hV_pos : 0 < V) (hV'_nonneg : 0 ≤ V') (hC_nonneg : 0 ≤ C)
    (h_volume_lower : ∀ i, μ (A i) ≥ ENNReal.ofReal V)
    (h_volume_upper : ∀ i, μ (A i) ≤ ENNReal.ofReal V')
    (h_intersection : ∀ i j, i ≠ j →
        μ (A i ∩ A j) ≤ ENNReal.ofReal (C / |(i : ℝ) - (j : ℝ)|)) :
    μ (⋃ i, A i) ≥
      ENNReal.ofReal ((k : ℝ)^2 * V^2) /
      ENNReal.ofReal ((k : ℝ) * V' + 2 * C * (k : ℝ) * (1 + Real.log (k : ℝ))) := by
  classical
  let U : Set X := ⋃ i, A i
  let f : X → ℝ := fun x => ∑ i : Fin k, (A i).indicator (fun _ => (1 : ℝ)) x
  let g : X → ℝ := U.indicator (fun _ => (1 : ℝ))

  have hU_meas : MeasurableSet U := by
    exact MeasurableSet.iUnion hA_meas

  let i0 : Fin k := ⟨0, hk_pos⟩
  have hV'_pos : 0 < V' := by
    have h1 : ENNReal.ofReal V ≤ μ (A i0) := h_volume_lower i0
    have h2 : μ (A i0) ≤ ENNReal.ofReal V' := h_volume_upper i0
    have h4 : ENNReal.ofReal V ≤ ENNReal.ofReal V' := h1.trans h2
    have h6 : V ≤ V' := (ENNReal.ofReal_le_ofReal_iff hV'_nonneg).mp h4
    linarith

  have h_fin_upper : ∀ i, μ (A i) < ⊤ := by
    intro i
    exact (h_volume_upper i).trans_lt ENNReal.ofReal_lt_top

  have hU_fin : μ U < ⊤ := by
    have hU_eq : U = ⋃ i ∈ (Finset.univ : Finset (Fin k)), A i := by
      ext x
      simp [U, Finset.mem_univ]
      <;> tauto
    rw [hU_eq]
    have h1 : μ (⋃ i ∈ (Finset.univ : Finset (Fin k)), A i) ≤ ∑ i : Fin k, μ (A i) :=
      MeasureTheory.measure_biUnion_finset_le (Finset.univ : Finset (Fin k)) A
    have h2 : ∑ i : Fin k, μ (A i) ≤ ∑ i : Fin k, ENNReal.ofReal V' := by
      apply Finset.sum_le_sum
      intro i _
      exact h_volume_upper i
    have h3 : ∑ i : Fin k, ENNReal.ofReal V' = (k : ENNReal) * ENNReal.ofReal V' := by
      simp [Finset.sum_const] <;> ring
    have h4 : (k : ENNReal) * ENNReal.ofReal V' < ⊤ := by
      apply ENNReal.mul_lt_top
      · exact_mod_cast (show (k : ENNReal) < ⊤ from by simp)
      · exact ENNReal.ofReal_lt_top
    rw [h3] at h2
    exact h1.trans_lt (h2.trans_lt h4)

  have h_int_indicator : ∀ (s : Set X), MeasurableSet s → μ s < ⊤ →
      Integrable (s.indicator (fun _ => (1 : ℝ))) μ := by
    intro s hs hms
    haveI : IsFiniteMeasure (μ.restrict s) := ⟨by simpa [Measure.restrict_apply] using hms⟩
    have h : Integrable (fun _ : X => (1 : ℝ)) (μ.restrict s) := by
      rw [integrable_const_iff]
      exact Or.inr (show IsFiniteMeasure (μ.restrict s) from inferInstance)
    have h' : IntegrableOn (fun _ : X => (1 : ℝ)) s μ := h
    rw [integrable_indicator_iff hs]
    exact h'

  have h_int_A : ∀ i, Integrable ((A i).indicator (fun _ => (1 : ℝ))) μ := by
    intro i
    exact h_int_indicator (A i) (hA_meas i) (h_fin_upper i)

  have hf_int : Integrable f μ := by
    have h : f = fun x => ∑ i : Fin k, (A i).indicator (fun _ => (1 : ℝ)) x := rfl
    rw [h]
    exact integrable_finset_sum _ (fun i _ => h_int_A i)

  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    apply Finset.sum_nonneg
    intro i _
    have h : 0 ≤ (A i).indicator (fun _ => (1 : ℝ)) x := by
      apply Set.indicator_nonneg
      intro y _
      exact zero_le_one
    exact h

  have hf_meas : AEStronglyMeasurable f μ := by
    have h_meas_ind : ∀ i : Fin k, Measurable ((A i).indicator (fun _ => (1 : ℝ))) := by
      intro i
      exact measurable_const.indicator (hA_meas i)
    have h : Measurable f := by
      have h' : f = fun x => ∑ i : Fin k, (A i).indicator (fun _ => (1 : ℝ)) x := rfl
      rw [h']
      exact measurable_sum (Finset.univ) (fun i _ => h_meas_ind i)
    exact h.aestronglyMeasurable

  have hfg : ∀ x, f x * g x = f x := by
    intro x
    by_cases hx : x ∈ U
    · have hgx : g x = 1 := by
        simp only [g]
        simp [hx]
      rw [hgx] <;> ring
    · have hfx : f x = 0 := by
        have h_notin_all : ∀ i : Fin k, x ∉ A i := by
          intro i
          exact fun h => hx (Set.mem_iUnion.mpr ⟨i, h⟩)
        have h_all_zero : ∀ i : Fin k, (A i).indicator (fun _ => (1 : ℝ)) x = 0 := by
          intro i
          have h' : x ∉ A i := h_notin_all i
          simp [h']
        have h_eq : f x = ∑ i : Fin k, (A i).indicator (fun _ => (1 : ℝ)) x := rfl
        rw [h_eq]
        rw [Finset.sum_congr rfl (fun i _ => h_all_zero i)]
        simp
      have hgx : g x = 0 := by
        simp only [g]
        simp [hx]
      rw [hfx, hgx] <;> ring

  have hg2 : ∀ x, g x ^ 2 = g x := by
    intro x
    by_cases hx : x ∈ U
    · have hgx : g x = 1 := by
        simp only [g]
        simp [hx]
      rw [hgx] <;> norm_num
    · have hgx : g x = 0 := by
        simp only [g]
        simp [hx]
      rw [hgx] <;> norm_num

  have h_int_U : Integrable g μ := h_int_indicator U hU_meas hU_fin

  have h_f2_eq : (fun x : X => f x ^ 2) =
      fun x : X => ∑ i : Fin k, ∑ j : Fin k, (A i ∩ A j).indicator (fun _ => (1 : ℝ)) x := by
    funext x
    have h1 : f x = ∑ i : Fin k, (A i).indicator (fun _ => (1 : ℝ)) x := rfl
    rw [h1]
    have h21 : (∑ i : Fin k, (A i).indicator (fun _ => (1 : ℝ)) x) ^ 2 =
        (∑ i : Fin k, (A i).indicator (fun _ => (1 : ℝ)) x) * (∑ j : Fin k, (A j).indicator (fun _ => (1 : ℝ)) x) := by ring
    rw [h21]
    have h2 : (∑ i : Fin k, (A i).indicator (fun _ => (1 : ℝ)) x) * (∑ j : Fin k, (A j).indicator (fun _ => (1 : ℝ)) x) =
        ∑ i : Fin k, ∑ j : Fin k,
          ((A i).indicator (fun _ => (1 : ℝ)) x * (A j).indicator (fun _ => (1 : ℝ)) x) := by
      rw [Finset.sum_mul_sum] <;> rfl
    rw [h2]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have h3 : (A i).indicator (fun _ => (1 : ℝ)) x * (A j).indicator (fun _ => (1 : ℝ)) x =
        (A i ∩ A j).indicator (fun _ => (1 : ℝ)) x := by
      by_cases hxi : x ∈ A i <;> by_cases hxj : x ∈ A j <;> simp [hxi, hxj, Set.indicator_apply] <;> rfl
    exact h3

  have h_int_inter : ∀ (i j : Fin k),
      Integrable ((A i ∩ A j).indicator (fun _ => (1 : ℝ))) μ := by
    intro i j
    have h_meas : MeasurableSet (A i ∩ A j) := (hA_meas i).inter (hA_meas j)
    have h_sub : A i ∩ A j ⊆ A i := by simp
    have h_fin : μ (A i ∩ A j) < ⊤ := (measure_mono h_sub).trans_lt (h_fin_upper i)
    exact h_int_indicator (A i ∩ A j) h_meas h_fin

  have hf2_int : Integrable (fun x : X => f x ^ 2) μ := by
    rw [h_f2_eq]
    exact integrable_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => h_int_inter i j))

  have hg2_int : Integrable (fun x : X => g x ^ 2) μ := by
    have h : (fun x : X => g x ^ 2) = g := by funext x; exact hg2 x
    rw [h]
    exact h_int_U

  have hfg_int : Integrable (fun x => f x * g x) μ := by
    have h_eq : (fun x => f x * g x) = f := by funext x; exact hfg x
    rw [h_eq]
    exact hf_int

  have h_quad_nonneg : ∀ (t : ℝ), 0 ≤ ∫ x, (f x - t * g x)^2 ∂μ := by
    intro t
    have h_nonneg : ∀ x, 0 ≤ (f x - t * g x)^2 := fun x => sq_nonneg _
    let H := (fun x : X => f x * g x)
    let G := (fun x : X => g x^2)
    have hH_smul : Integrable ((2 * t) • H) μ :=
      MeasureTheory.Integrable.smul_enorm (2 * t) hfg_int
    have hG_smul : Integrable ((t^2) • G) μ :=
      MeasureTheory.Integrable.smul_enorm (t^2) hg2_int
    have h_expand : (fun x : X => (f x - t * g x)^2) =
        (fun x => f x^2) - (2 * t) • H + (t^2) • G := by
      funext x
      simp [pow_two, smul_eq_mul] <;> ring
    have h_int : Integrable (fun x => (f x - t * g x)^2) μ := by
      rw [h_expand]
      exact (hf2_int.sub hH_smul).add hG_smul
    have h_main : 0 ≤ ∫ x, (f x - t * g x)^2 ∂μ := by
      have h : 0 ≤ ∫ x in Set.univ, (f x - t * g x)^2 ∂μ :=
        MeasureTheory.setIntegral_nonneg MeasurableSet.univ (fun x _ => sq_nonneg _)
      simpa using h
    exact h_main

  have h_expand_int : ∀ (t : ℝ), ∫ x, (f x - t * g x)^2 ∂μ =
      (∫ x, f x^2 ∂μ) - 2 * t * (∫ x, f x * g x ∂μ) + t^2 * (∫ x, g x^2 ∂μ) := by
    intro t
    set F := (fun x : X => f x^2) with hF_def
    set H := (fun x : X => f x * g x) with hH_def
    set G := (fun x : X => g x^2) with hG_def
    have hH_smul : Integrable ((2 * t) • H) μ := MeasureTheory.Integrable.smul_enorm (2 * t) hfg_int
    have hG_smul : Integrable ((t^2) • G) μ := MeasureTheory.Integrable.smul_enorm (t^2) hg2_int
    have hH_eq : ((2 * t) • H) = fun x => 2 * t * H x := by funext x; simp [smul_eq_mul] <;> ring
    have hG_eq : ((t^2) • G) = fun x => t^2 * G x := by funext x; simp [smul_eq_mul] <;> ring
    have hH_int : Integrable (fun x => 2 * t * H x) μ := by rw [←hH_eq]; exact hH_smul
    have hG_int : Integrable (fun x => t^2 * G x) μ := by rw [←hG_eq]; exact hG_smul
    have h_eq : (fun x : X => (f x - t * g x)^2) = fun x => F x - 2 * t * H x + t^2 * G x := by
      funext x
      simp [hF_def, hH_def, hG_def, pow_two] <;> ring
    rw [h_eq]
    have h_int1 : Integrable (fun x => F x - 2 * t * H x) μ := hf2_int.sub hH_int
    have h_step1 : ∫ x, (F x - 2 * t * H x) + t^2 * G x ∂μ =
        (∫ x, F x - 2 * t * H x ∂μ) + ∫ x, t^2 * G x ∂μ :=
      integral_add h_int1 hG_int
    have h_step2 : ∫ x, F x - 2 * t * H x ∂μ =
        (∫ x, F x ∂μ) - ∫ x, 2 * t * H x ∂μ :=
      integral_sub hf2_int hH_int
    have h_step3 : ∫ x, 2 * t * H x ∂μ = 2 * t * ∫ x, H x ∂μ := by
      rw [integral_const_mul]
    have h_step4 : ∫ x, t^2 * G x ∂μ = t^2 * ∫ x, G x ∂μ := by
      rw [integral_const_mul]
    rw [h_step1, h_step2, h_step3, h_step4] <;> ring

  set a := ∫ x, g x^2 ∂μ with ha_def
  set b := ∫ x, f x * g x ∂μ with hb_def
  set c := ∫ x, f x^2 ∂μ with hc_def

  have h_quad : ∀ (t : ℝ), 0 ≤ c - 2 * t * b + t^2 * a := by
    intro t
    have h := h_quad_nonneg t
    rw [h_expand_int t] at h
    simpa [ha_def, hb_def, hc_def] using h

  have h_nonneg_a : 0 ≤ a := by positivity
  have h_nonneg_c : 0 ≤ c := by positivity

  have h_cs2 : b^2 ≤ c * a := by
    by_cases ha_pos : 0 < a
    · have h7 : 0 ≤ c - b^2 / a := by
        have h_eq : c - 2 * (b / a) * b + (b / a)^2 * a = c - b^2 / a := by
          field_simp [ha_pos.ne'] <;> ring
        have h9 := h_quad (b / a)
        rw [h_eq] at h9
        exact h9
      have h8 : b^2 ≤ c * a := by
        have h7' : b^2 / a ≤ c := by linarith
        have h9 : (b^2 / a) * a ≤ c * a := mul_le_mul_of_nonneg_right h7' (by linarith)
        have h10 : b^2 = (b^2 / a) * a := by field_simp [ha_pos.ne'] <;> ring
        rw [h10]
        exact h9
      exact h8
    · have ha_zero : a = 0 := by linarith
      have h1 : ∀ t : ℝ, 0 ≤ c - 2 * t * b := by
        intro t
        simpa [ha_zero] using h_quad t
      have h_b_zero : b = 0 := by
        by_cases h_b_pos : 0 < b
        · have h2 := h1 (c / b + 1)
          have h3 : c - 2 * (c / b + 1) * b < 0 := by
            have h4 : 0 < b := h_b_pos
            have h5 : c - 2 * (c / b + 1) * b = -c - 2 * b := by
              field_simp [h4.ne'] <;> ring
            rw [h5]
            have h6 : 0 ≤ c := h_nonneg_c
            linarith
          linarith
        · by_cases h_b_neg : b < 0
          · have h2 := h1 (c / b - 1)
            have h3 : c - 2 * (c / b - 1) * b < 0 := by
              have h4 : b < 0 := h_b_neg
              have h5 : c - 2 * (c / b - 1) * b = -c + 2 * b := by
                field_simp [h4.ne] <;> ring
              rw [h5]
              have h6 : 0 ≤ c := h_nonneg_c
              linarith
            linarith
          · have h_b_zero : b = 0 := by linarith
            exact h_b_zero
      rw [h_b_zero, ha_zero] <;> norm_num

  have h_int_f : ∫ x, f x ∂μ = ∑ i : Fin k, (μ (A i)).toReal := by
    have h : ∫ x, f x ∂μ = ∑ i : Fin k, ∫ x, (A i).indicator (fun _ => (1 : ℝ)) x ∂μ := by
      rw [integral_finset_sum _ (fun i _ => h_int_A i)] <;> rfl
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator (hA_meas i)]
    rw [setIntegral_const, MeasureTheory.measureReal_def] <;> simp

  have h_int_g : ∫ x, g x ∂μ = (μ U).toReal := by
    rw [integral_indicator hU_meas]
    rw [setIntegral_const, MeasureTheory.measureReal_def] <;> simp

  have h_int_g2 : ∫ x, g x ^ 2 ∂μ = (μ U).toReal := by
    have h : (fun x : X => g x ^ 2) = g := by funext x; exact hg2 x
    rw [h]
    exact h_int_g

  have h_int_f2 : ∫ x, f x ^ 2 ∂μ =
      ∑ i : Fin k, ∑ j : Fin k, (μ (A i ∩ A j)).toReal := by
    rw [h_f2_eq]
    rw [integral_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => h_int_inter i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_inter i j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_indicator ((hA_meas i).inter (hA_meas j))]
    rw [setIntegral_const, MeasureTheory.measureReal_def] <;> simp

  have h_lower1 : ∀ i, (μ (A i)).toReal ≥ V := by
    intro i
    have h1 : ENNReal.ofReal V ≤ μ (A i) := h_volume_lower i
    have h_eq : μ (A i) = ENNReal.ofReal ((μ (A i)).toReal) := by
      rw [ENNReal.ofReal_toReal (h_fin_upper i).ne]
    have h4 : ENNReal.ofReal V ≤ ENNReal.ofReal ((μ (A i)).toReal) := by
      rw [h_eq] at h1
      exact h1
    have h5 : 0 ≤ (μ (A i)).toReal := by positivity
    haveI : 0 ≤ V := by linarith
    have h_iff : ENNReal.ofReal V ≤ ENNReal.ofReal ((μ (A i)).toReal) ↔ V ≤ (μ (A i)).toReal :=
      ENNReal.ofReal_le_ofReal_iff h5
    exact h_iff.mp h4

  have h_lower_sum : ∫ x, f x ∂μ ≥ (k : ℝ) * V := by
    rw [h_int_f]
    have h : ∑ i : Fin k, (μ (A i)).toReal ≥ ∑ i : Fin k, V := by
      apply Finset.sum_le_sum
      intro i _
      exact h_lower1 i
    simpa [Finset.sum_const] using h

  have h_upper1 : ∀ i, (μ (A i)).toReal ≤ V' := by
    intro i
    have h1 : μ (A i) ≤ ENNReal.ofReal V' := h_volume_upper i
    have h_eq : μ (A i) = ENNReal.ofReal ((μ (A i)).toReal) := by
      rw [ENNReal.ofReal_toReal (h_fin_upper i).ne]
    have h4 : ENNReal.ofReal ((μ (A i)).toReal) ≤ ENNReal.ofReal V' := by
      rw [h_eq] at h1
      exact h1
    have h5 : 0 ≤ (μ (A i)).toReal := by positivity
    haveI : 0 ≤ (μ (A i)).toReal := h5
    have h_iff : ENNReal.ofReal ((μ (A i)).toReal) ≤ ENNReal.ofReal V' ↔ (μ (A i)).toReal ≤ V' :=
      ENNReal.ofReal_le_ofReal_iff hV'_nonneg
    exact h_iff.mp h4

  have h_upper_inter : ∀ i j, i ≠ j → (μ (A i ∩ A j)).toReal ≤ C / |(i : ℝ) - (j : ℝ)| := by
    intro i j hne
    have h1 : μ (A i ∩ A j) ≤ ENNReal.ofReal (C / |(i : ℝ) - (j : ℝ)|) :=
      h_intersection i j hne
    have h_sub : A i ∩ A j ⊆ A i := by simp
    have h_fin : μ (A i ∩ A j) < ⊤ := (measure_mono h_sub).trans_lt (h_fin_upper i)
    have h_eq : μ (A i ∩ A j) = ENNReal.ofReal ((μ (A i ∩ A j)).toReal) := by
      rw [ENNReal.ofReal_toReal h_fin.ne]
    have h4 : ENNReal.ofReal ((μ (A i ∩ A j)).toReal) ≤ ENNReal.ofReal (C / |(i : ℝ) - (j : ℝ)|) := by
      rw [h_eq] at h1
      exact h1
    have h5 : 0 ≤ (μ (A i ∩ A j)).toReal := by positivity
    have h6 : 0 ≤ C / |(i : ℝ) - (j : ℝ)| := by
      apply div_nonneg hC_nonneg
      exact abs_nonneg _
    have h7 : 0 ≤ (μ (A i ∩ A j)).toReal := by positivity
    haveI : 0 ≤ (μ (A i ∩ A j)).toReal := h7
    have h_iff : ENNReal.ofReal ((μ (A i ∩ A j)).toReal) ≤ ENNReal.ofReal (C / |(i : ℝ) - (j : ℝ)|) ↔ (μ (A i ∩ A j)).toReal ≤ C / |(i : ℝ) - (j : ℝ)| :=
      ENNReal.ofReal_le_ofReal_iff h6
    exact h_iff.mp h4

  set D : ℝ := (k : ℝ) * V' + 2 * C * (k : ℝ) * (1 + Real.log (k : ℝ)) with hD_def

  have hD_pos : 0 < D := by
    have h1 : 0 < (k : ℝ) * V' := by positivity
    have h2 : 0 ≤ 2 * C * (k : ℝ) * (1 + Real.log (k : ℝ)) := by
      have hlog : 0 ≤ Real.log (k : ℝ) := by
        apply Real.log_nonneg <;> norm_cast <;> linarith
      positivity
    linarith

  have h_harmonic : ∑ i : Fin k, ∑ j : Fin k,
        (if i ≠ j then (1 : ℝ) / |(i : ℝ) - (j : ℝ)| else 0)
      ≤ 2 * (k : ℝ) * (1 + Real.log (k : ℝ)) :=
    harmonic_pairwise_sum_bound k hk_pos

  have h_int_f2_upper : ∫ x, f x ^ 2 ∂μ ≤ D := by
    rw [h_int_f2]
    have h_split : ∑ i : Fin k, ∑ j : Fin k, (μ (A i ∩ A j)).toReal =
        (∑ i : Fin k, (μ (A i)).toReal) +
        ∑ i : Fin k, ∑ j : Fin k, (if i ≠ j then (μ (A i ∩ A j)).toReal else 0) := by
      have h : ∀ i, ∑ j : Fin k, (μ (A i ∩ A j)).toReal =
          (μ (A i)).toReal + ∑ j : Fin k, (if i ≠ j then (μ (A i ∩ A j)).toReal else 0) := by
        intro i
        have h3 : ∀ j : Fin k, (μ (A i ∩ A j)).toReal =
            (if i = j then (μ (A i)).toReal else 0) +
            (if i ≠ j then (μ (A i ∩ A j)).toReal else 0) := by
          intro j
          by_cases h : i = j
          · simp [h]
          · simp [h]
        have h4 : ∑ j : Fin k, (if i = j then (μ (A i)).toReal else 0) = (μ (A i)).toReal := by
          simp [Finset.sum_ite, Finset.filter_eq']
          <;> aesop
        calc
          ∑ j : Fin k, (μ (A i ∩ A j)).toReal
            = ∑ j : Fin k, ((if i = j then (μ (A i)).toReal else 0) +
                (if i ≠ j then (μ (A i ∩ A j)).toReal else 0)) := by
              apply Finset.sum_congr rfl; intro j _; exact h3 j
          _ = (∑ j : Fin k, (if i = j then (μ (A i)).toReal else 0)) +
                ∑ j : Fin k, (if i ≠ j then (μ (A i ∩ A j)).toReal else 0) := by
              rw [Finset.sum_add_distrib]
          _ = (μ (A i)).toReal + ∑ j : Fin k, (if i ≠ j then (μ (A i ∩ A j)).toReal else 0) := by
              rw [h4] <;> ring
      calc
        ∑ i : Fin k, ∑ j : Fin k, (μ (A i ∩ A j)).toReal
          = ∑ i : Fin k, ((μ (A i)).toReal + ∑ j : Fin k, (if i ≠ j then (μ (A i ∩ A j)).toReal else 0)) := by
            apply Finset.sum_congr rfl
            intro i _
            exact h i
        _ = (∑ i : Fin k, (μ (A i)).toReal) + ∑ i : Fin k, ∑ j : Fin k, (if i ≠ j then (μ (A i ∩ A j)).toReal else 0) := by
            rw [Finset.sum_add_distrib]
    rw [h_split]
    have h1 : ∑ i : Fin k, (μ (A i)).toReal ≤ (k : ℝ) * V' := by
      have h : ∑ i : Fin k, (μ (A i)).toReal ≤ ∑ i : Fin k, V' := by
        apply Finset.sum_le_sum
        intro i _
        exact h_upper1 i
      simpa [Finset.sum_const] using h
    have h2 : ∑ i : Fin k, ∑ j : Fin k, (if i ≠ j then (μ (A i ∩ A j)).toReal else 0) ≤
        ∑ i : Fin k, ∑ j : Fin k, (if i ≠ j then C / |(i : ℝ) - (j : ℝ)| else 0) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hne : i ≠ j
      · simp [hne, h_upper_inter i j hne] <;> ring
      · simp [hne]
    have h2' : ∑ i : Fin k, ∑ j : Fin k, (if i ≠ j then C / |(i : ℝ) - (j : ℝ)| else 0) =
        C * ∑ i : Fin k, ∑ j : Fin k, (if i ≠ j then (1 : ℝ) / |(i : ℝ) - (j : ℝ)| else 0) := by
      have h4 : ∀ i, ∑ j : Fin k, (if i ≠ j then C / |(i : ℝ) - (j : ℝ)| else 0) =
          C * ∑ j : Fin k, (if i ≠ j then (1 : ℝ) / |(i : ℝ) - (j : ℝ)| else 0) := by
        intro i
        have h5 : ∑ j : Fin k, (if i ≠ j then C / |(i : ℝ) - (j : ℝ)| else 0) =
            ∑ j : Fin k, (C * (if i ≠ j then (1 : ℝ) / |(i : ℝ) - (j : ℝ)| else 0)) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hne : i ≠ j
          · simp [hne] <;> ring
          · simp [hne]
        rw [h5, Finset.mul_sum]
      have h5 : ∑ i : Fin k, ∑ j : Fin k, (if i ≠ j then C / |(i : ℝ) - (j : ℝ)| else 0) =
          ∑ i : Fin k, (C * ∑ j : Fin k, (if i ≠ j then (1 : ℝ) / |(i : ℝ) - (j : ℝ)| else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h4 i
      rw [h5, Finset.mul_sum]
    have h3 : C * ∑ i : Fin k, ∑ j : Fin k, (if i ≠ j then (1 : ℝ) / |(i : ℝ) - (j : ℝ)| else 0) ≤
        C * (2 * (k : ℝ) * (1 + Real.log (k : ℝ))) :=
      mul_le_mul_of_nonneg_left h_harmonic hC_nonneg
    linarith [hD_def, h2, h2']

  have h1 : (∫ x, f x ∂μ)^2 ≤ (∫ x, f x^2 ∂μ) * (μ U).toReal := by
    have h5 : b = ∫ x, f x ∂μ := by
      simp only [hb_def]
      congr with x
      exact hfg x
    have h6 : a = (μ U).toReal := by
      simp only [ha_def]
      exact h_int_g2
    rw [h5, h6] at h_cs2
    exact h_cs2

  have h_f2_pos : 0 < ∫ x, f x ^ 2 ∂μ := by
    have h_k_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
    have h_pos : 0 < (k : ℝ) * V := mul_pos h_k_pos hV_pos
    have h5 : 0 < ∫ x, f x ∂μ := by
      have h6 : ∫ x, f x ∂μ ≥ (k : ℝ) * V := h_lower_sum
      linarith
    have h6 : 0 < (∫ x, f x ∂μ)^2 := by positivity
    have h7 : 0 ≤ (∫ x, f x ^ 2 ∂μ) * (μ U).toReal := by positivity
    nlinarith [h1]

  have h_main_real : (μ U).toReal ≥ ((k : ℝ)^2 * V^2) / D := by
    have h2 : 0 < ∫ x, f x ^ 2 ∂μ := h_f2_pos
    have h_k_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
    have h_pos : 0 < (k : ℝ) * V := mul_pos h_k_pos hV_pos
    have h3 : (∫ x, f x ∂μ)^2 ≥ ((k : ℝ) * V)^2 := by
      have h4 : ∫ x, f x ∂μ ≥ (k : ℝ) * V := h_lower_sum
      have h5 : 0 ≤ (k : ℝ) * V := by positivity
      nlinarith
    have h4 : (∫ x, f x ^ 2 ∂μ) * (μ U).toReal ≥ ((k : ℝ) * V)^2 := by
      calc
        (∫ x, f x ^ 2 ∂μ) * (μ U).toReal ≥ (∫ x, f x ∂μ)^2 := h1
        _ ≥ ((k : ℝ) * V)^2 := h3
    have h5 : (μ U).toReal ≥ ((k : ℝ) * V)^2 / (∫ x, f x ^ 2 ∂μ) := by
      calc
        (μ U).toReal
          = ((∫ x, f x ^ 2 ∂μ) * (μ U).toReal) / (∫ x, f x ^ 2 ∂μ) := by
            field_simp [h2.ne'] <;> ring
        _ ≥ (((k : ℝ) * V)^2) / (∫ x, f x ^ 2 ∂μ) := by gcongr
        _ = ((k : ℝ) * V)^2 / (∫ x, f x ^ 2 ∂μ) := by ring
    have h_num : ((k : ℝ) * V)^2 = (k : ℝ)^2 * V^2 := by ring
    have h6 : ((k : ℝ) * V)^2 / (∫ x, f x ^ 2 ∂μ) ≥ ((k : ℝ)^2 * V^2) / D := by
      rw [h_num]
      have h7 : 0 ≤ (k : ℝ)^2 * V^2 := by positivity
      have h8 : 0 < ∫ x, f x ^ 2 ∂μ := h2
      have h9 : 0 < D := hD_pos
      exact div_le_div_of_nonneg_left h7 h8 h_int_f2_upper
    linarith

  have h_final : μ U ≥ ENNReal.ofReal (((k : ℝ)^2 * V^2) / D) := by
    have h1 : ENNReal.ofReal (((k : ℝ)^2 * V^2) / D) ≤ ENNReal.ofReal ((μ U).toReal) := by
      apply ENNReal.ofReal_le_ofReal
      exact h_main_real
    have h2 : ENNReal.ofReal ((μ U).toReal) = μ U := by
      rw [ENNReal.ofReal_toReal hU_fin.ne]
    rw [h2] at h1
    exact h1

  have h_div : ENNReal.ofReal ((k : ℝ)^2 * V^2) / ENNReal.ofReal D =
      ENNReal.ofReal (((k : ℝ)^2 * V^2) / D) := by
    have h_num_nonneg : 0 ≤ (k : ℝ)^2 * V^2 := by positivity
    have hD_nonneg : 0 ≤ D := by linarith
    have h_pos' : 0 < D := hD_pos
    have h1 : ((k : ℝ)^2 * V^2) / D = (k : ℝ)^2 * V^2 * D⁻¹ := by
      field_simp [h_pos'.ne'] <;> ring
    rw [h1]
    have h2 : ENNReal.ofReal ((k : ℝ)^2 * V^2 * D⁻¹) =
        ENNReal.ofReal ((k : ℝ)^2 * V^2) * ENNReal.ofReal (D⁻¹) := by
      rw [ENNReal.ofReal_mul (by positivity)]
    rw [h2]
    have h3 : ENNReal.ofReal (D⁻¹) = (ENNReal.ofReal D)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hD_pos]
    rw [h3]
    <;> rfl
  rw [h_div]
  exact h_final

end Kakeya.Assouad
