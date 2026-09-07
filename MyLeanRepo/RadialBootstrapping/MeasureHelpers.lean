module

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Measure-Theoretic Helper Lemmas

This module provides standard measure-theoretic lemmas used in the proof of
`radial_bootstrapping_measure_thin_tubes`:

1. `fubini_fiber_lowerBound` — Fubini pigeonhole: large product measure implies
   many fibers have large measure.
2. `fubini_fiber_upperBound` — Markov/Fubini: small product measure bounds the
   set of fibers with large measure.
3. `measure_inter_lowerBound` — Inclusion-exclusion lower bound for intersections
   under a probability measure.
4. `tube_fiber_measurable` — Measurability of the set of points whose tube-fiber
   measure exceeds a threshold.
5. `fubini_fix_y` — Fubini: large product measure implies some vertical fiber
   has large measure.
6. `finite_pigeonhole` — Finite pigeonhole for product measure.

Whiteprint node: measure-helpers
-/

open MeasureTheory Metric Set

noncomputable section

namespace RadialBootstrapping

/-! ### 1. Fubini fiber lower bound -/

/-- If `(μ.prod ν) E ≥ c` with `0 < c ≤ 1`, then there exists a measurable set
`A` with `μ A ≥ c/2` such that every fiber `E|_x` for `x ∈ A` has `ν`-measure
at least `c/2`. -/
lemma fubini_fiber_lowerBound {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set (α × β)} (hE : MeasurableSet E)
    {c : ℝ} (hc_pos : 0 < c) (hc_le_one : c ≤ 1)
    (h_main : (μ.prod ν) E ≥ ENNReal.ofReal c) :
    ∃ (A : Set α), MeasurableSet A ∧
      μ A ≥ ENNReal.ofReal (c / 2) ∧
      ∀ x ∈ A, ν (Prod.mk x ⁻¹' E) ≥ ENNReal.ofReal (c / 2) := by
  let f : α → ENNReal := fun x => ν (Prod.mk x ⁻¹' E)
  have hf_meas : Measurable f := measurable_measure_prodMk_left hE
  let A : Set α := {x | f x ≥ ENNReal.ofReal (c / 2)}
  have hA_meas : MeasurableSet A := by
    have h : A = f ⁻¹' (Set.Ici (ENNReal.ofReal (c / 2))) := by
      ext x; simp [A]
    rw [h]
    exact hf_meas measurableSet_Ici
  have h_fubini : (μ.prod ν) E = ∫⁻ x, f x ∂μ := Measure.prod_apply hE
  by_cases h : μ A ≥ ENNReal.ofReal (c / 2)
  · exact ⟨A, hA_meas, h, fun x hx => hx⟩
  · have h_lt : μ A < ENNReal.ofReal (c / 2) := lt_of_not_ge h
    have h1 : ∫⁻ x, f x ∂μ = ∫⁻ x in A, f x ∂μ + ∫⁻ x in Aᶜ, f x ∂μ := by
      have h_union : A ∪ Aᶜ = Set.univ := by simp
      have h_disj : Disjoint A (Aᶜ) := disjoint_compl_right
      have h := lintegral_union (μ := μ) hA_meas.compl h_disj (f := f)
      simpa [h_union, setLIntegral_univ] using h
    have h2a : ∀ x ∈ A, f x ≤ 1 := fun _ _ => prob_le_one
    have h2 : ∫⁻ x in A, f x ∂μ ≤ μ A := by
      calc
        ∫⁻ x in A, f x ∂μ ≤ ∫⁻ x in A, (1 : ENNReal) ∂μ :=
          setLIntegral_mono (measurable_const) h2a
        _ = μ A := setLIntegral_one _
    have h3a : ∀ x ∈ (Aᶜ), f x ≤ ENNReal.ofReal (c / 2) := by
      intro x hx
      have h4 : ¬(f x ≥ ENNReal.ofReal (c / 2)) := by simpa [A] using hx
      exact le_of_not_ge h4
    have h3 : ∫⁻ x in Aᶜ, f x ∂μ ≤ ENNReal.ofReal (c / 2) := by
      calc
        ∫⁻ x in Aᶜ, f x ∂μ ≤ ∫⁻ x in Aᶜ, ENNReal.ofReal (c / 2) ∂μ :=
          setLIntegral_mono (measurable_const) h3a
        _ = ENNReal.ofReal (c / 2) * μ (Aᶜ) := by simp
        _ ≤ ENNReal.ofReal (c / 2) * 1 := by gcongr <;> exact prob_le_one
        _ = ENNReal.ofReal (c / 2) := by simp
    have h_c2_ne_top : ENNReal.ofReal (c / 2) ≠ ⊤ := by simp
    have h62 : μ A + ENNReal.ofReal (c / 2) < ENNReal.ofReal c := by
      have h9 : μ A < ENNReal.ofReal (c / 2) := h_lt
      have h10 : μ A + ENNReal.ofReal (c / 2) <
          ENNReal.ofReal (c / 2) + ENNReal.ofReal (c / 2) :=
        ENNReal.add_lt_add_right h_c2_ne_top h9
      have h11 : ENNReal.ofReal (c / 2) + ENNReal.ofReal (c / 2) = ENNReal.ofReal c := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)] <;> ring_nf
      rw [h11] at h10
      exact h10
    have h6 : ∫⁻ x, f x ∂μ < ENNReal.ofReal c := by
      rw [h1]
      have h61 : ∫⁻ x in A, f x ∂μ + ∫⁻ x in Aᶜ, f x ∂μ ≤
          μ A + ENNReal.ofReal (c / 2) := add_le_add h2 h3
      exact lt_of_le_of_lt h61 h62
    rw [h_fubini] at h_main
    exact False.elim (not_le.mpr h6 h_main)

/-! ### 2. Fubini fiber upper bound -/

/-- If `(μ.prod ν) E ≤ c` with `c > 0`, then the set of `x` whose fiber
`E|_x` has `ν`-measure at least `√c` has `μ`-measure at most `√c`. -/
lemma fubini_fiber_upperBound {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set (α × β)} (hE : MeasurableSet E)
    {c : ℝ} (hc_pos : 0 < c)
    (h_main : (μ.prod ν) E ≤ ENNReal.ofReal c) :
    μ {x : α | ν (Prod.mk x ⁻¹' E) ≥ ENNReal.ofReal (Real.sqrt c)} ≤
      ENNReal.ofReal (Real.sqrt c) := by
  let f : α → ENNReal := fun x => ν (Prod.mk x ⁻¹' E)
  have hf_meas : Measurable f := measurable_measure_prodMk_left hE
  let A : Set α := {x | f x ≥ ENNReal.ofReal (Real.sqrt c)}
  have hA_meas : MeasurableSet A := by
    have h : A = f ⁻¹' (Set.Ici (ENNReal.ofReal (Real.sqrt c))) := by
      ext x; simp [A]
    rw [h]
    exact hf_meas measurableSet_Ici
  have h_sqrt_pos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc_pos
  have h_fubini : (μ.prod ν) E = ∫⁻ x, f x ∂μ := Measure.prod_apply hE
  have h1 : ∫⁻ x in A, f x ∂μ ≤ ∫⁻ x, f x ∂μ := setLIntegral_le_lintegral _ _
  have h2a : ∀ x ∈ A, ENNReal.ofReal (Real.sqrt c) ≤ f x := fun x hx => hx
  have h2 : ∫⁻ x in A, ENNReal.ofReal (Real.sqrt c) ∂μ ≤ ∫⁻ x in A, f x ∂μ :=
    setLIntegral_mono hf_meas h2a
  have h3 : ∫⁻ x in A, ENNReal.ofReal (Real.sqrt c) ∂μ =
      ENNReal.ofReal (Real.sqrt c) * μ A := by simp
  have h4 : ENNReal.ofReal (Real.sqrt c) * μ A ≤ (μ.prod ν) E := by
    calc
      ENNReal.ofReal (Real.sqrt c) * μ A
        = ∫⁻ x in A, ENNReal.ofReal (Real.sqrt c) ∂μ := h3.symm
      _ ≤ ∫⁻ x in A, f x ∂μ := h2
      _ ≤ ∫⁻ x, f x ∂μ := h1
      _ = (μ.prod ν) E := h_fubini.symm
  have h5 : ENNReal.ofReal (Real.sqrt c) * μ A ≤ ENNReal.ofReal c := le_trans h4 h_main
  have h_sqrt_sq : Real.sqrt c * Real.sqrt c = c := by
    have h : Real.sqrt c * Real.sqrt c = (Real.sqrt c) ^ 2 := by ring
    rw [h, Real.sq_sqrt (by linarith)]
  have h6 : ENNReal.ofReal c =
      ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal (Real.sqrt c) := by
    have h7 : ENNReal.ofReal (Real.sqrt c * Real.sqrt c) =
        ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal (Real.sqrt c) := by
      rw [ENNReal.ofReal_mul (by positivity)] <;> rfl
    have h8 : ENNReal.ofReal c = ENNReal.ofReal (Real.sqrt c * Real.sqrt c) := by rw [h_sqrt_sq]
    rw [h8, h7]
  rw [h6] at h5
  have h_sqrt_ne_zero : ENNReal.ofReal (Real.sqrt c) ≠ 0 := by
    simp [h_sqrt_pos.ne'] <;> linarith
  have h_sqrt_ne_top : ENNReal.ofReal (Real.sqrt c) ≠ ⊤ := by simp
  have h_iff : ENNReal.ofReal (Real.sqrt c) * μ A ≤
      ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal (Real.sqrt c) ↔
    μ A ≤ ENNReal.ofReal (Real.sqrt c) :=
    ENNReal.mul_le_mul_iff_right h_sqrt_ne_zero h_sqrt_ne_top
  exact h_iff.mp h5

/-! ### 3. Intersection measure lower bound -/

/-- If `μ A ≥ 1 - a` and `μ B ≥ 1 - b` under a probability measure `μ`, with
`a, b ≥ 0` and `a + b ≤ 1`, then `μ (A ∩ B) ≥ 1 - a - b`. -/
lemma measure_inter_lowerBound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {A B : Set α}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)
    (h1 : μ A ≥ ENNReal.ofReal (1 - a))
    (h2 : μ B ≥ ENNReal.ofReal (1 - b)) :
    μ (A ∩ B) ≥ ENNReal.ofReal (1 - a - b) := by
  have h_eq : μ (A ∪ B) + μ (A ∩ B) = μ A + μ B := measure_union_add_inter' hA B
  have h_union_le_one : μ (A ∪ B) ≤ 1 := prob_le_one
  have h4 : μ A + μ B ≥ ENNReal.ofReal (1 - a) + ENNReal.ofReal (1 - b) := add_le_add h1 h2
  have h5 : ENNReal.ofReal (1 - a) + ENNReal.ofReal (1 - b) = ENNReal.ofReal (2 - a - b) := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)] <;> ring_nf
  have h6 : μ (A ∪ B) + μ (A ∩ B) ≥ ENNReal.ofReal (2 - a - b) := by
    calc
      μ (A ∪ B) + μ (A ∩ B) = μ A + μ B := h_eq
      _ ≥ ENNReal.ofReal (1 - a) + ENNReal.ofReal (1 - b) := h4
      _ = ENNReal.ofReal (2 - a - b) := h5
  have h7 : ENNReal.ofReal (2 - a - b) ≤ (1 : ENNReal) + μ (A ∩ B) := by
    calc
      ENNReal.ofReal (2 - a - b) ≤ μ (A ∪ B) + μ (A ∩ B) := h6
      _ ≤ (1 : ENNReal) + μ (A ∩ B) := add_le_add h_union_le_one (le_refl _)
  have h8 : ENNReal.ofReal (2 - a - b) - (1 : ENNReal) ≤ μ (A ∩ B) := by
    exact tsub_le_iff_left.mpr h7
  have h_one : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
  have h9 : ENNReal.ofReal (2 - a - b) - (1 : ENNReal) = ENNReal.ofReal (1 - a - b) := by
    rw [h_one]
    have h10 : ENNReal.ofReal ((2 - a - b) - 1) =
        ENNReal.ofReal (2 - a - b) - ENNReal.ofReal 1 :=
      ENNReal.ofReal_sub (2 - a - b) (by norm_num)
    have h11 : (2 - a - b) - 1 = 1 - a - b := by ring
    rw [h11] at h10
    exact h10.symm
  rw [h9] at h8
  exact h8

/-! ### 4. Tube fiber measurability -/

/-- For a measurable set `E ⊆ α × β` and a measurable set `T ⊆ β`, the set
`{x : α | ν (T ∩ E|_x) ≥ a}` is measurable for any threshold `a : ENNReal`. -/
lemma tube_fiber_measurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure β} [SFinite ν]
    {E : Set (α × β)} (hE : MeasurableSet E)
    {T : Set β} (hT : MeasurableSet T)
    {a : ENNReal} :
    MeasurableSet {x : α | ν (T ∩ (Prod.mk x ⁻¹' E)) ≥ a} := by
  let S : Set (α × β) := (Set.univ ×ˢ T) ∩ E
  have hS : MeasurableSet S := (MeasurableSet.univ.prod hT).inter hE
  have h_eq : ∀ (x : α), T ∩ (Prod.mk x ⁻¹' E) = Prod.mk x ⁻¹' S := by
    intro x
    ext y
    simp only [S, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    <;> rfl
  let g : α → ENNReal := fun x => ν (T ∩ (Prod.mk x ⁻¹' E))
  have hg_meas : Measurable g := by
    have h_eq2 : g = fun x : α => ν (Prod.mk x ⁻¹' S) := by
      funext x
      have h : g x = ν (T ∩ (Prod.mk x ⁻¹' E)) := by rfl
      rw [h]
      exact congr_arg ν (h_eq x)
    rw [h_eq2]
    exact measurable_measure_prodMk_left hS
  have h_set : {x : α | g x ≥ a} = g ⁻¹' (Set.Ici a) := by
    ext x; simp
  rw [h_set]
  exact hg_meas measurableSet_Ici

/-! ### 5. Fix y by Fubini -/

/-- Given `H'' ⊂ X × Y` with `(μ.prod ν) H'' ≥ c` (where `0 < c ≤ 1`), there
exists `y ∈ Y` such that the vertical fiber `H''|^y := {x | (x,y) ∈ H''}` has
`μ`-measure at least `c`.

Proof: If every fiber had measure `< c`, then `g < c` everywhere but `∫⁻ g ≥ c`.
By `ae_eq_of_ae_le_of_lintegral_le`, `g = c` a.e., contradicting `g < c` everywhere. -/
lemma fubini_fix_y {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H'' : Set (α × β)} (hH'' : MeasurableSet H'')
    {c : ℝ} (hc_pos : 0 < c) (hc_le_one : c ≤ 1)
    (h_main : (μ.prod ν) H'' ≥ ENNReal.ofReal c) :
    ∃ (y : β), μ ((fun x => (x, y)) ⁻¹' H'') ≥ ENNReal.ofReal c := by
  let g : β → ENNReal := fun y => μ ((fun x => (x, y)) ⁻¹' H'')
  have hg_meas : Measurable g := measurable_measure_prodMk_right hH''
  have h_fubini : (μ.prod ν) H'' = ∫⁻ y, g y ∂ν := Measure.prod_apply_symm hH''
  have h_int_ge : ∫⁻ y, g y ∂ν ≥ ENNReal.ofReal c := by
    rw [← h_fubini]; exact h_main
  by_cases h : ∃ (y : β), g y ≥ ENNReal.ofReal c
  · rcases h with ⟨y, hy⟩
    exact ⟨y, hy⟩
  · have h1 : ∀ y, g y < ENNReal.ofReal c := by
      intro y
      have h2 : ¬(g y ≥ ENNReal.ofReal c) := by
        intro h3
        exact h ⟨y, h3⟩
      exact lt_of_not_ge h2
    have h2 : ∀ y, g y ≤ ENNReal.ofReal c := fun y => le_of_lt (h1 y)
    let c_const : β → ENNReal := fun _ => ENNReal.ofReal c
    have h2ae : g ≤ᵐ[ν] c_const := by
      filter_upwards with y
      exact h2 y
    have h_univ : ν Set.univ = 1 := by exact measure_univ
    have h4 : ∫⁻ y, g y ∂ν ≤ ∫⁻ y, c_const y ∂ν := by exact lintegral_mono_ae h2ae
    have h5 : ∫⁻ y, c_const y ∂ν = ENNReal.ofReal c := by
      have h51 : ∫⁻ y, c_const y ∂ν = ENNReal.ofReal c * ν Set.univ := by
        simp [c_const] <;> rfl
      rw [h51, h_univ] <;> simp
    have h3 : ∫⁻ y, g y ∂ν ≠ ⊤ := by
      rw [h5] at h4
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h4
    have h6 : ∫⁻ y, c_const y ∂ν ≤ ∫⁻ y, g y ∂ν := by
      rw [h5]
      exact h_int_ge
    have h8 : g =ᵐ[ν] c_const :=
      ae_eq_of_ae_le_of_lintegral_le h2ae h3 (measurable_const.aemeasurable) h6
    have h9 : ν {y : β | g y ≠ c_const y} = 0 := h8
    have h10 : {y : β | g y ≠ c_const y} = Set.univ := by
      ext y
      simp only [Set.mem_univ, iff_true]
      have h11 : g y < c_const y := h1 y
      exact ne_of_lt h11
    rw [h10] at h9
    rw [h_univ] at h9
    simp at h9

/-! ### 6. Finite pigeonhole for product measure -/

/-- Given finitely many measurable sets `H_0, ..., H_N ⊂ X × Y` with
`(μ.prod ν)(⋃ H_i) ≥ c`, there exists `i` such that
`(μ.prod ν)(H_i) ≥ c / (N + 1)`. -/
lemma finite_pigeonhole {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    {N : ℕ} (H : Fin (N + 1) → Set (α × β))
    (hH : ∀ i, MeasurableSet (H i))
    {c : ℝ} (hc_pos : 0 < c)
    (h_main : (μ.prod ν) (⋃ i, H i) ≥ ENNReal.ofReal c) :
    ∃ (i : Fin (N + 1)), (μ.prod ν) (H i) ≥ ENNReal.ofReal (c / (N + 1 : ℝ)) := by
  by_contra h
  push Not at h
  have h1 : ∀ i, (μ.prod ν) (H i) < ENNReal.ofReal (c / (N + 1 : ℝ)) := h
  let b : ENNReal := ENNReal.ofReal (c / (N + 1 : ℝ))
  have h_b_ne_top : b ≠ ⊤ := by simp [b]
  let i0 : Fin (N + 1) := 0
  let s : Finset (Fin (N + 1)) := (Finset.univ.erase i0)
  have h_nsmul_real : ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
      n • ENNReal.ofReal x = ENNReal.ofReal ((n : ℝ) * x) := by
    intro n x hx
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : n.succ • ENNReal.ofReal x = n • ENNReal.ofReal x + ENNReal.ofReal x := by
        simp [Nat.succ_eq_add_one, succ_nsmul] <;> ring
      rw [h1]
      have h_ih' : n • ENNReal.ofReal x = ENNReal.ofReal ((n : ℝ) * x) := ih
      rw [h_ih']
      have h2 : ENNReal.ofReal ((n : ℝ) * x) + ENNReal.ofReal x =
          ENNReal.ofReal ((n : ℝ) * x + x) := by
        rw [← ENNReal.ofReal_add (by positivity) hx] <;> ring
      rw [h2]
      have h3 : (n : ℝ) * x + x = ((n.succ : ℝ)) * x := by
        simp [Nat.cast_add, Nat.cast_one] <;> ring
      rw [h3] <;> rfl
  have h_sum_eq : ∑ i ∈ (Finset.univ : Finset (Fin (N + 1))), b = ENNReal.ofReal c := by
    have h_card : (Finset.univ : Finset (Fin (N + 1))).card = N + 1 := by simp
    rw [Finset.sum_const, h_card]
    have h_b_def : b = ENNReal.ofReal (c / (N + 1 : ℝ)) := by rfl
    have h_pos : 0 ≤ c / (N + 1 : ℝ) := by positivity
    have h_goal : (N + 1) • b = ENNReal.ofReal c := by
      rw [h_b_def]
      have h := h_nsmul_real (N + 1) (c / (N + 1 : ℝ)) h_pos
      have h_eq : ((N + 1 : ℝ)) * (c / (N + 1 : ℝ)) = c := by field_simp <;> ring
      simpa [h_eq] using h
    exact h_goal
  have h_sum_le : ∑ i ∈ s, (μ.prod ν) (H i) ≤ ∑ i ∈ s, b := by
    apply Finset.sum_le_sum
    intro i _
    exact le_of_lt (h1 i)
  have h_all_finite : ∀ i ∈ s, (μ.prod ν) (H i) ≠ ⊤ := by
    intro i _
    have h_lt : (μ.prod ν) (H i) < b := h1 i
    exact ne_top_of_lt h_lt
  have h_sum_H_finite : ∑ i ∈ s, (μ.prod ν) (H i) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr h_all_finite
  have h_i0_lt : (μ.prod ν) (H i0) < b := h1 i0
  have h_univ_eq : (Finset.univ : Finset (Fin (N + 1))) = insert i0 s := by
    ext x
    simp [s, Finset.mem_erase]
    <;> tauto
  have h_sum_strict : ∑ i ∈ (Finset.univ : Finset (Fin (N + 1))), (μ.prod ν) (H i) <
      ∑ i ∈ (Finset.univ : Finset (Fin (N + 1))), b := by
    rw [h_univ_eq, Finset.sum_insert (by simp [s]), Finset.sum_insert (by simp [s])]
    have h_strict1 : (μ.prod ν) (H i0) + ∑ i ∈ s, (μ.prod ν) (H i) <
        b + ∑ i ∈ s, (μ.prod ν) (H i) :=
      ENNReal.add_lt_add_right h_sum_H_finite h_i0_lt
    have h_strict2 : b + ∑ i ∈ s, (μ.prod ν) (H i) ≤ b + ∑ i ∈ s, b := by
      have h_comm1 : b + ∑ i ∈ s, (μ.prod ν) (H i) =
          ∑ i ∈ s, (μ.prod ν) (H i) + b := by exact add_comm _ _
      have h_comm2 : b + ∑ i ∈ s, b = ∑ i ∈ s, b + b := by exact add_comm _ _
      rw [h_comm1, h_comm2]
      exact add_le_add_left h_sum_le b
    exact lt_of_lt_of_le h_strict1 h_strict2
  have h3 : (μ.prod ν) (⋃ i : Fin (N + 1), H i) ≤
      ∑ i ∈ (Finset.univ : Finset (Fin (N + 1))), (μ.prod ν) (H i) := by
    have h_tsum : (μ.prod ν) (⋃ i : Fin (N + 1), H i) ≤
        ∑' i : Fin (N + 1), (μ.prod ν) (H i) := measure_iUnion_le _
    have h_eq_tsum : ∑' i : Fin (N + 1), (μ.prod ν) (H i) =
        ∑ i ∈ (Finset.univ : Finset (Fin (N + 1))), (μ.prod ν) (H i) := by
      rw [tsum_fintype] <;> rfl
    rw [h_eq_tsum] at h_tsum
    exact h_tsum
  rw [h_sum_eq] at h_sum_strict
  have h4 : (μ.prod ν) (⋃ i : Fin (N + 1), H i) < ENNReal.ofReal c :=
    lt_of_le_of_lt h3 h_sum_strict
  exact False.elim (not_le.mpr h4 h_main)

/-! ### 7. Localization lemma -/

/-- Given a set `X` of measure at least `m > 0`, there exists `R > 0` such that
`X ∩ closedBall 0 R` has measure at least `m / 2`.

Proof: the balls `closedBall 0 (n+1)` exhaust `Set.univ`, so by continuity
from below, `ν(X ∩ closedBall 0 (n+1)) ↑ ν(X)`. If every such intersection
had measure `< m/2`, the supremum would be `≤ m/2 < m ≤ ν(X)`, a contradiction. -/
lemma localize_measure {ν : Measure Point} [IsProbabilityMeasure ν]
    {X : Set Point} {m : ℝ} (hm : 0 < m)
    (hX : ν X ≥ ENNReal.ofReal m) :
    ∃ (R : ℝ), 0 < R ∧ ν (X ∩ closedBall 0 R) ≥ ENNReal.ofReal (m / 2) := by
  let f : ℕ → Set Point := fun n => X ∩ closedBall 0 ((n + 1 : ℝ))
  have hf_mono : Monotone f := by
    intro a b hab
    intro x hx
    have h' : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
    have h : (a + 1 : ℝ) ≤ (b + 1 : ℝ) := by linarith
    exact ⟨hx.1, closedBall_subset_closedBall h hx.2⟩
  have h_union : (⋃ n : ℕ, f n) = X := by
    ext x
    simp only [f, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hx, _⟩; exact hx
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge (dist 0 x)
      have h5 : dist 0 x ≤ (n + 1 : ℝ) := by
        have h6 : (n : ℝ) ≤ (n + 1 : ℝ) := by simp
        exact le_trans hn h6
      have h7 : x ∈ closedBall 0 ((n + 1 : ℝ)) := by
        simpa [Metric.mem_closedBall] using h5
      exact ⟨n, hx, h7⟩
  have h_cont : ν X = ⨆ n : ℕ, ν (f n) := by
    have h1 : ν (⋃ n : ℕ, f n) = ⨆ n : ℕ, ν (f n) := by
      exact Monotone.measure_iUnion hf_mono
    rw [h_union] at h1
    exact h1
  have h_half_pos : 0 < m / 2 := by linarith
  have h_half_lt : ENNReal.ofReal (m / 2) < ENNReal.ofReal m := by
    rw [ENNReal.ofReal_lt_ofReal_iff] <;> linarith
  by_cases h : ∃ n : ℕ, ν (f n) ≥ ENNReal.ofReal (m / 2)
  · rcases h with ⟨n, hn⟩
    refine' ⟨(n + 1 : ℝ), by positivity, _⟩
    simpa [f] using hn
  · have h_all : ∀ n : ℕ, ¬(ν (f n) ≥ ENNReal.ofReal (m / 2)) := by
      simpa [not_exists] using h
    have h' : ∀ n : ℕ, ν (f n) ≤ ENNReal.ofReal (m / 2) := by
      intro n
      exact le_of_not_ge (h_all n)
    have h4 : (⨆ n : ℕ, ν (f n)) ≤ ENNReal.ofReal (m / 2) := iSup_le h'
    have h4' : ν X ≤ ENNReal.ofReal (m / 2) := by
      calc
        ν X = ⨆ n : ℕ, ν (f n) := h_cont
        _ ≤ ENNReal.ofReal (m / 2) := h4
    exact False.elim (not_le.mpr h_half_lt (le_trans hX h4'))

end RadialBootstrapping
