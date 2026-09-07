module

/-
  Lower bound on code function from IsDeltaSSet property.

  Given a uniform set P that is also a (δ, t, C)-S-set, the code function
  satisfies f(j) ≥ t*j - ε*m - O(m), where the O(m) constant depends on Δ.

  This is a key ingredient for multiscaleDecompKaufman.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MultiscaleDecomposition

namespace CodeFunctionLowerBound

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Coordinate absolute value bounded by Euclidean norm. -/
lemma coord_abs_le_norm (x : Plane) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  have h1 : ‖x‖^2 = (x 0)^2 + (x 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
  have h_nonneg1 : 0 ≤ (x 0)^2 := by positivity
  have h_nonneg2 : 0 ≤ (x 1)^2 := by positivity
  have h2 : (x i)^2 ≤ ‖x‖^2 := by
    rw [h1]
    fin_cases i
    · exact le_add_of_nonneg_right h_nonneg2
    · exact le_add_of_nonneg_left h_nonneg1
  have h4 : (|x i|)^2 = (x i)^2 := by rw [sq_abs]
  have h5 : (|x i|)^2 ≤ ‖x‖^2 := by
    rw [h4]; exact h2
  have h6 : 0 ≤ |x i| := by positivity
  have h7 : 0 ≤ ‖x‖ := by positivity
  nlinarith

/-- P ⊆ B(0,1) is covered by at most 9 scale-1 dyadic squares. -/
lemma nine_squares_cover (P : Set Plane) (hP : P ⊆ Metric.closedBall (0 : Plane) 1) :
    ∃ (S : Finset (ℤ × ℤ)), S.card ≤ 9 ∧
      P ⊆ ⋃ p ∈ S, dyadicSquare (1 : ℝ) p.1 p.2 := by
  rcases ball_intersects_9_squares (1 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (0 : Plane)
    with ⟨S, hS_mem, hS_card⟩
  have h_cover : P ⊆ ⋃ p ∈ S, dyadicSquare (1 : ℝ) p.1 p.2 := by
    intro x hx
    have hxBall : x ∈ Metric.closedBall (0 : Plane) 1 := hP hx
    let a : ℤ := ⌊x 0⌋
    let b : ℤ := ⌊x 1⌋
    have ha1 : (a : ℝ) ≤ x 0 := Int.floor_le (x 0)
    have ha2 : x 0 < (a : ℝ) + 1 := Int.lt_floor_add_one (x 0)
    have hb1 : (b : ℝ) ≤ x 1 := Int.floor_le (x 1)
    have hb2 : x 1 < (b : ℝ) + 1 := Int.lt_floor_add_one (x 1)
    have hx_sq : x ∈ dyadicSquare (1 : ℝ) a b := by
      simp only [dyadicSquare, Set.mem_setOf_eq]
      constructor
      · simpa using ⟨ha1, ha2⟩
      · simpa using ⟨hb1, hb2⟩
    have h_inter : (Metric.closedBall (0 : Plane) 1 ∩ dyadicSquare (1 : ℝ) a b).Nonempty :=
      ⟨x, hxBall, hx_sq⟩
    have hab : (a, b) ∈ S := hS_mem a b h_inter
    have h_goal : x ∈ ⋃ p ∈ S, dyadicSquare (1 : ℝ) p.1 p.2 := by
      simp only [Set.mem_iUnion]
      exact ⟨(a, b), hab, hx_sq⟩
    exact h_goal
  exact ⟨S, hS_card, h_cover⟩

/-- Upper bound on covering number of P ∩ scale-1 square. -/
lemma covering_upper_per_square {P : Set Plane} {m j : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsUniform P m Δ N) (hj : j ≤ m) (a b : ℤ) :
    (Metric.externalCoveringNumber (Δ ^ j).toNNReal
       (P ∩ dyadicSquare (1 : ℝ) a b) : ENNReal) ≤
      (9 : ENNReal) ^ j * ∏ i ∈ Finset.range j, (↑(N i) : ENNReal) := by
  by_cases hQ : (P ∩ dyadicSquare (1 : ℝ) a b).Nonempty
  · have h_uniform_j : IsUniform P j Δ N :=
      ⟨h_uniform.1, h_uniform.2.1, h_uniform.2.2.1,
       fun i hi => h_uniform.2.2.2.1 i (by linarith),
       fun i hi => h_uniform.2.2.2.2 i (by linarith)⟩
    have h_delta0 : (Δ ^ 0 : ℝ) = 1 := by simp
    have hQ' : (P ∩ dyadicSquare (Δ ^ 0) a b).Nonempty := by
      rw [h_delta0] at *; exact hQ
    have h_main := covering_product_upper h_uniform_j (by linarith) a b hQ'
    have h_goal : (Metric.externalCoveringNumber (Δ ^ j).toNNReal
                       (P ∩ dyadicSquare (Δ ^ 0) a b) : ENNReal) ≤
                     (9 : ENNReal) ^ j * ∏ i ∈ Finset.range j, (↑(N i) : ENNReal) := by
      simpa [h_delta0] using h_main
    rw [h_delta0] at h_goal
    exact h_goal
  · have h_empty : P ∩ dyadicSquare (1 : ℝ) a b = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using hQ
    rw [h_empty]
    simp

/-- Total upper bound: N_{Δ^j}(P) ≤ 9^{j+1} * ∏ N(i) for P in unit ball. -/
lemma covering_upper_total {P : Set Plane} {m j : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsUniform P m Δ N) (hj : j ≤ m)
    (hP : P ⊆ Metric.closedBall (0 : Plane) 1) :
    (Metric.externalCoveringNumber (Δ ^ j).toNNReal P : ENNReal) ≤
      (9 : ENNReal) ^ (j + 1) * ∏ i ∈ Finset.range j, (↑(N i) : ENNReal) := by
  rcases nine_squares_cover P hP with ⟨S, hS_card, h_cover⟩
  let A : (ℤ × ℤ) → Set Plane := fun p => P ∩ dyadicSquare (1 : ℝ) p.1 p.2
  let U : Set Plane := ⋃ p ∈ S, A p
  have h_coverU : P ⊆ U := by
    intro x hx
    have h3 : x ∈ ⋃ p ∈ S, dyadicSquare (1 : ℝ) p.1 p.2 := h_cover hx
    have h4 : ∃ (p : ℤ × ℤ), p ∈ S ∧ x ∈ dyadicSquare (1 : ℝ) p.1 p.2 := by
      simpa [Set.mem_iUnion] using h3
    rcases h4 with ⟨p, hp, h5⟩
    have h6 : x ∈ A p := ⟨hx, h5⟩
    have h7 : x ∈ U := by
      simp only [U, Set.mem_iUnion]
      exact ⟨p, hp, h6⟩
    exact h7
  have h_sub : (Metric.externalCoveringNumber (Δ ^ j).toNNReal P : ENNReal) ≤
      (Metric.externalCoveringNumber (Δ ^ j).toNNReal U : ENNReal) := by
    have h : Metric.externalCoveringNumber (Δ ^ j).toNNReal P ≤
        Metric.externalCoveringNumber (Δ ^ j).toNNReal U :=
      Metric.externalCoveringNumber_mono_set h_coverU
    exact_mod_cast h
  letI : Fintype {p : ℤ × ℤ // p ∈ S} := by exact S.fintypeCoeSort
  let A' : {p : ℤ × ℤ // p ∈ S} → Set Plane := fun i => A i.val
  have hU_eq : U = ⋃ (i : {p // p ∈ S}), A' i := by
    ext y
    simp only [U, A', Set.mem_iUnion]
    constructor
    · rintro ⟨p, hp, hy⟩
      exact ⟨⟨p, hp⟩, hy⟩
    · rintro ⟨i, hy⟩
      exact ⟨i.val, i.property, hy⟩
  rw [hU_eq] at h_sub
  let ε' := (Δ ^ j).toNNReal
  let f : {p // p ∈ S} → ENNReal := fun i =>
    (Metric.externalCoveringNumber ε' (A' i) : ENNReal)
  have h_sum_enat : Metric.externalCoveringNumber ε' (⋃ (i : {p // p ∈ S}), A' i) ≤
      ∑ (i : {p // p ∈ S}), Metric.externalCoveringNumber ε' (A' i) :=
    externalCoveringNumber_iUnion_le
  have h_coe_sum : (↑(∑ (i : {p // p ∈ S}), Metric.externalCoveringNumber ε' (A' i)) : ENNReal) =
      ∑ (i : {p // p ∈ S}), f i := by
    have h_main : ∀ (s : Finset {p // p ∈ S}),
        (↑(∑ i ∈ s, Metric.externalCoveringNumber ε' (A' i)) : ENNReal) =
        ∑ i ∈ s, f i := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | @insert a s ha ih =>
        have h1 : (↑(Metric.externalCoveringNumber ε' (A' a) + ∑ x ∈ s, Metric.externalCoveringNumber ε' (A' x)) : ENNReal) =
            (Metric.externalCoveringNumber ε' (A' a) : ENNReal) + (↑(∑ x ∈ s, Metric.externalCoveringNumber ε' (A' x)) : ENNReal) := by
          exact ENat.toENNReal_add (Metric.externalCoveringNumber ε' (A' a))
            (∑ x ∈ s, Metric.externalCoveringNumber ε' (A' x))
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [h1, ih]
        <;> rfl
    exact h_main Finset.univ
  have h_sum : (Metric.externalCoveringNumber ε' (⋃ (i : {p // p ∈ S}), A' i) : ENNReal) ≤ ∑ i, f i := by
    have h_coe : (Metric.externalCoveringNumber ε' (⋃ (i : {p // p ∈ S}), A' i) : ENNReal) ≤
        (↑(∑ (i : {p // p ∈ S}), Metric.externalCoveringNumber ε' (A' i)) : ENNReal) := by
      exact_mod_cast h_sum_enat
    rw [h_coe_sum] at h_coe
    exact h_coe
  let B : ENNReal := (9 : ENNReal) ^ j * ∏ k ∈ Finset.range j, (↑(N k) : ENNReal)
  have h_each : ∀ i, f i ≤ B := by
    intro i
    exact covering_upper_per_square h_uniform hj i.val.1 i.val.2
  have h_sum2 : ∑ i, f i ≤ ∑ i : {p // p ∈ S}, B := Finset.sum_le_sum fun i _ => h_each i
  have h_card : Fintype.card {p // p ∈ S} = S.card := by simp
  have h_sum3 : ∑ i : {p // p ∈ S}, B = (Fintype.card {p // p ∈ S}) * B := by
    have h : ∑ i ∈ (Finset.univ : Finset {p // p ∈ S}), B =
        (Finset.univ : Finset {p // p ∈ S}).card • B := Finset.sum_const B
    rw [h]
    have h2 : (Finset.univ : Finset {p // p ∈ S}).card • B =
        (↑(Fintype.card {p // p ∈ S}) : ENNReal) * B := by
      simp [Finset.card_univ]
      <;> rfl
    exact h2
  calc (Metric.externalCoveringNumber ε' P : ENNReal)
    ≤ (Metric.externalCoveringNumber ε' (⋃ (i : {p // p ∈ S}), A' i) : ENNReal) := h_sub
  _ ≤ ∑ i, f i := h_sum
  _ ≤ ∑ i : {p // p ∈ S}, B := h_sum2
  _ = (Fintype.card {p // p ∈ S}) * B := h_sum3
  _ = S.card * B := by rw [h_card]
  _ ≤ 9 * B := by gcongr <;> exact_mod_cast hS_card
  _ = (9 : ENNReal) ^ (j + 1) * ∏ k ∈ Finset.range j, (↑(N k) : ENNReal) := by
    dsimp only [B]
    rw [pow_succ] <;> ring

/-- Dyadic total upper bound: N_{Δ^j}(P) ≤ 9^{j+1} * ∏ N(i) for P in unit ball. -/
lemma dyadicCovering_upper_total {P : Set Plane} {m j : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N) (hj : j ≤ m)
    (hP : P ⊆ Metric.closedBall (0 : Plane) 1) :
    (Metric.externalCoveringNumber (Δ ^ j).toNNReal P : ENNReal) ≤
      (9 : ENNReal) ^ (j + 1) * ∏ i ∈ Finset.range j, (↑(N i) : ENNReal) := by
  rcases nine_squares_cover P hP with ⟨S, hS_card, h_cover⟩
  let A : (ℤ × ℤ) → Set Plane := fun p => P ∩ dyadicSquare (1 : ℝ) p.1 p.2
  let U : Set Plane := ⋃ p ∈ S, A p
  have h_coverU : P ⊆ U := by
    intro x hx
    have h3 : x ∈ ⋃ p ∈ S, dyadicSquare (1 : ℝ) p.1 p.2 := h_cover hx
    have h4 : ∃ (p : ℤ × ℤ), p ∈ S ∧ x ∈ dyadicSquare (1 : ℝ) p.1 p.2 := by
      simpa [Set.mem_iUnion] using h3
    rcases h4 with ⟨p, hp, h5⟩
    have h6 : x ∈ A p := ⟨hx, h5⟩
    have h7 : x ∈ U := by
      simp only [U, Set.mem_iUnion]
      exact ⟨p, hp, h6⟩
    exact h7
  have h_sub : (Metric.externalCoveringNumber (Δ ^ j).toNNReal P : ENNReal) ≤
      (Metric.externalCoveringNumber (Δ ^ j).toNNReal U : ENNReal) := by
    have h : Metric.externalCoveringNumber (Δ ^ j).toNNReal P ≤
        Metric.externalCoveringNumber (Δ ^ j).toNNReal U :=
      Metric.externalCoveringNumber_mono_set h_coverU
    exact_mod_cast h
  letI : Fintype {p : ℤ × ℤ // p ∈ S} := by exact S.fintypeCoeSort
  let A' : {p : ℤ × ℤ // p ∈ S} → Set Plane := fun i => A i.val
  have hU_eq : U = ⋃ (i : {p // p ∈ S}), A' i := by
    ext y
    simp only [U, A', Set.mem_iUnion]
    constructor
    · rintro ⟨p, hp, hy⟩
      exact ⟨⟨p, hp⟩, hy⟩
    · rintro ⟨i, hy⟩
      exact ⟨i.val, i.property, hy⟩
  rw [hU_eq] at h_sub
  let ε' := (Δ ^ j).toNNReal
  let f : {p // p ∈ S} → ENNReal := fun i =>
    (Metric.externalCoveringNumber ε' (A' i) : ENNReal)
  have h_sum_enat : Metric.externalCoveringNumber ε' (⋃ (i : {p // p ∈ S}), A' i) ≤
      ∑ (i : {p // p ∈ S}), Metric.externalCoveringNumber ε' (A' i) :=
    externalCoveringNumber_iUnion_le
  have h_coe_sum : (↑(∑ (i : {p // p ∈ S}), Metric.externalCoveringNumber ε' (A' i)) : ENNReal) =
      ∑ (i : {p // p ∈ S}), f i := by
    have h_main : ∀ (s : Finset {p // p ∈ S}),
        (↑(∑ i ∈ s, Metric.externalCoveringNumber ε' (A' i)) : ENNReal) =
        ∑ i ∈ s, f i := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | @insert a s ha ih =>
        have h1 : (↑(Metric.externalCoveringNumber ε' (A' a) + ∑ x ∈ s, Metric.externalCoveringNumber ε' (A' x)) : ENNReal) =
            (Metric.externalCoveringNumber ε' (A' a) : ENNReal) + (↑(∑ x ∈ s, Metric.externalCoveringNumber ε' (A' x)) : ENNReal) := by
          exact ENat.toENNReal_add (Metric.externalCoveringNumber ε' (A' a))
            (∑ x ∈ s, Metric.externalCoveringNumber ε' (A' x))
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [h1, ih] <;> rfl
    exact h_main Finset.univ
  have h_sum : (Metric.externalCoveringNumber ε' (⋃ (i : {p // p ∈ S}), A' i) : ENNReal) ≤ ∑ i, f i := by
    have h_coe : (Metric.externalCoveringNumber ε' (⋃ (i : {p // p ∈ S}), A' i) : ENNReal) ≤
        (↑(∑ (i : {p // p ∈ S}), Metric.externalCoveringNumber ε' (A' i)) : ENNReal) := by
      exact_mod_cast h_sum_enat
    rw [h_coe_sum] at h_coe
    exact h_coe
  let B : ENNReal := (9 : ENNReal) ^ j * ∏ k ∈ Finset.range j, (↑(N k) : ENNReal)
  have h_each : ∀ i, f i ≤ B := by
    intro i
    exact dyadicCovering_upper_per_square h_uniform hj i.val.1 i.val.2
  have h_sum2 : ∑ i, f i ≤ ∑ i : {p // p ∈ S}, B := Finset.sum_le_sum fun i _ => h_each i
  have h_card : Fintype.card {p // p ∈ S} = S.card := by simp
  have h_sum3 : ∑ i : {p // p ∈ S}, B = (Fintype.card {p // p ∈ S}) * B := by
    have h : ∑ i ∈ (Finset.univ : Finset {p // p ∈ S}), B =
        (Finset.univ : Finset {p // p ∈ S}).card • B := Finset.sum_const B
    rw [h]
    have h2 : (Finset.univ : Finset {p // p ∈ S}).card • B =
        (↑(Fintype.card {p // p ∈ S}) : ENNReal) * B := by
      simp [Finset.card_univ] <;> rfl
    exact h2
  calc (Metric.externalCoveringNumber ε' P : ENNReal)
    ≤ (Metric.externalCoveringNumber ε' (⋃ (i : {p // p ∈ S}), A' i) : ENNReal) := h_sub
  _ ≤ ∑ i, f i := h_sum
  _ ≤ ∑ i : {p // p ∈ S}, B := h_sum2
  _ = (Fintype.card {p // p ∈ S}) * B := h_sum3
  _ = S.card * B := by rw [h_card]
  _ ≤ 9 * B := by gcongr <;> exact_mod_cast hS_card
  _ = (9 : ENNReal) ^ (j + 1) * ∏ k ∈ Finset.range j, (↑(N k) : ENNReal) := by
    dsimp only [B]
    rw [pow_succ] <;> ring

/-- Main lower bound: from S-set property, code function satisfies
    f(j) ≥ t*j - ε*m - (m+1)*log(9)/log(1/Δ). -/
lemma codeFunction_lower_bound {P : Set Plane} {m j : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    {t ε : ℝ}
    (h_uniform : IsDyadicUniform P m Δ N) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (ht : 0 ≤ t) (hε : 0 < ε)
    (hj : j ≤ m) (hm_pos : 0 < m)
    (hP : P ⊆ Metric.closedBall (0 : Plane) 1)
    (h_sset : IsDeltaSSet (Δ ^ m) t (Real.rpow (Δ ^ m) (-ε)) P) :
    codeFunction m Δ N (j : ℝ) ≥ t * (j : ℝ) - ε * (m : ℝ) -
      ((m : ℝ) + 1) * Real.log 9 / Real.log (1 / Δ) := by
  set δ : ℝ := Δ ^ m with hδ_def
  set C : ℝ := Real.rpow (Δ ^ m) (-ε) with hC_def
  have hδ_pos : 0 < δ := by positivity
  have hC_pos : 0 < C := Real.rpow_pos_of_pos hδ_pos _
  have hP_nonempty : P.Nonempty := h_uniform.2.2.1
  have hN_pos : ∀ i < m, N i ≥ 1 := h_uniform.2.2.2.1
  let δ' : NNReal := δ.toNNReal
  let r_j' : NNReal := (Δ ^ j).toNNReal
  have hδ_le_j : δ ≤ Δ ^ j := by
    have h1 : 0 ≤ Δ := by linarith
    have h2 : Δ ≤ 1 := by linarith
    have h3 : Δ ^ m ≤ Δ ^ j := by
      apply pow_le_pow_of_le_one h1 h2 <;> omega
    simpa [hδ_def] using h3

  -- Step 1: N_δ(P) is positive and finite (using dyadicCovering_upper_total at scale m)
  have h_upper_m := dyadicCovering_upper_total h_uniform (by linarith) hP
  have hNδ_pos_enat : 0 < Metric.externalCoveringNumber δ' P :=
    Metric.externalCoveringNumber_pos_iff.mpr hP_nonempty
  have hNδ_pos : (Metric.externalCoveringNumber δ' P : ENNReal) ≠ 0 := by
    have h' : (0 : ENNReal) < (Metric.externalCoveringNumber δ' P : ENNReal) := by
      exact_mod_cast hNδ_pos_enat
    exact ne_of_gt h'
  have hNδ_fin : (Metric.externalCoveringNumber δ' P : ENNReal) ≠ ⊤ := by
    have h : (Metric.externalCoveringNumber δ' P : ENNReal) ≤
        (9 : ENNReal) ^ (m + 1) * ∏ k ∈ Finset.range m, (↑(N k) : ENNReal) := by
      simpa [hδ_def] using h_upper_m
    have h' : ((9 : ENNReal) ^ (m + 1) * ∏ k ∈ Finset.range m, (↑(N k) : ENNReal)) ≠ ⊤ := by
      apply ENNReal.mul_ne_top <;> simp [ENNReal.prod_ne_top]
    exact ne_top_of_le_ne_top h' h

  -- Step 2: N_{Δ^j}(P) is finite via dyadicCovering_upper_total
  have h_upper_total := dyadicCovering_upper_total h_uniform hj hP
  have h_prod_fin : (∏ k ∈ Finset.range j, (↑(N k) : ENNReal)) ≠ ⊤ := by
    apply ENNReal.prod_ne_top; intro i _; simp
  have hNj_fin : (Metric.externalCoveringNumber r_j' P : ENNReal) ≠ ⊤ := by
    have h : (Metric.externalCoveringNumber r_j' P : ENNReal) ≤
        (9 : ENNReal) ^ (j + 1) * ∏ k ∈ Finset.range j, (↑(N k) : ENNReal) := h_upper_total
    have h' : ((9 : ENNReal) ^ (j + 1) * ∏ k ∈ Finset.range j, (↑(N k) : ENNReal)) ≠ ⊤ := by
      apply ENNReal.mul_ne_top <;> simp [h_prod_fin]
    exact ne_top_of_le_ne_top h' h

  -- Step 3: Extract finite cover at scale Δ^j
  rcases exists_finite_cover_le (le_refl (Metric.externalCoveringNumber r_j' P : ENNReal)) hNj_fin
    with ⟨C_j, hC_cover, hC_card⟩

  -- Step 4: Subadditivity + S-set gives 1 ≤ N_{Δ^j}(P) * C * (Δ^j)^t
  let A : C_j → Set Plane := fun c => P ∩ Metric.closedBall (c : Plane) r_j'
  let U : Set Plane := ⋃ (c : C_j), A c
  have h_coverU : P ⊆ U := by
    intro x hx
    have h3 : x ∈ ⋃ c ∈ C_j, Metric.closedBall c r_j' :=
      hC_cover.subset_iUnion_closedBall hx
    simp only [U, Set.mem_iUnion] at h3 ⊢
    rcases h3 with ⟨c, hc1, hc2⟩
    let c' : C_j := ⟨c, hc1⟩
    exact ⟨c', ⟨hx, hc2⟩⟩
  have h_subadd_enat : Metric.externalCoveringNumber δ' U ≤
      ∑ (c : C_j), Metric.externalCoveringNumber δ' (A c) :=
    externalCoveringNumber_iUnion_le
  let coeHom : ENat →+ ENNReal :=
    { toFun := fun x => ↑x
      map_zero' := by simp
      map_add' := by intro a b; exact ENat.toENNReal_add a b }
  have h_sum_coe : (↑(∑ (c : C_j), Metric.externalCoveringNumber δ' (A c)) : ENNReal) =
      ∑ (c : C_j), (Metric.externalCoveringNumber δ' (A c) : ENNReal) := by
    exact map_sum coeHom (fun c => Metric.externalCoveringNumber δ' (A c)) Finset.univ
  have h_subadd : (Metric.externalCoveringNumber δ' P : ENNReal) ≤
      ∑ (c : C_j), (Metric.externalCoveringNumber δ' (A c) : ENNReal) := by
    have h1 : (Metric.externalCoveringNumber δ' P : ENNReal) ≤
        (Metric.externalCoveringNumber δ' U : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h_coverU
    have h2 : (Metric.externalCoveringNumber δ' U : ENNReal) ≤
        (↑(∑ (c : C_j), Metric.externalCoveringNumber δ' (A c)) : ENNReal) := by
      exact_mod_cast h_subadd_enat
    rw [h_sum_coe] at h2
    exact le_trans h1 h2
  have hrj_eq : (r_j' : ℝ) = Δ ^ j := by
    have h_pos : 0 ≤ Δ ^ j := by positivity
    rw [Real.coe_toNNReal _ h_pos] <;> rfl
  have h_sset_each : ∀ (c : C_j), (Metric.externalCoveringNumber δ' (A c) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal (Δ ^ j)) ^ t * (Metric.externalCoveringNumber δ' P : ENNReal) := by
    intro c
    have h := h_sset.2.2.2.2 (c : Plane) (Δ ^ j) hδ_le_j
    have h_eq : A c = P ∩ Metric.closedBall (c : Plane) (Δ ^ j) := by
      simp [A, hrj_eq] <;> rfl
    rw [h_eq]
    simpa [hC_def] using h
  set K : ENNReal := ENNReal.ofReal C * (ENNReal.ofReal (Δ ^ j)) ^ t with hK_def
  set a : ENNReal := (Metric.externalCoveringNumber δ' P : ENNReal) with ha_def
  have h_sum_le : ∑ (c : C_j), (Metric.externalCoveringNumber δ' (A c) : ENNReal) ≤
      (C_j.card : ENNReal) * (K * a) := by
    have h_each : ∀ (c : C_j), (Metric.externalCoveringNumber δ' (A c) : ENNReal) ≤ K * a :=
      h_sset_each
    have h : ∑ (c : C_j), (Metric.externalCoveringNumber δ' (A c) : ENNReal) ≤
        ∑ (c : C_j), (K * a) := Finset.sum_le_sum fun c _ => h_each c
    have h2 : ∑ (c : C_j), (K * a) = (C_j.card : ENNReal) * (K * a) := by
      have h_sum : ∑ (c : C_j), (K * a) = (Finset.univ : Finset C_j).card * (K * a) := by
        rw [Finset.sum_const] <;> simp
      rw [h_sum]
      have h_card : (Finset.univ : Finset C_j).card = C_j.card := by simp
      rw [h_card] <;> rfl
    rw [h2] at h
    exact h
  set b : ENNReal := (Metric.externalCoveringNumber r_j' P : ENNReal) * K with hb_def
  have h_card_le : (C_j.card : ENNReal) ≤ (Metric.externalCoveringNumber r_j' P : ENNReal) := hC_card
  have h_main_ineq : a ≤ b * a := by
    calc a
      ≤ ∑ (c : C_j), (Metric.externalCoveringNumber δ' (A c) : ENNReal) := h_subadd
    _ ≤ (C_j.card : ENNReal) * (K * a) := h_sum_le
    _ = (C_j.card : ENNReal) * K * a := by ring
    _ ≤ b * a := by
      have h_card_K : (C_j.card : ENNReal) * K ≤ b := by
        have h : (C_j.card : ENNReal) * K ≤ (Metric.externalCoveringNumber r_j' P : ENNReal) * K := by
          gcongr <;> exact h_card_le
        simpa [hb_def] using h
      have h' : (C_j.card : ENNReal) * K * a ≤ b * a := by
        gcongr <;> exact h_card_K
      exact h'
  have h_one_le : (1 : ENNReal) ≤ b := by
    have h : a * (1 : ENNReal) ≤ a * b := by simpa [mul_comm] using h_main_ineq
    have h' : (1 : ENNReal) * a ≤ b * a := by simpa [mul_comm] using h
    exact (ENNReal.mul_le_mul_iff_left hNδ_pos hNδ_fin).mp h'
  have hK_pos : K ≠ 0 := by
    simp [hK_def, hC_pos, hΔ] <;> positivity
  have hK_top : K ≠ ⊤ := by
    have h1 : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
    have h_pos2 : 0 ≤ Δ ^ j := by positivity
    have h_eq2 : (ENNReal.ofReal (Δ ^ j)) ^ t = ENNReal.ofReal ((Δ ^ j) ^ t) := by
      rw [ENNReal.ofReal_rpow_of_nonneg h_pos2 ht] <;> rfl
    have h2 : (ENNReal.ofReal (Δ ^ j)) ^ t ≠ ⊤ := by
      rw [h_eq2]; exact ENNReal.ofReal_ne_top
    exact ENNReal.mul_ne_top h1 h2
  have h_lower : (Metric.externalCoveringNumber r_j' P : ENNReal) ≥ (1 : ENNReal) / K := by
    set Nj_enc : ENNReal := (Metric.externalCoveringNumber r_j' P : ENNReal) with hNj_enc
    have h1 : (1 : ENNReal) / K * K ≤ Nj_enc * K := by
      have h2 : (1 : ENNReal) / K * K = 1 := by
        rw [ENNReal.div_mul_cancel hK_pos hK_top] <;> ring
      rw [h2]
      exact h_one_le
    have h3 : (1 : ENNReal) / K ≤ Nj_enc := (ENNReal.mul_le_mul_iff_left hK_pos hK_top).mp h1
    exact h3

  -- Step 5: Combine lower and upper bounds, convert to real
  set Nj : ENNReal := (Metric.externalCoveringNumber r_j' P : ENNReal) with hNj_def
  set Prod : ENNReal := ∏ k ∈ Finset.range j, (↑(N k) : ENNReal) with hProd_def
  have h4 : Nj ≤ (9 : ENNReal) ^ (j + 1) * Prod := h_upper_total
  set R : ENNReal := (1 : ENNReal) / K with hR_def
  have h5 : R ≤ Nj := h_lower
  have h6 : R ≤ (9 : ENNReal) ^ (j + 1) * Prod := le_trans h5 h4
  have h_logC : Real.log C = (m : ℝ) * ε * Real.log (1 / Δ) := by
    rw [hC_def]
    have h_posδm : 0 < Δ ^ m := by positivity
    have h1 : Real.log (Real.rpow (Δ ^ m) (-ε)) = (-ε) * Real.log (Δ ^ m) := by
      have h : Real.log ((Δ ^ m) ^ (-ε)) = (-ε) * Real.log (Δ ^ m) :=
        Real.log_rpow h_posδm (-ε)
      simpa using h
    rw [h1]
    have h2 : Real.log (Δ ^ m) = (m : ℝ) * Real.log Δ := by
      rw [Real.log_pow] <;> ring
    rw [h2]
    have h3 : Real.log (1 / Δ) = -Real.log Δ := by
      rw [Real.log_div (by positivity) (by positivity)] <;> simp
    have h4 : (-ε : ℝ) * ((m : ℝ) * Real.log Δ) = (m : ℝ) * ε * Real.log (1 / Δ) := by
      rw [h3] <;> ring
    exact h4
  have h_log1 : 0 < Real.log (1 / Δ) := by
    have h : 1 < 1 / Δ := by apply one_lt_one_div <;> linarith
    exact Real.log_pos h
  have hProd_pos : 0 < ∏ k ∈ Finset.range j, (N k : ℝ) := by
    apply Finset.prod_pos
    intro k hk
    have h_k_lt_j : k < j := Finset.mem_range.mp hk
    have h_k_lt_m : k < m := by linarith
    have h7 : N k ≥ 1 := hN_pos k h_k_lt_m
    exact_mod_cast (by linarith)
  have h_prod_real : (Prod : ENNReal) = ENNReal.ofReal (∏ k ∈ Finset.range j, (N k : ℝ)) := by
    simp [hProd_def] <;> norm_cast
  have h_pos3 : 0 ≤ Δ ^ j := by positivity
  have hK_real : K = ENNReal.ofReal (C * (Δ ^ j) ^ t) := by
    have h_eq1 : (ENNReal.ofReal (Δ ^ j)) ^ t = ENNReal.ofReal ((Δ ^ j) ^ t) := by
      rw [ENNReal.ofReal_rpow_of_nonneg h_pos3 ht] <;> rfl
    rw [hK_def, h_eq1]
    have h_pos4 : 0 ≤ C := by positivity
    have h_pos5 : 0 ≤ (Δ ^ j) ^ t := by positivity
    rw [← ENNReal.ofReal_mul h_pos4] <;> rfl
  have h_pos6 : 0 < C * (Δ ^ j) ^ t := by positivity
  have hR_real : R = ENNReal.ofReal (1 / (C * (Δ ^ j) ^ t)) := by
    rw [hR_def, hK_real]
    have h_div : (1 : ENNReal) / ENNReal.ofReal (C * (Δ ^ j) ^ t) = (ENNReal.ofReal (C * (Δ ^ j) ^ t))⁻¹ := by
      simp [div_eq_mul_inv] <;> ring
    rw [h_div]
    have h_eq4 : (ENNReal.ofReal (C * (Δ ^ j) ^ t))⁻¹ = ENNReal.ofReal ((C * (Δ ^ j) ^ t)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos h_pos6]
    rw [h_eq4]
    have h_eq5 : (C * (Δ ^ j) ^ t)⁻¹ = 1 / (C * (Δ ^ j) ^ t) := by
      field_simp
    rw [h_eq5] <;> rfl
  have h6_real : 1 / (C * (Δ ^ j) ^ t) ≤ (9 : ℝ) ^ (j + 1) * (∏ k ∈ Finset.range j, (N k : ℝ)) := by
    have h7 : R ≤ ((9 : ENNReal) ^ (j + 1) * Prod) := h6
    rw [hR_real, h_prod_real] at h7
    exact_mod_cast h7
  have h_cf : (∏ k ∈ Finset.range j, (N k : ℝ)) = Real.rpow Δ (-(codeFunction m Δ N (j : ℝ))) :=
    codeFunction_product_dyadic h_uniform hΔ hΔ1 hj
  rw [h_cf] at h6_real

  -- Step 6: Take logs
  have h_pos1 : 0 < 1 / (C * (Δ ^ j) ^ t) := by positivity
  have h_pos7 : 0 < C * (Δ ^ j) ^ t := by positivity
  have h_pos8 : 0 < (Δ ^ j) ^ t := by positivity
  have h_log_ineq : Real.log (1 / (C * (Δ ^ j) ^ t)) ≤
      Real.log ((9 : ℝ) ^ (j + 1) * Real.rpow Δ (-(codeFunction m Δ N (j : ℝ)))) :=
    Real.log_le_log (by positivity) h6_real
  have h_log_left : Real.log (1 / (C * (Δ ^ j) ^ t)) =
      -Real.log C - (j : ℝ) * t * Real.log Δ := by
    have h1 : Real.log (1 / (C * (Δ ^ j) ^ t)) = Real.log 1 - Real.log (C * (Δ ^ j) ^ t) := by
      rw [Real.log_div (by norm_num) (ne_of_gt h_pos7)]
    rw [h1, Real.log_one]
    have h2 : Real.log (C * (Δ ^ j) ^ t) = Real.log C + Real.log ((Δ ^ j) ^ t) := by
      rw [Real.log_mul (ne_of_gt hC_pos) (ne_of_gt h_pos8)]
    rw [h2]
    have h3 : Real.log ((Δ ^ j) ^ t) = (j : ℝ) * t * Real.log Δ := by
      rw [Real.log_rpow (by positivity)]
      have h4 : Real.log (Δ ^ j) = (j : ℝ) * Real.log Δ := by
        rw [Real.log_pow] <;> ring
      rw [h4] <;> ring
    rw [h3] <;> ring
  have h_pos9 : 0 < (9 : ℝ) ^ (j + 1) := by positivity
  have h_pos10 : 0 < Real.rpow Δ (-(codeFunction m Δ N (j : ℝ))) := by
    apply Real.rpow_pos_of_pos
    linarith
  have h_log_right : Real.log ((9 : ℝ) ^ (j + 1) * Real.rpow Δ (-(codeFunction m Δ N (j : ℝ)))) =
      ((j : ℝ) + 1) * Real.log 9 + (-(codeFunction m Δ N (j : ℝ))) * Real.log Δ := by
    rw [Real.log_mul (ne_of_gt h_pos9) (ne_of_gt h_pos10)]
    have h4 : Real.log ((9 : ℝ) ^ (j + 1)) = ((j : ℝ) + 1) * Real.log 9 := by
      rw [Real.log_pow]
      <;> simp [Nat.cast_add] <;> ring
    have h5 : Real.log (Real.rpow Δ (-(codeFunction m Δ N (j : ℝ)))) =
        (-(codeFunction m Δ N (j : ℝ))) * Real.log Δ := by
      have h_posΔ : 0 < Δ := hΔ
      have h : Real.log (Δ ^ (-(codeFunction m Δ N (j : ℝ)))) =
          (-(codeFunction m Δ N (j : ℝ))) * Real.log Δ := Real.log_rpow h_posΔ _
      simpa using h
    rw [h4, h5] <;> ring
  rw [h_log_left, h_log_right] at h_log_ineq
  set L := Real.log (1 / Δ) with hL_def
  have hL_pos : 0 < L := h_log1
  have h_neg : Real.log Δ = -L := by
    have h : Real.log (1 / Δ) = -Real.log Δ := by
      rw [Real.log_div (by positivity) (by positivity)] <;> simp
    linarith
  rw [h_logC, h_neg] at h_log_ineq
  have h_alg : (m : ℝ) * ε * L + ((j : ℝ) + 1) * Real.log 9 +
      (codeFunction m Δ N (j : ℝ)) * L ≥ (j : ℝ) * t * L := by
    linarith
  have h_final : codeFunction m Δ N (j : ℝ) ≥ t * (j : ℝ) - ε * (m : ℝ) -
      ((m : ℝ) + 1) * Real.log 9 / L := by
    have h4 : (codeFunction m Δ N (j : ℝ)) * L ≥
        (j : ℝ) * t * L - (m : ℝ) * ε * L - ((j : ℝ) + 1) * Real.log 9 := by linarith
    have h5 : 0 < L := hL_pos
    have h6 : (j : ℝ) * t * L - (m : ℝ) * ε * L - ((j : ℝ) + 1) * Real.log 9 ≥
        (j : ℝ) * t * L - (m : ℝ) * ε * L - ((m : ℝ) + 1) * Real.log 9 := by
      have h7 : ((j : ℝ) + 1) * Real.log 9 ≤ ((m : ℝ) + 1) * Real.log 9 := by
        gcongr <;> linarith [Real.log_nonneg (by norm_num)]
      linarith
    have h8 : (codeFunction m Δ N (j : ℝ)) * L ≥
        (j : ℝ) * t * L - (m : ℝ) * ε * L - ((m : ℝ) + 1) * Real.log 9 := by linarith
    have h9 : codeFunction m Δ N (j : ℝ) ≥
        ((j : ℝ) * t * L - (m : ℝ) * ε * L - ((m : ℝ) + 1) * Real.log 9) / L := by
      have h10 : (codeFunction m Δ N (j : ℝ)) * L ≥
          (j : ℝ) * t * L - (m : ℝ) * ε * L - ((m : ℝ) + 1) * Real.log 9 := h8
      have h11 : codeFunction m Δ N (j : ℝ) = ((codeFunction m Δ N (j : ℝ)) * L) / L := by
        field_simp [h5.ne'] <;> ring
      rw [h11]
      gcongr
    have h12 : ((j : ℝ) * t * L - (m : ℝ) * ε * L - ((m : ℝ) + 1) * Real.log 9) / L =
        t * (j : ℝ) - ε * (m : ℝ) - ((m : ℝ) + 1) * Real.log 9 / L := by
      field_simp [h5.ne'] <;> ring
    rw [h12] at h9
    exact h9
  exact h_final

end CodeFunctionLowerBound
