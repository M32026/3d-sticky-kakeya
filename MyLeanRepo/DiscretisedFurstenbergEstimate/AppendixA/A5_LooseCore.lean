module

/-
  A5 combinatorial core with LOOSE A4 bounds and (d=20, c=25) thresholds.

  Adapted from A5_FreezeMultiplicities.lean to work with any CoarseTube type.

  Input bounds (derived from A4 using hΔ_3ε: Δ^{-3ε} ≥ 2):
  - C_lower: Δ^{-s+11ε}  (from (1/2)·Δ^{-s+8ε} ≥ Δ^{3ε}·Δ^{-s+8ε})
  - C_upper: Δ^{-s-9ε}   (from 2·Δ^{-s-6ε} ≤ Δ^{-3ε}·Δ^{-s-6ε})
  - total incidence: Δ^{-s-t+14ε}  (from (1/2)·Δ^{-s-t+11ε} ≥ Δ^{3ε}·Δ^{-s-t+11ε})

  Threshold choices:
  - goodQ (d=20): layer-j intersection ≥ Δ^{-s+20ε}
  - J (c=25): ≥ Δ^{-t+25ε} good squares

  Contradiction arithmetic:
  - Good part: < Δ^{-t+25ε}·Δ^{-s-9ε} = Δ^{-s-t+16ε}
  - Bad part: ≤ Δ^{-t-ε}·Δ^{-s+20ε} = Δ^{-s-t+19ε}
  - Since Δ^{-s-t+19ε} < Δ^{-s-t+16ε}: per-layer < 2·Δ^{-s-t+16ε}
  - K·per-layer < Δ^{-2ε}·Δ^{-s-t+16ε} = Δ^{-s-t+14ε}
  - This contradicts total incidence ≥ Δ^{-s-t+14ε}

  Output bounds:
  - |Qbar| ≥ |Qset|·Δ^{26ε}
  - |C_bar| ≥ Δ^{-s+20ε}
  - |Tbar| ≥ Δ^{-2s+3ε}
  - N ≤ Δ^{-2s-3ε}
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA5

abbrev CoarseSquare (Δ : ℝ) := ℤ × ℤ

/-- Reusable type for the 2s-bound incidence hypothesis.

    Given sufficiently many coarse squares (≥ Δ^{-t+31ε}) each with
    sufficiently many tubes (≥ Δ^{-s+23ε}), all contained in T_Δ,
    the union of those tubes has cardinality ≥ Δ^{-2s-2ε}.

    Parameterized by Qset and C so the proof can use geometric properties
    of C (S-set, separation, near-center). D(Q) must be a subset of C(Q). -/
abbrev TwoSBound (Δ s t ε : ℝ) {CoarseTube : Type*} [DecidableEq CoarseTube]
    (Qset : Finset (CoarseSquare Δ))
    (C : (Q : CoarseSquare Δ) → Q ∈ Qset → Finset CoarseTube)
    (T_Δ : Finset CoarseTube) :=
  ∀ (Qsub : Finset (CoarseSquare Δ))
    (hQsub_sub : Qsub ⊆ Qset)
    (D : (Q : CoarseSquare Δ) → Q ∈ Qsub → Finset CoarseTube),
    (∀ Q hQ, D Q hQ ⊆ C Q (hQsub_sub hQ)) →
    (Qsub.card : ℝ) ≥ Real.rpow Δ (-t + 49 * ε) →
    (∀ Q hQ, (D Q hQ).card ≥ Real.rpow Δ (-s + 23 * ε)) →
    (T_Δ.filter (fun T => ∃ Q hQ, T ∈ D Q hQ)).card ≥
      Real.rpow Δ (-2 * s - 2 * ε)

/-- Reusable type for the 2s-bound with uniform constant and parameterized exponent.

    There exists a uniform c > 0 such that for every Qsub, the union has
    cardinality ≥ c · Δ^exponent. Used for the weakened hP_large branch bound. -/
abbrev TwoSBoundWithLower (Δ s t ε : ℝ) {CoarseTube : Type*}
    (Qset : Finset (CoarseSquare Δ))
    (C : (Q : CoarseSquare Δ) → Q ∈ Qset → Finset CoarseTube)
    (T_Δ : Finset CoarseTube)
    (exponent : ℝ) : Prop :=
  ∃ (c : ℝ), 0 < c ∧
    c ≥ Real.rpow Δ ε ∧
    (2 : ℝ) / c ≤ Real.rpow Δ (-ε) ∧
    ∀ (Qsub : Finset (CoarseSquare Δ))
    (hQsub_sub : Qsub ⊆ Qset)
    (D : (Q : CoarseSquare Δ) → Q ∈ Qsub → Finset CoarseTube),
    (∀ Q hQ, D Q hQ ⊆ C Q (hQsub_sub hQ)) →
    (Qsub.card : ℝ) ≥ Real.rpow Δ (-t + 49 * ε) →
    (∀ Q hQ, (D Q hQ).card ≥ Real.rpow Δ (-s + 23 * ε)) →
    ∃ (S : Finset CoarseTube),
      (∀ T, T ∈ S ↔ T ∈ T_Δ ∧ ∃ Q hQ, T ∈ D Q hQ) ∧
      (S.card : ℝ) ≥ c * Real.rpow Δ exponent

/-- Weaken a `TwoSBoundWithLower` from exponent `e1` to `e2` when `e1 ≤ e2`.
    Since 0 < Δ < 1, Δ^e1 ≥ Δ^e2, so a lower bound at e1 implies one at e2. -/
lemma TwoSBoundWithLower.weaken
    {Δ s t ε : ℝ} {CoarseTube : Type*}
    {Qset : Finset (CoarseSquare Δ)}
    {C : (Q : CoarseSquare Δ) → Q ∈ Qset → Finset CoarseTube}
    {T_Δ : Finset CoarseTube}
    {e1 e2 : ℝ} (h : TwoSBoundWithLower Δ s t ε Qset C T_Δ e1)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1) (he : e1 ≤ e2) :
    TwoSBoundWithLower Δ s t ε Qset C T_Δ e2 := by
  rcases h with ⟨c, hc_pos, hc_ge, hc_absorb, h_bound⟩
  refine' ⟨c, hc_pos, hc_ge, hc_absorb, _⟩
  intro Qsub hQsub_sub D hD_sub hQsub hD1
  rcases h_bound Qsub hQsub_sub D hD_sub hQsub hD1 with ⟨S, hS_mem, hS_card⟩
  have h2 : Real.rpow Δ e1 ≥ Real.rpow Δ e2 :=
    Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le he
  have h3 : c * Real.rpow Δ e2 ≤ c * Real.rpow Δ e1 := by gcongr <;> linarith
  exact ⟨S, hS_mem, h3.trans hS_card⟩

/-- Output of the generic A5 core. -/
structure A5_core_output (Δ s t ε : ℝ)
    (Qset : Finset (CoarseSquare Δ))
    {CoarseTube : Type*} [DecidableEq CoarseTube]
    (C : (Q : CoarseSquare Δ) → Q ∈ Qset → Finset CoarseTube)
    (T_Δ : Finset CoarseTube)
    (n : CoarseTube → ℕ) where
  Qbar : Finset (CoarseSquare Δ)
  Tbar : Finset CoarseTube
  N : ℝ
  hQbar_sub : Qbar ⊆ Qset
  hTbar_sub : Tbar ⊆ T_Δ
  hQbar_size : (Qbar.card : ℝ) ≥ (Qset.card : ℝ) * Real.rpow Δ (50 * ε)
  hN_pos : 0 < N
  hN_upper : N ≤ Real.rpow Δ (-2 * s - 210 * ε)
  hN_uniform : ∀ T ∈ Tbar, N / 2 ≤ (n T : ℝ) ∧ (n T : ℝ) ≤ N
  hC_bar_size : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Qbar),
      ((C Q (hQbar_sub hQ)).filter (· ∈ Tbar)).card ≥
        Real.rpow Δ (-s + 23 * ε)
  hTbar_size_lower : (Tbar.card : ℝ) ≥ Real.rpow Δ (-2 * s + 207 * ε)
  hTbar_size_upper : (Tbar.card : ℝ) ≤ Real.rpow Δ (-2 * s + ε)

/-- Weighted pigeonhole over finite partition. -/
lemma weighted_pigeonhole'
    {α : Type*} [DecidableEq α]
    (A : Finset α) (w : α → ℕ)
    (layers : ℕ → Finset α) (K : ℕ)
    (hK_pos : 0 < K)
    (h_cover : A ⊆ Finset.biUnion (Finset.range K) layers)
    (h_disj : ∀ j1 ∈ Finset.range K, ∀ j2 ∈ Finset.range K,
        j1 ≠ j2 → Disjoint (layers j1) (layers j2)) :
    ∃ j ∈ Finset.range K,
      (∑ a ∈ layers j, w a) * K ≥ ∑ a ∈ A, w a := by
  have h_sum : ∑ j ∈ Finset.range K, ∑ a ∈ layers j, w a ≥ ∑ a ∈ A, w a := by
    have h1 : ∑ a ∈ A, w a ≤ ∑ a ∈ Finset.biUnion (Finset.range K) layers, w a :=
      Finset.sum_le_sum_of_subset_of_nonneg h_cover (fun _ _ _ => Nat.zero_le _)
    have h2 : ∑ j ∈ Finset.range K, ∑ a ∈ layers j, w a =
        ∑ a ∈ Finset.biUnion (Finset.range K) layers, w a := by
      rw [Finset.sum_biUnion h_disj]
    rw [h2] at *
    exact h1
  by_contra h
  push Not at h
  have h_all : ∀ j ∈ Finset.range K, (∑ a ∈ layers j, w a) * K < ∑ a ∈ A, w a := by
    intro j hj
    exact h j hj
  have h_rhs : ∑ j ∈ Finset.range K, (∑ a ∈ A, w a) = K * (∑ a ∈ A, w a) := by
    simp [Finset.sum_const] <;> ring
  have h_strict : ∑ j ∈ Finset.range K, ((∑ a ∈ layers j, w a) * K) <
      ∑ j ∈ Finset.range K, (∑ a ∈ A, w a) := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (ne_of_gt hK_pos))
    intro j hj
    exact h_all j hj
  rw [h_rhs] at h_strict
  have h_eq : ∑ j ∈ Finset.range K, ((∑ a ∈ layers j, w a) * K) =
      K * (∑ j ∈ Finset.range K, ∑ a ∈ layers j, w a) := by
    rw [Finset.mul_sum] <;> apply Finset.sum_congr rfl <;> intro _ _ <;> ring
  rw [h_eq] at h_strict
  have h4 : (∑ j ∈ Finset.range K, ∑ a ∈ layers j, w a) < ∑ a ∈ A, w a := by
    by_contra h5
    have h6 : K * (∑ j ∈ Finset.range K, ∑ a ∈ layers j, w a) ≥ K * (∑ a ∈ A, w a) := by
      gcongr
    linarith
  exact not_le.mpr h4 h_sum

/-- Generic A5 core: dyadic layer-summing, works for any DecidableEq tube type. -/
def a5_freeze_core
    {Δ s t ε : ℝ}
    {CoarseTube : Type*} [DecidableEq CoarseTube]
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t ≤ 2)
    (hε_pos : 0 < ε)
    (hε_small : 55 * ε ≤ 2 * (t - s))
    (hΔ_3ε : Real.rpow Δ (-3 * ε) ≥ 2)
    (hK_bound : (4 * s + 2 * ε) * Real.log (1 / Δ) / Real.log 2 + 1 ≤
        Real.rpow Δ (-2 * ε) / 2)
    (Qset : Finset (CoarseSquare Δ))
    (C : (Q : CoarseSquare Δ) → Q ∈ Qset → Finset CoarseTube)
    (T_Δ : Finset CoarseTube)
    (n : CoarseTube → ℕ)
    (hQset_size_lower : (Qset.card : ℝ) ≥ Real.rpow Δ (-t + 4 * ε))
    (hQset_size_upper : (Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε))
    (hC_size_lower : ∀ Q hQ, (C Q hQ).card ≥ Real.rpow Δ (-s + 12 * ε))
    (hC_size_upper : ∀ Q hQ, (C Q hQ).card ≤ Real.rpow Δ (-s - 28 * ε))
    (hT_Δ_size_upper : (T_Δ.card : ℝ) ≤ Real.rpow Δ (-2 * s + ε))
    (hC_sub_TΔ : ∀ Q hQ, (C Q hQ : Set CoarseTube) ⊆ (T_Δ : Set CoarseTube))
    (h_n_pos : ∀ T ∈ T_Δ, 0 < n T)
    (h_n_multiplicity : ∀ (S : Finset (CoarseSquare Δ)) (T : CoarseTube),
        (∀ Q ∈ S, ∃ (hQ : Q ∈ Qset), T ∈ C Q hQ) →
        (n T : ℝ) ≥ (Real.rpow Δ (-(s + t) + 32 * ε) / 2) * (S.card : ℝ))
    (h_total_incidence :
        ∑ Q ∈ Qset.attach, (C Q.val Q.property).card ≥
        Real.rpow Δ (-s - t + 16 * ε))
    (hT_fine_upper : ∑ T ∈ T_Δ, n T ≤ Real.rpow Δ (-(4 * s + 2 * ε)))
    (c_2s : ℝ)
    (hc_2s_pos : 0 < c_2s)
    (h_2s_bound : ∀ (Qsub : Finset (CoarseSquare Δ))
        (hQsub_sub : Qsub ⊆ Qset)
        (D : (Q : CoarseSquare Δ) → Q ∈ Qsub → Finset CoarseTube),
        (∀ Q hQ, D Q hQ ⊆ C Q (hQsub_sub hQ)) →
        (Qsub.card : ℝ) ≥ Real.rpow Δ (-t + 49 * ε) →
        (∀ Q hQ, (D Q hQ).card ≥ Real.rpow Δ (-s + 23 * ε)) →
        (T_Δ.filter (fun T => ∃ Q hQ, T ∈ D Q hQ)).card ≥
          c_2s * Real.rpow Δ (-2 * s + 206 * ε))
    (h_absorb_c1 : c_2s ≥ Real.rpow Δ ε)
    (h_absorb_c2 : (2 : ℝ) / c_2s ≤ Real.rpow Δ (-ε)) :
    A5_core_output Δ s t ε Qset C T_Δ n := by
  classical
  have hΔ_lt_one : Δ < 1 := by linarith
  have hQset_nonempty : Qset.Nonempty := by
    have hpos : 0 < Real.rpow Δ (-t + 4 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h : (Qset.card : ℝ) ≥ Real.rpow Δ (-t + 4 * ε) := hQset_size_lower
    have h2 : (Qset.card : ℝ) > 0 := by linarith
    exact Finset.card_pos.mp (by exact_mod_cast h2)
  have hTΔ_nonempty : T_Δ.Nonempty := by
    obtain ⟨Q, hQ⟩ := hQset_nonempty
    have hpos : 0 < Real.rpow Δ (-s + 12 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h : (C Q hQ).card ≥ Real.rpow Δ (-s + 12 * ε) := hC_size_lower Q hQ
    have h2 : (C Q hQ).card > 0 := by exact_mod_cast (lt_of_lt_of_le hpos h)
    have h3 : (C Q hQ).Nonempty := Finset.card_pos.mp h2
    obtain ⟨T, hT⟩ := h3
    exact ⟨T, hC_sub_TΔ Q hQ hT⟩
  let M : ℕ := Finset.sup T_Δ n
  have hM_pos : 0 < M := by
    obtain ⟨T, hT⟩ := hTΔ_nonempty
    have h1 : n T > 0 := h_n_pos T hT
    have h2 : n T ≤ M := Finset.le_sup hT
    omega
  let K : ℕ := Nat.log 2 M + 1
  have hK_pos : 0 < K := by simp [K, hM_pos] <;> omega
  have h_n_lt_2K : ∀ T ∈ T_Δ, n T < 2 ^ K := by
    intro T hT
    have h1 : n T ≤ M := Finset.le_sup hT
    have h2 : M < 2 ^ K := by
      have h3 : M < 2 ^ (Nat.log 2 M + 1) := by
        have h4 : Nat.log 2 M < Nat.log 2 M + 1 := by omega
        exact (Nat.log_lt_iff_lt_pow (by norm_num) hM_pos.ne').mp h4
      simpa [K] using h3
    omega
  have hK_le : (K : ℝ) ≤ (4 * s + 2 * ε) * Real.log (1 / Δ) / Real.log 2 + 1 := by
    have hM_le : (M : ℝ) ≤ Real.rpow Δ (-(4 * s + 2 * ε)) := by
      have h_exists : ∃ T ∈ T_Δ, Finset.sup T_Δ n = n T :=
        Finset.exists_mem_eq_sup T_Δ hTΔ_nonempty n
      rcases h_exists with ⟨T, hT, h_eq⟩
      have hM_eq : M = n T := by simpa [M] using h_eq
      have hM_sum : (n T : ℝ) ≤ (∑ T' ∈ T_Δ, n T' : ℝ) := by
        exact_mod_cast Finset.single_le_sum (fun _ _ => Nat.zero_le _) hT
      have h_total : (∑ T ∈ T_Δ, n T : ℝ) ≤ Real.rpow Δ (-(4 * s + 2 * ε)) := by
        exact_mod_cast hT_fine_upper
      rw [hM_eq]
      exact hM_sum.trans h_total
    have h_log1 : 2 ^ (Nat.log 2 M) ≤ M := Nat.pow_log_le_self 2 hM_pos.ne'
    have h_log : (Nat.log 2 M : ℝ) ≤ Real.log (M : ℝ) / Real.log 2 := by
      have h_pos1 : 0 < Real.log 2 := by positivity
      have h : (Nat.log 2 M : ℝ) * Real.log 2 ≤ Real.log (M : ℝ) := by
        have h2 : (2 ^ (Nat.log 2 M) : ℝ) ≤ (M : ℝ) := by exact_mod_cast h_log1
        have h3 : Real.log ((2 ^ (Nat.log 2 M) : ℝ)) ≤ Real.log (M : ℝ) := Real.log_le_log (by positivity) h2
        have h4 : Real.log ((2 ^ (Nat.log 2 M) : ℝ)) = (Nat.log 2 M : ℝ) * Real.log 2 := by
          simp [Real.log_pow] <;> ring
        rw [h4] at h3
        exact h3
      have h5 : (Nat.log 2 M : ℝ) ≤ Real.log (M : ℝ) / Real.log 2 := by
        calc
          (Nat.log 2 M : ℝ)
            = ((Nat.log 2 M : ℝ) * Real.log 2) / Real.log 2 := by field_simp [h_pos1.ne'] <;> ring
          _ ≤ Real.log (M : ℝ) / Real.log 2 := by gcongr
      exact h5
    have h_log2 : Real.log (M : ℝ) ≤ Real.log (Δ ^ (-(4 * s + 2 * ε))) := by
      apply Real.log_le_log
      · positivity
      · exact hM_le
    have h_log3 : Real.log (Δ ^ (-(4 * s + 2 * ε))) =
        (4 * s + 2 * ε) * Real.log (1 / Δ) := by
      have h4 : Real.log (Δ ^ (-(4 * s + 2 * ε))) =
          (-(4 * s + 2 * ε)) * Real.log Δ := Real.log_rpow hΔ_pos _
      rw [h4]
      have h5 : Real.log (1 / Δ) = -Real.log Δ := by
        rw [Real.log_div (by norm_num) (ne_of_gt hΔ_pos)] <;> simp
      rw [h5] <;> ring
    have h_log2' : Real.log (M : ℝ) / Real.log 2 ≤ (4 * s + 2 * ε) * Real.log (1 / Δ) / Real.log 2 := by
      have h_pos1 : 0 < Real.log 2 := by positivity
      have h : Real.log (M : ℝ) ≤ (4 * s + 2 * ε) * Real.log (1 / Δ) := by
        calc
          Real.log (M : ℝ) ≤ Real.log (Δ ^ (-(4 * s + 2 * ε))) := h_log2
          _ = (4 * s + 2 * ε) * Real.log (1 / Δ) := h_log3
      gcongr
    have hK_eq : (K : ℝ) = (Nat.log 2 M : ℝ) + 1 := by
      simp [K] <;> norm_cast
    rw [hK_eq]
    linarith [h_log, h_log2']
  have hK_small : (K : ℝ) ≤ Real.rpow Δ (-2 * ε) / 2 := by
    linarith [hK_le, hK_bound]
  let layer (j : ℕ) : Finset CoarseTube :=
    T_Δ.filter (fun T => 2 ^ j ≤ n T ∧ n T < 2 ^ (j + 1))
  have h_layer_mem : ∀ (j : ℕ) T, T ∈ layer j ↔
      T ∈ T_Δ ∧ 2 ^ j ≤ n T ∧ n T < 2 ^ (j + 1) := by
    intro j T
    simp [layer, Finset.mem_filter] <;> tauto
  have h_layers_cover : T_Δ ⊆ Finset.biUnion (Finset.range K) layer := by
    intro T hT
    let j : ℕ := Nat.log 2 (n T)
    have hj1 : 2 ^ j ≤ n T := Nat.pow_log_le_self 2 (h_n_pos T hT).ne'
    have hj2 : n T < 2 ^ (j + 1) := by
      have h : Nat.log 2 (n T) < Nat.log 2 (n T) + 1 := by omega
      exact (Nat.log_lt_iff_lt_pow (by norm_num) (h_n_pos T hT).ne').mp h
    have hj3 : j < K := by
      have h4 : n T < 2 ^ K := h_n_lt_2K T hT
      exact Nat.log_lt_of_lt_pow (h_n_pos T hT).ne' h4
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj3, by
      rw [h_layer_mem] <;> exact ⟨hT, hj1, hj2⟩⟩
  have h_layers_disj : ∀ j1 ∈ Finset.range K, ∀ j2 ∈ Finset.range K,
      j1 ≠ j2 → Disjoint (layer j1) (layer j2) := by
    intro j1 hj1 j2 hj2 hne
    rw [Finset.disjoint_left]
    intro T hT1 hT2
    have h1 := (h_layer_mem j1 T).mp hT1
    have h2 := (h_layer_mem j2 T).mp hT2
    by_cases h : j1 < j2
    · have h3 : j1 + 1 ≤ j2 := by omega
      have h_base : 1 ≤ (2 : ℕ) := by norm_num
      have h4 : 2 ^ (j1 + 1) ≤ 2 ^ j2 := pow_le_pow_right₀ h_base h3
      linarith
    · have h4 : j2 < j1 := by omega
      have h5 : j2 + 1 ≤ j1 := by omega
      have h_base : 1 ≤ (2 : ℕ) := by norm_num
      have h6 : 2 ^ (j2 + 1) ≤ 2 ^ j1 := pow_le_pow_right₀ h_base h5
      linarith
  let goodQ (j : ℕ) : Finset (CoarseSquare Δ) :=
    let pred (Q : {Q // Q ∈ Qset}) : Prop :=
      ((C Q.val Q.property).filter (· ∈ layer j)).card ≥ Real.rpow Δ (-s + 23 * ε)
    (Qset.attach.filter pred).image Subtype.val
  have hgoodQ_sub : ∀ j, goodQ j ⊆ Qset := by
    intro j x hx
    rcases Finset.mem_image.mp hx with ⟨Q, _, rfl⟩
    exact Q.property
  have hgoodQ_char : ∀ j Q, Q ∈ goodQ j ↔
      ∃ (hQ : Q ∈ Qset), ((C Q hQ).filter (· ∈ layer j)).card ≥ Real.rpow Δ (-s + 23 * ε) := by
    intro j Q
    simp only [goodQ, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and]
    constructor
    · rintro ⟨Q', hpred, rfl⟩
      exact ⟨Q'.property, hpred⟩
    · rintro ⟨hQ, hcard⟩
      refine ⟨⟨Q, hQ⟩, hcard, rfl⟩
  let J : Finset ℕ :=
    (Finset.range K).filter (fun j => (goodQ j).card ≥ Real.rpow Δ (-t + 49 * ε))
  have h_layer_lower : ∀ j ∈ J, (layer j).card ≥ c_2s * Real.rpow Δ (-2 * s + 206 * ε) := by
    intro j hj
    have hJ2 : (goodQ j).card ≥ Real.rpow Δ (-t + 49 * ε) := (Finset.mem_filter.mp hj).2
    let D : (Q : CoarseSquare Δ) → Q ∈ goodQ j → Finset CoarseTube :=
      fun Q hQ => (C Q (hgoodQ_sub j hQ)).filter (· ∈ layer j)
    have hD1 : ∀ Q hQ, (D Q hQ).card ≥ Real.rpow Δ (-s + 23 * ε) := by
      intro Q hQ
      have h_exists : ∃ (hQ' : Q ∈ Qset), ((C Q hQ').filter (· ∈ layer j)).card ≥ Real.rpow Δ (-s + 23 * ε) :=
        (hgoodQ_char j Q).mp hQ
      rcases h_exists with ⟨hQ', hcard⟩
      have h_eq : D Q hQ = (C Q hQ').filter (· ∈ layer j) := by rfl
      rw [h_eq]; exact hcard
    have hD2 : ∀ Q hQ, (D Q hQ : Set CoarseTube) ⊆ (T_Δ : Set CoarseTube) := by
      intro Q hQ T hT
      exact hC_sub_TΔ Q (hgoodQ_sub j hQ) (Finset.mem_filter.mp hT).1
    have hD_sub_C : ∀ Q hQ, D Q hQ ⊆ C Q (hgoodQ_sub j hQ) := by
      intro Q hQ
      exact Finset.filter_subset _ _
    have h_main := h_2s_bound (goodQ j) (hgoodQ_sub j) D hD_sub_C (by exact_mod_cast hJ2) hD1
    have h_union_sub : (T_Δ.filter (fun T => ∃ Q hQ, T ∈ D Q hQ)) ⊆ layer j := by
      intro T hT
      rcases (Finset.mem_filter.mp hT).2 with ⟨Q, hQ, hTD⟩
      exact (Finset.mem_filter.mp hTD).2
    have h'' : (T_Δ.filter (fun T => ∃ Q hQ, T ∈ D Q hQ)).card ≤ (layer j).card :=
      Finset.card_le_card h_union_sub
    have h''_cast : (↑(T_Δ.filter (fun T => ∃ Q hQ, T ∈ D Q hQ)).card : ℝ) ≤ ↑(layer j).card := by exact_mod_cast h''
    exact h_main.trans h''_cast
  have h_sum : ∑ j ∈ J, (2 : ℝ) ^ j ≤ Real.rpow Δ (-2 * s - 208 * ε) / c_2s := by
    have h_disj : ∀ j1 ∈ J, ∀ j2 ∈ J, j1 ≠ j2 → Disjoint (layer j1) (layer j2) := by
      intro j1 hj1 j2 hj2 hne
      exact h_layers_disj j1 (Finset.mem_filter.mp hj1).1 j2 (Finset.mem_filter.mp hj2).1 hne
    have h1 : ∑ j ∈ J, ((layer j).card : ℝ) * (2 : ℝ) ^ j ≤
        (∑ T ∈ T_Δ, (n T : ℝ)) := by
      have h_bij : ∑ j ∈ J, ∑ T ∈ layer j, (n T : ℝ) ≤ ∑ T ∈ T_Δ, (n T : ℝ) := by
        have h_sub : Finset.biUnion J layer ⊆ T_Δ := by
          intro T hT
          rcases Finset.mem_biUnion.mp hT with ⟨j, _, hTj⟩
          exact (h_layer_mem j T).mp hTj |>.1
        have h_sum_bij : ∑ j ∈ J, ∑ T ∈ layer j, (n T : ℝ) =
            ∑ T ∈ Finset.biUnion J layer, (n T : ℝ) := by
          rw [Finset.sum_biUnion h_disj]
        rw [h_sum_bij]
        exact Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => by positivity)
      have h_each : ∀ j ∈ J, ∑ T ∈ layer j, (n T : ℝ) ≥ ((layer j).card : ℝ) * (2 : ℝ) ^ j := by
        intro j hj
        have h3 : ∀ T ∈ layer j, (n T : ℝ) ≥ (2 : ℝ) ^ j := by
          intro T hT
          have h4 := (h_layer_mem j T).mp hT
          exact_mod_cast h4.2.1
        calc
          ∑ T ∈ layer j, (n T : ℝ) ≥ ∑ T ∈ layer j, (2 : ℝ) ^ j := Finset.sum_le_sum h3
          _ = ((layer j).card : ℝ) * (2 : ℝ) ^ j := by
            simp [Finset.sum_const] <;> ring
      have h4 : ∑ j ∈ J, ((layer j).card : ℝ) * (2 : ℝ) ^ j ≤
          ∑ j ∈ J, ∑ T ∈ layer j, (n T : ℝ) := Finset.sum_le_sum h_each
      linarith
    have h5 : ∀ j ∈ J, ((layer j).card : ℝ) ≥ c_2s * Real.rpow Δ (-2 * s + 206 * ε) := h_layer_lower
    have h6 : ∑ j ∈ J, ((layer j).card : ℝ) * (2 : ℝ) ^ j ≥
        (c_2s * Real.rpow Δ (-2 * s + 206 * ε)) * ∑ j ∈ J, (2 : ℝ) ^ j := by
      have h7 : ∑ j ∈ J, ((layer j).card : ℝ) * (2 : ℝ) ^ j ≥
          ∑ j ∈ J, (c_2s * Real.rpow Δ (-2 * s + 206 * ε)) * (2 : ℝ) ^ j := by
        apply Finset.sum_le_sum
        intro j hj
        have h8 : ((layer j).card : ℝ) ≥ c_2s * Real.rpow Δ (-2 * s + 206 * ε) := h5 j hj
        have hpos : 0 ≤ (2 : ℝ) ^ j := by positivity
        nlinarith
      have h9 : ∑ j ∈ J, (c_2s * Real.rpow Δ (-2 * s + 206 * ε)) * (2 : ℝ) ^ j =
          (c_2s * Real.rpow Δ (-2 * s + 206 * ε)) * ∑ j ∈ J, (2 : ℝ) ^ j := by
        rw [Finset.mul_sum]
      rw [h9] at h7
      exact h7
    have h10 : (∑ T ∈ T_Δ, (n T : ℝ)) ≤ Real.rpow Δ (-(4 * s + 2 * ε)) := by
      exact_mod_cast hT_fine_upper
    have h11 : 0 < c_2s * Real.rpow Δ (-2 * s + 206 * ε) :=
      mul_pos hc_2s_pos (Real.rpow_pos_of_pos hΔ_pos _)
    have h12 : (c_2s * Real.rpow Δ (-2 * s + 206 * ε)) * ∑ j ∈ J, (2 : ℝ) ^ j ≤
        Real.rpow Δ (-(4 * s + 2 * ε)) := by linarith
    have h13 : ∑ j ∈ J, (2 : ℝ) ^ j ≤
        Real.rpow Δ (-(4 * s + 2 * ε)) / (c_2s * Real.rpow Δ (-2 * s + 206 * ε)) := by
      by_contra h14
      have h15 : ∑ j ∈ J, (2 : ℝ) ^ j > Real.rpow Δ (-(4 * s + 2 * ε)) / (c_2s * Real.rpow Δ (-2 * s + 206 * ε)) := by linarith
      have h16 : (c_2s * Real.rpow Δ (-2 * s + 206 * ε)) * ∑ j ∈ J, (2 : ℝ) ^ j > Real.rpow Δ (-(4 * s + 2 * ε)) := by
        have h17 : 0 < c_2s * Real.rpow Δ (-2 * s + 206 * ε) := h11
        calc
          (c_2s * Real.rpow Δ (-2 * s + 206 * ε)) * ∑ j ∈ J, (2 : ℝ) ^ j
            > (c_2s * Real.rpow Δ (-2 * s + 206 * ε)) * (Real.rpow Δ (-(4 * s + 2 * ε)) / (c_2s * Real.rpow Δ (-2 * s + 206 * ε))) := by gcongr
          _ = Real.rpow Δ (-(4 * s + 2 * ε)) := by
            have hb : c_2s * Real.rpow Δ (-2 * s + 206 * ε) ≠ 0 := h11.ne'
            have h_cancel : (c_2s * Real.rpow Δ (-2 * s + 206 * ε)) * (Real.rpow Δ (-(4 * s + 2 * ε)) / (c_2s * Real.rpow Δ (-2 * s + 206 * ε))) = Real.rpow Δ (-(4 * s + 2 * ε)) := by
              have h_comm : (c_2s * Real.rpow Δ (-2 * s + 206 * ε)) * (Real.rpow Δ (-(4 * s + 2 * ε)) / (c_2s * Real.rpow Δ (-2 * s + 206 * ε))) =
                  (Real.rpow Δ (-(4 * s + 2 * ε)) / (c_2s * Real.rpow Δ (-2 * s + 206 * ε))) * (c_2s * Real.rpow Δ (-2 * s + 206 * ε)) := by ring
              rw [h_comm]
              exact div_mul_cancel₀ (Real.rpow Δ (-(4 * s + 2 * ε))) hb
            exact h_cancel
      have h_contra : ¬((c_2s * Real.rpow Δ (-2 * s + 206 * ε)) * ∑ j ∈ J, (2 : ℝ) ^ j ≤ Real.rpow Δ (-(4 * s + 2 * ε))) := by
        exact not_le.mpr h16
      exact h_contra h12
    have h14 : Real.rpow Δ (-(4 * s + 2 * ε)) / (c_2s * Real.rpow Δ (-2 * s + 206 * ε)) =
        Real.rpow Δ (-2 * s - 208 * ε) / c_2s := by
      have h_exp : (-2 * s - 208 * ε) + (-2 * s + 206 * ε) = -(4 * s + 2 * ε) := by ring
      have h_rpow : Real.rpow Δ ((-2 * s - 208 * ε) + (-2 * s + 206 * ε)) =
          Real.rpow Δ (-2 * s - 208 * ε) * Real.rpow Δ (-2 * s + 206 * ε) :=
        Real.rpow_add hΔ_pos (-2 * s - 208 * ε) (-2 * s + 206 * ε)
      have h15 : Real.rpow Δ (-(4 * s + 2 * ε)) =
          Real.rpow Δ (-2 * s - 208 * ε) * Real.rpow Δ (-2 * s + 206 * ε) := by
        rw [← h_exp, h_rpow]
      rw [h15]
      have hb : Real.rpow Δ (-2 * s + 206 * ε) ≠ 0 := (Real.rpow_pos_of_pos hΔ_pos _).ne'
      have h_final : (Real.rpow Δ (-2 * s - 208 * ε) * Real.rpow Δ (-2 * s + 206 * ε)) / (c_2s * Real.rpow Δ (-2 * s + 206 * ε)) =
          Real.rpow Δ (-2 * s - 208 * ε) / c_2s := by
        calc
          (Real.rpow Δ (-2 * s - 208 * ε) * Real.rpow Δ (-2 * s + 206 * ε)) / (c_2s * Real.rpow Δ (-2 * s + 206 * ε))
            = (Real.rpow Δ (-2 * s - 208 * ε) / c_2s) * (Real.rpow Δ (-2 * s + 206 * ε) / Real.rpow Δ (-2 * s + 206 * ε)) := by ring
          _ = (Real.rpow Δ (-2 * s - 208 * ε) / c_2s) * 1 := by rw [div_self hb]
          _ = Real.rpow Δ (-2 * s - 208 * ε) / c_2s := by ring
      exact h_final
    rw [h14] at h13
    exact h13
  let inc (j : ℕ) : ℝ := ∑ Q ∈ Qset.attach, ((C Q.val Q.property).filter (· ∈ layer j)).card
  have h_swap_total : ∑ j ∈ Finset.range K, inc j = (∑ Q ∈ Qset.attach, (C Q.val Q.property).card : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro Q _
    have h_disj : ∀ j1 ∈ Finset.range K, ∀ j2 ∈ Finset.range K,
        j1 ≠ j2 → Disjoint ((C Q.val Q.property).filter (· ∈ layer j1))
          ((C Q.val Q.property).filter (· ∈ layer j2)) := by
      intro j1 hj1 j2 hj2 hne
      apply Finset.disjoint_filter.mpr
      intro T _ hT1
      have h_disj' : Disjoint (layer j1) (layer j2) := h_layers_disj j1 hj1 j2 hj2 hne
      intro hT2
      have h9 : T ∈ (layer j1) ∩ (layer j2) := Finset.mem_inter.mpr ⟨hT1, hT2⟩
      have h10 : (layer j1) ∩ (layer j2) = ∅ := Finset.disjoint_iff_inter_eq_empty.mp h_disj'
      rw [h10] at h9; simpa using h9
    have h_cover : (C Q.val Q.property) ⊆ Finset.biUnion (Finset.range K) (fun j =>
        (C Q.val Q.property).filter (· ∈ layer j)) := by
      intro T hT
      have hTΔ : T ∈ T_Δ := hC_sub_TΔ Q.val Q.property hT
      have h := h_layers_cover hTΔ
      rcases Finset.mem_biUnion.mp h with ⟨j, hj, hTj⟩
      exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨hT, hTj⟩⟩
    have h_biUnion_eq : Finset.biUnion (Finset.range K) (fun j => (C Q.val Q.property).filter (· ∈ layer j)) = C Q.val Q.property := by
      apply Finset.Subset.antisymm
      · intro T hT
        rcases Finset.mem_biUnion.mp hT with ⟨j, _, hTj⟩
        exact (Finset.mem_filter.mp hTj).1
      · exact h_cover
    have h_sum_nat : ∑ j ∈ Finset.range K, ((C Q.val Q.property).filter (· ∈ layer j)).card = (C Q.val Q.property).card := by
      have h_card : (Finset.biUnion (Finset.range K) (fun j => (C Q.val Q.property).filter (· ∈ layer j))).card =
          ∑ j ∈ Finset.range K, ((C Q.val Q.property).filter (· ∈ layer j)).card := Finset.card_biUnion h_disj
      calc
        ∑ j ∈ Finset.range K, ((C Q.val Q.property).filter (· ∈ layer j)).card
          = (Finset.biUnion (Finset.range K) (fun j => (C Q.val Q.property).filter (· ∈ layer j))).card := h_card.symm
      _ = (C Q.val Q.property).card := by rw [h_biUnion_eq]
    exact_mod_cast h_sum_nat
  have h_rpow_mul : ∀ (x y : ℝ), Real.rpow Δ x * Real.rpow Δ y = Real.rpow Δ (x + y) :=
    fun x y => (Real.rpow_add hΔ_pos x y).symm
  have h_delta5 : Real.rpow Δ (5 * ε) ≤ 1 / 2 := by
    have h1 : Real.rpow Δ (-3 * ε) * Real.rpow Δ (-2 * ε) = Real.rpow Δ (-5 * ε) := by
      rw [h_rpow_mul, show (-3 * ε) + (-2 * ε) = -5 * ε by ring]
    have h2 : Real.rpow Δ (-2 * ε) ≥ 1 := by
      have h21 : Real.rpow Δ (-2 * ε) ≥ Real.rpow Δ 0 :=
        Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le (by linarith)
      simpa using h21
    have h3 : Real.rpow Δ (-5 * ε) ≥ 2 := by
      rw [← h1]
      have h4 : Real.rpow Δ (-3 * ε) ≥ 2 := hΔ_3ε
      have h5 : Real.rpow Δ (-3 * ε) * Real.rpow Δ (-2 * ε) ≥ 2 := by
        calc
          Real.rpow Δ (-3 * ε) * Real.rpow Δ (-2 * ε)
            ≥ 2 * Real.rpow Δ (-2 * ε) := by gcongr
          _ ≥ 2 * 1 := by gcongr
          _ = 2 := by ring
      exact h5
    have h6 : 0 < Real.rpow Δ (-5 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h7 : Real.rpow Δ (5 * ε) * Real.rpow Δ (-5 * ε) = 1 := by
      rw [h_rpow_mul, show (5 * ε) + (-5 * ε) = 0 by ring] <;> simp
    have h8 : Real.rpow Δ (5 * ε) = 1 / Real.rpow Δ (-5 * ε) := by
      exact (eq_div_iff h6.ne').mpr h7
    rw [h8]
    have h9 : 1 / Real.rpow Δ (-5 * ε) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le <;> linarith
    exact h9
  have h_mult_bound : ∀ j ∈ Finset.range K, inc j ≤ 2 * Real.rpow Δ (-3 * s + t - 34 * ε) := by
    intro j _
    let m : CoarseTube → ℕ := fun T => (Qset.attach.filter (fun Q => T ∈ C Q.val Q.property)).card
    have h_eq : inc j = ∑ T ∈ layer j, (m T : ℝ) := by
      have h1 : inc j = ∑ Q ∈ Qset.attach, ∑ T ∈ layer j, (if T ∈ C Q.val Q.property then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro Q _
        have h_comm : (C Q.val Q.property).filter (· ∈ layer j) = (layer j).filter (· ∈ C Q.val Q.property) := by
          ext T; simp [Finset.mem_filter] <;> tauto
        have h2 : ((C Q.val Q.property).filter (· ∈ layer j)).card = ∑ T ∈ layer j, (if T ∈ C Q.val Q.property then (1 : ℝ) else 0) := by
          rw [h_comm, Finset.sum_ite] <;> simp
        exact_mod_cast h2
      rw [h1, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T _
      have h3 : ∑ Q ∈ Qset.attach, (if T ∈ C Q.val Q.property then (1 : ℝ) else 0) = (m T : ℝ) := by
        have h4 : ∑ Q ∈ Qset.attach, (if T ∈ C Q.val Q.property then (1 : ℝ) else 0) = ↑((Qset.attach.filter (fun Q => T ∈ C Q.val Q.property)).card) := by
          rw [Finset.sum_ite] <;> simp
        rw [h4] <;> rfl
      exact h3
    have h_m_bound : ∀ T ∈ layer j, (m T : ℝ) ≤ 2 * (n T : ℝ) * Real.rpow Δ (s + t - 32 * ε) := by
      intro T hT
      let S : Finset (CoarseSquare Δ) := (Qset.attach.filter (fun Q => T ∈ C Q.val Q.property)).image (fun Q => Q.val)
      have hS_card : (S.card : ℝ) = (m T : ℝ) := by
        have h_inj : Set.InjOn (fun (Q : {Q // Q ∈ Qset}) => Q.val) (Qset.attach.filter (fun Q => T ∈ C Q.val Q.property)) := by
          intro _ _ _ _ h; exact Subtype.ext h
        have h : S.card = (Qset.attach.filter (fun Q => T ∈ C Q.val Q.property)).card := by
          rw [Finset.card_image_of_injOn h_inj]
        have h' : (S.card : ℝ) = ((Qset.attach.filter (fun Q => T ∈ C Q.val Q.property)).card : ℝ) := by exact_mod_cast h
        simpa [m] using h'
      have hS1 : ∀ Q ∈ S, ∃ (hQ : Q ∈ Qset), T ∈ C Q hQ := by
        intro Q hQ
        rcases Finset.mem_image.mp hQ with ⟨Q', hQ', rfl⟩
        exact ⟨Q'.property, (Finset.mem_filter.mp hQ').2⟩
      have h_mult : (n T : ℝ) ≥ (Real.rpow Δ (-(s + t) + 32 * ε) / 2) * (S.card : ℝ) :=
        h_n_multiplicity S T hS1
      have h_mult' : (n T : ℝ) ≥ (Real.rpow Δ (-(s + t) + 32 * ε) / 2) * (m T : ℝ) := by
        rw [hS_card] at h_mult
        exact h_mult
      have hX_pos : 0 < Real.rpow Δ (-(s + t) + 32 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have hX_ne : Real.rpow Δ (-(s + t) + 32 * ε) ≠ 0 := hX_pos.ne'
      have h_div : 1 / Real.rpow Δ (-(s + t) + 32 * ε) = Real.rpow Δ (s + t - 32 * ε) := by
        have h1 : Real.rpow Δ (-(s + t) + 32 * ε) * Real.rpow Δ (s + t - 32 * ε) = 1 := by
          rw [h_rpow_mul, show (-(s + t) + 32 * ε) + (s + t - 32 * ε) = 0 by ring] <;> simp
        have h2 : Real.rpow Δ (s + t - 32 * ε) * Real.rpow Δ (-(s + t) + 32 * ε) = 1 := by
          rw [mul_comm]; exact h1
        exact (eq_div_iff hX_ne).mpr h2 |>.symm
      have h4 : Real.rpow Δ (-(s + t) + 32 * ε) * (m T : ℝ) ≤ 2 * (n T : ℝ) := by linarith [h_mult']
      have h51 : (Real.rpow Δ (-(s + t) + 32 * ε) * (m T : ℝ)) / Real.rpow Δ (-(s + t) + 32 * ε) = (m T : ℝ) := by
        field_simp [hX_ne] <;> ring
      have h5 : (m T : ℝ) ≤ 2 * (n T : ℝ) / Real.rpow Δ (-(s + t) + 32 * ε) := by
        calc (m T : ℝ)
          = (Real.rpow Δ (-(s + t) + 32 * ε) * (m T : ℝ)) / Real.rpow Δ (-(s + t) + 32 * ε) := h51.symm
        _ ≤ (2 * (n T : ℝ)) / Real.rpow Δ (-(s + t) + 32 * ε) := by gcongr
      have h6 : 2 * (n T : ℝ) / Real.rpow Δ (-(s + t) + 32 * ε) = 2 * (n T : ℝ) * Real.rpow Δ (s + t - 32 * ε) := by
        have h7 : (2 * (n T : ℝ)) / Real.rpow Δ (-(s + t) + 32 * ε) = 2 * (n T : ℝ) * (1 / Real.rpow Δ (-(s + t) + 32 * ε)) := by
          field_simp [hX_ne] <;> ring
        rw [h7, h_div] <;> ring
      rw [h6] at h5
      exact h5
    rw [h_eq]
    have h_sum_comm : ∑ T ∈ layer j, (2 * (n T : ℝ) * Real.rpow Δ (s + t - 32 * ε)) =
        2 * Real.rpow Δ (s + t - 32 * ε) * ∑ T ∈ layer j, (n T : ℝ) := by
      have h_comm : ∀ T ∈ layer j, 2 * (n T : ℝ) * Real.rpow Δ (s + t - 32 * ε) = 2 * Real.rpow Δ (s + t - 32 * ε) * (n T : ℝ) := by
        intro T _; ring
      rw [Finset.sum_congr rfl h_comm]
      rw [Finset.mul_sum]
    have h_layer_sub : layer j ⊆ T_Δ := Finset.filter_subset _ _
    have h_sum_n : (∑ T ∈ layer j, (n T : ℝ)) ≤ (∑ T ∈ T_Δ, (n T : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg h_layer_sub (fun _ _ _ => by positivity)
    have hT_fine_upper' : (∑ T ∈ T_Δ, (n T : ℝ)) ≤ Real.rpow Δ (-(4 * s + 2 * ε)) := by
      simpa [Nat.cast_sum] using hT_fine_upper
    have h_pos_rpow : 0 ≤ 2 * Real.rpow Δ (s + t - 32 * ε) := by
      have h : 0 < Real.rpow Δ (s + t - 32 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      linarith
    have h_rpow_prod : Real.rpow Δ (s + t - 32 * ε) * Real.rpow Δ (-(4 * s + 2 * ε)) = Real.rpow Δ (-3 * s + t - 34 * ε) := by
      rw [h_rpow_mul, show (s + t - 32 * ε) + (-(4 * s + 2 * ε)) = -3 * s + t - 34 * ε by ring]
    have h_mul : 2 * Real.rpow Δ (s + t - 32 * ε) * ∑ T ∈ layer j, (n T : ℝ) ≤ 2 * Real.rpow Δ (s + t - 32 * ε) * Real.rpow Δ (-(4 * s + 2 * ε)) := by
      have h : (∑ T ∈ layer j, (n T : ℝ)) ≤ Real.rpow Δ (-(4 * s + 2 * ε)) := h_sum_n.trans hT_fine_upper'
      exact PosMulMono.mul_le_mul_of_nonneg_left h_pos_rpow h
    calc
      ∑ T ∈ layer j, (m T : ℝ)
        ≤ ∑ T ∈ layer j, (2 * (n T : ℝ) * Real.rpow Δ (s + t - 32 * ε)) := Finset.sum_le_sum h_m_bound
      _ = 2 * Real.rpow Δ (s + t - 32 * ε) * ∑ T ∈ layer j, (n T : ℝ) := h_sum_comm
      _ ≤ 2 * Real.rpow Δ (s + t - 32 * ε) * Real.rpow Δ (-(4 * s + 2 * ε)) := h_mul
      _ = 2 * Real.rpow Δ (-3 * s + t - 34 * ε) := by
        have h_eq : 2 * Real.rpow Δ (s + t - 32 * ε) * Real.rpow Δ (-(4 * s + 2 * ε)) = 2 * (Real.rpow Δ (s + t - 32 * ε) * Real.rpow Δ (-(4 * s + 2 * ε))) := by ring
        rw [h_eq, h_rpow_prod] <;> ring
  have h_mult_strict : ∀ j ∈ Finset.range K, inc j < Real.rpow Δ (-s - t + 16 * ε) := by
    intro j hj
    have h1 : inc j ≤ 2 * Real.rpow Δ (-3 * s + t - 34 * ε) := h_mult_bound j hj
    have h2 : 2 * Real.rpow Δ (-3 * s + t - 34 * ε) < Real.rpow Δ (-s - t + 16 * ε) := by
      have h3 : 2 * Real.rpow Δ (-3 * s + t - 34 * ε) ≤ Real.rpow Δ (-3 * ε) * Real.rpow Δ (-3 * s + t - 34 * ε) := by
        have hpos : 0 < Real.rpow Δ (-3 * s + t - 34 * ε) := Real.rpow_pos_of_pos hΔ_pos _
        exact mul_le_mul_of_nonneg_right hΔ_3ε hpos.le
      have h4 : Real.rpow Δ (-3 * ε) * Real.rpow Δ (-3 * s + t - 34 * ε) = Real.rpow Δ (-3 * s + t - 37 * ε) := by
        rw [h_rpow_mul, show (-3 * ε) + (-3 * s + t - 34 * ε) = -3 * s + t - 37 * ε by ring]
      rw [h4] at h3
      have h5 : Real.rpow Δ (-3 * s + t - 37 * ε) < Real.rpow Δ (-s - t + 16 * ε) := by
        apply Real.rpow_lt_rpow_of_exponent_gt hΔ_pos hΔ_lt_one
        linarith [hε_small]
      exact h3.trans_lt h5
    exact h1.trans_lt h2
  have hJ_nonempty : J.Nonempty := by
    by_contra h
    have hJ_empty : J = ∅ := by simpa using h
    have h_sum_upper : ∑ j ∈ Finset.range K, inc j ≤ (K : ℝ) * 2 * Real.rpow Δ (-3 * s + t - 34 * ε) := by
      have h : ∑ j ∈ Finset.range K, inc j ≤ ∑ j ∈ Finset.range K, (2 * Real.rpow Δ (-3 * s + t - 34 * ε)) :=
        Finset.sum_le_sum h_mult_bound
      have h_sum : ∑ j ∈ Finset.range K, (2 * Real.rpow Δ (-3 * s + t - 34 * ε)) = (K : ℝ) * (2 * Real.rpow Δ (-3 * s + t - 34 * ε)) := by
        rw [Finset.sum_const, Finset.card_range] <;> ring_nf
      rw [h_sum] at h
      have h_ring : (K : ℝ) * (2 * Real.rpow Δ (-3 * s + t - 34 * ε)) = (K : ℝ) * 2 * Real.rpow Δ (-3 * s + t - 34 * ε) := by ring
      rw [h_ring] at h
      exact h
    have hK2 : (K : ℝ) * 2 * Real.rpow Δ (-3 * s + t - 34 * ε) ≤ Real.rpow Δ (-3 * s + t - 36 * ε) := by
      have h : (K : ℝ) ≤ Real.rpow Δ (-2 * ε) / 2 := hK_small
      have hpos : 0 < 2 * Real.rpow Δ (-3 * s + t - 34 * ε) := by
        have h : 0 < Real.rpow Δ (-3 * s + t - 34 * ε) := Real.rpow_pos_of_pos hΔ_pos _
        linarith
      have h2 : (K : ℝ) * (2 * Real.rpow Δ (-3 * s + t - 34 * ε)) ≤
          (Real.rpow Δ (-2 * ε) / 2) * (2 * Real.rpow Δ (-3 * s + t - 34 * ε)) := by gcongr <;> linarith
      have h3 : (Real.rpow Δ (-2 * ε) / 2) * (2 * Real.rpow Δ (-3 * s + t - 34 * ε)) =
          Real.rpow Δ (-2 * ε) * Real.rpow Δ (-3 * s + t - 34 * ε) := by ring
      rw [h3] at h2
      have h4 : Real.rpow Δ (-2 * ε) * Real.rpow Δ (-3 * s + t - 34 * ε) =
          Real.rpow Δ (-3 * s + t - 36 * ε) := by
        rw [h_rpow_mul, show (-2 * ε) + (-3 * s + t - 34 * ε) = -3 * s + t - 36 * ε by ring]
      rw [h4] at h2
      have h_ring : (K : ℝ) * 2 * Real.rpow Δ (-3 * s + t - 34 * ε) = (K : ℝ) * (2 * Real.rpow Δ (-3 * s + t - 34 * ε)) := by ring
      rw [h_ring]
      exact h2
    have h_final : Real.rpow Δ (-3 * s + t - 36 * ε) < Real.rpow Δ (-s - t + 16 * ε) := by
      apply Real.rpow_lt_rpow_of_exponent_gt hΔ_pos hΔ_lt_one
      linarith [hε_small]
    have h_total_upper : (∑ Q ∈ Qset.attach, (C Q.val Q.property).card : ℝ) <
        Real.rpow Δ (-s - t + 16 * ε) := by
      have h5 : ∑ j ∈ Finset.range K, inc j < Real.rpow Δ (-s - t + 16 * ε) :=
        (h_sum_upper.trans hK2).trans_lt h_final
      rw [h_swap_total] at h5
      exact h5
    have h_total_lower : (∑ Q ∈ Qset.attach, (C Q.val Q.property).card : ℝ) ≥
        Real.rpow Δ (-s - t + 16 * ε) := by simpa [Nat.cast_sum] using h_total_incidence
    exact not_le.mpr h_total_upper h_total_lower

  have h_bad_sum : ∑ j ∈ Finset.range K \ J, inc j ≤ Real.rpow Δ (-3 * s + t - 36 * ε) := by
    have h1 : ∑ j ∈ Finset.range K \ J, inc j ≤ ∑ j ∈ Finset.range K \ J, (2 * Real.rpow Δ (-3 * s + t - 34 * ε)) :=
      Finset.sum_le_sum (fun j hj => h_mult_bound j (Finset.mem_sdiff.mp hj).1)
    have h2 : ∑ j ∈ Finset.range K \ J, (2 * Real.rpow Δ (-3 * s + t - 34 * ε)) =
        ((Finset.range K \ J).card : ℝ) * (2 * Real.rpow Δ (-3 * s + t - 34 * ε)) := by
      simp [Finset.sum_const] <;> ring
    rw [h2] at h1
    have h3 : ((Finset.range K \ J).card : ℝ) ≤ (K : ℝ) := by
      have h31 : (Finset.range K \ J).card ≤ (Finset.range K).card := Finset.card_le_card Finset.sdiff_subset
      have h32 : (Finset.range K).card = K := by simp
      rw [h32] at h31
      exact_mod_cast h31
    have hpos : 0 < 2 * Real.rpow Δ (-3 * s + t - 34 * ε) := by
      have h : 0 < Real.rpow Δ (-3 * s + t - 34 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      linarith
    have h4 : ((Finset.range K \ J).card : ℝ) * (2 * Real.rpow Δ (-3 * s + t - 34 * ε)) ≤
        (K : ℝ) * (2 * Real.rpow Δ (-3 * s + t - 34 * ε)) := by gcongr <;> exact hpos.le
    have h5 : (K : ℝ) * (2 * Real.rpow Δ (-3 * s + t - 34 * ε)) ≤ Real.rpow Δ (-3 * s + t - 36 * ε) := by
      have h6 : (K : ℝ) ≤ Real.rpow Δ (-2 * ε) / 2 := hK_small
      have h7 : (K : ℝ) * (2 * Real.rpow Δ (-3 * s + t - 34 * ε)) ≤
          (Real.rpow Δ (-2 * ε) / 2) * (2 * Real.rpow Δ (-3 * s + t - 34 * ε)) := by gcongr <;> exact hpos
      have h8 : (Real.rpow Δ (-2 * ε) / 2) * (2 * Real.rpow Δ (-3 * s + t - 34 * ε)) =
          Real.rpow Δ (-2 * ε) * Real.rpow Δ (-3 * s + t - 34 * ε) := by ring
      rw [h8] at h7
      have h9 : Real.rpow Δ (-2 * ε) * Real.rpow Δ (-3 * s + t - 34 * ε) =
          Real.rpow Δ (-3 * s + t - 36 * ε) := by
        rw [h_rpow_mul, show (-2 * ε) + (-3 * s + t - 34 * ε) = -3 * s + t - 36 * ε by ring]
      rw [h9] at h7
      exact h7
    exact h1.trans (h4.trans h5)
  have h_bad_sum_half : Real.rpow Δ (-3 * s + t - 36 * ε) ≤ (1 / 2 : ℝ) * Real.rpow Δ (-s - t + 16 * ε) := by
    have h1 : 2 * Real.rpow Δ (-3 * s + t - 36 * ε) ≤ Real.rpow Δ (-s - t + 16 * ε) := by
      have h2 : 2 ≤ Real.rpow Δ (-3 * ε) := hΔ_3ε
      have hpos2 : 0 ≤ Real.rpow Δ (-3 * s + t - 36 * ε) := (Real.rpow_pos_of_pos hΔ_pos _).le
      have h3 : 2 * Real.rpow Δ (-3 * s + t - 36 * ε) ≤ Real.rpow Δ (-3 * ε) * Real.rpow Δ (-3 * s + t - 36 * ε) :=
        mul_le_mul_of_nonneg_right h2 hpos2
      have h4 : Real.rpow Δ (-3 * ε) * Real.rpow Δ (-3 * s + t - 36 * ε) = Real.rpow Δ (-3 * s + t - 39 * ε) := by
        rw [h_rpow_mul, show (-3 * ε) + (-3 * s + t - 36 * ε) = -3 * s + t - 39 * ε by ring]
      rw [h4] at h3
      have h5 : Real.rpow Δ (-3 * s + t - 39 * ε) ≤ Real.rpow Δ (-s - t + 16 * ε) := by
        apply Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le
        linarith [hε_small]
      exact h3.trans h5
    have hpos : 0 < Real.rpow Δ (-s - t + 16 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    linarith
  have h_good_sum : ∑ j ∈ J, inc j ≥ (1 / 2 : ℝ) * Real.rpow Δ (-s - t + 16 * ε) := by
    have h1 : ∑ j ∈ Finset.range K, inc j = ∑ j ∈ J, inc j + ∑ j ∈ Finset.range K \ J, inc j := by
      have h_disj : Disjoint J (Finset.range K \ J) := by
        simp [Finset.disjoint_left]
        <;> tauto
      have h_union : J ∪ (Finset.range K \ J) = Finset.range K := by
        simp [J] <;> tauto
      rw [← Finset.sum_union h_disj, h_union]
    have h2 : (∑ Q ∈ Qset.attach, (C Q.val Q.property).card : ℝ) ≥ Real.rpow Δ (-s - t + 16 * ε) := by
      simpa [Nat.cast_sum] using h_total_incidence
    have h3 : ∑ j ∈ Finset.range K, inc j ≥ Real.rpow Δ (-s - t + 16 * ε) := by
      rw [h_swap_total]; exact h2
    have h4 : ∑ j ∈ J, inc j = ∑ j ∈ Finset.range K, inc j - ∑ j ∈ Finset.range K \ J, inc j := by
      linarith [h1]
    rw [h4]
    have h5 : Real.rpow Δ (-3 * s + t - 36 * ε) ≤ (1 / 2 : ℝ) * Real.rpow Δ (-s - t + 16 * ε) := h_bad_sum_half
    linarith [h_bad_sum, h3, h5]
  have h_exists_j : ∃ j ∈ J, inc j ≥ Real.rpow Δ (-s - t + 18 * ε) := by
    by_contra h
    push Not at h
    have h_all : ∀ j ∈ J, inc j < Real.rpow Δ (-s - t + 18 * ε) := h
    have h_sum_lt : ∑ j ∈ J, inc j < (J.card : ℝ) * Real.rpow Δ (-s - t + 18 * ε) := by
      have h1 : ∑ j ∈ J, inc j < ∑ j ∈ J, Real.rpow Δ (-s - t + 18 * ε) :=
        Finset.sum_lt_sum_of_nonempty hJ_nonempty h_all
      have h2 : ∑ j ∈ J, Real.rpow Δ (-s - t + 18 * ε) = (J.card : ℝ) * Real.rpow Δ (-s - t + 18 * ε) := by
        simp [Finset.sum_const] <;> ring
      rw [h2] at h1
      exact h1
    have h_Jcard : (J.card : ℝ) ≤ (K : ℝ) := by
      have hJ_sub : J ⊆ Finset.range K := Finset.filter_subset _ _
      have h : J.card ≤ (Finset.range K).card := Finset.card_le_card hJ_sub
      have h2 : (Finset.range K).card = K := by simp
      rw [h2] at h
      exact_mod_cast h
    have hpos3 : 0 < Real.rpow Δ (-s - t + 18 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_bound : (J.card : ℝ) * Real.rpow Δ (-s - t + 18 * ε) ≤
        (1 / 2 : ℝ) * Real.rpow Δ (-s - t + 16 * ε) := by
      calc
        (J.card : ℝ) * Real.rpow Δ (-s - t + 18 * ε)
          ≤ (K : ℝ) * Real.rpow Δ (-s - t + 18 * ε) := by gcongr <;> exact hpos3.le
        _ ≤ (Real.rpow Δ (-2 * ε) / 2) * Real.rpow Δ (-s - t + 18 * ε) := by
          exact mul_le_mul_of_nonneg_right hK_small hpos3.le
        _ = (1 / 2 : ℝ) * Real.rpow Δ (-s - t + 16 * ε) := by
          have h_eq : Real.rpow Δ (-2 * ε) * Real.rpow Δ (-s - t + 18 * ε) = Real.rpow Δ (-s - t + 16 * ε) := by
            rw [h_rpow_mul, show (-2 * ε) + (-s - t + 18 * ε) = -s - t + 16 * ε by ring]
          linarith
    linarith [h_good_sum, h_sum_lt, h_bound]
  let j : ℕ := Classical.choose h_exists_j
  have h_j_spec : j ∈ J ∧ inc j ≥ Real.rpow Δ (-s - t + 18 * ε) := Classical.choose_spec h_exists_j
  have hj : j ∈ J := h_j_spec.1
  have h_inc_j : inc j ≥ Real.rpow Δ (-s - t + 18 * ε) := h_j_spec.2
  let C' (Q : CoarseSquare Δ) : Finset CoarseTube :=
    if h : Q ∈ Qset then C Q h else ∅
  have hC'_eq : ∀ Q (hQ : Q ∈ Qset), C' Q = C Q hQ := by
    intro Q hQ
    simp [C', hQ]
  let S_T (T : CoarseTube) : Finset (CoarseSquare Δ) := Qset.filter (fun Q => T ∈ C' Q)
  have hS1 : ∀ T ∈ layer j, ∀ Q ∈ S_T T, ∃ (hQ : Q ∈ Qset), T ∈ C Q hQ := by
    intro T _ Q hQ
    have hQset : Q ∈ Qset := (Finset.mem_filter.mp hQ).1
    have hTin : T ∈ C' Q := (Finset.mem_filter.mp hQ).2
    refine ⟨hQset, ?_⟩
    rw [hC'_eq Q hQset] at hTin
    exact hTin
  have h_mult : ∀ T ∈ layer j, (n T : ℝ) ≥ (Real.rpow Δ (-(s + t) + 32 * ε) / 2) * ((S_T T).card : ℝ) := by
    intro T hT
    exact h_n_multiplicity (S_T T) T (hS1 T hT)
  have h_double_count : ∑ T ∈ layer j, ((S_T T).card : ℝ) = inc j := by
    calc
      ∑ T ∈ layer j, ((S_T T).card : ℝ)
        = ∑ T ∈ layer j, ∑ Q ∈ Qset, if T ∈ C' Q then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro T _
          simp [S_T, Finset.filter_eq', Finset.sum_ite] <;> ring
      _ = ∑ Q ∈ Qset, ∑ T ∈ layer j, if T ∈ C' Q then (1 : ℝ) else 0 := by
          rw [Finset.sum_comm]
      _ = ∑ Q ∈ Qset.attach, (((C Q.val Q.property).filter (· ∈ layer j)).card : ℝ) := by
          have h_step1 : ∑ Q ∈ Qset, (∑ T ∈ layer j, if T ∈ C' Q then (1 : ℝ) else 0) =
              ∑ Q ∈ Qset.attach, (∑ T ∈ layer j, if T ∈ C' Q.val then (1 : ℝ) else 0) := by
            have h := Finset.sum_attach Qset (fun Q : CoarseSquare Δ => ∑ T ∈ layer j, if T ∈ C' Q then (1 : ℝ) else 0)
            exact h.symm
          rw [h_step1]
          apply Finset.sum_congr rfl
          intro Q _
          have hC' : C' Q.val = C Q.val Q.property := hC'_eq Q.val Q.property
          have h_goal : ∑ T ∈ layer j, (if T ∈ C' Q.val then (1 : ℝ) else 0) =
              (((C Q.val Q.property).filter (· ∈ layer j)).card : ℝ) := by
            have h1 : ∑ T ∈ layer j, (if T ∈ C' Q.val then (1 : ℝ) else 0) =
                (((layer j).filter (fun T => T ∈ C' Q.val)).card : ℝ) := by
              have h_sum : ∑ T ∈ layer j, (if T ∈ C' Q.val then (1 : ℝ) else 0) =
                  ((layer j).filter (fun T => T ∈ C' Q.val)).card := by
                rw [Finset.sum_ite]
                <;> simp
              exact_mod_cast h_sum
            rw [h1]
            have h2 : (layer j).filter (fun T => T ∈ C' Q.val) = (C Q.val Q.property).filter (· ∈ layer j) := by
              rw [hC']
              ext T
              simp [Finset.mem_filter] <;> tauto
            rw [h2] <;> rfl
          exact h_goal
      _ = inc j := by rfl
  have h_fine_lower : ∑ T ∈ layer j, (n T : ℝ) ≥ (1 / 2 : ℝ) * Real.rpow Δ (-2 * s - 2 * t + 50 * ε) := by
    have h1 : ∑ T ∈ layer j, (n T : ℝ) ≥
        (Real.rpow Δ (-(s + t) + 32 * ε) / 2) * ∑ T ∈ layer j, ((S_T T).card : ℝ) := by
      calc
        ∑ T ∈ layer j, (n T : ℝ)
          ≥ ∑ T ∈ layer j, ((Real.rpow Δ (-(s + t) + 32 * ε) / 2) * ((S_T T).card : ℝ)) :=
            Finset.sum_le_sum h_mult
        _ = (Real.rpow Δ (-(s + t) + 32 * ε) / 2) * ∑ T ∈ layer j, ((S_T T).card : ℝ) := by
          rw [Finset.mul_sum] <;> ring
    have h1' : ∑ T ∈ layer j, (n T : ℝ) ≥
        (Real.rpow Δ (-(s + t) + 32 * ε) / 2) * inc j := by
      rw [h_double_count] at h1
      exact h1
    have h_pos_rpow30 : 0 < Real.rpow Δ (-(s + t) + 32 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_pos_mult : 0 ≤ Real.rpow Δ (-(s + t) + 32 * ε) / 2 := by positivity
    have h2 : (Real.rpow Δ (-(s + t) + 32 * ε) / 2) * inc j ≥
        (Real.rpow Δ (-(s + t) + 32 * ε) / 2) * Real.rpow Δ (-s - t + 18 * ε) := by
      exact mul_le_mul_of_nonneg_left h_inc_j h_pos_mult
    have h4 : Real.rpow Δ (-(s + t) + 32 * ε) * Real.rpow Δ (-s - t + 18 * ε) =
        Real.rpow Δ (-2 * s - 2 * t + 50 * ε) := by
      rw [h_rpow_mul, show (-(s + t) + 32 * ε) + (-s - t + 18 * ε) = -2 * s - 2 * t + 50 * ε by ring]
    have h3 : (Real.rpow Δ (-(s + t) + 32 * ε) / 2) * Real.rpow Δ (-s - t + 18 * ε) =
        (1 / 2 : ℝ) * Real.rpow Δ (-2 * s - 2 * t + 50 * ε) := by
      calc
        (Real.rpow Δ (-(s + t) + 32 * ε) / 2) * Real.rpow Δ (-s - t + 18 * ε)
          = (1 / 2 : ℝ) * (Real.rpow Δ (-(s + t) + 32 * ε) * Real.rpow Δ (-s - t + 18 * ε)) := by ring
        _ = (1 / 2 : ℝ) * Real.rpow Δ (-2 * s - 2 * t + 50 * ε) := by rw [h4]
    calc
      ∑ T ∈ layer j, (n T : ℝ)
        ≥ (Real.rpow Δ (-(s + t) + 32 * ε) / 2) * inc j := h1'
      _ ≥ (Real.rpow Δ (-(s + t) + 32 * ε) / 2) * Real.rpow Δ (-s - t + 18 * ε) := h2
      _ = (1 / 2 : ℝ) * Real.rpow Δ (-2 * s - 2 * t + 50 * ε) := h3
  let N : ℝ := (2 : ℝ) ^ (j + 1)
  have h_2j : (2 : ℝ) ^ j ≤ Real.rpow Δ (-2 * s - 208 * ε) / c_2s := by
    have h : (2 : ℝ) ^ j ≤ ∑ j' ∈ J, (2 : ℝ) ^ j' := by
      apply Finset.single_le_sum (fun _ _ => by positivity) hj
    exact h.trans h_sum
  have hN_upper2 : N ≤ Real.rpow Δ (-2 * s - 210 * ε) := by
    have h1 : N = 2 * (2 : ℝ) ^ j := by simp [N] <;> ring
    rw [h1]
    have h_pos2j : 0 ≤ (2 : ℝ) ^ j := by positivity
    have h_pos_rpow : 0 ≤ Real.rpow Δ (-2 * s - 208 * ε) := Real.rpow_nonneg hΔ_pos.le _
    have h2 : 2 * (2 : ℝ) ^ j ≤ (2 / c_2s) * Real.rpow Δ (-2 * s - 208 * ε) := by
      have h3 : (2 : ℝ) ^ j ≤ Real.rpow Δ (-2 * s - 208 * ε) / c_2s := h_2j
      have h4 : 0 < c_2s := hc_2s_pos
      calc
        2 * (2 : ℝ) ^ j
          ≤ 2 * (Real.rpow Δ (-2 * s - 208 * ε) / c_2s) := by gcongr
        _ = (2 / c_2s) * Real.rpow Δ (-2 * s - 208 * ε) := by ring
    have h7 : 2 / c_2s ≤ Real.rpow Δ (-ε) := h_absorb_c2
    have h10 : Real.rpow Δ (-ε) * Real.rpow Δ (-2 * s - 208 * ε) = Real.rpow Δ (-2 * s - 209 * ε) := by
      have h11 : (-ε) + (-2 * s - 208 * ε) = -2 * s - 209 * ε := by ring
      have h12 : Real.rpow Δ (-ε) * Real.rpow Δ (-2 * s - 208 * ε) = Real.rpow Δ ((-ε) + (-2 * s - 208 * ε)) :=
        (Real.rpow_add hΔ_pos (-ε) (-2 * s - 208 * ε)).symm
      rw [h12, h11]
    have h_weaken : Real.rpow Δ (-2 * s - 209 * ε) ≤ Real.rpow Δ (-2 * s - 210 * ε) := by
      have h_exp : (-2 * s - 210 * ε) ≤ (-2 * s - 209 * ε) := by linarith
      exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h_exp
    calc
      2 * (2 : ℝ) ^ j
        ≤ (2 / c_2s) * Real.rpow Δ (-2 * s - 208 * ε) := h2
      _ ≤ Real.rpow Δ (-ε) * Real.rpow Δ (-2 * s - 208 * ε) := by
        exact mul_le_mul_of_nonneg_right h7 h_pos_rpow
      _ = Real.rpow Δ (-2 * s - 209 * ε) := h10
      _ ≤ Real.rpow Δ (-2 * s - 210 * ε) := h_weaken
  have hTbar_lower : (layer j).card ≥ Real.rpow Δ (-2 * s + 207 * ε) := by
    have h1 : (layer j).card ≥ c_2s * Real.rpow Δ (-2 * s + 206 * ε) := h_layer_lower j hj
    have h3 : c_2s ≥ Real.rpow Δ ε := h_absorb_c1
    have hpos : 0 ≤ Real.rpow Δ (-2 * s + 206 * ε) := Real.rpow_nonneg hΔ_pos.le _
    have h4 : c_2s * Real.rpow Δ (-2 * s + 206 * ε) ≥
        Real.rpow Δ ε * Real.rpow Δ (-2 * s + 206 * ε) := by
      exact mul_le_mul_of_nonneg_right h3 hpos
    have h5 : Real.rpow Δ ε * Real.rpow Δ (-2 * s + 206 * ε) = Real.rpow Δ (-2 * s + 207 * ε) := by
      have h7 : ε + (-2 * s + 206 * ε) = -2 * s + 207 * ε := by ring
      have h8 : Real.rpow Δ ε * Real.rpow Δ (-2 * s + 206 * ε) = Real.rpow Δ (ε + (-2 * s + 206 * ε)) :=
        (Real.rpow_add hΔ_pos ε (-2 * s + 206 * ε)).symm
      rw [h8, h7]
    have h2 : c_2s * Real.rpow Δ (-2 * s + 206 * ε) ≥ Real.rpow Δ (-2 * s + 207 * ε) := by
      calc
        c_2s * Real.rpow Δ (-2 * s + 206 * ε)
          ≥ Real.rpow Δ ε * Real.rpow Δ (-2 * s + 206 * ε) := h4
        _ = Real.rpow Δ (-2 * s + 207 * ε) := h5
    exact h2.trans h1
  have hQbar_size2 : (goodQ j).card ≥ (Qset.card : ℝ) * Real.rpow Δ (50 * ε) := by
    have h1 : (goodQ j).card ≥ Real.rpow Δ (-t + 49 * ε) := (Finset.mem_filter.mp hj).2
    have h2 : (Qset.card : ℝ) * Real.rpow Δ (50 * ε) ≤ Real.rpow Δ (-t + 49 * ε) := by
      have h3 : (Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε) := hQset_size_upper
      have h4 : (Qset.card : ℝ) * Real.rpow Δ (50 * ε) ≤
          Real.rpow Δ (-t - ε) * Real.rpow Δ (50 * ε) := by
        have hpos : 0 ≤ Real.rpow Δ (50 * ε) := (Real.rpow_pos_of_pos hΔ_pos _).le
        exact mul_le_mul_of_nonneg_right h3 hpos
      have h5 : Real.rpow Δ (-t - ε) * Real.rpow Δ (50 * ε) = Real.rpow Δ (-t + 49 * ε) := by
        have h6 := Real.rpow_add hΔ_pos (-t - ε) (50 * ε)
        have h7 : (-t - ε) + (50 * ε) = -t + 49 * ε := by ring
        rw [h7] at h6
        exact h6.symm
      rw [h5] at h4
      exact h4
    linarith
  have hC_bar_size2 : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ goodQ j),
      ((C Q (hgoodQ_sub j hQ)).filter (· ∈ layer j)).card ≥ Real.rpow Δ (-s + 23 * ε) := by
    intro Q hQ
    have h_exists : ∃ (hQ' : Q ∈ Qset), ((C Q hQ').filter (· ∈ layer j)).card ≥ Real.rpow Δ (-s + 23 * ε) :=
      (hgoodQ_char j Q).mp hQ
    rcases h_exists with ⟨hQ', hcard⟩
    have h_eq : (C Q (hgoodQ_sub j hQ)).filter (· ∈ layer j) = (C Q hQ').filter (· ∈ layer j) := by congr
    rw [h_eq]
    exact_mod_cast hcard
  have hN_uniform2 : ∀ T ∈ layer j, N / 2 ≤ (n T : ℝ) ∧ (n T : ℝ) ≤ N := by
    intro T hT
    have h1 := (h_layer_mem j T).mp hT
    constructor
    · have h2 : N / 2 = (2 : ℝ) ^ j := by simp [N] <;> ring
      rw [h2]; exact_mod_cast h1.2.1
    · have h3 : (n T : ℝ) < N := by simp [N] <;> exact_mod_cast h1.2.2
      linarith
  exact
    { Qbar := goodQ j
    , Tbar := layer j
    , N := N
    , hQbar_sub := hgoodQ_sub j
    , hTbar_sub := Finset.filter_subset _ _
    , hQbar_size := hQbar_size2
    , hN_pos := by positivity
    , hN_upper := hN_upper2
    , hN_uniform := hN_uniform2
    , hC_bar_size := hC_bar_size2
    , hTbar_size_lower := hTbar_lower
    , hTbar_size_upper := by
        have h1 : (layer j).card ≤ T_Δ.card := Finset.card_le_card (Finset.filter_subset _ _)
        have h2 : (T_Δ.card : ℝ) ≤ Real.rpow Δ (-2 * s + ε) := hT_Δ_size_upper
        have h1' : ((layer j).card : ℝ) ≤ (T_Δ.card : ℝ) := by exact_mod_cast h1
        exact h1'.trans h2
    }

end DirecretisedFurstenbergEstimate.AppendixA5
