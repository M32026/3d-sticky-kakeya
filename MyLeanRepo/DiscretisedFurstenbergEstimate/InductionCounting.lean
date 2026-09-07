module

/-
  Induction-on-scales: incidence counting lemmas.

  Purely combinatorial parts of Proposition 5.1 (OS Section 5),
  specifically the lower bound:

    |T₀| / M ≳ |T_Δ| / M_Δ · |T_Q| / M_Q
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open Finset
open scoped BigOperators

namespace DiscretisedFurstenbergEstimate.InductionOnScales.Counting

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ### Disjoint union lower bound -/

/-- If `A i ⊆ U` are pairwise disjoint and each `|A i| ≥ N`, then
    `|U| ≥ |I| · N`. -/
lemma disjoint_family_lower {ι : Type*} [DecidableEq ι]
    (U : Finset α) (I : Finset ι) (A : ι → Finset α)
    (h_sub : ∀ i ∈ I, A i ⊆ U)
    (h_disj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j))
    (N : ℕ) (hN : ∀ i ∈ I, (A i).card ≥ N) :
    U.card ≥ I.card * N := by
  have h1 : (I.biUnion A).card = ∑ i ∈ I, (A i).card :=
    Finset.card_biUnion h_disj
  have h2 : (I.biUnion A) ⊆ U := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
    exact h_sub i hi hxi
  have h3 : ∑ i ∈ I, (A i).card ≥ I.card * N := by
    have h4 : ∑ i ∈ I, (A i).card ≥ ∑ i ∈ I, N := by
      apply sum_le_sum; intro i hi; exact hN i hi
    have h5 : ∑ i ∈ I, N = I.card * N := by
      simp [Finset.sum_const]
      <;> ring
    rw [h5] at h4
    exact h4
  have h6 : (I.biUnion A).card ≤ U.card := Finset.card_le_card h2
  rw [h1] at h6
  exact le_trans h3 h6

/-! ### Packet decomposition lower bound -/

/-- If packets `packet ξ` for `ξ ∈ S` are pairwise disjoint and each has
    real-cardinality ≥ m, then their union has cardinality ≥ |S| · m. -/
lemma disjoint_packets_lower_real
    (S : Finset γ) (packet : γ → Finset α)
    (h_disj : ∀ ξ1 ∈ S, ∀ ξ2 ∈ S, ξ1 ≠ ξ2 → Disjoint (packet ξ1) (packet ξ2))
    (m : ℝ) (hm : ∀ ξ ∈ S, ((packet ξ).card : ℝ) ≥ m) :
    ((S.biUnion packet).card : ℝ) ≥ (S.card : ℝ) * m := by
  have h1 : ((S.biUnion packet).card : ℝ) = ∑ ξ ∈ S, ((packet ξ).card : ℝ) := by
    have h11 := Finset.card_biUnion h_disj
    simpa using congr_arg (fun x : ℕ => (x : ℝ)) h11
  have h2 : ∑ ξ ∈ S, ((packet ξ).card : ℝ) ≥ (S.card : ℝ) * m := by
    have h21 : ∑ ξ ∈ S, ((packet ξ).card : ℝ) ≥ ∑ ξ ∈ S, m := by
      apply sum_le_sum; intro ξ hξ; exact hm ξ hξ
    have h22 : ∑ ξ ∈ S, m = (S.card : ℝ) * m := by
      simp [Finset.sum_const]
      <;> ring
    rw [h22] at h21
    exact h21
  rw [h1]
  exact h2

/-! ### Main lower bound combination -/

/-- **Core incidence counting lemma** for induction on scales.

    Combines:
    1. `|T₀| ≥ |T_Δ| · N_Δ`
    2. `|T(Q)| ≤ M_Δ · 2N_Δ`
    3. `|T(Q)| ≥ |T_Q_sep| · m`

    To conclude:
    `|T₀| · M_Δ ≥ |T_Δ| · |T_Q_sep| · m / 2`
-/
lemma induction_lower_bound_real
    (T₀ : Finset α)
    (T_Δ : Finset β)
    (children : β → Finset α)
    (N_Δ M_Δ : ℕ)
    (T_Δ_Q : Finset β)
    (T_Q_sep : Finset γ)
    (packet : γ → Finset α)
    (m : ℝ)
    (hMΔpos : 0 < M_Δ)
    (hm_nonneg : 0 ≤ m)
    -- Coarse tubes partition fine tubes
    (h_children_sub : ∀ T ∈ T_Δ, children T ⊆ T₀)
    (h_disj : ∀ T1 ∈ T_Δ, ∀ T2 ∈ T_Δ, T1 ≠ T2 → Disjoint (children T1) (children T2))
    -- Each coarse tube has ~ N_Δ fine tubes
    (h_N_lower : ∀ T ∈ T_Δ, (children T).card ≥ N_Δ)
    (h_N_upper : ∀ T ∈ T_Δ_Q, (children T).card ≤ 2 * N_Δ)
    -- T_Δ_Q ⊆ T_Δ and |T_Δ_Q| = M_Δ
    (h_TΔQ_sub : T_Δ_Q ⊆ T_Δ)
    (h_TΔQ_card : T_Δ_Q.card = M_Δ)
    -- Packet sizes
    (h_packet_size : ∀ ξ ∈ T_Q_sep, ((packet ξ).card : ℝ) ≥ m)
    -- Packets are pairwise disjoint
    (h_packet_disj : ∀ ξ1 ∈ T_Q_sep, ∀ ξ2 ∈ T_Q_sep, ξ1 ≠ ξ2 → Disjoint (packet ξ1) (packet ξ2))
    -- T(Q) = union of packets is contained in union of children through Q
    (h_TQ_in_children : (T_Q_sep.biUnion packet) ⊆ (T_Δ_Q.biUnion children)) :
    (T₀.card : ℝ) * (M_Δ : ℝ) ≥
      (T_Δ.card : ℝ) * (T_Q_sep.card : ℝ) * m / 2 := by
  set TQ_union : Finset α := T_Q_sep.biUnion packet with hTQ_def
  set children_Q : Finset α := T_Δ_Q.biUnion children with hchildren_def

  -- Step 1: |T₀| ≥ |T_Δ| · N_Δ
  have h1 : (T₀.card : ℝ) ≥ (T_Δ.card : ℝ) * (N_Δ : ℝ) := by
    have h11 := disjoint_family_lower T₀ T_Δ children h_children_sub h_disj N_Δ h_N_lower
    exact_mod_cast h11

  -- Step 2: |T(Q)| ≤ M_Δ · 2N_Δ
  have h21 : TQ_union ⊆ children_Q := h_TQ_in_children
  have h22 : children_Q.card ≤ ∑ T ∈ T_Δ_Q, (children T).card := by
    simpa [hchildren_def] using Finset.card_biUnion_le
  have h23 : (TQ_union.card : ℝ) ≤ (M_Δ : ℝ) * (2 * (N_Δ : ℝ)) := by
    have h24 : (TQ_union.card : ℝ) ≤ (children_Q.card : ℝ) := by
      exact_mod_cast Finset.card_le_card h21
    have h25 : (children_Q.card : ℝ) ≤ ∑ T ∈ T_Δ_Q, ((children T).card : ℝ) := by
      exact_mod_cast h22
    have h26 : ∑ T ∈ T_Δ_Q, ((children T).card : ℝ) ≤ ∑ T ∈ T_Δ_Q, (2 * (N_Δ : ℝ)) := by
      apply sum_le_sum; intro T hT; exact_mod_cast h_N_upper T hT
    have h27 : ∑ T ∈ T_Δ_Q, (2 * (N_Δ : ℝ)) = (M_Δ : ℝ) * (2 * (N_Δ : ℝ)) := by
      rw [Finset.sum_const, h_TΔQ_card] <;> ring
    linarith

  -- Step 3: |T(Q)| ≥ |T_Q_sep| · m
  have h3 : (TQ_union.card : ℝ) ≥ (T_Q_sep.card : ℝ) * m :=
    disjoint_packets_lower_real T_Q_sep packet h_packet_disj m h_packet_size

  -- Step 4: Algebra
  have hMΔr : (M_Δ : ℝ) > 0 := by exact_mod_cast hMΔpos
  have h4 : (N_Δ : ℝ) ≥ (TQ_union.card : ℝ) / (2 * (M_Δ : ℝ)) := by
    have h5 : (TQ_union.card : ℝ) ≤ 2 * (M_Δ : ℝ) * (N_Δ : ℝ) := by
      have h6 := h23
      ring_nf at h6 ⊢ <;> exact h6
    have hpos : 0 < 2 * (M_Δ : ℝ) := by positivity
    have h7 : (TQ_union.card : ℝ) / (2 * (M_Δ : ℝ)) ≤ (N_Δ : ℝ) := by
      calc (TQ_union.card : ℝ) / (2 * (M_Δ : ℝ))
        ≤ (2 * (M_Δ : ℝ) * (N_Δ : ℝ)) / (2 * (M_Δ : ℝ)) := by gcongr
      _ = (N_Δ : ℝ) := by
        field_simp [hpos.ne'] <;> ring
    exact h7

  have h5 : (T₀.card : ℝ) ≥ (T_Δ.card : ℝ) * (TQ_union.card : ℝ) / (2 * (M_Δ : ℝ)) := by
    have h51 : (T₀.card : ℝ) ≥ (T_Δ.card : ℝ) * (N_Δ : ℝ) := h1
    have h52 : (T_Δ.card : ℝ) * (N_Δ : ℝ) ≥
        (T_Δ.card : ℝ) * ((TQ_union.card : ℝ) / (2 * (M_Δ : ℝ))) := by gcongr
    have h53 : (T_Δ.card : ℝ) * ((TQ_union.card : ℝ) / (2 * (M_Δ : ℝ))) =
        (T_Δ.card : ℝ) * (TQ_union.card : ℝ) / (2 * (M_Δ : ℝ)) := by ring
    rw [h53] at h52
    linarith

  have h6 : (T₀.card : ℝ) * (M_Δ : ℝ) ≥
      (T_Δ.card : ℝ) * (T_Q_sep.card : ℝ) * m / 2 := by
    have h7 : (T₀.card : ℝ) * (M_Δ : ℝ) ≥
        (T_Δ.card : ℝ) * (TQ_union.card : ℝ) / 2 := by
      calc (T₀.card : ℝ) * (M_Δ : ℝ)
        ≥ ((T_Δ.card : ℝ) * (TQ_union.card : ℝ) / (2 * (M_Δ : ℝ))) * (M_Δ : ℝ) := by gcongr
      _ = (T_Δ.card : ℝ) * (TQ_union.card : ℝ) / 2 := by
        have h8 : ((T_Δ.card : ℝ) * (TQ_union.card : ℝ) / (2 * (M_Δ : ℝ))) * (M_Δ : ℝ) =
            (T_Δ.card : ℝ) * (TQ_union.card : ℝ) / 2 := by
          field_simp [hMΔr.ne'] <;> ring
        exact h8
    calc (T₀.card : ℝ) * (M_Δ : ℝ)
      ≥ (T_Δ.card : ℝ) * (TQ_union.card : ℝ) / 2 := h7
    _ ≥ (T_Δ.card : ℝ) * ((T_Q_sep.card : ℝ) * m) / 2 := by gcongr
    _ = (T_Δ.card : ℝ) * (T_Q_sep.card : ℝ) * m / 2 := by ring
  exact h6

end DiscretisedFurstenbergEstimate.InductionOnScales.Counting
