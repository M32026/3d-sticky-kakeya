module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Cardinality bound (OS 5.5)

Pure counting lemmas underlying the cardinality bound in the main induction.

The paper proves (5.5) by combining three estimates:
- form80: |T₀| ≥ |T_Δ| · N_Δ
- form71: |T(Q)| ≤ M_Δ · N_Δ
- form46: |T(Q)| ≳ |T_Q| · M / M_Q

Combining: |T₀| · M_Δ · M_Q ≥ |T_Δ| · |T_Q| · M.
-/

attribute [local instance] Classical.propDecidable

namespace InductionOnScales

section CardinalityBound

/-- **Cardinality bound via three estimates** (pure algebra).

Given `h1 : T₀ ≥ T_Δ * N_Δ`, `h2 : T_Q_local ≤ M_Δ * N_Δ`,
`h3 : T_Q_local ≥ T_Q * M / M_Q`, then
`T₀ * M_Δ * M_Q ≥ T_Δ * T_Q * M`. -/
lemma cardinality_bound_three_estimates
    (T₀ T_Δ T_Q T_Q_local N_Δ M_Δ M_Q M : ℝ)
    (hNΔ_pos : 0 ≤ N_Δ)
    (hMΔ_pos : 0 < M_Δ)
    (hMQ_pos : 0 < M_Q)
    (hM_pos : 0 < M)
    (hTΔ_pos : 0 < T_Δ)
    (h1 : T₀ ≥ T_Δ * N_Δ)
    (h2 : T_Q_local ≤ M_Δ * N_Δ)
    (h3 : T_Q_local ≥ T_Q * M / M_Q) :
    T₀ * M_Δ * M_Q ≥ T_Δ * T_Q * M := by
  have h4 : N_Δ ≤ T₀ / T_Δ := by
    have h : T_Δ > 0 := hTΔ_pos
    have h' : T_Δ * N_Δ ≤ T₀ := h1
    calc
      N_Δ = (T_Δ * N_Δ) / T_Δ := by field_simp [h.ne'] <;> ring
      _ ≤ T₀ / T_Δ := by gcongr
  have h5 : T_Q * M / M_Q ≤ M_Δ * (T₀ / T_Δ) := by
    calc
      T_Q * M / M_Q ≤ T_Q_local := h3
      _ ≤ M_Δ * N_Δ := h2
      _ ≤ M_Δ * (T₀ / T_Δ) := by gcongr
  have h6 : T_Q * M ≤ M_Δ * (T₀ / T_Δ) * M_Q := by
    have hMQ : 0 < M_Q := hMQ_pos
    calc
      T_Q * M
        = (T_Q * M / M_Q) * M_Q := by field_simp [hMQ.ne'] <;> ring
      _ ≤ (M_Δ * (T₀ / T_Δ)) * M_Q := by gcongr
  have h7 : T_Δ * T_Q * M ≤ T₀ * M_Δ * M_Q := by
    have hTΔ : 0 < T_Δ := hTΔ_pos
    calc
      T_Δ * T_Q * M
        = T_Δ * (T_Q * M) := by ring
      _ ≤ T_Δ * (M_Δ * (T₀ / T_Δ) * M_Q) := by gcongr
      _ = T₀ * M_Δ * M_Q := by
        field_simp [hTΔ.ne'] <;> ring
  exact h7

/-- **Disjoint packets lower bound**.

If `C` is a finite set of labels and for each `c ∈ C` there is a subset
`packet c ⊆ A` of size at least `m`, and the packets are pairwise disjoint,
then `|A| ≥ |C| * m`. -/
lemma disjoint_packets_lower_bound
    {α : Type*} [DecidableEq α]
    {C : Finset ℕ} {A : Finset α} {m : ℝ}
    (packet : ℕ → Finset α)
    (h_subset : ∀ c ∈ C, packet c ⊆ A)
    (h_size : ∀ c ∈ C, m ≤ (packet c).card)
    (h_disj : ∀ c1 ∈ C, ∀ c2 ∈ C, c1 ≠ c2 → Disjoint (packet c1) (packet c2)) :
    (C.card : ℝ) * m ≤ (A.card : ℝ) := by
  have h1 : (C.biUnion packet).card = ∑ c ∈ C, (packet c).card := by
    rw [Finset.card_biUnion]
    <;> intro i _ j _ h
    exact h_disj i ‹_› j ‹_› h
  have h2 : (C.biUnion packet) ⊆ A := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨c, hc, hxc⟩
    exact h_subset c hc hxc
  have h3 : ((C.biUnion packet).card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card h2
  have h4 : (∑ c ∈ C, (packet c).card : ℝ) ≥ ∑ c ∈ C, m := by
    exact_mod_cast Finset.sum_le_sum (fun c hc => h_size c hc)
  have h5 : (∑ c ∈ C, m : ℝ) = (C.card : ℝ) * m := by
    simp [Finset.sum_const]
    <;> ring
  rw [h1] at h3
  have h_sum_cast : (↑(∑ c ∈ C, (packet c).card) : ℝ) = ∑ c ∈ C, ↑(packet c).card := by
    rw [Nat.cast_sum]
  rw [h_sum_cast] at h3
  linarith [h4, h5, h3]

/-- **Cover upper bound**.

If `A` is covered by the `biUnion` of fibers over `B`, each fiber has size
at most `N_Δ`, and `|B| ≤ M_Δ`, then `|A| ≤ M_Δ * N_Δ`. -/
lemma cover_upper_bound
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A : Finset α} {B : Finset β} {N_Δ M_Δ : ℝ}
    (hNΔ_pos : 0 ≤ N_Δ)
    (fiber : β → Finset α)
    (h_cover : A ⊆ B.biUnion fiber)
    (h_size : ∀ b ∈ B, (fiber b).card ≤ N_Δ)
    (hB_card : (B.card : ℝ) ≤ M_Δ) :
    (A.card : ℝ) ≤ M_Δ * N_Δ := by
  have h1 : ((B.biUnion fiber).card : ℝ) ≤ ∑ b ∈ B, ↑(fiber b).card := by
    have h : (B.biUnion fiber).card ≤ ∑ b ∈ B, (fiber b).card := Finset.card_biUnion_le
    exact_mod_cast h
  have h2 : (∑ b ∈ B, ↑(fiber b).card : ℝ) ≤ ∑ b ∈ B, N_Δ := by
    exact_mod_cast Finset.sum_le_sum (fun b hb => h_size b hb)
  have h3 : (∑ b ∈ B, N_Δ : ℝ) = (B.card : ℝ) * N_Δ := by
    simp [Finset.sum_const]
    <;> ring
  have h4 : (A.card : ℝ) ≤ ((B.biUnion fiber).card : ℝ) := by
    exact_mod_cast Finset.card_le_card h_cover
  calc
    (A.card : ℝ) ≤ ((B.biUnion fiber).card : ℝ) := h4
    _ ≤ (∑ b ∈ B, (fiber b).card : ℝ) := h1
    _ ≤ (∑ b ∈ B, N_Δ : ℝ) := h2
    _ = (B.card : ℝ) * N_Δ := h3
    _ ≤ M_Δ * N_Δ := mul_le_mul_of_nonneg_right hB_card hNΔ_pos

/-- **Separated packets lower bound** (OS form46, Lemmas 3-4).

Given labels `L`, each with a packet `packet l ⊆ A`, if:
1. Every packet has size at least `m`
2. There is a separated subcollection `L' ⊆ L` with `|L| ≤ K * |L'|`
3. Packets of elements in `L'` are pairwise disjoint

Then `|A| ≥ |L| * m / K`.

This formalizes: select a separated subcollection of comparable cardinality
(Lemma 4), then use disjointness of their packets (Lemma 3) to bound |A|. -/
lemma separated_packets_lower_bound
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {L L' : Finset β} {A : Finset α} {m K : ℝ}
    (packet : β → Finset α)
    (h_subset : ∀ l ∈ L, packet l ⊆ A)
    (h_size : ∀ l ∈ L, m ≤ (packet l).card)
    (hL'_sub : L' ⊆ L)
    (h_card : (L.card : ℝ) ≤ K * (L'.card : ℝ))
    (h_disj : ∀ l1 ∈ L', ∀ l2 ∈ L', l1 ≠ l2 → Disjoint (packet l1) (packet l2))
    (hK_pos : 0 < K) (hm_pos : 0 ≤ m) :
    (L.card : ℝ) * m ≤ K * (A.card : ℝ) := by
  have h1 : (L'.biUnion packet).card = ∑ l ∈ L', (packet l).card := by
    rw [Finset.card_biUnion]
    <;> intro i _ j _ h
    exact h_disj i ‹_› j ‹_› h
  have h2 : (L'.biUnion packet) ⊆ A := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨l, hl, hxl⟩
    exact h_subset l (hL'_sub hl) hxl
  have h3 : ((L'.biUnion packet).card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card h2
  have h4 : (∑ l ∈ L', (packet l).card : ℝ) ≥ ∑ l ∈ L', m := by
    exact_mod_cast Finset.sum_le_sum (fun l hl => h_size l (hL'_sub hl))
  have h5 : (∑ l ∈ L', m : ℝ) = (L'.card : ℝ) * m := by
    simp [Finset.sum_const] <;> ring
  rw [h1] at h3
  have h_sum_cast : (↑(∑ l ∈ L', (packet l).card) : ℝ) = ∑ l ∈ L', ↑(packet l).card := by
    rw [Nat.cast_sum]
  rw [h_sum_cast] at h3
  have h6 : (L'.card : ℝ) * m ≤ (A.card : ℝ) := by
    linarith [h4, h5, h3]
  have h7 : (L.card : ℝ) * m ≤ K * ((L'.card : ℝ) * m) := by
    calc
      (L.card : ℝ) * m ≤ (K * (L'.card : ℝ)) * m := by gcongr
      _ = K * ((L'.card : ℝ) * m) := by ring
  calc
    (L.card : ℝ) * m ≤ K * ((L'.card : ℝ) * m) := h7
    _ ≤ K * (A.card : ℝ) := by gcongr

end CardinalityBound

end InductionOnScales
