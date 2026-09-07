module

/-
  Heavy Parent Filtering.

  Given a fine configuration at scale n and a coarse scale m ≤ n,
  filter coarse parent squares by fiber cardinality to retain only
  "heavy" parents.

  ## Main results

  1. `Qheavy` definition: coarse parents with fiber ≥ Δ^{-u+ε}
  2. `heavy_filter_light_bound`: light contribution ≤ (1/2) · Δ^{-2u+ε/5}
  3. `heavy_filter_retained_mass`: retained mass ≥ Δ^{-2u+ε/4}
  4. `heavy_filter_coarse_lower`: |Qheavy| ≥ Δ^{-u+ε}

  Whiteprint node: heavy_parent_filtering
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas.HeavyParentFiltering

open Finset

variable {α β : Type*} [DecidableEq β]

/-! ### Definitions -/

def coarseP₀ (P₀ : Finset α) (f : α → β) : Finset β :=
  P₀.image f

def fiber (P₀ : Finset α) (f : α → β) (Q : β) : Finset α :=
  P₀.filter (fun p => f p = Q)

def Qheavy (P₀ : Finset α) (f : α → β) (m_threshold : ℝ) : Finset β :=
  (coarseP₀ P₀ f).filter (fun Q => m_threshold ≤ (fiber P₀ f Q).card)

def Qlight (P₀ : Finset α) (f : α → β) (m_threshold : ℝ) : Finset β :=
  (coarseP₀ P₀ f).filter (fun Q => (fiber P₀ f Q).card < m_threshold)

/-! ### Basic properties -/

lemma heavy_light_partition (P₀ : Finset α) (f : α → β) (m_threshold : ℝ) :
    Qheavy P₀ f m_threshold ∪ Qlight P₀ f m_threshold = coarseP₀ P₀ f ∧
    Disjoint (Qheavy P₀ f m_threshold) (Qlight P₀ f m_threshold) := by
  let Qh := Qheavy P₀ f m_threshold
  let Ql := Qlight P₀ f m_threshold
  have h1 : Qh ∪ Ql = coarseP₀ P₀ f := by
    ext Q
    simp only [Qh, Ql, Qheavy, Qlight, mem_union, mem_filter]
    constructor
    · rintro (h | h) <;> tauto
    · intro hQ
      by_cases h : m_threshold ≤ (fiber P₀ f Q).card
      · exact Or.inl ⟨hQ, h⟩
      · have h' : (fiber P₀ f Q).card < m_threshold := by
          by_contra h''
          have : m_threshold ≤ (fiber P₀ f Q).card := Std.not_lt.mp h''
          exact h this
        exact Or.inr ⟨hQ, h'⟩
  have h2 : Disjoint Qh Ql := by
    rw [Finset.disjoint_left]
    intro Q hQ1 hQ2
    have h3 : m_threshold ≤ (fiber P₀ f Q).card := (mem_filter.mp hQ1).2
    have h4 : (fiber P₀ f Q).card < m_threshold := (mem_filter.mp hQ2).2
    linarith
  exact ⟨h1, h2⟩

lemma card_eq_sum_fibers (P₀ : Finset α) (f : α → β) :
    (P₀.card : ℝ) = ∑ Q ∈ coarseP₀ P₀ f, ((fiber P₀ f Q).card : ℝ) := by
  let S : Finset β := coarseP₀ P₀ f
  let fib : β → Finset α := fun Q => fiber P₀ f Q
  have h_biUnion : S.biUnion fib = P₀ := by
    ext p
    have h_iff : p ∈ S.biUnion fib ↔ p ∈ P₀ := by
      constructor
      · intro h
        rcases Finset.mem_biUnion.mp h with ⟨Q, hQ, hpQ⟩
        exact (Finset.mem_filter.mp hpQ).1
      · intro hp
        have h1 : f p ∈ S := by
          simp only [S, coarseP₀, Finset.mem_image]
          exact ⟨p, hp, rfl⟩
        have h2 : p ∈ fib (f p) := by
          apply Finset.mem_filter.mpr
          exact ⟨hp, by simp⟩
        exact Finset.mem_biUnion.mpr ⟨f p, h1, h2⟩
    simpa using h_iff
  have h_disj : ∀ (Q : β), Q ∈ S → ∀ (Q' : β), Q' ∈ S → Q ≠ Q' → Disjoint (fib Q) (fib Q') := by
    intro Q _ Q' _ hne
    rw [Finset.disjoint_left]
    intro p hp hp'
    have h1 : f p = Q := (mem_filter.mp hp).2
    have h2 : f p = Q' := (mem_filter.mp hp').2
    have h3 : Q = Q' := by rw [← h1, ← h2]
    exact hne h3
  have h_card : (S.biUnion fib).card = ∑ Q ∈ S, (fib Q).card :=
    Finset.card_biUnion h_disj
  have h1 : P₀.card = (S.biUnion fib).card := by
    exact congr_arg Finset.card h_biUnion.symm
  have h2 : P₀.card = ∑ Q ∈ S, (fib Q).card := h1.trans h_card
  have h3 : (P₀.card : ℝ) = ∑ Q ∈ S, ((fib Q).card : ℝ) := by
    have h_sum_cast : (↑(∑ Q ∈ S, (fib Q).card) : ℝ) = ∑ Q ∈ S, ((fib Q).card : ℝ) := by
      rw [Nat.cast_sum]
    have h4 : (P₀.card : ℝ) = (↑(∑ Q ∈ S, (fib Q).card) : ℝ) := by exact_mod_cast h2
    rw [h4, h_sum_cast]
  have h_final : (P₀.card : ℝ) = ∑ Q ∈ coarseP₀ P₀ f, ((fiber P₀ f Q).card : ℝ) := by
    convert h3 using 1 <;> rfl
  exact h_final

/-! ### Light contribution bound -/

lemma heavy_filter_light_bound
    (P₀ : Finset α) (f : α → β)
    (Δ u ε : ℝ) (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hε_pos : 0 < ε)
    (m_threshold : ℝ) (hm_threshold_eq : m_threshold = Real.rpow Δ (-u + ε))
    (h_coarse_upper : (coarseP₀ P₀ f).card ≤ Real.rpow Δ (-u - ε / 2))
    (h_small : Real.rpow Δ (3 * ε / 10) ≤ 1 / 2) :
    (∑ Q ∈ Qlight P₀ f m_threshold, (fiber P₀ f Q).card : ℝ) ≤
      (1 / 2 : ℝ) * Real.rpow Δ (-2 * u + ε / 5) := by
  let Ql := Qlight P₀ f m_threshold
  have h1 : ∀ Q ∈ Ql, ((fiber P₀ f Q).card : ℝ) ≤ m_threshold := by
    intro Q hQ
    have h : (fiber P₀ f Q).card < m_threshold := (mem_filter.mp hQ).2
    exact le_of_lt h
  have h2 : (∑ Q ∈ Ql, (fiber P₀ f Q).card : ℝ) ≤ (Ql.card : ℝ) * m_threshold := by
    calc (∑ Q ∈ Ql, (fiber P₀ f Q).card : ℝ)
      ≤ ∑ Q ∈ Ql, m_threshold := Finset.sum_le_sum h1
    _ = (Ql.card : ℝ) * m_threshold := by
      simp [Finset.sum_const] <;> ring
  have h3 : (Ql.card : ℝ) ≤ (coarseP₀ P₀ f).card := by
    exact_mod_cast Finset.card_le_card (filter_subset _ _)
  have h4 : (Ql.card : ℝ) ≤ Real.rpow Δ (-u - ε / 2) := by
    exact_mod_cast le_trans h3 h_coarse_upper
  rw [hm_threshold_eq] at h2
  have h5 : (Ql.card : ℝ) * Real.rpow Δ (-u + ε) ≤
      Real.rpow Δ (-u - ε / 2) * Real.rpow Δ (-u + ε) := by
    gcongr <;> exact Real.rpow_nonneg hΔ_pos.le _
  have h_add1 : (-u - ε / 2) + (-u + ε) = -2 * u + ε / 2 := by ring
  have h6 : Real.rpow Δ (-u - ε / 2) * Real.rpow Δ (-u + ε) =
      Real.rpow Δ ((-u - ε / 2) + (-u + ε)) := (Real.rpow_add hΔ_pos _ _).symm
  have h7 : Real.rpow Δ ((-u - ε / 2) + (-u + ε)) = Real.rpow Δ (-2 * u + ε / 2) := by
    rw [h_add1]
  have h_add2 : (3 * ε / 10) + (-2 * u + ε / 5) = -2 * u + ε / 2 := by ring
  have h9 : Real.rpow Δ ((3 * ε / 10) + (-2 * u + ε / 5)) =
      Real.rpow Δ (3 * ε / 10) * Real.rpow Δ (-2 * u + ε / 5) :=
    Real.rpow_add hΔ_pos _ _
  have h10 : Real.rpow Δ (-2 * u + ε / 2) =
      Real.rpow Δ (3 * ε / 10) * Real.rpow Δ (-2 * u + ε / 5) := by
    rw [h_add2] at h9
    exact h9
  have h11 : Real.rpow Δ (3 * ε / 10) * Real.rpow Δ (-2 * u + ε / 5) ≤
      (1 / 2 : ℝ) * Real.rpow Δ (-2 * u + ε / 5) := by
    have h12 : 0 ≤ Real.rpow Δ (-2 * u + ε / 5) := Real.rpow_nonneg hΔ_pos.le _
    nlinarith
  calc (∑ Q ∈ Ql, (fiber P₀ f Q).card : ℝ)
    ≤ (Ql.card : ℝ) * Real.rpow Δ (-u + ε) := h2
  _ ≤ Real.rpow Δ (-u - ε / 2) * Real.rpow Δ (-u + ε) := h5
  _ = Real.rpow Δ (-2 * u + ε / 2) := by rw [h6, h7]
  _ = Real.rpow Δ (3 * ε / 10) * Real.rpow Δ (-2 * u + ε / 5) := h10
  _ ≤ (1 / 2 : ℝ) * Real.rpow Δ (-2 * u + ε / 5) := h11

/-! ### Retained mass lower bound -/

lemma heavy_filter_retained_mass
    (P₀ : Finset α) (f : α → β)
    (Δ u ε : ℝ) (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hε_pos : 0 < ε)
    (m_threshold : ℝ)
    (h_fine_lower : (P₀.card : ℝ) ≥ Real.rpow Δ (-2 * u + ε / 5))
    (h_light_bound : (∑ Q ∈ Qlight P₀ f m_threshold, (fiber P₀ f Q).card : ℝ) ≤
        (1 / 2 : ℝ) * Real.rpow Δ (-2 * u + ε / 5))
    (h_small2 : Real.rpow Δ (ε / 20) ≤ 1 / 2) :
    (∑ Q ∈ Qheavy P₀ f m_threshold, (fiber P₀ f Q).card : ℝ) ≥
      Real.rpow Δ (-2 * u + ε / 4) := by
  let Qh := Qheavy P₀ f m_threshold
  let Ql := Qlight P₀ f m_threshold
  have h_disj := (heavy_light_partition P₀ f m_threshold).2
  have h_union := (heavy_light_partition P₀ f m_threshold).1
  have h_sum : (∑ Q ∈ coarseP₀ P₀ f, (fiber P₀ f Q).card : ℝ) =
        (∑ Q ∈ Qh, (fiber P₀ f Q).card : ℝ) +
        (∑ Q ∈ Ql, (fiber P₀ f Q).card : ℝ) := by
    have h : (∑ Q ∈ coarseP₀ P₀ f, (fiber P₀ f Q).card : ℝ) =
        (∑ Q ∈ (Qh ∪ Ql), (fiber P₀ f Q).card : ℝ) := by rw [h_union]
    rw [h]
    rw [Finset.sum_union h_disj] <;> rfl
  have h_card_eq : (P₀.card : ℝ) = (∑ Q ∈ coarseP₀ P₀ f, (fiber P₀ f Q).card : ℝ) :=
    card_eq_sum_fibers P₀ f
  have h_partition : (P₀.card : ℝ) =
      (∑ Q ∈ Qh, (fiber P₀ f Q).card : ℝ) +
      (∑ Q ∈ Ql, (fiber P₀ f Q).card : ℝ) := by
    rw [h_card_eq, h_sum]
  have h_heavy_sum : (∑ Q ∈ Qh, (fiber P₀ f Q).card : ℝ) =
      (P₀.card : ℝ) - (∑ Q ∈ Ql, (fiber P₀ f Q).card : ℝ) := by
    linarith [h_partition]
  have h5 : (∑ Q ∈ Qh, (fiber P₀ f Q).card : ℝ) ≥
      (1 / 2 : ℝ) * Real.rpow Δ (-2 * u + ε / 5) := by
    rw [h_heavy_sum]
    linarith [h_fine_lower, h_light_bound]
  have h_exp2 : (ε / 20) + (-2 * u + ε / 5) = -2 * u + ε / 4 := by ring
  have h9 : Real.rpow Δ ((ε / 20) + (-2 * u + ε / 5)) =
      Real.rpow Δ (ε / 20) * Real.rpow Δ (-2 * u + ε / 5) :=
    Real.rpow_add hΔ_pos _ _
  have h10 : Real.rpow Δ (-2 * u + ε / 4) =
      Real.rpow Δ (ε / 20) * Real.rpow Δ (-2 * u + ε / 5) := by
    rw [h_exp2] at h9
    exact h9
  have h11 : (1 / 2 : ℝ) * Real.rpow Δ (-2 * u + ε / 5) ≥
      Real.rpow Δ (-2 * u + ε / 4) := by
    rw [h10]
    have h12 : Real.rpow Δ (ε / 20) ≤ 1 / 2 := h_small2
    have h13 : 0 ≤ Real.rpow Δ (-2 * u + ε / 5) := Real.rpow_nonneg hΔ_pos.le _
    nlinarith
  exact le_trans h11 h5

/-! ### Coarse card lower bound -/

lemma heavy_filter_coarse_lower
    (P₀ : Finset α) (f : α → β)
    (Δ u ε : ℝ) (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hε_pos : 0 < ε)
    (m_threshold : ℝ)
    (h_retained : (∑ Q ∈ Qheavy P₀ f m_threshold, (fiber P₀ f Q).card : ℝ) ≥
        Real.rpow Δ (-2 * u + ε / 4))
    (h_fibre_upper : ∀ Q ∈ Qheavy P₀ f m_threshold,
        (fiber P₀ f Q).card ≤ Real.rpow Δ (-u - 3 * ε / 5)) :
    (Qheavy P₀ f m_threshold).card ≥ Real.rpow Δ (-u + ε) := by
  let Qh := Qheavy P₀ f m_threshold
  have h1 : (∑ Q ∈ Qh, (fiber P₀ f Q).card : ℝ) ≤
      (Qh.card : ℝ) * Real.rpow Δ (-u - 3 * ε / 5) := by
    have h2 : ∀ Q ∈ Qh, ((fiber P₀ f Q).card : ℝ) ≤ Real.rpow Δ (-u - 3 * ε / 5) :=
      h_fibre_upper
    calc (∑ Q ∈ Qh, (fiber P₀ f Q).card : ℝ)
      ≤ ∑ Q ∈ Qh, Real.rpow Δ (-u - 3 * ε / 5) := Finset.sum_le_sum h2
    _ = (Qh.card : ℝ) * Real.rpow Δ (-u - 3 * ε / 5) := by
      simp [Finset.sum_const] <;> ring
  have h_pos : 0 < Real.rpow Δ (-u - 3 * ε / 5) := Real.rpow_pos_of_pos hΔ_pos _
  have h3 : (Qh.card : ℝ) * Real.rpow Δ (-u - 3 * ε / 5) ≥
      Real.rpow Δ (-2 * u + ε / 4) := by
    calc (Qh.card : ℝ) * Real.rpow Δ (-u - 3 * ε / 5)
      ≥ (∑ Q ∈ Qh, (fiber P₀ f Q).card : ℝ) := h1
    _ ≥ Real.rpow Δ (-2 * u + ε / 4) := h_retained
  set b := Real.rpow Δ (-u - 3 * ε / 5) with hb
  have h_pos_b : 0 < b := h_pos
  have h4 : (Qh.card : ℝ) ≥ Real.rpow Δ (-2 * u + ε / 4) / b := by
    have h5 : (Qh.card : ℝ) * b ≥ Real.rpow Δ (-2 * u + ε / 4) := h3
    calc (Qh.card : ℝ)
      = ((Qh.card : ℝ) * b) / b := by field_simp [h_pos_b.ne'] <;> ring
    _ ≥ (Real.rpow Δ (-2 * u + ε / 4)) / b := by gcongr
  have h_exp3 : (-2 * u + ε / 4) - (-u - 3 * ε / 5) = -u + 17 * ε / 20 := by ring
  have h_rpow_div : Real.rpow Δ (-2 * u + ε / 4) / b =
      Real.rpow Δ ((-2 * u + ε / 4) + (u + 3 * ε / 5)) := by
    have h_neg : b⁻¹ = Real.rpow Δ (u + 3 * ε / 5) := by
      have h_exp : -(-u - 3 * ε / 5) = u + 3 * ε / 5 := by ring
      have h : (Real.rpow Δ (-u - 3 * ε / 5))⁻¹ = Real.rpow Δ (-(-u - 3 * ε / 5)) :=
        (Real.rpow_neg hΔ_pos.le (-u - 3 * ε / 5)).symm
      rw [h_exp] at h
      simpa [hb] using h
    have h : Real.rpow Δ (-2 * u + ε / 4) / b =
        Real.rpow Δ (-2 * u + ε / 4) * b⁻¹ := by ring
    rw [h, h_neg]
    exact (Real.rpow_add hΔ_pos _ _).symm
  rw [h_rpow_div] at h4
  have h7 : (-2 * u + ε / 4) + (u + 3 * ε / 5) = -u + 17 * ε / 20 := by ring
  rw [h7] at h4
  have h8 : Real.rpow Δ (-u + 17 * ε / 20) ≥ Real.rpow Δ (-u + ε) := by
    apply Real.rpow_le_rpow_of_exponent_ge hΔ_pos (by linarith)
    <;> linarith
  exact le_trans h8 h4

/-! ### Point set restriction -/

/-- Restrict P₀ to points whose coarse parent is in Qheavy. -/
def restrictPoints (P₀ : Finset α) (f : α → β) (m_threshold : ℝ) : Finset α :=
  P₀.filter (fun p => f p ∈ Qheavy P₀ f m_threshold)

/-- For a heavy Q, the restricted fiber equals the original fiber. -/
lemma restricted_fiber_eq_heavy
    (P₀ : Finset α) (f : α → β) (m_threshold : ℝ)
    (Q : β) (hQ : Q ∈ Qheavy P₀ f m_threshold) :
    fiber (restrictPoints P₀ f m_threshold) f Q = fiber P₀ f Q := by
  ext p
  simp only [fiber, restrictPoints, mem_filter]
  constructor
  · rintro ⟨⟨hp, h_in_heavy⟩, h_eq⟩
    exact ⟨hp, h_eq⟩
  · rintro ⟨hp, h_eq⟩
    have h_in_heavy : f p ∈ Qheavy P₀ f m_threshold := by
      rw [h_eq]
      exact hQ
    exact ⟨⟨hp, h_in_heavy⟩, h_eq⟩

/-- The restricted point set is a subset of the original. -/
lemma restrictPoints_subset (P₀ : Finset α) (f : α → β) (m_threshold : ℝ) :
    restrictPoints P₀ f m_threshold ⊆ P₀ := by
  exact filter_subset _ _

/-- Coarse parents of restricted points are exactly Qheavy.
    Requires `0 < m_threshold` so heavy fibers are nonempty. -/
lemma restricted_coarse_eq
    (P₀ : Finset α) (f : α → β) (m_threshold : ℝ) (hm_threshold_pos : 0 < m_threshold) :
    coarseP₀ (restrictPoints P₀ f m_threshold) f = Qheavy P₀ f m_threshold := by
  ext Q
  simp only [coarseP₀, mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_filter.mp hp).2
  · intro hQ
    have h1 : m_threshold ≤ (fiber P₀ f Q).card := (mem_filter.mp hQ).2
    have h_nonempty : (fiber P₀ f Q).Nonempty := by
      by_contra h
      have h2 : (fiber P₀ f Q).card = 0 := by
        simpa [Finset.not_nonempty_iff_eq_empty] using h
      have h3 : (m_threshold : ℝ) ≤ ((fiber P₀ f Q).card : ℝ) := h1
      rw [h2] at h3
      have h4 : (m_threshold : ℝ) ≤ 0 := by simpa using h3
      linarith
    rcases h_nonempty with ⟨p, hp⟩
    have h6 : f p = Q := (mem_filter.mp hp).2
    have h7 : p ∈ restrictPoints P₀ f m_threshold := by
      simp only [restrictPoints, mem_filter]
      exact ⟨(mem_filter.mp hp).1, by rw [h6] <;> exact hQ⟩
    exact ⟨p, h7, h6⟩

/-! ### Per-square upper weakening -/

/-- Weaken sharp per-square upper Δ^{-u-3ε/5} to public Δ^{-u-ε}. -/
lemma weaken_per_square_upper
    (Δ u ε : ℝ) (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1) (hε_pos : 0 < ε) :
    Real.rpow Δ (-u - 3 * ε / 5) ≤ Real.rpow Δ (-u - ε) := by
  apply Real.rpow_le_rpow_of_exponent_ge hΔ_pos (by linarith)
  <;> linarith

end DirecretisedFurstenbergEstimate.FrontEndLemmas.HeavyParentFiltering
