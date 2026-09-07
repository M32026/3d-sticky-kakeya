module

/-
# IsRealDeltaSet subset inheritance

If A ⊆ B, B is a (δ,s,C)-set, and Nreal δ A ≥ c · Nreal δ B,
then A is a (δ,s,C/c)-set.

## Proof sketch
For any dyadic cube Q at scale r:
  Nreal δ (A ∩ Q) ≤ Nreal δ (B ∩ Q)           (monotonicity)
    ≤ C · Nreal δ B · r^s                      (B's regularity)
    ≤ C · (1/c) · Nreal δ A · r^s              (fraction bound)
    = (C/c) · Nreal δ A · r^s

Nonemptiness of A follows from Nreal δ A > 0.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Finset Set Bornology Classical

namespace robust_projection

/-- Covering number is monotone with respect to set inclusion. -/
lemma dyadic_covering_number_mono {d : ℕ} {δ : ℝ}
    {P Q : Set (EuclideanSpace ℝ (Fin d))} (h : P ⊆ Q) :
    dyadicCoveringNumber δ P ≤ dyadicCoveringNumber δ Q := by
  have h1 : dyadicCubesMeeting δ P ⊆ dyadicCubesMeeting δ Q := by
    intro x hx
    have h2 : (x ∩ P).Nonempty := hx.2
    have h3 : (x ∩ Q).Nonempty := by
      exact h2.mono (Set.inter_subset_inter_right x h)
    exact ⟨hx.1, h3⟩
  exact Set.encard_mono h1

/-- Nonempty set has positive dyadic covering number. -/
lemma dyadic_covering_number_pos {d : ℕ} {δ : ℝ}
    {P : Set (EuclideanSpace ℝ (Fin d))} (hδ : 0 < δ)
    (hP : P.Nonempty) : 0 < dyadicCoveringNumber δ P := by
  rcases hP with ⟨x, hx⟩
  -- For each coordinate, find an integer k_i such that x i ∈ Ico (δ*k_i) (δ*(k_i+1))
  let k : Fin d → ℤ := fun i => Int.floor (x i / δ)
  have hk : ∀ i, x i ∈ Set.Ico (δ * (k i : ℝ)) (δ * ((k i : ℝ) + 1)) := by
    intro i
    have h4 : (k i : ℝ) ≤ x i / δ := Int.floor_le (x i / δ)
    have h5 : x i / δ < (k i : ℝ) + 1 := Int.lt_floor_add_one (x i / δ)
    constructor
    · calc x i = δ * (x i / δ) := by field_simp [hδ.ne'] <;> ring
      _ ≥ δ * (k i : ℝ) := by gcongr
    · calc x i = δ * (x i / δ) := by field_simp [hδ.ne'] <;> ring
      _ < δ * ((k i : ℝ) + 1) := by gcongr
  let Q := dyadicCube δ k
  have hQ_in : Q ∈ dyadicCubes d δ := ⟨k, rfl⟩
  have hQ_meet : (Q ∩ P).Nonempty := ⟨x, hk, hx⟩
  have h4 : Q ∈ dyadicCubesMeeting δ P := ⟨hQ_in, hQ_meet⟩
  have h5 : (dyadicCubesMeeting δ P).Nonempty := ⟨Q, h4⟩
  exact Set.encard_pos.mpr h5

/-- If A ⊆ B, B is a (δ,s,C)-set, and Nreal δ A ≥ c · Nreal δ B with c > 0,
then A is a (δ,s,C/c)-set. -/
lemma is_real_delta_set_of_subset_fraction
    {δ s C c : ℝ} {A B : Set ℝ}
    (hA_sub_B : A ⊆ B)
    (hB : IsRealDeltaSet δ s C B)
    (hc_pos : 0 < c)
    (h_fraction : ENNReal.ofReal c * Nreal δ B ≤ Nreal δ A) :
    IsRealDeltaSet δ s (C / c) A := by
  rcases hB with ⟨hB_bdd, hB_nonempty, h_d, hδ_dyadic, hδ_pos,
    hs_nonneg, hs_le_d, hC_pos, hB_reg⟩

  have h_copy_sub : realLineCopy A ⊆ realLineCopy B := by
    intro x hx
    exact hA_sub_B hx

  have hA_bdd : Bornology.IsBounded (realLineCopy A) :=
    hB_bdd.subset h_copy_sub

  -- Nreal δ B > 0
  have hN_B_pos : 0 < Nreal δ B := by
    have h : 0 < dyadicCoveringNumber δ (realLineCopy B) :=
      dyadic_covering_number_pos hδ_pos hB_nonempty
    have h' : dyadicCoveringNumber δ (realLineCopy B) ≠ 0 := h.ne'
    have h'' : ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy B)) ≠ 0 := by
      by_cases h7 : dyadicCoveringNumber δ (realLineCopy B) = ⊤
      · rw [h7] <;> simp
      · have h8 : ∃ (k : ℕ), (↑k : ENat) = dyadicCoveringNumber δ (realLineCopy B) :=
          ENat.ne_top_iff_exists.mp h7
        rcases h8 with ⟨k, hk⟩
        have hk0 : k ≠ 0 := by
          intro h9
          rw [h9] at hk
          rw [← hk] at h'
          simp at h'
        rw [← hk]
        simpa using hk0
    exact h''.bot_lt

  -- Nreal δ A > 0
  have hN_A_pos : 0 < Nreal δ A := by
    have h1 : ENNReal.ofReal c ≠ 0 := by
      exact (ENNReal.ofReal_pos.mpr hc_pos).ne'
    have h2 : 0 < ENNReal.ofReal c * Nreal δ B :=
      ENNReal.mul_pos h1 hN_B_pos.ne'
    exact lt_of_lt_of_le h2 h_fraction

  -- A nonempty
  have hA_nonempty : (realLineCopy A).Nonempty := by
    by_contra h
    have h3 : realLineCopy A = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have h4 : Nreal δ A = 0 := by
      rw [Nreal, h3]
      simp [dyadicCoveringNumber, dyadicCubesMeeting]
      <;> aesop
    rw [h4] at hN_A_pos
    simpa using hN_A_pos

  -- Nreal δ B ≤ (1/c) * Nreal δ A
  have hB_le : Nreal δ B ≤ ENNReal.ofReal (1 / c) * Nreal δ A := by
    have h1 : ENNReal.ofReal (1 / c) * (ENNReal.ofReal c * Nreal δ B) ≤
        ENNReal.ofReal (1 / c) * Nreal δ A := by
      gcongr
    have h2 : ENNReal.ofReal (1 / c) * ENNReal.ofReal c = 1 := by
      have h3 : (1 / c : ℝ) * c = 1 := by
        field_simp [hc_pos.ne'] <;> ring
      have h4 : ENNReal.ofReal (1 / c) * ENNReal.ofReal c = ENNReal.ofReal ((1 / c) * c) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        <;> ring
      rw [h4, h3]
      <;> simp
    have h4 : ENNReal.ofReal (1 / c) * (ENNReal.ofReal c * Nreal δ B) =
        (ENNReal.ofReal (1 / c) * ENNReal.ofReal c) * Nreal δ B := by ring
    rw [h4, h2] at h1
    simpa using h1

  -- Monotonicity helper
  have h_mono : ∀ {P Q : Set (EuclideanSpace ℝ (Fin 1))},
      P ⊆ Q → dyadicCoveringNumber δ P ≤ dyadicCoveringNumber δ Q :=
    fun {P Q} h => dyadic_covering_number_mono h

  -- Regularity for A
  have hA_reg : ∀ ⦃r : ℝ⦄ ⦃Q : Set (EuclideanSpace ℝ (Fin 1))⦄,
      r ∈ dyadicScales → Q ∈ dyadicCubes 1 r → δ ≤ r → r ≤ 1 →
      ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A ∩ Q)) ≤
        ENNReal.ofReal (C / c) * ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A)) *
          ENNReal.ofReal (r ^ s) := by
    intro r Q hr hQ hδr hr1
    have h4 : realLineCopy A ∩ Q ⊆ realLineCopy B ∩ Q :=
      Set.inter_subset_inter_left Q h_copy_sub
    have h5 : ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A ∩ Q)) ≤
        ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy B ∩ Q)) := by
      exact_mod_cast h_mono h4
    have h6 := hB_reg hr hQ hδr hr1
    have h7 : ENNReal.ofReal C * Nreal δ B * ENNReal.ofReal (r ^ s) ≤
        ENNReal.ofReal (C / c) * Nreal δ A * ENNReal.ofReal (r ^ s) := by
      have h8 : ENNReal.ofReal C * Nreal δ B ≤
          ENNReal.ofReal (C / c) * Nreal δ A := by
        calc
          ENNReal.ofReal C * Nreal δ B
            ≤ ENNReal.ofReal C * (ENNReal.ofReal (1 / c) * Nreal δ A) := by gcongr
          _ = (ENNReal.ofReal C * ENNReal.ofReal (1 / c)) * Nreal δ A := by ring
          _ = ENNReal.ofReal (C * (1 / c)) * Nreal δ A := by
              rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
          _ = ENNReal.ofReal (C / c) * Nreal δ A := by
              have h9 : C * (1 / c) = C / c := by ring
              rw [h9]
      gcongr
    calc
      ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A ∩ Q))
        ≤ ENNReal.ofReal C * Nreal δ B * ENNReal.ofReal (r ^ s) := h5.trans h6
      _ ≤ ENNReal.ofReal (C / c) * Nreal δ A * ENNReal.ofReal (r ^ s) := h7

  exact ⟨hA_bdd, hA_nonempty, h_d, hδ_dyadic, hδ_pos, hs_nonneg, hs_le_d,
    by positivity, hA_reg⟩

end robust_projection
