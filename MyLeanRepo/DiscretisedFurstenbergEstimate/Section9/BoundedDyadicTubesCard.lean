module

/-
  Bounded dyadic tubes cardinality bound.

  If a finset of dyadic tubes has |slope| ≤ 3/2 and |intercept| ≤ 3,
  then its cardinality is at most 2^(2n+7).

  Extracted from BridgeHelpers to break a reverse import chain:
  Section9Assembly → RawFibreProducer → BridgeHelpers → ... → target

  Whiteprint node: section9 / bounded_dyadic_tubes_card
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DiscretisedFurstenbergEstimate

/-- Bound cardinality of a finset of dyadic tubes with |slope| ≤ 3/2, |intercept| ≤ 3.
    The total number is at most 2^(2n+7). -/
lemma bounded_dyadic_tubes_card {n : ℕ} {S : Finset (DyadicTube n)}
    (h_slope : ∀ U ∈ S, |U.slope| ≤ 3 / 2)
    (h_intercept : ∀ U ∈ S, |U.intercept| ≤ 3) :
    S.card ≤ 2 ^ (2 * n + 7) := by
  let δ_n := dyadicDelta n
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  have hδn_inv : δ_n⁻¹ = (2 : ℝ)^n := by
    have h1 : δ_n = (1 / 2 : ℝ)^n := by
      simp [dyadicDelta, δ_n]
    have h2 : (1 / 2 : ℝ)^n = 1 / (2 : ℝ)^n := by
      induction n <;> simp [*, pow_succ] <;> field_simp <;> ring
    have h3 : δ_n = 1 / (2 : ℝ)^n := by
      rw [h1, h2]
    rw [h3]
    have h4 : (1 / (2 : ℝ)^n)⁻¹ = (2 : ℝ)^n := by
      field_simp <;> norm_cast
    exact h4
  have ha_bound : ∀ U ∈ S, |(U.a : ℝ)| ≤ 3 * 2^n + 1 := by
    intro U hU
    have h1 : |U.slope| ≤ 3 / 2 := h_slope U hU
    have h2 : |(U.a : ℝ)| * δ_n ≤ 3 / 2 := by
      have h_eq : U.slope = (U.a : ℝ) * δ_n := by rfl
      rw [h_eq] at h1
      have h_abs : |(U.a : ℝ) * δ_n| = |(U.a : ℝ)| * δ_n := by
        rw [abs_mul, abs_of_pos hδn_pos]
      rw [h_abs] at h1; exact h1
    have h3 : |(U.a : ℝ)| ≤ (3 / 2 : ℝ) * δ_n⁻¹ := by
      calc |(U.a : ℝ)|
        = |(U.a : ℝ)| * δ_n * δ_n⁻¹ := by field_simp [hδn_pos.ne'] <;> ring
      _ ≤ (3 / 2 : ℝ) * δ_n⁻¹ := by gcongr
    rw [hδn_inv] at h3
    have h4 : |(U.a : ℝ)| ≤ 3 / 2 * (2 : ℝ)^n := h3
    have h5 : (3 / 2 : ℝ) * (2 : ℝ)^n ≤ 3 * (2 : ℝ)^n + 1 := by
      have h6 : 0 ≤ (2 : ℝ)^n := by positivity
      nlinarith
    exact le_trans h4 h5
  have hb_bound : ∀ U ∈ S, |(U.b : ℝ)| ≤ 3 * 2^n + 1 := by
    intro U hU
    have h1 : |U.intercept| ≤ 3 := h_intercept U hU
    have h2 : |(U.b : ℝ)| * δ_n ≤ 3 := by
      have h_eq : U.intercept = (U.b : ℝ) * δ_n := by rfl
      rw [h_eq] at h1
      have h_abs : |(U.b : ℝ) * δ_n| = |(U.b : ℝ)| * δ_n := by
        rw [abs_mul, abs_of_pos hδn_pos]
      rw [h_abs] at h1; exact h1
    have h3 : |(U.b : ℝ)| ≤ (3 : ℝ) * δ_n⁻¹ := by
      calc |(U.b : ℝ)|
        = |(U.b : ℝ)| * δ_n * δ_n⁻¹ := by field_simp [hδn_pos.ne'] <;> ring
      _ ≤ (3 : ℝ) * δ_n⁻¹ := by gcongr
    rw [hδn_inv] at h3
    have h4 : |(U.b : ℝ)| ≤ 3 * (2 : ℝ)^n := h3
    have h5 : 3 * (2 : ℝ)^n ≤ 3 * (2 : ℝ)^n + 1 := by linarith
    exact le_trans h4 h5
  let N_int : ℕ := 3 * 2^n + 1
  let A : Finset ℤ := Finset.Icc (-(N_int : ℤ)) (N_int : ℤ)
  let B : Finset ℤ := Finset.Icc (-(N_int : ℤ)) (N_int : ℤ)
  have hA_card : A.card = 2 * N_int + 1 := by
    simp [A, Int.card_Icc] <;> omega
  have hB_card : B.card = 2 * N_int + 1 := by
    simp [B, Int.card_Icc] <;> omega
  have h_sub1 : ∀ U ∈ S, U.a ∈ A := by
    intro U hU
    have h6 : |(U.a : ℝ)| ≤ (N_int : ℝ) := by
      simpa [N_int] using ha_bound U hU
    have h7 : -(N_int : ℝ) ≤ (U.a : ℝ) := (abs_le.mp h6).1
    have h8 : (U.a : ℝ) ≤ (N_int : ℝ) := (abs_le.mp h6).2
    have h9 : -(N_int : ℤ) ≤ U.a := by exact_mod_cast h7
    have h10 : U.a ≤ (N_int : ℤ) := by exact_mod_cast h8
    simp only [A, Finset.mem_Icc] <;> exact ⟨h9, h10⟩
  have h_sub2 : ∀ U ∈ S, U.b ∈ B := by
    intro U hU
    have h6 : |(U.b : ℝ)| ≤ (N_int : ℝ) := by
      simpa [N_int] using hb_bound U hU
    have h7 : -(N_int : ℝ) ≤ (U.b : ℝ) := (abs_le.mp h6).1
    have h8 : (U.b : ℝ) ≤ (N_int : ℝ) := (abs_le.mp h6).2
    have h9 : -(N_int : ℤ) ≤ U.b := by exact_mod_cast h7
    have h10 : U.b ≤ (N_int : ℤ) := by exact_mod_cast h8
    simp only [B, Finset.mem_Icc] <;> exact ⟨h9, h10⟩
  let f : DyadicTube n → ℤ × ℤ := fun U => (U.a, U.b)
  have h_inj : Set.InjOn f (S : Set (DyadicTube n)) := by
    intro U1 _ U2 _ h
    have h1 : U1.a = U2.a := (Prod.ext_iff.mp h).1
    have h2 : U1.b = U2.b := (Prod.ext_iff.mp h).2
    cases U1 <;> cases U2 <;> simp_all <;> tauto
  have h_img_sub : (S.image f) ⊆ A ×ˢ B := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨U, hU, rfl⟩
    exact Finset.mem_product.mpr ⟨h_sub1 U hU, h_sub2 U hU⟩
  have h_card_img : (S.image f).card = S.card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h_card_prod : (A ×ˢ B).card = A.card * B.card := Finset.card_product A B
  have h_main : S.card ≤ (2 * N_int + 1) * (2 * N_int + 1) := by
    have h1 : S.card ≤ (A ×ˢ B).card := by
      calc S.card
        = (S.image f).card := h_card_img.symm
      _ ≤ (A ×ˢ B).card := Finset.card_le_card h_img_sub
    have h2 : (A ×ˢ B).card ≤ (2 * N_int + 1) * (2 * N_int + 1) := by
      have h21 : (A ×ˢ B).card = A.card * B.card := h_card_prod
      have ha : A.card ≤ 2 * N_int + 1 := hA_card.le
      have hb : B.card ≤ 2 * N_int + 1 := hB_card.le
      have h_pos1 : 0 ≤ A.card := by positivity
      have h_pos2 : 0 ≤ B.card := by positivity
      have h_ab : A.card * B.card ≤ (2 * N_int + 1) * (2 * N_int + 1) := by
        nlinarith
      rw [h21]
      exact h_ab
    exact le_trans h1 h2
  have h_final : (2 * N_int + 1) * (2 * N_int + 1) ≤ 2 ^ (2 * n + 7) := by
    simp only [N_int]
    have h6 : 2 * (3 * 2^n + 1) + 1 ≤ 9 * 2^n := by
      have h7 : 2 * (3 * 2^n + 1) + 1 = 6 * 2^n + 3 := by ring
      rw [h7]
      have h8 : 3 ≤ 3 * 2^n := by
        have h9 : 1 ≤ 2^n := by apply Nat.one_le_pow <;> norm_num
        nlinarith
      nlinarith
    have h7 : (2 * (3 * 2^n + 1) + 1) * (2 * (3 * 2^n + 1) + 1) ≤ (9 * 2^n) * (9 * 2^n) := by gcongr
    have h8 : (9 * 2^n) * (9 * 2^n) = 81 * 2^(2 * n) := by ring
    rw [h8] at h7
    have h9 : 81 * 2^(2 * n) ≤ 2 ^ (2 * n + 7) := by
      have h10 : 2 ^ (2 * n + 7) = 128 * 2^(2 * n) := by
        simp [pow_add] <;> ring
      rw [h10]
      have h11 : 0 ≤ 2^(2 * n) := by positivity
      nlinarith
    exact le_trans h7 h9
  exact le_trans h_main h_final

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
