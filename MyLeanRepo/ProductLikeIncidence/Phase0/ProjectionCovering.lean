module

/-
# 4δ-Neighborhood Covering Lemma

If B is pointwise within 4δ of A in ℝ, then the δ-covering number of B
is at most 9 times the δ-covering number of A.

This generalizes `thickening_covering_factor5` (which handles 2δ with factor 5)
to 4δ with factor 9.

## Key lemma

`neighborhood_covering_bound_1d`: If ∀ b ∈ B, ∃ a ∈ A, |b - a| ≤ 4δ,
then Nδ(B) ≤ 9 · Nδ(A).

Reuses `cubeIndexSet` and `coveringNumber_eq_cubeIndexSet` from CoefficientRounding.
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.CoefficientRounding
public import MyLeanRepo.SetDiscretizationBridge
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open ENNReal Set Bornology Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- If |b - a| ≤ 4δ, their δ-cube indices differ by at most 4. -/
private lemma index_diff_le_4 {δ : ℝ} (hδ_pos : 0 < δ) {a b : ℝ}
    (kb ka : ℤ)
    (hb1 : δ * (kb : ℝ) ≤ b) (hb2 : b < δ * ((kb : ℝ) + 1))
    (ha1 : δ * (ka : ℝ) ≤ a) (ha2 : a < δ * ((ka : ℝ) + 1))
    (h : |b - a| ≤ 4 * δ) : |kb - ka| ≤ 4 := by
  have h8 : b - a ≤ 4 * δ := (abs_le.mp h).2
  have h13 : a - b ≤ 4 * δ := by
    have h15 : |a - b| ≤ 4 * δ := by
      rw [abs_sub_comm]; exact h
    exact (abs_le.mp h15).2
  have h_upper : kb - ka ≤ 4 := by
    by_contra h
    have h' : kb - ka ≥ 5 := by omega
    have h9 : 4 ≤ (kb : ℝ) - (ka : ℝ) - 1 := by
      have h10 : (kb : ℝ) - (ka : ℝ) ≥ 5 := by exact_mod_cast h'
      linarith
    have h10 : b - a > δ * ((kb : ℝ) - (ka : ℝ) - 1) := by linarith
    have h11 : δ * 4 ≤ δ * ((kb : ℝ) - (ka : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left h9 (by linarith)
    linarith
  have h_lower : kb - ka ≥ -4 := by
    by_contra h
    have h' : ka - kb ≥ 5 := by omega
    have h9 : 4 ≤ (ka : ℝ) - (kb : ℝ) - 1 := by
      have h10 : (ka : ℝ) - (kb : ℝ) ≥ 5 := by exact_mod_cast h'
      linarith
    have h10 : a - b > δ * ((ka : ℝ) - (kb : ℝ) - 1) := by linarith
    have h11 : δ * 4 ≤ δ * ((ka : ℝ) - (kb : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left h9 (by linarith)
    linarith
  exact abs_le.mpr ⟨h_lower, h_upper⟩

/-- **Geometric neighborhood covering bound in 1D** (4δ version).

If every point of B is within 4δ of some point of A, then the δ-covering
number of B is at most 9 times the δ-covering number of A.

Requires A bounded (to ensure the cube index set is finite). -/
lemma neighborhood_covering_bound_1d {δ : ℝ} (hδ_pos : 0 < δ)
    {A B : Set ℝ} (hA_bdd : Bornology.IsBounded A)
    (h_near : ∀ b ∈ B, ∃ a ∈ A, |b - a| ≤ 4 * δ) :
    ENat.toENNReal (dyadicCoveringNumber (d := 1) δ (productLikeRealLineCopy B)) ≤
      (9 : ENNReal) * ENat.toENNReal (dyadicCoveringNumber (d := 1) δ (productLikeRealLineCopy A)) := by
  let idxA := cubeIndexSet δ A
  let idxB := cubeIndexSet δ B
  have h_idxA_finite : Set.Finite idxA :=
    SetDiscretizationBridge.cubeIndexSet_finite hδ_pos hA_bdd
  let idxA_fin : Finset ℤ := h_idxA_finite.toFinset
  have h_idxA_coe : (idxA_fin : Set ℤ) = idxA := Set.Finite.coe_toFinset _
  have h_main : idxB ⊆ ⋃ m ∈ idxA, (Finset.Icc (m - 4) (m + 4) : Set ℤ) := by
    intro k hk
    rcases hk with ⟨b, hb_range, hbB⟩
    rcases h_near b hbB with ⟨a, haA, hdist⟩
    let m : ℤ := Int.floor (a / δ)
    have hm1 : δ * (m : ℝ) ≤ a := by
      have h : (m : ℝ) ≤ a / δ := Int.floor_le (a / δ)
      have h2 : δ * (m : ℝ) ≤ δ * (a / δ) := by gcongr
      have h3 : δ * (a / δ) = a := by field_simp [hδ_pos.ne'] <;> ring
      rw [h3] at h2; exact h2
    have hm2 : a < δ * ((m : ℝ) + 1) := by
      have h : a / δ < (m : ℝ) + 1 := Int.lt_floor_add_one (a / δ)
      have h2 : δ * (a / δ) < δ * ((m : ℝ) + 1) := by gcongr
      have h3 : δ * (a / δ) = a := by field_simp [hδ_pos.ne'] <;> ring
      rw [h3] at h2; exact h2
    have hm_in_idxA : m ∈ idxA := by
      simp only [idxA, cubeIndexSet, Set.mem_setOf_eq]
      exact ⟨a, ⟨hm1, hm2⟩, haA⟩
    have h_kb1 : δ * (k : ℝ) ≤ b := hb_range.1
    have h_kb2 : b < δ * ((k : ℝ) + 1) := hb_range.2
    have hdiff : |k - m| ≤ 4 := index_diff_le_4 hδ_pos k m h_kb1 h_kb2 hm1 hm2 hdist
    have h_k_range : k ∈ (Finset.Icc (m - 4) (m + 4) : Set ℤ) := by
      have h1 : -4 ≤ k - m := (abs_le.mp hdiff).1
      have h2 : k - m ≤ 4 := (abs_le.mp hdiff).2
      simp only [Finset.mem_Icc, Finset.mem_coe]
      <;> omega
    exact Set.mem_iUnion₂.mpr ⟨m, hm_in_idxA, h_k_range⟩
  let U : Finset ℤ := idxA_fin.biUnion (fun m => Finset.Icc (m - 4) (m + 4))
  have hU : (U : Set ℤ) = (⋃ m ∈ idxA, (Finset.Icc (m - 4) (m + 4) : Set ℤ)) := by
    ext z
    simp [U, h_idxA_coe]
    <;> aesop
  have h1 : idxB.encard ≤ (U : Set ℤ).encard := by
    have h1a : idxB ⊆ (U : Set ℤ) := by
      rw [hU]
      exact h_main
    exact Set.encard_mono h1a
  have h_card9 : ∀ (m : ℤ), (Finset.Icc (m - 4) (m + 4)).card = 9 := by
    intro m
    have h : (Finset.Icc (m - 4) (m + 4)).card = (m + 4 + 1 - (m - 4)).toNat := by
      simp
    rw [h]
    have h2 : m + 4 + 1 - (m - 4) = 9 := by omega
    rw [h2]
    <;> simp [Int.toNat]
  have h2 : U.card ≤ 9 * idxA_fin.card := by
    have h_card_bunion : U.card ≤ ∑ m ∈ idxA_fin, (Finset.Icc (m - 4) (m + 4)).card :=
      Finset.card_biUnion_le
    have h_sum : ∑ m ∈ idxA_fin, (Finset.Icc (m - 4) (m + 4)).card ≤ ∑ m ∈ idxA_fin, 9 := by
      apply Finset.sum_le_sum
      intro m _
      rw [h_card9 m]
    have h_final : ∑ m ∈ idxA_fin, (9 : ℕ) = 9 * idxA_fin.card := by
      rw [Finset.sum_const, mul_comm] <;> rfl
    calc U.card
      ≤ ∑ m ∈ idxA_fin, (Finset.Icc (m - 4) (m + 4)).card := h_card_bunion
    _ ≤ ∑ m ∈ idxA_fin, 9 := h_sum
    _ = 9 * idxA_fin.card := h_final
  have h3 : ((U : Set ℤ).encard : ENNReal) ≤ (9 : ENNReal) * ((idxA : Set ℤ).encard : ENNReal) := by
    have h4 : ((U : Set ℤ).encard : ENNReal) = ↑U.card := by
      simp
    have h5 : ((idxA : Set ℤ).encard : ENNReal) = ↑idxA_fin.card := by
      rw [← h_idxA_coe] <;> simp
    rw [h4, h5]
    exact_mod_cast h2
  have h_card : (idxB.encard : ENNReal) ≤ (9 : ENNReal) * (idxA.encard : ENNReal) := by
    calc (idxB.encard : ENNReal)
      ≤ ((U : Set ℤ).encard : ENNReal) := by exact_mod_cast h1
    _ ≤ (9 : ENNReal) * (idxA.encard : ENNReal) := h3
  have h_eqB : dyadicCoveringNumber (d := 1) δ (productLikeRealLineCopy B) = idxB.encard :=
    coveringNumber_eq_cubeIndexSet hδ_pos
  have h_eqA : dyadicCoveringNumber (d := 1) δ (productLikeRealLineCopy A) = idxA.encard :=
    coveringNumber_eq_cubeIndexSet hδ_pos
  rw [h_eqB, h_eqA]
  exact h_card

end ProductLikeIncidence.ProductReduction
