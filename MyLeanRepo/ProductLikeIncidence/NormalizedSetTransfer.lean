module

/-
# Normalized Set Transfer Helpers

Lemmas for transferring δ-set bounds, difference-set bounds, and sum-set bounds
through normalization (independent additive translations).

## Main results

1. `normalized_self_diff_subset` — (B_norm+t) ⊆ B implies B_norm−B_norm ⊆ B−B
2. `normalized_cross_diff_subset_indep` — independent shifts for cross-difference
3. `normalized_self_difference_transfer` — transfer BSG bound through normalization
4. `delta_set_subset_with_retention` — A ⊆ B with retention gives δ-set blowup
5. `normalized_cross_difference_transfer` — cross-difference BSG with factor 2
6. `normalized_sum_transfer` — sum-set BSG with factor 2

## Dependencies

- `ProjectionBasic` for `Nreal`
- `Fjord.RingExpansionLemma51` for `translateSet`
- `DeltaSetTranslation` for `nreal_translate_real_le_two`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.Fjord.RingExpansionLemma51
public import MyLeanRepo.ProductLikeIncidence.DeltaSetTranslation
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Bornology ENNReal

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-! ### Helper: monotonicity of Nreal -/

/-- Monotonicity of `Nreal` under set inclusion. -/
lemma Nreal_mono {δ : ℝ} {A B : Set ℝ} (h : A ⊆ B) :
    Nreal δ A ≤ Nreal δ B := by
  dsimp only [Nreal]
  have h1 : realLineCopy A ⊆ realLineCopy B := by
    intro x hx
    have h2 : x 0 ∈ A := by simpa [realLineCopy] using hx
    have h3 : x 0 ∈ B := h h2
    simpa [realLineCopy] using h3
  exact ENat.toENNReal_mono (dyadicCoveringNumber_mono h1)

/-! ### Subset relations for normalized difference sets -/

/-- If (B_norm + t) ⊆ B, then B_norm − B_norm ⊆ B − B. -/
lemma normalized_self_diff_subset {t : ℝ} {B B_norm : Set ℝ}
    (h : (fun x => x + t) '' B_norm ⊆ B) :
    Set.image2 (· - ·) B_norm B_norm ⊆ Set.image2 (· - ·) B B := by
  intro z hz
  rcases hz with ⟨b1, hb1, b2, hb2, rfl⟩
  refine ⟨b1 + t, h ⟨b1, hb1, rfl⟩, b2 + t, h ⟨b2, hb2, rfl⟩, ?_⟩
  simp

/-- If B1_norm + k ⊆ B1 and B2_norm + j ⊆ B2, then
(B2_norm − B1_norm) ⊆ (B2 − B1) + (k − j). -/
lemma normalized_cross_diff_subset_indep
    {k j : ℝ} {B1 B2 B1_norm B2_norm : Set ℝ}
    (h1 : (fun x => x + k) '' B1_norm ⊆ B1)
    (h2 : (fun x => x + j) '' B2_norm ⊆ B2) :
    Set.image2 (· - ·) B2_norm B1_norm ⊆
      (fun x => x + (k - j)) '' (Set.image2 (· - ·) B2 B1) := by
  intro z hz
  rcases hz with ⟨b2, hb2, b1, hb1, rfl⟩
  have hb2' : b2 + j ∈ B2 := h2 ⟨b2, hb2, rfl⟩
  have hb1' : b1 + k ∈ B1 := h1 ⟨b1, hb1, rfl⟩
  refine ⟨(b2 + j) - (b1 + k), ⟨b2 + j, hb2', b1 + k, hb1', rfl⟩, ?_⟩
  simp [sub_add_sub_comm] <;> ring

/-! ### Self-difference transfer -/

/-- Transfer self-difference bound through normalization. -/
lemma normalized_self_difference_transfer
    {δ K R : ℝ} {B B_norm : Set ℝ} {t : ℝ}
    (hBSG : Nreal δ (Set.image2 (· - ·) B B) ≤ ENNReal.ofReal K * Nreal δ B)
    (h_retention : Nreal δ B ≤ ENNReal.ofReal R * Nreal δ B_norm)
    (h_chunk : (fun x => x + t) '' B_norm ⊆ B) :
    Nreal δ (Set.image2 (· - ·) B_norm B_norm) ≤
      ENNReal.ofReal K * ENNReal.ofReal R * Nreal δ B_norm := by
  have h_sub : Set.image2 (· - ·) B_norm B_norm ⊆ Set.image2 (· - ·) B B :=
    normalized_self_diff_subset h_chunk
  have h1 : Nreal δ (Set.image2 (· - ·) B_norm B_norm) ≤
      Nreal δ (Set.image2 (· - ·) B B) := Nreal_mono h_sub
  calc
    Nreal δ (Set.image2 (· - ·) B_norm B_norm)
      ≤ Nreal δ (Set.image2 (· - ·) B B) := h1
    _ ≤ ENNReal.ofReal K * Nreal δ B := hBSG
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal R * Nreal δ B_norm) := by
      exact mul_le_mul_of_nonneg_left h_retention (by positivity)
    _ = ENNReal.ofReal K * ENNReal.ofReal R * Nreal δ B_norm := by ring

/-! ### Subset preservation of δ-set with retention -/

/-- Subset preservation of δ-set with constant blowup via retention bound.
If A ⊆ B, B is a (δ, s, C)-set, and Nδ(B) ≤ M · Nδ(A),
then A is a (δ, s, C·M)-set. -/
lemma delta_set_subset_with_retention
    {δ s C M : ℝ} {A B : Set ℝ}
    (hA_bdd : IsBounded A) (hA_nonempty : A.Nonempty)
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hs_nonneg : 0 ≤ s) (hs_le_one : s ≤ 1)
    (hC_pos : 0 < C) (hM_pos : 0 < M)
    (hB : IsProductLikeRealDeltaSCSet δ s C B)
    (h_sub : A ⊆ B)
    (h_retention : Nreal δ B ≤ ENNReal.ofReal M * Nreal δ A) :
    IsProductLikeRealDeltaSCSet δ s (C * M) A := by
  rcases hB with ⟨hB_bdd, hB_nonempty, h1d, hδ_dyadic', hδ_pos', hs_nonneg', hs_le_one', hC_pos', hB_bound⟩
  have hA'_bdd : IsBounded (productLikeRealLineCopy A) :=
    productLikeRealLineCopy_bounded hA_bdd
  have hA'_nonempty : (productLikeRealLineCopy A).Nonempty := by
    rcases hA_nonempty with ⟨a, ha⟩
    let y : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 (Fin 1 → ℝ)).symm fun _ => a
    have h9 : y 0 = a := by simp [y]
    have h10 : y 0 ∈ A := by rw [h9]; exact ha
    have hy : y ∈ productLikeRealLineCopy A := by exact h10
    exact ⟨y, hy⟩
  refine ⟨hA'_bdd, hA'_nonempty, h1d, hδ_dyadic', hδ_pos', hs_nonneg', hs_le_one', by positivity, ?_⟩
  intro r Q hr_dyadic hQ hδ_le_r hr_le_one
  have h_sub1 : productLikeRealLineCopy A ∩ Q ⊆ productLikeRealLineCopy B ∩ Q := by
    intro x hx; exact ⟨h_sub hx.1, hx.2⟩
  have h_mono : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A ∩ Q)) ≤
      ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy B ∩ Q)) :=
    ENat.toENNReal_mono (Set.encard_mono (fun R hR =>
      ⟨hR.1, hR.2.mono (Set.inter_subset_inter_right R h_sub1)⟩))
  have h_boundB := hB_bound hr_dyadic hQ hδ_le_r hr_le_one
  have h_ret : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy B)) ≤
      ENNReal.ofReal M * ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A)) := by
    simpa [Nreal, productLikeRealLineCopy] using h_retention
  calc ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A ∩ Q))
    ≤ ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy B ∩ Q)) := h_mono
  _ ≤ ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy B)) *
        ENNReal.ofReal (r ^ s) := h_boundB
  _ ≤ ENNReal.ofReal C * (ENNReal.ofReal M * ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A))) *
        ENNReal.ofReal (r ^ s) := by gcongr <;> positivity
  _ = ENNReal.ofReal (C * M) * ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A)) *
        ENNReal.ofReal (r ^ s) := by
    rw [ENNReal.ofReal_mul (by positivity)] <;> ring

/-! ### Cross-difference transfer -/

/-- Transfer cross-difference bound through normalization with independent translations.
Uses factor 2 from translation covering. -/
lemma normalized_cross_difference_transfer
    {δ K R : ℝ} {B1 B2 B1_norm B2_norm : Set ℝ} {k j : ℝ}
    (hδ_pos : 0 < δ)
    (hB2B1_bdd : IsBounded (Set.image2 (· - ·) B2 B1))
    (hBSG : Nreal δ (Set.image2 (· - ·) B2 B1) ≤ ENNReal.ofReal K * Nreal δ B1)
    (h_retention : Nreal δ B1 ≤ ENNReal.ofReal R * Nreal δ B1_norm)
    (h_chunk1 : (fun x => x + k) '' B1_norm ⊆ B1)
    (h_chunk2 : (fun x => x + j) '' B2_norm ⊆ B2) :
    Nreal δ (Set.image2 (· - ·) B2_norm B1_norm) ≤
      (2 : ENNReal) * ENNReal.ofReal K * ENNReal.ofReal R * Nreal δ B1_norm := by
  let D := Set.image2 (· - ·) B2 B1
  let shift := k - j
  have h_sub : Set.image2 (· - ·) B2_norm B1_norm ⊆
      (fun x => x + shift) '' D := normalized_cross_diff_subset_indep h_chunk1 h_chunk2
  have h1 : Nreal δ (Set.image2 (· - ·) B2_norm B1_norm) ≤
      Nreal δ ((fun x => x + shift) '' D) := Nreal_mono h_sub
  have h2 : Nreal δ ((fun x => x + shift) '' D) ≤ 2 * Nreal δ D :=
    nreal_translate_real_le_two hδ_pos hB2B1_bdd shift
  calc
    Nreal δ (Set.image2 (· - ·) B2_norm B1_norm)
      ≤ Nreal δ ((fun x => x + shift) '' D) := h1
    _ ≤ 2 * Nreal δ D := h2
    _ ≤ 2 * (ENNReal.ofReal K * Nreal δ B1) := by
      exact mul_le_mul_of_nonneg_left hBSG (by positivity)
    _ = (2 : ENNReal) * ENNReal.ofReal K * Nreal δ B1 := by ring
    _ ≤ (2 : ENNReal) * ENNReal.ofReal K * (ENNReal.ofReal R * Nreal δ B1_norm) := by
      exact mul_le_mul_of_nonneg_left h_retention (by positivity)
    _ = (2 : ENNReal) * ENNReal.ofReal K * ENNReal.ofReal R * Nreal δ B1_norm := by ring

/-! ### Sum transfer -/

/-- Transfer sum bound through normalization with independent translations.
Uses factor 2 from translation covering. -/
lemma normalized_sum_transfer
    {δ K R : ℝ} {B1 B2 B1_norm B2_norm : Set ℝ} {k j : ℝ}
    (hδ_pos : 0 < δ)
    (hB1B2_sum_bdd : IsBounded (Set.image2 (· + ·) B1 B2))
    (hBSG : Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K * Nreal δ B1)
    (h_retention : Nreal δ B1 ≤ ENNReal.ofReal R * Nreal δ B1_norm)
    (h_chunk1 : (fun x => x + k) '' B1_norm ⊆ B1)
    (h_chunk2 : (fun x => x + j) '' B2_norm ⊆ B2) :
    Nreal δ (Set.image2 (· + ·) B1_norm B2_norm) ≤
      (2 : ENNReal) * ENNReal.ofReal K * ENNReal.ofReal R * Nreal δ B1_norm := by
  let S := Set.image2 (· + ·) B1 B2
  let shift : ℝ := -((k : ℝ) + (j : ℝ))
  have h_sub : Set.image2 (· + ·) B1_norm B2_norm ⊆ (fun x : ℝ => x + shift) '' S := by
    intro z hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    have h1 : x + (k : ℝ) ∈ B1 := h_chunk1 ⟨x, hx, rfl⟩
    have h2 : y + (j : ℝ) ∈ B2 := h_chunk2 ⟨y, hy, rfl⟩
    let w := (x + (k : ℝ)) + (y + (j : ℝ))
    have hw : w ∈ S := ⟨x + (k : ℝ), h1, y + (j : ℝ), h2, rfl⟩
    refine ⟨w, hw, ?_⟩
    simp [w, shift] <;> ring
  have h1 : Nreal δ (Set.image2 (· + ·) B1_norm B2_norm) ≤ 2 * Nreal δ S := by
    have h2 : Nreal δ (Set.image2 (· + ·) B1_norm B2_norm) ≤
        Nreal δ ((fun x : ℝ => x + shift) '' S) := Nreal_mono h_sub
    have h3 : Nreal δ ((fun x : ℝ => x + shift) '' S) ≤ 2 * Nreal δ S :=
      nreal_translate_real_le_two hδ_pos hB1B2_sum_bdd shift
    exact le_trans h2 h3
  have h_pos : 0 ≤ (2 : ENNReal) * ENNReal.ofReal K := by positivity
  calc Nreal δ (Set.image2 (· + ·) B1_norm B2_norm)
    ≤ 2 * Nreal δ S := h1
  _ ≤ 2 * (ENNReal.ofReal K * Nreal δ B1) := by gcongr
  _ = (2 : ENNReal) * ENNReal.ofReal K * Nreal δ B1 := by ring
  _ ≤ (2 : ENNReal) * ENNReal.ofReal K * (ENNReal.ofReal R * Nreal δ B1_norm) := by
      exact mul_le_mul_of_nonneg_left h_retention h_pos
  _ = (2 : ENNReal) * ENNReal.ofReal K * ENNReal.ofReal R * Nreal δ B1_norm := by ring

end ProductLikeIncidence.ProductReduction
