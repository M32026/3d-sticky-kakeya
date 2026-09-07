module

/-
# Normalization with Popularity Argument

Selects unit chunks k,j with size lower bounds and density guarantee
using a two-phase popularity argument.

Given G ⊆ S1 × S2 with |G| ≥ c_dense * |S1| * |S2|,
and unit-chunk partitions with at most M = 2R+1 chunks,
there exist chunks k,j such that:
- |B1_k| ≥ (c_dense/4) * |S1| / M
- |B2_j| ≥ (c_dense/4) * |S2| / M
- |G ∩ (B1_k × B2_j)| ≥ (c_dense/4) * |B1_k| * |B2_j|

## Proof

Phase 1: Call k "good" if |G_k| ≥ (c_dense/2) * |B1_k| * |S2|.
Bad k's contribute < (c_dense/2) * |S2| * |S1_bad|.
Good k's cover ≥ c_dense/(2-c_dense) * |S1| ≥ (c_dense/4) * |S1|.
Largest good k gives |B1_k| ≥ (c_dense/4) * |S1| / M.

Phase 2: Within selected k, call j "good" if
|G_{k,j}| ≥ (c_dense/4) * |B1_k| * |B2_j|.
Bad j's contribute < (c_dense/4) * |B1_k| * |S2|.
Good j's cover ≥ (c_dense/4) * |S2|.
Largest good j gives |B2_j| ≥ (c_dense/4) * |S2| / M.

## Whiteprint node
`normalize_chunk_grid_with_popularity`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProductLikeIncidence.RescalingRestructuring
public import MyLeanRepo.ProductLikeIncidence.SimpleNormalize
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Finset ENNReal Bornology Classical

set_option maxHeartbeats 500000

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- For a nonempty finset and a natural-valued function, there exists an element
whose value is at least the average. -/
lemma exists_max_ge_average {α : Type*} (s : Finset α) (f : α → ℕ) (hs : s.Nonempty) :
    ∃ (x : α), x ∈ s ∧ (f x : ℝ) ≥ (∑ y ∈ s, (f y : ℝ)) / (s.card : ℝ) := by
  have h_main : ∃ (x : α), x ∈ s ∧ ∀ (y : α), y ∈ s → f y ≤ f x :=
    Finset.exists_max_image s f hs
  rcases h_main with ⟨x, hx, hmax⟩
  have h1 : ∑ y ∈ s, (f y : ℝ) ≤ ∑ y ∈ s, (f x : ℝ) := by
    apply Finset.sum_le_sum
    intro y hy
    exact_mod_cast hmax y hy
  have h2 : ∑ y ∈ s, (f x : ℝ) = (s.card : ℝ) * (f x : ℝ) := by
    have h3 : ∑ y ∈ s, (f x : ℝ) = (f x : ℝ) * ∑ y ∈ s, (1 : ℝ) := by
      rw [Finset.mul_sum]
      <;> apply Finset.sum_congr rfl
      <;> intro _ _ <;> ring
    have h4 : ∑ y ∈ s, (1 : ℝ) = (s.card : ℝ) := by
      simp
    rw [h3, h4] <;> ring
  have h5 : ∑ y ∈ s, (f y : ℝ) ≤ (s.card : ℝ) * (f x : ℝ) := by
    rw [h2] at h1
    exact h1
  have h6 : (0 : ℝ) < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have h7 : (∑ y ∈ s, (f y : ℝ)) / (s.card : ℝ) ≤ (f x : ℝ) := by
    have h_div : (∑ y ∈ s, (f y : ℝ)) / (s.card : ℝ) ≤ ((s.card : ℝ) * (f x : ℝ)) / (s.card : ℝ) :=
      div_le_div_of_nonneg_right h5 (by exact_mod_cast Nat.zero_le s.card)
    have h_cancel : ((s.card : ℝ) * (f x : ℝ)) / (s.card : ℝ) = (f x : ℝ) := by
      field_simp [h6.ne'] <;> ring
    rw [h_cancel] at h_div
    exact h_div
  exact ⟨x, hx, h7⟩

/-- Phase 2 popularity argument: given total graph count ≥ (c_dense/2) * ck * N2,
select j with |B2_j| ≥ (c_dense/4) * N2 / |K| and density |G_{k,j}| ≥ (c_dense/4) * ck * |B2_j|.
Requires g j ≤ ck * b j and ck > 0. -/
lemma phase2_popularity {α : Type*} (K : Finset α) (g b : α → ℕ)
    (c_dense ck : ℝ) (N2 : ℕ)
    (hN2 : (N2 : ℝ) = ∑ j ∈ K, (b j : ℝ))
    (h_total : (∑ j ∈ K, (g j : ℝ)) ≥ (c_dense / 2) * ck * (N2 : ℝ))
    (h_g_le : ∀ j ∈ K, (g j : ℝ) ≤ ck * (b j : ℝ))
    (hck_pos : 0 < ck) (hc_dense_pos : 0 < c_dense) (hK_nonempty : K.Nonempty)
    (hN2_pos : 0 < N2) :
    ∃ (j : α), j ∈ K ∧
      (g j : ℝ) ≥ (c_dense / 4) * ck * (b j : ℝ) ∧
      (b j : ℝ) ≥ (c_dense / 4) * (N2 : ℝ) / (K.card : ℝ) := by
  let Good2 : Finset α := {j ∈ K | (g j : ℝ) ≥ (c_dense / 4) * ck * (b j : ℝ)}
  have hGood2_sub : Good2 ⊆ K := Finset.filter_subset _ _
  have h_bad : ∀ j ∈ K \ Good2, (g j : ℝ) ≤ (c_dense / 4) * ck * (b j : ℝ) := by
    intro j hj
    have hnj : j ∉ Good2 := (Finset.mem_sdiff.mp hj).2
    have hjK : j ∈ K := (Finset.mem_sdiff.mp hj).1
    have h_in : j ∈ Good2 ↔ (g j : ℝ) ≥ (c_dense / 4) * ck * (b j : ℝ) := by
      rw [Finset.mem_filter] <;> exact and_iff_right hjK
    exact le_of_lt (lt_of_not_ge (h_in.not.mp hnj))
  have h_sub : (K \ Good2) ⊆ K := by
    intro x hx
    exact (Finset.mem_sdiff.mp hx).1
  have h_sum_bad_b : ∑ j ∈ K \ Good2, (b j : ℝ) ≤ (N2 : ℝ) := by
    have h1 : ∑ j ∈ K \ Good2, (b j : ℝ) ≤ ∑ j ∈ K, (b j : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => Nat.cast_nonneg _)
    rw [hN2] at * <;> exact h1
  have h4_pos : 0 ≤ (c_dense / 4) * ck := mul_nonneg (by linarith) (by linarith)
  have h_sum_bad_g : ∑ j ∈ K \ Good2, (g j : ℝ) ≤ (c_dense / 4) * ck * (N2 : ℝ) := by
    have h2 : ∑ j ∈ K \ Good2, (g j : ℝ) ≤ ∑ j ∈ K \ Good2, ((c_dense / 4) * ck * (b j : ℝ)) :=
      Finset.sum_le_sum h_bad
    have h3 : ∑ j ∈ K \ Good2, ((c_dense / 4) * ck * (b j : ℝ)) =
        (c_dense / 4) * ck * ∑ j ∈ K \ Good2, (b j : ℝ) := by
      rw [Finset.mul_sum] <;> rfl
    calc ∑ j ∈ K \ Good2, (g j : ℝ)
      ≤ ∑ j ∈ K \ Good2, ((c_dense / 4) * ck * (b j : ℝ)) := h2
    _ = (c_dense / 4) * ck * ∑ j ∈ K \ Good2, (b j : ℝ) := h3
    _ ≤ (c_dense / 4) * ck * (N2 : ℝ) := mul_le_mul_of_nonneg_left h_sum_bad_b h4_pos
  have h_disj : Disjoint Good2 (K \ Good2) := Finset.disjoint_sdiff
  have h_union : Good2 ∪ (K \ Good2) = K := Finset.union_sdiff_of_subset hGood2_sub
  have h_sum_total : ∑ j ∈ K, (g j : ℝ) = ∑ j ∈ Good2, (g j : ℝ) + ∑ j ∈ K \ Good2, (g j : ℝ) := by
    rw [← Finset.sum_union h_disj, h_union]
  have h_good_sum : ∑ j ∈ Good2, (g j : ℝ) ≥ (c_dense / 4) * ck * (N2 : ℝ) := by
    linarith [h_total, h_sum_total, h_sum_bad_g]
  have h_good_upper : ∑ j ∈ Good2, (g j : ℝ) ≤ ck * ∑ j ∈ Good2, (b j : ℝ) := by
    have h5 : ∀ j ∈ Good2, (g j : ℝ) ≤ ck * (b j : ℝ) := by
      intro j hj
      exact h_g_le j (hGood2_sub hj)
    have h6 : ∑ j ∈ Good2, (g j : ℝ) ≤ ∑ j ∈ Good2, (ck * (b j : ℝ)) := Finset.sum_le_sum h5
    have h7 : ∑ j ∈ Good2, (ck * (b j : ℝ)) = ck * ∑ j ∈ Good2, (b j : ℝ) := by
      rw [Finset.mul_sum] <;> rfl
    rw [h7] at h6
    exact h6
  have h_S_good2 : ∑ j ∈ Good2, (b j : ℝ) ≥ (c_dense / 4) * (N2 : ℝ) := by
    have h8 : ck * ∑ j ∈ Good2, (b j : ℝ) ≥ (c_dense / 4) * ck * (N2 : ℝ) := by
      calc ck * ∑ j ∈ Good2, (b j : ℝ)
        ≥ ∑ j ∈ Good2, (g j : ℝ) := h_good_upper
      _ ≥ (c_dense / 4) * ck * (N2 : ℝ) := h_good_sum
    have h9 : 0 < ck := hck_pos
    nlinarith
  have hN2_pos' : 0 < (N2 : ℝ) := by exact_mod_cast hN2_pos
  have h_good2_nonempty : Good2.Nonempty := by
    by_contra h
    have h_empty : Good2 = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using h
    rw [h_empty] at h_S_good2
    have h_contra : (c_dense / 4) * (N2 : ℝ) ≤ 0 := h_S_good2
    have h_pos : 0 < (c_dense / 4) * (N2 : ℝ) := mul_pos (by linarith) hN2_pos'
    linarith
  have h_avg := exists_max_ge_average Good2 b h_good2_nonempty
  rcases h_avg with ⟨j, hj_Good2, h_j_size_good2⟩
  have hj_K : j ∈ K := hGood2_sub hj_Good2
  have h_j_density : (g j : ℝ) ≥ (c_dense / 4) * ck * (b j : ℝ) := (Finset.mem_filter.mp hj_Good2).2
  have h_card_le2 : (Good2.card : ℝ) ≤ (K.card : ℝ) := by
    have h : Good2.card ≤ K.card := Finset.card_le_card hGood2_sub
    exact Nat.cast_le.mpr h
  have h_S_good2_nonneg : 0 ≤ ∑ j ∈ Good2, (b j : ℝ) := by
    apply Finset.sum_nonneg
    intro _ _
    exact Nat.cast_nonneg _
  have h6 : (0 : ℝ) < (Good2.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr h_good2_nonempty
  have h7 : (∑ j ∈ Good2, (b j : ℝ)) / (K.card : ℝ) ≤ (∑ j ∈ Good2, (b j : ℝ)) / (Good2.card : ℝ) :=
    div_le_div_of_nonneg_left h_S_good2_nonneg h6 h_card_le2
  have h_j_size : (b j : ℝ) ≥ (c_dense / 4) * (N2 : ℝ) / (K.card : ℝ) := by
    calc (b j : ℝ)
      ≥ (∑ j ∈ Good2, (b j : ℝ)) / (Good2.card : ℝ) := h_j_size_good2
    _ ≥ (∑ j ∈ Good2, (b j : ℝ)) / (K.card : ℝ) := h7
    _ ≥ ((c_dense / 4) * (N2 : ℝ)) / (K.card : ℝ) := by
      gcongr
      <;> exact h_S_good2
  exact ⟨j, hj_K, h_j_density, h_j_size⟩

/-- Unit-chunk normalization with popularity argument: size lower bounds and density.

Given |G| ≥ c_dense * |S1| * |S2| with 0 < c_dense ≤ 1, selects chunks k,j
such that the normalized B1,B2,G' satisfy:
- |B1| ≥ (c_dense/4) * |S1| / M
- |B2| ≥ (c_dense/4) * |S2| / M
- |G'| ≥ (c_dense/4) * |B1| * |B2|
where M = 2R+1 is the maximum number of unit chunks. -/
lemma normalize_chunk_grid_with_popularity
    {δ R : ℝ} (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hR_pos : 0 < R) (hR_int : ∃ (c : ℤ), R = (c : ℝ))
    {S1 S2 : Set ℝ} {Gamma : Set (EuclideanSpace ℝ (Fin 2))}
    (hS1_bdd : ∀ x ∈ S1, |x| ≤ R)
    (hS2_bdd : ∀ x ∈ S2, |x| ≤ R)
    (hS1_fin : Set.Finite S1) (hS2_fin : Set.Finite S2)
    (hGamma_sub : ∀ p ∈ Gamma, p 0 ∈ S1 ∧ p 1 ∈ S2)
    (hGamma_fin : Set.Finite Gamma)
    (hS1_grid : ∀ x ∈ S1, ∃ k : ℤ, x = δ * (k : ℝ))
    (hS2_grid : ∀ x ∈ S2, ∃ k : ℤ, x = δ * (k : ℝ))
    (hS1_nonempty : S1.Nonempty) (hS2_nonempty : S2.Nonempty)
    {c_dense : ℝ} (hc_dense_pos : 0 < c_dense) (hc_dense_le_one : c_dense ≤ 1)
    (h_density : c_dense * (S1.ncard : ℝ) * (S2.ncard : ℝ) ≤ (Gamma.ncard : ℝ)) :
    ∃ (k j : ℤ) (B1 B2 : Set ℝ)
      (G' G_orig : Set (EuclideanSpace ℝ (Fin 2))),
      B1 ⊆ productLikeUnitGrid δ ∧
      B2 ⊆ productLikeUnitGrid δ ∧
      B1.Nonempty ∧ B2.Nonempty ∧
      G'.Finite ∧
      (∀ p ∈ G', ∀ i : Fin 2, ∃ m : ℤ, p i = δ * (m : ℝ)) ∧
      (∀ p ∈ G', p 0 ∈ B1 ∧ p 1 ∈ B2) ∧
      (c_dense / 4) * (B1.ncard : ℝ) * (B2.ncard : ℝ) ≤ (G'.ncard : ℝ) ∧
      (c_dense / 4) * (S1.ncard : ℝ) / (2 * R + 1) ≤ (B1.ncard : ℝ) ∧
      (c_dense / 4) * (S2.ncard : ℝ) / (2 * R + 1) ≤ (B2.ncard : ℝ) ∧
      B1 = Set.image (fun x => x - (k : ℝ)) (unitChunk S1 k) ∧
      B2 = Set.image (fun x => x - (j : ℝ)) (unitChunk S2 j) ∧
      G_orig ⊆ Gamma ∧
      (∀ p' ∈ G', ∃ g ∈ G_orig, p' 0 = g 0 - (k : ℝ) ∧ p' 1 = g 1 - (j : ℝ)) := by
  rcases hR_int with ⟨cR, hR_eq⟩
  have hcR_pos : 0 < cR := by
    have h : (cR : ℝ) > 0 := by linarith [hR_eq]
    exact_mod_cast h
  let K : Finset ℤ := Finset.Icc (-cR) cR
  let K2 : Finset (ℤ × ℤ) := K ×ˢ K
  have hK_card : (K.card : ℝ) = 2 * R + 1 := by
    have h1 : (K.card : ℤ) = 2 * cR + 1 := by
      simp [K] <;> omega
    have h2 : (K.card : ℝ) = 2 * (cR : ℝ) + 1 := by exact_mod_cast h1
    rw [h2, hR_eq] <;> ring
  have hK_card_pos : 0 < (K.card : ℝ) := by linarith [hK_card]
  have hM_pos : 0 < (2 * R + 1 : ℝ) := by linarith

  have h_chunk_in_K : ∀ (x : ℝ), |x| ≤ R → Int.floor x ∈ K := by
    intro x h_abs
    have h1 : -R ≤ x := (abs_le.mp h_abs).1
    have h2 : x ≤ R := (abs_le.mp h_abs).2
    let k : ℤ := Int.floor x
    have hk_low : -cR ≤ k := by
      have h4 : (-(cR : ℝ)) ≤ x := by rw [hR_eq] at h1; exact h1
      have h5 : ((-cR : ℤ) : ℝ) ≤ x := by exact_mod_cast h4
      exact Int.le_floor.mpr h5
    have hk_high : k ≤ cR := by
      have h4 : (k : ℝ) ≤ x := Int.floor_le x
      have h5 : x ≤ (cR : ℝ) := by rw [hR_eq] at h2; exact h2
      have h6 : (k : ℝ) ≤ (cR : ℝ) := by linarith
      exact_mod_cast h6
    simp only [K, Finset.mem_Icc]; exact ⟨hk_low, hk_high⟩

  let chunk1Fin (k : ℤ) : Finset ℝ :=
    if hk : k ∈ K then
      (hS1_fin.subset (fun {x : ℝ} (hx : x ∈ unitChunk S1 k) => hx.1)).toFinset
    else ∅
  let chunk2Fin (j : ℤ) : Finset ℝ :=
    if hj : j ∈ K then
      (hS2_fin.subset (fun {x : ℝ} (hx : x ∈ unitChunk S2 j) => hx.1)).toFinset
    else ∅
  let chunkGFin (kj : ℤ × ℤ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
    if hkj : kj ∈ K2 then
      (hGamma_fin.subset (fun {p} (hp : p ∈ chunkGraph Gamma S1 S2 kj.1 kj.2) => hp.1)).toFinset
    else ∅

  have h_chunk1Fin_mem : ∀ k ∈ K, ∀ x, x ∈ chunk1Fin k ↔ x ∈ unitChunk S1 k := by
    intro k hk x
    have h_eq : chunk1Fin k = (hS1_fin.subset (fun (x : ℝ) (hx : x ∈ unitChunk S1 k) => hx.1)).toFinset :=
      dif_pos hk
    rw [h_eq]; simp [Set.Finite.mem_toFinset]
  have h_chunk2Fin_mem : ∀ j ∈ K, ∀ x, x ∈ chunk2Fin j ↔ x ∈ unitChunk S2 j := by
    intro j hj x
    have h_eq : chunk2Fin j = (hS2_fin.subset (fun (x : ℝ) (hx : x ∈ unitChunk S2 j) => hx.1)).toFinset :=
      dif_pos hj
    rw [h_eq]; simp [Set.Finite.mem_toFinset]
  have h_chunkGFin_mem : ∀ kj ∈ K2, ∀ p, p ∈ chunkGFin kj ↔ p ∈ chunkGraph Gamma S1 S2 kj.1 kj.2 := by
    intro kj hkj p
    have h_eq : chunkGFin kj = (hGamma_fin.subset (fun (p : _) (hp : p ∈ chunkGraph Gamma S1 S2 kj.1 kj.2) => hp.1)).toFinset :=
      dif_pos hkj
    rw [h_eq]; simp [Set.Finite.mem_toFinset]

  have h_disj1 : ∀ k1 ∈ K, ∀ k2 ∈ K, k1 ≠ k2 → Disjoint (chunk1Fin k1) (chunk1Fin k2) := by
    intro k1 _ k2 _ hne
    simp only [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 : x ∈ unitChunk S1 k1 := (h_chunk1Fin_mem k1 ‹_› x).mp hx1
    have h2 : x ∈ unitChunk S1 k2 := (h_chunk1Fin_mem k2 ‹_› x).mp hx2
    have h11 : (k1 : ℝ) ≤ x := h1.2.1
    have h12 : x < (k1 : ℝ) + 1 := h1.2.2
    have h21 : (k2 : ℝ) ≤ x := h2.2.1
    have h22 : x < (k2 : ℝ) + 1 := h2.2.2
    by_cases h : k1 < k2
    · have h3 : (k2 : ℝ) < (k1 : ℝ) + 1 := by linarith
      have h4 : k2 < k1 + 1 := by exact_mod_cast h3
      have h5 : k2 ≤ k1 := by omega
      omega
    · have h' : k2 < k1 := by omega
      have h3 : (k1 : ℝ) < (k2 : ℝ) + 1 := by linarith
      have h4 : k1 < k2 + 1 := by exact_mod_cast h3
      have h5 : k1 ≤ k2 := by omega
      omega
  have h_disj2 : ∀ j1 ∈ K, ∀ j2 ∈ K, j1 ≠ j2 → Disjoint (chunk2Fin j1) (chunk2Fin j2) := by
    intro j1 _ j2 _ hne
    simp only [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 : x ∈ unitChunk S2 j1 := (h_chunk2Fin_mem j1 ‹_› x).mp hx1
    have h2 : x ∈ unitChunk S2 j2 := (h_chunk2Fin_mem j2 ‹_› x).mp hx2
    have h11 : (j1 : ℝ) ≤ x := h1.2.1
    have h12 : x < (j1 : ℝ) + 1 := h1.2.2
    have h21 : (j2 : ℝ) ≤ x := h2.2.1
    have h22 : x < (j2 : ℝ) + 1 := h2.2.2
    by_cases h : j1 < j2
    · have h3 : (j2 : ℝ) < (j1 : ℝ) + 1 := by linarith
      have h4 : j2 < j1 + 1 := by exact_mod_cast h3
      have h5 : j2 ≤ j1 := by omega
      omega
    · have h' : j2 < j1 := by omega
      have h3 : (j1 : ℝ) < (j2 : ℝ) + 1 := by linarith
      have h4 : j1 < j2 + 1 := by exact_mod_cast h3
      have h5 : j1 ≤ j2 := by omega
      omega

  have h_union1 : K.biUnion chunk1Fin = hS1_fin.toFinset := by
    ext x
    simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨k, hk, hx⟩
      have h : x ∈ unitChunk S1 k := (h_chunk1Fin_mem k hk x).mp hx
      exact h.1
    · intro hx
      have h_abs : |x| ≤ R := hS1_bdd x hx
      let k := Int.floor x
      have hkK : k ∈ K := h_chunk_in_K x h_abs
      have h_x_chunk : x ∈ unitChunk S1 k := by
        exact ⟨hx, Int.floor_le x, Int.lt_floor_add_one x⟩
      have h_x_fin : x ∈ chunk1Fin k := (h_chunk1Fin_mem k hkK x).mpr h_x_chunk
      exact ⟨k, hkK, h_x_fin⟩
  have h_union2 : K.biUnion chunk2Fin = hS2_fin.toFinset := by
    ext x
    simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨j, hj, hx⟩
      have h : x ∈ unitChunk S2 j := (h_chunk2Fin_mem j hj x).mp hx
      exact h.1
    · intro hx
      have h_abs : |x| ≤ R := hS2_bdd x hx
      let j := Int.floor x
      have hjK : j ∈ K := h_chunk_in_K x h_abs
      have h_x_chunk : x ∈ unitChunk S2 j := by
        exact ⟨hx, Int.floor_le x, Int.lt_floor_add_one x⟩
      have h_x_fin : x ∈ chunk2Fin j := (h_chunk2Fin_mem j hjK x).mpr h_x_chunk
      exact ⟨j, hjK, h_x_fin⟩

  have h_unionG : K2.biUnion chunkGFin = hGamma_fin.toFinset := by
    ext p
    simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨kj, hkj, hp⟩
      have h : p ∈ chunkGraph Gamma S1 S2 kj.1 kj.2 := (h_chunkGFin_mem kj hkj p).mp hp
      exact h.1
    · intro hp
      have h1 : p 0 ∈ S1 := (hGamma_sub p hp).1
      have h2 : p 1 ∈ S2 := (hGamma_sub p hp).2
      have h_abs1 : |p 0| ≤ R := hS1_bdd (p 0) h1
      have h_abs2 : |p 1| ≤ R := hS2_bdd (p 1) h2
      let k := Int.floor (p 0)
      let j := Int.floor (p 1)
      have hkK : k ∈ K := h_chunk_in_K (p 0) h_abs1
      have hjK : j ∈ K := h_chunk_in_K (p 1) h_abs2
      have hkj : (k, j) ∈ K2 := Finset.mem_product.mpr ⟨hkK, hjK⟩
      have h_p_chunk : p ∈ chunkGraph Gamma S1 S2 k j := by
        exact ⟨hp, ⟨h1, Int.floor_le (p 0), Int.lt_floor_add_one (p 0)⟩,
          ⟨h2, Int.floor_le (p 1), Int.lt_floor_add_one (p 1)⟩⟩
      have h_p_fin : p ∈ chunkGFin (k, j) := (h_chunkGFin_mem (k, j) hkj p).mpr h_p_chunk
      exact ⟨(k, j), hkj, h_p_fin⟩

  let N1 : ℕ := hS1_fin.toFinset.card
  let N2 : ℕ := hS2_fin.toFinset.card
  let NG : ℕ := hGamma_fin.toFinset.card
  have hN1_pos : 0 < N1 := by
    rcases hS1_nonempty with ⟨x, hx⟩
    have h : x ∈ hS1_fin.toFinset := by simpa using hx
    exact Finset.card_pos.mpr ⟨x, h⟩
  have hN2_pos : 0 < N2 := by
    rcases hS2_nonempty with ⟨x, hx⟩
    have h : x ∈ hS2_fin.toFinset := by simpa using hx
    exact Finset.card_pos.mpr ⟨x, h⟩

  have h_card1 : N1 = ∑ k ∈ K, (chunk1Fin k).card := by
    have h : K.biUnion chunk1Fin = hS1_fin.toFinset := h_union1
    rw [← Finset.card_biUnion h_disj1, h] <;> rfl
  have h_card2 : N2 = ∑ j ∈ K, (chunk2Fin j).card := by
    have h : K.biUnion chunk2Fin = hS2_fin.toFinset := h_union2
    rw [← Finset.card_biUnion h_disj2, h] <;> rfl
  have h_cardG : NG = ∑ kj ∈ K2, (chunkGFin kj).card := by
    have h_disjG : ∀ kj1 ∈ K2, ∀ kj2 ∈ K2, kj1 ≠ kj2 → Disjoint (chunkGFin kj1) (chunkGFin kj2) := by
      intro kj1 _ kj2 _ hne
      simp only [Finset.disjoint_left]
      intro p hp1 hp2
      have h1 : p ∈ chunkGraph Gamma S1 S2 kj1.1 kj1.2 := (h_chunkGFin_mem kj1 ‹_› p).mp hp1
      have h2 : p ∈ chunkGraph Gamma S1 S2 kj2.1 kj2.2 := (h_chunkGFin_mem kj2 ‹_› p).mp hp2
      have h11 : (kj1.1 : ℝ) ≤ p 0 := h1.2.1.2.1
      have h12 : p 0 < (kj1.1 : ℝ) + 1 := h1.2.1.2.2
      have h21 : (kj2.1 : ℝ) ≤ p 0 := h2.2.1.2.1
      have h22 : p 0 < (kj2.1 : ℝ) + 1 := h2.2.1.2.2
      have h3 : kj1.1 = kj2.1 := by
        by_cases h : kj1.1 < kj2.1
        · have h5 : (kj2.1 : ℝ) < (kj1.1 : ℝ) + 1 := by linarith
          have h6 : kj2.1 < kj1.1 + 1 := by exact_mod_cast h5
          omega
        · by_cases h' : kj2.1 < kj1.1
          · have h5 : (kj1.1 : ℝ) < (kj2.1 : ℝ) + 1 := by linarith
            have h6 : kj1.1 < kj2.1 + 1 := by exact_mod_cast h5
            omega
          · omega
      have h13 : (kj1.2 : ℝ) ≤ p 1 := h1.2.2.2.1
      have h14 : p 1 < (kj1.2 : ℝ) + 1 := h1.2.2.2.2
      have h23 : (kj2.2 : ℝ) ≤ p 1 := h2.2.2.2.1
      have h24 : p 1 < (kj2.2 : ℝ) + 1 := h2.2.2.2.2
      have h4 : kj1.2 = kj2.2 := by
        by_cases h : kj1.2 < kj2.2
        · have h5 : (kj2.2 : ℝ) < (kj1.2 : ℝ) + 1 := by linarith
          have h6 : kj2.2 < kj1.2 + 1 := by exact_mod_cast h5
          omega
        · by_cases h' : kj2.2 < kj1.2
          · have h5 : (kj1.2 : ℝ) < (kj2.2 : ℝ) + 1 := by linarith
            have h6 : kj1.2 < kj2.2 + 1 := by exact_mod_cast h5
            omega
          · omega
      exact hne (Prod.ext h3 h4)
    have h : K2.biUnion chunkGFin = hGamma_fin.toFinset := h_unionG
    rw [← Finset.card_biUnion h_disjG, h] <;> rfl

  have h_density_real : c_dense * (N1 : ℝ) * (N2 : ℝ) ≤ (NG : ℝ) := by
    have h1 : (S1.ncard : ℝ) = (N1 : ℝ) := by
      simp [Set.ncard_eq_toFinset_card S1 hS1_fin] <;> rfl
    have h2 : (S2.ncard : ℝ) = (N2 : ℝ) := by
      simp [Set.ncard_eq_toFinset_card S2 hS2_fin] <;> rfl
    have h3 : (Gamma.ncard : ℝ) = (NG : ℝ) := by
      simp [Set.ncard_eq_toFinset_card Gamma hGamma_fin] <;> rfl
    rw [h1, h2, h3] at h_density
    exact h_density

  -- For each k, total graph points with first coordinate in chunk k
  let gk (k : ℤ) : ℕ := ∑ j ∈ K, (chunkGFin (k, j)).card
  have h_gk_def : ∀ k ∈ K, (gk k : ℝ) = ∑ j ∈ K, ((chunkGFin (k, j)).card : ℝ) := by
    intro k _; simp [gk]

  -- Phase 1: Good k
  let Good1 : Finset ℤ := {k ∈ K | (gk k : ℝ) ≥ (c_dense / 2) * ((chunk1Fin k).card : ℝ) * (N2 : ℝ)}
  have hGood1_sub : Good1 ⊆ K := Finset.filter_subset _ _

  -- Sum over bad k ≤ (c_dense/2) * N2 * sum_bad |chunk1Fin k|
  have h_bad1_sum : ∑ k ∈ (K \ Good1), (gk k : ℝ) ≤
      (c_dense / 2) * (N2 : ℝ) * ∑ k ∈ (K \ Good1), ((chunk1Fin k).card : ℝ) := by
    have h : ∀ k ∈ (K \ Good1), (gk k : ℝ) < (c_dense / 2) * ((chunk1Fin k).card : ℝ) * (N2 : ℝ) := by
      intro k hk
      have hnk : k ∉ Good1 := (Finset.mem_sdiff.mp hk).2
      have hkK : k ∈ K := (Finset.mem_sdiff.mp hk).1
      have h' : ¬ ((gk k : ℝ) ≥ (c_dense / 2) * ((chunk1Fin k).card : ℝ) * (N2 : ℝ)) := by
        simpa [Good1, Finset.mem_filter, hkK] using hnk
      exact lt_of_not_ge h'
    by_cases hne : (K \ Good1).Nonempty
    · have h_strict := Finset.sum_lt_sum_of_nonempty hne h
      have h4 : ∀ k ∈ (K \ Good1), (c_dense / 2) * ((chunk1Fin k).card : ℝ) * (N2 : ℝ) =
          ((c_dense / 2) * (N2 : ℝ)) * ((chunk1Fin k).card : ℝ) := by
        intro k _; ring
      have h_rhs : ∑ k ∈ (K \ Good1), ((c_dense / 2) * ((chunk1Fin k).card : ℝ) * (N2 : ℝ)) =
          (c_dense / 2) * (N2 : ℝ) * ∑ k ∈ (K \ Good1), ((chunk1Fin k).card : ℝ) := by
        have h5 : ∑ k ∈ (K \ Good1), (((c_dense / 2) * (N2 : ℝ)) * ((chunk1Fin k).card : ℝ)) =
            ((c_dense / 2) * (N2 : ℝ)) * ∑ k ∈ (K \ Good1), ((chunk1Fin k).card : ℝ) := by
          rw [Finset.mul_sum]
        have h6 : ∑ k ∈ (K \ Good1), ((c_dense / 2) * ((chunk1Fin k).card : ℝ) * (N2 : ℝ)) =
            ∑ k ∈ (K \ Good1), (((c_dense / 2) * (N2 : ℝ)) * ((chunk1Fin k).card : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k _; ring
        rw [h6, h5] <;> ring
      rw [h_rhs] at h_strict
      exact le_of_lt h_strict
    · have h_empty : K \ Good1 = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using hne
      rw [h_empty]
      <;> simp

  -- Total gk over all k = NG
  have h_total_gk : ∑ k ∈ K, (gk k : ℝ) = (NG : ℝ) := by
    have h1 : ∑ k ∈ K, (gk k : ℝ) = ∑ k ∈ K, ∑ j ∈ K, ((chunkGFin (k, j)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact h_gk_def k hk
    have h2 : ∑ k ∈ K, ∑ j ∈ K, ((chunkGFin (k, j)).card : ℝ) =
        ∑ kj ∈ K2, ((chunkGFin kj).card : ℝ) := by
      have h3 : ∑ k ∈ K, ∑ j ∈ K, ((chunkGFin (k, j)).card : ℝ) =
          ∑ kj ∈ K2, ((chunkGFin (kj.1, kj.2)).card : ℝ) := by
        rw [Finset.sum_product]
      rw [h3]
      <;> simp
    rw [h1, h2]
    exact_mod_cast h_cardG.symm

  -- Good k sum ≥ (c_dense/2) * N1 * N2 + (c_dense/2) * N2 * S_good
  let S_good : ℝ := ∑ k ∈ Good1, ((chunk1Fin k).card : ℝ)
  let S_bad : ℝ := ∑ k ∈ (K \ Good1), ((chunk1Fin k).card : ℝ)
  have h_sum_chunk : (N1 : ℝ) = S_good + S_bad := by
    have h : ∑ k ∈ K, ((chunk1Fin k).card : ℝ) = S_good + S_bad := by
      rw [← Finset.sum_union (show Disjoint Good1 (K \ Good1) from Finset.disjoint_sdiff)]
      <;> rw [Finset.union_sdiff_of_subset hGood1_sub] <;> ring
    have h4 : (N1 : ℝ) = ∑ k ∈ K, ((chunk1Fin k).card : ℝ) := by exact_mod_cast h_card1
    linarith
  have h_bad1_le : ∑ k ∈ (K \ Good1), (gk k : ℝ) ≤
      (c_dense / 2) * (N2 : ℝ) * S_bad := by
    have h_eq : S_bad = ∑ k ∈ (K \ Good1), ((chunk1Fin k).card : ℝ) := by rfl
    rw [h_eq]
    exact h_bad1_sum
  have h_good_sum_lower : ∑ k ∈ Good1, (gk k : ℝ) ≥
      (c_dense / 2) * (N1 : ℝ) * (N2 : ℝ) + (c_dense / 2) * (N2 : ℝ) * S_good := by
    have h_sum_K : ∑ k ∈ K, (gk k : ℝ) = ∑ k ∈ Good1, (gk k : ℝ) + ∑ k ∈ (K \ Good1), (gk k : ℝ) := by
      rw [← Finset.sum_union (show Disjoint Good1 (K \ Good1) from Finset.disjoint_sdiff)]
      <;> rw [Finset.union_sdiff_of_subset hGood1_sub] <;> ring
    have h1 : ∑ k ∈ Good1, (gk k : ℝ) = (NG : ℝ) - ∑ k ∈ (K \ Good1), (gk k : ℝ) := by
      linarith [h_total_gk, h_sum_K]
    rw [h1]
    have h2 : (NG : ℝ) ≥ c_dense * (N1 : ℝ) * (N2 : ℝ) := h_density_real
    have h3 : S_bad = (N1 : ℝ) - S_good := by linarith [h_sum_chunk]
    rw [h3] at h_bad1_le
    linarith

  -- Upper bound: good sum ≤ N2 * S_good
  have h_good_sum_upper : ∑ k ∈ Good1, (gk k : ℝ) ≤ (N2 : ℝ) * S_good := by
    have h1 : ∀ k ∈ Good1, (gk k : ℝ) ≤ (N2 : ℝ) * ((chunk1Fin k).card : ℝ) := by
      intro k hk
      have hkK : k ∈ K := hGood1_sub hk
      have h2 : (gk k : ℝ) = ∑ j ∈ K, ((chunkGFin (k, j)).card : ℝ) := h_gk_def k hkK
      rw [h2]
      have h3 : ∑ j ∈ K, ((chunkGFin (k, j)).card : ℝ) ≤ ∑ j ∈ K, ((chunk1Fin k).card : ℝ) * ((chunk2Fin j).card : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hkj : (k, j) ∈ K2 := Finset.mem_product.mpr ⟨hkK, hj⟩
        have h4 : (chunkGFin (k, j)).card ≤ (chunk1Fin k).card * (chunk2Fin j).card := by
          have h5 : ∀ p ∈ chunkGFin (k, j), p 0 ∈ chunk1Fin k ∧ p 1 ∈ chunk2Fin j := by
            intro p hp
            have h6 : p ∈ chunkGraph Gamma S1 S2 k j := (h_chunkGFin_mem (k, j) hkj p).mp hp
            exact ⟨(h_chunk1Fin_mem k hkK (p 0)).mpr h6.2.1, (h_chunk2Fin_mem j hj (p 1)).mpr h6.2.2⟩
          let f : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ := fun p => (p 0, p 1)
          have h_inj : Set.InjOn f (chunkGFin (k, j) : Set (EuclideanSpace ℝ (Fin 2))) := by
            intro p _ q _ h
            have h_eq : (p 0, p 1) = (q 0, q 1) := h
            have h0 : p 0 = q 0 := by simp [Prod.ext_iff] at h_eq <;> tauto
            have h1 : p 1 = q 1 := by simp [Prod.ext_iff] at h_eq <;> tauto
            ext i
            fin_cases i <;> tauto
          let img : Finset (ℝ × ℝ) := (chunkGFin (k, j)).image f
          have h_sub : img ⊆ chunk1Fin k ×ˢ chunk2Fin j := by
            intro z hz
            rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
            exact Finset.mem_product.mpr (h5 p hp)
          have h_card_img : img.card = (chunkGFin (k, j)).card := by
            exact Finset.card_image_iff.mpr h_inj
          rw [← h_card_img]
          have h6 : img.card ≤ (chunk1Fin k ×ˢ chunk2Fin j).card := Finset.card_le_card h_sub
          rw [Finset.card_product] at h6
          exact h6
        exact_mod_cast h4
      have h4 : ∑ j ∈ K, (((chunk1Fin k).card : ℝ) * ((chunk2Fin j).card : ℝ)) =
          ((chunk1Fin k).card : ℝ) * ∑ j ∈ K, ((chunk2Fin j).card : ℝ) := by
        rw [Finset.mul_sum]
      rw [h4] at h3
      have h5 : ∑ j ∈ K, ((chunk2Fin j).card : ℝ) = (N2 : ℝ) := by
        exact_mod_cast h_card2.symm
      rw [h5] at h3
      linarith
    calc ∑ k ∈ Good1, (gk k : ℝ)
      ≤ ∑ k ∈ Good1, ((N2 : ℝ) * ((chunk1Fin k).card : ℝ)) := Finset.sum_le_sum h1
    _ = (N2 : ℝ) * S_good := by rw [Finset.mul_sum] <;> rfl

  -- S_good ≥ c_dense/(2-c_dense) * N1 ≥ (c_dense/4) * N1
  have h_c_dense_lt_two : c_dense < 2 := by linarith
  have h_S_good_lower : S_good ≥ (c_dense / 4) * (N1 : ℝ) := by
    have h1 : (N2 : ℝ) * S_good ≥ (c_dense / 2) * (N1 : ℝ) * (N2 : ℝ) + (c_dense / 2) * (N2 : ℝ) * S_good := by
      linarith [h_good_sum_upper, h_good_sum_lower]
    have hN2_pos' : (0 : ℝ) < (N2 : ℝ) := by exact_mod_cast hN2_pos
    have h2 : S_good ≥ (c_dense / (2 - c_dense)) * (N1 : ℝ) := by
      have h3 : (2 - c_dense : ℝ) > 0 := by linarith
      have h4 : (N2 : ℝ) * S_good * (2 - c_dense) ≥ c_dense * (N1 : ℝ) * (N2 : ℝ) := by
        have h41 : (N2 : ℝ) * S_good - (c_dense / 2) * (N2 : ℝ) * S_good ≥
            (c_dense / 2) * (N1 : ℝ) * (N2 : ℝ) := by linarith [h1]
        have h42 : (N2 : ℝ) * S_good * (2 - c_dense) =
            2 * ((N2 : ℝ) * S_good - (c_dense / 2) * (N2 : ℝ) * S_good) := by ring
        have h43 : c_dense * (N1 : ℝ) * (N2 : ℝ) =
            2 * ((c_dense / 2) * (N1 : ℝ) * (N2 : ℝ)) := by ring
        rw [h42, h43]
        gcongr
        <;> linarith
      have h5 : S_good * (2 - c_dense) ≥ c_dense * (N1 : ℝ) := by
        have h51 : (N2 : ℝ) * (S_good * (2 - c_dense)) ≥ (N2 : ℝ) * (c_dense * (N1 : ℝ)) := by linarith
        nlinarith [hN2_pos']
      have h6 : S_good ≥ (c_dense / (2 - c_dense)) * (N1 : ℝ) := by
        calc S_good
          = (S_good * (2 - c_dense)) / (2 - c_dense) := by field_simp [h3.ne'] <;> ring
        _ ≥ (c_dense * (N1 : ℝ)) / (2 - c_dense) := by gcongr
        _ = (c_dense / (2 - c_dense)) * (N1 : ℝ) := by ring
      exact h6
    have h4 : (c_dense / (2 - c_dense)) * (N1 : ℝ) ≥ (c_dense / 4) * (N1 : ℝ) := by
      have h5 : 0 ≤ (N1 : ℝ) := by positivity
      have h7 : 0 ≤ c_dense := by linarith
      have h8 : (2 - c_dense : ℝ) ≤ 4 := by linarith
      have h10 : c_dense / (2 - c_dense) ≥ c_dense / 4 :=
        div_le_div_of_nonneg_left h7 (by linarith) h8
      exact mul_le_mul_of_nonneg_right h10 h5
    exact le_trans h4 h2
  have h_S_good_pos : 0 < S_good := by
    have hN1_pos' : (0 : ℝ) < (N1 : ℝ) := by exact_mod_cast hN1_pos
    have h_cd4_pos : 0 < c_dense / 4 := by positivity
    have h : 0 < (c_dense / 4) * (N1 : ℝ) := mul_pos h_cd4_pos hN1_pos'
    exact lt_of_lt_of_le h h_S_good_lower

  -- Pick good k with MAX CARDINALITY using average argument
  have h_exists_good1 : Good1.Nonempty := by
    by_contra h
    have h_empty : Good1 = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using h
    have h_S_good_zero : S_good = 0 := by
      have h_sum : ∑ k ∈ Good1, ((chunk1Fin k).card : ℝ) = 0 := by
        rw [h_empty]
        exact Finset.sum_empty
      exact h_sum
    rw [h_S_good_zero] at h_S_good_pos
    <;> linarith
  have h_avg1 := exists_max_ge_average Good1 (fun k : ℤ => (chunk1Fin k).card) h_exists_good1
  rcases h_avg1 with ⟨k, hk_Good1, h_k_size_lower_good1⟩
  have hk_K : k ∈ K := hGood1_sub hk_Good1
  have h_card_le : (Good1.card : ℝ) ≤ (K.card : ℝ) := by
    have h : Good1.card ≤ K.card := Finset.card_le_card hGood1_sub
    exact Nat.cast_le.mpr h
  have h_S_good_nonneg : 0 ≤ S_good := by
    apply Finset.sum_nonneg
    intro _ _
    exact Nat.cast_nonneg _
  have h_k_size_lower : ((chunk1Fin k).card : ℝ) ≥ S_good / (K.card : ℝ) := by
    have h6 : (0 : ℝ) < (Good1.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr h_exists_good1
    have h7 : S_good / (K.card : ℝ) ≤ S_good / (Good1.card : ℝ) :=
      div_le_div_of_nonneg_left h_S_good_nonneg h6 h_card_le
    exact le_trans h7 h_k_size_lower_good1
  have h_k_size : ((chunk1Fin k).card : ℝ) ≥ (c_dense / 4) * (N1 : ℝ) / (K.card : ℝ) := by
    calc ((chunk1Fin k).card : ℝ)
      ≥ S_good / (K.card : ℝ) := h_k_size_lower
    _ ≥ ((c_dense / 4) * (N1 : ℝ)) / (K.card : ℝ) := by
      exact div_le_div_of_nonneg_right h_S_good_lower (le_of_lt hK_card_pos)
  have h_k_good : (gk k : ℝ) ≥ (c_dense / 2) * ((chunk1Fin k).card : ℝ) * (N2 : ℝ) :=
    (Finset.mem_filter.mp hk_Good1).2

  -- Phase 2: Use standalone popularity lemma to select j
  set ck : ℝ := ((chunk1Fin k).card : ℝ) with hck_def
  have hck_pos : 0 < ck := by
    rw [hck_def]
    have h : ((chunk1Fin k).card : ℝ) ≥ (c_dense / 4) * (N1 : ℝ) / (K.card : ℝ) := h_k_size
    have h_pos : 0 < (c_dense / 4) * (N1 : ℝ) / (K.card : ℝ) := by
      apply div_pos
      · exact mul_pos (by linarith) (by exact_mod_cast hN1_pos)
      · exact hK_card_pos
    linarith
  have h_g_le : ∀ j ∈ K, ((chunkGFin (k, j)).card : ℝ) ≤ ck * ((chunk2Fin j).card : ℝ) := by
    intro j hj
    rw [hck_def]
    let f : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ := fun p => (p 0, p 1)
    have h_inj : Set.InjOn f (chunkGFin (k, j) : Set (EuclideanSpace ℝ (Fin 2))) := by
      intro p _ q _ h
      have h0 : p 0 = q 0 := by simp [Prod.ext_iff] at h <;> tauto
      have h1 : p 1 = q 1 := by simp [Prod.ext_iff] at h <;> tauto
      ext i
      fin_cases i <;> tauto
    let img : Finset (ℝ × ℝ) := (chunkGFin (k, j)).image f
    have h4 : ∀ p ∈ chunkGFin (k, j), p 0 ∈ chunk1Fin k ∧ p 1 ∈ chunk2Fin j := by
      intro p hp
      have hkj : (k, j) ∈ K2 := Finset.mem_product.mpr ⟨hk_K, hj⟩
      have h5 : p ∈ chunkGraph Gamma S1 S2 k j := (h_chunkGFin_mem (k, j) hkj p).mp hp
      exact ⟨(h_chunk1Fin_mem k hk_K (p 0)).mpr h5.2.1, (h_chunk2Fin_mem j hj (p 1)).mpr h5.2.2⟩
    have h_sub : img ⊆ chunk1Fin k ×ˢ chunk2Fin j := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
      exact Finset.mem_product.mpr (h4 p hp)
    have h_card_img : img.card = (chunkGFin (k, j)).card := Finset.card_image_iff.mpr h_inj
    rw [← h_card_img]
    have h6 : img.card ≤ (chunk1Fin k ×ˢ chunk2Fin j).card := Finset.card_le_card h_sub
    rw [Finset.card_product] at h6
    exact_mod_cast h6
  have h_total2 : (∑ j ∈ K, ((chunkGFin (k, j)).card : ℝ)) ≥ (c_dense / 2) * ck * (N2 : ℝ) := by
    rw [hck_def]
    have h1 : (∑ j ∈ K, ((chunkGFin (k, j)).card : ℝ)) = (gk k : ℝ) := (h_gk_def k hk_K).symm
    rw [h1]
    exact h_k_good
  have hK_nonempty : K.Nonempty := by
    have h : 0 < K.card := by exact_mod_cast hK_card_pos
    exact Finset.card_pos.mp h
  have h_phase2 := phase2_popularity K (fun j => (chunkGFin (k, j)).card) (fun j => (chunk2Fin j).card)
    c_dense ck N2 (by exact_mod_cast h_card2) h_total2 h_g_le hck_pos hc_dense_pos hK_nonempty hN2_pos
  rcases h_phase2 with ⟨j, hj_K, h_j_density, h_j_size⟩

  -- Translate
  let B1 : Set ℝ := Set.image (fun x => x - (k : ℝ)) (unitChunk S1 k)
  let B2 : Set ℝ := Set.image (fun x => x - (j : ℝ)) (unitChunk S2 j)
  let G_orig : Set (EuclideanSpace ℝ (Fin 2)) :=
    chunkGraph Gamma S1 S2 k j
  let G' : Set (EuclideanSpace ℝ (Fin 2)) :=
    translateGraph2D k j G_orig

  -- Cardinalities
  have hB1_ncard : B1.ncard = (chunk1Fin k).card := by
    have h_fin : Set.Finite (unitChunk S1 k) := hS1_fin.subset (fun x hx => hx.1)
    have h_inj : Set.InjOn (fun x : ℝ => x - (k : ℝ)) (unitChunk S1 k) := by
      intro x _ y _ h; simpa using h
    have h : B1.ncard = (unitChunk S1 k).ncard := by
      rw [h_inj.ncard_image]
    rw [h]
    have h2 : (unitChunk S1 k).ncard = (chunk1Fin k).card := by
      have h_eq1 : (unitChunk S1 k).ncard = h_fin.toFinset.card := by exact ncard_eq_toFinset_card (unitChunk S1 k) h_fin
      rw [h_eq1]
      have h_eq2 : chunk1Fin k = h_fin.toFinset := by simp [chunk1Fin, hk_K]
      rw [h_eq2]
    exact h2
  have hB2_ncard : B2.ncard = (chunk2Fin j).card := by
    have h_fin : Set.Finite (unitChunk S2 j) := hS2_fin.subset (fun x hx => hx.1)
    have h_inj : Set.InjOn (fun x : ℝ => x - (j : ℝ)) (unitChunk S2 j) := by
      intro x _ y _ h; simpa using h
    have h : B2.ncard = (unitChunk S2 j).ncard := by
      rw [h_inj.ncard_image]
    rw [h]
    have h2 : (unitChunk S2 j).ncard = (chunk2Fin j).card := by
      have h_eq1 : (unitChunk S2 j).ncard = h_fin.toFinset.card := by exact ncard_eq_toFinset_card (unitChunk S2 j) h_fin
      rw [h_eq1]
      have h_eq2 : chunk2Fin j = h_fin.toFinset := by simp [chunk2Fin, hj_K]
      rw [h_eq2]
    exact h2
  have hG'_ncard : G'.ncard = (chunkGFin (k, j)).card := by
    let f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun p => (WithLp.equiv 2 (Fin 2 → ℝ)).symm
        (fun i : Fin 2 => if i = 0 then p 0 - (k : ℝ) else p 1 - (j : ℝ))
    have hG'_def : G' = Set.image f (chunkGraph Gamma S1 S2 k j) := by rfl
    have h_inj : Function.Injective f := by
      intro p q h
      have h0 : (f p) 0 = (f q) 0 := by rw [h]
      have h1 : (f p) 1 = (f q) 1 := by rw [h]
      have h0' : p 0 = q 0 := by simpa [f] using h0
      have h1' : p 1 = q 1 := by simpa [f] using h1
      ext i
      fin_cases i <;> tauto
    have h_inj_on : Set.InjOn f (chunkGraph Gamma S1 S2 k j) := fun x _ y _ hxy => h_inj hxy
    have h_ncard_img : (Set.image f (chunkGraph Gamma S1 S2 k j)).ncard = (chunkGraph Gamma S1 S2 k j).ncard :=
      h_inj_on.ncard_image
    have h_fin : Set.Finite (chunkGraph Gamma S1 S2 k j) := hGamma_fin.subset (fun p hp => hp.1)
    have hkj : (k, j) ∈ K2 := Finset.mem_product.mpr ⟨hk_K, hj_K⟩
    have h_eq2 : chunkGFin (k, j) = h_fin.toFinset := by
      unfold chunkGFin
      rw [dif_pos hkj]
    have h_ncard_eq : (chunkGraph Gamma S1 S2 k j).ncard = (chunkGFin (k, j)).card := by
      have h1 : (chunkGraph Gamma S1 S2 k j).ncard = h_fin.toFinset.card := by exact ncard_eq_toFinset_card (chunkGraph Gamma S1 S2 k j) h_fin
      rw [h1, h_eq2]
    rw [hG'_def, h_ncard_img, h_ncard_eq]

  -- B1, B2 ⊆ [0,1] and grid
  have hB1_sub_Icc : B1 ⊆ Set.Icc (0 : ℝ) 1 := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h1 : (k : ℝ) ≤ x := hx.2.1
    have h2 : x < (k : ℝ) + 1 := hx.2.2
    constructor <;> linarith
  have hB2_sub_Icc : B2 ⊆ Set.Icc (0 : ℝ) 1 := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h1 : (j : ℝ) ≤ x := hx.2.1
    have h2 : x < (j : ℝ) + 1 := hx.2.2
    constructor <;> linarith
  have hB1_grid : B1 ⊆ productLikeIntegerGrid δ :=
    int_translate_preserves_grid1d hδ_dyadic k (fun x hx => hS1_grid x hx.1)
  have hB2_grid : B2 ⊆ productLikeIntegerGrid δ :=
    int_translate_preserves_grid1d hδ_dyadic j (fun x hx => hS2_grid x hx.1)
  have hB1_unit : B1 ⊆ productLikeUnitGrid δ :=
    fun x hx => ⟨hB1_grid hx, hB1_sub_Icc hx⟩
  have hB2_unit : B2 ⊆ productLikeUnitGrid δ :=
    fun x hx => ⟨hB2_grid hx, hB2_sub_Icc hx⟩

  -- G' finite and grid
  have hG'_finite : G'.Finite :=
    (hGamma_fin.subset (fun p hp => hp.1)).image _
  have hG'_grid : ∀ p ∈ G', ∀ i : Fin 2, ∃ m : ℤ, p i = δ * (m : ℝ) :=
    int_translate_preserves_grid2d hδ_dyadic k j
      (fun p hp i =>
        have hsub : p 0 ∈ S1 ∧ p 1 ∈ S2 := hGamma_sub p hp.1
        by fin_cases i <;> simp [hsub] <;> tauto)

  -- G' subset
  have hG'_sub : ∀ p ∈ G', p 0 ∈ B1 ∧ p 1 ∈ B2 := by
    intro p hp
    rcases hp with ⟨q, hq, rfl⟩
    have hq0 : q 0 ∈ unitChunk S1 k := hq.2.1
    have hq1 : q 1 ∈ unitChunk S2 j := hq.2.2
    constructor
    · exact ⟨q 0, hq0, by simp [translateGraph2D]⟩
    · exact ⟨q 1, hq1, by simp [translateGraph2D]⟩

  -- Nonempty
  have hkj : (k, j) ∈ K2 := Finset.mem_product.mpr ⟨hk_K, hj_K⟩
  have h_bj_pos : 0 < ((chunk2Fin j).card : ℝ) := by
    have h_pos2 : 0 < (c_dense / 4) * (N2 : ℝ) / (K.card : ℝ) := by
      apply div_pos
      · exact mul_pos (by linarith) (by exact_mod_cast hN2_pos)
      · exact hK_card_pos
    linarith [h_j_size]
  have h_gkj_pos : 0 < ((chunkGFin (k, j)).card : ℝ) := by
    have h : ((chunkGFin (k, j)).card : ℝ) ≥ (c_dense / 4) * ck * ((chunk2Fin j).card : ℝ) := h_j_density
    have h_pos : 0 < (c_dense / 4) * ck * ((chunk2Fin j).card : ℝ) := by
      exact mul_pos (mul_pos (by linarith) hck_pos) h_bj_pos
    linarith
  have h3 : 0 < (chunkGFin (k, j)).card := by exact_mod_cast h_gkj_pos
  have h4 : (chunkGFin (k, j)).Nonempty := Finset.card_pos.mp h3
  rcases h4 with ⟨p, hp⟩
  have h5 : p ∈ chunkGraph Gamma S1 S2 k j := (h_chunkGFin_mem (k, j) hkj p).mp hp
  have h_p1 : p 0 ∈ unitChunk S1 k := h5.2.1
  have h_p2 : p 1 ∈ unitChunk S2 j := h5.2.2
  let f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun p => (WithLp.equiv 2 (Fin 2 → ℝ)).symm
      (fun i : Fin 2 => if i = 0 then p 0 - (k : ℝ) else p 1 - (j : ℝ))
  have hG'_eq : G' = Set.image f (chunkGraph Gamma S1 S2 k j) := by rfl
  have hG'_nonempty : G'.Nonempty := by
    rw [hG'_eq]
    exact Set.Nonempty.image f ⟨p, h5⟩
  have hB1_nonempty : B1.Nonempty := ⟨p 0 - (k : ℝ), Set.mem_image_of_mem _ h_p1⟩
  have hB2_nonempty : B2.Nonempty := ⟨p 1 - (j : ℝ), Set.mem_image_of_mem _ h_p2⟩

  -- Size lower bounds
  have h_size1_real : (c_dense / 4) * (S1.ncard : ℝ) / (2 * R + 1) ≤ (B1.ncard : ℝ) := by
    have hS1_ncard : (S1.ncard : ℝ) = (N1 : ℝ) := by
      simp [Set.ncard_eq_toFinset_card S1 hS1_fin] <;> rfl
    rw [hS1_ncard, hB1_ncard]
    rw [hK_card] at h_k_size
    exact h_k_size
  have h_size2_real : (c_dense / 4) * (S2.ncard : ℝ) / (2 * R + 1) ≤ (B2.ncard : ℝ) := by
    have hS2_ncard : (S2.ncard : ℝ) = (N2 : ℝ) := by
      simp [Set.ncard_eq_toFinset_card S2 hS2_fin] <;> rfl
    rw [hS2_ncard, hB2_ncard]
    rw [hK_card] at h_j_size
    exact h_j_size

  -- Density lower bound
  have h_density_real' : (c_dense / 4) * (B1.ncard : ℝ) * (B2.ncard : ℝ) ≤ (G'.ncard : ℝ) := by
    rw [hB1_ncard, hB2_ncard, hG'_ncard]
    exact h_j_density

  -- Witness: translated points come from original chunk graph
  have hG_orig_sub : G_orig ⊆ Gamma := by
    intro p hp
    exact hp.1
  have hG'_witness : ∀ p' ∈ G', ∃ g ∈ G_orig, p' 0 = g 0 - (k : ℝ) ∧ p' 1 = g 1 - (j : ℝ) := by
    intro p' hp'
    rcases hp' with ⟨g, hg, rfl⟩
    refine ⟨g, hg, ?_⟩
    simp [translateGraph2D]
    <;> aesop

  exact ⟨k, j, B1, B2, G', G_orig,
    hB1_unit, hB2_unit, hB1_nonempty, hB2_nonempty,
    hG'_finite, hG'_grid, hG'_sub,
    h_density_real', h_size1_real, h_size2_real, rfl, rfl,
    hG_orig_sub, hG'_witness⟩

end ProductLikeIncidence.ProductReduction
