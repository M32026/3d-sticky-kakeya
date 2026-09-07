module

/-
# Rescaling Restructuring — 2D Unit-Chunk Pigeonhole

Selects a unit chunk (k,j) of a 2D graph Gamma ⊆ S1 × S2,
translates it to [0,1]^2, preserving the density product bound.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.Compat
public import MyLeanRepo.ProductLikeIncidence.DeltaSetTranslation
public import MyLeanRepo.ProductLikeSetBasics
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Set ENNReal Bornology Classical

noncomputable section

namespace ProductLikeIncidence.ProductReduction

/-- Unit chunk S ∩ [k, k+1). -/
def unitChunk (S : Set ℝ) (k : ℤ) : Set ℝ :=
  S ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1)

/-- 2D chunk restriction. -/
def chunkGraph (Gamma : Set (EuclideanSpace ℝ (Fin 2)))
    (S1 S2 : Set ℝ) (k j : ℤ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  Gamma ∩ {p | p 0 ∈ unitChunk S1 k ∧ p 1 ∈ unitChunk S2 j}

/-- Translate a 2D set by integer vector (k,j). -/
def translateGraph2D (k j : ℤ) (G : Set (EuclideanSpace ℝ (Fin 2))) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  Set.image (fun p : EuclideanSpace ℝ (Fin 2) =>
    (WithLp.equiv 2 (Fin 2 → ℝ)).symm
      (fun i : Fin 2 => if i = 0 then p 0 - (k : ℝ) else p 1 - (j : ℝ))) G

/-- For dyadic δ, integer translation preserves δ-grid in 2D. -/
lemma int_translate_preserves_grid2d {δ : ℝ} (hδ_dyadic : δ ∈ dyadicScales)
    (k j : ℤ) {G : Set (EuclideanSpace ℝ (Fin 2))}
    (hG_grid : ∀ p ∈ G, ∀ i : Fin 2, ∃ m : ℤ, p i = δ * (m : ℝ)) :
    ∀ q ∈ translateGraph2D k j G, ∀ i : Fin 2, ∃ m : ℤ, q i = δ * (m : ℝ) := by
  rcases hδ_dyadic with ⟨n, hδ_eq⟩
  let mk : ℤ := k * (2 ^ n)
  let mj : ℤ := j * (2 ^ n)
  have hk : (k : ℝ) = δ * (mk : ℝ) := by
    rw [hδ_eq]; simp [mk, zpow_neg] <;> field_simp
  have hj : (j : ℝ) = δ * (mj : ℝ) := by
    rw [hδ_eq]; simp [mj, zpow_neg] <;> field_simp
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  let T := (WithLp.equiv 2 (Fin 2 → ℝ)).symm
      (fun i : Fin 2 => if i = 0 then p 0 - (k : ℝ) else p 1 - (j : ℝ))
  have hT0 : T 0 = p 0 - (k : ℝ) := by simp [T]
  have hT1 : T 1 = p 1 - (j : ℝ) := by simp [T]
  intro i
  have hpi : ∃ m : ℤ, p i = δ * (m : ℝ) := hG_grid p hp i
  rcases hpi with ⟨m, hm⟩
  have h_i_cases : i = 0 ∨ i = 1 := by fin_cases i <;> tauto
  rcases h_i_cases with (rfl | rfl)
  · refine ⟨m - mk, ?_⟩
    rw [hT0, hm, hk, Int.cast_sub] <;> ring
  · refine ⟨m - mj, ?_⟩
    rw [hT1, hm, hj, Int.cast_sub] <;> ring

/-- 2D covering number preservation under integer translation. -/
lemma covering2D_translate_by_int {δ : ℝ} (hδ_dyadic : δ ∈ dyadicScales) (hδ_pos : 0 < δ)
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG_fin : Set.Finite G)
    (hG_grid : ∀ p ∈ G, ∀ i : Fin 2, ∃ m : ℤ, p i = δ * (m : ℝ))
    (k j : ℤ) :
    dyadicCoveringNumber δ (translateGraph2D k j G) = dyadicCoveringNumber δ G := by
  let T : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun p => (WithLp.equiv 2 (Fin 2 → ℝ)).symm
      (fun i : Fin 2 => if i = 0 then p 0 - (k : ℝ) else p 1 - (j : ℝ))
  have hT_inj : Function.Injective T := by
    intro p q h
    have h0 : (T p) 0 = (T q) 0 := by rw [h]
    have h1 : (T p) 1 = (T q) 1 := by rw [h]
    have h0' : (T p) 0 = p 0 - (k : ℝ) := by simp [T]
    have h1' : (T p) 1 = p 1 - (j : ℝ) := by simp [T]
    have h0q : (T q) 0 = q 0 - (k : ℝ) := by simp [T]
    have h1q : (T q) 1 = q 1 - (j : ℝ) := by simp [T]
    have h2 : p 0 = q 0 := by linarith [h0, h0', h0q]
    have h3 : p 1 = q 1 := by linarith [h1, h1', h1q]
    ext i; fin_cases i <;> tauto
  have hG'_grid := int_translate_preserves_grid2d hδ_dyadic k j hG_grid
  have h1 : dyadicCoveringNumber δ (translateGraph2D k j G) = (translateGraph2D k j G).encard :=
    grid_set_coveringNumber_eq_encard hδ_pos hG'_grid
  have h2 : dyadicCoveringNumber δ G = G.encard :=
    grid_set_coveringNumber_eq_encard hδ_pos hG_grid
  rw [h1, h2]
  have h3 : (translateGraph2D k j G).encard = G.encard := hT_inj.encard_image G
  rw [h3]

/-- Nreal of finite grid set equals its encard. -/
lemma nreal_grid_eq_encard {δ : ℝ} (hδ_pos : 0 < δ) {S : Set ℝ} (hS_fin : Set.Finite S)
    (hS_grid : ∀ x ∈ S, ∃ m : ℤ, x = δ * (m : ℝ)) :
    Nreal δ S = ENat.toENNReal S.encard := by
  have hgrid : ∀ p ∈ productLikeRealLineCopy S, ∀ i : Fin 1, ∃ (m : ℤ), p i = δ * (m : ℝ) := by
    intro p hp i
    have h6 : p 0 ∈ S := by
      exact hp
    have h7 : ∃ (m : ℤ), p 0 = δ * (m : ℝ) := hS_grid (p 0) h6
    have h8 : p i = p 0 := by fin_cases i <;> rfl
    rw [h8]; exact h7
  have h : dyadicCoveringNumber δ (productLikeRealLineCopy S) = (productLikeRealLineCopy S).encard :=
    grid_set_coveringNumber_eq_encard hδ_pos hgrid
  let f : ℝ → EuclideanSpace ℝ (Fin 1) := fun x =>
    (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ => x)
  have hfinj : Function.Injective f := by
    intro x y h
    have h0 : (f x) 0 = (f y) 0 := by rw [h]
    simpa [f] using h0
  have h_eq : productLikeRealLineCopy S = f '' S := by
    ext p
    simp [productLikeRealLineCopy, f]
    <;> constructor
    · intro h
      refine ⟨p 0, h, ?_⟩
      ext i; fin_cases i <;> simp
    · rintro ⟨x, hx, rfl⟩
      exact hx
  have h4 : (productLikeRealLineCopy S).encard = S.encard := by
    rw [h_eq]; exact hfinj.encard_image S
  rw [Nreal, h, h4]

/-- The 2D unit-chunk pigeonhole. -/
theorem unit_chunk_pigeonhole_2d
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
    {c_dense : ENNReal}
    (h_density : c_dense * Nreal δ S1 * Nreal δ S2 ≤
        ENat.toENNReal (dyadicCoveringNumber δ Gamma)) :
    ∃ (k j : ℤ) (S1' S2' : Set ℝ)
      (Gamma' : Set (EuclideanSpace ℝ (Fin 2))),
      S1' ⊆ Set.Icc (0 : ℝ) 1 ∧
      S2' ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ p ∈ Gamma', p 0 ∈ S1' ∧ p 1 ∈ S2') ∧
      c_dense * Nreal δ S1' * Nreal δ S2' ≤
        ENat.toENNReal (dyadicCoveringNumber δ Gamma') := by
  rcases hR_int with ⟨cR, hR_eq⟩
  have hcR_pos : 0 < cR := by
    have h : (cR : ℝ) > 0 := by linarith [hR_eq]
    exact_mod_cast h
  let K : Finset ℤ := Finset.Icc (-cR) cR
  let Kset : Set ℤ := K
  have hK_nonempty : K.Nonempty := by
    refine ⟨0, ?_⟩
    simp only [K, Finset.mem_Icc] <;> constructor <;> linarith

  -- Chunk index in K for any x in [-R,R]
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
      have h4 : k ≤ x := Int.floor_le x
      have h5 : x ≤ (cR : ℝ) := by rw [hR_eq] at h2; exact h2
      have h6 : (k : ℝ) ≤ (cR : ℝ) := by linarith
      exact_mod_cast h6
    simp only [K, Finset.mem_Icc]
    exact ⟨hk_low, hk_high⟩

  -- Cover
  have h_cover1 : S1 = ⋃ k ∈ Kset, unitChunk S1 k := by
    apply Set.Subset.antisymm
    · intro x hx
      let k := Int.floor x
      have hkK : k ∈ K := h_chunk_in_K x (hS1_bdd x hx)
      have h1 : (k : ℝ) ≤ x := Int.floor_le x
      have h2 : x < (k : ℝ) + 1 := Int.lt_floor_add_one x
      exact Set.mem_iUnion₂.mpr ⟨k, hkK, ⟨hx, ⟨h1, h2⟩⟩⟩
    · intro x hx
      rcases Set.mem_iUnion₂.mp hx with ⟨k, _, hxk⟩
      exact hxk.1
  have h_cover2 : S2 = ⋃ j ∈ Kset, unitChunk S2 j := by
    apply Set.Subset.antisymm
    · intro x hx
      let j := Int.floor x
      have hjK : j ∈ K := h_chunk_in_K x (hS2_bdd x hx)
      have h1 : (j : ℝ) ≤ x := Int.floor_le x
      have h2 : x < (j : ℝ) + 1 := Int.lt_floor_add_one x
      exact Set.mem_iUnion₂.mpr ⟨j, hjK, ⟨hx, ⟨h1, h2⟩⟩⟩
    · intro x hx
      rcases Set.mem_iUnion₂.mp hx with ⟨j, _, hxj⟩
      exact hxj.1

  -- Chunks disjoint (set level)
  have h_disj1_set : Kset.PairwiseDisjoint (fun k => unitChunk S1 k) := by
    intro k1 _ k2 _ hne
    simp only [Set.disjoint_left]
    intro x hx1 hx2
    have hfl1 : Int.floor x = k1 := by
      rw [Int.floor_eq_iff] <;> exact ⟨hx1.2.1, by exact hx1.2.2⟩
    have hfl2 : Int.floor x = k2 := by
      rw [Int.floor_eq_iff] <;> exact ⟨hx2.2.1, by exact hx2.2.2⟩
    exact hne (hfl1.symm.trans hfl2)
  have h_disj2_set : Kset.PairwiseDisjoint (fun j => unitChunk S2 j) := by
    intro j1 _ j2 _ hne
    simp only [Set.disjoint_left]
    intro x hx1 hx2
    have hfl1 : Int.floor x = j1 := by
      rw [Int.floor_eq_iff] <;> exact ⟨hx1.2.1, by exact hx1.2.2⟩
    have hfl2 : Int.floor x = j2 := by
      rw [Int.floor_eq_iff] <;> exact ⟨hx2.2.1, by exact hx2.2.2⟩
    exact hne (hfl1.symm.trans hfl2)

  -- Cardinality of disjoint unions (directly in ENNReal)
  have h_chunk1_fin' : ∀ k ∈ K, (unitChunk S1 k).Finite := by
    intro k _; exact hS1_fin.subset (by intro x hx; exact hx.1)
  have h_chunk2_fin' : ∀ j ∈ K, (unitChunk S2 j).Finite := by
    intro j _; exact hS2_fin.subset (by intro x hx; exact hx.1)
  have h_disj1' : ∀ k1 ∈ K, ∀ k2 ∈ K, k1 ≠ k2 → Disjoint (unitChunk S1 k1) (unitChunk S1 k2) := by
    intro k1 hk1 k2 hk2 hne
    exact h_disj1_set hk1 hk2 hne
  have h_disj2' : ∀ j1 ∈ K, ∀ j2 ∈ K, j1 ≠ j2 → Disjoint (unitChunk S2 j1) (unitChunk S2 j2) := by
    intro j1 hj1 j2 hj2 hne
    exact h_disj2_set hj1 hj2 hne

  have h_cover1' : S1 = ⋃ k ∈ K, unitChunk S1 k := by
    simpa [Kset] using h_cover1
  have h_cover2' : S2 = ⋃ j ∈ K, unitChunk S2 j := by
    simpa [Kset] using h_cover2

  -- Finset-valued chunk functions (avoid proof arguments in sum binders)
  let chunk1Fin (k : ℤ) : Finset ℝ :=
    if hk : k ∈ K then (h_chunk1_fin' k hk).toFinset else ∅
  let chunk2Fin (j : ℤ) : Finset ℝ :=
    if hj : j ∈ K then (h_chunk2_fin' j hj).toFinset else ∅

  have h_chunk1Fin_mem : ∀ (k : ℤ) (hk : k ∈ K), ∀ x, x ∈ chunk1Fin k ↔ x ∈ unitChunk S1 k := by
    intro k hk x
    have h_eq : chunk1Fin k = (h_chunk1_fin' k hk).toFinset := by
      simp [chunk1Fin, hk]
    rw [h_eq]
    simp [Set.Finite.mem_toFinset]
  have h_chunk2Fin_mem : ∀ (j : ℤ) (hj : j ∈ K), ∀ x, x ∈ chunk2Fin j ↔ x ∈ unitChunk S2 j := by
    intro j hj x
    have h_eq : chunk2Fin j = (h_chunk2_fin' j hj).toFinset := by
      simp [chunk2Fin, hj]
    rw [h_eq]
    simp [Set.Finite.mem_toFinset]

  have h_card1_nat : hS1_fin.toFinset.card = ∑ k ∈ K, (chunk1Fin k).card := by
    have h_disj_finset : ∀ k1 ∈ K, ∀ k2 ∈ K, k1 ≠ k2 → Disjoint (chunk1Fin k1) (chunk1Fin k2) := by
      intro k1 hk1 k2 hk2 hne
      have h_disj : Disjoint (unitChunk S1 k1) (unitChunk S1 k2) := h_disj1_set hk1 hk2 hne
      simp only [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 : x ∈ unitChunk S1 k1 := (h_chunk1Fin_mem k1 hk1 x).mp hx1
      have h2 : x ∈ unitChunk S1 k2 := (h_chunk1Fin_mem k2 hk2 x).mp hx2
      exact h_disj.le_bot ⟨h1, h2⟩
    have h : (K.biUnion chunk1Fin).card = ∑ k ∈ K, (chunk1Fin k).card := Finset.card_biUnion h_disj_finset
    have h2 : K.biUnion chunk1Fin = hS1_fin.toFinset := by
      ext x
      simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨k, hk, hx⟩
        have h3 : x ∈ unitChunk S1 k := (h_chunk1Fin_mem k hk x).mp hx
        exact h3.1
      · intro hx
        have h4 : x ∈ ⋃ k ∈ K, unitChunk S1 k := by rw [←h_cover1']; exact hx
        rcases Set.mem_iUnion₂.mp h4 with ⟨k, hk, hxk⟩
        exact ⟨k, hk, (h_chunk1Fin_mem k hk x).mpr hxk⟩
    rw [←h2, h]

  have h_card2_nat : hS2_fin.toFinset.card = ∑ j ∈ K, (chunk2Fin j).card := by
    have h_disj_finset : ∀ j1 ∈ K, ∀ j2 ∈ K, j1 ≠ j2 → Disjoint (chunk2Fin j1) (chunk2Fin j2) := by
      intro j1 hj1 j2 hj2 hne
      have h_disj : Disjoint (unitChunk S2 j1) (unitChunk S2 j2) := h_disj2_set hj1 hj2 hne
      simp only [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 : x ∈ unitChunk S2 j1 := (h_chunk2Fin_mem j1 hj1 x).mp hx1
      have h2 : x ∈ unitChunk S2 j2 := (h_chunk2Fin_mem j2 hj2 x).mp hx2
      exact h_disj.le_bot ⟨h1, h2⟩
    have h : (K.biUnion chunk2Fin).card = ∑ j ∈ K, (chunk2Fin j).card := Finset.card_biUnion h_disj_finset
    have h2 : K.biUnion chunk2Fin = hS2_fin.toFinset := by
      ext x
      simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨j, hj, hx⟩
        have h3 : x ∈ unitChunk S2 j := (h_chunk2Fin_mem j hj x).mp hx
        exact h3.1
      · intro hx
        have h4 : x ∈ ⋃ j ∈ K, unitChunk S2 j := by rw [←h_cover2']; exact hx
        rcases Set.mem_iUnion₂.mp h4 with ⟨j, hj, hxj⟩
        exact ⟨j, hj, (h_chunk2Fin_mem j hj x).mpr hxj⟩
    rw [←h2, h]

  -- ENNReal versions
  have h_sum1_ENNReal : ENat.toENNReal S1.encard = ∑ k ∈ K, ENat.toENNReal (unitChunk S1 k).encard := by
    have h1 : ENat.toENNReal S1.encard = (↑hS1_fin.toFinset.card : ENNReal) := by
      rw [hS1_fin.encard_eq_coe_toFinset_card] <;> rfl
    rw [h1, h_card1_nat, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have h_eq : (chunk1Fin k).card = (h_chunk1_fin' k hk).toFinset.card := by
      have h : chunk1Fin k = (h_chunk1_fin' k hk).toFinset := by simp [chunk1Fin, hk]
      rw [h]
    rw [h_eq, (h_chunk1_fin' k hk).encard_eq_coe_toFinset_card] <;> rfl
  have h_sum2_ENNReal : ENat.toENNReal S2.encard = ∑ j ∈ K, ENat.toENNReal (unitChunk S2 j).encard := by
    have h1 : ENat.toENNReal S2.encard = (↑hS2_fin.toFinset.card : ENNReal) := by
      rw [hS2_fin.encard_eq_coe_toFinset_card] <;> rfl
    rw [h1, h_card2_nat, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have h_eq : (chunk2Fin j).card = (h_chunk2_fin' j hj).toFinset.card := by
      have h : chunk2Fin j = (h_chunk2_fin' j hj).toFinset := by simp [chunk2Fin, hj]
      rw [h]
    rw [h_eq, (h_chunk2_fin' j hj).encard_eq_coe_toFinset_card] <;> rfl

  -- Gamma partition
  let K2 : Finset (ℤ × ℤ) := K ×ˢ K
  let K2set : Set (ℤ × ℤ) := K2
  let chunkG (kj : ℤ × ℤ) : Set (EuclideanSpace ℝ (Fin 2)) :=
    chunkGraph Gamma S1 S2 kj.1 kj.2

  have hG_cover : Gamma = ⋃ kj ∈ K2set, chunkG kj := by
    apply Set.Subset.antisymm
    · intro p hp
      have hpsub : p 0 ∈ S1 ∧ p 1 ∈ S2 := hGamma_sub p hp
      have h1 : p 0 ∈ (⋃ k ∈ Kset, unitChunk S1 k) := by
        rw [←h_cover1] <;> exact hpsub.1
      have h2 : p 1 ∈ (⋃ j ∈ Kset, unitChunk S2 j) := by
        rw [←h_cover2] <;> exact hpsub.2
      rcases Set.mem_iUnion₂.mp h1 with ⟨k, hkK, hpk⟩
      rcases Set.mem_iUnion₂.mp h2 with ⟨j, hjK, hpj⟩
      have hkj : (k, j) ∈ K2 := Finset.mem_product.mpr ⟨hkK, hjK⟩
      exact Set.mem_iUnion₂.mpr ⟨(k, j), hkj, ⟨hp, ⟨hpk, hpj⟩⟩⟩
    · intro p hp
      rcases Set.mem_iUnion₂.mp hp with ⟨kj, _, hpkj⟩
      exact hpkj.1

  have h_disjG_set : K2set.PairwiseDisjoint chunkG := by
    intro ⟨k1,j1⟩ hk1 ⟨k2,j2⟩ hk2 hne
    simp only [Set.disjoint_left]
    intro p hp1 hp2
    have h1 : p 0 ∈ unitChunk S1 k1 := hp1.2.1
    have h2 : p 0 ∈ unitChunk S1 k2 := hp2.2.1
    if hk : k1 ≠ k2 then
      have hk1' : k1 ∈ K := (Finset.mem_product.mp hk1).1
      have hk2' : k2 ∈ K := (Finset.mem_product.mp hk2).1
      have h_disj : Disjoint (unitChunk S1 k1) (unitChunk S1 k2) := h_disj1_set hk1' hk2' hk
      exact h_disj.le_bot ⟨h1, h2⟩
    else
      have hk' : k1 = k2 := by tauto
      have hj : j1 ≠ j2 := by intro h; apply hne; exact Prod.ext hk' h
      have h3 : p 1 ∈ unitChunk S2 j1 := hp1.2.2
      have h4 : p 1 ∈ unitChunk S2 j2 := hp2.2.2
      have hj1' : j1 ∈ K := (Finset.mem_product.mp hk1).2
      have hj2' : j2 ∈ K := (Finset.mem_product.mp hk2).2
      have h_disj : Disjoint (unitChunk S2 j1) (unitChunk S2 j2) := h_disj2_set hj1' hj2' hj
      exact h_disj.le_bot ⟨h3, h4⟩

  have hK2_fin : Set.Finite K2set := K2.finite_toSet

  -- Gamma disjoint union
  have h_chunkG_fin' : ∀ kj ∈ K2, (chunkG kj).Finite := by
    intro kj _; exact hGamma_fin.subset (by simp [chunkG, chunkGraph] <;> tauto)

  let chunkGFin (kj : ℤ × ℤ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
    if hkj : kj ∈ K2 then (h_chunkG_fin' kj hkj).toFinset else ∅

  have h_chunkGFin_mem : ∀ (kj : ℤ × ℤ) (hkj : kj ∈ K2), ∀ x, x ∈ chunkGFin kj ↔ x ∈ chunkG kj := by
    intro kj hkj x
    have h_eq : chunkGFin kj = (h_chunkG_fin' kj hkj).toFinset := by
      simp [chunkGFin, hkj]
    rw [h_eq]
    simp [Set.Finite.mem_toFinset]

  have hG_cover' : Gamma = ⋃ kj ∈ K2, chunkG kj := by
    simpa [K2set] using hG_cover

  have h_cardG_nat : hGamma_fin.toFinset.card = ∑ kj ∈ K2, (chunkGFin kj).card := by
    have h_disj_finset : ∀ kj1 ∈ K2, ∀ kj2 ∈ K2, kj1 ≠ kj2 → Disjoint (chunkGFin kj1) (chunkGFin kj2) := by
      intro kj1 hkj1 kj2 hkj2 hne
      have h_disj : Disjoint (chunkG kj1) (chunkG kj2) := h_disjG_set hkj1 hkj2 hne
      simp only [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 : x ∈ chunkG kj1 := (h_chunkGFin_mem kj1 hkj1 x).mp hx1
      have h2 : x ∈ chunkG kj2 := (h_chunkGFin_mem kj2 hkj2 x).mp hx2
      exact h_disj.le_bot ⟨h1, h2⟩
    have h : (K2.biUnion chunkGFin).card = ∑ kj ∈ K2, (chunkGFin kj).card := Finset.card_biUnion h_disj_finset
    have h2 : K2.biUnion chunkGFin = hGamma_fin.toFinset := by
      ext x
      simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨kj, hkj, hx⟩
        have h3 : x ∈ chunkG kj := (h_chunkGFin_mem kj hkj x).mp hx
        exact h3.1
      · intro hx
        have h4 : x ∈ ⋃ kj ∈ K2, chunkG kj := by rw [←hG_cover']; exact hx
        rcases Set.mem_iUnion₂.mp h4 with ⟨kj, hkj, hxkj⟩
        exact ⟨kj, hkj, (h_chunkGFin_mem kj hkj x).mpr hxkj⟩
    rw [←h2, h]

  have h_sumG_ENNReal : ENat.toENNReal Gamma.encard = ∑ kj ∈ K2, ENat.toENNReal (chunkG kj).encard := by
    have h1 : ENat.toENNReal Gamma.encard = (↑hGamma_fin.toFinset.card : ENNReal) := by
      rw [hGamma_fin.encard_eq_coe_toFinset_card] <;> rfl
    rw [h1, h_cardG_nat, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro kj hkj
    have h_eq : (chunkGFin kj).card = (h_chunkG_fin' kj hkj).toFinset.card := by
      have h : chunkGFin kj = (h_chunkG_fin' kj hkj).toFinset := by simp [chunkGFin, hkj]
      rw [h]
    rw [h_eq, (h_chunkG_fin' kj hkj).encard_eq_coe_toFinset_card] <;> rfl

  -- Nreal = encard for grid sets
  have h_nreal_S1 : Nreal δ S1 = ENat.toENNReal S1.encard :=
    nreal_grid_eq_encard hδ_pos hS1_fin hS1_grid
  have h_nreal_S2 : Nreal δ S2 = ENat.toENNReal S2.encard :=
    nreal_grid_eq_encard hδ_pos hS2_fin hS2_grid
  have h_nreal_G : ENat.toENNReal (dyadicCoveringNumber δ Gamma) = ENat.toENNReal Gamma.encard := by
    have hgrid : ∀ p ∈ Gamma, ∀ i : Fin 2, ∃ (m : ℤ), p i = δ * (m : ℝ) := by
      intro p hp i
      have h : p 0 ∈ S1 ∧ p 1 ∈ S2 := hGamma_sub p hp
      fin_cases i <;> tauto
    have h : dyadicCoveringNumber δ Gamma = Gamma.encard := grid_set_coveringNumber_eq_encard hδ_pos hgrid
    rw [h]

  have hK2_nonempty : K2.Nonempty := by
    have h1 : K.Nonempty := hK_nonempty
    exact Finset.Nonempty.product hK_nonempty hK_nonempty

  -- Double counting in ENNReal
  have h_main : ∃ (kj : ℤ × ℤ), kj ∈ K2 ∧
      c_dense * ENat.toENNReal (unitChunk S1 kj.1).encard *
        ENat.toENNReal (unitChunk S2 kj.2).encard ≤
      ENat.toENNReal (chunkG kj).encard := by
    by_contra h; push Not at h
    have h_sum : (∑ kj ∈ K2, ENat.toENNReal (chunkG kj).encard) <
        c_dense * (∑ k ∈ K, ENat.toENNReal (unitChunk S1 k).encard) *
          (∑ j ∈ K, ENat.toENNReal (unitChunk S2 j).encard) := by
      calc
        (∑ kj ∈ K2, ENat.toENNReal (chunkG kj).encard)
          < ∑ kj ∈ K2, (c_dense * ENat.toENNReal (unitChunk S1 kj.1).encard *
                ENat.toENNReal (unitChunk S2 kj.2).encard) := by
            exact ENNReal.sum_lt_sum_of_nonempty hK2_nonempty (fun kj hkj => h kj hkj)
        _ = c_dense * (∑ k ∈ K, ENat.toENNReal (unitChunk S1 k).encard) *
              (∑ j ∈ K, ENat.toENNReal (unitChunk S2 j).encard) := by
          have h1 : ∑ kj ∈ K2, (c_dense * ENat.toENNReal (unitChunk S1 kj.1).encard *
                ENat.toENNReal (unitChunk S2 kj.2).encard) =
              c_dense * ∑ kj ∈ K2, (ENat.toENNReal (unitChunk S1 kj.1).encard *
                ENat.toENNReal (unitChunk S2 kj.2).encard) := by
            have h_assoc : ∀ (kj : ℤ × ℤ), c_dense * ENat.toENNReal (unitChunk S1 kj.1).encard *
                  ENat.toENNReal (unitChunk S2 kj.2).encard =
              c_dense * (ENat.toENNReal (unitChunk S1 kj.1).encard *
                  ENat.toENNReal (unitChunk S2 kj.2).encard) := by
              intro kj; exact mul_assoc c_dense _ _
            rw [Finset.sum_congr rfl (fun x _ => h_assoc x), ←Finset.mul_sum]
          rw [h1]
          have h2 : ∑ kj ∈ K2, (ENat.toENNReal (unitChunk S1 kj.1).encard *
                ENat.toENNReal (unitChunk S2 kj.2).encard) =
              (∑ k ∈ K, ENat.toENNReal (unitChunk S1 k).encard) *
                (∑ j ∈ K, ENat.toENNReal (unitChunk S2 j).encard) := by
            have hK2_eq : K2 = K ×ˢ K := by rfl
            rw [hK2_eq, Finset.sum_product]
            exact (Finset.sum_mul_sum K K (fun k => ENat.toENNReal (unitChunk S1 k).encard)
              (fun j => ENat.toENNReal (unitChunk S2 j).encard)).symm
          rw [h2] <;> ring
    rw [←h_sumG_ENNReal, ←h_sum1_ENNReal, ←h_sum2_ENNReal] at h_sum
    rw [h_nreal_G, h_nreal_S1, h_nreal_S2] at h_density
    exact lt_irrefl _ (lt_of_le_of_lt h_density h_sum)

  rcases h_main with ⟨⟨k, j⟩, hkj, h_ineq⟩

  -- Translate
  let S1' : Set ℝ := Set.image (fun x => x - (k : ℝ)) (unitChunk S1 k)
  let S2' : Set ℝ := Set.image (fun x => x - (j : ℝ)) (unitChunk S2 j)
  let Gamma' := translateGraph2D k j (chunkG (k, j))

  have hS1'_sub : S1' ⊆ Set.Icc (0 : ℝ) 1 := by
    intro y hy; rcases hy with ⟨x, hx, rfl⟩
    exact ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
  have hS2'_sub : S2' ⊆ Set.Icc (0 : ℝ) 1 := by
    intro y hy; rcases hy with ⟨x, hx, rfl⟩
    exact ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩

  have hG'_sub : ∀ p ∈ Gamma', p 0 ∈ S1' ∧ p 1 ∈ S2' := by
    intro p hp
    rcases hp with ⟨q, hq, rfl⟩
    have hq0 : q 0 ∈ unitChunk S1 k := hq.2.1
    have hq1 : q 1 ∈ unitChunk S2 j := hq.2.2
    constructor
    · exact ⟨q 0, hq0, by simp [translateGraph2D]⟩
    · exact ⟨q 1, hq1, by simp [translateGraph2D]⟩

  -- Nreal preservation under translation
  have h_chunk1_bdd : IsBounded (unitChunk S1 k) :=
    IsBounded.subset (Metric.isBounded_Icc _ _) (by
      intro x hx; exact ⟨hx.2.1, hx.2.2.le⟩)
  have h_chunk2_bdd : IsBounded (unitChunk S2 j) :=
    IsBounded.subset (Metric.isBounded_Icc _ _) (by
      intro x hx; exact ⟨hx.2.1, hx.2.2.le⟩)
  have hN1_eq : Nreal δ S1' = Nreal δ (unitChunk S1 k) := by
    have h_cast : (↑(-k) : ℝ) = -(k : ℝ) := by simp
    have h_main := nreal_translate_by_int hδ_dyadic h_chunk1_bdd (-k)
    have h_eq : S1' = translateSet (↑(-k)) (unitChunk S1 k) := by
      dsimp only [S1', translateSet]
      congr with x <;> simp [h_cast] <;> ring
    rw [h_eq]
    exact h_main
  have hN2_eq : Nreal δ S2' = Nreal δ (unitChunk S2 j) := by
    have h_cast : (↑(-j) : ℝ) = -(j : ℝ) := by simp
    have h_main := nreal_translate_by_int hδ_dyadic h_chunk2_bdd (-j)
    have h_eq : S2' = translateSet (↑(-j)) (unitChunk S2 j) := by
      dsimp only [S2', translateSet]
      congr with x <;> simp [h_cast] <;> ring
    rw [h_eq]
    exact h_main

  -- Chunk graph grid
  have h_chunkG_grid : ∀ p ∈ chunkG (k, j), ∀ i : Fin 2, ∃ m : ℤ, p i = δ * (m : ℝ) := by
    intro p hp i
    have hsub : p 0 ∈ S1 ∧ p 1 ∈ S2 := hGamma_sub p hp.1
    fin_cases i <;> tauto
  have h_chunkG_fin : Set.Finite (chunkG (k, j)) :=
    hGamma_fin.subset (by simp [chunkG, chunkGraph] <;> tauto)

  have hNG_eq : dyadicCoveringNumber δ Gamma' = dyadicCoveringNumber δ (chunkG (k, j)) :=
    covering2D_translate_by_int hδ_dyadic hδ_pos h_chunkG_fin h_chunkG_grid k j

  -- Nreal for chunks
  have h_chunk1_grid : ∀ x ∈ unitChunk S1 k, ∃ m : ℤ, x = δ * (m : ℝ) := by
    intro x hx; exact hS1_grid x hx.1
  have h_chunk2_grid : ∀ x ∈ unitChunk S2 j, ∃ m : ℤ, x = δ * (m : ℝ) := by
    intro x hx; exact hS2_grid x hx.1
  have h_chunk1_fin : Set.Finite (unitChunk S1 k) := hS1_fin.subset (by
    intro x hx; exact hx.1)
  have h_chunk2_fin : Set.Finite (unitChunk S2 j) := hS2_fin.subset (by
    intro x hx; exact hx.1)

  have h_nreal_chunk1 : Nreal δ (unitChunk S1 k) = ENat.toENNReal (unitChunk S1 k).encard :=
    nreal_grid_eq_encard hδ_pos h_chunk1_fin h_chunk1_grid
  have h_nreal_chunk2 : Nreal δ (unitChunk S2 j) = ENat.toENNReal (unitChunk S2 j).encard :=
    nreal_grid_eq_encard hδ_pos h_chunk2_fin h_chunk2_grid

  have h_nreal_chunkG : ENat.toENNReal (dyadicCoveringNumber δ (chunkG (k, j))) =
      ENat.toENNReal (chunkG (k, j)).encard := by
    have h : dyadicCoveringNumber δ (chunkG (k, j)) = (chunkG (k, j)).encard :=
      grid_set_coveringNumber_eq_encard hδ_pos h_chunkG_grid
    rw [h]

  have h_final : c_dense * Nreal δ S1' * Nreal δ S2' ≤ ENat.toENNReal (dyadicCoveringNumber δ Gamma') := by
    rw [hN1_eq, hN2_eq, hNG_eq, h_nreal_chunk1, h_nreal_chunk2, h_nreal_chunkG]
    exact h_ineq

  exact ⟨k, j, S1', S2', Gamma', hS1'_sub, hS2'_sub, hG'_sub, h_final⟩

end ProductLikeIncidence.ProductReduction
