module

/-
# Discretized Balog-Szemerédi-Gowers Theorem

Transfers the finite-set BSG theorem to dyadic covering numbers by mapping
bounded real sets to their cube index sets.

## Main result

`discretized_bsg`: Given dense G ⊂ A × B with small restricted sumset at
scale δ, extract large subsets A' ⊂ A, B' ⊂ B with small sumset and
dense G-intersection.

## Proof route

1. Map A, B to 1D cube index sets IA, IB ⊂ ℤ
2. Map G ⊂ A×B to product index set IG ⊂ IA × IB
3. Compare restricted sumset covering number to finite restricted sumset
4. Apply `balog_szemeredi_gowers_dense` to index sets
5. Map output index subsets back to real sets

## Whiteprint node
`robust_projection/DiscretizedBSG`
-/

public import MyLeanRepo.DiscretizedPluennecke
public import MyLeanRepo.AdditiveCombinatorics.DenseSubgraphBSG
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped Pointwise

namespace ProductLikeIncidence.DiscretizedBSG

/-! ## Product index set -/

/-- Pairs (i,j) of δ-dyadic cube indices whose product cube
`[δi,δ(i+1)) × [δj,δ(j+1))` meets G. -/
def productIndexSet (δ : ℝ) (G : Set (ℝ × ℝ)) : Set (ℤ × ℤ) :=
  {p | ((Set.Ico (δ * (p.1 : ℝ)) (δ * ((p.1 : ℝ) + 1)) ×ˢ
         Set.Ico (δ * (p.2 : ℝ)) (δ * ((p.2 : ℝ) + 1))) ∩ G).Nonempty}

/-- The product index set is finite for bounded G. -/
lemma productIndexSet_finite {δ : ℝ} (hδ : 0 < δ) {G : Set (ℝ × ℝ)}
    (hG : Bornology.IsBounded G) : (productIndexSet δ G).Finite := by
  let A1 := Prod.fst '' G
  let A2 := Prod.snd '' G
  have h1 : Bornology.IsBounded A1 := hG.image_fst
  have h2 : Bornology.IsBounded A2 := hG.image_snd
  have h3 : productIndexSet δ G ⊆ (realCubeIndexSet δ A1) ×ˢ (realCubeIndexSet δ A2) := by
    intro p hp
    rcases hp with ⟨z, hz_cube, hzG⟩
    let x := z.1
    let y := z.2
    have hx_cube : x ∈ Set.Ico (δ * (p.1 : ℝ)) (δ * ((p.1 : ℝ) + 1)) := hz_cube.1
    have hy_cube : y ∈ Set.Ico (δ * (p.2 : ℝ)) (δ * ((p.2 : ℝ) + 1)) := hz_cube.2
    have hx : x ∈ A1 := ⟨z, hzG, rfl⟩
    have hy : y ∈ A2 := ⟨z, hzG, rfl⟩
    exact ⟨⟨x, hx_cube, hx⟩, ⟨y, hy_cube, hy⟩⟩
  have h4 : (realCubeIndexSet δ A1).Finite := realCubeIndexSet_finite hδ h1
  have h5 : (realCubeIndexSet δ A2).Finite := realCubeIndexSet_finite hδ h2
  have h6 : ((realCubeIndexSet δ A1) ×ˢ (realCubeIndexSet δ A2)).Finite :=
    Set.Finite.prod h4 h5
  exact Set.Finite.subset h6 h3

/-- Finset version of productIndexSet. -/
noncomputable def productIndexFinset (δ : ℝ) (hδ : 0 < δ) {G : Set (ℝ × ℝ)}
    (hG : Bornology.IsBounded G) : Finset (ℤ × ℤ) :=
  (productIndexSet_finite hδ hG).toFinset

/-- Finset version of realCubeIndexSet. -/
noncomputable def realCubeIndexFinset (δ : ℝ) (hδ : 0 < δ) {A : Set ℝ}
    (hA : Bornology.IsBounded A) : Finset ℤ :=
  (realCubeIndexSet_finite hδ hA).toFinset

/-! ## Restricted sumset comparison -/

/-- The restricted sumset {x+y | (x,y) ∈ G}. -/
def restrictedSumSet (G : Set (ℝ × ℝ)) : Set ℝ :=
  (fun p : ℝ × ℝ => p.1 + p.2) '' G

/-- restrictedSumSet G is bounded when G is bounded. -/
lemma restrictedSumSet_bounded {G : Set (ℝ × ℝ)}
    (hG : Bornology.IsBounded G) : Bornology.IsBounded (restrictedSumSet G) := by
  have h1 : Bornology.IsBounded (Prod.fst '' G) := hG.image_fst
  have h2 : Bornology.IsBounded (Prod.snd '' G) := hG.image_snd
  have h3 : restrictedSumSet G ⊆ Set.image2 (· + ·) (Prod.fst '' G) (Prod.snd '' G) := by
    intro z hz
    rcases hz with ⟨p, hp, rfl⟩
    exact ⟨p.1, ⟨p, hp, rfl⟩, p.2, ⟨p, hp, rfl⟩, rfl⟩
  exact (h1.add h2).subset h3

/-- Finset version of the restricted sumset index set. -/
noncomputable def restrictedSumIndexFinset (δ : ℝ) (hδ : 0 < δ) {G : Set (ℝ × ℝ)}
    (hG : Bornology.IsBounded G) : Finset ℤ :=
  (realCubeIndexSet_finite hδ (restrictedSumSet_bounded hG)).toFinset

/-- Key inclusion: finite restricted-sum indices map to covering indices {k, k-1}. -/
lemma finite_sumset_inclusion {δ : ℝ} (hδ : 0 < δ) {G : Set (ℝ × ℝ)} :
    (productIndexSet δ G).image (fun p : ℤ × ℤ => p.1 + p.2) ⊆
      (realCubeIndexSet δ (restrictedSumSet G)) ∪
      (fun k : ℤ => k - 1) '' (realCubeIndexSet δ (restrictedSumSet G)) := by
  intro s hs
  have h_exists : ∃ (p : ℤ × ℤ), p ∈ productIndexSet δ G ∧ p.1 + p.2 = s := by
    simpa [Set.mem_image] using hs
  rcases h_exists with ⟨p, hp, rfl⟩
  rcases hp with ⟨z, hz_cube, hzG⟩
  let x := z.1
  let y := z.2
  let z_sum := x + y
  have hz : z_sum ∈ restrictedSumSet G := ⟨z, hzG, rfl⟩
  have h_x1 : δ * (p.1 : ℝ) ≤ x := hz_cube.1.1
  have h_x2 : x < δ * ((p.1 : ℝ) + 1) := hz_cube.1.2
  have h_y1 : δ * (p.2 : ℝ) ≤ y := hz_cube.2.1
  have h_y2 : y < δ * ((p.2 : ℝ) + 1) := hz_cube.2.2
  let k : ℤ := Int.floor (z_sum / δ)
  have hk1 : δ * (k : ℝ) ≤ z_sum := by
    have h : (k : ℝ) ≤ z_sum / δ := Int.floor_le (z_sum / δ)
    have h2 : δ * (k : ℝ) ≤ δ * (z_sum / δ) := by gcongr
    have h3 : δ * (z_sum / δ) = z_sum := by field_simp [hδ.ne'] <;> ring
    rw [h3] at h2; exact h2
  have hk2 : z_sum < δ * ((k : ℝ) + 1) := by
    have h : z_sum / δ < (k : ℝ) + 1 := Int.lt_floor_add_one (z_sum / δ)
    have h2 : δ * (z_sum / δ) < δ * ((k : ℝ) + 1) := by gcongr
    have h3 : δ * (z_sum / δ) = z_sum := by field_simp [hδ.ne'] <;> ring
    rw [h3] at h2; exact h2
  have h_k_in : k ∈ realCubeIndexSet δ (restrictedSumSet G) :=
    ⟨z_sum, ⟨hk1, hk2⟩, hz⟩
  have h_s_le_k : p.1 + p.2 ≤ k := by
    by_contra h
    have h' : k + 1 ≤ p.1 + p.2 := by omega
    have h'' : (k : ℝ) + 1 ≤ (p.1 + p.2 : ℝ) := by exact_mod_cast h'
    have h51 : δ * (p.1 : ℝ) + δ * (p.2 : ℝ) ≤ x + y := by linarith
    have h52 : δ * (p.1 + p.2 : ℝ) = δ * (p.1 : ℝ) + δ * (p.2 : ℝ) := by ring
    have h5 : δ * (p.1 + p.2 : ℝ) ≤ z_sum := by rw [h52]; exact h51
    have h7 : δ * ((k : ℝ) + 1) ≤ δ * (p.1 + p.2 : ℝ) := by gcongr
    have h8 : δ * ((k : ℝ) + 1) ≤ z_sum := le_trans h7 h5
    linarith
  have h_k_le_s1 : k ≤ p.1 + p.2 + 1 := by
    by_contra h
    have h' : p.1 + p.2 + 2 ≤ k := by omega
    have h'' : (p.1 + p.2 : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast h'
    have h71 : δ * ((p.1 + p.2 : ℝ) + 2) = δ * ((p.1 + p.2 : ℝ)) + δ * 2 := by ring
    have h72 : z_sum < δ * ((p.1 + p.2 : ℝ) + 2) := by
      rw [h71]
      linarith [h_x2, h_y2]
    have h7 : δ * ((p.1 + p.2 : ℝ) + 2) ≤ δ * (k : ℝ) :=
      mul_le_mul_of_nonneg_left h'' (by linarith)
    have h8 : z_sum < δ * (k : ℝ) := lt_of_lt_of_le h72 h7
    linarith
  have h9 : p.1 + p.2 = k ∨ p.1 + p.2 = k - 1 := by omega
  rcases h9 with (h9 | h9)
  · left; rw [h9]; exact h_k_in
  · right; exact ⟨k, h_k_in, Eq.symm h9⟩

/-- Finite restricted sumset cardinality ≤ 2 * covering cardinality. -/
lemma finite_sumset_le_two_cover {δ : ℝ} (hδ : 0 < δ) {G : Set (ℝ × ℝ)}
    (hG : Bornology.IsBounded G) :
    ((productIndexFinset δ hδ hG).image (fun p : ℤ × ℤ => p.1 + p.2)).card ≤
      2 * (restrictedSumIndexFinset δ hδ hG).card := by
  let I_SG := restrictedSumIndexFinset δ hδ hG
  let F_SG := (productIndexFinset δ hδ hG).image (fun p : ℤ × ℤ => p.1 + p.2)
  have hI_SG_eq : (I_SG : Set ℤ) = realCubeIndexSet δ (restrictedSumSet G) := by
    simp [I_SG, restrictedSumIndexFinset, realCubeIndexFinset]
  have hF_SG_eq : (F_SG : Set ℤ) = (productIndexSet δ G).image (fun p : ℤ × ℤ => p.1 + p.2) := by
    simp [F_SG, productIndexFinset] <;> rfl
  have h_incl : (F_SG : Set ℤ) ⊆
      (I_SG : Set ℤ) ∪ (fun k : ℤ => k - 1) '' (I_SG : Set ℤ) := by
    rw [hI_SG_eq, hF_SG_eq]
    exact finite_sumset_inclusion hδ
  have h_card : F_SG.card ≤ (I_SG ∪ I_SG.image (fun k => k - 1)).card := by
    apply Finset.card_le_card
    intro x hx
    have h' := h_incl hx
    simp only [Finset.mem_union, Finset.mem_image] at h' ⊢
    exact h'
  have h_union : (I_SG ∪ I_SG.image (fun k => k - 1)).card ≤
      I_SG.card + (I_SG.image (fun k => k - 1)).card :=
    Finset.card_union_le _ _
  have h_image : (I_SG.image (fun k => k - 1)).card = I_SG.card := by
    apply Finset.card_image_of_injOn
    intro a _ b _ h; simpa using h
  rw [h_image] at h_union
  linarith

/-! ## Index set to real set -/

/-- The subset of A lying in the δ-cubes indexed by I. -/
def indexToRealSet (δ : ℝ) (I : Finset ℤ) (A : Set ℝ) : Set ℝ :=
  {x ∈ A | ∃ i ∈ I, x ∈ Set.Ico (δ * (i : ℝ)) (δ * ((i : ℝ) + 1))}

/-- Dyadic cubes of the same scale are disjoint. -/
lemma dyadic_cubes_disjoint1D {δ : ℝ} (hδ : 0 < δ) {i j : ℤ}
    {x : ℝ} (hxi : x ∈ Set.Ico (δ * (i : ℝ)) (δ * ((i : ℝ) + 1)))
    (hxj : x ∈ Set.Ico (δ * (j : ℝ)) (δ * ((j : ℝ) + 1))) : i = j := by
  by_contra h
  have h_cases : i < j ∨ j < i := by omega
  rcases h_cases with (hlt | hlt)
  · have h1 : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hlt
    have h2 : x < δ * ((i : ℝ) + 1) := hxi.2
    have h3 : δ * (j : ℝ) ≤ x := hxj.1
    have h4 : δ * ((i : ℝ) + 1) ≤ δ * (j : ℝ) := by gcongr <;> linarith
    linarith
  · have h1 : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hlt
    have h2 : x < δ * ((j : ℝ) + 1) := hxj.2
    have h3 : δ * (i : ℝ) ≤ x := hxi.1
    have h4 : δ * ((j : ℝ) + 1) ≤ δ * (i : ℝ) := by gcongr <;> linarith
    linarith

/-- If I ⊆ realCubeIndexSet δ A, then the covering number of indexToRealSet
equals |I|. -/
lemma indexToRealSet_covering {δ : ℝ} (hδ : 0 < δ) {I : Finset ℤ} {A : Set ℝ}
    (hI : (I : Set ℤ) ⊆ realCubeIndexSet δ A) :
    realCubeIndexSet δ (indexToRealSet δ I A) = (I : Set ℤ) := by
  ext k
  simp only [indexToRealSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hxk, hx_A'⟩
    rcases hx_A' with ⟨hx_A, ⟨i, hiI, hxi⟩⟩
    have h_eq : k = i := dyadic_cubes_disjoint1D hδ hxk hxi
    rw [h_eq]; exact hiI
  · intro hk
    have h1 : k ∈ realCubeIndexSet δ A := hI hk
    rcases h1 with ⟨x, hx_cube, hx_A⟩
    have h_x_in : x ∈ indexToRealSet δ I A := by
      simp only [indexToRealSet, Set.mem_setOf_eq]
      exact ⟨hx_A, k, hk, hx_cube⟩
    exact ⟨x, hx_cube, h_x_in⟩

/-! ## Sumset bound for output sets -/

/-- If A' is a union of cubes indexed by AI and B' by BI, then
N_δ(A'+B') ≤ 2 * |AI + BI|. -/
lemma output_sumset_bound {δ : ℝ} (hδ : 0 < δ) {AI BI : Finset ℤ}
    {A B : Set ℝ} (hA_bdd : Bornology.IsBounded A) (hB_bdd : Bornology.IsBounded B)
    (hAI : (AI : Set ℤ) ⊆ realCubeIndexSet δ A)
    (hBI : (BI : Set ℤ) ⊆ realCubeIndexSet δ B)
    {S : Set ℝ} (hS : Bornology.IsBounded S)
    (hS_eq : S = indexToRealSet δ AI A + indexToRealSet δ BI B) :
    (realCubeIndexFinset δ hδ hS).card ≤ 2 * (AI + BI).card := by
  let A' := indexToRealSet δ AI A
  let B' := indexToRealSet δ BI B
  have hA'_sub : A' ⊆ A := by intro x hx; exact hx.1
  have hB'_sub : B' ⊆ B := by intro x hx; exact hx.1
  have hA'_bdd : Bornology.IsBounded A' := hA_bdd.subset hA'_sub
  have hB'_bdd : Bornology.IsBounded B' := hB_bdd.subset hB'_sub
  have hS' : Bornology.IsBounded (A' + B') := bounded_image2_add hA'_bdd hB'_bdd
  have h_eq : (realCubeIndexFinset δ hδ hS).card = (realCubeIndexFinset δ hδ hS').card := by
    congr
    <;> rw [hS_eq]
  rw [h_eq]
  let S := AI + BI
  have h_incl : realCubeIndexSet δ (A' + B') ⊆
      (S : Set ℤ) ∪ (fun k : ℤ => k + 1) '' (S : Set ℤ) := by
    intro k hk
    rcases hk with ⟨z, hz_cube, hz_sum⟩
    rcases hz_sum with ⟨x, hx_A', y, hy_B', h_eq⟩
    rcases hx_A' with ⟨hx_A, ⟨i, hiI, hxi⟩⟩
    rcases hy_B' with ⟨hy_B, ⟨j, hjI, hyj⟩⟩
    let s : ℤ := i + j
    have hs : s ∈ (S : Set ℤ) := Finset.mem_add.mpr ⟨i, hiI, j, hjI, rfl⟩
    have hxi1 : δ * (i : ℝ) ≤ x := hxi.1
    have hxi2 : x < δ * ((i : ℝ) + 1) := hxi.2
    have hyj1 : δ * (j : ℝ) ≤ y := hyj.1
    have hyj2 : y < δ * ((j : ℝ) + 1) := hyj.2
    have h1 : δ * (s : ℝ) ≤ x + y := by
      have h11 : δ * (i : ℝ) + δ * (j : ℝ) ≤ x + y := by linarith
      have h12 : δ * ((s : ℝ)) = δ * (i : ℝ) + δ * (j : ℝ) := by
        simp [s] <;> ring
      rw [h12]; exact h11
    have h2 : x + y < δ * ((s : ℝ) + 2) := by
      have h21 : x + y < δ * ((i : ℝ) + 1) + δ * ((j : ℝ) + 1) := by linarith
      have h22 : δ * ((i : ℝ) + 1) + δ * ((j : ℝ) + 1) = δ * ((s : ℝ) + 2) := by
        have h23 : s = i + j := by rfl
        simp [h23, mul_add] <;> ring
      calc x + y
        < δ * ((i : ℝ) + 1) + δ * ((j : ℝ) + 1) := h21
      _ = δ * ((s : ℝ) + 2) := h22
    have hz1 : δ * (k : ℝ) ≤ z := hz_cube.1
    have h_z_eq : z = x + y := h_eq.symm
    have h3 : (s : ℝ) < (k : ℝ) + 1 := by
      have h31 : δ * (s : ℝ) ≤ z := by rw [h_z_eq]; exact h1
      have hz2 : z < δ * ((k : ℝ) + 1) := hz_cube.2
      have h32 : δ * (s : ℝ) < δ * ((k : ℝ) + 1) := lt_of_le_of_lt h31 hz2
      calc (s : ℝ)
        = (δ * (s : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
      _ < (δ * ((k : ℝ) + 1)) / δ := by gcongr
      _ = (k : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
    have h4 : (k : ℝ) < (s : ℝ) + 2 := by
      have h41 : δ * (k : ℝ) ≤ x + y := by
        calc δ * (k : ℝ) ≤ z := hz1
             _ = x + y := h_z_eq
      have h42 : δ * (k : ℝ) < δ * ((s : ℝ) + 2) := lt_of_le_of_lt h41 h2
      calc (k : ℝ)
        = (δ * (k : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
      _ < (δ * ((s : ℝ) + 2)) / δ := by gcongr
      _ = (s : ℝ) + 2 := by field_simp [hδ.ne'] <;> ring
    have h51 : s ≤ k := by
      by_contra h
      have h' : k < s := by omega
      have h2 : k + 1 ≤ s := by omega
      have h3' : (k : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast h2
      linarith
    have h52 : k ≤ s + 1 := by
      by_contra h
      have h' : s + 1 < k := by omega
      have h2 : s + 2 ≤ k := by omega
      have h3' : (s : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast h2
      linarith
    have h5 : k = s ∨ k = s + 1 := by omega
    rcases h5 with (h5 | h5)
    · left; rw [h5]; exact hs
    · right; exact ⟨s, hs, Eq.symm h5⟩
  let hS_bdd : Bornology.IsBounded (A' + B') := bounded_image2_add hA'_bdd hB'_bdd
  let I_SG := realCubeIndexFinset δ hδ hS_bdd
  have hI_SG_eq : (I_SG : Set ℤ) = realCubeIndexSet δ (A' + B') := by
    simp [I_SG, realCubeIndexFinset]
  have h_card : I_SG.card ≤ (S ∪ S.image (fun k => k + 1)).card := by
    apply Finset.card_le_card
    intro x hx
    have h_x_in_set : x ∈ realCubeIndexSet δ (A' + B') := by
      rw [←hI_SG_eq]; exact hx
    have h' := h_incl h_x_in_set
    simp only [Finset.mem_union, Finset.mem_image] at h' ⊢
    exact h'
  have h_union : (S ∪ S.image (fun k => k + 1)).card ≤
      S.card + (S.image (fun k => k + 1)).card :=
    Finset.card_union_le _ _
  have h_image : (S.image (fun k => k + 1)).card = S.card := by
    apply Finset.card_image_of_injOn
    intro a _ b _ h; simpa using h
  rw [h_image] at h_union
  have h_final : I_SG.card ≤ 2 * S.card := by linarith
  exact h_final

/-! ## Product index set of intersection -/

/-- If AI ⊆ I(A) and BI ⊆ I(B), then the product index set of
G ∩ (A'×B') equals IG ∩ (AI ×ˢ BI). -/
lemma intersection_indexSet {δ : ℝ} (hδ : 0 < δ) {G : Set (ℝ × ℝ)}
    {A B : Set ℝ} {AI BI : Finset ℤ}
    (hAI : (AI : Set ℤ) ⊆ realCubeIndexSet δ A)
    (hBI : (BI : Set ℤ) ⊆ realCubeIndexSet δ B)
    (hG_sub : G ⊆ Set.prod A B) :
    productIndexSet δ (G ∩ Set.prod (indexToRealSet δ AI A) (indexToRealSet δ BI B)) =
      (productIndexSet δ G) ∩ ((AI : Set ℤ) ×ˢ (BI : Set ℤ)) := by
  ext ⟨i, j⟩
  simp only [productIndexSet, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_prod]
  constructor
  · intro h
    rcases h with ⟨z, hz_cube, hzG⟩
    let x := z.1
    let y := z.2
    have hx1 : δ * (i : ℝ) ≤ x := hz_cube.1.1
    have hx2 : x < δ * ((i : ℝ) + 1) := hz_cube.1.2
    have hy1 : δ * (j : ℝ) ≤ y := hz_cube.2.1
    have hy2 : y < δ * ((j : ℝ) + 1) := hz_cube.2.2
    have hxyG : z ∈ G := hzG.1
    have hx_A' : x ∈ indexToRealSet δ AI A := hzG.2.1
    have hy_B' : y ∈ indexToRealSet δ BI B := hzG.2.2
    have h_i_AI : i ∈ (AI : Set ℤ) := by
      rcases hx_A' with ⟨_, ⟨i', hi'I, hxi'⟩⟩
      have h_eq : i = i' := dyadic_cubes_disjoint1D hδ ⟨hx1, hx2⟩ hxi'
      rw [h_eq]; exact hi'I
    have h_j_BI : j ∈ (BI : Set ℤ) := by
      rcases hy_B' with ⟨_, ⟨j', hj'I, hyj'⟩⟩
      have h_eq : j = j' := dyadic_cubes_disjoint1D hδ ⟨hy1, hy2⟩ hyj'
      rw [h_eq]; exact hj'I
    exact ⟨⟨z, hz_cube, hxyG⟩, ⟨h_i_AI, h_j_BI⟩⟩
  · rintro ⟨⟨z, hz_cube, hxyG⟩, ⟨hiI, hjI⟩⟩
    let x := z.1
    let y := z.2
    have hx1 : δ * (i : ℝ) ≤ x := hz_cube.1.1
    have hx2 : x < δ * ((i : ℝ) + 1) := hz_cube.1.2
    have hy1 : δ * (j : ℝ) ≤ y := hz_cube.2.1
    have hy2 : y < δ * ((j : ℝ) + 1) := hz_cube.2.2
    have hxA : x ∈ A := (hG_sub hxyG).1
    have hyB : y ∈ B := (hG_sub hxyG).2
    have hx_A' : x ∈ indexToRealSet δ AI A := by
      exact ⟨hxA, i, hiI, ⟨hx1, hx2⟩⟩
    have hy_B' : y ∈ indexToRealSet δ BI B := by
      exact ⟨hyB, j, hjI, ⟨hy1, hy2⟩⟩
    exact ⟨z, hz_cube, ⟨hxyG, ⟨hx_A', hy_B'⟩⟩⟩

/-! ## Main theorem -/

/-- Discretized Balog-Szemerédi-Gowers theorem.

Given bounded A, B ⊂ ℝ, G ⊂ A × B, K > 1 with:
- |G|_δ ≥ |A|_δ · |B|_δ / K  (density)
- |A +^G B|_δ ≤ K · sqrt(|A|_δ · |B|_δ)  (small restricted sumset)

Then there exist A' ⊂ A, B' ⊂ B with:
- |A'|_δ ≥ K^{-10}/3^{10} · |A|_δ
- |B'|_δ ≥ K^{-10}/3^{10} · |B|_δ
- |A'+B'|_δ ≤ 2^{13}·3^{10}·K^{10} · sqrt(|A|_δ·|B|_δ)
- |G ∩ (A'×B')|_δ ≥ K^{-22}/(16·3^{22}) · |A|_δ·|B|_δ

All cardinalities are given as real numbers (use `.card` of index sets).
-/
theorem discretized_bsg
    {δ : ℝ} (hδ : 0 < δ)
    {A B : Set ℝ} (hA_bdd : Bornology.IsBounded A)
    (hB_bdd : Bornology.IsBounded B)
    {G : Set (ℝ × ℝ)} (hG_bdd : Bornology.IsBounded G)
    (hG_sub : G ⊆ Set.prod A B)
    {K : ℝ} (hK : 1 < K)
    (h_density : (realCubeIndexFinset δ hδ hA_bdd).card * (realCubeIndexFinset δ hδ hB_bdd).card ≤
        K * (productIndexFinset δ hδ hG_bdd).card)
    (h_sumset : (restrictedSumIndexFinset δ hδ hG_bdd).card ≤
        K * Real.sqrt ((realCubeIndexFinset δ hδ hA_bdd).card *
          (realCubeIndexFinset δ hδ hB_bdd).card)) :
    ∃ (AI BI : Finset ℤ),
      AI ⊆ realCubeIndexFinset δ hδ hA_bdd ∧
      BI ⊆ realCubeIndexFinset δ hδ hB_bdd ∧
      (AI.card : ℝ) ≥ 1 / (K^10 * (3 : ℝ)^10) * (realCubeIndexFinset δ hδ hA_bdd).card ∧
      (BI.card : ℝ) ≥ 1 / (K^10 * (3 : ℝ)^10) * (realCubeIndexFinset δ hδ hB_bdd).card ∧
      let A' := indexToRealSet δ AI A
      let B' := indexToRealSet δ BI B
      let hA'_bdd : Bornology.IsBounded A' := hA_bdd.subset (fun x hx => hx.1)
      let hB'_bdd : Bornology.IsBounded B' := hB_bdd.subset (fun x hx => hx.1)
      let hS_bdd : Bornology.IsBounded (A' + B') := bounded_image2_add hA'_bdd hB'_bdd
      (realCubeIndexFinset δ hδ hS_bdd).card ≤
        (2 : ℝ)^13 * (3 : ℝ)^10 * K^10 * Real.sqrt ((realCubeIndexFinset δ hδ hA_bdd).card *
          (realCubeIndexFinset δ hδ hB_bdd).card) ∧
      let A' := indexToRealSet δ AI A
      let B' := indexToRealSet δ BI B
      let G' := G ∩ Set.prod A' B'
      let hG'_bdd : Bornology.IsBounded G' := hG_bdd.subset (fun x hx => hx.1)
      (productIndexFinset δ hδ hG'_bdd).card ≥
        1 / ((16 : ℝ) * K^22 * (3 : ℝ)^22) * (realCubeIndexFinset δ hδ hA_bdd).card *
          (realCubeIndexFinset δ hδ hB_bdd).card := by
  let IA := realCubeIndexFinset δ hδ hA_bdd
  let IB := realCubeIndexFinset δ hδ hB_bdd
  let IG := productIndexFinset δ hδ hG_bdd
  let ISG := restrictedSumIndexFinset δ hδ hG_bdd
  let FSG := IG.image (fun p : ℤ × ℤ => p.1 + p.2)
  have hIG_sub : (IG : Set (ℤ × ℤ)) ⊆ (IA : Set ℤ) ×ˢ (IB : Set ℤ) := by
    intro p hp
    have hpm : p ∈ productIndexSet δ G := by
      simpa [IG, productIndexFinset] using hp
    rcases hpm with ⟨z, hz_cube, hzG⟩
    let x := z.1
    let y := z.2
    have hx_cube : x ∈ Set.Ico (δ * (p.1 : ℝ)) (δ * ((p.1 : ℝ) + 1)) := hz_cube.1
    have hy_cube : y ∈ Set.Ico (δ * (p.2 : ℝ)) (δ * ((p.2 : ℝ) + 1)) := hz_cube.2
    have hxA : x ∈ A := (hG_sub hzG).1
    have hyB : y ∈ B := (hG_sub hzG).2
    have h1 : p.1 ∈ realCubeIndexSet δ A := ⟨x, hx_cube, hxA⟩
    have h2 : p.2 ∈ realCubeIndexSet δ B := ⟨y, hy_cube, hyB⟩
    have hIA_eq : (IA : Set ℤ) = realCubeIndexSet δ A := by simp [IA, realCubeIndexFinset]
    have hIB_eq : (IB : Set ℤ) = realCubeIndexSet δ B := by simp [IB, realCubeIndexFinset]
    exact ⟨by rw [hIA_eq]; exact h1, by rw [hIB_eq]; exact h2⟩
  let K_bsg : ℕ := Int.toNat (Int.ceil (2 * K))
  have hK_bsg_pos : 0 < K_bsg := by
    have h1 : (2 : ℝ) < 2 * K := by linarith
    have h2 : (Int.ceil (2 * K) : ℝ) > 2 := by
      have h3 : (2 * K : ℝ) ≤ (Int.ceil (2 * K) : ℝ) := Int.le_ceil (2 * K)
      linarith
    have h4 : 3 ≤ Int.ceil (2 * K) := by
      by_contra h5
      have h6 : Int.ceil (2 * K) ≤ 2 := by omega
      have h7 : (Int.ceil (2 * K) : ℝ) ≤ 2 := by exact_mod_cast h6
      linarith
    have h5 : 0 < Int.ceil (2 * K) := by linarith
    have h6 : 0 < Int.toNat (Int.ceil (2 * K)) := by
      exact Int.pos_iff_toNat_pos.mp h5
    simpa [K_bsg] using h6
  have h_ceil_nonneg : 0 ≤ Int.ceil (2 * K) := by
    have h1 : (0 : ℝ) < 2 * K := by linarith
    have h2 : (0 : ℝ) ≤ (Int.ceil (2 * K) : ℝ) := by
      have h3 : (2 * K : ℝ) ≤ (Int.ceil (2 * K) : ℝ) := Int.le_ceil (2 * K)
      linarith
    exact_mod_cast h2
  have hK_bsg_eq : (K_bsg : ℝ) = (Int.ceil (2 * K) : ℝ) := by
    have h_pos : 0 ≤ Int.ceil (2 * K) := h_ceil_nonneg
    have h1 : Int.toNat (Int.ceil (2 * K)) = Int.ceil (2 * K) := by
      exact Int.toNat_of_nonneg h_ceil_nonneg
    simp [K_bsg, h1] <;> norm_cast
  have hK_bsg1 : (K_bsg : ℝ) ≥ 2 * K := by
    rw [hK_bsg_eq]
    exact Int.le_ceil (2 * K)
  have hK_bsg2 : (K_bsg : ℝ) ≤ 3 * K := by
    rw [hK_bsg_eq]
    have h1 : (Int.ceil (2 * K) : ℝ) < 2 * K + 1 := Int.ceil_lt_add_one (2 * K)
    have h2 : 2 * K + 1 ≤ 3 * K := by linarith
    linarith
  have h_density' : (IA.card : ℝ) * (IB.card : ℝ) ≤ (K_bsg : ℝ) * (IG.card : ℝ) := by
    have h : (K : ℝ) ≤ (K_bsg : ℝ) := by linarith
    calc (IA.card : ℝ) * (IB.card : ℝ)
      ≤ K * (IG.card : ℝ) := h_density
    _ ≤ (K_bsg : ℝ) * (IG.card : ℝ) := by gcongr
  have h_sumset1 : FSG.card ≤ 2 * ISG.card :=
    finite_sumset_le_two_cover hδ hG_bdd
  have h_sumset' : FSG.card ≤ (K_bsg : ℝ) * Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ)) := by
    have h1 : (FSG.card : ℝ) ≤ 2 * (ISG.card : ℝ) := by exact_mod_cast h_sumset1
    have h2 : (ISG.card : ℝ) ≤ K * Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ)) := h_sumset
    calc (FSG.card : ℝ)
      ≤ 2 * (ISG.card : ℝ) := h1
    _ ≤ 2 * K * Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ)) := by
      have h2' : 2 * (ISG.card : ℝ) ≤ 2 * (K * Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ))) := by gcongr
      have h3 : 2 * (K * Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ))) = 2 * K * Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ)) := by ring
      rw [h3] at h2'
      exact h2'
    _ ≤ (K_bsg : ℝ) * Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ)) := by
      have h3 : 2 * K ≤ (K_bsg : ℝ) := by linarith
      have h4 : 0 ≤ Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ)) := Real.sqrt_nonneg _
      exact mul_le_mul_of_nonneg_right h3 h4
  have h_FSG_eq : AdditiveCombinatorics.BSG.restrictedSum IA IB IG = FSG := by
    simp [AdditiveCombinatorics.BSG.restrictedSum, FSG]
  have h_sumset'' : (AdditiveCombinatorics.BSG.restrictedSum IA IB IG).card ≤
      (K_bsg : ℝ) * Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ)) := by
    rw [h_FSG_eq]
    exact h_sumset'
  have hIG_sub' : IG ⊆ IA ×ˢ IB := by
    intro p hp
    have h : p ∈ (IG : Set (ℤ × ℤ)) := hp
    have h' : p ∈ (IA : Set ℤ) ×ˢ (IB : Set ℤ) := hIG_sub h
    simpa [Finset.mem_product] using h'
  rcases AdditiveCombinatorics.BSG.balog_szemeredi_gowers_dense
      IA IB IG hIG_sub' K_bsg (by linarith) h_density' h_sumset'' with
    ⟨AI', BI', hAI'_sub, hBI'_sub, hAI'_card, hBI'_card, h_sum_card, h_inter_card⟩
  let A' := indexToRealSet δ AI' A
  let B' := indexToRealSet δ BI' B
  have hA'_sub : A' ⊆ A := by intro x hx; exact hx.1
  have hB'_sub : B' ⊆ B := by intro x hx; exact hx.1
  have hA'_bdd : Bornology.IsBounded A' := hA_bdd.subset hA'_sub
  have hB'_bdd : Bornology.IsBounded B' := hB_bdd.subset hB'_sub
  have hAI'_incl : (AI' : Set ℤ) ⊆ realCubeIndexSet δ A := by
    intro i hi
    have h1 : i ∈ IA := hAI'_sub hi
    have h2 : (IA : Set ℤ) = realCubeIndexSet δ A := by
      simp [IA, realCubeIndexFinset]
    rw [←h2]
    exact h1
  have hBI'_incl : (BI' : Set ℤ) ⊆ realCubeIndexSet δ B := by
    intro j hj
    have h1 : j ∈ IB := hBI'_sub hj
    have h2 : (IB : Set ℤ) = realCubeIndexSet δ B := by
      simp [IB, realCubeIndexFinset]
    rw [←h2]
    exact h1
  have hA'B'_bound := output_sumset_bound hδ hA_bdd hB_bdd hAI'_incl hBI'_incl
    (S := A' + B') (bounded_image2_add hA'_bdd hB'_bdd) (by simp [A', B'])
  have hG'_bdd : Bornology.IsBounded (G ∩ Set.prod A' B') :=
    hG_bdd.subset (fun x hx => hx.1)
  have h_inter_index : productIndexSet δ (G ∩ Set.prod A' B') =
      (productIndexSet δ G) ∩ ((AI' : Set ℤ) ×ˢ (BI' : Set ℤ)) :=
    intersection_indexSet hδ hAI'_incl hBI'_incl hG_sub
  have h_nG'_eq : (productIndexFinset δ hδ hG'_bdd).card =
      (IG ∩ (AI' ×ˢ BI')).card := by
    have h_coe : (productIndexFinset δ hδ hG'_bdd : Set (ℤ × ℤ)) =
        (IG ∩ (AI' ×ˢ BI') : Set (ℤ × ℤ)) := by
      simp [productIndexFinset, h_inter_index, IG]
      <;> rfl
    have h_eq : productIndexFinset δ hδ hG'_bdd = IG ∩ (AI' ×ˢ BI') := by
      apply Finset.ext
      intro x
      have h_set : (productIndexFinset δ hδ hG'_bdd : Set (ℤ × ℤ)) = ((IG ∩ (AI' ×ˢ BI')) : Set (ℤ × ℤ)) := h_coe
      have h_iff : (x ∈ productIndexFinset δ hδ hG'_bdd) ↔ (x ∈ IG ∩ (AI' ×ˢ BI')) := by
        simpa [Finset.mem_coe] using congr_arg (fun (s : Set (ℤ × ℤ)) => x ∈ s) h_set
      exact h_iff
    rw [h_eq]
  have h1 : (AI'.card : ℝ) ≥ 1 / (K_bsg : ℝ)^10 * (IA.card : ℝ) := by
    exact_mod_cast hAI'_card
  have h2 : (BI'.card : ℝ) ≥ 1 / (K_bsg : ℝ)^10 * (IB.card : ℝ) := by
    exact_mod_cast hBI'_card
  have h3 : (realCubeIndexFinset δ hδ (bounded_image2_add hA'_bdd hB'_bdd)).card ≤
      2 * ((AI' + BI').card : ℝ) := by
    exact_mod_cast hA'B'_bound
  have h4 : ((AI' + BI').card : ℝ) ≤ (2 : ℝ)^12 * (K_bsg : ℝ)^10 *
      Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ)) := by
    exact_mod_cast h_sum_card
  have h5 : (productIndexFinset δ hδ hG'_bdd).card ≥
      (AI'.card : ℝ) * (BI'.card : ℝ) / (16 * (K_bsg : ℝ)^2) := by
    rw [h_nG'_eq]
    exact_mod_cast h_inter_card
  have h1' : (AI'.card : ℝ) ≥ 1 / (K^10 * (3 : ℝ)^10) * (IA.card : ℝ) := by
    have h6 : (K_bsg : ℝ)^10 ≤ (3 * K)^10 := by gcongr <;> linarith
    have h_pos : 0 ≤ (IA.card : ℝ) := by positivity
    calc (AI'.card : ℝ)
      ≥ 1 / (K_bsg : ℝ)^10 * (IA.card : ℝ) := h1
    _ ≥ 1 / ((3 * K)^10) * (IA.card : ℝ) := by gcongr
    _ = 1 / (K^10 * (3 : ℝ)^10) * (IA.card : ℝ) := by
        have h9 : (3 * K)^10 = K^10 * (3 : ℝ)^10 := by ring
        rw [h9]
  have h2' : (BI'.card : ℝ) ≥ 1 / (K^10 * (3 : ℝ)^10) * (IB.card : ℝ) := by
    have h6 : (K_bsg : ℝ)^10 ≤ (3 * K)^10 := by gcongr <;> linarith
    have h_pos : 0 ≤ (IB.card : ℝ) := by positivity
    calc (BI'.card : ℝ)
      ≥ 1 / (K_bsg : ℝ)^10 * (IB.card : ℝ) := h2
    _ ≥ 1 / ((3 * K)^10) * (IB.card : ℝ) := by gcongr
    _ = 1 / (K^10 * (3 : ℝ)^10) * (IB.card : ℝ) := by
        have h9 : (3 * K)^10 = K^10 * (3 : ℝ)^10 := by ring
        rw [h9]
  have h3' : (realCubeIndexFinset δ hδ (bounded_image2_add hA'_bdd hB'_bdd)).card ≤
      2^13 * 3^10 * K^10 * Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ)) := by
    have h9 : (K_bsg : ℝ)^10 ≤ (3 * K)^10 := by gcongr <;> linarith
    calc (realCubeIndexFinset δ hδ (bounded_image2_add hA'_bdd hB'_bdd)).card
      ≤ 2 * ((AI' + BI').card : ℝ) := h3
    _ ≤ 2 * ((2 : ℝ)^12 * (K_bsg : ℝ)^10 * Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ))) := by gcongr
    _ = 2^13 * (K_bsg : ℝ)^10 * Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ)) := by ring
    _ ≤ 2^13 * (3 * K)^10 * Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ)) := by gcongr
    _ = 2^13 * 3^10 * K^10 * Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ)) := by ring
  have h5' : (productIndexFinset δ hδ hG'_bdd).card ≥
      1 / ((16 : ℝ) * K^22 * (3 : ℝ)^22) * (IA.card : ℝ) * (IB.card : ℝ) := by
    have h12 : (productIndexFinset δ hδ hG'_bdd).card ≥
        (AI'.card : ℝ) * (BI'.card : ℝ) / (16 * (K_bsg : ℝ)^2) := h5
    have h13 : (AI'.card : ℝ) ≥ 1 / (K_bsg : ℝ)^10 * (IA.card : ℝ) := h1
    have h14 : (BI'.card : ℝ) ≥ 1 / (K_bsg : ℝ)^10 * (IB.card : ℝ) := h2
    have h15 : (productIndexFinset δ hδ hG'_bdd).card ≥
        (IA.card : ℝ) * (IB.card : ℝ) / (16 * (K_bsg : ℝ)^22) := by
      calc (productIndexFinset δ hδ hG'_bdd).card
        ≥ (AI'.card : ℝ) * (BI'.card : ℝ) / (16 * (K_bsg : ℝ)^2) := h12
      _ ≥ (1 / (K_bsg : ℝ)^10 * (IA.card : ℝ)) *
            (1 / (K_bsg : ℝ)^10 * (IB.card : ℝ)) / (16 * (K_bsg : ℝ)^2) := by gcongr
      _ = (IA.card : ℝ) * (IB.card : ℝ) / (16 * (K_bsg : ℝ)^22) := by ring
    have h16 : (K_bsg : ℝ)^22 ≤ (3 * K)^22 := by gcongr <;> linarith
    have h17 : 1 / (16 * (K_bsg : ℝ)^22) ≥ 1 / ((16 : ℝ) * K^22 * (3 : ℝ)^22) := by
      have h171 : (16 : ℝ) * (K_bsg : ℝ)^22 ≤ (16 : ℝ) * K^22 * (3 : ℝ)^22 := by
        calc (16 : ℝ) * (K_bsg : ℝ)^22
          ≤ (16 : ℝ) * (3 * K)^22 := by gcongr
        _ = (16 : ℝ) * K^22 * (3 : ℝ)^22 := by ring
      have h_pos1 : 0 < (16 : ℝ) * (K_bsg : ℝ)^22 := by positivity
      exact one_div_le_one_div_of_le h_pos1 h171
    have h18 : (productIndexFinset δ hδ hG'_bdd).card ≥
        (IA.card : ℝ) * (IB.card : ℝ) * (1 / ((16 : ℝ) * K^22 * (3 : ℝ)^22)) := by
      calc (productIndexFinset δ hδ hG'_bdd).card
        ≥ (IA.card : ℝ) * (IB.card : ℝ) / (16 * (K_bsg : ℝ)^22) := h15
      _ = (IA.card : ℝ) * (IB.card : ℝ) * (1 / (16 * (K_bsg : ℝ)^22)) := by ring
      _ ≥ (IA.card : ℝ) * (IB.card : ℝ) * (1 / ((16 : ℝ) * K^22 * (3 : ℝ)^22)) := by gcongr
    linarith
  exact ⟨AI', BI', hAI'_sub, hBI'_sub, h1', h2', h3', h5'⟩

end ProductLikeIncidence.DiscretizedBSG
