module

/-
# Discretized Plünnecke-Ruzsa inequality

Proves `discretized_pluennecke_ruzsa_diff`:
`N(X-X, δ) · N(Y, δ) ≤ 9 · N(X+Y, δ)^2`

for bounded subsets of ℝ, using dyadic covering numbers.

## Proof route

1. Associate to each bounded set S its set of δ-cube indices `I(S) : Set ℤ`.
2. Show N(S, δ) = |I(S)|.
3. Show I(X-X) ⊆ I(X) - I(X) + {-1, 0}, so |I(X-X)| ≤ 2·|I(X)-I(X)|.
4. Show I(X)+I(Y) ⊆ I(X+Y) + {-1, 0}, so |I(X)+I(Y)| ≤ 2·|I(X+Y)|.
5. Apply finite Ruzsa triangle: |I(X)-I(X)|·|I(Y)| ≤ |I(X)+I(Y)|².
6. Combine: N(X-X)·N(Y) ≤ 2·(2·N(X+Y))² = 8·N(X+Y)² ≤ 9·N(X+Y)².
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.Compat
public import MyLeanRepo.CubeIndexSet
public import MyLeanRepo.OSWPrelude
public import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

@[expose] public section

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence


/-! ## Index set inclusions -/

/-- If k indexes a cube meeting X-X, then k = i - j + e with i,j indexing X,
and e ∈ {-1, 0}. -/
lemma diff_self_index_inclusion {δ : ℝ} (hδ : 0 < δ) {X : Set ℝ} :
    realCubeIndexSet δ (Set.image2 (· - ·) X X) ⊆
      (realCubeIndexSet δ X - realCubeIndexSet δ X) + ({-1, 0} : Set ℤ) := by
  intro k hk
  rcases hk with ⟨w, hw⟩
  have hIco : w ∈ Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := hw.1
  have hImg : w ∈ Set.image2 (· - ·) X X := hw.2
  have hw1 : δ * (k : ℝ) ≤ w := hIco.1
  have hw2 : w < δ * ((k : ℝ) + 1) := hIco.2
  rcases hImg with ⟨x, hxX, y, hyY, rfl⟩
  let i : ℤ := Int.floor (x / δ)
  let j : ℤ := Int.floor (y / δ)
  have hi1 : δ * (i : ℝ) ≤ x := by
    have h : (i : ℝ) ≤ x / δ := Int.floor_le (x / δ)
    have h' : δ * (i : ℝ) ≤ δ * (x / δ) := by gcongr
    have h'' : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
    rw [h''] at h' <;> exact h'
  have hi2 : x < δ * ((i : ℝ) + 1) := by
    have h : x / δ < (i : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
    have h' : δ * (x / δ) < δ * ((i : ℝ) + 1) := by gcongr
    have h'' : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
    rw [h''] at h' <;> exact h'
  have hj1 : δ * (j : ℝ) ≤ y := by
    have h : (j : ℝ) ≤ y / δ := Int.floor_le (y / δ)
    have h' : δ * (j : ℝ) ≤ δ * (y / δ) := by gcongr
    have h'' : δ * (y / δ) = y := by field_simp [hδ.ne'] <;> ring
    rw [h''] at h' <;> exact h'
  have hj2 : y < δ * ((j : ℝ) + 1) := by
    have h : y / δ < (j : ℝ) + 1 := Int.lt_floor_add_one (y / δ)
    have h' : δ * (y / δ) < δ * ((j : ℝ) + 1) := by gcongr
    have h'' : δ * (y / δ) = y := by field_simp [hδ.ne'] <;> ring
    rw [h''] at h' <;> exact h'
  have hiX : i ∈ realCubeIndexSet δ X := by
    simp only [realCubeIndexSet, Set.mem_setOf_eq]
    exact ⟨x, ⟨hi1, hi2⟩, hxX⟩
  have hjX : j ∈ realCubeIndexSet δ X := by
    simp only [realCubeIndexSet, Set.mem_setOf_eq]
    exact ⟨y, ⟨hj1, hj2⟩, hyY⟩
  -- Upper bound: k ≤ i - j
  have h_k_upper : k ≤ i - j := by
    have h1 : x - y < δ * ((i : ℝ) + 1) - δ * (j : ℝ) := by linarith
    have h2 : x - y < δ * (((i - j : ℤ) : ℝ) + 1) := by
      have h_eq : δ * ((i : ℝ) + 1) - δ * (j : ℝ) = δ * (((i - j : ℤ) : ℝ) + 1) := by
        simp [sub_eq_add_neg] <;> ring
      rw [h_eq] at h1
      exact h1
    have h3 : δ * (k : ℝ) < δ * (((i - j : ℤ) : ℝ) + 1) := by
      calc δ * (k : ℝ) ≤ x - y := hw1
           _ < δ * (((i - j : ℤ) : ℝ) + 1) := h2
    have h4 : (k : ℝ) < ((i - j : ℤ) : ℝ) + 1 := by nlinarith
    have h5 : k < i - j + 1 := by exact_mod_cast h4
    omega
  -- Lower bound: i - j - 1 ≤ k
  have h_k_lower : i - j - 1 ≤ k := by
    have h1 : δ * (i : ℝ) - δ * ((j : ℝ) + 1) < x - y := by linarith
    have h2 : δ * (((i - j - 1 : ℤ) : ℝ)) < x - y := by
      have h_eq : δ * (i : ℝ) - δ * ((j : ℝ) + 1) = δ * (((i - j - 1 : ℤ) : ℝ)) := by
        simp [sub_eq_add_neg] <;> ring
      rw [h_eq] at h1
      exact h1
    have h3 : δ * (((i - j - 1 : ℤ) : ℝ)) < δ * ((k : ℝ) + 1) := by
      calc δ * (((i - j - 1 : ℤ) : ℝ)) < x - y := h2
           _ < δ * ((k : ℝ) + 1) := hw2
    have h4 : ((i - j - 1 : ℤ) : ℝ) < (k : ℝ) + 1 := by nlinarith
    have h5 : i - j - 1 < k + 1 := by exact_mod_cast h4
    have h6 : i - j - 1 ≤ k := by linarith
    exact h6
  have h_e3 : k - (i - j) ∈ ({-1, 0} : Set ℤ) := by
    have h6 : k - (i - j) ≤ 0 := by omega
    have h7 : -1 ≤ k - (i - j) := by omega
    have h8 : k - (i - j) = -1 ∨ k - (i - j) = 0 := by omega
    rcases h8 with (h8 | h8)
    · rw [h8] <;> simp
    · rw [h8] <;> simp
  have h_ij : i - j ∈ (realCubeIndexSet δ X - realCubeIndexSet δ X) := by
    exact ⟨i, hiX, j, hjX, rfl⟩
  have h_eq : (i - j) + (k - (i - j)) = k := by omega
  have h_goal : k ∈ (realCubeIndexSet δ X - realCubeIndexSet δ X) + ({-1, 0} : Set ℤ) := by
    have h : (i - j) + (k - (i - j)) ∈ (realCubeIndexSet δ X - realCubeIndexSet δ X) + ({-1, 0} : Set ℤ) := by
      exact ⟨i - j, h_ij, k - (i - j), h_e3, rfl⟩
    rw [h_eq] at h
    exact h
  exact h_goal

/-- If k = i + j with i indexing X and j indexing Y, then k ∈ I(X+Y) + {-1,0}. -/
lemma sum_index_inclusion {δ : ℝ} (hδ : 0 < δ) {X Y : Set ℝ} :
    (realCubeIndexSet δ X + realCubeIndexSet δ Y) ⊆
      realCubeIndexSet δ (Set.image2 (· + ·) X Y) + ({-1, 0} : Set ℤ) := by
  intro k hk
  rcases hk with ⟨i, hi, j, hj, rfl⟩
  rcases hi with ⟨x, hx⟩
  have hxIco : x ∈ Set.Ico (δ * (i : ℝ)) (δ * ((i : ℝ) + 1)) := hx.1
  have hxX : x ∈ X := hx.2
  have hx1 : δ * (i : ℝ) ≤ x := hxIco.1
  have hx2 : x < δ * ((i : ℝ) + 1) := hxIco.2
  rcases hj with ⟨z, hz⟩
  have hzIco : z ∈ Set.Ico (δ * (j : ℝ)) (δ * ((j : ℝ) + 1)) := hz.1
  have hzZ : z ∈ Y := hz.2
  have hz1 : δ * (j : ℝ) ≤ z := hzIco.1
  have hz2 : z < δ * ((j : ℝ) + 1) := hzIco.2
  -- Bounds on x + z
  have h_sum1 : δ * ((i + j : ℤ) : ℝ) ≤ x + z := by
    have h1 : δ * (i : ℝ) ≤ x := hx1
    have h2 : δ * (j : ℝ) ≤ z := hz1
    have h3 : δ * ((i + j : ℤ) : ℝ) = δ * (i : ℝ) + δ * (j : ℝ) := by
      simp [add_mul] <;> ring
    rw [h3]
    linarith
  have h_sum_upper : x + z < δ * (((i + j : ℤ) : ℝ) + 2) := by
    have h1 : x < δ * ((i : ℝ) + 1) := hx2
    have h2 : z < δ * ((j : ℝ) + 1) := hz2
    have h3 : δ * (((i + j : ℤ) : ℝ) + 2) = δ * ((i : ℝ) + 1) + δ * ((j : ℝ) + 1) := by
      simp [add_mul] <;> ring
    rw [h3]
    linarith
  by_cases h_case : x + z < δ * (((i + j : ℤ) : ℝ) + 1)
  · -- Case 1: x+z is in cube i+j
    have h_alt : (i + j : ℤ) ∈ realCubeIndexSet δ (Set.image2 (· + ·) X Y) := by
      simp only [realCubeIndexSet, Set.mem_setOf_eq]
      exact ⟨x + z, ⟨h_sum1, h_case⟩, ⟨x, hxX, z, hzZ, rfl⟩⟩
    have h_zero : (0 : ℤ) ∈ ({-1, 0} : Set ℤ) := by simp
    have h_goal : (i + j : ℤ) + (0 : ℤ) ∈ realCubeIndexSet δ (Set.image2 (· + ·) X Y) + ({-1, 0} : Set ℤ) := by
      exact ⟨i + j, h_alt, (0 : ℤ), h_zero, rfl⟩
    simpa using h_goal
  · -- Case 2: x+z ≥ δ*(i+j+1), so it's in cube i+j+1
    have h_ge : δ * (((i + j : ℤ) : ℝ) + 1) ≤ x + z := by linarith
    let m : ℤ := i + j + 1
    have hm1 : δ * (m : ℝ) ≤ x + z := by
      have h_eq : (m : ℝ) = ((i + j : ℤ) : ℝ) + 1 := by
        simp [m] <;> ring
      rw [h_eq]
      exact h_ge
    have hm2 : x + z < δ * ((m : ℝ) + 1) := by
      have h_eq : (m : ℝ) + 1 = ((i + j : ℤ) : ℝ) + 2 := by
        simp [m] <;> ring
      rw [h_eq]
      exact h_sum_upper
    have h_m_in : m ∈ realCubeIndexSet δ (Set.image2 (· + ·) X Y) := by
      simp only [realCubeIndexSet, Set.mem_setOf_eq]
      exact ⟨x + z, ⟨hm1, hm2⟩, ⟨x, hxX, z, hzZ, rfl⟩⟩
    have h_neg : (-1 : ℤ) ∈ ({-1, 0} : Set ℤ) := by simp
    have h_eq : m + (-1 : ℤ) = (i + j : ℤ) := by simp [m] <;> omega
    have h_goal : m + (-1 : ℤ) ∈ realCubeIndexSet δ (Set.image2 (· + ·) X Y) + ({-1, 0} : Set ℤ) := by
      exact ⟨m, h_m_in, (-1 : ℤ), h_neg, rfl⟩
    rw [h_eq] at h_goal
    simpa using h_goal

/-- Reverse sum index inclusion: if k indexes a cube meeting X+Y, then
k ∈ I(X) + I(Y) + {0, 1}. -/
lemma sum_index_inclusion_rev {δ : ℝ} (hδ : 0 < δ) {X Y : Set ℝ} :
    realCubeIndexSet δ (Set.image2 (· + ·) X Y) ⊆
      realCubeIndexSet δ X + realCubeIndexSet δ Y + ({0, 1} : Set ℤ) := by
  intro k hk
  rcases hk with ⟨w, hw⟩
  have hIco : w ∈ Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := hw.1
  have hImg : w ∈ Set.image2 (· + ·) X Y := hw.2
  have hw1 : δ * (k : ℝ) ≤ w := hIco.1
  have hw2 : w < δ * ((k : ℝ) + 1) := hIco.2
  rcases hImg with ⟨x, hxX, y, hyY, h_eq⟩
  have hxy : w = x + y := Eq.symm h_eq
  have h1 : δ * (k : ℝ) ≤ x + y := by
    rw [←hxy]; exact hw1
  have h2 : x + y < δ * ((k : ℝ) + 1) := by
    rw [←hxy]; exact hw2
  let i : ℤ := Int.floor (x / δ)
  let j : ℤ := Int.floor (y / δ)
  have hi1 : δ * (i : ℝ) ≤ x := by
    have h : (i : ℝ) ≤ x / δ := Int.floor_le (x / δ)
    have h2 : δ * (i : ℝ) ≤ δ * (x / δ) := by gcongr
    have h3 : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
    rw [h3] at h2; exact h2
  have hi2 : x < δ * ((i : ℝ) + 1) := by
    have h : x / δ < (i : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
    have h2 : δ * (x / δ) < δ * ((i : ℝ) + 1) := by gcongr
    have h3 : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
    rw [h3] at h2; exact h2
  have hj1 : δ * (j : ℝ) ≤ y := by
    have h : (j : ℝ) ≤ y / δ := Int.floor_le (y / δ)
    have h2 : δ * (j : ℝ) ≤ δ * (y / δ) := by gcongr
    have h3 : δ * (y / δ) = y := by field_simp [hδ.ne'] <;> ring
    rw [h3] at h2; exact h2
  have hj2 : y < δ * ((j : ℝ) + 1) := by
    have h : y / δ < (j : ℝ) + 1 := Int.lt_floor_add_one (y / δ)
    have h2 : δ * (y / δ) < δ * ((j : ℝ) + 1) := by gcongr
    have h3 : δ * (y / δ) = y := by field_simp [hδ.ne'] <;> ring
    rw [h3] at h2; exact h2
  have hi_in : i ∈ realCubeIndexSet δ X := by
    simp only [realCubeIndexSet, Set.mem_setOf_eq]
    exact ⟨x, ⟨hi1, hi2⟩, hxX⟩
  have hj_in : j ∈ realCubeIndexSet δ Y := by
    simp only [realCubeIndexSet, Set.mem_setOf_eq]
    exact ⟨y, ⟨hj1, hj2⟩, hyY⟩
  have h_lower1 : δ * ((i + j : ℤ) : ℝ) ≤ x + y := by
    have h4 : δ * ((i + j : ℤ) : ℝ) = δ * (i : ℝ) + δ * (j : ℝ) := by simp [add_mul] <;> ring
    rw [h4]; linarith
  have h_upper1 : x + y < δ * (((i + j : ℤ) : ℝ) + 2) := by
    have h4 : δ * (((i + j : ℤ) : ℝ) + 2) = δ * ((i : ℝ) + 1) + δ * ((j : ℝ) + 1) := by
      simp [add_mul] <;> ring
    rw [h4]; linarith
  have h_k_ge : (i + j : ℤ) ≤ k := by
    have h_a : (i + j : ℝ) ≤ (x + y) / δ := by
      have h : δ * ((i + j : ℤ) : ℝ) ≤ x + y := h_lower1
      have h' : ((i + j : ℤ) : ℝ) ≤ (x + y) / δ := by
        calc ((i + j : ℤ) : ℝ)
          = (δ * ((i + j : ℤ) : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
        _ ≤ (x + y) / δ := by gcongr
      have h_eq : ((i + j : ℤ) : ℝ) = (i + j : ℝ) := by simp [Int.cast_add]
      rw [h_eq] at h'
      exact h'
    have h_b : (x + y) / δ < (k : ℝ) + 1 := by
      have h : x + y < δ * ((k : ℝ) + 1) := h2
      have h' : (x + y) / δ < (k : ℝ) + 1 := by
        calc (x + y) / δ
          < (δ * ((k : ℝ) + 1)) / δ := by gcongr
        _ = (k : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
      exact h'
    have h_c : (i + j : ℝ) < (k : ℝ) + 1 := by linarith
    have h_d : i + j < k + 1 := by exact_mod_cast h_c
    omega
  have h_k_le : k ≤ i + j + 1 := by
    have h_a : (k : ℝ) ≤ (x + y) / δ := by
      have h : δ * (k : ℝ) ≤ x + y := h1
      have h' : (k : ℝ) ≤ (x + y) / δ := by
        calc (k : ℝ)
          = (δ * (k : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
        _ ≤ (x + y) / δ := by gcongr
      exact h'
    have h_b : (x + y) / δ < ((i + j : ℝ) + 2) := by
      have h : x + y < δ * (((i + j : ℤ) : ℝ) + 2) := h_upper1
      have h' : (x + y) / δ < ((i + j : ℝ) + 2) := by
        calc (x + y) / δ
          < (δ * (((i + j : ℤ) : ℝ) + 2)) / δ := by gcongr
        _ = ((i + j : ℝ) + 2) := by field_simp [hδ.ne'] <;> norm_cast <;> ring
      exact h'
    have h_c : (k : ℝ) < (i + j : ℝ) + 2 := by linarith
    have h_d : k < i + j + 2 := by exact_mod_cast h_c
    omega
  have h_k_cases : k = i + j ∨ k = i + j + 1 := by omega
  rcases h_k_cases with (rfl | rfl)
  · exact ⟨i + j, ⟨i, hi_in, j, hj_in, rfl⟩, (0 : ℤ), by simp, by ring⟩
  · exact ⟨i + j, ⟨i, hi_in, j, hj_in, rfl⟩, (1 : ℤ), by simp, by ring⟩

/-! ## Boundedness helpers -/

lemma bounded_image2_sub {X Y : Set ℝ}
    (hX : Bornology.IsBounded X) (hY : Bornology.IsBounded Y) :
    Bornology.IsBounded (Set.image2 (· - ·) X Y) :=
  hX.sub hY

lemma bounded_image2_add {X Y : Set ℝ}
    (hX : Bornology.IsBounded X) (hY : Bornology.IsBounded Y) :
    Bornology.IsBounded (Set.image2 (· + ·) X Y) :=
  hX.add hY

/-! ## Finset helper lemmas -/

lemma finset_pointwise_add_card_le {α : Type*} [AddCommMonoid α] [DecidableEq α]
    {A B : Finset α} : (A + B).card ≤ A.card * B.card := by
  have h : (A + B) ⊆ (A ×ˢ B).image (fun p : α × α => p.1 + p.2) := by
    intro x hx
    have h_mem : ∃ (a : α), a ∈ A ∧ ∃ (b : α), b ∈ B ∧ a + b = x := by
      simpa [Finset.mem_add] using hx
    rcases h_mem with ⟨a, ha, b, hb, rfl⟩
    have h_ab : (a, b) ∈ A ×ˢ B := Finset.mem_product.mpr ⟨ha, hb⟩
    exact Finset.mem_image.mpr ⟨(a, b), h_ab, rfl⟩
  calc
    (A + B).card ≤ ((A ×ˢ B).image (fun p : α × α => p.1 + p.2)).card :=
      Finset.card_le_card h
    _ ≤ (A ×ˢ B).card := Finset.card_image_le
    _ = A.card * B.card := by rw [Finset.card_product]

/-! ## Main theorem -/

/-- Discretized Plünnecke-Ruzsa inequality for 1D dyadic covering numbers.

`N(X-X, δ) · N(Y, δ) ≤ 9 · N(X+Y, δ)^2` -/
lemma discretized_pluennecke_ruzsa_diff {δ : ℝ} (hδ : 0 < δ) {X Y : Set ℝ}
    (hX : Bornology.IsBounded X) (hY : Bornology.IsBounded Y)
    (hY_nonempty : Y.Nonempty) :
    let Nxy := ENat.toENNReal (dyadicCoveringNumber δ
      (productLikeRealLineCopy (Set.image2 (· + ·) X Y)))
    ENat.toENNReal (dyadicCoveringNumber δ
      (productLikeRealLineCopy (Set.image2 (· - ·) X X))) *
      ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy Y)) ≤
    9 * Nxy * Nxy := by
  let IX := (realCubeIndexSet_finite hδ hX).toFinset
  let IY := (realCubeIndexSet_finite hδ hY).toFinset
  have hIX : (IX : Set ℤ) = realCubeIndexSet δ X :=
    Set.Finite.coe_toFinset (realCubeIndexSet_finite hδ hX)
  have hIY : (IY : Set ℤ) = realCubeIndexSet δ Y :=
    Set.Finite.coe_toFinset (realCubeIndexSet_finite hδ hY)
  have h_diff : (realCubeIndexSet δ (Set.image2 (· - ·) X X)).Finite :=
    realCubeIndexSet_finite hδ (bounded_image2_sub hX hX)
  let IXX := h_diff.toFinset
  have hIXX : (IXX : Set ℤ) = realCubeIndexSet δ (Set.image2 (· - ·) X X) :=
    Set.Finite.coe_toFinset h_diff
  have h_sum : (realCubeIndexSet δ (Set.image2 (· + ·) X Y)).Finite :=
    realCubeIndexSet_finite hδ (bounded_image2_add hX hY)
  let IXY := h_sum.toFinset
  have hIXY : (IXY : Set ℤ) = realCubeIndexSet δ (Set.image2 (· + ·) X Y) :=
    h_sum.coe_toFinset
  let E : Finset ℤ := {-1, 0}
  have hE2 : E.card = 2 := by decide
  -- IXX ⊆ (IX - IX) + E
  have h1 : (IXX : Set ℤ) ⊆ ((IX - IX : Finset ℤ) + E : Set ℤ) := by
    calc
      (IXX : Set ℤ) = realCubeIndexSet δ (Set.image2 (· - ·) X X) := hIXX
      _ ⊆ (realCubeIndexSet δ X - realCubeIndexSet δ X) + ({-1, 0} : Set ℤ) :=
        diff_self_index_inclusion hδ
      _ = ((IX - IX : Finset ℤ) + E : Set ℤ) := by
        simp [hIX, hIY, E] <;> rfl
  have h1' : IXX ⊆ (IX - IX) + E := by exact_mod_cast h1
  -- IX + IY ⊆ IXY + E
  have h2 : ((IX + IY : Finset ℤ) : Set ℤ) ⊆ ((IXY + E : Finset ℤ) : Set ℤ) := by
    calc
      ((IX + IY : Finset ℤ) : Set ℤ)
        = (realCubeIndexSet δ X + realCubeIndexSet δ Y) := by simp [hIX, hIY] <;> rfl
      _ ⊆ realCubeIndexSet δ (Set.image2 (· + ·) X Y) + ({-1, 0} : Set ℤ) :=
        sum_index_inclusion hδ
      _ = ((IXY + E : Finset ℤ) : Set ℤ) := by simp [hIXY, E] <;> rfl
  have h2' : (IX + IY) ⊆ IXY + E := by exact_mod_cast h2
  -- Card bounds
  have h_card1 : IXX.card ≤ 2 * (IX - IX).card := by
    have h4 : IXX ⊆ (IX - IX) + E := h1'
    have h5 : ((IX - IX) + E).card ≤ (IX - IX).card * E.card :=
      finset_pointwise_add_card_le
    calc
      IXX.card ≤ ((IX - IX) + E).card := Finset.card_le_card h4
      _ ≤ (IX - IX).card * E.card := h5
      _ = (IX - IX).card * 2 := by rw [hE2] <;> ring
      _ = 2 * (IX - IX).card := by ring
  have h_card2 : (IX + IY).card ≤ 2 * IXY.card := by
    have h4 : (IX + IY) ⊆ IXY + E := h2'
    have h5 : (IXY + E).card ≤ IXY.card * E.card := finset_pointwise_add_card_le
    calc
      (IX + IY).card ≤ (IXY + E).card := Finset.card_le_card h4
      _ ≤ IXY.card * E.card := h5
      _ = IXY.card * 2 := by rw [hE2] <;> ring
      _ = 2 * IXY.card := by ring
  -- Finite Ruzsa triangle: |IX - IX| * |IY| ≤ |IX + IY|^2
  have h_ruzsa : (IX - IX).card * IY.card ≤ (IX + IY).card * (IX + IY).card := by
    exact Finset.ruzsa_triangle_inequality_sub_add_add IX IY IX
  -- Combine
  have h_main : IXX.card * IY.card ≤ 8 * IXY.card * IXY.card := by
    calc
      IXX.card * IY.card
        ≤ (2 * (IX - IX).card) * IY.card := by gcongr
      _ = 2 * ((IX - IX).card * IY.card) := by ring
      _ ≤ 2 * ((IX + IY).card * (IX + IY).card) := by gcongr
      _ ≤ 2 * ((2 * IXY.card) * (2 * IXY.card)) := by gcongr
      _ = 8 * IXY.card * IXY.card := by ring
  -- Convert to ENNReal
  have hNXX := realCoveringNumber_eq_card hδ (bounded_image2_sub hX hX)
  have hNY := realCoveringNumber_eq_card hδ hY
  have hNXY := realCoveringNumber_eq_card hδ (bounded_image2_add hX hY)
  dsimp only
  rw [hNXX, hNY, hNXY]
  have h_encard_IXX : (realCubeIndexSet δ (Set.image2 (· - ·) X X)).encard = IXX.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card h_diff]
    <;> rfl
  have h_encard_IY : (realCubeIndexSet δ Y).encard = IY.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hY)]
    <;> rfl
  have h_encard_IXY : (realCubeIndexSet δ (Set.image2 (· + ·) X Y)).encard = IXY.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card h_sum]
    <;> rfl
  rw [h_encard_IXX, h_encard_IY, h_encard_IXY]
  have h_final : IXX.card * IY.card ≤ 9 * IXY.card * IXY.card := by
    calc
      IXX.card * IY.card ≤ 8 * IXY.card * IXY.card := h_main
      _ ≤ 9 * IXY.card * IXY.card := by
        have h_nonneg : 0 ≤ IXY.card * IXY.card := by positivity
        nlinarith
  norm_cast
  <;> exact_mod_cast h_final

/-- Discretized Plünnecke-Ruzsa inequality for sumsets:

`N(X+X, δ) · N(Y, δ) ≤ 9 · N(X+Y, δ)^2` -/
lemma discretized_pluennecke_ruzsa_sum {δ : ℝ} (hδ : 0 < δ) {X Y : Set ℝ}
    (hX : Bornology.IsBounded X) (hY : Bornology.IsBounded Y)
    (hY_nonempty : Y.Nonempty) :
    let Nxy := ENat.toENNReal (dyadicCoveringNumber δ
      (productLikeRealLineCopy (Set.image2 (· + ·) X Y)))
    ENat.toENNReal (dyadicCoveringNumber δ
      (productLikeRealLineCopy (Set.image2 (· + ·) X X))) *
      ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy Y)) ≤
    9 * Nxy * Nxy := by
  let IX := (realCubeIndexSet_finite hδ hX).toFinset
  let IY := (realCubeIndexSet_finite hδ hY).toFinset
  have hIX : (IX : Set ℤ) = realCubeIndexSet δ X :=
    Set.Finite.coe_toFinset (realCubeIndexSet_finite hδ hX)
  have hIY : (IY : Set ℤ) = realCubeIndexSet δ Y :=
    Set.Finite.coe_toFinset (realCubeIndexSet_finite hδ hY)
  have h_sumXX : (realCubeIndexSet δ (Set.image2 (· + ·) X X)).Finite :=
    realCubeIndexSet_finite hδ (bounded_image2_add hX hX)
  let IXX := h_sumXX.toFinset
  have hIXX : (IXX : Set ℤ) = realCubeIndexSet δ (Set.image2 (· + ·) X X) :=
    Set.Finite.coe_toFinset h_sumXX
  have h_sumXY : (realCubeIndexSet δ (Set.image2 (· + ·) X Y)).Finite :=
    realCubeIndexSet_finite hδ (bounded_image2_add hX hY)
  let IXY := h_sumXY.toFinset
  have hIXY : (IXY : Set ℤ) = realCubeIndexSet δ (Set.image2 (· + ·) X Y) :=
    h_sumXY.coe_toFinset
  let E01 : Finset ℤ := {0, 1}
  let Em10 : Finset ℤ := {-1, 0}
  have hE01 : E01.card = 2 := by decide
  have hEm10 : Em10.card = 2 := by decide
  -- IXX ⊆ (IX + IX) + E01
  have h1 : (IXX : Set ℤ) ⊆ ((IX + IX : Finset ℤ) + E01 : Set ℤ) := by
    calc
      (IXX : Set ℤ) = realCubeIndexSet δ (Set.image2 (· + ·) X X) := hIXX
      _ ⊆ (realCubeIndexSet δ X + realCubeIndexSet δ X) + ({0, 1} : Set ℤ) :=
        sum_index_inclusion_rev hδ
      _ = ((IX + IX : Finset ℤ) + E01 : Set ℤ) := by
        simp [hIX, E01] <;> rfl
  have h1' : IXX ⊆ (IX + IX) + E01 := by exact_mod_cast h1
  -- IX + IY ⊆ IXY + Em10
  have h2 : ((IX + IY : Finset ℤ) : Set ℤ) ⊆ ((IXY + Em10 : Finset ℤ) : Set ℤ) := by
    calc
      ((IX + IY : Finset ℤ) : Set ℤ)
        = (realCubeIndexSet δ X + realCubeIndexSet δ Y) := by simp [hIX, hIY] <;> rfl
      _ ⊆ realCubeIndexSet δ (Set.image2 (· + ·) X Y) + ({-1, 0} : Set ℤ) :=
        sum_index_inclusion hδ
      _ = ((IXY + Em10 : Finset ℤ) : Set ℤ) := by simp [hIXY, Em10] <;> rfl
  have h2' : (IX + IY) ⊆ IXY + Em10 := by exact_mod_cast h2
  -- Card bounds
  have h_card1 : IXX.card ≤ 2 * (IX + IX).card := by
    have h4 : IXX ⊆ (IX + IX) + E01 := h1'
    have h5 : ((IX + IX) + E01).card ≤ (IX + IX).card * E01.card :=
      finset_pointwise_add_card_le
    calc
      IXX.card ≤ ((IX + IX) + E01).card := Finset.card_le_card h4
      _ ≤ (IX + IX).card * E01.card := h5
      _ = (IX + IX).card * 2 := by rw [hE01] <;> ring
      _ = 2 * (IX + IX).card := by ring
  have h_card2 : (IX + IY).card ≤ 2 * IXY.card := by
    have h4 : (IX + IY) ⊆ IXY + Em10 := h2'
    have h5 : (IXY + Em10).card ≤ IXY.card * Em10.card := finset_pointwise_add_card_le
    calc
      (IX + IY).card ≤ (IXY + Em10).card := Finset.card_le_card h4
      _ ≤ IXY.card * Em10.card := h5
      _ = IXY.card * 2 := by rw [hEm10] <;> ring
      _ = 2 * IXY.card := by ring
  -- Finite Ruzsa: |IX + IX| * |IY| ≤ |IX + IY|^2
  have h_set_eq : IY + IX = IX + IY := by
    ext z
    simp [Finset.mem_add, add_comm]
    <;> tauto
  have h_comm : (IY + IX).card = (IX + IY).card := by
    rw [h_set_eq]
  have h_ruzsa : (IX + IX).card * IY.card ≤ (IX + IY).card * (IX + IY).card := by
    have h := Finset.ruzsa_triangle_inequality_add_add_add IX IY IX
    rw [h_comm] at h
    exact h
  -- Combine
  have h_main : IXX.card * IY.card ≤ 8 * IXY.card * IXY.card := by
    calc
      IXX.card * IY.card
        ≤ (2 * (IX + IX).card) * IY.card := by gcongr
      _ = 2 * ((IX + IX).card * IY.card) := by ring
      _ ≤ 2 * ((IX + IY).card * (IX + IY).card) := by gcongr
      _ ≤ 2 * ((2 * IXY.card) * (2 * IXY.card)) := by gcongr
      _ = 8 * IXY.card * IXY.card := by ring
  -- Convert to ENNReal
  have hNXX := realCoveringNumber_eq_card hδ (bounded_image2_add hX hX)
  have hNY := realCoveringNumber_eq_card hδ hY
  have hNXY := realCoveringNumber_eq_card hδ (bounded_image2_add hX hY)
  dsimp only
  rw [hNXX, hNY, hNXY]
  have h_encard_IXX : (realCubeIndexSet δ (Set.image2 (· + ·) X X)).encard = IXX.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card h_sumXX] <;> rfl
  have h_encard_IY : (realCubeIndexSet δ Y).encard = IY.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hY)] <;> rfl
  have h_encard_IXY : (realCubeIndexSet δ (Set.image2 (· + ·) X Y)).encard = IXY.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card h_sumXY] <;> rfl
  rw [h_encard_IXX, h_encard_IY, h_encard_IXY]
  have h_final : IXX.card * IY.card ≤ 9 * IXY.card * IXY.card := by
    calc
      IXX.card * IY.card ≤ 8 * IXY.card * IXY.card := h_main
      _ ≤ 9 * IXY.card * IXY.card := by
        have h_nonneg : 0 ≤ IXY.card * IXY.card := by positivity
        nlinarith
  norm_cast
  <;> exact_mod_cast h_final

end ProductLikeIncidence
