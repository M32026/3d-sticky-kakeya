module

/-
# Approximate Cube Trimming

Trim a (δ,s,C)-set lying in an approximate-incidence strip to controlled size
while preserving (δ,s)-regularity.

## Strip structure

Given x, y ∈ [0,1], the strip S = {p : |p0*y + p1 - x| ≤ 2δ} has width O(δ).
δ-cubes in S can be ordered lexicographically by (p0, p1) grid coordinates.

Key geometric facts:
1. At most 7 strip cubes share the same p0 grid coordinate.
2. Strip cubes inside an r-cube R form a contiguous block in this ordering, up to
   at most 13 adjacent r-cubes in the p1 direction (boundary error ≤ 6δ).

## Selection

Order all strip cubes by rank (lexicographic position). Select every K-th cube
where K ≈ N/M. The contiguity property ensures any r-cube contains at most
L/K + 1 selected cubes, giving regularity with constant O(C).

## Constants

Size: M/2 ≤ |A'| ≤ 2M+1
Regularity: (δ,s,20*C)-set

## Dependencies

- CoreDefinitions, ProductLikeBasic — dyadic cubes/scales
- ProductLikeProof — dyadicCube_nesting, dyadic_cubes_disjoint
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.DualityBridge
public import MyLeanRepo.ProductLikeIncidence.ProductLikeProof
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Bornology ENNReal Finset Classical Real

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-! ### Strip geometry -/

/-- If a δ-cube Q meets the 2δ-strip, then its lower-left corner (a,b) satisfies
a*y + b ≤ x + 2δ and (a+δ)*y + (b+δ) ≥ x - 2δ.
Note: the supremum (a+δ)*y+(b+δ) is not attained in the half-open cube, but the
weak inequality is sufficient for bounding arguments. -/
private lemma strip_cube_bounds {δ x y : ℝ} (hδ : 0 < δ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    {k : Fin 2 → ℤ}
    (h : ∃ p ∈ dyadicCube δ k, |p 0 * y + p 1 - x| ≤ 2 * δ) :
    δ * (k 0 : ℝ) * y + δ * (k 1 : ℝ) ≤ x + 2 * δ ∧
    δ * ((k 0 : ℝ) + 1) * y + δ * ((k 1 : ℝ) + 1) ≥ x - 2 * δ := by
  rcases h with ⟨p, hp, h_ineq⟩
  have h_p0_lo : δ * (k 0 : ℝ) ≤ p 0 := (hp 0).1
  have h_p0_hi : p 0 < δ * ((k 0 : ℝ) + 1) := (hp 0).2
  have h_p1_lo : δ * (k 1 : ℝ) ≤ p 1 := (hp 1).1
  have h_p1_hi : p 1 < δ * ((k 1 : ℝ) + 1) := (hp 1).2
  have h4 : |p 0 * y + p 1 - x| ≤ 2 * δ := h_ineq
  have h5 : p 0 * y + p 1 - x ≤ 2 * δ := (abs_le.mp h4).2
  have h6 : -(2 * δ) ≤ p 0 * y + p 1 - x := (abs_le.mp h4).1
  constructor
  · nlinarith
  · nlinarith

/-- Width parameter W = 2δ + δ*(y+1) ≤ 4δ for y ≤ 1. -/
private def stripW (δ y : ℝ) : ℝ := 2 * δ + δ * (y + 1)

private lemma stripW_le_4δ {δ y : ℝ} (hδ : 0 < δ) (hy1 : y ≤ 1) :
    stripW δ y ≤ 4 * δ := by
  have h1 : δ * (y + 1) ≤ 2 * δ := by
    have h2 : y + 1 ≤ 2 := by linarith
    have h3 : 0 ≤ δ := by linarith
    nlinarith
  have h4 : stripW δ y = 2 * δ + δ * (y + 1) := by rfl
  rw [h4]
  linarith

/-- For fixed p0 grid coordinate k0, at most 7 strip δ-cubes exist. -/
private lemma strip_cubes_per_p0 {δ x y : ℝ} (hδ : 0 < δ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    {k0 : ℤ} :
    Set.Finite {k1 : ℤ | ∃ p ∈ dyadicCube δ (fun i : Fin 2 => if i = 0 then k0 else k1),
      |p 0 * y + p 1 - x| ≤ 2 * δ} ∧
    ({k1 : ℤ | ∃ p ∈ dyadicCube δ (fun i : Fin 2 => if i = 0 then k0 else k1),
      |p 0 * y + p 1 - x| ≤ 2 * δ}).encard ≤ 7 := by
  let a := δ * (k0 : ℝ)
  let W := stripW δ y
  have hW_le : W ≤ 4 * δ := stripW_le_4δ hδ hy1
  let S : Set ℤ := {k1 | ∃ p ∈ dyadicCube δ (fun i : Fin 2 => if i = 0 then k0 else k1),
      |p 0 * y + p 1 - x| ≤ 2 * δ}
  have hS_bounds : ∀ k1 ∈ S,
      (x - W - a * y) / δ ≤ (k1 : ℝ) ∧ (k1 : ℝ) ≤ (x + 2 * δ - a * y) / δ := by
    intro k1 hk1
    let k : Fin 2 → ℤ := fun i => if i = 0 then k0 else k1
    have hk0 : k 0 = k0 := by simp [k]
    have hk1' : k 1 = k1 := by simp [k]
    have h_bounds := strip_cube_bounds hδ hy0 hy1 (k := k) hk1
    have h_bounds' : δ * (k0 : ℝ) * y + δ * (k1 : ℝ) ≤ x + 2 * δ ∧
        δ * ((k0 : ℝ) + 1) * y + δ * ((k1 : ℝ) + 1) ≥ x - 2 * δ := by
      simpa [hk0, hk1'] using h_bounds
    have h1 : a * y + δ * (k1 : ℝ) ≤ x + 2 * δ := by
      simpa [a] using h_bounds'.1
    have h2 : (a + δ) * y + δ * ((k1 : ℝ) + 1) ≥ x - 2 * δ := by
      have h2' := h_bounds'.2
      have h_eq : (a + δ) * y + δ * ((k1 : ℝ) + 1) =
          δ * ((k0 : ℝ) + 1) * y + δ * ((k1 : ℝ) + 1) := by
        have ha : a = δ * (k0 : ℝ) := by rfl
        rw [ha] <;> ring
      rw [h_eq]
      exact h2'
    have hW_def : W = 3 * δ + δ * y := by
      simp [W, stripW] <;> ring
    constructor
    · have h3 : δ * (k1 : ℝ) ≥ x - W - a * y := by
        rw [hW_def]
        linarith
      have h4 : (x - W - a * y) / δ ≤ (k1 : ℝ) := by
        calc (x - W - a * y) / δ
          ≤ (δ * (k1 : ℝ)) / δ := by gcongr
        _ = (k1 : ℝ) := by field_simp [hδ.ne'] <;> ring
      exact h4
    · have h3 : δ * (k1 : ℝ) ≤ x + 2 * δ - a * y := by linarith
      have h4 : (k1 : ℝ) ≤ (x + 2 * δ - a * y) / δ := by
        calc (k1 : ℝ)
          = (δ * (k1 : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
        _ ≤ (x + 2 * δ - a * y) / δ := by gcongr
      exact h4
  let lo : ℝ := (x - W - a * y) / δ
  let hi : ℝ := (x + 2 * δ - a * y) / δ
  have h_len : hi - lo ≤ 6 := by
    dsimp only [lo, hi]
    have h : hi - lo = (W + 2 * δ) / δ := by ring
    rw [h]
    have h2 : W + 2 * δ ≤ 6 * δ := by linarith [hW_le]
    have h3 : (W + 2 * δ) / δ ≤ 6 := by
      calc (W + 2 * δ) / δ ≤ (6 * δ) / δ := by gcongr
        _ = 6 := by field_simp [hδ.ne'] <;> ring
    exact h3
  let k_lo : ℤ := ⌈lo⌉
  let k_hi : ℤ := ⌊hi⌋
  have hS_sub : S ⊆ (Finset.Icc k_lo k_hi : Set ℤ) := by
    intro k1 hk1
    have h4 : lo ≤ (k1 : ℝ) := (hS_bounds k1 hk1).1
    have h5 : (k1 : ℝ) ≤ hi := (hS_bounds k1 hk1).2
    have h6 : k_lo ≤ k1 := by
      dsimp only [k_lo]
      exact Int.ceil_le.mpr h4
    have h7 : k1 ≤ k_hi := by
      dsimp only [k_hi]
      exact Int.le_floor.mpr h5
    simp only [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨h6, h7⟩
  have h_fin : S.Finite := Set.Finite.subset (Finset.finite_toSet (Finset.Icc k_lo k_hi)) hS_sub
  have h_card : S.encard ≤ ↑(Finset.Icc k_lo k_hi).card := by
    have h1 : S.encard ≤ (↑(Finset.Icc k_lo k_hi) : Set ℤ).encard := Set.encard_mono hS_sub
    have h2 : (↑(Finset.Icc k_lo k_hi) : Set ℤ).encard = ↑(Finset.Icc k_lo k_hi).card :=
      Set.encard_coe_eq_coe_finsetCard _
    rw [h2] at h1
    exact h1
  have h9 : (k_hi : ℝ) - (k_lo : ℝ) ≤ 6 := by
    have h10 : (k_hi : ℝ) ≤ hi := by dsimp only [k_hi]; exact Int.floor_le hi
    have h11 : lo ≤ (k_lo : ℝ) := by dsimp only [k_lo]; exact Int.le_ceil lo
    linarith
  have h10 : (Finset.Icc k_lo k_hi).card ≤ 7 := by
    by_cases h : k_lo ≤ k_hi
    · have h11 : k_hi - k_lo ≤ 6 := by exact_mod_cast h9
      have h12 : (Finset.Icc k_lo k_hi).card = (k_hi - k_lo).toNat + 1 := by
        simp [Finset.Icc_eq_empty_of_lt, h] <;> omega
      rw [h12]
      have h13 : (k_hi - k_lo).toNat ≤ 6 := Int.toNat_le.mpr (by omega)
      omega
    · have h14 : Finset.Icc k_lo k_hi = ∅ := by
        apply Finset.Icc_eq_empty_of_lt
        omega
      rw [h14] <;> simp
  exact ⟨h_fin, le_trans h_card (by exact_mod_cast h10)⟩

/-! ### Multiples counting (reused from tube proof pattern) -/

/-- Number of multiples of K in {a,...,b} is ≤ (b-a)/K + 1. -/
private lemma multiples_count_bound (K a b : ℕ) (hK : 0 < K)
    (S : Finset ℕ) (hS1 : ∀ n ∈ S, n % K = 0) (hS2 : S ⊆ Finset.Icc a b) :
    S.card ≤ (b - a) / K + 1 := by
  by_cases hS_empty : S = ∅
  · rw [hS_empty]; simp
  · have hS_nonempty : S.Nonempty := by
      rwa [Finset.nonempty_iff_ne_empty]
    let m0 := Finset.min' S hS_nonempty
    have hm0_in : m0 ∈ S := Finset.min'_mem S hS_nonempty
    have hm0_mult : m0 % K = 0 := hS1 m0 hm0_in
    have ha : a ≤ m0 := (Finset.mem_Icc.mp (hS2 hm0_in)).1
    let f : ℕ → ℕ := fun n => (n - m0) / K
    have h_inj : Set.InjOn f (S : Set ℕ) := by
      intro n1 hn1 n2 hn2 h
      have h1 : n1 % K = 0 := hS1 n1 hn1
      have h2 : n2 % K = 0 := hS1 n2 hn2
      have h3 : m0 ≤ n1 := Finset.min'_le S n1 hn1
      have h4 : m0 ≤ n2 := Finset.min'_le S n2 hn2
      have h_dvd1 : K ∣ n1 - m0 := by
        have hdiv : K ∣ n1 := Nat.dvd_iff_mod_eq_zero.mpr h1
        have h0 : K ∣ m0 := Nat.dvd_iff_mod_eq_zero.mpr hm0_mult
        rcases hdiv with ⟨a, ha⟩; rcases h0 with ⟨b, hb⟩
        refine' ⟨a - b, _⟩
        have h_ab : b ≤ a := by nlinarith
        have h_eq : n1 - m0 = K * (a - b) := by
          rw [ha, hb, Nat.mul_sub_left_distrib] <;> omega
        exact h_eq
      have h_dvd2 : K ∣ n2 - m0 := by
        have hdiv : K ∣ n2 := Nat.dvd_iff_mod_eq_zero.mpr h2
        have h0 : K ∣ m0 := Nat.dvd_iff_mod_eq_zero.mpr hm0_mult
        rcases hdiv with ⟨a, ha⟩; rcases h0 with ⟨b, hb⟩
        refine' ⟨a - b, _⟩
        have h_ab : b ≤ a := by nlinarith
        have h_eq : n2 - m0 = K * (a - b) := by
          rw [ha, hb, Nat.mul_sub_left_distrib] <;> omega
        exact h_eq
      have h5 : (n1 - m0) / K = (n2 - m0) / K := h
      have h6 : n1 - m0 = n2 - m0 := by
        have h7 : n1 - m0 = ((n1 - m0) / K) * K := by exact Eq.symm (Nat.div_mul_cancel h_dvd1)
        have h8 : n2 - m0 = ((n2 - m0) / K) * K := by exact Eq.symm (Nat.div_mul_cancel h_dvd2)
        rw [h7, h8, h5]
      have h9 : n1 = n2 := by omega
      exact h9
    have h_image : S.image f ⊆ Finset.range ((b - a) / K + 1) := by
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
      have h_n_in : n ∈ Finset.Icc a b := hS2 hn
      have h1 : n ≤ b := (Finset.mem_Icc.mp h_n_in).2
      have h2 : m0 ≤ n := Finset.min'_le S n hn
      have h3 : n - m0 ≤ b - a := by omega
      have h4 : (n - m0) / K ≤ (b - a) / K := Nat.div_le_div_right h3
      have h5 : (n - m0) / K < (b - a) / K + 1 := by
        apply Nat.lt_succ_of_le; exact h4
      exact Finset.mem_range.mpr h5
    have h4 : S.card = (S.image f).card := by
      rw [Finset.card_image_of_injOn h_inj]
    rw [h4]
    have h5 : (S.image f).card ≤ (Finset.range ((b - a) / K + 1)).card :=
      Finset.card_le_card h_image
    simpa using h5

/-! ### ENNReal to real conversion -/

private lemma ennreal_to_real_bound {C r s : ℝ} {N L : ℕ}
    (hC_pos : 0 < C) (hr_nonneg : 0 ≤ r) (hs_nonneg : 0 ≤ s)
    (h1 : (L : ENNReal) ≤ ENNReal.ofReal C * (N : ENNReal) * ENNReal.ofReal (r ^ s)) :
    (L : ℝ) ≤ C * (N : ℝ) * r ^ s := by
  have hpos_C : 0 ≤ C := by linarith
  have hpos_r : 0 ≤ r ^ s := Real.rpow_nonneg hr_nonneg s
  have h2 : ENNReal.ofReal C * (N : ENNReal) * ENNReal.ofReal (r ^ s) =
      ENNReal.ofReal (C * (N : ℝ) * r ^ s) := by
    have h3 : (N : ENNReal) = ENNReal.ofReal (N : ℝ) := by simp
    rw [h3]
    have h41 : ENNReal.ofReal C * ENNReal.ofReal (N : ℝ) = ENNReal.ofReal (C * (N : ℝ)) := by
      rw [← ENNReal.ofReal_mul hpos_C] <;> rfl
    rw [h41]
    have h42 : ENNReal.ofReal (C * (N : ℝ)) * ENNReal.ofReal (r ^ s) =
        ENNReal.ofReal ((C * (N : ℝ)) * r ^ s) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
    rw [h42] <;> ring
  rw [h2] at h1
  have h5 : (L : ENNReal) = ENNReal.ofReal (L : ℝ) := by simp
  rw [h5] at h1
  have hpos : 0 ≤ C * (N : ℝ) * r ^ s := by positivity
  exact (ENNReal.ofReal_le_ofReal_iff hpos).mp h1

/-! ### Geometric contiguity for strip cubes -/

/-- Lexicographic comparison on integer pairs. -/
private def lexLess (a b : ℤ × ℤ) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

/-- Given a δ-cube contained in an r-cube, extract coordinate bounds:
the δ-cube's lower-left corner lies within the r-cube. -/
private lemma dyadicCube_nesting_subset {δ r : ℝ} {d : ℕ}
    (hδ : 0 < δ) (hδr : δ ≤ r)
    (k : Fin d → ℤ) (j : Fin d → ℤ)
    (h_sub : dyadicCube δ k ⊆ dyadicCube r j)
    (i : Fin d) :
    r * (j i : ℝ) ≤ δ * (k i : ℝ) ∧ δ * (k i : ℝ) < r * ((j i : ℝ) + 1) := by
  let p : EuclideanSpace ℝ (Fin d) := (WithLp.equiv 2 _).symm (fun i => δ * (k i : ℝ))
  have hpδ : p ∈ dyadicCube δ k := by
    intro i
    have h4 : p i = δ * (k i : ℝ) := by
      simp [p, WithLp.equiv_symm_apply]
    rw [h4]
    exact ⟨by linarith, by linarith [hδ]⟩
  have hpr : p ∈ dyadicCube r j := h_sub hpδ
  have h1 : r * (j i : ℝ) ≤ p i := (hpr i).1
  have h2 : p i < r * ((j i : ℝ) + 1) := (hpr i).2
  have h3 : p i = δ * (k i : ℝ) := by
    simp [p, WithLp.equiv_symm_apply]
  constructor
  · rw [h3] at h1; exact h1
  · rw [h3] at h2; exact h2

/-- If Q1, Q3 are strip cubes inside r-cube R, and Q2 is lex-between them,
then Q2's lower-left corner lies in R expanded by 6δ in p1 direction. -/
private lemma strip_contiguity_bounds {δ x y r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    {j : Fin 2 → ℤ}
    {k1 k2 k3 : Fin 2 → ℤ}
    (h1_strip : ∃ p ∈ dyadicCube δ k1, |p 0 * y + p 1 - x| ≤ 2 * δ)
    (h3_strip : ∃ p ∈ dyadicCube δ k3, |p 0 * y + p 1 - x| ≤ 2 * δ)
    (h2_strip : ∃ p ∈ dyadicCube δ k2, |p 0 * y + p 1 - x| ≤ 2 * δ)
    (h1_in_R : dyadicCube δ k1 ⊆ dyadicCube r j)
    (h3_in_R : dyadicCube δ k3 ⊆ dyadicCube r j)
    (h_lex1 : ¬ lexLess (k2 0, k2 1) (k1 0, k1 1))
    (h_lex2 : ¬ lexLess (k3 0, k3 1) (k2 0, k2 1)) :
    let A := r * (j 0 : ℝ); let B := r * (j 1 : ℝ)
    δ * (k2 0 : ℝ) ∈ Set.Ico A (A + r) ∧
    δ * (k2 1 : ℝ) ∈ Set.Icc (B - 6 * δ) (B + r + 6 * δ) := by
  let a1 := δ * (k1 0 : ℝ); let b1 := δ * (k1 1 : ℝ)
  let a2 := δ * (k2 0 : ℝ); let b2 := δ * (k2 1 : ℝ)
  let a3 := δ * (k3 0 : ℝ); let b3 := δ * (k3 1 : ℝ)
  let A := r * (j 0 : ℝ); let B := r * (j 1 : ℝ)
  have h_nest1 := dyadicCube_nesting_subset hδ hδr k1 j h1_in_R
  have h_nest3 := dyadicCube_nesting_subset hδ hδr k3 j h3_in_R
  have h_a1 : A ≤ a1 := (h_nest1 0).1
  have h_a1' : a1 < A + r := by
    have h := (h_nest1 0).2
    have h_eq : r * ((j 0 : ℝ) + 1) = A + r := by ring
    rw [h_eq] at h
    exact h
  have h_a3 : A ≤ a3 := (h_nest3 0).1
  have h_a3' : a3 < A + r := by
    have h := (h_nest3 0).2
    have h_eq : r * ((j 0 : ℝ) + 1) = A + r := by ring
    rw [h_eq] at h
    exact h
  have h_b1 : B ≤ b1 := (h_nest1 1).1
  have h_b1' : b1 < B + r := by
    have h := (h_nest1 1).2
    have h_eq : r * ((j 1 : ℝ) + 1) = B + r := by ring
    rw [h_eq] at h
    exact h
  have h_b3 : B ≤ b3 := (h_nest3 1).1
  have h_b3' : b3 < B + r := by
    have h := (h_nest3 1).2
    have h_eq : r * ((j 1 : ℝ) + 1) = B + r := by ring
    rw [h_eq] at h
    exact h
  have h1b := strip_cube_bounds hδ hy0 hy1 h1_strip
  have h3b := strip_cube_bounds hδ hy0 hy1 h3_strip
  have h2b := strip_cube_bounds hδ hy0 hy1 h2_strip
  have h1_1 : a1 * y + b1 ≤ x + 2 * δ := by simpa [a1, b1] using h1b.1
  have h1_2 : (a1 + δ) * y + (b1 + δ) ≥ x - 2 * δ := by
    have h := h1b.2
    have h_eq : (a1 + δ) * y + (b1 + δ) = δ * ((k1 0 : ℝ) + 1) * y + δ * ((k1 1 : ℝ) + 1) := by
      simp [a1, b1] <;> ring
    rw [h_eq]; exact h
  have h3_1 : a3 * y + b3 ≤ x + 2 * δ := by simpa [a3, b3] using h3b.1
  have h3_2 : (a3 + δ) * y + (b3 + δ) ≥ x - 2 * δ := by
    have h := h3b.2
    have h_eq : (a3 + δ) * y + (b3 + δ) = δ * ((k3 0 : ℝ) + 1) * y + δ * ((k3 1 : ℝ) + 1) := by
      simp [a3, b3] <;> ring
    rw [h_eq]; exact h
  have h2_1 : a2 * y + b2 ≤ x + 2 * δ := by simpa [a2, b2] using h2b.1
  have h2_2 : (a2 + δ) * y + (b2 + δ) ≥ x - 2 * δ := by
    have h := h2b.2
    have h_eq : (a2 + δ) * y + (b2 + δ) = δ * ((k2 0 : ℝ) + 1) * y + δ * ((k2 1 : ℝ) + 1) := by
      simp [a2, b2] <;> ring
    rw [h_eq]; exact h
  have h_k2_0 : k1 0 ≤ k2 0 ∧ k2 0 ≤ k3 0 := by
    have h1' : ¬ (k2 0 < k1 0 ∨ (k2 0 = k1 0 ∧ k2 1 < k1 1)) := h_lex1
    have h2' : ¬ (k3 0 < k2 0 ∨ (k3 0 = k2 0 ∧ k3 1 < k2 1)) := h_lex2
    exact ⟨by omega, by omega⟩
  have h_a2_lo : A ≤ a2 := by
    have h : k1 0 ≤ k2 0 := h_k2_0.1
    have h' : a1 ≤ a2 := by dsimp only [a1, a2]; gcongr
    linarith
  have h_a2_hi : a2 < A + r := by
    have h : k2 0 ≤ k3 0 := h_k2_0.2
    have h' : a2 ≤ a3 := by dsimp only [a2, a3]; gcongr
    linarith
  have h_x_a1_lo : B - 2 * δ ≤ x - a1 * y := by
    nlinarith
  have h_x_a1_hi : x - a1 * y ≤ B + r + 4 * δ := by
    nlinarith [hy1]
  have h_x_a3_lo : B - 2 * δ ≤ x - a3 * y := by nlinarith
  have h_x_a3_hi : x - a3 * y ≤ B + r + 4 * δ := by nlinarith [hy1]
  have h_a2_le_a3 : a2 ≤ a3 := by dsimp only [a2, a3]; gcongr; exact h_k2_0.2
  have h_a1_le_a2 : a1 ≤ a2 := by dsimp only [a1, a2]; gcongr; exact h_k2_0.1
  have h_x_a2_lo : B - 2 * δ ≤ x - a2 * y := by
    have h : x - a3 * y ≤ x - a2 * y := by
      have h' : a2 ≤ a3 := h_a2_le_a3
      have h'' : a2 * y ≤ a3 * y := by gcongr <;> linarith
      linarith
    linarith [h_x_a3_lo]
  have h_x_a2_hi : x - a2 * y ≤ B + r + 4 * δ := by
    have h : x - a2 * y ≤ x - a1 * y := by
      have h' : a1 ≤ a2 := h_a1_le_a2
      have h'' : a1 * y ≤ a2 * y := by gcongr <;> linarith
      linarith
    linarith [h_x_a1_hi]
  have h_b2_lo : B - 6 * δ ≤ b2 := by
    nlinarith [hy1]
  have h_b2_hi : b2 ≤ B + r + 6 * δ := by
    nlinarith [hy1]
  exact ⟨⟨h_a2_lo, h_a2_hi⟩, ⟨h_b2_lo, h_b2_hi⟩⟩

/-- The expanded region [A,A+r) × [B-7δ,B+r+7δ) is covered by 15 dyadic r-cubes. -/
private lemma expanded_region_cover {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hδr : δ ≤ r)
    {j : Fin 2 → ℤ} :
    {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ Set.Ico (r * (j 0 : ℝ)) (r * ((j 0 : ℝ) + 1)) ∧
      p 1 ∈ Set.Ico (r * (j 1 : ℝ) - 7 * δ) (r * ((j 1 : ℝ) + 1) + 7 * δ)} ⊆
    ⋃ m ∈ Finset.Icc (-7 : ℤ) 7, dyadicCube r (fun i : Fin 2 => if i = 0 then j 0 else j 1 + m) := by
  intro p hp
  have h0 : p 0 ∈ Set.Ico (r * (j 0 : ℝ)) (r * ((j 0 : ℝ) + 1)) := hp.1
  have h1_lo : r * (j 1 : ℝ) - 7 * δ ≤ p 1 := hp.2.1
  have h1_hi : p 1 < r * ((j 1 : ℝ) + 1) + 7 * δ := hp.2.2
  let m_abs : ℤ := ⌊(p 1) / r⌋
  have hm1 : r * (m_abs : ℝ) ≤ p 1 := by
    have h : (m_abs : ℝ) ≤ (p 1) / r := Int.floor_le ((p 1) / r)
    calc r * (m_abs : ℝ) ≤ r * ((p 1) / r) := by gcongr
      _ = p 1 := by field_simp [hr.ne'] <;> ring
  have hm2 : p 1 < r * ((m_abs : ℝ) + 1) := by
    have h : (p 1) / r < (m_abs : ℝ) + 1 := Int.lt_floor_add_one ((p 1) / r)
    calc p 1 = r * ((p 1) / r) := by field_simp [hr.ne'] <;> ring
      _ < r * ((m_abs : ℝ) + 1) := by gcongr
  have h_m_abs_lo : (j 1 : ℤ) - 7 ≤ m_abs := by
    have h : r * ((j 1 : ℝ) - 7) < r * ((m_abs : ℝ) + 1) := by
      calc r * ((j 1 : ℝ) - 7)
        = r * (j 1 : ℝ) - 7 * r := by ring
      _ ≤ r * (j 1 : ℝ) - 7 * δ := by gcongr
      _ ≤ p 1 := h1_lo
      _ < r * ((m_abs : ℝ) + 1) := hm2
    have h2 : (j 1 : ℝ) - 7 < (m_abs : ℝ) + 1 := by
      have hdiv : (r * ((j 1 : ℝ) - 7)) / r < (r * ((m_abs : ℝ) + 1)) / r := div_lt_div_of_pos_right h hr
      have hleft : (r * ((j 1 : ℝ) - 7)) / r = (j 1 : ℝ) - 7 := by field_simp [hr.ne'] <;> ring
      have hright : (r * ((m_abs : ℝ) + 1)) / r = (m_abs : ℝ) + 1 := by field_simp [hr.ne'] <;> ring
      rw [hleft, hright] at hdiv
      exact hdiv
    have h3 : (j 1 : ℝ) - 8 < (m_abs : ℝ) := by linarith
    have h4 : (j 1 : ℤ) - 8 < m_abs := by exact_mod_cast h3
    omega
  have h_m_abs_hi : m_abs ≤ (j 1 : ℤ) + 7 := by
    have h : r * (m_abs : ℝ) < r * ((j 1 : ℝ) + 8) := by
      calc r * (m_abs : ℝ) ≤ p 1 := hm1
        _ < r * ((j 1 : ℝ) + 1) + 7 * δ := h1_hi
        _ ≤ r * ((j 1 : ℝ) + 1) + 7 * r := by gcongr
        _ = r * ((j 1 : ℝ) + 8) := by ring
    have h2 : (m_abs : ℝ) < (j 1 : ℝ) + 8 := by
      have hdiv : (r * (m_abs : ℝ)) / r < (r * ((j 1 : ℝ) + 8)) / r := div_lt_div_of_pos_right h hr
      have hleft : (r * (m_abs : ℝ)) / r = (m_abs : ℝ) := by field_simp [hr.ne'] <;> ring
      have hright : (r * ((j 1 : ℝ) + 8)) / r = (j 1 : ℝ) + 8 := by field_simp [hr.ne'] <;> ring
      rw [hleft, hright] at hdiv
      exact hdiv
    have h3 : m_abs < (j 1 : ℤ) + 8 := by exact_mod_cast h2
    omega
  let m : ℤ := m_abs - j 1
  have hm_range : m ∈ Finset.Icc (-7 : ℤ) 7 := by
    simp only [Finset.mem_Icc, m]
    constructor <;> omega
  have h7 : p ∈ dyadicCube r (fun i : Fin 2 => if i = 0 then j 0 else j 1 + m) := by
    simp only [dyadicCube, Set.mem_setOf_eq]
    intro i
    fin_cases i
    · exact h0
    · have h_goal : p 1 ∈ Set.Ico (r * (m_abs : ℝ)) (r * ((m_abs : ℝ) + 1)) := ⟨hm1, hm2⟩
      simpa [m] using h_goal
  exact Set.mem_iUnion₂.mpr ⟨m, hm_range, h7⟩

/-! ### Covering number equalities -/

/-- For a finset A of distinct δ-cubes whose union is P, the δ-cubes meeting P
are exactly the cubes in A. -/
private lemma covering_cubes_eq_union
    {δ : ℝ} (hδ : 0 < δ)
    {A : Finset (Set (EuclideanSpace ℝ (Fin 2)))}
    (hA_cubes : ∀ Q ∈ A, Q ∈ dyadicCubes 2 δ)
    (P : Set (EuclideanSpace ℝ (Fin 2)))
    (hP : P = Set.sUnion (A : Set (Set (EuclideanSpace ℝ (Fin 2))))) :
    dyadicCubesMeeting δ P = (A : Set _) := by
  ext Q
  simp only [dyadicCubesMeeting, Set.mem_setOf_eq, Finset.mem_coe]
  constructor
  · rintro ⟨hQ, hnonempty⟩
    rcases hnonempty with ⟨p, hpQ, hpP⟩
    have hpP' : p ∈ Set.sUnion (A : Set (Set (EuclideanSpace ℝ (Fin 2)))) := by
      rw [←hP]; exact hpP
    rcases Set.mem_sUnion.mp hpP' with ⟨Q', hQ'inA, hpQ'⟩
    have hQ_eq : Q = Q' := by
      rcases hQ with ⟨k, rfl⟩
      rcases hA_cubes Q' hQ'inA with ⟨k', hk'⟩
      have h_inter : (dyadicCube δ k ∩ dyadicCube δ k').Nonempty :=
        ⟨p, hpQ, by rw [← hk']; exact hpQ'⟩
      have h_k_eq : k = k' := by
        by_contra hne
        have h_disj : Disjoint (dyadicCube δ k) (dyadicCube δ k') :=
          DualityBridge.dyadic_cubes_disjoint hδ hne
        have h_empty : (dyadicCube δ k ∩ dyadicCube δ k') = ∅ :=
          Set.disjoint_iff_inter_eq_empty.mp h_disj
        have h_contra : (dyadicCube δ k ∩ dyadicCube δ k').Nonempty :=
          ⟨p, hpQ, by rw [← hk']; exact hpQ'⟩
        rw [h_empty] at h_contra
        simpa using h_contra
      rw [hk', h_k_eq]
    rw [← hQ_eq] at hQ'inA
    exact hQ'inA
  · intro hQ_inA
    have hQ_cube : Q ∈ dyadicCubes 2 δ := hA_cubes Q hQ_inA
    have hQ_nonempty : Q.Nonempty := by
      rcases hQ_cube with ⟨k, rfl⟩
      exact dyadicCube_nonempty hδ k
    rcases hQ_nonempty with ⟨p, hp⟩
    have hpP : p ∈ P := by
      rw [hP]
      exact Set.mem_sUnion.mpr ⟨Q, hQ_inA, hp⟩
    exact ⟨hQ_cube, ⟨p, hp, hpP⟩⟩

/-- For a finset A of distinct δ-cubes whose union is P, and an r-cube R,
the δ-cubes meeting P ∩ R are exactly the cubes in A that are subsets of R. -/
private lemma covering_cubes_eq_intersection
    {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    (hδ_dyadic : δ ∈ dyadicScales) (hr_dyadic : r ∈ dyadicScales)
    {A : Finset (Set (EuclideanSpace ℝ (Fin 2)))}
    (hA_cubes : ∀ Q ∈ A, Q ∈ dyadicCubes 2 δ)
    (P : Set (EuclideanSpace ℝ (Fin 2)))
    (hP : P = Set.sUnion (A : Set (Set (EuclideanSpace ℝ (Fin 2)))))
    (j : Fin 2 → ℤ) :
    dyadicCubesMeeting δ (P ∩ dyadicCube r j) =
    (A.filter (fun Q => Q ⊆ dyadicCube r j) : Set _) := by
  let R := dyadicCube r j
  ext Q
  simp only [dyadicCubesMeeting, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
  constructor
  · rintro ⟨hQ, hnonempty⟩
    rcases hnonempty with ⟨p, hpQ, ⟨hpP, hpR⟩⟩
    have hpP' : p ∈ Set.sUnion (A : Set (Set (EuclideanSpace ℝ (Fin 2)))) := by
      rw [←hP]; exact hpP
    rcases Set.mem_sUnion.mp hpP' with ⟨Q', hQ'inA, hpQ'⟩
    have hQ_eq : Q = Q' := by
      rcases hQ with ⟨k, rfl⟩
      rcases hA_cubes Q' hQ'inA with ⟨k', hk'⟩
      have h_inter : (dyadicCube δ k ∩ dyadicCube δ k').Nonempty :=
        ⟨p, hpQ, by rw [← hk']; exact hpQ'⟩
      have h_k_eq : k = k' := by
        by_contra hne
        have h_disj : Disjoint (dyadicCube δ k) (dyadicCube δ k') :=
          DualityBridge.dyadic_cubes_disjoint hδ hne
        have h_empty : (dyadicCube δ k ∩ dyadicCube δ k') = ∅ :=
          Set.disjoint_iff_inter_eq_empty.mp h_disj
        have h_contra : (dyadicCube δ k ∩ dyadicCube δ k').Nonempty :=
          ⟨p, hpQ, by rw [← hk']; exact hpQ'⟩
        rw [h_empty] at h_contra
        simpa using h_contra
      rw [hk', h_k_eq]
    have hQ_inA : Q ∈ A := by rw [← hQ_eq] at hQ'inA; exact hQ'inA
    have hQ_sub : Q ⊆ R := by
      rcases hQ with ⟨k, rfl⟩
      have h_inter : (dyadicCube δ k ∩ R).Nonempty := ⟨p, hpQ, hpR⟩
      exact dyadicCube_nesting hδ hδr hδ_dyadic hr_dyadic k j h_inter
    exact ⟨hQ_inA, hQ_sub⟩
  · rintro ⟨hQ_inA, hQ_sub⟩
    have hQ_cube : Q ∈ dyadicCubes 2 δ := hA_cubes Q hQ_inA
    have hQ_nonempty : Q.Nonempty := by
      rcases hQ_cube with ⟨k, rfl⟩
      exact dyadicCube_nonempty hδ k
    rcases hQ_nonempty with ⟨p, hp⟩
    have hpP : p ∈ P := by
      rw [hP]
      exact Set.mem_sUnion.mpr ⟨Q, hQ_inA, hp⟩
    have hpR : p ∈ R := hQ_sub hp
    exact ⟨hQ_cube, ⟨p, hp, ⟨hpP, hpR⟩⟩⟩

/-! ### Main trimming theorem -/

set_option maxHeartbeats 500000

/-- If `δ, r` are dyadic scales with `δ ≤ r`, then `r` is an integer multiple of `δ`. -/
private lemma dyadic_scale_multiple {δ r : ℝ} (hδ : 0 < δ)
    (hδ_dyadic : δ ∈ dyadicScales) (hr_dyadic : r ∈ dyadicScales) (hδr : δ ≤ r) :
    ∃ (m : ℕ), r = δ * (m : ℝ) := by
  rcases hδ_dyadic with ⟨n, rfl⟩
  rcases hr_dyadic with ⟨m, rfl⟩
  have hnm : n ≥ m := by
    have h : (2 : ℝ)^(-(n : ℤ)) ≤ (2 : ℝ)^(-(m : ℤ)) := hδr
    have h' : (n : ℤ) ≥ (m : ℤ) := by
      by_contra h''
      have h''' : (n : ℤ) < (m : ℤ) := by linarith
      have h4 : (2 : ℝ)^(-(n : ℤ)) > (2 : ℝ)^(-(m : ℤ)) := by
        have h5 : (-(n : ℤ) : ℝ) > (-(m : ℤ) : ℝ) := by exact_mod_cast (by linarith : -(n : ℤ) > -(m : ℤ))
        have h6 : (1 : ℝ) < (2 : ℝ) := by norm_num
        have h7 : (2 : ℝ) ^ (-(n : ℤ)) = (2 : ℝ) ^ (-(n : ℤ) : ℝ) := by norm_cast
        have h8 : (2 : ℝ) ^ (-(m : ℤ)) = (2 : ℝ) ^ (-(m : ℤ) : ℝ) := by norm_cast
        rw [h7, h8]
        exact Real.rpow_lt_rpow_of_exponent_lt h6 h5
      linarith
    exact_mod_cast h'
  let k : ℕ := 2 ^ (n - m)
  have h5 : (n - m : ℕ) = n - m := by omega
  have h6 : (k : ℝ) = (2 : ℝ)^((n - m : ℤ)) := by
    simp [k, h5] <;> norm_cast
  refine ⟨k, ?_⟩
  have h7 : (2 : ℝ)^(-(n : ℤ)) * (2 : ℝ)^((n - m : ℤ)) = (2 : ℝ)^(-(m : ℤ)) := by
    have h8 : -(n : ℤ) + (n - m : ℤ) = -(m : ℤ) := by omega
    have h9 : (2 : ℝ)^(-(n : ℤ)) * (2 : ℝ)^((n - m : ℤ)) = (2 : ℝ)^(-(n : ℤ) + (n - m : ℤ)) := by
      rw [← zpow_add₀ (by norm_num)]
    rw [h9, h8]
  have h10 : (2 : ℝ)^(-(m : ℤ)) = (2 : ℝ)^(-(n : ℤ)) * (k : ℝ) := by
    rw [h6]
    exact h7.symm
  exact h10

/-- If `δ * k < r * j` where `r = δ * m` for `m : ℕ` and `k,j : ℤ`,
then `δ * (k+1) ≤ r * j`. -/
private lemma int_grid_strict_le {δ r : ℝ} (hδ : 0 < δ) {k j : ℤ}
    (m : ℕ) (hr : r = δ * (m : ℝ)) (h : δ * (k : ℝ) < r * (j : ℝ)) :
    δ * ((k : ℝ) + 1) ≤ r * (j : ℝ) := by
  have h6 : (k : ℝ) < (m : ℝ) * (j : ℝ) := by
    rw [hr] at h
    nlinarith
  have h7 : k < m * j := by exact_mod_cast h6
  have h8 : (k + 1 : ℤ) ≤ m * j := Int.add_one_le_of_lt h7
  have h9 : ((k + 1 : ℤ) : ℝ) ≤ ((m * j : ℤ) : ℝ) := by exact_mod_cast h8
  have h10 : (k : ℝ) + 1 = ((k + 1 : ℤ) : ℝ) := by simp
  have h11 : δ * ((k : ℝ) + 1) ≤ δ * ((m * j : ℤ) : ℝ) := by
    rw [h10]; gcongr
  have h12 : δ * ((m * j : ℤ) : ℝ) = r * (j : ℝ) := by
    have h13 : ((m * j : ℤ) : ℝ) = (m : ℝ) * (j : ℝ) := by simp
    rw [h13, hr] <;> ring
  rw [h12] at h11
  exact h11

/-- **Approximate cube trimming**: given a finite family A of distinct δ-dyadic
cubes lying in an approximate-incidence strip, whose union is a (δ,s,C)-set,
produce a subfamily A' ⊆ A of controlled size whose union is a (δ,s,35*C)-set. -/
lemma approximate_cube_trimming
    {δ s C M : ℝ}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales) (hδ_le_one : δ ≤ 1)
    (hs_pos : 0 < s) (hs_lt_one : s < 1) (hC_ge1 : 1 ≤ C)
    (hM_pos : 0 < M) (hM_lower : C⁻¹ * δ ^ (-s) ≤ M)
    {x y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    {Pz : Set (EuclideanSpace ℝ (Fin 2))}
    (A : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (hA_cubes : ∀ Q ∈ A, Q ∈ dyadicCubes 2 δ)
    (hA_meet : ∀ Q ∈ A, (Q ∩ Pz).Nonempty)
    (hA_strip : ∀ Q ∈ A, ∃ p ∈ Q, |p 0 * y + p 1 - x| ≤ 2 * δ)
    (hA_regular : IsDeltaSCSet δ s C (Set.sUnion (A : Set (Set (EuclideanSpace ℝ (Fin 2))))))
    (hM_le : ENNReal.ofReal M ≤ ENat.toENNReal A.card) :
    ∃ (A' : Finset (Set (EuclideanSpace ℝ (Fin 2)))),
      A' ⊆ A ∧
      ENNReal.ofReal (M / 2) ≤ ENat.toENNReal A'.card ∧
      ENat.toENNReal A'.card ≤ ENNReal.ofReal (2 * M + 1) ∧
      IsDeltaSCSet δ s (35 * C) (Set.sUnion (A' : Set (Set (EuclideanSpace ℝ (Fin 2))))) ∧
      ∀ Q ∈ A', (Q ∩ Pz).Nonempty := by
  let P : Set (EuclideanSpace ℝ (Fin 2)) := Set.sUnion (A : Set _)
  have hP_union : P = Set.sUnion (A : Set _) := by rfl
  have hC_pos : 0 < C := by linarith
  have hs_nonneg : 0 ≤ s := by linarith
  have hP_bdd : Bornology.IsBounded P := hA_regular.1
  have hA_reg : ∀ (r : ℝ) (Q : Set (EuclideanSpace ℝ (Fin 2))),
      r ∈ dyadicScales → Q ∈ dyadicCubes 2 r → δ ≤ r → r ≤ 1 →
        ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q)) ≤
          ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber δ P) *
            ENNReal.ofReal (r ^ s) := hA_regular.2.2.2.2.2.2.2.2
  let N : ℕ := A.card
  have hN_pos : 0 < N := by
    have h1 : P.Nonempty := hA_regular.2.1
    rcases h1 with ⟨p, hp⟩
    rcases Set.mem_sUnion.mp hp with ⟨Q, hQ, _⟩
    exact Finset.card_pos.mpr ⟨Q, hQ⟩
  have hN_ge_M : (N : ℝ) ≥ M := by
    have h2 : ENNReal.ofReal M ≤ (N : ENNReal) := by
      simpa [N] using hM_le
    exact_mod_cast h2
  let kQ (Q : Set _) : Fin 2 → ℤ :=
    if hQ : Q ∈ A then Classical.choose (hA_cubes Q hQ) else fun _ => 0
  have hkQ : ∀ Q ∈ A, Q = dyadicCube δ (kQ Q) := by
    intro Q hQ
    simp [kQ, hQ]
    exact Classical.choose_spec (hA_cubes Q hQ)
  have hQ_strip : ∀ Q ∈ A, ∃ p ∈ Q, |p 0 * y + p 1 - x| ≤ 2 * δ := hA_strip
  let coord (Q : Set _) : ℤ × ℤ := (kQ Q 0, kQ Q 1)
  let rank (Q : Set _) : ℕ :=
    (A.filter (fun Q' => lexLess (coord Q') (coord Q))).card
  have h_rank_lt_N : ∀ Q ∈ A, rank Q < N := by
    intro Q hQ
    have h1 : (A.filter (fun Q' => lexLess (coord Q') (coord Q))) ⊂ A := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · exact Finset.filter_subset _ _
      · intro h
        have h2 : Q ∈ A.filter (fun Q' => lexLess (coord Q') (coord Q)) := by
          rw [h]; exact hQ
        have h3 : lexLess (coord Q) (coord Q) := (Finset.mem_filter.mp h2).2
        simp only [lexLess] at h3
        rcases h3 with (h3 | h3)
        · exact lt_irrefl _ h3
        · exact lt_irrefl _ h3.2
    exact Finset.card_lt_card h1
  have h_strict_mono : ∀ Q1 ∈ A, ∀ Q2 ∈ A,
      lexLess (coord Q1) (coord Q2) → rank Q1 < rank Q2 := by
    intro Q1 hQ1 Q2 hQ2 hlt
    have h1 : (A.filter (fun Q' => lexLess (coord Q') (coord Q1))) ⊆
        (A.filter (fun Q' => lexLess (coord Q') (coord Q2))) := by
      intro Q' hQ'
      have h2 : Q' ∈ A := (Finset.mem_filter.mp hQ').1
      have h3 : lexLess (coord Q') (coord Q1) := (Finset.mem_filter.mp hQ').2
      have h4 : lexLess (coord Q') (coord Q2) := by
        have h_trans : lexLess (coord Q') (coord Q1) → lexLess (coord Q1) (coord Q2) → lexLess (coord Q') (coord Q2) := by
          intro h3 hlt
          rcases h3 with (h31 | h32)
          · rcases hlt with (hlt1 | hlt2)
            · left; linarith
            · left; linarith [hlt2.1]
          · rcases hlt with (hlt1 | hlt2)
            · left; linarith [h32.1]
            · right; exact ⟨by linarith [h32.1, hlt2.1], by linarith [h32.2, hlt2.2]⟩
        exact h_trans h3 hlt
      exact Finset.mem_filter.mpr ⟨h2, h4⟩
    have h2 : Q1 ∈ A.filter (fun Q' => lexLess (coord Q') (coord Q2)) :=
      Finset.mem_filter.mpr ⟨hQ1, hlt⟩
    have h3 : Q1 ∉ A.filter (fun Q' => lexLess (coord Q') (coord Q1)) := by
      intro h
      have h4 : lexLess (coord Q1) (coord Q1) := (Finset.mem_filter.mp h).2
      simp only [lexLess] at h4
      rcases h4 with (h4 | h4)
      · exact lt_irrefl _ h4
      · exact lt_irrefl _ h4.2
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨h1, by intro h5; exact h3 (h5 ▸ h2)⟩)
  have h_rank_inj : Set.InjOn rank (A : Set _) := by
    intro Q1 hQ1 Q2 hQ2 h
    by_cases hlt : lexLess (coord Q1) (coord Q2)
    · have h5 : rank Q1 < rank Q2 := h_strict_mono Q1 hQ1 Q2 hQ2 hlt
      rw [h] at h5; exact False.elim (lt_irrefl _ h5)
    · by_cases hgt : lexLess (coord Q2) (coord Q1)
      · have h5 : rank Q2 < rank Q1 := h_strict_mono Q2 hQ2 Q1 hQ1 hgt
        rw [h] at h5; exact False.elim (lt_irrefl _ h5)
      · have heq : coord Q1 = coord Q2 := by
          let a := coord Q1
          let b := coord Q2
          have h1 : ¬ (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)) := hlt
          have h2 : ¬ (b.1 < a.1 ∨ (b.1 = a.1 ∧ b.2 < a.2)) := hgt
          have h3 : a.1 = b.1 := by
            have h4 : a.1 ≥ b.1 := by
              by_contra h5; have h6 : a.1 < b.1 := by linarith
              exact h1 (Or.inl h6)
            have h5 : b.1 ≥ a.1 := by
              by_contra h6; have h7 : b.1 < a.1 := by linarith
              exact h2 (Or.inl h7)
            linarith
          have h4 : a.2 = b.2 := by
            have h5 : a.2 ≥ b.2 := by
              by_contra h6; have h7 : a.2 < b.2 := by linarith
              exact h1 (Or.inr ⟨h3, h7⟩)
            have h6 : b.2 ≥ a.2 := by
              by_contra h7; have h8 : b.2 < a.2 := by linarith
              exact h2 (Or.inr ⟨by linarith, h8⟩)
            linarith
          exact Prod.ext h3 h4
        have h1 : kQ Q1 0 = kQ Q2 0 := by simp [coord] at heq <;> omega
        have h2 : kQ Q1 1 = kQ Q2 1 := by simp [coord] at heq <;> omega
        have h3 : kQ Q1 = kQ Q2 := by
          ext i; fin_cases i <;> simp [h1, h2]
        have h4 : Q1 = Q2 := by
          rw [hkQ Q1 hQ1, hkQ Q2 hQ2, h3]
        exact h4
  have h_rank_image : A.image rank = Finset.range N := by
    apply Finset.eq_of_subset_of_card_le
    · intro n hn
      rcases Finset.mem_image.mp hn with ⟨Q, hQ, rfl⟩
      exact Finset.mem_range.mpr (h_rank_lt_N Q hQ)
    · have h_card : (A.image rank).card = A.card :=
        Finset.card_image_of_injOn h_rank_inj
      rw [h_card] <;> simp [N] <;> omega
  let K_raw : ℕ := (Int.floor ((N : ℝ) / M)).toNat
  let K : ℕ := min K_raw N
  have h_floor_nonneg : 0 ≤ Int.floor ((N : ℝ) / M) := by
    have h1 : 0 ≤ (N : ℝ) / M := by positivity
    exact Int.floor_nonneg.mpr h1
  have hK_raw_pos : 0 < K_raw := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) / M := by
      rw [one_le_div (by linarith)] <;> linarith
    have h1' : 1 ≤ Int.floor ((N : ℝ) / M) := by
      exact Int.le_floor.mpr (show (↑(1 : ℤ) : ℝ) ≤ (N : ℝ) / M from by exact_mod_cast h1)
    have h2 : 0 ≤ Int.floor ((N : ℝ) / M) := by linarith
    have h3 : (K_raw : ℤ) = Int.floor ((N : ℝ) / M) := by
      rw [Int.toNat_of_nonneg h2] <;> rfl
    omega
  have hK_pos : 0 < K := by omega
  have hK_le_N : K ≤ N := Nat.min_le_right _ _
  have hK_raw_le : (K_raw : ℝ) ≤ (N : ℝ) / M := by
    have h3 : (K_raw : ℤ) = Int.floor ((N : ℝ) / M) := by
      rw [Int.toNat_of_nonneg h_floor_nonneg] <;> rfl
    have h4 : (K_raw : ℝ) = ↑(Int.floor ((N : ℝ) / M)) := by exact_mod_cast h3
    rw [h4]; exact Int.floor_le _
  have hK_raw_gt : (N : ℝ) / M < (K_raw : ℝ) + 1 := by
    have h3 : (K_raw : ℤ) = Int.floor ((N : ℝ) / M) := by
      rw [Int.toNat_of_nonneg h_floor_nonneg] <;> rfl
    have h4 : (K_raw : ℝ) = ↑(Int.floor ((N : ℝ) / M)) := by exact_mod_cast h3
    rw [h4]; exact Int.lt_floor_add_one _
  let q : ℕ := N / K
  let selected_ranks : Finset ℕ := Finset.image (fun i : ℕ => i * K) (Finset.range q)
  let A'_fin : Finset (Set (EuclideanSpace ℝ (Fin 2))) :=
    A.filter (fun Q => rank Q ∈ selected_ranks)
  have h_card : A'_fin.card = q := by
    have h1 : A'_fin.image rank = selected_ranks := by
      ext n
      simp only [A'_fin, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨T, ⟨hT, hsel⟩, rfl⟩; exact hsel
      · intro hn
        have h2 : ∃ (i : ℕ), i ∈ Finset.range q ∧ i * K = n := by
          simpa [selected_ranks] using hn
        rcases h2 with ⟨i, ⟨hi, h_eq⟩⟩
        have h3 : i * K < N := by
          have hq_def : q = N / K := by rfl
          rw [hq_def] at hi
          have h4 : i < N / K := Finset.mem_range.mp hi
          have h5 : i * K < (N / K) * K := by gcongr
          have h6 : (N / K) * K ≤ N := Nat.div_mul_le_self N K
          linarith
        have h8 : i * K ∈ A.image rank := by
          rw [h_rank_image]
          exact Finset.mem_range.mpr h3
        rcases Finset.mem_image.mp h8 with ⟨T, hT, h_eq2⟩
        have h10 : rank T ∈ selected_ranks := by
          have h11 : rank T = i * K := h_eq2
          rw [h11]
          exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
        have h13 : rank T = n := by rw [h_eq2, h_eq]
        exact ⟨T, ⟨hT, h10⟩, h13⟩
    have h_rank_inj' : Set.InjOn rank (A'_fin : Set _) := by
      intro T hT T2 hT2 h
      have hT' : T ∈ A := (Finset.mem_filter.mp hT).1
      have hT2' : T2 ∈ A := (Finset.mem_filter.mp hT2).1
      exact h_rank_inj hT' hT2' h
    have h2 : (A'_fin.image rank).card = A'_fin.card :=
      Finset.card_image_of_injOn h_rank_inj'
    rw [← h2, h1]
    have h_inj : Function.Injective (fun i : ℕ => i * K) := by
      intro i1 i2 h; apply mul_right_cancel₀ hK_pos.ne'; exact h
    have h4 : selected_ranks.card = (Finset.range q).card :=
      Finset.card_image_of_injective _ h_inj
    rw [h4] <;> simp [selected_ranks, q]
  let P' : Set (EuclideanSpace ℝ (Fin 2)) := Set.sUnion (A'_fin : Set _)
  have hP'_sub : P' ⊆ P := by
    intro p hp
    rcases Set.mem_sUnion.mp hp with ⟨Q, hQ, hpQ⟩
    have hQ_in_A : Q ∈ A := (Finset.mem_filter.mp hQ).1
    exact Set.mem_sUnion.mpr ⟨Q, hQ_in_A, hpQ⟩
  have h_trim_pos : 1 ≤ q := by
    simp [q]; apply Nat.one_le_div_iff (by omega) |>.mpr; exact hK_le_N
  have h_lower_real : (M / 2 : ℝ) ≤ (q : ℝ) := by
    by_cases hM2 : M ≤ 2
    · have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h_trim_pos
      linarith
    · have hM_gt2 : 2 < M := by linarith
      have hK_raw_lt_N : K_raw < N := by
        have h4 : (K_raw : ℝ) ≤ (N : ℝ) / M := hK_raw_le
        have h5 : (N : ℝ) / M < (N : ℝ) := by
          apply div_lt_self (by exact_mod_cast hN_pos) <;> linarith
        have h6 : (K_raw : ℝ) < (N : ℝ) := by linarith
        exact_mod_cast h6
      have hK_eq : K = K_raw := by
        simp [K] <;> omega
      have hK_le : (K : ℝ) ≤ (N : ℝ) / M := by
        rw [hK_eq] <;> exact hK_raw_le
      by_cases hK1 : K = 1
      · have hq_N : q = N := by
          simp [q, hK1, Nat.div_one]
        rw [hq_N]
        have hN_ge : (N : ℝ) ≥ M := hN_ge_M
        linarith
      · have hK_ge2 : 2 ≤ K := by omega
        have hK_pos' : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
        have hKM : (K : ℝ) * M ≤ (N : ℝ) := by
          have h : (K : ℝ) ≤ (N : ℝ) / M := hK_le
          have h5 : (K : ℝ) * M ≤ ((N : ℝ) / M) * M :=
            mul_le_mul_of_nonneg_right h hM_pos.le
          have h6 : ((N : ℝ) / M) * M = (N : ℝ) := by
            field_simp [hM_pos.ne'] <;> ring
          rw [h6] at h5; exact h5
        have hNK_ge_M : (N : ℝ) / (K : ℝ) ≥ M := by
          have h7 : ((K : ℝ) * M) / (K : ℝ) ≤ (N : ℝ) / (K : ℝ) :=
            div_le_div_of_nonneg_right hKM hK_pos'.le
          have h8 : ((K : ℝ) * M) / (K : ℝ) = M := by
            field_simp [hK_pos'.ne'] <;> ring
          rw [h8] at h7; exact h7
        have hq_ge : (q : ℝ) ≥ (N : ℝ) / (K : ℝ) - 1 := by
          have h_div : K * (N / K) + N % K = N := Nat.div_add_mod N K
          have h3 : (N : ℝ) = (q : ℝ) * (K : ℝ) + ↑(N % K) := by
            have hq' : q = N / K := rfl
            rw [hq']
            have h : (N : ℝ) = (K : ℝ) * ↑(N / K) + ↑(N % K) := by
              exact_mod_cast h_div.symm
            rw [h] <;> ring
          have h41 : N % K < K := Nat.mod_lt N hK_pos
          have h4 : ((N % K : ℕ) : ℝ) < (K : ℝ) := by exact_mod_cast h41
          have h5 : (N : ℝ) / (K : ℝ) ≤ (q : ℝ) + 1 := by
            calc (N : ℝ) / (K : ℝ)
              = ((q : ℝ) * (K : ℝ) + ↑(N % K)) / (K : ℝ) := by rw [h3]
            _ = (q : ℝ) + ↑(N % K) / (K : ℝ) := by
              field_simp [hK_pos'.ne'] <;> ring
            _ ≤ (q : ℝ) + 1 := by
              have h7 : ↑(N % K) / (K : ℝ) ≤ 1 := by
                apply (div_le_one hK_pos').mpr
                exact_mod_cast (Nat.mod_lt N hK_pos).le
              linarith
          linarith
        have hM_ge2 : 2 ≤ M := by linarith
        linarith
  have h_upper_real : (q : ℝ) ≤ 2 * M + 1 := by
    have h_case : K = K_raw ∨ K = N := by
      by_cases h : K_raw ≤ N
      · left; simp [K, h] <;> omega
      · right; simp [K, h] <;> omega
    rcases h_case with (hK_eq | hK_eq2)
    · have hK_gt : (N : ℝ) / M < (K : ℝ) + 1 := by
        rw [hK_eq] <;> exact hK_raw_gt
      have h1 : (N : ℝ) < (K : ℝ) * M + M := by
        have h2 : (N : ℝ) / M < (K : ℝ) + 1 := hK_gt
        have h3 : 0 < M := hM_pos
        calc (N : ℝ)
          = ((N : ℝ) / M) * M := by field_simp [h3.ne'] <;> ring
        _ < ((K : ℝ) + 1) * M := by gcongr
        _ = (K : ℝ) * M + M := by ring
      have h3 : (q : ℝ) ≤ (N : ℝ) / (K : ℝ) := by
        simp [q]; exact Nat.cast_div_le
      have h4 : (K : ℝ) ≥ 1 := by exact_mod_cast hK_pos
      have h5 : (N : ℝ) / (K : ℝ) < 2 * M := by
        have h6 : (N : ℝ) < (K : ℝ) * M + M := h1
        have h7 : 0 < (K : ℝ) := by exact_mod_cast hK_pos
        have h9 : (N : ℝ) / (K : ℝ) < ((K : ℝ) * M + M) / (K : ℝ) :=
          div_lt_div_of_pos_right h6 h7
        calc (N : ℝ) / (K : ℝ)
          < ((K : ℝ) * M + M) / (K : ℝ) := h9
        _ = M + M / (K : ℝ) := by field_simp [h7.ne'] <;> ring
        _ ≤ M + M := by
          have h8 : M / (K : ℝ) ≤ M := by
            apply div_le_self (by linarith) (by linarith)
          linarith
        _ = 2 * M := by ring
      have h9 : (q : ℝ) ≤ (N : ℝ) / (K : ℝ) := h3
      have h10 : (q : ℝ) < 2 * M := by linarith
      linarith
    · have hq_one : q = 1 := by
        have h : K = N := hK_eq2
        have h2 : q = N / K := rfl
        rw [h2, h]; exact Nat.div_self hN_pos
      rw [hq_one]
      have h5 : (1 : ℝ) ≤ 2 * M + 1 := by linarith [hM_pos]
      exact_mod_cast h5
  have hCMδs : 1 ≤ C * M * δ ^ s := by
    have h1 : C⁻¹ * δ^(-s) ≤ M := hM_lower
    have h2 : 0 < C := hC_pos
    have h3 : 0 < δ^s := by positivity
    have h4 : C * (C⁻¹ * δ^(-s)) * δ^s ≤ C * M * δ^s := by gcongr
    have h6 : δ^(-s) * δ^s = 1 := by
      rw [← Real.rpow_add hδ] <;> ring_nf <;> rw [Real.rpow_zero]
    have h7 : C * C⁻¹ = 1 := by field_simp [h2.ne']
    have h5 : C * (C⁻¹ * δ^(-s)) * δ^s = 1 := by
      calc C * (C⁻¹ * δ^(-s)) * δ^s
        = (C * C⁻¹) * (δ^(-s) * δ^s) := by ring
      _ = 1 * 1 := by rw [h7, h6] <;> ring
      _ = 1 := by ring
    rw [h5] at h4; exact h4
  have hP'_delta : IsDeltaSCSet δ s (35 * C) P' := by
    have hP_bdd2 : Bornology.IsBounded P := hA_regular.1
    have hP'_bdd : Bornology.IsBounded P' := hP_bdd2.subset hP'_sub
    have hP'_nonempty : P'.Nonempty := by
      have h_pos : 0 < A'_fin.card := by
        rw [h_card]; exact h_trim_pos
      rcases Finset.card_pos.mp h_pos with ⟨Q, hQ⟩
      have hQ_nonempty : Q.Nonempty := by
        have hQ_dyadic : Q ∈ dyadicCubes 2 δ := hA_cubes Q ((Finset.mem_filter.mp hQ).1)
        rcases hQ_dyadic with ⟨k, rfl⟩
        exact dyadicCube_nonempty hδ k
      rcases hQ_nonempty with ⟨p, hp⟩
      exact ⟨p, Set.mem_sUnion.mpr ⟨Q, hQ, hp⟩⟩
    have hs_le_two : s ≤ (2 : ℝ) := by linarith [hs_lt_one]
    refine ⟨hP'_bdd, hP'_nonempty, by norm_num, hδ_dyadic, hδ, hs_nonneg, hs_le_two, by positivity, ?_⟩
    intro r R hr hQ hδr hr1
    rcases hQ with ⟨j, rfl⟩
    let Q0 := dyadicCube (d := 2) r j
    let S_R := A.filter (fun Q => Q ⊆ Q0)
    let S_trim_R := A'_fin.filter (fun Q => Q ⊆ Q0)
    have hA'_cubes_common : ∀ Q ∈ A'_fin, Q ∈ dyadicCubes 2 δ := by
      intro Q hQ
      have hQ_A : Q ∈ A := (Finset.mem_filter.mp hQ).1
      exact hA_cubes Q hQ_A
    have hP'_union_common : P' = Set.sUnion (A'_fin : Set _) := by rfl
    have h_cover1_common : dyadicCoveringNumber δ (P' ∩ Q0) = ↑S_trim_R.card := by
      have h_eq := covering_cubes_eq_intersection hδ hδr hδ_dyadic hr
        hA'_cubes_common P' hP'_union_common j
      rw [dyadicCoveringNumber, h_eq]
      have h_filter_eq : (A'_fin.filter (fun Q => Q ⊆ dyadicCube r j)) = S_trim_R := by
        ext Q
        simp [S_trim_R, Q0]
      rw [h_filter_eq]
      exact Set.encard_coe_eq_coe_finsetCard _
    by_cases hSR_empty : S_R = ∅
    · have hSTR_empty : S_trim_R = ∅ := by
        by_contra h
        have hne : S_trim_R.Nonempty := Finset.nonempty_iff_ne_empty.mpr h
        rcases hne with ⟨Q, hQ⟩
        have hQ_in_A' : Q ∈ A'_fin := (Finset.mem_filter.mp hQ).1
        have hQ_sub : Q ⊆ Q0 := (Finset.mem_filter.mp hQ).2
        have hQ_in_SR : Q ∈ S_R := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hQ_in_A').1, hQ_sub⟩
        rw [hSR_empty] at hQ_in_SR <;> simpa using hQ_in_SR
      rw [h_cover1_common, hSTR_empty] <;> simp
    · have hSR_nonempty : S_R.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSR_empty
      have h_exists_min : ∃ Q_min ∈ S_R, ∀ Q ∈ S_R, rank Q_min ≤ rank Q :=
        Finset.exists_min_image S_R rank hSR_nonempty
      have h_exists_max : ∃ Q_max ∈ S_R, ∀ Q ∈ S_R, rank Q ≤ rank Q_max :=
        Finset.exists_max_image S_R rank hSR_nonempty
      rcases h_exists_min with ⟨Q_min, hQmin_in, hQmin_min⟩
      rcases h_exists_max with ⟨Q_max, hQmax_in, hQmax_max⟩
      have hQmin_A : Q_min ∈ A := (Finset.mem_filter.mp hQmin_in).1
      have hQmax_A : Q_max ∈ A := (Finset.mem_filter.mp hQmax_in).1
      have hQmin_sub : Q_min ⊆ Q0 := (Finset.mem_filter.mp hQmin_in).2
      have hQmax_sub : Q_max ⊆ Q0 := (Finset.mem_filter.mp hQmax_in).2
      have h_rank_between : ∀ Q ∈ A,
          rank Q_min ≤ rank Q → rank Q ≤ rank Q_max →
          ¬ lexLess (coord Q) (coord Q_min) ∧ ¬ lexLess (coord Q_max) (coord Q) := by
        intro Q _ h1 h2
        constructor
        · intro h
          have h3 : rank Q < rank Q_min := h_strict_mono Q ‹_› Q_min hQmin_A h
          linarith
        · intro h
          have h3 : rank Q_max < rank Q := h_strict_mono Q_max hQmax_A Q ‹_› h
          linarith
      let expanded_cubes : Finset (Set (EuclideanSpace ℝ (Fin 2))) :=
        (Finset.Icc (-7 : ℤ) 7).biUnion (fun m =>
          A.filter (fun Q => Q ⊆ dyadicCube r (fun i : Fin 2 =>
            if i = 0 then j 0 else j 1 + m)))
      have h_between_sub_expanded : ∀ Q ∈ A,
          rank Q_min ≤ rank Q → rank Q ≤ rank Q_max → Q ∈ expanded_cubes := by
        intro Q hQA h1 h2
        have h_lex := h_rank_between Q hQA h1 h2
        let k1 := kQ Q_min
        let k2 := kQ Q
        let k3 := kQ Q_max
        have h1_strip' : ∃ p ∈ dyadicCube δ k1, |p 0 * y + p 1 - x| ≤ 2 * δ := by
          have h := hQ_strip Q_min hQmin_A
          rw [hkQ Q_min hQmin_A] at h; exact h
        have h3_strip' : ∃ p ∈ dyadicCube δ k3, |p 0 * y + p 1 - x| ≤ 2 * δ := by
          have h := hQ_strip Q_max hQmax_A
          rw [hkQ Q_max hQmax_A] at h; exact h
        have h2_strip' : ∃ p ∈ dyadicCube δ k2, |p 0 * y + p 1 - x| ≤ 2 * δ := by
          have h := hQ_strip Q hQA
          rw [hkQ Q hQA] at h; exact h
        have h1_in_R' : dyadicCube δ k1 ⊆ dyadicCube r j := by
          have h : Q_min ⊆ Q0 := hQmin_sub
          rw [hkQ Q_min hQmin_A] at h; exact h
        have h3_in_R' : dyadicCube δ k3 ⊆ dyadicCube r j := by
          have h : Q_max ⊆ Q0 := hQmax_sub
          rw [hkQ Q_max hQmax_A] at h; exact h
        have h_lex1' : ¬ lexLess (k2 0, k2 1) (k1 0, k1 1) := by
          simpa [k1, k2, coord] using h_lex.1
        have h_lex2' : ¬ lexLess (k3 0, k3 1) (k2 0, k2 1) := by
          simpa [k2, k3, coord] using h_lex.2
        have h_bounds_raw := strip_contiguity_bounds hδ hδr hy0 hy1
            h1_strip' h3_strip' h2_strip' h1_in_R' h3_in_R' h_lex1' h_lex2'
        have h_eq1 : r * (j 0 : ℝ) + r = r * ((j 0 : ℝ) + 1) := by ring
        have h_eq2 : r * (j 1 : ℝ) + r + 6 * δ = r * ((j 1 : ℝ) + 1) + 6 * δ := by ring
        have h_bounds : δ * (k2 0 : ℝ) ∈ Set.Ico (r * (j 0 : ℝ)) (r * ((j 0 : ℝ) + 1)) ∧
            δ * (k2 1 : ℝ) ∈ Set.Icc (r * (j 1 : ℝ) - 6 * δ) (r * ((j 1 : ℝ) + 1) + 6 * δ) := by
          simpa [h_eq1, h_eq2] using h_bounds_raw
        have hr_pos : 0 < r := by
          rcases hr with ⟨m, rfl⟩; positivity
        have h_in_region : Q ⊆ {p : EuclideanSpace ℝ (Fin 2) |
            p 0 ∈ Set.Ico (r * (j 0 : ℝ)) (r * ((j 0 : ℝ) + 1)) ∧
            p 1 ∈ Set.Ico (r * (j 1 : ℝ) - 7 * δ) (r * ((j 1 : ℝ) + 1) + 7 * δ)} := by
          rw [hkQ Q hQA]
          intro p hp
          have h_k20_bounds : δ * (k2 0 : ℝ) ∈ Set.Ico (r * (j 0 : ℝ)) (r * ((j 0 : ℝ) + 1)) := h_bounds.1
          have h_k21_bounds : δ * (k2 1 : ℝ) ∈ Set.Icc (r * (j 1 : ℝ) - 6 * δ) (r * ((j 1 : ℝ) + 1) + 6 * δ) := h_bounds.2
          rcases dyadic_scale_multiple hδ hδ_dyadic hr hδr with ⟨m_mult, hm_mult⟩
          have h_p0_lo : r * (j 0 : ℝ) ≤ p 0 := by linarith [(hp 0).1, h_k20_bounds.1]
          have h_p0_hi : p 0 < r * ((j 0 : ℝ) + 1) := by
            let j0' : ℤ := j 0 + 1
            have h_j0' : (j0' : ℝ) = (j 0 : ℝ) + 1 := by simp [j0']
            have h9 : δ * ((k2 0 : ℝ) + 1) ≤ r * (j0' : ℝ) :=
              int_grid_strict_le hδ m_mult hm_mult (by rw [h_j0']; exact h_k20_bounds.2)
            rw [h_j0'] at h9
            linarith [(hp 0).2]
          have h_p0 : p 0 ∈ Set.Ico (r * (j 0 : ℝ)) (r * ((j 0 : ℝ) + 1)) := ⟨h_p0_lo, h_p0_hi⟩
          have h_p1_lo : r * (j 1 : ℝ) - 7 * δ ≤ p 1 := by linarith [(hp 1).1, h_k21_bounds.1]
          have h_p1_hi : p 1 < r * ((j 1 : ℝ) + 1) + 7 * δ := by linarith [(hp 1).2, h_k21_bounds.2]
          exact ⟨h_p0, ⟨h_p1_lo, h_p1_hi⟩⟩
        have h_in_union : Q ⊆ ⋃ m ∈ Finset.Icc (-7 : ℤ) 7,
            dyadicCube r (fun i : Fin 2 => if i = 0 then j 0 else j 1 + m) :=
          h_in_region.trans (expanded_region_cover hδ hr_pos hδr)
        have hQ_dyadic : Q ∈ dyadicCubes 2 δ := hA_cubes Q hQA
        have hQ_nonempty : Q.Nonempty := by
          rcases hQ_dyadic with ⟨k, rfl⟩
          exact dyadicCube_nonempty hδ k
        rcases hQ_nonempty with ⟨p, hp⟩
        have h_p_in_union : p ∈ ⋃ m ∈ Finset.Icc (-7 : ℤ) 7,
            dyadicCube r (fun i : Fin 2 => if i = 0 then j 0 else j 1 + m) :=
          h_in_union hp
        rcases Set.mem_iUnion₂.mp h_p_in_union with ⟨m, hm, hpm⟩
        have hQ_sub_cube : Q ⊆ dyadicCube r (fun i : Fin 2 => if i = 0 then j 0 else j 1 + m) := by
          rcases hQ_dyadic with ⟨k, rfl⟩
          have h_inter : (dyadicCube δ k ∩ dyadicCube r (fun i : Fin 2 => if i = 0 then j 0 else j 1 + m)).Nonempty :=
            ⟨p, hp, hpm⟩
          exact dyadicCube_nesting hδ hδr hδ_dyadic hr k _ h_inter
        have hQ_in_filter : Q ∈ A.filter (fun Q' => Q' ⊆ dyadicCube r
            (fun i : Fin 2 => if i = 0 then j 0 else j 1 + m)) :=
          Finset.mem_filter.mpr ⟨hQA, hQ_sub_cube⟩
        exact Finset.mem_biUnion.mpr ⟨m, hm, hQ_in_filter⟩
      let B_R := A.filter (fun Q => rank Q_min ≤ rank Q ∧ rank Q ≤ rank Q_max)
      have hBR_sub : B_R ⊆ expanded_cubes := by
        intro Q hQ
        have hQA : Q ∈ A := (Finset.mem_filter.mp hQ).1
        have h1 : rank Q_min ≤ rank Q := (Finset.mem_filter.mp hQ).2.1
        have h2 : rank Q ≤ rank Q_max := (Finset.mem_filter.mp hQ).2.2
        exact h_between_sub_expanded Q hQA h1 h2
      have h_trim_sub_BR : S_trim_R ⊆ B_R := by
        intro Q hQ
        have hQA' : Q ∈ A'_fin := (Finset.mem_filter.mp hQ).1
        have hQA : Q ∈ A := (Finset.mem_filter.mp hQA').1
        have hQ_sub : Q ⊆ Q0 := (Finset.mem_filter.mp hQ).2
        have hQ_in_SR : Q ∈ S_R := Finset.mem_filter.mpr ⟨hQA, hQ_sub⟩
        have h1 : rank Q_min ≤ rank Q := hQmin_min Q hQ_in_SR
        have h2 : rank Q ≤ rank Q_max := hQmax_max Q hQ_in_SR
        exact Finset.mem_filter.mpr ⟨hQA, ⟨h1, h2⟩⟩
      have h_expanded_card : (expanded_cubes.card : ℝ) ≤ 15 * C * (N : ℝ) * r ^ s := by
        have h1 : expanded_cubes.card ≤ ∑ m ∈ Finset.Icc (-7 : ℤ) 7,
            (A.filter (fun Q => Q ⊆ dyadicCube r (fun i : Fin 2 =>
              if i = 0 then j 0 else j 1 + m))).card := by
          apply Finset.card_biUnion_le
        have h1' : (expanded_cubes.card : ℝ) ≤ ∑ m ∈ Finset.Icc (-7 : ℤ) 7,
            ((A.filter (fun Q => Q ⊆ dyadicCube r (fun i : Fin 2 =>
              if i = 0 then j 0 else j 1 + m))).card : ℝ) := by
          exact_mod_cast h1
        have h2 : ∀ m ∈ Finset.Icc (-7 : ℤ) 7,
            ((A.filter (fun Q => Q ⊆ dyadicCube r (fun i : Fin 2 =>
              if i = 0 then j 0 else j 1 + m))).card : ℝ) ≤ C * (N : ℝ) * r ^ s := by
          intro m _
          let R_m := dyadicCube r (fun i : Fin 2 => if i = 0 then j 0 else j 1 + m)
          have hR_m_dyadic : R_m ∈ dyadicCubes 2 r := by
            refine' ⟨(fun i : Fin 2 => if i = 0 then j 0 else j 1 + m), rfl⟩
          have hP_reg := hA_reg r R_m hr hR_m_dyadic hδr hr1
          have h_cover : (A.filter (fun Q => Q ⊆ R_m)).card ≤ C * (N : ℝ) * r ^ s := by
            have h3 : dyadicCoveringNumber δ (P ∩ R_m) = ↑(A.filter (fun Q => Q ⊆ R_m)).card := by
              have h_eq := covering_cubes_eq_intersection hδ hδr hδ_dyadic hr
                hA_cubes P hP_union (fun i : Fin 2 => if i = 0 then j 0 else j 1 + m)
              rw [dyadicCoveringNumber, h_eq]
              exact Set.encard_coe_eq_coe_finsetCard _
            have h4 : ENat.toENNReal (dyadicCoveringNumber δ P) = (N : ENNReal) := by
              have h5 : dyadicCoveringNumber δ P = ↑N := by
                have h_eq2 : dyadicCubesMeeting δ P = (A : Set _) :=
                  covering_cubes_eq_union hδ hA_cubes P hP_union
                rw [dyadicCoveringNumber, h_eq2] <;> simp [N]
              rw [h5] <;> simp
            rw [h3, h4] at hP_reg
            exact ennreal_to_real_bound hC_pos (by linarith) hs_nonneg hP_reg
          exact h_cover
        calc (expanded_cubes.card : ℝ)
          ≤ ∑ m ∈ Finset.Icc (-7 : ℤ) 7,
              ((A.filter (fun Q => Q ⊆ dyadicCube r (fun i : Fin 2 =>
                if i = 0 then j 0 else j 1 + m))).card : ℝ) := h1'
        _ ≤ ∑ m ∈ Finset.Icc (-7 : ℤ) 7, C * (N : ℝ) * r ^ s :=
          Finset.sum_le_sum h2
        _ = 15 * (C * (N : ℝ) * r ^ s) := by
          have h3 : (Finset.Icc (-7 : ℤ) 7).card = 15 := by decide
          rw [Finset.sum_const, h3] <;> ring
        _ = 15 * C * (N : ℝ) * r ^ s := by ring
      have hBR_card : (B_R.card : ℝ) ≤ 15 * C * (N : ℝ) * r ^ s :=
        calc (B_R.card : ℝ)
          ≤ (expanded_cubes.card : ℝ) := by exact_mod_cast Finset.card_le_card hBR_sub
        _ ≤ 15 * C * (N : ℝ) * r ^ s := h_expanded_card
      have h_selected_le : S_trim_R.card ≤ (B_R.card : ℝ) / (K : ℝ) + 1 := by
        let selected_in_BR := B_R.filter (fun Q => rank Q ∈ selected_ranks)
        have h1 : S_trim_R ⊆ selected_in_BR := by
          intro Q hQ
          have h2 : Q ∈ B_R := h_trim_sub_BR hQ
          have hQ_in_A' : Q ∈ A'_fin := (Finset.mem_filter.mp hQ).1
          have h3 : rank Q ∈ selected_ranks := (Finset.mem_filter.mp hQ_in_A').2
          exact Finset.mem_filter.mpr ⟨h2, h3⟩
        have h4 : S_trim_R.card ≤ selected_in_BR.card := Finset.card_le_card h1
        have h5 : selected_in_BR.card ≤ (B_R.card : ℝ) / (K : ℝ) + 1 := by
          let S_ranks : Finset ℕ := (B_R.image rank) ∩ selected_ranks
          have hS1 : selected_in_BR.image rank = S_ranks := by
            ext n
            simp only [S_ranks, selected_in_BR, Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
            constructor
            · rintro ⟨Q, ⟨hQ_BR, hQ_sel⟩, rfl⟩
              exact ⟨⟨Q, hQ_BR, rfl⟩, hQ_sel⟩
            · rintro ⟨⟨Q, hQ_BR, rfl⟩, hQ_sel⟩
              exact ⟨Q, ⟨hQ_BR, hQ_sel⟩, rfl⟩
          have h_rank_inj_BR : Set.InjOn rank (selected_in_BR : Set _) := by
            intro Q hQ Q' hQ' h
            have hQ_BR : Q ∈ B_R := (Finset.mem_filter.mp hQ).1
            have hQ'_BR : Q' ∈ B_R := (Finset.mem_filter.mp hQ').1
            have hQ_A : Q ∈ A := (Finset.mem_filter.mp hQ_BR).1
            have hQ'_A : Q' ∈ A := (Finset.mem_filter.mp hQ'_BR).1
            exact h_rank_inj hQ_A hQ'_A h
          have h_card_eq : selected_in_BR.card = S_ranks.card := by
            rw [← Finset.card_image_of_injOn h_rank_inj_BR, hS1]
          rw [h_card_eq]
          have h_mult : ∀ n ∈ S_ranks, n % K = 0 := by
            intro n hn
            have h6 : n ∈ selected_ranks := (Finset.mem_inter.mp hn).2
            rcases Finset.mem_image.mp h6 with ⟨i, _, rfl⟩
            simp [Nat.mul_mod]
          have hBR_image : B_R.image rank = Finset.Icc (rank Q_min) (rank Q_max) := by
            ext n
            simp only [Finset.mem_image, Finset.mem_Icc]
            constructor
            · rintro ⟨Q, hQ, rfl⟩
              have h7 : rank Q_min ≤ rank Q ∧ rank Q ≤ rank Q_max :=
                (Finset.mem_filter.mp hQ).2
              exact ⟨h7.1, h7.2⟩
            · intro hn
              have h8 : n ∈ Finset.range N := by
                have h9 : n ≤ rank Q_max := hn.2
                have h10 : rank Q_max < N := h_rank_lt_N Q_max hQmax_A
                exact Finset.mem_range.mpr (by linarith)
              rw [←h_rank_image] at h8
              rcases Finset.mem_image.mp h8 with ⟨Q, hQ, rfl⟩
              have h11 : Q ∈ B_R := by
                apply Finset.mem_filter.mpr
                exact ⟨hQ, hn⟩
              exact ⟨Q, h11, rfl⟩
          have hS_sub : S_ranks ⊆ Finset.Icc (rank Q_min) (rank Q_max) := by
            intro n hn
            have h9 : n ∈ B_R.image rank := (Finset.mem_inter.mp hn).1
            rw [hBR_image] at h9
            exact h9
          have h_bound := multiples_count_bound K (rank Q_min) (rank Q_max) hK_pos
            S_ranks h_mult hS_sub
          have h_min_le_max : rank Q_min ≤ rank Q_max := hQmin_min Q_max hQmax_in
          have hBR_inj : Set.InjOn rank (B_R : Set _) := by
            intro Q hQ Q' hQ' h
            have hQ_A : Q ∈ A := (Finset.mem_filter.mp hQ).1
            have hQ'_A : Q' ∈ A := (Finset.mem_filter.mp hQ').1
            exact h_rank_inj hQ_A hQ'_A h
          have hBR_card_eq : B_R.card = (Finset.Icc (rank Q_min) (rank Q_max)).card := by
            have h : (B_R.image rank).card = B_R.card := Finset.card_image_of_injOn hBR_inj
            rw [←h, hBR_image]
          have h10 : (Finset.Icc (rank Q_min) (rank Q_max)).card =
              rank Q_max - rank Q_min + 1 := by
            rw [Nat.card_Icc]
            <;> omega
          have h11 : B_R.card = rank Q_max - rank Q_min + 1 := by
            rw [hBR_card_eq, h10]
          let a : ℕ := rank Q_max - rank Q_min
          have h_a_le : a ≤ B_R.card := by
            have h : B_R.card = a + 1 := by
              simp [h11, show a = rank Q_max - rank Q_min from rfl] <;> omega
            omega
          have h_bound' : S_ranks.card ≤ a / K + 1 := by
            simpa [show a = rank Q_max - rank Q_min from rfl] using h_bound
          have hK_pos' : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
          have h_div_le : ((a / K : ℕ) : ℝ) ≤ (a : ℝ) / (K : ℝ) := by
            have h_mul : ((a / K : ℕ) : ℝ) * (K : ℝ) = ↑((a / K) * K) := by
              rw [Nat.cast_mul]
            have h_le_nat : (a / K) * K ≤ a := Nat.div_mul_le_self a K
            have h' : ((a / K : ℕ) : ℝ) * (K : ℝ) ≤ (a : ℝ) := by
              rw [h_mul]
              exact_mod_cast h_le_nat
            calc ((a / K : ℕ) : ℝ)
              = (((a / K : ℕ) : ℝ) * (K : ℝ)) / (K : ℝ) := by field_simp [hK_pos'.ne'] <;> ring
            _ ≤ (a : ℝ) / (K : ℝ) := by
              exact div_le_div_of_nonneg_right h' hK_pos'.le
          have h12 : (S_ranks.card : ℝ) ≤ (a : ℝ) / (K : ℝ) + 1 := by
            have h121 : (S_ranks.card : ℝ) ≤ ↑(a / K + 1) := by exact_mod_cast h_bound'
            have h122 : ↑(a / K + 1) = ((a / K : ℕ) : ℝ) + 1 := by simp
            rw [h122] at h121
            linarith
          have h13 : (a : ℝ) / (K : ℝ) ≤ (B_R.card : ℝ) / (K : ℝ) := by
            have h14 : (a : ℝ) ≤ (B_R.card : ℝ) := by exact_mod_cast h_a_le
            exact div_le_div_of_nonneg_right h14 hK_pos'.le
          linarith
        have h6 : (S_trim_R.card : ℝ) ≤ (selected_in_BR.card : ℝ) := by
          exact Nat.cast_le.mpr h4
        linarith
      have h_final : (S_trim_R.card : ℝ) ≤ 35 * C * (q : ℝ) * r ^ s := by
        have hr_pos : 0 < r := by
          rcases hr with ⟨m, rfl⟩
          positivity
        have hr_nonneg : 0 ≤ r := by linarith
        have hrs_nonneg : 0 ≤ r ^ s := Real.rpow_nonneg hr_nonneg s
        have hC_nonneg : 0 ≤ C := by linarith
        have hK_nonneg : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
        have h1 : (S_trim_R.card : ℝ) ≤ (B_R.card : ℝ) / (K : ℝ) + 1 := h_selected_le
        have h2 : (B_R.card : ℝ) ≤ 15 * C * (N : ℝ) * r ^ s := by exact_mod_cast hBR_card
        have h3 : (B_R.card : ℝ) / (K : ℝ) ≤ 15 * C * ((q : ℝ) + 1) * r ^ s := by
          have h4 : (N : ℝ) / (K : ℝ) ≤ (q : ℝ) + 1 := by
            have h_div : K * (N / K) + N % K = N := Nat.div_add_mod N K
            have h5 : (N : ℝ) = (q : ℝ) * (K : ℝ) + ↑(N % K) := by
              have hq' : q = N / K := rfl
              rw [hq']
              have h : (N : ℝ) = (K : ℝ) * ↑(N / K) + ↑(N % K) := by
                exact_mod_cast h_div.symm
              rw [h] <;> ring
            have h6 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
            have h7 : (N : ℝ) / (K : ℝ) = (q : ℝ) + ↑(N % K) / (K : ℝ) := by
              rw [h5]; field_simp [h6.ne'] <;> ring
            rw [h7]
            have h8 : ↑(N % K) / (K : ℝ) ≤ 1 := by
              have h9 : ↑(N % K) ≤ (K : ℝ) := by exact_mod_cast (Nat.mod_lt N hK_pos).le
              have h10 : ↑(N % K) / (K : ℝ) ≤ (K : ℝ) / (K : ℝ) := div_le_div_of_nonneg_right h9 hK_nonneg
              have h11 : (K : ℝ) / (K : ℝ) = 1 := by field_simp [h6.ne'] <;> ring
              rw [h11] at h10; exact h10
            linarith
          calc (B_R.card : ℝ) / (K : ℝ)
            ≤ (15 * C * (N : ℝ) * r ^ s) / (K : ℝ) := div_le_div_of_nonneg_right h2 hK_nonneg
          _ = 15 * C * ((N : ℝ) / (K : ℝ)) * r ^ s := by ring
          _ ≤ 15 * C * ((q : ℝ) + 1) * r ^ s := by
            have h_pos : 0 ≤ 15 * C * r ^ s := by
              have h1 : 0 ≤ 15 * C := by linarith
              exact mul_nonneg h1 hrs_nonneg
            nlinarith
        have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h_trim_pos
        have h_absorb : (1 : ℝ) ≤ 2 * C * (q : ℝ) * r ^ s := by
          have h9 : (1 : ℝ) ≤ C * M * δ ^ s := hCMδs
          have h10 : (M / 2 : ℝ) ≤ (q : ℝ) := h_lower_real
          have h11 : δ ^ s ≤ r ^ s := by
            apply Real.rpow_le_rpow <;> linarith <;> exact hs_nonneg
          have h12 : (1 : ℝ) / 2 ≤ C * (q : ℝ) * r ^ s := by
            have h13 : C * (M / 2 : ℝ) * δ ^ s = (C * M * δ ^ s) / 2 := by ring
            have h14 : (1 : ℝ) / 2 ≤ C * (M / 2 : ℝ) * δ ^ s := by
              rw [h13]
              have h15 : (1 : ℝ) / 2 ≤ (C * M * δ ^ s) / 2 := by gcongr
              exact h15
            have h16 : C * (M / 2 : ℝ) * δ ^ s ≤ C * (q : ℝ) * r ^ s := by
              gcongr <;> linarith
            exact h14.trans h16
          have h17 : (1 : ℝ) ≤ 2 * (C * (q : ℝ) * r ^ s) := by linarith
          have h18 : 2 * (C * (q : ℝ) * r ^ s) = 2 * C * (q : ℝ) * r ^ s := by ring
          rw [h18] at h17; exact h17
        have h4 : (S_trim_R.card : ℝ) ≤ 15 * C * ((q : ℝ) + 1) * r ^ s + 1 := by linarith
        have h5 : (S_trim_R.card : ℝ) ≤ 15 * C * ((q : ℝ) + 1) * r ^ s + 2 * C * (q : ℝ) * r ^ s := by
          calc (S_trim_R.card : ℝ)
            ≤ 15 * C * ((q : ℝ) + 1) * r ^ s + 1 := h4
          _ ≤ 15 * C * ((q : ℝ) + 1) * r ^ s + 2 * C * (q : ℝ) * r ^ s := by
            gcongr <;> linarith
        have h6 : 15 * C * ((q : ℝ) + 1) * r ^ s + 2 * C * (q : ℝ) * r ^ s ≤ 35 * C * (q : ℝ) * r ^ s := by
          have h7 : 17 * (q : ℝ) + 15 ≤ 35 * (q : ℝ) := by linarith
          have h8 : 15 * C * ((q : ℝ) + 1) * r ^ s + 2 * C * (q : ℝ) * r ^ s =
              C * r ^ s * (17 * (q : ℝ) + 15) := by ring
          have h9 : 35 * C * (q : ℝ) * r ^ s = C * r ^ s * (35 * (q : ℝ)) := by ring
          rw [h8, h9]
          have h10 : 0 ≤ C * r ^ s := mul_nonneg hC_nonneg hrs_nonneg
          nlinarith
        have h_final2 : (S_trim_R.card : ℝ) ≤ 35 * C * (q : ℝ) * r ^ s := by
          calc (S_trim_R.card : ℝ)
            ≤ 15 * C * ((q : ℝ) + 1) * r ^ s + 2 * C * (q : ℝ) * r ^ s := h5
          _ ≤ 35 * C * (q : ℝ) * r ^ s := h6
        exact h_final2
      have h_cover2 : dyadicCoveringNumber δ P' = ↑A'_fin.card := by
        have h_eq := covering_cubes_eq_union hδ hA'_cubes_common P' hP'_union_common
        rw [dyadicCoveringNumber, h_eq]
        <;> simp
      rw [h_cover1_common, h_cover2, h_card]
      have hpos1 : 0 ≤ 35 * C := by linarith
      have hpos2 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
      have hpos3 : 0 ≤ r ^ s := Real.rpow_nonneg (by linarith) s
      have h13 : ENat.toENNReal S_trim_R.card ≤
          ENNReal.ofReal ((35 * C) * (q : ℝ) * r ^ s) := by
        have h14 : (S_trim_R.card : ℝ) ≤ (35 * C) * (q : ℝ) * r ^ s := h_final
        have h15 : ENat.toENNReal S_trim_R.card = ENNReal.ofReal (S_trim_R.card : ℝ) := by simp
        rw [h15]
        exact ENNReal.ofReal_le_ofReal h14
      have h14 : ENNReal.ofReal ((35 * C) * (q : ℝ) * r ^ s) =
          ENNReal.ofReal (35 * C) * (↑q : ENNReal) * ENNReal.ofReal (r ^ s) := by
        have h1 : ENNReal.ofReal ((35 * C) * (q : ℝ)) =
            ENNReal.ofReal (35 * C) * ENNReal.ofReal (q : ℝ) := ENNReal.ofReal_mul hpos1
        have h2 : ENNReal.ofReal (((35 * C) * (q : ℝ)) * r ^ s) =
            ENNReal.ofReal ((35 * C) * (q : ℝ)) * ENNReal.ofReal (r ^ s) :=
          ENNReal.ofReal_mul (mul_nonneg hpos1 hpos2)
        have h3 : ENNReal.ofReal (q : ℝ) = (↑q : ENNReal) := by simp
        have h4 : ENNReal.ofReal ((35 * C) * (q : ℝ) * r ^ s) =
            ENNReal.ofReal (((35 * C) * (q : ℝ)) * r ^ s) := by ring_nf
        rw [h4, h2, h1, h3] <;> ring
      exact h13.trans_eq h14
  have h_cover_P' : dyadicCoveringNumber δ P' = ↑A'_fin.card := by
    have hA'_cubes : ∀ Q ∈ A'_fin, Q ∈ dyadicCubes 2 δ := by
      intro Q hQ
      have hQ_A : Q ∈ A := (Finset.mem_filter.mp hQ).1
      exact hA_cubes Q hQ_A
    have hP'_union : P' = Set.sUnion (A'_fin : Set _) := by rfl
    have h_eq := covering_cubes_eq_union hδ hA'_cubes P' hP'_union
    rw [dyadicCoveringNumber, h_eq]
    <;> simp
  refine' ⟨A'_fin, Finset.filter_subset _ _, ?_, ?_, hP'_delta, ?_⟩
  · have h3 : ENat.toENNReal A'_fin.card = ENNReal.ofReal (A'_fin.card : ℝ) := by simp
    have h4 : (A'_fin.card : ℝ) = (q : ℝ) := by exact_mod_cast h_card
    rw [h3, h4]
    exact ENNReal.ofReal_le_ofReal h_lower_real
  · have h3 : ENat.toENNReal A'_fin.card = ENNReal.ofReal (A'_fin.card : ℝ) := by simp
    have h4 : (A'_fin.card : ℝ) = (q : ℝ) := by exact_mod_cast h_card
    rw [h3, h4]
    exact ENNReal.ofReal_le_ofReal h_upper_real
  · intro Q hQ
    have hQ_in_A : Q ∈ A := (Finset.mem_filter.mp hQ).1
    exact hA_meet Q hQ_in_A

end ProductLikeIncidence.ProductReduction
