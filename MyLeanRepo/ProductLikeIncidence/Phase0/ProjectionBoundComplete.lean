module

/-
# Projection Bound — Complete Self-Contained Implementation

Uses C1=C (original double count) and C2=C_work=35C (Tbar lower bound).
Keeps 35² as a FIXED constant, does NOT charge it as δ-exponent.

Exponent budget:
- Double count uses original C^{-1} (exact from Phase0)
- Tbar lower bound uses C_work^{-4} (exact match from Phase0)
- C1=C (original double count), C2=C_work=35C (Tbar lower bound)
- Combined factor: C1·C2² = C·(35C)² = 35²·C³ ≤ 35² · δ^{-3η}
- Pre-absorption: 14√98 · 35² · C³ · δ^{-3η/2} ≤ 14√98 · 35² · δ^{-9η/2}
- Weaken δ^{-9η/2} ≤ δ^{-6η} (for δ<1)
- Neighborhood factor 9: 126√98 · 35² · δ^{-6η}
- Absorb into δ^{-7η} (L=7): need 126√98 · 35² ≤ δ^{-η}

Contains:
1. projection_comparison_algebra_gen — generalized real algebra (C1, C2 separate)
2. projection_comparison_bound_gen — ENNReal wrapper
3. grid_covering_eq_card — Nδ(X_y) = |X_y| for δ-grid subsets
4. cube_family_le_covering — |Tbar| ≤ Nplane(⋃₀ Tbar)
5. projection_bound_full — main lemma
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.Compat
public import MyLeanRepo.CubeIndexSet
public import MyLeanRepo.ProductLikeIncidence.Phase0.OverlapBound
public import MyLeanRepo.ProductLikeIncidence.Phase0.ProjectionCovering
public import MyLeanRepo.ProductLikeIncidence.Phase0.DoubleCountHelper
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Bornology ENNReal Finset Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-! ## 1. Generalized Projection Comparison Algebra -/

/-- Pure-real algebra with separate C1 (double-count) and C2 (Tbar) constants.
Conclusion: Xcard ≤ 14√98 · C1 · C2² · δ^{-3η/2} · √Tbarcard -/
lemma projection_comparison_algebra_gen
    {δ s η C1 C2 Xcard Tcard Tbarcard : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (hη_pos : 0 < η)
    (hC1_pos : 0 < C1) (hC2_pos : 0 < C2)
    (hX_nonneg : 0 ≤ Xcard) (hTbar_pos : 0 < Tbarcard)
    (h1 : Xcard * ((1/2:ℝ) * C1⁻¹ * δ ^ (-s)) ≤ 7 * Tcard)
    (h2 : Tcard < δ ^ (-(2 * s + η)))
    (h3 : Tbarcard ≥ δ ^ (-2 * s + η) / (98 * C2 ^ 4)) :
    Xcard ≤ 14 * Real.sqrt 98 * C1 * C2^2 * δ ^ (-3 * η / 2) * Real.sqrt Tbarcard := by
  set fiber : ℝ := (1 / 2 : ℝ) * C1⁻¹ * δ ^ (-s) with hfiber_def
  have h_fiber_pos : 0 < fiber := by positivity
  have rpow_add' : ∀ (a b : ℝ), δ ^ a * δ ^ b = δ ^ (a + b) := by
    intro a b; rw [← Real.rpow_add hδ_pos] <;> ring
  have rpow_sub' : ∀ (a b : ℝ), δ ^ a / δ ^ b = δ ^ (a - b) := by
    intro a b; rw [Real.rpow_sub hδ_pos] <;> ring

  have h4 : Xcard * fiber < 7 * δ ^ (-(2 * s + η)) := by
    calc Xcard * fiber ≤ 7 * Tcard := h1
         _ < 7 * δ ^ (-(2 * s + η)) := by gcongr

  have h_fiber_inv : fiber⁻¹ = 2 * C1 * δ ^ s := by
    rw [hfiber_def]
    have h : ((1 / 2 : ℝ) * C1⁻¹ * δ ^ (-s))⁻¹ =
        (1 / 2 : ℝ)⁻¹ * (C1⁻¹)⁻¹ * (δ ^ (-s))⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev] <;> ring
    rw [h]
    have h2 : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
    have h3 : (C1⁻¹)⁻¹ = C1 := by field_simp [hC1_pos.ne'] <;> ring
    have h4 : (δ ^ (-s))⁻¹ = δ ^ s := by
      rw [← Real.rpow_neg hδ_pos.le] <;> ring_nf
    rw [h2, h3, h4] <;> ring

  have hX_upper : Xcard < 14 * C1 * δ ^ (-s - η) := by
    have h5 : Xcard < (7 * δ ^ (-(2 * s + η))) * fiber⁻¹ := by
      have h_eq : Xcard = (Xcard * fiber) * fiber⁻¹ := by
        field_simp [h_fiber_pos.ne'] <;> ring
      rw [h_eq]; gcongr
    rw [h_fiber_inv] at h5
    have h6 : (7 * δ ^ (-(2 * s + η))) * (2 * C1 * δ ^ s) = 14 * C1 * δ ^ (-s - η) := by
      have h7 : δ ^ (-(2 * s + η)) * δ ^ s = δ ^ (-s - η) := by
        rw [rpow_add' (-(2 * s + η)) s] <;> ring_nf
      have h8 : (7 * δ ^ (-(2 * s + η))) * (2 * C1 * δ ^ s) =
          14 * (δ ^ (-(2 * s + η)) * δ ^ s) * C1 := by ring
      rw [h8, h7] <;> ring
    rw [h6] at h5; exact h5

  have h_sqrt_lower : Real.sqrt Tbarcard ≥ δ ^ (-s + η / 2) / (Real.sqrt 98 * C2 ^ 2) := by
    have h_pos : 0 ≤ δ ^ (-2 * s + η) / (98 * C2 ^ 4) := by positivity
    have h1 : Real.sqrt Tbarcard ≥ Real.sqrt (δ ^ (-2 * s + η) / (98 * C2 ^ 4)) :=
      Real.sqrt_le_sqrt h3
    have h2 : Real.sqrt (δ ^ (-2 * s + η) / (98 * C2 ^ 4)) =
        δ ^ (-s + η / 2) / (Real.sqrt 98 * C2 ^ 2) := by
      have h31 : Real.sqrt (δ ^ (-2 * s + η) / (98 * C2 ^ 4)) =
          Real.sqrt (δ ^ (-2 * s + η)) / Real.sqrt (98 * C2 ^ 4) := by
        rw [Real.sqrt_div (by positivity)]
      rw [h31]
      have h4 : Real.sqrt (δ ^ (-2 * s + η)) = δ ^ (-s + η / 2) := by
        rw [Real.sqrt_eq_rpow]
        have h5 : (δ ^ (-2 * s + η)) ^ (1 / 2 : ℝ) = δ ^ ((-2 * s + η) * (1 / 2 : ℝ)) := by
          rw [← Real.rpow_mul hδ_pos.le] <;> ring
        rw [h5] <;> ring_nf
      have h6 : Real.sqrt (98 * C2 ^ 4) = Real.sqrt 98 * C2 ^ 2 := by
        have h7 : Real.sqrt (98 * C2 ^ 4) = Real.sqrt 98 * Real.sqrt (C2 ^ 4) := by
          rw [Real.sqrt_mul] <;> positivity
        rw [h7]
        have h8 : Real.sqrt (C2 ^ 4) = C2 ^ 2 := by
          have h9 : C2 ^ 4 = (C2 ^ 2) ^ 2 := by ring
          rw [h9, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
        rw [h8] <;> ring
      rw [h4, h6] <;> ring
    rw [h2] at h1; exact h1

  have h_sqrt_pos : 0 < Real.sqrt Tbarcard := Real.sqrt_pos.mpr hTbar_pos
  have h_pos5 : 0 < δ ^ (-s + η / 2) := by positivity
  have h_pos6 : 0 < Real.sqrt 98 * C2 ^ 2 := by positivity

  have h_inner_inv : (δ ^ (-s + η / 2) / (Real.sqrt 98 * C2 ^ 2))⁻¹ =
      (Real.sqrt 98 * C2 ^ 2) / δ ^ (-s + η / 2) := by
    rw [inv_div] <;> positivity

  have h_div1 : Xcard / Real.sqrt Tbarcard ≤
      Xcard / (δ ^ (-s + η / 2) / (Real.sqrt 98 * C2 ^ 2)) := by
    gcongr
  have h_pos7 : 0 < δ ^ (-s + η / 2) / (Real.sqrt 98 * C2 ^ 2) := by positivity
  have h_div2 : Xcard / (δ ^ (-s + η / 2) / (Real.sqrt 98 * C2 ^ 2)) <
      (14 * C1 * δ ^ (-s - η)) / (δ ^ (-s + η / 2) / (Real.sqrt 98 * C2 ^ 2)) := by
    gcongr
  have h_div : Xcard / Real.sqrt Tbarcard <
      (14 * C1 * δ ^ (-s - η)) * ((Real.sqrt 98 * C2 ^ 2) / δ ^ (-s + η / 2)) := by
    have h9 : Xcard / Real.sqrt Tbarcard <
        (14 * C1 * δ ^ (-s - η)) / (δ ^ (-s + η / 2) / (Real.sqrt 98 * C2 ^ 2)) :=
      lt_of_le_of_lt h_div1 h_div2
    have h10 : (14 * C1 * δ ^ (-s - η)) / (δ ^ (-s + η / 2) / (Real.sqrt 98 * C2 ^ 2)) =
        (14 * C1 * δ ^ (-s - η)) * (δ ^ (-s + η / 2) / (Real.sqrt 98 * C2 ^ 2))⁻¹ := by
      rw [div_eq_mul_inv]
    rw [h10, h_inner_inv] at h9
    exact h9

  have h_step2 : (14 * C1 * δ ^ (-s - η)) * ((Real.sqrt 98 * C2 ^ 2) / δ ^ (-s + η / 2)) =
      14 * Real.sqrt 98 * C1 * C2 ^ 2 * (δ ^ (-s - η) / δ ^ (-s + η / 2)) := by
    have h_mult : (14 * C1 * δ ^ (-s - η)) * (Real.sqrt 98 * C2 ^ 2) =
        14 * Real.sqrt 98 * C1 * C2 ^ 2 * δ ^ (-s - η) := by ring
    have h : (14 * C1 * δ ^ (-s - η)) * ((Real.sqrt 98 * C2 ^ 2) / δ ^ (-s + η / 2)) =
        ((14 * C1 * δ ^ (-s - η)) * (Real.sqrt 98 * C2 ^ 2)) / δ ^ (-s + η / 2) := by
      simp [mul_div_assoc] <;> ring
    rw [h, h_mult] <;> simp [mul_div_assoc] <;> ring

  have h_exp2 : δ ^ (-s - η) / δ ^ (-s + η / 2) = δ ^ (-3 * η / 2) := by
    rw [rpow_sub' (-s - η) (-s + η / 2)] <;> ring_nf

  have h_ratio : Xcard / Real.sqrt Tbarcard <
      14 * Real.sqrt 98 * C1 * C2 ^ 2 * δ ^ (-3 * η / 2) := by
    rw [h_step2, h_exp2] at h_div
    exact h_div

  have h12 : Xcard < (14 * Real.sqrt 98 * C1 * C2 ^ 2 * δ ^ (-3 * η / 2)) * Real.sqrt Tbarcard := by
    have h13 : Xcard = (Xcard / Real.sqrt Tbarcard) * Real.sqrt Tbarcard := by
      field_simp [h_sqrt_pos.ne'] <;> ring
    rw [h13]
    gcongr
  exact le_of_lt h12

/-! ## 2. ENNReal Wrapper for Generalized Comparison -/

/-- Generalized projection comparison bound with separate C1, C2 constants.
|X_y| ≤ 14√98 · C1 · C2² · δ^{-3η/2} · √|Tbar| -/
lemma projection_comparison_bound_gen
    {δ s η C1 C2 : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hs_pos : 0 < s) (hη_pos : 0 < η)
    (hC1_pos : 0 < C1) (hC2_pos : 0 < C2)
    {X_y : Set ℝ}
    {T Tbar : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hX_finite : X_y.Finite)
    (hT_finite : T.Finite)
    (hTbar_finite : Tbar.Finite)
    (h_double_count : (X_y.encard : ENNReal) *
        ENNReal.ofReal ((1/2:ℝ) * C1⁻¹ * δ ^ (-s)) ≤
        ENNReal.ofReal (7 : ℝ) * (T.encard : ENNReal))
    (hT_upper : (T.encard : ENNReal) < ENNReal.ofReal (δ ^ (-(2 * s + η))))
    (hTbar_lower : ENNReal.ofReal (δ ^ (-2 * s + η) / (98 * C2 ^ 4)) ≤
        (Tbar.encard : ENNReal)) :
    (X_y.encard : ENNReal) ≤
        ENNReal.ofReal (14 * Real.sqrt 98 * C1 * C2^2 * δ ^ (-3 * η / 2)) *
        ENNReal.ofReal (Real.sqrt ((Tbar.encard : ENNReal).toReal)) := by
  let Xfin := hX_finite.toFinset
  let Tfin := hT_finite.toFinset
  let Tbarfin := hTbar_finite.toFinset
  let Xcard : ℝ := Xfin.card
  let Tcard : ℝ := Tfin.card
  let Tbarcard : ℝ := Tbarfin.card

  have hX_encard : (X_y.encard : ENNReal) = ↑Xfin.card := by
    have h1 : X_y.encard = ↑Xfin.card := Finite.encard_eq_coe_toFinset_card hX_finite
    exact_mod_cast h1
  have hT_encard : (T.encard : ENNReal) = ↑Tfin.card := by
    have h1 : T.encard = ↑Tfin.card := Finite.encard_eq_coe_toFinset_card hT_finite
    exact_mod_cast h1
  have hTbar_encard : (Tbar.encard : ENNReal) = ↑Tbarfin.card := by
    have h1 : Tbar.encard = ↑Tbarfin.card := Finite.encard_eq_coe_toFinset_card hTbar_finite
    exact_mod_cast h1

  let fiber : ℝ := (1 / 2 : ℝ) * C1⁻¹ * δ ^ (-s)
  have h_fiber_pos : 0 < fiber := by positivity

  have h1_real : Xcard * fiber ≤ 7 * Tcard := by
    rw [hX_encard, hT_encard] at h_double_count
    set a : ENNReal := (↑Xfin.card : ENNReal) * ENNReal.ofReal fiber with ha
    set b : ENNReal := ENNReal.ofReal (7 : ℝ) * (↑Tfin.card : ENNReal) with hb
    have h_ne_top1 : a ≠ ⊤ := by rw [ha]; apply mul_ne_top <;> simp <;> positivity
    have h_ne_top2 : b ≠ ⊤ := by rw [hb]; apply mul_ne_top <;> simp <;> positivity
    have h_toReal : a.toReal ≤ b.toReal := (ENNReal.toReal_le_toReal h_ne_top1 h_ne_top2).mpr h_double_count
    have h_left : a.toReal = (↑Xfin.card : ℝ) * fiber := by
      rw [ha, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] <;> simp <;> ring
    have h_right : b.toReal = 7 * (↑Tfin.card : ℝ) := by
      rw [hb, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] <;> simp <;> ring
    rw [h_left, h_right] at h_toReal
    simpa [Xcard, Tcard] using h_toReal

  have h2_real : Tcard < δ ^ (-(2 * s + η)) := by
    rw [hT_encard] at hT_upper
    exact natCast_lt_ofReal.mp hT_upper

  have h3_real : Tbarcard ≥ δ ^ (-2 * s + η) / (98 * C2 ^ 4) := by
    rw [hTbar_encard] at hTbar_lower
    exact ofReal_le_natCast.mp hTbar_lower

  have hTbar_pos : 0 < Tbarcard := by
    have h_pos2 : 0 < δ ^ (-2 * s + η) / (98 * C2 ^ 4) := by positivity
    linarith [h3_real]

  have h_main : Xcard ≤ 14 * Real.sqrt 98 * C1 * C2^2 * δ ^ (-3 * η / 2) * Real.sqrt Tbarcard :=
    projection_comparison_algebra_gen hδ_pos hδ_lt_one hη_pos hC1_pos hC2_pos
      (by positivity) hTbar_pos h1_real h2_real h3_real

  have hX_eq : (X_y.encard : ENNReal).toReal = Xcard := by
    rw [hX_encard] <;> simp [Xcard] <;> norm_cast
  have hTbar_eq : (Tbar.encard : ENNReal).toReal = Tbarcard := by
    rw [hTbar_encard] <;> simp [Tbarcard] <;> norm_cast
  have h_nonneg : 0 ≤ 14 * Real.sqrt 98 * C1 * C2^2 * δ ^ (-3 * η / 2) * Real.sqrt Tbarcard := by positivity
  have hX_ennreal : (X_y.encard : ENNReal) = ENNReal.ofReal Xcard := by
    rw [hX_encard] <;> simp [Xcard] <;> norm_cast
  have h_ennreal : (X_y.encard : ENNReal) ≤
      ENNReal.ofReal (14 * Real.sqrt 98 * C1 * C2^2 * δ ^ (-3 * η / 2) * Real.sqrt Tbarcard) := by
    rw [hX_ennreal]
    rw [ENNReal.ofReal_le_ofReal_iff h_nonneg]
    exact h_main
  have h_mul : ENNReal.ofReal (14 * Real.sqrt 98 * C1 * C2^2 * δ ^ (-3 * η / 2) * Real.sqrt Tbarcard) =
      ENNReal.ofReal (14 * Real.sqrt 98 * C1 * C2^2 * δ ^ (-3 * η / 2)) *
      ENNReal.ofReal (Real.sqrt Tbarcard) := by
    rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
  rw [h_mul] at h_ennreal
  have h_final : ENNReal.ofReal (Real.sqrt Tbarcard) =
      ENNReal.ofReal (Real.sqrt ((Tbar.encard : ENNReal).toReal)) := by
    rw [hTbar_eq]
  rw [h_final] at h_ennreal
  exact h_ennreal

/-! ## 3. Grid Covering Equals Cardinality -/

/-- For a subset X_y of the δ-grid, the dyadic covering number equals cardinality. -/
lemma grid_covering_eq_card
    {δ : ℝ} (hδ_pos : 0 < δ)
    {X_y : Set ℝ} (_hX_finite : X_y.Finite)
    (hX_grid : X_y ⊆ productLikeIntegerGrid δ)
    (hX_bdd : Bornology.IsBounded X_y) :
    ENat.toENNReal (dyadicCoveringNumber (d := 1) δ (productLikeRealLineCopy X_y)) =
      ENat.toENNReal X_y.encard := by
  have h_eq1 : ENat.toENNReal (dyadicCoveringNumber (d := 1) δ (productLikeRealLineCopy X_y)) =
      ENat.toENNReal (realCubeIndexSet δ X_y).encard :=
    realCoveringNumber_eq_card_ennreal hδ_pos hX_bdd
  rw [h_eq1]
  let f : ℝ → ℤ := fun x => Int.floor (x / δ)
  have h_inj : Set.InjOn f X_y := by
    intro x hx y hy h_eq
    have hx_grid : x ∈ productLikeIntegerGrid δ := hX_grid hx
    have hy_grid : y ∈ productLikeIntegerGrid δ := hX_grid hy
    rcases hx_grid with ⟨kx, rfl⟩
    rcases hy_grid with ⟨ky, rfl⟩
    have h_floor_x : f (δ * (kx : ℝ)) = kx := by
      dsimp only [f]
      have h : (δ * (kx : ℝ)) / δ = (kx : ℝ) := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [h]; simp
    have h_floor_y : f (δ * (ky : ℝ)) = ky := by
      dsimp only [f]
      have h : (δ * (ky : ℝ)) / δ = (ky : ℝ) := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [h]; simp
    have h_eq2 : f (δ * (kx : ℝ)) = f (δ * (ky : ℝ)) := h_eq
    rw [h_floor_x, h_floor_y] at h_eq2
    have h_k_eq : kx = ky := by exact_mod_cast h_eq2
    rw [h_k_eq]
  have h_image : f '' X_y = realCubeIndexSet δ X_y := by
    ext k
    simp only [Set.mem_image, realCubeIndexSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : x ∈ Set.Ico (δ * (f x : ℝ)) (δ * ((f x : ℝ) + 1)) := by
        dsimp only [f]
        have h2 : (Int.floor (x / δ) : ℝ) ≤ x / δ := Int.floor_le (x / δ)
        have h3 : x / δ < (Int.floor (x / δ) : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
        have h4 : δ * (Int.floor (x / δ) : ℝ) ≤ x := by
          calc δ * (Int.floor (x / δ) : ℝ) ≤ δ * (x / δ) := by gcongr
            _ = x := by field_simp [hδ_pos.ne'] <;> ring
        have h5 : x < δ * ((Int.floor (x / δ) : ℝ) + 1) := by
          calc x = δ * (x / δ) := by field_simp [hδ_pos.ne'] <;> ring
            _ < δ * ((Int.floor (x / δ) : ℝ) + 1) := by gcongr
        exact ⟨h4, h5⟩
      exact ⟨x, ⟨h1, hx⟩⟩
    · rintro ⟨x, hx⟩
      have h_ineq1 : (k : ℝ) ≤ x / δ := by
        have h : δ * (k : ℝ) ≤ x := hx.1.1
        have h2 : (k : ℝ) ≤ x / δ := by
          calc (k : ℝ) = (δ * (k : ℝ)) / δ := by field_simp [hδ_pos.ne'] <;> ring
            _ ≤ x / δ := by gcongr
        exact h2
      have h_ineq2 : x / δ < (k : ℝ) + 1 := by
        have h : x < δ * ((k : ℝ) + 1) := hx.1.2
        have h2 : x / δ < (k : ℝ) + 1 := by
          calc x / δ < (δ * ((k : ℝ) + 1)) / δ := by gcongr
            _ = (k : ℝ) + 1 := by field_simp [hδ_pos.ne'] <;> ring
        exact h2
      have h_floor_eq : Int.floor (x / δ) = k := by
        rw [Int.floor_eq_iff]
        exact ⟨by exact_mod_cast h_ineq1, by exact_mod_cast h_ineq2⟩
      exact ⟨x, hx.2, by simpa [f] using h_floor_eq⟩
  have h_encard : X_y.encard = (realCubeIndexSet δ X_y).encard := by
    rw [←h_image]
    exact (Set.InjOn.encard_image h_inj).symm
  rw [h_encard]

/-! ## 4. Cube Family ≤ Covering Number -/

/-- For a family Tbar of dyadic δ-cubes, |Tbar| ≤ Nplane(⋃₀ Tbar). -/
lemma cube_family_le_covering
    {δ : ℝ} (hδ_pos : 0 < δ)
    {Tbar : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hTbar_sub : Tbar ⊆ dyadicCubes 2 δ)
    (hTbar_finite : Tbar.Finite) :
    ENat.toENNReal Tbar.encard ≤
      ENat.toENNReal (dyadicCoveringNumber δ (⋃₀ Tbar)) := by
  have h1 : Tbar ⊆ dyadicCubesMeeting δ (⋃₀ Tbar) := by
    intro Q hQ
    have hQ_cube : Q ∈ dyadicCubes 2 δ := hTbar_sub hQ
    rcases hQ_cube with ⟨k, hQ_eq⟩
    let p : EuclideanSpace ℝ (Fin 2) := (WithLp.equiv 2 (Fin 2 → ℝ)).symm fun i => δ * (k i : ℝ)
    have hp_in_Q : p ∈ Q := by
      rw [hQ_eq]
      intro i
      have h_lower : δ * (k i : ℝ) ≤ p i := by rfl
      have h_upper : p i < δ * ((k i : ℝ) + 1) := by
        have h_pos : 0 < δ := hδ_pos
        simpa [p] using mul_lt_mul_of_pos_left (by linarith) h_pos
      exact ⟨h_lower, h_upper⟩
    have hp_in_union : p ∈ ⋃₀ Tbar := ⟨Q, hQ, hp_in_Q⟩
    have hQ_cube' : Q ∈ dyadicCubes 2 δ := by
      rw [hQ_eq]; exact ⟨k, rfl⟩
    exact ⟨hQ_cube', ⟨p, hp_in_Q, hp_in_union⟩⟩
  have h2 : ENat.toENNReal Tbar.encard ≤
      ENat.toENNReal (dyadicCoveringNumber δ (⋃₀ Tbar)) := by
    simpa [dyadicCoveringNumber, ENat.coe_le_coe] using Set.encard_mono h1
  exact h2

/-! ## 5. Full Projection Bound -/

/-- Full projection bound with correct 35² constant handling.

For each y ∈ Y, the projection of the Tbar points near y has covering number
≤ δ^{-L_exp·η} · √Nplane(Pbar_param).

Requires absorption hypothesis: 126√98 · 35² ≤ δ^{-η}. -/
lemma projection_bound_full
    {δ s η η_work L_exp C C_work : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (hδ_dyadic : δ ∈ dyadicScales)
    (hs_pos : 0 < s) (hη_pos : 0 < η) (hη_work_pos : 0 < η_work)
    (hη_work_eq_two : η_work = 2 * η)
    (hL_exp_pos : 0 < L_exp) (hL_exp_eq_seven : L_exp = 7)
    (hC_pos : 0 < C) (hC_ge1 : 1 ≤ C)
    (hC_work_eq : C_work = 35 * C)
    (hC_work_pos : 0 < C_work)
    (hC_le_target : C ≤ δ ^ (-η))
    {Y : Set ℝ} {X : ℝ → Set ℝ}
    {Pz Pz_trim : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    {T Tbar : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    {Pbar_param : Set (EuclideanSpace ℝ (Fin 2))}
    (hY_sub : Y ⊆ productLikeUnitGrid δ)
    (hXy_delta : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ ∧
      IsProductLikeRealDeltaSCSet δ s C (X y))
    -- Original Pz (constant C) for double counting (C1 = C)
    (hPz_delta : ∀ z ∈ productLikeIncidenceSet Y X,
      IsDeltaSCSet (d := 2) δ s C (Pz z))
    (hPz_approx : ∀ z ∈ productLikeIncidenceSet Y X,
      ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hPz_bounded : ∀ z ∈ productLikeIncidenceSet Y X,
      Bornology.IsBounded (Pz z))
    -- Trimmed Pz for near-point property (Tbar selection)
    (hPz_trim_approx : ∀ z ∈ productLikeIncidenceSet Y X,
      ∀ p ∈ Pz_trim z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hPz_trim_bounded : ∀ z ∈ productLikeIncidenceSet Y X,
      Bornology.IsBounded (Pz_trim z))
    (hT_finite : T.Finite)
    (hT_upper : ENat.toENNReal T.encard < ENNReal.ofReal (δ ^ (-(2 * s + η))))
    (hTbar_finite : Tbar.Finite)
    (hTbar_lower : ENNReal.ofReal (δ ^ (-2 * s + η) / (98 * C_work ^ 4)) ≤
      ENat.toENNReal Tbar.encard)
    -- U_y for double count uses ORIGINAL Pz (constant C)
    (hU_y_sub_T : ∀ y ∈ Y,
      (⋃ x ∈ X y, dyadicCubesMeeting δ (Pz (mkPoint2 x y))) ⊆ T)
    (hTbar_sub_cubes : Tbar ⊆ dyadicCubes 2 δ)
    (hPbar_eq : Pbar_param = ⋃₀ Tbar)
    (hPbar_bounded : Bornology.IsBounded Pbar_param)
    (h_absorb : (126 : ℝ) * Real.sqrt 98 * (35 : ℝ)^2 ≤ δ ^ (-η)) :
    ∀ y ∈ Y,
      Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1)
        (⋃₀ (Tbar ∩ (⋃ x ∈ X y, dyadicCubesMeeting δ (Pz_trim (mkPoint2 x y)))))) ≤
      ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by
  intro y hy
  let X_y := X y
  let U_y_trim := ⋃ x ∈ X_y, dyadicCubesMeeting δ (Pz_trim (mkPoint2 x y))
  let U_y := ⋃ x ∈ X_y, dyadicCubesMeeting δ (Pz (mkPoint2 x y))
  let T_y_points := ⋃₀ (Tbar ∩ U_y_trim)
  let π_y := fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1

  have hy0 : 0 ≤ y := (hY_sub hy).2.1
  have hy1 : y ≤ 1 := (hY_sub hy).2.2
  have hX_unit : X_y ⊆ productLikeUnitGrid δ := (hXy_delta y hy).1
  have hX_finite : X_y.Finite :=
    Set.Finite.subset (productLikeUnitGrid_finite hδ_pos) hX_unit

  -- Double counting with original C
  have h_double_count_C : (X_y.encard : ENNReal) *
      ENNReal.ofReal ((1 / 2 : ℝ) * C⁻¹ * δ ^ (-s)) ≤
      ENNReal.ofReal (7 : ℝ) * ENat.toENNReal T.encard :=
    double_count_per_y
      (hy := hy) (hy0 := hy0) (hy1 := hy1)
      (hδ_pos := hδ_pos) (hC_pos := hC_pos)
      (hX_grid := fun y' hy' => (hXy_delta y' hy').1)
      (hXy_delta := hXy_delta)
      (hPz_delta := hPz_delta)
      (hPz_approx := hPz_approx)
      (hPz_bounded := hPz_bounded)
      (hT := T) (hT_finite := hT_finite)
      (hU_sub := hU_y_sub_T y hy)

  -- Use original C for double count (C1=C), C_work for Tbar (C2=C_work)
  -- Combined factor: C1 * C2^2 = C * C_work^2 = 35^2 * C^3

  -- Generalized projection comparison with C1 = C, C2 = C_work
  have hXy_bound : (X_y.encard : ENNReal) ≤
      ENNReal.ofReal (14 * Real.sqrt 98 * C * C_work^2 * δ ^ (-3 * η / 2)) *
      ENNReal.ofReal (Real.sqrt ((Tbar.encard : ENNReal).toReal)) :=
    projection_comparison_bound_gen
      hδ_pos hδ_lt_one hs_pos hη_pos hC_pos hC_work_pos
      hX_finite hT_finite hTbar_finite
      h_double_count_C hT_upper hTbar_lower

  -- Helper: (δ^a)^3 = δ^(3*a)
  have rpow_cube : ∀ (a : ℝ), (δ ^ a) ^ 3 = δ ^ (3 * a) := by
    intro a
    have h_add : ∀ (b c : ℝ), δ ^ b * δ ^ c = δ ^ (b + c) := by
      intro b c; rw [← Real.rpow_add hδ_pos] <;> ring
    have h : (δ ^ a) ^ 3 = (δ ^ a) * (δ ^ a) * (δ ^ a) := by ring
    rw [h]
    have h2 : (δ ^ a) * (δ ^ a) * (δ ^ a) = δ ^ (a + a + a) := by
      rw [h_add a a, h_add (a + a) a] <;> ring
    rw [h2] <;> ring_nf

  -- Bound C * C_work² = 35² * C³ ≤ 35² · δ^{-3η}
  have hC_factor_le : C * C_work^2 ≤ (35 : ℝ)^2 * δ ^ (-3 * η) := by
    have h1 : C_work = 35 * C := hC_work_eq
    have h2 : C ≤ δ ^ (-η) := hC_le_target
    rw [h1]
    have h3 : C * (35 * C)^2 = (35 : ℝ)^2 * C^3 := by ring
    rw [h3]
    have h4 : C^3 ≤ (δ ^ (-η))^3 := by gcongr
    have h5 : (δ ^ (-η))^3 = δ ^ (-3 * η) := by
      have h51 := rpow_cube (-η)
      rw [h51]
      have h52 : 3 * (-η) = -3 * η := by ring
      rw [h52]
    rw [h5] at h4
    gcongr

  -- Weaken factor: 14√98 · C·C_work² · δ^{-3η/2} ≤ 14√98 · 35² · δ^{-9η/2}
  have h_factor1 : 14 * Real.sqrt 98 * C * C_work^2 * δ ^ (-3 * η / 2) ≤
      14 * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-9 * η / 2) := by
    have h_pos : 0 < 14 * Real.sqrt 98 := by positivity
    have h_mult : C * C_work^2 * δ ^ (-3 * η / 2) ≤ (35 : ℝ)^2 * δ ^ (-9 * η / 2) := by
      have h9 : C * C_work^2 ≤ (35 : ℝ)^2 * δ ^ (-3 * η) := hC_factor_le
      have h10 : 0 ≤ δ ^ (-3 * η / 2) := by positivity
      have h11 : C * C_work^2 * δ ^ (-3 * η / 2) ≤ ((35 : ℝ)^2 * δ ^ (-3 * η)) * δ ^ (-3 * η / 2) :=
        mul_le_mul_of_nonneg_right h9 h10
      have h12 : ((35 : ℝ)^2 * δ ^ (-3 * η)) * δ ^ (-3 * η / 2) = (35 : ℝ)^2 * δ ^ (-9 * η / 2) := by
        have h13 : δ ^ (-3 * η) * δ ^ (-3 * η / 2) = δ ^ (-9 * η / 2) := by
          rw [← Real.rpow_add hδ_pos] <;> ring_nf
        rw [mul_assoc, h13] <;> ring
      rw [h12] at h11
      exact h11
    have h_pos2 : 0 ≤ 14 * Real.sqrt 98 := by positivity
    have h_result : (14 * Real.sqrt 98) * (C * C_work^2 * δ ^ (-3 * η / 2)) ≤
        (14 * Real.sqrt 98) * ((35 : ℝ)^2 * δ ^ (-9 * η / 2)) := by
      exact mul_le_mul_of_nonneg_left h_mult h_pos2
    have h_assoc : 14 * Real.sqrt 98 * C * C_work^2 * δ ^ (-3 * η / 2) =
        (14 * Real.sqrt 98) * (C * C_work^2 * δ ^ (-3 * η / 2)) := by ring
    have h_assoc2 : 14 * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-9 * η / 2) =
        (14 * Real.sqrt 98) * ((35 : ℝ)^2 * δ ^ (-9 * η / 2)) := by ring
    rw [h_assoc, h_assoc2]
    exact h_result

  -- Weaken δ^{-9η/2} ≤ δ^{-6η} (since -9η/2 ≥ -6η for δ<1)
  have h_exp_weaken : δ ^ (-9 * η / 2) ≤ δ ^ (-6 * η) := by
    have h1 : -9 * η / 2 ≥ -6 * η := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hδ_pos (by linarith) h1

  have h_factor2 : 14 * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-9 * η / 2) ≤
      14 * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-6 * η) := by
    gcongr

  have hXy_bound2 : (X_y.encard : ENNReal) ≤
      ENNReal.ofReal (14 * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-6 * η)) *
      ENNReal.ofReal (Real.sqrt ((Tbar.encard : ENNReal).toReal)) := by
    have h10 : ENNReal.ofReal (14 * Real.sqrt 98 * C * C_work^2 * δ ^ (-3 * η / 2)) ≤
        ENNReal.ofReal (14 * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-6 * η)) :=
      ENNReal.ofReal_le_ofReal (le_trans h_factor1 h_factor2)
    calc (X_y.encard : ENNReal)
      ≤ ENNReal.ofReal (14 * Real.sqrt 98 * C * C_work^2 * δ ^ (-3 * η / 2)) *
          ENNReal.ofReal (Real.sqrt ((Tbar.encard : ENNReal).toReal)) := hXy_bound
    _ ≤ ENNReal.ofReal (14 * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-6 * η)) *
        ENNReal.ofReal (Real.sqrt ((Tbar.encard : ENNReal).toReal)) := by gcongr

  -- Near-point property
  have h_near : ∀ z ∈ Set.image π_y T_y_points, ∃ x ∈ X_y, |z - x| ≤ 4 * δ := by
    intro z hz
    rcases hz with ⟨p, hpT, rfl⟩
    rcases hpT with ⟨Q, hQ_in_TbarU, hpQ⟩
    have hQ_in_U : Q ∈ U_y_trim := hQ_in_TbarU.2
    simp only [U_y_trim, Set.mem_iUnion] at hQ_in_U
    rcases hQ_in_U with ⟨x, hxX, hQ_meeting⟩
    have hQ_meet : (Q ∩ Pz_trim (mkPoint2 x y)).Nonempty := hQ_meeting.2
    rcases hQ_meet with ⟨p', hp'_Q, hp'_trim⟩
    have hz_inc : mkPoint2 x y ∈ productLikeIncidenceSet Y X := by
      simp only [productLikeIncidenceSet, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨y, hy, hxX, rfl⟩
    have h_approx : |p' 0 * y + p' 1 - x| ≤ 2 * δ :=
      hPz_trim_approx (mkPoint2 x y) hz_inc p' hp'_trim
    have hQ_dyadic : Q ∈ dyadicCubes 2 δ := hQ_meeting.1
    rcases hQ_dyadic with ⟨k, hQ_eq⟩
    have hpQ' : p ∈ dyadicCube δ k := by rw [hQ_eq] at hpQ; exact hpQ
    have hp'Q' : p' ∈ dyadicCube δ k := by rw [hQ_eq] at hp'_Q; exact hp'_Q
    have h_var : |p 0 * y + p 1 - (p' 0 * y + p' 1)| ≤ 2 * δ := by
      have h1 : |p 0 - p' 0| < δ := by
        have h11 : δ * (k 0 : ℝ) ≤ p 0 := (hpQ' 0).1
        have h12 : p 0 < δ * ((k 0 : ℝ) + 1) := (hpQ' 0).2
        have h21 : δ * (k 0 : ℝ) ≤ p' 0 := (hp'Q' 0).1
        have h22 : p' 0 < δ * ((k 0 : ℝ) + 1) := (hp'Q' 0).2
        exact abs_lt.mpr ⟨by linarith, by linarith⟩
      have h2 : |p 1 - p' 1| < δ := by
        have h11 : δ * (k 1 : ℝ) ≤ p 1 := (hpQ' 1).1
        have h12 : p 1 < δ * ((k 1 : ℝ) + 1) := (hpQ' 1).2
        have h21 : δ * (k 1 : ℝ) ≤ p' 1 := (hp'Q' 1).1
        have h22 : p' 1 < δ * ((k 1 : ℝ) + 1) := (hp'Q' 1).2
        exact abs_lt.mpr ⟨by linarith, by linarith⟩
      calc |p 0 * y + p 1 - (p' 0 * y + p' 1)|
        = |(p 0 - p' 0) * y + (p 1 - p' 1)| := by ring_nf
      _ ≤ |p 0 - p' 0| * y + |p 1 - p' 1| := by
        have h_tri : |(p 0 - p' 0) * y + (p 1 - p' 1)| ≤ |(p 0 - p' 0) * y| + |p 1 - p' 1| := by
          exact abs_add_le ((p.ofLp 0 - p'.ofLp 0) * y) (p.ofLp 1 - p'.ofLp 1)
        have h_mul : |(p 0 - p' 0) * y| = |p 0 - p' 0| * y := by
          rw [abs_mul, abs_of_nonneg hy0]
        rw [h_mul] at h_tri; exact h_tri
      _ ≤ δ * 1 + δ := by gcongr <;> linarith
      _ = 2 * δ := by ring
    have h_final : |(p 0 * y + p 1) - x| ≤ 4 * δ := by
      have h_eq : (p 0 * y + p 1) - x = ((p 0 * y + p 1) - (p' 0 * y + p' 1)) + (p' 0 * y + p' 1 - x) := by ring
      have h_abs : |(p 0 * y + p 1) - x| ≤ |(p 0 * y + p 1) - (p' 0 * y + p' 1)| + |p' 0 * y + p' 1 - x| := by
        rw [h_eq]; exact abs_add_le (p.ofLp 0 * y + p.ofLp 1 - (p'.ofLp 0 * y + p'.ofLp 1)) (p'.ofLp 0 * y + p'.ofLp 1 - x)
      linarith [h_var, h_approx]
    exact ⟨x, hxX, h_final⟩

  have hXy_bdd : Bornology.IsBounded X_y := by
    have h1 : X_y ⊆ Set.Icc (0 : ℝ) 1 := by
      intro x hx; have h2 : x ∈ productLikeUnitGrid δ := hX_unit hx; exact h2.2
    have h_bdd : Bornology.IsBounded (Set.Icc (0 : ℝ) 1) := by exact Metric.isBounded_Icc 0 1
    exact h_bdd.subset h1

  have h_neighborhood : Nreal δ (Set.image π_y T_y_points) ≤
      (9 : ENNReal) * Nreal δ X_y :=
    neighborhood_covering_bound_1d hδ_pos hXy_bdd h_near

  have hXy_grid : X_y ⊆ productLikeIntegerGrid δ := by
    intro x hx; exact (hXy_delta y hy |>.1 hx).1
  have hN_Xy_eq : Nreal δ X_y = ENat.toENNReal X_y.encard := by
    have h_eq : Nreal δ X_y = ENat.toENNReal (dyadicCoveringNumber (d := 1) δ (productLikeRealLineCopy X_y)) := by rfl
    rw [h_eq]
    exact grid_covering_eq_card hδ_pos hX_finite hXy_grid hXy_bdd

  have hTbar_le_Nplane : ENat.toENNReal Tbar.encard ≤ Nplane δ Pbar_param := by
    rw [hPbar_eq]
    exact cube_family_le_covering hδ_pos hTbar_sub_cubes hTbar_finite
  have hNplane_ne_top : Nplane δ Pbar_param ≠ ⊤ := by
    have hfin : (dyadicCubesMeeting δ Pbar_param).Finite := dyadicCubesMeeting_finite hδ_pos hPbar_bounded
    let sFinset := hfin.toFinset
    have hcard : (dyadicCubesMeeting δ Pbar_param).encard = ↑sFinset.card :=
      Set.Finite.encard_eq_coe_toFinset_card hfin
    simp only [Nplane, dyadicCoveringNumber, hcard]
    <;> simp

  have h_sqrt_le : ENNReal.ofReal (Real.sqrt ((Tbar.encard : ENNReal).toReal)) ≤
      ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by
    let Tbarfin := hTbar_finite.toFinset
    have hTbar_card : Tbar.encard = ↑Tbarfin.card := Finite.encard_eq_coe_toFinset_card hTbar_finite
    have h5 : (Tbar.encard : ENNReal) ≠ ⊤ := by
      rw [hTbar_card] <;> simp
    have h6 : (Nplane δ Pbar_param) ≠ ⊤ := hNplane_ne_top
    have h7 : (Tbar.encard : ENNReal).toReal ≤ (Nplane δ Pbar_param).toReal :=
      (ENNReal.toReal_le_toReal h5 h6).mpr hTbar_le_Nplane
    have h8 : Real.sqrt ((Tbar.encard : ENNReal).toReal) ≤ Real.sqrt ((Nplane δ Pbar_param).toReal) :=
      Real.sqrt_le_sqrt h7
    exact ENNReal.ofReal_le_ofReal h8

  have h_main : Nreal δ (Set.image π_y T_y_points) ≤
      ENNReal.ofReal ((126 : ℝ) * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-6 * η)) *
      ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by
    let A := ENNReal.ofReal (14 * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-6 * η))
    let B := ENNReal.ofReal (Real.sqrt ((Tbar.encard : ENNReal).toReal))
    let C := ENNReal.ofReal ((126 : ℝ) * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-6 * η))
    have h9_eq : (9 : ENNReal) * A = C := by
      have h_eq1 : (9 : ENNReal) = ENNReal.ofReal (9 : ℝ) := by simp
      rw [h_eq1]
      have h_pos1 : 0 ≤ (9 : ℝ) := by norm_num
      have h_pos2 : 0 ≤ (14 * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-6 * η)) := by positivity
      have h_mul : ENNReal.ofReal (9 : ℝ) * A =
          ENNReal.ofReal ((9 : ℝ) * (14 * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-6 * η))) := by
        rw [← ENNReal.ofReal_mul h_pos1]
        <;> rfl
      rw [h_mul]
      have h_real : (9 : ℝ) * (14 * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-6 * η)) =
          (126 : ℝ) * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-6 * η) := by ring
      rw [h_real]
    have h_step2 : (9 : ENNReal) * (X_y.encard : ENNReal) ≤ (9 : ENNReal) * (A * B) := by gcongr
    have h_step3 : (9 : ENNReal) * (A * B) = C * B := by
      have h_assoc : (9 : ENNReal) * (A * B) = ((9 : ENNReal) * A) * B := by
        simp [mul_assoc]
      rw [h_assoc, h9_eq]
    have h_main1 : Nreal δ (Set.image π_y T_y_points) ≤ C * B := by
      calc Nreal δ (Set.image π_y T_y_points)
        ≤ (9 : ENNReal) * Nreal δ X_y := h_neighborhood
      _ = (9 : ENNReal) * (X_y.encard : ENNReal) := by rw [hN_Xy_eq]
      _ ≤ (9 : ENNReal) * (A * B) := h_step2
      _ = C * B := h_step3
    have h_main2 : C * B ≤ C * ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by
      gcongr
    exact le_trans h_main1 h_main2

  -- Absorb: 126√98 · 35² · δ^{-6η} ≤ δ^{-7η} when 126√98 · 35² ≤ δ^{-η}
  have h_absorb' : ENNReal.ofReal ((126 : ℝ) * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-6 * η)) ≤
      ENNReal.ofReal (δ ^ (-(L_exp * η))) := by
    have h1 : (126 : ℝ) * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-6 * η) ≤ δ ^ (-(L_exp * η)) := by
      have h2 : (126 : ℝ) * Real.sqrt 98 * (35 : ℝ)^2 ≤ δ ^ (-η) := h_absorb
      have h3 : L_exp = 7 := hL_exp_eq_seven
      rw [h3]
      have h4 : δ ^ (-η) * δ ^ (-6 * η) = δ ^ (-(7 * η)) := by
        have h5 : (-η) + (-6 * η) = -(7 * η) := by ring
        rw [← Real.rpow_add hδ_pos, h5]
      calc (126 : ℝ) * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-6 * η)
        ≤ δ ^ (-η) * δ ^ (-6 * η) := by gcongr
      _ = δ ^ (-(7 * η)) := h4
    exact ENNReal.ofReal_le_ofReal h1

  calc Nreal δ (Set.image π_y T_y_points)
    ≤ ENNReal.ofReal ((126 : ℝ) * Real.sqrt 98 * (35 : ℝ)^2 * δ ^ (-6 * η)) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := h_main
  _ ≤ ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by
    exact mul_le_mul_of_nonneg_right h_absorb' (by positivity)

end ProductLikeIncidence.ProductReduction
