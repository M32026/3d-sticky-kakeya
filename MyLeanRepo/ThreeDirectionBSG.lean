module

/-
# Three-Direction BSG Proposition

Abstract version of the three-direction Balog-Szemerédi-Gowers argument.

Given three families of 1D sets B₁(y), B₂(y), B₃(y) indexed by y ∈ D with
uniform pairwise product density, apply the 3-factor graph lemma to extract
a large D' ⊆ D where all three thickened intersections are simultaneously large.

Then apply DiscretizedBSG to get dense product structure.

## Whiteprint node

`three_direction_bsg`
-/

public import MyLeanRepo.TwoSidedBigCap
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.DiscretizedBSG
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Finset Set Classical ENNReal Bornology

/-- Local helper: convert `realCoveringNumber_eq_card` to ENNReal equality. -/
private lemma nreal_eq_index_ennreal {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (hS : Bornology.IsBounded S) :
    Nreal δ S = ENat.toENNReal ((ProductLikeIncidence.realCubeIndexSet δ S).encard) := by
  have h : dyadicCoveringNumber δ (ProductLikeIncidence.productLikeRealLineCopy S) =
      (ProductLikeIncidence.realCubeIndexSet δ S).encard :=
    ProductLikeIncidence.realCoveringNumber_eq_card hδ hS
  have h' : Nreal δ S = ENat.toENNReal (dyadicCoveringNumber δ (ProductLikeIncidence.productLikeRealLineCopy S)) := by rfl
  rw [h', h]

namespace ProductLikeIncidence

/-!
## Three-factor graph lemma (from dune)
-/

namespace GraphLemma

/-- From a product intersection bound a·b·c ≥ α·A*·B*·C* with
    a ≤ A*, b ≤ B*, c ≤ C* and all stars positive, derive each
    factor bound a ≥ α·A*, b ≥ α·B*, c ≥ α·C*. -/
lemma three_factor_counting
    {a b c Astar Bstar Cstar α : ℝ}
    (h1 : a * b * c ≥ α * (Astar * Bstar * Cstar))
    (ha_le : a ≤ Astar) (hb_le : b ≤ Bstar) (hc_le : c ≤ Cstar)
    (hA_pos : 0 < Astar) (hB_pos : 0 < Bstar) (hC_pos : 0 < Cstar)
    (ha_nonneg : 0 ≤ a) (hb_nonneg : 0 ≤ b) (hc_nonneg : 0 ≤ c) :
    a ≥ α * Astar ∧ b ≥ α * Bstar ∧ c ≥ α * Cstar := by
  have ha : a ≥ α * Astar := by
    by_contra h
    have h' : a < α * Astar := by linarith
    have h2 : a * b * c ≤ a * (Bstar * Cstar) := by
      have h21 : b * c ≤ Bstar * Cstar := by
        exact mul_le_mul hb_le hc_le hc_nonneg (by linarith)
      have h : a * b * c = a * (b * c) := by ring
      rw [h]
      exact mul_le_mul_of_nonneg_left h21 ha_nonneg
    have hBC_pos : 0 < Bstar * Cstar := mul_pos hB_pos hC_pos
    have h3 : a * (Bstar * Cstar) < α * Astar * (Bstar * Cstar) :=
      mul_lt_mul_of_pos_right h' hBC_pos
    have h4 : a * b * c < α * (Astar * Bstar * Cstar) := by
      calc a * b * c ≤ a * (Bstar * Cstar) := h2
           _ < α * Astar * (Bstar * Cstar) := h3
           _ = α * (Astar * Bstar * Cstar) := by ring
    linarith
  have hb : b ≥ α * Bstar := by
    by_contra h
    have h' : b < α * Bstar := by linarith
    have h2 : a * b * c ≤ (Astar * Cstar) * b := by
      have h21 : a * c ≤ Astar * Cstar := by
        exact mul_le_mul ha_le hc_le hc_nonneg (by linarith)
      have h : a * b * c = (a * c) * b := by ring
      rw [h]
      exact mul_le_mul_of_nonneg_right h21 hb_nonneg
    have hAC_pos : 0 < Astar * Cstar := mul_pos hA_pos hC_pos
    have h3 : (Astar * Cstar) * b < (Astar * Cstar) * (α * Bstar) :=
      mul_lt_mul_of_pos_left h' hAC_pos
    have h4 : a * b * c < α * (Astar * Bstar * Cstar) := by
      calc a * b * c ≤ (Astar * Cstar) * b := h2
           _ < (Astar * Cstar) * (α * Bstar) := h3
           _ = α * (Astar * Bstar * Cstar) := by ring
    linarith
  have hc : c ≥ α * Cstar := by
    by_contra h
    have h' : c < α * Cstar := by linarith
    have h2 : a * b * c ≤ (Astar * Bstar) * c := by
      have h21 : a * b ≤ Astar * Bstar := by
        exact mul_le_mul ha_le hb_le hb_nonneg (by linarith)
      have h : a * b * c = (a * b) * c := by ring
      rw [h]
      exact mul_le_mul_of_nonneg_right h21 hc_nonneg
    have hAB_pos : 0 < Astar * Bstar := mul_pos hA_pos hB_pos
    have h3 : (Astar * Bstar) * c < (Astar * Bstar) * (α * Cstar) :=
      mul_lt_mul_of_pos_left h' hAB_pos
    have h4 : a * b * c < α * (Astar * Bstar * Cstar) := by
      calc a * b * c ≤ (Astar * Bstar) * c := h2
           _ < (Astar * Bstar) * (α * Cstar) := h3
           _ = α * (Astar * Bstar * Cstar) := by ring
    linarith
  exact ⟨ha, hb, hc⟩

/-- Given three families of finite sets C1(y), C2(y), C3(y) with uniform
    product-cardinality lower bounds, find y* and a large-weight D' such
    that all three pairwise intersections are simultaneously large. -/
lemma representative_big_intersection_graph_three
    {Cube1 Cube2 Cube3 : Type*} [DecidableEq Cube1] [DecidableEq Cube2] [DecidableEq Cube3]
    {D : Finset ℝ} (hD_nonempty : D.Nonempty)
    {w : ℝ → ℝ} (hw_nonneg : ∀ y ∈ D, 0 ≤ w y)
    {W : ℝ} (hW_pos : 0 < W) (hW_sum : ∑ y ∈ D, w y = W)
    {ambient1 : Finset Cube1} {ambient2 : Finset Cube2} {ambient3 : Finset Cube3}
    (hambient1_nonempty : ambient1.Nonempty)
    (hambient2_nonempty : ambient2.Nonempty)
    (hambient3_nonempty : ambient3.Nonempty)
    {C1 : ℝ → Finset Cube1} {C2 : ℝ → Finset Cube2} {C3 : ℝ → Finset Cube3}
    (hC1_sub : ∀ y ∈ D, C1 y ⊆ ambient1)
    (hC2_sub : ∀ y ∈ D, C2 y ⊆ ambient2)
    (hC3_sub : ∀ y ∈ D, C3 y ⊆ ambient3)
    {c : ℝ} (hc_pos : 0 < c) (hc_le_one : c ≤ 1)
    (hC_lower : ∀ y ∈ D,
      ((C1 y).card : ℝ) * ((C2 y).card : ℝ) * ((C3 y).card : ℝ) ≥
      c * ((ambient1.card : ℝ) * (ambient2.card : ℝ) * (ambient3.card : ℝ)))
    {α mass : ℝ} (hα_pos : 0 < α) (hmass_pos : 0 < mass)
    (hα_le : α ≤ c^3 / 32) (hmass_le : mass ≤ c^2 / 16) :
    ∃ (y_star : ℝ) (hy_star : y_star ∈ D) (D' : Finset ℝ),
      D' ⊆ D ∧
      (∑ y ∈ D', w y) ≥ mass * W ∧
      ∀ y ∈ D',
        ((C1 y ∩ C1 y_star).card : ℝ) ≥ α * ((C1 y_star).card : ℝ) ∧
        ((C2 y ∩ C2 y_star).card : ℝ) ≥ α * ((C2 y_star).card : ℝ) ∧
        ((C3 y ∩ C3 y_star).card : ℝ) ≥ α * ((C3 y_star).card : ℝ) := by
  let C : ℝ → Finset (Cube1 × Cube2 × Cube3) := fun y =>
    (C1 y) ×ˢ ((C2 y) ×ˢ (C3 y))
  let ambient : Finset (Cube1 × Cube2 × Cube3) :=
    ambient1 ×ˢ (ambient2 ×ˢ ambient3)
  have hC_sub : ∀ y ∈ D, C y ⊆ ambient := by
    intro y hy
    have h23 : (C2 y ×ˢ C3 y) ⊆ (ambient2 ×ˢ ambient3) :=
      Finset.product_subset_product (hC2_sub y hy) (hC3_sub y hy)
    exact Finset.product_subset_product (hC1_sub y hy) h23
  have hC_lower' : ∀ y ∈ D, ((C y).card : ℝ) ≥ c * (ambient.card : ℝ) := by
    intro y hy
    have h1 : ((C y).card : ℝ) =
        ((C1 y).card : ℝ) * (((C2 y).card : ℝ) * ((C3 y).card : ℝ)) := by
      simp [C, Finset.card_product, Nat.cast_mul]
    have h2 : (ambient.card : ℝ) =
        (ambient1.card : ℝ) * ((ambient2.card : ℝ) * (ambient3.card : ℝ)) := by
      simp [ambient, Finset.card_product, Nat.cast_mul]
    rw [h1, h2]
    have h3 := hC_lower y hy
    ring_nf at h3 ⊢
    exact h3
  have h_ambient_nonempty : ambient.Nonempty := by
    rcases hambient1_nonempty with ⟨x, hx⟩
    rcases hambient2_nonempty with ⟨y, hy⟩
    rcases hambient3_nonempty with ⟨z, hz⟩
    exact ⟨(x, (y, z)), by simp [ambient, hx, hy, hz]⟩
  have h_amb_card_pos : 0 < (ambient.card : ℝ) := by
    have h : 0 < ambient.card := Finset.Nonempty.card_pos h_ambient_nonempty
    exact_mod_cast h
  have h_main := _root_.GraphLemma.representative_big_intersection_graph_cubes
    hD_nonempty hw_nonneg hW_pos hW_sum hC_sub hc_pos hc_le_one hC_lower'
    hα_pos hmass_pos hα_le hmass_le
  rcases h_main with ⟨y_star, hy_star, D', hD'_sub, h_mass, h_shared⟩
  have h_Cstar_pos : 0 < ((C y_star).card : ℝ) := by
    have h1 : ((C y_star).card : ℝ) ≥ c * (ambient.card : ℝ) := hC_lower' y_star hy_star
    have h2 : 0 < c * (ambient.card : ℝ) := mul_pos hc_pos h_amb_card_pos
    linarith
  have h_eq_star : ((C y_star).card : ℝ) =
      ((C1 y_star).card : ℝ) * (((C2 y_star).card : ℝ) * ((C3 y_star).card : ℝ)) := by
    simp [C, Finset.card_product, Nat.cast_mul] <;> ring
  have h1_pos : 0 < ((C1 y_star).card : ℝ) := by
    by_contra h
    have h'' : ((C1 y_star).card : ℝ) = 0 := by linarith [show (0 : ℝ) ≤ ((C1 y_star).card : ℝ) from by positivity]
    rw [h_eq_star] at h_Cstar_pos
    rw [h''] at h_Cstar_pos
    simp at h_Cstar_pos <;> linarith
  have h2_pos : 0 < ((C2 y_star).card : ℝ) := by
    by_contra h
    have h'' : ((C2 y_star).card : ℝ) = 0 := by linarith [show (0 : ℝ) ≤ ((C2 y_star).card : ℝ) from by positivity]
    rw [h_eq_star] at h_Cstar_pos
    rw [h''] at h_Cstar_pos
    simp at h_Cstar_pos <;> linarith
  have h3_pos : 0 < ((C3 y_star).card : ℝ) := by
    by_contra h
    have h'' : ((C3 y_star).card : ℝ) = 0 := by linarith [show (0 : ℝ) ≤ ((C3 y_star).card : ℝ) from by positivity]
    rw [h_eq_star] at h_Cstar_pos
    rw [h''] at h_Cstar_pos
    simp at h_Cstar_pos <;> linarith
  refine ⟨y_star, hy_star, D', hD'_sub, h_mass, fun y hy => ?_⟩
  set a := ((C1 y ∩ C1 y_star).card : ℝ) with ha_def
  set b := ((C2 y ∩ C2 y_star).card : ℝ) with hb_def
  set c3 := ((C3 y ∩ C3 y_star).card : ℝ) with hc3_def
  set Astar := ((C1 y_star).card : ℝ) with hA_def
  set Bstar := ((C2 y_star).card : ℝ) with hB_def
  set Cstar := ((C3 y_star).card : ℝ) with hC_def
  have h_prod : a * b * c3 ≥ α * (Astar * Bstar * Cstar) := by
    have h_orig : ((C y ∩ C y_star).card : ℝ) ≥ α * ((C y_star).card : ℝ) := h_shared y hy
    have h_eq1 : ((C y ∩ C y_star).card : ℝ) = a * b * c3 := by
      have h_set : C y ∩ C y_star =
          (C1 y ∩ C1 y_star) ×ˢ ((C2 y ∩ C2 y_star) ×ˢ (C3 y ∩ C3 y_star)) := by
        ext ⟨x, y2, z⟩; simp [C, Finset.mem_inter, Finset.mem_product] <;> tauto
      rw [h_set, Finset.card_product, Finset.card_product]
      simp [ha_def, hb_def, hc3_def, Nat.cast_mul] <;> ring
    have h_eq2 : ((C y_star).card : ℝ) = Astar * Bstar * Cstar := by
      simp [C, Finset.card_product, hA_def, hB_def, hC_def, Nat.cast_mul] <;> ring
    rw [h_eq1, h_eq2] at h_orig
    exact h_orig
  have ha_le : a ≤ Astar := by
    have h_sub : (C1 y ∩ C1 y_star) ⊆ C1 y_star := by simp
    have h_card : (C1 y ∩ C1 y_star).card ≤ (C1 y_star).card := Finset.card_le_card h_sub
    have h_cast : ((C1 y ∩ C1 y_star).card : ℝ) ≤ ((C1 y_star).card : ℝ) := by exact_mod_cast h_card
    simpa [ha_def, hA_def] using h_cast
  have hb_le : b ≤ Bstar := by
    have h_sub : (C2 y ∩ C2 y_star) ⊆ C2 y_star := by simp
    have h_card : (C2 y ∩ C2 y_star).card ≤ (C2 y_star).card := Finset.card_le_card h_sub
    have h_cast : ((C2 y ∩ C2 y_star).card : ℝ) ≤ ((C2 y_star).card : ℝ) := by exact_mod_cast h_card
    simpa [hb_def, hB_def] using h_cast
  have hc3_le : c3 ≤ Cstar := by
    have h_sub : (C3 y ∩ C3 y_star) ⊆ C3 y_star := by simp
    have h_card : (C3 y ∩ C3 y_star).card ≤ (C3 y_star).card := Finset.card_le_card h_sub
    have h_cast : ((C3 y ∩ C3 y_star).card : ℝ) ≤ ((C3 y_star).card : ℝ) := by exact_mod_cast h_card
    simpa [hc3_def, hC_def] using h_cast
  have ha_nonneg : 0 ≤ a := by positivity
  have hb_nonneg : 0 ≤ b := by positivity
  have hc3_nonneg : 0 ≤ c3 := by positivity
  exact three_factor_counting h_prod ha_le hb_le hc3_le h1_pos h2_pos h3_pos ha_nonneg hb_nonneg hc3_nonneg

end GraphLemma

/-!
## Triple product bound (from nimbus)
-/

/-- Pure real-algebra triple product bound: from three pairwise product density
    bounds x₁·x₂ ≥ c·a₁·a₂, x₂·x₃ ≥ c·a₂·a₃, x₁·x₃ ≥ c·a₁·a₃
    derive x₁·x₂·x₃ ≥ c^(3/2)·a₁·a₂·a₃. -/
lemma triple_product_bound {x1 x2 x3 a1 a2 a3 c : ℝ}
    (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (hc : 0 ≤ c)
    (h12 : x1 * x2 ≥ c * a1 * a2)
    (h23 : x2 * x3 ≥ c * a2 * a3)
    (h13 : x1 * x3 ≥ c * a1 * a3) :
    x1 * x2 * x3 ≥ c ^ (3 / 2 : ℝ) * a1 * a2 * a3 := by
  have h_mul : (x1 * x2) * (x2 * x3) * (x1 * x3) ≥
      (c * a1 * a2) * (c * a2 * a3) * (c * a1 * a3) := by gcongr
  have h_eq1 : (x1 * x2) * (x2 * x3) * (x1 * x3) = (x1 * x2 * x3) ^ 2 := by ring
  have h_eq2 : (c * a1 * a2) * (c * a2 * a3) * (c * a1 * a3) = c ^ 3 * (a1 * a2 * a3) ^ 2 := by ring
  have h_mul2 : (x1 * x2 * x3) ^ 2 ≥ c ^ 3 * (a1 * a2 * a3) ^ 2 := by
    rw [h_eq1, h_eq2] at h_mul; exact h_mul
  have h11 : (c ^ (3 / 2 : ℝ)) ^ 2 = c ^ 3 := by
    by_cases hc0 : c = 0
    · rw [hc0]
      have h_pos : (3 / 2 : ℝ) ≠ 0 := by norm_num
      have h_zero : (0 : ℝ) ^ (3 / 2 : ℝ) = 0 := Real.zero_rpow h_pos
      rw [h_zero]; norm_num
    · have hc_pos' : 0 < c := by
        by_contra h
        have h' : c ≤ 0 := by linarith
        have h'' : c = 0 := by linarith
        contradiction
      have h1 : (c ^ (3 / 2 : ℝ)) ^ 2 = (c ^ (3 / 2 : ℝ)) * (c ^ (3 / 2 : ℝ)) := by ring
      rw [h1]
      have h2 : (c ^ (3 / 2 : ℝ)) * (c ^ (3 / 2 : ℝ)) = c ^ ((3 / 2 : ℝ) + (3 / 2 : ℝ)) :=
        (Real.rpow_add hc_pos' (3 / 2 : ℝ) (3 / 2 : ℝ)).symm
      rw [h2]
      have h3 : (3 / 2 : ℝ) + (3 / 2 : ℝ) = 3 := by norm_num
      rw [h3]
      norm_cast
  have h10 : c ^ 3 * (a1 * a2 * a3) ^ 2 = (c ^ (3 / 2 : ℝ) * a1 * a2 * a3) ^ 2 := by
    have h101 : c ^ 3 = (c ^ (3 / 2 : ℝ)) ^ 2 := h11.symm
    rw [h101]; ring
  have h9 : (x1 * x2 * x3) ^ 2 ≥ (c ^ (3 / 2 : ℝ) * a1 * a2 * a3) ^ 2 := by
    calc (x1 * x2 * x3) ^ 2 ≥ c ^ 3 * (a1 * a2 * a3) ^ 2 := h_mul2
    _ = (c ^ (3 / 2 : ℝ) * a1 * a2 * a3) ^ 2 := h10
  have h_nonneg1 : 0 ≤ x1 * x2 * x3 := by positivity
  have h_nonneg2 : 0 ≤ c ^ (3 / 2 : ℝ) * a1 * a2 * a3 := by positivity
  by_contra h
  have h' : x1 * x2 * x3 < c ^ (3 / 2 : ℝ) * a1 * a2 * a3 := by linarith
  have h2 : (x1 * x2 * x3) ^ 2 < (c ^ (3 / 2 : ℝ) * a1 * a2 * a3) ^ 2 := by
    gcongr <;> linarith
  linarith [h9]

/-- Finset-card version of triple product bound. -/
lemma triple_finset_card_bound {α1 α2 α3 : Type*}
    {A1 B1 : Finset α1} {A2 B2 : Finset α2} {A3 B3 : Finset α3}
    {c : ℝ} (hc : 0 ≤ c)
    (h12 : (B1.card : ℝ) * (B2.card : ℝ) ≥ c * (A1.card : ℝ) * (A2.card : ℝ))
    (h23 : (B2.card : ℝ) * (B3.card : ℝ) ≥ c * (A2.card : ℝ) * (A3.card : ℝ))
    (h13 : (B1.card : ℝ) * (B3.card : ℝ) ≥ c * (A1.card : ℝ) * (A3.card : ℝ)) :
    (B1.card : ℝ) * (B2.card : ℝ) * (B3.card : ℝ) ≥
    c ^ (3 / 2 : ℝ) * (A1.card : ℝ) * (A2.card : ℝ) * (A3.card : ℝ) :=
  triple_product_bound (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) hc h12 h23 h13

/-!
## Thickening bridge helper
-/

/-- Convert an index-intersection cardinality lower bound into a thickened
    intersection `Nreal` lower bound. -/
lemma thickening_step {δ : ℝ} (hδ : 0 < δ)
    {A_star A_y : Set ℝ}
    (hA_star_bdd : Bornology.IsBounded A_star)
    (hA_y_bdd : Bornology.IsBounded A_y)
    (idxA_y idxA_star : Finset ℤ)
    (h_idxA_y : idxA_y = (ProductLikeIncidence.realCubeIndexSet_finite hδ hA_y_bdd).toFinset)
    (h_idxA_star : idxA_star = (ProductLikeIncidence.realCubeIndexSet_finite hδ hA_star_bdd).toFinset)
    {α : ℝ} (hα_pos : 0 < α)
    (h_count : ((idxA_y ∩ idxA_star).card : ℝ) ≥ α * ((idxA_star).card : ℝ)) :
    Nreal δ (Metric.cthickening (Real.sqrt 2 * δ) A_star ∩ A_y) ≥
    ENNReal.ofReal α * Nreal δ A_star := by
  have hA_thick_bdd : Bornology.IsBounded (Metric.cthickening (Real.sqrt 2 * δ) A_star ∩ A_y) :=
    hA_star_bdd.cthickening.subset Set.inter_subset_left
  let K_A := (ProductLikeIncidence.realCubeIndexSet_finite hδ hA_thick_bdd).toFinset
  have hA_idx_sub : (idxA_y ∩ idxA_star) ⊆ K_A := by
    rw [h_idxA_y, h_idxA_star]
    intro k hk
    have hkA : k ∈ ProductLikeIncidence.realCubeIndexSet δ A_y := by
      simpa [Set.Finite.coe_toFinset] using (Finset.mem_inter.mp hk).1
    have hkAstar : k ∈ ProductLikeIncidence.realCubeIndexSet δ A_star := by
      simpa [Set.Finite.coe_toFinset] using (Finset.mem_inter.mp hk).2
    have h : k ∈ ProductLikeIncidence.realCubeIndexSet δ (A_y ∩ Metric.cthickening (Real.sqrt 2 * δ) A_star) :=
      TwoSidedBigCap.index_intersection_subset_thickened hδ k hkA hkAstar
    have h_eq : (A_y ∩ Metric.cthickening (Real.sqrt 2 * δ) A_star) =
                (Metric.cthickening (Real.sqrt 2 * δ) A_star ∩ A_y) := by
      ext z; simp [and_comm]
    rw [h_eq] at h
    simpa [K_A, Set.Finite.coe_toFinset] using h
  have hA_card_le : ((idxA_y ∩ idxA_star).card : ℝ) ≤ (K_A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hA_idx_sub
  have h_Nreal_card : ∀ (S : Set ℝ) (hS : Bornology.IsBounded S),
      Nreal δ S = (↑((ProductLikeIncidence.realCubeIndexSet_finite hδ hS).toFinset.card) : ENNReal) := by
    intro S hS
    have h_eq1 : Nreal δ S = ENat.toENNReal (ProductLikeIncidence.realCubeIndexSet δ S).encard :=
      nreal_eq_index_ennreal hδ hS
    have h_fin : (ProductLikeIncidence.realCubeIndexSet δ S).Finite :=
      ProductLikeIncidence.realCubeIndexSet_finite hδ hS
    rw [h_eq1, Set.Finite.encard_eq_coe_toFinset_card h_fin] <;> norm_cast
  have hA_eq : Nreal δ (Metric.cthickening (Real.sqrt 2 * δ) A_star ∩ A_y) = (↑K_A.card : ENNReal) :=
    h_Nreal_card _ hA_thick_bdd
  have hAstar_eq : Nreal δ A_star = (↑((idxA_star).card) : ENNReal) := by
    rw [h_Nreal_card A_star hA_star_bdd, h_idxA_star] <;> rfl
  rw [hA_eq, hAstar_eq]
  have h1 : (K_A.card : ℝ) ≥ α * ((idxA_star).card : ℝ) := by
    linarith [hA_card_le, h_count]
  have h2 : (↑K_A.card : ENNReal) ≥ ENNReal.ofReal (α * ((idxA_star).card : ℝ)) := by
    have h_coe : (↑K_A.card : ENNReal) = ENNReal.ofReal ((K_A.card : ℝ)) := by simp
    rw [h_coe]; exact ENNReal.ofReal_le_ofReal h1
  have h3 : ENNReal.ofReal α * (↑((idxA_star).card) : ENNReal) =
      ENNReal.ofReal (α * ((idxA_star).card : ℝ)) := by
    rw [ENNReal.ofReal_mul hα_pos.le] <;> simp
  rw [h3]; exact h2

/-- Convert a pairwise Nplane density bound to a Finset.card product bound. -/
lemma pairwise_bound_to_card {δ : ℝ} (hδ : 0 < δ)
    {A B ambA ambB : Set ℝ}
    (hA_bdd : Bornology.IsBounded A) (hB_bdd : Bornology.IsBounded B)
    (hambA_bdd : Bornology.IsBounded ambA) (hambB_bdd : Bornology.IsBounded ambB)
    (idxA idxB IambA IambB : Finset ℤ)
    (h_idxA : idxA = (ProductLikeIncidence.realCubeIndexSet_finite hδ hA_bdd).toFinset)
    (h_idxB : idxB = (ProductLikeIncidence.realCubeIndexSet_finite hδ hB_bdd).toFinset)
    (h_IambA : IambA = (ProductLikeIncidence.realCubeIndexSet_finite hδ hambA_bdd).toFinset)
    (h_IambB : IambB = (ProductLikeIncidence.realCubeIndexSet_finite hδ hambB_bdd).toFinset)
    {c : ℝ} (hc_pos : 0 < c)
    (hG : Nplane δ (TwoSidedBigCap.prodSet A B) ≥
          ENNReal.ofReal c * Nplane δ (TwoSidedBigCap.prodSet ambA ambB))
    (h_Nreal_card : ∀ (S : Set ℝ) (hS : Bornology.IsBounded S),
        Nreal δ S = (↑((ProductLikeIncidence.realCubeIndexSet_finite hδ hS).toFinset.card) : ENNReal)) :
    ((idxA.card : ℝ) * (idxB.card : ℝ) ≥ c * (IambA.card : ℝ) * (IambB.card : ℝ)) := by
  have h1 : Nplane δ (TwoSidedBigCap.prodSet A B) = Nreal δ A * Nreal δ B :=
    TwoSidedBigCap.prodSet_covering_eq hδ hA_bdd hB_bdd
  have h2 : Nplane δ (TwoSidedBigCap.prodSet ambA ambB) = Nreal δ ambA * Nreal δ ambB :=
    TwoSidedBigCap.prodSet_covering_eq hδ hambA_bdd hambB_bdd
  have hG' : Nreal δ A * Nreal δ B ≥ ENNReal.ofReal c * (Nreal δ ambA * Nreal δ ambB) := by
    rw [h1, h2] at hG; exact hG
  have h4 : Nreal δ A = (↑(idxA.card) : ENNReal) := by
    rw [h_Nreal_card A hA_bdd, h_idxA] <;> rfl
  have h5 : Nreal δ B = (↑(idxB.card) : ENNReal) := by
    rw [h_Nreal_card B hB_bdd, h_idxB] <;> rfl
  have h6 : Nreal δ ambA = (↑IambA.card : ENNReal) := by
    rw [h_Nreal_card ambA hambA_bdd, h_IambA] <;> rfl
  have h7 : Nreal δ ambB = (↑IambB.card : ENNReal) := by
    rw [h_Nreal_card ambB hambB_bdd, h_IambB] <;> rfl
  rw [h4, h5, h6, h7] at hG'
  have h_left : (↑(idxA.card) : ENNReal) * (↑(idxB.card) : ENNReal) =
      ENNReal.ofReal ((idxA.card : ℝ) * (idxB.card : ℝ)) := by
    have h1 : (↑(idxA.card) : ENNReal) = ENNReal.ofReal (idxA.card : ℝ) := by simp
    have h2 : (↑(idxB.card) : ENNReal) = ENNReal.ofReal (idxB.card : ℝ) := by simp
    rw [h1, h2, ← ENNReal.ofReal_mul (by positivity)] <;> rfl
  have h_right : ENNReal.ofReal c * ((↑IambA.card : ENNReal) * (↑IambB.card : ENNReal)) =
      ENNReal.ofReal (c * ((IambA.card : ℝ) * (IambB.card : ℝ))) := by
    have h1 : (↑IambA.card : ENNReal) = ENNReal.ofReal (IambA.card : ℝ) := by simp
    have h2 : (↑IambB.card : ENNReal) = ENNReal.ofReal (IambB.card : ℝ) := by simp
    rw [h1, h2]
    have h3 : ENNReal.ofReal (IambA.card : ℝ) * ENNReal.ofReal (IambB.card : ℝ) =
        ENNReal.ofReal ((IambA.card : ℝ) * (IambB.card : ℝ)) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
    rw [h3, ← ENNReal.ofReal_mul hc_pos.le] <;> ring
  rw [h_left, h_right] at hG'
  have h_pos2 : 0 ≤ ((idxA.card : ℝ) * (idxB.card : ℝ)) := by positivity
  have h_eq : c * ((IambA.card : ℝ) * (IambB.card : ℝ)) = c * (IambA.card : ℝ) * (IambB.card : ℝ) := by ring
  have hG_flip : ENNReal.ofReal (c * (IambA.card : ℝ) * (IambB.card : ℝ)) ≤
      ENNReal.ofReal ((idxA.card : ℝ) * (idxB.card : ℝ)) := by
    rw [← h_eq]
    exact hG'
  exact (ENNReal.ofReal_le_ofReal_iff h_pos2).mp hG_flip

/-!
## Three-direction intersection theorem

Uses the 3-factor graph lemma plus triple product bound and thickening bridge
to prove the main intersection result.
-/

/--
Three-direction two-sided big intersection.

Given weighted families B₁(y), B₂(y), B₃(y) ⊆ ℝ for y ∈ D with uniform
pairwise product covering lower bounds, select y_star ∈ D and D' ⊆ D of
weight ≥ mass · W such that for every y ∈ D' all three thickened
intersections are large.

Proof: derive triple product bound from pairwise bounds, apply
`GraphLemma.representative_big_intersection_graph_three` to 3D product
index sets, extract individual factor bounds, then thickening bridge.
-/
theorem three_direction_intersection
    {δ : ℝ} (hδ : 0 < δ) (hδ_lt_one : δ < 1)
    {D : Finset ℝ} (hD_nonempty : D.Nonempty)
    {w : ℝ → ℝ} (hw_nonneg : ∀ y ∈ D, 0 ≤ w y)
    {W : ℝ} (hW_pos : 0 < W) (hW_sum : ∑ y ∈ D, w y = W)
    {ambient₁ ambient₂ ambient₃ : Set ℝ}
    (hamb₁_bdd : Bornology.IsBounded ambient₁)
    (hamb₁_nonempty : ambient₁.Nonempty)
    (hamb₂_bdd : Bornology.IsBounded ambient₂)
    (hamb₂_nonempty : ambient₂.Nonempty)
    (hamb₃_bdd : Bornology.IsBounded ambient₃)
    (hamb₃_nonempty : ambient₃.Nonempty)
    {B₁ B₂ B₃ : ℝ → Set ℝ}
    (hB₁_bdd : ∀ y ∈ D, Bornology.IsBounded (B₁ y))
    (hB₂_bdd : ∀ y ∈ D, Bornology.IsBounded (B₂ y))
    (hB₃_bdd : ∀ y ∈ D, Bornology.IsBounded (B₃ y))
    (hB₁_sub : ∀ y ∈ D, B₁ y ⊆ ambient₁)
    (hB₂_sub : ∀ y ∈ D, B₂ y ⊆ ambient₂)
    (hB₃_sub : ∀ y ∈ D, B₃ y ⊆ ambient₃)
    {c : ℝ} (hc_pos : 0 < c) (hc_le_one : c ≤ 1)
    {α mass : ℝ} (hα_pos : 0 < α) (hmass_pos : 0 < mass)
    (hα_le : α ≤ c ^ (9 / 2 : ℝ) / 32) (hmass_le : mass ≤ c ^ 3 / 16)
    (hG12 : ∀ y ∈ D,
      Nplane δ (TwoSidedBigCap.prodSet (B₁ y) (B₂ y)) ≥
        ENNReal.ofReal c * Nplane δ (TwoSidedBigCap.prodSet ambient₁ ambient₂))
    (hG23 : ∀ y ∈ D,
      Nplane δ (TwoSidedBigCap.prodSet (B₂ y) (B₃ y)) ≥
        ENNReal.ofReal c * Nplane δ (TwoSidedBigCap.prodSet ambient₂ ambient₃))
    (hG13 : ∀ y ∈ D,
      Nplane δ (TwoSidedBigCap.prodSet (B₁ y) (B₃ y)) ≥
        ENNReal.ofReal c * Nplane δ (TwoSidedBigCap.prodSet ambient₁ ambient₃)) :
    ∃ (y_star : ℝ) (hy_star : y_star ∈ D) (D' : Finset ℝ),
      D' ⊆ D ∧
      (∑ y ∈ D', w y) ≥ mass * W ∧
      ∀ y ∈ D',
        (Nreal δ (Metric.cthickening (Real.sqrt 2 * δ) (B₁ y_star) ∩ B₁ y) ≥
           ENNReal.ofReal α * Nreal δ (B₁ y_star)) ∧
        (Nreal δ (Metric.cthickening (Real.sqrt 2 * δ) (B₂ y_star) ∩ B₂ y) ≥
           ENNReal.ofReal α * Nreal δ (B₂ y_star)) ∧
        (Nreal δ (Metric.cthickening (Real.sqrt 2 * δ) (B₃ y_star) ∩ B₃ y) ≥
           ENNReal.ofReal α * Nreal δ (B₃ y_star))
:= by
  -- Step 1: Define index finsets
  let idx1 : ℝ → Finset ℤ := fun y =>
    if h : y ∈ D then
      (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₁_bdd y h)).toFinset
    else ∅
  let idx2 : ℝ → Finset ℤ := fun y =>
    if h : y ∈ D then
      (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₂_bdd y h)).toFinset
    else ∅
  let idx3 : ℝ → Finset ℤ := fun y =>
    if h : y ∈ D then
      (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₃_bdd y h)).toFinset
    else ∅
  let Iamb1 := (ProductLikeIncidence.realCubeIndexSet_finite hδ hamb₁_bdd).toFinset
  let Iamb2 := (ProductLikeIncidence.realCubeIndexSet_finite hδ hamb₂_bdd).toFinset
  let Iamb3 := (ProductLikeIncidence.realCubeIndexSet_finite hδ hamb₃_bdd).toFinset

  have h1_sub : ∀ y ∈ D, idx1 y ⊆ Iamb1 := by
    intro y hy
    have h_idx : idx1 y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₁_bdd y hy)).toFinset := by
      simp [idx1, hy]
    rw [h_idx]
    intro k hk
    have h2 : k ∈ ProductLikeIncidence.realCubeIndexSet δ (B₁ y) := by
      simpa [Set.Finite.coe_toFinset] using hk
    rcases h2 with ⟨x, hxIco, hxB⟩
    have h3 : x ∈ ambient₁ := hB₁_sub y hy hxB
    have h4 : k ∈ ProductLikeIncidence.realCubeIndexSet δ ambient₁ := ⟨x, hxIco, h3⟩
    simpa [Iamb1, Set.Finite.coe_toFinset] using h4
  have h2_sub : ∀ y ∈ D, idx2 y ⊆ Iamb2 := by
    intro y hy
    have h_idx : idx2 y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₂_bdd y hy)).toFinset := by
      simp [idx2, hy]
    rw [h_idx]
    intro k hk
    have h2 : k ∈ ProductLikeIncidence.realCubeIndexSet δ (B₂ y) := by
      simpa [Set.Finite.coe_toFinset] using hk
    rcases h2 with ⟨x, hxIco, hxB⟩
    have h3 : x ∈ ambient₂ := hB₂_sub y hy hxB
    have h4 : k ∈ ProductLikeIncidence.realCubeIndexSet δ ambient₂ := ⟨x, hxIco, h3⟩
    simpa [Iamb2, Set.Finite.coe_toFinset] using h4
  have h3_sub : ∀ y ∈ D, idx3 y ⊆ Iamb3 := by
    intro y hy
    have h_idx : idx3 y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₃_bdd y hy)).toFinset := by
      simp [idx3, hy]
    rw [h_idx]
    intro k hk
    have h2 : k ∈ ProductLikeIncidence.realCubeIndexSet δ (B₃ y) := by
      simpa [Set.Finite.coe_toFinset] using hk
    rcases h2 with ⟨x, hxIco, hxB⟩
    have h3 : x ∈ ambient₃ := hB₃_sub y hy hxB
    have h4 : k ∈ ProductLikeIncidence.realCubeIndexSet δ ambient₃ := ⟨x, hxIco, h3⟩
    simpa [Iamb3, Set.Finite.coe_toFinset] using h4

  -- Step 2: Convert Nplane bounds to real card bounds
  have h_Nreal_card : ∀ (S : Set ℝ) (hS : Bornology.IsBounded S),
      Nreal δ S = (↑((ProductLikeIncidence.realCubeIndexSet_finite hδ hS).toFinset.card) : ENNReal) := by
    intro S hS
    have h_eq1 : Nreal δ S = ENat.toENNReal (ProductLikeIncidence.realCubeIndexSet δ S).encard :=
      nreal_eq_index_ennreal hδ hS
    have h_fin : (ProductLikeIncidence.realCubeIndexSet δ S).Finite :=
      ProductLikeIncidence.realCubeIndexSet_finite hδ hS
    rw [h_eq1, Set.Finite.encard_eq_coe_toFinset_card h_fin] <;> norm_cast

  have h_pair12 : ∀ y ∈ D,
      ((idx1 y).card : ℝ) * ((idx2 y).card : ℝ) ≥
      c * (Iamb1.card : ℝ) * (Iamb2.card : ℝ) := by
    intro y hy
    have h_idx1 : idx1 y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₁_bdd y hy)).toFinset := by
      simp [idx1, hy]
    have h_idx2 : idx2 y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₂_bdd y hy)).toFinset := by
      simp [idx2, hy]
    exact pairwise_bound_to_card hδ (hB₁_bdd y hy) (hB₂_bdd y hy) hamb₁_bdd hamb₂_bdd
      (idx1 y) (idx2 y) Iamb1 Iamb2 h_idx1 h_idx2 rfl rfl hc_pos (hG12 y hy) h_Nreal_card

  have h_pair23 : ∀ y ∈ D,
      ((idx2 y).card : ℝ) * ((idx3 y).card : ℝ) ≥
      c * (Iamb2.card : ℝ) * (Iamb3.card : ℝ) := by
    intro y hy
    have h_idx2 : idx2 y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₂_bdd y hy)).toFinset := by
      simp [idx2, hy]
    have h_idx3 : idx3 y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₃_bdd y hy)).toFinset := by
      simp [idx3, hy]
    exact pairwise_bound_to_card hδ (hB₂_bdd y hy) (hB₃_bdd y hy) hamb₂_bdd hamb₃_bdd
      (idx2 y) (idx3 y) Iamb2 Iamb3 h_idx2 h_idx3 rfl rfl hc_pos (hG23 y hy) h_Nreal_card

  have h_pair13 : ∀ y ∈ D,
      ((idx1 y).card : ℝ) * ((idx3 y).card : ℝ) ≥
      c * (Iamb1.card : ℝ) * (Iamb3.card : ℝ) := by
    intro y hy
    have h_idx1 : idx1 y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₁_bdd y hy)).toFinset := by
      simp [idx1, hy]
    have h_idx3 : idx3 y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₃_bdd y hy)).toFinset := by
      simp [idx3, hy]
    exact pairwise_bound_to_card hδ (hB₁_bdd y hy) (hB₃_bdd y hy) hamb₁_bdd hamb₃_bdd
      (idx1 y) (idx3 y) Iamb1 Iamb3 h_idx1 h_idx3 rfl rfl hc_pos (hG13 y hy) h_Nreal_card

  -- Step 3: Triple product bound
  let c' : ℝ := c ^ (3 / 2 : ℝ)
  have hc'_pos : 0 < c' := by positivity
  have hc'_le_one : c' ≤ 1 := by
    have h1 : c ^ (3 / 2 : ℝ) ≤ 1 := by
      apply Real.rpow_le_one (by linarith) (by linarith) (by norm_num)
    exact h1
  have h_triple : ∀ y ∈ D,
      ((idx1 y).card : ℝ) * ((idx2 y).card : ℝ) * ((idx3 y).card : ℝ) ≥
      c' * ((Iamb1.card : ℝ) * (Iamb2.card : ℝ) * (Iamb3.card : ℝ)) := by
    intro y hy
    have h := triple_finset_card_bound hc_pos.le (h_pair12 y hy) (h_pair23 y hy) (h_pair13 y hy)
    have h_eq : c ^ (3 / 2 : ℝ) * (Iamb1.card : ℝ) * (Iamb2.card : ℝ) * (Iamb3.card : ℝ) =
        c' * ((Iamb1.card : ℝ) * (Iamb2.card : ℝ) * (Iamb3.card : ℝ)) := by
      simp [c'] <;> ring
    rw [h_eq] at h
    exact h

  -- Step 4: Ambient nonemptiness
  have h_amb1_nonempty : Iamb1.Nonempty :=
    ProductLikeIncidence.cube_index_nonempty hδ hamb₁_bdd hamb₁_nonempty
  have h_amb2_nonempty : Iamb2.Nonempty :=
    ProductLikeIncidence.cube_index_nonempty hδ hamb₂_bdd hamb₂_nonempty
  have h_amb3_nonempty : Iamb3.Nonempty :=
    ProductLikeIncidence.cube_index_nonempty hδ hamb₃_bdd hamb₃_nonempty

  -- Step 5: Apply 3-factor graph lemma
  have hα_le' : α ≤ c'^3 / 32 := by
    have h1 : c'^3 = c ^ (9 / 2 : ℝ) := by
      simp only [c']
      have h21 : (c ^ (3 / 2 : ℝ)) ^ 3 = (c ^ (3 / 2 : ℝ)) * (c ^ (3 / 2 : ℝ)) * (c ^ (3 / 2 : ℝ)) := by ring
      rw [h21]
      have h22 : (c ^ (3 / 2 : ℝ)) * (c ^ (3 / 2 : ℝ)) * (c ^ (3 / 2 : ℝ)) =
          c ^ ((3 / 2 : ℝ) + (3 / 2 : ℝ) + (3 / 2 : ℝ)) := by
        have h_a : (c ^ (3 / 2 : ℝ)) * (c ^ (3 / 2 : ℝ)) = c ^ ((3 / 2 : ℝ) + (3 / 2 : ℝ)) :=
          (Real.rpow_add hc_pos (3 / 2 : ℝ) (3 / 2 : ℝ)).symm
        rw [h_a]
        have h_b : c ^ ((3 / 2 : ℝ) + (3 / 2 : ℝ)) * (c ^ (3 / 2 : ℝ)) =
            c ^ (((3 / 2 : ℝ) + (3 / 2 : ℝ)) + (3 / 2 : ℝ)) :=
          (Real.rpow_add hc_pos ((3 / 2 : ℝ) + (3 / 2 : ℝ)) (3 / 2 : ℝ)).symm
        rw [h_b] <;> ring
      rw [h22]
      have h23 : (3 / 2 : ℝ) + (3 / 2 : ℝ) + (3 / 2 : ℝ) = (9 / 2 : ℝ) := by norm_num
      rw [h23]
    rw [h1]
    exact hα_le
  have hmass_le' : mass ≤ c'^2 / 16 := by
    have h1 : c'^2 = c ^ 3 := by
      simp only [c']
      have h21 : (c ^ (3 / 2 : ℝ)) ^ 2 = (c ^ (3 / 2 : ℝ)) * (c ^ (3 / 2 : ℝ)) := by ring
      rw [h21]
      have h22 : (c ^ (3 / 2 : ℝ)) * (c ^ (3 / 2 : ℝ)) = c ^ ((3 / 2 : ℝ) + (3 / 2 : ℝ)) :=
        (Real.rpow_add hc_pos (3 / 2 : ℝ) (3 / 2 : ℝ)).symm
      rw [h22]
      have h23 : (3 / 2 : ℝ) + (3 / 2 : ℝ) = 3 := by norm_num
      rw [h23]
      norm_cast
    rw [h1]
    exact hmass_le

  have h_main := GraphLemma.representative_big_intersection_graph_three
    hD_nonempty hw_nonneg hW_pos hW_sum
    h_amb1_nonempty h_amb2_nonempty h_amb3_nonempty
    h1_sub h2_sub h3_sub
    hc'_pos hc'_le_one h_triple
    hα_pos hmass_pos hα_le' hmass_le'

  rcases h_main with ⟨y_star, hy_star, D', hD'_sub, h_mass, h_shared⟩

  -- Step 6: Geometric thickening bridge for each factor
  refine ⟨y_star, hy_star, D', hD'_sub, h_mass, fun y hy => ?_⟩
  have h_counts := h_shared y hy
  have hyD : y ∈ D := hD'_sub hy

  have h_idx1_y : idx1 y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₁_bdd y hyD)).toFinset := by
    simp [idx1, hyD]
  have h_idx1_ystar : idx1 y_star = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₁_bdd y_star hy_star)).toFinset := by
    simp [idx1, hy_star]
  have h_idx2_y : idx2 y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₂_bdd y hyD)).toFinset := by
    simp [idx2, hyD]
  have h_idx2_ystar : idx2 y_star = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₂_bdd y_star hy_star)).toFinset := by
    simp [idx2, hy_star]
  have h_idx3_y : idx3 y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₃_bdd y hyD)).toFinset := by
    simp [idx3, hyD]
  have h_idx3_ystar : idx3 y_star = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB₃_bdd y_star hy_star)).toFinset := by
    simp [idx3, hy_star]

  let S1 := Metric.cthickening (Real.sqrt 2 * δ) (B₁ y_star) ∩ B₁ y
  let S2 := Metric.cthickening (Real.sqrt 2 * δ) (B₂ y_star) ∩ B₂ y
  let S3 := Metric.cthickening (Real.sqrt 2 * δ) (B₃ y_star) ∩ B₃ y
  have hS1_bdd : Bornology.IsBounded S1 := (hB₁_bdd y_star hy_star).cthickening.subset Set.inter_subset_left
  have hS2_bdd : Bornology.IsBounded S2 := (hB₂_bdd y_star hy_star).cthickening.subset Set.inter_subset_left
  have hS3_bdd : Bornology.IsBounded S3 := (hB₃_bdd y_star hy_star).cthickening.subset Set.inter_subset_left
  let K1 := (ProductLikeIncidence.realCubeIndexSet_finite hδ hS1_bdd).toFinset
  let K2 := (ProductLikeIncidence.realCubeIndexSet_finite hδ hS2_bdd).toFinset
  let K3 := (ProductLikeIncidence.realCubeIndexSet_finite hδ hS3_bdd).toFinset

  have h1_idx_sub : (idx1 y ∩ idx1 y_star) ⊆ K1 := by
    rw [h_idx1_y, h_idx1_ystar]
    intro k hk
    have hkA : k ∈ ProductLikeIncidence.realCubeIndexSet δ (B₁ y) := by
      simpa [Set.Finite.coe_toFinset] using (Finset.mem_inter.mp hk).1
    have hkAstar : k ∈ ProductLikeIncidence.realCubeIndexSet δ (B₁ y_star) := by
      simpa [Set.Finite.coe_toFinset] using (Finset.mem_inter.mp hk).2
    have h : k ∈ ProductLikeIncidence.realCubeIndexSet δ
        (B₁ y ∩ Metric.cthickening (Real.sqrt 2 * δ) (B₁ y_star)) :=
      TwoSidedBigCap.index_intersection_subset_thickened hδ k hkA hkAstar
    have h_eq : (B₁ y ∩ Metric.cthickening (Real.sqrt 2 * δ) (B₁ y_star)) =
        (Metric.cthickening (Real.sqrt 2 * δ) (B₁ y_star) ∩ B₁ y) := by
      ext z; simp [and_comm]
    rw [h_eq] at h
    simpa [K1, Set.Finite.coe_toFinset] using h

  have h2_idx_sub : (idx2 y ∩ idx2 y_star) ⊆ K2 := by
    rw [h_idx2_y, h_idx2_ystar]
    intro k hk
    have hkB : k ∈ ProductLikeIncidence.realCubeIndexSet δ (B₂ y) := by
      simpa [Set.Finite.coe_toFinset] using (Finset.mem_inter.mp hk).1
    have hkBstar : k ∈ ProductLikeIncidence.realCubeIndexSet δ (B₂ y_star) := by
      simpa [Set.Finite.coe_toFinset] using (Finset.mem_inter.mp hk).2
    have h : k ∈ ProductLikeIncidence.realCubeIndexSet δ
        (B₂ y ∩ Metric.cthickening (Real.sqrt 2 * δ) (B₂ y_star)) :=
      TwoSidedBigCap.index_intersection_subset_thickened hδ k hkB hkBstar
    have h_eq : (B₂ y ∩ Metric.cthickening (Real.sqrt 2 * δ) (B₂ y_star)) =
        (Metric.cthickening (Real.sqrt 2 * δ) (B₂ y_star) ∩ B₂ y) := by
      ext z; simp [and_comm]
    rw [h_eq] at h
    simpa [K2, Set.Finite.coe_toFinset] using h

  have h3_idx_sub : (idx3 y ∩ idx3 y_star) ⊆ K3 := by
    rw [h_idx3_y, h_idx3_ystar]
    intro k hk
    have hkC : k ∈ ProductLikeIncidence.realCubeIndexSet δ (B₃ y) := by
      simpa [Set.Finite.coe_toFinset] using (Finset.mem_inter.mp hk).1
    have hkCstar : k ∈ ProductLikeIncidence.realCubeIndexSet δ (B₃ y_star) := by
      simpa [Set.Finite.coe_toFinset] using (Finset.mem_inter.mp hk).2
    have h : k ∈ ProductLikeIncidence.realCubeIndexSet δ
        (B₃ y ∩ Metric.cthickening (Real.sqrt 2 * δ) (B₃ y_star)) :=
      TwoSidedBigCap.index_intersection_subset_thickened hδ k hkC hkCstar
    have h_eq : (B₃ y ∩ Metric.cthickening (Real.sqrt 2 * δ) (B₃ y_star)) =
        (Metric.cthickening (Real.sqrt 2 * δ) (B₃ y_star) ∩ B₃ y) := by
      ext z; simp [and_comm]
    rw [h_eq] at h
    simpa [K3, Set.Finite.coe_toFinset] using h

  have h1_card_le : ((idx1 y ∩ idx1 y_star).card : ℝ) ≤ (K1.card : ℝ) := by
    exact_mod_cast Finset.card_le_card h1_idx_sub
  have h2_card_le : ((idx2 y ∩ idx2 y_star).card : ℝ) ≤ (K2.card : ℝ) := by
    exact_mod_cast Finset.card_le_card h2_idx_sub
  have h3_card_le : ((idx3 y ∩ idx3 y_star).card : ℝ) ≤ (K3.card : ℝ) := by
    exact_mod_cast Finset.card_le_card h3_idx_sub

  have h1_eq : Nreal δ S1 = (↑K1.card : ENNReal) := h_Nreal_card S1 hS1_bdd
  have h2_eq : Nreal δ S2 = (↑K2.card : ENNReal) := h_Nreal_card S2 hS2_bdd
  have h3_eq : Nreal δ S3 = (↑K3.card : ENNReal) := h_Nreal_card S3 hS3_bdd

  have h1star_eq : Nreal δ (B₁ y_star) = (↑((idx1 y_star).card) : ENNReal) := by
    rw [h_Nreal_card (B₁ y_star) (hB₁_bdd y_star hy_star), h_idx1_ystar] <;> rfl
  have h2star_eq : Nreal δ (B₂ y_star) = (↑((idx2 y_star).card) : ENNReal) := by
    rw [h_Nreal_card (B₂ y_star) (hB₂_bdd y_star hy_star), h_idx2_ystar] <;> rfl
  have h3star_eq : Nreal δ (B₃ y_star) = (↑((idx3 y_star).card) : ENNReal) := by
    rw [h_Nreal_card (B₃ y_star) (hB₃_bdd y_star hy_star), h_idx3_ystar] <;> rfl

  have h1_concl : Nreal δ (Metric.cthickening (Real.sqrt 2 * δ) (B₁ y_star) ∩ B₁ y) ≥
      ENNReal.ofReal α * Nreal δ (B₁ y_star) := by
    rw [h1_eq, h1star_eq]
    have h1 : (K1.card : ℝ) ≥ α * ((idx1 y_star).card : ℝ) := by
      linarith [h1_card_le, h_counts.1]
    have h2 : (↑K1.card : ENNReal) ≥ ENNReal.ofReal (α * ((idx1 y_star).card : ℝ)) := by
      have h_coe : (↑K1.card : ENNReal) = ENNReal.ofReal ((K1.card : ℝ)) := by simp
      rw [h_coe]
      exact ENNReal.ofReal_le_ofReal h1
    have h3 : ENNReal.ofReal α * (↑((idx1 y_star).card) : ENNReal) =
        ENNReal.ofReal (α * ((idx1 y_star).card : ℝ)) := by
      rw [ENNReal.ofReal_mul hα_pos.le] <;> simp
    rw [h3]
    exact h2

  have h2_concl : Nreal δ (Metric.cthickening (Real.sqrt 2 * δ) (B₂ y_star) ∩ B₂ y) ≥
      ENNReal.ofReal α * Nreal δ (B₂ y_star) := by
    rw [h2_eq, h2star_eq]
    have h1 : (K2.card : ℝ) ≥ α * ((idx2 y_star).card : ℝ) := by
      linarith [h2_card_le, h_counts.2.1]
    have h2 : (↑K2.card : ENNReal) ≥ ENNReal.ofReal (α * ((idx2 y_star).card : ℝ)) := by
      have h_coe : (↑K2.card : ENNReal) = ENNReal.ofReal ((K2.card : ℝ)) := by simp
      rw [h_coe]
      exact ENNReal.ofReal_le_ofReal h1
    have h3 : ENNReal.ofReal α * (↑((idx2 y_star).card) : ENNReal) =
        ENNReal.ofReal (α * ((idx2 y_star).card : ℝ)) := by
      rw [ENNReal.ofReal_mul hα_pos.le] <;> simp
    rw [h3]
    exact h2

  have h3_concl : Nreal δ (Metric.cthickening (Real.sqrt 2 * δ) (B₃ y_star) ∩ B₃ y) ≥
      ENNReal.ofReal α * Nreal δ (B₃ y_star) := by
    rw [h3_eq, h3star_eq]
    have h1 : (K3.card : ℝ) ≥ α * ((idx3 y_star).card : ℝ) := by
      linarith [h3_card_le, h_counts.2.2]
    have h2 : (↑K3.card : ENNReal) ≥ ENNReal.ofReal (α * ((idx3 y_star).card : ℝ)) := by
      have h_coe : (↑K3.card : ENNReal) = ENNReal.ofReal ((K3.card : ℝ)) := by simp
      rw [h_coe]
      exact ENNReal.ofReal_le_ofReal h1
    have h3 : ENNReal.ofReal α * (↑((idx3 y_star).card) : ENNReal) =
        ENNReal.ofReal (α * ((idx3 y_star).card : ℝ)) := by
      rw [ENNReal.ofReal_mul hα_pos.le] <;> simp
    rw [h3]
    exact h2

  exact ⟨h1_concl, h2_concl, h3_concl⟩

/-!
## BSG corollary

Wrapper around `DiscretizedBSG.discretized_bsg` using `Nreal`/`Nplane` notation.
-/

/-- Convert a set of pairs to a subset of the Euclidean plane. -/
def graphToPlane (G : Set (ℝ × ℝ)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  (fun p : ℝ × ℝ => (WithLp.equiv 2 (Fin 2 → ℝ)).symm
    (fun i : Fin 2 => if i = 0 then p.1 else p.2)) '' G

/-- Helper: `Nplane δ (graphToPlane G)` equals the cardinality of the product index finset. -/
lemma nplane_eq_productIndexFinset {δ : ℝ} (hδ : 0 < δ)
    {G : Set (ℝ × ℝ)} (hG_bdd : Bornology.IsBounded G) :
    Nplane δ (graphToPlane G) = (↑(DiscretizedBSG.productIndexFinset δ hδ hG_bdd).card : ENNReal) := by
  let idxG := DiscretizedBSG.productIndexSet δ G
  let f : ℤ × ℤ → Set (EuclideanSpace ℝ (Fin 2)) := fun p =>
    dyadicCube δ (fun i : Fin 2 => if i = 0 then p.1 else p.2)
  have h_main : dyadicCubesMeeting (d := 2) δ (graphToPlane G) = f '' idxG := by
    ext Q
    simp only [dyadicCubesMeeting, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hQ_cube, ⟨p, hpQ, hpG⟩⟩
      rcases hQ_cube with ⟨k, rfl⟩
      rcases hpG with ⟨r, hrG, rfl⟩
      have h_p0_in : r.1 ∈ Set.Ico (δ * (k 0 : ℝ)) (δ * ((k 0 : ℝ) + 1)) := hpQ 0
      have h_p1_in : r.2 ∈ Set.Ico (δ * (k 1 : ℝ)) (δ * ((k 1 : ℝ) + 1)) := hpQ 1
      have h1 : (k 0, k 1) ∈ idxG := by
        simpa [DiscretizedBSG.productIndexSet, Set.mem_prod] using ⟨r, ⟨h_p0_in, h_p1_in⟩, hrG⟩
      refine ⟨(k 0, k 1), h1, ?_⟩
      have h3 : (fun i : Fin 2 => if i = 0 then (k 0, k 1).1 else (k 0, k 1).2) = k := by
        ext i; fin_cases i <;> simp
      exact congr_arg (dyadicCube δ) h3
    · rintro ⟨⟨kA, kB⟩, hk, rfl⟩
      have h1 : ((Set.Ico (δ * (kA : ℝ)) (δ * ((kA : ℝ) + 1)) ×ˢ
                 Set.Ico (δ * (kB : ℝ)) (δ * ((kB : ℝ) + 1))) ∩ G).Nonempty := hk
      rcases h1 with ⟨p, hp_cube, hpG⟩
      let g : Fin 2 → ℝ := fun i => if i = 0 then p.1 else p.2
      let q : EuclideanSpace ℝ (Fin 2) := (WithLp.equiv 2 (Fin 2 → ℝ)).symm g
      have hqQ : q ∈ dyadicCube δ (fun i : Fin 2 => if i = 0 then kA else kB) := by
        intro i; fin_cases i <;> simp [q, g, hp_cube.1, hp_cube.2]
      have hqG : q ∈ graphToPlane G := by
        exact ⟨p, hpG, rfl⟩
      exact ⟨⟨(fun i : Fin 2 => if i = 0 then kA else kB), rfl⟩, ⟨q, hqQ, hqG⟩⟩
  have h_inj : Set.InjOn f idxG := by
    rintro ⟨kA1, kB1⟩ _ ⟨kA2, kB2⟩ _ h
    have h_inj' : Function.Injective (dyadicCube δ : (Fin 2 → ℤ) → Set (EuclideanSpace ℝ (Fin 2))) :=
      TwoSidedBigCap.dyadicCube_injective hδ
    have h_eq : (fun i : Fin 2 => if i = 0 then kA1 else kB1) = (fun i : Fin 2 => if i = 0 then kA2 else kB2) := h_inj' h
    have hkA : kA1 = kA2 := by have h := congr_fun h_eq 0; simpa using h
    have hkB : kB1 = kB2 := by have h := congr_fun h_eq 1; simpa using h
    exact Prod.ext hkA hkB
  have hG_fin : idxG.Finite := DiscretizedBSG.productIndexSet_finite hδ hG_bdd
  rw [Nplane, dyadicCoveringNumber, h_main]
  rw [h_inj.encard_image]
  have h_eq2 : idxG.encard = ↑(DiscretizedBSG.productIndexFinset δ hδ hG_bdd).card := by
    simp [DiscretizedBSG.productIndexFinset, Set.Finite.encard_eq_coe_toFinset_card hG_fin] <;> rfl
  rw [h_eq2] <;> norm_cast

/-- Helper: `Nreal δ A` equals the cardinality of the real cube index finset. -/
lemma nreal_eq_realCubeIndexFinset {δ : ℝ} (hδ : 0 < δ)
    {A : Set ℝ} (hA_bdd : Bornology.IsBounded A) :
    Nreal δ A = (↑(DiscretizedBSG.realCubeIndexFinset δ hδ hA_bdd).card : ENNReal) := by
  have h_eq1 : Nreal δ A = ENat.toENNReal (ProductLikeIncidence.realCubeIndexSet δ A).encard :=
    nreal_eq_index_ennreal hδ hA_bdd
  rw [h_eq1]
  have h_fin : (ProductLikeIncidence.realCubeIndexSet δ A).Finite :=
    ProductLikeIncidence.realCubeIndexSet_finite hδ hA_bdd
  rw [Set.Finite.encard_eq_coe_toFinset_card h_fin]
  <;> simp [DiscretizedBSG.realCubeIndexFinset] <;> norm_cast

/-- Helper: convert `a * b ≤ (n : ℝ)` to ENNReal. -/
lemma ofReal_mul_le_coe {n : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a * b ≤ (n : ℝ)) :
    ENNReal.ofReal a * ENNReal.ofReal b ≤ (↑n : ENNReal) := by
  have h1 : (↑n : ENNReal) = ENNReal.ofReal (n : ℝ) := by simp
  have h2 : ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) := by
    rw [← ENNReal.ofReal_mul ha] <;> rfl
  rw [h1, h2]
  exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr h

/-- Helper: convert `(n : ℝ) ≤ a * b` to ENNReal. -/
lemma coe_le_ofReal_mul {n : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : (n : ℝ) ≤ a * b) :
    (↑n : ENNReal) ≤ ENNReal.ofReal a * ENNReal.ofReal b := by
  have h1 : (↑n : ENNReal) = ENNReal.ofReal (n : ℝ) := by simp
  have h2 : ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) := by
    rw [← ENNReal.ofReal_mul ha] <;> rfl
  rw [h1, h2]
  exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr h

/-- Helper: convert `a * (m : ℝ) ≤ (n : ℝ)` to ENNReal with nat coeffs. -/
lemma ofReal_natMul_le_natCoe {n m : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (h : a * (m : ℝ) ≤ (n : ℝ)) :
    ENNReal.ofReal a * (↑m : ENNReal) ≤ (↑n : ENNReal) := by
  have hm : (↑m : ENNReal) = ENNReal.ofReal (m : ℝ) := by simp
  rw [hm]
  exact ofReal_mul_le_coe ha (by positivity) h

/-- Helper: convert `a * b * c ≤ (n : ℝ)` to ENNReal. -/
lemma ofReal_mul3_le_coe {n : ℕ} {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a * b * c ≤ (n : ℝ)) :
    ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c ≤ (↑n : ENNReal) := by
  have h_pos : 0 ≤ a * b := by positivity
  have h_ab : ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) := by
    rw [← ENNReal.ofReal_mul ha] <;> rfl
  have h2 : ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c =
      ENNReal.ofReal (a * b * c) := by
    rw [h_ab, ← ENNReal.ofReal_mul h_pos] <;> ring
  have h1 : (↑n : ENNReal) = ENNReal.ofReal (n : ℝ) := by simp
  rw [h1, h2]
  exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr h

/-- Helper: convert `a * (m : ℝ) * (k : ℝ) ≤ (n : ℝ)` to ENNReal. -/
lemma ofReal_natMul3_le_natCoe {n m k : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (h : a * (m : ℝ) * (k : ℝ) ≤ (n : ℝ)) :
    ENNReal.ofReal a * (↑m : ENNReal) * (↑k : ENNReal) ≤ (↑n : ENNReal) := by
  have hm : (↑m : ENNReal) = ENNReal.ofReal (m : ℝ) := by simp
  have hk : (↑k : ENNReal) = ENNReal.ofReal (k : ℝ) := by simp
  rw [hm, hk]
  exact ofReal_mul3_le_coe ha (by positivity) (by positivity) h

/-- Helper: convert `(n : ℝ) ≤ a` to ENNReal. -/
lemma natCoe_le_ofReal {n : ℕ} {a : ℝ} (h : (n : ℝ) ≤ a) :
    (↑n : ENNReal) ≤ ENNReal.ofReal a := by
  have h_npos : 0 ≤ (n : ℝ) := by positivity
  have h_apos : 0 ≤ a := by linarith
  have h1 : (↑n : ENNReal) = ENNReal.ofReal (n : ℝ) := by simp
  rw [h1]
  exact ENNReal.ofReal_le_ofReal_iff h_apos |>.mpr h

/-- Helper: convert `(n : ℝ) ≤ a * (m : ℝ)` to ENNReal with nat coeff. -/
lemma natCoe_le_ofReal_natMul {n m : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (h : (n : ℝ) ≤ a * (m : ℝ)) :
    (↑n : ENNReal) ≤ ENNReal.ofReal a * (↑m : ENNReal) := by
  have hm : (↑m : ENNReal) = ENNReal.ofReal (m : ℝ) := by simp
  rw [hm]
  exact coe_le_ofReal_mul ha (by positivity) h

/--
**BSG corollary** in `Nreal`/`Nplane` notation.

Given bounded `A, B ⊂ ℝ`, a graph `G ⊂ A × B` with density
`Nplane(graphToPlane G) ≥ (1/K) · Nreal(A) · Nreal(B)` and small restricted sumset
`Nreal(A +^G B) ≤ K · sqrt(Nreal(A) · Nreal(B))`, apply DiscretizedBSG
to extract large subsets `A' ⊆ A`, `B' ⊆ B` with controlled sumset and
dense graph intersection.
-/
theorem bsg_corollary
    {δ : ℝ} (hδ : 0 < δ)
    {A B : Set ℝ} (hA_bdd : Bornology.IsBounded A) (hB_bdd : Bornology.IsBounded B)
    {G : Set (ℝ × ℝ)} (hG_bdd : Bornology.IsBounded G) (hG_sub : G ⊆ Set.prod A B)
    {K : ℝ} (hK : 1 < K)
    (h_density : Nplane δ (graphToPlane G) ≥ ENNReal.ofReal (1 / K) * Nreal δ A * Nreal δ B)
    (h_sumset : Nreal δ (DiscretizedBSG.restrictedSumSet G) ≤
        ENNReal.ofReal K * ENNReal.ofReal (Real.sqrt ((Nreal δ A).toReal * (Nreal δ B).toReal))) :
    ∃ (A' B' : Set ℝ),
      A' ⊆ A ∧ B' ⊆ B ∧
      Nreal δ A' ≥ ENNReal.ofReal (1 / (K^10 * (3 : ℝ)^10)) * Nreal δ A ∧
      Nreal δ B' ≥ ENNReal.ofReal (1 / (K^10 * (3 : ℝ)^10)) * Nreal δ B ∧
      Nreal δ (Set.image2 (· + ·) A' B') ≤
        ENNReal.ofReal ((2 : ℝ)^13 * (3 : ℝ)^10 * K^10) *
          ENNReal.ofReal (Real.sqrt ((Nreal δ A).toReal * (Nreal δ B).toReal)) ∧
      Nplane δ (graphToPlane (G ∩ Set.prod A' B')) ≥
        ENNReal.ofReal (1 / ((16 : ℝ) * K^22 * (3 : ℝ)^22)) * Nreal δ A * Nreal δ B := by
  let IA := DiscretizedBSG.realCubeIndexFinset δ hδ hA_bdd
  let IB := DiscretizedBSG.realCubeIndexFinset δ hδ hB_bdd
  let IG := DiscretizedBSG.productIndexFinset δ hδ hG_bdd
  let ISG := DiscretizedBSG.restrictedSumIndexFinset δ hδ hG_bdd
  have hIA_eq : Nreal δ A = (↑IA.card : ENNReal) := nreal_eq_realCubeIndexFinset hδ hA_bdd
  have hIB_eq : Nreal δ B = (↑IB.card : ENNReal) := nreal_eq_realCubeIndexFinset hδ hB_bdd
  have hIG_eq : Nplane δ (graphToPlane G) = (↑IG.card : ENNReal) := nplane_eq_productIndexFinset hδ hG_bdd
  have hISG_eq : Nreal δ (DiscretizedBSG.restrictedSumSet G) = (↑ISG.card : ENNReal) :=
    nreal_eq_realCubeIndexFinset hδ (DiscretizedBSG.restrictedSumSet_bounded hG_bdd)
  have h_density' : (IA.card : ℝ) * (IB.card : ℝ) ≤ K * (IG.card : ℝ) := by
    have h : (↑IG.card : ENNReal) ≥ ENNReal.ofReal (1 / K) * (↑IA.card : ENNReal) * (↑IB.card : ENNReal) := by
      rw [hIG_eq, hIA_eq, hIB_eq] at h_density; exact h_density
    have h_pos : 0 ≤ (1 / K) * (IA.card : ℝ) * (IB.card : ℝ) := by positivity
    have h1 : (↑IG.card : ENNReal) = ENNReal.ofReal (IG.card : ℝ) := by simp
    have h_IA : (↑IA.card : ENNReal) = ENNReal.ofReal (IA.card : ℝ) := by simp
    have h_IB : (↑IB.card : ENNReal) = ENNReal.ofReal (IB.card : ℝ) := by simp
    rw [h1, h_IA, h_IB] at h
    have h2 : ENNReal.ofReal (1 / K) * ENNReal.ofReal (IA.card : ℝ) * ENNReal.ofReal (IB.card : ℝ) =
        ENNReal.ofReal ((1 / K) * (IA.card : ℝ) * (IB.card : ℝ)) := by
      have h_ab : ENNReal.ofReal (1 / K) * ENNReal.ofReal (IA.card : ℝ) =
          ENNReal.ofReal ((1 / K) * (IA.card : ℝ)) := by
        rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
      rw [h_ab]
      rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
    rw [h2] at h
    have h_igpos : 0 ≤ (IG.card : ℝ) := by positivity
    have h_real : (1 / K) * (IA.card : ℝ) * (IB.card : ℝ) ≤ (IG.card : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff h_igpos).mp h
    have hK_pos : 0 < K := by linarith
    calc (IA.card : ℝ) * (IB.card : ℝ)
        = K * ((1 / K) * (IA.card : ℝ) * (IB.card : ℝ)) := by field_simp [hK_pos.ne'] <;> ring
      _ ≤ K * (IG.card : ℝ) := by gcongr
  have h_sumset' : (ISG.card : ℝ) ≤ K * Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ)) := by
    have h : (↑ISG.card : ENNReal) ≤ ENNReal.ofReal K * ENNReal.ofReal (Real.sqrt ((Nreal δ A).toReal * (Nreal δ B).toReal)) := by
      rw [hISG_eq] at h_sumset; exact h_sumset
    have h_ISG : (↑ISG.card : ENNReal) = ENNReal.ofReal (ISG.card : ℝ) := by simp
    have h_toReal1 : (Nreal δ A).toReal = (IA.card : ℝ) := by rw [hIA_eq] <;> simp
    have h_toReal2 : (Nreal δ B).toReal = (IB.card : ℝ) := by rw [hIB_eq] <;> simp
    have h_simp : ENNReal.ofReal K * ENNReal.ofReal (Real.sqrt ((Nreal δ A).toReal * (Nreal δ B).toReal)) =
        ENNReal.ofReal (K * Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ))) := by
      rw [h_toReal1, h_toReal2, ← ENNReal.ofReal_mul (by positivity)] <;> rfl
    rw [h_ISG, h_simp] at h
    have h_rpos : 0 ≤ K * Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ)) := by positivity
    exact (ENNReal.ofReal_le_ofReal_iff h_rpos).mp h
  have h_main := DiscretizedBSG.discretized_bsg hδ hA_bdd hB_bdd hG_bdd hG_sub hK h_density' h_sumset'
  rcases h_main with ⟨AI, BI, hAI_sub, hBI_sub, hAI_card, hBI_card, h_sumset_bound, h_graph_density⟩
  let A' := DiscretizedBSG.indexToRealSet δ AI A
  let B' := DiscretizedBSG.indexToRealSet δ BI B
  have hA'_sub : A' ⊆ A := by intro x hx; exact hx.1
  have hB'_sub : B' ⊆ B := by intro x hx; exact hx.1
  have hA'_bdd : Bornology.IsBounded A' := hA_bdd.subset hA'_sub
  have hB'_bdd : Bornology.IsBounded B' := hB_bdd.subset hB'_sub
  have hIA_coe : (↑IA : Set ℤ) = ProductLikeIncidence.realCubeIndexSet δ A := by
    simp [IA, DiscretizedBSG.realCubeIndexFinset] <;> rfl
  have hA'_eq : Nreal δ A' = (↑AI.card : ENNReal) := by
    have h1 : Nreal δ A' = ENat.toENNReal (ProductLikeIncidence.realCubeIndexSet δ A').encard :=
      nreal_eq_index_ennreal hδ hA'_bdd
    rw [h1]
    have h2 : ProductLikeIncidence.realCubeIndexSet δ A' = (↑AI : Set ℤ) := by
      ext k
      simp only [Finset.mem_coe, ProductLikeIncidence.realCubeIndexSet]
      constructor
      · rintro ⟨x, hxIco, hxA'⟩
        rcases hxA'.2 with ⟨i, hiAI, hxi⟩
        have h4 : k = i := DiscretizedBSG.dyadic_cubes_disjoint1D hδ hxIco hxi
        rw [h4]; exact hiAI
      · intro hk
        have h3 : k ∈ IA := hAI_sub hk
        have h4 : k ∈ ProductLikeIncidence.realCubeIndexSet δ A := by
          have h5 : k ∈ (↑IA : Set ℤ) := h3
          rw [hIA_coe] at h5; exact h5
        have h6 : (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ A).Nonempty := h4
        rcases h6 with ⟨x, hxIco, hxA⟩
        exact ⟨x, hxIco, ⟨hxA, k, hk, hxIco⟩⟩
    rw [h2, Set.encard_coe_eq_coe_finsetCard] <;> norm_cast
  have hIB_coe : (↑IB : Set ℤ) = ProductLikeIncidence.realCubeIndexSet δ B := by
    simp [IB, DiscretizedBSG.realCubeIndexFinset] <;> rfl
  have hB'_eq : Nreal δ B' = (↑BI.card : ENNReal) := by
    have h1 : Nreal δ B' = ENat.toENNReal (ProductLikeIncidence.realCubeIndexSet δ B').encard :=
      nreal_eq_index_ennreal hδ hB'_bdd
    rw [h1]
    have h2 : ProductLikeIncidence.realCubeIndexSet δ B' = (↑BI : Set ℤ) := by
      ext k
      simp only [Finset.mem_coe, ProductLikeIncidence.realCubeIndexSet]
      constructor
      · rintro ⟨x, hxIco, hxB'⟩
        rcases hxB'.2 with ⟨i, hiBI, hxi⟩
        have h4 : k = i := DiscretizedBSG.dyadic_cubes_disjoint1D hδ hxIco hxi
        rw [h4]; exact hiBI
      · intro hk
        have h3 : k ∈ IB := hBI_sub hk
        have h4 : k ∈ ProductLikeIncidence.realCubeIndexSet δ B := by
          have h5 : k ∈ (↑IB : Set ℤ) := h3
          rw [hIB_coe] at h5; exact h5
        have h6 : (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ B).Nonempty := h4
        rcases h6 with ⟨x, hxIco, hxB⟩
        exact ⟨x, hxIco, ⟨hxB, k, hk, hxIco⟩⟩
    rw [h2, Set.encard_coe_eq_coe_finsetCard] <;> norm_cast
  let G' := G ∩ Set.prod A' B'
  have hG'_bdd : Bornology.IsBounded G' := hG_bdd.subset (fun x hx => hx.1)
  have hG'_eq : Nplane δ (graphToPlane G') = (↑(DiscretizedBSG.productIndexFinset δ hδ hG'_bdd).card : ENNReal) :=
    nplane_eq_productIndexFinset hδ hG'_bdd
  let S := Set.image2 (· + ·) A' B'
  have hS_bdd : Bornology.IsBounded S := bounded_image2_add hA'_bdd hB'_bdd
  have hS_eq : Nreal δ S = (↑(DiscretizedBSG.realCubeIndexFinset δ hδ hS_bdd).card : ENNReal) :=
    nreal_eq_realCubeIndexFinset hδ hS_bdd
  refine' ⟨A', B', hA'_sub, hB'_sub, _ , _ , _ , _⟩
  · -- Nreal A' ≥ c * Nreal A
    rw [hA'_eq, hIA_eq]
    exact ofReal_natMul_le_natCoe (by positivity) hAI_card
  · -- Nreal B' ≥ c * Nreal B
    rw [hB'_eq, hIB_eq]
    exact ofReal_natMul_le_natCoe (by positivity) hBI_card
  · -- Nreal (A' + B') ≤ C * sqrt(...)
    rw [hS_eq]
    have h_toReal1 : (Nreal δ A).toReal = (IA.card : ℝ) := by rw [hIA_eq] <;> simp
    have h_toReal2 : (Nreal δ B).toReal = (IB.card : ℝ) := by rw [hIB_eq] <;> simp
    have h_rhs_eq : ENNReal.ofReal ((2 : ℝ)^13 * (3 : ℝ)^10 * K^10) *
        ENNReal.ofReal (Real.sqrt ((Nreal δ A).toReal * (Nreal δ B).toReal)) =
        ENNReal.ofReal (((2 : ℝ)^13 * (3 : ℝ)^10 * K^10) * Real.sqrt ((IA.card : ℝ) * (IB.card : ℝ))) := by
      rw [h_toReal1, h_toReal2, ← ENNReal.ofReal_mul (by positivity)] <;> rfl
    rw [h_rhs_eq]
    exact natCoe_le_ofReal h_sumset_bound
  · -- Nplane (G ∩ A'×B') ≥ c' * Nreal A * Nreal B
    rw [hG'_eq, hIA_eq, hIB_eq]
    exact ofReal_natMul3_le_natCoe (by positivity) h_graph_density

end ProductLikeIncidence
