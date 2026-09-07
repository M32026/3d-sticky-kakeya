module

/-
# Grid-Separated Set Covering Number Equals Cardinality

For a finite set on the δ-grid, the dyadic covering number equals
the cardinality, because each grid point occupies a unique δ-cube
(as its lower-left corner) and each cube contains at most one grid point.

## Main results

- `grid_separated_nreal_eq_card`: 2D version
- `grid_separated_nreal_eq_card1d`: 1D version (for `Nreal`)
-/

public import MyLeanRepo.ProductLikeIncidence.RoundedGraphAdapter
public import MyLeanRepo.CubeIndexSet
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set ENNReal Bornology Classical

/-- For a finite 2D set on the δ-grid, the dyadic covering number
equals the cardinality. Each grid point is the lower-left corner
of a unique dyadic cube. -/
lemma grid_separated_nreal_eq_card {δ : ℝ}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hδ_pos : 0 < δ) (hS_finite : S.Finite)
    (hS_grid : ∀ z ∈ S, ∀ i : Fin 2, z i ∈ productLikeIntegerGrid δ)
    (hS_separated : ∀ z ∈ S, ∀ w ∈ S, z ≠ w → dist z w ≥ δ) :
    ENat.toENNReal (dyadicCoveringNumber δ S) =
      ENNReal.ofReal (S.ncard : ℝ) := by
  let g := ProductLikeIncidence.cubeIndexOfPoint δ
  let Sf := hS_finite.toFinset
  have hSf_coe : (Sf : Set _) = S := hS_finite.coe_toFinset

  -- cubeIndexOfPoint is injective on S because grid points have unique integer coords
  have h_inj : Set.InjOn g S := by
    intro z hz w hw h_eq
    have h1 : ∀ i : Fin 2, z i = w i := by
      intro i
      have h2 : g z i = g w i := by rw [h_eq]
      simp only [g, ProductLikeIncidence.cubeIndexOfPoint] at h2
      rcases hS_grid z hz i with ⟨k, hkz⟩
      rcases hS_grid w hw i with ⟨m, hmw⟩
      have h3 : Int.floor ((z i) / δ) = k := by
        rw [hkz]
        have h4 : (δ * (k : ℝ)) / δ = (k : ℝ) := by
          field_simp [hδ_pos.ne'] <;> ring
        rw [h4] <;> simp
      have h4 : Int.floor ((w i) / δ) = m := by
        rw [hmw]
        have h5 : (δ * (m : ℝ)) / δ = (m : ℝ) := by
          field_simp [hδ_pos.ne'] <;> ring
        rw [h5] <;> simp
      rw [h3, h4] at h2
      have h5 : k = m := by exact_mod_cast h2
      calc z i = δ * (k : ℝ) := hkz
        _ = δ * (m : ℝ) := by rw [h5]
        _ = w i := hmw.symm
    have h5 : z = w := by
      ext i
      exact h1 i
    exact h5

  have h_inj' : Set.InjOn g (Sf : Set _) := by
    rw [hSf_coe]
    exact h_inj

  -- Covering number = number of distinct cube indices
  have h1 : ENat.toENNReal (dyadicCoveringNumber δ S) =
      ↑(Sf.image g).card :=
    ProductLikeIncidence.finite_covering2_eq_card hδ_pos hS_finite

  -- Number of distinct cube indices = |S| by injectivity
  have h2 : (Sf.image g).card = Sf.card := by
    rw [Finset.card_image_of_injOn]
    exact h_inj'

  -- Convert to ENNReal.ofReal (S.ncard : ℝ)
  have h_ncard : (S.ncard : ℝ) = (Sf.card : ℝ) := by
    have h4 : S.ncard = ↑Sf.card := by
      rw [←hSf_coe] <;> simp
    exact_mod_cast h4

  calc ENat.toENNReal (dyadicCoveringNumber δ S)
      = ↑(Sf.image g).card := h1
    _ = ↑Sf.card := by rw [h2]
    _ = ENNReal.ofReal (Sf.card : ℝ) := by
      simp <;> norm_cast
    _ = ENNReal.ofReal (S.ncard : ℝ) := by rw [h_ncard]

/-- For a finite 1D set on the δ-grid, `Nreal δ S` equals the cardinality. -/
lemma grid_separated_nreal_eq_card1d {δ : ℝ} {S : Set ℝ}
    (hδ_pos : 0 < δ) (hS_finite : S.Finite)
    (hS_grid : ∀ x ∈ S, x ∈ productLikeIntegerGrid δ)
    (hS_separated : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → |x - y| ≥ δ) :
    Nreal δ S = ENNReal.ofReal (S.ncard : ℝ) := by
  let Sf := hS_finite.toFinset
  have hSf_coe : (Sf : Set _) = S := hS_finite.coe_toFinset

  -- Map each grid point to its cube index
  let idx : ℝ → ℤ := fun x =>
    if h : x ∈ S then
      Classical.choose (hS_grid x h)
    else 0

  have h_idx_spec : ∀ x ∈ S, x = δ * (idx x : ℝ) := by
    intro x hx
    dsimp only [idx]
    rw [dif_pos hx]
    exact Classical.choose_spec (hS_grid x hx)

  -- idx is injective on S
  have h_inj : Set.InjOn idx S := by
    intro x hx y hy h_eq
    have h1 : x = δ * (idx x : ℝ) := h_idx_spec x hx
    have h2 : y = δ * (idx y : ℝ) := h_idx_spec y hy
    rw [h_eq] at h1
    exact h1.trans h2.symm

  -- realCubeIndexSet δ S is exactly idx '' S
  have h_idx_set : bourgain_projection_theorem.realCubeIndexSet δ S = idx '' S := by
    ext k
    simp only [bourgain_projection_theorem.realCubeIndexSet, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨x, hx⟩
      have hx1 : δ * (k : ℝ) ≤ x := hx.1.1
      have hx2 : x < δ * ((k : ℝ) + 1) := hx.1.2
      have hxS : x ∈ S := hx.2
      have h_x_eq : x = δ * (idx x : ℝ) := h_idx_spec x hxS
      have h_left : δ * (k : ℝ) ≤ δ * (idx x : ℝ) := by
        rw [h_x_eq] at hx1; exact hx1
      have h_right : δ * (idx x : ℝ) < δ * ((k : ℝ) + 1) := by
        rw [h_x_eq] at hx2; exact hx2
      have h5 : (k : ℝ) ≤ (idx x : ℝ) := by
        have h : δ * (k : ℝ) ≤ δ * (idx x : ℝ) := h_left
        nlinarith
      have h6 : (idx x : ℝ) < (k : ℝ) + 1 := by
        have h : δ * (idx x : ℝ) < δ * ((k : ℝ) + 1) := h_right
        nlinarith
      have h7 : k ≤ idx x := by exact_mod_cast h5
      have h8 : idx x < k + 1 := by exact_mod_cast h6
      have h9 : idx x = k := by omega
      exact ⟨x, hxS, h9⟩
    · rintro ⟨x, hxS, rfl⟩
      have h_x_eq : x = δ * (idx x : ℝ) := h_idx_spec x hxS
      have h_goal1 : δ * (idx x : ℝ) ≤ x := by
        exact le_of_eq h_x_eq.symm
      have h_goal2 : x < δ * ((idx x : ℝ) + 1) := by
        have h_pos : 0 < δ := hδ_pos
        have h : (idx x : ℝ) < (idx x : ℝ) + 1 := by linarith
        have h' : δ * (idx x : ℝ) < δ * ((idx x : ℝ) + 1) := mul_lt_mul_of_pos_left h h_pos
        have h_x_eq' : x = δ * (idx x : ℝ) := h_idx_spec x hxS
        calc x = δ * (idx x : ℝ) := h_x_eq'
          _ < δ * ((idx x : ℝ) + 1) := h'
      exact ⟨x, ⟨h_goal1, h_goal2⟩, hxS⟩

  -- Covering number = |realCubeIndexSet|
  have hS_bdd : IsBounded S := Set.Finite.isBounded hS_finite
  have h1 : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy S)) =
      ENat.toENNReal (bourgain_projection_theorem.realCubeIndexSet δ S).encard :=
    bourgain_projection_theorem.realCoveringNumber_eq_card hδ_pos hS_bdd

  have h_main : Nreal δ S = ENat.toENNReal (bourgain_projection_theorem.realCubeIndexSet δ S).encard := by
    simpa [Nreal] using h1

  rw [h_main, h_idx_set]

  -- |idx '' S| = |S| by injectivity
  have h2 : (idx '' S).encard = S.encard := by
    exact h_inj.encard_image

  rw [h2]

  -- Convert to ENNReal.ofReal (S.ncard : ℝ)
  have h_ncard : (S.ncard : ℝ) = (Sf.card : ℝ) := by
    have h4 : S.ncard = ↑Sf.card := by
      rw [←hSf_coe] <;> simp
    exact_mod_cast h4

  calc ENat.toENNReal S.encard
      = ↑Sf.card := by
        have h5 : S.encard = ↑Sf.card := by
          rw [←hSf_coe] <;> simp
        rw [h5] <;> norm_cast
    _ = ENNReal.ofReal (Sf.card : ℝ) := by simp <;> norm_cast
    _ = ENNReal.ofReal (S.ncard : ℝ) := by rw [h_ncard]

end
