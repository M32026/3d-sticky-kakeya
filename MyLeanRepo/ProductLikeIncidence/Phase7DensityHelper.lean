module

/-
# Per-Y Density Helper for Phase7DoubleCountingHelper

Standalone extraction of the per-y density bound to reduce type inference
overhead in the main double counting lemma.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.Phase7Budgets
public import MyLeanRepo.ProductLikeSetBasics
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set ENNReal Bornology MeasureTheory Classical


namespace ProductLikeIncidence.ProductReduction

/-- Standalone per-y density bound for the double counting helper. -/
lemma phase7_per_y_density
    {δ : ℝ} (hδ_pos : 0 < δ)
    {F_graph : Set (EuclideanSpace ℝ (Fin 2))}
    (hF_graph_finite : F_graph.Finite)
    (hF_graph_grid : ∀ p ∈ F_graph, ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ))
    {A : Finset (EuclideanSpace ℝ (Fin 2))}
    (hA_eq : (A : Set _) = F_graph)
    {T : ℝ → Finset (EuclideanSpace ℝ (Fin 2))}
    (y : ℝ)
    (c_mult_dir c_proj : ℝ)
    (hc_mult_dir_pos : 0 < c_mult_dir)
    (hc_proj_pos : 0 < c_proj)
    (hT_density : ((T y).card : ℝ) ≥ (c_mult_dir / 2) * (A.card : ℝ))
    {B1 B2 : Set ℝ}
    (hF_graph_covering : ENat.toENNReal (dyadicCoveringNumber δ F_graph) ≥
        ENNReal.ofReal (2 / c_mult_dir) * ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2)
    {S_pre : ℝ → Set ℝ}
    (x : ℝ → ℝ)
    (hT_def : (T y : Set _) = (A : Set _) ∩ {p : EuclideanSpace ℝ (Fin 2) | p 0 * x y + p 1 ∈ S_pre y}) :
    ENat.toENNReal (dyadicCoveringNumber δ
      (F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y})) ≥
    ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2 := by
  let G_y : Set (EuclideanSpace ℝ (Fin 2)) := (T y : Set _)
  let A_set : Set (EuclideanSpace ℝ (Fin 2)) := ↑A
  have hT_sub_A : (T y : Set _) ⊆ A_set := by
    rw [hT_def]
    exact inter_subset_left
  have hG_sub_F : G_y ⊆ F_graph := by
    intro p hp
    have hpinA : p ∈ A_set := hT_sub_A hp
    rw [← hA_eq] <;> exact hpinA
  have hG_proj : ∀ p ∈ G_y, p 0 * x y + p 1 ∈ S_pre y := by
    intro p hp
    have hpinT_set : p ∈ (T y : Set _) := hp
    rw [hT_def] at hpinT_set
    exact hpinT_set.2
  have hG_finite : G_y.Finite := Set.Finite.subset hF_graph_finite hG_sub_F
  have hG_grid : ∀ p ∈ G_y, ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ) := by
    intro p hp i
    exact hF_graph_grid p (hG_sub_F hp) i
  have hG_cover_eq : dyadicCoveringNumber δ G_y = G_y.encard :=
    grid_set_coveringNumber_eq_encard hδ_pos hG_grid
  have hG_card_ennreal : ENat.toENNReal G_y.encard = (↑(T y).card : ENNReal) := by
    have h_eq : G_y = (T y : Set _) := by rfl
    rw [h_eq, Set.encard_coe_eq_coe_finsetCard (T y)] <;> norm_cast
  have h_density_ennreal : (↑(T y).card : ENNReal) ≥
      ENNReal.ofReal (c_mult_dir / 2) * (↑A.card : ENNReal) := by
    have h : ENNReal.ofReal (↑(T y).card : ℝ) ≥
        ENNReal.ofReal ((c_mult_dir / 2) * (A.card : ℝ)) :=
      ENNReal.ofReal_le_ofReal hT_density
    have h2 : ENNReal.ofReal (↑(T y).card : ℝ) = (↑(T y).card : ENNReal) := by simp
    have h3 : ENNReal.ofReal ((c_mult_dir / 2) * (A.card : ℝ)) =
        ENNReal.ofReal (c_mult_dir / 2) * (↑A.card : ENNReal) := by
      rw [ENNReal.ofReal_mul (by positivity)] <;> simp
    rw [h2, h3] at h <;> exact h
  have hF_cover_eq : dyadicCoveringNumber δ F_graph = F_graph.encard :=
    grid_set_coveringNumber_eq_encard hδ_pos hF_graph_grid
  have hF_encard : ENat.toENNReal F_graph.encard = (↑A.card : ENNReal) := by
    have h1 : F_graph.encard = ↑A.card := by
      rw [← hA_eq] <;> exact Set.encard_coe_eq_coe_finsetCard A
    rw [h1] <;> norm_cast
  have hcov' : ENat.toENNReal F_graph.encard ≥
      ENNReal.ofReal (2 / c_mult_dir) * ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2 := by
    have h : ENat.toENNReal (dyadicCoveringNumber δ F_graph) ≥ _ := hF_graph_covering
    rwa [hF_cover_eq] at h
  have h_main_density : ENNReal.ofReal (c_mult_dir / 2) * ENat.toENNReal F_graph.encard ≥
      ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2 := by
    have h4 : ENNReal.ofReal (c_mult_dir / 2) * ENat.toENNReal F_graph.encard ≥
        ENNReal.ofReal (c_mult_dir / 2) *
        (ENNReal.ofReal (2 / c_mult_dir) * ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2) := by
      exact mul_le_mul_left' hcov' _
    have h6 : ENNReal.ofReal (c_mult_dir / 2) * ENNReal.ofReal (2 / c_mult_dir) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have h7 : (c_mult_dir / 2) * (2 / c_mult_dir) = 1 := by
        field_simp [hc_mult_dir_pos.ne'] <;> ring
      rw [h7] <;> simp
    have h5 : ENNReal.ofReal (c_mult_dir / 2) *
        (ENNReal.ofReal (2 / c_mult_dir) * ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2) =
        ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2 := by
      have h51 : ENNReal.ofReal (c_mult_dir / 2) *
          (ENNReal.ofReal (2 / c_mult_dir) * ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2) =
          (ENNReal.ofReal (c_mult_dir / 2) * ENNReal.ofReal (2 / c_mult_dir)) *
          (ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2) := by
        simp [mul_assoc]
        <;> rfl
      rw [h51, h6, one_mul]
    rw [h5] at h4 <;> exact h4
  have hG_y_sub' : G_y ⊆ F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y} := by
    intro p hp
    have hpinF : p ∈ F_graph := hG_sub_F hp
    have hproj : p 0 * x y + p 1 ∈ S_pre y := hG_proj p hp
    exact ⟨hpinF, hproj⟩
  have hmono : ENat.toENNReal (dyadicCoveringNumber δ G_y) ≤
      ENat.toENNReal (dyadicCoveringNumber δ (F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y})) := by
    have h1 : dyadicCubesMeeting δ G_y ⊆ dyadicCubesMeeting δ (F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y}) := by
      intro Q hQ
      have hQ1 : Q ∈ dyadicCubes 2 δ := hQ.1
      have hQ2 : (Q ∩ G_y).Nonempty := hQ.2
      have hQ3 : (Q ∩ (F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y})).Nonempty := by
        exact hQ2.mono (Set.inter_subset_inter_right _ hG_y_sub')
      exact ⟨hQ1, hQ3⟩
    exact ENat.toENNReal_mono (Set.encard_mono h1)
  have hG_y_dense : ENat.toENNReal (dyadicCoveringNumber δ G_y) ≥
      ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2 := by
    calc ENat.toENNReal (dyadicCoveringNumber δ G_y)
      = ENat.toENNReal G_y.encard := by rw [hG_cover_eq]
    _ = (↑(T y).card : ENNReal) := hG_card_ennreal
    _ ≥ ENNReal.ofReal (c_mult_dir / 2) * (↑A.card : ENNReal) := h_density_ennreal
    _ = ENNReal.ofReal (c_mult_dir / 2) * ENat.toENNReal F_graph.encard := by rw [hF_encard]
    _ ≥ ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2 := h_main_density
  exact le_trans hG_y_dense hmono

end ProductLikeIncidence.ProductReduction
