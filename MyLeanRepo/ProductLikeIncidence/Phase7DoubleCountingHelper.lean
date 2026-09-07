module

/-
# Double Counting Helper for Phase7FullIntegrationV2

Extracts Step 1 (double counting → Θ_bad) from the main theorem
to reduce per-elaboration memory.

Returns Θ_bad with its mass bound and per-y dense subgraph density.
Does NOT include four-sector pigeonhole — that stays in V2.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.Phase7Budgets
public import MyLeanRepo.ProductLikeIncidence.Phase7DensityHelper
public import MyLeanRepo.ProductLikeIncidence.Phase7MassBoundHelper
public import MyLeanRepo.ProductLikeSetBasics
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set ENNReal Bornology MeasureTheory Classical


namespace ProductLikeIncidence.ProductReduction



/-- Double counting helper: extract Θ_bad with mass and per-y density.

Given the incidence graph F_graph, point multiplicity h_point_mult, and
Frostman measure ν, produces Θ_bad ⊆ Y with:
- ν Θ_bad ≥ δ^ε_mass
- For each y ∈ Θ_bad, the dyadic covering number of the incidence fiber
  F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y} is at least c_proj * Nδ(B1) * Nδ(B2). -/
lemma phase7_double_counting_helper
    {δ ε_mass : ℝ}
    {Y : Set ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hδ_pos : 0 < δ)
    (hε_mass_pos : 0 < ε_mass)
    (hY_sub_unit : Y ⊆ Set.Icc 0 1)
    (Yfin : Finset ℝ)
    (hYfin_eq : (Yfin : Set ℝ) = Y)
    (hY_mass : ν Y ≥ ENNReal.ofReal (δ ^ ε_mass))
    {F_graph : Set (EuclideanSpace ℝ (Fin 2))}
    (hF_graph_finite : F_graph.Finite)
    (hF_graph_grid : ∀ p ∈ F_graph, ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ))
    {B1 B2 : Set ℝ}
    {S_pre : ℝ → Set ℝ}
    (x : ℝ → ℝ)
    (c_mult_dir : ℝ)
    (hc_mult_dir_pos : 0 < c_mult_dir)
    (hc_mult_dir_le_one : c_mult_dir ≤ 1)
    (h_point_mult : ∀ p ∈ F_graph,
      ({y ∈ Yfin | p 0 * x y + p 1 ∈ S_pre y}.card : ℝ) ≥ c_mult_dir * Yfin.card)
    (hν_uniform : ∀ y ∈ Y, ν {y} = ENNReal.ofReal (1 / (Y.ncard : ℝ)))
    (h_mass_budget : δ ^ ε_mass ≤ c_mult_dir / 2)
    (c_proj : ℝ)
    (hc_proj_pos : 0 < c_proj)
    (hF_graph_covering : ENat.toENNReal (dyadicCoveringNumber δ F_graph) ≥
      ENNReal.ofReal (2 / c_mult_dir) * ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2) :
    ∃ (Θ_bad : Set ℝ),
      Θ_bad ⊆ Y ∧
      ν Θ_bad ≥ ENNReal.ofReal (δ ^ ε_mass) ∧
      (∀ y ∈ Θ_bad,
        ENat.toENNReal (dyadicCoveringNumber δ
          (F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y})) ≥
        ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2) := by
  have hY_nonempty : Y.Nonempty := by
    by_contra h
    have hY_empty : Y = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h
    rw [hY_empty] at hY_mass
    have h_contra : (0 : ENNReal) ≥ ENNReal.ofReal (δ ^ ε_mass) := by simpa using hY_mass
    have h_pos : (0 : ENNReal) < ENNReal.ofReal (δ ^ ε_mass) := by positivity
    exact False.elim (not_le.mpr h_pos h_contra)

  let A : Finset (EuclideanSpace ℝ (Fin 2)) := hF_graph_finite.toFinset
  have hA_eq : (A : Set (EuclideanSpace ℝ (Fin 2))) = F_graph := hF_graph_finite.coe_toFinset
  let T : ℝ → Finset (EuclideanSpace ℝ (Fin 2)) := fun y =>
    A.filter (fun p => p 0 * x y + p 1 ∈ S_pre y)

  have hT_sub_A : ∀ y ∈ Yfin, T y ⊆ A := fun y _ => Finset.filter_subset _ _

  let P : EuclideanSpace ℝ (Fin 2) → ℝ → Prop := fun p y =>
    p ∈ A ∧ p 0 * x y + p 1 ∈ S_pre y

  have hP : ∀ (p : EuclideanSpace ℝ (Fin 2)) (y : ℝ), P p y ↔ p ∈ T y := by
    intro p y
    simp [P, T, Finset.mem_filter] <;> tauto

  have h_mult : ∀ p ∈ A, (↑(∑ y ∈ Yfin, (if P p y then 1 else 0)) : ℝ) ≥ c_mult_dir * ↑Yfin.card := by
    intro p hp
    have h_p_in_F : p ∈ F_graph := by rw [← hA_eq] <;> exact hp
    have hP_eq : ∀ y, P p y ↔ p 0 * x y + p 1 ∈ S_pre y := by
      intro y
      simp [P, hp] <;> tauto
    have h_filter_eq : Yfin.filter (fun y => P p y) =
        Yfin.filter (fun y => p 0 * x y + p 1 ∈ S_pre y) := by
      apply Finset.filter_congr
      intro y _
      exact hP_eq y
    have h_card_sum : (Yfin.filter (fun y => P p y)).card = ∑ y ∈ Yfin, (if P p y then 1 else 0) := by
      rw [Finset.card_filter] <;> rfl
    have h_goal : (↑(∑ y ∈ Yfin, (if P p y then 1 else 0)) : ℝ) =
        ({y ∈ Yfin | p 0 * x y + p 1 ∈ S_pre y}.card : ℝ) := by
      calc
        (↑(∑ y ∈ Yfin, (if P p y then 1 else 0)) : ℝ)
          = ↑(Yfin.filter (fun y => P p y)).card := by exact_mod_cast h_card_sum.symm
        _ = ↑(Yfin.filter (fun y => p 0 * x y + p 1 ∈ S_pre y)).card := by
          rw [h_filter_eq]
        _ = ({y ∈ Yfin | p 0 * x y + p 1 ∈ S_pre y}.card : ℝ) := by rfl
    rw [h_goal]
    exact h_point_mult p h_p_in_F

  rcases double_counting_good_directions_subset Yfin A T P hP c_mult_dir hc_mult_dir_pos hc_mult_dir_le_one hT_sub_A h_mult
    with ⟨Θ_bad_fin, hΘ_sub, hΘ_card, h_density⟩

  let Θ_bad : Set ℝ := (Θ_bad_fin : Set ℝ)
  have hΘ_bad_sub_Y : Θ_bad ⊆ Y := by
    intro y hy
    have h1 : y ∈ Θ_bad_fin := by exact_mod_cast hy
    have h2 : y ∈ Yfin := hΘ_sub h1
    have h3 : y ∈ (Yfin : Set ℝ) := h2
    have h4 : y ∈ Y := by simpa [hYfin_eq] using h3
    exact h4

  have h_Θbad_mass : ν Θ_bad ≥ ENNReal.ofReal (δ ^ ε_mass) :=
    phase7_mass_bound hε_mass_pos Yfin hYfin_eq hY_nonempty c_mult_dir hc_mult_dir_pos
      Θ_bad_fin hΘ_sub hΘ_card hν_uniform h_mass_budget

  have hG_density : ∀ y ∈ Θ_bad,
      ENat.toENNReal (dyadicCoveringNumber δ
        (F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y})) ≥
      ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2 := by
    intro y hy
    have hy_fin : y ∈ Θ_bad_fin := by exact_mod_cast hy
    have hT_density : ((T y).card : ℝ) ≥ (c_mult_dir / 2) * (A.card : ℝ) := h_density y hy_fin
    have hT_def : (T y : Set _) = (A : Set _) ∩ {p : EuclideanSpace ℝ (Fin 2) | p 0 * x y + p 1 ∈ S_pre y} := by
      ext p
      simp [T, Finset.mem_filter, Set.mem_inter_iff]
      <;> tauto
    exact phase7_per_y_density hδ_pos hF_graph_finite hF_graph_grid hA_eq y c_mult_dir c_proj
      hc_mult_dir_pos hc_proj_pos hT_density hF_graph_covering x hT_def

  exact ⟨Θ_bad, hΘ_bad_sub_Y, h_Θbad_mass, hG_density⟩

end ProductLikeIncidence.ProductReduction
