import MyLeanRepo.Kakeya.Assouad.WZ1.DensityPigeonhole
import MyLeanRepo.Kakeya.Assouad.WZ1.HypergraphRefinementHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.InducedTripleRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellSelectionSplitStatements

/-!
PDF Proposition 8.9 wide branch: refine the selected heavy cell by Lemma 37
and replace its ambient cell classes by the three active projections of that
same refined graph.
-/

namespace Kakeya.Assouad

theorem wz1_wide_fixed_refined_active :
    WZ1WideFixedRefinedActiveStatement := by
  intro hHeavy hRefine delta epsilon eta parameters F G₁ G₂ H data coarse hscale_le
  classical
  let c : ENNReal := Kakeya.realRpowENN delta eta / (2 ^ 27 : ENNReal)
  let L : ENNReal := wz1WideFixedCellCountLoss
  let product : ENNReal :=
    coarse.coarseF.enncard * coarse.coarseG₁.enncard * coarse.coarseG₂.enncard

  -- Step 1: Select heavy cell
  have h_coarseH_nonempty : coarse.coarseH.Nonempty := coarse.uniform_margin.1
  have h_coarseH_support : ∀ edge ∈ coarse.coarseH,
      edge.1 ∈ coarse.coarseF ∧ edge.2.1 ∈ coarse.coarseG₁ ∧ edge.2.2 ∈ coarse.coarseG₂ :=
    density_vertex_containment coarse.uniform_margin
  rcases hHeavy coarse.coarseF coarse.coarseG₁ coarse.coarseG₂ coarse.coarseH
      h_coarseH_nonempty h_coarseH_support
      coarse.coarseF_bounded coarse.coarseG₁_bounded coarse.coarseG₂_bounded with
    ⟨heavy⟩

  -- Step 2: Apply tripartite refinement inside heavy.inducedH
  have h_inducedH_support : ∀ edge ∈ heavy.inducedH,
      edge.1 ∈ coarse.coarseF ∧ edge.2.1 ∈ coarse.coarseG₁ ∧ edge.2.2 ∈ coarse.coarseG₂ := by
    intro edge hedge
    have h_support := heavy.inducedH_support edge hedge
    exact ⟨heavy.ambientCellF_subset h_support.1,
           heavy.ambientCellG₁_subset h_support.2.1,
           heavy.ambientCellG₂_subset h_support.2.2⟩
  rcases tripartite_refinement_apply
      (hRef := hRefine)
      h_inducedH_support
      heavy.inducedH_nonempty
      (epsilon := (1 / 2 : ENNReal))
      (by norm_num) (by norm_num) with
    ⟨cellH, h_cellH_subset, _h_card, h_uniform_ref⟩

  -- Step 3: Lower bound the refined density
  have hF_enncard_ne_zero : coarse.coarseF.enncard ≠ 0 := by
    simp [DiscreteSet.enncard, Finset.card_ne_zero.mpr coarse.coarseF_nonempty]
  have hG1_enncard_ne_zero : coarse.coarseG₁.enncard ≠ 0 := by
    simp [DiscreteSet.enncard, Finset.card_ne_zero.mpr coarse.coarseG₁_nonempty]
  have hG2_enncard_ne_zero : coarse.coarseG₂.enncard ≠ 0 := by
    simp [DiscreteSet.enncard, Finset.card_ne_zero.mpr coarse.coarseG₂_nonempty]
  have h_product_ne_zero : product ≠ 0 :=
    mul_ne_zero (mul_ne_zero hF_enncard_ne_zero hG1_enncard_ne_zero) hG2_enncard_ne_zero
  have h_L_ne_zero : L ≠ 0 := by
    simp [L, wz1WideFixedCellCountLoss]

  -- From coarse.uniform_margin with I = ∅: c * product ≤ coarseH.card
  have h_density_lower1 : c * product ≤ (coarse.coarseH.card : ENNReal) := by
    rcases coarse.uniform_margin with ⟨_, h_density⟩
    rcases h_density with ⟨h_support, h_fibers⟩
    rcases h_coarseH_nonempty with ⟨edge, hedge⟩
    let encodedEdge := wz1TripleCoordinate edge
    have h_encodedEdge : encodedEdge ∈ wz1EncodeTriples coarse.coarseH :=
      Finset.mem_image_of_mem _ hedge
    have h := h_fibers encodedEdge h_encodedEdge (∅ : Finset (Fin 3))
    have h_univ : (Finset.univ \ (∅ : Finset (Fin 3))) = (Finset.univ : Finset (Fin 3)) := by simp
    have h_univ2 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    have h_product_eq : wz1VertexCardProduct (wz1TripleVertexClasses coarse.coarseF coarse.coarseG₁ coarse.coarseG₂) (Finset.univ \ (∅ : Finset (Fin 3))) = product := by
      rw [h_univ, h_univ2]
      simp [wz1VertexCardProduct, wz1TripleVertexClasses, product, DiscreteSet.enncard, Finset.prod_insert]
      <;> ring
    have h_fiber_eq : (wz1HypergraphFiber (wz1EncodeTriples coarse.coarseH) (∅ : Finset (Fin 3)) encodedEdge) = wz1EncodeTriples coarse.coarseH := by
      ext x
      simp [wz1HypergraphFiber]
    have h_card_eq : (wz1EncodeTriples coarse.coarseH).card = coarse.coarseH.card :=
      wz1HypergraphEncodeTriples_card coarse.coarseH
    rw [h_product_eq, h_fiber_eq, h_card_eq] at h
    exact h

  have h_retention : (coarse.coarseH.card : ENNReal) ≤ L * (heavy.inducedH.card : ENNReal) :=
    heavy.edge_retention

  have h_density_lower2 : c * product ≤ L * (heavy.inducedH.card : ENNReal) :=
    h_density_lower1.trans h_retention

  let d_ref : ENNReal :=
    (1 / 2 : ENNReal) / (2 : ENNReal) ^ 3 *
      ((heavy.inducedH.card : ENNReal) / product)

  have h_const_eq : (1 / 2 : ENNReal) / (2 : ENNReal) ^ 3 = (1 / 16 : ENNReal) := by
    have hpow : (2 : ENNReal) ^ (3 : ℕ) = 8 := by norm_num
    rw [hpow, div_eq_mul_inv]
    rw [show (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ by simp [one_div]]
    rw [show (8 : ENNReal)⁻¹ = (1 / 8 : ENNReal) by simp [one_div]]
    have hmul : (2 : ENNReal)⁻¹ * (1 / 8 : ENNReal) = (16 : ENNReal)⁻¹ := by
      rw [show (1 / 8 : ENNReal) = (8 : ENNReal)⁻¹ by simp [one_div]]
      rw [← ENNReal.mul_inv] <;> norm_num
    rw [hmul]
    simp [one_div]
  have h_d_ref_eq : d_ref = (1 / 16 : ENNReal) * ((heavy.inducedH.card : ENNReal) / product) := by
    dsimp only [d_ref]
    rw [h_const_eq]

  set X : ENNReal := (heavy.inducedH.card : ENNReal) with hX
  have h16_ne_zero : (16 : ENNReal) ≠ 0 := by norm_num
  have h16_ne_top : (16 : ENNReal) ≠ ⊤ := by norm_num
  have h_product_ne_top : product ≠ ⊤ := by
    have h1 : ∀ (s : DiscreteSet 2), s.enncard ≠ ⊤ := by
      intro s
      simp [DiscreteSet.enncard]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (h1 coarse.coarseF) (h1 coarse.coarseG₁)) (h1 coarse.coarseG₂)
  have h_L_ne_top : L ≠ ⊤ := by
    simp [L, wz1WideFixedCellCountLoss]

  -- Step 1: c * product ≤ L * X implies c / L ≤ X / product
  set K1 : ENNReal := L⁻¹ * product⁻¹ with hK1
  have h_step1 : c * product * K1 ≤ L * X * K1 := by gcongr
  have h_left1 : c * product * K1 = c / L := by
    dsimp only [K1]
    have h_cancel : product * product⁻¹ = 1 := ENNReal.mul_inv_cancel h_product_ne_zero h_product_ne_top
    have h_eq : c * product * (L⁻¹ * product⁻¹) = c * L⁻¹ * (product * product⁻¹) := by
      rw [mul_mul_mul_comm c product L⁻¹ product⁻¹]
    rw [h_eq, h_cancel, mul_one, div_eq_mul_inv]
  have h_right1 : L * X * K1 = X / product := by
    dsimp only [K1]
    have h_cancel : L * L⁻¹ = 1 := ENNReal.mul_inv_cancel h_L_ne_zero h_L_ne_top
    have h_eq : L * X * (L⁻¹ * product⁻¹) = (L * L⁻¹) * (X * product⁻¹) := by
      rw [mul_mul_mul_comm L X L⁻¹ product⁻¹]
    rw [h_eq, h_cancel, one_mul, div_eq_mul_inv]
  have h1 : c / L ≤ X / product := by
    rw [h_left1, h_right1] at h_step1
    exact h_step1

  -- Step 2: divide both sides by 16
  have h_div_left : c / (16 * L) = (c / L) / 16 := by
    have h_mul_inv : (16 * L)⁻¹ = (16 : ENNReal)⁻¹ * L⁻¹ := by
      rw [ENNReal.mul_inv] <;> norm_num
    calc
      c / (16 * L)
        = c * (16 * L)⁻¹ := by rw [div_eq_mul_inv]
      _ = c * ((16 : ENNReal)⁻¹ * L⁻¹) := by rw [h_mul_inv]
      _ = (c * L⁻¹) * (16 : ENNReal)⁻¹ := by
        rw [mul_assoc, mul_comm ((16 : ENNReal)⁻¹) L⁻¹, ←mul_assoc]
      _ = (c / L) / 16 := by
        simp [div_eq_mul_inv]
  have h_div_right : (1 / 16 : ENNReal) * (X / product) = (X / product) / 16 := by
    calc
      (1 / 16 : ENNReal) * (X / product)
        = (16 : ENNReal)⁻¹ * (X * product⁻¹) := by
          simp [div_eq_mul_inv]
      _ = (X * product⁻¹) * (16 : ENNReal)⁻¹ := by rw [mul_comm]
      _ = (X / product) / 16 := by
        simp [div_eq_mul_inv]
  have h_goal : c / (16 * L) ≤ d_ref := by
    rw [h_d_ref_eq, h_div_left, h_div_right]
    gcongr

  have h_uniform_target : WZ1UniformTripleDensity (c / (16 * L))
      coarse.coarseF coarse.coarseG₁ coarse.coarseG₂ cellH :=
    uniform_triple_density_mono h_uniform_ref h_goal

  -- Step 4: Active projections
  let cellF := wz1ActiveTripleProjection cellH 0
  let cellG₁ := wz1ActiveTripleProjection cellH 1
  let cellG₂ := wz1ActiveTripleProjection cellH 2

  have h_uniform_active : WZ1UniformTripleDensity (c / (16 * L))
      cellF cellG₁ cellG₂ cellH :=
    uniform_density_on_active_projections h_uniform_target

  have h_cellF_retention : (c / (16 * L)) * coarse.coarseF.enncard ≤ cellF.enncard :=
    active_triple_projection_card_lower h_uniform_target 0
  have h_cellG₁_retention : (c / (16 * L)) * coarse.coarseG₁.enncard ≤ cellG₁.enncard :=
    active_triple_projection_card_lower h_uniform_target 1
  have h_cellG₂_retention : (c / (16 * L)) * coarse.coarseG₂.enncard ≤ cellG₂.enncard :=
    active_triple_projection_card_lower h_uniform_target 2

  -- Step 5: Remaining fields
  have h_cellF_nonempty : cellF.Nonempty := active_triple_projection_nonempty h_uniform_target 0
  have h_cellG₁_nonempty : cellG₁.Nonempty := active_triple_projection_nonempty h_uniform_target 1
  have h_cellG₂_nonempty : cellG₂.Nonempty := active_triple_projection_nonempty h_uniform_target 2
  have h_cellH_nonempty : cellH.Nonempty := h_uniform_target.1

  have h_cellF_subset_ambient : cellF ⊆ heavy.ambientCellF := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with ⟨edge, hedge, rfl⟩
    have h_edge_in_inducedH : edge ∈ heavy.inducedH := h_cellH_subset hedge
    exact (heavy.inducedH_support edge h_edge_in_inducedH).1
  have h_cellG₁_subset_ambient : cellG₁ ⊆ heavy.ambientCellG₁ := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with ⟨edge, hedge, rfl⟩
    have h_edge_in_inducedH : edge ∈ heavy.inducedH := h_cellH_subset hedge
    exact (heavy.inducedH_support edge h_edge_in_inducedH).2.1
  have h_cellG₂_subset_ambient : cellG₂ ⊆ heavy.ambientCellG₂ := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with ⟨edge, hedge, rfl⟩
    have h_edge_in_inducedH : edge ∈ heavy.inducedH := h_cellH_subset hedge
    exact (heavy.inducedH_support edge h_edge_in_inducedH).2.2

  have h_cellH_support : ∀ edge ∈ cellH,
      edge.1 ∈ cellF ∧ edge.2.1 ∈ cellG₁ ∧ edge.2.2 ∈ cellG₂ := by
    intro edge hedge
    exact ⟨Finset.mem_image.mpr ⟨edge, hedge, rfl⟩,
           Finset.mem_image.mpr ⟨edge, hedge, rfl⟩,
           Finset.mem_image.mpr ⟨edge, hedge, rfl⟩⟩

  have h_cellF_separated : cellF.IsDeltaSeparated coarse.scale := by
    intro x hx y hy hne
    have hxF : x ∈ coarse.coarseF := heavy.ambientCellF_subset (h_cellF_subset_ambient hx)
    have hyF : y ∈ coarse.coarseF := heavy.ambientCellF_subset (h_cellF_subset_ambient hy)
    exact coarse.coarseF_separated hxF hyF hne
  have h_cellG₁_separated : cellG₁.IsDeltaSeparated coarse.scale := by
    intro x hx y hy hne
    have hxG : x ∈ coarse.coarseG₁ := heavy.ambientCellG₁_subset (h_cellG₁_subset_ambient hx)
    have hyG : y ∈ coarse.coarseG₁ := heavy.ambientCellG₁_subset (h_cellG₁_subset_ambient hy)
    exact coarse.coarseG₁_separated hxG hyG hne
  have h_cellG₂_separated : cellG₂.IsDeltaSeparated coarse.scale := by
    intro x hx y hy hne
    have hxG : x ∈ coarse.coarseG₂ := heavy.ambientCellG₂_subset (h_cellG₂_subset_ambient hx)
    have hyG : y ∈ coarse.coarseG₂ := heavy.ambientCellG₂_subset (h_cellG₂_subset_ambient hy)
    exact coarse.coarseG₂_separated hxG hyG hne

  have h_cellH_subset_coarseH : cellH ⊆ coarse.coarseH := by
    calc cellH ⊆ heavy.inducedH := h_cellH_subset
         _ ⊆ coarse.coarseH := heavy.inducedH_subset

  have h_quantitative_separation : ∀ edge ∈ cellH,
      1 / 3 ≤ dist edge.1 0 ∧ 2 / 5 ≤ dist edge.2.1 edge.2.2 := by
    intro edge hedge
    exact quantitative_separation_from_source hscale_le (h_cellH_subset_coarseH hedge)

  exact ⟨heavy, cellH, cellF, cellG₁, cellG₂,
    h_cellH_subset, rfl, rfl, rfl,
    h_cellF_nonempty, h_cellG₁_nonempty, h_cellG₂_nonempty, h_cellH_nonempty,
    h_cellF_subset_ambient, h_cellG₁_subset_ambient, h_cellG₂_subset_ambient,
    h_cellH_support,
    h_cellF_separated, h_cellG₁_separated, h_cellG₂_separated,
    h_uniform_active,
    h_cellF_retention, h_cellG₁_retention, h_cellG₂_retention,
    h_quantitative_separation⟩

end Kakeya.Assouad
