import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellSelectionSplitStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.GridPigeonhole

/-!
PDF Proposition 8.9 wide branch: select one heavy absolute `1/100`
grid-cell triple from the bounded coarse graph.

The output must retain actual subsets of the input graph and classes.  The
edge retention is paid by the fixed absolute constant
`wz1WideFixedCellCountLoss`; do not replace the graph by a singleton or
reselect unrelated vertex witnesses.
-/

namespace Kakeya.Assouad

theorem wz1_wide_fixed_heavy_cell :
    WZ1WideFixedHeavyCellStatement := by
  intro F G₁ G₂ H hH_nonempty h_support hF_ball hG₁_ball hG₂_ball
  set r : ℝ := 1 / 100 with hr_def
  have hr_pos : 0 < r := by norm_num
  have hr_le3 : r ≤ 3 := by norm_num

  set centersF := F.image (gridCenter r) with hcF_def
  set centersG₁ := G₁.image (gridCenter r) with hcG₁_def
  set centersG₂ := G₂.image (gridCenter r) with hcG₂_def
  set cells : Finset (Point2 × Point2 × Point2) :=
    centersF.product (centersG₁.product centersG₂) with hcells_def
  set f : (Point2 × Point2 × Point2) → (Point2 × Point2 × Point2) := fun edge =>
    (gridCenter r edge.1, gridCenter r edge.2.1, gridCenter r edge.2.2) with hf_def

  -- Bound the number of grid centers per class
  have hcardF : (centersF.card : ℝ) ≤ (6 / r + 2) ^ 2 :=
    grid_image_card_bound_radius3 hF_ball hr_pos hr_le3
  have hcardG₁ : (centersG₁.card : ℝ) ≤ (6 / r + 2) ^ 2 :=
    grid_image_card_bound_radius3 hG₁_ball hr_pos hr_le3
  have hcardG₂ : (centersG₂.card : ℝ) ≤ (6 / r + 2) ^ 2 :=
    grid_image_card_bound_radius3 hG₂_ball hr_pos hr_le3

  have h6r : (6 / r + 2 : ℝ) = 602 := by
    rw [hr_def] <;> norm_num

  -- Bound total number of cell triples
  have hcard_cells : (cells.card : ℝ) ≤ (602 : ℝ) ^ 6 := by
    have h1 : (cells.card : ℝ) = (centersF.card : ℝ) * (centersG₁.card : ℝ) * (centersG₂.card : ℝ) := by
      simp [hcells_def, Finset.card_product] <;> ring
    rw [h1]
    rw [h6r] at hcardF hcardG₁ hcardG₂
    have h2 : (centersF.card : ℝ) * (centersG₁.card : ℝ) * (centersG₂.card : ℝ) ≤
        (602 : ℝ) ^ 2 * (602 : ℝ) ^ 2 * (602 : ℝ) ^ 2 := by gcongr <;> positivity
    have h3 : (602 : ℝ) ^ 2 * (602 : ℝ) ^ 2 * (602 : ℝ) ^ 2 = (602 : ℝ) ^ 6 := by ring
    rw [h3] at h2
    exact h2

  have h602_le : (602 : ℝ) ^ 6 ≤ (10 : ℝ) ^ 18 := by
    have h4 : (602 : ℝ) ≤ 1000 := by norm_num
    have h5 : (602 : ℝ) ^ 6 ≤ (1000 : ℝ) ^ 6 := by gcongr
    have h6 : (1000 : ℝ) ^ 6 = (10 : ℝ) ^ 18 := by norm_num
    linarith

  -- Every edge maps to a cell
  have hmaps : ∀ edge ∈ H, f edge ∈ cells := by
    intro edge hedge
    have hs := h_support edge hedge
    have hF : gridCenter r edge.1 ∈ centersF :=
      Finset.mem_image.mpr ⟨edge.1, hs.1, rfl⟩
    have hG₁ : gridCenter r edge.2.1 ∈ centersG₁ :=
      Finset.mem_image.mpr ⟨edge.2.1, hs.2.1, rfl⟩
    have hG₂ : gridCenter r edge.2.2 ∈ centersG₂ :=
      Finset.mem_image.mpr ⟨edge.2.2, hs.2.2, rfl⟩
    have hinner : (gridCenter r edge.2.1, gridCenter r edge.2.2) ∈ centersG₁.product centersG₂ :=
      Finset.mem_product.mpr ⟨hG₁, hG₂⟩
    have h : (gridCenter r edge.1, (gridCenter r edge.2.1, gridCenter r edge.2.2)) ∈ cells :=
      Finset.mem_product.mpr ⟨hF, hinner⟩
    simpa [hf_def] using h

  -- Cells is nonempty
  have hcells_ne : cells.Nonempty := by
    rcases hH_nonempty with ⟨edge, hedge⟩
    exact ⟨f edge, hmaps edge hedge⟩

  -- Apply pigeonhole
  rcases finset_pigeonhole hmaps hcells_ne with ⟨⟨cF, cG₁, cG₂⟩, hct_in, hbound⟩

  let inducedH : Finset (Point2 × Point2 × Point2) :=
    H.filter (fun edge =>
      gridCenter r edge.1 = cF ∧
      gridCenter r edge.2.1 = cG₁ ∧
      gridCenter r edge.2.2 = cG₂)

  let ambientCellF : DiscreteSet 2 :=
    F.filter (fun point => gridCenter r point = cF)
  let ambientCellG₁ : DiscreteSet 2 :=
    G₁.filter (fun point => gridCenter r point = cG₁)
  let ambientCellG₂ : DiscreteSet 2 :=
    G₂.filter (fun point => gridCenter r point = cG₂)

  -- The filter from pigeonhole equals inducedH
  have hfilter_eq : H.filter (fun edge => f edge = (cF, cG₁, cG₂)) = inducedH := by
    ext edge
    simp only [Finset.mem_filter, hf_def, inducedH]
    constructor
    · rintro ⟨hh, h_eq⟩
      have h10 : gridCenter r edge.1 = cF ∧ gridCenter r edge.2.1 = cG₁ ∧ gridCenter r edge.2.2 = cG₂ := by
        simpa [Prod.ext_iff] using h_eq
      exact ⟨hh, h10⟩
    · rintro ⟨hh, h10⟩
      have h_eq : f edge = (cF, cG₁, cG₂) := by
        simp [hf_def, h10.1, h10.2.1, h10.2.2]
      exact ⟨hh, h_eq⟩

  -- Retention bound in ℝ
  have h_retention_real : (H.card : ℝ) ≤ (10 : ℝ)^18 * (inducedH.card : ℝ) := by
    rw [hfilter_eq] at hbound
    have h7 : (H.card : ℝ) ≤ (cells.card : ℝ) * (inducedH.card : ℝ) := hbound
    have h8 : (cells.card : ℝ) * (inducedH.card : ℝ) ≤ (602 : ℝ)^6 * (inducedH.card : ℝ) := by
      gcongr <;> positivity
    have h9 : (602 : ℝ)^6 * (inducedH.card : ℝ) ≤ (10 : ℝ)^18 * (inducedH.card : ℝ) := by
      gcongr <;> positivity
    exact h7.trans (h8.trans h9)

  -- inducedH is nonempty (use a copy of h_retention_real to avoid modifying it)
  have hinducedH_nonempty : inducedH.Nonempty := by
    by_contra h
    have h10 : inducedH = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using h
    have h11 : (inducedH.card : ℝ) = 0 := by
      rw [h10] <;> simp
    have h12 : (H.card : ℝ) ≤ (10 : ℝ)^18 * (inducedH.card : ℝ) := h_retention_real
    rw [h11] at h12
    have h13 : (H.card : ℝ) ≤ 0 := by
      have h14 : (10 : ℝ)^18 * (0 : ℝ) = 0 := by ring
      rw [h14] at h12
      exact h12
    have h15 : 0 < H.card := Finset.card_pos.mpr hH_nonempty
    have h16 : (H.card : ℝ) > 0 := by exact_mod_cast h15
    linarith

  -- Build the record fields
  have hinducedH_subset : inducedH ⊆ H := Finset.filter_subset _ _

  have hinducedH_support : ∀ edge ∈ inducedH,
      edge.1 ∈ ambientCellF ∧ edge.2.1 ∈ ambientCellG₁ ∧ edge.2.2 ∈ ambientCellG₂ := by
    intro edge hedge
    have h10 : gridCenter r edge.1 = cF ∧ gridCenter r edge.2.1 = cG₁ ∧ gridCenter r edge.2.2 = cG₂ :=
      (Finset.mem_filter.mp hedge).2
    have hs := h_support edge (Finset.mem_filter.mp hedge).1
    exact ⟨by
      simp only [ambientCellF, Finset.mem_filter]
      exact ⟨hs.1, h10.1⟩, by
      simp only [ambientCellG₁, Finset.mem_filter]
      exact ⟨hs.2.1, h10.2.1⟩, by
      simp only [ambientCellG₂, Finset.mem_filter]
      exact ⟨hs.2.2, h10.2.2⟩⟩

  have hambientCellF_nonempty : ambientCellF.Nonempty := by
    rcases hinducedH_nonempty with ⟨edge, hedge⟩
    have h10 := (Finset.mem_filter.mp hedge).2
    have hs := h_support edge (Finset.mem_filter.mp hedge).1
    exact ⟨edge.1, by
      simp only [ambientCellF, Finset.mem_filter]
      exact ⟨hs.1, h10.1⟩⟩

  have hambientCellG₁_nonempty : ambientCellG₁.Nonempty := by
    rcases hinducedH_nonempty with ⟨edge, hedge⟩
    have h10 := (Finset.mem_filter.mp hedge).2
    have hs := h_support edge (Finset.mem_filter.mp hedge).1
    exact ⟨edge.2.1, by
      simp only [ambientCellG₁, Finset.mem_filter]
      exact ⟨hs.2.1, h10.2.1⟩⟩

  have hambientCellG₂_nonempty : ambientCellG₂.Nonempty := by
    rcases hinducedH_nonempty with ⟨edge, hedge⟩
    have h10 := (Finset.mem_filter.mp hedge).2
    have hs := h_support edge (Finset.mem_filter.mp hedge).1
    exact ⟨edge.2.2, by
      simp only [ambientCellG₂, Finset.mem_filter]
      exact ⟨hs.2.2, h10.2.2⟩⟩

  have hambientCellF_subset : ambientCellF ⊆ F := Finset.filter_subset _ _
  have hambientCellG₁_subset : ambientCellG₁ ⊆ G₁ := Finset.filter_subset _ _
  have hambientCellG₂_subset : ambientCellG₂ ⊆ G₂ := Finset.filter_subset _ _

  have hambientCellF_ball : ∀ point ∈ ambientCellF, dist point cF ≤ 1 / 100 := by
    intro point hpoint
    have h10 : gridCenter r point = cF := (Finset.mem_filter.mp hpoint).2
    have h11 : dist point (gridCenter r point) ≤ r := gridCenter_rho_close r hr_pos point
    rw [h10] at h11
    rw [hr_def] at h11
    exact h11

  have hambientCellG₁_ball : ∀ point ∈ ambientCellG₁, dist point cG₁ ≤ 1 / 100 := by
    intro point hpoint
    have h10 : gridCenter r point = cG₁ := (Finset.mem_filter.mp hpoint).2
    have h11 : dist point (gridCenter r point) ≤ r := gridCenter_rho_close r hr_pos point
    rw [h10] at h11
    rw [hr_def] at h11
    exact h11

  have hambientCellG₂_ball : ∀ point ∈ ambientCellG₂, dist point cG₂ ≤ 1 / 100 := by
    intro point hpoint
    have h10 : gridCenter r point = cG₂ := (Finset.mem_filter.mp hpoint).2
    have h11 : dist point (gridCenter r point) ≤ r := gridCenter_rho_close r hr_pos point
    rw [h10] at h11
    rw [hr_def] at h11
    exact h11

  have hedge_retention : (H.card : ENNReal) ≤ wz1WideFixedCellCountLoss * (inducedH.card : ENNReal) := by
    have h12 : (H.card : ENNReal) ≤ (10 : ENNReal)^18 * (inducedH.card : ENNReal) := by
      exact_mod_cast h_retention_real
    simpa [wz1WideFixedCellCountLoss] using h12

  exact ⟨{
    centerF := cF,
    centerG₁ := cG₁,
    centerG₂ := cG₂,
    ambientCellF := ambientCellF,
    ambientCellG₁ := ambientCellG₁,
    ambientCellG₂ := ambientCellG₂,
    inducedH := inducedH,
    ambientCellF_eq := by rfl,
    ambientCellG₁_eq := by rfl,
    ambientCellG₂_eq := by rfl,
    inducedH_eq := by rfl,
    inducedH_nonempty := hinducedH_nonempty,
    inducedH_subset := hinducedH_subset,
    inducedH_support := hinducedH_support,
    ambientCellF_nonempty := hambientCellF_nonempty,
    ambientCellG₁_nonempty := hambientCellG₁_nonempty,
    ambientCellG₂_nonempty := hambientCellG₂_nonempty,
    ambientCellF_subset := hambientCellF_subset,
    ambientCellG₁_subset := hambientCellG₁_subset,
    ambientCellG₂_subset := hambientCellG₂_subset,
    ambientCellF_ball := hambientCellF_ball,
    ambientCellG₁_ball := hambientCellG₁_ball,
    ambientCellG₂_ball := hambientCellG₂_ball,
    edge_retention := hedge_retention
  }⟩

end Kakeya.Assouad
