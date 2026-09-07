import MyLeanRepo.Kakeya.Assouad.WZ1.DensityBijection
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49ActiveFiberSeparatedSelection
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulAffineTransport
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulFixedGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionDichotomyFromLeaves

/-!
# Target: faithful fixed-viewpoint affine preparation for PDF Lemma 8.13

The statement fixes the actual viewpoint and actual separated source before
any refinement, then requires the literal half-scaled affine image and its
source-edge witnesses.
-/

namespace Kakeya.Assouad

open scoped ENNReal

theorem wz1_lemma8_13_faithful_viewpoint_affine :
    WZ1Lemma8_13FaithfulViewpointAffineStatement := by
  intro epsilon hepsilon hepsilonOne
  rcases wz1Lemma8_13_faithful_parameter_window epsilon hepsilon hepsilonOne with
    ⟨delta₀, hdelta₀_pos, hdelta₀_one, hwindow⟩
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta hdelta hdeltaSmall input
  let eta := wz1Lemma8_13FaithfulEta epsilon
  have heta_pos : 0 < eta := by
    dsimp only [eta, wz1Lemma8_13FaithfulEta]
    positivity
  rcases hwindow delta hdelta hdeltaSmall eta input with ⟨pw⟩
  let normalizationWidth := wz1Lemma8_13FaithfulNormalizationWidth input
  have hwidth_pos : 0 < normalizationWidth := pw.normalizationWidth_pos
  have hdeltaOne : delta ≤ 1 := hdeltaSmall.trans hdelta₀_one

  -- Step 2: Viewpoint
  have hwidth_lt_active :
      input.width < wz1Lemma8_13FaithfulActiveWidth input :=
    wz1Lemma49_input_width_lt_active_width
      hdelta hdeltaOne hepsilon hepsilonOne
      input.width_pos input.active_width_large
  rcases wz1_lemma49_active_viewpoint
      input.density input.base input.direction input.direction_unit
      input.width_pos input.delta_le_width input.G₁_strip
      hwidth_lt_active with
    ⟨viewpoint⟩

  -- Step 3: Separated selection
  rcases wz1_lemma49_active_fiber_separated_selection
      viewpoint hdelta pw.delta_le_selectionScale
      pw.selectionScale_le_one input.G₁_frostman with
    ⟨separatedSource⟩

  -- Step 4: Fixed graph
  let fixedH : Finset (Point2 × Point2 × Point2) :=
    input.H.filter fun edge =>
      edge.2.1 ∈ separatedSource.selected ∧
        edge.2.2 = viewpoint.viewpoint
  have hselected_active :
      ∀ b ∈ separatedSource.selected,
        ∃ edge ∈ input.H,
          edge.2.1 = b ∧ edge.2.2 = viewpoint.viewpoint := by
    intro b hb
    refine ⟨(viewpoint.sourceEdge.1, b, viewpoint.viewpoint),
      separatedSource.actual b hb, rfl, rfl⟩
  have hcard :
      Kakeya.realRpowENN delta eta * input.F.enncard *
          separatedSource.selected.enncard ≤
        (fixedH.card : ENNReal) :=
    restrict_g1_g2_card_lower input.density hselected_active
  have hfixedH_nonempty : fixedH.Nonempty := by
    rcases separatedSource.selected_nonempty with ⟨b, hb⟩
    have h := separatedSource.actual b hb
    exact ⟨(viewpoint.sourceEdge.1, b, viewpoint.viewpoint),
      Finset.mem_filter.mpr ⟨h, by simp [hb]⟩⟩
  have hfixedH_subset : fixedH ⊆ input.H :=
    Finset.filter_subset _ _

  -- Step 5: Refinement
  let singletonG₂ : DiscreteSet 2 := {viewpoint.viewpoint}
  have hsupport :
      ∀ edge ∈ fixedH,
        edge.1 ∈ input.F ∧
          edge.2.1 ∈ separatedSource.selected ∧
            edge.2.2 ∈ singletonG₂ := by
    intro edge hedge
    have hfilter := Finset.mem_filter.mp hedge
    have hedgeH : edge ∈ input.H := hfilter.1
    have hsupported :=
      density_vertex_containment input.density edge hedgeH
    exact ⟨hsupported.1, hfilter.2.1,
      by simp [singletonG₂, hfilter.2.2]⟩
  have hF_enncard_ne_zero : input.F.enncard ≠ 0 := by
    dsimp only [DiscreteSet.enncard]
    have h : 0 < input.F.card := Finset.card_pos.mpr input.F_nonempty
    exact Nat.cast_ne_zero.mpr h.ne'
  have hselected_enncard_ne_zero : separatedSource.selected.enncard ≠ 0 := by
    dsimp only [DiscreteSet.enncard]
    have h : 0 < separatedSource.selected.card :=
      Finset.card_pos.mpr separatedSource.selected_nonempty
    exact Nat.cast_ne_zero.mpr h.ne'
  have hdenom_ne_zero :
      (input.F.enncard * separatedSource.selected.enncard) ≠ 0 :=
    mul_ne_zero hF_enncard_ne_zero hselected_enncard_ne_zero
  have hsingleton_enncard : singletonG₂.enncard = 1 := by
    change (singletonG₂.card : ENNReal) = 1
    have h : singletonG₂.card = 1 := by
      simp [singletonG₂]
      <;> norm_num
    rw [h]
    <;> norm_num
  have hcard' :
      Kakeya.realRpowENN delta eta *
        (input.F.enncard * separatedSource.selected.enncard) ≤
        (fixedH.card : ENNReal) := by
    have h : Kakeya.realRpowENN delta eta * input.F.enncard *
          separatedSource.selected.enncard =
        Kakeya.realRpowENN delta eta *
          (input.F.enncard * separatedSource.selected.enncard) := by
      ring
    rw [h] at hcard
    exact hcard
  have hratio :
      Kakeya.realRpowENN delta eta ≤
        (fixedH.card : ENNReal) /
          (input.F.enncard * separatedSource.selected.enncard *
            singletonG₂.enncard) := by
    rw [hsingleton_enncard, mul_one]
    rw [ENNReal.le_div_iff_mul_le
        (Or.inl hdenom_ne_zero)
        (Or.inr (by simp))]
    exact hcard'
  rcases tripartite_refinement_apply
      (hRef := wz1_tripartite_hypergraph_refinement)
      hsupport hfixedH_nonempty
      (epsilon := (1 / 2 : ENNReal))
      (show (0 : ENNReal) < (1 / 2 : ENNReal) from by norm_num)
      (show (1 / 2 : ENNReal) < (1 : ENNReal) from by norm_num) with
    ⟨refinedH, hrefined_subset, _hcard_refined, hUniform_ref⟩
  have hdensity_lower :
      Kakeya.realRpowENN delta eta / 16 ≤
        ((1 / 2 : ENNReal) / (2 : ENNReal) ^ (3 : ℕ)) *
          ((fixedH.card : ENNReal) /
            (input.F.enncard * separatedSource.selected.enncard *
              singletonG₂.enncard)) := by
    have hconstant :
        ((1 / 2 : ENNReal) / (2 : ENNReal) ^ (3 : ℕ)) = (1 : ENNReal) / 16 := by
      simp [div_eq_mul_inv, one_div]
      <;> rw [← ENNReal.mul_inv] <;> norm_num
    rw [hconstant]
    have h2 : Kakeya.realRpowENN delta eta / 16 =
        (1 : ENNReal) / 16 * Kakeya.realRpowENN delta eta := by
      simp [div_eq_mul_inv, one_div, mul_comm]
    rw [h2]
    gcongr
  have hUniform :
      WZ1UniformTripleDensity
        (Kakeya.realRpowENN delta eta / 16)
        input.F separatedSource.selected singletonG₂ refinedH :=
    uniform_triple_density_mono hUniform_ref hdensity_lower

  -- Step 6: Active projections
  let sourceF := wz1ActiveTripleProjection refinedH 0
  let sourceG₁ := wz1ActiveTripleProjection refinedH 1
  let sourceG₂ := wz1ActiveTripleProjection refinedH 2
  have sourceUniform :
      WZ1UniformTripleDensity
        (Kakeya.realRpowENN delta eta / 16)
        sourceF sourceG₁ sourceG₂ refinedH :=
    uniform_density_on_active_projections hUniform
  have hsourceG₁_subset : sourceG₁ ⊆ separatedSource.selected := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with ⟨edge, hedge, rfl⟩
    have hfilter := Finset.mem_filter.mp (hrefined_subset hedge)
    exact hfilter.2.1
  have hsourceG₁_viewpoint : sourceG₁ ⊆ viewpoint.source :=
    hsourceG₁_subset.trans separatedSource.selected_subset
  have hsourceG₂_subset_singleton : sourceG₂ ⊆ singletonG₂ := by
    intro point hpoint
    have h_img : point ∈ refinedH.image (fun edge : Point2 × Point2 × Point2 => edge.2.2) := hpoint
    have h_exists : ∃ (edge : Point2 × Point2 × Point2), edge ∈ refinedH ∧ edge.2.2 = point := by
      simpa [Finset.mem_image] using h_img
    rcases h_exists with ⟨edge, hedge, rfl⟩
    have hfilter := Finset.mem_filter.mp (hrefined_subset hedge)
    have hthird : edge.2.2 = viewpoint.viewpoint := hfilter.2.2
    simpa [singletonG₂] using hthird
  have hsingleton_subset_sourceG₂ : singletonG₂ ⊆ sourceG₂ := by
    intro point hpoint
    have hpt : point = viewpoint.viewpoint := by
      simpa [singletonG₂, Finset.mem_singleton] using hpoint
    rw [hpt]
    have hnonempty : refinedH.Nonempty := hUniform.1
    have h_exists : ∃ (edge : Point2 × Point2 × Point2), edge ∈ refinedH := hnonempty
    rcases h_exists with ⟨edge, hedge⟩
    have hfilter := Finset.mem_filter.mp (hrefined_subset hedge)
    have hthird : edge.2.2 = viewpoint.viewpoint := hfilter.2.2
    have h : viewpoint.viewpoint ∈ sourceG₂ := by
      exact Finset.mem_image.mpr ⟨edge, hedge, hthird⟩
    exact h
  have hsourceG₂_eq : sourceG₂ = singletonG₂ :=
    Finset.Subset.antisymm hsourceG₂_subset_singleton hsingleton_subset_sourceG₂

  -- Step 7: Normalization
  let fMap := wz1Lemma8_13FaithfulFMap input hwidth_pos
  let gMap := wz1Lemma8_13FaithfulGMap input hwidth_pos
  let normalizedF : DiscreteSet 2 := sourceF.image fMap
  let normalizedG₁ : DiscreteSet 2 := sourceG₁.image gMap
  let normalizedG₂ : DiscreteSet 2 := sourceG₂.image gMap
  let normalizedH :=
    refinedH.image (wz1Lemma8_13FaithfulTripleMap input hwidth_pos)
  have normalizedUniform :
      WZ1UniformTripleDensity
        (Kakeya.realRpowENN delta eta / 16)
        normalizedF normalizedG₁ normalizedG₂ normalizedH :=
    density_under_coordinate_equivalences sourceUniform fMap gMap gMap

  -- Step 8: Geometric fields
  have normalizedF_separated :
      normalizedF.IsDeltaSeparated
        (wz1Lemma8_13FaithfulFineScale input) :=
    wz1Lemma8_13_activeF_image_separated input hwidth_pos hUniform
  have normalizedF_frostman :
      normalizedF.IsFrostman
        (wz1Lemma8_13FaithfulFineScale input) 1
        (ENNReal.ofReal (wz1Lemma8_13FaithfulFineConstant input)) :=
    wz1Lemma8_13_activeF_image_frostman
      input hdelta hdeltaOne heta_pos hwidth_pos hUniform
  let fineConstant := wz1Lemma8_13FaithfulFineConstant input
  have fineConstant_ge_one : 1 ≤ fineConstant :=
    wz1Lemma8_13_fineConstant_ge_one
      input hdelta hdeltaOne heta_pos
  have fineConstant_bound :
      fineConstant ≤
        96 * Real.rpow delta
          (-(2 * eta + wz1Lemma8_13FaithfulEpsilonOne epsilon)) :=
    wz1Lemma8_13_fineConstant_bound
      input hdelta pw.aspect_upper
  have hsourceG1_separated :
      sourceG₁.IsDeltaSeparated
        (wz1Lemma8_13FaithfulSelectionScale input) := by
    intro x hx y hy hne
    exact separatedSource.separated
      (hsourceG₁_subset hx) (hsourceG₁_subset hy) hne
  have normalizedSource_separated :
      normalizedG₁.IsDeltaSeparated
        (wz1Lemma8_13FaithfulSourceScale input) :=
    wz1Lemma8_13_source_image_separated
      input hwidth_pos hsourceG1_separated
  let normalizedViewpoint := gMap viewpoint.viewpoint
  let normalizedBase := gMap input.base
  have normalizedViewpoint_mem : normalizedViewpoint ∈ normalizedG₂ := by
    have hviewpoint_in_sourceG₂ : viewpoint.viewpoint ∈ sourceG₂ := by
      rw [hsourceG₂_eq]
      <;> simp [singletonG₂]
    exact Finset.mem_image.mpr
      ⟨viewpoint.viewpoint, hviewpoint_in_sourceG₂, rfl⟩
  have normalizedSource_strip :
      ∀ point ∈ normalizedG₁,
        |inner ℝ (point - normalizedBase)
          (wz1Perp2 viewpoint.orientedDirection)| ≤
          wz1Lemma8_13FaithfulAngularScale input / 2 := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with
      ⟨sourcePoint, hsourcePoint, rfl⟩
    exact wz1Lemma8_13FaithfulGMap_source_strip
      input hwidth_pos viewpoint
      (hsourceG₁_viewpoint hsourcePoint)
  have normalizedSource_side :
      ∀ point ∈ normalizedG₁,
        wz1Lemma8_13FaithfulSide input / 2 ≤
          inner ℝ (point - normalizedViewpoint)
            (wz1Perp2 viewpoint.orientedDirection) := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with
      ⟨sourcePoint, hsourcePoint, rfl⟩
    exact wz1Lemma8_13FaithfulGMap_source_side
      input hwidth_pos viewpoint
      (hsourceG₁_viewpoint hsourcePoint)
  have normalizedSource_cardinality :
      Kakeya.realRpowENN delta (3 * eta) ≤
        16 * Kakeya.realRpowENN
          (wz1Lemma8_13FaithfulSelectionScale input) 1 *
          normalizedG₁.enncard := by
    dsimp only [eta]
    exact wz1Lemma8_13_normalized_source_cardinality
      hdelta separatedSource.cardinality hUniform gMap

  -- Step 9: Unit ball
  have hsourceF_ball : sourceF.IsInUnitBall := by
    intro p hp
    exact input.F_ball p (active_triple_projection_subset hUniform 0 hp)
  have hsourceG1_ball : sourceG₁.IsInUnitBall := by
    intro p hp
    have h1 : p ∈ viewpoint.source := hsourceG₁_viewpoint hp
    have h2 : p ∈ input.G₁ := viewpoint.source_subset h1
    exact input.G₁_ball p h2
  have hsourceG2_ball : sourceG₂.IsInUnitBall := by
    intro p hp
    have h_eq : p = viewpoint.viewpoint := by
      rw [hsourceG₂_eq] at hp
      simpa [singletonG₂] using hp
    rw [h_eq]
    exact input.G₂_ball viewpoint.viewpoint viewpoint.viewpoint_mem
  have hF_strip_active :
      ∀ p ∈ sourceF,
        |inner ℝ p input.direction| ≤ normalizationWidth := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨edge, hedge, rfl⟩
    have hedgeH : edge ∈ input.H := hfixedH_subset (hrefined_subset hedge)
    have h_perp2 : wz1Perp2 (wz1Perp2 input.direction) = -input.direction := by
      ext i; fin_cases i <;> simp [wz1Perp2] <;> decide
    have heps_eq :
        wz1Lemma8_13FaithfulEpsilonOne epsilon =
        wz1Lemma49AuxiliaryEpsilon epsilon := by rfl
    have h1 : |inner ℝ edge.1 (wz1Perp2 (wz1Perp2 input.direction))| ≤
        Real.rpow delta (-wz1Lemma49AuxiliaryEpsilon epsilon) *
          wz1ActiveCommonWidth delta input.H input.density.1 input.base input.direction := by
      have hstrip := input.F_strip edge hedgeH
      simpa [wz1LineNeighborhood] using hstrip
    have h2 : |inner ℝ edge.1 input.direction| ≤
        Real.rpow delta (-wz1Lemma49AuxiliaryEpsilon epsilon) *
          wz1ActiveCommonWidth delta input.H input.density.1 input.base input.direction := by
      rw [h_perp2] at h1
      simpa [inner_neg_right, abs_neg] using h1
    have h3 : Real.rpow delta (-wz1Lemma49AuxiliaryEpsilon epsilon) *
          wz1ActiveCommonWidth delta input.H input.density.1 input.base input.direction =
        normalizationWidth := by
      dsimp only [normalizationWidth,
        wz1Lemma8_13FaithfulNormalizationWidth,
        wz1Lemma8_13FaithfulActiveWidth]
      rw [heps_eq]
    rw [h3] at h2
    exact h2
  have hnormalizedF_ball : normalizedF.IsInUnitBall := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with
      ⟨sourcePoint, hsourcePoint, rfl⟩
    have hbounded :
        dist (wideCoarsePhiF input.direction normalizationWidth
          hwidth_pos input.direction_unit sourcePoint) 0 ≤ 2 :=
      wideCoarsePhiF_image_bounded
        hF_strip_active hsourceF_ball sourcePoint hsourcePoint
    have h_eq : fMap sourcePoint =
        (1 / 2 : ℝ) • wideCoarsePhiF input.direction normalizationWidth
          hwidth_pos input.direction_unit sourcePoint := by rfl
    rw [h_eq]
    have h_dist : dist ((1 / 2 : ℝ) • wideCoarsePhiF input.direction normalizationWidth
          hwidth_pos input.direction_unit sourcePoint) 0 =
        (1 / 2 : ℝ) * dist (wideCoarsePhiF input.direction normalizationWidth
          hwidth_pos input.direction_unit sourcePoint) 0 := by
      simp [dist_zero_right, norm_smul]
      <;> ring
    rw [h_dist]
    linarith
  have hactive_le_norm :
      wz1Lemma8_13FaithfulActiveWidth input ≤ normalizationWidth := by
    dsimp only [normalizationWidth, wz1Lemma8_13FaithfulNormalizationWidth]
    have hfactor : 1 ≤ Real.rpow delta
          (-wz1Lemma8_13FaithfulEpsilonOne epsilon) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        hdelta hdeltaOne (by
          dsimp only [wz1Lemma8_13FaithfulEpsilonOne]
          <;> linarith [sq_nonneg epsilon])
    have hactive_pos : 0 < wz1Lemma8_13FaithfulActiveWidth input :=
      lt_trans input.width_pos hwidth_lt_active
    have hactive_nonneg : 0 ≤ wz1Lemma8_13FaithfulActiveWidth input :=
      hactive_pos.le
    have h : 1 * wz1Lemma8_13FaithfulActiveWidth input ≤
        Real.rpow delta (-wz1Lemma8_13FaithfulEpsilonOne epsilon) *
          wz1Lemma8_13FaithfulActiveWidth input :=
      mul_le_mul_of_nonneg_right hfactor hactive_nonneg
    simpa using h
  have hG1_strip_active :
      ∀ p ∈ sourceG₁,
        |inner ℝ (p - input.base)
          (wz1Perp2 input.direction)| ≤ normalizationWidth := by
    intro p hp
    have hpinSelected : p ∈ separatedSource.selected := hsourceG₁_subset hp
    have hpinSource : p ∈ viewpoint.source :=
      separatedSource.selected_subset hpinSelected
    have hpinG1 : p ∈ input.G₁ := viewpoint.source_subset hpinSource
    have h := input.G₁_strip p hpinG1
    have hwidth_le : input.width ≤ normalizationWidth := by
      have h1 : input.width ≤ wz1Lemma8_13FaithfulActiveWidth input :=
        hwidth_lt_active.le
      exact h1.trans hactive_le_norm
    simpa [wz1LineNeighborhood] using h.trans hwidth_le
  have hnormalizedG₁_ball : normalizedG₁.IsInUnitBall := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with
      ⟨sourcePoint, hsourcePoint, rfl⟩
    have hsourcePoint_G1 : sourcePoint ∈ sourceG₁ := hsourcePoint
    have hsourcePoint_G1 : sourcePoint ∈ sourceG₁ := hsourcePoint
    have hbounded :
        dist (wideCoarsePhiG input.direction normalizationWidth
          hwidth_pos input.base 0 input.direction_unit sourcePoint) 0 ≤ 2 :=
      wideCoarsePhiG_zero_anchor_image_bounded
        hG1_strip_active hsourceG1_ball sourcePoint hsourcePoint_G1
    have h_eq : gMap sourcePoint =
        (1 / 2 : ℝ) • wideCoarsePhiG input.direction normalizationWidth
          hwidth_pos input.base 0 input.direction_unit sourcePoint := by rfl
    rw [h_eq]
    have h_dist : dist ((1 / 2 : ℝ) • wideCoarsePhiG input.direction normalizationWidth
          hwidth_pos input.base 0 input.direction_unit sourcePoint) 0 =
        (1 / 2 : ℝ) * dist (wideCoarsePhiG input.direction normalizationWidth
          hwidth_pos input.base 0 input.direction_unit sourcePoint) 0 := by
      simp [dist_zero_right, norm_smul] <;> ring
    rw [h_dist]
    linarith
  have hG2_strip_active :
      ∀ p ∈ sourceG₂,
        |inner ℝ (p - input.base)
          (wz1Perp2 input.direction)| ≤ normalizationWidth := by
    intro p hp
    have h_eq : p = viewpoint.viewpoint := by
      rw [hsourceG₂_eq] at hp
      simpa [singletonG₂] using hp
    rw [h_eq]
    have hviewpoint_eq : viewpoint.viewpoint = viewpoint.sourceEdge.2.2 :=
      viewpoint.viewpoint_eq
    have h_active_width_le :
        |inner ℝ (viewpoint.viewpoint - input.base)
          (wz1Perp2 input.direction)| ≤
          wz1Lemma8_13FaithfulActiveWidth input := by
      rw [hviewpoint_eq]
      have h := wz1Lemma49_third_mem_activeCommonStrip
        (delta := delta) input.density.1 input.base input.direction
        viewpoint.sourceEdge_mem
      simpa [wz1LineNeighborhood,
        wz1Lemma8_13FaithfulActiveWidth] using h
    exact h_active_width_le.trans hactive_le_norm
  have hnormalizedG₂_ball : normalizedG₂.IsInUnitBall := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with
      ⟨sourcePoint, hsourcePoint, rfl⟩
    have hsp_eq : sourcePoint = viewpoint.viewpoint := by
      have h : sourcePoint ∈ sourceG₂ := hsourcePoint
      rw [hsourceG₂_eq] at h
      simpa [singletonG₂] using h
    rw [hsp_eq]
    have hviewpoint_in_G2 : viewpoint.viewpoint ∈ sourceG₂ := by
      rw [hsourceG₂_eq]
      <;> simp [singletonG₂]
    have hbounded :
        dist (wideCoarsePhiG input.direction normalizationWidth
          hwidth_pos input.base 0 input.direction_unit viewpoint.viewpoint) 0 ≤ 2 :=
      wideCoarsePhiG_zero_anchor_image_bounded
        hG2_strip_active hsourceG2_ball viewpoint.viewpoint hviewpoint_in_G2
    have h_eq : gMap viewpoint.viewpoint =
        (1 / 2 : ℝ) • wideCoarsePhiG input.direction normalizationWidth
          hwidth_pos input.base 0 input.direction_unit viewpoint.viewpoint := by rfl
    rw [h_eq]
    have h_dist : dist ((1 / 2 : ℝ) • wideCoarsePhiG input.direction normalizationWidth
          hwidth_pos input.base 0 input.direction_unit viewpoint.viewpoint) 0 =
        (1 / 2 : ℝ) * dist (wideCoarsePhiG input.direction normalizationWidth
          hwidth_pos input.base 0 input.direction_unit viewpoint.viewpoint) 0 := by
      simp [dist_zero_right, norm_smul] <;> ring
    rw [h_dist]
    linarith

  -- Step 10: Source witness
  have sourceWitness :
      ∀ normalizedEdge ∈ normalizedH,
        ∃ sourceEdge ∈ input.H,
          sourceEdge.2.2 = viewpoint.viewpoint ∧
            normalizedEdge =
              wz1Lemma8_13FaithfulTripleMap
                input hwidth_pos sourceEdge := by
    intro normalizedEdge hnormalizedEdge
    rcases Finset.mem_image.mp hnormalizedEdge with
      ⟨sourceEdge, hsourceEdge, rfl⟩
    have h_in_fixedH : sourceEdge ∈ fixedH :=
      hrefined_subset hsourceEdge
    have h_in_H : sourceEdge ∈ input.H :=
      hfixedH_subset h_in_fixedH
    have h_third : sourceEdge.2.2 = viewpoint.viewpoint :=
      (Finset.mem_filter.mp h_in_fixedH).2.2
    exact ⟨sourceEdge, h_in_H, h_third, rfl⟩

  -- Step 11: Dot identity
  have sourceDot_eq :
      ∀ sourceEdge ∈ input.H,
        inner ℝ sourceEdge.1
            (sourceEdge.2.1 - sourceEdge.2.2) =
          4 * normalizationWidth *
            inner ℝ (fMap sourceEdge.1)
              (gMap sourceEdge.2.1 - gMap sourceEdge.2.2) := by
    intro sourceEdge _
    have hdot := wideCoarseDotIdentity
      input.direction normalizationWidth hwidth_pos
      input.direction_unit input.base 0
      sourceEdge.1 sourceEdge.2.1 sourceEdge.2.2
    have hscale :
        inner ℝ (fMap sourceEdge.1)
          (gMap sourceEdge.2.1 - gMap sourceEdge.2.2) =
          (1 / 4 : ℝ) * inner ℝ
            (wideCoarsePhiF input.direction normalizationWidth
              hwidth_pos input.direction_unit sourceEdge.1)
            (wideCoarsePhiG input.direction normalizationWidth
              hwidth_pos input.base 0 input.direction_unit
              sourceEdge.2.1 -
              wideCoarsePhiG input.direction normalizationWidth
                hwidth_pos input.base 0 input.direction_unit
                sourceEdge.2.2) := by
      let phiF := wideCoarsePhiF input.direction normalizationWidth
        hwidth_pos input.direction_unit
      let phiG := wideCoarsePhiG input.direction normalizationWidth
        hwidth_pos input.base 0 input.direction_unit
      have hf : fMap sourceEdge.1 = (1 / 2 : ℝ) • phiF sourceEdge.1 := by rfl
      have hg1 : gMap sourceEdge.2.1 = (1 / 2 : ℝ) • phiG sourceEdge.2.1 := by rfl
      have hg2 : gMap sourceEdge.2.2 = (1 / 2 : ℝ) • phiG sourceEdge.2.2 := by rfl
      rw [hf, hg1, hg2]
      have hsub : (1 / 2 : ℝ) • phiG sourceEdge.2.1 -
            (1 / 2 : ℝ) • phiG sourceEdge.2.2 =
          (1 / 2 : ℝ) • (phiG sourceEdge.2.1 - phiG sourceEdge.2.2) := by
        rw [smul_sub]
      rw [hsub]
      have hinner : inner ℝ ((1 / 2 : ℝ) • phiF sourceEdge.1)
            ((1 / 2 : ℝ) • (phiG sourceEdge.2.1 - phiG sourceEdge.2.2)) =
          (1 / 2 : ℝ) * (1 / 2 : ℝ) *
            inner ℝ (phiF sourceEdge.1) (phiG sourceEdge.2.1 - phiG sourceEdge.2.2) := by
        simp [inner_smul_left, inner_smul_right]
        <;> ring
      rw [hinner]
      <;> ring
    have hgoal : inner ℝ sourceEdge.1 (sourceEdge.2.1 - sourceEdge.2.2) =
        4 * normalizationWidth * inner ℝ (fMap sourceEdge.1)
          (gMap sourceEdge.2.1 - gMap sourceEdge.2.2) := by
      rw [hscale]
      have h4 : 4 * normalizationWidth * ((1 / 4 : ℝ) * inner ℝ
            (wideCoarsePhiF input.direction normalizationWidth
              hwidth_pos input.direction_unit sourceEdge.1)
            (wideCoarsePhiG input.direction normalizationWidth
              hwidth_pos input.base 0 input.direction_unit sourceEdge.2.1 -
              wideCoarsePhiG input.direction normalizationWidth
                hwidth_pos input.base 0 input.direction_unit sourceEdge.2.2)) =
          normalizationWidth * inner ℝ
            (wideCoarsePhiF input.direction normalizationWidth
              hwidth_pos input.direction_unit sourceEdge.1)
            (wideCoarsePhiG input.direction normalizationWidth
              hwidth_pos input.base 0 input.direction_unit sourceEdge.2.1 -
              wideCoarsePhiG input.direction normalizationWidth
                hwidth_pos input.base 0 input.direction_unit sourceEdge.2.2) := by ring
      rw [h4]
      exact hdot
    exact hgoal

  -- normalizedSupport from normalizedUniform
  have normalizedSupport :
      ∀ edge ∈ normalizedH,
        edge.1 ∈ normalizedF ∧
          edge.2.1 ∈ normalizedG₁ ∧
            edge.2.2 ∈ normalizedG₂ := by
    intro edge hedge
    have h := normalizedUniform.2.1
      (wz1TripleCoordinate edge)
      (Finset.mem_image.mpr ⟨edge, hedge, rfl⟩)
    exact ⟨h 0, h 1, h 2⟩

  exact
    ⟨{
      eta_eq := rfl
      normalizationWidth_pos := pw.normalizationWidth_pos
      normalizationWidth_upper := pw.normalizationWidth_upper
      normalizationWidth_lower := pw.normalizationWidth_lower
      aspect_upper := pw.aspect_upper
      width_le_eighth := pw.width_le_eighth
      angularScale_pos := pw.angularScale_pos
      angularScale_le_quarter := pw.angularScale_le_quarter
      fineScale_pos := pw.fineScale_pos
      fineScale_le_angular := pw.fineScale_le_angular
      selectionScale_pos := pw.selectionScale_pos
      delta_le_selectionScale := pw.delta_le_selectionScale
      selectionScale_le_one := pw.selectionScale_le_one
      sourceScale_pos := pw.sourceScale_pos
      sourceScale_le_one := pw.sourceScale_le_one
      side_pos := pw.side_pos
      radial_threshold := pw.radial_threshold
      radial_angular_bound := pw.radial_angular_bound
      viewpoint := viewpoint
      separatedSource := separatedSource
      fixedH := fixedH
      fixedH_eq := rfl
      fixedH_nonempty := hfixedH_nonempty
      fixedH_subset := hfixedH_subset
      refinedH := refinedH
      refinedH_subset := hrefined_subset
      sourceF := sourceF
      sourceG₁ := sourceG₁
      sourceG₂ := sourceG₂
      sourceF_eq := rfl
      sourceG₁_eq := rfl
      sourceG₂_eq := rfl
      sourceG₁_subset := hsourceG₁_subset
      sourceG₂_eq_singleton := by
        simp [singletonG₂, hsourceG₂_eq]
      sourceUniform := sourceUniform
      normalizedF := normalizedF
      normalizedG₁ := normalizedG₁
      normalizedG₂ := normalizedG₂
      normalizedH := normalizedH
      normalizedF_eq := rfl
      normalizedG₁_eq := rfl
      normalizedG₂_eq := rfl
      normalizedH_eq := rfl
      normalizedUniform := normalizedUniform
      normalizedF_ball := hnormalizedF_ball
      normalizedG₁_ball := hnormalizedG₁_ball
      normalizedG₂_ball := hnormalizedG₂_ball
      fineConstant := fineConstant
      fineConstant_ge_one := fineConstant_ge_one
      fineConstant_bound := fineConstant_bound
      normalizedF_separated := normalizedF_separated
      normalizedF_frostman := normalizedF_frostman
      normalizedViewpoint := normalizedViewpoint
      normalizedViewpoint_eq := rfl
      normalizedViewpoint_mem := normalizedViewpoint_mem
      normalizedSource_separated := normalizedSource_separated
      normalizedBase := normalizedBase
      normalizedBase_eq := rfl
      normalizedSource_strip := normalizedSource_strip
      normalizedSource_side := normalizedSource_side
      normalizedSource_cardinality := normalizedSource_cardinality
      normalizedSupport := normalizedSupport
      sourceWitness := sourceWitness
      sourceDot_eq := sourceDot_eq
    }⟩

end Kakeya.Assouad
