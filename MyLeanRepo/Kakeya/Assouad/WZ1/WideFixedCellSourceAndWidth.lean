import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellNormalizationStatements
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Helper lemmas for WZ1 wide fixed-cell normalization

This scratch module contains three groups of reusable lemmas:

1. Effective width arithmetic identities and bounds.
2. Source approximation error bound from the coarse witness.
3. Normalized dot-difference bound from unit-ball containment.
-/

namespace Kakeya.Assouad

open scoped ENNReal

section EffectiveWidthArithmetic

variable {delta dataWidth firstScale endpointScale scaleFactor coarseScale scale effectiveWidth : ℝ}

lemma wide_fixed_effective_width_scale_eq
    (h_coarseScale : coarseScale = delta / dataWidth)
    (h_scale : scale = scaleFactor * coarseScale)
    (h_eff : effectiveWidth = dataWidth / (firstScale * endpointScale))
    (h_dataWidth_pos : 0 < dataWidth)
    (h_first_pos : 0 < firstScale)
    (h_endpoint_pos : 0 < endpointScale) :
    effectiveWidth * scale =
      delta * scaleFactor / (firstScale * endpointScale) := by
  rw [h_eff, h_scale, h_coarseScale]
  field_simp [h_dataWidth_pos.ne', h_first_pos.ne', h_endpoint_pos.ne']

lemma wide_fixed_scale_factor_ratio_lower
    (h_first_lower : 1 / 4 ≤ firstScale)
    (h_endpoint_lower : 1 / 4 ≤ endpointScale)
    (h_first_le : firstScale ≤ 100)
    (h_endpoint_le : endpointScale ≤ 100)
    (h_product_le : firstScale * endpointScale ≤ 100)
    (h_scaleFactor_eq : scaleFactor = min 1 (min firstScale endpointScale)) :
    1 / 100 ≤ scaleFactor / (firstScale * endpointScale) := by
  have h1 : 0 < firstScale := by linarith
  have h2 : 0 < endpointScale := by linarith
  have h3 : 0 < firstScale * endpointScale := mul_pos h1 h2
  rw [h_scaleFactor_eq]
  by_cases h : firstScale ≤ endpointScale
  · -- firstScale ≤ endpointScale
    have h4 : min firstScale endpointScale = firstScale := by
      rw [min_eq_left] <;> linarith
    rw [h4]
    by_cases h5 : firstScale ≤ 1
    · -- min 1 firstScale = firstScale, ratio = 1/endpointScale ≥ 1/100
      have hmin : min 1 firstScale = firstScale := by
        rw [min_eq_right h5]
      rw [hmin]
      have h_goal : 1 / 100 ≤ firstScale / (firstScale * endpointScale) := by
        have h_eq2 : firstScale / (firstScale * endpointScale) = 1 / endpointScale := by
          field_simp [h1.ne'] <;> ring
        rw [h_eq2]
        apply one_div_le_one_div_of_le
        <;> linarith
      exact h_goal
    · -- 1 < firstScale, min 1 firstScale = 1, ratio = 1/product ≥ 1/100
      have hmin : min 1 firstScale = 1 := by
        rw [min_eq_left] <;> linarith
      rw [hmin]
      have h_goal : 1 / 100 ≤ 1 / (firstScale * endpointScale) := by
        apply one_div_le_one_div_of_le
        <;> linarith
      exact h_goal
  · -- endpointScale < firstScale
    have h4 : min firstScale endpointScale = endpointScale := by
      rw [min_eq_right] <;> linarith
    rw [h4]
    by_cases h5 : endpointScale ≤ 1
    · -- min 1 endpointScale = endpointScale, ratio = 1/firstScale ≥ 1/100
      have hmin : min 1 endpointScale = endpointScale := by
        rw [min_eq_right h5]
      rw [hmin]
      have h_goal : 1 / 100 ≤ endpointScale / (firstScale * endpointScale) := by
        have h_eq2 : endpointScale / (firstScale * endpointScale) = 1 / firstScale := by
          field_simp [h2.ne'] <;> ring
        rw [h_eq2]
        apply one_div_le_one_div_of_le
        <;> linarith
      exact h_goal
    · -- 1 < endpointScale, min 1 endpointScale = 1, ratio = 1/product ≥ 1/100
      have hmin : min 1 endpointScale = 1 := by
        rw [min_eq_left] <;> linarith
      rw [hmin]
      have h_goal : 1 / 100 ≤ 1 / (firstScale * endpointScale) := by
        apply one_div_le_one_div_of_le
        <;> linarith
      exact h_goal

lemma wide_fixed_scale_factor_ratio_upper
    (h_first_lower : 1 / 4 ≤ firstScale)
    (h_endpoint_lower : 1 / 4 ≤ endpointScale)
    (h_scaleFactor_eq : scaleFactor = min 1 (min firstScale endpointScale)) :
    scaleFactor / (firstScale * endpointScale) ≤ 4 := by
  have h1 : 0 < firstScale := by linarith
  have h2 : 0 < endpointScale := by linarith
  rw [h_scaleFactor_eq]
  by_cases h : firstScale ≤ endpointScale
  · have h4 : min firstScale endpointScale = firstScale := by
      rw [min_eq_left] <;> linarith
    rw [h4]
    by_cases h5 : firstScale ≤ 1
    · -- min 1 firstScale = firstScale, ratio = 1/endpointScale ≤ 4
      have hmin : min 1 firstScale = firstScale := by
        rw [min_eq_right h5]
      rw [hmin]
      have h_ep_lower : 1 / 4 ≤ endpointScale := h_endpoint_lower
      have h_goal : 1 / endpointScale ≤ 4 := by
        have h : 1 / endpointScale ≤ 1 / (1 / 4 : ℝ) := by
          gcongr
          <;> linarith
        norm_num at h ⊢
        <;> exact h
      have h_eq : firstScale / (firstScale * endpointScale) = 1 / endpointScale := by
        field_simp [h1.ne'] <;> ring
      rw [h_eq]
      exact h_goal
    · -- 1 < firstScale, min 1 firstScale = 1, ratio = 1/product ≤ 1 ≤ 4
      have hmin : min 1 firstScale = 1 := by
        rw [min_eq_left] <;> linarith
      rw [hmin]
      have h_gt1 : 1 < firstScale := by linarith
      have h_gep : 1 < endpointScale := by linarith
      have h_product_gt1 : 1 < firstScale * endpointScale := by nlinarith
      have h_goal : 1 / (firstScale * endpointScale) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        linarith
      linarith
  · have h4 : min firstScale endpointScale = endpointScale := by
      rw [min_eq_right] <;> linarith
    rw [h4]
    by_cases h5 : endpointScale ≤ 1
    · -- min 1 endpointScale = endpointScale, ratio = 1/firstScale ≤ 4
      have hmin : min 1 endpointScale = endpointScale := by
        rw [min_eq_right h5]
      rw [hmin]
      have h_fs_lower : 1 / 4 ≤ firstScale := h_first_lower
      have h_goal : 1 / firstScale ≤ 4 := by
        have h : 1 / firstScale ≤ 1 / (1 / 4 : ℝ) := by
          gcongr <;> linarith
        norm_num at h ⊢ <;> exact h
      have h_eq : endpointScale / (firstScale * endpointScale) = 1 / firstScale := by
        field_simp [h2.ne'] <;> ring
      rw [h_eq]
      exact h_goal
    · -- 1 < endpointScale, min 1 endpointScale = 1, ratio = 1/product ≤ 1 ≤ 4
      have hmin : min 1 endpointScale = 1 := by
        rw [min_eq_left] <;> linarith
      rw [hmin]
      have h_gt1 : 1 < endpointScale := by linarith
      have h_gfs : 1 < firstScale := by linarith
      have h_product_gt1 : 1 < firstScale * endpointScale := by nlinarith
      have h_goal : 1 / (firstScale * endpointScale) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        linarith
      linarith

lemma wide_fixed_effective_width_scale_lower
    (h_delta_pos : 0 < delta)
    (h_coarseScale : coarseScale = delta / dataWidth)
    (h_scale : scale = scaleFactor * coarseScale)
    (h_eff : effectiveWidth = dataWidth / (firstScale * endpointScale))
    (h_dataWidth_pos : 0 < dataWidth)
    (h_first_pos : 0 < firstScale)
    (h_endpoint_pos : 0 < endpointScale)
    (h_ratio_lower : 1 / 100 ≤ scaleFactor / (firstScale * endpointScale)) :
    delta / 100 ≤ effectiveWidth * scale := by
  have h_eq1 : effectiveWidth * scale =
      delta * scaleFactor / (firstScale * endpointScale) :=
    wide_fixed_effective_width_scale_eq h_coarseScale h_scale h_eff
      h_dataWidth_pos h_first_pos h_endpoint_pos
  have h_eq2 : delta * scaleFactor / (firstScale * endpointScale) =
      delta * (scaleFactor / (firstScale * endpointScale)) := by ring
  rw [h_eq1, h_eq2]
  have h : delta * (1 / 100 : ℝ) ≤ delta * (scaleFactor / (firstScale * endpointScale)) := by
    gcongr <;> linarith
  have h_final : delta / 100 ≤ delta * (scaleFactor / (firstScale * endpointScale)) := by
    have h_eq3 : delta / 100 = delta * (1 / 100 : ℝ) := by ring
    rw [h_eq3]
    exact h
  exact h_final

lemma wide_fixed_effective_width_scale_upper
    (h_delta_pos : 0 < delta)
    (h_coarseScale : coarseScale = delta / dataWidth)
    (h_scale : scale = scaleFactor * coarseScale)
    (h_eff : effectiveWidth = dataWidth / (firstScale * endpointScale))
    (h_dataWidth_pos : 0 < dataWidth)
    (h_first_pos : 0 < firstScale)
    (h_endpoint_pos : 0 < endpointScale)
    (h_ratio_upper : scaleFactor / (firstScale * endpointScale) ≤ 4) :
    effectiveWidth * scale ≤ 4 * delta := by
  have h_eq1 : effectiveWidth * scale =
      delta * scaleFactor / (firstScale * endpointScale) :=
    wide_fixed_effective_width_scale_eq h_coarseScale h_scale h_eff
      h_dataWidth_pos h_first_pos h_endpoint_pos
  have h_eq2 : delta * scaleFactor / (firstScale * endpointScale) =
      delta * (scaleFactor / (firstScale * endpointScale)) := by ring
  rw [h_eq1, h_eq2]
  have h : delta * (scaleFactor / (firstScale * endpointScale)) ≤ delta * 4 := by
    gcongr <;> linarith
  have h_final : delta * (scaleFactor / (firstScale * endpointScale)) ≤ 4 * delta := by
    have h_eq3 : delta * 4 = 4 * delta := by ring
    rw [h_eq3] at h
    exact h
  exact h_final

lemma wide_fixed_effective_width_lower
    (h_eff : effectiveWidth = dataWidth / (firstScale * endpointScale))
    (h_dataWidth_pos : 0 < dataWidth)
    (h_first_pos : 0 < firstScale)
    (h_endpoint_pos : 0 < endpointScale)
    (h_product_le : firstScale * endpointScale ≤ 100) :
    dataWidth / 100 ≤ effectiveWidth := by
  rw [h_eff]
  have h_pos : 0 < firstScale * endpointScale := mul_pos h_first_pos h_endpoint_pos
  have h : dataWidth / 100 ≤ dataWidth / (firstScale * endpointScale) := by
    apply div_le_div_of_nonneg_left h_dataWidth_pos.le
    <;> linarith
  exact h

lemma wide_fixed_effective_width_upper
    (h_eff : effectiveWidth = dataWidth / (firstScale * endpointScale))
    (h_dataWidth_pos : 0 < dataWidth)
    (h_first_pos : 0 < firstScale)
    (h_endpoint_pos : 0 < endpointScale)
    (h_product_lower : 1 / 16 ≤ firstScale * endpointScale) :
    effectiveWidth ≤ 100 * dataWidth := by
  rw [h_eff]
  have h_pos : 0 < firstScale * endpointScale := mul_pos h_first_pos h_endpoint_pos
  have h : dataWidth / (firstScale * endpointScale) ≤ 100 * dataWidth := by
    calc
      dataWidth / (firstScale * endpointScale)
        ≤ dataWidth / (1 / 16 : ℝ) := by
          gcongr
          <;> linarith
      _ = 16 * dataWidth := by
        field_simp
        <;> ring
      _ ≤ 100 * dataWidth := by linarith
  exact h

end EffectiveWidthArithmetic

section SourceApproximation

/--
Generic inner-product perturbation bound.

Given `a, b, c, f, g₁, g₂` in an inner product space with
`‖a-f‖ ≤ ε`, `‖b-g₁‖ ≤ ε`, `‖c-g₂‖ ≤ ε`, `‖b-c‖ ≤ B`, `‖f‖ ≤ C`,
we have
`|inner a (b-c) - inner f (g₁-g₂)| ≤ ε * B + C * 2 * ε`.
-/
lemma inner_product_perturbation_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b c f g1 g2 : E} {epsilon B C : ℝ}
    (h1 : dist a f ≤ epsilon)
    (h2 : dist b g1 ≤ epsilon)
    (h3 : dist c g2 ≤ epsilon)
    (h4 : dist b c ≤ B)
    (h5 : dist f 0 ≤ C)
    (heps : 0 ≤ epsilon) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    |inner ℝ a (b - c) - inner ℝ f (g1 - g2)| ≤
      epsilon * B + C * 2 * epsilon := by
  have h_main : inner ℝ a (b - c) - inner ℝ f (g1 - g2) =
      inner ℝ (a - f) (b - c) + inner ℝ f ((b - g1) - (c - g2)) := by
    simp [inner_sub_left, inner_sub_right]
    <;> abel
  rw [h_main]
  have h6 : |inner ℝ (a - f) (b - c)| ≤ ‖a - f‖ * ‖b - c‖ :=
    abs_real_inner_le_norm _ _
  have h7 : |inner ℝ f ((b - g1) - (c - g2))| ≤
      ‖f‖ * ‖(b - g1) - (c - g2)‖ :=
    abs_real_inner_le_norm _ _
  have h8 : ‖a - f‖ ≤ epsilon := by simpa [dist_eq_norm] using h1
  have h9 : ‖b - c‖ ≤ B := by simpa [dist_eq_norm] using h4
  have h10 : ‖f‖ ≤ C := by simpa [dist_eq_norm] using h5
  have h11 : ‖(b - g1) - (c - g2)‖ ≤ ‖b - g1‖ + ‖c - g2‖ :=
    norm_sub_le _ _
  have h12 : ‖b - g1‖ ≤ epsilon := by simpa [dist_eq_norm] using h2
  have h13 : ‖c - g2‖ ≤ epsilon := by simpa [dist_eq_norm] using h3
  set x := inner ℝ (a - f) (b - c) with hx
  set y := inner ℝ f ((b - g1) - (c - g2)) with hy
  have h_abs : |x + y| ≤ |x| + |y| := by
    have h1 : x ≤ |x| := le_abs_self x
    have h2 : y ≤ |y| := le_abs_self y
    have h3 : -x ≤ |x| := by
      have h31 : -x ≤ |-x| := le_abs_self (-x)
      have h32 : |-x| = |x| := abs_neg x
      rw [h32] at h31
      exact h31
    have h4 : -y ≤ |y| := by
      have h41 : -y ≤ |-y| := le_abs_self (-y)
      have h42 : |-y| = |y| := abs_neg y
      rw [h42] at h41
      exact h41
    have h5 : x + y ≤ |x| + |y| := by linarith
    have h6 : -(x + y) ≤ |x| + |y| := by linarith
    have h7 : -(|x| + |y|) ≤ x + y := by linarith
    exact abs_le.mpr ⟨h7, h5⟩
  calc
    |x + y| ≤ |x| + |y| := h_abs
    _ ≤ ‖a - f‖ * ‖b - c‖ + ‖f‖ * ‖(b - g1) - (c - g2)‖ := by
      simp only [hx, hy] <;> gcongr <;> exact h6 <;> exact h7
    _ ≤ epsilon * B + C * (‖b - g1‖ + ‖c - g2‖) := by
      gcongr <;> linarith
    _ ≤ epsilon * B + C * (epsilon + epsilon) := by
      gcongr <;> linarith
    _ = epsilon * B + C * 2 * epsilon := by ring

/--
Source approximation error for one normalized fixed-cell edge.

Given a cell edge `(f, g₁, g₂) ∈ cellH`, use the coarse source witness to
obtain `sourceEdge ∈ data.refinedH` and bound the error between the source
dot product and `effectiveWidth` times the normalized dot product.

The error is bounded by `1200 * effectiveWidth * coarse.scale`.
-/
lemma wide_fixed_source_approximation
    {delta epsilon eta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data : WZ1Proposition8_9CommonStripData delta epsilon eta parameters F G₁ G₂ H}
    {coarse : WZ1Proposition8_9WideCoarseData delta epsilon eta parameters F G₁ G₂ H data}
    {fixed : WZ1Proposition8_9WideFixedCellData coarse}
    {firstScale endpointScale effectiveWidth : ℝ}
    {endpointTranslation : Point2}
    (h_first_pos : 0 < firstScale)
    (h_endpoint_pos : 0 < endpointScale)
    (h_product_le : firstScale * endpointScale ≤ 100)
    (h_eff_eq : effectiveWidth = data.width / (firstScale * endpointScale))
    (f g1 g2 : Point2)
    (h_edge_in_cellH : (f, g1, g2) ∈ fixed.cellH) :
    ∃ sourceEdge ∈ data.refinedH,
      |inner ℝ sourceEdge.1 (sourceEdge.2.1 - sourceEdge.2.2) -
        effectiveWidth * inner ℝ (firstScale • f)
          ((endpointScale • g1 + endpointTranslation) -
           (endpointScale • g2 + endpointTranslation))| ≤
        1200 * effectiveWidth * coarse.scale := by
  have h_cellH_subset_coarseH : fixed.cellH ⊆ coarse.coarseH := by
    have h1 : fixed.cellH ⊆ fixed.inducedH := fixed.cellH_subset
    have h2 : fixed.inducedH ⊆ coarse.coarseH := by
      rw [fixed.inducedH_eq]
      exact Finset.filter_subset _ _
    exact Finset.Subset.trans h1 h2
  have h_coarseEdge : (f, g1, g2) ∈ coarse.coarseH :=
    h_cellH_subset_coarseH h_edge_in_cellH
  rcases coarse.source_witness (f, g1, g2) h_coarseEdge with
    ⟨sourceEdge, h_sourceEdge, transformedEdge, h_dot_eq,
     h_dist1, h_dist2, h_dist3, h_norm1, h_norm2, h_norm3, _, _⟩
  have h_f_in_coarseF : f ∈ coarse.coarseF := by
    have h_support : f ∈ fixed.cellF :=
      (fixed.cellH_support (f, g1, g2) h_edge_in_cellH).1
    have h1 : fixed.cellF ⊆ fixed.ambientCellF := fixed.cellF_subset
    have h2 : fixed.ambientCellF ⊆ coarse.coarseF := by
      rw [fixed.ambientCellF_eq]
      simpa using Finset.filter_subset coarse.coarseF _
    exact h2 (h1 h_support)
  have h_f_norm : dist f 0 ≤ 3 := coarse.coarseF_bounded f h_f_in_coarseF
  have h_bc_norm : dist transformedEdge.2.1 transformedEdge.2.2 ≤ 4 := by
    have h_comm : dist 0 transformedEdge.2.2 = dist transformedEdge.2.2 0 := dist_comm _ _
    calc
      dist transformedEdge.2.1 transformedEdge.2.2
          ≤ dist transformedEdge.2.1 0 + dist 0 transformedEdge.2.2 :=
        dist_triangle transformedEdge.2.1 0 transformedEdge.2.2
      _ = dist transformedEdge.2.1 0 + dist transformedEdge.2.2 0 := by
        rw [h_comm]
      _ ≤ 2 + 2 := by gcongr
      _ = 4 := by norm_num
  have h_inner_err :
      |inner ℝ transformedEdge.1 (transformedEdge.2.1 - transformedEdge.2.2) -
        inner ℝ f (g1 - g2)| ≤ 10 * coarse.scale := by
    have h_eps : 0 ≤ coarse.scale := coarse.scale_pos.le
    have h_B : (0 : ℝ) ≤ 4 := by norm_num
    have h_C : (0 : ℝ) ≤ 3 := by norm_num
    have h := inner_product_perturbation_bound
      (epsilon := coarse.scale) (B := (4 : ℝ)) (C := (3 : ℝ))
      h_dist1 h_dist2 h_dist3 h_bc_norm h_f_norm h_eps h_B h_C
    have h_bound : coarse.scale * (4 : ℝ) + (3 : ℝ) * 2 * coarse.scale ≤
        10 * coarse.scale := by ring_nf <;> linarith
    exact h.trans h_bound
  have h_normalized_dot :
      inner ℝ (firstScale • f)
        ((endpointScale • g1 + endpointTranslation) -
         (endpointScale • g2 + endpointTranslation)) =
      firstScale * endpointScale * inner ℝ f (g1 - g2) := by
    have h1 : (endpointScale • g1 + endpointTranslation) -
        (endpointScale • g2 + endpointTranslation) =
        endpointScale • (g1 - g2) := by
      calc
        (endpointScale • g1 + endpointTranslation) -
            (endpointScale • g2 + endpointTranslation)
          = endpointScale • g1 - endpointScale • g2 := by abel
        _ = endpointScale • (g1 - g2) := by
          rw [smul_sub]
    rw [h1]
    have h2 : inner ℝ (firstScale • f) (endpointScale • (g1 - g2)) =
        firstScale * endpointScale * inner ℝ f (g1 - g2) := by
      rw [real_inner_smul_left, real_inner_smul_right]
      <;> ring
    exact h2
  have h_source_dot :
      inner ℝ sourceEdge.1 (sourceEdge.2.1 - sourceEdge.2.2) =
        data.width * inner ℝ transformedEdge.1
          (transformedEdge.2.1 - transformedEdge.2.2) := h_dot_eq
  have h_product_pos : 0 < firstScale * endpointScale :=
    mul_pos h_first_pos h_endpoint_pos
  have h_dataWidth_pos : 0 < data.width := data.width_pos
  have h_main :
      |inner ℝ sourceEdge.1 (sourceEdge.2.1 - sourceEdge.2.2) -
        effectiveWidth * inner ℝ (firstScale • f)
          ((endpointScale • g1 + endpointTranslation) -
           (endpointScale • g2 + endpointTranslation))| ≤
      10 * data.width * coarse.scale := by
    rw [h_source_dot, h_normalized_dot, h_eff_eq]
    have h_eq2 :
        data.width * inner ℝ transformedEdge.1 (transformedEdge.2.1 - transformedEdge.2.2) -
        (data.width / (firstScale * endpointScale)) *
          (firstScale * endpointScale * inner ℝ f (g1 - g2)) =
        data.width * (inner ℝ transformedEdge.1 (transformedEdge.2.1 - transformedEdge.2.2) -
          inner ℝ f (g1 - g2)) := by
      field_simp [h_product_pos.ne'] <;> ring
    rw [h_eq2]
    have h_abs : |data.width * (inner ℝ transformedEdge.1 (transformedEdge.2.1 - transformedEdge.2.2) -
        inner ℝ f (g1 - g2))| =
        data.width * |inner ℝ transformedEdge.1 (transformedEdge.2.1 - transformedEdge.2.2) -
          inner ℝ f (g1 - g2)| := by
      rw [abs_mul, abs_of_pos h_dataWidth_pos]
    rw [h_abs]
    have h_goal : data.width * |inner ℝ transformedEdge.1 (transformedEdge.2.1 - transformedEdge.2.2) -
        inner ℝ f (g1 - g2)| ≤ data.width * (10 * coarse.scale) :=
      mul_le_mul_of_nonneg_left h_inner_err h_dataWidth_pos.le
    have h_final2 : data.width * (10 * coarse.scale) = 10 * data.width * coarse.scale := by ring
    rw [h_final2] at h_goal
    exact h_goal
  have h_final : 10 * data.width * coarse.scale ≤
      1200 * effectiveWidth * coarse.scale := by
    rw [h_eff_eq]
    have h6 : 0 < firstScale * endpointScale := h_product_pos
    have h7 : 10 * (firstScale * endpointScale) ≤ 1200 := by linarith
    have h_eq : 10 * data.width * coarse.scale =
        (10 * (firstScale * endpointScale)) *
        ((data.width / (firstScale * endpointScale)) * coarse.scale) := by
      field_simp [h6.ne'] <;> ring
    rw [h_eq]
    have h_pos2 : 0 < (data.width / (firstScale * endpointScale)) * coarse.scale :=
      mul_pos (div_pos h_dataWidth_pos h_product_pos) coarse.scale_pos
    have h_goal : (10 * (firstScale * endpointScale)) *
        ((data.width / (firstScale * endpointScale)) * coarse.scale) ≤
        1200 * ((data.width / (firstScale * endpointScale)) * coarse.scale) :=
      mul_le_mul_of_nonneg_right h7 h_pos2.le
    have h_rhs : 1200 * ((data.width / (firstScale * endpointScale)) * coarse.scale) =
        1200 * (data.width / (firstScale * endpointScale)) * coarse.scale := by ring
    rw [h_rhs] at h_goal
    exact h_goal
  exact ⟨sourceEdge, h_sourceEdge, h_main.trans h_final⟩

end SourceApproximation

section NormalizedDotBound

/--
If all vertices of a tripartite graph lie in the unit ball, then every
dot-difference value has absolute value at most 2.

`|inner a (b - c)| ≤ ‖a‖ * ‖b - c‖ ≤ 1 * (‖b‖ + ‖c‖) ≤ 2`.
-/
lemma unitBall_imp_dot_bound
    {H : Finset (Point2 × Point2 × Point2)}
    (hF : ∀ edge ∈ H, dist edge.1 0 ≤ 1)
    (hG1 : ∀ edge ∈ H, dist edge.2.1 0 ≤ 1)
    (hG2 : ∀ edge ∈ H, dist edge.2.2 0 ≤ 1) :
    ∀ value ∈ wz1DotDifferenceSet H, |value| ≤ 2 := by
  intro value hvalue
  rcases Finset.mem_image.mp hvalue with ⟨edge, hedge, rfl⟩
  have h1 : ‖edge.1‖ ≤ 1 := by simpa [dist_eq_norm] using hF edge hedge
  have h21 : ‖edge.2.1‖ ≤ 1 := by simpa [dist_eq_norm] using hG1 edge hedge
  have h22 : ‖edge.2.2‖ ≤ 1 := by simpa [dist_eq_norm] using hG2 edge hedge
  have h2 : ‖edge.2.1 - edge.2.2‖ ≤ 2 := by
    calc
      ‖edge.2.1 - edge.2.2‖
          ≤ ‖edge.2.1‖ + ‖edge.2.2‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by gcongr
      _ = 2 := by norm_num
  have h3 : |inner ℝ edge.1 (edge.2.1 - edge.2.2)| ≤
      ‖edge.1‖ * ‖edge.2.1 - edge.2.2‖ :=
    abs_real_inner_le_norm _ _
  calc
    |inner ℝ edge.1 (edge.2.1 - edge.2.2)|
        ≤ ‖edge.1‖ * ‖edge.2.1 - edge.2.2‖ := h3
    _ ≤ 1 * 2 := by gcongr
    _ = 2 := by norm_num

end NormalizedDotBound

end Kakeya.Assouad
