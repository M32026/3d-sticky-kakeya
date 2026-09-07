import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9WideSplitStatements

/-!
# Scale and quantitative separation helpers for fixed-cell selection

Provides:
- `wide_coarse_scale_lt_rpow`: `scale < delta^(epsilon/10)` from width lower bound
- `exists_delta_scale_le_one_twentieth`: choose `delta₀` so `scale ≤ 1/20`
- `quantitative_separation_from_source`: derive `1/3` and `2/5` separation from coarse source witness
-/

namespace Kakeya.Assouad

/--
From `width > delta^(1 - epsilon/10)` and `scale = delta / width`,
conclude `scale < delta^(epsilon/10)`.
-/
lemma wide_coarse_scale_lt_rpow
    {delta epsilon width scale : ℝ}
    (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon)
    (hwidth : 0 < width)
    (hscale : scale = delta / width)
    (hwidth_lower : Real.rpow delta (1 - epsilon / 10) < width) :
    scale < Real.rpow delta (epsilon / 10) := by
  set r := Real.rpow delta (1 - epsilon / 10) with hr_def
  have hpos : 0 < r := Real.rpow_pos_of_pos hdelta _
  have h1 : delta / width < delta / r :=
    div_lt_div_of_pos_left hdelta hpos hwidth_lower
  have h_e1 : 0 < Real.rpow delta (epsilon / 10) := Real.rpow_pos_of_pos hdelta _
  have h_sum : (epsilon / 10) + (1 - epsilon / 10) = 1 := by ring
  have h_mul : Real.rpow delta (epsilon / 10) * r = Real.rpow delta 1 := by
    have hr : r = Real.rpow delta (1 - epsilon / 10) := by simp [r, hr_def]
    rw [hr]
    have h : Real.rpow delta (epsilon / 10) * Real.rpow delta (1 - epsilon / 10) =
        Real.rpow delta ((epsilon / 10) + (1 - epsilon / 10)) :=
      (Real.rpow_add hdelta (epsilon / 10) (1 - epsilon / 10)).symm
    rw [h, h_sum]
  have h2 : delta / r = Real.rpow delta (epsilon / 10) := by
    have h3 : Real.rpow delta 1 = delta := by simp
    rw [h3] at h_mul
    field_simp [hpos.ne'] at h_mul ⊢
    <;> exact h_mul.symm
  rw [hscale]
  exact h1.trans_eq h2

/--
Choose `delta₀` so that whenever `delta ≤ delta₀` and `width > delta^(1-epsilon/10)`,
we have `scale = delta / width ≤ 1/20`.
-/
lemma exists_delta_scale_le_one_twentieth
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
      ∀ (width scale : ℝ), 0 < width → scale = delta / width →
      Real.rpow delta (1 - epsilon / 10) < width →
      scale ≤ 1 / 20 := by
  let delta₀ : ℝ := (1 / 20 : ℝ) ^ (10 / epsilon)
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_one : delta₀ ≤ 1 := by
    have h1 : (0 : ℝ) ≤ (1 / 20 : ℝ) := by norm_num
    have h2 : (1 / 20 : ℝ) ≤ 1 := by norm_num
    have h3 : 0 ≤ 10 / epsilon := by positivity
    exact Real.rpow_le_one h1 h2 h3
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta hdelta hdelta_le width scale hwidth hscale hwidth_lower
  have h4 : scale < Real.rpow delta (epsilon / 10) :=
    wide_coarse_scale_lt_rpow hdelta hepsilon hwidth hscale hwidth_lower
  have h5 : Real.rpow delta (epsilon / 10) ≤ 1 / 20 := by
    have h6 : delta ≤ (1 / 20 : ℝ) ^ (10 / epsilon) := hdelta_le
    have h7 : 0 < epsilon / 10 := by positivity
    have h8 : Real.rpow delta (epsilon / 10) ≤
        Real.rpow ((1 / 20 : ℝ) ^ (10 / epsilon)) (epsilon / 10) :=
      Real.rpow_le_rpow hdelta.le h6 h7.le
    have h9 : Real.rpow ((1 / 20 : ℝ) ^ (10 / epsilon)) (epsilon / 10) = (1 / 20 : ℝ) := by
      have h10 : Real.rpow ((1 / 20 : ℝ) ^ (10 / epsilon)) (epsilon / 10) =
          Real.rpow (1 / 20 : ℝ) ((10 / epsilon) * (epsilon / 10)) :=
        (Real.rpow_mul (by norm_num) (10 / epsilon) (epsilon / 10)).symm
      rw [h10]
      have h11 : (10 / epsilon) * (epsilon / 10) = 1 := by
        field_simp [hepsilon.ne'] <;> ring
      rw [h11] <;> norm_num
    rw [h9] at h8
    exact h8
  linarith

/--
From the coarse source witness, derive quantitative separation:
`1/3 ≤ dist edge.1 0` and `2/5 ≤ dist edge.2.1 edge.2.2`.
Requires `scale ≤ 1/20`.
-/
lemma quantitative_separation_from_source
    {delta epsilon eta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data : WZ1Proposition8_9CommonStripData delta epsilon eta parameters F G₁ G₂ H}
    {coarse : WZ1Proposition8_9WideCoarseData delta epsilon eta parameters F G₁ G₂ H data}
    (hscale_le : coarse.scale ≤ 1 / 20)
    {edge : Point2 × Point2 × Point2}
    (hedge : edge ∈ coarse.coarseH) :
    1 / 3 ≤ dist edge.1 0 ∧ 2 / 5 ≤ dist edge.2.1 edge.2.2 := by
  rcases coarse.source_witness edge hedge with
    ⟨_sourceEdge, _, transformedEdge,
      _h_dot, hdist1, hdist2, hdist3, _b1, _b2, _b3, hsep1, hsep2⟩
  have hrev1 : dist edge.1 0 ≥ dist transformedEdge.1 0 - dist transformedEdge.1 edge.1 := by
    have h : dist transformedEdge.1 0 ≤ dist transformedEdge.1 edge.1 + dist edge.1 0 :=
      dist_triangle transformedEdge.1 edge.1 0
    linarith
  have h1 : dist edge.1 0 ≥ 1 / 2 - coarse.scale := by
    calc
      dist edge.1 0
        ≥ dist transformedEdge.1 0 - dist transformedEdge.1 edge.1 := hrev1
      _ ≥ 1 / 2 - coarse.scale := by
        have hsub : dist transformedEdge.1 0 - dist transformedEdge.1 edge.1 ≥
            1 / 2 - coarse.scale := by
          linarith [hsep1, hdist1]
        exact hsub
  have hrev2 : dist edge.2.1 edge.2.2 ≥
      dist transformedEdge.2.1 transformedEdge.2.2
        - dist transformedEdge.2.1 edge.2.1
        - dist transformedEdge.2.2 edge.2.2 := by
    have h_a : dist transformedEdge.2.1 transformedEdge.2.2 ≤
        dist transformedEdge.2.1 edge.2.1 + dist edge.2.1 transformedEdge.2.2 :=
      dist_triangle transformedEdge.2.1 edge.2.1 transformedEdge.2.2
    have h_b : dist edge.2.1 transformedEdge.2.2 ≤
        dist edge.2.1 edge.2.2 + dist edge.2.2 transformedEdge.2.2 :=
      dist_triangle edge.2.1 edge.2.2 transformedEdge.2.2
    have h_c : dist edge.2.2 transformedEdge.2.2 = dist transformedEdge.2.2 edge.2.2 :=
      dist_comm _ _
    linarith
  have h_est2 : dist transformedEdge.2.1 transformedEdge.2.2 -
      dist transformedEdge.2.1 edge.2.1 -
      dist transformedEdge.2.2 edge.2.2 ≥ 1 / 2 - 2 * coarse.scale := by
    linarith [hsep2, hdist2, hdist3]
  have h2 : dist edge.2.1 edge.2.2 ≥ 1 / 2 - 2 * coarse.scale := by
    calc
      dist edge.2.1 edge.2.2
        ≥ dist transformedEdge.2.1 transformedEdge.2.2
            - dist transformedEdge.2.1 edge.2.1
            - dist transformedEdge.2.2 edge.2.2 := hrev2
      _ ≥ 1 / 2 - 2 * coarse.scale := h_est2
  have h3 : 1 / 3 ≤ dist edge.1 0 := by
    have h4 : 1 / 2 - coarse.scale ≥ 1 / 3 := by linarith
    linarith
  have h5 : 2 / 5 ≤ dist edge.2.1 edge.2.2 := by
    have h6 : 1 / 2 - 2 * coarse.scale ≥ 2 / 5 := by linarith
    linarith
  exact ⟨h3, h5⟩

end Kakeya.Assouad
