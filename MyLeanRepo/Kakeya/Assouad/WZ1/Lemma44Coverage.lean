import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44BadPairStatements

/-!
# Coverage lemma for WZ1 Lemma 44

If two lines through a common base point are not separated at scale `r`,
then the `r`-thickening of one is contained in the `13r`-thickening of the other
(for points in the unit ball).

Proof: non-separation gives unit normals `n, n'` with `‖n - n'‖ < r`.
The strip inequality gives `|inner (p-base) n| ≤ r`.
Triangle inequality gives `|inner (p-base) n'| ≤ r + 2r = 3r < 13r`.
Orthogonal projection onto `ℓ'` shows `dist p ℓ' ≤ |inner (p-base) n'|`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
If two lines through `base` are not `r`-separated, then any point `p` in the
unit ball that lies in the `r`-thickening of `ℓ` also lies in the
`13r`-thickening of `ℓ'`.
-/
lemma coverage_enlarged_thickening {r : ℝ} (hr : 0 < r)
    {base p : Point2} (hbase_ball : ‖base‖ ≤ 1) (hp_ball : ‖p‖ ≤ 1)
    {ℓ ℓ' : AffineSubspace ℝ Point2}
    (hℓ_base : base ∈ (ℓ : Set Point2))
    (hℓ'_base : base ∈ (ℓ' : Set Point2))
    (hfin : Module.finrank ℝ ℓ.direction = 1)
    (hfin' : Module.finrank ℝ ℓ'.direction = 1)
    (h_not_sep : ¬ WZ1LinesSeparated r ℓ ℓ') :
    p ∈ Metric.thickening r (ℓ : Set Point2) →
    p ∈ Metric.thickening (13 * r) (ℓ' : Set Point2) := by
  -- Step 1: From non-separation, obtain unit normals n, n' with ‖n - n'‖ < r
  have h_main : ∃ (n n' : Point2),
      ‖n‖ = 1 ∧ (∀ v ∈ ℓ.direction, inner ℝ v n = 0) ∧
      ‖n'‖ = 1 ∧ (∀ v ∈ ℓ'.direction, inner ℝ v n' = 0) ∧
      ‖n - n'‖ < r := by
    simp only [WZ1LinesSeparated] at h_not_sep
    push Not at h_not_sep
    rcases h_not_sep with ⟨n1, n2, hn1_norm, hn2_norm, hn1_orth, hn2_orth, h⟩
    -- h : r ≤ ‖n1 - n2‖ → ‖n1 + n2‖ < r
    have h_cases : ‖n1 - n2‖ < r ∨ ‖n1 + n2‖ < r := by
      by_cases h4 : r ≤ ‖n1 - n2‖
      · exact Or.inr (h h4)
      · have h5 : ‖n1 - n2‖ < r := by linarith
        exact Or.inl h5
    rcases h_cases with (h_lt | h_lt)
    · -- Case 1: ‖n1 - n2‖ < r
      exact ⟨n1, n2, hn1_norm, hn1_orth, hn2_norm, hn2_orth, h_lt⟩
    · -- Case 2: ‖n1 + n2‖ < r, replace n2 by -n2
      have hneg_norm : ‖(-n2)‖ = 1 := by
        rw [norm_neg] <;> exact hn2_norm
      have hneg_orth : ∀ v ∈ ℓ'.direction, inner ℝ v (-n2) = 0 := by
        intro v hv
        have h4 : inner ℝ v n2 = 0 := hn2_orth v hv
        simpa [inner_neg_right] using h4
      have hdist : ‖n1 - (-n2)‖ < r := by
        have h5 : n1 - (-n2) = n1 + n2 := by abel
        rw [h5] <;> exact h_lt
      exact ⟨n1, -n2, hn1_norm, hn1_orth, hneg_norm, hneg_orth, hdist⟩
  rcases h_main with ⟨n, n', hn_norm, hn_orth, hn'_norm, hn'_orth, h_nn'_lt⟩

  intro h_p_in

  -- Step 2: From p ∈ thickening r ℓ, get |inner (p - base) n| ≤ r
  have h_strip_set : p ∈ {y : Point2 | |inner ℝ y n - inner ℝ base n| ≤ r} :=
    thickening_subset_strip hfin n hn_norm hn_orth base hℓ_base r hr h_p_in
  have h_strip1 : |inner ℝ (p - base) n| ≤ r := by
    have h9 : |inner ℝ p n - inner ℝ base n| ≤ r := h_strip_set
    have h10 : inner ℝ p n - inner ℝ base n = inner ℝ (p - base) n := by
      rw [←inner_sub_left]
    rw [h10] at h9
    exact h9

  -- Step 3: Bound |inner (p - base) n'| by 3r < 13r
  set v := p - base with hv_def
  have h_decomp : inner ℝ v n' = inner ℝ v n + inner ℝ v (n' - n) := by
    have h : inner ℝ v n' = inner ℝ v (n + (n' - n)) := by
      have h2 : n + (n' - n) = n' := by abel
      rw [h2]
    rw [h, inner_add_right]
  have h_abs : |inner ℝ v n'| ≤ |inner ℝ v n| + |inner ℝ v (n' - n)| := by
    rw [h_decomp]
    exact abs_add_le (inner ℝ v n) (inner ℝ v (n' - n))
  have h_cauchy : |inner ℝ v (n' - n)| ≤ ‖v‖ * ‖n' - n‖ :=
    abs_real_inner_le_norm v (n' - n)
  have h_norm_v : ‖v‖ ≤ 2 := by
    have h1 : ‖p - base‖ ≤ ‖p‖ + ‖base‖ := by
      calc ‖p - base‖ = ‖p + (-base)‖ := by rw [show p + (-base) = p - base by abel]
        _ ≤ ‖p‖ + ‖(-base)‖ := norm_add_le p (-base)
        _ = ‖p‖ + ‖base‖ := by rw [norm_neg]
    exact h1.trans (by linarith)
  have h_nn'_symm : ‖n' - n‖ < r := by
    have h_symm : ‖n' - n‖ = ‖n - n'‖ := by
      have h : n' - n = -(n - n') := by abel
      rw [h, norm_neg]
    rw [h_symm] <;> exact h_nn'_lt
  have h_bound : |inner ℝ v n'| < 13 * r := by
    have h1 : |inner ℝ v n'| ≤ |inner ℝ v n| + ‖v‖ * ‖n' - n‖ := by
      calc |inner ℝ v n'|
        ≤ |inner ℝ v n| + |inner ℝ v (n' - n)| := h_abs
      _ ≤ |inner ℝ v n| + ‖v‖ * ‖n' - n‖ := by
        gcongr
        <;> exact h_cauchy
    have h4 : ‖v‖ * ‖n' - n‖ ≤ 2 * r := by
      calc ‖v‖ * ‖n' - n‖ ≤ 2 * ‖n' - n‖ := by gcongr
        _ ≤ 2 * r := by linarith [h_nn'_symm]
    have h2 : |inner ℝ v n| + ‖v‖ * ‖n' - n‖ ≤ r + 2 * r := by
      have h3 : |inner ℝ v n| ≤ r := h_strip1
      linarith
    linarith

  -- Step 4: Construct orthogonal projection q onto ℓ'
  set c : ℝ := inner ℝ v n' with hc_def
  set q : Point2 := p - c • n' with hq_def

  have h_q_dist : dist p q = |c| := by
    have h1 : p - q = c • n' := by
      simp [hq_def] <;> abel
    have h2 : dist p q = ‖p - q‖ := by rfl
    have h3 : ‖p - q‖ = ‖c • n'‖ := by rw [h1]
    have h4 : ‖c • n'‖ = ‖c‖ * ‖n'‖ := norm_smul c n'
    have h5 : ‖c‖ = |c| := Real.norm_eq_abs c
    rw [h2, h3, h4, hn'_norm, h5] <;> ring

  have h_n'_ne_zero : n' ≠ 0 := by
    intro h
    rw [h] at hn'_norm
    norm_num at hn'_norm <;> linarith

  have h_orth_complement : ℓ'.direction = (ℝ ∙ n')ᗮ := by
    have h_le : ℓ'.direction ≤ (ℝ ∙ n')ᗮ := by
      intro v hv
      simp only [Submodule.mem_orthogonal] at *
      intro w hw
      rcases Submodule.mem_span_singleton.mp hw with ⟨k, rfl⟩
      have h_comm : inner ℝ (k • n') v = inner ℝ v (k • n') :=
        (real_inner_comm (k • n') v).symm
      rw [h_comm]
      have h4 : inner ℝ v (k • n') = k * inner ℝ v n' := by
        rw [inner_smul_right]
      have h5 : inner ℝ v n' = 0 := hn'_orth v hv
      rw [h4, h5] <;> ring
    have h_rank_span : Module.finrank ℝ (ℝ ∙ n') = 1 :=
      finrank_span_singleton h_n'_ne_zero
    have h_rank_orth : Module.finrank ℝ (ℝ ∙ n')ᗮ = 1 := by
      have h_add : Module.finrank ℝ (ℝ ∙ n') + Module.finrank ℝ (ℝ ∙ n')ᗮ =
          Module.finrank ℝ Point2 :=
        Submodule.finrank_add_finrank_orthogonal (ℝ ∙ n')
      have h_pt2 : Module.finrank ℝ Point2 = 2 := by simp
      omega
    exact Submodule.eq_of_le_of_finrank_eq h_le (by rw [hfin', h_rank_orth])

  have h_inner_zero : inner ℝ (q - base) n' = 0 := by
    have h_qbase : q - base = v - c • n' := by
      simp [hq_def, hv_def] <;> abel
    rw [h_qbase]
    have h3 : inner ℝ (v - c • n') n' = inner ℝ v n' - inner ℝ (c • n') n' := by
      rw [inner_sub_left]
    rw [h3]
    have h4 : inner ℝ (c • n') n' = c * inner ℝ n' n' := by
      simp [inner_smul_left]
      <;> ring
    rw [h4]
    have h5 : inner ℝ n' n' = ‖n'‖ ^ 2 := real_inner_self_eq_norm_sq n'
    rw [h5, hn'_norm, hc_def] <;> ring

  have h_mem_orth : q - base ∈ (ℝ ∙ n')ᗮ := by
    simp only [Submodule.mem_orthogonal]
    intro w hw
    rcases Submodule.mem_span_singleton.mp hw with ⟨k, rfl⟩
    have h_comm2 : inner ℝ (k • n') (q - base) = inner ℝ (q - base) (k • n') :=
      (real_inner_comm (k • n') (q - base)).symm
    rw [h_comm2]
    have h6 : inner ℝ (q - base) (k • n') = k * inner ℝ (q - base) n' := by
      rw [inner_smul_right]
    rw [h6, h_inner_zero] <;> ring

  have h7 : q - base ∈ ℓ'.direction := by
    rw [h_orth_complement] <;> exact h_mem_orth

  have h_q_in_line : q ∈ (ℓ' : Set Point2) := by
    have h8 : (q - base) +ᵥ base ∈ (ℓ' : Set Point2) :=
      AffineSubspace.vadd_mem_of_mem_direction h7 hℓ'_base
    have h9 : (q - base) +ᵥ base = q := by
      simp
    rw [h9] at h8
    exact h8

  have h_final : dist p q < 13 * r := by
    rw [h_q_dist] <;> exact h_bound
  simpa [Metric.mem_thickening_iff] using ⟨q, h_q_in_line, h_final⟩

end Kakeya.Assouad
