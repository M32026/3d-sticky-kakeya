module

/-
  Derive the good product bound from OS equation (90).

  Given the multiscale decomposition data, prove:
    ∏_{good scales} ratio^η ≥ δ_d^(-ε_G * η / 8)

  The derivation:
  1. Total product ∏_{all} ratio = 1/δ_d
  2. Normal scales have t_j < t - ε_G/2, so their contribution to h_S_product
     is at most δ_d^(-(t - ε_G/2))
  3. Good scales have t_j ≤ 2, so (∏_{good} ratio)^2 ≥ ∏_{good} ratio^(t_j)
  4. Therefore ∏_{good} ratio ≥ δ_d^(ε_bad/2 - ε_G/4) ≥ δ_d^(-ε_G/8)
     (since ε_bad ≤ ε_G/4)
  5. Raising to η: ∏_{good} ratio^η ≥ δ_d^(-ε_G*η/8)

  Whiteprint node: section9 / good_product_bound
  Status: DRAFT
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

/-- Derive the good product bound from the decomposition data. -/
lemma good_product_bound
    (δ_d : ℝ) (hδ_d_pos : 0 < δ_d) (hδ_d_lt_one : δ_d < 1)
    (s t ε_G ε_bad η : ℝ)
    (hs : 0 < s) (hst : s < t) (hεG_pos : 0 < ε_G) (hε_bad_pos : 0 < ε_bad)
    (hη_nonneg : 0 ≤ η)
    (hεG_small : ε_G < 2 * (t - s))
    (hε_bad_le : ε_bad ≤ ε_G / 4)
    {n : ℕ}
    (ratio : Fin n → ℝ)
    (h_ratio_gt_one : ∀ j, 1 < ratio j)
    -- Total product
    (h_total : ∏ j ∈ Finset.univ, ratio j = 1 / δ_d)
    -- S and B partition
    (S B : Finset (Fin n))
    (h_SB_univ : S ∪ B = Finset.univ)
    (h_SB_disj : Disjoint S B)
    -- t_j values
    (t_j : Fin n → ℝ)
    (h_tj_le_two : ∀ j ∈ S, t_j j ≤ 2)
    -- S product bound
    (h_S_prod : ∏ j ∈ S, (ratio j) ^ (t_j j) ≥ δ_d ^ (ε_bad - t))
    -- Good scales: t_j ≥ t - ε_G/2
    (G : Finset (Fin n))
    (hG_def : G = S.filter (fun j => t_j j ≥ t - ε_G / 2)) :
    (∏ j ∈ G, (ratio j) ^ η) ≥ δ_d ^ (-(ε_G * η / 8)) := by
  let N := S.filter (fun j => t_j j < t - ε_G / 2)

  have h_threshold_pos : 0 < t - ε_G / 2 := by linarith
  have h_ratio_pos : ∀ j, 0 < ratio j := by
    intro j; have h := h_ratio_gt_one j; linarith

  -- G and N partition S
  have hG_sub_S : G ⊆ S := by
    rw [hG_def]; exact Finset.filter_subset _ _
  have hN_sub_S : N ⊆ S := Finset.filter_subset _ _
  have h_partition : S = G ∪ N := by
    rw [hG_def]
    ext j
    simp only [N, Finset.mem_union, Finset.mem_filter]
    <;> constructor
    · intro h
      by_cases h2 : t_j j ≥ t - ε_G / 2
      · left; exact ⟨h, h2⟩
      · have h3 : t_j j < t - ε_G / 2 := by linarith
        right; exact ⟨h, h3⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have h_disj : Disjoint G N := by
    rw [hG_def]
    rw [Finset.disjoint_left]
    intro j hGj hNj
    have h4 : t_j j ≥ t - ε_G / 2 := (Finset.mem_filter.mp hGj).2
    have h5 : t_j j < t - ε_G / 2 := (Finset.mem_filter.mp hNj).2
    linarith

  -- Step 1: Bound normal product contribution
  -- ∏_{j∈N} ratio_j^(t_j) ≤ ∏_{j∈N} ratio_j^(t - ε_G/2)
  have h1 : ∏ j ∈ N, (ratio j) ^ (t_j j) ≤ ∏ j ∈ N, (ratio j) ^ (t - ε_G / 2) := by
    apply Finset.prod_le_prod
    · intro j _; exact Real.rpow_nonneg (by linarith [h_ratio_pos j]) _
    · intro j hj
      have h2 : t_j j < t - ε_G / 2 := (Finset.mem_filter.mp hj).2
      have h3 : 1 < ratio j := h_ratio_gt_one j
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

  -- ∏_{j∈N} ratio_j ≤ ∏_{all} ratio_j = 1/δ_d
  have hN_prod_le : ∏ j ∈ N, ratio j ≤ 1 / δ_d := by
    let D := (Finset.univ : Finset (Fin n)) \ N
    have h_disj : Disjoint N D := by
      simp only [D, Finset.disjoint_left, Finset.mem_sdiff, Finset.mem_univ, true_and]
      <;> tauto
    have h_union : N ∪ D = (Finset.univ : Finset (Fin n)) := by
      simp [D] <;> tauto
    have h3 : ∏ j ∈ Finset.univ, ratio j = (∏ j ∈ N, ratio j) * ∏ j ∈ D, ratio j := by
      rw [← Finset.prod_union h_disj, h_union]
    have h4 : 1 ≤ ∏ j ∈ D, ratio j := by
      have h5 : ∏ j ∈ D, (1 : ℝ) ≤ ∏ j ∈ D, ratio j :=
        Finset.prod_le_prod (fun j _ => by norm_num) (fun j _ => by linarith [h_ratio_gt_one j])
      simpa using h5
    have h6 : (∏ j ∈ N, ratio j) * ∏ j ∈ D, ratio j = 1 / δ_d := by
      rw [← h3, h_total]
    have h7 : 0 < ∏ j ∈ D, ratio j := by
      apply Finset.prod_pos
      intro j _; exact h_ratio_pos j
    have h8 : ((∏ j ∈ N, ratio j) * ∏ j ∈ D, ratio j) / ∏ j ∈ D, ratio j = ∏ j ∈ N, ratio j :=
      mul_div_cancel_right₀ _ h7.ne'
    have h9 : (1 / δ_d) / ∏ j ∈ D, ratio j ≤ 1 / δ_d := by
      have h10 : 0 < ∏ j ∈ D, ratio j := h7
      have h11 : 1 ≤ ∏ j ∈ D, ratio j := h4
      have h12 : 0 < 1 / δ_d := by positivity
      have h13 : (1 / δ_d) / ∏ j ∈ D, ratio j ≤ (1 / δ_d) / 1 := by
        apply div_le_div_of_nonneg_left h12.le
        <;> linarith
      simpa using h13
    calc ∏ j ∈ N, ratio j
      = ((∏ j ∈ N, ratio j) * ∏ j ∈ D, ratio j) / ∏ j ∈ D, ratio j := h8.symm
    _ = (1 / δ_d) / ∏ j ∈ D, ratio j := by rw [h6]
    _ ≤ 1 / δ_d := h9

  -- ∏_{j∈N} ratio_j^(t - ε_G/2) = (∏_{j∈N} ratio_j)^(t - ε_G/2)
  have h3 : ∏ j ∈ N, (ratio j) ^ (t - ε_G / 2) = (∏ j ∈ N, ratio j) ^ (t - ε_G / 2) :=
    Real.finsetProd_rpow N ratio (fun j _ => by linarith [h_ratio_pos j]) (t - ε_G / 2)

  -- (∏_{j∈N} ratio_j)^(t - ε_G/2) ≤ (1/δ_d)^(t - ε_G/2)
  have h4 : (∏ j ∈ N, ratio j) ^ (t - ε_G / 2) ≤ (1 / δ_d) ^ (t - ε_G / 2) := by
    have h5 : 0 ≤ ∏ j ∈ N, ratio j := by
      apply Finset.prod_nonneg; intro j _; linarith [h_ratio_pos j]
    exact Real.rpow_le_rpow h5 hN_prod_le (by linarith)

  have h5 : (1 / δ_d) ^ (t - ε_G / 2) = δ_d ^ (-(t - ε_G / 2)) := by
    have h6 : (1 / δ_d) = δ_d⁻¹ := by field_simp
    rw [h6]
    have h7 : (δ_d⁻¹) ^ (t - ε_G / 2) = (δ_d ^ (t - ε_G / 2))⁻¹ := by
      rw [Real.inv_rpow hδ_d_pos.le]
    rw [h7]
    have h8 : (δ_d ^ (t - ε_G / 2))⁻¹ = δ_d ^ (-(t - ε_G / 2)) := by
      rw [← Real.rpow_neg hδ_d_pos.le] <;> ring
    exact h8

  have h_normal_bound : ∏ j ∈ N, (ratio j) ^ (t_j j) ≤ δ_d ^ (-(t - ε_G / 2)) := by
    calc ∏ j ∈ N, (ratio j) ^ (t_j j)
      ≤ ∏ j ∈ N, (ratio j) ^ (t - ε_G / 2) := h1
    _ = (∏ j ∈ N, ratio j) ^ (t - ε_G / 2) := h3
    _ ≤ (1 / δ_d) ^ (t - ε_G / 2) := h4
    _ = δ_d ^ (-(t - ε_G / 2)) := h5

  -- Step 2: Split S product into G and N
  have h_S_split : ∏ j ∈ S, (ratio j) ^ (t_j j) =
      (∏ j ∈ G, (ratio j) ^ (t_j j)) * (∏ j ∈ N, (ratio j) ^ (t_j j)) := by
    rw [h_partition, Finset.prod_union h_disj]

  rw [h_S_split] at h_S_prod

  have h8_pos : 0 < ∏ j ∈ N, (ratio j) ^ (t_j j) := by
    apply Finset.prod_pos
    intro j _
    exact Real.rpow_pos_of_pos (h_ratio_pos j) (t_j j)

  -- ∏_{j∈G} ratio_j^(t_j) ≥ δ_d^(ε_bad - t) / δ_d^(-(t - ε_G/2))
  set A : ℝ := ∏ j ∈ G, (ratio j) ^ (t_j j) with hA_def
  set B : ℝ := ∏ j ∈ N, (ratio j) ^ (t_j j) with hB_def
  set Z : ℝ := δ_d ^ (ε_bad - t) with hZ_def
  set Y : ℝ := δ_d ^ (-(t - ε_G / 2)) with hY_def

  have hB_pos : 0 < B := by
    rw [hB_def]
    apply Finset.prod_pos
    intro j _
    exact Real.rpow_pos_of_pos (h_ratio_pos j) (t_j j)

  have h7 : A * B ≥ Z := by
    simpa [hA_def, hB_def, hZ_def] using h_S_prod

  have h9 : A ≥ Z / B := by
    have h10 : A = (A * B) / B := by
      field_simp [hB_pos.ne'] <;> ring
    rw [h10]
    gcongr

  have h11 : Z / B ≥ Z / Y := by
    have h12 : B ≤ Y := by
      simpa [hB_def, hY_def] using h_normal_bound
    have h13 : 0 < Z := by
      simp only [hZ_def]
      positivity
    gcongr

  have h6 : A ≥ Z / Y := by
    have h11' : Z / Y ≤ Z / B := h11
    have h9' : Z / B ≤ A := h9
    exact le_trans h11' h9'

  have h14 : Z / Y = δ_d ^ (ε_bad - ε_G / 2) := by
    simp only [hZ_def, hY_def]
    have h15 : δ_d ^ (ε_bad - t) / (δ_d ^ (-(t - ε_G / 2))) =
        δ_d ^ ((ε_bad - t) - (-(t - ε_G / 2))) := by
      rw [← Real.rpow_sub hδ_d_pos] <;> ring
    rw [h15] <;> ring_nf

  have h6' : A ≥ δ_d ^ (ε_bad - ε_G / 2) := by
    rw [h14] at h6
    exact h6

  -- Step 3: ∏_{j∈G} ratio_j^(t_j) ≤ (∏_{j∈G} ratio_j)^2 since t_j ≤ 2
  have h13 : ∏ j ∈ G, (ratio j) ^ (t_j j) ≤ (∏ j ∈ G, ratio j) ^ 2 := by
    have h14 : ∏ j ∈ G, (ratio j) ^ (t_j j) ≤ ∏ j ∈ G, (ratio j) ^ (2 : ℝ) := by
      apply Finset.prod_le_prod
      · intro j _; exact Real.rpow_nonneg (by linarith [h_ratio_pos j]) _
      · intro j hj
        have h15 : j ∈ S := hG_sub_S hj
        have h16 : t_j j ≤ 2 := h_tj_le_two j h15
        have h17 : 1 < ratio j := h_ratio_gt_one j
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h18 : ∏ j ∈ G, (ratio j) ^ (2 : ℝ) = (∏ j ∈ G, ratio j) ^ 2 := by
      rw [Real.finsetProd_rpow G ratio (fun j _ => by linarith [h_ratio_pos j]) (2 : ℝ)]
      <;> norm_cast
    rw [h18] at h14
    exact h14

  have h19 : (∏ j ∈ G, ratio j) ^ 2 ≥ δ_d ^ (ε_bad - ε_G / 2) := by
    calc (∏ j ∈ G, ratio j) ^ 2
      ≥ ∏ j ∈ G, (ratio j) ^ (t_j j) := h13
    _ ≥ δ_d ^ (ε_bad - ε_G / 2) := h6'

  -- Step 4: Take square root
  have h20 : 0 < ∏ j ∈ G, ratio j := by
    apply Finset.prod_pos
    intro j _; exact h_ratio_pos j

  set x : ℝ := ∏ j ∈ G, ratio j with hx_def
  set y : ℝ := δ_d ^ (ε_bad - ε_G / 2) with hy_def
  have hx_pos : 0 < x := h20
  have hy_nonneg : 0 ≤ y := by positivity
  have h19' : x ^ 2 ≥ y := h19
  have h_sqrt_y : Real.sqrt y = δ_d ^ ((ε_bad - ε_G / 2) / 2) := by
    have h23 : Real.sqrt y = y ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    rw [h23, hy_def]
    rw [← Real.rpow_mul hδ_d_pos.le] <;> ring_nf
  have h21 : x ≥ Real.sqrt y := by
    by_contra h24
    have h25 : x < Real.sqrt y := by linarith
    have h26 : 0 ≤ x := by linarith
    have h27 : x ^ 2 < (Real.sqrt y) ^ 2 := by nlinarith [Real.sqrt_nonneg y]
    have h28 : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy_nonneg
    rw [h28] at h27
    linarith
  rw [h_sqrt_y] at h21
  have h21' : x ≥ δ_d ^ ((ε_bad - ε_G / 2) / 2) := h21

  -- Step 5: ε_bad/2 - ε_G/4 ≤ -ε_G/8 (since ε_bad ≤ ε_G/4)
  have h28 : (ε_bad - ε_G / 2) / 2 ≤ -(ε_G / 8) := by linarith

  -- For δ_d < 1, smaller exponent → larger value
  have h29 : δ_d ^ ((ε_bad - ε_G / 2) / 2) ≥ δ_d ^ (-(ε_G / 8)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_d_pos (by linarith) h28

  have h30 : ∏ j ∈ G, ratio j ≥ δ_d ^ (-(ε_G / 8)) := by
    calc ∏ j ∈ G, ratio j
      ≥ δ_d ^ ((ε_bad - ε_G / 2) / 2) := h21'
    _ ≥ δ_d ^ (-(ε_G / 8)) := h29

  -- Step 6: Raise to η
  have h31 : (∏ j ∈ G, ratio j) ^ η ≥ (δ_d ^ (-(ε_G / 8))) ^ η := by
    have h32 : 0 ≤ ∏ j ∈ G, ratio j := by positivity
    have h33 : 0 ≤ δ_d ^ (-(ε_G / 8)) := by positivity
    gcongr

  have h34 : (δ_d ^ (-(ε_G / 8))) ^ η = δ_d ^ (-(ε_G * η / 8)) := by
    rw [← Real.rpow_mul hδ_d_pos.le] <;> ring_nf

  have h35 : (∏ j ∈ G, (ratio j) ^ η) = (∏ j ∈ G, ratio j) ^ η :=
    Real.finsetProd_rpow G ratio (fun j _ => by linarith [h_ratio_pos j]) η

  have h36 : (∏ j ∈ G, ratio j) ^ η ≥ δ_d ^ (-(ε_G * η / 8)) := by
    calc (∏ j ∈ G, ratio j) ^ η
      ≥ (δ_d ^ (-(ε_G / 8))) ^ η := h31
    _ = δ_d ^ (-(ε_G * η / 8)) := by
      rw [← Real.rpow_mul hδ_d_pos.le] <;> ring_nf

  rw [h35]
  exact h36

end DirecretisedFurstenbergEstimate.Section9
