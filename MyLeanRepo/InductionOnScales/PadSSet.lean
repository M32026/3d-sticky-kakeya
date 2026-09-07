module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.SSet
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Padding an SSet family to a larger cardinality

Given an SSet family F of size M and N ≥ M, construct G ⊇ F of size N
that is also an SSet with the same constant C, by adding tubes far away
in the intercept direction.

## Proof approach

Add tubes one at a time, each very far from the existing family.
For a ball of radius r:
- If r < d/2 (d = min distance to new tube): ball intersects at most one of
  the old family or the new tube. Frostman follows from old family's bound
  or the trivial bound 1 ≤ C·r^s·(|G|+1).
- If r ≥ d/2: ball contains at most |G|+1 tubes, and C·r^s ≥ 1 by choice of d.
-/

open scoped BigOperators

namespace InductionOnScales

/-- Add one tube far from an SSet family while preserving the SSet property. -/
lemma add_one_tube_preserves_sset {n : ℕ} {s C : ℝ} {G : Finset (DyadicTube n)}
    (hG : IsFiniteTubeSSet s C G) :
    ∃ (U : DyadicTube n), U ∉ G ∧ IsFiniteTubeSSet s C (G ∪ {U}) := by
  rcases hG with ⟨hG_nonempty, hC_one, hs, h_sep_G, h_frost_G⟩
  set δ := dyadicDelta n with hδ_def
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_nonneg : 0 ≤ δ := hδ_pos.le
  have hδ_le_one : δ ≤ 1 := by
    rw [hδ_def, dyadicDelta]
    have h1 : (-(n : ℝ)) ≤ 0 := by simp
    have h2 : Real.rpow 2 (-(n : ℝ)) ≤ Real.rpow 2 0 :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    simpa using h2
  have hC_pos : 0 < C := by linarith
  set N' := G.card with hN'_def
  have hN'_pos : 0 < N' := hG_nonempty.card_pos

  -- From G's Frostman at r = δ: 1 ≤ C * δ^s * N'
  have h_frost_delta : (1 : ℝ) ≤ C * Real.rpow δ s * (N' : ℝ) := by
    rcases hG_nonempty with ⟨T0, hT0⟩
    have h1 : T0 ∈ G.filter (fun T => tubeParamDist T T0 ≤ δ) := by
      rw [Finset.mem_filter]
      exact ⟨hT0, by simp [tubeParamDist, hδ_nonneg]⟩
    have h2 : 0 < (G.filter (fun T => tubeParamDist T T0 ≤ δ)).card :=
      Finset.card_pos.mpr ⟨T0, h1⟩
    have h3 := h_frost_G T0 δ (by linarith [hδ_pos])
    have h4 : ((G.filter (fun T => tubeParamDist T T0 ≤ δ)).card : ℝ) ≤
        C * Real.rpow δ s * (N' : ℝ) := h3
    have h5 : (1 : ℝ) ≤ ((G.filter (fun T => tubeParamDist T T0 ≤ δ)).card : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr h2)
    exact h5.trans h4

  -- Choose a0 > all slope indices in G
  let a_image := G.image (fun T => T.a)
  have ha_img_nonempty : a_image.Nonempty := Finset.Nonempty.image hG_nonempty _
  let max_a : ℤ := Finset.max' a_image ha_img_nonempty
  let a0 : ℤ := max_a + 1
  have ha0_gt : ∀ T ∈ G, a0 > T.a := by
    intro T hT
    have h1 : T.a ∈ a_image := Finset.mem_image.mpr ⟨T, hT, rfl⟩
    have h2 : T.a ≤ max_a := Finset.le_max' a_image (T.a) h1
    simp [a0, max_a] at h2 ⊢ <;> omega

  -- Choose b0 far from all intercepts in G
  let b_image := G.image (fun T => T.b)
  have hb_img_nonempty : b_image.Nonempty := Finset.Nonempty.image hG_nonempty _
  let max_b : ℤ := Finset.max' b_image hb_img_nonempty

  -- d: threshold distance. Need C * (d/2)^s ≥ 1 and δ ≤ d.
  let d : ℝ := if s = 0 then (1 : ℝ) else max δ (2 * Real.rpow C (-1 / s))
  have hd_pos : 0 < d := by
    dsimp only [d]
    split_ifs with hs0
    · norm_num
    · have h1 : 0 < δ := hδ_pos
      positivity
  have hδ_le_d : δ ≤ d := by
    dsimp only [d]
    split_ifs with hs0
    · exact hδ_le_one
    · exact le_max_left _ _
  have h_C_d2 : 1 ≤ C * Real.rpow (d / 2) s := by
    by_cases hs0 : s = 0
    · rw [hs0]
      have h9 : Real.rpow (d / 2) 0 = 1 := by simp [hd_pos.ne']
      rw [h9] <;> linarith
    · have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
      have h_ge : d / 2 ≥ Real.rpow C (-1 / s) := by
        dsimp only [d]
        rw [if_neg hs0]
        have h_max : 2 * Real.rpow C (-1 / s) ≤ max δ (2 * Real.rpow C (-1 / s)) :=
          le_max_right _ _
        linarith
      have h_pos_base : 0 ≤ Real.rpow C (-1 / s) := Real.rpow_nonneg (by linarith [hC_pos]) _
      have h2 : Real.rpow (Real.rpow C (-1 / s)) s ≤ Real.rpow (d / 2) s :=
        Real.rpow_le_rpow h_pos_base h_ge hs
      have h3 : Real.rpow (Real.rpow C (-1 / s)) s = Real.rpow C ((-1 / s) * s) :=
        (Real.rpow_mul (by linarith) (-1 / s) s).symm
      have h4 : (-1 / s) * s = -1 := by field_simp [hs_pos.ne'] <;> ring
      have h5 : Real.rpow C ((-1 / s) * s) = Real.rpow C (-1 : ℝ) := by rw [h4]
      have h6 : Real.rpow C (-1 : ℝ) = 1 / C := by
        have h61 : Real.rpow C (-1 : ℝ) = (Real.rpow C 1)⁻¹ :=
          Real.rpow_neg (show 0 ≤ C from by linarith [hC_pos]) (1 : ℝ)
        rw [h61]
        have h62 : Real.rpow C 1 = C := by simp
        rw [h62] <;> field_simp [hC_pos.ne']
      have h7 : Real.rpow (d / 2) s ≥ 1 / C := by
        calc Real.rpow (d / 2) s
          ≥ Real.rpow (Real.rpow C (-1 / s)) s := h2
        _ = Real.rpow C ((-1 / s) * s) := h3
        _ = Real.rpow C (-1 : ℝ) := h5
        _ = 1 / C := h6
      have h8 : C * Real.rpow (d / 2) s ≥ 1 := by
        calc C * Real.rpow (d / 2) s
          ≥ C * (1 / C) := by gcongr
        _ = 1 := by field_simp [hC_pos.ne'] <;> linarith
      exact h8

  -- R_idx such that R_idx * δ > d
  have h_exists_R : ∃ (R : ℕ), (R : ℝ) * δ > d := by
    obtain ⟨R, hR⟩ := exists_nat_gt (d / δ)
    refine ⟨R, ?_⟩
    have h9 : (R : ℝ) > d / δ := by exact_mod_cast hR
    have h10 : (R : ℝ) * δ > (d / δ) * δ := by gcongr
    have h11 : (d / δ) * δ = d := by
      field_simp [hδ_pos.ne'] <;> ring
    rw [h11] at h10
    exact h10
  rcases h_exists_R with ⟨R_idx, hR_gt⟩

  let b0 : ℤ := max_b + R_idx + 1
  let U : DyadicTube n := ⟨a0, b0⟩

  -- Symmetry of tubeParamDist
  have h_symm : ∀ (A B : DyadicTube n), tubeParamDist A B = tubeParamDist B A := by
    intro A B
    unfold tubeParamDist
    have h1 : |A.slope - B.slope| = |B.slope - A.slope| := by
      rw [show A.slope - B.slope = -(B.slope - A.slope) by ring, abs_neg]
    have h2 : |A.intercept - B.intercept| = |B.intercept - A.intercept| := by
      rw [show A.intercept - B.intercept = -(B.intercept - A.intercept) by ring, abs_neg]
    rw [h1, h2]

  -- Distance from U to any T ∈ G is > d
  have h_dist_gt : ∀ T ∈ G, tubeParamDist T U > d := by
    intro T hT
    have h1 : tubeParamDist T U ≥ |T.intercept - U.intercept| := le_max_right _ _
    have h2 : T.b ≤ max_b := by
      have h3 : T.b ∈ b_image := Finset.mem_image.mpr ⟨T, hT, rfl⟩
      exact Finset.le_max' b_image (T.b) h3
    have h4 : (b0 : ℝ) - (T.b : ℝ) ≥ (R_idx + 1 : ℝ) := by
      simp [b0, max_b] at h2 ⊢ <;> norm_cast <;> omega
    have h5 : |T.intercept - U.intercept| = ((b0 : ℝ) - (T.b : ℝ)) * δ := by
      have h6 : T.intercept - U.intercept = ((T.b : ℝ) - (b0 : ℝ)) * δ := by
        simp [U, DyadicTube.intercept, hδ_def] <;> ring
      rw [h6]
      have h7 : (T.b : ℝ) ≤ (b0 : ℝ) := by linarith
      have h8 : |((T.b : ℝ) - (b0 : ℝ)) * δ| = ((b0 : ℝ) - (T.b : ℝ)) * δ := by
        rw [abs_mul, abs_of_nonpos (show (T.b : ℝ) - (b0 : ℝ) ≤ 0 by linarith),
          abs_of_pos hδ_pos] <;> ring
      exact h8
    rw [h5] at h1
    have h6 : ((b0 : ℝ) - (T.b : ℝ)) * δ ≥ (R_idx + 1 : ℝ) * δ := by gcongr
    have h7 : (R_idx + 1 : ℝ) * δ > d := by
      have h8 : (R_idx + 1 : ℝ) * δ = (R_idx : ℝ) * δ + δ := by ring
      rw [h8]
      linarith [hR_gt, hδ_pos]
    linarith

  have hU_notin_G : U ∉ G := by
    intro hU
    have h9 : tubeParamDist U U > d := h_dist_gt U hU
    simp [tubeParamDist] at h9 <;> linarith

  let G' := G ∪ {U}
  have hG'_card : G'.card = N' + 1 := by
    rw [Finset.card_union_of_disjoint (show Disjoint G ({U} : Finset (DyadicTube n)) from by
      simpa [Finset.disjoint_singleton] using hU_notin_G)]
    <;> simp [hN'_def] <;> ring

  -- Separation for G'
  have h_sep_G' : ∀ T ∈ G', ∀ V ∈ G', T ≠ V → δ ≤ tubeParamDist T V := by
    intro T hT V hV hne
    have hT_G : T ∈ G ∨ T = U := by simp [G'] at hT ⊢ <;> tauto
    have hV_G : V ∈ G ∨ V = U := by simp [G'] at hV ⊢ <;> tauto
    rcases hT_G with (hT_G | rfl)
    · rcases hV_G with (hV_G | rfl)
      · exact h_sep_G T hT_G V hV_G hne
      · have h9 : d < tubeParamDist T U := h_dist_gt T hT_G
        have h10 : δ ≤ d := hδ_le_d
        linarith
    · rcases hV_G with (hV_G | rfl)
      · have h9 : tubeParamDist V U > d := h_dist_gt V hV_G
        have h10 : tubeParamDist U V = tubeParamDist V U := h_symm U V
        have h11 : d < tubeParamDist U V := by rw [h10]; exact h9
        have h12 : δ ≤ d := hδ_le_d
        linarith
      · contradiction

  -- Frostman for G'
  have h_frost_G' : ∀ (center : DyadicTube n) (r : ℝ), δ ≤ r →
      ((G'.filter fun T => tubeParamDist T center ≤ r).card : ℝ) ≤
        C * Real.rpow r s * (G'.card : ℝ) := by
    intro center r hr
    set B_all := G'.filter (fun T => tubeParamDist T center ≤ r) with hB_def
    set B_G := G.filter (fun T => tubeParamDist T center ≤ r) with hBG_def
    have hU_notin_BG : U ∉ B_G := by
      intro h
      have h' : U ∈ G := (Finset.mem_filter.mp h).1
      exact hU_notin_G h'
    by_cases hU_in : tubeParamDist U center ≤ r
    · -- U in ball: B_all = B_G ∪ {U}
      have h1 : B_all = B_G ∪ {U} := by
        ext x
        have h_iff : x ∈ B_all ↔ x ∈ B_G ∪ {U} := by
          simp only [hB_def, hBG_def, Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
          constructor
          · rintro ⟨h_x_in_G', h_dist⟩
            have h_x : x ∈ G ∨ x = U := by
              have h : x = U ∨ x ∈ G := by simpa [G'] using h_x_in_G'
              rcases h with (h | h)
              · exact Or.inr h
              · exact Or.inl h
            rcases h_x with (h_x | rfl)
            · left; exact ⟨h_x, h_dist⟩
            · right; rfl
          · rintro (h | rfl)
            · exact ⟨by simp [G', h], h.2⟩
            · exact ⟨by simp [G'], hU_in⟩
        exact h_iff
      rw [h1]
      have h_disj : Disjoint B_G ({U} : Finset (DyadicTube n)) := by
        simpa [Finset.disjoint_singleton] using hU_notin_BG
      have h_card : ((B_G ∪ {U}).card : ℝ) = (B_G.card : ℝ) + 1 := by
        rw [Finset.card_union_of_disjoint h_disj] <;> simp <;> norm_cast
      rw [h_card]
      by_cases h_case : r < d / 2
      · -- r < d/2: ball can't contain both U and any G tube
        have hBG_empty : B_G = ∅ := by
          by_contra h
          have h3 : B_G.Nonempty := Finset.nonempty_iff_ne_empty.mpr h
          rcases h3 with ⟨T, hT⟩
          have hT_G : T ∈ G := (Finset.mem_filter.mp hT).1
          have hT_in : tubeParamDist T center ≤ r := (Finset.mem_filter.mp hT).2
          have h_dist : tubeParamDist T U ≤ tubeParamDist T center + tubeParamDist center U :=
            tubeParamDist_triangle T U center
          have h_comm : tubeParamDist center U = tubeParamDist U center := h_symm center U
          rw [h_comm] at h_dist
          have h9 : tubeParamDist T U ≤ 2 * r := by linarith
          have h10 : tubeParamDist T U > d := h_dist_gt T hT_G
          linarith
        rw [hBG_empty] <;> simp
        have h11 : (1 : ℝ) ≤ C * Real.rpow r s * (G'.card : ℝ) := by
          have h12 : Real.rpow δ s ≤ Real.rpow r s :=
            Real.rpow_le_rpow hδ_nonneg hr hs
          have hr_pos : 0 < r := lt_of_lt_of_le hδ_pos hr
          have h_rpow_pos : 0 < Real.rpow r s := Real.rpow_pos_of_pos hr_pos _
          have h_pos : 0 ≤ C * Real.rpow r s := mul_nonneg (by linarith [hC_pos]) h_rpow_pos.le
          have h13 : (G'.card : ℝ) = ((N' + 1 : ℕ) : ℝ) := by
            rw [hG'_card] <;> norm_cast
          rw [h13]
          have h14 : (1 : ℝ) ≤ C * Real.rpow δ s * (N' : ℝ) := h_frost_delta
          have h15 : C * Real.rpow δ s * (N' : ℝ) ≤ C * Real.rpow r s * (N' : ℝ) := by
            gcongr
          have h16 : (N' : ℝ) ≤ ((N' + 1 : ℕ) : ℝ) := by
            simp [Nat.cast_add] <;> linarith
          have h17 : C * Real.rpow r s * (N' : ℝ) ≤ C * Real.rpow r s * ((N' + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left h16 h_pos
          exact h14.trans (h15.trans h17)
        exact h11
      · -- r ≥ d/2: C * r^s ≥ 1
        have h_ge : d / 2 ≤ r := by linarith
        have h_d2_nonneg : 0 ≤ d / 2 := by linarith [hd_pos]
        have h2 : Real.rpow (d / 2) s ≤ Real.rpow r s :=
          Real.rpow_le_rpow h_d2_nonneg h_ge hs
        have hr_pos : 0 < r := lt_of_lt_of_le hδ_pos hr
        have h_rpow_pos : 0 < Real.rpow r s := Real.rpow_pos_of_pos hr_pos _
        have h_pos : 0 ≤ C * Real.rpow r s := mul_nonneg (by linarith [hC_pos]) h_rpow_pos.le
        have h_C_r : 1 ≤ C * Real.rpow r s := by
          have h3 : C * Real.rpow (d / 2) s ≤ C * Real.rpow r s := by gcongr
          exact le_trans h_C_d2 h3
        have h4 : (B_G.card : ℝ) ≤ C * Real.rpow r s * (N' : ℝ) := h_frost_G center r hr
        have h5 : (1 : ℝ) ≤ C * Real.rpow r s := h_C_r
        have h6 : (B_G.card : ℝ) + 1 ≤ C * Real.rpow r s * (N' : ℝ) + C * Real.rpow r s := by
          exact add_le_add h4 h5
        have h7 : C * Real.rpow r s * (N' : ℝ) + C * Real.rpow r s =
            C * Real.rpow r s * ((N' + 1 : ℕ) : ℝ) := by
          simp [mul_add] <;> ring_nf <;> norm_cast <;> ring
        rw [h7] at h6
        have h8 : (G'.card : ℝ) = ((N' + 1 : ℕ) : ℝ) := by
          rw [hG'_card] <;> norm_cast
        rw [h8]
        exact h6
    · -- U not in ball: B_all = B_G
      have h1 : B_all = B_G := by
        ext x
        have h_iff : x ∈ B_all ↔ x ∈ B_G := by
          simp only [hB_def, hBG_def, Finset.mem_filter]
          constructor
          · rintro ⟨h_x_in_G', h_dist⟩
            have h_x : x ∈ G ∨ x = U := by
              have h : x = U ∨ x ∈ G := by simpa [G'] using h_x_in_G'
              rcases h with (h | h)
              · exact Or.inr h
              · exact Or.inl h
            rcases h_x with (h_x | rfl)
            · exact ⟨h_x, h_dist⟩
            · exfalso; exact hU_in h_dist
          · rintro ⟨h_x, h_dist⟩
            have h_x' : x ∈ G ∪ ({U} : Finset (DyadicTube n)) := by
              simp [G', h_x]
            exact ⟨by simpa [G'] using h_x', h_dist⟩
        exact h_iff
      rw [h1]
      have h4 : (B_G.card : ℝ) ≤ C * Real.rpow r s * (N' : ℝ) := h_frost_G center r hr
      have h5 : (N' : ℝ) ≤ (G'.card : ℝ) := by
        rw [hG'_card] <;> simp [Nat.cast_add] <;> linarith
      have hr_pos : 0 < r := lt_of_lt_of_le hδ_pos hr
      have h_rpow_pos : 0 < Real.rpow r s := Real.rpow_pos_of_pos hr_pos _
      have h_pos : 0 ≤ C * Real.rpow r s := mul_nonneg (by linarith [hC_pos]) h_rpow_pos.le
      have h6 : C * Real.rpow r s * (N' : ℝ) ≤ C * Real.rpow r s * (G'.card : ℝ) :=
        mul_le_mul_of_nonneg_left h5 h_pos
      exact h4.trans h6

  have hG'_nonempty : G'.Nonempty := by
    exact hG_nonempty.mono (show G ⊆ G' from by simp [G'])

  refine ⟨U, hU_notin_G, ?_⟩
  exact ⟨hG'_nonempty, hC_one, hs, h_sep_G', h_frost_G'⟩

/-- Helper: pad by k tubes. -/
lemma pad_by_k {n : ℕ} {s C : ℝ} {F : Finset (DyadicTube n)}
    (hF : IsFiniteTubeSSet s C F) :
    ∀ (k : ℕ), ∃ (G : Finset (DyadicTube n)),
      F ⊆ G ∧ G.card = F.card + k ∧ IsFiniteTubeSSet s C G
  | 0 => ⟨F, by simp, by simp, hF⟩
  | k + 1 => by
    rcases pad_by_k hF k with ⟨G, hFG, hG_card, hG_sset⟩
    rcases add_one_tube_preserves_sset hG_sset with ⟨U, hU_notin, hU_sset⟩
    refine ⟨G ∪ {U}, ?_, ?_, hU_sset⟩
    · exact Finset.Subset.trans hFG (by simp)
    · have h_disj : Disjoint G ({U} : Finset (DyadicTube n)) := by
        simpa [Finset.disjoint_singleton] using hU_notin
      rw [Finset.card_union_of_disjoint h_disj, hG_card]
      <;> simp [Nat.add_assoc] <;> ring

/-- Pad an SSet family to a larger cardinality by adding spread-out tubes. -/
lemma pad_sset_family {n : ℕ} {s C : ℝ} {F : Finset (DyadicTube n)}
    (hF : IsFiniteTubeSSet s C F) (N : ℕ) (hN : F.card ≤ N) :
    ∃ (G : Finset (DyadicTube n)), F ⊆ G ∧ G.card = N ∧
      IsFiniteTubeSSet s C G := by
  let K := N - F.card
  have hNK : N = F.card + K := by omega
  rcases pad_by_k hF K with ⟨G, hFG, hG_card, hG_sset⟩
  have hN_card : G.card = N := by
    rw [hG_card, hNK]
  exact ⟨G, hFG, hN_card, hG_sset⟩

end InductionOnScales
