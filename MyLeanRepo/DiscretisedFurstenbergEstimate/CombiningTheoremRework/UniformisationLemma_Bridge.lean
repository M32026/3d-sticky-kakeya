module

/-
  Bridge lemmas for TailUniformisationConsumer.

  Connects dyadicSquareCount of setFromIndices sets intersected with
  coarse dyadic squares to cardinalities of filtered parentBy images.

  Whiteprint node: combining_theorem_rework / tail_bridge
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.BasicUniformization
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformisationLemma
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.OSUniformisation

open BasicUniformization


/-! Bridge from dyadicSquareCount to filtered index counts.

These lemmas connect `dyadicSquareCount` of a `setFromIndices` set
intersected with a coarse dyadic square, to the cardinality of a
filtered `parentBy` image of the index finset. -/

/-- Helper: if `c * b ≤ a < (c+1) * b` for `b > 0`, then `a / b = c`. -/
lemma int_ediv_eq_of_bounds {a b c : ℤ} (hb : 0 < b)
    (h1 : c * b ≤ a) (h2 : a < (c + 1) * b) : a / b = c := by
  have hne : b ≠ 0 := ne_of_gt hb
  have h3 : (a / b) * b ≤ a := Int.ediv_mul_le a hne
  have h4 : a % b + (a / b) * b = a := Int.emod_add_ediv_mul a b
  have h5 : 0 ≤ a % b := Int.emod_nonneg a hne
  have h6 : a % b < b := Int.emod_lt_of_pos a hb
  have h7 : a < ((a / b) + 1) * b := by
    calc a
      = a % b + (a / b) * b := h4.symm
    _ < b + (a / b) * b := by linarith
    _ = ((a / b) + 1) * b := by ring
  have h_le1 : c ≤ a / b := by
    by_contra h
    have h' : a / b < c := by omega
    have h'' : (a / b + 1) * b ≤ c * b := by gcongr <;> omega
    linarith
  have h_le2 : a / b ≤ c := by
    by_contra h
    have h' : c < a / b := by omega
    have h'' : (c + 1) * b ≤ (a / b) * b := by gcongr <;> omega
    linarith
  omega

/-- Scale relation: `dyadicDelta (n - m) = 2^m * dyadicDelta n`. -/
lemma dyadicDelta_scale {n m : ℕ} (hm : m ≤ n) :
    dyadicDelta (n - m) = (2^m : ℝ) * dyadicDelta n := by
  dsimp only [dyadicDelta]
  have h_sum : (n - m : ℕ) + m = n := by omega
  have h2 : (2 : ℝ) ^ m * (2 : ℝ) ^ (n - m) = (2 : ℝ) ^ n := by
    have h_comm : m + (n - m) = n := by omega
    rw [← pow_add, h_comm] <;> ring
  calc
    (1 : ℝ) / (2 : ℝ) ^ (n - m)
      = (2 : ℝ) ^ m * ((1 : ℝ) / ((2 : ℝ) ^ m * (2 : ℝ) ^ (n - m))) := by
        field_simp <;> ring
    _ = (2 : ℝ) ^ m * ((1 : ℝ) / (2 : ℝ) ^ n) := by rw [h2]

/-- A δ-dyadic square is contained in its parentBy-m dyadic square. -/
lemma dyadicSquare_parentBy_subset {nδ m : ℕ} (hm : m ≤ nδ)
    (idx : ℤ × ℤ) :
    dyadicSquare (dyadicDelta nδ) idx.1 idx.2 ⊆
    dyadicSquare (dyadicDelta (nδ - m))
      (BasicUniformization.parentBy m idx).1
      (BasicUniformization.parentBy m idx).2 := by
  let δ := dyadicDelta nδ
  let δ' := dyadicDelta (nδ - m)
  have hδ_pos : 0 < δ := dyadicDelta_pos nδ
  have h_scale : δ' = (2^m : ℝ) * δ := dyadicDelta_scale hm
  let p := BasicUniformization.parentBy m idx
  have h_pos : 0 < (2^m : ℤ) := by positivity
  have hne : (2^m : ℤ) ≠ 0 := by positivity
  have h1 : p.1 * (2^m : ℤ) ≤ idx.1 := Int.ediv_mul_le idx.1 hne
  have h2 : idx.1 < (p.1 + 1) * (2^m : ℤ) := by
    have h_rem : idx.1 % (2^m : ℤ) < (2^m : ℤ) := Int.emod_lt_of_pos idx.1 h_pos
    have h_eq : idx.1 % (2^m : ℤ) + p.1 * (2^m : ℤ) = idx.1 := by
      simp [p, BasicUniformization.parentBy] <;> exact Int.emod_add_ediv_mul idx.1 (2 ^ m)
    linarith
  have h3 : p.2 * (2^m : ℤ) ≤ idx.2 := Int.ediv_mul_le idx.2 hne
  have h4 : idx.2 < (p.2 + 1) * (2^m : ℤ) := by
    have h_rem : idx.2 % (2^m : ℤ) < (2^m : ℤ) := Int.emod_lt_of_pos idx.2 h_pos
    have h_eq : idx.2 % (2^m : ℤ) + p.2 * (2^m : ℤ) = idx.2 := by
      simp [p, BasicUniformization.parentBy] <;> exact Int.emod_add_ediv_mul idx.2 (2 ^ m)
    linarith
  intro x hx
  simp only [dyadicSquare, Set.mem_setOf_eq] at hx ⊢
  constructor
  · constructor
    · calc (p.1 : ℝ) * δ'
        = (p.1 : ℝ) * ((2^m : ℝ) * δ) := by rw [h_scale]
      _ = ((p.1 : ℝ) * (2^m : ℝ)) * δ := by ring
      _ ≤ (idx.1 : ℝ) * δ := by gcongr; exact_mod_cast h1
      _ ≤ x 0 := hx.1.1
    · calc x 0
        < (idx.1 + 1 : ℝ) * δ := hx.1.2
      _ ≤ ((p.1 + 1 : ℝ) * (2^m : ℝ)) * δ := by gcongr; exact_mod_cast h2
      _ = (p.1 + 1 : ℝ) * δ' := by rw [h_scale] <;> ring
  · constructor
    · calc (p.2 : ℝ) * δ'
        = (p.2 : ℝ) * ((2^m : ℝ) * δ) := by rw [h_scale]
      _ = ((p.2 : ℝ) * (2^m : ℝ)) * δ := by ring
      _ ≤ (idx.2 : ℝ) * δ := by gcongr; exact_mod_cast h3
      _ ≤ x 1 := hx.2.1
    · calc x 1
        < (idx.2 + 1 : ℝ) * δ := hx.2.2
      _ ≤ ((p.2 + 1 : ℝ) * (2^m : ℝ)) * δ := by gcongr; exact_mod_cast h4
      _ = (p.2 + 1 : ℝ) * δ' := by rw [h_scale] <;> ring

/-- If a fine dyadic square intersects a coarse dyadic square, then the
    coarse index is the `parentBy` of the fine index. -/
lemma dyadicSquare_inter_parentBy {nδ m : ℕ} (hm : m ≤ nδ)
    (idx p : ℤ × ℤ)
    (h : (dyadicSquare (dyadicDelta nδ) idx.1 idx.2 ∩
          dyadicSquare (dyadicDelta (nδ - m)) p.1 p.2).Nonempty) :
    BasicUniformization.parentBy m idx = p := by
  let δ := dyadicDelta nδ
  let δ' := dyadicDelta (nδ - m)
  have hδ_pos : 0 < δ := dyadicDelta_pos nδ
  have h_scale : δ' = (2^m : ℝ) * δ := dyadicDelta_scale hm
  rcases h with ⟨x, hx1, hx2⟩
  simp only [dyadicSquare, Set.mem_setOf_eq] at hx1 hx2
  have h_pos : 0 < (2^m : ℤ) := by positivity
  have h_i1 : (p.1 : ℤ) * (2^m : ℤ) ≤ idx.1 := by
    have h5 : (p.1 : ℝ) * δ' ≤ x 0 := hx2.1.1
    have h6 : x 0 < (idx.1 + 1 : ℝ) * δ := hx1.1.2
    rw [h_scale] at h5
    have h7 : (p.1 : ℝ) * ((2^m : ℝ) * δ) < (idx.1 + 1 : ℝ) * δ := by linarith
    have h8 : (p.1 : ℝ) * (2^m : ℝ) < (idx.1 + 1 : ℝ) := by nlinarith
    have h9 : (p.1 : ℤ) * (2^m : ℤ) < idx.1 + 1 := by exact_mod_cast h8
    omega
  have h_i2 : idx.1 < (p.1 + 1) * (2^m : ℤ) := by
    have h5 : (idx.1 : ℝ) * δ ≤ x 0 := hx1.1.1
    have h6 : x 0 < (p.1 + 1 : ℝ) * δ' := hx2.1.2
    rw [h_scale] at h6
    have h7 : (idx.1 : ℝ) * δ < (p.1 + 1 : ℝ) * ((2^m : ℝ) * δ) := by linarith
    have h8 : (idx.1 : ℝ) < (p.1 + 1 : ℝ) * (2^m : ℝ) := by nlinarith
    exact_mod_cast h8
  have h_eq1 : idx.1 / (2^m : ℤ) = p.1 :=
    int_ediv_eq_of_bounds h_pos h_i1 h_i2
  have h_j1 : (p.2 : ℤ) * (2^m : ℤ) ≤ idx.2 := by
    have h5 : (p.2 : ℝ) * δ' ≤ x 1 := hx2.2.1
    have h6 : x 1 < (idx.2 + 1 : ℝ) * δ := hx1.2.2
    rw [h_scale] at h5
    have h7 : (p.2 : ℝ) * ((2^m : ℝ) * δ) < (idx.2 + 1 : ℝ) * δ := by linarith
    have h8 : (p.2 : ℝ) * (2^m : ℝ) < (idx.2 + 1 : ℝ) := by nlinarith
    have h9 : (p.2 : ℤ) * (2^m : ℤ) < idx.2 + 1 := by exact_mod_cast h8
    omega
  have h_j2 : idx.2 < (p.2 + 1) * (2^m : ℤ) := by
    have h5 : (idx.2 : ℝ) * δ ≤ x 1 := hx1.2.1
    have h6 : x 1 < (p.2 + 1 : ℝ) * δ' := hx2.2.2
    rw [h_scale] at h6
    have h7 : (idx.2 : ℝ) * δ < (p.2 + 1 : ℝ) * ((2^m : ℝ) * δ) := by linarith
    have h8 : (idx.2 : ℝ) < (p.2 + 1 : ℝ) * (2^m : ℝ) := by nlinarith
    exact_mod_cast h8
  have h_eq2 : idx.2 / (2^m : ℤ) = p.2 :=
    int_ediv_eq_of_bounds h_pos h_j1 h_j2
  have h_main : BasicUniformization.parentBy m idx = p := by
    simp [BasicUniformization.parentBy, h_eq1, h_eq2]
    <;> exact Prod.ext h_eq1 h_eq2
  exact h_main

/-- Bridge lemma: `dyadicSquareCount` of a `setFromIndices` set intersected
    with a coarse dyadic square equals the cardinality of the filtered
    `parentBy` image. -/
lemma dyadicSquareCount_setFromIndices_inter
    (nδ a_fine a_coarse : ℕ)
    (h_coarse_le_fine : a_coarse ≤ a_fine)
    (h_fine_le_delta : a_fine ≤ nδ)
    (S : Finset (ℤ × ℤ)) (g : ℤ × ℤ) :
    dyadicSquareCount (dyadicDelta a_fine)
      (BasicUniformization.setFromIndices (dyadicDelta nδ) S ∩
       dyadicSquare (dyadicDelta a_coarse) g.1 g.2) =
    ↑((S.image (BasicUniformization.parentBy (nδ - a_fine))).filter
      (fun idx => BasicUniformization.parentBy (a_fine - a_coarse) idx = g)).card := by
  let m1 := nδ - a_fine
  let m2 := a_fine - a_coarse
  let fineImg := S.image (BasicUniformization.parentBy m1)
  let filtered := fineImg.filter (fun idx => BasicUniformization.parentBy m2 idx = g)
  let A := BasicUniformization.setFromIndices (dyadicDelta nδ) S ∩
           dyadicSquare (dyadicDelta a_coarse) g.1 g.2
  have h_m1m2 : m1 + m2 = nδ - a_coarse := by omega
  have h_set_eq : {p : ℤ × ℤ | (A ∩ dyadicSquare (dyadicDelta a_fine) p.1 p.2).Nonempty} = ↑filtered := by
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · -- Forward: intersection nonempty → p in filtered image
      rintro ⟨x, hxA, hx_fine⟩
      have hx_in_union : x ∈ BasicUniformization.setFromIndices (dyadicDelta nδ) S := hxA.1
      rcases Set.mem_iUnion₂.mp hx_in_union with ⟨idx, hidx, hx_square⟩
      have hx_coarse : x ∈ dyadicSquare (dyadicDelta a_coarse) g.1 g.2 := hxA.2
      have h_m1_le : m1 ≤ nδ := by omega
      have h1 : nδ - m1 = a_fine := by omega
      have h_parent1 : BasicUniformization.parentBy m1 idx = p := by
        have h_inter : (dyadicSquare (dyadicDelta nδ) idx.1 idx.2 ∩
                        dyadicSquare (dyadicDelta a_fine) p.1 p.2).Nonempty :=
          ⟨x, hx_square, hx_fine⟩
        have h_inter' : (dyadicSquare (dyadicDelta nδ) idx.1 idx.2 ∩
                        dyadicSquare (dyadicDelta (nδ - m1)) p.1 p.2).Nonempty := by
          simpa [h1] using h_inter
        exact dyadicSquare_inter_parentBy h_m1_le idx p h_inter'
      have h_parent_total : BasicUniformization.parentBy (m1 + m2) idx = g := by
        have h_inter2 : (dyadicSquare (dyadicDelta nδ) idx.1 idx.2 ∩
                         dyadicSquare (dyadicDelta a_coarse) g.1 g.2).Nonempty :=
          ⟨x, hx_square, hx_coarse⟩
        have h_le : m1 + m2 ≤ nδ := by omega
        have h_rewrite : nδ - (m1 + m2) = a_coarse := by omega
        have h_inter2' : (dyadicSquare (dyadicDelta nδ) idx.1 idx.2 ∩
                         dyadicSquare (dyadicDelta (nδ - (m1 + m2))) g.1 g.2).Nonempty := by
          simpa [h_rewrite] using h_inter2
        exact dyadicSquare_inter_parentBy h_le idx g h_inter2'
      have h_parent2 : BasicUniformization.parentBy m2 p = g := by
        have h_comp : BasicUniformization.parentBy m2 (BasicUniformization.parentBy m1 idx) =
            BasicUniformization.parentBy (m1 + m2) idx := by
          have h := parentBy_comp m2 m1 idx
          rw [add_comm m2 m1] at h
          exact h
        rw [h_parent1] at h_comp
        exact h_comp.trans h_parent_total
      have h_in_img : p ∈ fineImg := Finset.mem_image.mpr ⟨idx, hidx, h_parent1⟩
      have h_p_in_filtered : p ∈ filtered := by
        rw [Finset.mem_filter]
        exact ⟨h_in_img, h_parent2⟩
      exact Finset.mem_coe.mpr h_p_in_filtered
    · -- Backward: p in filtered image → intersection nonempty
      intro h_p_in_coe
      have h_p_in_filtered : p ∈ filtered := Finset.mem_coe.mp h_p_in_coe
      rw [Finset.mem_filter] at h_p_in_filtered
      rcases h_p_in_filtered with ⟨h_in_img, h_parent2⟩
      rcases Finset.mem_image.mp h_in_img with ⟨idx, hidx, h_parent1⟩
      have h_parent_total : BasicUniformization.parentBy (m1 + m2) idx = g := by
        have h_comp : BasicUniformization.parentBy m2 (BasicUniformization.parentBy m1 idx) =
            BasicUniformization.parentBy (m1 + m2) idx := by
          have h := parentBy_comp m2 m1 idx
          rw [add_comm m2 m1] at h
          exact h
        rw [h_parent1] at h_comp
        exact h_comp.symm.trans h_parent2
      have hδ_pos : 0 < dyadicDelta nδ := dyadicDelta_pos nδ
      let x : EuclideanPlane :=
        WithLp.toLp (2 : ENNReal) fun k : Fin 2 =>
          if k = 0 then (idx.1 : ℝ) * dyadicDelta nδ else (idx.2 : ℝ) * dyadicDelta nδ
      have hx0 : x 0 = (idx.1 : ℝ) * dyadicDelta nδ := by
        simp [x, PiLp.toLp_apply] <;> norm_num
      have hx1 : x 1 = (idx.2 : ℝ) * dyadicDelta nδ := by
        simp [x, PiLp.toLp_apply] <;> norm_num
      have hx_square : x ∈ dyadicSquare (dyadicDelta nδ) idx.1 idx.2 := by
        simp only [dyadicSquare, Set.mem_setOf_eq]
        constructor
        · simp [Set.mem_Ico, hx0] <;> linarith
        · simp [Set.mem_Ico, hx1] <;> linarith
      have hx_in_union : x ∈ BasicUniformization.setFromIndices (dyadicDelta nδ) S :=
        Set.mem_iUnion₂.mpr ⟨idx, hidx, hx_square⟩
      have h1 : nδ - m1 = a_fine := by omega
      have h_m1_le : m1 ≤ nδ := by omega
      have hx_fine : x ∈ dyadicSquare (dyadicDelta a_fine) p.1 p.2 := by
        have h_sub : dyadicSquare (dyadicDelta nδ) idx.1 idx.2 ⊆
            dyadicSquare (dyadicDelta (nδ - m1))
              (BasicUniformization.parentBy m1 idx).1
              (BasicUniformization.parentBy m1 idx).2 :=
          dyadicSquare_parentBy_subset h_m1_le idx
        have h_goal : dyadicSquare (dyadicDelta nδ) idx.1 idx.2 ⊆
            dyadicSquare (dyadicDelta a_fine) p.1 p.2 := by
          simpa [h1, h_parent1] using h_sub
        exact h_goal hx_square
      have h2 : nδ - (m1 + m2) = a_coarse := by omega
      have h_le : m1 + m2 ≤ nδ := by omega
      have hx_coarse : x ∈ dyadicSquare (dyadicDelta a_coarse) g.1 g.2 := by
        have h_sub : dyadicSquare (dyadicDelta nδ) idx.1 idx.2 ⊆
            dyadicSquare (dyadicDelta (nδ - (m1 + m2)))
              (BasicUniformization.parentBy (m1 + m2) idx).1
              (BasicUniformization.parentBy (m1 + m2) idx).2 :=
          dyadicSquare_parentBy_subset h_le idx
        have h_goal : dyadicSquare (dyadicDelta nδ) idx.1 idx.2 ⊆
            dyadicSquare (dyadicDelta a_coarse) g.1 g.2 := by
          simpa [h2, h_parent_total] using h_sub
        exact h_goal hx_square
      exact ⟨x, ⟨hx_in_union, hx_coarse⟩, hx_fine⟩
  have h_main : dyadicSquareCount (dyadicDelta a_fine) A =
      Set.encard {p : ℤ × ℤ | (A ∩ dyadicSquare (dyadicDelta a_fine) p.1 p.2).Nonempty} := by
    rfl
  rw [h_main, h_set_eq]
  rw [Set.encard_coe_eq_coe_finsetCard]

end DiscretisedFurstenbergEstimate.OSUniformisation
