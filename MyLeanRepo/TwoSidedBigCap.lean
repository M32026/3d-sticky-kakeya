module

/-
# Two-Sided Representative Big Intersection

Given coordinate families A_y, B_y with uniform product covering lower bounds,
select y_star and D' such that thickened intersections on BOTH sides are
simultaneously large.

## Proof route

1. Convert covering numbers to finite cube-index sets (ℤ).
2. Product index set: C(y) = IA(y) ×ˢ IB(y), ambient = IambA ×ˢ IambB.
3. Apply abstract graph lemma (weighted Cauchy-Schwarz + Markov) to get
   |C(y) ∩ C(y*)| ≥ α · |C(y*)| for y in a large-weight D'.
4. Counting argument: from |IA∩IA*| · |IB∩IB*| ≥ α · |IA*| · |IB*|
   and |IA∩IA*| ≤ |IA*|, |IB∩IB*| ≤ |IB*|, derive both
   |IA∩IA*| ≥ α · |IA*| and |IB∩IB*| ≥ α · |IB*|.
5. Geometric step: each shared 1D interval meets A_y ∩ thickening(√2δ, A_*),
   so Nreal(thickening ∩ A_y) ≥ |IA∩IA*| ≥ α · Nreal(A_*). Same for B.
-/

public import MyLeanRepo.DiscretizedPluennecke
public import MyLeanRepo.DiscretizedPluenneckeFull
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Finset Set Classical ENNReal Bornology

namespace GraphLemma

/-! ## Abstract graph lemma (weighted Cauchy-Schwarz + Markov) -/

lemma representative_big_intersection_graph_cubes
    {Cube : Type*} [DecidableEq Cube]
    {D : Finset ℝ} (hD_nonempty : D.Nonempty)
    {w : ℝ → ℝ} (hw_nonneg : ∀ y ∈ D, 0 ≤ w y)
    {W : ℝ} (hW_pos : 0 < W) (hW_sum : ∑ y ∈ D, w y = W)
    {ambientCubes : Finset Cube} {C : ℝ → Finset Cube}
    (hC_sub : ∀ y ∈ D, C y ⊆ ambientCubes)
    {c : ℝ} (hc_pos : 0 < c) (hc_le_one : c ≤ 1)
    (hC_lower : ∀ y ∈ D, ((C y).card : ℝ) ≥ c * (ambientCubes.card : ℝ))
    {α mass : ℝ} (hα_pos : 0 < α) (_ : 0 < mass)
    (hα_le : α ≤ c^3 / 32) (hmass_le : mass ≤ c^2 / 16) :
    ∃ (y_star : ℝ) (hy_star : y_star ∈ D) (D' : Finset ℝ),
      D' ⊆ D ∧
      (∑ y ∈ D', w y) ≥ mass * W ∧
      ∀ y ∈ D', ((C y ∩ C y_star).card : ℝ) ≥ α * ((C y_star).card : ℝ) := by
  let n : ℕ := ambientCubes.card
  by_cases hn : n = 0
  · have h_amb_empty : ambientCubes = ∅ := Finset.card_eq_zero.mp hn
    have hC_empty : ∀ y ∈ D, C y = ∅ := by
      intro y hy; have h : C y ⊆ ambientCubes := hC_sub y hy
      rw [h_amb_empty] at h; simpa using h
    rcases hD_nonempty with ⟨y_star, hy_star⟩
    refine' ⟨y_star, hy_star, D, Finset.Subset.refl D, _ , _⟩
    · have h_mass_le_one : mass ≤ 1 := by
        have h1 : c^2 ≤ 1 := by nlinarith
        have h2 : c^2 / 16 ≤ 1 := by nlinarith
        linarith [hmass_le]
      rw [hW_sum]; nlinarith
    · intro y _; have h1 : C y = ∅ := hC_empty y ‹_›
      have h2 : C y_star = ∅ := hC_empty y_star hy_star
      simp [h1, h2]
  · have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    let d : Cube → ℝ := fun Q => ∑ y ∈ D, w y * if Q ∈ C y then 1 else 0
    let S : ℝ → ℝ := fun y1 => ∑ y2 ∈ D, w y2 * ((C y1 ∩ C y2).card : ℝ)
    have h_total : ∑ Q ∈ ambientCubes, d Q = ∑ y ∈ D, w y * ((C y).card : ℝ) := by
      simp only [d]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro y hy
      have h_sum_ind : ∑ Q ∈ ambientCubes, (if Q ∈ C y then (1 : ℝ) else 0) = ((C y).card : ℝ) := by
        rw [Finset.sum_ite]
        have h_filter : ambientCubes.filter (fun Q => Q ∈ C y) = C y := by
          ext Q; simp [hC_sub y hy] <;> tauto
        rw [h_filter] <;> simp
      have h_goal : ∑ Q ∈ ambientCubes, w y * (if Q ∈ C y then (1 : ℝ) else 0) =
                     w y * ((C y).card : ℝ) := by
        rw [← Finset.mul_sum, h_sum_ind]
      exact h_goal
    have h_lower1 : ∑ Q ∈ ambientCubes, d Q ≥ c * W * (n : ℝ) := by
      rw [h_total]
      have h : ∑ y ∈ D, w y * ((C y).card : ℝ) ≥ ∑ y ∈ D, w y * (c * (n : ℝ)) := by
        apply Finset.sum_le_sum; intro y hy
        have h2 : ((C y).card : ℝ) ≥ c * (n : ℝ) := hC_lower y hy
        have h3 : 0 ≤ w y := hw_nonneg y hy; nlinarith
      have h4 : ∑ y ∈ D, w y * (c * (n : ℝ)) = c * (n : ℝ) * W := by
        have h5 : ∑ y ∈ D, w y * (c * (n : ℝ)) = ∑ y ∈ D, (c * (n : ℝ)) * w y := by
          apply Finset.sum_congr rfl; intro y _; ring
        rw [h5, ← Finset.mul_sum, hW_sum]
      linarith [h, h4]
    have h_cs : ∑ Q ∈ ambientCubes, (d Q)^2 ≥ c^2 * W^2 * (n : ℝ) := by
      have h1 : (∑ Q ∈ ambientCubes, d Q)^2 ≤ (n : ℝ) * ∑ Q ∈ ambientCubes, (d Q)^2 :=
        sq_sum_le_card_mul_sum_sq (s := ambientCubes) (f := d)
      have h2 : (c * W * (n : ℝ))^2 ≤ (∑ Q ∈ ambientCubes, d Q)^2 := by gcongr <;> linarith
      have h3 : c^2 * W^2 * (n : ℝ)^2 ≤ (n : ℝ) * ∑ Q ∈ ambientCubes, (d Q)^2 := by
        calc c^2 * W^2 * (n : ℝ)^2 = (c * W * (n : ℝ))^2 := by ring
             _ ≤ (∑ Q ∈ ambientCubes, d Q)^2 := h2
             _ ≤ (n : ℝ) * ∑ Q ∈ ambientCubes, (d Q)^2 := h1
      nlinarith
    have h_identity1 : ∑ Q ∈ ambientCubes, (d Q)^2 = ∑ y1 ∈ D, w y1 * ∑ Q ∈ C y1, d Q := by
      calc
        ∑ Q ∈ ambientCubes, (d Q)^2
          = ∑ Q ∈ ambientCubes, d Q * (∑ y1 ∈ D, w y1 * if Q ∈ C y1 then 1 else 0) := by
            apply Finset.sum_congr rfl; intro Q _
            have h_eq : d Q = ∑ y1 ∈ D, w y1 * if Q ∈ C y1 then 1 else 0 := by rfl
            rw [h_eq] <;> ring
        _ = ∑ Q ∈ ambientCubes, ∑ y1 ∈ D, (d Q * w y1 * if Q ∈ C y1 then 1 else 0) := by
            apply Finset.sum_congr rfl; intro Q _
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y1 _; ring
        _ = ∑ y1 ∈ D, ∑ Q ∈ ambientCubes, (d Q * w y1 * if Q ∈ C y1 then 1 else 0) := by rw [Finset.sum_comm]
        _ = ∑ y1 ∈ D, w y1 * ∑ Q ∈ C y1, d Q := by
            apply Finset.sum_congr rfl; intro y1 hy1
            have h5 : ∑ Q ∈ ambientCubes, (d Q * w y1 * if Q ∈ C y1 then 1 else 0) =
                       w y1 * ∑ Q ∈ C y1, d Q := by
              have h61 : ∀ Q, d Q * w y1 * (if Q ∈ C y1 then (1 : ℝ) else 0) =
                           (if Q ∈ C y1 then d Q * w y1 else 0) := by
                intro Q; split_ifs <;> ring
              have h62 : ∑ Q ∈ ambientCubes, (d Q * w y1 * if Q ∈ C y1 then 1 else 0) =
                           ∑ Q ∈ ambientCubes, (if Q ∈ C y1 then d Q * w y1 else 0) := by
                apply Finset.sum_congr rfl; intro Q _; exact h61 Q
              rw [h62]
              have h63 : ∑ Q ∈ ambientCubes, (if Q ∈ C y1 then d Q * w y1 else 0) =
                         ∑ Q ∈ C y1, (d Q * w y1) := by
                rw [Finset.sum_ite]
                have h_filter : ambientCubes.filter (fun Q => Q ∈ C y1) = C y1 := by
                  ext Q; simp [hC_sub y1 hy1] <;> tauto
                rw [h_filter] <;> simp
              rw [h63]
              have h64 : ∑ Q ∈ C y1, d Q * w y1 = ∑ Q ∈ C y1, w y1 * d Q := by
                apply Finset.sum_congr rfl; intro Q _; ring
              rw [h64, ← Finset.mul_sum] <;> ring
            exact h5
    have h_identity2 : ∀ y1 ∈ D, ∑ Q ∈ C y1, d Q = S y1 := by
      intro y1 hy1; simp only [d, S]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro y2 hy2
      have h7 : ∑ Q ∈ C y1, (if Q ∈ C y2 then (1 : ℝ) else 0) = ((C y1 ∩ C y2).card : ℝ) := by
        rw [Finset.sum_ite]
        have h_filter : (C y1).filter (fun Q => Q ∈ C y2) = C y1 ∩ C y2 := by
          ext Q; simp [Finset.mem_inter] <;> tauto
        rw [h_filter] <;> simp
      have h71 : ∑ Q ∈ C y1, w y2 * (if Q ∈ C y2 then (1 : ℝ) else 0) =
                 w y2 * ((C y1 ∩ C y2).card : ℝ) := by
        rw [← Finset.mul_sum, h7]
      exact h71
    have h_identity : ∑ Q ∈ ambientCubes, (d Q)^2 = ∑ y1 ∈ D, w y1 * S y1 := by
      rw [h_identity1]; apply Finset.sum_congr rfl; intro y1 hy1; rw [h_identity2 y1 hy1] <;> ring
    have h_upper1 : ∑ y ∈ D, w y * ((C y).card : ℝ) ≤ W * (n : ℝ) := by
      have h : ∑ y ∈ D, w y * ((C y).card : ℝ) ≤ ∑ y ∈ D, w y * (n : ℝ) := by
        apply Finset.sum_le_sum; intro y hy
        have h2 : ((C y).card : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast Finset.card_le_card (hC_sub y hy)
        have h3 : 0 ≤ w y := hw_nonneg y hy; nlinarith
      have h4 : ∑ y ∈ D, w y * (n : ℝ) = (n : ℝ) * W := by
        have h5 : ∑ y ∈ D, w y * (n : ℝ) = ∑ y ∈ D, (n : ℝ) * w y := by
          apply Finset.sum_congr rfl; intro y _; ring
        rw [h5, ← Finset.mul_sum, hW_sum]
      linarith [h, h4]
    have h_exists_pos : ∃ (y0 : ℝ), y0 ∈ D ∧ 0 < w y0 := by
      by_contra h; push Not at h
      have h3 : ∀ y ∈ D, w y = 0 := by
        intro y hy; have h4 : w y ≤ 0 := by linarith [h y hy]
        have h5 : 0 ≤ w y := hw_nonneg y hy; linarith
      have h6 : ∑ y ∈ D, w y = 0 := by
        rw [Finset.sum_congr rfl h3] <;> simp
      rw [hW_sum] at h6; linarith
    rcases h_exists_pos with ⟨y0, hy0, hw0_pos⟩
    have h_exists : ∃ (y_star : ℝ), y_star ∈ D ∧ S y_star ≥ c^2 * W * ((C y_star).card : ℝ) := by
      by_contra h; push Not at h
      have h_all_le : ∀ y ∈ D, w y * S y ≤ w y * (c^2 * W * ((C y).card : ℝ)) := by
        intro y hy; have h5 : S y < c^2 * W * ((C y).card : ℝ) := h y hy
        have h6 : 0 ≤ w y := hw_nonneg y hy; nlinarith
      have h_y0_strict : w y0 * S y0 < w y0 * (c^2 * W * ((C y0).card : ℝ)) := by
        have h5 : S y0 < c^2 * W * ((C y0).card : ℝ) := h y0 hy0
        have h6 : 0 < w y0 := hw0_pos; nlinarith
      have h_strict : ∑ y ∈ D, w y * S y < ∑ y ∈ D, w y * (c^2 * W * ((C y).card : ℝ)) := by
        let g y := w y * (c^2 * W * ((C y).card : ℝ))
        let f y := w y * S y
        have h1 : ∀ y ∈ D, 0 ≤ g y - f y := by
          intro y hy; have h2 : f y ≤ g y := h_all_le y hy; linarith
        have h2 : 0 < g y0 - f y0 := by have h3 : f y0 < g y0 := h_y0_strict; linarith
        have h3 : g y0 - f y0 ≤ ∑ y ∈ D, (g y - f y) := Finset.single_le_sum h1 hy0
        have h4 : 0 < ∑ y ∈ D, (g y - f y) := by linarith
        have h5 : ∑ y ∈ D, (g y - f y) = ∑ y ∈ D, g y - ∑ y ∈ D, f y := by
          rw [Finset.sum_sub_distrib] <;> rfl
        linarith
      rw [← h_identity] at h_strict
      have h9 : ∑ y ∈ D, w y * (c^2 * W * ((C y).card : ℝ)) =
                 c^2 * W * ∑ y ∈ D, w y * ((C y).card : ℝ) := by
        have h91 : ∑ y ∈ D, w y * (c^2 * W * ((C y).card : ℝ)) =
                   ∑ y ∈ D, (c^2 * W) * (w y * ((C y).card : ℝ)) := by
          apply Finset.sum_congr rfl; intro y _; ring
        rw [h91, ← Finset.mul_sum]
      rw [h9] at h_strict
      have h10 : c^2 * W * ∑ y ∈ D, w y * ((C y).card : ℝ) ≤ c^2 * W^2 * (n : ℝ) := by
        calc c^2 * W * ∑ y ∈ D, w y * ((C y).card : ℝ)
               ≤ c^2 * W * (W * (n : ℝ)) := by gcongr
             _ = c^2 * W^2 * (n : ℝ) := by ring
      linarith
    rcases h_exists with ⟨y_star, hy_star, hS_ystar⟩
    let P : ℝ → Prop := fun y => ((C y ∩ C y_star).card : ℝ) ≥ α * ((C y_star).card : ℝ)
    let D' : Finset ℝ := D.filter P
    have hD'_sub : D' ⊆ D := Finset.filter_subset _ _
    have hP : ∀ y ∈ D', P y := by
      intro y hy; exact (Finset.mem_filter.mp hy).2
    have hCstar_pos : 0 < ((C y_star).card : ℝ) := by
      have h10 : ((C y_star).card : ℝ) ≥ c * (n : ℝ) := hC_lower y_star hy_star
      have h11 : 0 < c * (n : ℝ) := mul_pos hc_pos hn_pos; linarith
    by_cases h_weight : (∑ y ∈ D', w y) ≥ mass * W
    · exact ⟨y_star, hy_star, D', hD'_sub, h_weight, hP⟩
    · have h_weight_lt : (∑ y ∈ D', w y) < mass * W := by linarith
      let Dcomp := D.filter (fun y => y ∉ D')
      have hDcomp_sub : Dcomp ⊆ D := by simp [Dcomp] <;> tauto
      have h_partition : D = D' ∪ Dcomp := by ext x; simp [Dcomp] <;> tauto
      have h_disj : Disjoint D' Dcomp := by simp [Dcomp, Finset.disjoint_left] <;> tauto
      have hS_upper : S y_star ≤ ((C y_star).card : ℝ) *
           ((∑ y ∈ D', w y) + α * (∑ y ∈ Dcomp, w y)) := by
        have h_split : S y_star =
            ∑ y ∈ D', w y * ((C y_star ∩ C y).card : ℝ) +
            ∑ y ∈ Dcomp, w y * ((C y_star ∩ C y).card : ℝ) := by
          simp only [S]; rw [← Finset.sum_union h_disj, h_partition] <;> rfl
        rw [h_split]
        have h1 : ∑ y ∈ D', w y * ((C y_star ∩ C y).card : ℝ) ≤
                   ((C y_star).card : ℝ) * ∑ y ∈ D', w y := by
          have h2 : ∀ y ∈ D', ((C y_star ∩ C y).card : ℝ) ≤ ((C y_star).card : ℝ) := by
            intro y _; have h21 : (C y_star ∩ C y) ⊆ (C y_star) := by simp
            exact_mod_cast Finset.card_le_card h21
          calc
            ∑ y ∈ D', w y * ((C y_star ∩ C y).card : ℝ)
              ≤ ∑ y ∈ D', w y * ((C y_star).card : ℝ) :=
                Finset.sum_le_sum (fun y hy =>
                  mul_le_mul_of_nonneg_left (h2 y hy) (hw_nonneg y (hD'_sub hy)))
            _ = ((C y_star).card : ℝ) * ∑ y ∈ D', w y := by
              have h_comm : ∑ y ∈ D', w y * ((C y_star).card : ℝ) =
                         ∑ y ∈ D', ((C y_star).card : ℝ) * w y := by
                apply Finset.sum_congr rfl; intro y _; ring
              rw [h_comm, ← Finset.mul_sum] <;> ring
        have h3 : ∀ y ∈ Dcomp, ((C y_star ∩ C y).card : ℝ) < α * ((C y_star).card : ℝ) := by
          intro y hy
          have h4 : y ∈ D := hDcomp_sub hy
          have h5 : y ∉ D' := (Finset.mem_filter.mp hy).2
          have h6 : ¬P y := by
            intro hP; exact h5 (by rw [Finset.mem_filter]; exact ⟨h4, hP⟩)
          have h7 : ((C y ∩ C y_star).card : ℝ) < α * ((C y_star).card : ℝ) :=
            lt_of_not_ge h6
          have h8 : (C y_star ∩ C y).card = (C y ∩ C y_star).card := by
            rw [Finset.inter_comm]
          rw [h8]; exact h7
        have h4 : ∑ y ∈ Dcomp, w y * ((C y_star ∩ C y).card : ℝ) ≤
                   α * ((C y_star).card : ℝ) * ∑ y ∈ Dcomp, w y := by
          calc
            ∑ y ∈ Dcomp, w y * ((C y_star ∩ C y).card : ℝ)
              ≤ ∑ y ∈ Dcomp, w y * (α * ((C y_star).card : ℝ)) :=
                Finset.sum_le_sum (fun y hy =>
                  mul_le_mul_of_nonneg_left (le_of_lt (h3 y hy))
                    (hw_nonneg y (hDcomp_sub hy)))
            _ = α * ((C y_star).card : ℝ) * ∑ y ∈ Dcomp, w y := by
              have h_comm : ∑ y ∈ Dcomp, w y * (α * ((C y_star).card : ℝ)) =
                         ∑ y ∈ Dcomp, (α * ((C y_star).card : ℝ)) * w y := by
                apply Finset.sum_congr rfl; intro y _; ring
              rw [h_comm, ← Finset.mul_sum] <;> ring
        linarith
      have h_sum_comp : ∑ y ∈ Dcomp, w y ≤ W := by
        have h5 : ∑ y ∈ Dcomp, w y ≤ ∑ y ∈ D, w y := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hDcomp_sub
          intro i _ _; exact hw_nonneg i ‹_›
        rw [hW_sum] at h5; exact h5
      have h_sum_lt : (∑ y ∈ D', w y) + α * (∑ y ∈ Dcomp, w y) < mass * W + α * W := by
        have h1 : (∑ y ∈ D', w y) < mass * W := h_weight_lt
        have h2 : α * (∑ y ∈ Dcomp, w y) ≤ α * W := by gcongr <;> linarith
        linarith
      have hS_upper2 : S y_star < ((C y_star).card : ℝ) * W * (mass + α) := by
        calc
          S y_star
            ≤ ((C y_star).card : ℝ) * ((∑ y ∈ D', w y) + α * (∑ y ∈ Dcomp, w y)) := hS_upper
          _ < ((C y_star).card : ℝ) * (mass * W + α * W) := by
            exact mul_lt_mul_of_pos_left h_sum_lt hCstar_pos
          _ = ((C y_star).card : ℝ) * W * (mass + α) := by ring
      have h_const : mass + α < c^2 := by
        have h1 : α ≤ c^2 / 32 := by
          have h2 : c^2 * c ≤ c^2 := by nlinarith
          have h3 : c^2 * c / 32 ≤ c^2 / 32 := by gcongr
          calc α ≤ c^3 / 32 := hα_le
               _ = c^2 * c / 32 := by ring
               _ ≤ c^2 / 32 := h3
        have h4 : mass + α ≤ c^2 / 16 + c^2 / 32 := by linarith
        have h5 : c^2 / 16 + c^2 / 32 < c^2 := by
          have h6 : 0 < c^2 := by positivity
          nlinarith
        linarith
      have h_contra : S y_star < c^2 * W * ((C y_star).card : ℝ) := by
        calc
          S y_star < ((C y_star).card : ℝ) * W * (mass + α) := hS_upper2
          _ < ((C y_star).card : ℝ) * W * c^2 := by
            have h_pos1 : 0 < ((C y_star).card : ℝ) * W := mul_pos hCstar_pos hW_pos
            nlinarith
          _ = c^2 * W * ((C y_star).card : ℝ) := by ring
      linarith [hS_ystar]

end GraphLemma

namespace TwoSidedBigCap

/-! ## Product set and covering identity -/

/-- Product of two 1D sets embedded in 2D Euclidean space. -/
def prodSet (A B : Set ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | p 0 ∈ A ∧ p 1 ∈ B}

/-- Injectivity of dyadic cube construction. -/
lemma dyadicCube_injective {d : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    Function.Injective (dyadicCube δ : (Fin d → ℤ) → Set (EuclideanSpace ℝ (Fin d))) := by
  intro k1 k2 h
  ext i
  have h1 : ∀ (k : Fin d → ℤ), ∀ (p : EuclideanSpace ℝ (Fin d)),
      p ∈ dyadicCube δ k → ∀ i, δ * (k i : ℝ) ≤ p i ∧ p i < δ * ((k i : ℝ) + 1) := by
    intro k p hp i; exact hp i
  let p : EuclideanSpace ℝ (Fin d) := (WithLp.equiv 2 (Fin d → ℝ)).symm
    (fun i => δ * (k1 i : ℝ))
  have hp1 : p ∈ dyadicCube δ k1 := by
    intro i
    have hpi : p i = δ * (k1 i : ℝ) := by simp [p]
    rw [hpi]
    constructor <;> linarith
  rw [h] at hp1
  have h2 := h1 k2 p hp1 i
  have h3 : δ * (k2 i : ℝ) ≤ δ * (k1 i : ℝ) := h2.1
  have h4 : δ * (k1 i : ℝ) < δ * ((k2 i : ℝ) + 1) := h2.2
  have h5 : (k2 i : ℝ) ≤ (k1 i : ℝ) := by nlinarith
  have h6 : (k1 i : ℝ) < (k2 i : ℝ) + 1 := by nlinarith
  have h7 : k1 i = k2 i := by
    have h8 : k2 i ≤ k1 i := by exact_mod_cast h5
    have h9 : k1 i < k2 i + 1 := by exact_mod_cast h6
    omega
  exact h7

/-- Product covering identity: Nplane δ (A × B) = Nreal δ A * Nreal δ B. -/
lemma prodSet_covering_eq {δ : ℝ} (hδ : 0 < δ) {A B : Set ℝ}
    (hA_bdd : Bornology.IsBounded A) (hB_bdd : Bornology.IsBounded B) :
    Nplane δ (prodSet A B) = Nreal δ A * Nreal δ B := by
  let idxA := ProductLikeIncidence.realCubeIndexSet δ A
  let idxB := ProductLikeIncidence.realCubeIndexSet δ B
  let f : ℤ × ℤ → Set (EuclideanSpace ℝ (Fin 2)) := fun p =>
    dyadicCube δ (fun i : Fin 2 => if i = 0 then p.1 else p.2)
  have h_main : dyadicCubesMeeting δ (prodSet A B) = f '' (idxA ×ˢ idxB) := by
    ext Q
    simp only [dyadicCubesMeeting, Set.mem_setOf_eq, Set.mem_image, Set.mem_prod]
    constructor
    · rintro ⟨hQ_cube, ⟨p, hpQ, hpAB⟩⟩
      rcases hQ_cube with ⟨k, rfl⟩
      have h1 : k 0 ∈ idxA := by
        have h_p0_in : p 0 ∈ Set.Ico (δ * (k 0 : ℝ)) (δ * ((k 0 : ℝ) + 1)) := hpQ 0
        exact ⟨p 0, h_p0_in, hpAB.1⟩
      have h2 : k 1 ∈ idxB := by
        have h_p1_in : p 1 ∈ Set.Ico (δ * (k 1 : ℝ)) (δ * ((k 1 : ℝ) + 1)) := hpQ 1
        exact ⟨p 1, h_p1_in, hpAB.2⟩
      refine ⟨(k 0, k 1), ⟨h1, h2⟩, ?_⟩
      have h3 : (fun i : Fin 2 => if i = 0 then (k 0, k 1).1 else (k 0, k 1).2) = k := by
        ext i; fin_cases i <;> simp
      have h4 : f (k 0, k 1) = dyadicCube δ k :=
        congr_arg (dyadicCube δ) h3
      exact h4
    · rintro ⟨⟨kA, kB⟩, ⟨hkA, hkB⟩, rfl⟩
      rcases hkA with ⟨x, hxIco, hxA⟩
      rcases hkB with ⟨y, hyIco, hyB⟩
      let g : Fin 2 → ℝ := fun i => if i = 0 then x else y
      let p : EuclideanSpace ℝ (Fin 2) := (WithLp.equiv 2 (Fin 2 → ℝ)).symm g
      have hpQ : p ∈ dyadicCube δ (fun i : Fin 2 => if i = 0 then kA else kB) := by
        intro i; fin_cases i <;> simp [p, g, hxIco, hyIco] <;> tauto
      have hpAB : p ∈ prodSet A B := by
        simp only [prodSet, p, g, Set.mem_setOf_eq] <;> tauto
      exact ⟨⟨(fun i : Fin 2 => if i = 0 then kA else kB), rfl⟩, ⟨p, hpQ, hpAB⟩⟩
  have h_inj : Set.InjOn f (idxA ×ˢ idxB) := by
    rintro ⟨kA1, kB1⟩ _ ⟨kA2, kB2⟩ _ h
    have h_inj' : Function.Injective (dyadicCube δ : (Fin 2 → ℤ) → Set (EuclideanSpace ℝ (Fin 2))) :=
      dyadicCube_injective hδ
    have h_eq : (fun i : Fin 2 => if i = 0 then kA1 else kB1) = (fun i : Fin 2 => if i = 0 then kA2 else kB2) := h_inj' h
    have hkA : kA1 = kA2 := by have h := congr_fun h_eq 0; simpa using h
    have hkB : kB1 = kB2 := by have h := congr_fun h_eq 1; simpa using h
    exact Prod.ext hkA hkB
  have hA_fin : idxA.Finite := ProductLikeIncidence.realCubeIndexSet_finite hδ hA_bdd
  have hB_fin : idxB.Finite := ProductLikeIncidence.realCubeIndexSet_finite hδ hB_bdd
  rw [Nplane, dyadicCoveringNumber, h_main]
  rw [h_inj.encard_image, Set.encard_prod]
  have hA_eq : Nreal δ A = ENat.toENNReal idxA.encard := by
    simpa [Nreal, realLineCopy] using ProductLikeIncidence.realCoveringNumber_eq_card hδ hA_bdd
  have hB_eq : Nreal δ B = ENat.toENNReal idxB.encard := by
    simpa [Nreal, realLineCopy] using ProductLikeIncidence.realCoveringNumber_eq_card hδ hB_bdd
  rw [hA_eq, hB_eq]
  <;> simp <;> rfl

/-! ## Interval-thickening connection -/

/-- If a dyadic interval meets both A and B, then it meets
    A ∩ cthickening(√2·δ, B). -/
lemma interval_meets_thickened_intersection {δ : ℝ} (hδ : 0 < δ)
    {A B : Set ℝ} {k : ℤ}
    (hA : (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ A).Nonempty)
    (hB : (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ B).Nonempty) :
    (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩
      (A ∩ Metric.cthickening (Real.sqrt 2 * δ) B)).Nonempty := by
  rcases hA with ⟨x, hxIco, hxA⟩
  rcases hB with ⟨y, hyIco, hyB⟩
  have h_dist : |x - y| < δ := by
    have h1 : δ * (k : ℝ) ≤ x := hxIco.1
    have h2 : x < δ * ((k : ℝ) + 1) := hxIco.2
    have h3 : δ * (k : ℝ) ≤ y := hyIco.1
    have h4 : y < δ * ((k : ℝ) + 1) := hyIco.2
    rw [abs_lt]
    constructor <;> linarith
  have h5 : |x - y| ≤ Real.sqrt 2 * δ := by
    have h7 : |x - y| < δ := h_dist
    have h8 : (1 : ℝ) ≤ Real.sqrt 2 := by
      apply Real.le_sqrt_of_sq_le <;> norm_num
    have h9 : δ ≤ Real.sqrt 2 * δ := by
      have h10 : 0 ≤ δ := by linarith
      nlinarith
    linarith
  have h_x_thick : x ∈ Metric.cthickening (Real.sqrt 2 * δ) B := by
    have h1 : Metric.infEDist x B ≤ edist x y := Metric.infEDist_le_edist_of_mem hyB
    have h2 : edist x y = ENNReal.ofReal (dist x y) := edist_dist _ _
    have h3 : dist x y = |x - y| := by simp [dist_eq_norm]
    calc Metric.infEDist x B
      ≤ edist x y := h1
    _ = ENNReal.ofReal (dist x y) := h2
    _ = ENNReal.ofReal (|x - y|) := by rw [h3]
    _ ≤ ENNReal.ofReal (Real.sqrt 2 * δ) := ENNReal.ofReal_le_ofReal h5
  exact ⟨x, hxIco, ⟨hxA, h_x_thick⟩⟩

/-- If k is in both index sets, then the k-th interval meets the thickened intersection. -/
lemma index_intersection_subset_thickened {δ : ℝ} (hδ : 0 < δ)
    {A B : Set ℝ} (k : ℤ)
    (hkA : k ∈ ProductLikeIncidence.realCubeIndexSet δ A)
    (hkB : k ∈ ProductLikeIncidence.realCubeIndexSet δ B) :
    k ∈ ProductLikeIncidence.realCubeIndexSet δ
          (A ∩ Metric.cthickening (Real.sqrt 2 * δ) B) := by
  have hA : (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ A).Nonempty := hkA
  have hB : (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ B).Nonempty := hkB
  exact interval_meets_thickened_intersection hδ hA hB

/-- A nonempty bounded set has nonempty cube index set. -/
lemma realCubeIndexSet_nonempty {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (hS_nonempty : S.Nonempty) : (ProductLikeIncidence.realCubeIndexSet δ S).Nonempty := by
  rcases hS_nonempty with ⟨x, hx⟩
  let k : ℤ := Int.floor (x / δ)
  have h1 : δ * (k : ℝ) ≤ x := by
    have h2 : (k : ℝ) ≤ x / δ := Int.floor_le (x / δ)
    calc δ * (k : ℝ) ≤ δ * (x / δ) := by gcongr
      _ = x := by field_simp [hδ.ne'] <;> ring
  have h2 : x < δ * ((k : ℝ) + 1) := by
    have h3 : x / δ < (k : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
    calc x = δ * (x / δ) := by field_simp [hδ.ne'] <;> ring
      _ < δ * ((k : ℝ) + 1) := by gcongr
  exact ⟨k, x, ⟨h1, h2⟩, hx⟩

/-! ## Main theorem -/

/-- Two-sided representative big intersection: given coordinate families A_y, B_y
    with uniform product covering lower bounds, select y_star and D' such that
    thickened intersections on BOTH sides are simultaneously large. -/
lemma representative_big_intersection_two_sided
    {δ : ℝ} (hδ : 0 < δ) (_ : δ < 1)
    {D : Finset ℝ} (hD_nonempty : D.Nonempty)
    {w : ℝ → ℝ} (hw_nonneg : ∀ y ∈ D, 0 ≤ w y)
    {W : ℝ} (hW_pos : 0 < W) (hW_sum : ∑ y ∈ D, w y = W)
    {ambient_A ambient_B : Set ℝ}
    (hambient_A_bdd : Bornology.IsBounded ambient_A)
    (hambient_A_nonempty : ambient_A.Nonempty)
    (hambient_B_bdd : Bornology.IsBounded ambient_B)
    (hambient_B_nonempty : ambient_B.Nonempty)
    {A B : ℝ → Set ℝ}
    (hA_bdd : ∀ y ∈ D, Bornology.IsBounded (A y))
    (hB_bdd : ∀ y ∈ D, Bornology.IsBounded (B y))
    (hA_sub : ∀ y ∈ D, A y ⊆ ambient_A)
    (hB_sub : ∀ y ∈ D, B y ⊆ ambient_B)
    {c : ℝ} (hc_pos : 0 < c) (hc_le_one : c ≤ 1)
    {α mass : ℝ} (hα_pos : 0 < α) (hmass_pos : 0 < mass)
    (hα_le : α ≤ c^3 / 32) (hmass_le : mass ≤ c^2 / 16)
    (hG_lower : ∀ y ∈ D,
      Nplane δ (prodSet (A y) (B y)) ≥ ENNReal.ofReal c * Nplane δ (prodSet ambient_A ambient_B)) :
    ∃ (y_star : ℝ) (hy_star : y_star ∈ D) (D' : Finset ℝ),
      D' ⊆ D ∧
      (∑ y ∈ D', w y) ≥ mass * W ∧
      ∀ y ∈ D',
        Nreal δ (Metric.cthickening (Real.sqrt 2 * δ) (A y_star) ∩ A y) ≥
          ENNReal.ofReal α * Nreal δ (A y_star) ∧
        Nreal δ (Metric.cthickening (Real.sqrt 2 * δ) (B y_star) ∩ B y) ≥
          ENNReal.ofReal α * Nreal δ (B y_star) := by
  let idxA : ℝ → Finset ℤ := fun y =>
    if h : y ∈ D then
      (ProductLikeIncidence.realCubeIndexSet_finite hδ (hA_bdd y h)).toFinset
    else
      ∅
  let idxB : ℝ → Finset ℤ := fun y =>
    if h : y ∈ D then
      (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB_bdd y h)).toFinset
    else
      ∅
  let IambA := (ProductLikeIncidence.realCubeIndexSet_finite hδ hambient_A_bdd).toFinset
  let IambB := (ProductLikeIncidence.realCubeIndexSet_finite hδ hambient_B_bdd).toFinset
  let C y := idxA y ×ˢ idxB y
  let ambientCubes := IambA ×ˢ IambB

  have hC_sub : ∀ y ∈ D, C y ⊆ ambientCubes := by
    intro y hy
    have h_idxA : idxA y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hA_bdd y hy)).toFinset := by
      simp [idxA, hy]
    have h_idxB : idxB y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB_bdd y hy)).toFinset := by
      simp [idxB, hy]
    have h1 : idxA y ⊆ IambA := by
      rw [h_idxA]
      intro k hk
      have h2 : k ∈ ProductLikeIncidence.realCubeIndexSet δ (A y) := by
        simpa [Set.Finite.coe_toFinset] using hk
      rcases h2 with ⟨x, hxIco, hxA⟩
      have h3 : x ∈ ambient_A := hA_sub y hy hxA
      have h4 : k ∈ ProductLikeIncidence.realCubeIndexSet δ ambient_A := ⟨x, hxIco, h3⟩
      simpa [IambA, Set.Finite.coe_toFinset] using h4
    have h2 : idxB y ⊆ IambB := by
      rw [h_idxB]
      intro k hk
      have h3 : k ∈ ProductLikeIncidence.realCubeIndexSet δ (B y) := by
        simpa [Set.Finite.coe_toFinset] using hk
      rcases h3 with ⟨x, hxIco, hxB⟩
      have h4 : x ∈ ambient_B := hB_sub y hy hxB
      have h5 : k ∈ ProductLikeIncidence.realCubeIndexSet δ ambient_B := ⟨x, hxIco, h4⟩
      simpa [IambB, Set.Finite.coe_toFinset] using h5
    exact Finset.product_subset_product h1 h2

  have h_Nreal_card : ∀ (S : Set ℝ) (hS : Bornology.IsBounded S),
      Nreal δ S = (↑((ProductLikeIncidence.realCubeIndexSet_finite hδ hS).toFinset.card) : ENNReal) := by
    intro S hS
    have h_eq1 : Nreal δ S = ENat.toENNReal (ProductLikeIncidence.realCubeIndexSet δ S).encard := by
      have h : dyadicCoveringNumber δ (ProductLikeIncidence.productLikeRealLineCopy S) =
          (ProductLikeIncidence.realCubeIndexSet δ S).encard :=
        ProductLikeIncidence.realCoveringNumber_eq_card hδ hS
      have h' : Nreal δ S = ENat.toENNReal (dyadicCoveringNumber δ (ProductLikeIncidence.productLikeRealLineCopy S)) := by rfl
      rw [h', h]
    have h_fin : (ProductLikeIncidence.realCubeIndexSet δ S).Finite :=
      ProductLikeIncidence.realCubeIndexSet_finite hδ hS
    rw [h_eq1]
    rw [Set.Finite.encard_eq_coe_toFinset_card h_fin]
    <;> norm_cast

  have hC_lower' : ∀ y ∈ D, ((C y).card : ℝ) ≥ c * (ambientCubes.card : ℝ) := by
    intro y hy
    have h_idxA : idxA y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hA_bdd y hy)).toFinset := by
      simp [idxA, hy]
    have h_idxB : idxB y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB_bdd y hy)).toFinset := by
      simp [idxB, hy]
    have h1 : Nplane δ (prodSet (A y) (B y)) = Nreal δ (A y) * Nreal δ (B y) :=
      prodSet_covering_eq hδ (hA_bdd y hy) (hB_bdd y hy)
    have h2 : Nplane δ (prodSet ambient_A ambient_B) = Nreal δ ambient_A * Nreal δ ambient_B :=
      prodSet_covering_eq hδ hambient_A_bdd hambient_B_bdd
    have hG' : Nreal δ (A y) * Nreal δ (B y) ≥
               ENNReal.ofReal c * (Nreal δ ambient_A * Nreal δ ambient_B) := by
      have hG_inst := hG_lower y hy
      rw [h1, h2] at hG_inst
      exact hG_inst
    have h4 : Nreal δ (A y) = (↑((idxA y).card) : ENNReal) := by
      rw [h_Nreal_card (A y) (hA_bdd y hy), h_idxA] <;> rfl
    have h5 : Nreal δ (B y) = (↑((idxB y).card) : ENNReal) := by
      rw [h_Nreal_card (B y) (hB_bdd y hy), h_idxB] <;> rfl
    have h6 : Nreal δ ambient_A = (↑IambA.card : ENNReal) :=
      h_Nreal_card ambient_A hambient_A_bdd
    have h7 : Nreal δ ambient_B = (↑IambB.card : ENNReal) :=
      h_Nreal_card ambient_B hambient_B_bdd
    rw [h4, h5, h6, h7] at hG'
    have h_card_C : (C y).card = (idxA y).card * (idxB y).card := by
      simp [C, Finset.card_product]
    have h_card_amb : ambientCubes.card = IambA.card * IambB.card := by
      simp [ambientCubes, Finset.card_product]
    have hG'' : (↑((C y).card) : ENNReal) ≥ ENNReal.ofReal (c * (ambientCubes.card : ℝ)) := by
      simpa [h_card_C, h_card_amb, ENNReal.coe_mul, ENNReal.ofReal_mul hc_pos.le] using hG'
    have h_eq : (↑((C y).card) : ENNReal) = ENNReal.ofReal ((C y).card : ℝ) := by simp
    rw [h_eq] at hG''
    have h_q_pos : 0 ≤ ((C y).card : ℝ) := by positivity
    exact (ENNReal.ofReal_le_ofReal_iff h_q_pos).mp hG''

  have h_main := GraphLemma.representative_big_intersection_graph_cubes
    hD_nonempty hw_nonneg hW_pos hW_sum hC_sub hc_pos hc_le_one hC_lower'
    hα_pos hmass_pos hα_le hmass_le

  rcases h_main with ⟨y_star, hy_star, D', hD'_sub, h_mass, h_shared⟩

  have h_ambA_idx_nonempty : IambA.Nonempty :=
    ProductLikeIncidence.cube_index_nonempty hδ hambient_A_bdd hambient_A_nonempty
  have h_ambB_idx_nonempty : IambB.Nonempty :=
    ProductLikeIncidence.cube_index_nonempty hδ hambient_B_bdd hambient_B_nonempty
  have h_amb_card_pos : 0 < (ambientCubes.card : ℝ) := by
    have h1 : 0 < IambA.card := Finset.Nonempty.card_pos h_ambA_idx_nonempty
    have h2 : 0 < IambB.card := Finset.Nonempty.card_pos h_ambB_idx_nonempty
    simp [ambientCubes, Finset.card_product] <;> positivity
  have h_Cstar_pos : 0 < ((C y_star).card : ℝ) := by
    have h1 : ((C y_star).card : ℝ) ≥ c * (ambientCubes.card : ℝ) := hC_lower' y_star hy_star
    have h2 : 0 < c * (ambientCubes.card : ℝ) := mul_pos hc_pos h_amb_card_pos
    linarith
  have h_Astar_pos : 0 < ((idxA y_star).card : ℝ) := by
    have h1 : ((C y_star).card : ℝ) = ((idxA y_star).card : ℝ) * ((idxB y_star).card : ℝ) := by
      simp [C, Finset.card_product] <;> ring
    have h2 : 0 < ((idxA y_star).card : ℝ) * ((idxB y_star).card : ℝ) := by
      rw [← h1]; exact h_Cstar_pos
    by_contra h3
    have h4 : ((idxA y_star).card : ℝ) = 0 := by linarith
    rw [h4] at h2
    simp at h2 <;> linarith
  have h_Bstar_pos : 0 < ((idxB y_star).card : ℝ) := by
    have h1 : ((C y_star).card : ℝ) = ((idxA y_star).card : ℝ) * ((idxB y_star).card : ℝ) := by
      simp [C, Finset.card_product] <;> ring
    have h2 : 0 < ((idxA y_star).card : ℝ) * ((idxB y_star).card : ℝ) := by
      rw [← h1]; exact h_Cstar_pos
    by_contra h3
    have h4 : ((idxB y_star).card : ℝ) = 0 := by linarith
    rw [h4] at h2
    simp at h2 <;> linarith

  have h_counting : ∀ y ∈ D',
      ((idxA y ∩ idxA y_star).card : ℝ) ≥ α * ((idxA y_star).card : ℝ) ∧
      ((idxB y ∩ idxB y_star).card : ℝ) ≥ α * ((idxB y_star).card : ℝ) := by
    intro y hy
    set a := ((idxA y ∩ idxA y_star).card : ℝ) with ha_def
    set b := ((idxB y ∩ idxB y_star).card : ℝ) with hb_def
    set Astar := ((idxA y_star).card : ℝ) with hA_def
    set Bstar := ((idxB y_star).card : ℝ) with hB_def
    have h1 : a * b ≥ α * (Astar * Bstar) := by
      have h_orig : ((C y ∩ C y_star).card : ℝ) ≥ α * ((C y_star).card : ℝ) := h_shared y hy
      have h2 : (C y ∩ C y_star).card = (idxA y ∩ idxA y_star).card * (idxB y ∩ idxB y_star).card := by
        have h_eq : C y ∩ C y_star = (idxA y ∩ idxA y_star) ×ˢ (idxB y ∩ idxB y_star) := by
          ext ⟨x, z⟩; simp [C, Finset.mem_inter, Finset.mem_product] <;> tauto
        rw [h_eq, Finset.card_product]
      have h3 : (C y_star).card = (idxA y_star).card * (idxB y_star).card := by
        simp [C, Finset.card_product]
      rw [h2, h3] at h_orig
      simpa [ha_def, hb_def, hA_def, hB_def] using h_orig
    have h5 : a ≤ Astar := by
      have h_sub : (idxA y ∩ idxA y_star) ⊆ idxA y_star := by simp
      have h_card : (idxA y ∩ idxA y_star).card ≤ (idxA y_star).card := Finset.card_le_card h_sub
      have h_cast : ((idxA y ∩ idxA y_star).card : ℝ) ≤ ((idxA y_star).card : ℝ) := by exact_mod_cast h_card
      rw [ha_def, hA_def]; exact h_cast
    have h6 : b ≤ Bstar := by
      have h_sub : (idxB y ∩ idxB y_star) ⊆ idxB y_star := by simp
      have h_card : (idxB y ∩ idxB y_star).card ≤ (idxB y_star).card := Finset.card_le_card h_sub
      have h_cast : ((idxB y ∩ idxB y_star).card : ℝ) ≤ ((idxB y_star).card : ℝ) := by exact_mod_cast h_card
      rw [hb_def, hB_def]; exact h_cast
    have hBstar_pos' : 0 < Bstar := by
      rw [hB_def]; exact h_Bstar_pos
    have hAstar_pos' : 0 < Astar := by
      rw [hA_def]; exact h_Astar_pos
    have ha : a ≥ α * Astar := by
      by_contra h
      have h' : a < α * Astar := by linarith
      have h_a_nonneg : 0 ≤ a := by rw [ha_def] <;> exact_mod_cast Nat.zero_le _
      have h10 : a * b ≤ a * Bstar := mul_le_mul_of_nonneg_left h6 h_a_nonneg
      have h11 : a * Bstar < α * Astar * Bstar :=
        mul_lt_mul_of_pos_right h' hBstar_pos'
      have h13 : a * b < α * (Astar * Bstar) := by
        calc a * b ≤ a * Bstar := h10
             _ < α * Astar * Bstar := h11
             _ = α * (Astar * Bstar) := by ring
      linarith
    have hb : b ≥ α * Bstar := by
      by_contra h
      have h' : b < α * Bstar := by linarith
      have h_b_nonneg : 0 ≤ b := by rw [hb_def] <;> exact_mod_cast Nat.zero_le _
      have h10 : a * b ≤ Astar * b := mul_le_mul_of_nonneg_right h5 h_b_nonneg
      have h11 : Astar * b < α * Astar * Bstar := by
        have h12 : Astar * b < Astar * (α * Bstar) := mul_lt_mul_of_pos_left h' hAstar_pos'
        have h13 : Astar * (α * Bstar) = α * Astar * Bstar := by ring
        rw [h13] at h12
        exact h12
      have h13 : a * b < α * (Astar * Bstar) := by
        calc a * b ≤ Astar * b := h10
             _ < α * Astar * Bstar := h11
             _ = α * (Astar * Bstar) := by ring
      linarith
    exact ⟨ha, hb⟩

  refine ⟨y_star, hy_star, D', hD'_sub, h_mass, fun y hy => ?_⟩
  have h_counts := h_counting y hy
  have hyD : y ∈ D := hD'_sub hy

  have h_idxA_y : idxA y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hA_bdd y hyD)).toFinset := by
    simp [idxA, hyD]
  have h_idxA_ystar : idxA y_star = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hA_bdd y_star hy_star)).toFinset := by
    simp [idxA, hy_star]
  have h_idxB_y : idxB y = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB_bdd y hyD)).toFinset := by
    simp [idxB, hyD]
  have h_idxB_ystar : idxB y_star = (ProductLikeIncidence.realCubeIndexSet_finite hδ (hB_bdd y_star hy_star)).toFinset := by
    simp [idxB, hy_star]

  have hA_thick_bdd : Bornology.IsBounded
      (Metric.cthickening (Real.sqrt 2 * δ) (A y_star) ∩ A y) :=
    (hA_bdd y_star hy_star).cthickening.subset Set.inter_subset_left

  have hB_thick_bdd : Bornology.IsBounded
      (Metric.cthickening (Real.sqrt 2 * δ) (B y_star) ∩ B y) :=
    (hB_bdd y_star hy_star).cthickening.subset Set.inter_subset_left

  let K_A := (ProductLikeIncidence.realCubeIndexSet_finite hδ hA_thick_bdd).toFinset
  let K_B := (ProductLikeIncidence.realCubeIndexSet_finite hδ hB_thick_bdd).toFinset

  have hA_idx_sub : (idxA y ∩ idxA y_star) ⊆ K_A := by
    rw [h_idxA_y, h_idxA_ystar]
    intro k hk
    have hkA : k ∈ ProductLikeIncidence.realCubeIndexSet δ (A y) := by
      simpa [Set.Finite.coe_toFinset] using (Finset.mem_inter.mp hk).1
    have hkAstar : k ∈ ProductLikeIncidence.realCubeIndexSet δ (A y_star) := by
      simpa [Set.Finite.coe_toFinset] using (Finset.mem_inter.mp hk).2
    have h : k ∈ ProductLikeIncidence.realCubeIndexSet δ (A y ∩ Metric.cthickening (Real.sqrt 2 * δ) (A y_star)) :=
      index_intersection_subset_thickened hδ k hkA hkAstar
    have h_eq : (A y ∩ Metric.cthickening (Real.sqrt 2 * δ) (A y_star)) =
                (Metric.cthickening (Real.sqrt 2 * δ) (A y_star) ∩ A y) := by
      ext z; simp [and_comm]
    rw [h_eq] at h
    simpa [K_A, Set.Finite.coe_toFinset] using h

  have hB_idx_sub : (idxB y ∩ idxB y_star) ⊆ K_B := by
    rw [h_idxB_y, h_idxB_ystar]
    intro k hk
    have hkB : k ∈ ProductLikeIncidence.realCubeIndexSet δ (B y) := by
      simpa [Set.Finite.coe_toFinset] using (Finset.mem_inter.mp hk).1
    have hkBstar : k ∈ ProductLikeIncidence.realCubeIndexSet δ (B y_star) := by
      simpa [Set.Finite.coe_toFinset] using (Finset.mem_inter.mp hk).2
    have h : k ∈ ProductLikeIncidence.realCubeIndexSet δ (B y ∩ Metric.cthickening (Real.sqrt 2 * δ) (B y_star)) :=
      index_intersection_subset_thickened hδ k hkB hkBstar
    have h_eq : (B y ∩ Metric.cthickening (Real.sqrt 2 * δ) (B y_star)) =
                (Metric.cthickening (Real.sqrt 2 * δ) (B y_star) ∩ B y) := by
      ext z; simp [and_comm]
    rw [h_eq] at h
    simpa [K_B, Set.Finite.coe_toFinset] using h

  have hA_card_le : ((idxA y ∩ idxA y_star).card : ℝ) ≤ (K_A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hA_idx_sub

  have hB_card_le : ((idxB y ∩ idxB y_star).card : ℝ) ≤ (K_B.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hB_idx_sub

  have hA_eq : Nreal δ (Metric.cthickening (Real.sqrt 2 * δ) (A y_star) ∩ A y) =
      (↑K_A.card : ENNReal) := h_Nreal_card _ hA_thick_bdd

  have hB_eq : Nreal δ (Metric.cthickening (Real.sqrt 2 * δ) (B y_star) ∩ B y) =
      (↑K_B.card : ENNReal) := h_Nreal_card _ hB_thick_bdd

  have hAstar_eq : Nreal δ (A y_star) = (↑((idxA y_star).card) : ENNReal) := by
    rw [h_Nreal_card (A y_star) (hA_bdd y_star hy_star), h_idxA_ystar] <;> rfl

  have hBstar_eq : Nreal δ (B y_star) = (↑((idxB y_star).card) : ENNReal) := by
    rw [h_Nreal_card (B y_star) (hB_bdd y_star hy_star), h_idxB_ystar] <;> rfl

  have hA_concl : Nreal δ (Metric.cthickening (Real.sqrt 2 * δ) (A y_star) ∩ A y) ≥
      ENNReal.ofReal α * Nreal δ (A y_star) := by
    rw [hA_eq, hAstar_eq]
    have h1 : (K_A.card : ℝ) ≥ α * ((idxA y_star).card : ℝ) := by
      linarith [hA_card_le, h_counts.1]
    have h2 : (↑K_A.card : ENNReal) ≥ ENNReal.ofReal (α * ((idxA y_star).card : ℝ)) := by
      have h_coe : (↑K_A.card : ENNReal) = ENNReal.ofReal ((K_A.card : ℝ)) := by simp
      rw [h_coe]
      exact ENNReal.ofReal_le_ofReal h1
    have h3 : ENNReal.ofReal α * (↑((idxA y_star).card) : ENNReal) =
        ENNReal.ofReal (α * ((idxA y_star).card : ℝ)) := by
      rw [ENNReal.ofReal_mul hα_pos.le] <;> simp
    rw [h3]
    exact h2

  have hB_concl : Nreal δ (Metric.cthickening (Real.sqrt 2 * δ) (B y_star) ∩ B y) ≥
      ENNReal.ofReal α * Nreal δ (B y_star) := by
    rw [hB_eq, hBstar_eq]
    have h1 : (K_B.card : ℝ) ≥ α * ((idxB y_star).card : ℝ) := by
      linarith [hB_card_le, h_counts.2]
    have h2 : (↑K_B.card : ENNReal) ≥ ENNReal.ofReal (α * ((idxB y_star).card : ℝ)) := by
      have h_coe : (↑K_B.card : ENNReal) = ENNReal.ofReal ((K_B.card : ℝ)) := by simp
      rw [h_coe]
      exact ENNReal.ofReal_le_ofReal h1
    have h3 : ENNReal.ofReal α * (↑((idxB y_star).card) : ENNReal) =
        ENNReal.ofReal (α * ((idxB y_star).card : ℝ)) := by
      rw [ENNReal.ofReal_mul hα_pos.le] <;> simp
    rw [h3]
    exact h2

  exact ⟨hA_concl, hB_concl⟩

end TwoSidedBigCap
