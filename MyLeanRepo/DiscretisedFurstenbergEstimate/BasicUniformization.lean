module

/-
  Basic Uniformization (OS Lemma 7.1) — full theorem.

  Given P (union of dyadic δ-squares) and scales δ = Δ_n < ... < Δ_0 = 1,
  construct a uniform subset P' ⊂ P with dyadic covering number at least
  |P| / (24 * log(1/δ) / n)^n.

  Uses range uniformity [N, 2N) at each level via pigeonhole_dyadic_range.

  Whiteprint node: uniformization
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Uniformization
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.Core
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal BigOperators
open DirecretisedFurstenbergEstimate

namespace DiscretisedFurstenbergEstimate.BasicUniformization

open DiscretisedFurstenbergEstimate.Uniformization
open DiscretisedFurstenbergEstimate.DyadicCubes

abbrev dyadicSquare (Δ : ℝ) (i j : ℤ) : Set EuclideanPlane :=
  MultiscaleDecomposition.dyadicSquare Δ i j

/-- A dyadic square is bounded. -/
lemma dyadicSquare_isBounded (δ : ℝ) (hδ_pos : 0 < δ) (i j : ℤ) :
    Bornology.IsBounded (dyadicSquare δ i j) := by
  let R : ℝ := (|(i : ℝ)| + |(j : ℝ)| + 2) * δ
  have hR_nonneg : 0 ≤ R := by positivity
  have h : dyadicSquare δ i j ⊆ Metric.closedBall (0 : EuclideanPlane) R := by
    intro x hx
    have h1 : (i : ℝ) * δ ≤ x 0 := hx.1.1
    have h2 : x 0 < ((i : ℝ) + 1) * δ := hx.1.2
    have h3 : (j : ℝ) * δ ≤ x 1 := hx.2.1
    have h4 : x 1 < ((j : ℝ) + 1) * δ := hx.2.2
    have h5 : |x 0| ≤ (|(i : ℝ)| + 1) * δ := by
      have h_lower : -((|(i : ℝ)| + 1) * δ) ≤ x 0 := by
        have h1 : -(|(i : ℝ)|) ≤ (i : ℝ) := neg_abs_le (i : ℝ)
        nlinarith [hδ_pos, abs_nonneg (i : ℝ)]
      have h_upper : x 0 ≤ (|(i : ℝ)| + 1) * δ := by
        have h2 : (i : ℝ) ≤ |(i : ℝ)| := le_abs_self (i : ℝ)
        nlinarith [hδ_pos, abs_nonneg (i : ℝ)]
      rw [abs_le] <;> exact ⟨h_lower, h_upper⟩
    have h6 : |x 1| ≤ (|(j : ℝ)| + 1) * δ := by
      have h_lower : -((|(j : ℝ)| + 1) * δ) ≤ x 1 := by
        have h1 : -(|(j : ℝ)|) ≤ (j : ℝ) := neg_abs_le (j : ℝ)
        nlinarith [hδ_pos, abs_nonneg (j : ℝ)]
      have h_upper : x 1 ≤ (|(j : ℝ)| + 1) * δ := by
        have h2 : (j : ℝ) ≤ |(j : ℝ)| := le_abs_self (j : ℝ)
        nlinarith [hδ_pos, abs_nonneg (j : ℝ)]
      rw [abs_le] <;> exact ⟨h_lower, h_upper⟩
    have h7 : ‖x‖ ≤ |x 0| + |x 1| := by
      have h11 : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq x]
        <;> simp [Fin.sum_univ_two]
      have h141 : |x 0| ^ 2 = (x 0) ^ 2 := by rw [sq_abs]
      have h142 : |x 1| ^ 2 = (x 1) ^ 2 := by rw [sq_abs]
      have h12 : (x 0) ^ 2 + (x 1) ^ 2 ≤ (|x 0| + |x 1|) ^ 2 := by
        have h13 : 0 ≤ 2 * |x 0| * |x 1| := by positivity
        have h14 : (|x 0| + |x 1|) ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + 2 * |x 0| * |x 1| := by
          calc
            (|x 0| + |x 1|) ^ 2
              = |x 0| ^ 2 + |x 1| ^ 2 + 2 * |x 0| * |x 1| := by ring
            _ = (x 0) ^ 2 + |x 1| ^ 2 + 2 * |x 0| * |x 1| := by rw [h141]
            _ = (x 0) ^ 2 + (x 1) ^ 2 + 2 * |x 0| * |x 1| := by rw [h142]
        linarith
      have h15 : ‖x‖ ^ 2 ≤ (|x 0| + |x 1|) ^ 2 := by
        rw [h11] <;> exact h12
      have h16 : 0 ≤ ‖x‖ := by positivity
      have h17 : 0 ≤ |x 0| + |x 1| := by positivity
      nlinarith
    have h16 : ‖x‖ ≤ R := by
      calc ‖x‖ ≤ |x 0| + |x 1| := h7
           _ ≤ (|(i : ℝ)| + 1) * δ + (|(j : ℝ)| + 1) * δ := by gcongr
           _ = R := by simp [R] <;> ring
    simpa [Metric.mem_closedBall] using h16
  exact Metric.isBounded_closedBall.subset h

/-! # Parent map and children count -/

def parentBy (m : ℕ) (idx : ℤ × ℤ) : ℤ × ℤ :=
  (idx.1 / (2^m : ℤ), idx.2 / (2^m : ℤ))

def childrenPerParent (m : ℕ) : ℕ := 4 ^ m

lemma childrenPerParent_gt_one {m : ℕ} (hm : 0 < m) : 1 < childrenPerParent m := by
  have h7 : 1 ≤ m := by omega
  have h8 : 4 ≤ (4 : ℕ) ^ m := by
    have h9 : (4 : ℕ) ^ 1 ≤ (4 : ℕ) ^ m := by
      gcongr <;> omega
    simpa using h9
  have h10 : 1 < (4 : ℕ) ^ m := by omega
  simpa [childrenPerParent] using h10

lemma int_ediv_ediv (a : ℤ) {b c : ℤ} (hb : 0 < b) (hc : 0 < c) :
    (a / b) / c = a / (b * c) := by
  set q : ℤ := a / (b * c) with hq
  set r : ℤ := a % (b * c) with hr
  have hbc : 0 < b * c := mul_pos hb hc
  have h_eq : a = q * (b * c) + r := by
    have h : (a / (b * c)) * (b * c) + a % (b * c) = a := Int.ediv_mul_add_emod a (b * c)
    simpa [hq, hr] using h.symm
  have hr_nonneg : 0 ≤ r := Int.emod_nonneg a (by linarith)
  have hr_lt : r < b * c := Int.emod_lt_of_pos a hbc
  set s : ℤ := r / b with hs
  have hs_nonneg : 0 ≤ s := by apply Int.ediv_nonneg <;> linarith
  have hs_lt : s < c := by
    by_contra h; have h' : s ≥ c := by linarith
    have h2 : s * b ≥ c * b := by gcongr
    have h3 : r ≥ s * b := by
      have h4 : r = s * b + r % b := by exact Eq.symm (Int.ediv_mul_add_emod r b)
      have h5 : 0 ≤ r % b := Int.emod_nonneg r (by linarith)
      linarith
    linarith
  have h6 : a = (q * c + s) * b + r % b := by
    have h7 : r = s * b + r % b := by exact Eq.symm (Int.ediv_mul_add_emod r b)
    linarith
  have h8 : 0 ≤ r % b := Int.emod_nonneg r (by linarith)
  have h9 : r % b < b := Int.emod_lt_of_pos r hb
  have h10 : a % b = r % b := by
    rw [h6, Int.add_emod, Int.mul_emod] <;> simp [h8] <;> omega
  have h11 : (a / b) * b + a % b = a := Int.ediv_mul_add_emod a b
  have h12 : a / b = q * c + s := by
    rw [h10] at h11
    apply (mul_right_inj' (show (b : ℤ) ≠ 0 from by linarith)).mp
    linarith
  rw [h12]
  have h13 : (q * c + s) % c = s := by
    have h14 : (q * c + s) % c = s % c := by
      rw [Int.add_emod, Int.mul_emod] <;> simp <;> omega
    rw [h14]
    have h15 : s % c = s := by
      rw [Int.emod_eq_of_lt] <;> linarith
    exact h15
  have h16 : ((q * c + s) / c) * c + (q * c + s) % c = q * c + s :=
    Int.ediv_mul_add_emod (q * c + s) c
  rw [h13] at h16
  have h17 : (q * c + s) / c = q := by
    apply (mul_right_inj' (show (c : ℤ) ≠ 0 from by linarith)).mp
    linarith
  exact h17

lemma parentBy_comp (m1 m2 : ℕ) (idx : ℤ × ℤ) :
    parentBy m1 (parentBy m2 idx) = parentBy (m1 + m2) idx := by
  have h_pos1 : 0 < (2 ^ m1 : ℤ) := by positivity
  have h_pos2 : 0 < (2 ^ m2 : ℤ) := by positivity
  have h1 : (idx.1 / (2 ^ m2 : ℤ)) / (2 ^ m1 : ℤ) =
      idx.1 / ((2 ^ m2 : ℤ) * (2 ^ m1 : ℤ)) :=
    int_ediv_ediv idx.1 h_pos2 h_pos1
  have h2 : (idx.2 / (2 ^ m2 : ℤ)) / (2 ^ m1 : ℤ) =
      idx.2 / ((2 ^ m2 : ℤ) * (2 ^ m1 : ℤ)) :=
    int_ediv_ediv idx.2 h_pos2 h_pos1
  have h3 : (2 ^ m2 : ℤ) * (2 ^ m1 : ℤ) = (2 ^ (m1 + m2) : ℤ) := by
    rw [← pow_add] <;> ring
  have h4 : (parentBy m1 (parentBy m2 idx)).1 = (parentBy (m1 + m2) idx).1 := by
    simp [parentBy, h1, h2, h3]
  have h5 : (parentBy m1 (parentBy m2 idx)).2 = (parentBy (m1 + m2) idx).2 := by
    simp [parentBy, h1, h2, h3]
  exact Prod.ext h4 h5

lemma max_children_bound (m : ℕ) (g : ℤ × ℤ) (items : Finset (ℤ × ℤ)) :
    (items.filter (fun idx => parentBy m idx = g)).card ≤ childrenPerParent m := by
  let I := Finset.Ico (g.1 * (2^m : ℤ)) ((g.1 + 1) * (2^m : ℤ))
  let J := Finset.Ico (g.2 * (2^m : ℤ)) ((g.2 + 1) * (2^m : ℤ))
  have h_pos : 0 < (2^m : ℤ) := by positivity
  have h1 : (items.filter (fun idx => parentBy m idx = g)) ⊆ I ×ˢ J := by
    intro idx hidx
    have h2 : parentBy m idx = g := (Finset.mem_filter.mp hidx).2
    have hdiv1 : idx.1 / (2^m : ℤ) = g.1 := by
      simpa [parentBy] using congr_arg Prod.fst h2
    have hdiv2 : idx.2 / (2^m : ℤ) = g.2 := by
      simpa [parentBy] using congr_arg Prod.snd h2
    have h4 : (idx.1 / (2^m : ℤ)) * (2^m : ℤ) ≤ idx.1 := by
      have h5 : idx.1 = (idx.1 / (2^m : ℤ)) * (2^m : ℤ) + idx.1 % (2^m : ℤ) :=
        (Int.ediv_mul_add_emod idx.1 (2^m : ℤ)).symm
      have h6 : 0 ≤ idx.1 % (2^m : ℤ) := Int.emod_nonneg idx.1 (by linarith)
      linarith
    have h5 : idx.1 < (g.1 + 1) * (2^m : ℤ) := by
      have h7 : idx.1 = (idx.1 / (2^m : ℤ)) * (2^m : ℤ) + idx.1 % (2^m : ℤ) :=
        (Int.ediv_mul_add_emod idx.1 (2^m : ℤ)).symm
      have h8 : idx.1 % (2^m : ℤ) < (2^m : ℤ) := Int.emod_lt_of_pos idx.1 h_pos
      rw [hdiv1] at h7
      linarith
    have h7 : (idx.2 / (2^m : ℤ)) * (2^m : ℤ) ≤ idx.2 := by
      have h8 : idx.2 = (idx.2 / (2^m : ℤ)) * (2^m : ℤ) + idx.2 % (2^m : ℤ) :=
        (Int.ediv_mul_add_emod idx.2 (2^m : ℤ)).symm
      have h9 : 0 ≤ idx.2 % (2^m : ℤ) := Int.emod_nonneg idx.2 (by linarith)
      linarith
    have h9 : idx.2 < (g.2 + 1) * (2^m : ℤ) := by
      have h10 : idx.2 = (idx.2 / (2^m : ℤ)) * (2^m : ℤ) + idx.2 % (2^m : ℤ) :=
        (Int.ediv_mul_add_emod idx.2 (2^m : ℤ)).symm
      have h11 : idx.2 % (2^m : ℤ) < (2^m : ℤ) := Int.emod_lt_of_pos idx.2 h_pos
      rw [hdiv2] at h10
      linarith
    have h4' : g.1 * (2^m : ℤ) ≤ idx.1 := by rw [← hdiv1]; exact h4
    have h7' : g.2 * (2^m : ℤ) ≤ idx.2 := by rw [← hdiv2]; exact h7
    exact Finset.mem_product.mpr ⟨by
      simp only [I, Finset.mem_Ico] <;> exact ⟨h4', h5⟩, by
      simp only [J, Finset.mem_Ico] <;> exact ⟨h7', h9⟩⟩
  have hI : I.card = 2^m := by
    have h_le : g.1 * (2^m : ℤ) ≤ (g.1 + 1) * (2^m : ℤ) := by
      have h : (0 : ℤ) ≤ (2^m : ℤ) := by positivity
      nlinarith
    have h : (I.card : ℤ) = ((g.1 + 1) * (2^m : ℤ)) - g.1 * (2^m : ℤ) := Int.card_Ico_of_le _ _ h_le
    have h' : (I.card : ℤ) = (2^m : ℤ) := by rw [h] <;> ring
    exact_mod_cast h'
  have hJ : J.card = 2^m := by
    have h_le2 : g.2 * (2^m : ℤ) ≤ (g.2 + 1) * (2^m : ℤ) := by
      have h : (0 : ℤ) ≤ (2^m : ℤ) := by positivity
      nlinarith
    have h : (J.card : ℤ) = ((g.2 + 1) * (2^m : ℤ)) - g.2 * (2^m : ℤ) := Int.card_Ico_of_le _ _ h_le2
    have h' : (J.card : ℤ) = (2^m : ℤ) := by rw [h] <;> ring
    exact_mod_cast h'
  calc
    (items.filter (fun idx => parentBy m idx = g)).card
      ≤ (I ×ˢ J).card := Finset.card_le_card h1
    _ = I.card * J.card := by rw [Finset.card_product]
    _ = (2^m) * (2^m) := by rw [hI, hJ]
    _ = 4^m := by
      have h : (2^m : ℕ) * (2^m : ℕ) = 4^m := by
        calc (2^m : ℕ) * (2^m : ℕ)
          = 2^(m + m) := by rw [← pow_add] <;> ring
        _ = 2^(2 * m) := by ring
        _ = (2^2)^m := by rw [pow_mul] <;> ring
        _ = 4^m := by norm_num
      exact h
    _ = childrenPerParent m := by rfl

/-! # Range uniformity property -/

/-- P is range-uniform across scales: for each j, each coarse square has
    either 0 or between N_j and 2*N_j fine squares. -/
def RangeUniformityProp (n : ℕ) (a : Fin (n + 1) → ℕ)
    (S : Finset (ℤ × ℤ)) (N : Fin n → ℕ) : Prop :=
  S.Nonempty ∧
  (∀ j : Fin n, 1 ≤ N j) ∧
  ∀ (j : Fin n) (g : ℤ × ℤ),
    let k := a (Fin.last n)
    let m_fine := k - a (Fin.succ j)
    let m_coarse := a (Fin.succ j) - a j.castSucc
    let fineSquares := S.image (parentBy m_fine)
    let count := (fineSquares.filter (fun idx => parentBy m_coarse idx = g)).card
    count = 0 ∨ (N j ≤ count ∧ count < 2 * N j)

/-! # Single-level range uniformization using pigeonhole_dyadic_range -/

lemma single_level_range (m : ℕ) (hm : 0 < m)
    (S : Finset (ℤ × ℤ)) (hS_nonempty : S.Nonempty) :
    ∃ (S1 : Finset (ℤ × ℤ)) (N : ℕ),
      0 < N ∧ S1 ⊆ S ∧
      (∀ (g : ℤ × ℤ),
        let count := (S1.filter (fun y => parentBy m y = g)).card
        count = 0 ∨ (N ≤ count ∧ count < 2 * N)) ∧
      (S1.card : ℝ) * (6 * Real.log ((childrenPerParent m : ℝ))) ≥ (S.card : ℝ) ∧
      (S1.card : ℝ) * (12 * Real.log ((childrenPerParent m : ℝ))) ≥ (S.card : ℝ) := by
  let M_max := childrenPerParent m
  have hMmax : 1 < M_max := childrenPerParent_gt_one hm
  let groups := S.image (parentBy m)
  let c : ℤ × ℤ → ℕ := fun g => (S.filter (fun y => parentBy m y = g)).card
  have hc1 : ∀ g ∈ groups, 1 ≤ c g := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨x, hx, h_eq⟩
    have h3 : x ∈ S.filter (fun y => parentBy m y = g) := by
      simp only [Finset.mem_filter] <;> exact ⟨hx, h_eq⟩
    exact Finset.card_pos.mpr ⟨x, h3⟩
  have hc2 : ∀ g ∈ groups, c g ≤ M_max := by
    intro g hg
    exact max_children_bound m g S
  have h_main := pigeonhole_dyadic_range groups c c M_max hMmax hc1 hc2
  rcases h_main with ⟨N, hNpos, h_size⟩
  let selected_groups := groups.filter (fun g => N ≤ c g ∧ c g < 2 * N)
  let S1 : Finset (ℤ × ℤ) := S.filter (fun x => parentBy m x ∈ selected_groups)
  have hS1_sub : S1 ⊆ S := Finset.filter_subset _ _
  have h_unif : ∀ (g : ℤ × ℤ),
      (S1.filter (fun y => parentBy m y = g)).card = 0 ∨
      (N ≤ (S1.filter (fun y => parentBy m y = g)).card ∧
       (S1.filter (fun y => parentBy m y = g)).card < 2 * N) := by
    intro g
    by_cases hg : g ∈ selected_groups
    · have h_eq : S1.filter (fun y => parentBy m y = g) = S.filter (fun y => parentBy m y = g) := by
        ext x
        simp only [S1, Finset.mem_filter]
        constructor
        · rintro ⟨⟨h_x_in_S, h_in_sel⟩, h_eq2⟩
          exact ⟨h_x_in_S, h_eq2⟩
        · rintro ⟨h_x_in_S, h_eq2⟩
          have h_in_sel : parentBy m x ∈ selected_groups := by rw [h_eq2]; exact hg
          exact ⟨⟨h_x_in_S, h_in_sel⟩, h_eq2⟩
      rw [h_eq]
      have h3 : N ≤ c g ∧ c g < 2 * N := (Finset.mem_filter.mp hg).2
      exact Or.inr h3
    · have h_eq : S1.filter (fun y => parentBy m y = g) = ∅ := by
        ext x
        constructor
        · intro h
          have h' : x ∈ S1 ∧ parentBy m x = g := by
            simpa [Finset.mem_filter] using h
          rcases h' with ⟨h_x_in_S1, h_eq2⟩
          have h5 : parentBy m x ∈ selected_groups := (Finset.mem_filter.mp h_x_in_S1).2
          rw [h_eq2] at h5
          exact False.elim (hg h5)
        · intro h; contradiction
      rw [h_eq]; simp
  have h_card : S1.card = ∑ g ∈ selected_groups, c g := by
    have h_disj : Set.PairwiseDisjoint (↑selected_groups) (fun g => S.filter (fun y => parentBy m y = g)) := by
      intro g _ h _ hne; simp only [Finset.disjoint_left]; intro x hx1 hx2
      have h5 : parentBy m x = g := (Finset.mem_filter.mp hx1).2
      have h6 : parentBy m x = h := (Finset.mem_filter.mp hx2).2
      rw [h5] at h6; exact hne h6
    have h_eq : S1 = selected_groups.biUnion (fun g => S.filter (fun y => parentBy m y = g)) := by
      ext x; simp [S1] <;> tauto
    rw [h_eq, Finset.card_biUnion h_disj] <;> rfl
  have h_sum_groups : (∑ g ∈ groups, c g) = S.card := by
    have h_disj : Set.PairwiseDisjoint (↑groups) (fun g => S.filter (fun y => parentBy m y = g)) := by
      intro g _ h _ hne; simp only [Finset.disjoint_left]; intro x hx1 hx2
      have h5 : parentBy m x = g := (Finset.mem_filter.mp hx1).2
      have h6 : parentBy m x = h := (Finset.mem_filter.mp hx2).2
      rw [h5] at h6; exact hne h6
    have h_eq : S = groups.biUnion (fun g => S.filter (fun y => parentBy m y = g)) := by
      ext x; simp [groups] <;> tauto
    rw [h_eq, Finset.card_biUnion h_disj] <;> rfl
  have h_size' : (S1.card : ℝ) * (6 * Real.log (M_max : ℝ)) ≥ (S.card : ℝ) := by
    have h : (∑ g ∈ selected_groups, (c g : ℝ)) * (6 * Real.log (M_max : ℝ)) ≥ (∑ g ∈ groups, (c g : ℝ)) := h_size
    have h_card' : (S1.card : ℝ) = ∑ g ∈ selected_groups, (c g : ℝ) := by
      exact_mod_cast h_card
    have h_sum' : (S.card : ℝ) = ∑ g ∈ groups, (c g : ℝ) := by
      exact_mod_cast h_sum_groups.symm
    rw [h_card', h_sum']
    exact h
  have h_final : (S1.card : ℝ) * (12 * Real.log (M_max : ℝ)) ≥ (S.card : ℝ) := by
    have h_pos : 0 < Real.log (M_max : ℝ) := Real.log_pos (by exact_mod_cast hMmax)
    linarith
  exact ⟨S1, N, hNpos, hS1_sub, h_unif, h_size', h_final⟩

/-! # Multi-level uniformization by induction -/

lemma multi_level_indices (n : ℕ) :
    ∀ (a : Fin (n + 1) → ℕ), (∀ j : Fin n, a j.castSucc < a (Fin.succ j)) →
    ∀ (S : Finset (ℤ × ℤ)), S.Nonempty →
    ∃ (S' : Finset (ℤ × ℤ)) (N : Fin n → ℕ),
      S' ⊆ S ∧ RangeUniformityProp n a S' N ∧
      (S'.card : ℝ) *
        ∏ j : Fin n, (12 * Real.log ((childrenPerParent (a (Fin.succ j) - a j.castSucc) : ℝ))) ≥
      (S.card : ℝ) := by
  induction n with
  | zero =>
    intro a _ S hS_nonempty
    refine ⟨S, (fun _ : Fin 0 => 0), ?_, ?_, ?_⟩
    · tauto
    · exact ⟨hS_nonempty, by simp, by simp⟩
    · simp
  | succ n ih =>
    intro a ha_strict S hS_nonempty
    let j_last : Fin (n + 1) := Fin.last n
    let m_finest := a (Fin.succ j_last) - a j_last.castSucc
    have hm_finest_pos : 0 < m_finest := by
      have h := ha_strict j_last
      simpa [m_finest, j_last] using h
    rcases single_level_range m_finest hm_finest_pos S hS_nonempty with
      ⟨S1, N_finest, hNpos, hS1_sub, h_unif_finest, h_size1_6, h_size1_12⟩
    have hS1_nonempty : S1.Nonempty := by
      have h_pos : 0 < S.card := hS_nonempty.card_pos
      have hlog_pos : 0 < 12 * Real.log ((childrenPerParent m_finest : ℝ)) := by
        have h1 : 1 < (childrenPerParent m_finest : ℝ) := by
          simpa using childrenPerParent_gt_one hm_finest_pos
        have h2 : 0 < Real.log ((childrenPerParent m_finest : ℝ)) := Real.log_pos h1
        linarith
      have h_card_pos : 0 < S1.card := by
        by_contra h4
        have h5 : S1.card = 0 := by omega
        have h6 : (S1.card : ℝ) = 0 := by exact_mod_cast h5
        rw [h6] at h_size1_12
        have h7 : (0 : ℝ) * (12 * Real.log ((childrenPerParent m_finest : ℝ))) = 0 := by simp
        rw [h7] at h_size1_12
        have h8 : (S.card : ℝ) ≤ 0 := h_size1_12
        have h9 : 0 < (S.card : ℝ) := by exact_mod_cast h_pos
        exact not_le.mpr h9 h8
      exact Finset.card_pos.mp h_card_pos
    let T1 := S1.image (parentBy m_finest)
    have hT1_nonempty : T1.Nonempty := hS1_nonempty.image _
    let a' : Fin (n + 1) → ℕ := fun i => a i.castSucc
    have ha'_strict : ∀ j : Fin n, a' j.castSucc < a' (Fin.succ j) := by
      intro j; exact ha_strict j.castSucc
    rcases ih a' ha'_strict T1 hT1_nonempty with
      ⟨T', N_coarse, hT'_sub, h_unif_coarse, h_size_coarse⟩
    let S' : Finset (ℤ × ℤ) := S1.filter (fun q => parentBy m_finest q ∈ T')
    have hS'_sub_S1 : S' ⊆ S1 := Finset.filter_subset _ _
    have hS'_sub : S' ⊆ S := hS'_sub_S1.trans hS1_sub
    have hS'_nonempty : S'.Nonempty := by
      have hT'_nonempty : T'.Nonempty := h_unif_coarse.1
      rcases hT'_nonempty with ⟨t, ht⟩
      have h1 : t ∈ T1 := hT'_sub ht
      rcases Finset.mem_image.mp h1 with ⟨s1, hs1, rfl⟩
      have h2 : s1 ∈ S' := by
        simp only [S', Finset.mem_filter] <;> exact ⟨hs1, ht⟩
      exact ⟨s1, h2⟩
    have h_unif_S'_finest : ∀ (g : ℤ × ℤ),
        (S'.filter (fun y => parentBy m_finest y = g)).card = 0 ∨
        (N_finest ≤ (S'.filter (fun y => parentBy m_finest y = g)).card ∧
         (S'.filter (fun y => parentBy m_finest y = g)).card < 2 * N_finest) := by
      intro g
      by_cases hg : g ∈ T'
      · have h_eq : S'.filter (fun y => parentBy m_finest y = g) =
            S1.filter (fun y => parentBy m_finest y = g) := by
          ext x; simp only [S', Finset.mem_filter] <;> aesop
        rw [h_eq]
        exact h_unif_finest g
      · have h_eq : S'.filter (fun y => parentBy m_finest y = g) = ∅ := by
          ext x
          constructor
          · intro h
            have hmem := Finset.mem_filter.mp h
            have h_x_in_S' : x ∈ S' := hmem.1
            have h_eq2 : parentBy m_finest x = g := hmem.2
            have h4 : parentBy m_finest x ∈ T' := (Finset.mem_filter.mp h_x_in_S').2
            rw [h_eq2] at h4
            exact False.elim (hg h4)
          · intro h; contradiction
        rw [h_eq]; simp
    let T'_actual := S'.image (parentBy m_finest)
    have hT'_eq : T'_actual = T' := by
      ext g
      simp only [T'_actual, Finset.mem_image]
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact (Finset.mem_filter.mp hq).2
      · intro hg
        have h1 : g ∈ T1 := hT'_sub hg
        rcases Finset.mem_image.mp h1 with ⟨t, ht, rfl⟩
        have h2 : parentBy m_finest t ∈ T' := hg
        have h3 : t ∈ S' := by
          simp only [S', Finset.mem_filter] <;> exact ⟨ht, h2⟩
        exact ⟨t, h3, rfl⟩
    let N : Fin (n + 1) → ℕ := fun i =>
      if h : i.val < n then N_coarse ⟨i.val, h⟩ else N_finest
    have hN_last : N (Fin.last n) = N_finest := by
      have h1 : (Fin.last n).val = n := by exact Fin.val_last n
      have h2 : ¬((Fin.last n).val < n) := by rw [h1] <;> omega
      simp [N, h2]
    have hN_coarse : ∀ (j : Fin n), N j.castSucc = N_coarse j := by
      intro j
      have h1 : (j.castSucc : Fin (n + 1)).val < n := j.is_lt
      simp [N, h1]
      <;> apply Fin.ext <;> simp
    have h_unif_all : RangeUniformityProp (n + 1) a S' N := by
      refine ⟨hS'_nonempty, fun j => ?_, fun j g => ?_⟩
      · by_cases h : j = Fin.last n
        · rw [h]; rw [hN_last]; exact hNpos
        · have h_j_lt_n : j.val < n := by
            have h1 : j.val < n + 1 := j.is_lt
            have h2 : j.val ≠ n := by
              intro h3; have h4 : j = Fin.last n := by
                apply Fin.ext
                have h5 : j.val = n := by omega
                simpa [Fin.last] using h5
              exact h h4
            omega
          let j' : Fin n := ⟨j.val, h_j_lt_n⟩
          have h_j'_cast : j'.castSucc = j := by
            apply Fin.ext
            simp [j']
          have h_goal : N j = N_coarse j' := by
            have h1 : N j'.castSucc = N_coarse j' := hN_coarse j'
            have h2 : N j = N j'.castSucc := by rw [h_j'_cast]
            exact h2.trans h1
          rw [h_goal]
          exact h_unif_coarse.2.1 j'
      · by_cases h : j = Fin.last n
        · subst h
          have h_last_eq1 : Fin.last (n + 1) = Fin.succ (Fin.last n) := by
            apply Fin.ext <;> simp [Fin.last]
          have h_eq1 : a (Fin.last (n + 1)) - a (Fin.succ (Fin.last n)) = 0 := by
            rw [h_last_eq1] <;> simp
          have h_eq2 : a (Fin.succ (Fin.last n)) - a ((Fin.last n).castSucc) = m_finest := by rfl
          have h_parent0 : parentBy 0 = id := by
            funext x; simp [parentBy]
          have h_goal : ∀ (g : ℤ × ℤ),
              let k := a (Fin.last (n + 1))
              let m_fine := k - a (Fin.succ (Fin.last n))
              let m_coarse := a (Fin.succ (Fin.last n)) - a ((Fin.last n).castSucc)
              let fineSquares := S'.image (parentBy m_fine)
              let count := (fineSquares.filter (fun idx => parentBy m_coarse idx = g)).card
              count = 0 ∨ (N (Fin.last n) ≤ count ∧ count < 2 * N (Fin.last n)) := by
            intro g
            have h_image_id : S'.image id = S' := by
              rw [Finset.image_id]
            simp only [h_eq1, h_eq2, h_parent0, h_image_id, hN_last]
            exact h_unif_S'_finest g
          simpa using h_goal g
        · have h_j_lt_n : j.val < n := by
            have h1 : j.val < n + 1 := j.is_lt
            have h2 : j.val ≠ n := by
              intro h3; have h4 : j = Fin.last n := by
                apply Fin.ext
                have h5 : j.val = n := by omega
                simpa [Fin.last] using h5
              exact h h4
            omega
          let j' : Fin n := ⟨j.val, h_j_lt_n⟩
          have h_j'_cast : j'.castSucc = j := by
            apply Fin.ext <;> simp [j']
          have h_j'_succ_cast : (Fin.succ j').castSucc = Fin.succ j := by
            apply Fin.ext <;> simp [j']
          have ha_mono : ∀ (x y : Fin (n + 2)), x.val ≤ y.val → a x ≤ a y := by
            intro x y hxy
            have h_main : ∀ (k : ℕ), x.val + k ≤ n + 1 →
                ∃ (z : Fin (n + 2)), z.val = x.val + k ∧ a x ≤ a z := by
              intro k
              induction k with
              | zero =>
                intro hk
                refine ⟨x, by omega, le_refl _⟩
              | succ k ih =>
                intro hk
                rcases ih (by omega) with ⟨z, hz_val, h_ineq⟩
                have hz_lt : z.val < n + 1 := by omega
                let j0 : Fin (n + 1) := ⟨z.val, hz_lt⟩
                have h1 : (j0.castSucc : Fin (n + 2)) = z := by
                  apply Fin.ext <;> simp [j0]
                have h2 : a z < a (Fin.succ j0) := by
                  rw [←h1]
                  exact ha_strict j0
                refine ⟨Fin.succ j0, ?_, le_trans h_ineq (le_of_lt h2)⟩
                simp [j0, hz_val] <;> omega
            rcases h_main (y.val - x.val) (by omega) with ⟨z, hz_val, h_ineq⟩
            have hz_eq_y : z = y := by
              apply Fin.ext
              omega
            rw [hz_eq_y] at h_ineq
            exact h_ineq
          have h_last_eq1 : Fin.last (n + 1) = Fin.succ (Fin.last n) := by
            apply Fin.ext <;> simp [Fin.last]
          have h_le1 : a (Fin.succ j) ≤ a ((Fin.last n).castSucc) := by
            apply ha_mono <;> simp [Fin.last, h_j'_cast] <;> omega
          have h_le2 : a ((Fin.last n).castSucc) ≤ a (Fin.succ (Fin.last n)) := by
            apply ha_mono <;> simp [Fin.last] <;> omega
          have h3 : a (Fin.last (n + 1)) - a (Fin.succ j) =
              m_finest + (a' (Fin.last n) - a' (Fin.succ j')) := by
            have h4 : a (Fin.last (n + 1)) = a (Fin.succ (Fin.last n)) := by rw [h_last_eq1]
            have h5 : a' (Fin.last n) = a ((Fin.last n).castSucc) := by rfl
            have h6 : a' (Fin.succ j') = a (Fin.succ j) := by
              have h7 : a' (Fin.succ j') = a ((Fin.succ j').castSucc) := by rfl
              rw [h7, h_j'_succ_cast]
            rw [h4, h5, h6]
            have h_lemma : ∀ (x y z : ℕ), x ≤ y → y ≤ z → (z - y) + (y - x) = z - x := by
              intro x y z hxy hyz; omega
            have h_eq2 : (a (Fin.succ (Fin.last n)) - a ((Fin.last n).castSucc)) + (a ((Fin.last n).castSucc) - a (Fin.succ j)) =
                a (Fin.succ (Fin.last n)) - a (Fin.succ j) :=
              h_lemma (a (Fin.succ j)) (a ((Fin.last n).castSucc)) (a (Fin.succ (Fin.last n))) h_le1 h_le2
            exact h_eq2.symm
          let m_coarse := a' (Fin.last n) - a' (Fin.succ j')
          have h_image_eq : S'.image (parentBy (a (Fin.last (n + 1)) - a (Fin.succ j))) =
              T'.image (parentBy m_coarse) := by
            ext x
            simp only [Finset.mem_image]
            constructor
            · rintro ⟨q, hq, rfl⟩
              have h1 : parentBy m_finest q ∈ T' := (Finset.mem_filter.mp hq).2
              have h2 : parentBy m_coarse (parentBy m_finest q) =
                  parentBy (a (Fin.last (n + 1)) - a (Fin.succ j)) q := by
                rw [h3]
                have h4 := parentBy_comp m_coarse m_finest q
                have h_comm : m_coarse + m_finest = m_finest + m_coarse := by omega
                rw [h_comm] at h4
                exact h4
              exact ⟨parentBy m_finest q, h1, h2⟩
            · rintro ⟨t, ht, h_eq_val⟩
              rcases Finset.mem_image.mp (hT'_sub ht) with ⟨q, hq, h_eq_t⟩
              have hq' : q ∈ S' := by
                simp only [S', Finset.mem_filter] <;> exact ⟨hq, h_eq_t ▸ ht⟩
              have h2 : parentBy (a (Fin.last (n + 1)) - a (Fin.succ j)) q =
                  parentBy m_coarse t := by
                rw [h3]
                have h4 := parentBy_comp m_coarse m_finest q
                have h_comm : m_coarse + m_finest = m_finest + m_coarse := by omega
                rw [h_comm] at h4
                rw [h_eq_t] at h4
                exact h4.symm
              have h5 : parentBy (a (Fin.last (n + 1)) - a (Fin.succ j)) q = x := by
                rw [h2, h_eq_val]
              exact ⟨q, hq', h5⟩
          have h_coarse_eq : N j = N_coarse j' := by
            have h1 : N j'.castSucc = N_coarse j' := hN_coarse j'
            have h2 : N j = N j'.castSucc := by rw [h_j'_cast]
            exact h2.trans h1
          rw [h_coarse_eq]
          have h_mc : a ((Fin.last n).castSucc) - a (Fin.succ j) = m_coarse := by rfl
          have h_main := h_unif_coarse.2.2 j' g
          simp only [RangeUniformityProp, a', h_j'_cast, h_j'_succ_cast] at h_main
          rw [h_mc] at h_main
          rw [←h_image_eq] at h_main
          exact h_main
    have h_prod : ∏ j : Fin (n + 1), (12 * Real.log ((childrenPerParent (a (Fin.succ j) - a j.castSucc) : ℝ))) =
        (12 * Real.log ((childrenPerParent m_finest : ℝ))) *
        ∏ j : Fin n, (12 * Real.log ((childrenPerParent (a' (Fin.succ j) - a' j.castSucc) : ℝ))) := by
      let f : Fin (n + 1) → ℝ := fun j => 12 * Real.log ((childrenPerParent (a (Fin.succ j) - a j.castSucc) : ℝ))
      have h_inj : Function.Injective (Fin.castSucc : Fin n → Fin (n + 1)) := by
        intro a b h; apply Fin.ext; simpa [Fin.ext_iff] using h
      have h_inj' : Set.InjOn (Fin.castSucc : Fin n → Fin (n + 1)) (↑(Finset.univ : Finset (Fin n))) :=
        fun x _ y _ h => h_inj h
      have h3 : (Finset.univ.erase (Fin.last n)) = Finset.image Fin.castSucc (Finset.univ : Finset (Fin n)) := by
        ext x; simp [Fin.ext_iff] <;> omega
      have h41 : (∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase (Fin.last n), f j) * f (Fin.last n) =
          ∏ j : Fin (n + 1), f j := by
        have h_notin : Fin.last n ∉ (Finset.univ.erase (Fin.last n)) := by simp
        have h_eq : insert (Fin.last n) ((Finset.univ.erase (Fin.last n))) = (Finset.univ : Finset (Fin (n + 1))) := by
          rw [Finset.insert_erase (Finset.mem_univ _)]
        have h : ∏ j ∈ insert (Fin.last n) ((Finset.univ.erase (Fin.last n))), f j =
            f (Fin.last n) * ∏ j ∈ (Finset.univ.erase (Fin.last n)), f j :=
          Finset.prod_insert h_notin
        rw [h_eq] at h
        have h_comm : f (Fin.last n) * ∏ j ∈ (Finset.univ.erase (Fin.last n)), f j =
            (∏ j ∈ (Finset.univ.erase (Fin.last n)), f j) * f (Fin.last n) := by ring
        rw [h_comm] at h
        exact h.symm
      have h4 : f (Fin.last n) * ∏ j ∈ (Finset.univ.erase (Fin.last n)), f j = ∏ j : Fin (n + 1), f j := by
        rw [mul_comm]
        exact h41
      have h5 : ∏ j : Fin (n + 1), f j = f (Fin.last n) * ∏ j ∈ (Finset.univ.erase (Fin.last n)), f j := h4.symm
      rw [h5, h3, Finset.prod_image h_inj']
      <;> rfl
    rw [h_prod]
    have h_S'_ge : (S'.card : ℝ) ≥ (N_finest : ℝ) * (T'.card : ℝ) := by
      have h : S'.card = ∑ g ∈ T', (S'.filter (fun y => parentBy m_finest y = g)).card := by
        have h_disj : Set.PairwiseDisjoint (↑T') (fun g => S'.filter (fun y => parentBy m_finest y = g)) := by
          intro g _ h _ hne; simp only [Finset.disjoint_left]; intro x hx1 hx2
          have h5 : parentBy m_finest x = g := (Finset.mem_filter.mp hx1).2
          have h6 : parentBy m_finest x = h := (Finset.mem_filter.mp hx2).2
          rw [h5] at h6; exact hne h6
        have h_card : (T'.biUnion (fun g => S'.filter (fun y => parentBy m_finest y = g))).card =
            ∑ g ∈ T', (S'.filter (fun y => parentBy m_finest y = g)).card := by
          rw [Finset.card_biUnion h_disj]
          <;> rfl
        have h_eq : S' = T'.biUnion (fun g => S'.filter (fun y => parentBy m_finest y = g)) := by
          ext x; simp [S'] <;> tauto
        have h1 : S'.card = (T'.biUnion (fun g => S'.filter (fun y => parentBy m_finest y = g))).card := by
          exact congr_arg (fun X : Finset (ℤ × ℤ) => X.card) h_eq
        exact h1.trans h_card
      rw [h]
      have h5 : ∀ g ∈ T', N_finest ≤ (S'.filter (fun y => parentBy m_finest y = g)).card := by
        intro g hg
        have h6 := h_unif_S'_finest g
        rcases h6 with (h6 | h6)
        · exfalso
          have h7 : g ∈ T'_actual := by rw [hT'_eq]; exact hg
          rcases Finset.mem_image.mp h7 with ⟨x, hx, h_eq_g⟩
          have h8 : x ∈ S'.filter (fun y => parentBy m_finest y = g) := by
            simp only [Finset.mem_filter]; exact ⟨hx, h_eq_g⟩
          have h9 : (S'.filter (fun y => parentBy m_finest y = g)) = ∅ := by
            rw [←Finset.card_eq_zero]; exact h6
          rw [h9] at h8; simp at h8
        · exact h6.1
      have h6 : ∑ g ∈ T', (S'.filter (fun y => parentBy m_finest y = g)).card ≥ ∑ g ∈ T', N_finest := by
        apply Finset.sum_le_sum; intro g hg; exact h5 g hg
      have h7 : ∑ g ∈ T', N_finest = N_finest * T'.card := by
        simp [Finset.sum_const] <;> ring
      rw [h7] at h6
      exact_mod_cast h6
    have h_S1_le : (S1.card : ℝ) ≤ 2 * (N_finest : ℝ) * (T1.card : ℝ) := by
      have h : S1.card = ∑ g ∈ T1, (S1.filter (fun y => parentBy m_finest y = g)).card := by
        have h_disj : Set.PairwiseDisjoint (↑T1) (fun g => S1.filter (fun y => parentBy m_finest y = g)) := by
          intro g _ h _ hne; simp only [Finset.disjoint_left]; intro x hx1 hx2
          have h5 : parentBy m_finest x = g := (Finset.mem_filter.mp hx1).2
          have h6 : parentBy m_finest x = h := (Finset.mem_filter.mp hx2).2
          rw [h5] at h6; exact hne h6
        have h_card2 : (T1.biUnion (fun g => S1.filter (fun y => parentBy m_finest y = g))).card =
            ∑ g ∈ T1, (S1.filter (fun y => parentBy m_finest y = g)).card := by
          rw [Finset.card_biUnion h_disj]
          <;> rfl
        have h_eq2 : S1 = T1.biUnion (fun g => S1.filter (fun y => parentBy m_finest y = g)) := by
          ext x; simp [T1] <;> tauto
        have h1 : S1.card = (T1.biUnion (fun g => S1.filter (fun y => parentBy m_finest y = g))).card := by
          exact congr_arg (fun X : Finset (ℤ × ℤ) => X.card) h_eq2
        exact h1.trans h_card2
      rw [h]
      have h5 : ∀ g ∈ T1, (S1.filter (fun y => parentBy m_finest y = g)).card < 2 * N_finest := by
        intro g hg
        have h6 := h_unif_finest g
        rcases h6 with (h6 | h6)
        · exfalso
          have h7 : g ∈ T1 := hg
          rcases Finset.mem_image.mp h7 with ⟨x, hx, h_eq_g⟩
          have h8 : x ∈ S1.filter (fun y => parentBy m_finest y = g) := by
            simp only [Finset.mem_filter]; exact ⟨hx, h_eq_g⟩
          have h9 : (S1.filter (fun y => parentBy m_finest y = g)) = ∅ := by
            rw [←Finset.card_eq_zero]; exact h6
          rw [h9] at h8; simp at h8
        · exact h6.2
      have h6 : ∑ g ∈ T1, (S1.filter (fun y => parentBy m_finest y = g)).card ≤ ∑ g ∈ T1, (2 * N_finest) := by
        apply Finset.sum_le_sum; intro g hg; exact Nat.le_of_lt (h5 g hg)
      have h7 : ∑ g ∈ T1, (2 * N_finest) = 2 * N_finest * T1.card := by
        simp [Finset.sum_const] <;> ring
      rw [h7] at h6
      exact_mod_cast h6
    let P : ℝ := ∏ j : Fin n, (12 * Real.log ((childrenPerParent (a' (Fin.succ j) - a' j.castSucc) : ℝ)))
    have h_size_coarse' : (T'.card : ℝ) * P ≥ (T1.card : ℝ) := h_size_coarse
    have h_final : (S'.card : ℝ) * (12 * Real.log ((childrenPerParent m_finest : ℝ))) * P ≥ (S.card : ℝ) := by
      have hlog_pos : 0 < Real.log ((childrenPerParent m_finest : ℝ)) := by
        have h1 : 1 < (childrenPerParent m_finest : ℝ) := by
          simpa using childrenPerParent_gt_one hm_finest_pos
        exact Real.log_pos h1
      calc
        (S'.card : ℝ) * (12 * Real.log ((childrenPerParent m_finest : ℝ))) * P
          ≥ (N_finest : ℝ) * (T'.card : ℝ) * (12 * Real.log ((childrenPerParent m_finest : ℝ))) * P := by gcongr
        _ = (N_finest : ℝ) * (12 * Real.log ((childrenPerParent m_finest : ℝ))) * ((T'.card : ℝ) * P) := by ring
        _ ≥ (N_finest : ℝ) * (12 * Real.log ((childrenPerParent m_finest : ℝ))) * (T1.card : ℝ) := by
          gcongr
          <;> exact h_size_coarse'
        _ ≥ (S1.card : ℝ) * (6 * Real.log ((childrenPerParent m_finest : ℝ))) := by
          have h9 : (N_finest : ℝ) * (12 * Real.log ((childrenPerParent m_finest : ℝ))) * (T1.card : ℝ) =
              (2 * (N_finest : ℝ) * (T1.card : ℝ)) * (6 * Real.log ((childrenPerParent m_finest : ℝ))) := by ring
          rw [h9]
          gcongr <;> linarith
        _ ≥ (S.card : ℝ) := h_size1_6
    have h_final' : (S'.card : ℝ) * ((12 * Real.log ((childrenPerParent m_finest : ℝ))) * P) ≥ (S.card : ℝ) := by
      have h_assoc : (S'.card : ℝ) * ((12 * Real.log ((childrenPerParent m_finest : ℝ))) * P) =
          (S'.card : ℝ) * (12 * Real.log ((childrenPerParent m_finest : ℝ))) * P := by ring
      rw [h_assoc]
      exact h_final
    exact ⟨S', N, hS'_sub, h_unif_all, h_final'⟩

/-! # From indices to geometric sets -/

def setFromIndices (δ : ℝ) (S : Finset (ℤ × ℤ)) : Set EuclideanPlane :=
  ⋃ idx ∈ S, dyadicSquare δ idx.1 idx.2

lemma setFromIndices_subset {δ : ℝ} {S S' : Finset (ℤ × ℤ)} (h : S' ⊆ S) :
    setFromIndices δ S' ⊆ setFromIndices δ S := by
  intro x hx
  rcases Set.mem_iUnion₂.mp hx with ⟨idx, hidx, hx2⟩
  exact Set.mem_iUnion₂.mpr ⟨idx, h hidx, hx2⟩

/-- Dyadic squares at same scale are equal or disjoint. -/
lemma dyadicSquare_eq_or_disjoint (δ : ℝ) (hδ_pos : 0 < δ)
    (i1 j1 i2 j2 : ℤ) :
    (dyadicSquare δ i1 j1 = dyadicSquare δ i2 j2) ∨
    Disjoint (dyadicSquare δ i1 j1) (dyadicSquare δ i2 j2) := by
  by_cases h : i1 = i2 ∧ j1 = j2
  · rcases h with ⟨rfl, rfl⟩; exact Or.inl rfl
  · have h' : i1 ≠ i2 ∨ j1 ≠ j2 := by tauto
    exact Or.inr (by
      simp only [dyadicSquare, Set.disjoint_left, Set.mem_setOf_eq]
      intro x h1 h2
      rcases h' with (h_i | h_j)
      · -- i1 ≠ i2: x-coordinate intervals disjoint
        have h41 : x 0 ∈ Set.Ico ((i1 : ℝ) * δ) (((i1 : ℝ) + 1) * δ) := h1.1
        have h42 : x 0 ∈ Set.Ico ((i2 : ℝ) * δ) (((i2 : ℝ) + 1) * δ) := h2.1
        have : i1 = i2 := by
          by_contra hne
          have h_lt : i1 < i2 ∨ i2 < i1 := by omega
          rcases h_lt with (h_lt | h_lt)
          · have h6 : i1 + 1 ≤ i2 := by omega
            have h7 : ((i1 : ℝ) + 1) * δ ≤ (i2 : ℝ) * δ := by gcongr <;> exact_mod_cast h6
            have h8 : x 0 < ((i1 : ℝ) + 1) * δ := h41.2
            have h9 : (i2 : ℝ) * δ ≤ x 0 := h42.1
            linarith
          · have h6 : i2 + 1 ≤ i1 := by omega
            have h7 : ((i2 : ℝ) + 1) * δ ≤ (i1 : ℝ) * δ := by gcongr <;> exact_mod_cast h6
            have h8 : x 0 < ((i2 : ℝ) + 1) * δ := h42.2
            have h9 : (i1 : ℝ) * δ ≤ x 0 := h41.1
            linarith
        exact h_i this
      · -- j1 ≠ j2: y-coordinate intervals disjoint
        have h41 : x 1 ∈ Set.Ico ((j1 : ℝ) * δ) (((j1 : ℝ) + 1) * δ) := h1.2
        have h42 : x 1 ∈ Set.Ico ((j2 : ℝ) * δ) (((j2 : ℝ) + 1) * δ) := h2.2
        have : j1 = j2 := by
          by_contra hne
          have h_lt : j1 < j2 ∨ j2 < j1 := by omega
          rcases h_lt with (h_lt | h_lt)
          · have h6 : j1 + 1 ≤ j2 := by omega
            have h7 : ((j1 : ℝ) + 1) * δ ≤ (j2 : ℝ) * δ := by gcongr <;> exact_mod_cast h6
            have h8 : x 1 < ((j1 : ℝ) + 1) * δ := h41.2
            have h9 : (j2 : ℝ) * δ ≤ x 1 := h42.1
            linarith
          · have h6 : j2 + 1 ≤ j1 := by omega
            have h7 : ((j2 : ℝ) + 1) * δ ≤ (j1 : ℝ) * δ := by gcongr <;> exact_mod_cast h6
            have h8 : x 1 < ((j2 : ℝ) + 1) * δ := h42.2
            have h9 : (j1 : ℝ) * δ ≤ x 1 := h41.1
            linarith
        exact h_j this)

/-- If P is a union of δ-squares, any δ-square meeting P is contained in P. -/
lemma meeting_square_subset (δ : ℝ) (hδ_pos : 0 < δ)
    (P : Set EuclideanPlane)
    (hP_union : ∀ (x : EuclideanPlane), x ∈ P →
      ∃ (i j : ℤ), x ∈ dyadicSquare δ i j ∧ (dyadicSquare δ i j : Set EuclideanPlane) ⊆ P)
    {i j : ℤ} (h_meet : (dyadicSquare δ i j ∩ P).Nonempty) :
    (dyadicSquare δ i j) ⊆ P := by
  rcases h_meet with ⟨x, hxQ, hxP⟩
  rcases hP_union x hxP with ⟨i', j', hxQ', hQ'_sub⟩
  have h_eq : (dyadicSquare δ i j) = (dyadicSquare δ i' j') := by
    rcases dyadicSquare_eq_or_disjoint δ hδ_pos i j i' j' with (h | h)
    · exact h
    · exfalso
      exact Set.disjoint_left.mp h hxQ hxQ'
  rw [h_eq]
  exact hQ'_sub

/-- q.toSet equals dyadicSquare at the same scale. -/
lemma dyadicCube_toSet_eq (nδ : ℕ) (q : DyadicCube nδ) :
    q.toSet = dyadicSquare (dyadicDelta nδ) q.i q.j := by
  ext y
  have hside : q.side = dyadicDelta nδ := by rfl
  simp only [DyadicCube.toSet, dyadicSquare, Set.mem_setOf_eq, Set.mem_Ico]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rw [hside] at h1 h2 h3 h4
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    rw [← hside] at h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩

/-- A dyadic cube is bounded. -/
lemma dyadicCube_isBounded (nδ : ℕ) (q : DyadicCube nδ) :
    Bornology.IsBounded (q.toSet) := by
  have h1 : q.toSet ⊆ Metric.closedBall q.lower (q.side * Real.sqrt 2) := by
    intro x hx
    have h2 : dist x q.lower ≤ q.side * Real.sqrt 2 :=
      DyadicCube.dist_le_side_sqrt2 hx q.lower_mem
    exact h2
  exact Metric.isBounded_closedBall.subset h1

/-- Count of dyadic squares meeting setFromIndices equals the finset card. -/
lemma setFromIndices_isBounded (nδ : ℕ) (S : Finset (ℤ × ℤ)) :
    Bornology.IsBounded (setFromIndices (dyadicDelta nδ) S) := by
  have h : ∀ idx ∈ S, Bornology.IsBounded (dyadicSquare (dyadicDelta nδ) idx.1 idx.2) := by
    intro idx _
    exact dyadicSquare_isBounded (dyadicDelta nδ) (dyadicDelta_pos nδ) idx.1 idx.2
  have h_union : Bornology.IsBounded (setFromIndices (dyadicDelta nδ) S) := by
    induction S using Finset.induction with
    | empty =>
      simp [setFromIndices]
      <;> exact Bornology.isBounded_empty
    | @insert idx S' hidx ih =>
      have h_S' : ∀ idx ∈ S', Bornology.IsBounded (dyadicSquare (dyadicDelta nδ) idx.1 idx.2) :=
        fun i hi => h i (Finset.mem_insert_of_mem hi)
      have h_eq : setFromIndices (dyadicDelta nδ) (insert idx S') =
          dyadicSquare (dyadicDelta nδ) idx.1 idx.2 ∪ setFromIndices (dyadicDelta nδ) S' := by
        ext x
        simp [setFromIndices, Finset.mem_insert, Set.mem_iUnion₂]
        <;> tauto
      rw [h_eq]
      exact Bornology.IsBounded.union (h idx (Finset.mem_insert_self idx S')) (ih h_S')
  exact h_union

lemma count_eq_card (nδ : ℕ) (S : Finset (ℤ × ℤ)) (hS_nonempty : S.Nonempty) :
    DyadicCubes.dyadicCoveringNumber nδ (setFromIndices (dyadicDelta nδ) S)
      (setFromIndices_isBounded nδ S) = S.card := by
  let P := setFromIndices (dyadicDelta nδ) S
  have h_main : ∀ (q : DyadicCube nδ),
      (q.toSet ∩ P).Nonempty ↔ (q.i, q.j) ∈ S := by
    intro q
    constructor
    · rintro ⟨x, hxq, hxP⟩
      rcases Set.mem_iUnion₂.mp hxP with ⟨idx, hidx, hxidx⟩
      have h_disj : q.toSet = dyadicSquare (dyadicDelta nδ) q.i q.j := dyadicCube_toSet_eq nδ q
      rw [h_disj] at hxq
      have h_eq : (q.i, q.j) = idx := by
        have hq1 := Set.mem_Ico.mp hxq.1
        have hq2 := Set.mem_Ico.mp hxq.2
        have hi1 := Set.mem_Ico.mp hxidx.1
        have hi2 := Set.mem_Ico.mp hxidx.2
        have hi : q.i = idx.1 := by
          have hδ_pos' : 0 < dyadicDelta nδ := dyadicDelta_pos nδ
          by_contra hne; have h5 : q.i ≤ idx.1 ∨ idx.1 ≤ q.i := by omega
          rcases h5 with (h5 | h5)
          · have h6 : q.i + 1 ≤ idx.1 := by omega
            have h7 : ((q.i : ℝ) + 1) * dyadicDelta nδ ≤ (idx.1 : ℝ) * dyadicDelta nδ := by gcongr <;> exact_mod_cast h6
            linarith
          · have h6 : idx.1 + 1 ≤ q.i := by omega
            have h7 : ((idx.1 : ℝ) + 1) * dyadicDelta nδ ≤ (q.i : ℝ) * dyadicDelta nδ := by gcongr <;> exact_mod_cast h6
            linarith
        have hj : q.j = idx.2 := by
          have hδ_pos' : 0 < dyadicDelta nδ := dyadicDelta_pos nδ
          by_contra hne; have h5 : q.j ≤ idx.2 ∨ idx.2 ≤ q.j := by omega
          rcases h5 with (h5 | h5)
          · have h6 : q.j + 1 ≤ idx.2 := by omega
            have h7 : ((q.j : ℝ) + 1) * dyadicDelta nδ ≤ (idx.2 : ℝ) * dyadicDelta nδ := by gcongr <;> exact_mod_cast h6
            linarith
          · have h6 : idx.2 + 1 ≤ q.j := by omega
            have h7 : ((idx.2 : ℝ) + 1) * dyadicDelta nδ ≤ (q.j : ℝ) * dyadicDelta nδ := by gcongr <;> exact_mod_cast h6
            linarith
        exact Prod.ext hi hj
      rw [h_eq]; exact hidx
    · intro h
      let idx := (q.i, q.j)
      have hidx : idx ∈ S := h
      have hq_set : q.toSet = dyadicSquare (dyadicDelta nδ) q.i q.j := dyadicCube_toSet_eq nδ q
      have h_nonempty : q.toSet.Nonempty := ⟨q.lower, q.lower_mem⟩
      rcases h_nonempty with ⟨x, hx⟩
      have hx2 : x ∈ P := by
        have h3 : x ∈ dyadicSquare (dyadicDelta nδ) q.i q.j := by
          rw [← hq_set]; exact hx
        exact Set.mem_iUnion₂.mpr ⟨idx, hidx, h3⟩
      exact ⟨x, hx, hx2⟩
  have hD_eq : D_nFinset nδ P (setFromIndices_isBounded nδ S) =
      S.image (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : DyadicCube nδ)) := by
    ext q
    simp only [D_nFinset_mem, Finset.mem_image]
    rw [h_main q]
    constructor
    · intro h
      refine ⟨(q.i, q.j), h, ?_⟩
      cases q <;> rfl
    · rintro ⟨p, hp, rfl⟩
      exact hp
  have h_inj : Set.InjOn (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : DyadicCube nδ)) (S : Set (ℤ × ℤ)) := by
    intro p _ q _ h
    have h1 : p.1 = q.1 ∧ p.2 = q.2 := by simpa using h
    exact Prod.ext h1.1 h1.2
  rw [DyadicCubes.dyadicCoveringNumber, hD_eq, Finset.card_image_of_injOn h_inj]

/-! # dyadicDelta anti-monotonicity -/

lemma dyadicDelta_anti {m n : ℕ} (h : m ≤ n) : dyadicDelta n ≤ dyadicDelta m := by
  simp only [dyadicDelta]
  have h1 : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ n := by
    gcongr <;> norm_num <;> linarith
  have h2 : 0 < (2 : ℝ) ^ m := by positivity
  have h3 : 0 < (2 : ℝ) ^ n := by positivity
  have h4 : 1 / (2 : ℝ) ^ n ≤ 1 / (2 : ℝ) ^ m := by
    gcongr
    <;> linarith
  exact h4

/-! # Telescoping ratio -/

lemma telescoping_ratio (n : ℕ) (Δ : Fin (n + 1) → ℝ) (hΔ_pos : ∀ i, 0 < Δ i) :
    ∏ j : Fin n, Δ (Fin.succ j) / Δ j.castSucc = Δ (Fin.last n) / Δ 0 := by
  have h_main : ∀ (m : ℕ) (f : Fin (m + 1) → ℝ), (∀ i, 0 < f i) →
      ∏ j : Fin m, f (Fin.succ j) / f j.castSucc = f (Fin.last m) / f 0 := by
    intro m
    induction m with
    | zero =>
      intro f hf
      have h_last0 : (Fin.last 0 : Fin 1) = 0 := by decide
      have h : f (Fin.last 0) / f 0 = 1 := by
        rw [h_last0]
        <;> field_simp [(hf 0).ne']
      exact h.symm
    | succ m ih =>
      intro f hf
      let f' : Fin (m + 1) → ℝ := fun i => f (Fin.succ i)
      have hf' : ∀ i, 0 < f' i := fun i => hf (Fin.succ i)
      have h_ih := ih f' hf'
      calc
        (∏ j : Fin (m + 1), f (Fin.succ j) / f j.castSucc)
          = (f (Fin.succ 0) / f 0) * ∏ j : Fin m, f (Fin.succ (Fin.succ j)) / f ((Fin.succ j).castSucc) := by
            rw [Fin.prod_univ_succ] <;> congr with j <;> simp
        _ = (f (Fin.succ 0) / f 0) * ∏ j : Fin m, f' (Fin.succ j) / f' j.castSucc := by
          apply congr_arg (fun x => (f (Fin.succ 0) / f 0) * x)
          have h_eq2 : ∏ j : Fin m, f (Fin.succ (Fin.succ j)) / f ((Fin.succ j).castSucc) =
              ∏ j : Fin m, f' (Fin.succ j) / f' j.castSucc := by
            refine Finset.prod_congr rfl ?_
            intro j _
            have h3 : (Fin.succ j).castSucc = Fin.succ (j.castSucc) := by rfl
            simp [f', h3] <;> rfl
          exact h_eq2
        _ = (f (Fin.succ 0) / f 0) * (f' (Fin.last m) / f' 0) := by rw [h_ih]
        _ = (f (Fin.succ 0) / f 0) * (f (Fin.last (m + 1)) / f (Fin.succ 0)) := by
          simp [f', Fin.last] <;> rfl
        _ = f (Fin.last (m + 1)) / f 0 := by
          have h_ne1 : f (Fin.succ 0) ≠ 0 := (hf (Fin.succ 0)).ne'
          have h_ne2 : f 0 ≠ 0 := (hf 0).ne'
          field_simp [h_ne1, h_ne2] <;> ring
  exact h_main n Δ hΔ_pos

/-! # AM-GM -/

lemma prod_rpow {α : Type*} (s : Finset α) (f : α → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (r : ℝ) :
    ∏ i ∈ s, f i ^ r = (∏ i ∈ s, f i) ^ r := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hprod_nonneg : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg hfs
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih hfs]
    rw [← Real.mul_rpow hfa hprod_nonneg]

lemma am_gm_real {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hx_pos : ∀ i, 0 < x i) :
    ∏ i : Fin n, x i ≤ ((∑ i : Fin n, x i) / (n : ℝ)) ^ n := by
  let s : Finset (Fin n) := Finset.univ
  let w : Fin n → ℝ := fun _ => 1 / (n : ℝ)
  have hw_nonneg : ∀ i ∈ s, 0 ≤ w i := by intro i _; positivity
  have hw_sum : ∑ i ∈ s, w i = 1 := by
    have hcard : s.card = n := by simp [s]
    have h : ∑ i ∈ s, w i = (s.card : ℝ) * (1 / (n : ℝ)) := by
      calc
        ∑ i ∈ s, w i = ∑ i ∈ s, (1 / (n : ℝ)) := by apply Finset.sum_congr rfl; intro i _; rfl
        _ = (s.card : ℝ) * (1 / (n : ℝ)) := by
          rw [Finset.sum_const]
          <;> simp [nsmul_eq_mul] <;> norm_cast
    rw [h, hcard]
    field_simp [hn.ne'] <;> ring
  have hz_nonneg : ∀ i ∈ s, 0 ≤ x i := by intro i _; exact le_of_lt (hx_pos i)
  have h1 : ∏ i ∈ s, x i ^ (w i) ≤ ∑ i ∈ s, w i * x i :=
    Real.geom_mean_le_arith_mean_weighted (s := s) w x hw_nonneg hw_sum hz_nonneg
  have h2 : ∏ i ∈ s, x i ^ (w i) = (∏ i ∈ s, x i) ^ (1 / (n : ℝ)) := by
    have h3 : ∀ i ∈ s, x i ^ (w i) = x i ^ (1 / (n : ℝ)) := by intro i _; rfl
    rw [Finset.prod_congr rfl h3]
    exact prod_rpow s x hz_nonneg (1 / (n : ℝ))
  have h4 : ∑ i ∈ s, w i * x i = (∑ i ∈ s, x i) / (n : ℝ) := by
    have h5 : ∑ i ∈ s, w i * x i = ∑ i ∈ s, ((1 / (n : ℝ)) * x i) := by
      apply Finset.sum_congr rfl; intro i _; rfl
    rw [h5]
    have h6 : ∑ i ∈ s, ((1 / (n : ℝ)) * x i) = (1 / (n : ℝ)) * ∑ i ∈ s, x i := by
      rw [Finset.mul_sum]
    rw [h6] <;> ring
  rw [h2, h4] at h1
  set P : ℝ := ∏ i ∈ s, x i with hP
  set A : ℝ := (∑ i ∈ s, x i) / (n : ℝ) with hA
  have hP_nonneg : 0 ≤ P := by
    apply Finset.prod_nonneg; intro i _; exact le_of_lt (hx_pos i)
  have hA_pos : 0 < A := by
    dsimp only [A]
    have hsum_pos : 0 < ∑ i ∈ s, x i := by
      apply Finset.sum_pos
      · intro i _; exact hx_pos i
      · have hne : s.Nonempty := by
          simp [s]
          refine ⟨⟨0, hn⟩, by simp⟩
        exact hne
    positivity
  have h5 : P ^ (1 / (n : ℝ)) ≤ A := h1
  have h6 : P ≤ A ^ n := by
    have h7 : (P ^ (1 / (n : ℝ))) ^ n ≤ A ^ n := by gcongr
    have h81 : (P ^ (1 / (n : ℝ))) ^ (n : ℝ) = (P ^ (1 / (n : ℝ))) ^ n := by
      rw [Real.rpow_natCast]
    have h8 : (P ^ (1 / (n : ℝ))) ^ n = P := by
      have h9 : (1 / (n : ℝ)) * (n : ℝ) = 1 := by field_simp [hn.ne'] <;> ring
      have h10 : (P ^ (1 / (n : ℝ))) ^ (n : ℝ) = P ^ ((1 / (n : ℝ)) * (n : ℝ)) := by
        rw [← Real.rpow_mul hP_nonneg]
      have h11 : (P ^ (1 / (n : ℝ))) ^ (n : ℝ) = P := by
        rw [h10, h9, Real.rpow_one]
      rw [← h81]
      exact h11
    rw [h8] at h7; exact h7
  simpa [hP, hA] using h6

/-! # Main theorem -/

/-- Multi-level uniformization (OS Lemma 7.1) using dyadic square counts. -/
theorem basic_uniformization_dyadic
    (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (nδ : ℕ) (hδ_eq : δ = dyadicDelta nδ)
    (Δ : Fin (n + 1) → ℝ)
    (hΔ_dyadic : ∀ i, Δ i ∈ dyadicScales)
    (hΔ_pos : ∀ i, 0 < Δ i)
    (hΔ_strict : ∀ j : Fin n, Δ (Fin.succ j) < Δ j.castSucc)
    (hΔ_end : Δ (Fin.last n) = δ)
    (hΔ_start : Δ 0 = 1)
    (P : Set EuclideanPlane)
    (hP_bounded : Bornology.IsBounded P)
    (hP_nonempty : P.Nonempty)
    (hP_union_squares : ∀ (x : EuclideanPlane), x ∈ P →
      ∃ (i j : ℤ), x ∈ dyadicSquare δ i j ∧
        (dyadicSquare δ i j : Set EuclideanPlane) ⊆ P) :
    ∃ (S' : Finset (ℤ × ℤ)) (N : Fin n → ℕ),
      (setFromIndices δ S') ⊆ P ∧
      RangeUniformityProp n (fun i => Classical.choose (hΔ_dyadic i)) S' N ∧
      (DyadicCubes.dyadicCoveringNumber nδ (setFromIndices δ S')
        (hδ_eq.symm ▸ setFromIndices_isBounded nδ S') : ℝ) ≥
      (DyadicCubes.dyadicCoveringNumber nδ P hP_bounded : ℝ) /
        ((24 * Real.log (1 / δ) / (n : ℝ)) ^ n) := by
  let a : Fin (n + 1) → ℕ := fun i => Classical.choose (hΔ_dyadic i)
  have ha_spec : ∀ i, Δ i = (2 : ℝ)^(-(a i : ℤ)) := by
    intro i; exact Classical.choose_spec (hΔ_dyadic i)
  have ha_eq_delta : ∀ i, Δ i = dyadicDelta (a i) := by
    intro i
    have h1 : Δ i = (2 : ℝ)^(-(a i : ℤ)) := ha_spec i
    have h2 : dyadicDelta (a i) = (2 : ℝ)^(-(a i : ℤ)) := by
      simp [dyadicDelta] <;> field_simp <;> ring
    rw [h1, h2]
  have ha_strict : ∀ j : Fin n, a j.castSucc < a (Fin.succ j) := by
    intro j
    have h1 : Δ (Fin.succ j) < Δ j.castSucc := hΔ_strict j
    rw [ha_eq_delta (Fin.succ j), ha_eq_delta j.castSucc] at h1
    have h2 : dyadicDelta (a (Fin.succ j)) < dyadicDelta (a j.castSucc) := h1
    have h3 : a j.castSucc < a (Fin.succ j) := by
      contrapose h2
      have h4 : a (Fin.succ j) ≤ a j.castSucc := by linarith
      have h5 : dyadicDelta (a j.castSucc) ≤ dyadicDelta (a (Fin.succ j)) := dyadicDelta_anti h4
      linarith
    exact h3
  have h_delta_inj : Function.Injective dyadicDelta := by
    intro m n h
    simp only [dyadicDelta] at h
    have h_pos1 : 0 < (2 : ℝ) ^ m := by positivity
    have h_pos2 : 0 < (2 : ℝ) ^ n := by positivity
    have h2 : (2 : ℝ) ^ m = (2 : ℝ) ^ n := by
      calc
        (2 : ℝ) ^ m
          = 1 / (1 / (2 : ℝ) ^ m) := by field_simp [h_pos1.ne'] <;> ring
        _ = 1 / (1 / (2 : ℝ) ^ n) := by rw [h]
        _ = (2 : ℝ) ^ n := by field_simp [h_pos2.ne'] <;> ring
    have h_strict_mono : StrictMono (fun k : ℕ => (2 : ℝ) ^ k) := by
      intro a b h
      have h6 : (1 : ℕ) < 2 := by norm_num
      have h7 : (2 : ℕ) ^ a < (2 : ℕ) ^ b := Nat.pow_lt_pow_right h6 h
      have h8 : (2 : ℝ) ^ a < (2 : ℝ) ^ b := by
        have h9 : ((2 : ℝ) ^ a) = ↑((2 : ℕ) ^ a) := by norm_cast
        have h10 : ((2 : ℝ) ^ b) = ↑((2 : ℕ) ^ b) := by norm_cast
        rw [h9, h10]
        exact_mod_cast h7
      exact h8
    exact h_strict_mono.injective h2
  have h1 : Δ (Fin.last n) = dyadicDelta (a (Fin.last n)) := ha_eq_delta (Fin.last n)
  have h2 : Δ (Fin.last n) = δ := hΔ_end
  have h3 : dyadicDelta (a (Fin.last n)) = dyadicDelta nδ := by
    rw [← h1, h2, hδ_eq]
  have h_a_last_eq : a (Fin.last n) = nδ := h_delta_inj h3
  let S_dyadic : Finset (DyadicCube nδ) := D_nFinset nδ P hP_bounded
  let S : Finset (ℤ × ℤ) := S_dyadic.image (fun q => (q.i, q.j))
  have hS_nonempty : S.Nonempty := by
    rcases hP_nonempty with ⟨x, hx⟩
    have h1 : ∃ (q : DyadicCube nδ), x ∈ q.toSet := by
      have hcov : (⋃ (i : ℤ), ⋃ (j : ℤ), (⟨i, j⟩ : DyadicCube nδ).toSet) = Set.univ :=
        DyadicCube.cover nδ
      have h2 : x ∈ (⋃ (i : ℤ), ⋃ (j : ℤ), (⟨i, j⟩ : DyadicCube nδ).toSet) := by
        rw [hcov] <;> trivial
      have h3 := Set.mem_iUnion.mp h2
      rcases h3 with ⟨i, h2⟩
      have h4 := Set.mem_iUnion.mp h2
      rcases h4 with ⟨j, hx⟩
      exact ⟨⟨i, j⟩, hx⟩
    rcases h1 with ⟨q, hxq⟩
    have hq_in : q ∈ S_dyadic := by
      rw [D_nFinset_mem]; exact ⟨x, hxq, hx⟩
    have h : S.Nonempty := by
      apply Finset.Nonempty.image
      exact ⟨q, hq_in⟩
    exact h
  have hP_eq : P = setFromIndices (dyadicDelta nδ) S := by
    ext x
    constructor
    · intro hx
      rcases hP_union_squares x hx with ⟨i, j, hxQ, hQ_sub⟩
      let q : DyadicCube nδ := ⟨i, j⟩
      have hq_in_S : (i, j) ∈ S := by
        have hq_meet : (q.toSet ∩ P).Nonempty := ⟨x, by
          have h_eq : q.toSet = dyadicSquare (dyadicDelta nδ) i j := dyadicCube_toSet_eq nδ q
          have hxQ' : x ∈ dyadicSquare (dyadicDelta nδ) i j := by
            rw [← hδ_eq]; exact hxQ
          rw [h_eq]; exact hxQ', hx⟩
        have hqD : q ∈ S_dyadic := by
          rw [D_nFinset_mem]; exact hq_meet
        exact Finset.mem_image.mpr ⟨q, hqD, rfl⟩
      have hδ_eq2 : δ = dyadicDelta nδ := hδ_eq
      have hxQ' : x ∈ dyadicSquare (dyadicDelta nδ) i j := by
        rw [← hδ_eq2]; exact hxQ
      exact Set.mem_iUnion₂.mpr ⟨(i, j), hq_in_S, hxQ'⟩
    · intro h
      have h2 : ∃ (idx : ℤ × ℤ), idx ∈ (↑S : Set (ℤ × ℤ)) ∧ x ∈ dyadicSquare (dyadicDelta nδ) idx.1 idx.2 := by
        simpa [setFromIndices, Set.mem_iUnion₂] using h
      rcases h2 with ⟨idx, hidx, hxidx⟩
      have h_S_def : S = S_dyadic.image (fun q : DyadicCube nδ => (q.i, q.j)) := by rfl
      rw [h_S_def] at hidx
      rcases Finset.mem_image.mp hidx with ⟨q, hqD, rfl⟩
      have hq_meet : (q.toSet ∩ P).Nonempty := (D_nFinset_mem nδ).mp hqD
      have hP_union_squares' : ∀ (x : EuclideanPlane), x ∈ P →
          ∃ (i j : ℤ), x ∈ dyadicSquare (dyadicDelta nδ) i j ∧
            (dyadicSquare (dyadicDelta nδ) i j : Set EuclideanPlane) ⊆ P := by
        intro x hx
        rcases hP_union_squares x hx with ⟨i, j, hxQ, hQ_sub⟩
        have hxQ' : x ∈ dyadicSquare (dyadicDelta nδ) i j := by
          rw [← hδ_eq]; exact hxQ
        have hQ_sub' : dyadicSquare (dyadicDelta nδ) i j ⊆ P := by
          have h_eq2 : dyadicSquare (dyadicDelta nδ) i j = dyadicSquare δ i j := by
            congr <;> exact hδ_eq.symm
          rw [h_eq2]
          exact hQ_sub
        exact ⟨i, j, hxQ', hQ_sub'⟩
      have hq_meet' : (dyadicSquare (dyadicDelta nδ) q.i q.j ∩ P).Nonempty := by
        have h_eq : q.toSet = dyadicSquare (dyadicDelta nδ) q.i q.j := dyadicCube_toSet_eq nδ q
        rw [h_eq] at hq_meet
        exact hq_meet
      exact meeting_square_subset (dyadicDelta nδ) (dyadicDelta_pos nδ) P hP_union_squares'
        (i := q.i) (j := q.j) hq_meet' hxidx
  rcases multi_level_indices n a ha_strict S hS_nonempty with
    ⟨S', N, hS'_sub, h_unif, h_size⟩
  let P' : Set EuclideanPlane := setFromIndices (dyadicDelta nδ) S'
  have hP'_sub : P' ⊆ P := by
    rw [hP_eq]
    exact setFromIndices_subset hS'_sub
  have hP'_eq : P' = setFromIndices δ S' := by
    have hδ_eq2 : δ = dyadicDelta nδ := hδ_eq
    rw [hδ_eq2] <;> rfl
  have h_count_P' : DyadicCubes.dyadicCoveringNumber nδ (setFromIndices δ S')
      (hδ_eq.symm ▸ setFromIndices_isBounded nδ S') = S'.card := by
    subst hδ_eq
    exact count_eq_card nδ S' h_unif.1
  have h_count_P : DyadicCubes.dyadicCoveringNumber nδ P hP_bounded = S.card := by
    have hP_bounded' : Bornology.IsBounded (setFromIndices (dyadicDelta nδ) S) :=
      setFromIndices_isBounded nδ S
    have h : DyadicCubes.dyadicCoveringNumber nδ (setFromIndices (dyadicDelta nδ) S) hP_bounded' = S.card :=
      count_eq_card nδ S hS_nonempty
    have h_eq1 : P = setFromIndices (dyadicDelta nδ) S := hP_eq
    simpa [h_eq1] using h
  let x : Fin n → ℝ := fun j => Real.log ((childrenPerParent (a (Fin.succ j) - a j.castSucc) : ℝ))
  have hx_pos : ∀ j, 0 < x j := by
    intro j
    have hm_pos : 0 < a (Fin.succ j) - a j.castSucc := Nat.sub_pos_of_lt (ha_strict j)
    have h1 : 1 < (childrenPerParent (a (Fin.succ j) - a j.castSucc) : ℝ) := by
      exact_mod_cast childrenPerParent_gt_one hm_pos
    exact Real.log_pos h1
  have h_sum : ∑ j : Fin n, x j = 2 * Real.log (1 / δ) := by
    have h1 : ∀ j : Fin n, x j = 2 * Real.log (Δ j.castSucc / Δ (Fin.succ j)) := by
      intro j
      let m := a (Fin.succ j) - a j.castSucc
      have hm_pos : 0 < m := Nat.sub_pos_of_lt (ha_strict j)
      have hm2 : a (Fin.succ j) = a j.castSucc + m := by omega
      have h_eq1 : Δ j.castSucc / Δ (Fin.succ j) = (2 : ℝ) ^ m := by
        rw [ha_eq_delta j.castSucc, ha_eq_delta (Fin.succ j), hm2]
        simp [dyadicDelta, pow_add] <;> field_simp <;> ring
      have h2 : x j = Real.log ((childrenPerParent m : ℝ)) := by rfl
      rw [h2]
      have h3 : (childrenPerParent m : ℝ) = (4 : ℝ) ^ m := by simp [childrenPerParent] <;> norm_cast
      rw [h3, h_eq1]
      have hlog4 : Real.log 4 = 2 * Real.log 2 := by
        have h : Real.log 4 = Real.log (2 ^ 2) := by norm_num
        rw [h, Real.log_pow] <;> norm_num
      have h4 : Real.log ((4 : ℝ) ^ m) = 2 * (m : ℝ) * Real.log 2 := by
        rw [Real.log_pow, hlog4] <;> ring
      have h5 : Real.log ((2 : ℝ) ^ m) = (m : ℝ) * Real.log 2 := by
        rw [Real.log_pow] <;> ring
      rw [h4, h5] <;> ring
    have h_sum1 : ∑ j : Fin n, x j = ∑ j : Fin n, (2 * Real.log (Δ j.castSucc / Δ (Fin.succ j))) := by
      apply Finset.sum_congr rfl; intro j _; exact h1 j
    rw [h_sum1]
    have h51 : ∑ j : Fin n, (2 * Real.log (Δ j.castSucc / Δ (Fin.succ j))) =
        2 * ∑ j : Fin n, Real.log (Δ j.castSucc / Δ (Fin.succ j)) := by
      rw [Finset.mul_sum]
    rw [h51]
    have hpos' : ∀ j ∈ (Finset.univ : Finset (Fin n)), (Δ j.castSucc / Δ (Fin.succ j)) ≠ 0 := by
      intro j _; have h := div_pos (hΔ_pos j.castSucc) (hΔ_pos (Fin.succ j)); exact h.ne'
    have h52 : ∑ j : Fin n, Real.log (Δ j.castSucc / Δ (Fin.succ j)) =
        Real.log (∏ j : Fin n, (Δ j.castSucc / Δ (Fin.succ j))) := by
      rw [← Real.log_prod hpos']
    rw [h52]
    have h6 : ∏ j : Fin n, (Δ j.castSucc / Δ (Fin.succ j)) = Δ 0 / Δ (Fin.last n) := by
      have h71 : ∏ j : Fin n, (Δ j.castSucc / Δ (Fin.succ j)) =
          ∏ j : Fin n, (Δ (Fin.succ j) / Δ j.castSucc)⁻¹ := by
        apply Finset.prod_congr rfl
        intro j _
        have hpos1 : 0 < Δ j.castSucc := hΔ_pos j.castSucc
        have hpos2 : 0 < Δ (Fin.succ j) := hΔ_pos (Fin.succ j)
        field_simp [hpos1.ne', hpos2.ne'] <;> ring
      have h72 : ∏ j : Fin n, (Δ (Fin.succ j) / Δ j.castSucc)⁻¹ =
          (∏ j : Fin n, (Δ (Fin.succ j) / Δ j.castSucc))⁻¹ := by
        let g : Fin n → ℝ := fun j => Δ (Fin.succ j) / Δ j.castSucc
        have hnz : ∀ j ∈ (Finset.univ : Finset (Fin n)), g j ≠ 0 := by
          intro j _; have hpos := div_pos (hΔ_pos (Fin.succ j)) (hΔ_pos j.castSucc); exact hpos.ne'
        have h_main : ∀ (s : Finset (Fin n)), (∀ j ∈ s, g j ≠ 0) →
            ∏ j ∈ s, (g j)⁻¹ = (∏ j ∈ s, g j)⁻¹ := by
          intro s
          induction s using Finset.induction with
          | empty =>
            intro _; simp
          | @insert a s ha ih =>
            intro hnz_all
            have hnz_a : g a ≠ 0 := hnz_all a (Finset.mem_insert_self a s)
            have hnz_s : ∀ j ∈ s, g j ≠ 0 := fun j hj => hnz_all j (Finset.mem_insert_of_mem hj)
            rw [Finset.prod_insert ha, Finset.prod_insert ha, ih hnz_s]
            field_simp [hnz_a] <;> ring
        exact h_main Finset.univ hnz
      rw [h71, h72, telescoping_ratio n Δ hΔ_pos]
      have hpos0 : 0 < Δ 0 := hΔ_pos 0
      have hpos_last : 0 < Δ (Fin.last n) := hΔ_pos (Fin.last n)
      rw [inv_div] <;> ring
    rw [h6, hΔ_start, hΔ_end] <;> ring
  have h_am_gm : ∏ j : Fin n, x j ≤ ((∑ j : Fin n, x j) / (n : ℝ)) ^ n :=
    am_gm_real hn x hx_pos
  rw [h_sum] at h_am_gm
  have h_loss : ∏ j : Fin n, (12 * x j) ≤ (24 * Real.log (1 / δ) / (n : ℝ)) ^ n := by
    have h7 : ∏ j : Fin n, (12 * x j) = 12 ^ n * ∏ j : Fin n, x j := by
      rw [Finset.prod_mul_distrib] <;> simp
    rw [h7]
    have h8 : 12 ^ n * ∏ j : Fin n, x j ≤ 12 ^ n * ((2 * Real.log (1 / δ) / (n : ℝ)) ^ n) := by
      gcongr <;> linarith
    have h9 : 12 ^ n * ((2 * Real.log (1 / δ) / (n : ℝ)) ^ n) =
        (24 * Real.log (1 / δ) / (n : ℝ)) ^ n := by
      have h10 : (12 : ℝ) ^ n * ((2 * Real.log (1 / δ) / (n : ℝ)) ^ n) =
          ((12 : ℝ) * (2 * Real.log (1 / δ) / (n : ℝ))) ^ n := by
        rw [← mul_pow] <;> ring
      rw [h10] <;> ring
    exact h8.trans (le_of_eq h9)
  have h10 : (S'.card : ℝ) ≥ (S.card : ℝ) / ((24 * Real.log (1 / δ) / (n : ℝ)) ^ n) := by
    have h11 : (S'.card : ℝ) * ∏ j : Fin n, (12 * x j) ≥ (S.card : ℝ) := h_size
    have h_pos : 0 < ∏ j : Fin n, (12 * x j) := by
      apply Finset.prod_pos; intro j _; have h12 : 0 < x j := hx_pos j; linarith
    have h13 : (S.card : ℝ) / (∏ j : Fin n, (12 * x j)) ≤ (S'.card : ℝ) := by
      have h : (S.card : ℝ) ≤ (S'.card : ℝ) * (∏ j : Fin n, (12 * x j)) := h11
      have hpos : 0 < ∏ j : Fin n, (12 * x j) := h_pos
      calc
        (S.card : ℝ) / (∏ j : Fin n, (12 * x j))
          ≤ ((S'.card : ℝ) * (∏ j : Fin n, (12 * x j))) / (∏ j : Fin n, (12 * x j)) := by gcongr
        _ = (S'.card : ℝ) := by
          have hpos_ne : (∏ j : Fin n, (12 * x j)) ≠ 0 := hpos.ne'
          have h_eq : ((S'.card : ℝ) * (∏ j : Fin n, (12 * x j))) / (∏ j : Fin n, (12 * x j)) =
              (S'.card : ℝ) * ((∏ j : Fin n, (12 * x j)) / (∏ j : Fin n, (12 * x j))) := by
            rw [mul_div_assoc]
          rw [h_eq]
          have h_div : (∏ j : Fin n, (12 * x j)) / (∏ j : Fin n, (12 * x j)) = 1 := div_self hpos_ne
          rw [h_div] <;> ring
    have h14 : (∏ j : Fin n, (12 * x j)) ≤ (24 * Real.log (1 / δ) / (n : ℝ)) ^ n := h_loss
    have h15 : 0 < (24 * Real.log (1 / δ) / (n : ℝ)) ^ n := by
      have h16 : 0 < 24 * Real.log (1 / δ) / (n : ℝ) := by
        have h17 : 1 < 1 / δ := by
          apply one_lt_one_div
          <;> linarith
        have h18 : 0 < Real.log (1 / δ) := Real.log_pos h17
        positivity
      positivity
    have h19 : (S.card : ℝ) / ((24 * Real.log (1 / δ) / (n : ℝ)) ^ n) ≤
        (S.card : ℝ) / (∏ j : Fin n, (12 * x j)) := by
      apply div_le_div_of_nonneg_left
      · exact Nat.cast_nonneg S.card
      · exact h_pos
      · exact h14
    exact h19.trans h13
  have h_main_ineq : (DyadicCubes.dyadicCoveringNumber nδ (setFromIndices δ S')
        (hδ_eq.symm ▸ setFromIndices_isBounded nδ S') : ℝ) ≥
      (DyadicCubes.dyadicCoveringNumber nδ P hP_bounded : ℝ) / ((24 * Real.log (1 / δ) / (n : ℝ)) ^ n) := by
    rw [h_count_P', h_count_P]
    exact h10
  have h_final_sub : (setFromIndices δ S') ⊆ P := by
    rw [← hP'_eq]
    exact hP'_sub
  exact ⟨S', N, h_final_sub, h_unif, h_main_ineq⟩

end DiscretisedFurstenbergEstimate.BasicUniformization
