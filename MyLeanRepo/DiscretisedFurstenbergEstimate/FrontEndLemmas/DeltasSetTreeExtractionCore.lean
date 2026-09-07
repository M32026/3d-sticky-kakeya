module

/-
  DeltasSet extraction via maximal capacity-respecting subset.

  Algorithm:
  1. Work at dyadic scale s = dyadicDelta n with s ≤ δ < 2s
  2. Pick one representative per s-cube meeting P → leaves
  3. Find maximal subset Pbar satisfying capacity bounds at all dyadic levels
  4. Half-capacity cover: greedily split cubes until each has ≥ cap/2 survivors
  5. Cover covers all original leaves (by maximality)
  6. Mass lower bound via S-set cancellation on the cover
  7. S-set property from capacity bounds
  8. Modulo-3 coloring for δ-separation

  Whiteprint node: fine_point_thinning
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.RobustKaufmanProjection.Basics
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate

abbrev Ncover (δ : ℝ) (E : Set EuclideanPlane) : ENNReal :=
  Metric.externalCoveringNumber δ.toNNReal E

/-! ### Helper: coordinate bound -/

lemma abs_coord_le_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  have h1 : (x i)^2 ≤ ‖x‖^2 := by
    have h2 : ‖x‖^2 = ∑ j : Fin n, (x j)^2 := by
      have h21 : ‖x‖ = Real.sqrt (∑ j : Fin n, (x j)^2) := by
        simp [EuclideanSpace.norm_eq]
      rw [h21]
      have h22 : 0 ≤ ∑ j : Fin n, (x j)^2 := by positivity
      rw [Real.sq_sqrt h22]
    rw [h2]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have h3 : 0 ≤ ‖x‖ := by positivity
  nlinarith [sq_abs (x i)]

/-! ### Dyadic square helpers (standalone to avoid namespace issues) -/

/-- Ancestor of a level-k dyadic square at level j (j ≤ k). -/
def dyadicAncestor {k : ℕ} (j : ℕ) (h : j ≤ k) (Q : DiscretisedFurstenbergEstimate.DyadicSquare k) :
    DiscretisedFurstenbergEstimate.DyadicSquare j :=
  let shift : ℤ := 2 ^ (k - j)
  ⟨Q.i / shift, Q.j / shift⟩

/-- Capacity of a level-j cube at base scale n: (side_j / side_n)^u. -/
def dyadicCap (n j : ℕ) (u : ℝ) : ℝ :=
  (dyadicDelta j / dyadicDelta n) ^ u

lemma dyadicDelta_antitone {j k : ℕ} (h : j ≤ k) : dyadicDelta j ≥ dyadicDelta k := by
  have h1 : 1 ≤ (2 : ℝ) := by norm_num
  have h2 : (2 : ℝ)^j ≤ (2 : ℝ)^k := by gcongr
  have h5 : 1 / (2 : ℝ)^j ≥ 1 / (2 : ℝ)^k := one_div_le_one_div_of_le (by positivity) h2
  simpa [dyadicDelta] using h5

lemma dyadicCap_pos (n j : ℕ) (u : ℝ) (hu_pos : 0 < u) (h : j ≤ n) :
    0 < dyadicCap n j u := by
  have h1 : 0 < dyadicDelta j := dyadicDelta_pos j
  have h2 : 0 < dyadicDelta n := dyadicDelta_pos n
  have h3 : 0 < dyadicDelta j / dyadicDelta n := by positivity
  exact Real.rpow_pos_of_pos h3 u

lemma dyadicCap_leaf (n : ℕ) (u : ℝ) : dyadicCap n n u = 1 := by
  have hpos : 0 < dyadicDelta n := dyadicDelta_pos n
  have h1 : dyadicDelta n / dyadicDelta n = 1 := div_self hpos.ne'
  rw [dyadicCap, h1]
  simp

lemma dyadicCap_one_le (n j : ℕ) (u : ℝ) (hu_pos : 0 < u) (h : j ≤ n) :
    1 ≤ dyadicCap n j u := by
  have h2 : dyadicDelta j ≥ dyadicDelta n := dyadicDelta_antitone h
  have h3 : 0 < dyadicDelta n := dyadicDelta_pos n
  have h4 : dyadicDelta j / dyadicDelta n ≥ 1 := by
    calc dyadicDelta j / dyadicDelta n
      ≥ dyadicDelta n / dyadicDelta n := by gcongr
    _ = 1 := div_self h3.ne'
  have h5 : 0 ≤ u := by linarith
  exact Real.one_le_rpow h4 h5

lemma dyadicCap_floor_pos (n j : ℕ) (u : ℝ) (hu_pos : 0 < u) (h : j ≤ n) :
    1 ≤ Nat.floor (dyadicCap n j u) := by
  have h1 : 1 ≤ dyadicCap n j u := dyadicCap_one_le n j u hu_pos h
  have h2 : (1 : ℝ) ≤ dyadicCap n j u := h1
  by_contra h3
  have h4 : Nat.floor (dyadicCap n j u) = 0 := by omega
  have h5 : 0 ≤ dyadicCap n j u := by positivity
  have h6 : (Nat.floor (dyadicCap n j u) : ℝ) ≤ dyadicCap n j u := Nat.floor_le h5
  rw [h4] at h6
  have h7 : dyadicCap n j u < 1 := by exact Nat.floor_eq_zero.mp h4
  linarith

/-- The four children of a level-j dyadic square. -/
def dyadicChildren {j : ℕ} (Q : DiscretisedFurstenbergEstimate.DyadicSquare j) :
    Finset (DiscretisedFurstenbergEstimate.DyadicSquare (j + 1)) :=
  {⟨2 * Q.i, 2 * Q.j⟩, ⟨2 * Q.i + 1, 2 * Q.j⟩,
   ⟨2 * Q.i, 2 * Q.j + 1⟩, ⟨2 * Q.i + 1, 2 * Q.j + 1⟩}

lemma ancestor_child {j : ℕ} (Q : DiscretisedFurstenbergEstimate.DyadicSquare j)
    (child : DiscretisedFurstenbergEstimate.DyadicSquare (j + 1))
    (hchild : child ∈ dyadicChildren Q) :
    dyadicAncestor j (by linarith) child = Q := by
  simp only [dyadicChildren, Finset.mem_insert, Finset.mem_singleton] at hchild
  rcases hchild with (rfl | rfl | rfl | rfl)
  · simp [dyadicAncestor, Int.mul_ediv_cancel_left]
  · have hdiv : (2 * Q.i + 1 : ℤ) / 2 = Q.i := by omega
    simp [dyadicAncestor, hdiv, Int.mul_ediv_cancel_left] <;> aesop
  · have hdiv : (2 * Q.j + 1 : ℤ) / 2 = Q.j := by omega
    simp [dyadicAncestor, hdiv, Int.mul_ediv_cancel_left] <;> aesop
  · have hdivi : (2 * Q.i + 1 : ℤ) / 2 = Q.i := by omega
    have hdivj : (2 * Q.j + 1 : ℤ) / 2 = Q.j := by omega
    simp [dyadicAncestor, hdivi, hdivj, Int.mul_ediv_cancel_left] <;> aesop

/-- Leaves contained in a level-j cube. -/
def leavesInCube {n : ℕ} (j : ℕ) (h : j ≤ n)
    (Q : DiscretisedFurstenbergEstimate.DyadicSquare j)
    (leaves : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n)) :
    Finset (DiscretisedFurstenbergEstimate.DyadicSquare n) :=
  leaves.filter (fun L => dyadicAncestor j h L = Q)

/-! ### Capacity-respecting subsets -/

/-- A subset of leaves respects the capacity bound at every dyadic level. -/
def CapacityRespecting (n : ℕ) (u : ℝ)
    (Pbar : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n)) : Prop :=
  ∀ (j : ℕ) (hjn : j ≤ n) (Q : DiscretisedFurstenbergEstimate.DyadicSquare j),
    (leavesInCube j hjn Q Pbar).card ≤ Nat.floor (dyadicCap n j u)

/-- There exists a maximal capacity-respecting subset. -/
lemma exists_maximal_capacity_respecting {n : ℕ} {u : ℝ}
    (leaves : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n))
    (hu_pos : 0 < u) :
    ∃ (Pbar : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n)),
      Pbar ⊆ leaves ∧
      CapacityRespecting n u Pbar ∧
      ∀ (p : DiscretisedFurstenbergEstimate.DyadicSquare n),
        p ∈ leaves → p ∉ Pbar →
        ∃ (j : ℕ) (hjn : j ≤ n)
          (Q : DiscretisedFurstenbergEstimate.DyadicSquare j),
          dyadicAncestor j hjn p = Q ∧
          (leavesInCube j hjn Q Pbar).card = Nat.floor (dyadicCap n j u) := by
  let allCandidates := (Finset.powerset leaves).filter (CapacityRespecting n u)
  have h_empty : ∅ ∈ allCandidates := by
    simp [allCandidates, CapacityRespecting, leavesInCube] <;> omega
  have h_nonempty : allCandidates.Nonempty := ⟨∅, h_empty⟩
  rcases Finset.exists_max_image allCandidates (fun S => S.card) h_nonempty with
    ⟨Pbar, hPbar_in, hPbar_max⟩
  have hPbar_sub : Pbar ⊆ leaves := by
    have h1 : Pbar ∈ Finset.powerset leaves := (Finset.mem_filter.mp hPbar_in).1
    exact Finset.mem_powerset.mp h1
  have hPbar_cap : CapacityRespecting n u Pbar :=
    (Finset.mem_filter.mp hPbar_in).2
  refine' ⟨Pbar, hPbar_sub, hPbar_cap, _⟩
  intro p hp hnp
  let Pbar' := insert p Pbar
  have hPbar'_sub : Pbar' ⊆ leaves := by
    intro x hx
    simp only [Pbar', Finset.mem_insert] at hx
    rcases hx with (rfl | hx)
    · exact hp
    · exact hPbar_sub hx
  have hPbar'_card : Pbar'.card > Pbar.card := by
    have h_card : Pbar'.card = Pbar.card + 1 := by
      rw [show Pbar' = insert p Pbar from rfl]
      have h : (insert p Pbar).card = Pbar.card + 1 := by
        simp [hnp] <;> omega
      exact h
    linarith
  have hPbar'_not_cand : ¬ CapacityRespecting n u Pbar' := by
    intro h
    have h2 : Pbar' ∈ allCandidates := by
      rw [Finset.mem_filter] <;> exact ⟨Finset.mem_powerset.mpr hPbar'_sub, h⟩
    have h3 := hPbar_max Pbar' h2
    omega
  have hPbar'_not_cand' : ∃ (j : ℕ) (hjn : j ≤ n) (Q : DyadicSquare j),
      (leavesInCube j hjn Q Pbar').card > Nat.floor (dyadicCap n j u) := by
    simpa [CapacityRespecting] using hPbar'_not_cand
  rcases hPbar'_not_cand' with ⟨j, hjn, Q, hQ⟩
  have h4 : (leavesInCube j hjn Q Pbar').card > Nat.floor (dyadicCap n j u) := hQ
  -- p must be in the violating cube (otherwise Pbar' and Pbar have same count in Q)
  have hp_in : p ∈ leavesInCube j hjn Q Pbar' := by
    by_contra h
    have hpnQ : dyadicAncestor j hjn p ≠ Q := by
      by_contra hpnQ2
      have hpin : p ∈ leavesInCube j hjn Q Pbar' := by
        have h1 : p ∈ Pbar' := by simp [Pbar']
        exact Finset.mem_filter.mpr ⟨h1, hpnQ2⟩
      exact h hpin
    have h_cont : leavesInCube j hjn Q Pbar' = leavesInCube j hjn Q Pbar := by
      ext x
      simp only [leavesInCube, Finset.mem_filter, Pbar', Finset.mem_insert]
      constructor
      · rintro ⟨hx1, hx2⟩
        have hx3 : x ∈ Pbar := by
          rcases hx1 with (rfl | hx3)
          · exfalso; exact hpnQ hx2
          · exact hx3
        exact ⟨hx3, hx2⟩
      · rintro ⟨hx1, hx2⟩
        exact ⟨Or.inr hx1, hx2⟩
    rw [h_cont] at h4
    have h9 : (leavesInCube j hjn Q Pbar).card ≤ Nat.floor (dyadicCap n j u) := hPbar_cap j hjn Q
    linarith
  have h12 : dyadicAncestor j hjn p = Q := (Finset.mem_filter.mp hp_in).2
  have h5 : leavesInCube j hjn Q Pbar' = insert p (leavesInCube j hjn Q Pbar) := by
    ext x
    simp only [leavesInCube, Finset.mem_filter, Pbar', Finset.mem_insert]
    constructor
    · rintro ⟨hx1, hx2⟩
      rcases hx1 with (rfl | hx3)
      · exact Or.inl rfl
      · exact Or.inr ⟨hx3, hx2⟩
    · rintro (rfl | ⟨hx3, hx2⟩)
      · exact ⟨Or.inl rfl, h12⟩
      · exact ⟨Or.inr hx3, hx2⟩
  rw [h5] at h4
  by_cases h6 : p ∈ leavesInCube j hjn Q Pbar
  · have h7 : p ∈ Pbar := (Finset.mem_filter.mp h6).1
    exact False.elim (hnp h7)
  · have h_card2 : (insert p (leavesInCube j hjn Q Pbar)).card =
        (leavesInCube j hjn Q Pbar).card + 1 := by
      have h : (insert p (leavesInCube j hjn Q Pbar)).card =
          (leavesInCube j hjn Q Pbar).card + 1 := by
        simp [h6] <;> omega
      exact h
    rw [h_card2] at h4
    have h8 : (leavesInCube j hjn Q Pbar).card ≥ Nat.floor (dyadicCap n j u) := by omega
    have h9 : (leavesInCube j hjn Q Pbar).card ≤ Nat.floor (dyadicCap n j u) :=
      hPbar_cap j hjn Q
    have h10 : (leavesInCube j hjn Q Pbar).card = Nat.floor (dyadicCap n j u) := by omega
    exact ⟨j, hjn, Q, h12, h10⟩

/-! ### Half-capacity cover -/

/-- A dyadic cube at some level, packaged with its level. -/
structure SomeDyadicSquare : Type where
  level : ℕ
  square : DiscretisedFurstenbergEstimate.DyadicSquare level

/-- Greedily construct a half-capacity cover of the occupied leaves in Q. -/
noncomputable def halfCapCoverCube {n : ℕ} (u : ℝ)
    (Pbar : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n))
    (j : ℕ) (hjn : j ≤ n)
    (Q : DiscretisedFurstenbergEstimate.DyadicSquare j) :
    Finset SomeDyadicSquare :=
  if h : j < n then
    if ((leavesInCube j hjn Q Pbar).card : ℝ) ≥ (dyadicCap n j u) / 2 then
      {⟨j, Q⟩}
    else
      (dyadicChildren Q).biUnion (fun child =>
        halfCapCoverCube u Pbar (j + 1) (by omega) child)
  else
    -- j = n, so Q is already at leaf level
    if (leavesInCube j hjn Q Pbar).card > 0 then
      {⟨j, Q⟩}
    else
      ∅
termination_by n - j

/-- The 9 unit dyadic squares covering the unit ball. -/
def rootSquares : Finset (DiscretisedFurstenbergEstimate.DyadicSquare 0) :=
  (Finset.Icc (-1 : ℤ) 1).biUnion fun i =>
    (Finset.Icc (-1 : ℤ) 1).image fun j => ⟨i, j⟩

/-- Half-capacity cover of all occupied leaves in the unit ball. -/
noncomputable def halfCapCover {n : ℕ} (u : ℝ)
    (Pbar : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n)) :
    Finset SomeDyadicSquare :=
  rootSquares.biUnion (fun Q => halfCapCoverCube u Pbar 0 (by linarith) Q)

/-- Side length of a SomeDyadicSquare. -/
def SomeDyadicSquare.side (Q : SomeDyadicSquare) : ℝ :=
  dyadicDelta Q.level

/-! ### Ball-cube intersection bound -/

/-- A ball of radius r with s ≤ r ≤ 2s intersects at most 25 level-j dyadic squares. -/
lemma ball_intersects_dyadic_squares_25 {j : ℕ} {c : EuclideanPlane} {r : ℝ}
    (hr_pos : 0 < r) (hs_le : dyadicDelta j ≤ r) (hr_lt : r ≤ 2 * dyadicDelta j) :
    ∃ (I : Finset (DiscretisedFurstenbergEstimate.DyadicSquare j)),
      I.card ≤ 25 ∧
      ∀ (Q : DiscretisedFurstenbergEstimate.DyadicSquare j),
        ((Q.toSet : Set EuclideanPlane) ∩ Metric.closedBall c r).Nonempty → Q ∈ I := by
  set s : ℝ := dyadicDelta j with hs
  have hs_pos : 0 < s := dyadicDelta_pos j
  let mi : ℤ := ⌊c 0 / s⌋
  let mj : ℤ := ⌊c 1 / s⌋
  let I : Finset (DyadicSquare j) :=
    (Finset.Icc (mi - 2) (mi + 2)).biUnion fun i =>
      (Finset.Icc (mj - 2) (mj + 2)).image fun jk => ⟨i, jk⟩
  have h_card : I.card ≤ 25 := by
    have h1 : I.card ≤ ∑ i ∈ Finset.Icc (mi - 2) (mi + 2),
        ((Finset.Icc (mj - 2) (mj + 2)).image fun jk : ℤ => (⟨i, jk⟩ : DyadicSquare j)).card :=
      Finset.card_biUnion_le
    have h2 : ∀ i ∈ Finset.Icc (mi - 2) (mi + 2),
        ((Finset.Icc (mj - 2) (mj + 2)).image fun jk : ℤ => (⟨i, jk⟩ : DyadicSquare j)).card ≤ 5 := by
      intro i _
      have h3 : ((Finset.Icc (mj - 2) (mj + 2)).image fun jk : ℤ => (⟨i, jk⟩ : DyadicSquare j)).card ≤
          (Finset.Icc (mj - 2) (mj + 2)).card := Finset.card_image_le
      have h4 : (Finset.Icc (mj - 2) (mj + 2)).card = 5 := by
        simp [Finset.Icc_eq_empty_of_lt] <;> omega
      rw [h4] at h3 <;> omega
    have h3 : I.card ≤ ∑ i ∈ Finset.Icc (mi - 2) (mi + 2), 5 := by
      calc I.card
        ≤ ∑ i ∈ Finset.Icc (mi - 2) (mi + 2), _ := h1
      _ ≤ ∑ i ∈ Finset.Icc (mi - 2) (mi + 2), 5 := Finset.sum_le_sum h2
    have h4 : (Finset.Icc (mi - 2) (mi + 2)).card = 5 := by
      simp [Finset.Icc_eq_empty_of_lt] <;> omega
    rw [Finset.sum_const, h4] at h3 <;> omega
  refine' ⟨I, h_card, _⟩
  intro Q hQ
  rcases hQ with ⟨x, hxQ, hxball⟩
  have h_x_in_Q : x ∈ Q.toSet := hxQ
  have h_x_in_ball : x ∈ Metric.closedBall c r := hxball
  have h_dist0 : |x 0 - c 0| ≤ r := by
    have h : |x 0 - c 0| ≤ ‖x - c‖ := abs_coord_le_norm (x - c) 0
    have h2 : ‖x - c‖ ≤ r := h_x_in_ball
    linarith
  have h_dist1 : |x 1 - c 1| ≤ r := by
    have h : |x 1 - c 1| ≤ ‖x - c‖ := abs_coord_le_norm (x - c) 1
    have h2 : ‖x - c‖ ≤ r := h_x_in_ball
    linarith
  have hQ_i1 : (Q.i : ℝ) * s ≤ x 0 := h_x_in_Q.1
  have hQ_i2 : x 0 < ((Q.i : ℝ) + 1) * s := h_x_in_Q.2.1
  have hQ_j1 : (Q.j : ℝ) * s ≤ x 1 := h_x_in_Q.2.2.1
  have hQ_j2 : x 1 < ((Q.j : ℝ) + 1) * s := h_x_in_Q.2.2.2
  have h_i_upper : Q.i ≤ mi + 2 := by
    have h4 : x 0 ≤ c 0 + r := by linarith [abs_le.mp h_dist0]
    have h5 : (Q.i : ℝ) * s ≤ c 0 + 2 * s := by linarith
    have h6 : (Q.i : ℝ) ≤ (c 0 + 2 * s) / s := by
      calc (Q.i : ℝ)
        = (Q.i : ℝ) * s / s := by field_simp [hs_pos.ne'] <;> ring
      _ ≤ (c 0 + 2 * s) / s := by gcongr
    have h7 : (c 0 + 2 * s) / s = c 0 / s + 2 := by
      field_simp [hs_pos.ne'] <;> ring
    rw [h7] at h6
    have h8 : c 0 / s < (mi : ℝ) + 1 := Int.lt_floor_add_one (c 0 / s)
    have h9 : (Q.i : ℝ) < (mi : ℝ) + 3 := by linarith
    have h10 : Q.i < mi + 3 := by exact_mod_cast h9
    omega
  have h_i_lower : Q.i ≥ mi - 2 := by
    have h4 : x 0 ≥ c 0 - r := by linarith [abs_le.mp h_dist0]
    have h5 : ((Q.i : ℝ) + 1) * s > c 0 - 2 * s := by linarith
    have h6 : (Q.i : ℝ) + 1 > (c 0 - 2 * s) / s := by
      calc (Q.i : ℝ) + 1
        = ((Q.i : ℝ) + 1) * s / s := by field_simp [hs_pos.ne'] <;> ring
      _ > (c 0 - 2 * s) / s := by gcongr
    have h7 : (c 0 - 2 * s) / s = c 0 / s - 2 := by
      field_simp [hs_pos.ne'] <;> ring
    rw [h7] at h6
    have h8 : (mi : ℝ) ≤ c 0 / s := Int.floor_le (c 0 / s)
    have h9 : (Q.i : ℝ) > (mi : ℝ) - 3 := by linarith
    have h10 : Q.i > mi - 3 := by exact_mod_cast h9
    omega
  have h_j_upper : Q.j ≤ mj + 2 := by
    have h4 : x 1 ≤ c 1 + r := by linarith [abs_le.mp h_dist1]
    have h5 : (Q.j : ℝ) * s ≤ c 1 + 2 * s := by linarith
    have h6 : (Q.j : ℝ) ≤ (c 1 + 2 * s) / s := by
      calc (Q.j : ℝ)
        = (Q.j : ℝ) * s / s := by field_simp [hs_pos.ne'] <;> ring
      _ ≤ (c 1 + 2 * s) / s := by gcongr
    have h7 : (c 1 + 2 * s) / s = c 1 / s + 2 := by
      field_simp [hs_pos.ne'] <;> ring
    rw [h7] at h6
    have h8 : c 1 / s < (mj : ℝ) + 1 := Int.lt_floor_add_one (c 1 / s)
    have h9 : (Q.j : ℝ) < (mj : ℝ) + 3 := by linarith
    have h10 : Q.j < mj + 3 := by exact_mod_cast h9
    omega
  have h_j_lower : Q.j ≥ mj - 2 := by
    have h4 : x 1 ≥ c 1 - r := by linarith [abs_le.mp h_dist1]
    have h5 : ((Q.j : ℝ) + 1) * s > c 1 - 2 * s := by linarith
    have h6 : (Q.j : ℝ) + 1 > (c 1 - 2 * s) / s := by
      calc (Q.j : ℝ) + 1
        = ((Q.j : ℝ) + 1) * s / s := by field_simp [hs_pos.ne'] <;> ring
      _ > (c 1 - 2 * s) / s := by gcongr
    have h7 : (c 1 - 2 * s) / s = c 1 / s - 2 := by
      field_simp [hs_pos.ne'] <;> ring
    rw [h7] at h6
    have h8 : (mj : ℝ) ≤ c 1 / s := Int.floor_le (c 1 / s)
    have h9 : (Q.j : ℝ) > (mj : ℝ) - 3 := by linarith
    have h10 : Q.j > mj - 3 := by exact_mod_cast h9
    omega
  have h_i_in : Q.i ∈ Finset.Icc (mi - 2) (mi + 2) := by
    simp only [Finset.mem_Icc] <;> omega
  have h_j_in : Q.j ∈ Finset.Icc (mj - 2) (mj + 2) := by
    simp only [Finset.mem_Icc] <;> omega
  have hQ_in_I : Q ∈ I := by
    simp only [I, Finset.mem_biUnion]
    refine' ⟨Q.i, h_i_in, _⟩
    simp only [Finset.mem_image]
    refine' ⟨Q.j, h_j_in, _⟩
    cases Q <;> rfl
  exact hQ_in_I

/-! ### Modulo-3 coloring (corrected: OR disjunction) -/

/-- Helper: if two integers are congruent mod 3 and distinct, their abs diff ≥ 3. -/
lemma int_mod3_distinct_abs_ge3 {a b : ℤ} (hmod : a % 3 = b % 3) (hne : a ≠ b) :
    |a - b| ≥ 3 := by
  have h3 : 3 ∣ (a - b) := by omega
  have h4 : 3 ∣ |a - b| := by
    exact (dvd_abs 3 (a - b)).mpr h3
  have hne2 : a - b ≠ 0 := by omega
  have hpos : 0 < |a - b| := abs_pos.mpr hne2
  exact Int.le_of_dvd hpos h4

lemma int_div3_distinct_abs_ge3 {a b : ℤ} (hdiv : 3 ∣ (a - b)) (hne : a ≠ b) :
    |a - b| ≥ 3 := by
  have h4 : 3 ∣ |a - b| := by exact (dvd_abs 3 (a - b)).mpr hdiv
  have hne2 : a - b ≠ 0 := by omega
  have hpos : 0 < |a - b| := abs_pos.mpr hne2
  exact Int.le_of_dvd hpos h4

/-- Same-color dyadic squares are 3*side apart in at least one coordinate,
    hence distance ≥ side. Uses correct OR disjunction. -/
lemma mod3_color_separation_corrected {n : ℕ} {δ : ℝ} (hδ_le : δ ≤ dyadicDelta n)
    {Q1 Q2 : DiscretisedFurstenbergEstimate.DyadicSquare n} (hQ1_ne_Q2 : Q1 ≠ Q2)
    (hdiv_i : 3 ∣ (Q1.i - Q2.i)) (hdiv_j : 3 ∣ (Q1.j - Q2.j))
    {p q : EuclideanPlane} (hp : p ∈ Q1.toSet) (hq : q ∈ Q2.toSet) :
    2 * dyadicDelta n < dist p q := by
  set s : ℝ := dyadicDelta n with hs
  have hs_pos : 0 < s := dyadicDelta_pos n
  have h_coord : Q1.i ≠ Q2.i ∨ Q1.j ≠ Q2.j := by
    by_contra h
    push Not at h
    have hQ : Q1 = Q2 := by
      cases Q1 <;> cases Q2 <;> simp_all <;> omega
    exact hQ1_ne_Q2 hQ
  have h_main : |p 0 - q 0| > 2 * s ∨ |p 1 - q 1| > 2 * s := by
    rcases h_coord with (h_i | h_j)
    · -- Coordinate i differs
      have h_abs3 : |Q1.i - Q2.i| ≥ 3 := int_div3_distinct_abs_ge3 hdiv_i h_i
      by_cases h_lt : Q1.i ≤ Q2.i
      · have h_diff : Q2.i - Q1.i ≥ 3 := by omega
        have h_diff' : (Q2.i : ℝ) - (Q1.i : ℝ) - 1 ≥ 2 := by
          have h : (Q2.i : ℝ) - (Q1.i : ℝ) ≥ 3 := by exact_mod_cast h_diff
          linarith
        have h_p1 : p 0 < ((Q1.i : ℝ) + 1) * s := by simpa [DyadicSquare.toSet] using hp.2.1
        have h_q1 : q 0 ≥ (Q2.i : ℝ) * s := by simpa [DyadicSquare.toSet] using hq.1
        have h9 : q 0 - p 0 > 2 * s := by
          have h10 : q 0 - p 0 > ((Q2.i : ℝ) - (Q1.i : ℝ) - 1) * s := by linarith
          have h11 : ((Q2.i : ℝ) - (Q1.i : ℝ) - 1) * s ≥ 2 * s := by
            gcongr <;> linarith
          linarith
        exact Or.inl (by rw [abs_of_neg (by linarith)] <;> linarith)
      · have h_gt : Q2.i < Q1.i := by omega
        have h_diff : Q1.i - Q2.i ≥ 3 := by omega
        have h_diff' : (Q1.i : ℝ) - (Q2.i : ℝ) - 1 ≥ 2 := by
          have h : (Q1.i : ℝ) - (Q2.i : ℝ) ≥ 3 := by exact_mod_cast h_diff
          linarith
        have h_q1 : q 0 < ((Q2.i : ℝ) + 1) * s := by simpa [DyadicSquare.toSet] using hq.2.1
        have h_p1 : p 0 ≥ (Q1.i : ℝ) * s := by simpa [DyadicSquare.toSet] using hp.1
        have h9 : p 0 - q 0 > 2 * s := by
          have h10 : p 0 - q 0 > ((Q1.i : ℝ) - (Q2.i : ℝ) - 1) * s := by linarith
          have h11 : ((Q1.i : ℝ) - (Q2.i : ℝ) - 1) * s ≥ 2 * s := by
            gcongr <;> linarith
          linarith
        exact Or.inl (by rw [abs_of_pos (by linarith)] <;> linarith)
    · -- Coordinate j differs
      have h_abs3 : |Q1.j - Q2.j| ≥ 3 := int_div3_distinct_abs_ge3 hdiv_j h_j
      by_cases h_lt : Q1.j ≤ Q2.j
      · have h_diff : Q2.j - Q1.j ≥ 3 := by omega
        have h_diff' : (Q2.j : ℝ) - (Q1.j : ℝ) - 1 ≥ 2 := by
          have h : (Q2.j : ℝ) - (Q1.j : ℝ) ≥ 3 := by exact_mod_cast h_diff
          linarith
        have h_p1 : p 1 < ((Q1.j : ℝ) + 1) * s := by simpa [DyadicSquare.toSet] using hp.2.2.2
        have h_q1 : q 1 ≥ (Q2.j : ℝ) * s := by simpa [DyadicSquare.toSet] using hq.2.2.1
        have h9 : q 1 - p 1 > 2 * s := by
          have h10 : q 1 - p 1 > ((Q2.j : ℝ) - (Q1.j : ℝ) - 1) * s := by linarith
          have h11 : ((Q2.j : ℝ) - (Q1.j : ℝ) - 1) * s ≥ 2 * s := by
            gcongr <;> linarith
          linarith
        exact Or.inr (by rw [abs_of_neg (by linarith)] <;> linarith)
      · have h_gt : Q2.j < Q1.j := by omega
        have h_diff : Q1.j - Q2.j ≥ 3 := by omega
        have h_diff' : (Q1.j : ℝ) - (Q2.j : ℝ) - 1 ≥ 2 := by
          have h : (Q1.j : ℝ) - (Q2.j : ℝ) ≥ 3 := by exact_mod_cast h_diff
          linarith
        have h_q1 : q 1 < ((Q2.j : ℝ) + 1) * s := by simpa [DyadicSquare.toSet] using hq.2.2.2
        have h_p1 : p 1 ≥ (Q1.j : ℝ) * s := by simpa [DyadicSquare.toSet] using hp.2.2.1
        have h9 : p 1 - q 1 > 2 * s := by
          have h10 : p 1 - q 1 > ((Q1.j : ℝ) - (Q2.j : ℝ) - 1) * s := by linarith
          have h11 : ((Q1.j : ℝ) - (Q2.j : ℝ) - 1) * s ≥ 2 * s := by
            gcongr <;> linarith
          linarith
        exact Or.inr (by rw [abs_of_pos (by linarith)] <;> linarith)
  have h_abs0 : |(p - q) 0| ≤ ‖p - q‖ := abs_coord_le_norm (p - q) 0
  have h_abs1 : |(p - q) 1| ≤ ‖p - q‖ := abs_coord_le_norm (p - q) 1
  rcases h_main with (h0 | h1)
  · have h10 : |(p - q) 0| = |p 0 - q 0| := by rfl
    rw [h10] at h_abs0
    have h11 : ‖p - q‖ > 2 * s := by linarith
    simpa [dist_eq_norm] using h11
  · have h10 : |(p - q) 1| = |p 1 - q 1| := by rfl
    rw [h10] at h_abs1
    have h11 : ‖p - q‖ > 2 * s := by linarith
    simpa [dist_eq_norm] using h11

/-- Color function for dyadic squares (9 colors). -/
def colorOf {n : ℕ} (Q : DiscretisedFurstenbergEstimate.DyadicSquare n) : Fin 9 :=
  let ci : ℕ := (Q.i % 3).natAbs
  let cj : ℕ := (Q.j % 3).natAbs
  ⟨ci * 3 + cj, by omega⟩

/-- From color equality, deduce 3 divides the index difference. -/
lemma color_eq_implies_div3 {n : ℕ} {Q1 Q2 : DyadicSquare n}
    (hcolor : colorOf Q1 = colorOf Q2) :
    3 ∣ (Q1.i - Q2.i) ∧ 3 ∣ (Q1.j - Q2.j) := by
  have h_i_lt1 : (Q1.i % 3).toNat < 3 := by omega
  have h_i_lt2 : (Q2.i % 3).toNat < 3 := by omega
  have h_j_lt1 : (Q1.j % 3).toNat < 3 := by omega
  have h_j_lt2 : (Q2.j % 3).toNat < 3 := by omega
  have h_val_eq : (colorOf Q1).val = (colorOf Q2).val := by rw [hcolor]
  have h1 : (Q1.i % 3).toNat = (Q2.i % 3).toNat := by
    have h_eq1 : (colorOf Q1).val = (Q1.i % 3).toNat * 3 + (Q1.j % 3).toNat := by
      simp [colorOf] <;> omega
    have h_eq2 : (colorOf Q2).val = (Q2.i % 3).toNat * 3 + (Q2.j % 3).toNat := by
      simp [colorOf] <;> omega
    rw [h_eq1, h_eq2] at h_val_eq
    omega
  have h2 : (Q1.j % 3).toNat = (Q2.j % 3).toNat := by
    have h_eq1 : (colorOf Q1).val = (Q1.i % 3).toNat * 3 + (Q1.j % 3).toNat := by
      simp [colorOf] <;> omega
    have h_eq2 : (colorOf Q2).val = (Q2.i % 3).toNat * 3 + (Q2.j % 3).toNat := by
      simp [colorOf] <;> omega
    rw [h_eq1, h_eq2] at h_val_eq
    omega
  have h_i1 : 0 ≤ Q1.i % 3 := by omega
  have h_i2 : 0 ≤ Q2.i % 3 := by omega
  have h_j1 : 0 ≤ Q1.j % 3 := by omega
  have h_j2 : 0 ≤ Q2.j % 3 := by omega
  have h3 : Q1.i % 3 = Q2.i % 3 := by
    have h31 : ((Q1.i % 3).toNat : ℤ) = Q1.i % 3 := Int.toNat_of_nonneg h_i1
    have h32 : ((Q2.i % 3).toNat : ℤ) = Q2.i % 3 := Int.toNat_of_nonneg h_i2
    calc Q1.i % 3
      = ((Q1.i % 3).toNat : ℤ) := h31.symm
    _ = ((Q2.i % 3).toNat : ℤ) := by exact_mod_cast h1
    _ = Q2.i % 3 := h32
  have h4 : Q1.j % 3 = Q2.j % 3 := by
    have h41 : ((Q1.j % 3).toNat : ℤ) = Q1.j % 3 := Int.toNat_of_nonneg h_j1
    have h42 : ((Q2.j % 3).toNat : ℤ) = Q2.j % 3 := Int.toNat_of_nonneg h_j2
    calc Q1.j % 3
      = ((Q1.j % 3).toNat : ℤ) := h41.symm
    _ = ((Q2.j % 3).toNat : ℤ) := by exact_mod_cast h2
    _ = Q2.j % 3 := h42
  have h5 : 3 ∣ (Q1.i - Q2.i) := by omega
  have h6 : 3 ∣ (Q1.j - Q2.j) := by omega
  exact ⟨h5, h6⟩

/-- Pigeonhole: among N colored points, some color class has ≥ N/9. -/
lemma exists_large_fiber_9 {α : Type*} {S : Finset α} {f : α → Fin 9} :
    ∃ (c : Fin 9), (S.filter (fun x => f x = c)).card * 9 ≥ S.card := by
  have h_sum : ∑ c : Fin 9, (S.filter (fun x => f x = c)).card = S.card := by
    calc
      ∑ c : Fin 9, (S.filter (fun x => f x = c)).card
        = ∑ c : Fin 9, ∑ x ∈ S, (if f x = c then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro c _
          simp [Finset.filter_eq']
          <;> rfl
      _ = ∑ x ∈ S, ∑ c : Fin 9, (if f x = c then 1 else 0) := by
          rw [Finset.sum_comm]
      _ = ∑ x ∈ S, 1 := by
          apply Finset.sum_congr rfl
          intro x _
          have h : ∑ c : Fin 9, (if f x = c then 1 else 0) = 1 := by
            let c0 : Fin 9 := f x
            have hc0 : f x = c0 := rfl
            rw [Finset.sum_eq_single_of_mem c0 (Finset.mem_univ c0)]
            · rw [if_pos hc0]
            · intro b _ hb
              rw [if_neg]
              intro h
              have : b = c0 := by
                rw [←h, hc0]
              exact hb this
          exact h
      _ = S.card := by simp
  by_contra h
  push Not at h
  have h1 : ∀ c : Fin 9, ((S.filter (fun x => f x = c)).card : ℝ) < (S.card : ℝ) / 9 := by
    intro c
    have h2 : (S.filter (fun x => f x = c)).card * 9 < S.card := h c
    have h3 : ((S.filter (fun x => f x = c)).card : ℝ) * 9 < (S.card : ℝ) := by exact_mod_cast h2
    linarith
  have h4 : ∑ c : Fin 9, ((S.filter (fun x => f x = c)).card : ℝ) < ∑ c : Fin 9, ((S.card : ℝ) / 9) := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨0, by simp⟩
    · intro i _; exact h1 i
  have h5 : ∑ c : Fin 9, ((S.card : ℝ) / 9) = (S.card : ℝ) := by
    simp [Finset.sum_const] <;> ring
  have h6 : ∑ c : Fin 9, ((S.filter (fun x => f x = c)).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast h_sum
  rw [h6] at h4
  rw [h5] at h4
  <;> linarith

/-! ### Cover properties -/

/-- Helper: floor(x) ≥ x/2 for x ≥ 1. -/
lemma floor_ge_half (x : ℝ) (hx : 1 ≤ x) : (Nat.floor x : ℝ) ≥ x / 2 := by
  by_cases h : x < 2
  · -- 1 ≤ x < 2, floor(x) = 1
    have h1 : 1 ≤ Nat.floor x := by
      rw [Nat.le_floor_iff (by linarith)]
      <;> norm_num <;> linarith
    have h2 : Nat.floor x < 2 := by
      by_contra h3
      have h4 : 2 ≤ Nat.floor x := by omega
      have h5 : (2 : ℝ) ≤ (Nat.floor x : ℝ) := by exact_mod_cast h4
      have h6 : (Nat.floor x : ℝ) ≤ x := Nat.floor_le (by linarith)
      linarith
    have h3 : Nat.floor x = 1 := by omega
    rw [h3]
    norm_num <;> linarith
  · -- x ≥ 2
    have h2 : x ≥ 2 := by linarith
    have h3 : 0 ≤ x := by linarith
    have h4 : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
    have h5 : (Nat.floor x : ℝ) > x - 1 := by linarith
    have h6 : x - 1 ≥ x / 2 := by linarith
    linarith

/-- Combined correctness: every cube produced by `halfCapCoverCube` has level ≤ n
    and satisfies the half-cap condition. Proved by induction on n - j. -/
lemma halfCapCoverCube_correct {n : ℕ} {u : ℝ} {Pbar : Finset (DyadicSquare n)} :
    ∀ (d : ℕ) (j : ℕ) (hjn : j ≤ n) (hd : n - j = d)
      (Q : DyadicSquare j) (Q' : SomeDyadicSquare),
      Q' ∈ halfCapCoverCube u Pbar j hjn Q →
      ∃ (h : Q'.level ≤ n),
        ((leavesInCube Q'.level h Q'.square Pbar).card : ℝ) ≥
          (dyadicCap n Q'.level u) / 2 := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro j hjn hd Q Q' hQ'
    by_cases h : j < n
    · -- j < n case
      have hd_pos : 0 < d := by omega
      by_cases hcap : ((leavesInCube j hjn Q Pbar).card : ℝ) ≥ (dyadicCap n j u) / 2
      · -- count ≥ cap/2: output is {⟨j, Q⟩}
        have h_def : halfCapCoverCube u Pbar j hjn Q = {⟨j, Q⟩} := by
          rw [halfCapCoverCube]
          rw [dif_pos h]
          rw [if_pos hcap]
          <;> rfl
        rw [h_def] at hQ'
        have h_eq : Q' = ⟨j, Q⟩ := by simpa using hQ'
        subst h_eq
        exact ⟨hjn, hcap⟩
      · -- count < cap/2: recurse into children
        have h_def : halfCapCoverCube u Pbar j hjn Q =
            (dyadicChildren Q).biUnion (fun child =>
              halfCapCoverCube u Pbar (j + 1) (by omega) child) := by
          rw [halfCapCoverCube]
          rw [dif_pos h]
          rw [if_neg hcap]
          <;> rfl
        rw [h_def] at hQ'
        rcases Finset.mem_biUnion.mp hQ' with ⟨child, hchild, hQ'_child⟩
        have h_d' : n - (j + 1) = d - 1 := by omega
        exact ih (d - 1) (by omega) (j + 1) (by omega) h_d' child Q' hQ'_child
    · -- j = n case
      have h_not : ¬j < n := h
      have h_jn : j = n := by omega
      by_cases hpos : (leavesInCube j hjn Q Pbar).card > 0
      · -- count > 0: output is {⟨j, Q⟩}
        have h_def : halfCapCoverCube u Pbar j hjn Q = {⟨j, Q⟩} := by
          rw [halfCapCoverCube]
          rw [dif_neg h_not]
          rw [if_pos hpos]
          <;> rfl
        rw [h_def] at hQ'
        have h_eq : Q' = ⟨j, Q⟩ := by simpa using hQ'
        subst h_eq
        have h_leaf : dyadicCap n j u = 1 := by
          have h_jn' : j = n := h_jn
          rw [h_jn']
          exact dyadicCap_leaf n u
        have h_card : ((leavesInCube j hjn Q Pbar).card : ℝ) ≥ 1 := by exact_mod_cast hpos
        refine' ⟨hjn, _⟩
        rw [h_leaf]
        norm_num <;> linarith
      · -- count = 0: output is ∅
        have h_def : halfCapCoverCube u Pbar j hjn Q = ∅ := by
          rw [halfCapCoverCube]
          rw [dif_neg h_not]
          rw [if_neg hpos]
          <;> rfl
        rw [h_def] at hQ'
        simp at hQ'

/-- Each cover cube has at least half-capacity survivors.
    Returns the level bound together with the half-cap condition. -/
lemma halfCapCover_halfCap {n : ℕ} {u : ℝ} {Pbar : Finset (DyadicSquare n)}
    (Q : SomeDyadicSquare) (hQ : Q ∈ halfCapCover u Pbar) :
    ∃ (h : Q.level ≤ n),
      ((leavesInCube Q.level h Q.square Pbar).card : ℝ) ≥ (dyadicCap n Q.level u) / 2 := by
  have h1 : Q ∈ rootSquares.biUnion (fun Q0 => halfCapCoverCube u Pbar 0 (by linarith) Q0) := by
    simpa [halfCapCover] using hQ
  rcases Finset.mem_biUnion.mp h1 with ⟨Q0, hQ0, hQ'⟩
  have h_correct := halfCapCoverCube_correct n 0 (by linarith) (by omega) Q0 Q hQ'
  rcases h_correct with ⟨h, h_half⟩
  exact ⟨h, h_half⟩

/-- Distinct dyadic squares at the same level have disjoint point sets. -/
lemma dyadicSquare_toSet_disjoint {j : ℕ} {Q1 Q2 : DyadicSquare j} (hne : Q1 ≠ Q2) :
    Disjoint (Q1.toSet) (Q2.toSet) := by
  have h : Q1.i ≠ Q2.i ∨ Q1.j ≠ Q2.j := by
    by_contra h'; push Not at h'; cases Q1 <;> cases Q2 <;> simp_all <;> omega
  have hδ_pos : 0 < dyadicDelta j := dyadicDelta_pos j
  rw [Set.disjoint_left]
  rcases h with (hi | hj)
  · -- different i indices
    by_cases h_lt : Q1.i < Q2.i
    · have h1 : (Q1.i : ℝ) + 1 ≤ (Q2.i : ℝ) := by exact_mod_cast (Int.add_one_le_of_lt h_lt)
      intro x hx1
      intro hx2
      have h2 : x 0 < ((Q1.i : ℝ) + 1) * dyadicDelta j := hx1.2.1
      have h3 : (Q2.i : ℝ) * dyadicDelta j ≤ x 0 := hx2.1
      have h4 : ((Q1.i : ℝ) + 1) * dyadicDelta j ≤ (Q2.i : ℝ) * dyadicDelta j := by
        gcongr <;> linarith
      linarith [hδ_pos]
    · have h_gt : Q2.i < Q1.i := by omega
      have h1 : (Q2.i : ℝ) + 1 ≤ (Q1.i : ℝ) := by exact_mod_cast (Int.add_one_le_of_lt h_gt)
      intro x hx1
      intro hx2
      have h2 : x 0 < ((Q2.i : ℝ) + 1) * dyadicDelta j := hx2.2.1
      have h3 : (Q1.i : ℝ) * dyadicDelta j ≤ x 0 := hx1.1
      have h4 : ((Q2.i : ℝ) + 1) * dyadicDelta j ≤ (Q1.i : ℝ) * dyadicDelta j := by
        gcongr <;> linarith
      linarith [hδ_pos]
  · -- different j indices
    by_cases h_lt : Q1.j < Q2.j
    · have h1 : (Q1.j : ℝ) + 1 ≤ (Q2.j : ℝ) := by exact_mod_cast (Int.add_one_le_of_lt h_lt)
      intro x hx1
      intro hx2
      have h2 : x 1 < ((Q1.j : ℝ) + 1) * dyadicDelta j := hx1.2.2.2
      have h3 : (Q2.j : ℝ) * dyadicDelta j ≤ x 1 := hx2.2.2.1
      have h4 : ((Q1.j : ℝ) + 1) * dyadicDelta j ≤ (Q2.j : ℝ) * dyadicDelta j := by
        gcongr <;> linarith
      linarith [hδ_pos]
    · have h_gt : Q2.j < Q1.j := by omega
      have h1 : (Q2.j : ℝ) + 1 ≤ (Q1.j : ℝ) := by exact_mod_cast (Int.add_one_le_of_lt h_gt)
      intro x hx1
      intro hx2
      have h2 : x 1 < ((Q2.j : ℝ) + 1) * dyadicDelta j := hx2.2.2.2
      have h3 : (Q1.j : ℝ) * dyadicDelta j ≤ x 1 := hx1.2.2.1
      have h4 : ((Q2.j : ℝ) + 1) * dyadicDelta j ≤ (Q1.j : ℝ) * dyadicDelta j := by
        gcongr <;> linarith
      linarith [hδ_pos]

/-- A child dyadic square's point set is a subset of its parent's. -/
lemma dyadicChild_toSet_subset {j : ℕ} {Q : DyadicSquare j} {child : DyadicSquare (j + 1)}
    (hchild : child ∈ dyadicChildren Q) : child.toSet ⊆ Q.toSet := by
  have h_anc : dyadicAncestor j (by linarith) child = Q := ancestor_child Q child hchild
  have h_i_div2 : child.i / 2 = Q.i := by
    simpa [dyadicAncestor] using congr_arg DyadicSquare.i h_anc
  have h_j_div2 : child.j / 2 = Q.j := by
    simpa [dyadicAncestor] using congr_arg DyadicSquare.j h_anc
  have h_i1 : 2 * Q.i ≤ child.i := by omega
  have h_i2 : child.i ≤ 2 * Q.i + 1 := by omega
  have h_j1 : 2 * Q.j ≤ child.j := by omega
  have h_j2 : child.j ≤ 2 * Q.j + 1 := by omega
  have h_delta : dyadicDelta (j + 1) = dyadicDelta j / 2 := by
    simp [dyadicDelta] <;> ring
  intro x hx
  have hxi1 : (child.i : ℝ) * dyadicDelta (j + 1) ≤ x 0 := hx.1
  have hxi2 : x 0 < ((child.i : ℝ) + 1) * dyadicDelta (j + 1) := hx.2.1
  have hxj1 : (child.j : ℝ) * dyadicDelta (j + 1) ≤ x 1 := hx.2.2.1
  have hxj2 : x 1 < ((child.j : ℝ) + 1) * dyadicDelta (j + 1) := hx.2.2.2
  have hδ_pos : 0 < dyadicDelta j := dyadicDelta_pos j
  have h_half_pos : 0 < dyadicDelta j / 2 := half_pos hδ_pos
  have h_i1' : (2 * (Q.i : ℝ)) ≤ (child.i : ℝ) := by exact_mod_cast h_i1
  have h_i2' : (child.i : ℝ) ≤ 2 * (Q.i : ℝ) + 1 := by exact_mod_cast h_i2
  have h_j1' : (2 * (Q.j : ℝ)) ≤ (child.j : ℝ) := by exact_mod_cast h_j1
  have h_j2' : (child.j : ℝ) ≤ 2 * (Q.j : ℝ) + 1 := by exact_mod_cast h_j2
  have h_eq_i1 : (Q.i : ℝ) * dyadicDelta j = (2 * (Q.i : ℝ)) * (dyadicDelta j / 2) := by ring
  have h_eq_i2 : ((Q.i : ℝ) + 1) * dyadicDelta j = ((2 * (Q.i : ℝ) + 1) + 1) * (dyadicDelta j / 2) := by ring
  have h_eq_j1 : (Q.j : ℝ) * dyadicDelta j = (2 * (Q.j : ℝ)) * (dyadicDelta j / 2) := by ring
  have h_eq_j2 : ((Q.j : ℝ) + 1) * dyadicDelta j = ((2 * (Q.j : ℝ) + 1) + 1) * (dyadicDelta j / 2) := by ring
  have hQ_i1 : (Q.i : ℝ) * dyadicDelta j ≤ x 0 := by
    rw [h_eq_i1]
    have h : (2 * (Q.i : ℝ)) * (dyadicDelta j / 2) ≤ (child.i : ℝ) * (dyadicDelta j / 2) :=
      mul_le_mul_of_nonneg_right h_i1' h_half_pos.le
    have h2 : (child.i : ℝ) * (dyadicDelta j / 2) = (child.i : ℝ) * dyadicDelta (j + 1) := by
      rw [h_delta] <;> ring
    rw [h2] at h
    exact le_trans h hxi1
  have hQ_i2 : x 0 < ((Q.i : ℝ) + 1) * dyadicDelta j := by
    rw [h_eq_i2]
    have h : ((child.i : ℝ) + 1) * (dyadicDelta j / 2) ≤ ((2 * (Q.i : ℝ) + 1) + 1) * (dyadicDelta j / 2) :=
      mul_le_mul_of_nonneg_right (by linarith) h_half_pos.le
    have h2 : ((child.i : ℝ) + 1) * dyadicDelta (j + 1) = ((child.i : ℝ) + 1) * (dyadicDelta j / 2) := by
      rw [h_delta] <;> ring
    rw [h2] at hxi2
    exact lt_of_lt_of_le hxi2 h
  have hQ_j1 : (Q.j : ℝ) * dyadicDelta j ≤ x 1 := by
    rw [h_eq_j1]
    have h : (2 * (Q.j : ℝ)) * (dyadicDelta j / 2) ≤ (child.j : ℝ) * (dyadicDelta j / 2) :=
      mul_le_mul_of_nonneg_right h_j1' h_half_pos.le
    have h2 : (child.j : ℝ) * (dyadicDelta j / 2) = (child.j : ℝ) * dyadicDelta (j + 1) := by
      rw [h_delta] <;> ring
    rw [h2] at h
    exact le_trans h hxj1
  have hQ_j2 : x 1 < ((Q.j : ℝ) + 1) * dyadicDelta j := by
    rw [h_eq_j2]
    have h : ((child.j : ℝ) + 1) * (dyadicDelta j / 2) ≤ ((2 * (Q.j : ℝ) + 1) + 1) * (dyadicDelta j / 2) :=
      mul_le_mul_of_nonneg_right (by linarith) h_half_pos.le
    have h2 : ((child.j : ℝ) + 1) * dyadicDelta (j + 1) = ((child.j : ℝ) + 1) * (dyadicDelta j / 2) := by
      rw [h_delta] <;> ring
    rw [h2] at hxj2
    exact lt_of_lt_of_le hxj2 h
  exact ⟨hQ_i1, hQ_i2, hQ_j1, hQ_j2⟩

/-- Any cube produced by `halfCapCoverCube` from Q has point set ⊆ Q.toSet. -/
lemma halfCapCoverCube_subset {n : ℕ} {u : ℝ} {Pbar : Finset (DyadicSquare n)} :
    ∀ (d : ℕ) (j : ℕ) (hjn : j ≤ n) (hd : n - j = d)
      (Q : DyadicSquare j) (Q' : SomeDyadicSquare),
      Q' ∈ halfCapCoverCube u Pbar j hjn Q → Q'.square.toSet ⊆ Q.toSet := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro j hjn hd Q Q' hQ'
    by_cases h : j < n
    · by_cases hcap : ((leavesInCube j hjn Q Pbar).card : ℝ) ≥ (dyadicCap n j u) / 2
      · have h_def : halfCapCoverCube u Pbar j hjn Q = {⟨j, Q⟩} := by
          rw [halfCapCoverCube, dif_pos h, if_pos hcap] <;> rfl
        rw [h_def] at hQ'
        have h_eq : Q' = ⟨j, Q⟩ := by simpa using hQ'
        subst h_eq
        exact subset_refl _
      · have h_def : halfCapCoverCube u Pbar j hjn Q =
            (dyadicChildren Q).biUnion (fun child =>
              halfCapCoverCube u Pbar (j + 1) (by omega) child) := by
          rw [halfCapCoverCube, dif_pos h, if_neg hcap] <;> rfl
        rw [h_def] at hQ'
        rcases Finset.mem_biUnion.mp hQ' with ⟨child, hchild, hQ'_child⟩
        have h_d' : n - (j + 1) = d - 1 := by omega
        have h_sub1 : Q'.square.toSet ⊆ child.toSet :=
          ih (d - 1) (by omega) (j + 1) (by omega) h_d' child Q' hQ'_child
        have h_sub2 : child.toSet ⊆ Q.toSet := dyadicChild_toSet_subset hchild
        exact Set.Subset.trans h_sub1 h_sub2
    · have h_not : ¬j < n := h
      by_cases hpos : (leavesInCube j hjn Q Pbar).card > 0
      · have h_def : halfCapCoverCube u Pbar j hjn Q = {⟨j, Q⟩} := by
          rw [halfCapCoverCube, dif_neg h_not, if_pos hpos] <;> rfl
        rw [h_def] at hQ'
        have h_eq : Q' = ⟨j, Q⟩ := by simpa using hQ'
        subst h_eq
        exact subset_refl _
      · have h_def : halfCapCoverCube u Pbar j hjn Q = ∅ := by
          rw [halfCapCoverCube, dif_neg h_not, if_neg hpos] <;> rfl
        rw [h_def] at hQ'
        simp at hQ'

/-- Helper: integer division identity (a / b) / 2 = a / (b * 2) for b > 0. -/
lemma int_ediv_div2 (a : ℤ) {b : ℤ} (hb : 0 < b) :
    (a / b) / 2 = a / (b * 2) := by
  set q : ℤ := a / b with hq
  set r : ℤ := a % b with hr
  have h_eq : a = q * b + r := by
    have h : a = (a / b) * b + a % b := by exact Eq.symm (Int.ediv_mul_add_emod a b)
    exact h
  have hr_nonneg : 0 ≤ r := Int.emod_nonneg a (by linarith)
  have hr_lt : r < b := Int.emod_lt_of_pos a hb
  have h_qmod_nonneg : 0 ≤ q % 2 := Int.emod_nonneg q (by norm_num)
  have h_qmod_lt : q % 2 < 2 := Int.emod_lt_of_pos q (by norm_num)
  have h_qmod : q % 2 = 0 ∨ q % 2 = 1 := by omega
  set c : ℤ := b * 2 with hc_def
  have hc_pos : 0 < c := by positivity
  have h9 : q = (q / 2) * 2 + q % 2 := by exact Eq.symm (Int.ediv_mul_add_emod q 2)
  have h10 : a = (q / 2) * c + (q % 2 * b + r) := by
    have h11 : q * b + r = (q / 2) * c + (q % 2 * b + r) := by
      have h12 : q * b = ((q / 2) * 2 + q % 2) * b := by
        exact congr_arg (fun x => x * b) h9
      rw [h12]
      simp only [hc_def] <;> ring
    rw [h_eq]
    exact h11
  have h4 : 0 ≤ q % 2 * b + r := by
    have h41 : 0 ≤ q % 2 * b := by
      exact mul_nonneg h_qmod_nonneg hb.le
    linarith
  have h5 : q % 2 * b + r < c := by
    rcases h_qmod with (h0 | h1)
    · rw [h0, hc_def]
      <;> linarith
    · rw [h1, hc_def]
      <;> linarith
  have h13 : (q % 2 * b + r) / c = 0 := Int.ediv_eq_zero_of_lt h4 h5
  have h14 : ((q % 2 * b + r) + (q / 2) * c) / c = (q % 2 * b + r) / c + q / 2 := by
    have hc_ne : c ≠ 0 := hc_pos.ne'
    have h : ((q % 2 * b + r) + (q / 2) * c) / c = (q % 2 * b + r) / c + q / 2 := by
      rw [show (q % 2 * b + r) + (q / 2) * c = (q % 2 * b + r) + (q / 2) * c from rfl]
      letI : NeZero c := ⟨hc_ne⟩
      exact Int.add_mul_ediv_right (q % 2 * b + r) (q / 2) hc_ne
    exact h
  have h15 : a / c = q / 2 := by
    rw [h10]
    have h_comm : (q / 2) * c + (q % 2 * b + r) = (q % 2 * b + r) + (q / 2) * c := by ring
    rw [h_comm]
    rw [h14, h13] <;> ring
  have h_final : a / (b * 2) = q / 2 := by
    simpa [hc_def] using h15
  exact h_final.symm

/-- Extensionality for dyadic squares. -/
lemma DyadicSquare.ext {n : ℕ} {x y : DyadicSquare n}
    (hi : x.i = y.i) (hj : x.j = y.j) : x = y := by
  cases x <;> cases y <;> simp_all <;> tauto

/-- The level-(j+1) ancestor of p is a child of its level-j ancestor Q. -/
lemma level_succ_ancestor_in_children {n j : ℕ} (hjn : j < n)
    (p : DyadicSquare n) (Q : DyadicSquare j)
    (hQ : dyadicAncestor j (by linarith) p = Q) :
    dyadicAncestor (j + 1) (by linarith) p ∈ dyadicChildren Q := by
  set c : DyadicSquare (j + 1) := dyadicAncestor (j + 1) (by linarith) p with hc_def
  have h_pos1 : (0 : ℤ) < 2 ^ (n - (j + 1)) := by positivity
  have h1 : c.i / 2 = Q.i := by
    simp only [hc_def, dyadicAncestor]
    have h2 : (p.i / (2 ^ (n - (j + 1)))) / 2 = p.i / ((2 ^ (n - (j + 1))) * 2) :=
      int_ediv_div2 p.i h_pos1
    have h3 : (2 ^ (n - (j + 1)) : ℤ) * 2 = 2 ^ (n - j) := by
      have h4 : n - j = (n - (j + 1)) + 1 := by omega
      rw [h4, pow_succ] <;> ring
    have h5 : p.i / ((2 ^ (n - (j + 1)) : ℤ) * 2) = p.i / (2 ^ (n - j)) := by rw [h3]
    rw [h2, h5]
    exact congr_arg DyadicSquare.i hQ
  have h2 : c.j / 2 = Q.j := by
    simp only [hc_def, dyadicAncestor]
    have h3 : (p.j / (2 ^ (n - (j + 1)))) / 2 = p.j / ((2 ^ (n - (j + 1))) * 2) :=
      int_ediv_div2 p.j h_pos1
    have h4 : (2 ^ (n - (j + 1)) : ℤ) * 2 = 2 ^ (n - j) := by
      have h5 : n - j = (n - (j + 1)) + 1 := by omega
      rw [h5, pow_succ] <;> ring
    have h6 : p.j / ((2 ^ (n - (j + 1)) : ℤ) * 2) = p.j / (2 ^ (n - j)) := by rw [h4]
    rw [h3, h6]
    exact congr_arg DyadicSquare.j hQ
  have h3 : c.i = 2 * Q.i ∨ c.i = 2 * Q.i + 1 := by omega
  have h4 : c.j = 2 * Q.j ∨ c.j = 2 * Q.j + 1 := by omega
  simp only [dyadicChildren, Finset.mem_insert, Finset.mem_singleton]
  rcases h3 with (h3a | h3b)
  · rcases h4 with (h4a | h4b)
    · have h_eq : c = (⟨2 * Q.i, 2 * Q.j⟩ : DyadicSquare (j + 1)) := DyadicSquare.ext h3a h4a
      exact Or.inl h_eq
    · have h_eq : c = (⟨2 * Q.i, 2 * Q.j + 1⟩ : DyadicSquare (j + 1)) := DyadicSquare.ext h3a h4b
      exact Or.inr (Or.inr (Or.inl h_eq))
  · rcases h4 with (h4a | h4b)
    · have h_eq : c = (⟨2 * Q.i + 1, 2 * Q.j⟩ : DyadicSquare (j + 1)) := DyadicSquare.ext h3b h4a
      exact Or.inr (Or.inl h_eq)
    · have h_eq : c = (⟨2 * Q.i + 1, 2 * Q.j + 1⟩ : DyadicSquare (j + 1)) := DyadicSquare.ext h3b h4b
      exact Or.inr (Or.inr (Or.inr h_eq))

/-- If a leaf square meets the unit ball, its level-0 ancestor is in rootSquares. -/
lemma leaf_meets_unitBall_has_root {n : ℕ} (p : DyadicSquare n)
    (h : Set.Nonempty ((p.toSet : Set EuclideanPlane) ∩ Metric.closedBall 0 1)) :
    dyadicAncestor 0 (by linarith) p ∈ rootSquares := by
  rcases h with ⟨x, hx, hball⟩
  have hball' : ‖x‖ ≤ 1 := by
    simpa [Metric.mem_closedBall] using hball
  have hx0 : |x 0| ≤ 1 := by
    have h : |x 0| ≤ ‖x‖ := abs_coord_le_norm x 0
    linarith
  have hx1 : |x 1| ≤ 1 := by
    have h : |x 1| ≤ ‖x‖ := abs_coord_le_norm x 1
    linarith
  set δ : ℝ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_eq : δ = 1 / (2 : ℝ)^n := by
    simp only [δ, dyadicDelta]
    <;> rw [Real.rpow_neg (by norm_num)]
    <;> field_simp
  have hpi1 : (p.i : ℝ) * δ ≤ x 0 := hx.1
  have hpi2 : x 0 < ((p.i : ℝ) + 1) * δ := hx.2.1
  have hpj1 : (p.j : ℝ) * δ ≤ x 1 := hx.2.2.1
  have hpj2 : x 1 < ((p.j : ℝ) + 1) * δ := hx.2.2.2
  have h_x0_lower : -1 ≤ x 0 := by linarith [abs_le.mp hx0]
  have h_x0_upper : x 0 ≤ 1 := by linarith [abs_le.mp hx0]
  have h_x1_lower : -1 ≤ x 1 := by linarith [abs_le.mp hx1]
  have h_x1_upper : x 1 ≤ 1 := by linarith [abs_le.mp hx1]
  have h_i_upper : p.i ≤ (2 : ℤ)^n := by
    have h6 : (p.i : ℝ) * δ ≤ 1 := by linarith
    have h7 : (p.i : ℝ) ≤ 1 / δ := by
      calc (p.i : ℝ)
        = (p.i : ℝ) * δ / δ := by field_simp [hδ_pos.ne'] <;> ring
      _ ≤ 1 / δ := by gcongr
    have h8 : 1 / δ = (2 : ℝ)^n := by
      rw [hδ_eq] <;> field_simp <;> ring
    have h9 : (p.i : ℝ) ≤ (2 : ℝ)^n := by linarith [h7, h8]
    exact_mod_cast h9
  have h_i_lower : -(2 : ℤ)^n ≤ p.i := by
    have h6 : ((p.i : ℝ) + 1) * δ > -1 := by linarith
    have h7 : (p.i : ℝ) + 1 > -1 / δ := by
      by_contra h8
      have h9 : (p.i : ℝ) + 1 ≤ -1 / δ := by linarith
      have h10 : ((p.i : ℝ) + 1) * δ ≤ (-1 / δ) * δ := by gcongr
      have h11 : (-1 / δ) * δ = -1 := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [h11] at h10
      linarith
    have h8 : 1 / δ = (2 : ℝ)^n := by
      rw [hδ_eq] <;> field_simp <;> ring
    have h9 : -1 / δ = -(2 : ℝ)^n := by
      have h10 : (-1 : ℝ) / δ = -((1 : ℝ) / δ) := by ring
      rw [h10, h8]
    have h10 : (p.i : ℝ) + 1 > -(2 : ℝ)^n := by
      rw [h9] at h7
      exact h7
    have h11 : (p.i : ℝ) > -(2 : ℝ)^n - 1 := by linarith
    have h12 : p.i > -(2 ^ n) - 1 := by exact_mod_cast h11
    omega
  have h_j_upper : p.j ≤ (2 : ℤ)^n := by
    have h6 : (p.j : ℝ) * δ ≤ 1 := by linarith
    have h7 : (p.j : ℝ) ≤ 1 / δ := by
      calc (p.j : ℝ)
        = (p.j : ℝ) * δ / δ := by field_simp [hδ_pos.ne'] <;> ring
      _ ≤ 1 / δ := by gcongr
    have h8 : 1 / δ = (2 : ℝ)^n := by
      rw [hδ_eq] <;> field_simp <;> ring
    have h9 : (p.j : ℝ) ≤ (2 : ℝ)^n := by linarith [h7, h8]
    exact_mod_cast h9
  have h_j_lower : -(2 : ℤ)^n ≤ p.j := by
    have h6 : ((p.j : ℝ) + 1) * δ > -1 := by linarith
    have h7 : (p.j : ℝ) + 1 > -1 / δ := by
      by_contra h8
      have h9 : (p.j : ℝ) + 1 ≤ -1 / δ := by linarith
      have h10 : ((p.j : ℝ) + 1) * δ ≤ (-1 / δ) * δ := by gcongr
      have h11 : (-1 / δ) * δ = -1 := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [h11] at h10
      linarith
    have h8 : 1 / δ = (2 : ℝ)^n := by
      rw [hδ_eq] <;> field_simp <;> ring
    have h9 : -1 / δ = -(2 : ℝ)^n := by
      have h10 : (-1 : ℝ) / δ = -((1 : ℝ) / δ) := by ring
      rw [h10, h8]
    have h10 : (p.j : ℝ) + 1 > -(2 : ℝ)^n := by
      rw [h9] at h7
      exact h7
    have h11 : (p.j : ℝ) > -(2 : ℝ)^n - 1 := by linarith
    have h12 : p.j > -(2 ^ n) - 1 := by exact_mod_cast h11
    omega
  let R := dyadicAncestor 0 (by linarith) p
  have hRi : R.i = p.i / (2 ^ n) := by
    simp [R, dyadicAncestor] <;> rfl
  have hRj : R.j = p.j / (2 ^ n) := by
    simp [R, dyadicAncestor] <;> rfl
  have h_pos2 : (0 : ℤ) < 2 ^ n := by positivity
  have hRi_range : R.i ∈ Finset.Icc (-1 : ℤ) 1 := by
    rw [hRi]
    simp only [Finset.mem_Icc]
    have h10 : -1 ≤ p.i / (2 ^ n) := by
      have h11 : (-(2 ^ n : ℤ)) / (2 ^ n) ≤ p.i / (2 ^ n) :=
        Int.ediv_le_ediv (by positivity) h_i_lower
      have h12 : (-(2 ^ n : ℤ)) / (2 ^ n) = -1 := by
        have h13 : (2 ^ n : ℤ) ≠ 0 := by positivity
        rw [Int.neg_ediv, Int.ediv_self h13] <;> norm_num
      rw [h12] at h11
      exact h11
    have h14 : p.i / (2 ^ n) ≤ 1 := by
      have h15 : p.i / (2 ^ n) ≤ (2 ^ n : ℤ) / (2 ^ n) :=
        Int.ediv_le_ediv (by positivity) h_i_upper
      have h16 : (2 ^ n : ℤ) / (2 ^ n) = 1 := by
        have h17 : (2 ^ n : ℤ) ≠ 0 := by positivity
        rw [Int.ediv_self h17]
      rw [h16] at h15
      exact h15
    exact ⟨h10, h14⟩
  have hRj_range : R.j ∈ Finset.Icc (-1 : ℤ) 1 := by
    rw [hRj]
    simp only [Finset.mem_Icc]
    have h10 : -1 ≤ p.j / (2 ^ n) := by
      have h11 : (-(2 ^ n : ℤ)) / (2 ^ n) ≤ p.j / (2 ^ n) :=
        Int.ediv_le_ediv (by positivity) h_j_lower
      have h12 : (-(2 ^ n : ℤ)) / (2 ^ n) = -1 := by
        have h13 : (2 ^ n : ℤ) ≠ 0 := by positivity
        rw [Int.neg_ediv, Int.ediv_self h13] <;> norm_num
      rw [h12] at h11
      exact h11
    have h14 : p.j / (2 ^ n) ≤ 1 := by
      have h15 : p.j / (2 ^ n) ≤ (2 ^ n : ℤ) / (2 ^ n) :=
        Int.ediv_le_ediv (by positivity) h_j_upper
      have h16 : (2 ^ n : ℤ) / (2 ^ n) = 1 := by
        have h17 : (2 ^ n : ℤ) ≠ 0 := by positivity
        rw [Int.ediv_self h17]
      rw [h16] at h15
      exact h15
    exact ⟨h10, h14⟩
  have h_final : R ∈ rootSquares := by
    simp only [rootSquares, Finset.mem_biUnion]
    refine' ⟨R.i, hRi_range, ?_⟩
    simp only [Finset.mem_image]
    exact ⟨R.j, hRj_range, by cases R <;> rfl⟩
  exact h_final

/-- If p descends from Q and has a half-cap ancestor at or below Q, then
    p is covered by `halfCapCoverCube` from Q. -/
lemma halfCapCoverCube_covers_path {n : ℕ} {u : ℝ} {Pbar : Finset (DyadicSquare n)}
    (hu_pos : 0 < u) :
    ∀ (d : ℕ) (j : ℕ) (hjn : j ≤ n) (hd : n - j = d)
      (Q : DyadicSquare j) (p : DyadicSquare n),
      dyadicAncestor j hjn p = Q →
      (∃ (k : ℕ) (hkn : k ≤ n) (hjk : j ≤ k) (R : DyadicSquare k),
        dyadicAncestor k hkn p = R ∧
        ((leavesInCube k hkn R Pbar).card : ℝ) ≥ dyadicCap n k u / 2) →
      ∃ (Q' : SomeDyadicSquare), Q' ∈ halfCapCoverCube u Pbar j hjn Q ∧
        ∃ (hlev : Q'.level ≤ n), dyadicAncestor Q'.level hlev p = Q'.square := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro j hjn hd Q p hQ_ancestor h_half_cap
    by_cases h : j < n
    · -- j < n case
      by_cases hcap : ((leavesInCube j hjn Q Pbar).card : ℝ) ≥ (dyadicCap n j u) / 2
      · -- Q itself has half cap: it is kept
        have h_def : halfCapCoverCube u Pbar j hjn Q = {⟨j, Q⟩} := by
          rw [halfCapCoverCube, dif_pos h, if_pos hcap] <;> rfl
        refine' ⟨⟨j, Q⟩, _⟩
        rw [h_def]
        exact ⟨by simp, hjn, hQ_ancestor⟩
      · -- Q has < half cap: recurse into child
        rcases h_half_cap with ⟨k, hkn, hjk, R, hR_ancestor, hR_cap⟩
        have h_k_gt_j : j < k := by
          by_contra h'
          have h_k_eq_j : k = j := by omega
          subst h_k_eq_j
          have hR_eq_Q : R = Q := by
            exact hR_ancestor.symm.trans hQ_ancestor
          rw [hR_eq_Q] at hR_cap
          exact hcap hR_cap
        let c := dyadicAncestor (j + 1) (by linarith) p
        have hc_in : c ∈ dyadicChildren Q :=
          level_succ_ancestor_in_children h p Q hQ_ancestor
        have h_d' : n - (j + 1) = d - 1 := by omega
        have h_ih' := ih (d - 1) (by omega) (j + 1) (by omega) h_d' c p
        have h_c_ancestor : dyadicAncestor (j + 1) (by linarith) p = c := rfl
        have h_half_cap' : ∃ (k : ℕ) (hkn : k ≤ n) (hjk : j + 1 ≤ k) (R : DyadicSquare k),
            dyadicAncestor k hkn p = R ∧
            ((leavesInCube k hkn R Pbar).card : ℝ) ≥ dyadicCap n k u / 2 := by
          refine' ⟨k, hkn, by omega, R, hR_ancestor, hR_cap⟩
        rcases h_ih' h_c_ancestor h_half_cap' with ⟨Q', hQ'_in, hlev, hQ'_ancestor⟩
        have h_def : halfCapCoverCube u Pbar j hjn Q =
            (dyadicChildren Q).biUnion (fun child =>
              halfCapCoverCube u Pbar (j + 1) (by omega) child) := by
          rw [halfCapCoverCube, dif_pos h, if_neg hcap] <;> rfl
        refine' ⟨Q', _⟩
        rw [h_def]
        exact ⟨Finset.mem_biUnion.mpr ⟨c, hc_in, hQ'_in⟩, hlev, hQ'_ancestor⟩
    · -- j = n case
      have h_jn : j = n := by omega
      have h_not : ¬j < n := by omega
      rcases h_half_cap with ⟨k, hkn, hjk, R, hR_ancestor, hR_cap⟩
      have h_k_eq_j : k = j := by omega
      have h1 : (leavesInCube k hkn R Pbar).card > 0 := by
        have h_k_eq_n : k = n := by omega
        have h_cap1 : dyadicCap n k u = 1 := by
          rw [h_k_eq_n]
          exact dyadicCap_leaf n u
        rw [h_cap1] at hR_cap
        exact Nat.pos_of_ne_zero (fun h => by rw [h] at hR_cap; norm_num at hR_cap <;> linarith)
      have h2 : leavesInCube k hkn R Pbar = leavesInCube j hjn Q Pbar := by
        subst h_k_eq_j
        have hR_eq_Q : R = Q := hR_ancestor.symm.trans hQ_ancestor
        rw [hR_eq_Q] <;> rfl
      have h_pos : (leavesInCube j hjn Q Pbar).card > 0 := by
        rw [←h2]
        exact h1
      have h_def : halfCapCoverCube u Pbar j hjn Q = {⟨j, Q⟩} := by
        rw [halfCapCoverCube, dif_neg h_not, if_pos h_pos] <;> rfl
      refine' ⟨⟨j, Q⟩, _⟩
      rw [h_def]
      exact ⟨by simp, hjn, hQ_ancestor⟩

/-- The cover cubes are pairwise disjoint. -/
lemma halfCapCover_disjoint {n : ℕ} {u : ℝ} {Pbar : Finset (DyadicSquare n)} :
    ∀ Q1 ∈ halfCapCover u Pbar, ∀ Q2 ∈ halfCapCover u Pbar,
      Q1 ≠ Q2 → Disjoint (Q1.square.toSet) (Q2.square.toSet) := by
  have h_main : ∀ (d : ℕ) (j : ℕ) (hjn : j ≤ n) (hd : n - j = d) (Q : DyadicSquare j),
      ∀ Q1 ∈ halfCapCoverCube u Pbar j hjn Q, ∀ Q2 ∈ halfCapCoverCube u Pbar j hjn Q,
        Q1 ≠ Q2 → Disjoint (Q1.square.toSet) (Q2.square.toSet) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro j hjn hd Q Q1 hQ1 Q2 hQ2 hne
      by_cases h : j < n
      · by_cases hcap : ((leavesInCube j hjn Q Pbar).card : ℝ) ≥ (dyadicCap n j u) / 2
        · -- cover is singleton
          have h_def : halfCapCoverCube u Pbar j hjn Q = {⟨j, Q⟩} := by
            rw [halfCapCoverCube, dif_pos h, if_pos hcap] <;> rfl
          rw [h_def] at hQ1 hQ2
          have h1 : Q1 = ⟨j, Q⟩ := by simpa using hQ1
          have h2 : Q2 = ⟨j, Q⟩ := by simpa using hQ2
          exfalso
          exact hne (by rw [h1, h2])
        · -- recurse into children
          have h_def : halfCapCoverCube u Pbar j hjn Q =
              (dyadicChildren Q).biUnion (fun child =>
                halfCapCoverCube u Pbar (j + 1) (by omega) child) := by
            rw [halfCapCoverCube, dif_pos h, if_neg hcap] <;> rfl
          rw [h_def] at hQ1 hQ2
          rcases Finset.mem_biUnion.mp hQ1 with ⟨c1, hc1, hQ1'⟩
          rcases Finset.mem_biUnion.mp hQ2 with ⟨c2, hc2, hQ2'⟩
          by_cases hc : c1 = c2
          · subst hc
            have h_d' : n - (j + 1) = d - 1 := by omega
            exact ih (d - 1) (by omega) (j + 1) (by omega) h_d' c1 Q1 hQ1' Q2 hQ2' hne
          · -- different children: their sets are disjoint
            have h_cne : c1 ≠ c2 := hc
            have h_disj : Disjoint (c1.toSet) (c2.toSet) :=
              dyadicSquare_toSet_disjoint h_cne
            have h_d1 : n - (j + 1) < d := by omega
            have h_sub1 : Q1.square.toSet ⊆ c1.toSet :=
              halfCapCoverCube_subset (n - (j + 1)) (j + 1) (by omega) (by omega) c1 Q1 hQ1'
            have h_sub2 : Q2.square.toSet ⊆ c2.toSet :=
              halfCapCoverCube_subset (n - (j + 1)) (j + 1) (by omega) (by omega) c2 Q2 hQ2'
            exact Disjoint.mono h_sub1 h_sub2 h_disj
      · -- j = n
        have h_not : ¬j < n := h
        by_cases hpos : (leavesInCube j hjn Q Pbar).card > 0
        · have h_def : halfCapCoverCube u Pbar j hjn Q = {⟨j, Q⟩} := by
            rw [halfCapCoverCube, dif_neg h_not, if_pos hpos] <;> rfl
          rw [h_def] at hQ1 hQ2
          have h1 : Q1 = ⟨j, Q⟩ := by simpa using hQ1
          have h2 : Q2 = ⟨j, Q⟩ := by simpa using hQ2
          exfalso
          exact hne (by rw [h1, h2])
        · have h_def : halfCapCoverCube u Pbar j hjn Q = ∅ := by
            rw [halfCapCoverCube, dif_neg h_not, if_neg hpos] <;> rfl
          rw [h_def] at hQ1
          simp at hQ1
  intro Q1 hQ1 Q2 hQ2 hne
  have h1 : Q1 ∈ rootSquares.biUnion (fun Q0 => halfCapCoverCube u Pbar 0 (by linarith) Q0) := by
    simpa [halfCapCover] using hQ1
  have h2 : Q2 ∈ rootSquares.biUnion (fun Q0 => halfCapCoverCube u Pbar 0 (by linarith) Q0) := by
    simpa [halfCapCover] using hQ2
  rcases Finset.mem_biUnion.mp h1 with ⟨R1, hR1, hQ1'⟩
  rcases Finset.mem_biUnion.mp h2 with ⟨R2, hR2, hQ2'⟩
  by_cases hR : R1 = R2
  · subst hR
    exact h_main n 0 (by linarith) (by omega) R1 Q1 hQ1' Q2 hQ2' hne
  · -- different root squares: disjoint
    have h_Rne : R1 ≠ R2 := hR
    have h_disj : Disjoint (R1.toSet) (R2.toSet) :=
      dyadicSquare_toSet_disjoint h_Rne
    have h_sub1 : Q1.square.toSet ⊆ R1.toSet :=
      halfCapCoverCube_subset n 0 (by linarith) (by omega) R1 Q1 hQ1'
    have h_sub2 : Q2.square.toSet ⊆ R2.toSet :=
      halfCapCoverCube_subset n 0 (by linarith) (by omega) R2 Q2 hQ2'
    exact Disjoint.mono h_sub1 h_sub2 h_disj

/-- The cover covers every leaf of a maximal capacity-respecting subset's ground set.
    By maximality, any deleted leaf is in a full-capacity cube, which is kept in the cover. -/
lemma halfCapCover_covers_all {n : ℕ} {u : ℝ} {leaves Pbar : Finset (DyadicSquare n)}
    (hu_pos : 0 < u)
    (hPbar_sub : Pbar ⊆ leaves)
    (hPbar_cap : CapacityRespecting n u Pbar)
    (hPbar_max : ∀ p, p ∈ leaves → p ∉ Pbar →
      ∃ j hjn Q, dyadicAncestor j hjn p = Q ∧
        (leavesInCube j hjn Q Pbar).card = Nat.floor (dyadicCap n j u))
    (h_root : ∀ (L : DyadicSquare n), L ∈ leaves →
      dyadicAncestor 0 (by linarith) L ∈ rootSquares)
    (L : DyadicSquare n) (hL : L ∈ leaves) :
    ∃ (Q : SomeDyadicSquare), Q ∈ halfCapCover u Pbar ∧
      ∃ (hlev : Q.level ≤ n), dyadicAncestor Q.level hlev L = Q.square := by
  have hR : dyadicAncestor 0 (by linarith) L ∈ rootSquares := h_root L hL
  set R : DyadicSquare 0 := dyadicAncestor 0 (by linarith) L with hR_def
  have hR_in : R ∈ rootSquares := hR
  have h_half_cap : ∃ (k : ℕ) (hkn : k ≤ n) (h0k : 0 ≤ k) (Q : DyadicSquare k),
      dyadicAncestor k hkn L = Q ∧
      ((leavesInCube k hkn Q Pbar).card : ℝ) ≥ dyadicCap n k u / 2 := by
    by_cases hL_in : L ∈ Pbar
    · -- L ∈ Pbar: L itself has count ≥ 1 ≥ 1/2
      refine' ⟨n, by linarith, by linarith, L, _⟩
      have h_anc_n : dyadicAncestor n (by linarith) L = L := by
        simp [dyadicAncestor] <;> cases L <;> rfl
      have h1 : L ∈ leavesInCube n (by linarith) L Pbar := by
        simp only [leavesInCube, Finset.mem_filter]
        exact ⟨hL_in, h_anc_n⟩
      have h2 : 0 < (leavesInCube n (by linarith) L Pbar).card := Finset.card_pos.mpr ⟨L, h1⟩
      have h3 : ((leavesInCube n (by linarith) L Pbar).card : ℝ) ≥ 1 := by exact_mod_cast h2
      have h4 : dyadicCap n n u = 1 := dyadicCap_leaf n u
      exact ⟨h_anc_n, by rw [h4]; linarith⟩
    · -- L ∉ Pbar: maximality gives a full-capacity ancestor
      have hL' : L ∈ leaves := hL
      rcases hPbar_max L hL' hL_in with ⟨k, hkn, Q, hQ_anc, hQ_card⟩
      refine' ⟨k, hkn, by linarith, Q, hQ_anc, _⟩
      have h_cap_ge_one : 1 ≤ dyadicCap n k u := dyadicCap_one_le n k u hu_pos hkn
      have h_floor_ge_half : (Nat.floor (dyadicCap n k u) : ℝ) ≥ dyadicCap n k u / 2 :=
        floor_ge_half (dyadicCap n k u) h_cap_ge_one
      rw [hQ_card]
      exact h_floor_ge_half
  have h_main := halfCapCoverCube_covers_path hu_pos n 0 (by linarith) (by omega) R L
    (by exact hR_def.symm) h_half_cap
  rcases h_main with ⟨Q, hQ_in, hlev, hQ_anc⟩
  have hQ_in_cover : Q ∈ halfCapCover u Pbar := by
    simp only [halfCapCover, Finset.mem_biUnion]
    exact ⟨R, hR_in, hQ_in⟩
  exact ⟨Q, hQ_in_cover, hlev, hQ_anc⟩

/-! ### S-set cancellation mass bound -/

/-- External covering number is subadditive over finite unions. -/
lemma externalCoveringNumber_biUnion_le {X : Type*} [PseudoMetricSpace X]
    {ε : NNReal} {ι : Type*} (I : Finset ι) (A : ι → Set X) :
    Metric.externalCoveringNumber ε (⋃ i ∈ I, A i) ≤
      ∑ i ∈ I, Metric.externalCoveringNumber ε (A i) := by
  by_cases h : (∀ i ∈ I, Metric.externalCoveringNumber ε (A i) ≠ ⊤)
  · have h_choose : ∀ (i : ι), i ∈ I → ∃ (C_i : Set X),
        Metric.IsCover ε (A i) C_i ∧ C_i.encard = Metric.externalCoveringNumber ε (A i) := by
      intro i hi
      letI : Nonempty {C : Set X // Metric.IsCover ε (A i) C} := ⟨⟨A i, by simp⟩⟩
      have h_exists := ENat.exists_eq_iInf
        (fun (C : {C : Set X // Metric.IsCover ε (A i) C}) => (C.val : Set X).encard)
      rcases h_exists with ⟨C, hC_eq⟩
      have h_ext : (C.val : Set X).encard = Metric.externalCoveringNumber ε (A i) := by
        rw [hC_eq]; simp_rw [Metric.externalCoveringNumber, iInf_subtype] <;> rfl
      exact ⟨C.val, C.property, h_ext⟩
    let C : ι → Set X := fun i => if h : i ∈ I then Classical.choose (h_choose i h) else ∅
    have hC_cover : ∀ i ∈ I, Metric.IsCover ε (A i) (C i) := by
      intro i hi; have hC_def : C i = Classical.choose (h_choose i hi) := by simp [C, hi]
      rw [hC_def]; exact (Classical.choose_spec (h_choose i hi)).1
    have hC_eq : ∀ i ∈ I, (C i).encard = Metric.externalCoveringNumber ε (A i) := by
      intro i hi; have hC_def : C i = Classical.choose (h_choose i hi) := by simp [C, hi]
      rw [hC_def]; exact (Classical.choose_spec (h_choose i hi)).2
    let C_union : Set X := ⋃ i ∈ I, C i
    have h_cover : Metric.IsCover ε (⋃ i ∈ I, A i) C_union := by
      intro x hx; have h5 : x ∈ ⋃ i ∈ I, A i := hx
      have h_mem : ∃ (i : ι), i ∈ I ∧ x ∈ A i := by simpa [Set.mem_iUnion₂] using h5
      rcases h_mem with ⟨i, hi, hxi⟩
      rcases hC_cover i hi hxi with ⟨c, hc, hdist⟩
      exact ⟨c, Set.mem_iUnion₂.mpr ⟨i, hi, hc⟩, hdist⟩
    have h1 : Metric.externalCoveringNumber ε (⋃ i ∈ I, A i) ≤ C_union.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard h_cover
    have h_fin : ∀ i ∈ I, (C i).Finite := by
      intro i hi; have h_ne_top : (C i).encard ≠ ⊤ := by rw [hC_eq i hi]; exact h i hi
      exact Set.encard_ne_top_iff.mp h_ne_top
    let Cfin : ι → Finset X := fun i => if h : i ∈ I then (h_fin i h).toFinset else ∅
    have hCfin_coe : ∀ i ∈ I, (Cfin i : Set X) = C i := by
      intro i hi; have hdef : Cfin i = (h_fin i hi).toFinset := by simp [Cfin, hi]
      rw [hdef]; exact (h_fin i hi).coe_toFinset
    let Ufinset : Finset X := I.biUnion Cfin
    have hU_eq : (Ufinset : Set X) = C_union := by
      ext x; simp only [Ufinset, Finset.mem_coe, Finset.mem_biUnion, C_union, Set.mem_iUnion₂]
      constructor
      · rintro ⟨i, hi, hx⟩; have h_eq : (Cfin i : Set X) = C i := hCfin_coe i hi
        exact ⟨i, hi, h_eq ▸ hx⟩
      · rintro ⟨i, hi, hx⟩; have h_eq : (Cfin i : Set X) = C i := hCfin_coe i hi
        have h9 : C i = (Cfin i : Set X) := h_eq.symm
        rw [h9] at hx
        exact ⟨i, hi, hx⟩
    have h2 : C_union.encard ≤ ∑ i ∈ I, (C i).encard := by
      rw [← hU_eq]; have h3 : (Ufinset : Set X).encard = ↑Ufinset.card := by simp
      rw [h3]; have h4 : ↑Ufinset.card ≤ ∑ i ∈ I, ↑(Cfin i).card := by exact_mod_cast Finset.card_biUnion_le
      have h5 : ∑ i ∈ I, ↑(Cfin i).card ≤ ∑ i ∈ I, (C i).encard := by
        apply Finset.sum_le_sum; intro i hi
        have h6 : (Cfin i : Set X) = C i := hCfin_coe i hi
        have h7 : ↑(Cfin i).card = (C i).encard := by simpa using congr_arg Set.encard h6
        rw [h7]
      exact le_trans (by exact_mod_cast h4) h5
    have h6 : ∑ i ∈ I, (C i).encard = ∑ i ∈ I, Metric.externalCoveringNumber ε (A i) := by
      apply Finset.sum_congr rfl; intro i hi; exact hC_eq i hi
    calc Metric.externalCoveringNumber ε (⋃ i ∈ I, A i)
        ≤ C_union.encard := h1
      _ ≤ ∑ i ∈ I, (C i).encard := h2
      _ = ∑ i ∈ I, Metric.externalCoveringNumber ε (A i) := h6
  · have h' : ∃ i ∈ I, Metric.externalCoveringNumber ε (A i) = ⊤ := by simpa [not_forall] using h
    rcases h' with ⟨i, hi, htop⟩
    have h5 : (∑ j ∈ I, Metric.externalCoveringNumber ε (A j)) = ⊤ := by
      have h_zero_le : ∀ (j : ι), j ∈ I → 0 ≤ Metric.externalCoveringNumber ε (A j) := fun _ _ => bot_le
      have h6 : Metric.externalCoveringNumber ε (A i) ≤ ∑ j ∈ I, Metric.externalCoveringNumber ε (A j) :=
        Finset.single_le_sum h_zero_le hi
      rw [htop] at h6; simpa using h6
    rw [h5] <;> exact le_top

/-- Given a (δ, u, C)-set P covered by finitely many sets Q_i, each contained
    in a ball of radius r_i ≥ δ, then `1 ≤ C * Σ r_i^u`. -/
lemma sset_cover_sum_radii_bound_real {δ u C : ℝ} {P : Set EuclideanPlane}
    (hP : IsDeltaSSet δ u C P) (hP_bounded : Bornology.IsBounded P)
    (hδ_pos : 0 < δ) (hu_pos : 0 < u)
    {ι : Type*} (I : Finset ι) (Q : ι → Set EuclideanPlane) (r : ι → ℝ)
    (hcover : P ⊆ ⋃ i ∈ I, Q i)
    (hr_geδ : ∀ i ∈ I, δ ≤ r i) (hr_nonneg : ∀ i ∈ I, 0 ≤ r i)
    (hQ_in_ball : ∀ i ∈ I, ∃ c : EuclideanPlane, Q i ⊆ Metric.closedBall c (r i)) :
    (1 : ℝ) ≤ C * ∑ i ∈ I, (r i)^u := by
  let δnn := δ.toNNReal
  have hδnn_pos : 0 < δnn := by
    have h : (δnn : ℝ) = δ := by rw [Real.coe_toNNReal] <;> linarith
    exact NNReal.coe_pos.mp (h ▸ hδ_pos)
  have hP_nonempty : P.Nonempty := hP.1
  have hC_pos : 0 < C := hP.2.2.1
  have hs_nonneg : 0 ≤ u := hP.2.2.2.1
  have hNP_ne_top : Metric.externalCoveringNumber δnn P ≠ ⊤ := by
    rcases hP_bounded.subset_closedBall (0 : EuclideanPlane) with ⟨R, hR⟩
    have hK : IsCompact (Metric.closedBall (0 : EuclideanPlane) R) := isCompact_closedBall _ _
    have h_tb : TotallyBounded P := hK.totallyBounded.subset hR
    rcases Metric.exists_finite_isCover_of_totallyBounded hδnn_pos.ne' h_tb with ⟨N, _, hNfin, hNcover⟩
    have h : Metric.externalCoveringNumber δnn P ≤ N.encard := Metric.IsCover.externalCoveringNumber_le_encard hNcover
    have h2 : N.encard ≠ ⊤ := by exact Set.encard_ne_top_iff.mpr hNfin
    exact ne_top_of_le_ne_top h2 h
  have hNP_pos : 0 < Metric.externalCoveringNumber δnn P := Metric.externalCoveringNumber_pos_iff.mpr hP_nonempty
  have h_bound : ∀ i ∈ I, (Metric.externalCoveringNumber δnn (P ∩ Q i) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal (r i)) ^ u * (Metric.externalCoveringNumber δnn P : ENNReal) := by
    intro i hi; rcases hQ_in_ball i hi with ⟨c, hc⟩
    have h1 : P ∩ Q i ⊆ P ∩ Metric.closedBall c (r i) := by gcongr <;> exact hc
    have h2 : (Metric.externalCoveringNumber δnn (P ∩ Q i) : ENNReal) ≤
        (Metric.externalCoveringNumber δnn (P ∩ Metric.closedBall c (r i)) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h1
    have h3 := hP.2.2.2.2 c (r i) (hr_geδ i hi)
    exact le_trans h2 h3
  have h_sub : (Metric.externalCoveringNumber δnn P : ENNReal) ≤
      ∑ i ∈ I, (Metric.externalCoveringNumber δnn (P ∩ Q i) : ENNReal) := by
    have h4 : P ⊆ ⋃ i ∈ I, P ∩ Q i := by
      intro x hx; have h5 : x ∈ ⋃ i ∈ I, Q i := hcover hx
      have h_mem : ∃ (i : ι), i ∈ I ∧ x ∈ Q i := by simpa [Set.mem_iUnion₂] using h5
      rcases h_mem with ⟨i, hi, hxi⟩; exact Set.mem_iUnion₂.mpr ⟨i, hi, ⟨hx, hxi⟩⟩
    have h5 : (Metric.externalCoveringNumber δnn P : ENNReal) ≤
        (Metric.externalCoveringNumber δnn (⋃ i ∈ I, P ∩ Q i) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h4
    have h6 : (Metric.externalCoveringNumber δnn (⋃ i ∈ I, P ∩ Q i) : ENNReal) ≤
        ∑ i ∈ I, (Metric.externalCoveringNumber δnn (P ∩ Q i) : ENNReal) := by
      have h7 := externalCoveringNumber_biUnion_le (ε := δnn) I (fun i => P ∩ Q i)
      have h_sum_coe : ((∑ i ∈ I, Metric.externalCoveringNumber δnn (P ∩ Q i) : ENat) : ENNReal) =
          ∑ i ∈ I, (Metric.externalCoveringNumber δnn (P ∩ Q i) : ENNReal) := by
        have h_main : ∀ (s : Finset ι), ((∑ i ∈ s, Metric.externalCoveringNumber δnn (P ∩ Q i) : ENat) : ENNReal) =
            ∑ i ∈ s, (Metric.externalCoveringNumber δnn (P ∩ Q i) : ENNReal) := by
          intro s; induction s using Finset.induction with
          | empty => simp
          | @insert a s ha ih =>
            rw [Finset.sum_insert ha, Finset.sum_insert ha]
            have h_add : ((Metric.externalCoveringNumber δnn (P ∩ Q a) + ∑ i ∈ s, Metric.externalCoveringNumber δnn (P ∩ Q i) : ENat) : ENNReal) =
                (Metric.externalCoveringNumber δnn (P ∩ Q a) : ENNReal) + ((∑ i ∈ s, Metric.externalCoveringNumber δnn (P ∩ Q i) : ENat) : ENNReal) := by norm_cast
            rw [h_add, ih]
        exact h_main I
      have h8 : (Metric.externalCoveringNumber δnn (⋃ i ∈ I, P ∩ Q i) : ENNReal) ≤
          ((∑ i ∈ I, Metric.externalCoveringNumber δnn (P ∩ Q i) : ENat) : ENNReal) := by exact_mod_cast h7
      rw [h_sum_coe] at h8; exact h8
    exact le_trans h5 h6
  have h_sum_rpow : ∑ i ∈ I, (ENNReal.ofReal (r i)) ^ u = ENNReal.ofReal (∑ i ∈ I, (r i)^u) := by
    have h3 : ∀ i ∈ I, (ENNReal.ofReal (r i)) ^ u = ENNReal.ofReal ((r i)^u) := by
      intro i _; rw [← ENNReal.ofReal_rpow_of_nonneg (hr_nonneg i ‹_›) hs_nonneg] <;> rfl
    rw [Finset.sum_congr rfl h3]
    have h4 : ∀ (s : Finset ι), s ⊆ I → ∑ i ∈ s, ENNReal.ofReal ((r i)^u) = ENNReal.ofReal (∑ i ∈ s, (r i)^u) := by
      intro s hs; induction s using Finset.induction with
      | empty => simp
      | @insert a s ha ih =>
        have ha' : a ∈ I := hs (Finset.mem_insert_self a s)
        have hs' : s ⊆ I := fun x hx => hs (Finset.mem_insert_of_mem hx)
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        have h_nonneg1 : 0 ≤ (r a)^u := Real.rpow_nonneg (hr_nonneg a ha') u
        have h_nonneg2 : 0 ≤ ∑ i ∈ s, (r i)^u := by
          apply Finset.sum_nonneg; intro i hi; exact Real.rpow_nonneg (hr_nonneg i (hs' hi)) u
        rw [ih hs', ← ENNReal.ofReal_add h_nonneg1 h_nonneg2]
    exact h4 I (by simp)
  have h7 : ∑ i ∈ I, (Metric.externalCoveringNumber δnn (P ∩ Q i) : ENNReal) ≤
      (ENNReal.ofReal C * ENNReal.ofReal (∑ i ∈ I, (r i)^u)) * (Metric.externalCoveringNumber δnn P : ENNReal) := by
    calc
      ∑ i ∈ I, (Metric.externalCoveringNumber δnn (P ∩ Q i) : ENNReal)
        ≤ ∑ i ∈ I, (ENNReal.ofReal C * (ENNReal.ofReal (r i)) ^ u * (Metric.externalCoveringNumber δnn P : ENNReal)) :=
          Finset.sum_le_sum h_bound
    _ = (∑ i ∈ I, (ENNReal.ofReal C * (ENNReal.ofReal (r i)) ^ u)) * (Metric.externalCoveringNumber δnn P : ENNReal) := by rw [Finset.sum_mul]
    _ = (ENNReal.ofReal C * ∑ i ∈ I, (ENNReal.ofReal (r i)) ^ u) * (Metric.externalCoveringNumber δnn P : ENNReal) := by rw [Finset.mul_sum]
    _ = (ENNReal.ofReal C * ENNReal.ofReal (∑ i ∈ I, (r i)^u)) * (Metric.externalCoveringNumber δnn P : ENNReal) := by rw [h_sum_rpow]
  have h8 : (Metric.externalCoveringNumber δnn P : ENNReal) ≤
      (ENNReal.ofReal C * ENNReal.ofReal (∑ i ∈ I, (r i)^u)) * (Metric.externalCoveringNumber δnn P : ENNReal) :=
    le_trans h_sub h7
  let NP_ENN : ENNReal := ENat.toENNReal (Metric.externalCoveringNumber δnn P)
  have hNP_ENN_ne_top : NP_ENN ≠ ⊤ := by simp only [NP_ENN, ENat.toENNReal_ne_top]; exact hNP_ne_top
  have hNP_ENN_pos : 0 < NP_ENN := by
    have h_ne_zero : Metric.externalCoveringNumber δnn P ≠ 0 := hNP_pos.ne'
    have h : NP_ENN ≠ 0 := by
      intro h2
      have h5 : NP_ENN = ENat.toENNReal (Metric.externalCoveringNumber δnn P) := by rfl
      rw [h5] at h2
      have h6 : ENat.toENNReal (Metric.externalCoveringNumber δnn P) ≤ ENat.toENNReal 0 := by
        simpa using h2
      have h7 : Metric.externalCoveringNumber δnn P ≤ 0 := ENat.toENNReal_le.mp h6
      have h8 : Metric.externalCoveringNumber δnn P = 0 := bot_unique h7
      exact h_ne_zero h8
    have h_zero_le : 0 ≤ NP_ENN := by simp
    exact lt_of_le_of_ne h_zero_le h.symm
  let NP : ℝ := NP_ENN.toReal
  have hNP_pos' : 0 < NP := by
    have h_iff : 0 < NP_ENN.toReal ↔ 0 < NP_ENN ∧ NP_ENN < ⊤ := by rw [ENNReal.toReal_pos_iff]
    have h_lt_top : NP_ENN < ⊤ := Ne.lt_top hNP_ENN_ne_top
    exact h_iff.mpr ⟨hNP_ENN_pos, h_lt_top⟩
  have h9 : NP ≤ (C * ∑ i ∈ I, (r i)^u) * NP := by
    have h10 : ENNReal.ofReal C * ENNReal.ofReal (∑ i ∈ I, (r i)^u) =
        ENNReal.ofReal (C * ∑ i ∈ I, (r i)^u) := by rw [← ENNReal.ofReal_mul] <;> positivity
    rw [h10] at h8
    have h11 : NP_ENN ≤ ENNReal.ofReal (C * ∑ i ∈ I, (r i)^u) * NP_ENN := h8
    have h_b_ne_top : (ENNReal.ofReal (C * ∑ i ∈ I, (r i)^u) * NP_ENN) ≠ ⊤ := by
      apply ENNReal.mul_ne_top; exact ENNReal.ofReal_ne_top; exact hNP_ENN_ne_top
    have h12 : (ENNReal.ofReal (C * ∑ i ∈ I, (r i)^u) * NP_ENN).toReal =
        (ENNReal.ofReal (C * ∑ i ∈ I, (r i)^u)).toReal * NP_ENN.toReal := by
      rw [ENNReal.toReal_mul] <;> simp [hNP_ENN_ne_top]
    have h_iff : NP_ENN.toReal ≤ (ENNReal.ofReal (C * ∑ i ∈ I, (r i)^u) * NP_ENN).toReal ↔
        NP_ENN ≤ ENNReal.ofReal (C * ∑ i ∈ I, (r i)^u) * NP_ENN :=
      ENNReal.toReal_le_toReal hNP_ENN_ne_top h_b_ne_top
    have h13 : NP_ENN.toReal ≤ (ENNReal.ofReal (C * ∑ i ∈ I, (r i)^u) * NP_ENN).toReal := h_iff.mpr h11
    rw [h12] at h13
    have h14 : NP_ENN.toReal = NP := by rfl
    rw [h14] at h13
    have h15 : (ENNReal.ofReal (C * ∑ i ∈ I, (r i)^u)).toReal = C * ∑ i ∈ I, (r i)^u := by
      have h_nonneg : 0 ≤ C * ∑ i ∈ I, (r i)^u := by
        have hC : 0 ≤ C := by linarith
        have hS : 0 ≤ ∑ i ∈ I, (r i)^u := by
          apply Finset.sum_nonneg; intro i _; exact Real.rpow_nonneg (hr_nonneg i ‹_›) u
        positivity
      rw [ENNReal.toReal_ofReal h_nonneg]
    rw [h15] at h13; exact h13
  have h12 : (1 : ℝ) ≤ C * ∑ i ∈ I, (r i)^u := by nlinarith
  exact h12

/-- Mass lower bound from half-capacity cover + S-set cancellation:
    `Pbar_card ≥ (1/(8*C)) * δ^(-u)`. -/
lemma mass_lower_bound_half_cap
    {δ u C side_n : ℝ} {P : Set EuclideanPlane}
    (hP : IsDeltaSSet δ u C P) (hP_bounded : Bornology.IsBounded P)
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hu_pos : 0 < u) (hu_le_two : u ≤ 2)
    (h_side_n_pos : 0 < side_n) (h_side_n_leδ : side_n ≤ δ)
    {ι : Type*} (I : Finset ι) (Q : ι → Set EuclideanPlane) (side : ι → ℝ)
    (hcover : P ⊆ ⋃ i ∈ I, Q i)
    (hside_pos : ∀ i ∈ I, 0 < side i)
    (hside_ge_halfδ : ∀ i ∈ I, δ / 2 ≤ side i)
    (hQ_in_ball : ∀ i ∈ I, ∃ c : EuclideanPlane, Q i ⊆ Metric.closedBall c (2 * side i))
    (Pbar_card : ℝ) (hPbar_card_nonneg : 0 ≤ Pbar_card)
    (h_half_cap_sum : Pbar_card ≥ (1 / 2) * side_n^(-u) * ∑ i ∈ I, (side i)^u) :
    Pbar_card ≥ (1 / (8 * C)) * δ^(-u) := by
  let r : ι → ℝ := fun i => 2 * side i
  have hr_geδ : ∀ i ∈ I, δ ≤ r i := by intro i hi; linarith [hside_ge_halfδ i hi]
  have hr_nonneg : ∀ i ∈ I, 0 ≤ r i := by intro i hi; have h : 0 < side i := hside_pos i hi; linarith
  have hQ_in_ball' : ∀ i ∈ I, ∃ c : EuclideanPlane, Q i ⊆ Metric.closedBall c (r i) := by
    intro i hi; simpa [r] using hQ_in_ball i hi
  have h_sum_bound : (1 : ℝ) ≤ C * ∑ i ∈ I, (r i)^u :=
    sset_cover_sum_radii_bound_real hP hP_bounded hδ_pos hu_pos I Q r hcover hr_geδ hr_nonneg hQ_in_ball'
  have h_rpow : ∀ i ∈ I, (r i)^u = (2 : ℝ)^u * (side i)^u := by
    intro i hi; have h : r i = 2 * side i := by rfl
    rw [h]; have hpos1 : 0 ≤ (2 : ℝ) := by norm_num
    have hpos2 : 0 ≤ side i := (hside_pos i hi).le
    rw [Real.mul_rpow hpos1 hpos2]
  have h_sum_r : ∑ i ∈ I, (r i)^u = (2 : ℝ)^u * ∑ i ∈ I, (side i)^u := by
    rw [Finset.sum_congr rfl h_rpow, Finset.mul_sum] <;> ring
  have h_sum_bound3 : (1 : ℝ) ≤ C * (2 : ℝ)^u * ∑ i ∈ I, (side i)^u := by
    rw [h_sum_r] at h_sum_bound
    have h : C * ((2 : ℝ)^u * ∑ i ∈ I, (side i)^u) = C * (2 : ℝ)^u * ∑ i ∈ I, (side i)^u := by ring
    rw [h] at h_sum_bound; exact h_sum_bound
  have hC_pos : 0 < C := hP.2.2.1
  have h2u_pos : 0 < (2 : ℝ)^u := Real.rpow_pos_of_pos (by norm_num) u
  have h_pos : 0 < C * (2 : ℝ)^u := mul_pos hC_pos h2u_pos
  have h_sum_side_lower : ∑ i ∈ I, (side i)^u ≥ 1 / (C * (2 : ℝ)^u) := by
    have h : (1 : ℝ) ≤ C * (2 : ℝ)^u * ∑ i ∈ I, (side i)^u := h_sum_bound3
    calc
      1 / (C * (2 : ℝ)^u)
        ≤ (C * (2 : ℝ)^u * ∑ i ∈ I, (side i)^u) / (C * (2 : ℝ)^u) := by gcongr
      _ = ∑ i ∈ I, (side i)^u := by field_simp [h_pos.ne'] <;> ring
  have h_side_n_rpow : side_n^(-u) ≥ δ^(-u) := by
    have h1 : 0 ≤ u := by linarith
    have h2 : side_n^u ≤ δ^u := by gcongr <;> linarith
    have h3 : side_n^(-u) = (side_n^u)⁻¹ := by rw [Real.rpow_neg (by linarith)]
    have h4 : δ^(-u) = (δ^u)⁻¹ := by rw [Real.rpow_neg (by linarith)]
    rw [h3, h4]
    have h5 : 0 < side_n^u := Real.rpow_pos_of_pos h_side_n_pos u
    have h6 : 0 < δ^u := Real.rpow_pos_of_pos hδ_pos u
    have h7 : (side_n^u)⁻¹ ≥ (δ^u)⁻¹ := by
      have h8 : 1 / (δ^u) ≤ 1 / (side_n^u) := one_div_le_one_div_of_le h5 h2
      have h9 : (side_n^u)⁻¹ = 1 / (side_n^u) := by simp
      have h10 : (δ^u)⁻¹ = 1 / (δ^u) := by simp
      rw [h9, h10]; exact h8
    exact h7
  have h_main1 : Pbar_card ≥ (1 / 2) * side_n^(-u) * ∑ i ∈ I, (side i)^u := h_half_cap_sum
  have h_main2 : (1 / 2) * side_n^(-u) * ∑ i ∈ I, (side i)^u ≥
      (1 / 2) * δ^(-u) * (1 / (C * (2 : ℝ)^u)) := by gcongr <;> linarith
  have h_main3 : (1 / 2) * δ^(-u) * (1 / (C * (2 : ℝ)^u)) =
      (1 / (C * (2 : ℝ)^(u + 1))) * δ^(-u) := by
    have h4 : (2 : ℝ)^(u + 1) = 2 * (2 : ℝ)^u := by rw [Real.rpow_add (by norm_num)] <;> ring
    field_simp [hC_pos.ne', h2u_pos.ne'] <;> rw [h4] <;> ring
  have h_main4 : Pbar_card ≥ (1 / (C * (2 : ℝ)^(u + 1))) * δ^(-u) := by
    calc Pbar_card
        ≥ (1 / 2) * side_n^(-u) * ∑ i ∈ I, (side i)^u := h_main1
      _ ≥ (1 / 2) * δ^(-u) * (1 / (C * (2 : ℝ)^u)) := h_main2
      _ = (1 / (C * (2 : ℝ)^(u + 1))) * δ^(-u) := h_main3
  have h5 : (2 : ℝ)^(u + 1) ≤ 8 := by
    have h6 : u + 1 ≤ 3 := by linarith
    have h7 : 1 ≤ (2 : ℝ) := by norm_num
    have h8 : (2 : ℝ)^(u + 1) ≤ (2 : ℝ)^(3 : ℝ) := Real.rpow_le_rpow_of_exponent_le h7 h6
    have h9 : (2 : ℝ)^(3 : ℝ) = 8 := by norm_num
    rw [h9] at h8; exact h8
  have h10 : 1 / (C * (2 : ℝ)^(u + 1)) ≥ 1 / (8 * C) := by
    have h11 : 0 < C * (2 : ℝ)^(u + 1) := by positivity
    have h12 : C * (2 : ℝ)^(u + 1) ≤ 8 * C := by
      calc C * (2 : ℝ)^(u + 1)
          ≤ C * 8 := mul_le_mul_of_nonneg_left h5 hC_pos.le
        _ = 8 * C := by ring
    exact one_div_le_one_div_of_le h11 h12
  calc Pbar_card
      ≥ (1 / (C * (2 : ℝ)^(u + 1))) * δ^(-u) := h_main4
    _ ≥ (1 / (8 * C)) * δ^(-u) := by gcongr

/-! ### Core dyadic extraction theorem -/

/-- If Q is the level-j ancestor of leaf L, then L.toSet ⊆ Q.toSet. -/
lemma dyadicAncestor_toSet_subset {n : ℕ} :
    ∀ (d : ℕ) (j : ℕ) (hjn : j ≤ n) (hd : n - j = d)
      (L : DyadicSquare n) (Q : DyadicSquare j),
      dyadicAncestor j hjn L = Q → L.toSet ⊆ Q.toSet := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro j hjn hd L Q h
    by_cases h_jn : j = n
    · cases h_jn with
      | refl =>
        have h_anc_n : dyadicAncestor n (by linarith) L = L := by
          simp [dyadicAncestor] <;> cases L <;> rfl
        have hQ : Q = L := by
          rw [h_anc_n] at h
          exact h.symm
        rw [hQ]
    · have h_j_lt_n : j < n := by omega
      let c := dyadicAncestor (j + 1) (by omega) L
      have hc_in : c ∈ dyadicChildren Q := level_succ_ancestor_in_children h_j_lt_n L Q h
      have h1 : c.toSet ⊆ Q.toSet := dyadicChild_toSet_subset hc_in
      have h_d' : n - (j + 1) = d - 1 := by omega
      have h2 : L.toSet ⊆ c.toSet := ih (d - 1) (by omega) (j + 1) (by omega) h_d' L c rfl
      exact subset_trans h2 h1

/-- Existence of dyadic level j with side_j ≤ r ≤ 2 * side_j. -/
lemma exists_dyadic_level_for_ball {n : ℕ} {r : ℝ}
    (hr_ge : dyadicDelta n ≤ r) (hr_le : r ≤ 1) :
    ∃ (j : ℕ), j ≤ n ∧ dyadicDelta j ≤ r ∧ r ≤ 2 * dyadicDelta j := by
  have h_exists : ∃ (j : ℕ), dyadicDelta j ≤ r := ⟨n, hr_ge⟩
  let j : ℕ := Nat.find h_exists
  have hj_le : dyadicDelta j ≤ r := Nat.find_spec h_exists
  have hj_min : ∀ k < j, ¬(dyadicDelta k ≤ r) := fun k hk => Nat.find_min h_exists hk
  have h_j_le_n : j ≤ n := by
    by_cases h : j ≤ n
    · exact h
    · have h' : n < j := by omega
      have h_contra : ¬(dyadicDelta n ≤ r) := hj_min n h'
      exact False.elim (h_contra hr_ge)
  have h_r_le_2side : r ≤ 2 * dyadicDelta j := by
    by_cases h_j0 : j = 0
    · rw [h_j0]
      have h1 : dyadicDelta 0 = 1 := by simp [dyadicDelta]
      rw [h1] <;> linarith
    · have h_jpos : 0 < j := by omega
      have h_pred : j - 1 < j := by omega
      have h2 : ¬(dyadicDelta (j - 1) ≤ r) := hj_min (j - 1) h_pred
      have h3 : dyadicDelta (j - 1) = 2 * dyadicDelta j := by
        simp only [dyadicDelta]
        have h4 : j = (j - 1) + 1 := by omega
        rw [h4]
        simp [pow_succ]
        <;> field_simp
        <;> ring
      rw [h3] at h2
      have h4 : r < 2 * dyadicDelta j := by linarith
      linarith
  exact ⟨j, h_j_le_n, hj_le, h_r_le_2side⟩

/-- For a finite >2δ-separated set, external δ-covering number equals cardinality. -/
lemma ncover_eq_card_of_twoδ_separated {X : Type*} [PseudoMetricSpace X] {δ : ℝ} (hδ_pos : 0 < δ)
    {S : Finset X} (h_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2 * δ < dist x y) :
    Metric.externalCoveringNumber δ.toNNReal (S : Set X) = ↑(S.card) := by
  let ε : NNReal := δ.toNNReal
  have hε_coe : (ε : ℝ) = δ := by
    simp [ε, hδ_pos.le]
  have h1 : Metric.externalCoveringNumber ε (S : Set X) ≤ (S.card : ENat) := by
    have h1' : Metric.externalCoveringNumber ε (S : Set X) ≤ (S : Set X).encard :=
      Metric.externalCoveringNumber_le_encard_self (S : Set X)
    have h2 : (S : Set X).encard = (S.card : ENat) := by simp
    rw [h2] at h1'
    exact h1'
  have h_is_sep : Metric.IsSeparated (↑(2 * ε) : ENNReal) (S : Set X) := by
    simp only [Metric.IsSeparated, Set.Pairwise]
    intro x hx y hy hne
    have h_dist : 2 * δ < dist x y := h_sep x hx y hy hne
    have h_edist : edist x y = ENNReal.ofReal (dist x y) := by
      rw [edist_dist] <;> rfl
    rw [h_edist]
    have h_final : (↑(2 * ε) : ENNReal) < ENNReal.ofReal (dist x y) := by
      have h : 2 * (ε : ℝ) < dist x y := by rw [hε_coe] <;> linarith
      have hpos : 0 < dist x y := by linarith
      have h_coe : (↑(2 * ε) : ENNReal) = ENNReal.ofReal (2 * (ε : ℝ)) := by
        simp
      rw [h_coe]
      exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr h
    exact h_final
  have h3 : (S.card : ENat) ≤ Metric.packingNumber (2 * ε) (S : Set X) := by
    have h4 : (S : Set X).encard = (S.card : ENat) := by simp
    have h5 : (S : Set X).encard ≤ Metric.packingNumber (2 * ε) (S : Set X) :=
      Metric.IsSeparated.encard_le_packingNumber (Set.Subset.refl _) h_is_sep
    rw [h4] at h5
    exact h5
  have h6 : Metric.packingNumber (2 * ε) (S : Set X) ≤ Metric.externalCoveringNumber ε (S : Set X) :=
    Metric.packingNumber_two_mul_le_externalCoveringNumber ε (S : Set X)
  have h7 : (S.card : ENat) ≤ Metric.externalCoveringNumber ε (S : Set X) :=
    le_trans h3 h6
  exact le_antisymm h1 h7

end DirecretisedFurstenbergEstimate.FrontEndLemmas

end
