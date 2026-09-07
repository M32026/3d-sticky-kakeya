module

/-
  Heavy square refinement and non-concentration transfer.

  ## Main results

  1. `qset_nonconcentration`: transfer of non-concentration from a point set P''
     to the centers of heavy Δ-squares Qset.

  Whiteprint: heavy_squares (refinement sub-part)
  Dependencies: HeavySquareEnergyBound
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.HeavySquareEnergyBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicRefinement
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate.Lagoon

open DirecretisedFurstenbergEstimate

/-! ### Heavy square refinement and non-concentration -/

local notation "Plane" => EuclideanPlane

/-- The set of plane points belonging to a coarse Δ-square. -/
def squareSet (Δ : ℝ) (Q : ℤ × ℤ) : Set Plane :=
  {p | p 0 ∈ Set.Ico (Δ * (Q.1 : ℝ)) (Δ * ((Q.1 : ℝ) + 1)) ∧
       p 1 ∈ Set.Ico (Δ * (Q.2 : ℝ)) (Δ * ((Q.2 : ℝ) + 1))}

/-- Center of a coarse square in the plane. -/
noncomputable def squareCenter (Δ : ℝ) (Q : ℤ × ℤ) : EuclideanPlane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm
    (fun i : Fin 2 => if i = 0 then Δ * ((Q.1 : ℝ) + 1 / 2) else Δ * ((Q.2 : ℝ) + 1 / 2))

lemma squareCenter_zero (Δ : ℝ) (Q : ℤ × ℤ) :
    squareCenter Δ Q 0 = Δ * ((Q.1 : ℝ) + 1 / 2) := by
  simp [squareCenter]

lemma squareCenter_one (Δ : ℝ) (Q : ℤ × ℤ) :
    squareCenter Δ Q 1 = Δ * ((Q.2 : ℝ) + 1 / 2) := by
  simp [squareCenter]

/-- Geometric fact: any point in a Δ-square is within √2 * Δ / 2 of its center. -/
lemma point_in_square_close_to_center {Δ : ℝ} (hΔ_pos : 0 < Δ) (Q : ℤ × ℤ)
    (p : Plane) (hp : p ∈ squareSet Δ Q) :
    dist p (squareCenter Δ Q) ≤ Real.sqrt 2 * Δ / 2 := by
  have hx1 : Δ * (Q.1 : ℝ) ≤ p 0 := hp.1.1
  have hx2 : p 0 < Δ * ((Q.1 : ℝ) + 1) := hp.1.2
  have hy1 : Δ * (Q.2 : ℝ) ≤ p 1 := hp.2.1
  have hy2 : p 1 < Δ * ((Q.2 : ℝ) + 1) := hp.2.2
  have hcx : squareCenter Δ Q 0 = Δ * ((Q.1 : ℝ) + 1 / 2) := squareCenter_zero Δ Q
  have hcy : squareCenter Δ Q 1 = Δ * ((Q.2 : ℝ) + 1 / 2) := squareCenter_one Δ Q
  have hdx : |p 0 - squareCenter Δ Q 0| ≤ Δ / 2 := by
    rw [hcx]
    have h1 : -(Δ / 2) ≤ p 0 - Δ * ((Q.1 : ℝ) + 1 / 2) := by linarith
    have h2 : p 0 - Δ * ((Q.1 : ℝ) + 1 / 2) ≤ Δ / 2 := by linarith
    exact abs_le.mpr ⟨h1, h2⟩
  have hdy : |p 1 - squareCenter Δ Q 1| ≤ Δ / 2 := by
    rw [hcy]
    have h1 : -(Δ / 2) ≤ p 1 - Δ * ((Q.2 : ℝ) + 1 / 2) := by linarith
    have h2 : p 1 - Δ * ((Q.2 : ℝ) + 1 / 2) ≤ Δ / 2 := by linarith
    exact abs_le.mpr ⟨h1, h2⟩
  have h3 : ‖p - squareCenter Δ Q‖ ^ 2 =
      (p 0 - squareCenter Δ Q 0) ^ 2 + (p 1 - squareCenter Δ Q 1) ^ 2 := by
    have h_norm : ‖p - squareCenter Δ Q‖ =
        Real.sqrt ((p 0 - squareCenter Δ Q 0) ^ 2 + (p 1 - squareCenter Δ Q 1) ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      <;> simp [Fin.sum_univ_two]
      <;> ring
    rw [h_norm]
    rw [Real.sq_sqrt (by positivity)]
    <;> ring
  have h4 : ‖p - squareCenter Δ Q‖ ^ 2 ≤ (Δ / 2) ^ 2 + (Δ / 2) ^ 2 := by
    rw [h3]
    have h5 : (p 0 - squareCenter Δ Q 0) ^ 2 ≤ (Δ / 2) ^ 2 := by
      have h6 : |p 0 - squareCenter Δ Q 0| ≤ Δ / 2 := hdx
      have h7 : |p 0 - squareCenter Δ Q 0| ^ 2 ≤ (Δ / 2) ^ 2 := by gcongr
      rw [sq_abs] at h7; exact h7
    have h8 : (p 1 - squareCenter Δ Q 1) ^ 2 ≤ (Δ / 2) ^ 2 := by
      have h9 : |p 1 - squareCenter Δ Q 1| ≤ Δ / 2 := hdy
      have h10 : |p 1 - squareCenter Δ Q 1| ^ 2 ≤ (Δ / 2) ^ 2 := by gcongr
      rw [sq_abs] at h10; exact h10
    linarith
  have h10 : ‖p - squareCenter Δ Q‖ ≤ Real.sqrt 2 * Δ / 2 := by
    have h11 : 0 ≤ ‖p - squareCenter Δ Q‖ := by positivity
    have h12 : (Real.sqrt 2 * Δ / 2) ^ 2 = (Δ / 2) ^ 2 + (Δ / 2) ^ 2 := by
      have h13 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      have h14 : (Real.sqrt 2 * Δ / 2) ^ 2 = (Real.sqrt 2) ^ 2 * (Δ / 2) ^ 2 := by ring
      rw [h14]
      have h15 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      rw [h15] <;> ring
    have h16 : ‖p - squareCenter Δ Q‖ ^ 2 ≤ (Real.sqrt 2 * Δ / 2) ^ 2 := by
      rw [h3, h12] <;> linarith
    have h17 : 0 ≤ Real.sqrt 2 * Δ / 2 := by positivity
    nlinarith
  have h14 : dist p (squareCenter Δ Q) = ‖p - squareCenter Δ Q‖ := by rw [dist_eq_norm]
  rw [h14]; exact h10

section Classical

attribute [local instance] Classical.propDecidable

/-- Core non-concentration transfer: if every selected square has ≥ m points of P'',
    and P'' has the ball-count property, then the square centers are non-concentrated.
-/
lemma qset_nonconcentration
    {Δ t C m K : ℝ} (hΔ_pos : 0 < Δ) (ht_pos : 0 < t) (hC_pos : 0 < C)
    (hm_pos : 0 < m) (hK_pos : 0 < K)
    (P'' : Finset Plane)
    (Qset : Finset (ℤ × ℤ))
    (hP''_ball : ∀ (x : Plane) (r : ℝ), Δ ≤ r →
      ((P''.filter (fun y => dist x y ≤ r)).card : ℝ) ≤ C * r^t * (P''.card : ℝ))
    (h_mult : ∀ Q ∈ Qset, m ≤ (P''.filter (fun p => p ∈ squareSet Δ Q)).card)
    (h_size : (P''.card : ℝ) ≤ K * m * (Qset.card : ℝ)) :
    ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card : ℝ) ≤
        C * K * (1 + Real.sqrt 2 / 2)^t * r^t * (Qset.card : ℝ) := by
  classical
  intro c r hr
  let Q_in := Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)
  have h1 : ∀ Q ∈ Q_in, (P''.filter (fun p => p ∈ squareSet Δ Q)).card ≥ m := by
    intro Q hQ
    have hQ' : Q ∈ Qset := (Finset.mem_filter.mp hQ).1
    exact h_mult Q hQ'
  have h_disj : ∀ (Q1 Q2 : ℤ × ℤ), Q1 ≠ Q2 →
      Disjoint (P''.filter (fun p => p ∈ squareSet Δ Q1))
        (P''.filter (fun p => p ∈ squareSet Δ Q2)) := by
    intro Q1 Q2 hne
    simp only [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 : p ∈ squareSet Δ Q1 := (Finset.mem_filter.mp hp1).2
    have h2 : p ∈ squareSet Δ Q2 := (Finset.mem_filter.mp hp2).2
    have hx11 : Δ * (Q1.1 : ℝ) ≤ p 0 := h1.1.1
    have hx12 : p 0 < Δ * ((Q1.1 : ℝ) + 1) := h1.1.2
    have hx21 : Δ * (Q2.1 : ℝ) ≤ p 0 := h2.1.1
    have hx22 : p 0 < Δ * ((Q2.1 : ℝ) + 1) := h2.1.2
    have h3 : Q1.1 = Q2.1 := by
      by_contra hne
      have h_lt : Q1.1 < Q2.1 ∨ Q2.1 < Q1.1 := by omega
      rcases h_lt with (h_lt | h_lt)
      · have h_ineq1 : (Q1.1 : ℝ) + 1 ≤ (Q2.1 : ℝ) := by exact_mod_cast (by omega)
        have h_ineq2 : Δ * ((Q1.1 : ℝ) + 1) ≤ Δ * (Q2.1 : ℝ) := by gcongr
        have h_ineq3 : Δ * ((Q1.1 : ℝ) + 1) ≤ p 0 := by linarith [hx21]
        exact False.elim (not_le.mpr hx12 h_ineq3)
      · have h_ineq1 : (Q2.1 : ℝ) + 1 ≤ (Q1.1 : ℝ) := by exact_mod_cast (by omega)
        have h_ineq2 : Δ * ((Q2.1 : ℝ) + 1) ≤ Δ * (Q1.1 : ℝ) := by gcongr
        have h_ineq3 : Δ * ((Q2.1 : ℝ) + 1) ≤ p 0 := by linarith [hx11]
        exact False.elim (not_le.mpr hx22 h_ineq3)
    have hy11 : Δ * (Q1.2 : ℝ) ≤ p 1 := h1.2.1
    have hy12 : p 1 < Δ * ((Q1.2 : ℝ) + 1) := h1.2.2
    have hy21 : Δ * (Q2.2 : ℝ) ≤ p 1 := h2.2.1
    have hy22 : p 1 < Δ * ((Q2.2 : ℝ) + 1) := h2.2.2
    have h4 : Q1.2 = Q2.2 := by
      by_contra hne
      have h_lt : Q1.2 < Q2.2 ∨ Q2.2 < Q1.2 := by omega
      rcases h_lt with (h_lt | h_lt)
      · have h_ineq1 : (Q1.2 : ℝ) + 1 ≤ (Q2.2 : ℝ) := by exact_mod_cast (by omega)
        have h_ineq2 : Δ * ((Q1.2 : ℝ) + 1) ≤ Δ * (Q2.2 : ℝ) := by gcongr
        have h_ineq3 : Δ * ((Q1.2 : ℝ) + 1) ≤ p 1 := by linarith [hy21]
        exact False.elim (not_le.mpr hy12 h_ineq3)
      · have h_ineq1 : (Q2.2 : ℝ) + 1 ≤ (Q1.2 : ℝ) := by exact_mod_cast (by omega)
        have h_ineq2 : Δ * ((Q2.2 : ℝ) + 1) ≤ Δ * (Q1.2 : ℝ) := by gcongr
        have h_ineq3 : Δ * ((Q2.2 : ℝ) + 1) ≤ p 1 := by linarith [hy11]
        exact False.elim (not_le.mpr hy22 h_ineq3)
    have h5 : Q1 = Q2 := by
      ext <;> tauto
    exact hne h5
  have h_disj' : Set.PairwiseDisjoint (Q_in : Set (ℤ × ℤ))
      (fun Q => P''.filter (fun p => p ∈ squareSet Δ Q)) := by
    intro Q1 hQ1 Q2 hQ2 hne
    exact h_disj Q1 Q2 hne
  have h_sum_card : ∑ Q ∈ Q_in, (P''.filter (fun p => p ∈ squareSet Δ Q)).card =
      (Q_in.biUnion (fun Q => P''.filter (fun p => p ∈ squareSet Δ Q))).card := by
    rw [Finset.card_biUnion h_disj']
  have h_points_in_ball : (P''.filter (fun p => dist c p ≤ r + Real.sqrt 2 * Δ / 2)).card ≥
      ∑ Q ∈ Q_in, (P''.filter (fun p => p ∈ squareSet Δ Q)).card := by
    rw [h_sum_card]
    apply Finset.card_le_card
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨Q, hQ, hpQ⟩
    have hpc : p ∈ squareSet Δ Q := (Finset.mem_filter.mp hpQ).2
    have hdist1 : dist p (squareCenter Δ Q) ≤ Real.sqrt 2 * Δ / 2 :=
      point_in_square_close_to_center hΔ_pos Q p hpc
    have hdist2 : dist (squareCenter Δ Q) c ≤ r := (Finset.mem_filter.mp hQ).2
    have hdist3 : dist c p ≤ r + Real.sqrt 2 * Δ / 2 := by
      have h : dist c p ≤ dist c (squareCenter Δ Q) + dist (squareCenter Δ Q) p := dist_triangle _ _ _
      have hdist1' : dist (squareCenter Δ Q) p ≤ Real.sqrt 2 * Δ / 2 := by
        rw [dist_comm]; exact hdist1
      have hdist2' : dist c (squareCenter Δ Q) ≤ r := by
        rw [dist_comm]; exact hdist2
      linarith
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpQ).1, hdist3⟩
  have h1' : ∀ Q ∈ Q_in, (m : ℝ) ≤ ((P''.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) := by
    intro Q hQ
    exact_mod_cast h1 Q hQ
  have h_sum_ineq : ∑ Q ∈ Q_in, (m : ℝ) ≤
      ∑ Q ∈ Q_in, ((P''.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) :=
    Finset.sum_le_sum h1'
  have h_sum_m : ∑ Q ∈ Q_in, (m : ℝ) = (Q_in.card : ℝ) * m := by
    simp [Finset.sum_const] <;> ring
  have h2 : (Q_in.card : ℝ) * m ≤
      ∑ Q ∈ Q_in, ((P''.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) := by
    rw [←h_sum_m]
    exact h_sum_ineq
  have hR : Δ ≤ r + Real.sqrt 2 * Δ / 2 := by
    have h3 : 0 < Real.sqrt 2 * Δ / 2 := by positivity
    linarith
  have h3 : ((P''.filter (fun p => dist c p ≤ r + Real.sqrt 2 * Δ / 2)).card : ℝ) ≤
      C * (r + Real.sqrt 2 * Δ / 2)^t * (P''.card : ℝ) :=
    hP''_ball c (r + Real.sqrt 2 * Δ / 2) hR
  have h_pos_a : 0 ≤ 1 + Real.sqrt 2 / 2 := by positivity
  have h_pos_r : 0 ≤ r := by linarith
  have h4 : r + Real.sqrt 2 * Δ / 2 ≤ (1 + Real.sqrt 2 / 2) * r := by
    have h5 : Real.sqrt 2 * Δ / 2 ≤ (Real.sqrt 2 / 2) * r := by
      have h6 : Δ ≤ r := hr
      have h7 : 0 ≤ Real.sqrt 2 / 2 := by positivity
      nlinarith
    linarith
  have h5 : C * (r + Real.sqrt 2 * Δ / 2)^t * (P''.card : ℝ) ≤
      C * ((1 + Real.sqrt 2 / 2) * r)^t * (P''.card : ℝ) := by
    gcongr <;> linarith
  have h6 : ((1 + Real.sqrt 2 / 2) * r)^t = (1 + Real.sqrt 2 / 2)^t * r^t := by
    rw [Real.mul_rpow h_pos_a h_pos_r] <;> ring
  have h_main : (Q_in.card : ℝ) * m ≤
      C * K * (1 + Real.sqrt 2 / 2)^t * r^t * (Qset.card : ℝ) * m := by
    have h_cast : (∑ Q ∈ Q_in, (P''.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) =
        ∑ Q ∈ Q_in, ((P''.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) := by
      rfl
    calc (Q_in.card : ℝ) * m
      ≤ ∑ Q ∈ Q_in, ((P''.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) := h2
    _ = (∑ Q ∈ Q_in, (P''.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) := h_cast.symm
    _ ≤ (P''.filter (fun p => dist c p ≤ r + Real.sqrt 2 * Δ / 2)).card := by exact_mod_cast h_points_in_ball
    _ ≤ C * (r + Real.sqrt 2 * Δ / 2)^t * (P''.card : ℝ) := h3
    _ ≤ C * ((1 + Real.sqrt 2 / 2) * r)^t * (P''.card : ℝ) := h5
    _ = C * (1 + Real.sqrt 2 / 2)^t * r^t * (P''.card : ℝ) := by rw [h6] <;> ring
    _ ≤ C * (1 + Real.sqrt 2 / 2)^t * r^t * (K * m * (Qset.card : ℝ)) := by gcongr <;> linarith
    _ = C * K * (1 + Real.sqrt 2 / 2)^t * r^t * (Qset.card : ℝ) * m := by ring
  have h7 : (Q_in.card : ℝ) * m ≤
      C * K * (1 + Real.sqrt 2 / 2)^t * r^t * (Qset.card : ℝ) * m := h_main
  have h8 : (Q_in.card : ℝ) ≤ C * K * (1 + Real.sqrt 2 / 2)^t * r^t * (Qset.card : ℝ) := by
    have h9 : 0 < m := hm_pos
    nlinarith
  exact h8

end Classical


end DirecretisedFurstenbergEstimate.Lagoon
