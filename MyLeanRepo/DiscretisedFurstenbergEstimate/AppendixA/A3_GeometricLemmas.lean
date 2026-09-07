module

/-
  Geometric lemmas for the genuine global 2s bound approach in A3.

  1. Separation: points from 2-separated coarse squares are Δ-separated.
  2. Common tube bound for arbitrary points p ∈ P_Q, q ∈ P_R.

  Whiteprint node: a3_geometric_lemmas
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TEnergyBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.CommonCoarseTubesBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA3

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MainAppendix
open DirecretisedFurstenbergEstimate.Lagoon (squareCenter point_in_square_close_to_center)
open DirecretisedFurstenbergEstimate.AppendixA.CommonCoarseTubesBound

abbrev Plane := EuclideanPlane
abbrev CoarseTube := AffineLine

/-- Coarse square region in the plane. -/
def squareSet (Δ : ℝ) (Q : CoarseSquare Δ) : Set Plane :=
  {p | p 0 ∈ Set.Ico (Δ * (Q.1 : ℝ)) (Δ * ((Q.1 : ℝ) + 1)) ∧
       p 1 ∈ Set.Ico (Δ * (Q.2 : ℝ)) (Δ * ((Q.2 : ℝ) + 1))}

/-- Helper: if x is in cthickening r s and dist x y ≤ d, then y is in cthickening (r + d) s. -/
lemma cthickening_triangle {X : Type*} [PseudoMetricSpace X] {s : Set X} {x y : X} {r d : ℝ}
    (hs_nonempty : s.Nonempty) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (hx : x ∈ Metric.cthickening r s) (hxy : dist x y ≤ d) :
    y ∈ Metric.cthickening (r + d) s := by
  have h_ne_top : Metric.infEDist x s ≠ ⊤ := Metric.infEDist_ne_top hs_nonempty
  have h1 : Metric.infDist x s ≤ r := by
    have h_edist : Metric.infEDist x s ≤ ENNReal.ofReal r := Metric.mem_cthickening_iff.mp hx
    have h_conv : Metric.infDist x s = ENNReal.toReal (Metric.infEDist x s) := by rfl
    rw [h_conv]
    have h_mono : ENNReal.toReal (Metric.infEDist x s) ≤ ENNReal.toReal (ENNReal.ofReal r) :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h_edist
    rw [ENNReal.toReal_ofReal hr] at h_mono
    exact h_mono
  have h2 : Metric.infDist y s ≤ Metric.infDist x s + dist y x :=
    Metric.infDist_le_infDist_add_dist
  have h_dist_comm : dist y x = dist x y := dist_comm y x
  rw [h_dist_comm] at h2
  have h3 : Metric.infDist y s ≤ r + d := by linarith
  have h_ne_top2 : Metric.infEDist y s ≠ ⊤ := Metric.infEDist_ne_top hs_nonempty
  have h4 : Metric.infEDist y s ≤ ENNReal.ofReal (r + d) := by
    have h_eq : Metric.infEDist y s = ENNReal.ofReal (Metric.infDist y s) := by
      simp [Metric.infDist, ENNReal.ofReal_toReal h_ne_top2]
    rw [h_eq]
    exact ENNReal.ofReal_le_ofReal h3
  exact Metric.mem_cthickening_iff.mpr h4

/-- If two coarse squares are at distance ≥ 2 in the max metric, then any points
    in those squares are at least Δ apart in the Euclidean metric. -/
lemma points_from_separated_squares_Δ_separated {Δ : ℝ} (hΔ_pos : 0 < Δ)
    {Q R : CoarseSquare Δ} (hQR : 2 ≤ dist Q R)
    {p q : Plane} (hp : p ∈ squareSet Δ Q) (hq : q ∈ squareSet Δ R) :
    Δ ≤ dist p q := by
  have h1 : (2 : ℝ) ≤ max |(Q.1 : ℝ) - (R.1 : ℝ)| |(Q.2 : ℝ) - (R.2 : ℝ)| := by
    simpa [Prod.dist_eq, Int.dist_eq] using hQR
  by_cases hcase : (2 : ℝ) ≤ |(Q.1 : ℝ) - (R.1 : ℝ)|
  · -- x-coordinates differ by at least 2
    have h2 : 2 ≤ |(Q.1 : ℝ) - (R.1 : ℝ)| := hcase
    by_cases h3 : (Q.1 : ℝ) ≤ (R.1 : ℝ)
    · have h4' : (Q.1 : ℝ) - (R.1 : ℝ) ≤ 0 := by linarith
      have h5' : |(Q.1 : ℝ) - (R.1 : ℝ)| = (R.1 : ℝ) - (Q.1 : ℝ) := by
        rw [abs_of_nonpos h4'] <;> ring
      have h6 : 2 ≤ (R.1 : ℝ) - (Q.1 : ℝ) := by
        rw [←h5']; exact h2
      have hpx2 : p 0 < Δ * ((Q.1 : ℝ) + 1) := (hp.1).2
      have hqx1 : Δ * (R.1 : ℝ) ≤ q 0 := (hq.1).1
      have h7 : q 0 - p 0 > Δ * ((R.1 : ℝ) - (Q.1 : ℝ) - 1) := by linarith
      have h8 : Δ * ((R.1 : ℝ) - (Q.1 : ℝ) - 1) ≥ Δ := by
        have h9 : (R.1 : ℝ) - (Q.1 : ℝ) - 1 ≥ 1 := by linarith
        have h10 : 0 ≤ Δ := by linarith
        nlinarith
      have h11 : Δ < q 0 - p 0 := by linarith
      have h12 : Δ ≤ |q 0 - p 0| := by
        have h13 : 0 < q 0 - p 0 := by linarith
        rw [abs_of_pos h13] <;> linarith
      have h14 : |q 0 - p 0| ≤ dist p q := by
        have h15 : |(q - p) 0| ≤ ‖q - p‖ := by exact TubesAndSlopes.coord_abs_le_norm (q - p) 0
        have h16 : ‖q - p‖ = ‖p - q‖ := by rw [norm_sub_rev]
        rw [h16] at h15
        simpa [dist_eq_norm] using h15
      linarith
    · have h4' : (R.1 : ℝ) < (Q.1 : ℝ) := by linarith
      have h5' : (Q.1 : ℝ) - (R.1 : ℝ) > 0 := by linarith
      have h6' : |(Q.1 : ℝ) - (R.1 : ℝ)| = (Q.1 : ℝ) - (R.1 : ℝ) := by
        rw [abs_of_pos h5']
      have h7 : 2 ≤ (Q.1 : ℝ) - (R.1 : ℝ) := by
        rw [←h6']; exact h2
      have hqx2 : q 0 < Δ * ((R.1 : ℝ) + 1) := (hq.1).2
      have hpx1 : Δ * (Q.1 : ℝ) ≤ p 0 := (hp.1).1
      have h8 : p 0 - q 0 > Δ * ((Q.1 : ℝ) - (R.1 : ℝ) - 1) := by linarith
      have h9 : Δ * ((Q.1 : ℝ) - (R.1 : ℝ) - 1) ≥ Δ := by
        have h10 : (Q.1 : ℝ) - (R.1 : ℝ) - 1 ≥ 1 := by linarith
        have h11 : 0 ≤ Δ := by linarith
        nlinarith
      have h12 : Δ < p 0 - q 0 := by linarith
      have h13 : Δ ≤ |p 0 - q 0| := by
        have h14 : 0 < p 0 - q 0 := by linarith
        rw [abs_of_pos h14] <;> linarith
      have h15 : |p 0 - q 0| ≤ dist p q := by
        have h16 : |(p - q) 0| ≤ ‖p - q‖ := by exact TubesAndSlopes.coord_abs_le_norm (p - q) 0
        simpa [dist_eq_norm] using h16
      linarith
  · -- y-coordinates must differ by at least 2
    have h2 : ¬(2 ≤ |(Q.1 : ℝ) - (R.1 : ℝ)|) := hcase
    have h3 : (2 : ℝ) ≤ |(Q.2 : ℝ) - (R.2 : ℝ)| := by
      by_contra h4
      have h5 : |(Q.1 : ℝ) - (R.1 : ℝ)| < 2 := by linarith
      have h6 : |(Q.2 : ℝ) - (R.2 : ℝ)| < 2 := by linarith
      have h7 : max |(Q.1 : ℝ) - (R.1 : ℝ)| |(Q.2 : ℝ) - (R.2 : ℝ)| < 2 :=
        max_lt h5 h6
      linarith
    by_cases h4 : (Q.2 : ℝ) ≤ (R.2 : ℝ)
    · have h5' : (Q.2 : ℝ) - (R.2 : ℝ) ≤ 0 := by linarith
      have h6' : |(Q.2 : ℝ) - (R.2 : ℝ)| = (R.2 : ℝ) - (Q.2 : ℝ) := by
        rw [abs_of_nonpos h5'] <;> ring
      have h7 : 2 ≤ (R.2 : ℝ) - (Q.2 : ℝ) := by
        rw [←h6']; exact h3
      have hpy2 : p 1 < Δ * ((Q.2 : ℝ) + 1) := (hp.2).2
      have hqy1 : Δ * (R.2 : ℝ) ≤ q 1 := (hq.2).1
      have h8 : q 1 - p 1 > Δ * ((R.2 : ℝ) - (Q.2 : ℝ) - 1) := by linarith
      have h9 : Δ * ((R.2 : ℝ) - (Q.2 : ℝ) - 1) ≥ Δ := by
        have h10 : (R.2 : ℝ) - (Q.2 : ℝ) - 1 ≥ 1 := by linarith
        have h11 : 0 ≤ Δ := by linarith
        nlinarith
      have h12 : Δ < q 1 - p 1 := by linarith
      have h13 : Δ ≤ |q 1 - p 1| := by
        have h14 : 0 < q 1 - p 1 := by linarith
        rw [abs_of_pos h14] <;> linarith
      have h15 : |q 1 - p 1| ≤ dist p q := by
        have h16 : |(q - p) 1| ≤ ‖q - p‖ := by exact TubesAndSlopes.coord_abs_le_norm (q - p) 1
        have h17 : ‖q - p‖ = ‖p - q‖ := by rw [norm_sub_rev]
        rw [h17] at h16
        simpa [dist_eq_norm] using h16
      linarith
    · have h5' : (R.2 : ℝ) < (Q.2 : ℝ) := by linarith
      have h6' : (Q.2 : ℝ) - (R.2 : ℝ) > 0 := by linarith
      have h7' : |(Q.2 : ℝ) - (R.2 : ℝ)| = (Q.2 : ℝ) - (R.2 : ℝ) := by
        rw [abs_of_pos h6']
      have h8 : 2 ≤ (Q.2 : ℝ) - (R.2 : ℝ) := by
        rw [←h7']; exact h3
      have hqy2 : q 1 < Δ * ((R.2 : ℝ) + 1) := (hq.2).2
      have hpy1 : Δ * (Q.2 : ℝ) ≤ p 1 := (hp.2).1
      have h9 : p 1 - q 1 > Δ * ((Q.2 : ℝ) - (R.2 : ℝ) - 1) := by linarith
      have h10 : Δ * ((Q.2 : ℝ) - (R.2 : ℝ) - 1) ≥ Δ := by
        have h11 : (Q.2 : ℝ) - (R.2 : ℝ) - 1 ≥ 1 := by linarith
        have h12 : 0 ≤ Δ := by linarith
        nlinarith
      have h13 : Δ < p 1 - q 1 := by linarith
      have h14 : Δ ≤ |p 1 - q 1| := by
        have h15 : 0 < p 1 - q 1 := by linarith
        rw [abs_of_pos h15] <;> linarith
      have h16 : |p 1 - q 1| ≤ dist p q := by
        have h17 : |(p - q) 1| ≤ ‖p - q‖ := by exact TubesAndSlopes.coord_abs_le_norm (p - q) 1
        simpa [dist_eq_norm] using h17
      linarith

/-- Common tube bound for arbitrary points p and q in coarse squares.

    If C_Q is a family of tubes near the center of square Q (within kΔ),
    and p is any point in square Q, then all tubes in C_Q are near p
    (within (k+1)Δ). Similarly for q in square R.

    Applying the geometric common tube bound with points p, q directly gives:
    |C_Q ∩ C_R| ≤ packing_constant * C_T * (800*(k+1))^s * M * (Δ / dist(p,q))^s
-/
lemma arbitrary_point_common_tubes_bound
    {Δ s C_T M k : ℝ} (hk : 1 ≤ k)
    (hΔ_pos : 0 < Δ) (hs_pos : 0 < s)
    (hC_T_pos : 0 < C_T) (hM_pos : 0 < M)
    {Q R : CoarseSquare Δ}
    {C_Q C_R : Finset CoarseTube}
    (hC_Q_sset : IsDeltaSSet Δ s C_T (C_Q : Set CoarseTube))
    (hC_Q_sep : SeparatedAt Δ (C_Q : Set CoarseTube))
    (hC_Q_card : (C_Q.card : ℝ) ≤ M)
    (hC_Q_near_center : ∀ ℓ ∈ C_Q,
      squareCenter Δ Q ∈ Metric.cthickening (k * Δ) (ℓ.1 : Set Plane))
    (hC_R_near_center : ∀ ℓ ∈ C_R,
      squareCenter Δ R ∈ Metric.cthickening (k * Δ) (ℓ.1 : Set Plane))
    {p q : Plane}
    (hp_in_square : p ∈ squareSet Δ Q)
    (hq_in_square : q ∈ squareSet Δ R)
    (hp_bound : ‖p‖ ≤ 2) (hq_bound : ‖q‖ ≤ 2)
    (h_dist_pos : 0 < dist p q)
    (h_dist_le_3 : dist p q ≤ 3) :
    ((C_Q) ∩ (C_R)).card ≤
      (affineLine_packing_constant : ℝ) * C_T * ((800 * (k + 1)) : ℝ)^s * M *
        (Δ / dist p q)^s := by
  let k' := k + 1
  have hk'_one : 1 ≤ k' := by linarith
  have h_kΔ_nonneg : 0 ≤ k * Δ := by positivity
  have h_Δ_nonneg : 0 ≤ Δ := by linarith

  -- dist(p, center Q) ≤ Δ
  have h_dist_p_center : dist p (squareCenter Δ Q) ≤ Δ := by
    have h1 : dist p (squareCenter Δ Q) ≤ Real.sqrt 2 * Δ / 2 :=
      point_in_square_close_to_center hΔ_pos Q p hp_in_square
    have h2 : Real.sqrt 2 * Δ / 2 ≤ Δ := by
      have h3 : Real.sqrt 2 ≤ 2 := by
        have h4 : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
        have h5 : Real.sqrt 4 = 2 := by rw [Real.sqrt_eq_cases] <;> norm_num
        linarith
      nlinarith
    linarith

  -- dist(q, center R) ≤ Δ
  have h_dist_q_center : dist q (squareCenter Δ R) ≤ Δ := by
    have h1 : dist q (squareCenter Δ R) ≤ Real.sqrt 2 * Δ / 2 :=
      point_in_square_close_to_center hΔ_pos R q hq_in_square
    have h2 : Real.sqrt 2 * Δ / 2 ≤ Δ := by
      have h3 : Real.sqrt 2 ≤ 2 := by
        have h4 : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
        have h5 : Real.sqrt 4 = 2 := by rw [Real.sqrt_eq_cases] <;> norm_num
        linarith
      nlinarith
    linarith

  -- Every tube in C_Q is near p
  have hC_Q_near_p : ∀ ℓ ∈ C_Q, p ∈ Metric.cthickening (k' * Δ) (ℓ.1 : Set Plane) := by
    intro ℓ hℓ
    have h1 : squareCenter Δ Q ∈ Metric.cthickening (k * Δ) (ℓ.1 : Set Plane) :=
      hC_Q_near_center ℓ hℓ
    have h_line_nonempty : (ℓ.1 : Set Plane).Nonempty := AffineLine.nonempty ℓ
    have h_k'Δ_eq : k' * Δ = k * Δ + Δ := by
      simp [k'] <;> ring
    rw [h_k'Δ_eq]
    have h_dist_comm : dist (squareCenter Δ Q) p ≤ Δ := by
      rw [dist_comm] <;> exact h_dist_p_center
    exact cthickening_triangle h_line_nonempty h_kΔ_nonneg h_Δ_nonneg h1 h_dist_comm

  -- Every tube in C_R is near q
  have hC_R_near_q : ∀ ℓ ∈ C_R, q ∈ Metric.cthickening (k' * Δ) (ℓ.1 : Set Plane) := by
    intro ℓ hℓ
    have h1 : squareCenter Δ R ∈ Metric.cthickening (k * Δ) (ℓ.1 : Set Plane) :=
      hC_R_near_center ℓ hℓ
    have h_line_nonempty : (ℓ.1 : Set Plane).Nonempty := AffineLine.nonempty ℓ
    have h_k'Δ_eq : k' * Δ = k * Δ + Δ := by
      simp [k'] <;> ring
    rw [h_k'Δ_eq]
    have h_dist_comm : dist (squareCenter Δ R) q ≤ Δ := by
      rw [dist_comm] <;> exact h_dist_q_center
    exact cthickening_triangle h_line_nonempty h_kΔ_nonneg h_Δ_nonneg h1 h_dist_comm

  -- Intersection C_Q ∩ C_R is subset of C_Q filtered by tubes near both p and q
  let F := C_Q.filter (fun ℓ : CoarseTube =>
    p ∈ Metric.cthickening (k' * Δ) (ℓ.1 : Set Plane) ∧
    q ∈ Metric.cthickening (k' * Δ) (ℓ.1 : Set Plane))
  have h_subset : (C_Q ∩ C_R) ⊆ F := by
    intro ℓ hℓ
    have hℓQ : ℓ ∈ C_Q := (Finset.mem_inter.mp hℓ).1
    have hℓR : ℓ ∈ C_R := (Finset.mem_inter.mp hℓ).2
    have h_near_p : p ∈ Metric.cthickening (k' * Δ) (ℓ.1 : Set Plane) :=
      hC_Q_near_p ℓ hℓQ
    have h_near_q : q ∈ Metric.cthickening (k' * Δ) (ℓ.1 : Set Plane) :=
      hC_R_near_q ℓ hℓR
    exact Finset.mem_filter.mpr ⟨hℓQ, ⟨h_near_p, h_near_q⟩⟩

  have h_card_le : ((C_Q ∩ C_R).card : ℝ) ≤ (F.card : ℝ) := by
    exact_mod_cast Finset.card_le_card h_subset

  -- Apply the geometric common tube bound
  have h_bound : (F.card : ℝ) ≤
      (affineLine_packing_constant : ℝ) * C_T * ((800 * k') : ℝ)^s *
        (Δ / dist p q)^s * (C_Q.card : ℝ) :=
    common_coarse_tubes_bound_kΔ hk'_one hΔ_pos hs_pos hC_T_pos
      hC_Q_sset hC_Q_sep p q h_dist_pos h_dist_le_3 hp_bound hq_bound

  have h_card_M : (C_Q.card : ℝ) ≤ M := hC_Q_card
  have h_nonneg1 : 0 ≤ (affineLine_packing_constant : ℝ) * C_T * ((800 * k') : ℝ)^s *
      (Δ / dist p q)^s := by positivity

  calc ((C_Q ∩ C_R).card : ℝ)
    ≤ (F.card : ℝ) := h_card_le
  _ ≤ (affineLine_packing_constant : ℝ) * C_T * ((800 * k') : ℝ)^s *
        (Δ / dist p q)^s * (C_Q.card : ℝ) := h_bound
  _ ≤ (affineLine_packing_constant : ℝ) * C_T * ((800 * k') : ℝ)^s *
        (Δ / dist p q)^s * M := by
    exact mul_le_mul_of_nonneg_left h_card_M h_nonneg1
  _ = (affineLine_packing_constant : ℝ) * C_T * ((800 * (k + 1)) : ℝ)^s *
        M * (Δ / dist p q)^s := by
    have h_eq : k' = k + 1 := by simp [k']
    have h9 : (800 * k' : ℝ)^s = (800 * (k + 1) : ℝ)^s := by rw [h_eq]
    rw [h9]
    have h10 : (affineLine_packing_constant : ℝ) * C_T * ((800 * (k + 1)) : ℝ)^s *
        (Δ / dist p q)^s * M =
        (affineLine_packing_constant : ℝ) * C_T * ((800 * (k + 1)) : ℝ)^s *
        M * (Δ / dist p q)^s := by
      ring
    exact h10

end DirecretisedFurstenbergEstimate.AppendixA3
