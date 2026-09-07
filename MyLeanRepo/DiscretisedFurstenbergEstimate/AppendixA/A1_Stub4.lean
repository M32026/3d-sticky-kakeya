module

/-
  A1 Stub 4: Convert center ball-growth to IsDeltaSSet on CoarseSquare.

  Corrected signature: adds hQset_nonempty and geometric absorption hypotheses.

  Proof route:
  - CoarseSquare = ℤ×ℤ with max metric; distinct points have dist ≥ 1
  - Since 2Δ < 1, Δ-covering number of any finite subset equals its cardinality
  - For r ≥ 1/2: convert CoarseSquare ball to plane ball (center dist ≤ √2·Δ·2r),
    apply h_ball_growth, absorb geometric constant into 20ε budget
  - For Δ ≤ r < 1/2: ball contains ≤ 1 point; use h_ball_growth at r=Δ to get
    lower bound on |Qset|, then show 1 ≤ C·r^t·|Qset| via small-radius absorption
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.HeavySquareRefinement
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Cobalt

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Lagoon (squareSet squareCenter squareCenter_zero squareCenter_one)

local notation "Plane" => EuclideanPlane

abbrev CoarseSquare (Δ : ℝ) := ℤ × ℤ

attribute [local instance] Classical.propDecidable

/-- Distinct elements of ℤ×ℤ have max-metric distance at least 1. -/
lemma coarseSquare_dist_one_le {Q1 Q2 : ℤ × ℤ} (hne : Q1 ≠ Q2) :
    (1 : ℝ) ≤ dist Q1 Q2 := by
  have h : Q1.1 ≠ Q2.1 ∨ Q1.2 ≠ Q2.2 := by
    by_contra h'; push Not at h'; exact hne (Prod.ext h'.1 h'.2)
  rcases h with (h | h)
  · have h3 : (1 : ℝ) ≤ dist Q1.1 Q2.1 := by
      rw [Int.dist_eq']
      have h4 : Q1.1 - Q2.1 ≠ 0 := by omega
      have h5 : (1 : ℤ) ≤ |Q1.1 - Q2.1| := by
        by_contra h6
        have h7 : |Q1.1 - Q2.1| < 1 := by linarith
        have h8 : |Q1.1 - Q2.1| ≤ 0 := by linarith
        have h9 : 0 ≤ |Q1.1 - Q2.1| := abs_nonneg _
        have h10 : |Q1.1 - Q2.1| = 0 := by linarith
        have h11 : Q1.1 - Q2.1 = 0 := by simpa [abs_eq_zero] using h10
        exact h4 h11
      exact_mod_cast h5
    have h4 : dist Q1.1 Q2.1 ≤ dist Q1 Q2 := by
      rw [Prod.dist_eq] <;> exact le_max_left _ _
    linarith
  · have h3 : (1 : ℝ) ≤ dist Q1.2 Q2.2 := by
      rw [Int.dist_eq']
      have h4 : Q1.2 - Q2.2 ≠ 0 := by omega
      have h5 : (1 : ℤ) ≤ |Q1.2 - Q2.2| := by
        by_contra h6
        have h7 : |Q1.2 - Q2.2| < 1 := by linarith
        have h8 : |Q1.2 - Q2.2| ≤ 0 := by linarith
        have h9 : 0 ≤ |Q1.2 - Q2.2| := abs_nonneg _
        have h10 : |Q1.2 - Q2.2| = 0 := by linarith
        have h11 : Q1.2 - Q2.2 = 0 := by simpa [abs_eq_zero] using h10
        exact h4 h11
      exact_mod_cast h5
    have h4 : dist Q1.2 Q2.2 ≤ dist Q1 Q2 := by
      rw [Prod.dist_eq] <;> exact le_max_right _ _
    linarith

/-- For a finite subset S of ℤ×ℤ with 2Δ < 1, the Δ-covering number
    (as ENNReal) equals the cardinality. -/
lemma ncover_eq_card {Δ : ℝ} (hΔ_pos : 0 < Δ) (h2Δ_lt_one : 2 * Δ < 1)
    (S : Finset (ℤ × ℤ)) :
    (Metric.externalCoveringNumber Δ.toNNReal (S : Set (ℤ × ℤ)) : ENNReal) = (S.card : ENNReal) := by
  let εnn : NNReal := Δ.toNNReal
  have hεnn_coe : (εnn : ℝ) = Δ := by
    simp [εnn, Real.toNNReal_of_nonneg hΔ_pos.le]
  have h2εnn_lt_one : (2 * εnn : ℝ) < 1 := by
    simp [hεnn_coe] <;> linarith
  -- Upper bound
  have h_upper : Metric.externalCoveringNumber εnn (S : Set (ℤ × ℤ)) ≤ ↑S.card := by
    have h : Metric.externalCoveringNumber εnn (S : Set (ℤ × ℤ)) ≤ (S : Set (ℤ × ℤ)).encard :=
      Metric.externalCoveringNumber_le_encard_self _
    have h2 : (S : Set (ℤ × ℤ)).encard = ↑S.card := by simp
    rw [h2] at h
    exact h
  -- Lower bound via packing number
  have h_lower1 : Metric.packingNumber (2 * εnn) (S : Set (ℤ × ℤ)) ≤
      Metric.externalCoveringNumber εnn (S : Set (ℤ × ℤ)) :=
    Metric.packingNumber_two_mul_le_externalCoveringNumber εnn (S : Set (ℤ × ℤ))
  have h_sep : Metric.IsSeparated (2 * εnn) (S : Set (ℤ × ℤ)) := by
    intro x hx y hy hne
    have h1 : (1 : ℝ) ≤ dist x y := coarseSquare_dist_one_le hne
    have h2 : (2 * εnn : ℝ) < 1 := h2εnn_lt_one
    have h4 : (2 * εnn : ℝ) < dist x y := by linarith
    have h5 : (2 * εnn : ENNReal) < edist x y := by
      rw [edist_dist]
      have h6 : (2 * εnn : ENNReal) = ENNReal.ofReal (2 * εnn : ℝ) := by simp
      rw [h6]
      have h7 : 0 ≤ (2 * εnn : ℝ) := by positivity
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg h7]
      exact h4
    exact h5
  have h_pack_ge : (↑S.card : ENat) ≤ Metric.packingNumber (2 * εnn) (S : Set (ℤ × ℤ)) := by
    have h4 : (S : Set (ℤ × ℤ)).encard ≤ Metric.packingNumber (2 * εnn) (S : Set (ℤ × ℤ)) :=
      h_sep.encard_le_packingNumber (show (S : Set (ℤ × ℤ)) ⊆ (S : Set (ℤ × ℤ)) from fun x hx => hx)
    have h5 : (S : Set (ℤ × ℤ)).encard = ↑S.card := by simp
    simpa [h5] using h4
  have h_main : Metric.externalCoveringNumber εnn (S : Set (ℤ × ℤ)) = ↑S.card :=
    le_antisymm h_upper (le_trans h_pack_ge h_lower1)
  exact_mod_cast h_main

/-- Distance between square centers is bounded by √2·Δ·(max coordinate difference). -/
lemma squareCenter_dist_le {Δ : ℝ} (hΔ_pos : 0 < Δ) {Q' q : ℤ × ℤ} {r : ℝ}
    (h : dist Q' q ≤ r) :
    dist (squareCenter Δ Q') (squareCenter Δ q) ≤ Real.sqrt 2 * Δ * r := by
  have h1 : dist Q' q = max (dist Q'.1 q.1) (dist Q'.2 q.2) := Prod.dist_eq
  rw [h1] at h
  have h2 : dist Q'.1 q.1 ≤ r := le_trans (le_max_left _ _) h
  have h3 : dist Q'.2 q.2 ≤ r := le_trans (le_max_right _ _) h
  have h2' : |(Q'.1 : ℝ) - (q.1 : ℝ)| ≤ r := by
    have hdi : dist Q'.1 q.1 = ↑|Q'.1 - q.1| := Int.dist_eq' Q'.1 q.1
    rw [hdi] at h2
    exact_mod_cast h2
  have h3' : |(Q'.2 : ℝ) - (q.2 : ℝ)| ≤ r := by
    have hdi : dist Q'.2 q.2 = ↑|Q'.2 - q.2| := Int.dist_eq' Q'.2 q.2
    rw [hdi] at h3
    exact_mod_cast h3
  have h4 : |squareCenter Δ Q' 0 - squareCenter Δ q 0| ≤ Δ * r := by
    have hcx : squareCenter Δ Q' 0 = Δ * ((Q'.1 : ℝ) + 1 / 2) := squareCenter_zero Δ Q'
    have hcy : squareCenter Δ q 0 = Δ * ((q.1 : ℝ) + 1 / 2) := squareCenter_zero Δ q
    rw [hcx, hcy]
    have h_eq : Δ * ((Q'.1 : ℝ) + 1 / 2) - Δ * ((q.1 : ℝ) + 1 / 2) = Δ * ((Q'.1 : ℝ) - (q.1 : ℝ)) := by ring
    rw [h_eq, abs_mul, abs_of_nonneg (show 0 ≤ Δ by linarith)]
    exact mul_le_mul_of_nonneg_left h2' (by linarith)
  have h5 : |squareCenter Δ Q' 1 - squareCenter Δ q 1| ≤ Δ * r := by
    have hcx : squareCenter Δ Q' 1 = Δ * ((Q'.2 : ℝ) + 1 / 2) := squareCenter_one Δ Q'
    have hcy : squareCenter Δ q 1 = Δ * ((q.2 : ℝ) + 1 / 2) := squareCenter_one Δ q
    rw [hcx, hcy]
    have h_eq : Δ * ((Q'.2 : ℝ) + 1 / 2) - Δ * ((q.2 : ℝ) + 1 / 2) = Δ * ((Q'.2 : ℝ) - (q.2 : ℝ)) := by ring
    rw [h_eq, abs_mul, abs_of_nonneg (show 0 ≤ Δ by linarith)]
    exact mul_le_mul_of_nonneg_left h3' (by linarith)
  have h6 : dist (squareCenter Δ Q') (squareCenter Δ q) ^ 2 ≤ 2 * (Δ * r)^2 := by
    have h_norm2 : dist (squareCenter Δ Q') (squareCenter Δ q) ^ 2 =
        (squareCenter Δ Q' 0 - squareCenter Δ q 0)^2 + (squareCenter Δ Q' 1 - squareCenter Δ q 1)^2 := by
      rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> simp
    rw [h_norm2]
    have h7 : (squareCenter Δ Q' 0 - squareCenter Δ q 0)^2 ≤ (Δ * r)^2 := by
      nlinarith [abs_le.mp h4]
    have h8 : (squareCenter Δ Q' 1 - squareCenter Δ q 1)^2 ≤ (Δ * r)^2 := by
      nlinarith [abs_le.mp h5]
    linarith
  have h9 : 0 ≤ dist (squareCenter Δ Q') (squareCenter Δ q) := by positivity
  have h10 : (Real.sqrt 2 * Δ * r)^2 = 2 * (Δ * r)^2 := by
    have h11 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    have h : (Real.sqrt 2 * Δ * r)^2 = (Real.sqrt 2)^2 * (Δ * r)^2 := by ring
    rw [h, h11] <;> ring
  have hr_nonneg : 0 ≤ r := by
    have h_dpos : 0 ≤ dist Q' q := dist_nonneg
    linarith
  have h_pos : 0 ≤ Real.sqrt 2 * Δ * r := by positivity
  have h12 : dist (squareCenter Δ Q') (squareCenter Δ q)^2 ≤ (Real.sqrt 2 * Δ * r)^2 := by
    rw [h10] <;> exact h6
  by_contra h13
  have h14 : Real.sqrt 2 * Δ * r < dist (squareCenter Δ Q') (squareCenter Δ q) := by linarith
  have h15 : (Real.sqrt 2 * Δ * r)^2 < dist (squareCenter Δ Q') (squareCenter Δ q)^2 := by
    nlinarith [h_pos, h9]
  linarith

/-- Corrected Stub 4: Convert center ball-growth to IsDeltaSSet on CoarseSquare. -/
lemma a1_ball_growth_to_sset
    {Δ t ε K : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (ht : 0 < t) (hε_pos : 0 < ε)
    (Qset : Finset (ℤ × ℤ))
    (hQset_nonempty : Qset.Nonempty)
    (hK_absorb : K ≤ Real.rpow Δ (-ε))
    (h_ball_growth : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card : ℝ) ≤
        Real.rpow Δ (-ε) * K * (1 + Real.sqrt 2 / 2)^t * r^t * (Qset.card : ℝ))
    (h_geom_absorb :
      (1 + Real.sqrt 2 / 2)^t * (2 * Real.sqrt 2)^t * Real.rpow Δ (t - 2 * ε) ≤ Real.rpow Δ (-20 * ε))
    (h_small_absorb :
      (1 + Real.sqrt 2 / 2)^t ≤ Real.rpow Δ (-18 * ε)) :
    IsDeltaSSet Δ t (Real.rpow Δ (-20 * ε)) (Qset : Set (CoarseSquare Δ)) := by
  let C_target : ℝ := Real.rpow Δ (-20 * ε)
  have hC_pos : 0 < C_target := Real.rpow_pos_of_pos hΔ_pos _
  have hQcard_pos : 0 < (Qset.card : ℝ) := by
    have h : 0 < Qset.card := Finset.card_pos.mpr hQset_nonempty
    exact_mod_cast h
  have h2Δ_lt_one : 2 * Δ < 1 := by linarith

  -- Helper: rpow multiplication
  have h_rpow_mul : ∀ (a b : ℝ), Real.rpow Δ a * Real.rpow Δ b = Real.rpow Δ (a + b) := by
    intro a b
    exact (Real.rpow_add hΔ_pos a b).symm
  have h_rpow_neg2e : Real.rpow Δ (-ε) * Real.rpow Δ (-ε) = Real.rpow Δ (-2 * ε) := by
    have h := h_rpow_mul (-ε) (-ε)
    have h2 : (-ε) + (-ε) = -2 * ε := by ring
    rw [h2] at h
    exact h
  have h_rpow_t_minus_2e : Real.rpow Δ (-2 * ε) * Real.rpow Δ t = Real.rpow Δ (t - 2 * ε) := by
    have h := h_rpow_mul (-2 * ε) t
    have h2 : (-2 * ε) + t = t - 2 * ε := by ring
    rw [h2] at h
    exact h

  -- Lower bound on |Qset| from ball-growth at r=Δ
  have hQset_lower : (Qset.card : ℝ) ≥ Real.rpow Δ (2 * ε - t) / (1 + Real.sqrt 2 / 2)^t := by
    rcases hQset_nonempty with ⟨Q, hQ⟩
    let c := squareCenter Δ Q
    have h1 : Q ∈ Qset.filter (fun Q' => dist (squareCenter Δ Q') c ≤ Δ) := by
      simp only [Finset.mem_filter, c, dist_self]
      exact ⟨hQ, by linarith [hΔ_pos]⟩
    have h2 : 0 < (Qset.filter (fun Q' => dist (squareCenter Δ Q') c ≤ Δ)).card :=
      Finset.card_pos.mpr ⟨Q, h1⟩
    have h3 := h_ball_growth c Δ (by linarith)
    have h4 : (1 : ℝ) ≤ ((Qset.filter (fun Q' => dist (squareCenter Δ Q') c ≤ Δ)).card : ℝ) := by exact_mod_cast h2
    have h5 : (1 : ℝ) ≤ Real.rpow Δ (-ε) * K * (1 + Real.sqrt 2 / 2)^t * Real.rpow Δ t * (Qset.card : ℝ) := le_trans h4 h3
    have h6 : Real.rpow Δ (-ε) * K ≤ Real.rpow Δ (-2 * ε) := by
      have hK2 : K ≤ Real.rpow Δ (-ε) := hK_absorb
      have hpos : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos _
      calc
        Real.rpow Δ (-ε) * K ≤ Real.rpow Δ (-ε) * Real.rpow Δ (-ε) := by gcongr
        _ = Real.rpow Δ (-2 * ε) := h_rpow_neg2e
    have hposC : 0 < (1 + Real.sqrt 2 / 2)^t := by positivity
    have hposD : 0 < Real.rpow Δ t := Real.rpow_pos_of_pos hΔ_pos _
    have h7 : Real.rpow Δ (-ε) * K * ((1 + Real.sqrt 2 / 2)^t * Real.rpow Δ t * (Qset.card : ℝ)) ≤
        Real.rpow Δ (-2 * ε) * ((1 + Real.sqrt 2 / 2)^t * Real.rpow Δ t * (Qset.card : ℝ)) :=
      mul_le_mul_of_nonneg_right h6 (by positivity)
    have h5' : (1 : ℝ) ≤ Real.rpow Δ (-ε) * K * ((1 + Real.sqrt 2 / 2)^t * Real.rpow Δ t * (Qset.card : ℝ)) := by
      simpa [mul_assoc] using h5
    have h7' : (1 : ℝ) ≤ Real.rpow Δ (-2 * ε) * ((1 + Real.sqrt 2 / 2)^t * Real.rpow Δ t * (Qset.card : ℝ)) :=
      le_trans h5' h7
    have h8 : Real.rpow Δ (-2 * ε) * ((1 + Real.sqrt 2 / 2)^t * Real.rpow Δ t * (Qset.card : ℝ)) =
        (1 + Real.sqrt 2 / 2)^t * (Real.rpow Δ (-2 * ε) * Real.rpow Δ t) * (Qset.card : ℝ) := by ring
    rw [h8] at h7'
    rw [h_rpow_t_minus_2e] at h7'
    have h_pos1 : 0 < (1 + Real.sqrt 2 / 2)^t := by positivity
    have h_pos2 : 0 < Real.rpow Δ (t - 2 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    set A : ℝ := (1 + Real.sqrt 2 / 2)^t with hA_def
    set B : ℝ := Real.rpow Δ (t - 2 * ε) with hB_def
    have h_pos3 : 0 < A * B := mul_pos h_pos1 h_pos2
    have h9 : A * B * (Qset.card : ℝ) ≥ 1 := h7'
    have h10 : B * Real.rpow Δ (2 * ε - t) = 1 := by
      rw [hB_def]
      have h11 := h_rpow_mul (t - 2 * ε) (2 * ε - t)
      have h12 : (t - 2 * ε) + (2 * ε - t) = 0 := by ring
      rw [h12] at h11
      simpa using h11
    have h13 : (Qset.card : ℝ) ≥ 1 / (A * B) := by
      have h14 : (A * B)⁻¹ * (A * B * (Qset.card : ℝ)) ≥ (A * B)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h9 (by positivity)
      have h15 : (A * B)⁻¹ * (A * B * (Qset.card : ℝ)) = (Qset.card : ℝ) := by
        rw [inv_mul_cancel_left₀ h_pos3.ne'] <;> ring
      have h16 : (A * B)⁻¹ * 1 = 1 / (A * B) := by ring
      rw [h15, h16] at h14
      exact h14
    have h15 : 1 / (A * B) = Real.rpow Δ (2 * ε - t) / A := by
      have h16 : 1 / (A * B) = (1 / A) * (1 / B) := by
        field_simp [h_pos3.ne'] <;> ring
      rw [h16]
      have h17 : 1 / B = Real.rpow Δ (2 * ε - t) := by
        have h18 : B * Real.rpow Δ (2 * ε - t) = 1 := h10
        field_simp [h_pos2.ne'] <;> linarith
      rw [h17] <;> ring
    rw [h15] at h13
    exact h13

  refine' ⟨hQset_nonempty, hΔ_pos, hC_pos, by linarith, _⟩
  intro x r hr
  have hr_pos : 0 < r := by linarith
  let S_r : Finset (ℤ × ℤ) := Qset.filter (fun Q => dist Q x ≤ r)

  by_cases hS_empty : S_r.Nonempty
  · rcases hS_empty with ⟨q, hq⟩
    have hq_in : q ∈ Qset := (Finset.mem_filter.mp hq).1
    have hq_dist : dist q x ≤ r := (Finset.mem_filter.mp hq).2
    have h_sub : S_r ⊆ Qset.filter (fun Q' => dist Q' q ≤ 2 * r) := by
      intro Q' hQ'
      have h1 : Q' ∈ Qset := (Finset.mem_filter.mp hQ').1
      have h2 : dist Q' x ≤ r := (Finset.mem_filter.mp hQ').2
      have h3 : dist Q' q ≤ dist Q' x + dist x q := dist_triangle _ _ _
      have h4 : dist x q ≤ r := by simpa [dist_comm] using hq_dist
      have h5 : dist Q' q ≤ 2 * r := by linarith
      exact Finset.mem_filter.mpr ⟨h1, h5⟩
    have h_card_le : S_r.card ≤ (Qset.filter (fun Q' => dist Q' q ≤ 2 * r)).card :=
      Finset.card_le_card h_sub

    by_cases h_small : 2 * r < 1
    · -- Small radius: ball contains at most 1 point (since dist ≥ 1 for distinct)
      have h_at_most_one : ∀ (Q' : ℤ × ℤ), Q' ∈ Qset.filter (fun Q'' => dist Q'' q ≤ 2 * r) → Q' = q := by
        intro Q' hQ'
        have hdist : dist Q' q ≤ 2 * r := (Finset.mem_filter.mp hQ').2
        have hlt : dist Q' q < 1 := by linarith
        by_cases h : Q' = q
        · exact h
        · have h' : (1 : ℝ) ≤ dist Q' q := coarseSquare_dist_one_le h
          linarith
      have h_one : (Qset.filter (fun Q' => dist Q' q ≤ 2 * r)).card ≤ 1 := by
        by_contra h2
        have h3 : 2 ≤ (Qset.filter (fun Q' => dist Q' q ≤ 2 * r)).card := by omega
        rcases Finset.one_lt_card.mp h3 with ⟨Q1, hQ1, Q2, hQ2, hne⟩
        have hQ1_eq : Q1 = q := h_at_most_one Q1 hQ1
        have hQ2_eq : Q2 = q := h_at_most_one Q2 hQ2
        rw [hQ1_eq, hQ2_eq] at hne
        <;> tauto
      have hS_le_one : S_r.card ≤ 1 := le_trans h_card_le h_one
      have h_main : (S_r.card : ℝ) ≤ C_target * r^t * (Qset.card : ℝ) := by
        have h10 : C_target * r^t * (Qset.card : ℝ) ≥ C_target * Real.rpow Δ t * (Qset.card : ℝ) := by
          have h11 : Real.rpow Δ t ≤ r^t := Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
          gcongr <;> positivity
        have h12 : C_target * Real.rpow Δ t = Real.rpow Δ (t - 20 * ε) := by
          dsimp only [C_target]
          have h := h_rpow_mul (-20 * ε) t
          have h2 : (-20 * ε) + t = t - 20 * ε := by ring
          rw [h2] at h
          exact h
        rw [h12] at h10
        have h13 : (1 : ℝ) ≤ Real.rpow Δ (t - 20 * ε) * (Qset.card : ℝ) := by
          have h14 : (Qset.card : ℝ) ≥ Real.rpow Δ (2 * ε - t) / (1 + Real.sqrt 2 / 2)^t := hQset_lower
          have h15 : Real.rpow Δ (t - 20 * ε) * (Qset.card : ℝ) ≥
              Real.rpow Δ (t - 20 * ε) * (Real.rpow Δ (2 * ε - t) / (1 + Real.sqrt 2 / 2)^t) := by
            have hpos : 0 < Real.rpow Δ (t - 20 * ε) := Real.rpow_pos_of_pos hΔ_pos _
            gcongr
          have h16 : Real.rpow Δ (t - 20 * ε) * Real.rpow Δ (2 * ε - t) = Real.rpow Δ (-18 * ε) := by
            have h := h_rpow_mul (t - 20 * ε) (2 * ε - t)
            have h2 : (t - 20 * ε) + (2 * ε - t) = -18 * ε := by ring
            rw [h2] at h
            exact h
          have h16' : Real.rpow Δ (t - 20 * ε) * (Real.rpow Δ (2 * ε - t) / (1 + Real.sqrt 2 / 2)^t) =
              Real.rpow Δ (-18 * ε) / (1 + Real.sqrt 2 / 2)^t := by
            rw [← mul_div_assoc, h16]
          rw [h16'] at h15
          have h17 : 1 ≤ Real.rpow Δ (-18 * ε) / (1 + Real.sqrt 2 / 2)^t := by
            have h18 : (1 + Real.sqrt 2 / 2)^t ≤ Real.rpow Δ (-18 * ε) := h_small_absorb
            have h19 : 0 < (1 + Real.sqrt 2 / 2)^t := by positivity
            calc
              1 = (1 + Real.sqrt 2 / 2)^t / (1 + Real.sqrt 2 / 2)^t := by
                field_simp [h19.ne'] <;> ring
              _ ≤ Real.rpow Δ (-18 * ε) / (1 + Real.sqrt 2 / 2)^t := by gcongr
          linarith
        have h20 : (S_r.card : ℝ) ≤ 1 := by exact_mod_cast hS_le_one
        linarith
      have h_sub2 : (Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r ⊆ (S_r : Set (ℤ × ℤ)) := by
        intro y hy
        have h_dist : dist y x ≤ r := by simpa [Metric.mem_closedBall, dist_comm] using hy.2
        exact Finset.mem_filter.mpr ⟨hy.1, h_dist⟩
      have h_ncover1 : Metric.externalCoveringNumber Δ.toNNReal ((Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r) ≤
          Metric.externalCoveringNumber Δ.toNNReal (S_r : Set (ℤ × ℤ)) :=
        Metric.externalCoveringNumber_mono_set h_sub2
      have h_ncover2 : (Metric.externalCoveringNumber Δ.toNNReal (S_r : Set (ℤ × ℤ)) : ENNReal) = (S_r.card : ENNReal) :=
        ncover_eq_card hΔ_pos h2Δ_lt_one S_r
      have h_ncover1' : (Metric.externalCoveringNumber Δ.toNNReal ((Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r) : ENNReal) ≤
          (Metric.externalCoveringNumber Δ.toNNReal (S_r : Set (ℤ × ℤ)) : ENNReal) := by
        exact_mod_cast h_ncover1
      have h_ncover : (Metric.externalCoveringNumber Δ.toNNReal ((Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r) : ENNReal) ≤
          (S_r.card : ENNReal) :=
        le_trans h_ncover1' (le_of_eq h_ncover2)
      have h_qset_cover : (Metric.externalCoveringNumber Δ.toNNReal (Qset : Set (ℤ × ℤ)) : ENNReal) = (Qset.card : ENNReal) :=
        ncover_eq_card hΔ_pos h2Δ_lt_one Qset
      have h_final_enn : (S_r.card : ENNReal) ≤ ENNReal.ofReal C_target * (ENNReal.ofReal r) ^ t * (Qset.card : ENNReal) := by
        have h_main_enn : ENNReal.ofReal (S_r.card : ℝ) ≤ ENNReal.ofReal (C_target * r^t * (Qset.card : ℝ)) :=
          ENNReal.ofReal_le_ofReal h_main
        have h_card_coe : ENNReal.ofReal (S_r.card : ℝ) = (S_r.card : ENNReal) := by simp
        rw [h_card_coe] at h_main_enn
        have h_rhs : ENNReal.ofReal (C_target * r^t * (Qset.card : ℝ)) =
            ENNReal.ofReal C_target * ENNReal.ofReal (r^t) * ENNReal.ofReal (Qset.card : ℝ) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)] <;> ring
        rw [h_rhs] at h_main_enn
        have h_rpow : ENNReal.ofReal (r^t) = (ENNReal.ofReal r)^t := by
          have h := ENNReal.ofReal_rpow_of_nonneg hr_pos.le ht.le
          exact h.symm
        rw [h_rpow] at h_main_enn
        have h_qcard : ENNReal.ofReal (Qset.card : ℝ) = (Qset.card : ENNReal) := by simp
        rw [h_qcard] at h_main_enn
        exact h_main_enn
      have h_goal : (S_r.card : ENNReal) ≤ ENNReal.ofReal C_target * (ENNReal.ofReal r) ^ t * (Metric.externalCoveringNumber Δ.toNNReal (Qset : Set (ℤ × ℤ)) : ENNReal) := by
        rw [h_qset_cover]
        exact h_final_enn
      exact le_trans h_ncover h_goal

    · -- Large radius: 2r ≥ 1
      have h_large : 1 ≤ 2 * r := by linarith
      let c := squareCenter Δ q
      have h_center_dist : ∀ (Q' : ℤ × ℤ), dist Q' q ≤ 2 * r →
          dist (squareCenter Δ Q') c ≤ Real.sqrt 2 * Δ * (2 * r) := by
        intro Q' hdist
        exact squareCenter_dist_le hΔ_pos hdist
      have h_r_ge_delta : Δ ≤ Real.sqrt 2 * Δ * (2 * r) := by
        have h13 : 1 ≤ Real.sqrt 2 * (2 * r) := by
          have h14 : 1 ≤ 2 * r := h_large
          have h15 : 1 ≤ Real.sqrt 2 := by
            have h16 : (1 : ℝ)^2 ≤ 2 := by norm_num
            exact Real.le_sqrt_of_sq_le h16
          nlinarith
        nlinarith
      have h_filter_sub : (Qset.filter (fun Q' => dist Q' q ≤ 2 * r)) ⊆
          Qset.filter (fun Q' => dist (squareCenter Δ Q') c ≤ Real.sqrt 2 * Δ * (2 * r)) := by
        intro Q' hQ'
        have h1 : Q' ∈ Qset := (Finset.mem_filter.mp hQ').1
        have h2 : dist Q' q ≤ 2 * r := (Finset.mem_filter.mp hQ').2
        exact Finset.mem_filter.mpr ⟨h1, h_center_dist Q' h2⟩
      have h_card2 : ((Qset.filter (fun Q' => dist Q' q ≤ 2 * r)).card : ℝ) ≤
          ((Qset.filter (fun Q' => dist (squareCenter Δ Q') c ≤ Real.sqrt 2 * Δ * (2 * r))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card h_filter_sub
      have h_growth := h_ball_growth c (Real.sqrt 2 * Δ * (2 * r)) h_r_ge_delta
      have h_main : ((Qset.filter (fun Q' => dist Q' q ≤ 2 * r)).card : ℝ) ≤
          C_target * r^t * (Qset.card : ℝ) := by
        calc ((Qset.filter (fun Q' => dist Q' q ≤ 2 * r)).card : ℝ)
          ≤ ((Qset.filter (fun Q' => dist (squareCenter Δ Q') c ≤ Real.sqrt 2 * Δ * (2 * r))).card : ℝ) := h_card2
        _ ≤ Real.rpow Δ (-ε) * K * (1 + Real.sqrt 2 / 2)^t * (Real.sqrt 2 * Δ * (2 * r))^t * (Qset.card : ℝ) := h_growth
        _ = Real.rpow Δ (-ε) * K * (1 + Real.sqrt 2 / 2)^t * (2 * Real.sqrt 2)^t * Δ^t * r^t * (Qset.card : ℝ) := by
            have h17 : (Real.sqrt 2 * Δ * (2 * r))^t = (2 * Real.sqrt 2)^t * Δ^t * r^t := by
              have h : Real.sqrt 2 * Δ * (2 * r) = (2 * Real.sqrt 2) * Δ * r := by ring
              rw [h]
              rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)] <;> ring
            rw [h17] <;> ring
        _ ≤ Real.rpow Δ (-2 * ε) * (1 + Real.sqrt 2 / 2)^t * (2 * Real.sqrt 2)^t * Δ^t * r^t * (Qset.card : ℝ) := by
            have h19 : Real.rpow Δ (-ε) * K ≤ Real.rpow Δ (-2 * ε) := by
              have hK2 : K ≤ Real.rpow Δ (-ε) := hK_absorb
              have hpos : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos _
              calc
                Real.rpow Δ (-ε) * K ≤ Real.rpow Δ (-ε) * Real.rpow Δ (-ε) := by gcongr
                _ = Real.rpow Δ (-2 * ε) := h_rpow_neg2e
            gcongr <;> linarith
        _ = (1 + Real.sqrt 2 / 2)^t * (2 * Real.sqrt 2)^t * Real.rpow Δ (t - 2 * ε) * r^t * (Qset.card : ℝ) := by
            have h20 : Real.rpow Δ (-2 * ε) * Δ^t = Real.rpow Δ (t - 2 * ε) := h_rpow_t_minus_2e
            have h_rearr : Real.rpow Δ (-2 * ε) * (1 + Real.sqrt 2 / 2)^t * (2 * Real.sqrt 2)^t * Δ^t * r^t * (Qset.card : ℝ) =
                (1 + Real.sqrt 2 / 2)^t * (2 * Real.sqrt 2)^t * (Real.rpow Δ (-2 * ε) * Δ^t) * r^t * (Qset.card : ℝ) := by ring
            rw [h_rearr, h20] <;> ring
        _ ≤ C_target * r^t * (Qset.card : ℝ) := by
            have h21 : (1 + Real.sqrt 2 / 2)^t * (2 * Real.sqrt 2)^t * Real.rpow Δ (t - 2 * ε) ≤ C_target := h_geom_absorb
            gcongr <;> positivity
      have hS_card : (S_r.card : ℝ) ≤ C_target * r^t * (Qset.card : ℝ) := by
        calc (S_r.card : ℝ)
          ≤ ((Qset.filter (fun Q' => dist Q' q ≤ 2 * r)).card : ℝ) := by exact_mod_cast h_card_le
        _ ≤ C_target * r^t * (Qset.card : ℝ) := h_main
      have h_sub2 : (Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r ⊆ (S_r : Set (ℤ × ℤ)) := by
        intro y hy
        have h_dist : dist y x ≤ r := by simpa [Metric.mem_closedBall, dist_comm] using hy.2
        exact Finset.mem_filter.mpr ⟨hy.1, h_dist⟩
      have h_ncover1 : Metric.externalCoveringNumber Δ.toNNReal ((Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r) ≤
          Metric.externalCoveringNumber Δ.toNNReal (S_r : Set (ℤ × ℤ)) :=
        Metric.externalCoveringNumber_mono_set h_sub2
      have h_ncover2 : (Metric.externalCoveringNumber Δ.toNNReal (S_r : Set (ℤ × ℤ)) : ENNReal) = (S_r.card : ENNReal) :=
        ncover_eq_card hΔ_pos h2Δ_lt_one S_r
      have h_ncover1' : (Metric.externalCoveringNumber Δ.toNNReal ((Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r) : ENNReal) ≤
          (Metric.externalCoveringNumber Δ.toNNReal (S_r : Set (ℤ × ℤ)) : ENNReal) := by
        exact_mod_cast h_ncover1
      have h_ncover : (Metric.externalCoveringNumber Δ.toNNReal ((Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r) : ENNReal) ≤
          (S_r.card : ENNReal) :=
        le_trans h_ncover1' (le_of_eq h_ncover2)
      have h_qset_cover2 : (Metric.externalCoveringNumber Δ.toNNReal (Qset : Set (ℤ × ℤ)) : ENNReal) = (Qset.card : ENNReal) :=
        ncover_eq_card hΔ_pos h2Δ_lt_one Qset
      have h_final_enn2 : (S_r.card : ENNReal) ≤ ENNReal.ofReal C_target * (ENNReal.ofReal r) ^ t * (Qset.card : ENNReal) := by
        have h_main_enn : ENNReal.ofReal (S_r.card : ℝ) ≤ ENNReal.ofReal (C_target * r^t * (Qset.card : ℝ)) :=
          ENNReal.ofReal_le_ofReal hS_card
        have h_card_coe : ENNReal.ofReal (S_r.card : ℝ) = (S_r.card : ENNReal) := by simp
        rw [h_card_coe] at h_main_enn
        have h_rhs : ENNReal.ofReal (C_target * r^t * (Qset.card : ℝ)) =
            ENNReal.ofReal C_target * ENNReal.ofReal (r^t) * ENNReal.ofReal (Qset.card : ℝ) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)] <;> ring
        rw [h_rhs] at h_main_enn
        have h_rpow : ENNReal.ofReal (r^t) = (ENNReal.ofReal r)^t := by
          have h := ENNReal.ofReal_rpow_of_nonneg hr_pos.le ht.le
          exact h.symm
        rw [h_rpow] at h_main_enn
        have h_qcard : ENNReal.ofReal (Qset.card : ℝ) = (Qset.card : ENNReal) := by simp
        rw [h_qcard] at h_main_enn
        exact h_main_enn
      have h_goal2 : (S_r.card : ENNReal) ≤ ENNReal.ofReal C_target * (ENNReal.ofReal r) ^ t * (Metric.externalCoveringNumber Δ.toNNReal (Qset : Set (ℤ × ℤ)) : ENNReal) := by
        rw [h_qset_cover2]
        exact h_final_enn2
      exact le_trans h_ncover h_goal2

  · -- S_r empty
    have h_empty : S_r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS_empty
    have h_ncover : (Metric.externalCoveringNumber Δ.toNNReal ((Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r) : ENNReal) = 0 := by
      have h_sub : (Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r ⊆ (S_r : Set (ℤ × ℤ)) := by
        intro y hy
        have h_dist : dist y x ≤ r := by simpa [Metric.mem_closedBall, dist_comm] using hy.2
        exact Finset.mem_filter.mpr ⟨hy.1, h_dist⟩
      rw [h_empty] at h_sub
      have h_eq : (Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r = ∅ := by simpa using h_sub
      rw [h_eq] <;> simp
    rw [h_ncover] <;> simp

/-- Tight Stub 4: ball-growth constant Δ^{-5ε/2} produces S-set constant Δ^{-8ε}
    using tight |Pfin|/|Qset| ratio and absorption. -/
lemma a1_ball_growth_to_sset_weak
    {Δ t ε : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (ht : 0 < t) (hε_pos : 0 < ε)
    (Qset : Finset (ℤ × ℤ))
    (hQset_nonempty : Qset.Nonempty)
    (h_ball_growth : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card : ℝ) ≤
        Real.rpow Δ (-17 * ε / 2) * (1 + Real.sqrt 2 / 2)^t * r^t * (Qset.card : ℝ))
    (h_geom_absorb :
      (1 + Real.sqrt 2 / 2)^t * (2 * Real.sqrt 2)^t * Real.rpow Δ (t - 17 * ε / 2) ≤ Real.rpow Δ (-15 * ε))
    (h_small_absorb :
      (1 + Real.sqrt 2 / 2)^t ≤ Real.rpow Δ (-13 * ε / 2)) :
    IsDeltaSSet Δ t (Real.rpow Δ (-15 * ε)) (Qset : Set (CoarseSquare Δ)) := by
  let C_target : ℝ := Real.rpow Δ (-15 * ε)
  have hC_pos : 0 < C_target := Real.rpow_pos_of_pos hΔ_pos _
  have hQcard_pos : 0 < (Qset.card : ℝ) := by
    have h : 0 < Qset.card := Finset.card_pos.mpr hQset_nonempty
    exact_mod_cast h
  have h2Δ_lt_one : 2 * Δ < 1 := by linarith

  have h_rpow_mul : ∀ (a b : ℝ), Real.rpow Δ a * Real.rpow Δ b = Real.rpow Δ (a + b) := by
    intro a b
    exact (Real.rpow_add hΔ_pos a b).symm

  -- Lower bound on |Qset| from ball-growth at r=Δ
  have hQset_lower : (Qset.card : ℝ) ≥ Real.rpow Δ (17 * ε / 2 - t) / (1 + Real.sqrt 2 / 2)^t := by
    rcases hQset_nonempty with ⟨Q, hQ⟩
    let c := squareCenter Δ Q
    have h1 : Q ∈ Qset.filter (fun Q' => dist (squareCenter Δ Q') c ≤ Δ) := by
      simp only [Finset.mem_filter, c, dist_self]
      exact ⟨hQ, by linarith [hΔ_pos]⟩
    have h2 : 0 < (Qset.filter (fun Q' => dist (squareCenter Δ Q') c ≤ Δ)).card :=
      Finset.card_pos.mpr ⟨Q, h1⟩
    have h3 := h_ball_growth c Δ (by linarith)
    have h4 : (1 : ℝ) ≤ ((Qset.filter (fun Q' => dist (squareCenter Δ Q') c ≤ Δ)).card : ℝ) := by exact_mod_cast h2
    have h5 : (1 : ℝ) ≤ Real.rpow Δ (-17 * ε / 2) * (1 + Real.sqrt 2 / 2)^t * Real.rpow Δ t * (Qset.card : ℝ) := le_trans h4 h3
    have h_posC : 0 < (1 + Real.sqrt 2 / 2)^t := by positivity
    have h_posD : 0 < Real.rpow Δ t := Real.rpow_pos_of_pos hΔ_pos _
    set A : ℝ := (1 + Real.sqrt 2 / 2)^t with hA_def
    set B : ℝ := Real.rpow Δ (t - 17 * ε / 2) with hB_def
    have h6 : Real.rpow Δ (-17 * ε / 2) * Real.rpow Δ t = B := by
      have h := h_rpow_mul (-17 * ε / 2) t
      have h2 : (-17 * ε / 2) + t = t - 17 * ε / 2 := by ring
      rw [h2] at h
      exact h
    have h7 : (1 : ℝ) ≤ A * B * (Qset.card : ℝ) := by
      have h5' : (1 : ℝ) ≤ Real.rpow Δ (-17 * ε / 2) * A * Real.rpow Δ t * (Qset.card : ℝ) := h5
      have h5'' : Real.rpow Δ (-17 * ε / 2) * A * Real.rpow Δ t * (Qset.card : ℝ) = A * B * (Qset.card : ℝ) := by
        have hB_eq : B = Real.rpow Δ (-17 * ε / 2) * Real.rpow Δ t := h6.symm
        rw [hB_eq] <;> ring
      rw [h5''] at h5'
      exact h5'
    have h_pos3 : 0 < A * B := mul_pos h_posC (Real.rpow_pos_of_pos hΔ_pos _)
    have h8 : B * Real.rpow Δ (17 * ε / 2 - t) = 1 := by
      rw [hB_def]
      have h9 := h_rpow_mul (t - 17 * ε / 2) (17 * ε / 2 - t)
      have h10 : (t - 17 * ε / 2) + (17 * ε / 2 - t) = 0 := by ring
      rw [h10] at h9
      simpa using h9
    have h9 : (Qset.card : ℝ) ≥ 1 / (A * B) := by
      have h10 : (A * B)⁻¹ * (A * B * (Qset.card : ℝ)) ≥ (A * B)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h7 (by positivity)
      have h11 : (A * B)⁻¹ * (A * B * (Qset.card : ℝ)) = (Qset.card : ℝ) := by
        rw [inv_mul_cancel_left₀ h_pos3.ne'] <;> ring
      have h12 : (A * B)⁻¹ * 1 = 1 / (A * B) := by ring
      rw [h11, h12] at h10
      exact h10
    have h13 : 1 / (A * B) = Real.rpow Δ (17 * ε / 2 - t) / A := by
      have h14 : 1 / (A * B) = (1 / A) * (1 / B) := by
        field_simp [h_pos3.ne'] <;> ring
      rw [h14]
      have hB_pos : 0 < B := Real.rpow_pos_of_pos hΔ_pos _
      have h15 : 1 / B = Real.rpow Δ (17 * ε / 2 - t) := by
        have h16 : B * Real.rpow Δ (17 * ε / 2 - t) = 1 := h8
        have h17 : Real.rpow Δ (17 * ε / 2 - t) = 1 / B := by
          exact (eq_div_iff hB_pos.ne').mpr (by rw [mul_comm] <;> exact h16)
        exact h17.symm
      rw [h15] <;> ring
    rw [h13] at h9
    exact h9

  refine' ⟨hQset_nonempty, hΔ_pos, hC_pos, by linarith, _⟩
  intro x r hr
  have hr_pos : 0 < r := by linarith
  let S_r : Finset (ℤ × ℤ) := Qset.filter (fun Q => dist Q x ≤ r)

  by_cases hS_empty : S_r.Nonempty
  · rcases hS_empty with ⟨q, hq⟩
    have hq_in : q ∈ Qset := (Finset.mem_filter.mp hq).1
    have hq_dist : dist q x ≤ r := (Finset.mem_filter.mp hq).2
    have h_sub : S_r ⊆ Qset.filter (fun Q' => dist Q' q ≤ 2 * r) := by
      intro Q' hQ'
      have h1 : Q' ∈ Qset := (Finset.mem_filter.mp hQ').1
      have h2 : dist Q' x ≤ r := (Finset.mem_filter.mp hQ').2
      have h3 : dist Q' q ≤ dist Q' x + dist x q := dist_triangle _ _ _
      have h4 : dist x q ≤ r := by simpa [dist_comm] using hq_dist
      have h5 : dist Q' q ≤ 2 * r := by linarith
      exact Finset.mem_filter.mpr ⟨h1, h5⟩
    have h_card_le : S_r.card ≤ (Qset.filter (fun Q' => dist Q' q ≤ 2 * r)).card :=
      Finset.card_le_card h_sub

    by_cases h_small : 2 * r < 1
    · -- Small radius: ball contains at most 1 point
      have h_at_most_one : ∀ (Q' : ℤ × ℤ), Q' ∈ Qset.filter (fun Q'' => dist Q'' q ≤ 2 * r) → Q' = q := by
        intro Q' hQ'
        have hdist : dist Q' q ≤ 2 * r := (Finset.mem_filter.mp hQ').2
        have hlt : dist Q' q < 1 := by linarith
        by_cases h : Q' = q
        · exact h
        · have h' : (1 : ℝ) ≤ dist Q' q := coarseSquare_dist_one_le h
          linarith
      have h_one : (Qset.filter (fun Q' => dist Q' q ≤ 2 * r)).card ≤ 1 := by
        by_contra h2
        have h3 : 2 ≤ (Qset.filter (fun Q' => dist Q' q ≤ 2 * r)).card := by omega
        rcases Finset.one_lt_card.mp h3 with ⟨Q1, hQ1, Q2, hQ2, hne⟩
        have hQ1_eq : Q1 = q := h_at_most_one Q1 hQ1
        have hQ2_eq : Q2 = q := h_at_most_one Q2 hQ2
        rw [hQ1_eq, hQ2_eq] at hne <;> tauto
      have hS_le_one : S_r.card ≤ 1 := le_trans h_card_le h_one
      have h_main : (S_r.card : ℝ) ≤ C_target * r^t * (Qset.card : ℝ) := by
        have h10 : C_target * r^t * (Qset.card : ℝ) ≥ C_target * Real.rpow Δ t * (Qset.card : ℝ) := by
          have h11 : Real.rpow Δ t ≤ r^t := Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
          gcongr <;> positivity
        have h12 : C_target * Real.rpow Δ t = Real.rpow Δ (t - 15 * ε) := by
          dsimp only [C_target]
          have h := h_rpow_mul (-15 * ε) t
          have h2 : (-15 * ε) + t = t - 15 * ε := by ring
          rw [h2] at h
          exact h
        rw [h12] at h10
        have h13 : (1 : ℝ) ≤ Real.rpow Δ (t - 15 * ε) * (Qset.card : ℝ) := by
          have h14 : (Qset.card : ℝ) ≥ Real.rpow Δ (17 * ε / 2 - t) / (1 + Real.sqrt 2 / 2)^t := hQset_lower
          have h15 : Real.rpow Δ (t - 15 * ε) * (Qset.card : ℝ) ≥
              Real.rpow Δ (t - 15 * ε) * (Real.rpow Δ (17 * ε / 2 - t) / (1 + Real.sqrt 2 / 2)^t) := by
              have hpos : 0 < Real.rpow Δ (t - 15 * ε) := Real.rpow_pos_of_pos hΔ_pos _
              gcongr
          have h16 : Real.rpow Δ (t - 15 * ε) * Real.rpow Δ (17 * ε / 2 - t) = Real.rpow Δ (-13 * ε / 2) := by
            have h := h_rpow_mul (t - 15 * ε) (17 * ε / 2 - t)
            have h2 : (t - 15 * ε) + (17 * ε / 2 - t) = -13 * ε / 2 := by ring
            rw [h2] at h
            exact h
          have h16' : Real.rpow Δ (t - 15 * ε) * (Real.rpow Δ (17 * ε / 2 - t) / (1 + Real.sqrt 2 / 2)^t) =
              Real.rpow Δ (-13 * ε / 2) / (1 + Real.sqrt 2 / 2)^t := by
              rw [← mul_div_assoc, h16]
          rw [h16'] at h15
          have h17 : 1 ≤ Real.rpow Δ (-13 * ε / 2) / (1 + Real.sqrt 2 / 2)^t := by
            have h18 : (1 + Real.sqrt 2 / 2)^t ≤ Real.rpow Δ (-13 * ε / 2) := h_small_absorb
            have h19 : 0 < (1 + Real.sqrt 2 / 2)^t := by positivity
            have h20 : 0 < Real.rpow Δ (-13 * ε / 2) := Real.rpow_pos_of_pos hΔ_pos _
            have h21 : Real.rpow Δ (-13 * ε / 2) / (1 + Real.sqrt 2 / 2)^t ≥
                Real.rpow Δ (-13 * ε / 2) / Real.rpow Δ (-13 * ε / 2) := by
              have h221 : (1 + Real.sqrt 2 / 2)^t ≤ Real.rpow Δ (-13 * ε / 2) := h18
              have h222 : 0 < (1 + Real.sqrt 2 / 2)^t := h19
              have h223 : 0 < Real.rpow Δ (-13 * ε / 2) := h20
              have h224 : 1 / (1 + Real.sqrt 2 / 2)^t ≥ 1 / Real.rpow Δ (-13 * ε / 2) := by gcongr
              have h : Real.rpow Δ (-13 * ε / 2) / (1 + Real.sqrt 2 / 2)^t =
                  Real.rpow Δ (-13 * ε / 2) * (1 / (1 + Real.sqrt 2 / 2)^t) := by ring
              rw [h]
              have h2 : Real.rpow Δ (-13 * ε / 2) * (1 / (1 + Real.sqrt 2 / 2)^t) ≥
                  Real.rpow Δ (-13 * ε / 2) * (1 / Real.rpow Δ (-13 * ε / 2)) := by
                exact mul_le_mul_of_nonneg_left h224 h20.le
              have h3 : Real.rpow Δ (-13 * ε / 2) * (1 / Real.rpow Δ (-13 * ε / 2)) =
                  Real.rpow Δ (-13 * ε / 2) / Real.rpow Δ (-13 * ε / 2) := by ring
              rw [h3] at h2
              exact h2
            have h23 : Real.rpow Δ (-13 * ε / 2) / Real.rpow Δ (-13 * ε / 2) = 1 :=
              div_self h20.ne'
            have h28 : Real.rpow Δ (-13 * ε / 2) / (1 + Real.sqrt 2 / 2)^t ≥ 1 := by
              calc _ ≥ Real.rpow Δ (-13 * ε / 2) / Real.rpow Δ (-13 * ε / 2) := h21
                   _ = 1 := h23
            exact h28
          linarith
        have h20 : (S_r.card : ℝ) ≤ 1 := by exact_mod_cast hS_le_one
        linarith
      have h_sub2 : (Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r ⊆ (S_r : Set (ℤ × ℤ)) := by
        intro y hy
        have h_dist : dist y x ≤ r := by simpa [Metric.mem_closedBall, dist_comm] using hy.2
        exact Finset.mem_filter.mpr ⟨hy.1, h_dist⟩
      have h_ncover1 : Metric.externalCoveringNumber Δ.toNNReal ((Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r) ≤
          Metric.externalCoveringNumber Δ.toNNReal (S_r : Set (ℤ × ℤ)) :=
        Metric.externalCoveringNumber_mono_set h_sub2
      have h_ncover2 : (Metric.externalCoveringNumber Δ.toNNReal (S_r : Set (ℤ × ℤ)) : ENNReal) = (S_r.card : ENNReal) :=
        ncover_eq_card hΔ_pos h2Δ_lt_one S_r
      have h_ncover1' : (Metric.externalCoveringNumber Δ.toNNReal ((Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r) : ENNReal) ≤
          (Metric.externalCoveringNumber Δ.toNNReal (S_r : Set (ℤ × ℤ)) : ENNReal) := by
        exact_mod_cast h_ncover1
      have h_ncover : (Metric.externalCoveringNumber Δ.toNNReal ((Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r) : ENNReal) ≤
          (S_r.card : ENNReal) :=
        le_trans h_ncover1' (le_of_eq h_ncover2)
      have h_qset_cover : (Metric.externalCoveringNumber Δ.toNNReal (Qset : Set (ℤ × ℤ)) : ENNReal) = (Qset.card : ENNReal) :=
        ncover_eq_card hΔ_pos h2Δ_lt_one Qset
      have h_final_enn : (S_r.card : ENNReal) ≤ ENNReal.ofReal C_target * (ENNReal.ofReal r) ^ t * (Qset.card : ENNReal) := by
        have h_main_enn : ENNReal.ofReal (S_r.card : ℝ) ≤ ENNReal.ofReal (C_target * r^t * (Qset.card : ℝ)) :=
          ENNReal.ofReal_le_ofReal h_main
        have h_card_coe : ENNReal.ofReal (S_r.card : ℝ) = (S_r.card : ENNReal) := by simp
        rw [h_card_coe] at h_main_enn
        have h_rhs : ENNReal.ofReal (C_target * r^t * (Qset.card : ℝ)) =
            ENNReal.ofReal C_target * ENNReal.ofReal (r^t) * ENNReal.ofReal (Qset.card : ℝ) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)] <;> ring
        rw [h_rhs] at h_main_enn
        have h_rpow : ENNReal.ofReal (r^t) = (ENNReal.ofReal r)^t := by
          have h := ENNReal.ofReal_rpow_of_nonneg hr_pos.le ht.le
          exact h.symm
        rw [h_rpow] at h_main_enn
        have h_qcard : ENNReal.ofReal (Qset.card : ℝ) = (Qset.card : ENNReal) := by simp
        rw [h_qcard] at h_main_enn
        exact h_main_enn
      have h_goal : (S_r.card : ENNReal) ≤ ENNReal.ofReal C_target * (ENNReal.ofReal r) ^ t * (Metric.externalCoveringNumber Δ.toNNReal (Qset : Set (ℤ × ℤ)) : ENNReal) := by
        rw [h_qset_cover]
        exact h_final_enn
      exact le_trans h_ncover h_goal

    · -- Large radius: 2r ≥ 1
      have h_large : 1 ≤ 2 * r := by linarith
      let c := squareCenter Δ q
      have h_center_dist : ∀ (Q' : ℤ × ℤ), dist Q' q ≤ 2 * r →
          dist (squareCenter Δ Q') c ≤ Real.sqrt 2 * Δ * (2 * r) := by
        intro Q' hdist
        exact squareCenter_dist_le hΔ_pos hdist
      have h_r_ge_delta : Δ ≤ Real.sqrt 2 * Δ * (2 * r) := by
        have h13 : 1 ≤ Real.sqrt 2 * (2 * r) := by
          have h14 : 1 ≤ 2 * r := h_large
          have h15 : 1 ≤ Real.sqrt 2 := by
            have h16 : (1 : ℝ)^2 ≤ 2 := by norm_num
            exact Real.le_sqrt_of_sq_le h16
          nlinarith
        nlinarith
      have h_filter_sub : (Qset.filter (fun Q' => dist Q' q ≤ 2 * r)) ⊆
          Qset.filter (fun Q' => dist (squareCenter Δ Q') c ≤ Real.sqrt 2 * Δ * (2 * r)) := by
        intro Q' hQ'
        have h1 : Q' ∈ Qset := (Finset.mem_filter.mp hQ').1
        have h2 : dist Q' q ≤ 2 * r := (Finset.mem_filter.mp hQ').2
        exact Finset.mem_filter.mpr ⟨h1, h_center_dist Q' h2⟩
      have h_card2 : ((Qset.filter (fun Q' => dist Q' q ≤ 2 * r)).card : ℝ) ≤
          ((Qset.filter (fun Q' => dist (squareCenter Δ Q') c ≤ Real.sqrt 2 * Δ * (2 * r))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card h_filter_sub
      have h_growth := h_ball_growth c (Real.sqrt 2 * Δ * (2 * r)) h_r_ge_delta
      have h_main : ((Qset.filter (fun Q' => dist Q' q ≤ 2 * r)).card : ℝ) ≤
          C_target * r^t * (Qset.card : ℝ) := by
        calc ((Qset.filter (fun Q' => dist Q' q ≤ 2 * r)).card : ℝ)
          ≤ ((Qset.filter (fun Q' => dist (squareCenter Δ Q') c ≤ Real.sqrt 2 * Δ * (2 * r))).card : ℝ) := h_card2
        _ ≤ Real.rpow Δ (-17 * ε / 2) * (1 + Real.sqrt 2 / 2)^t * (Real.sqrt 2 * Δ * (2 * r))^t * (Qset.card : ℝ) := h_growth
        _ = Real.rpow Δ (-17 * ε / 2) * (1 + Real.sqrt 2 / 2)^t * (2 * Real.sqrt 2)^t * Δ^t * r^t * (Qset.card : ℝ) := by
            have h17 : (Real.sqrt 2 * Δ * (2 * r))^t = (2 * Real.sqrt 2)^t * Δ^t * r^t := by
              have h : Real.sqrt 2 * Δ * (2 * r) = (2 * Real.sqrt 2) * Δ * r := by ring
              rw [h]
              rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)] <;> ring
            rw [h17] <;> ring
        _ = (1 + Real.sqrt 2 / 2)^t * (2 * Real.sqrt 2)^t * Real.rpow Δ (t - 17 * ε / 2) * r^t * (Qset.card : ℝ) := by
            have h20 : Real.rpow Δ (-17 * ε / 2) * Δ^t = Real.rpow Δ (t - 17 * ε / 2) := by
              have h := h_rpow_mul (-17 * ε / 2) t
              have h2 : (-17 * ε / 2) + t = t - 17 * ε / 2 := by ring
              rw [h2] at h
              exact h
            have h_rearr : Real.rpow Δ (-17 * ε / 2) * (1 + Real.sqrt 2 / 2)^t * (2 * Real.sqrt 2)^t * Δ^t * r^t * (Qset.card : ℝ) =
                (1 + Real.sqrt 2 / 2)^t * (2 * Real.sqrt 2)^t * (Real.rpow Δ (-17 * ε / 2) * Δ^t) * r^t * (Qset.card : ℝ) := by ring
            rw [h_rearr, h20] <;> ring
        _ ≤ C_target * r^t * (Qset.card : ℝ) := by
            have h21 : (1 + Real.sqrt 2 / 2)^t * (2 * Real.sqrt 2)^t * Real.rpow Δ (t - 17 * ε / 2) ≤ C_target := h_geom_absorb
            gcongr <;> positivity
      have hS_card : (S_r.card : ℝ) ≤ C_target * r^t * (Qset.card : ℝ) := by
        calc (S_r.card : ℝ)
          ≤ ((Qset.filter (fun Q' => dist Q' q ≤ 2 * r)).card : ℝ) := by exact_mod_cast h_card_le
        _ ≤ C_target * r^t * (Qset.card : ℝ) := h_main
      have h_sub2 : (Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r ⊆ (S_r : Set (ℤ × ℤ)) := by
        intro y hy
        have h_dist : dist y x ≤ r := by simpa [Metric.mem_closedBall, dist_comm] using hy.2
        exact Finset.mem_filter.mpr ⟨hy.1, h_dist⟩
      have h_ncover1 : Metric.externalCoveringNumber Δ.toNNReal ((Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r) ≤
          Metric.externalCoveringNumber Δ.toNNReal (S_r : Set (ℤ × ℤ)) :=
        Metric.externalCoveringNumber_mono_set h_sub2
      have h_ncover2 : (Metric.externalCoveringNumber Δ.toNNReal (S_r : Set (ℤ × ℤ)) : ENNReal) = (S_r.card : ENNReal) :=
        ncover_eq_card hΔ_pos h2Δ_lt_one S_r
      have h_ncover1' : (Metric.externalCoveringNumber Δ.toNNReal ((Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r) : ENNReal) ≤
          (Metric.externalCoveringNumber Δ.toNNReal (S_r : Set (ℤ × ℤ)) : ENNReal) := by
        exact_mod_cast h_ncover1
      have h_ncover : (Metric.externalCoveringNumber Δ.toNNReal ((Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r) : ENNReal) ≤
          (S_r.card : ENNReal) :=
        le_trans h_ncover1' (le_of_eq h_ncover2)
      have h_qset_cover2 : (Metric.externalCoveringNumber Δ.toNNReal (Qset : Set (ℤ × ℤ)) : ENNReal) = (Qset.card : ENNReal) :=
        ncover_eq_card hΔ_pos h2Δ_lt_one Qset
      have h_final_enn2 : (S_r.card : ENNReal) ≤ ENNReal.ofReal C_target * (ENNReal.ofReal r) ^ t * (Qset.card : ENNReal) := by
        have h_main_enn : ENNReal.ofReal (S_r.card : ℝ) ≤ ENNReal.ofReal (C_target * r^t * (Qset.card : ℝ)) :=
          ENNReal.ofReal_le_ofReal hS_card
        have h_card_coe : ENNReal.ofReal (S_r.card : ℝ) = (S_r.card : ENNReal) := by simp
        rw [h_card_coe] at h_main_enn
        have h_rhs : ENNReal.ofReal (C_target * r^t * (Qset.card : ℝ)) =
            ENNReal.ofReal C_target * ENNReal.ofReal (r^t) * ENNReal.ofReal (Qset.card : ℝ) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)] <;> ring
        rw [h_rhs] at h_main_enn
        have h_rpow : ENNReal.ofReal (r^t) = (ENNReal.ofReal r)^t := by
          have h := ENNReal.ofReal_rpow_of_nonneg hr_pos.le ht.le
          exact h.symm
        rw [h_rpow] at h_main_enn
        have h_qcard : ENNReal.ofReal (Qset.card : ℝ) = (Qset.card : ENNReal) := by simp
        rw [h_qcard] at h_main_enn
        exact h_main_enn
      have h_goal2 : (S_r.card : ENNReal) ≤ ENNReal.ofReal C_target * (ENNReal.ofReal r) ^ t * (Metric.externalCoveringNumber Δ.toNNReal (Qset : Set (ℤ × ℤ)) : ENNReal) := by
        rw [h_qset_cover2]
        exact h_final_enn2
      exact le_trans h_ncover h_goal2

  · -- S_r empty
    have h_empty : S_r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS_empty
    have h_ncover : (Metric.externalCoveringNumber Δ.toNNReal ((Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r) : ENNReal) = 0 := by
      have h_sub : (Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r ⊆ (S_r : Set (ℤ × ℤ)) := by
        intro y hy
        have h_dist : dist y x ≤ r := by simpa [Metric.mem_closedBall, dist_comm] using hy.2
        exact Finset.mem_filter.mpr ⟨hy.1, h_dist⟩
      rw [h_empty] at h_sub
      have h_eq : (Qset : Set (ℤ × ℤ)) ∩ Metric.closedBall x r = ∅ := by simpa using h_sub
      rw [h_eq] <;> simp
    rw [h_ncover] <;> simp

end DirecretisedFurstenbergEstimate.Cobalt

namespace DirecretisedFurstenbergEstimate.Pelican

/-- Helper: U_upper / m₀^2 ≤ Δ^{t-10ε} given the A1 parameter bounds. -/
lemma ratio_bound {Δ t ε : ℝ}
    (hΔ_pos : 0 < Δ) (hε_pos : 0 < ε) (ht : 0 < t)
    (h_small_strong : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (U_upper m₀ : ℝ)
    (hU_exp : U_upper = 81 * Real.rpow Δ (-t - 9 * ε / 4))
    (hm0_lower : m₀ ≥ Real.rpow Δ (-t + 5 * ε / 2) / 162) :
    U_upper / m₀^2 ≤ Real.rpow Δ (t - 10 * ε) := by
  have h_rpow_add : ∀ (a b : ℝ), Real.rpow Δ a * Real.rpow Δ b = Real.rpow Δ (a + b) := by
    intro a b; exact (Real.rpow_add hΔ_pos a b).symm
  have h_rpow_sub : ∀ (a b : ℝ), Real.rpow Δ a / Real.rpow Δ b = Real.rpow Δ (a - b) := by
    intro a b; have h := Real.rpow_sub hΔ_pos a b; simpa using h.symm
  have h_rpow_mul_nat : ∀ (a : ℝ) (n : ℕ), Real.rpow Δ (a * (n : ℝ)) = (Real.rpow Δ a) ^ n := by
    intro a n; simpa [Real.rpow_mul] using Real.rpow_mul hΔ_pos.le a (n : ℝ)
  have h_pos2 : 0 < Real.rpow Δ (-2 * t + 5 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  have h_pos4 : 0 < Real.rpow Δ (t - 29 * ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
  have h_m0_pos : 0 < m₀ := by
    have h_rpow_pos : 0 < Real.rpow Δ (-t + 5 * ε / 2) := Real.rpow_pos_of_pos hΔ_pos _
    have h : 0 < Real.rpow Δ (-t + 5 * ε / 2) / 162 := by
      apply div_pos h_rpow_pos
      norm_num
    linarith
  have h1 : m₀^2 ≥ (Real.rpow Δ (-t + 5 * ε / 2) / 162) ^ 2 := by
    have h_nonneg : 0 ≤ Real.rpow Δ (-t + 5 * ε / 2) / 162 := by
      have h_rpow_pos : 0 < Real.rpow Δ (-t + 5 * ε / 2) := Real.rpow_pos_of_pos hΔ_pos _
      exact div_nonneg h_rpow_pos.le (by norm_num)
    gcongr
  have h21 : Real.rpow Δ (-t + 5 * ε / 2) * Real.rpow Δ (-t + 5 * ε / 2) =
      Real.rpow Δ (-2 * t + 5 * ε) := by
    have h := h_rpow_add (-t + 5 * ε / 2) (-t + 5 * ε / 2)
    have h2 : (-t + 5 * ε / 2) + (-t + 5 * ε / 2) = -2 * t + 5 * ε := by ring
    rw [h2] at h
    exact h
  have h2 : (Real.rpow Δ (-t + 5 * ε / 2) / 162) ^ 2 =
      Real.rpow Δ (-2 * t + 5 * ε) / 162 ^ 2 := by
    calc
      (Real.rpow Δ (-t + 5 * ε / 2) / 162) ^ 2
        = (Real.rpow Δ (-t + 5 * ε / 2)) ^ 2 / 162 ^ 2 := by ring
      _ = (Real.rpow Δ (-t + 5 * ε / 2) * Real.rpow Δ (-t + 5 * ε / 2)) / 162 ^ 2 := by ring
      _ = Real.rpow Δ (-2 * t + 5 * ε) / 162 ^ 2 := by rw [h21]
  have h3 : U_upper / m₀^2 ≤
      (81 : ℝ) * Real.rpow Δ (-t - 9 * ε / 4) /
        (Real.rpow Δ (-2 * t + 5 * ε) / 162 ^ 2) := by
    rw [hU_exp]
    have h4 : m₀^2 ≥ Real.rpow Δ (-2 * t + 5 * ε) / 162 ^ 2 := by
      calc m₀^2 ≥ (Real.rpow Δ (-t + 5 * ε / 2) / 162) ^ 2 := h1
           _ = Real.rpow Δ (-2 * t + 5 * ε) / 162 ^ 2 := h2
    have h5 : 0 < Real.rpow Δ (-2 * t + 5 * ε) / 162 ^ 2 := by
      have h_pos : 0 < Real.rpow Δ (-2 * t + 5 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      exact div_pos h_pos (by norm_num)
    have h_num_pos : 0 < (81 : ℝ) * Real.rpow Δ (-t - 9 * ε / 4) := by
      exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hΔ_pos _)
    exact div_le_div_of_nonneg_left h_num_pos.le h5 h4
  have h51 : Real.rpow Δ (-t - 9 * ε / 4) / Real.rpow Δ (-2 * t + 5 * ε) =
      Real.rpow Δ (t - 29 * ε / 4) := by
    have h_exp : (-t - 9 * ε / 4) - (-2 * t + 5 * ε) = t - 29 * ε / 4 := by ring
    have h_sub' := h_rpow_sub (-t - 9 * ε / 4) (-2 * t + 5 * ε)
    rw [h_sub', h_exp]
  have h4 : (81 : ℝ) * Real.rpow Δ (-t - 9 * ε / 4) /
        (Real.rpow Δ (-2 * t + 5 * ε) / 162 ^ 2) =
      (2125764 : ℝ) * Real.rpow Δ (t - 29 * ε / 4) := by
    have h_pos2' : 0 < Real.rpow Δ (-2 * t + 5 * ε) := h_pos2
    have h_eq1 : (81 : ℝ) * Real.rpow Δ (-t - 9 * ε / 4) /
          (Real.rpow Δ (-2 * t + 5 * ε) / 162 ^ 2) =
        (81 * 162 ^ 2 : ℝ) * (Real.rpow Δ (-t - 9 * ε / 4) / Real.rpow Δ (-2 * t + 5 * ε)) := by
      field_simp [h_pos2'.ne'] <;> ring
    rw [h_eq1, h51]
    have h_const : (81 * 162 ^ 2 : ℝ) = (2125764 : ℝ) := by norm_num
    rw [h_const]
  have h61 : (11 * ε / 4 : ℝ) = (ε / 4) * (11 : ℝ) := by ring
  have h62 : Real.rpow Δ (11 * ε / 4) = (Real.rpow Δ (ε / 4)) ^ 11 := by
    have h : Real.rpow Δ ((ε / 4) * (11 : ℝ)) = (Real.rpow Δ (ε / 4)) ^ 11 :=
      h_rpow_mul_nat (ε / 4) 11
    convert h using 1 <;> ring_nf
  have h5 : Real.rpow Δ (11 * ε / 4) ≤ (1 / 2125764 : ℝ) := by
    rw [h62]
    have h8 : (Real.rpow Δ (ε / 4)) ^ 11 ≤ (1 / 100 : ℝ) ^ 11 := by
      gcongr <;> exact Real.rpow_nonneg hΔ_pos.le _
    have h9 : (1 / 100 : ℝ) ^ 11 ≤ (1 / 2125764 : ℝ) := by norm_num
    exact le_trans h8 h9
  have h6 : Real.rpow Δ (-11 * ε / 4) ≥ (2125764 : ℝ) := by
    have h71 : (-11 * ε / 4 : ℝ) = -(11 * ε / 4) := by ring
    have h72 : Real.rpow Δ (-11 * ε / 4) = (Real.rpow Δ (11 * ε / 4))⁻¹ := by
      rw [h71]; exact Real.rpow_neg hΔ_pos.le (11 * ε / 4)
    rw [h72]
    have h_pos : 0 < Real.rpow Δ (11 * ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
    have h9 : (Real.rpow Δ (11 * ε / 4))⁻¹ ≥ ((1 / 2125764 : ℝ))⁻¹ := by gcongr
    have h10 : ((1 / 2125764 : ℝ))⁻¹ = 2125764 := by norm_num
    rw [h10] at h9; exact h9
  have h7 : (2125764 : ℝ) * Real.rpow Δ (t - 29 * ε / 4) ≤ Real.rpow Δ (t - 10 * ε) := by
    have h8 : Real.rpow Δ (t - 10 * ε) =
        Real.rpow Δ (t - 29 * ε / 4) * Real.rpow Δ (-11 * ε / 4) := by
      have h_exp2 : (t - 29 * ε / 4) + (-11 * ε / 4) = t - 10 * ε := by ring
      have h_add' := h_rpow_add (t - 29 * ε / 4) (-11 * ε / 4)
      rw [h_add', h_exp2]
    rw [h8]
    have h9 : 0 < Real.rpow Δ (t - 29 * ε / 4) := h_pos4
    nlinarith
  calc U_upper / m₀^2
    ≤ (81 : ℝ) * Real.rpow Δ (-t - 9 * ε / 4) /
          (Real.rpow Δ (-2 * t + 5 * ε) / 162 ^ 2) := h3
  _ = (2125764 : ℝ) * Real.rpow Δ (t - 29 * ε / 4) := h4
  _ ≤ Real.rpow Δ (t - 10 * ε) := h7

/-- Generalized ratio bound: U_upper / m₀^2 ≤ Δ^{t-10ε}.
    Requires C_U * C_m^2 ≤ 100^11. -/
lemma ratio_bound_general {Δ t ε C_U C_m : ℝ}
    (hΔ_pos : 0 < Δ) (hε_pos : 0 < ε) (ht : 0 < t)
    (h_small_strong : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (U_upper m₀ : ℝ)
    (hCU_pos : 0 < C_U) (hCm_pos : 0 < C_m)
    (h_const_bound : C_U * C_m^2 ≤ (100 : ℝ)^11)
    (hU_exp : U_upper = C_U * Real.rpow Δ (-t - 9 * ε / 4))
    (hm0_lower : m₀ ≥ Real.rpow Δ (-t + 5 * ε / 2) / C_m) :
    U_upper / m₀^2 ≤ Real.rpow Δ (t - 10 * ε) := by
  have h_rpow_add : ∀ (a b : ℝ), Real.rpow Δ a * Real.rpow Δ b = Real.rpow Δ (a + b) := by
    intro a b; exact (Real.rpow_add hΔ_pos a b).symm
  have h_rpow_sub : ∀ (a b : ℝ), Real.rpow Δ a / Real.rpow Δ b = Real.rpow Δ (a - b) := by
    intro a b; have h := Real.rpow_sub hΔ_pos a b; simpa using h.symm
  have h_rpow_mul_nat : ∀ (a : ℝ) (n : ℕ), Real.rpow Δ (a * (n : ℝ)) = (Real.rpow Δ a) ^ n := by
    intro a n; simpa [Real.rpow_mul] using Real.rpow_mul hΔ_pos.le a (n : ℝ)
  have h_pos2 : 0 < Real.rpow Δ (-2 * t + 5 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  have h_pos4 : 0 < Real.rpow Δ (t - 29 * ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
  have h_m0_pos : 0 < m₀ := by
    have h_rpow_pos : 0 < Real.rpow Δ (-t + 5 * ε / 2) := Real.rpow_pos_of_pos hΔ_pos _
    have h : 0 < Real.rpow Δ (-t + 5 * ε / 2) / C_m := div_pos h_rpow_pos hCm_pos
    linarith
  have h1 : m₀^2 ≥ (Real.rpow Δ (-t + 5 * ε / 2) / C_m) ^ 2 := by
    have h_nonneg : 0 ≤ Real.rpow Δ (-t + 5 * ε / 2) / C_m := by
      have h_rpow_pos : 0 < Real.rpow Δ (-t + 5 * ε / 2) := Real.rpow_pos_of_pos hΔ_pos _
      exact div_nonneg h_rpow_pos.le hCm_pos.le
    gcongr
  have h21 : Real.rpow Δ (-t + 5 * ε / 2) * Real.rpow Δ (-t + 5 * ε / 2) =
      Real.rpow Δ (-2 * t + 5 * ε) := by
    have h := h_rpow_add (-t + 5 * ε / 2) (-t + 5 * ε / 2)
    have h2 : (-t + 5 * ε / 2) + (-t + 5 * ε / 2) = -2 * t + 5 * ε := by ring
    rw [h2] at h; exact h
  have h2 : (Real.rpow Δ (-t + 5 * ε / 2) / C_m) ^ 2 =
      Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2 := by
    calc
      (Real.rpow Δ (-t + 5 * ε / 2) / C_m) ^ 2
        = (Real.rpow Δ (-t + 5 * ε / 2)) ^ 2 / C_m ^ 2 := by ring
      _ = (Real.rpow Δ (-t + 5 * ε / 2) * Real.rpow Δ (-t + 5 * ε / 2)) / C_m ^ 2 := by ring
      _ = Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2 := by rw [h21]
  have h3 : U_upper / m₀^2 ≤
      C_U * Real.rpow Δ (-t - 9 * ε / 4) / (Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2) := by
    rw [hU_exp]
    have h4 : m₀^2 ≥ Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2 := by
      calc m₀^2 ≥ (Real.rpow Δ (-t + 5 * ε / 2) / C_m) ^ 2 := h1
           _ = Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2 := h2
    have h5 : 0 < Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2 := by
      have h_pos : 0 < Real.rpow Δ (-2 * t + 5 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      exact div_pos h_pos (pow_pos hCm_pos 2)
    have h_num_pos : 0 < C_U * Real.rpow Δ (-t - 9 * ε / 4) :=
      mul_pos hCU_pos (Real.rpow_pos_of_pos hΔ_pos _)
    exact div_le_div_of_nonneg_left h_num_pos.le h5 h4
  have h51 : Real.rpow Δ (-t - 9 * ε / 4) / Real.rpow Δ (-2 * t + 5 * ε) =
      Real.rpow Δ (t - 29 * ε / 4) := by
    have h_exp : (-t - 9 * ε / 4) - (-2 * t + 5 * ε) = t - 29 * ε / 4 := by ring
    have h_sub' := h_rpow_sub (-t - 9 * ε / 4) (-2 * t + 5 * ε)
    rw [h_sub', h_exp]
  have h4 : C_U * Real.rpow Δ (-t - 9 * ε / 4) /
        (Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2) =
      (C_U * C_m ^ 2) * Real.rpow Δ (t - 29 * ε / 4) := by
    have h_pos2' : 0 < Real.rpow Δ (-2 * t + 5 * ε) := h_pos2
    have h_eq1 : C_U * Real.rpow Δ (-t - 9 * ε / 4) /
          (Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2) =
        (C_U * C_m ^ 2) * (Real.rpow Δ (-t - 9 * ε / 4) / Real.rpow Δ (-2 * t + 5 * ε)) := by
      field_simp [h_pos2'.ne', hCm_pos.ne'] <;> ring
    rw [h_eq1, h51] <;> ring
  have h61 : (11 * ε / 4 : ℝ) = (ε / 4) * (11 : ℝ) := by ring
  have h62 : Real.rpow Δ (11 * ε / 4) = (Real.rpow Δ (ε / 4)) ^ 11 := by
    have h : Real.rpow Δ ((ε / 4) * (11 : ℝ)) = (Real.rpow Δ (ε / 4)) ^ 11 :=
      h_rpow_mul_nat (ε / 4) 11
    convert h using 1 <;> ring_nf
  have h5 : Real.rpow Δ (11 * ε / 4) ≤ 1 / (C_U * C_m ^ 2) := by
    rw [h62]
    have h8 : (Real.rpow Δ (ε / 4)) ^ 11 ≤ (1 / 100 : ℝ) ^ 11 := by
      gcongr <;> exact Real.rpow_nonneg hΔ_pos.le _
    have h9 : (1 / 100 : ℝ) ^ 11 ≤ 1 / (C_U * C_m ^ 2) := by
      have h10 : C_U * C_m ^ 2 ≤ (100 : ℝ) ^ 11 := h_const_bound
      have h_pos : 0 < C_U * C_m ^ 2 := mul_pos hCU_pos (pow_pos hCm_pos 2)
      have h11 : (1 / 100 : ℝ) ^ 11 = 1 / (100 : ℝ) ^ 11 := by
        simp
      rw [h11]
      gcongr
    exact le_trans h8 h9
  have h6 : Real.rpow Δ (-11 * ε / 4) ≥ C_U * C_m ^ 2 := by
    have h71 : (-11 * ε / 4 : ℝ) = -(11 * ε / 4) := by ring
    have h72 : Real.rpow Δ (-11 * ε / 4) = (Real.rpow Δ (11 * ε / 4))⁻¹ := by
      rw [h71]; exact Real.rpow_neg hΔ_pos.le (11 * ε / 4)
    rw [h72]
    have h_pos : 0 < Real.rpow Δ (11 * ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
    have h_pos2 : 0 < C_U * C_m ^ 2 := mul_pos hCU_pos (pow_pos hCm_pos 2)
    have h9 : (Real.rpow Δ (11 * ε / 4))⁻¹ ≥ (1 / (C_U * C_m ^ 2))⁻¹ := by gcongr
    have h10 : (1 / (C_U * C_m ^ 2))⁻¹ = C_U * C_m ^ 2 := by
      field_simp [h_pos2.ne'] <;> ring
    rw [h10] at h9; exact h9
  have h7 : (C_U * C_m ^ 2) * Real.rpow Δ (t - 29 * ε / 4) ≤ Real.rpow Δ (t - 10 * ε) := by
    have h8 : Real.rpow Δ (t - 10 * ε) =
        Real.rpow Δ (t - 29 * ε / 4) * Real.rpow Δ (-11 * ε / 4) := by
      have h_exp2 : (t - 29 * ε / 4) + (-11 * ε / 4) = t - 10 * ε := by ring
      have h_add' := h_rpow_add (t - 29 * ε / 4) (-11 * ε / 4)
      rw [h_add', h_exp2]
    rw [h8]
    have h9 : 0 < Real.rpow Δ (t - 29 * ε / 4) := h_pos4
    nlinarith
  calc U_upper / m₀^2
    ≤ C_U * Real.rpow Δ (-t - 9 * ε / 4) /
          (Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2) := h3
  _ = (C_U * C_m ^ 2) * Real.rpow Δ (t - 29 * ε / 4) := h4
  _ ≤ Real.rpow Δ (t - 10 * ε) := h7

/-- Generalized ratio bound with direct absorption hypothesis.
    Useful when C_U, C_m contain polylog factors that must be absorbed by Δ smallness. -/
lemma ratio_bound_absorb {Δ t ε C_U C_m : ℝ}
    (hΔ_pos : 0 < Δ) (hε_pos : 0 < ε) (ht : 0 < t)
    (U_upper m₀ : ℝ)
    (hCU_pos : 0 < C_U) (hCm_pos : 0 < C_m)
    (h_absorb : C_U * C_m^2 * Real.rpow Δ (11 * ε / 4) ≤ 1)
    (hU_exp : U_upper = C_U * Real.rpow Δ (-t - 9 * ε / 4))
    (hm0_lower : m₀ ≥ Real.rpow Δ (-t + 5 * ε / 2) / C_m) :
    U_upper / m₀^2 ≤ Real.rpow Δ (t - 10 * ε) := by
  have h_rpow_add : ∀ (a b : ℝ), Real.rpow Δ a * Real.rpow Δ b = Real.rpow Δ (a + b) := by
    intro a b; exact (Real.rpow_add hΔ_pos a b).symm
  have h_rpow_sub : ∀ (a b : ℝ), Real.rpow Δ a / Real.rpow Δ b = Real.rpow Δ (a - b) := by
    intro a b; have h := Real.rpow_sub hΔ_pos a b; simpa using h.symm
  have h_pos2 : 0 < Real.rpow Δ (-2 * t + 5 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  have h_pos4 : 0 < Real.rpow Δ (t - 29 * ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
  have h_m0_pos : 0 < m₀ := by
    have h_rpow_pos : 0 < Real.rpow Δ (-t + 5 * ε / 2) := Real.rpow_pos_of_pos hΔ_pos _
    have h : 0 < Real.rpow Δ (-t + 5 * ε / 2) / C_m := div_pos h_rpow_pos hCm_pos
    linarith
  have h1 : m₀^2 ≥ (Real.rpow Δ (-t + 5 * ε / 2) / C_m) ^ 2 := by
    have h_nonneg : 0 ≤ Real.rpow Δ (-t + 5 * ε / 2) / C_m := by
      have h_rpow_pos : 0 < Real.rpow Δ (-t + 5 * ε / 2) := Real.rpow_pos_of_pos hΔ_pos _
      exact div_nonneg h_rpow_pos.le hCm_pos.le
    gcongr
  have h21 : Real.rpow Δ (-t + 5 * ε / 2) * Real.rpow Δ (-t + 5 * ε / 2) =
      Real.rpow Δ (-2 * t + 5 * ε) := by
    have h := h_rpow_add (-t + 5 * ε / 2) (-t + 5 * ε / 2)
    have h2 : (-t + 5 * ε / 2) + (-t + 5 * ε / 2) = -2 * t + 5 * ε := by ring
    rw [h2] at h; exact h
  have h2 : (Real.rpow Δ (-t + 5 * ε / 2) / C_m) ^ 2 =
      Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2 := by
    calc
      (Real.rpow Δ (-t + 5 * ε / 2) / C_m) ^ 2
        = (Real.rpow Δ (-t + 5 * ε / 2)) ^ 2 / C_m ^ 2 := by ring
      _ = (Real.rpow Δ (-t + 5 * ε / 2) * Real.rpow Δ (-t + 5 * ε / 2)) / C_m ^ 2 := by ring
      _ = Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2 := by rw [h21]
  have h3 : U_upper / m₀^2 ≤
      C_U * Real.rpow Δ (-t - 9 * ε / 4) / (Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2) := by
    rw [hU_exp]
    have h4 : m₀^2 ≥ Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2 := by
      calc m₀^2 ≥ (Real.rpow Δ (-t + 5 * ε / 2) / C_m) ^ 2 := h1
           _ = Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2 := h2
    have h5 : 0 < Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2 := by
      have h_pos : 0 < Real.rpow Δ (-2 * t + 5 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      exact div_pos h_pos (pow_pos hCm_pos 2)
    have h_num_pos : 0 < C_U * Real.rpow Δ (-t - 9 * ε / 4) :=
      mul_pos hCU_pos (Real.rpow_pos_of_pos hΔ_pos _)
    exact div_le_div_of_nonneg_left h_num_pos.le h5 h4
  have h51 : Real.rpow Δ (-t - 9 * ε / 4) / Real.rpow Δ (-2 * t + 5 * ε) =
      Real.rpow Δ (t - 29 * ε / 4) := by
    have h_exp : (-t - 9 * ε / 4) - (-2 * t + 5 * ε) = t - 29 * ε / 4 := by ring
    have h_sub' := h_rpow_sub (-t - 9 * ε / 4) (-2 * t + 5 * ε)
    rw [h_sub', h_exp]
  have h4 : C_U * Real.rpow Δ (-t - 9 * ε / 4) /
        (Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2) =
      (C_U * C_m ^ 2) * Real.rpow Δ (t - 29 * ε / 4) := by
    have h_pos2' : 0 < Real.rpow Δ (-2 * t + 5 * ε) := h_pos2
    have h_eq1 : C_U * Real.rpow Δ (-t - 9 * ε / 4) /
          (Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2) =
        (C_U * C_m ^ 2) * (Real.rpow Δ (-t - 9 * ε / 4) / Real.rpow Δ (-2 * t + 5 * ε)) := by
      field_simp [h_pos2'.ne', hCm_pos.ne'] <;> ring
    rw [h_eq1, h51] <;> ring
  have h6 : Real.rpow Δ (-11 * ε / 4) ≥ C_U * C_m ^ 2 := by
    have h71 : (-11 * ε / 4 : ℝ) = -(11 * ε / 4) := by ring
    have h72 : Real.rpow Δ (-11 * ε / 4) = (Real.rpow Δ (11 * ε / 4))⁻¹ := by
      rw [h71]; exact Real.rpow_neg hΔ_pos.le (11 * ε / 4)
    rw [h72]
    have h_pos : 0 < Real.rpow Δ (11 * ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
    have h_pos2 : 0 < C_U * C_m ^ 2 := mul_pos hCU_pos (pow_pos hCm_pos 2)
    have h9 : (Real.rpow Δ (11 * ε / 4))⁻¹ ≥ (1 / (C_U * C_m ^ 2))⁻¹ := by
      have h10 : Real.rpow Δ (11 * ε / 4) ≤ 1 / (C_U * C_m ^ 2) := by
        have h11 : C_U * C_m ^ 2 * Real.rpow Δ (11 * ε / 4) ≤ 1 := h_absorb
        have h12 : 0 < C_U * C_m ^ 2 := h_pos2
        have h13 : Real.rpow Δ (11 * ε / 4) ≤ 1 / (C_U * C_m ^ 2) := by
          calc Real.rpow Δ (11 * ε / 4)
            = (C_U * C_m ^ 2 * Real.rpow Δ (11 * ε / 4)) / (C_U * C_m ^ 2) := by field_simp [h12.ne'] <;> ring
          _ ≤ 1 / (C_U * C_m ^ 2) := by gcongr
        exact h13
      gcongr
    have h10 : (1 / (C_U * C_m ^ 2))⁻¹ = C_U * C_m ^ 2 := by
      field_simp [h_pos2.ne'] <;> ring
    rw [h10] at h9; exact h9
  have h7 : (C_U * C_m ^ 2) * Real.rpow Δ (t - 29 * ε / 4) ≤ Real.rpow Δ (t - 10 * ε) := by
    have h8 : Real.rpow Δ (t - 10 * ε) =
        Real.rpow Δ (t - 29 * ε / 4) * Real.rpow Δ (-11 * ε / 4) := by
      have h_exp2 : (t - 29 * ε / 4) + (-11 * ε / 4) = t - 10 * ε := by ring
      have h_add' := h_rpow_add (t - 29 * ε / 4) (-11 * ε / 4)
      rw [h_add', h_exp2]
    rw [h8]
    have h9 : 0 < Real.rpow Δ (t - 29 * ε / 4) := h_pos4
    nlinarith
  calc U_upper / m₀^2
    ≤ C_U * Real.rpow Δ (-t - 9 * ε / 4) /
          (Real.rpow Δ (-2 * t + 5 * ε) / C_m ^ 2) := h3
  _ = (C_U * C_m ^ 2) * Real.rpow Δ (t - 29 * ε / 4) := h4
  _ ≤ Real.rpow Δ (t - 10 * ε) := h7

end DirecretisedFurstenbergEstimate.Pelican
