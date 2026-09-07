module

/-
  A2 → A3 Bridge

  Derives the hypotheses required by A3_uniformize_canonical from
  A2_Output + A1 data + explicit numerical absorption assumptions.

  Key derivations:
  - hQset_sset_in: weaken constant Δ^{-8ε} → Δ^{-20ε}
  - hKpack_ε: K_pack ≤ Δ^{-ε} (fixed constant, small Δ)
  - hCenter_bound / hDist_le_3: geometric from unit-ball containment
  - h_energy_all: explicit hypothesis (lattice-specific argument needed separately)

  Important downstream note:
  A3 selects Q0 (largest bin) as its output Qset. A3 proves
  |Q0| ≥ |Qset_all| · Δ^ε ≥ Δ^{-t+4ε}. However, A5 requires
  |Q0| ≥ Δ^{-t+3ε}. Since Δ^{-t+4ε} < Δ^{-t+3ε} for 0<Δ<1,
  there is a 1ε cardinality gap at the A3→A5 boundary that must
  be resolved separately (e.g., by relaxing A5's requirement or
  strengthening A3's bin selection).

  Whiteprint node: appendix_a_alternative / a2_to_a3_bridge
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A3_Canonical
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A3_CoarseSquareEnergyBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.EnergyBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HeavySquareRefinement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HeavySquaresToEnergy
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Lagoon (squareCenter point_in_square_close_to_center)
open DirecretisedFurstenbergEstimate.AppendixA3

/-- Weaken IsDeltaSSet constant: if C₁ ≤ C₂, then (δ,s,C₁)-set → (δ,s,C₂)-set. -/
lemma IsDeltaSSet.weaken_C' {X : Type*} [PseudoMetricSpace X] {δ s C₁ C₂ : ℝ} {P : Set X}
    (h : IsDeltaSSet δ s C₁ P) (hC : C₁ ≤ C₂) : IsDeltaSSet δ s C₂ P := by
  rcases h with ⟨hne, hδ, hC₁, hs, h_main⟩
  have hC₂_pos : 0 < C₂ := by linarith
  refine' ⟨hne, hδ, hC₂_pos, hs, _⟩
  intro x r hr
  have h1 := h_main x r hr
  have h2 : ENNReal.ofReal C₁ ≤ ENNReal.ofReal C₂ := ENNReal.ofReal_le_ofReal hC
  calc
    (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ℝ≥0∞)
      ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal P := h1
    _ ≤ ENNReal.ofReal C₂ * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal P := by
      gcongr

/-- Bridge from A2_Output to A3_Output. -/
def A2_to_A3_bridge
    {Δ δ s t ε : ℝ}
    (a1 : A1_Output Δ δ t s ε)
    (a2 : A2_Output Δ δ s t ε)
    -- Basic parameter conditions
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (ht_pos : 0 < t) (ht_lt_two : t < 2)
    (hst : s < t)
    -- A3 numerical conditions
    (hΔ_small : 50000 * (Real.log (1 / Δ) + 1)^3 ≤ Real.rpow Δ (-ε))
    (hΔ_absorb1 : 8 * (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s ≤ Real.rpow Δ (-2 * ε))
    (hΔ_absorb2 : (8 : ℝ) ≤ Real.rpow Δ (s - t - 22 * ε))
    (hs_ge_12ε : 12 * ε ≤ s)
    -- K_pack ≤ Δ^{-ε} (K_pack is a fixed constant from A1; true for sufficiently small Δ)
    (hKpack_le_ε : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a2.Qset),
      (a2.perSquare Q hQ).K_pack ≤ Real.rpow Δ (-ε))
    -- Qset equality (in assembly, a2.Qset = a1.Qset)
    (hQset_eq : a2.Qset = a1.Qset)
    -- C_Q ⊆ C_global
    (hC_Q_sub_global : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a2.Qset),
      (a2.perSquare Q hQ).C_Q ⊆ a2.C_global)
    -- Energy bound for all Qset centers (explicit hypothesis; resolved separately, at -12ε)
    (h_energy_all : ∑ p ∈ (a2.Qset.image (squareCenter Δ)),
        ∑ q ∈ (a2.Qset.image (squareCenter Δ)).erase p, Real.rpow (dist p q) (-s) ≤
        Real.rpow Δ (-12 * ε) * ((a2.Qset.image (squareCenter Δ)).card : ℝ)^2) :
    A3_Output Δ δ s t ε := by
  -- Derive Qset-related facts from a1 using hQset_eq
  have hQset_sset_A1 : IsDeltaSSet Δ t (Real.rpow Δ (-15 * ε)) (a2.Qset : Set (CoarseSquare Δ)) := by
    rw [hQset_eq]
    exact a1.hQset_sset
  have hQset_card_lower_A3 : (a2.Qset.card : ℝ) ≥ Real.rpow Δ (-t + 3 * ε) := by
    rw [hQset_eq]
    exact a1.hQset_card_lower
  have hQset_card_upper_A3 : (a2.Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε) := by
    rw [hQset_eq]
    exact a1.hQset_card_upper
  have h_squares_in_ball : ∀ Q ∈ a2.Qset, ∃ p : Plane, p ∈ squareSet Δ Q ∧ ‖p‖ ≤ Real.sqrt 2 := by
    intro Q hQ
    have hQ1 : Q ∈ a1.Qset := by rwa [hQset_eq] at hQ
    have hcard : 0 < (a1.points Q hQ1).card := by
      have h2 : 0 < Real.rpow Δ (-t + 3 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have h3 : Real.rpow Δ (-t + 3 * ε) ≤ (a1.points Q hQ1).card := a1.h_points_card_lower Q hQ1
      have h4 : (0 : ℝ) < (a1.points Q hQ1).card := by linarith
      exact_mod_cast h4
    have hP_nonempty : (a1.points Q hQ1).Nonempty := Finset.card_pos.mp hcard
    rcases hP_nonempty with ⟨p, hp⟩
    have hp_sq : p ∈ squareSet Δ Q := a1.h_points_in_square Q hQ1 p hp
    have hp_ball : p ∈ Metric.closedBall (0 : Plane) (Real.sqrt 2) := a1.h_points_in_ball Q hQ1 hp
    have hp_norm : ‖p‖ ≤ Real.sqrt 2 := by simpa [Metric.mem_closedBall] using hp_ball
    exact ⟨p, hp_sq, hp_norm⟩

  -- Tighter center norm bound: ‖center Q‖ ≤ √2 + √2 * Δ / 2
  have hCenter_bound_tight : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a2.Qset),
      ‖squareCenter Δ Q‖ ≤ Real.sqrt 2 + Real.sqrt 2 * Δ / 2 := by
    intro Q hQ
    rcases h_squares_in_ball Q hQ with ⟨p, hp_sq, hp_norm⟩
    have hdist : dist p (squareCenter Δ Q) ≤ Real.sqrt 2 * Δ / 2 :=
      point_in_square_close_to_center hΔ_pos Q p hp_sq
    have h1 : ‖squareCenter Δ Q‖ ≤ ‖p‖ + ‖squareCenter Δ Q - p‖ := by
      calc
        ‖squareCenter Δ Q‖ = ‖p + (squareCenter Δ Q - p)‖ := by simp [add_sub_cancel]
        _ ≤ ‖p‖ + ‖squareCenter Δ Q - p‖ := norm_add_le p (squareCenter Δ Q - p)
    have h2 : ‖squareCenter Δ Q - p‖ = dist p (squareCenter Δ Q) := by
      rw [dist_eq_norm, norm_sub_rev]
    have h3 : ‖squareCenter Δ Q‖ ≤ ‖p‖ + dist p (squareCenter Δ Q) := by
      rw [h2] at h1
      exact h1
    linarith [hp_norm, hdist]

  -- Prove Δ < 3/√2 - 2 from hΔ_small: for Δ ≥ 3/√2 - 2, LHS > 50000 but RHS < 10
  have h_c_pos : 0 < 3 / Real.sqrt 2 - 2 := by
    have h1 : (3 : ℝ) > 2 * Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h2 : (3 : ℝ) / Real.sqrt 2 > 2 := by
      have h3 : 0 < Real.sqrt 2 := by positivity
      have h4 : (3 : ℝ) > 2 * Real.sqrt 2 := h1
      have h5 : (3 : ℝ) / Real.sqrt 2 > (2 * Real.sqrt 2) / Real.sqrt 2 := by gcongr
      have h6 : (2 * Real.sqrt 2) / Real.sqrt 2 = 2 := by
        field_simp [h3.ne'] <;> ring
      rw [h6] at h5
      exact h5
    linarith
  have h_c_gt_tenth : 3 / Real.sqrt 2 - 2 > 1 / 10 := by
    have h1 : (3 : ℝ) > (21 / 10 : ℝ) * Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h2 : 0 < Real.sqrt 2 := by positivity
    have h3 : (3 : ℝ) / Real.sqrt 2 > 21 / 10 := by
      have h4 : (3 : ℝ) / Real.sqrt 2 > ((21 / 10 : ℝ) * Real.sqrt 2) / Real.sqrt 2 := by gcongr
      have h5 : ((21 / 10 : ℝ) * Real.sqrt 2) / Real.sqrt 2 = (21 / 10 : ℝ) := by
        field_simp [h2.ne'] <;> ring
      rw [h5] at h4
      exact h4
    linarith
  have hΔ_lt_c : Δ < 3 / Real.sqrt 2 - 2 := by
    by_contra h
    have hge : Δ ≥ 3 / Real.sqrt 2 - 2 := by linarith
    have h_log_pos : 0 < Real.log (1 / Δ) := by
      have h1 : 1 < 1 / Δ := by
        have h2 : Δ < 1 := by linarith
        apply one_lt_one_div
        <;> linarith
      exact Real.log_pos h1
    have h_lhs_gt : 50000 * (Real.log (1 / Δ) + 1)^3 > 50000 := by
      have h3 : 1 < Real.log (1 / Δ) + 1 := by linarith
      have h4 : 0 < Real.log (1 / Δ) + 1 := by linarith
      have h5 : 1 < (Real.log (1 / Δ) + 1)^3 := by
        have h6 : (1 : ℝ) < Real.log (1 / Δ) + 1 := h3
        have h7 : (1 : ℝ)^3 < (Real.log (1 / Δ) + 1)^3 := by gcongr
        simpa using h7
      nlinarith
    have h_rhs_lt : Real.rpow Δ (-ε) < 50000 := by
      have h1 : Real.rpow Δ (-ε) = (1 / Δ)^ε := by
        have hlog : Real.log (1 / Δ) = - Real.log Δ := by
          rw [Real.log_div (by positivity) (by positivity)] <;> simp
        have h_eq1 : Real.rpow Δ (-ε) = Real.exp (Real.log Δ * (-ε)) := by
          simpa using Real.rpow_def_of_pos hΔ_pos (-ε)
        have h_pos2 : 0 < (1 / Δ) := by positivity
        have h_eq2 : (1 / Δ)^ε = Real.exp (Real.log (1 / Δ) * ε) :=
          Real.rpow_def_of_pos h_pos2 ε
        have h_comm1 : Real.exp (Real.log Δ * (-ε)) = Real.exp ((-ε) * Real.log Δ) := by
          rw [mul_comm (Real.log Δ) (-ε)]
        have h_comm2 : Real.exp (Real.log (1 / Δ) * ε) = Real.exp (ε * Real.log (1 / Δ)) := by
          rw [mul_comm (Real.log (1 / Δ)) ε]
        rw [h_eq1, h_comm1, h_eq2, h_comm2, hlog] <;> ring_nf
      rw [h1]
      have h4 : 1 ≤ 1 / Δ := by
        have h5 : Δ ≤ 1 := by linarith
        apply one_le_one_div <;> linarith
      have hε_le_one' : ε ≤ 1 := by linarith
      have h5 : (1 / Δ)^ε ≤ (1 / Δ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h4 hε_le_one'
      have h5' : (1 / Δ)^(1 : ℝ) = 1 / Δ := by
        rw [Real.rpow_one]
      rw [h5'] at h5
      have h6 : 1 / Δ ≤ 1 / (3 / Real.sqrt 2 - 2) := by
        gcongr <;> linarith
      have h_pos_c : 0 < 3 / Real.sqrt 2 - 2 := h_c_pos
      have h7 : 1 / (3 / Real.sqrt 2 - 2) < 10 := by
        have h8 : 1 / 10 < 3 / Real.sqrt 2 - 2 := h_c_gt_tenth
        have h9 : (0 : ℝ) < 1 / 10 := by norm_num
        have h10 : 1 / (3 / Real.sqrt 2 - 2) < 1 / (1 / 10 : ℝ) := one_div_lt_one_div_of_lt h9 h8
        have h11 : (1 / (1 / 10 : ℝ)) = 10 := by norm_num
        rw [h11] at h10
        exact h10
      have h12 : (1 / Δ)^ε < 50000 := by
        calc
          (1 / Δ)^ε ≤ 1 / Δ := h5
          _ ≤ 1 / (3 / Real.sqrt 2 - 2) := h6
          _ < 10 := h7
          _ < 50000 := by norm_num
      exact h12
    have h_contra : 50000 * (Real.log (1 / Δ) + 1)^3 ≤ Real.rpow Δ (-ε) := hΔ_small
    have h_gt : 50000 * (Real.log (1 / Δ) + 1)^3 > Real.rpow Δ (-ε) := by
      calc
        50000 * (Real.log (1 / Δ) + 1)^3 > 50000 := h_lhs_gt
        _ > Real.rpow Δ (-ε) := h_rhs_lt
    exact False.elim (not_le.mpr h_gt h_contra)


  -- Step 1: Weaken Qset S-set constant from Δ^{-15ε} to Δ^{-20ε}
  have h15_le_20 : Real.rpow Δ (-15 * ε) ≤ Real.rpow Δ (-20 * ε) := by
    have h1 : -15 * ε ≥ -20 * ε := by linarith
    have h2 : Δ < 1 := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos h2.le h1
  have hQset_sset_in : IsDeltaSSet Δ t (Real.rpow Δ (-20 * ε)) (a2.Qset : Set (CoarseSquare Δ)) :=
    IsDeltaSSet.weaken_C' hQset_sset_A1 h15_le_20

  -- Step 2: K_pack bound: directly from hypothesis
  -- (K_pack is the fixed affineLine_packing_constant; for small Δ it is ≤ Δ^{-ε})
  have hKpack_ε : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a2.Qset),
      (a2.perSquare Q hQ).K_pack ≤ Real.rpow Δ (-ε) := hKpack_le_ε

  -- Step 3: Geometric bound on square center norm
  have hCenter_bound : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a2.Qset),
      ‖squareCenter Δ Q‖ ≤ 2 := by
    intro Q hQ
    rcases h_squares_in_ball Q hQ with ⟨p, hp_sq, hp_norm⟩
    have hdist : dist p (squareCenter Δ Q) ≤ Real.sqrt 2 * Δ / 2 :=
      point_in_square_close_to_center hΔ_pos Q p hp_sq
    have h1 : ‖squareCenter Δ Q‖ ≤ ‖p‖ + ‖squareCenter Δ Q - p‖ := by
      have h_eq : p + (squareCenter Δ Q - p) = squareCenter Δ Q := by simp [add_sub_cancel]
      have h_norm_eq : ‖p + (squareCenter Δ Q - p)‖ = ‖squareCenter Δ Q‖ := by rw [h_eq]
      have h : ‖squareCenter Δ Q‖ = ‖p + (squareCenter Δ Q - p)‖ := h_norm_eq.symm
      rw [h]
      exact norm_add_le _ _
    have h2 : ‖squareCenter Δ Q - p‖ = dist p (squareCenter Δ Q) := by
      have h3 : ‖squareCenter Δ Q - p‖ = ‖p - squareCenter Δ Q‖ := by
        rw [show squareCenter Δ Q - p = -(p - squareCenter Δ Q) from by abel]
        rw [norm_neg]
      rw [h3, dist_eq_norm]
    rw [h2] at h1
    have h3 : ‖squareCenter Δ Q‖ ≤ ‖p‖ + dist p (squareCenter Δ Q) := h1
    have h4 : ‖p‖ + dist p (squareCenter Δ Q) ≤ Real.sqrt 2 + Real.sqrt 2 * Δ / 2 := by
      gcongr
      <;> linarith [hp_norm, hdist]
    have h5 : Real.sqrt 2 + Real.sqrt 2 * Δ / 2 ≤ 2 := by
      have h6 : Δ ≤ 1 / 2 := by linarith
      have h_sqrt2_pos : 0 < Real.sqrt 2 := by positivity
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith

  -- Step 4: Distance between any two square centers ≤ 3
  -- Using tight center norm bound and Δ < 3/√2 - 2
  have hDist_le_3 : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a2.Qset)
      (R : CoarseSquare Δ) (hR : R ∈ a2.Qset),
      dist (squareCenter Δ Q) (squareCenter Δ R) ≤ 3 := by
    intro Q hQ R hR
    have h1 : ‖squareCenter Δ Q‖ ≤ Real.sqrt 2 + Real.sqrt 2 * Δ / 2 := hCenter_bound_tight Q hQ
    have h2 : ‖squareCenter Δ R‖ ≤ Real.sqrt 2 + Real.sqrt 2 * Δ / 2 := hCenter_bound_tight R hR
    have h3 : dist (squareCenter Δ Q) (squareCenter Δ R) ≤ ‖squareCenter Δ Q‖ + ‖squareCenter Δ R‖ := by
      rw [dist_eq_norm]
      exact norm_sub_le _ _
    have h4 : ‖squareCenter Δ Q‖ + ‖squareCenter Δ R‖ ≤ 2 * (Real.sqrt 2 + Real.sqrt 2 * Δ / 2) := by linarith
    have h5 : 2 * (Real.sqrt 2 + Real.sqrt 2 * Δ / 2) ≤ 3 := by
      have h6 : 2 * (Real.sqrt 2 + Real.sqrt 2 * Δ / 2) = 2 * Real.sqrt 2 + Real.sqrt 2 * Δ := by ring
      rw [h6]
      have h7 : Δ ≤ 3 / Real.sqrt 2 - 2 := by linarith [hΔ_lt_c]
      have h_sqrt2_pos : 0 < Real.sqrt 2 := by positivity
      have h9 : Real.sqrt 2 * Δ ≤ Real.sqrt 2 * (3 / Real.sqrt 2 - 2) := by
        gcongr
        <;> linarith
      have h10 : Real.sqrt 2 * (3 / Real.sqrt 2 - 2) = 3 - 2 * Real.sqrt 2 := by
        have h11 : Real.sqrt 2 * (3 / Real.sqrt 2 - 2) = Real.sqrt 2 * (3 / Real.sqrt 2) - Real.sqrt 2 * 2 := by ring
        rw [h11]
        have h12 : Real.sqrt 2 * (3 / Real.sqrt 2) = 3 := by
          field_simp [h_sqrt2_pos.ne'] <;> ring
        rw [h12] <;> ring
      have h13 : Real.sqrt 2 * Δ ≤ 3 - 2 * Real.sqrt 2 := by
        linarith [h9, h10]
      linarith
    linarith

  -- Step 5: Energy bound is provided as explicit hypothesis h_energy_all.
  -- See `energy_all_from_a1_with_witness` below for how to discharge it
  -- using dune's EnergyBound lemmas plus a constant absorption hypothesis.

  -- Step 6: Call A3_uniformize_canonical
  exact A3_uniformize_canonical
    Δ δ s t ε hΔ_pos hΔ_lt_half hδ_pos hδ_le_Δ
    hε_pos hε_lt_one hs_pos hs_lt_one ht_pos ht_lt_two hst
    hΔ_small hΔ_absorb1 hΔ_absorb2 hs_ge_12ε
    a2 hQset_sset_in a2.hC_global_card_upper hC_Q_sub_global
    hCenter_bound hDist_le_3 hQset_card_lower_A3 hQset_card_upper_A3 h_energy_all hKpack_ε
    a2.hQset_phys_growth

/-- **Energy bound witness lemma**.

    Chains dune's `center_ball_growth_from_a1` and `energy_bound_from_ball_growth`
    to produce an explicit constant `C_energy` such that, if
    `C_energy ≤ Δ^{-4ε}`, then the required `h_energy_all` holds.

    The constant `C_energy` is independent of Δ in the sense that it equals
    `K_total * Cball * Δ^{6ε}`, where `K_total` and `Cball` come from dune's
    lemmas. For fixed s,t, `C_energy` is bounded by a fixed constant
    (depending on packing constants and parameter values), so
    `constant_absorbable C_energy (4*ε)` shows the absorption holds
    for sufficiently small Δ.

    Use this lemma to discharge `h_energy_all` in `A2_to_A3_bridge`. -/
lemma energy_all_from_a1_with_witness
    {Δ δ s t ε : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hδ_pos : 0 < δ) (hδ_eq : δ = Δ ^ 2)
    (h_small_delta : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (hε_pos : 0 < ε)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (ht_pos : 0 < t) (ht_lt_two : t < 2) (hst : s < t)
    (a1 : A1_Output Δ δ t s ε)
    (h_center_bdd : ∀ Q ∈ a1.Qset, ‖squareCenter Δ Q‖ ≤ 2)
    (hQset_nonempty : a1.Qset.Nonempty) :
    ∃ (C_energy : ℝ), 0 < C_energy ∧
      C_energy = (MainAppendix.plane_energy_constant s t 2) * (MainAppendix.plane_packing_constant : ℝ) * Real.rpow Δ (-3 * ε) ∧
      (C_energy ≤ Real.rpow Δ (-4 * ε) →
        ∑ p ∈ (a1.Qset.image (squareCenter Δ)),
          ∑ q ∈ (a1.Qset.image (squareCenter Δ)).erase p,
            Real.rpow (dist p q) (-s) ≤
          Real.rpow Δ (-12 * ε) * ((a1.Qset.image (squareCenter Δ)).card : ℝ)^2) := by
  let centers := a1.Qset.image (squareCenter Δ)
  have hδ_le_Δ : δ ≤ Δ := by
    rw [hδ_eq]
    have h : Δ ^ 2 ≤ Δ := by
      have h2 : Δ < 1 := by linarith
      nlinarith
    exact h
  have hR_pos : 0 < (2 : ℝ) := by norm_num
  have h_sep : Set.Pairwise (centers : Set Plane) (fun p p' => Δ ≤ dist p p') :=
    squareCenters_separated hΔ_pos
  have h_bdd : ∀ p ∈ centers, ‖p‖ ≤ 2 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨Q, hQ, rfl⟩
    exact h_center_bdd Q hQ
  have h_rpow8_pos : 0 < Real.rpow Δ (8 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  have h_rpow_neg8_pos : 0 < Real.rpow Δ (-8 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  have h_rpow_neg6_pos : 0 < Real.rpow Δ (-6 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  have h_rpow_neg12_pos : 0 < Real.rpow Δ (-12 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  -- Step 1: Ball-growth bound from A1
  rcases center_ball_growth_from_a1 hΔ_pos hδ_pos hδ_le_Δ hε_pos (by linarith) a1
    with ⟨Cball, hCball_pos, hCball_eq, h_ball⟩
  -- Step 2: Energy bound from ball-growth
  rcases energy_bound_from_ball_growth hΔ_pos hs_pos hst hR_pos hCball_pos
    hQset_nonempty h_sep h_bdd h_ball
    with ⟨K_total, hK_pos, hK_total_eq, hE⟩
  -- Step 3: Define witness constant C_energy = K_total * Cball * Δ^{6ε}
  let C_energy : ℝ := K_total * Cball * Real.rpow Δ (8 * ε)
  have hC_energy_pos : 0 < C_energy := mul_pos (mul_pos hK_pos hCball_pos) h_rpow8_pos
  have hC_energy_eq : C_energy = (MainAppendix.plane_energy_constant s t 2) * (MainAppendix.plane_packing_constant : ℝ) * Real.rpow Δ (-3 * ε) := by
    dsimp only [C_energy]
    rw [hK_total_eq, hCball_eq]
    have h : Real.rpow Δ (-11 * ε) * Real.rpow Δ (8 * ε) = Real.rpow Δ ((-11 * ε) + (8 * ε)) := by
      exact (Real.rpow_add hΔ_pos (-11 * ε) (8 * ε)).symm
    have h2 : (-11 * ε) + (8 * ε) = -3 * ε := by ring
    have h3 : Real.rpow Δ (-11 * ε) * Real.rpow Δ (8 * ε) = Real.rpow Δ (-3 * ε) := by
      rw [h, h2]
    have h4 : (MainAppendix.plane_energy_constant s t 2) * (MainAppendix.plane_packing_constant : ℝ) * Real.rpow Δ (-11 * ε) * Real.rpow Δ (8 * ε) =
        (MainAppendix.plane_energy_constant s t 2) * (MainAppendix.plane_packing_constant : ℝ) * Real.rpow Δ (-3 * ε) := by
      have h5 : (MainAppendix.plane_energy_constant s t 2) * (MainAppendix.plane_packing_constant : ℝ) * Real.rpow Δ (-11 * ε) * Real.rpow Δ (8 * ε) =
          (MainAppendix.plane_energy_constant s t 2) * (MainAppendix.plane_packing_constant : ℝ) * (Real.rpow Δ (-11 * ε) * Real.rpow Δ (8 * ε)) := by ring
      rw [h5, h3]
    exact h4
  refine' ⟨C_energy, hC_energy_pos, hC_energy_eq, _⟩
  intro h_absorb
  have h_rpow_mul1 : Real.rpow Δ (8 * ε) * Real.rpow Δ (-8 * ε) = 1 := by
    have h := Real.rpow_add hΔ_pos (8 * ε) (-8 * ε)
    have h_sum : (8 * ε) + (-8 * ε) = 0 := by ring
    have h1 : Real.rpow Δ ((8 * ε) + (-8 * ε)) = Real.rpow Δ (8 * ε) * Real.rpow Δ (-8 * ε) := h
    rw [h_sum] at h1
    have h2 : Real.rpow Δ (8 * ε) * Real.rpow Δ (-8 * ε) = Real.rpow Δ 0 := h1.symm
    have h3 : Real.rpow Δ 0 = 1 := by simp
    exact Eq.trans h2 h3
  have h_rpow_mul2 : Real.rpow Δ (-4 * ε) * Real.rpow Δ (-8 * ε) = Real.rpow Δ (-12 * ε) := by
    have h := Real.rpow_add hΔ_pos (-4 * ε) (-8 * ε)
    have h_sum : (-4 * ε) + (-8 * ε) = -12 * ε := by ring
    rw [h_sum] at h
    exact h.symm
  have h9 : K_total * Cball ≤ Real.rpow Δ (-12 * ε) := by
    have h10 : K_total * Cball = C_energy * Real.rpow Δ (-8 * ε) := by
      dsimp only [C_energy]
      have h11 : (K_total * Cball * Real.rpow Δ (8 * ε)) * Real.rpow Δ (-8 * ε) =
               K_total * Cball := by
        calc
          (K_total * Cball * Real.rpow Δ (8 * ε)) * Real.rpow Δ (-8 * ε)
            = K_total * Cball * (Real.rpow Δ (8 * ε) * Real.rpow Δ (-8 * ε)) := by ring
          _ = K_total * Cball * 1 := by rw [h_rpow_mul1]
          _ = K_total * Cball := by ring
      exact h11.symm
    rw [h10]
    have h13 : 0 ≤ Real.rpow Δ (-8 * ε) := le_of_lt h_rpow_neg8_pos
    have h14 : C_energy * Real.rpow Δ (-8 * ε) ≤
              Real.rpow Δ (-4 * ε) * Real.rpow Δ (-8 * ε) :=
      mul_le_mul_of_nonneg_right h_absorb h13
    rw [h_rpow_mul2] at h14
    exact h14
  calc
    (∑ p ∈ centers, ∑ q ∈ centers.erase p, Real.rpow (dist p q) (-s))
      ≤ K_total * Cball * (centers.card : ℝ)^2 := hE
    _ ≤ Real.rpow Δ (-12 * ε) * (centers.card : ℝ)^2 := by
      exact mul_le_mul_of_nonneg_right h9 (by positivity)

/-- Exact `Δ^{-12ε}` energy bound for Qset centers from A1 output.

    This is a convenience wrapper around `energy_all_from_a1_with_witness`
    that absorbs the geometric constant `plane_energy_constant * plane_packing_constant`
    into `Δ^{-ε}`.

    Supply the conclusion directly as `h_energy_all` to `linkedA2_to_A4_v2`.

    The absorption hypothesis `h_absorb_energy` is satisfiable for sufficiently
    small `Δ` because the LHS is a fixed constant depending only on `s, t`. -/
lemma energy_all_from_a1_exact
    {Δ δ s t ε : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hδ_pos : 0 < δ) (hδ_eq : δ = Δ ^ 2)
    (h_small_delta : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (hε_pos : 0 < ε)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (ht_pos : 0 < t) (ht_lt_two : t < 2) (hst : s < t)
    (a1 : A1_Output Δ δ t s ε)
    (h_center_bdd : ∀ Q ∈ a1.Qset, ‖squareCenter Δ Q‖ ≤ 2)
    (hQset_nonempty : a1.Qset.Nonempty)
    (h_absorb_energy :
      (MainAppendix.plane_energy_constant s t 2) *
      (MainAppendix.plane_packing_constant : ℝ) ≤ Real.rpow Δ (-ε)) :
    ∑ p ∈ (a1.Qset.image (squareCenter Δ)),
      ∑ q ∈ (a1.Qset.image (squareCenter Δ)).erase p,
        Real.rpow (dist p q) (-s) ≤
      Real.rpow Δ (-12 * ε) * ((a1.Qset.image (squareCenter Δ)).card : ℝ)^2 := by
  rcases energy_all_from_a1_with_witness hΔ_pos hΔ_lt_half hδ_pos hδ_eq
      h_small_delta hε_pos hs_pos hs_lt_one ht_pos ht_lt_two hst
      a1 h_center_bdd hQset_nonempty
    with ⟨C_energy, hC_pos, hC_eq, h_main⟩
  have h_absorb : C_energy ≤ Real.rpow Δ (-4 * ε) := by
    rw [hC_eq]
    have h_rpow_neg3_pos : 0 < Real.rpow Δ (-3 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h1 : (MainAppendix.plane_energy_constant s t 2) *
               (MainAppendix.plane_packing_constant : ℝ) * Real.rpow Δ (-3 * ε) ≤
             Real.rpow Δ (-ε) * Real.rpow Δ (-3 * ε) := by
      gcongr
      <;> linarith
    have h2 : Real.rpow Δ (-ε) * Real.rpow Δ (-3 * ε) = Real.rpow Δ (-4 * ε) := by
      have h21 : Real.rpow Δ ((-ε) + (-3 * ε)) = Real.rpow Δ (-ε) * Real.rpow Δ (-3 * ε) :=
        Real.rpow_add hΔ_pos (-ε) (-3 * ε)
      have h22 : (-ε) + (-3 * ε) = -4 * ε := by ring
      rw [h22] at h21
      exact h21.symm
    rw [h2] at h1
    exact h1
  exact h_main h_absorb

end DirecretisedFurstenbergEstimate.AppendixA
