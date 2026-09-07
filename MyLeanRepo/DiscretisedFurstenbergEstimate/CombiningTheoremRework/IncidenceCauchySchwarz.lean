module

/-
  Incidence Cauchy-Schwarz lemmas for the base case.

  Provides:
  1. `sset_lower_bound`: covering number lower bound from S-set property
  2. `incidence_cauchy_schwarz_largeN`: diagonal-dominated case → |T| ≥ N·M/8
  3. `incidence_cauchy_schwarz_smallM`: off-diagonal-dominated case → |T| ≥ M²·δ^{-s}/C

  Whiteprint node: combining_theorem_rework / incidence_cauchy_schwarz
  Dependencies: Global2sBoundNoHLarge (cauchy_schwarz_card, sum_weighted_fiber)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Global2sBoundNoHLarge
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DirecretisedFurstenbergEstimate.Global2sBound

/-- Lower bound on covering number from S-set property. -/
lemma sset_lower_bound {X : Type*} [PseudoMetricSpace X]
    {δ s C : ℝ} {P : Set X} (hP : IsDeltaSSet δ s C P) :
    (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≥ ENNReal.ofReal (1 / (C * δ^s)) := by
  have h1 : P.Nonempty := hP.1
  have h2 : 0 < δ := hP.2.1
  have h3 : 0 < C := hP.2.2.1
  have h4 : 0 ≤ s := hP.2.2.2.1
  rcases h1 with ⟨p, hp⟩
  have h5 : p ∈ P ∩ Metric.closedBall p δ := by
    simp [hp, dist_self] <;> linarith
  have h6 : ({p} : Set X) ⊆ P ∩ Metric.closedBall p δ := by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    rw [hx]
    exact h5
  have h7 : Metric.externalCoveringNumber δ.toNNReal ({p} : Set X) = 1 :=
    Metric.externalCoveringNumber_eq_one_of_ediam_le (Set.singleton_nonempty p) (by simp)
  have h8 : (Metric.externalCoveringNumber δ.toNNReal ({p} : Set X) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall p δ) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set h6
  have h9 : (1 : ENNReal) ≤ (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall p δ) : ENNReal) := by
    have h91 : (Metric.externalCoveringNumber δ.toNNReal ({p} : Set X) : ENNReal) = (1 : ENNReal) := by
      exact_mod_cast h7
    rw [h91] at h8
    exact h8
  have h10 := hP.2.2.2.2 p δ (by linarith)
  have h11 : 0 ≤ C := by linarith
  have h13 : ENNReal.ofReal C * (ENNReal.ofReal δ)^s = ENNReal.ofReal (C * δ^s) := by
    have h14 : (ENNReal.ofReal δ)^s = ENNReal.ofReal (δ^s) := by
      exact ENNReal.ofReal_rpow_of_pos h2
    rw [h14]
    have h15 : ENNReal.ofReal C * ENNReal.ofReal (δ^s) = ENNReal.ofReal (C * δ^s) := by
      rw [← ENNReal.ofReal_mul h11] <;> ring
    exact h15
  rw [h13] at h10
  have h14 : (1 : ENNReal) ≤ ENNReal.ofReal (C * δ^s) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) :=
    le_trans h9 h10
  have h15 : 0 < C * δ^s := by
    have h16 : 0 < δ^s := Real.rpow_pos_of_pos h2 s
    positivity
  have h17 : ENNReal.ofReal (C * δ^s) ≠ 0 := by
    have h171 : (0 : ENNReal) < ENNReal.ofReal (C * δ^s) := by
      apply ENNReal.ofReal_pos.mpr
      exact h15
    exact ne_of_gt h171
  have h18 : ENNReal.ofReal (1 / (C * δ^s)) = (ENNReal.ofReal (C * δ^s))⁻¹ := by
    have h19 : ENNReal.ofReal (1 / (C * δ^s)) = ENNReal.ofReal ((C * δ^s)⁻¹) := by ring_nf
    rw [h19]
    rw [ENNReal.ofReal_inv_of_pos h15]
  have h19 : (ENNReal.ofReal (C * δ^s))⁻¹ * (1 : ENNReal) ≤ (ENNReal.ofReal (C * δ^s))⁻¹ * (ENNReal.ofReal (C * δ^s) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal)) := by
    gcongr
  have h20 : (ENNReal.ofReal (C * δ^s))⁻¹ * (ENNReal.ofReal (C * δ^s) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal)) =
      (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
    have h21 : (ENNReal.ofReal (C * δ^s))⁻¹ * ENNReal.ofReal (C * δ^s) = 1 := by
      rw [ENNReal.inv_mul_cancel] <;> simp [h17] <;> norm_num
    rw [← mul_assoc, h21, one_mul]
  have h22 : (ENNReal.ofReal (C * δ^s))⁻¹ ≤ (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
    calc (ENNReal.ofReal (C * δ^s))⁻¹
      = (ENNReal.ofReal (C * δ^s))⁻¹ * (1 : ENNReal) := by simp
    _ ≤ (ENNReal.ofReal (C * δ^s))⁻¹ * (ENNReal.ofReal (C * δ^s) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal)) := h19
    _ = (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h20
  rw [h18]
  exact h22

/-- Generic Cauchy-Schwarz incidence setup: computes I = ∑|Tp p|, E = ∑d(ℓ)². -/
lemma incidence_energy_setup
    {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    {P : Finset X} {Tp : X → Finset Tube} {M : ℝ}
    (hP_nonempty : P.Nonempty)
    (hTp_card_lower : ∀ p ∈ P, (M / 2 : ℝ) ≤ (Tp p).card)
    (hTp_card_upper : ∀ p ∈ P, (Tp p).card ≤ M)
    (hM_pos : 0 < M) :
    let N : ℝ := (P.card : ℝ)
    let U : Finset Tube := P.biUnion Tp
    let d : Tube → ℕ := fun ℓ => (P.filter (fun p => ℓ ∈ Tp p)).card
    (0 < N) ∧
    ((∑ ℓ ∈ U, (d ℓ : ℝ)) = (∑ p ∈ P, (Tp p).card : ℝ)) ∧
    ((∑ p ∈ P, (Tp p).card : ℝ) ≥ N * M / 2) ∧
    ((∑ p ∈ P, (Tp p).card : ℝ) ≤ N * M) ∧
    ((∑ ℓ ∈ U, (d ℓ : ℝ)^2) = ∑ p ∈ P, ∑ q ∈ P, (((Tp p) ∩ (Tp q)).card : ℝ)) ∧
    (∑ p ∈ P, ∑ q ∈ P, (((Tp p) ∩ (Tp q)).card : ℝ) =
      (∑ p ∈ P, ((Tp p).card : ℝ)) + ∑ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ)) := by
  let N : ℝ := (P.card : ℝ)
  let U : Finset Tube := P.biUnion Tp
  let d : Tube → ℕ := fun ℓ => (P.filter (fun p => ℓ ∈ Tp p)).card
  have hN_pos : 0 < N := by
    dsimp only [N]
    have h : 0 < P.card := Finset.card_pos.mpr hP_nonempty
    have h' : (0 : ℝ) < (P.card : ℝ) := by exact_mod_cast h
    exact h'
  have hTp_sub : ∀ p ∈ P, Tp p ⊆ U := by
    intro p hp ℓ hℓ
    exact Finset.mem_biUnion.mpr ⟨p, hp, hℓ⟩
  have hI_eq : (∑ ℓ ∈ U, (d ℓ : ℝ)) = (∑ p ∈ P, (Tp p).card : ℝ) := by
    have h1 := sum_weighted_fiber (f := fun (_ : Tube) => (1 : ℝ)) hTp_sub
    simpa [d, Finset.sum_const] using h1
  have hI_lower : (∑ p ∈ P, (Tp p).card : ℝ) ≥ N * M / 2 := by
    have h : ∀ p ∈ P, (M / 2 : ℝ) ≤ ((Tp p).card : ℝ) := by
      intro p hp; exact_mod_cast hTp_card_lower p hp
    have h2 : ∑ p ∈ P, (M / 2 : ℝ) ≤ ∑ p ∈ P, ((Tp p).card : ℝ) := Finset.sum_le_sum h
    have h3 : ∑ p ∈ P, (M / 2 : ℝ) = N * M / 2 := by
      simp [Finset.sum_const, mul_comm] <;> ring
    rw [h3] at h2
    exact h2
  have hI_upper : (∑ p ∈ P, (Tp p).card : ℝ) ≤ N * M := by
    have h : ∀ p ∈ P, ((Tp p).card : ℝ) ≤ M := by
      intro p hp; exact_mod_cast hTp_card_upper p hp
    have h2 : ∑ p ∈ P, ((Tp p).card : ℝ) ≤ ∑ p ∈ P, M := Finset.sum_le_sum h
    simpa [Finset.sum_const] using h2
  have h_sum_d2 : (∑ ℓ ∈ U, (d ℓ : ℝ)^2) =
      ∑ p ∈ P, ∑ q ∈ P, (((Tp p) ∩ (Tp q)).card : ℝ) := by
    have h1 : (∑ ℓ ∈ U, (d ℓ : ℝ)^2) = ∑ p ∈ P, ∑ ℓ ∈ Tp p, (d ℓ : ℝ) := by
      have h2 : ∑ ℓ ∈ U, (d ℓ : ℝ)^2 = ∑ ℓ ∈ U, (d ℓ : ℝ) * (d ℓ : ℝ) := by
        apply Finset.sum_congr rfl; intro ℓ _; ring
      rw [h2]
      exact sum_weighted_fiber hTp_sub
    rw [h1]
    apply Finset.sum_congr rfl
    intro p _
    have h3 : ∑ ℓ ∈ Tp p, (d ℓ : ℝ) =
        ∑ q ∈ P, (((Tp p) ∩ (Tp q)).card : ℝ) := by
      have h4 : ∑ ℓ ∈ Tp p, (d ℓ : ℝ) =
          ∑ q ∈ P, ∑ ℓ ∈ Tp p, (if ℓ ∈ Tp q then (1 : ℝ) else 0) := by
        have h5 : ∀ ℓ ∈ Tp p, (d ℓ : ℝ) = ∑ q ∈ P, (if ℓ ∈ Tp q then (1 : ℝ) else 0) := by
          intro ℓ _
          simp [d, Finset.filter_eq'] <;> ring
        rw [Finset.sum_congr rfl h5]
        rw [Finset.sum_comm]
      rw [h4]
      apply Finset.sum_congr rfl
      intro q _
      simp [Finset.sum_ite, Finset.mem_inter] <;> ring
    exact h3
  have h_split : ∑ p ∈ P, ∑ q ∈ P, (((Tp p) ∩ (Tp q)).card : ℝ) =
      (∑ p ∈ P, ((Tp p).card : ℝ)) + ∑ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ) := by
    have h_per_p : ∀ p ∈ P, ∑ q ∈ P, (((Tp p) ∩ (Tp q)).card : ℝ) =
        ((Tp p).card : ℝ) + ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ) := by
      intro p hp
      let f : X → ℝ := fun q => ((Tp p) ∩ (Tp q)).card
      have h_sum : f p + ∑ q ∈ P.erase p, f q = ∑ q ∈ P, f q := by exact Finset.add_sum_erase P f hp
      have h5 : ∑ q ∈ P, (((Tp p) ∩ (Tp q)).card : ℝ) =
          (((Tp p) ∩ (Tp p)).card : ℝ) + ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ) := by
        exact h_sum.symm
      rw [h5] <;> simp
    have h_step1 : ∑ p ∈ P, ∑ q ∈ P, (((Tp p) ∩ (Tp q)).card : ℝ) =
        ∑ p ∈ P, (((Tp p).card : ℝ) + ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ)) := by
      exact Finset.sum_congr rfl (fun p hp => h_per_p p hp)
    have h_step2 : ∑ p ∈ P, (((Tp p).card : ℝ) + ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ)) =
        (∑ p ∈ P, ((Tp p).card : ℝ)) + ∑ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ) := by
      rw [Finset.sum_add_distrib]
    rw [h_step1, h_step2]
  exact ⟨hN_pos, hI_eq, hI_lower, hI_upper, h_sum_d2, h_split⟩

/-- Incidence Cauchy-Schwarz: diagonal-dominated (large N) case.

    Given diagonal dominance N ≥ C_cross·δ^s·K_energy·C_P·N²,
    then |T| ≥ N·M/8. -/
lemma incidence_cauchy_schwarz_largeN
    {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    {δ s C_P C_cross K_energy M : ℝ}
    (hδ_pos : 0 < δ) (hs : 0 ≤ s)
    (hCP_pos : 0 < C_P) (hCcross_pos : 0 < C_cross)
    (hM_pos : 0 < M) (hK_pos : 0 < K_energy)
    {P : Finset X}
    (hP_nonempty : P.Nonempty)
    {Tp : X → Finset Tube}
    (hTp_card_lower : ∀ p ∈ P, (M / 2 : ℝ) ≤ (Tp p).card)
    (hTp_card_upper : ∀ p ∈ P, (Tp p).card ≤ M)
    (h_common_bound : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      ((Tp p) ∩ (Tp q)).card ≤ C_cross * M * (δ / dist p q)^s)
    (h_energy : ∑ p ∈ P, ∑ q ∈ P.erase p, (dist p q)^(-s) ≤
        K_energy * C_P * (P.card : ℝ)^2)
    (h_diag_dom : (P.card : ℝ) ≥ C_cross * δ^s * K_energy * C_P * (P.card : ℝ)^2) :
    ((P.biUnion Tp).card : ℝ) ≥ (P.card : ℝ) * M / 8 := by
  let N : ℝ := (P.card : ℝ)
  let U : Finset Tube := P.biUnion Tp
  let d : Tube → ℕ := fun ℓ => (P.filter (fun p => ℓ ∈ Tp p)).card
  have setup := incidence_energy_setup hP_nonempty hTp_card_lower hTp_card_upper hM_pos
  have hN_pos := setup.1
  have hI_eq := setup.2.1
  have hI_lower := setup.2.2.1
  have hI_upper := setup.2.2.2.1
  have h_sum_d2 := setup.2.2.2.2.1
  have h_split := setup.2.2.2.2.2
  let C_off : ℝ := C_cross * M * δ^s
  have hCoff_pos : 0 < C_off := by positivity
  have hE_off : ∑ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ) ≤
      C_off * (K_energy * C_P * N^2) := by
    have h1 : ∀ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ) ≤
        ∑ q ∈ P.erase p, (C_off * (dist p q)^(-s)) := by
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      have hq' : q ∈ P := (Finset.mem_erase.mp hq).2
      have hne : p ≠ q := Ne.symm (Finset.mem_erase.mp hq).1
      have h20 := h_common_bound p hp q hq' hne
      have h2 : (((Tp p) ∩ (Tp q)).card : ℝ) ≤ C_cross * M * (δ / dist p q)^s := by
        exact_mod_cast h20
      have h3 : (δ / dist p q)^s = δ^s * (dist p q)^(-s) := by
        have h4 : (δ / dist p q)^s = δ^s / (dist p q)^s := Real.div_rpow (by positivity) (by positivity) _
        rw [h4]
        have h5 : δ^s / (dist p q)^s = δ^s * (dist p q)^(-s) := by
          have h51 : (dist p q)^(-s) = ((dist p q)^s)⁻¹ := by
            have hdn : 0 ≤ dist p q := dist_nonneg
            rw [Real.rpow_neg hdn]
          rw [h51] <;> ring
        exact h5
      rw [h3] at h2
      have h6 : C_cross * M * (δ^s * (dist p q)^(-s)) = C_off * (dist p q)^(-s) := by
        simp only [C_off] <;> ring
      rw [h6] at h2
      exact h2
    have h2 : ∑ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ) ≤
        ∑ p ∈ P, ∑ q ∈ P.erase p, (C_off * (dist p q)^(-s)) :=
      Finset.sum_le_sum (fun p hp => h1 p hp)
    have h3 : ∑ p ∈ P, ∑ q ∈ P.erase p, (C_off * (dist p q)^(-s)) =
        C_off * ∑ p ∈ P, ∑ q ∈ P.erase p, (dist p q)^(-s) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
    rw [h3] at h2
    have h4 : ∑ p ∈ P, ∑ q ∈ P.erase p, (dist p q)^(-s) ≤ K_energy * C_P * N^2 := h_energy
    have h5 : 0 ≤ C_off := by positivity
    exact le_trans h2 (mul_le_mul_of_nonneg_left h4 h5)
  have hE_total : (∑ ℓ ∈ U, (d ℓ : ℝ)^2) ≤ N * M + C_off * (K_energy * C_P * N^2) := by
    rw [h_sum_d2, h_split]
    have h5 : (∑ p ∈ P, ((Tp p).card : ℝ)) ≤ N * M := hI_upper
    linarith [hE_off]
  have hE_le : (∑ ℓ ∈ U, (d ℓ : ℝ)^2) ≤ 2 * N * M := by
    have h6 : C_off * (K_energy * C_P * N^2) ≤ N * M := by
      simp only [C_off] at * <;> nlinarith
    linarith [hE_total, h6]
  have h_cs : (∑ ℓ ∈ U, (d ℓ : ℝ))^2 ≤ (U.card : ℝ) * (∑ ℓ ∈ U, (d ℓ : ℝ)^2) :=
    cauchy_schwarz_card (S := U) (f := fun ℓ => (d ℓ : ℝ))
  have hS2_pos : 0 < (∑ ℓ ∈ U, (d ℓ : ℝ)^2) := by
    have h_nonneg : ∀ ℓ ∈ U, 0 ≤ (d ℓ : ℝ)^2 := fun ℓ _ => by positivity
    by_cases h : (∑ ℓ ∈ U, (d ℓ : ℝ)^2) = 0
    · have h_all_zero : ∀ ℓ ∈ U, (d ℓ : ℝ)^2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h
      have h_d_zero : ∀ ℓ ∈ U, (d ℓ : ℝ) = 0 := by
        intro ℓ hℓ
        have hsq : (d ℓ : ℝ)^2 = 0 := h_all_zero ℓ hℓ
        exact sq_eq_zero_iff.mp hsq
      have h16 : (∑ ℓ ∈ U, (d ℓ : ℝ)) = 0 := by
        rw [Finset.sum_congr rfl h_d_zero] <;> simp
      rw [hI_eq] at h16
      have h17 : (∑ p ∈ P, (Tp p).card : ℝ) = 0 := h16
      have h18 : (∑ p ∈ P, (Tp p).card : ℝ) ≥ N * M / 2 := hI_lower
      have h19 : 0 < N * M / 2 := by positivity
      linarith
    · have h_pos : 0 ≤ (∑ ℓ ∈ U, (d ℓ : ℝ)^2) := Finset.sum_nonneg h_nonneg
      exact lt_of_le_of_ne h_pos (Ne.symm h)
  have h_main : (U.card : ℝ) ≥ (N * M / 2)^2 / (2 * N * M) := by
    have h7 : (∑ ℓ ∈ U, (d ℓ : ℝ))^2 ≤ (U.card : ℝ) * (∑ ℓ ∈ U, (d ℓ : ℝ)^2) := h_cs
    rw [hI_eq] at h7
    have h8 : (∑ ℓ ∈ U, (d ℓ : ℝ)^2) ≤ 2 * N * M := hE_le
    have h9 : (∑ p ∈ P, (Tp p).card : ℝ)^2 ≤ (U.card : ℝ) * (2 * N * M) := by
      calc (∑ p ∈ P, (Tp p).card : ℝ)^2 ≤ (U.card : ℝ) * (∑ ℓ ∈ U, (d ℓ : ℝ)^2) := h7
        _ ≤ (U.card : ℝ) * (2 * N * M) := by gcongr
    have h10 : 0 ≤ N * M / 2 := by positivity
    have h11 : N * M / 2 ≤ (∑ p ∈ P, (Tp p).card : ℝ) := hI_lower
    have h12 : (N * M / 2)^2 ≤ (∑ p ∈ P, (Tp p).card : ℝ)^2 := by nlinarith
    have h13 : (N * M / 2)^2 ≤ (U.card : ℝ) * (2 * N * M) := by
      calc (N * M / 2)^2 ≤ (∑ p ∈ P, (Tp p).card : ℝ)^2 := h12
        _ ≤ (U.card : ℝ) * (2 * N * M) := h9
    have h14 : 0 < 2 * N * M := by positivity
    have h_div : ((U.card : ℝ) * (2 * N * M)) / (2 * N * M) = (U.card : ℝ) := by
      rw [mul_comm (U.card : ℝ)]
      exact mul_div_cancel_left₀ (U.card : ℝ) h14.ne'
    calc (U.card : ℝ) = ((U.card : ℝ) * (2 * N * M)) / (2 * N * M) := h_div.symm
      _ ≥ (N * M / 2)^2 / (2 * N * M) := by gcongr
  have h_final : (N * M / 2)^2 / (2 * N * M) = N * M / 8 := by
    field_simp [hN_pos.ne', hM_pos.ne']
    <;> ring
  rw [h_final] at h_main
  exact h_main

/-- Incidence Cauchy-Schwarz: off-diagonal-dominated (small M) case.

    Given off-diagonal dominance N·M ≤ C_bound·δ^s·K_energy·C_P·N²,
    then |T| ≥ M²·δ^{-s}/(8·C_bound·K_energy·C_P). -/
lemma incidence_cauchy_schwarz_smallM
    {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    {δ s C_P C_bound K_energy M : ℝ}
    (hδ_pos : 0 < δ) (hs : 0 ≤ s)
    (hCP_pos : 0 < C_P) (hCbound_pos : 0 < C_bound)
    (hM_pos : 0 < M) (hK_pos : 0 < K_energy)
    {P : Finset X}
    (hP_nonempty : P.Nonempty)
    {Tp : X → Finset Tube}
    (hTp_card_lower : ∀ p ∈ P, (M / 2 : ℝ) ≤ (Tp p).card)
    (hTp_card_upper : ∀ p ∈ P, (Tp p).card ≤ M)
    (h_common_bound : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      ((Tp p) ∩ (Tp q)).card ≤ C_bound * (δ / dist p q)^s)
    (h_energy : ∑ p ∈ P, ∑ q ∈ P.erase p, (dist p q)^(-s) ≤
        K_energy * C_P * (P.card : ℝ)^2)
    (h_off_dom : (P.card : ℝ) * M ≤ C_bound * δ^s * K_energy * C_P * (P.card : ℝ)^2) :
    ∃ (C_out : ℝ), 0 < C_out ∧
      ((P.biUnion Tp).card : ℝ) ≥ M^2 * δ^(-s) / C_out := by
  let N : ℝ := (P.card : ℝ)
  let U : Finset Tube := P.biUnion Tp
  let d : Tube → ℕ := fun ℓ => (P.filter (fun p => ℓ ∈ Tp p)).card
  have setup := incidence_energy_setup hP_nonempty hTp_card_lower hTp_card_upper hM_pos
  have hN_pos := setup.1
  have hI_eq := setup.2.1
  have hI_lower := setup.2.2.1
  have hI_upper := setup.2.2.2.1
  have h_sum_d2 := setup.2.2.2.2.1
  have h_split := setup.2.2.2.2.2
  let C_off : ℝ := C_bound * δ^s
  have hCoff_pos : 0 < C_off := by positivity
  have hE_off : ∑ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ) ≤
      C_off * (K_energy * C_P * N^2) := by
    have h1 : ∀ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ) ≤
        ∑ q ∈ P.erase p, (C_off * (dist p q)^(-s)) := by
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      have hq' : q ∈ P := (Finset.mem_erase.mp hq).2
      have hne : p ≠ q := Ne.symm (Finset.mem_erase.mp hq).1
      have h20 := h_common_bound p hp q hq' hne
      have h2 : (((Tp p) ∩ (Tp q)).card : ℝ) ≤ C_bound * (δ / dist p q)^s := by
        exact_mod_cast h20
      have h3 : (δ / dist p q)^s = δ^s * (dist p q)^(-s) := by
        have h4 : (δ / dist p q)^s = δ^s / (dist p q)^s := Real.div_rpow (by positivity) (by positivity) _
        rw [h4]
        have h5 : δ^s / (dist p q)^s = δ^s * (dist p q)^(-s) := by
          have h51 : (dist p q)^(-s) = ((dist p q)^s)⁻¹ := by
            have hdn : 0 ≤ dist p q := dist_nonneg
            rw [Real.rpow_neg hdn]
          rw [h51] <;> ring
        exact h5
      rw [h3] at h2
      have h6 : C_bound * (δ^s * (dist p q)^(-s)) = C_off * (dist p q)^(-s) := by
        simp only [C_off] <;> ring
      rw [h6] at h2
      exact h2
    have h2 : ∑ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ) ≤
        ∑ p ∈ P, ∑ q ∈ P.erase p, (C_off * (dist p q)^(-s)) :=
      Finset.sum_le_sum (fun p hp => h1 p hp)
    have h3 : ∑ p ∈ P, ∑ q ∈ P.erase p, (C_off * (dist p q)^(-s)) =
        C_off * ∑ p ∈ P, ∑ q ∈ P.erase p, (dist p q)^(-s) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
    rw [h3] at h2
    have h4 : ∑ p ∈ P, ∑ q ∈ P.erase p, (dist p q)^(-s) ≤ K_energy * C_P * N^2 := h_energy
    have h5 : 0 ≤ C_off := by positivity
    exact le_trans h2 (mul_le_mul_of_nonneg_left h4 h5)
  have hE_total : (∑ ℓ ∈ U, (d ℓ : ℝ)^2) ≤ N * M + C_off * (K_energy * C_P * N^2) := by
    rw [h_sum_d2, h_split]
    have h5 : (∑ p ∈ P, ((Tp p).card : ℝ)) ≤ N * M := hI_upper
    linarith [hE_off]
  have hE_le : (∑ ℓ ∈ U, (d ℓ : ℝ)^2) ≤ 2 * C_off * (K_energy * C_P * N^2) := by
    linarith [hE_total, h_off_dom]
  have h_cs : (∑ ℓ ∈ U, (d ℓ : ℝ))^2 ≤ (U.card : ℝ) * (∑ ℓ ∈ U, (d ℓ : ℝ)^2) :=
    cauchy_schwarz_card (S := U) (f := fun ℓ => (d ℓ : ℝ))
  have hS2_pos : 0 < (∑ ℓ ∈ U, (d ℓ : ℝ)^2) := by
    have h_nonneg : ∀ ℓ ∈ U, 0 ≤ (d ℓ : ℝ)^2 := fun ℓ _ => by positivity
    by_cases h : (∑ ℓ ∈ U, (d ℓ : ℝ)^2) = 0
    · have h_all_zero : ∀ ℓ ∈ U, (d ℓ : ℝ)^2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h
      have h_d_zero : ∀ ℓ ∈ U, (d ℓ : ℝ) = 0 := by
        intro ℓ hℓ
        have hsq : (d ℓ : ℝ)^2 = 0 := h_all_zero ℓ hℓ
        exact sq_eq_zero_iff.mp hsq
      have h16 : (∑ ℓ ∈ U, (d ℓ : ℝ)) = 0 := by
        rw [Finset.sum_congr rfl h_d_zero] <;> simp
      rw [hI_eq] at h16
      have h17 : (∑ p ∈ P, (Tp p).card : ℝ) = 0 := h16
      have h18 : (∑ p ∈ P, (Tp p).card : ℝ) ≥ N * M / 2 := hI_lower
      have h19 : 0 < N * M / 2 := by positivity
      linarith
    · have h_pos : 0 ≤ (∑ ℓ ∈ U, (d ℓ : ℝ)^2) := Finset.sum_nonneg h_nonneg
      exact lt_of_le_of_ne h_pos (Ne.symm h)
  let C_out : ℝ := 8 * C_bound * K_energy * C_P
  have hCout_pos : 0 < C_out := by positivity
  have h_main : (U.card : ℝ) ≥ M^2 * δ^(-s) / C_out := by
    have h7 : (∑ ℓ ∈ U, (d ℓ : ℝ))^2 ≤ (U.card : ℝ) * (∑ ℓ ∈ U, (d ℓ : ℝ)^2) := h_cs
    rw [hI_eq] at h7
    have h8 : (∑ ℓ ∈ U, (d ℓ : ℝ)^2) ≤ 2 * C_off * (K_energy * C_P * N^2) := hE_le
    have h9 : (∑ p ∈ P, (Tp p).card : ℝ)^2 ≤ (U.card : ℝ) * (2 * C_off * (K_energy * C_P * N^2)) := by
      calc (∑ p ∈ P, (Tp p).card : ℝ)^2 ≤ (U.card : ℝ) * (∑ ℓ ∈ U, (d ℓ : ℝ)^2) := h7
        _ ≤ (U.card : ℝ) * (2 * C_off * (K_energy * C_P * N^2)) := by gcongr
    have h10 : 0 ≤ N * M / 2 := by positivity
    have h11 : N * M / 2 ≤ (∑ p ∈ P, (Tp p).card : ℝ) := hI_lower
    have h12 : (N * M / 2)^2 ≤ (∑ p ∈ P, (Tp p).card : ℝ)^2 := by nlinarith
    have h13 : (N * M / 2)^2 ≤ (U.card : ℝ) * (2 * C_off * (K_energy * C_P * N^2)) := by
      calc (N * M / 2)^2 ≤ (∑ p ∈ P, (Tp p).card : ℝ)^2 := h12
        _ ≤ (U.card : ℝ) * (2 * C_off * (K_energy * C_P * N^2)) := h9
    have h14 : 0 < 2 * C_off * (K_energy * C_P * N^2) := by positivity
    have h_div2 : ((U.card : ℝ) * (2 * C_off * (K_energy * C_P * N^2))) / (2 * C_off * (K_energy * C_P * N^2)) = (U.card : ℝ) := by
      rw [mul_comm (U.card : ℝ)]
      exact mul_div_cancel_left₀ (U.card : ℝ) h14.ne'
    have h15 : (U.card : ℝ) ≥ (N * M / 2)^2 / (2 * C_off * (K_energy * C_P * N^2)) := by
      calc (U.card : ℝ) = ((U.card : ℝ) * (2 * C_off * (K_energy * C_P * N^2))) / (2 * C_off * (K_energy * C_P * N^2)) := h_div2.symm
        _ ≥ (N * M / 2)^2 / (2 * C_off * (K_energy * C_P * N^2)) := by gcongr
    have h16 : (N * M / 2)^2 / (2 * C_off * (K_energy * C_P * N^2)) = M^2 * δ^(-s) / C_out := by
      dsimp only [C_off, C_out]
      have hN : N ≠ 0 := hN_pos.ne'
      have hδs : 0 < δ^s := Real.rpow_pos_of_pos hδ_pos s
      have hδs_ne : δ^s ≠ 0 := hδs.ne'
      have hCb : C_bound ≠ 0 := hCbound_pos.ne'
      have hK : K_energy ≠ 0 := hK_pos.ne'
      have hCP : C_P ≠ 0 := hCP_pos.ne'
      have h4 : δ^(-s) = (δ^s)⁻¹ := by
        rw [Real.rpow_neg (show 0 ≤ δ by linarith)]
        <;> ring
      have h_lhs : (N * M / 2)^2 / (2 * (C_bound * δ^s) * (K_energy * C_P * N^2)) =
          M^2 / (8 * C_bound * δ^s * K_energy * C_P) := by
        have h : (N * M / 2)^2 / (2 * (C_bound * δ^s) * (K_energy * C_P * N^2)) =
            (N^2 * M^2) / (8 * C_bound * δ^s * K_energy * C_P * N^2) := by ring
        rw [h]
        have h2 : (N^2 * M^2) / (8 * C_bound * δ^s * K_energy * C_P * N^2) =
            M^2 / (8 * C_bound * δ^s * K_energy * C_P) := by
          field_simp [hN, hδs_ne, hCb, hK, hCP]
          <;> ring
        exact h2
      have h_rhs : M^2 * δ^(-s) / (8 * C_bound * K_energy * C_P) =
          M^2 / (8 * C_bound * δ^s * K_energy * C_P) := by
        rw [h4]
        field_simp [hδs_ne]
        <;> ring
      rw [h_lhs, h_rhs]
    rw [h16] at h15
    exact h15
  exact ⟨C_out, hCout_pos, h_main⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
