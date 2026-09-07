module

/-
  Source-to-NiceConfiguration bridge — helper lemmas.

  Extracted from SourceToNiceConfiguration_hmass2.lean to reduce
  per-file compilation time.

  Contains:
  - bounded_dyadic_tubes_card: cardinality bound for bounded dyadic tubes
  - local_finset_squares_ncover_lower: factor-9 covering lower bound
  - exp_dominates_linear: exponential beats linear
  - choose_finer_dyadic_scale: find nearby dyadic scale
  - rpow_neg_antitone, rpow_root_cancel, absorb_const: real power helpers
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.NearbyDyadicTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction.GeometricAndExternal
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DiscretisedFurstenbergEstimate

abbrev BridgePlane := EuclideanSpace ℝ (Fin 2)

/-- Bound cardinality of a finset of dyadic tubes with |slope| ≤ 3/2, |intercept| ≤ 3.
    The total number is at most 2^(2n+7). -/
lemma bounded_dyadic_tubes_card {n : ℕ} {S : Finset (DyadicTube n)}
    (h_slope : ∀ U ∈ S, |U.slope| ≤ 3 / 2)
    (h_intercept : ∀ U ∈ S, |U.intercept| ≤ 3) :
    S.card ≤ 2 ^ (2 * n + 7) := by
  let δ_n := dyadicDelta n
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  have hδn_inv : δ_n⁻¹ = (2 : ℝ)^n := by
    have h1 : δ_n = (1 / 2 : ℝ)^n := by
      simp [dyadicDelta, δ_n]
    have h2 : (1 / 2 : ℝ)^n = 1 / (2 : ℝ)^n := by
      induction n <;> simp [*, pow_succ] <;> field_simp <;> ring
    have h3 : δ_n = 1 / (2 : ℝ)^n := by
      rw [h1, h2]
    rw [h3]
    have h4 : (1 / (2 : ℝ)^n)⁻¹ = (2 : ℝ)^n := by
      field_simp <;> norm_cast
    exact h4
  have ha_bound : ∀ U ∈ S, |(U.a : ℝ)| ≤ 3 * 2^n + 1 := by
    intro U hU
    have h1 : |U.slope| ≤ 3 / 2 := h_slope U hU
    have h2 : |(U.a : ℝ)| * δ_n ≤ 3 / 2 := by
      have h_eq : U.slope = (U.a : ℝ) * δ_n := by rfl
      rw [h_eq] at h1
      have h_abs : |(U.a : ℝ) * δ_n| = |(U.a : ℝ)| * δ_n := by
        rw [abs_mul, abs_of_pos hδn_pos]
      rw [h_abs] at h1; exact h1
    have h3 : |(U.a : ℝ)| ≤ (3 / 2 : ℝ) * δ_n⁻¹ := by
      calc |(U.a : ℝ)|
        = |(U.a : ℝ)| * δ_n * δ_n⁻¹ := by field_simp [hδn_pos.ne'] <;> ring
      _ ≤ (3 / 2 : ℝ) * δ_n⁻¹ := by gcongr
    rw [hδn_inv] at h3
    have h4 : |(U.a : ℝ)| ≤ 3 / 2 * (2 : ℝ)^n := h3
    have h5 : (3 / 2 : ℝ) * (2 : ℝ)^n ≤ 3 * (2 : ℝ)^n + 1 := by
      have h6 : 0 ≤ (2 : ℝ)^n := by positivity
      nlinarith
    exact le_trans h4 h5
  have hb_bound : ∀ U ∈ S, |(U.b : ℝ)| ≤ 3 * 2^n + 1 := by
    intro U hU
    have h1 : |U.intercept| ≤ 3 := h_intercept U hU
    have h2 : |(U.b : ℝ)| * δ_n ≤ 3 := by
      have h_eq : U.intercept = (U.b : ℝ) * δ_n := by rfl
      rw [h_eq] at h1
      have h_abs : |(U.b : ℝ) * δ_n| = |(U.b : ℝ)| * δ_n := by
        rw [abs_mul, abs_of_pos hδn_pos]
      rw [h_abs] at h1; exact h1
    have h3 : |(U.b : ℝ)| ≤ (3 : ℝ) * δ_n⁻¹ := by
      calc |(U.b : ℝ)|
        = |(U.b : ℝ)| * δ_n * δ_n⁻¹ := by field_simp [hδn_pos.ne'] <;> ring
      _ ≤ (3 : ℝ) * δ_n⁻¹ := by gcongr
    rw [hδn_inv] at h3
    have h4 : |(U.b : ℝ)| ≤ 3 * (2 : ℝ)^n := h3
    have h5 : 3 * (2 : ℝ)^n ≤ 3 * (2 : ℝ)^n + 1 := by linarith
    exact le_trans h4 h5
  let N_int : ℕ := 3 * 2^n + 1
  let A : Finset ℤ := Finset.Icc (-(N_int : ℤ)) (N_int : ℤ)
  let B : Finset ℤ := Finset.Icc (-(N_int : ℤ)) (N_int : ℤ)
  have hA_card : A.card = 2 * N_int + 1 := by
    simp [A, Int.card_Icc] <;> omega
  have hB_card : B.card = 2 * N_int + 1 := by
    simp [B, Int.card_Icc] <;> omega
  have h_sub1 : ∀ U ∈ S, U.a ∈ A := by
    intro U hU
    have h6 : |(U.a : ℝ)| ≤ (N_int : ℝ) := by
      simpa [N_int] using ha_bound U hU
    have h7 : -(N_int : ℝ) ≤ (U.a : ℝ) := (abs_le.mp h6).1
    have h8 : (U.a : ℝ) ≤ (N_int : ℝ) := (abs_le.mp h6).2
    have h9 : -(N_int : ℤ) ≤ U.a := by exact_mod_cast h7
    have h10 : U.a ≤ (N_int : ℤ) := by exact_mod_cast h8
    simp only [A, Finset.mem_Icc] <;> exact ⟨h9, h10⟩
  have h_sub2 : ∀ U ∈ S, U.b ∈ B := by
    intro U hU
    have h6 : |(U.b : ℝ)| ≤ (N_int : ℝ) := by
      simpa [N_int] using hb_bound U hU
    have h7 : -(N_int : ℝ) ≤ (U.b : ℝ) := (abs_le.mp h6).1
    have h8 : (U.b : ℝ) ≤ (N_int : ℝ) := (abs_le.mp h6).2
    have h9 : -(N_int : ℤ) ≤ U.b := by exact_mod_cast h7
    have h10 : U.b ≤ (N_int : ℤ) := by exact_mod_cast h8
    simp only [B, Finset.mem_Icc] <;> exact ⟨h9, h10⟩
  let f : DyadicTube n → ℤ × ℤ := fun U => (U.a, U.b)
  have h_inj : Set.InjOn f (S : Set (DyadicTube n)) := by
    intro U1 _ U2 _ h
    have h1 : U1.a = U2.a := (Prod.ext_iff.mp h).1
    have h2 : U1.b = U2.b := (Prod.ext_iff.mp h).2
    cases U1 <;> cases U2 <;> simp_all <;> tauto
  have h_img_sub : (S.image f) ⊆ A ×ˢ B := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨U, hU, rfl⟩
    exact Finset.mem_product.mpr ⟨h_sub1 U hU, h_sub2 U hU⟩
  have h_card_img : (S.image f).card = S.card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h_card_prod : (A ×ˢ B).card = A.card * B.card := Finset.card_product A B
  have h_main : S.card ≤ (2 * N_int + 1) * (2 * N_int + 1) := by
    have h1 : S.card ≤ (A ×ˢ B).card := by
      calc S.card
        = (S.image f).card := h_card_img.symm
      _ ≤ (A ×ˢ B).card := Finset.card_le_card h_img_sub
    have h2 : (A ×ˢ B).card ≤ (2 * N_int + 1) * (2 * N_int + 1) := by
      have h21 : (A ×ˢ B).card = A.card * B.card := h_card_prod
      have ha : A.card ≤ 2 * N_int + 1 := hA_card.le
      have hb : B.card ≤ 2 * N_int + 1 := hB_card.le
      have h_pos1 : 0 ≤ A.card := by positivity
      have h_pos2 : 0 ≤ B.card := by positivity
      have h_ab : A.card * B.card ≤ (2 * N_int + 1) * (2 * N_int + 1) := by
        nlinarith
      rw [h21]
      exact h_ab
    exact le_trans h1 h2
  have h_final : (2 * N_int + 1) * (2 * N_int + 1) ≤ 2 ^ (2 * n + 7) := by
    simp only [N_int]
    have h6 : 2 * (3 * 2^n + 1) + 1 ≤ 9 * 2^n := by
      have h7 : 2 * (3 * 2^n + 1) + 1 = 6 * 2^n + 3 := by ring
      rw [h7]
      have h8 : 3 ≤ 3 * 2^n := by
        have h9 : 1 ≤ 2^n := by apply Nat.one_le_pow <;> norm_num
        nlinarith
      nlinarith
    have h7 : (2 * (3 * 2^n + 1) + 1) * (2 * (3 * 2^n + 1) + 1) ≤ (9 * 2^n) * (9 * 2^n) := by gcongr
    have h8 : (9 * 2^n) * (9 * 2^n) = 81 * 2^(2 * n) := by ring
    rw [h8] at h7
    have h9 : 81 * 2^(2 * n) ≤ 2 ^ (2 * n + 7) := by
      have h10 : 2 ^ (2 * n + 7) = 128 * 2^(2 * n) := by
        simp [pow_add] <;> ring
      rw [h10]
      have h11 : 0 ≤ 2^(2 * n) := by positivity
      nlinarith
    exact le_trans h7 h9
  exact le_trans h_main h_final

/-- Local factor-9 lower bound: |squares| ≤ 9 * Ncover(δ_n, union of squares). -/
lemma local_finset_squares_ncover_lower
    {n : ℕ} (P_Q : Finset (DyadicSquare n)) :
    (P_Q.card : ENNReal) ≤ (9 : ENNReal) *
      Metric.externalCoveringNumber (dyadicDelta n).toNNReal
        (⋃ p ∈ (P_Q : Set (DyadicSquare n)), (p.toSet : Set BridgePlane)) := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  let E := (⋃ p ∈ (P_Q : Set (DyadicSquare n)), (p.toSet : Set BridgePlane))
  have h_main : ∀ (C : Set BridgePlane), Metric.IsCover δ.toNNReal E C →
      (P_Q.card : ENNReal) / 9 ≤ (C.encard : ENNReal) := by
    intro C hC
    by_cases hCfin : Set.Finite C
    · let Cfin := hCfin.toFinset
      have h2 : (Cfin : Set BridgePlane) = C := Set.Finite.coe_toFinset _
      let Q_c (c : BridgePlane) : Finset (DyadicSquare n) :=
        P_Q.filter (fun p => (p.toSet : Set BridgePlane) ∩ Metric.closedBall c δ ≠ ∅)
      have h3 : ∀ c ∈ Cfin, (Q_c c).card ≤ 9 := by
        intro c _
        rcases ball_intersects_at_most_9_squares c δ hδ_pos rfl with ⟨I, hI9, hI_mem⟩
        have h4 : Q_c c ⊆ I := by
          intro p hp
          have h5 : (p.toSet : Set BridgePlane) ∩ Metric.closedBall c δ ≠ ∅ :=
            (Finset.mem_filter.mp hp).2
          exact hI_mem p h5
        have h5 : (Q_c c).card ≤ I.card := Finset.card_le_card h4
        have h6 : I.card ≤ 9 := hI9
        linarith
      have h4 : P_Q ⊆ Cfin.biUnion Q_c := by
        intro p hp
        have h10 : (p.toSet : Set BridgePlane).Nonempty := by
          let z : BridgePlane := WithLp.toLp 2 ![((p.i : ℝ) * δ), ((p.j : ℝ) * δ)]
          have hz : z ∈ (p.toSet : Set BridgePlane) := by
            simp [DyadicSquare.toSet, z]
            <;> exact ⟨by linarith, by linarith [hδ_pos], by linarith, by linarith [hδ_pos]⟩
          exact ⟨z, hz⟩
        rcases h10 with ⟨z, hz⟩
        have hz_in_E : z ∈ E := Set.mem_iUnion₂.mpr ⟨p, hp, hz⟩
        have h10 : z ∈ ⋃ c ∈ (Cfin : Set BridgePlane), Metric.closedBall c δ.toNNReal := by
          have h11 : z ∈ ⋃ c ∈ C, Metric.closedBall c δ.toNNReal := hC.subset_iUnion_closedBall hz_in_E
          have h2' : C = (Cfin : Set BridgePlane) := h2.symm
          rw [h2'] at h11; exact h11
        rcases Set.mem_iUnion₂.mp h10 with ⟨c, hc, hzc⟩
        have h11 : (p.toSet : Set BridgePlane) ∩ Metric.closedBall c δ ≠ ∅ := by
          have h13 : (δ.toNNReal : ℝ) = δ := by
            have h14 : 0 ≤ δ := by linarith
            simp [Real.toNNReal, h14]
          have h14 : Metric.closedBall c δ.toNNReal = Metric.closedBall c δ := by
            congr <;> exact h13
          have h15 : Set.Nonempty ((p.toSet : Set BridgePlane) ∩ Metric.closedBall c δ.toNNReal) := ⟨z, hz, hzc⟩
          have h16 : (p.toSet : Set BridgePlane) ∩ Metric.closedBall c δ ≠ ∅ := by
            have h17 : (p.toSet : Set BridgePlane) ∩ Metric.closedBall c δ.toNNReal ≠ ∅ := h15.ne_empty
            rw [h14] at h17
            exact h17
          exact h16
        exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨hp, h11⟩⟩
      have h5 : P_Q.card ≤ ∑ c ∈ Cfin, (Q_c c).card := by
        calc P_Q.card
          ≤ (Cfin.biUnion Q_c).card := Finset.card_le_card h4
        _ ≤ ∑ c ∈ Cfin, (Q_c c).card := Finset.card_biUnion_le
      have h6 : ∑ c ∈ Cfin, (Q_c c).card ≤ ∑ c ∈ Cfin, (9 : ℕ) := by
        apply Finset.sum_le_sum; intro c hc; exact h3 c hc
      have h7 : ∑ c ∈ Cfin, (9 : ℕ) = 9 * Cfin.card := by
        simp [Finset.sum_const] <;> ring
      rw [h7] at h6
      have h8 : (P_Q.card : ENNReal) ≤ (9 : ENNReal) * (Cfin.card : ENNReal) := by
        exact_mod_cast h5.trans h6
      have h9 : (C.encard : ENNReal) = (Cfin.card : ENNReal) := by
        have h10 : C.encard = (Cfin.card : ENat) := by rw [←h2]; simp
        rw [h10] <;> norm_cast
      rw [h9]
      calc (P_Q.card : ENNReal) / 9
        ≤ ((9 : ENNReal) * (Cfin.card : ENNReal)) / 9 := by gcongr
      _ = (Cfin.card : ENNReal) := by
        have h_comm : (9 : ENNReal) * (Cfin.card : ENNReal) = (Cfin.card : ENNReal) * (9 : ENNReal) := by ring
        rw [h_comm]
        exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
    · have h6 : C.encard = ⊤ := by rw [Set.encard_eq_top_iff]; exact hCfin
      rw [h6] <;> simp
  have h4 : (P_Q.card : ENNReal) / 9 ≤ (Metric.externalCoveringNumber δ.toNNReal E : ENNReal) := by
    simpa [Metric.externalCoveringNumber] using le_iInf₂ h_main
  have h5 : ((P_Q.card : ENNReal) / 9) * 9 ≤ (Metric.externalCoveringNumber δ.toNNReal E : ENNReal) * 9 := by gcongr
  have h6 : ((P_Q.card : ENNReal) / 9) * 9 = (P_Q.card : ENNReal) := by
    exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
  have h7 : (P_Q.card : ENNReal) ≤ (9 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal E : ENNReal) := by
    have h8 : (Metric.externalCoveringNumber δ.toNNReal E : ENNReal) * 9 =
        (9 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal E : ENNReal) := by ring
    rw [h8] at h5
    rw [h6] at h5
    exact h5
  exact h7

/-- Exponential domination: for a > 1, ∃ N, ∀ n ≥ N, 2*n + 10 ≤ a^n. -/
lemma exp_dominates_linear (a : ℝ) (ha : 1 < a) :
    ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → (2 * (n : ℝ) + 10) ≤ a ^ n := by
  have hL_pos : 0 < Real.log a := Real.log_pos ha
  set L := Real.log a with hL
  have h_exp2 : ∀ (x : ℝ), 0 ≤ x → Real.exp x ≥ x^2 / 4 := by
    intro x hx
    have h1 : Real.exp (x / 2) ≥ x / 2 + 1 := Real.add_one_le_exp (x / 2)
    have h21 : Real.exp x = Real.exp (x / 2 + x / 2) := by ring_nf
    have h2 : Real.exp x = (Real.exp (x / 2))^2 := by
      rw [h21, Real.exp_add] <;> ring
    rw [h2]
    have h3 : 0 ≤ x / 2 + 1 := by linarith
    nlinarith
  let C : ℝ := 20 / L^2 + 10
  have hC : ∀ (n : ℕ), (n : ℝ) ≥ C → (2 * (n : ℝ) + 10) ≤ ((n : ℝ) * L)^2 / 4 := by
    intro n hn
    have h_ge : (n : ℝ) ≥ 20 / L^2 + 10 := by simpa [C] using hn
    have h_nonneg : 0 ≤ 20 / L^2 := by positivity
    have h1 : (n : ℝ) ≥ 20 / L^2 := by linarith [h_ge, h_nonneg]
    have h2 : (n : ℝ) ≥ 10 := by linarith [h_ge, h_nonneg]
    have h3 : L^2 * (n : ℝ)^2 ≥ 20 * (n : ℝ) := by
      have h4 : (n : ℝ)^2 ≥ (n : ℝ) * (20 / L^2) := by
        have h5 : 0 ≤ (n : ℝ) := by positivity
        nlinarith
      have h6 : L^2 * (n : ℝ)^2 ≥ L^2 * ((n : ℝ) * (20 / L^2)) := by gcongr
      have h7 : L^2 * ((n : ℝ) * (20 / L^2)) = 20 * (n : ℝ) := by
        field_simp [hL_pos.ne'] <;> ring
      rw [h7] at h6
      exact h6
    nlinarith
  rcases exists_nat_ge C with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hN' : (n : ℝ) ≥ C := by
    have h : (N : ℝ) ≥ C := hN
    have h' : (n : ℝ) ≥ (N : ℝ) := by exact_mod_cast hn
    linarith
  have h1 : (2 * (n : ℝ) + 10) ≤ ((n : ℝ) * L)^2 / 4 := hC n hN'
  have h2 : ((n : ℝ) * L)^2 / 4 ≤ Real.exp ((n : ℝ) * L) := h_exp2 ((n : ℝ) * L) (by positivity)
  have h3 : Real.exp ((n : ℝ) * L) = a ^ n := by
    have h4 : Real.exp ((n : ℝ) * Real.log a) = (Real.exp (Real.log a)) ^ n := by
      rw [Real.exp_nat_mul]
    have h5 : Real.exp (Real.log a) = a := Real.exp_log (by linarith)
    rw [h4, h5]
  rw [h3] at h2
  exact le_trans h1 h2

/-- Given 0 < δ ≤ 1, find n with dyadicDelta n ≤ δ < 2 * dyadicDelta n. -/
lemma choose_finer_dyadic_scale (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) :
    ∃ (n : ℕ), dyadicDelta n ≤ δ ∧ δ < 2 * dyadicDelta n := by
  by_cases h : δ = 1
  · refine ⟨0, ?_, ?_⟩
    · simp [h, dyadicDelta]
    · simp [h, dyadicDelta] <;> norm_num
  · have hδ_lt_one : δ < 1 := lt_of_le_of_ne hδ_le_one h
    rcases NearbyDyadicTransfer.choose_coarser_dyadic_scale δ hδ_pos hδ_lt_one with ⟨m, hlt, hle⟩
    have h_eq : dyadicDelta (m + 1) = dyadicDelta m / 2 := by
      simp [dyadicDelta, pow_succ] <;> ring
    refine ⟨m + 1, ?_, ?_⟩
    · rw [h_eq]; linarith
    · rw [h_eq]; linarith [hlt]

/-- If 0 < x ≤ y and e > 0, then x^(-e) ≥ y^(-e). -/
lemma rpow_neg_antitone {x y e : ℝ} (hx_pos : 0 < x) (hxy : x ≤ y) (he : 0 < e) :
    x^(-e) ≥ y^(-e) := by
  have h1 : x^e ≤ y^e := by
    have hx_nonneg : 0 ≤ x := by linarith
    gcongr
  have h2 : x^(-e) = (x^e)⁻¹ := by rw [← Real.rpow_neg (by linarith)] <;> ring
  have h3 : y^(-e) = (y^e)⁻¹ := by rw [← Real.rpow_neg (by linarith)] <;> ring
  rw [h2, h3]
  gcongr

/-- If x > 0 and e > 0, then (x^(1/e))^e = x. -/
lemma rpow_root_cancel {x e : ℝ} (hx_pos : 0 < x) (he : 0 < e) :
    (x^(1/e))^e = x := by
  have h1 : (x^(1/e))^e = x^((1/e) * e) := by
    rw [← Real.rpow_mul (by linarith)] <;> ring
  rw [h1]
  have h2 : (1/e) * e = 1 := by field_simp [he.ne'] <;> ring
  rw [h2]; simp

/-- Absorption: if δ ≤ (1/C)^(1/d), then C ≤ δ^(-d). -/
lemma absorb_const {C d δ : ℝ} (hC_pos : 0 < C) (hd_pos : 0 < d) (hδ_pos : 0 < δ)
    (h : δ ≤ (1/C)^(1/d)) : C ≤ δ^(-d) := by
  have h1 : δ^d ≤ 1/C := by
    have h2 : δ^d ≤ ((1/C)^(1/d))^d := by gcongr
    have h3 : ((1/C)^(1/d))^d = 1/C := rpow_root_cancel (by positivity) hd_pos
    rw [h3] at h2; exact h2
  have h4 : δ^(-d) = (δ^d)⁻¹ := by rw [← Real.rpow_neg (by linarith)] <;> ring
  rw [h4]
  have h5 : (δ^d)⁻¹ ≥ C := by
    calc (δ^d)⁻¹
      ≥ (1/C)⁻¹ := by gcongr
    _ = C := by field_simp [hC_pos.ne'] <;> ring
  exact h5

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
