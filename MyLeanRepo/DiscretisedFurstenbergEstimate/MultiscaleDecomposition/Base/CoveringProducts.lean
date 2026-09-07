module

/-
Copyright (c) 2024 The Discretised Furstenberg Estimate Team.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raven Team
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.CoveringBasics
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.DyadicUniform

@[expose] public section

noncomputable section

namespace DirecretisedFurstenbergEstimate

namespace MultiscaleDecomposition

/-! # Product covering number lemmas

This module contains the key product formulas for covering numbers of uniform sets:
- `covering_product_upper`: upper bound N_{Δ^m}(P ∩ Q) ≤ 9^(m-j) · ∏ N_i
- `covering_step_lower`: single-step lower bound with factor N(k)/4
- `covering_product_lower`: lower bound N_{Δ^m}(P) ≥ (∏ N_i) / 4^m
-/

/-- Upper bound: δ-covering number of P ∩ Q ≤ 9^(m-j) * ∏ N_i. -/
lemma covering_product_upper {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsUniform P m Δ N) {j : ℕ} (hj : j ≤ m)
    (a b : ℤ) (hQ : (P ∩ dyadicSquare (Δ ^ j) a b).Nonempty) :
    (Metric.externalCoveringNumber (Δ ^ m).toNNReal
       (P ∩ dyadicSquare (Δ ^ j) a b) : ENNReal) ≤
      (9 : ENNReal) ^ (m - j) * ∏ i ∈ Finset.range (m - j), (↑(N (j + i)) : ENNReal) := by
  let P_j := P ∩ dyadicSquare (Δ ^ j) a b
  have hΔ : 0 < Δ := h_uniform.1
  have hΔ_pos : ∀ k : ℕ, 0 < Δ ^ k := by
    intro k
    exact pow_pos hΔ k
  have h_main : ∀ (k : ℕ), j + k ≤ m →
      (Metric.externalCoveringNumber (Δ ^ (j + k)).toNNReal P_j : ENNReal) ≤
        (9 : ENNReal) ^ k * ∏ i ∈ Finset.range k, (↑(N (j + i)) : ENNReal) := by
    intro k hk
    induction k with
    | zero =>
      -- Base case k=0: single ball covers the square
      have h1 : ∃ (x : EuclideanPlane), dyadicSquare (Δ ^ j) a b ⊆ Metric.closedBall x (Δ ^ j) :=
        single_ball_covers_dyadicSquare (Δ ^ j) (hΔ_pos j) a b
      rcases h1 with ⟨x, hx⟩
      have h2 : P_j ⊆ Metric.closedBall x (Δ ^ j) := by
        exact Set.Subset.trans (show P_j ⊆ dyadicSquare (Δ ^ j) a b from Set.inter_subset_right) hx
      have h2' : P_j ⊆ Metric.closedBall x (Δ ^ j).toNNReal := by
        have h_eq : Metric.closedBall x (Δ ^ j) = Metric.closedBall x (Δ ^ j).toNNReal := by
          ext y
          simp [Metric.mem_closedBall, show 0 ≤ Δ ^ j from by linarith [hΔ_pos j]]
          <;> rfl
        rw [h_eq] at h2
        exact h2
      have h3 : Metric.IsCover (Δ ^ j).toNNReal P_j ({x} : Set EuclideanPlane) := by
        rw [Metric.isCover_iff_subset_iUnion_closedBall]
        simpa using h2'
      have h4 : Metric.externalCoveringNumber (Δ ^ j).toNNReal P_j ≤ ({x} : Set EuclideanPlane).encard :=
        Metric.IsCover.externalCoveringNumber_le_encard h3
      have h5 : ({x} : Set EuclideanPlane).encard = 1 := by simp
      rw [h5] at h4
      have h6 : (Metric.externalCoveringNumber (Δ ^ j).toNNReal P_j : ENNReal) ≤ (1 : ENNReal) := by
        have h7 : (Metric.externalCoveringNumber (Δ ^ j).toNNReal P_j : ENNReal) ≤ (↑(1 : ENat) : ENNReal) :=
          enat_to_ennreal_mono h4
        have h8 : (↑(1 : ENat) : ENNReal) = (1 : ENNReal) := by simp
        rw [h8] at h7
        exact h7
      simpa using h6
    | succ k ih =>
      -- Inductive step
      have h_jk_lt_m : j + k < m := by omega
      let M : ENNReal := (9 : ENNReal) ^ k * ∏ i ∈ Finset.range k, (↑(N (j + i)) : ENNReal)
      have hM_fin : M ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · have h9 : (9 : ENNReal) ^ k ≠ ⊤ := by
            simp
          exact h9
        · apply ENNReal.prod_ne_top
          intro i _
          simp
      have h_ih' : Metric.externalCoveringNumber (Δ ^ (j + k)).toNNReal P_j ≤ M := ih (by omega)
      rcases exists_finite_cover_le h_ih' hM_fin with ⟨C, hC_cover, hC_card⟩
      have h_refine := refine_cover_by_squares h_uniform h_jk_lt_m P_j (Set.inter_subset_left) C hC_cover
      calc (Metric.externalCoveringNumber (Δ ^ (j + k + 1)).toNNReal P_j : ENNReal)
        ≤ (C.card : ENNReal) * 9 * (N (j + k) : ENNReal) := h_refine
      _ ≤ M * 9 * (N (j + k) : ENNReal) := by
          gcongr <;> assumption
      _ = (9 : ENNReal) ^ (k + 1) * ∏ i ∈ Finset.range (k + 1), (↑(N (j + i)) : ENNReal) := by
          simp [M, Finset.prod_range_succ, pow_succ, mul_assoc] <;> ring
  have h_final := h_main (m - j) (by omega)
  have h_eq : j + (m - j) = m := by omega
  rw [h_eq] at h_final
  exact h_final

/-- Key step for covering_product_lower: if Δ ≤ 1/2, then
covering_number(Δ^{k+1}, P) ≥ covering_number(Δ^k, P) * N(k) / 4. -/
lemma covering_step_lower {P : Set EuclideanPlane} {k : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsUniform P (k + 1) Δ N) (hΔ2 : Δ ≤ 1 / 2) :
    (Metric.externalCoveringNumber (Δ ^ (k + 1)).toNNReal P : ENNReal) ≥
      (Metric.externalCoveringNumber (Δ ^ k).toNNReal P : ENNReal) * (N k : ENNReal) / 4 := by
  let ε1 := (Δ ^ (k + 1)).toNNReal
  let ε0 := (Δ ^ k).toNNReal
  have hΔ : 0 < Δ := h_uniform.1
  have hΔk_pos : 0 < Δ ^ k := by positivity
  have hΔk1_pos : 0 < Δ ^ (k + 1) := by positivity
  have h_rle : Δ ^ (k + 1) ≤ (Δ ^ k) / 2 := by
    calc Δ ^ (k + 1) = Δ * Δ ^ k := by ring
      _ ≤ (1 / 2 : ℝ) * Δ ^ k := by gcongr
      _ = (Δ ^ k) / 2 := by ring
  have h_le1 : Δ ^ (k + 1) ≤ Δ ^ k := by
    have h1 : Δ < 1 := h_uniform.2.1
    have h2 : 0 ≤ Δ := by linarith
    have h3 : Δ ^ (k + 1) ≤ Δ ^ k := by
      rw [pow_succ]
      have h4 : Δ * Δ ^ k ≤ 1 * Δ ^ k := by gcongr
      linarith
    exact h3
  have h_nnle : ε1 ≤ ε0 := by
    simp only [ε1, ε0]
    exact Real.toNNReal_mono h_le1
  have h_anti : (Metric.externalCoveringNumber ε0 P : ENNReal) ≤ (Metric.externalCoveringNumber ε1 P : ENNReal) :=
    enat_to_ennreal_mono (Metric.externalCoveringNumber_anti h_nnle)
  by_cases h_top1 : (Metric.externalCoveringNumber ε1 P : ENNReal) = ⊤
  · rw [h_top1] <;> simp
  · classical
    rcases exists_finite_cover_le (le_refl (Metric.externalCoveringNumber ε1 P : ENNReal)) h_top1 with ⟨C, hC_cover, hC_card⟩
    let S (c : EuclideanPlane) : Finset (ℤ × ℤ) :=
      Classical.choose (ball_dyadic_squares_bound_4 (Δ ^ k) (Δ ^ (k + 1)) hΔk_pos hΔk1_pos h_rle c)
    have hS1 (c : EuclideanPlane) : ∀ (i j : ℤ),
        (Metric.closedBall c (Δ ^ (k + 1)) ∩ dyadicSquare (Δ ^ k) i j).Nonempty → (i, j) ∈ S c :=
      (Classical.choose_spec (ball_dyadic_squares_bound_4 (Δ ^ k) (Δ ^ (k + 1)) hΔk_pos hΔk1_pos h_rle c)).1
    have hS2 (c : EuclideanPlane) : (S c).card ≤ 4 :=
      (Classical.choose_spec (ball_dyadic_squares_bound_4 (Δ ^ k) (Δ ^ (k + 1)) hΔk_pos hΔk1_pos h_rle c)).2
    let T : Finset (ℤ × ℤ) := C.biUnion S
    let Q (p : ℤ × ℤ) := dyadicSquare (Δ ^ k) p.1 p.2
    let Tne := T.filter (fun p => (P ∩ Q p).Nonempty)
    let Cp (p : ℤ × ℤ) := C.filter (fun c => p ∈ S c)
    have h_cov_p : ∀ p ∈ Tne, Metric.IsCover ε1 (P ∩ Q p) (Cp p) := by
      intro p hp
      rw [Metric.isCover_iff_subset_iUnion_closedBall]
      intro y hy
      have yP : y ∈ P := hy.1; have yQ : y ∈ Q p := hy.2
      have h2 : y ∈ ⋃ c ∈ C, Metric.closedBall c ε1 := hC_cover.subset_iUnion_closedBall yP
      rcases Set.mem_iUnion₂.mp h2 with ⟨c, hcC, hcBall⟩
      have hdist : dist y c ≤ Δ ^ (k + 1) := by
        simpa [ε1, Metric.mem_closedBall, show 0 ≤ Δ ^ (k + 1) by positivity] using hcBall
      have h_int : (Metric.closedBall c (Δ ^ (k + 1)) ∩ Q p).Nonempty :=
        ⟨y, by simpa [Metric.mem_closedBall] using hdist, yQ⟩
      have hps : p ∈ S c := hS1 c p.1 p.2 h_int
      have hcp : c ∈ Cp p := by simp [Cp, hcC, hps]
      exact Set.mem_iUnion₂.mpr ⟨c, hcp, hcBall⟩
    have h_card_p : ∀ p ∈ Tne, (N k : ENNReal) ≤ ((Cp p).card : ENNReal) := by
      intro p hp
      have hne : (P ∩ Q p).Nonempty := (Finset.mem_filter.mp hp).2
      have h_unif : (Metric.externalCoveringNumber ε1 (P ∩ Q p) : ENNReal) = (↑(N k) : ENNReal) :=
        h_uniform.2.2.2.2 k (by linarith) p.1 p.2 hne
      have h_le : Metric.externalCoveringNumber ε1 (P ∩ Q p) ≤ (Cp p : Set EuclideanPlane).encard :=
        Metric.IsCover.externalCoveringNumber_le_encard (h_cov_p p hp)
      have h_eq : (Cp p : Set EuclideanPlane).encard = ↑((Cp p).card) := by simp
      have h_le' : Metric.externalCoveringNumber ε1 (P ∩ Q p) ≤ ↑((Cp p).card) := by
        rw [h_eq] at h_le; exact h_le
      have h_enat : (Metric.externalCoveringNumber ε1 (P ∩ Q p) : ENNReal) ≤ ((Cp p).card : ENNReal) :=
        enat_to_ennreal_mono h_le'
      rw [h_unif] at h_enat
      exact h_enat
    have h_sum : ∑ p ∈ Tne, (Cp p).card ≤ 4 * C.card := by
      have h1 : ∑ p ∈ Tne, (Cp p).card ≤ ∑ p ∈ T, (Cp p).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
      have h2 : ∑ p ∈ T, (Cp p).card = ∑ c ∈ C, (S c).card := by
        have h3 : ∀ p ∈ T, (Cp p).card = ∑ c ∈ C, if p ∈ S c then 1 else 0 := by
          intro p _
          simp [Cp, Finset.filter_eq']
          <;> rfl
        calc ∑ p ∈ T, (Cp p).card
          = ∑ p ∈ T, ∑ c ∈ C, (if p ∈ S c then 1 else 0) :=
            Finset.sum_congr rfl (fun p hp => h3 p hp)
        _ = ∑ c ∈ C, ∑ p ∈ T, (if p ∈ S c then 1 else 0) := by rw [Finset.sum_comm]
        _ = ∑ c ∈ C, (S c).card := by
          apply Finset.sum_congr rfl
          intro c hc
          have h4 : S c ⊆ T := by
            intro x hx
            exact Finset.mem_biUnion.mpr ⟨c, hc, hx⟩
          have h5 : ∑ p ∈ T, (if p ∈ S c then 1 else 0) = (S c).card := by
            rw [Finset.sum_ite]
            <;> simp [h4]
            <;> rfl
          exact h5
      rw [h2] at h1
      have h4 : ∑ c ∈ C, (S c).card ≤ ∑ c ∈ C, 4 := Finset.sum_le_sum (fun c _ => hS2 c)
      have h5 : ∑ c ∈ C, (4 : ℕ) = 4 * C.card := by
        rw [Finset.sum_const] <;> ring
      rw [h5] at h4
      exact le_trans h1 h4
    let center (p : ℤ × ℤ) := Classical.choose (single_ball_covers_dyadicSquare (Δ ^ k) hΔk_pos p.1 p.2)
    have hcenter : ∀ p, Q p ⊆ Metric.closedBall (center p) (Δ ^ k) :=
      fun p => Classical.choose_spec (single_ball_covers_dyadicSquare (Δ ^ k) hΔk_pos p.1 p.2)
    let D : Finset EuclideanPlane := Tne.image center
    have hD_cover : Metric.IsCover ε0 P D := by
      rw [Metric.isCover_iff_subset_iUnion_closedBall]
      intro y hy
      let a : ℤ := ⌊y 0 / (Δ ^ k)⌋
      let b : ℤ := ⌊y 1 / (Δ ^ k)⌋
      have hyQ : y ∈ Q (a, b) := by
        simp only [Q]
        constructor
        · constructor
          · have h1 : (a : ℝ) ≤ y 0 / (Δ ^ k) := Int.floor_le (y 0 / (Δ ^ k))
            calc (a : ℝ) * (Δ ^ k) ≤ (y 0 / (Δ ^ k)) * (Δ ^ k) := by gcongr
              _ = y 0 := by field_simp [hΔk_pos.ne'] <;> ring
          · have h2 : y 0 / (Δ ^ k) < (a + 1 : ℝ) := Int.lt_floor_add_one (y 0 / (Δ ^ k))
            calc y 0 = (y 0 / (Δ ^ k)) * (Δ ^ k) := by field_simp [hΔk_pos.ne'] <;> ring
              _ < ((a + 1 : ℝ)) * (Δ ^ k) := by gcongr
        · constructor
          · have h1 : (b : ℝ) ≤ y 1 / (Δ ^ k) := Int.floor_le (y 1 / (Δ ^ k))
            calc (b : ℝ) * (Δ ^ k) ≤ (y 1 / (Δ ^ k)) * (Δ ^ k) := by gcongr
              _ = y 1 := by field_simp [hΔk_pos.ne'] <;> ring
          · have h2 : y 1 / (Δ ^ k) < (b + 1 : ℝ) := Int.lt_floor_add_one (y 1 / (Δ ^ k))
            calc y 1 = (y 1 / (Δ ^ k)) * (Δ ^ k) := by field_simp [hΔk_pos.ne'] <;> ring
              _ < ((b + 1 : ℝ)) * (Δ ^ k) := by gcongr
      have hne : (P ∩ Q (a, b)).Nonempty := ⟨y, hy, hyQ⟩
      have h3 : ∃ c : EuclideanPlane, c ∈ C ∧ y ∈ Metric.closedBall c ε1 := by
        have h4 := hC_cover.subset_iUnion_closedBall hy
        simpa [Set.mem_iUnion] using h4
      rcases h3 with ⟨c, hcC, hcBall⟩
      have hdist : dist y c ≤ Δ ^ (k + 1) := by
        simpa [ε1, Metric.mem_closedBall, show 0 ≤ Δ ^ (k + 1) by positivity] using hcBall
      have h_int : (Metric.closedBall c (Δ ^ (k + 1)) ∩ Q (a, b)).Nonempty :=
        ⟨y, by simpa [Metric.mem_closedBall] using hdist, hyQ⟩
      have habS : (a, b) ∈ S c := hS1 c a b h_int
      have habT : (a, b) ∈ T := Finset.mem_biUnion.mpr ⟨c, hcC, habS⟩
      have habTne : (a, b) ∈ Tne := by
        simp only [Tne, Finset.mem_filter]; exact ⟨habT, hne⟩
      have hcinD : center (a, b) ∈ D := Finset.mem_image.mpr ⟨(a, b), habTne, rfl⟩
      have hyball : y ∈ Metric.closedBall (center (a, b)) ε0 := by
        have h5 : y ∈ Q (a, b) := hyQ
        have h6 : Q (a, b) ⊆ Metric.closedBall (center (a, b)) (Δ ^ k) := hcenter (a, b)
        have h7 : y ∈ Metric.closedBall (center (a, b)) (Δ ^ k) := h6 h5
        simpa [ε0, Metric.mem_closedBall, show 0 ≤ Δ ^ k by positivity] using h7
      exact Set.mem_iUnion₂.mpr ⟨center (a, b), hcinD, hyball⟩
    have h_cover0 : Metric.externalCoveringNumber ε0 P ≤ (D : Set EuclideanPlane).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hD_cover
    have h_cover0' : Metric.externalCoveringNumber ε0 P ≤ ↑(D.card) := by
      have h_eq : (D : Set EuclideanPlane).encard = ↑(D.card) := by
        simp
      rw [h_eq] at h_cover0
      exact h_cover0
    have hDcard : D.card ≤ Tne.card := Finset.card_image_le
    have h4 : (Metric.externalCoveringNumber ε0 P : ENNReal) ≤ (Tne.card : ENNReal) := by
      have h5 : (Metric.externalCoveringNumber ε0 P : ENNReal) ≤ (↑(D.card) : ENNReal) := enat_to_ennreal_mono h_cover0'
      have h6 : (↑(D.card) : ENNReal) ≤ (↑(Tne.card) : ENNReal) := by exact_mod_cast hDcard
      exact le_trans h5 h6
    have h_prod_le : Tne.card * N k ≤ 4 * C.card := by
      have h_sum1 : Tne.card * N k ≤ ∑ p ∈ Tne, (Cp p).card := by
        have h : ∑ p ∈ Tne, (Cp p).card ≥ ∑ p ∈ Tne, N k := by
          apply Finset.sum_le_sum
          intro p hp
          exact_mod_cast h_card_p p hp
        have h2 : ∑ p ∈ Tne, (N k) = Tne.card * N k := by
          rw [Finset.sum_const] <;> ring
        linarith
      linarith [h_sum]
    have h5 : (Tne.card : ENNReal) * (N k : ENNReal) ≤ (4 : ENNReal) * (C.card : ENNReal) := by
      exact_mod_cast h_prod_le
    have h6 : (Metric.externalCoveringNumber ε0 P : ENNReal) * (N k : ENNReal) ≤ (4 : ENNReal) * (C.card : ENNReal) := by
      calc (Metric.externalCoveringNumber ε0 P : ENNReal) * (N k : ENNReal)
        ≤ (Tne.card : ENNReal) * (N k : ENNReal) := by gcongr
      _ ≤ (4 : ENNReal) * (C.card : ENNReal) := h5
    have hC_ne_top : (C.card : ENNReal) ≠ ⊤ := by simp
    have h7 : (Metric.externalCoveringNumber ε0 P : ENNReal) * (N k : ENNReal) / 4 ≤ (C.card : ENNReal) := by
      have h9 : (4 : ENNReal) * (C.card : ENNReal) / 4 = (C.card : ENNReal) := by
        have h_comm : (4 : ENNReal) * (C.card : ENNReal) = (C.card : ENNReal) * (4 : ENNReal) := by
          exact mul_comm _ _
        rw [h_comm]
        exact ENNReal.mul_div_cancel_right (by simp) (by simp)
      calc (Metric.externalCoveringNumber ε0 P : ENNReal) * (N k : ENNReal) / 4
        ≤ (4 : ENNReal) * (C.card : ENNReal) / 4 := by gcongr
      _ = (C.card : ENNReal) := h9
    have h8 : (C.card : ENNReal) ≤ (Metric.externalCoveringNumber ε1 P : ENNReal) := hC_card
    exact le_trans h7 h8

/-- Helper: division of `ofReal` values. -/
lemma ennreal_ofReal_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    ENNReal.ofReal a / ENNReal.ofReal b = ENNReal.ofReal (a / b) :=
  (ENNReal.ofReal_div_of_pos hb).symm

lemma covering_product_lower {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsUniform P m Δ N) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (Metric.externalCoveringNumber (Δ ^ m).toNNReal P : ENNReal) ≥
      (↑(∏ i ∈ Finset.range m, N i) : ENNReal) / (4 : ENNReal) ^ m := by
  have h_main : ∀ (k : ℕ), IsUniform P k Δ N →
    (Metric.externalCoveringNumber (Δ ^ k).toNNReal P : ENNReal) ≥
      (↑(∏ i ∈ Finset.range k, N i) : ENNReal) / (4 : ENNReal) ^ k := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h_nonempty : P.Nonempty := hk.2.2.1
      have h_ne_zero : Metric.externalCoveringNumber (Δ ^ 0).toNNReal P ≠ 0 :=
        have h_pos : 0 < Metric.externalCoveringNumber (Δ ^ 0).toNNReal P :=
          Metric.externalCoveringNumber_pos_iff.mpr h_nonempty
        ne_of_gt h_pos
      have h1 : (1 : ENat) ≤ Metric.externalCoveringNumber (Δ ^ 0).toNNReal P := by
        exact Order.one_le_iff_ne_zero.mpr h_ne_zero
      have h2 : (1 : ENNReal) ≤ (Metric.externalCoveringNumber (Δ ^ 0).toNNReal P : ENNReal) := by
        exact_mod_cast h1
      simpa using h2
    | succ k ih =>
      intro hk
      let hk' : IsUniform P k Δ N :=
        ⟨hk.1, hk.2.1, hk.2.2.1,
         fun i hi => hk.2.2.2.1 i (by linarith),
         fun i hi => hk.2.2.2.2 i (by linarith)⟩
      have h_ih' := ih hk'
      by_cases h_half : Δ ≤ 1 / 2
      · -- Δ ≤ 1/2: use covering_step_lower
        have h_step := covering_step_lower hk h_half
        set B : ENNReal := (↑(∏ i ∈ Finset.range k, N i) : ENNReal) / (4 : ENNReal) ^ k with hB_def
        set A : ENNReal := (Metric.externalCoveringNumber (Δ ^ k).toNNReal P : ENNReal) with hA_def
        have h_ineq : B ≤ A := h_ih'
        have h4_ne : (4 : ENNReal) ≠ 0 := by simp
        have h4_top : (4 : ENNReal) ≠ ⊤ := by simp
        have h_assoc : ∀ (x : ENNReal), x * (N k : ENNReal) / 4 = x * ((N k : ENNReal) / 4) := by
          intro x
          simp [div_eq_mul_inv, mul_assoc]
        have h_mul_le : B * (N k : ENNReal) / 4 ≤ A * (N k : ENNReal) / 4 := by
          rw [h_assoc B, h_assoc A]
          exact mul_le_mul_of_nonneg_right h_ineq (by positivity)
        let X : ENNReal := (↑(∏ i ∈ Finset.range k, N i) : ENNReal)
        let Y : ENNReal := (4 : ENNReal) ^ k
        let Z : ENNReal := (N k : ENNReal)
        have hB2 : B = X / Y := by rfl
        have h_prod : (↑(∏ i ∈ Finset.range (k + 1), N i) : ENNReal) = X * Z := by
          simp [X, Z, Finset.prod_range_succ, ENNReal.coe_mul] <;> norm_cast
        have h_pow : (4 : ENNReal) ^ (k + 1) = Y * 4 := by
          simp [Y, pow_succ] <;> ring
        have h1 : (X / Y) * Z = X * Z / Y := by
          simp only [div_eq_mul_inv]
          have h : (X * Y⁻¹) * Z = X * Z * Y⁻¹ := by
            simp [mul_assoc, mul_comm, mul_left_comm] <;> ac_rfl
          rw [h]
          <;> simp only [div_eq_mul_inv]
        let x : ℝ := (∏ i ∈ Finset.range k, N i : ℝ)
        let y : ℝ := (4 ^ k : ℝ)
        let z : ℝ := (N k : ℝ)
        have hX : X = ENNReal.ofReal x := by simp [X, x] <;> norm_cast
        have hY : Y = ENNReal.ofReal y := by simp [Y, y] <;> norm_cast
        have hZ : Z = ENNReal.ofReal z := by simp [Z, z] <;> norm_cast
        have h_pos_y : 0 < y := by simp [y] <;> positivity
        have h_nonneg_x : 0 ≤ x := by simp [x] <;> positivity
        have h_nonneg_z : 0 ≤ z := by simp [z] <;> positivity
        have h_eq_real : (x / y) * z / 4 = (x * z) / (y * 4) := by
          field_simp [h_pos_y.ne'] <;> ring
        have h_div : (X / Y) * Z / 4 = (X * Z) / (Y * 4) := by
          rw [hX, hY, hZ]
          have h4_pos : (0 : ℝ) < 4 := by norm_num
          have h_left : (ENNReal.ofReal x / ENNReal.ofReal y) * ENNReal.ofReal z / 4 =
              ENNReal.ofReal ((x / y) * z / 4) := by
            have h1 : (ENNReal.ofReal x / ENNReal.ofReal y) = ENNReal.ofReal (x / y) :=
              ennreal_ofReal_div h_nonneg_x h_pos_y
            rw [h1]
            have h_nonneg1 : 0 ≤ x / y := by positivity
            have h2 : ENNReal.ofReal ((x / y) * z) = ENNReal.ofReal (x / y) * ENNReal.ofReal z :=
              ENNReal.ofReal_mul h_nonneg1
            rw [←h2]
            have h3 : (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) := by norm_cast
            rw [h3]
            exact ennreal_ofReal_div (by positivity) (by norm_num)
          have h_right : (ENNReal.ofReal x * ENNReal.ofReal z) / (ENNReal.ofReal y * 4) =
              ENNReal.ofReal ((x * z) / (y * 4)) := by
            have h4 : (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) := by norm_cast
            have h_y4 : ENNReal.ofReal y * (4 : ENNReal) = ENNReal.ofReal (y * 4) := by
              rw [h4]
              have h : ENNReal.ofReal (y * (4 : ℝ)) = ENNReal.ofReal y * ENNReal.ofReal (4 : ℝ) :=
                ENNReal.ofReal_mul h_pos_y.le
              exact h.symm
            have h_xz : ENNReal.ofReal (x * z) = ENNReal.ofReal x * ENNReal.ofReal z :=
              ENNReal.ofReal_mul h_nonneg_x
            rw [h_y4, ←h_xz]
            exact ennreal_ofReal_div (mul_nonneg h_nonneg_x h_nonneg_z) (mul_pos h_pos_y h4_pos)
          rw [h_left, h_right, h_eq_real]
        have h_eq : B * Z / 4 = (↑(∏ i ∈ Finset.range (k + 1), N i) : ENNReal) / (4 : ENNReal) ^ (k + 1) := by
          calc B * Z / 4
            = (X / Y) * Z / 4 := by rw [hB2]
          _ = (X * Z) / (Y * 4) := h_div
          _ = (↑(∏ i ∈ Finset.range (k + 1), N i) : ENNReal) / (Y * 4) := by rw [h_prod]
          _ = (↑(∏ i ∈ Finset.range (k + 1), N i) : ENNReal) / (4 : ENNReal) ^ (k + 1) := by rw [h_pow]
        calc (Metric.externalCoveringNumber (Δ ^ (k + 1)).toNNReal P : ENNReal)
          ≥ A * (N k : ENNReal) / 4 := h_step
        _ ≥ B * (N k : ENNReal) / 4 := h_mul_le
        _ = (↑(∏ i ∈ Finset.range (k + 1), N i) : ENNReal) / (4 : ENNReal) ^ (k + 1) := h_eq
      · -- Δ > 1/2: all N(i) ≤ 4, so RHS ≤ 1
        have h_half' : Δ > 1 / 2 := by linarith
        have hN4 : ∀ i < k + 1, N i ≤ 4 := by
          intro i hi
          have hP_ne : P.Nonempty := hk.2.2.1
          rcases hP_ne with ⟨x, hx⟩
          let a : ℤ := ⌊x 0 / (Δ ^ i)⌋
          let b : ℤ := ⌊x 1 / (Δ ^ i)⌋
          have h_x_in_square : x ∈ dyadicSquare (Δ ^ i) a b := by
            have hΔi_pos : 0 < Δ ^ i := by positivity
            simp only [dyadicSquare]
            have h1a : (a : ℝ) ≤ x 0 / (Δ ^ i) := Int.floor_le (x 0 / (Δ ^ i))
            have h2a : x 0 / (Δ ^ i) < (a : ℝ) + 1 := Int.lt_floor_add_one (x 0 / (Δ ^ i))
            have h1b : (b : ℝ) ≤ x 1 / (Δ ^ i) := Int.floor_le (x 1 / (Δ ^ i))
            have h2b : x 1 / (Δ ^ i) < (b : ℝ) + 1 := Int.lt_floor_add_one (x 1 / (Δ ^ i))
            have ha1 : (a : ℝ) * (Δ ^ i) ≤ x 0 := by
              have h : (Δ ^ i) * (a : ℝ) ≤ (Δ ^ i) * (x 0 / (Δ ^ i)) := by gcongr
              have h' : (Δ ^ i) * (x 0 / (Δ ^ i)) = x 0 := by field_simp [hΔi_pos.ne'] <;> ring
              have h'' : (a : ℝ) * (Δ ^ i) = (Δ ^ i) * (a : ℝ) := by ring
              rw [h'']
              linarith
            have ha2 : x 0 < ((a : ℝ) + 1) * (Δ ^ i) := by
              have h : x 0 = (Δ ^ i) * (x 0 / (Δ ^ i)) := by field_simp [hΔi_pos.ne'] <;> ring
              have h' : (Δ ^ i) * (x 0 / (Δ ^ i)) < (Δ ^ i) * ((a : ℝ) + 1) := by gcongr
              have h'' : ((a : ℝ) + 1) * (Δ ^ i) = (Δ ^ i) * ((a : ℝ) + 1) := by ring
              rw [h'']
              linarith
            have hb1 : (b : ℝ) * (Δ ^ i) ≤ x 1 := by
              have h : (Δ ^ i) * (b : ℝ) ≤ (Δ ^ i) * (x 1 / (Δ ^ i)) := by gcongr
              have h' : (Δ ^ i) * (x 1 / (Δ ^ i)) = x 1 := by field_simp [hΔi_pos.ne'] <;> ring
              have h'' : (b : ℝ) * (Δ ^ i) = (Δ ^ i) * (b : ℝ) := by ring
              rw [h'']
              linarith
            have hb2 : x 1 < ((b : ℝ) + 1) * (Δ ^ i) := by
              have h : x 1 = (Δ ^ i) * (x 1 / (Δ ^ i)) := by field_simp [hΔi_pos.ne'] <;> ring
              have h' : (Δ ^ i) * (x 1 / (Δ ^ i)) < (Δ ^ i) * ((b : ℝ) + 1) := by gcongr
              have h'' : ((b : ℝ) + 1) * (Δ ^ i) = (Δ ^ i) * ((b : ℝ) + 1) := by ring
              rw [h'']
              linarith
            exact ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩
          have hne : (P ∩ dyadicSquare (Δ ^ i) a b).Nonempty := ⟨x, hx, h_x_in_square⟩
          have h_cov : (Metric.externalCoveringNumber (Δ ^ (i + 1)).toNNReal
              (P ∩ dyadicSquare (Δ ^ i) a b) : ENNReal) = (↑(N i) : ENNReal) :=
            hk.2.2.2.2 i hi a b hne
          have hΔi_pos : 0 < Δ ^ i := by positivity
          have hΔi1_pos : 0 < Δ ^ (i + 1) := by positivity
          have h_r : Δ ^ (i + 1) ≥ (Δ ^ i) * Real.sqrt 2 / 4 := by
            have h1 : Δ > 1 / 2 := h_half'
            calc Δ ^ (i + 1) = Δ * Δ ^ i := by ring
              _ ≥ (1 / 2 : ℝ) * Δ ^ i := by gcongr
              _ ≥ (Δ ^ i) * Real.sqrt 2 / 4 := by
                have h2 : (1 / 2 : ℝ) ≥ Real.sqrt 2 / 4 := by
                  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                have h3 : (1 / 2 : ℝ) * Δ ^ i ≥ (Δ ^ i) * Real.sqrt 2 / 4 := by
                  calc (1 / 2 : ℝ) * Δ ^ i
                    = (Δ ^ i) * (1 / 2 : ℝ) := by ring
                  _ ≥ (Δ ^ i) * (Real.sqrt 2 / 4) := by gcongr
                  _ = (Δ ^ i) * Real.sqrt 2 / 4 := by ring
                exact h3
          rcases four_balls_cover_square (Δ ^ i) (Δ ^ (i + 1)) hΔi_pos hΔi1_pos h_r a b with ⟨c, hcover, hcard⟩
          have h9 : (↑((Δ ^ (i + 1)).toNNReal) : ℝ) = Δ ^ (i + 1) := by
            have h_nonneg : 0 ≤ Δ ^ (i + 1) := by linarith
            exact Real.coe_toNNReal (Δ ^ (i + 1)) h_nonneg
          have h_ball_eq : ∀ (x : EuclideanPlane), Metric.closedBall x (Δ ^ (i + 1)) = Metric.closedBall x ((Δ ^ (i + 1)).toNNReal) := by
            intro x
            apply congr_arg (fun r : ℝ => Metric.closedBall x r)
            exact h9.symm
          have h10 : (⋃ x ∈ c, Metric.closedBall x (Δ ^ (i + 1))) =
              (⋃ x ∈ c, Metric.closedBall x ((Δ ^ (i + 1)).toNNReal)) := by
            have h_congr : ∀ (x : EuclideanPlane), x ∈ c →
                Metric.closedBall x (Δ ^ (i + 1)) = Metric.closedBall x ((Δ ^ (i + 1)).toNNReal) :=
              fun x _ => h_ball_eq x
            exact Set.iUnion₂_congr h_congr
          have h_sub : P ∩ dyadicSquare (Δ ^ i) a b ⊆ ⋃ x ∈ c, Metric.closedBall x (Δ ^ (i + 1)).toNNReal := by
            rw [←h10]
            exact Set.Subset.trans (Set.inter_subset_right) hcover
          have h_iscover : Metric.IsCover (Δ ^ (i + 1)).toNNReal (P ∩ dyadicSquare (Δ ^ i) a b) c := by
            rw [Metric.isCover_iff_subset_iUnion_closedBall]; exact h_sub
          have h_le : Metric.externalCoveringNumber (Δ ^ (i + 1)).toNNReal (P ∩ dyadicSquare (Δ ^ i) a b) ≤ (c : Set EuclideanPlane).encard :=
            Metric.IsCover.externalCoveringNumber_le_encard h_iscover
          have h_eq_encard : (c : Set EuclideanPlane).encard = ↑(c.card) := by simp
          have h_le' : Metric.externalCoveringNumber (Δ ^ (i + 1)).toNNReal (P ∩ dyadicSquare (Δ ^ i) a b) ≤ ↑(c.card) := by
            rw [h_eq_encard] at h_le; exact h_le
          have h_enat : (Metric.externalCoveringNumber (Δ ^ (i + 1)).toNNReal (P ∩ dyadicSquare (Δ ^ i) a b) : ENNReal) ≤ (4 : ENNReal) := by
            have h5 : (Metric.externalCoveringNumber (Δ ^ (i + 1)).toNNReal (P ∩ dyadicSquare (Δ ^ i) a b) : ENNReal) ≤ (↑(c.card) : ENNReal) :=
              enat_to_ennreal_mono h_le'
            have h6 : (↑(c.card) : ENNReal) ≤ (4 : ENNReal) := by exact_mod_cast hcard
            exact le_trans h5 h6
          rw [h_cov] at h_enat
          exact_mod_cast h_enat
        have h_prod4 : (∏ i ∈ Finset.range (k + 1), N i) ≤ 4 ^ (k + 1) := by
          have h1 : ∀ i ∈ Finset.range (k + 1), N i ≤ 4 := fun i hi => hN4 i (Finset.mem_range.mp hi)
          have h_nonneg : ∀ i ∈ Finset.range (k + 1), 0 ≤ N i := fun i _ => Nat.zero_le (N i)
          calc ∏ i ∈ Finset.range (k + 1), N i
            ≤ ∏ i ∈ Finset.range (k + 1), 4 := Finset.prod_le_prod h_nonneg h1
          _ = 4 ^ (k + 1) := by simp
        have h_rhs_le_one : (↑(∏ i ∈ Finset.range (k + 1), N i) : ENNReal) / (4 : ENNReal) ^ (k + 1) ≤ 1 := by
          have h2 : (↑(∏ i ∈ Finset.range (k + 1), N i) : ENNReal) ≤ (↑(4 ^ (k + 1)) : ENNReal) := by exact_mod_cast h_prod4
          have h3 : (↑(4 ^ (k + 1)) : ENNReal) = (4 : ENNReal) ^ (k + 1) := by simp
          rw [h3] at h2
          have h4 : (↑(∏ i ∈ Finset.range (k + 1), N i) : ENNReal) / (4 : ENNReal) ^ (k + 1) ≤ 1 := by
            calc (↑(∏ i ∈ Finset.range (k + 1), N i) : ENNReal) / (4 : ENNReal) ^ (k + 1)
              ≤ (4 : ENNReal) ^ (k + 1) / (4 : ENNReal) ^ (k + 1) := by gcongr
            _ = 1 := by
              have h5 : (4 : ENNReal) ^ (k + 1) ≠ 0 := by simp
              have h6 : (4 : ENNReal) ^ (k + 1) ≠ ⊤ := by simp
              rw [ENNReal.div_self h5 h6]
          exact h4
        have h_nonempty : P.Nonempty := hk.2.2.1
        have h_pos_enat : 0 < Metric.externalCoveringNumber (Δ ^ (k + 1)).toNNReal P := by
          exact Metric.externalCoveringNumber_pos_iff.mpr h_nonempty
        have h1_enat : 1 ≤ Metric.externalCoveringNumber (Δ ^ (k + 1)).toNNReal P := by
          exact Order.one_le_iff_pos.mpr h_pos_enat
        have h5 : (1 : ENNReal) ≤ (Metric.externalCoveringNumber (Δ ^ (k + 1)).toNNReal P : ENNReal) := by
          exact_mod_cast h1_enat
        exact le_trans h_rhs_le_one h5
  exact h_main m h_uniform

/-! # Dyadic uniformity covering products

With `IsDyadicUniform`, the exact metric covering equality is replaced by a
dyadic square count equality. Since each ball of radius Δ^(k+1) intersects at
most 9 fine squares and at most 4 coarse squares, the lower-bound factor
becomes 36 = 9 × 4 instead of 4.
-/

/-- Single-step lower bound for IsDyadicUniform:
covering_number(Δ^{k+1}, P) ≥ covering_number(Δ^k, P) * N(k) / 36. -/
lemma dyadic_covering_step_lower {P : Set EuclideanPlane} {k : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P (k + 1) Δ N) (hΔ2 : Δ ≤ 1 / 2) :
    (Metric.externalCoveringNumber (Δ ^ (k + 1)).toNNReal P : ENNReal) ≥
      (Metric.externalCoveringNumber (Δ ^ k).toNNReal P : ENNReal) * (N k : ENNReal) / 36 := by
  let ε1 := (Δ ^ (k + 1)).toNNReal
  let ε0 := (Δ ^ k).toNNReal
  have hΔ : 0 < Δ := h_uniform.1
  have hΔk_pos : 0 < Δ ^ k := by positivity
  have hΔk1_pos : 0 < Δ ^ (k + 1) := by positivity
  have h_rle : Δ ^ (k + 1) ≤ (Δ ^ k) / 2 := by
    calc Δ ^ (k + 1) = Δ * Δ ^ k := by ring
      _ ≤ (1 / 2 : ℝ) * Δ ^ k := by gcongr
      _ = (Δ ^ k) / 2 := by ring
  by_cases h_top1 : (Metric.externalCoveringNumber ε1 P : ENNReal) = ⊤
  · rw [h_top1] <;> simp
  · classical
    rcases exists_finite_cover_le (le_refl (Metric.externalCoveringNumber ε1 P : ENNReal)) h_top1 with ⟨C, hC_cover, hC_card⟩
    let S (c : EuclideanPlane) : Finset (ℤ × ℤ) :=
      Classical.choose (ball_dyadic_squares_bound (Δ ^ (k + 1)) hΔk1_pos c)
    have hS1 (c : EuclideanPlane) : ∀ (i j : ℤ),
        (Metric.closedBall c (Δ ^ (k + 1)) ∩ dyadicSquare (Δ ^ (k + 1)) i j).Nonempty → (i, j) ∈ S c :=
      (Classical.choose_spec (ball_dyadic_squares_bound (Δ ^ (k + 1)) hΔk1_pos c)).1
    have hS2 (c : EuclideanPlane) : (S c).card ≤ 9 :=
      (Classical.choose_spec (ball_dyadic_squares_bound (Δ ^ (k + 1)) hΔk1_pos c)).2
    let Tc (c : EuclideanPlane) : Finset (ℤ × ℤ) :=
      Classical.choose (ball_dyadic_squares_bound_4 (Δ ^ k) (Δ ^ (k + 1)) hΔk_pos hΔk1_pos h_rle c)
    have hTc1 (c : EuclideanPlane) : ∀ (i j : ℤ),
        (Metric.closedBall c (Δ ^ (k + 1)) ∩ dyadicSquare (Δ ^ k) i j).Nonempty → (i, j) ∈ Tc c :=
      (Classical.choose_spec (ball_dyadic_squares_bound_4 (Δ ^ k) (Δ ^ (k + 1)) hΔk_pos hΔk1_pos h_rle c)).1
    have hTc2 (c : EuclideanPlane) : (Tc c).card ≤ 4 :=
      (Classical.choose_spec (ball_dyadic_squares_bound_4 (Δ ^ k) (Δ ^ (k + 1)) hΔk_pos hΔk1_pos h_rle c)).2
    let T : Finset (ℤ × ℤ) := C.biUnion Tc
    let Q (p : ℤ × ℤ) := dyadicSquare (Δ ^ k) p.1 p.2
    let Tne := T.filter (fun p => (P ∩ Q p).Nonempty)
    let Cp (p : ℤ × ℤ) := C.filter (fun c => p ∈ Tc c)
    have h_cov_p : ∀ p ∈ Tne, Metric.IsCover ε1 (P ∩ Q p) (Cp p) := by
      intro p hp
      rw [Metric.isCover_iff_subset_iUnion_closedBall]
      intro y hy
      have yP : y ∈ P := hy.1; have yQ : y ∈ Q p := hy.2
      have h2 : y ∈ ⋃ c ∈ C, Metric.closedBall c ε1 := hC_cover.subset_iUnion_closedBall yP
      rcases Set.mem_iUnion₂.mp h2 with ⟨c, hcC, hcBall⟩
      have hdist : dist y c ≤ Δ ^ (k + 1) := by
        simpa [ε1, Metric.mem_closedBall, show 0 ≤ Δ ^ (k + 1) by positivity] using hcBall
      have h_int : (Metric.closedBall c (Δ ^ (k + 1)) ∩ Q p).Nonempty :=
        ⟨y, by simpa [Metric.mem_closedBall] using hdist, yQ⟩
      have hps : p ∈ Tc c := hTc1 c p.1 p.2 h_int
      have hcp : c ∈ Cp p := by simp [Cp, hcC, hps]
      exact Set.mem_iUnion₂.mpr ⟨c, hcp, hcBall⟩
    have h_card_p : ∀ p ∈ Tne, (N k : ENNReal) ≤ (9 : ENNReal) * ((Cp p).card : ENNReal) := by
      intro p hp
      have hne : (P ∩ Q p).Nonempty := (Finset.mem_filter.mp hp).2
      have h_unif : (dyadicSquareCount (Δ ^ (k + 1)) (P ∩ Q p) : ENNReal) = (↑(N k) : ENNReal) :=
        h_uniform.2.2.2.2 k (by linarith) p.1 p.2 hne
      let F : Finset (ℤ × ℤ) := (Cp p).biUnion S
      have hF_cover : ∀ (i j : ℤ), (P ∩ Q p ∩ dyadicSquare (Δ ^ (k + 1)) i j).Nonempty → (i, j) ∈ F := by
        intro i j h_int
        rcases h_int with ⟨y, hyPQ, hyFine⟩
        have h2 : y ∈ ⋃ c ∈ Cp p, Metric.closedBall c ε1 := (h_cov_p p hp).subset_iUnion_closedBall hyPQ
        rcases Set.mem_iUnion₂.mp h2 with ⟨c, hcC, hcBall⟩
        have hdist : dist y c ≤ Δ ^ (k + 1) := by
          simpa [ε1, Metric.mem_closedBall, show 0 ≤ Δ ^ (k + 1) by positivity] using hcBall
        have h_int2 : (Metric.closedBall c (Δ ^ (k + 1)) ∩ dyadicSquare (Δ ^ (k + 1)) i j).Nonempty :=
          ⟨y, by simpa [Metric.mem_closedBall] using hdist, hyFine⟩
        have hps : (i, j) ∈ S c := hS1 c i j h_int2
        exact Finset.mem_biUnion.mpr ⟨c, hcC, hps⟩
      have hF_card : F.card ≤ 9 * (Cp p).card := by
        have h1 : F.card ≤ ∑ c ∈ Cp p, (S c).card := Finset.card_biUnion_le
        have h2 : ∑ c ∈ Cp p, (S c).card ≤ ∑ c ∈ Cp p, 9 := Finset.sum_le_sum (fun c _ => hS2 c)
        have h3 : ∑ c ∈ Cp p, (9 : ℕ) = 9 * (Cp p).card := by
          rw [Finset.sum_const] <;> ring
        rw [h3] at h2
        exact le_trans h1 h2
      have h_dyadic_le : (dyadicSquareCount (Δ ^ (k + 1)) (P ∩ Q p) : ENNReal) ≤ (↑(F.card) : ENNReal) := by
        have h_set : {q : ℤ × ℤ | (P ∩ Q p ∩ dyadicSquare (Δ ^ (k + 1)) q.1 q.2).Nonempty} ⊆ (F : Set (ℤ × ℤ)) := by
          intro q hq
          exact hF_cover q.1 q.2 hq
        have h_fin : Set.Finite {q : ℤ × ℤ | (P ∩ Q p ∩ dyadicSquare (Δ ^ (k + 1)) q.1 q.2).Nonempty} :=
          Set.Finite.subset (Finset.finite_toSet F) h_set
        have h1 : Set.encard _ ≤ Set.encard (↑F : Set (ℤ × ℤ)) := Set.encard_le_encard h_set
        have h2 : Set.encard (↑F : Set (ℤ × ℤ)) = ↑(F.card) := by simp
        rw [h2] at h1
        exact_mod_cast h1
      rw [h_unif] at h_dyadic_le
      have h4 : (↑(N k) : ENNReal) ≤ (↑(F.card) : ENNReal) := h_dyadic_le
      have h5 : (↑(F.card) : ENNReal) ≤ (9 : ENNReal) * ((Cp p).card : ENNReal) := by
        exact_mod_cast hF_card
      exact le_trans h4 h5
    have h_sum : ∑ p ∈ Tne, (Cp p).card ≤ 4 * C.card := by
      have h1 : ∑ p ∈ Tne, (Cp p).card ≤ ∑ p ∈ T, (Cp p).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
      have h2 : ∑ p ∈ T, (Cp p).card = ∑ c ∈ C, (Tc c).card := by
        have h3 : ∀ p ∈ T, (Cp p).card = ∑ c ∈ C, if p ∈ Tc c then 1 else 0 := by
          intro p _; simp [Cp, Finset.filter_eq'] <;> rfl
        calc ∑ p ∈ T, (Cp p).card
          = ∑ p ∈ T, ∑ c ∈ C, (if p ∈ Tc c then 1 else 0) := Finset.sum_congr rfl (fun p hp => h3 p hp)
        _ = ∑ c ∈ C, ∑ p ∈ T, (if p ∈ Tc c then 1 else 0) := by rw [Finset.sum_comm]
        _ = ∑ c ∈ C, (Tc c).card := by
          apply Finset.sum_congr rfl
          intro c hc
          have h4 : Tc c ⊆ T := by
            intro x hx; exact Finset.mem_biUnion.mpr ⟨c, hc, hx⟩
          have h5 : ∑ p ∈ T, (if p ∈ Tc c then 1 else 0) = (Tc c).card := by
            rw [Finset.sum_ite] <;> simp [h4] <;> rfl
          exact h5
      rw [h2] at h1
      have h4 : ∑ c ∈ C, (Tc c).card ≤ ∑ c ∈ C, 4 := Finset.sum_le_sum (fun c _ => hTc2 c)
      have h5 : ∑ c ∈ C, (4 : ℕ) = 4 * C.card := by
        rw [Finset.sum_const] <;> ring
      rw [h5] at h4
      exact le_trans h1 h4
    have h_prod_le : Tne.card * N k ≤ 36 * C.card := by
      have h_sum1 : Tne.card * N k ≤ ∑ p ∈ Tne, (9 * (Cp p).card) := by
        have h : ∑ p ∈ Tne, (N k) ≤ ∑ p ∈ Tne, (9 * (Cp p).card) := by
          apply Finset.sum_le_sum
          intro p hp
          have h6 : (N k : ENNReal) ≤ (9 : ENNReal) * ((Cp p).card : ENNReal) := h_card_p p hp
          exact_mod_cast h6
        have h2 : ∑ p ∈ Tne, (N k) = Tne.card * N k := by
          rw [Finset.sum_const] <;> ring
        linarith
      have h3 : ∑ p ∈ Tne, (9 * (Cp p).card) = 9 * ∑ p ∈ Tne, (Cp p).card := by
        rw [Finset.mul_sum]
      rw [h3] at h_sum1
      linarith [h_sum]
    let center (p : ℤ × ℤ) := Classical.choose (single_ball_covers_dyadicSquare (Δ ^ k) hΔk_pos p.1 p.2)
    have hcenter : ∀ p, Q p ⊆ Metric.closedBall (center p) (Δ ^ k) :=
      fun p => Classical.choose_spec (single_ball_covers_dyadicSquare (Δ ^ k) hΔk_pos p.1 p.2)
    let D : Finset EuclideanPlane := Tne.image center
    have hD_cover : Metric.IsCover ε0 P D := by
      rw [Metric.isCover_iff_subset_iUnion_closedBall]
      intro y hy
      let a : ℤ := ⌊y 0 / (Δ ^ k)⌋
      let b : ℤ := ⌊y 1 / (Δ ^ k)⌋
      have hyQ : y ∈ Q (a, b) := by
        simp only [Q]
        constructor
        · constructor
          · have h1 : (a : ℝ) ≤ y 0 / (Δ ^ k) := Int.floor_le (y 0 / (Δ ^ k))
            calc (a : ℝ) * (Δ ^ k) ≤ (y 0 / (Δ ^ k)) * (Δ ^ k) := by gcongr
              _ = y 0 := by field_simp [hΔk_pos.ne'] <;> ring
          · have h2 : y 0 / (Δ ^ k) < (a + 1 : ℝ) := Int.lt_floor_add_one (y 0 / (Δ ^ k))
            calc y 0 = (y 0 / (Δ ^ k)) * (Δ ^ k) := by field_simp [hΔk_pos.ne'] <;> ring
              _ < ((a + 1 : ℝ)) * (Δ ^ k) := by gcongr
        · constructor
          · have h1 : (b : ℝ) ≤ y 1 / (Δ ^ k) := Int.floor_le (y 1 / (Δ ^ k))
            calc (b : ℝ) * (Δ ^ k) ≤ (y 1 / (Δ ^ k)) * (Δ ^ k) := by gcongr
              _ = y 1 := by field_simp [hΔk_pos.ne'] <;> ring
          · have h2 : y 1 / (Δ ^ k) < (b + 1 : ℝ) := Int.lt_floor_add_one (y 1 / (Δ ^ k))
            calc y 1 = (y 1 / (Δ ^ k)) * (Δ ^ k) := by field_simp [hΔk_pos.ne'] <;> ring
              _ < ((b + 1 : ℝ)) * (Δ ^ k) := by gcongr
      have hne : (P ∩ Q (a, b)).Nonempty := ⟨y, hy, hyQ⟩
      have h3 : ∃ c : EuclideanPlane, c ∈ C ∧ y ∈ Metric.closedBall c ε1 := by
        have h4 := hC_cover.subset_iUnion_closedBall hy
        simpa [Set.mem_iUnion] using h4
      rcases h3 with ⟨c, hcC, hcBall⟩
      have hdist : dist y c ≤ Δ ^ (k + 1) := by
        simpa [ε1, Metric.mem_closedBall, show 0 ≤ Δ ^ (k + 1) by positivity] using hcBall
      have h_int : (Metric.closedBall c (Δ ^ (k + 1)) ∩ Q (a, b)).Nonempty :=
        ⟨y, by simpa [Metric.mem_closedBall] using hdist, hyQ⟩
      have habS : (a, b) ∈ Tc c := hTc1 c a b h_int
      have habT : (a, b) ∈ T := Finset.mem_biUnion.mpr ⟨c, hcC, habS⟩
      have habTne : (a, b) ∈ Tne := by
        simp only [Tne, Finset.mem_filter]; exact ⟨habT, hne⟩
      have hcinD : center (a, b) ∈ D := Finset.mem_image.mpr ⟨(a, b), habTne, rfl⟩
      have hyball : y ∈ Metric.closedBall (center (a, b)) ε0 := by
        have h5 : y ∈ Q (a, b) := hyQ
        have h6 : Q (a, b) ⊆ Metric.closedBall (center (a, b)) (Δ ^ k) := hcenter (a, b)
        have h7 : y ∈ Metric.closedBall (center (a, b)) (Δ ^ k) := h6 h5
        simpa [ε0, Metric.mem_closedBall, show 0 ≤ Δ ^ k by positivity] using h7
      exact Set.mem_iUnion₂.mpr ⟨center (a, b), hcinD, hyball⟩
    have h_cover0 : Metric.externalCoveringNumber ε0 P ≤ (D : Set EuclideanPlane).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hD_cover
    have h_cover0' : Metric.externalCoveringNumber ε0 P ≤ ↑(D.card) := by
      have h_eq : (D : Set EuclideanPlane).encard = ↑(D.card) := by simp
      rw [h_eq] at h_cover0; exact h_cover0
    have hDcard : D.card ≤ Tne.card := Finset.card_image_le
    have h4 : (Metric.externalCoveringNumber ε0 P : ENNReal) ≤ (Tne.card : ENNReal) := by
      have h5 : (Metric.externalCoveringNumber ε0 P : ENNReal) ≤ (↑(D.card) : ENNReal) := enat_to_ennreal_mono h_cover0'
      have h6 : (↑(D.card) : ENNReal) ≤ (↑(Tne.card) : ENNReal) := by exact_mod_cast hDcard
      exact le_trans h5 h6
    have h5 : (Metric.externalCoveringNumber ε0 P : ENNReal) * (N k : ENNReal) ≤ (36 : ENNReal) * (C.card : ENNReal) := by
      have h6 : (Tne.card : ENNReal) * (N k : ENNReal) ≤ (36 : ENNReal) * (C.card : ENNReal) := by
        exact_mod_cast h_prod_le
      calc (Metric.externalCoveringNumber ε0 P : ENNReal) * (N k : ENNReal)
        ≤ (Tne.card : ENNReal) * (N k : ENNReal) := by gcongr
      _ ≤ (36 : ENNReal) * (C.card : ENNReal) := h6
    have h7 : (Metric.externalCoveringNumber ε0 P : ENNReal) * (N k : ENNReal) / 36 ≤ (C.card : ENNReal) := by
      have h9 : (36 : ENNReal) * (C.card : ENNReal) / 36 = (C.card : ENNReal) := by
        have h_comm : (36 : ENNReal) * (C.card : ENNReal) = (C.card : ENNReal) * (36 : ENNReal) := by exact mul_comm _ _
        rw [h_comm]
        exact ENNReal.mul_div_cancel_right (by simp) (by simp)
      calc (Metric.externalCoveringNumber ε0 P : ENNReal) * (N k : ENNReal) / 36
        ≤ (36 : ENNReal) * (C.card : ENNReal) / 36 := by gcongr
      _ = (C.card : ENNReal) := h9
    have h8 : (C.card : ENNReal) ≤ (Metric.externalCoveringNumber ε1 P : ENNReal) := hC_card
    exact le_trans h7 h8

/-- Product lower bound for IsDyadicUniform:
N_{Δ^m}(P) ≥ (∏ N_i) / 36^m. Requires Δ ≤ 1/2. -/
lemma dyadic_covering_product_lower {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hΔ2 : Δ ≤ 1 / 2) :
    (Metric.externalCoveringNumber (Δ ^ m).toNNReal P : ENNReal) ≥
      (↑(∏ i ∈ Finset.range m, N i) : ENNReal) / (36 : ENNReal) ^ m := by
  have h_main : ∀ (k : ℕ), IsDyadicUniform P k Δ N →
    (Metric.externalCoveringNumber (Δ ^ k).toNNReal P : ENNReal) ≥
      (↑(∏ i ∈ Finset.range k, N i) : ENNReal) / (36 : ENNReal) ^ k := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h_nonempty : P.Nonempty := hk.2.2.1
      have h_ne_zero : Metric.externalCoveringNumber (Δ ^ 0).toNNReal P ≠ 0 :=
        have h_pos : 0 < Metric.externalCoveringNumber (Δ ^ 0).toNNReal P :=
          Metric.externalCoveringNumber_pos_iff.mpr h_nonempty
        ne_of_gt h_pos
      have h1 : (1 : ENat) ≤ Metric.externalCoveringNumber (Δ ^ 0).toNNReal P := by exact Order.one_le_iff_ne_zero.mpr h_ne_zero
      have h2 : (1 : ENNReal) ≤ (Metric.externalCoveringNumber (Δ ^ 0).toNNReal P : ENNReal) := by
        exact_mod_cast h1
      simpa using h2
    | succ k ih =>
      intro hk
      let hk' : IsDyadicUniform P k Δ N :=
        ⟨hk.1, hk.2.1, hk.2.2.1,
         fun i hi => hk.2.2.2.1 i (by linarith),
         fun i hi => hk.2.2.2.2 i (by linarith)⟩
      have h_ih' := ih hk'
      have h_step := dyadic_covering_step_lower hk hΔ2
      set B : ENNReal := (↑(∏ i ∈ Finset.range k, N i) : ENNReal) / (36 : ENNReal) ^ k with hB_def
      set A : ENNReal := (Metric.externalCoveringNumber (Δ ^ k).toNNReal P : ENNReal) with hA_def
      have h_ineq : B ≤ A := h_ih'
      have h36_ne : (36 : ENNReal) ≠ 0 := by simp
      have h36_top : (36 : ENNReal) ≠ ⊤ := by simp
      have h_assoc : ∀ (x : ENNReal), x * (N k : ENNReal) / 36 = x * ((N k : ENNReal) / 36) := by
        intro x; simp [div_eq_mul_inv, mul_assoc]
      have h_mul_le : B * (N k : ENNReal) / 36 ≤ A * (N k : ENNReal) / 36 := by
        rw [h_assoc B, h_assoc A]
        exact mul_le_mul_of_nonneg_right h_ineq (by positivity)
      let X : ENNReal := (↑(∏ i ∈ Finset.range k, N i) : ENNReal)
      let Y : ENNReal := (36 : ENNReal) ^ k
      let Z : ENNReal := (N k : ENNReal)
      have hB2 : B = X / Y := by rfl
      have h_prod : (↑(∏ i ∈ Finset.range (k + 1), N i) : ENNReal) = X * Z := by
        simp [X, Z, Finset.prod_range_succ, ENNReal.coe_mul] <;> norm_cast
      have h_pow : (36 : ENNReal) ^ (k + 1) = Y * 36 := by
        simp [Y, pow_succ] <;> ring
      let x : ℝ := (∏ i ∈ Finset.range k, N i : ℝ)
      let y : ℝ := (36 ^ k : ℝ)
      let z : ℝ := (N k : ℝ)
      have hX : X = ENNReal.ofReal x := by simp [X, x] <;> norm_cast
      have hY : Y = ENNReal.ofReal y := by simp [Y, y] <;> norm_cast
      have hZ : Z = ENNReal.ofReal z := by simp [Z, z] <;> norm_cast
      have h_pos_y : 0 < y := by simp [y] <;> positivity
      have h_nonneg_x : 0 ≤ x := by simp [x] <;> positivity
      have h_nonneg_z : 0 ≤ z := by simp [z] <;> positivity
      have h_eq_real : (x / y) * z / 36 = (x * z) / (y * 36) := by
        field_simp [h_pos_y.ne'] <;> ring
      have h_div : (X / Y) * Z / 36 = (X * Z) / (Y * 36) := by
        rw [hX, hY, hZ]
        have h36_pos : (0 : ℝ) < 36 := by norm_num
        have h_left : (ENNReal.ofReal x / ENNReal.ofReal y) * ENNReal.ofReal z / 36 =
            ENNReal.ofReal ((x / y) * z / 36) := by
          have h1 : (ENNReal.ofReal x / ENNReal.ofReal y) = ENNReal.ofReal (x / y) :=
            ennreal_ofReal_div h_nonneg_x h_pos_y
          rw [h1]
          have h_nonneg1 : 0 ≤ x / y := by positivity
          have h2 : ENNReal.ofReal ((x / y) * z) = ENNReal.ofReal (x / y) * ENNReal.ofReal z :=
            ENNReal.ofReal_mul h_nonneg1
          rw [←h2]
          have h3 : (36 : ENNReal) = ENNReal.ofReal (36 : ℝ) := by norm_cast
          rw [h3]
          exact ennreal_ofReal_div (by positivity) (by norm_num)
        have h_right : (ENNReal.ofReal x * ENNReal.ofReal z) / (ENNReal.ofReal y * 36) =
            ENNReal.ofReal ((x * z) / (y * 36)) := by
          have h4 : (36 : ENNReal) = ENNReal.ofReal (36 : ℝ) := by norm_cast
          have h_y4 : ENNReal.ofReal y * (36 : ENNReal) = ENNReal.ofReal (y * 36) := by
            rw [h4]
            have h : ENNReal.ofReal (y * (36 : ℝ)) = ENNReal.ofReal y * ENNReal.ofReal (36 : ℝ) :=
              ENNReal.ofReal_mul h_pos_y.le
            exact h.symm
          have h_xz : ENNReal.ofReal (x * z) = ENNReal.ofReal x * ENNReal.ofReal z :=
            ENNReal.ofReal_mul h_nonneg_x
          rw [h_y4, ←h_xz]
          exact ennreal_ofReal_div (mul_nonneg h_nonneg_x h_nonneg_z) (mul_pos h_pos_y h36_pos)
        rw [h_left, h_right, h_eq_real]
      have h_eq : B * Z / 36 = (↑(∏ i ∈ Finset.range (k + 1), N i) : ENNReal) / (36 : ENNReal) ^ (k + 1) := by
        calc B * Z / 36
          = (X / Y) * Z / 36 := by rw [hB2]
        _ = (X * Z) / (Y * 36) := h_div
        _ = (↑(∏ i ∈ Finset.range (k + 1), N i) : ENNReal) / (Y * 36) := by rw [h_prod]
        _ = (↑(∏ i ∈ Finset.range (k + 1), N i) : ENNReal) / (36 : ENNReal) ^ (k + 1) := by rw [h_pow]
      calc (Metric.externalCoveringNumber (Δ ^ (k + 1)).toNNReal P : ENNReal)
        ≥ A * (N k : ENNReal) / 36 := h_step
      _ ≥ B * (N k : ENNReal) / 36 := h_mul_le
      _ = (↑(∏ i ∈ Finset.range (k + 1), N i) : ENNReal) / (36 : ENNReal) ^ (k + 1) := h_eq
  exact h_main m h_uniform

end MultiscaleDecomposition

end DirecretisedFurstenbergEstimate

end
