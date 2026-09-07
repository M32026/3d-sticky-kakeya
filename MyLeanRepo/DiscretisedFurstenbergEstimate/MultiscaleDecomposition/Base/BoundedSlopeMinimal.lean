module

/-
  Minimal-constant bounded-slope regularity theorems.

  Uses exact dyadic cardinalities (no per-level geometric factors) to achieve
  constants independent of m:
    boundedSlopeToDeltaSSet_minimal:       81 * Δ^{-4} * Δ^{-E}
    boundedSlopeHalfScaleCovering_minimal: Δ^{-4} * Δ^{-E}
    boundedSlopeToRegular_minimal:         81 * Δ^{-4} * Δ^{-E}

  Dependencies: ExactMetricBounds, DyadicUniform, Dictionary, SubintervalRescaling
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.ExactMetricBounds
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.DyadicUniform
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.Dictionary
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.SubintervalRescaling
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

namespace DirecretisedFurstenbergEstimate.MultiscaleDecomposition

/-! # Constant check for minimal bounded-slope S-set -/

/-- `81 * Δ^(s*j - E) ≤ (81 * Δ^{-4} * Δ^{-E}) * r^s` when Δ^(j+1) ≤ r and s ≤ 4. -/
lemma boundedSlopeMinimal_constantCheck {m : ℕ} {Δ r s E : ℝ} {j : ℕ}
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hs_nonneg : 0 ≤ s) (hs_le_4 : s ≤ 4) (hE_nonneg : 0 ≤ E)
    (hm_pos : 0 < m) (hj_le_m : j ≤ m) (h_le : Δ ^ (j + 1) ≤ r) :
    (81 : ℝ) * Real.rpow Δ (s * (j : ℝ) - E) ≤
      (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) * r ^ s := by
  have h1 : Real.rpow Δ (s * (j : ℝ) - E) =
      Real.rpow Δ (-s) * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) * Real.rpow Δ (-E) := by
    have h_sum : s * (j : ℝ) - E = (-s) + (s * ((j + 1 : ℕ) : ℝ)) + (-E) := by
      simp [add_mul] <;> ring
    rw [h_sum]
    have h_a : Real.rpow Δ ((-s) + (s * ((j + 1 : ℕ) : ℝ))) =
        Real.rpow Δ (-s) * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) := Real.rpow_add hΔ _ _
    have h_b : Real.rpow Δ (((-s) + (s * ((j + 1 : ℕ) : ℝ))) + (-E)) =
        Real.rpow Δ ((-s) + (s * ((j + 1 : ℕ) : ℝ))) * Real.rpow Δ (-E) := Real.rpow_add hΔ _ _
    rw [h_b, h_a] <;> ring
  rw [h1]
  have h2 : Real.rpow Δ (-s) ≤ Real.rpow Δ (-4 : ℝ) := by
    have h5 : -s ≥ -4 := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1.le h5
  have h3 : Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) ≤ r ^ s := by
    have h_rpow_j1 : Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) = Real.rpow (Δ ^ (j + 1)) s := by
      have h_eq1 : s * ((j + 1 : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) * s := by ring
      rw [h_eq1]
      have h : Real.rpow Δ (((j + 1 : ℕ) : ℝ) * s) = (Real.rpow Δ ((j + 1 : ℕ) : ℝ)) ^ s :=
        Real.rpow_mul hΔ.le _ _
      rw [h]
      have h2 : Real.rpow Δ ((j + 1 : ℕ) : ℝ) = (Δ ^ (j + 1) : ℝ) := by
        simp [Real.rpow_natCast] <;> norm_cast
      rw [h2] <;> rfl
    rw [h_rpow_j1]
    exact Real.rpow_le_rpow (by positivity) h_le hs_nonneg
  have h_posE : 0 ≤ Real.rpow Δ (-E) := Real.rpow_nonneg hΔ.le _
  have h4 : Real.rpow Δ (-s) * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) * Real.rpow Δ (-E) ≤
      Real.rpow Δ (-4 : ℝ) * r ^ s * Real.rpow Δ (-E) := by
    have h_a : Real.rpow Δ (-s) * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) ≤
        Real.rpow Δ (-4 : ℝ) * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hΔ.le _)
    have h_a' : Real.rpow Δ (-s) * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) * Real.rpow Δ (-E) ≤
        Real.rpow Δ (-4 : ℝ) * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) * Real.rpow Δ (-E) :=
      mul_le_mul_of_nonneg_right h_a h_posE
    have h_b : Real.rpow Δ (-4 : ℝ) * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) * Real.rpow Δ (-E) ≤
        Real.rpow Δ (-4 : ℝ) * r ^ s * Real.rpow Δ (-E) := by
      have h_c : Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) * Real.rpow Δ (-E) ≤ r ^ s * Real.rpow Δ (-E) :=
        mul_le_mul_of_nonneg_right h3 h_posE
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left h_c (by positivity)
    calc Real.rpow Δ (-s) * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) * Real.rpow Δ (-E)
      ≤ Real.rpow Δ (-4 : ℝ) * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) * Real.rpow Δ (-E) := h_a'
    _ ≤ Real.rpow Δ (-4 : ℝ) * r ^ s * Real.rpow Δ (-E) := h_b
  have h5 : (81 : ℝ) * (Real.rpow Δ (-s) * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) * Real.rpow Δ (-E)) ≤
      (81 : ℝ) * (Real.rpow Δ (-4 : ℝ) * r ^ s * Real.rpow Δ (-E)) :=
    mul_le_mul_of_nonneg_left h4 (by norm_num)
  have h6 : (81 : ℝ) * (Real.rpow Δ (-4 : ℝ) * r ^ s * Real.rpow Δ (-E)) =
      (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) * r ^ s := by ring
  rw [h6] at h5
  exact h5

/-! # Theorem 4: Bounded slope → S-set with minimal constant -/

/-- Bounded slope `f(j) ≥ s0*j - E` implies IsDeltaSSet with constant
    `81 * Δ^{-4} * Δ^{-E}`. Uses exact dyadic cardinalities. -/
lemma boundedSlopeToDeltaSSet_minimal
    {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N)
    {n : ℕ} (hn_pos : 0 < n) (h1 : (1 : ℝ) = (n : ℝ) * Δ)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hΔ2 : Δ ≤ 1 / 2)
    (s0 E C : ℝ) (hs0_nonneg : 0 ≤ s0) (hs0_le_4 : s0 ≤ 4)
    (hE_nonneg : 0 ≤ E)
    (hC : (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) ≤ C)
    (hm_pos : 0 < m)
    (h_lower : ∀ (j : ℕ), j ≤ m →
      codeFunction m Δ N (j : ℝ) ≥ s0 * (j : ℝ) - E)
    (hP_sub : P ⊆ dyadicSquare 1 0 0) :
    IsDeltaSSet (Δ ^ m) s0 C P := by
  set f : ℝ → ℝ := codeFunction m Δ N with hf_def
  set δ : ℝ := Δ ^ m with hδ_def
  have hP_nonempty : P.Nonempty := h_uniform.2.2.1
  have hN_pos : ∀ i < m, N i ≥ 1 := h_uniform.2.2.2.1
  have hδ_pos : 0 < δ := by positivity
  have h_pos4 : 0 < Real.rpow Δ (-4) := Real.rpow_pos_of_pos hΔ _
  have h_posE : 0 < Real.rpow Δ (-E) := Real.rpow_pos_of_pos hΔ _
  have hC_pos : 0 < C := by
    have h1' : 0 < (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) := by positivity
    exact lt_of_lt_of_le h1' hC
  have hC_ge_one : (1 : ℝ) ≤ C := by
    have h2 : (1 : ℝ) ≤ Real.rpow Δ (-4) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hΔ (by linarith) (by norm_num)
    have h3 : (1 : ℝ) ≤ Real.rpow Δ (-E) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hΔ hΔ1.le (by linarith)
    have h4 : (1 : ℝ) ≤ (81 : ℝ) := by norm_num
    have h5 : (1 : ℝ) ≤ (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) := by
      calc (1 : ℝ)
        = (1 : ℝ) * (1 : ℝ) * (1 : ℝ) := by ring
      _ ≤ (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) := by gcongr
    linarith [hC, h5]

  have h_main_goal : ∀ (x : EuclideanPlane) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
    intro x r hδ_le_r
    by_cases h_r_ge_one : 1 ≤ r
    · -- Case r ≥ 1: trivial bound
      have h1 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
        exact_mod_cast Metric.externalCoveringNumber_mono_set (Set.inter_subset_left)
      have h2 : (1 : ENNReal) ≤ ENNReal.ofReal C := ENNReal.one_le_ofReal.mpr hC_ge_one
      have h31 : (1 : ℝ) ≤ r ^ s0 := Real.one_le_rpow h_r_ge_one hs0_nonneg
      have h_rpow_s : (ENNReal.ofReal r) ^ s0 = ENNReal.ofReal (r ^ s0) :=
        ENNReal.ofReal_rpow_of_nonneg (by linarith) hs0_nonneg
      have h3 : (1 : ENNReal) ≤ (ENNReal.ofReal r) ^ s0 := by
        rw [h_rpow_s]; exact ENNReal.one_le_ofReal.mpr h31
      have h4 : (1 : ENNReal) ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 := by
        calc (1 : ENNReal)
          = (1 : ENNReal) * (1 : ENNReal) := by simp
        _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 := by gcongr
      calc (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal)
        ≤ (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h1
      _ = (1 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by simp
      _ ≤ (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by gcongr
      _ = ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by ring

    · -- Case δ ≤ r < 1
      have h_r_lt_one : r < 1 := by linarith
      have h_r_pos : 0 < r := lt_of_lt_of_le hδ_pos hδ_le_r
      let S_j : Finset ℕ := Finset.filter (fun k => Δ ^ k > r) (Finset.range m)
      have hSj_nonempty : S_j.Nonempty := by
        have h0 : 0 ∈ S_j := by
          simp only [S_j, Finset.mem_filter, Finset.mem_range]
          constructor
          · exact hm_pos
          · simpa using h_r_lt_one
        exact ⟨0, h0⟩
      let j : ℕ := S_j.max' hSj_nonempty
      have hj_mem : j ∈ S_j := Finset.max'_mem S_j hSj_nonempty
      have hj_in_range : j ∈ Finset.range m := (Finset.mem_filter.mp hj_mem).1
      have hj_lt_m : j < m := Finset.mem_range.mp hj_in_range
      have hj_le_m : j ≤ m := by linarith
      have h_gt : Δ ^ j > r := (Finset.mem_filter.mp hj_mem).2
      have h_le : Δ ^ (j + 1) ≤ r := by
        by_cases h : j + 1 < m
        · have h4 : j + 1 ∉ S_j := by
            intro h5
            have h6 : j + 1 ≤ j := Finset.le_max' S_j (j + 1) h5
            omega
          have h5 : ¬(Δ ^ (j + 1) > r) := by
            simpa [S_j, Finset.mem_filter, h] using h4
          linarith
        · have h6 : j + 1 = m := by omega
          rw [h6]; exact hδ_le_r
      have hΔj_pos : 0 < Δ ^ j := by positivity
      rcases ball_dyadic_squares_bound (Δ ^ j) hΔj_pos x with ⟨Sq, hSq_prop, hSq_card⟩
      have h_ball_sub : Metric.closedBall x r ⊆ Metric.closedBall x (Δ ^ j) := by
        intro y hy
        have h_dist : dist y x ≤ r := by simpa [Metric.mem_closedBall] using hy
        have h : dist y x ≤ Δ ^ j := by linarith
        simpa [Metric.mem_closedBall] using h
      have h_cover : P ∩ Metric.closedBall x r ⊆
          ⋃ p ∈ Sq, P ∩ dyadicSquare (Δ ^ j) p.1 p.2 := by
        intro y hy
        have hyP : y ∈ P := hy.1
        have hyB : y ∈ Metric.closedBall x r := hy.2
        let a : ℤ := ⌊y 0 / (Δ ^ j)⌋
        let b : ℤ := ⌊y 1 / (Δ ^ j)⌋
        have ha1 : (a : ℝ) ≤ y 0 / (Δ ^ j) := Int.floor_le _
        have ha2 : y 0 / (Δ ^ j) < (a : ℝ) + 1 := Int.lt_floor_add_one _
        have hb1 : (b : ℝ) ≤ y 1 / (Δ ^ j) := Int.floor_le _
        have hb2 : y 1 / (Δ ^ j) < (b : ℝ) + 1 := Int.lt_floor_add_one _
        have hy_sq : y ∈ dyadicSquare (Δ ^ j) a b := by
          simp only [dyadicSquare]
          constructor
          · constructor
            · calc (a : ℝ) * (Δ ^ j) ≤ (y 0 / (Δ ^ j)) * (Δ ^ j) := by gcongr
                _ = y 0 := by field_simp [hΔj_pos.ne'] <;> ring
            · calc y 0 = (y 0 / (Δ ^ j)) * (Δ ^ j) := by field_simp [hΔj_pos.ne'] <;> ring
                _ < ((a : ℝ) + 1) * (Δ ^ j) := by gcongr
          · constructor
            · calc (b : ℝ) * (Δ ^ j) ≤ (y 1 / (Δ ^ j)) * (Δ ^ j) := by gcongr
                _ = y 1 := by field_simp [hΔj_pos.ne'] <;> ring
            · calc y 1 = (y 1 / (Δ ^ j)) * (Δ ^ j) := by field_simp [hΔj_pos.ne'] <;> ring
                _ < ((b : ℝ) + 1) * (Δ ^ j) := by gcongr
        have h_intersect : (Metric.closedBall x (Δ ^ j) ∩ dyadicSquare (Δ ^ j) a b).Nonempty :=
          ⟨y, h_ball_sub hyB, hy_sq⟩
        have h_in_Sq : (a, b) ∈ Sq := hSq_prop a b h_intersect
        exact Set.mem_iUnion₂.mpr ⟨(a, b), h_in_Sq, ⟨hyP, hy_sq⟩⟩

      -- Products
      let Prod_jm : ℕ := ∏ i ∈ Finset.Ico j m, N i
      let Prod_0m : ℕ := ∏ i ∈ Finset.range m, N i
      let Prod_0j : ℕ := ∏ i ∈ Finset.range j, N i

      have h_Ico_eq : Finset.Ico 0 m = Finset.range m := by
        ext x; simp [Finset.mem_Ico, Finset.mem_range] <;> omega
      have h_prod_decomp : (Prod_0m : ℝ) = (Prod_0j : ℝ) * (Prod_jm : ℝ) := by
        have h2 : Finset.range m = Finset.range j ∪ Finset.Ico j m := by
          ext x; simp [Finset.mem_range, Finset.mem_Ico] <;> omega
        have h3 : Disjoint (Finset.range j) (Finset.Ico j m) := by
          simp [Finset.disjoint_left, Finset.mem_range, Finset.mem_Ico] <;> omega
        have h4 : ∏ i ∈ Finset.range m, N i =
            (∏ i ∈ Finset.range j, N i) * ∏ i ∈ Finset.Ico j m, N i := by
          rw [h2, Finset.prod_union h3] <;> ring
        norm_cast <;> exact h4

      have h_prod_0j_coe : (Prod_0j : ℝ) = ∏ i ∈ Finset.range j, (N i : ℝ) := by
        simp [Prod_0j] <;> norm_cast
      have h_prod_0j : (Prod_0j : ℝ) = Real.rpow Δ (-(f (j : ℝ))) := by
        rw [h_prod_0j_coe]
        exact codeFunction_product_dyadic h_uniform hΔ hΔ1 hj_le_m

      have h_fj_lower : f (j : ℝ) ≥ s0 * (j : ℝ) - E := h_lower j hj_le_m
      have h_rpow_fj : Real.rpow Δ (f (j : ℝ)) ≤ Real.rpow Δ (s0 * (j : ℝ) - E) :=
        Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1.le h_fj_lower

      -- Upper bound for each square: extCover ≤ exact dyadic count
      have h_each : ∀ (p : ℤ × ℤ), p ∈ Sq →
          (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) ≤
            (↑Prod_jm : ENNReal) := by
        intro p _
        by_cases hne : (P ∩ dyadicSquare (Δ ^ j) p.1 p.2).Nonempty
        · have h_count : dyadicSquareCount (Δ ^ m) (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) = ↑Prod_jm :=
            dyadicSquareCount_multilevel h_uniform hn_pos h1 (by linarith) (by linarith) p.1 p.2 hne
          have h_enat : Metric.externalCoveringNumber (Δ ^ m).toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) ≤ ↑Prod_jm :=
            metricCovering_le_of_dyadicSquareCount_eq (pow_pos hΔ m) h_count
          exact enat_to_ennreal_mono h_enat
        · have h_empty : P ∩ dyadicSquare (Δ ^ j) p.1 p.2 = ∅ := by
            simpa [Set.not_nonempty_iff_eq_empty] using hne
          rw [h_empty]; simp [Metric.externalCoveringNumber_empty] <;> positivity

      -- Sum upper bound (same as existing code)
      let A : {p : ℤ × ℤ // p ∈ Sq} → Set EuclideanPlane :=
        fun p => P ∩ dyadicSquare (Δ ^ j) p.val.1 p.val.2
      have h_sum : (Metric.externalCoveringNumber δ.toNNReal
            (⋃ p ∈ Sq, P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) ≤
          ∑ p ∈ Sq, (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) := by
        have h_iUnion : (⋃ p ∈ Sq, P ∩ dyadicSquare (Δ ^ j) p.1 p.2) = ⋃ (i : {p // p ∈ Sq}), A i := by
          ext z; simp [A, Set.mem_iUnion] <;> aesop
        rw [h_iUnion]
        have h_enat := externalCoveringNumber_iUnion_le (ε := δ.toNNReal) (A := A)
        let coeHom : ENat →+ ENNReal :=
          { toFun := fun x => ↑x
            map_zero' := by simp
            map_add' := by intro a b; exact ENat.toENNReal_add a b }
        have h_sum_coe : (↑(∑ i : {p // p ∈ Sq}, Metric.externalCoveringNumber δ.toNNReal (A i)) : ENNReal) =
            ∑ i : {p // p ∈ Sq}, (Metric.externalCoveringNumber δ.toNNReal (A i) : ENNReal) := by
          exact map_sum coeHom (fun i => Metric.externalCoveringNumber δ.toNNReal (A i)) Finset.univ
        have h_coerced : (Metric.externalCoveringNumber δ.toNNReal (⋃ (i : {p // p ∈ Sq}), A i) : ENNReal) ≤
            (↑(∑ i : {p // p ∈ Sq}, Metric.externalCoveringNumber δ.toNNReal (A i)) : ENNReal) :=
          enat_to_ennreal_mono h_enat
        rw [h_sum_coe] at h_coerced
        have h_univ : (Finset.univ : Finset {p // p ∈ Sq}) = Finset.attach Sq := by
          ext x; simp
        have h_attach : ∑ (i : {p // p ∈ Sq}), (Metric.externalCoveringNumber δ.toNNReal (A i) : ENNReal) =
            ∑ p ∈ Sq, (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) := by
          have h1 : ∑ (i : {p // p ∈ Sq}), (Metric.externalCoveringNumber δ.toNNReal (A i) : ENNReal) =
              ∑ i ∈ Finset.attach Sq, (Metric.externalCoveringNumber δ.toNNReal (A i) : ENNReal) := by
            rw [h_univ]
          rw [h1]
          have h2 : ∑ i ∈ Finset.attach Sq, (Metric.externalCoveringNumber δ.toNNReal (A i) : ENNReal) =
              ∑ p ∈ Sq, (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) := by
            apply Finset.sum_bij' (fun (x : {p // p ∈ Sq}) _ => x.val) (fun (p : ℤ × ℤ) hp => ⟨p, hp⟩)
            <;> simp [A, Subtype.ext_iff] <;> tauto
          exact h2
        rw [h_attach] at h_coerced
        exact h_coerced

      have h_upper1 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
          ∑ p ∈ Sq, (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) := by
        have h_mono : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
            (Metric.externalCoveringNumber δ.toNNReal (⋃ p ∈ Sq, P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) := by
          exact_mod_cast Metric.externalCoveringNumber_mono_set h_cover
        calc _ ≤ _ := h_mono
             _ ≤ _ := h_sum

      have h_upper2 : ∑ p ∈ Sq, (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) ≤
          (9 : ENNReal) * (↑Prod_jm : ENNReal) := by
        calc ∑ p ∈ Sq, _
          ≤ ∑ p ∈ Sq, (↑Prod_jm : ENNReal) := Finset.sum_le_sum fun i _ => h_each i ‹_›
        _ = (Sq.card : ENNReal) * (↑Prod_jm : ENNReal) := by
          simp [Finset.sum_const] <;> ring
        _ ≤ (9 : ENNReal) * (↑Prod_jm : ENNReal) := by
          have h_card : (Sq.card : ENNReal) ≤ (9 : ENNReal) := by exact_mod_cast hSq_card
          gcongr <;> positivity

      -- Lower bound for extCover(P): ≥ Prod_0m / 9
      have hP_inter : (P ∩ dyadicSquare (Δ ^ 0) 0 0).Nonempty := by
        have h10 : (Δ ^ 0 : ℝ) = 1 := by simp
        have h_eq : P ∩ dyadicSquare (Δ ^ 0) 0 0 = P := by
          rw [h10]
          exact Set.inter_eq_left.mpr hP_sub
        rw [h_eq]
        exact hP_nonempty
      have h_Ico0 : Finset.Ico 0 m = Finset.range m := by
        ext x; simp [Finset.mem_Ico, Finset.mem_range] <;> omega
      have h_lower_raw : (Metric.externalCoveringNumber (Δ ^ m).toNNReal (P ∩ dyadicSquare (Δ ^ 0) 0 0) : ENNReal) ≥
          (↑(∏ k ∈ Finset.Ico 0 m, N k) : ENNReal) / 9 :=
        exactCovering_product_lower h_uniform hn_pos h1 (Nat.zero_le m) (by rfl) 0 0 hP_inter
      have h_eq_set : P ∩ dyadicSquare (Δ ^ 0) 0 0 = P := by
        have h10 : (Δ ^ 0 : ℝ) = 1 := by simp
        rw [h10]
        exact Set.inter_eq_left.mpr hP_sub
      have h_lower_cover : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≥
          (↑Prod_0m : ENNReal) / 9 := by
        have h9 : (Metric.externalCoveringNumber (Δ ^ m).toNNReal (P ∩ dyadicSquare (Δ ^ 0) 0 0) : ENNReal) =
            (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
          rw [h_eq_set]
          <;> rfl
        rw [h9] at h_lower_raw
        have h10 : (↑(∏ k ∈ Finset.Ico 0 m, N k) : ENNReal) = (↑Prod_0m : ENNReal) := by
          congr 1
          <;> rw [h_Ico0] <;> rfl
        rw [h10] at h_lower_raw
        exact h_lower_raw

      -- Positivity of products
      have h_pos_0j_nat : 0 < Prod_0j := by
        apply Finset.prod_pos
        intro i hi
        have h_i_lt_j : i < j := Finset.mem_range.mp hi
        have h_i_lt_m : i < m := by linarith
        exact hN_pos i h_i_lt_m
      have h_pos_0m_nat : 0 < Prod_0m := by
        apply Finset.prod_pos
        intro i hi
        have h_i_lt_m : i < m := Finset.mem_range.mp hi
        exact hN_pos i h_i_lt_m
      have h_pos_0j : (0 : ℝ) < (Prod_0j : ℝ) := by
        exact_mod_cast h_pos_0j_nat
      have h_pos_0m : (0 : ℝ) < (Prod_0m : ℝ) := by
        exact_mod_cast h_pos_0m_nat

      -- Product decomposition
      have h5 : (Prod_jm : ℝ) = (Prod_0m : ℝ) / (Prod_0j : ℝ) := by
        rw [h_prod_decomp]
        field_simp [h_pos_0j.ne'] <;> ring
      have h6 : (Prod_0j : ℝ) = Real.rpow Δ (-(f (j : ℝ))) := h_prod_0j
      have h_rpow_inv : Real.rpow Δ (-(f (j : ℝ))) * Real.rpow Δ (f (j : ℝ)) = 1 := by
        have h : Real.rpow Δ ((-(f (j : ℝ))) + (f (j : ℝ))) = Real.rpow Δ (-(f (j : ℝ))) * Real.rpow Δ (f (j : ℝ)) :=
          Real.rpow_add hΔ _ _
        have h9 : (-(f (j : ℝ))) + (f (j : ℝ)) = 0 := by ring
        have h10 : Real.rpow Δ ((-(f (j : ℝ))) + (f (j : ℝ))) = 1 := by
          rw [h9]
          <;> simp
        have h11 : Real.rpow Δ (-(f (j : ℝ))) * Real.rpow Δ (f (j : ℝ)) = 1 := by
          rw [←h]
          exact h10
        exact h11
      have h7 : (Prod_0m : ℝ) / Real.rpow Δ (-(f (j : ℝ))) =
          (Prod_0m : ℝ) * Real.rpow Δ (f (j : ℝ)) := by
        have h8 : Real.rpow Δ (-(f (j : ℝ))) ≠ 0 := (Real.rpow_pos_of_pos hΔ _).ne'
        have h9 : (Real.rpow Δ (-(f (j : ℝ))))⁻¹ = Real.rpow Δ (f (j : ℝ)) := by
          apply inv_eq_of_mul_eq_one_right
          exact h_rpow_inv
        rw [div_eq_mul_inv, h9] <;> ring

      -- Key real inequality: 81 * Prod_jm ≤ C * r^s0 * Prod_0m
      have h_key_real : (81 : ℝ) * (Prod_jm : ℝ) ≤ C * r ^ s0 * (Prod_0m : ℝ) := by
        have h_expr : (81 : ℝ) * (Prod_jm : ℝ) =
            (81 : ℝ) * (Prod_0m : ℝ) * Real.rpow Δ (f (j : ℝ)) := by
          rw [h5, h6, h7] <;> ring
        rw [h_expr]
        have h9 : Real.rpow Δ (f (j : ℝ)) ≤ Real.rpow Δ (s0 * (j : ℝ) - E) := h_rpow_fj
        have h10 : (81 : ℝ) * Real.rpow Δ (s0 * (j : ℝ) - E) ≤
            (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) * r ^ s0 :=
          boundedSlopeMinimal_constantCheck hΔ hΔ1 hs0_nonneg hs0_le_4 hE_nonneg hm_pos hj_le_m h_le
        have h11 : (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) ≤ C := hC
        have h12 : 0 ≤ r ^ s0 := by positivity
        have h13 : (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) * r ^ s0 ≤ C * r ^ s0 := by
          calc (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) * r ^ s0
            = ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E)) * r ^ s0 := by ring
          _ ≤ C * r ^ s0 := by gcongr
        have h14 : (81 : ℝ) * (Prod_0m : ℝ) * Real.rpow Δ (f (j : ℝ)) ≤
            (Prod_0m : ℝ) * (C * r ^ s0) := by
          have h_pos_coeff : 0 ≤ (81 : ℝ) * (Prod_0m : ℝ) := by positivity
          have h_step1 : (81 : ℝ) * (Prod_0m : ℝ) * Real.rpow Δ (f (j : ℝ)) ≤
              (81 : ℝ) * (Prod_0m : ℝ) * Real.rpow Δ (s0 * (j : ℝ) - E) :=
            mul_le_mul_of_nonneg_left h_rpow_fj h_pos_coeff
          have h_step2 : (81 : ℝ) * (Prod_0m : ℝ) * Real.rpow Δ (s0 * (j : ℝ) - E) =
              (Prod_0m : ℝ) * ((81 : ℝ) * Real.rpow Δ (s0 * (j : ℝ) - E)) := by ring
          have h_step3 : (Prod_0m : ℝ) * ((81 : ℝ) * Real.rpow Δ (s0 * (j : ℝ) - E)) ≤
              (Prod_0m : ℝ) * ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) * r ^ s0) :=
            mul_le_mul_of_nonneg_left h10 (by positivity)
          have h_step4 : (Prod_0m : ℝ) * ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) * r ^ s0) ≤
              (Prod_0m : ℝ) * (C * r ^ s0) :=
            mul_le_mul_of_nonneg_left h13 (by positivity)
          calc (81 : ℝ) * (Prod_0m : ℝ) * Real.rpow Δ (f (j : ℝ))
            ≤ (81 : ℝ) * (Prod_0m : ℝ) * Real.rpow Δ (s0 * (j : ℝ) - E) := h_step1
          _ = (Prod_0m : ℝ) * ((81 : ℝ) * Real.rpow Δ (s0 * (j : ℝ) - E)) := h_step2
          _ ≤ (Prod_0m : ℝ) * ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) * r ^ s0) := h_step3
          _ ≤ (Prod_0m : ℝ) * (C * r ^ s0) := h_step4
        linarith

      -- From 81 * Prod_jm ≤ C * r^s0 * Prod_0m, get 9 * Prod_jm ≤ C * r^s0 * (Prod_0m / 9)
      have h_key9_real : (9 : ℝ) * (Prod_jm : ℝ) ≤ C * r ^ s0 * ((Prod_0m : ℝ) / 9) := by
        have h : (81 : ℝ) * (Prod_jm : ℝ) ≤ C * r ^ s0 * (Prod_0m : ℝ) := h_key_real
        have h_div : ((81 : ℝ) * (Prod_jm : ℝ)) / 9 ≤ (C * r ^ s0 * (Prod_0m : ℝ)) / 9 :=
          div_le_div_of_nonneg_right h (by norm_num)
        have h_eq2 : (C * r ^ s0 * (Prod_0m : ℝ)) / 9 = C * r ^ s0 * ((Prod_0m : ℝ) / 9) := by ring
        have h_goal : ((81 : ℝ) * (Prod_jm : ℝ)) / 9 ≤ C * r ^ s0 * ((Prod_0m : ℝ) / 9) := by
          rw [h_eq2] at h_div
          exact h_div
        have h_eq1 : (9 : ℝ) * (Prod_jm : ℝ) = ((81 : ℝ) * (Prod_jm : ℝ)) / 9 := by ring
        rw [h_eq1]
        exact h_goal

      -- Lift to ENNReal: 9 * Prod_jm ≤ C * r^s0 * extCover(P)
      have h_rpow_s : (ENNReal.ofReal r) ^ s0 = ENNReal.ofReal (r ^ s0) :=
        ENNReal.ofReal_rpow_of_nonneg (by linarith) hs0_nonneg
      have h_lower9 : (↑Prod_0m : ENNReal) / 9 ≤ (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) :=
        h_lower_cover
      have h_final : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
          ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 *
            (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
        calc (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal)
          ≤ (9 : ENNReal) * (↑Prod_jm : ENNReal) := le_trans h_upper1 h_upper2
        _ ≤ ENNReal.ofReal (C * r ^ s0) * ((↑Prod_0m : ENNReal) / 9) := by
          have h1 : (9 : ENNReal) * (↑Prod_jm : ENNReal) = ENNReal.ofReal ((9 : ℝ) * (Prod_jm : ℝ)) := by
            simp [ENNReal.ofReal_mul] <;> norm_cast
          rw [h1]
          have h_pos9 : (0 : ℝ) < 9 := by norm_num
          have h_div : ((↑Prod_0m : ENNReal) / 9) = ENNReal.ofReal ((Prod_0m : ℝ) / 9) := by
            rw [ENNReal.ofReal_div_of_pos h_pos9]
            <;> norm_cast
          rw [h_div]
          have h_mul : ENNReal.ofReal (C * r ^ s0) * ENNReal.ofReal ((Prod_0m : ℝ) / 9) =
              ENNReal.ofReal (C * r ^ s0 * ((Prod_0m : ℝ) / 9)) := by
            rw [← ENNReal.ofReal_mul (show 0 ≤ C * r ^ s0 by positivity)]
            <;> ring
          rw [h_mul]
          exact ENNReal.ofReal_le_ofReal h_key9_real
        _ ≤ ENNReal.ofReal (C * r ^ s0) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
          gcongr
          <;> exact h_lower9
        _ = ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
          rw [h_rpow_s]
          have h_eq : ENNReal.ofReal C * ENNReal.ofReal (r ^ s0) = ENNReal.ofReal (C * r ^ s0) := by
            rw [← ENNReal.ofReal_mul (show 0 ≤ C by linarith)]
            <;> ring
          rw [h_eq] <;> ring
      exact h_final

  exact ⟨hP_nonempty, hδ_pos, hC_pos, hs0_nonneg, h_main_goal⟩

/-! # Constant check for minimal half-scale covering -/

/-- `Δ^(-(s*k + E)) ≤ Δ^{-4} * Δ^{-E} * (Δ^m)^(-s/2)` when `2*k ≤ m+1` and `s ≤ 4`. -/
lemma boundedSlopeMinimal_halfScaleConstantCheck {m : ℕ} {Δ : ℝ} {s E : ℝ} {k : ℕ}
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hs_nonneg : 0 ≤ s) (hs_le_4 : s ≤ 4) (hE_nonneg : 0 ≤ E)
    (hm_pos : 0 < m) (hk_le : k ≤ m) (h2k_le : 2 * k ≤ m + 1) :
    Real.rpow Δ (-(s * (k : ℝ) + E)) ≤
      Real.rpow Δ (-4) * Real.rpow Δ (-E) * Real.rpow (Δ ^ m) (-s / 2) := by
  have h_k_le2 : (k : ℝ) ≤ (m : ℝ) / 2 + 1 := by
    have h : (2 : ℝ) * (k : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast h2k_le
    linarith
  have h_sk_le : s * (k : ℝ) ≤ s * ((m : ℝ) / 2 + 1) :=
    mul_le_mul_of_nonneg_left h_k_le2 hs_nonneg
  have h_exp1 : -s * (k : ℝ) ≥ -s * ((m : ℝ) / 2 + 1) := by linarith
  have h_exp2 : -s * ((m : ℝ) / 2 + 1) = (-s) + (-s * (m : ℝ) / 2) := by ring
  have h_rpow1 : Real.rpow Δ (-s * (k : ℝ)) ≤ Real.rpow Δ (-s * ((m : ℝ) / 2 + 1)) :=
    Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1.le h_exp1
  have h_rpow2 : Real.rpow Δ (-s * ((m : ℝ) / 2 + 1)) =
      Real.rpow Δ (-s) * Real.rpow Δ (-s * (m : ℝ) / 2) := by
    calc
      Real.rpow Δ (-s * ((m : ℝ) / 2 + 1))
        = Real.rpow Δ ((-s) + (-s * (m : ℝ) / 2)) := by rw [h_exp2]
    _ = Real.rpow Δ (-s) * Real.rpow Δ (-s * (m : ℝ) / 2) := Real.rpow_add hΔ _ _
  have h_rpow3 : Real.rpow Δ (-s) ≤ Real.rpow Δ (-4 : ℝ) := by
    have h : -s ≥ -4 := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1.le h
  have h_rpow4 : Real.rpow Δ (-s * (m : ℝ) / 2) = Real.rpow (Δ ^ m) (-s / 2) := by
    have h_eq1 : -s * (m : ℝ) / 2 = (m : ℝ) * (-s / 2) := by ring
    rw [h_eq1]
    have h : Real.rpow Δ ((m : ℝ) * (-s / 2)) = (Real.rpow Δ (m : ℝ)) ^ (-s / 2) :=
      Real.rpow_mul hΔ.le _ _
    rw [h]
    have h_nat : Real.rpow Δ (m : ℝ) = (Δ ^ m : ℝ) := by simp
    rw [h_nat] <;> rfl
  have h_posE : 0 ≤ Real.rpow Δ (-E) := Real.rpow_nonneg hΔ.le _
  have h_first : Real.rpow Δ (-(s * (k : ℝ) + E)) =
      Real.rpow Δ (-s * (k : ℝ)) * Real.rpow Δ (-E) := by
    have h_sum3 : -(s * (k : ℝ) + E) = (-s * (k : ℝ)) + (-E) := by ring
    have h_eq1 : Real.rpow Δ (-(s * (k : ℝ) + E)) = Real.rpow Δ ((-s * (k : ℝ)) + (-E)) := by
      rw [h_sum3]
    rw [h_eq1]
    exact Real.rpow_add hΔ _ _
  have h_step1 : Real.rpow Δ (-s * (k : ℝ)) * Real.rpow Δ (-E) ≤
      Real.rpow Δ (-s * ((m : ℝ) / 2 + 1)) * Real.rpow Δ (-E) :=
    mul_le_mul_of_nonneg_right h_rpow1 h_posE
  have h_step2 : Real.rpow Δ (-s * ((m : ℝ) / 2 + 1)) * Real.rpow Δ (-E) =
      (Real.rpow Δ (-s) * Real.rpow Δ (-s * (m : ℝ) / 2)) * Real.rpow Δ (-E) := by
    rw [h_rpow2] <;> ring
  have h_pos_smid : 0 ≤ Real.rpow Δ (-s * (m : ℝ) / 2) := Real.rpow_nonneg hΔ.le _
  have h_step3 : (Real.rpow Δ (-s) * Real.rpow Δ (-s * (m : ℝ) / 2)) * Real.rpow Δ (-E) ≤
      (Real.rpow Δ (-4 : ℝ) * Real.rpow Δ (-s * (m : ℝ) / 2)) * Real.rpow Δ (-E) := by
    have h_mul : Real.rpow Δ (-s) * Real.rpow Δ (-s * (m : ℝ) / 2) ≤
        Real.rpow Δ (-4 : ℝ) * Real.rpow Δ (-s * (m : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right h_rpow3 h_pos_smid
    exact mul_le_mul_of_nonneg_right h_mul h_posE
  have h_step4 : (Real.rpow Δ (-4 : ℝ) * Real.rpow Δ (-s * (m : ℝ) / 2)) * Real.rpow Δ (-E) =
      Real.rpow Δ (-4) * Real.rpow Δ (-E) * Real.rpow (Δ ^ m) (-s / 2) := by
    rw [h_rpow4] <;> ring
  have h_final : Real.rpow Δ (-s * (k : ℝ)) * Real.rpow Δ (-E) ≤
      Real.rpow Δ (-4) * Real.rpow Δ (-E) * Real.rpow (Δ ^ m) (-s / 2) := by
    calc Real.rpow Δ (-s * (k : ℝ)) * Real.rpow Δ (-E)
      ≤ Real.rpow Δ (-s * ((m : ℝ) / 2 + 1)) * Real.rpow Δ (-E) := h_step1
    _ = (Real.rpow Δ (-s) * Real.rpow Δ (-s * (m : ℝ) / 2)) * Real.rpow Δ (-E) := h_step2
    _ ≤ (Real.rpow Δ (-4 : ℝ) * Real.rpow Δ (-s * (m : ℝ) / 2)) * Real.rpow Δ (-E) := h_step3
    _ = Real.rpow Δ (-4) * Real.rpow Δ (-E) * Real.rpow (Δ ^ m) (-s / 2) := h_step4
  exact h_first.trans_le h_final

/-! # Theorem 5: Half-scale covering with minimal constant -/

/-- Half-scale covering bound from bounded slope with NO per-level geometric
    factors. Constant: `Δ^{-4} * Δ^{-E}`. Uses exact dyadic cardinalities. -/
lemma boundedSlopeHalfScaleCovering_minimal
    {P' : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform' : IsDyadicUniform P' m Δ N)
    {n : ℕ} (hn_pos : 0 < n) (h1 : (1 : ℝ) = (n : ℝ) * Δ)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (s0 E C : ℝ) (hs0_nonneg : 0 ≤ s0) (hs0_le_4 : s0 ≤ 4)
    (hE_nonneg : 0 ≤ E)
    (hC : Real.rpow Δ (-4) * Real.rpow Δ (-E) ≤ C)
    (hm_pos : 0 < m)
    (h_bounds : ∀ (j : ℕ), j ≤ m →
        |codeFunction m Δ N (j : ℝ) - s0 * (j : ℝ)| ≤ E)
    (hP'_sub : P' ⊆ dyadicSquare 1 0 0) :
    (Metric.externalCoveringNumber (Real.sqrt (Δ ^ m)).toNNReal P' : ENNReal) ≤
      ENNReal.ofReal (C * Real.rpow (Δ ^ m) (-s0 / 2)) := by
  set f : ℝ → ℝ := codeFunction m Δ N with hf_def
  set δ : ℝ := Δ ^ m with hδ_def
  let k : ℕ := Nat.ceil ((m : ℝ) / 2)
  have hk_ge : (k : ℝ) ≥ (m : ℝ) / 2 := Nat.le_ceil _
  have hk_le : k ≤ m := by
    apply Nat.ceil_le.mpr
    have h : (m : ℝ) / 2 ≤ (m : ℝ) := by linarith [hm_pos]
    exact h
  have hk_pos : 0 < k := by
    have h_pos : 0 < (m : ℝ) / 2 := by positivity
    exact Nat.ceil_pos.mpr h_pos
  have h2k_le : 2 * k ≤ m + 1 := by
    have h_nonneg : 0 ≤ (m : ℝ) / 2 := by positivity
    have h : (k : ℝ) < (m : ℝ) / 2 + 1 := Nat.ceil_lt_add_one h_nonneg
    have h' : (2 : ℝ) * (k : ℝ) < (m : ℝ) + 2 := by linarith
    have h_int : 2 * k < m + 2 := by exact_mod_cast h'
    omega
  have h_delta_k_le_sqrt : (Δ ^ k : ℝ) ≤ Real.sqrt δ := by
    have h2 : (Δ ^ k : ℝ) ≤ Real.rpow Δ ((m : ℝ) / 2) := by
      have h_eq : (Δ ^ k : ℝ) = Real.rpow Δ (k : ℝ) := by simp
      rw [h_eq]
      exact Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1.le hk_ge
    have h_pos1 : 0 ≤ Real.rpow Δ ((m : ℝ) / 2) := Real.rpow_nonneg hΔ.le _
    have h_sq1 : (Real.rpow Δ ((m : ℝ) / 2)) ^ 2 = Δ ^ m := by
      have h_mul : (Real.rpow Δ ((m : ℝ) / 2)) ^ 2 =
          Real.rpow Δ ((m : ℝ) / 2) * Real.rpow Δ ((m : ℝ) / 2) := by ring
      rw [h_mul]
      have h_add : Real.rpow Δ ((m : ℝ) / 2) * Real.rpow Δ ((m : ℝ) / 2) =
          Real.rpow Δ (((m : ℝ) / 2) + ((m : ℝ) / 2)) :=
        (Real.rpow_add hΔ ((m : ℝ) / 2) ((m : ℝ) / 2)).symm
      rw [h_add]
      have h4 : (m : ℝ) / 2 + (m : ℝ) / 2 = (m : ℝ) := by ring
      rw [h4] <;> simp
    have h_sq2 : (Real.sqrt (Δ ^ m)) ^ 2 = Δ ^ m := by rw [Real.sq_sqrt] <;> positivity
    have h_pos2 : 0 ≤ Real.sqrt (Δ ^ m) := Real.sqrt_nonneg _
    have h_eq_sq : (Real.rpow Δ ((m : ℝ) / 2)) ^ 2 = (Real.sqrt (Δ ^ m)) ^ 2 := by
      rw [h_sq1, h_sq2]
    have h3 : Real.rpow Δ ((m : ℝ) / 2) = Real.sqrt (Δ ^ m) := by
      nlinarith [h_pos1, h_pos2, h_eq_sq]
    calc (Δ ^ k : ℝ)
      ≤ Real.rpow Δ ((m : ℝ) / 2) := h2
    _ = Real.sqrt (Δ ^ m) := h3
    _ = Real.sqrt δ := by rw [hδ_def]
  have h_toNNReal_le : (Δ ^ k).toNNReal ≤ (Real.sqrt δ).toNNReal := by
    apply Real.toNNReal_le_toNNReal <;> linarith [h_delta_k_le_sqrt]
  have h_anti : (Metric.externalCoveringNumber (Real.sqrt δ).toNNReal P' : ENNReal) ≤
      (Metric.externalCoveringNumber (Δ ^ k).toNNReal P' : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_anti h_toNNReal_le

  -- Exact dyadic count: dyadicSquareCount(Δ^k, P') = ∏_{i=0}^{k-1} N(i)
  have hP'_nonempty : P'.Nonempty := h_uniform'.2.2.1
  have h10 : (Δ ^ 0 : ℝ) = 1 := by simp
  have h_eq_set : P' ∩ dyadicSquare (Δ ^ 0) 0 0 = P' := by
    rw [h10]
    exact Set.inter_eq_left.mpr hP'_sub
  have hP'_inter : (P' ∩ dyadicSquare (Δ ^ 0) 0 0).Nonempty := by
    rw [h_eq_set]; exact hP'_nonempty
  let Prod_0k : ℕ := ∏ i ∈ Finset.range k, N i
  have h_Ico_eq : Finset.Ico 0 k = Finset.range k := by
    ext x; simp [Finset.mem_Ico, Finset.mem_range] <;> omega
  have h_count : dyadicSquareCount (Δ ^ k) P' = ↑Prod_0k := by
    have h_raw : dyadicSquareCount (Δ ^ k) (P' ∩ dyadicSquare (Δ ^ 0) 0 0) =
        ↑(∏ i ∈ Finset.Ico 0 k, N i) :=
      dyadicSquareCount_multilevel h_uniform' hn_pos h1 (Nat.zero_le k) hk_le 0 0 hP'_inter
    rw [h_eq_set] at h_raw
    have h9 : (↑(∏ i ∈ Finset.Ico 0 k, N i) : ENat) = (↑Prod_0k : ENat) := by
      congr 1 <;> rw [h_Ico_eq] <;> rfl
    rw [h9] at h_raw
    exact h_raw
  have h_enat : Metric.externalCoveringNumber (Δ ^ k).toNNReal P' ≤ ↑Prod_0k :=
    metricCovering_le_of_dyadicSquareCount_eq (pow_pos hΔ k) h_count
  have h_upper : (Metric.externalCoveringNumber (Δ ^ k).toNNReal P' : ENNReal) ≤
      (↑Prod_0k : ENNReal) := enat_to_ennreal_mono h_enat

  -- Product = Δ^{-f(k)}
  have h_prod_coe : (Prod_0k : ℝ) = ∏ i ∈ Finset.range k, (N i : ℝ) := by
    simp [Prod_0k] <;> norm_cast
  have h_prod : (Prod_0k : ℝ) = Real.rpow Δ (-(f (k : ℝ))) := by
    rw [h_prod_coe]
    exact codeFunction_product_dyadic h_uniform' hΔ hΔ1 hk_le

  -- f(k) ≤ s0*k + E from upper bound
  have h_f_k_upper : f (k : ℝ) ≤ s0 * (k : ℝ) + E := by
    have h := h_bounds k hk_le
    have h' : f (k : ℝ) - s0 * (k : ℝ) ≤ E := by
      linarith [abs_le.mp h]
    linarith
  have h_prod_upper : (Prod_0k : ℝ) ≤ Real.rpow Δ (-(s0 * (k : ℝ) + E)) := by
    rw [h_prod]
    have h_exp : -(f (k : ℝ)) ≥ -(s0 * (k : ℝ) + E) := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1.le h_exp

  -- Constant check
  have h_const : Real.rpow Δ (-(s0 * (k : ℝ) + E)) ≤
      Real.rpow Δ (-4) * Real.rpow Δ (-E) * Real.rpow (Δ ^ m) (-s0 / 2) :=
    boundedSlopeMinimal_halfScaleConstantCheck hΔ hΔ1 hs0_nonneg hs0_le_4 hE_nonneg
      hm_pos hk_le h2k_le
  have h_rpow_nonneg : 0 ≤ Real.rpow (Δ ^ m) (-s0 / 2) := Real.rpow_nonneg (by positivity) _
  have hC' : Real.rpow Δ (-4) * Real.rpow Δ (-E) * Real.rpow (Δ ^ m) (-s0 / 2) ≤
      C * Real.rpow (Δ ^ m) (-s0 / 2) := by
    have h : Real.rpow Δ (-4) * Real.rpow Δ (-E) ≤ C := hC
    calc Real.rpow Δ (-4) * Real.rpow Δ (-E) * Real.rpow (Δ ^ m) (-s0 / 2)
      = (Real.rpow Δ (-4) * Real.rpow Δ (-E)) * Real.rpow (Δ ^ m) (-s0 / 2) := by ring
    _ ≤ C * Real.rpow (Δ ^ m) (-s0 / 2) := by gcongr

  -- Lift to ENNReal
  have h_final : (Metric.externalCoveringNumber (Δ ^ k).toNNReal P' : ENNReal) ≤
      ENNReal.ofReal (C * Real.rpow (Δ ^ m) (-s0 / 2)) := by
    have h1 : (↑Prod_0k : ENNReal) = ENNReal.ofReal ((Prod_0k : ℝ)) := by
      simp <;> norm_cast
    rw [h1] at h_upper
    calc (Metric.externalCoveringNumber (Δ ^ k).toNNReal P' : ENNReal)
      ≤ ENNReal.ofReal ((Prod_0k : ℝ)) := h_upper
    _ ≤ ENNReal.ofReal (Real.rpow Δ (-(s0 * (k : ℝ) + E))) :=
        ENNReal.ofReal_le_ofReal h_prod_upper
    _ ≤ ENNReal.ofReal (Real.rpow Δ (-4) * Real.rpow Δ (-E) * Real.rpow (Δ ^ m) (-s0 / 2)) :=
        ENNReal.ofReal_le_ofReal h_const
    _ ≤ ENNReal.ofReal (C * Real.rpow (Δ ^ m) (-s0 / 2)) :=
        ENNReal.ofReal_le_ofReal hC'
  exact le_trans h_anti h_final

/-! # Theorem 6: Full regularity from bounded slope with minimal constant -/

/-- Full regularity from bounded slope with minimal constant.
    Constant C must satisfy `81 * Δ^{-4} * Δ^{-E} ≤ C`. -/
lemma boundedSlopeToRegular_minimal
    {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N)
    {n : ℕ} (hn_pos : 0 < n) (h1 : (1 : ℝ) = (n : ℝ) * Δ)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hΔ2 : Δ ≤ 1 / 2)
    (s0 E C : ℝ) (hs0_nonneg : 0 ≤ s0) (hs0_le_4 : s0 ≤ 4)
    (hE_nonneg : 0 ≤ E)
    (hC : (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) ≤ C)
    (hm_pos : 0 < m)
    (h_bounds : ∀ (j : ℕ), j ≤ m →
        |codeFunction m Δ N (j : ℝ) - s0 * (j : ℝ)| ≤ E) :
    IsRegularBetweenScales P (Δ ^ m) 1 s0 C C := by
  set δ : ℝ := Δ ^ m with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have hδ_le_one : δ ≤ 1 := by
    rw [hδ_def]
    have h1' : 0 ≤ Δ := by linarith
    have h2' : Δ ≤ 1 := by linarith
    exact pow_le_one₀ h1' h2'
  have h_pos4 : 0 < Real.rpow Δ (-4) := Real.rpow_pos_of_pos hΔ _
  have h_posE : 0 < Real.rpow Δ (-E) := Real.rpow_pos_of_pos hΔ _
  have hC_pos : 0 < C := by
    have h1' : 0 < (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) := by positivity
    exact lt_of_lt_of_le h1' hC
  have hC_half : Real.rpow Δ (-4) * Real.rpow Δ (-E) ≤ C := by
    have h : Real.rpow Δ (-4) * Real.rpow Δ (-E) ≤
        (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) := by
      have h2 : (1 : ℝ) ≤ (81 : ℝ) := by norm_num
      calc Real.rpow Δ (-4) * Real.rpow Δ (-E)
        = (1 : ℝ) * (Real.rpow Δ (-4) * Real.rpow Δ (-E)) := by ring
      _ ≤ (81 : ℝ) * (Real.rpow Δ (-4) * Real.rpow Δ (-E)) := by gcongr
      _ = (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow Δ (-E) := by ring
    linarith [hC, h]
  have h_lower : ∀ (j : ℕ), j ≤ m →
      codeFunction m Δ N (j : ℝ) ≥ s0 * (j : ℝ) - E := by
    intro j hj
    have h := h_bounds j hj
    have h' : -(E) ≤ codeFunction m Δ N (j : ℝ) - s0 * (j : ℝ) := by
      linarith [abs_le.mp h]
    linarith

  have h_set : IsSetBetweenScales P δ 1 s0 C := by
    refine' ⟨hδ_pos, by norm_num, hδ_le_one, hs0_nonneg, hC_pos, _⟩
    intro i j hQ
    let P' := homothetyS 1 i j '' (P ∩ dyadicSquare 1 i j)
    have h_uniform' : IsDyadicUniform P' m Δ N := by
      simpa [pow_zero] using uniform_rescaled_square_dyadic h_uniform hm_pos (by linarith) hn_pos h1 i j hQ
    have hP'_sub : P' ⊆ dyadicSquare 1 0 0 := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have hxQ : x ∈ dyadicSquare 1 i j := hx.2
      simp only [dyadicSquare, Set.mem_setOf_eq] at hxQ ⊢
      have h10 : (homothetyS 1 i j x) 0 = x 0 - (i : ℝ) := by simp [homothetyS] <;> rfl
      have h11 : (homothetyS 1 i j x) 1 = x 1 - (j : ℝ) := by simp [homothetyS] <;> rfl
      rw [h10, h11]
      have h_goal : (x 0 - (i : ℝ)) ∈ Set.Ico (0 : ℝ) 1 ∧ (x 1 - (j : ℝ)) ∈ Set.Ico (0 : ℝ) 1 := by
        constructor
        · exact ⟨by linarith [hxQ.1.1, hxQ.1.2], by linarith [hxQ.1.1, hxQ.1.2]⟩
        · exact ⟨by linarith [hxQ.2.1, hxQ.2.2], by linarith [hxQ.2.1, hxQ.2.2]⟩
      simpa [Set.mem_Ico, mul_one] using h_goal
    have h_result : IsDeltaSSet (Δ ^ m) s0 C P' :=
      boundedSlopeToDeltaSSet_minimal h_uniform' hn_pos h1 hΔ hΔ1 hΔ2 s0 E C
        hs0_nonneg hs0_le_4 hE_nonneg hC hm_pos h_lower hP'_sub
    simpa [hδ_def] using h_result

  have h_reg : ∀ (i j : ℤ), (P ∩ dyadicSquare 1 i j).Nonempty →
      (Metric.externalCoveringNumber (Real.sqrt δ).toNNReal
         (homothetyS 1 i j '' (P ∩ dyadicSquare 1 i j)) : ENNReal) ≤
        ENNReal.ofReal (C * Real.rpow δ (-s0 / 2)) := by
    intro i j hQ
    let P' := homothetyS 1 i j '' (P ∩ dyadicSquare 1 i j)
    have h_uniform' : IsDyadicUniform P' m Δ N := by
      simpa [pow_zero] using uniform_rescaled_square_dyadic h_uniform hm_pos (by linarith) hn_pos h1 i j hQ
    have hP'_sub : P' ⊆ dyadicSquare 1 0 0 := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have hxQ : x ∈ dyadicSquare 1 i j := hx.2
      simp only [dyadicSquare, Set.mem_setOf_eq] at hxQ ⊢
      have h10 : (homothetyS 1 i j x) 0 = x 0 - (i : ℝ) := by simp [homothetyS] <;> rfl
      have h11 : (homothetyS 1 i j x) 1 = x 1 - (j : ℝ) := by simp [homothetyS] <;> rfl
      rw [h10, h11]
      have h_goal : (x 0 - (i : ℝ)) ∈ Set.Ico (0 : ℝ) 1 ∧ (x 1 - (j : ℝ)) ∈ Set.Ico (0 : ℝ) 1 := by
        constructor
        · exact ⟨by linarith [hxQ.1.1, hxQ.1.2], by linarith [hxQ.1.1, hxQ.1.2]⟩
        · exact ⟨by linarith [hxQ.2.1, hxQ.2.2], by linarith [hxQ.2.1, hxQ.2.2]⟩
      simpa [Set.mem_Ico, mul_one] using h_goal
    exact boundedSlopeHalfScaleCovering_minimal h_uniform' hn_pos h1 hΔ hΔ1 s0 E C
      hs0_nonneg hs0_le_4 hE_nonneg hC_half hm_pos h_bounds hP'_sub

  exact ⟨h_set, hC_pos, by simpa [div_one] using h_reg⟩

end DirecretisedFurstenbergEstimate.MultiscaleDecomposition

end
