module

/-
  Tail Uniformisation Consumer (OS Lemma 5)

  Composes basic_uniformization_dyadic → per_level_density →
  single_level_density → uniformisation_Sset_transfer to produce a
  uniform subset P'' ⊆ P' with transferred between-scales S-set
  properties, given that P' has global density ≥ 1/K relative to a
  uniform full set P.

  Whiteprint node: combining_theorem_rework / tail_uniformisation_consumer
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.BasicUniformization
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformisationLemma
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformisationLemma_Bridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.GoodTransfer
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal BigOperators Classical


noncomputable section

namespace DiscretisedFurstenbergEstimate.OSUniformisation

open BasicUniformization

/-- If setFromIndices δ S₁ ⊆ setFromIndices δ S₂ then S₁ ⊆ S₂,
    since dyadic squares at the same scale are equal or disjoint. -/
lemma setFromIndices_subset_iff {δ : ℝ} (hδ_pos : 0 < δ)
    {S₁ S₂ : Finset (ℤ × ℤ)} :
    setFromIndices δ S₁ ⊆ setFromIndices δ S₂ ↔ S₁ ⊆ S₂ := by
  constructor
  · intro h
    intro idx hidx
    let x : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp (2 : ENNReal) fun k : Fin 2 =>
        if k = 0 then (idx.1 : ℝ) * δ else (idx.2 : ℝ) * δ
    have hx0 : x 0 = (idx.1 : ℝ) * δ := by
      simp [x, PiLp.toLp_apply] <;> norm_num
    have hx1 : x 1 = (idx.2 : ℝ) * δ := by
      simp [x, PiLp.toLp_apply] <;> norm_num
    have hx : x ∈ dyadicSquare δ idx.1 idx.2 := by
      simp only [dyadicSquare, Set.mem_setOf_eq]
      constructor
      · simp [Set.mem_Ico, hx0] <;> linarith
      · simp [Set.mem_Ico, hx1] <;> linarith
    have h2 : x ∈ setFromIndices δ S₁ := Set.mem_iUnion₂.mpr ⟨idx, hidx, hx⟩
    have h3 : x ∈ setFromIndices δ S₂ := h h2
    rcases Set.mem_iUnion₂.mp h3 with ⟨idx', hidx', hx'⟩
    have h4 : x ∈ dyadicSquare δ idx'.1 idx'.2 := hx'
    simp only [dyadicSquare, Set.mem_setOf_eq] at h4
    have h_i1 : (idx.1 : ℝ) * δ ≤ x 0 := by linarith [hx0]
    have h_i2 : x 0 < (idx'.1 + 1 : ℝ) * δ := h4.1.2
    have h_j1 : (idx'.1 : ℝ) * δ ≤ x 0 := h4.1.1
    have h_j2 : x 0 < (idx.1 + 1 : ℝ) * δ := by linarith [hx0]
    have h61 : (idx.1 : ℝ) < (idx'.1 : ℝ) + 1 := by nlinarith
    have h6 : idx.1 ≤ idx'.1 := by
      have h : idx.1 < idx'.1 + 1 := by exact_mod_cast h61
      omega
    have h71 : (idx'.1 : ℝ) < (idx.1 : ℝ) + 1 := by nlinarith
    have h7 : idx'.1 ≤ idx.1 := by
      have h : idx'.1 < idx.1 + 1 := by exact_mod_cast h71
      omega
    have h8 : idx.1 = idx'.1 := by omega
    have h91 : (idx.2 : ℝ) < (idx'.2 : ℝ) + 1 := by nlinarith [h4.2.1, h4.2.2, hx1]
    have h9 : idx.2 ≤ idx'.2 := by
      have h : idx.2 < idx'.2 + 1 := by exact_mod_cast h91
      omega
    have h101 : (idx'.2 : ℝ) < (idx.2 : ℝ) + 1 := by nlinarith [h4.2.1, h4.2.2, hx1]
    have h10 : idx'.2 ≤ idx.2 := by
      have h : idx'.2 < idx.2 + 1 := by exact_mod_cast h101
      omega
    have h11 : idx.2 = idx'.2 := by omega
    have h12 : idx = idx' := by
      ext <;> tauto
    exact h12 ▸ hidx'
  · exact setFromIndices_subset

/-- Injectivity of dyadicDelta. -/
lemma dyadicDelta_injective : Function.Injective dyadicDelta := by
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

/-- OS Lemma 5 consumer: given a uniform full set S and a retained subset S'
    with global density ≥ 1/K, uniformize S' and transfer between-scales
    S-set properties from S to the uniformized subset S''.

    The constant amplification is polylogarithmic in δ:
    M = K · (24 · log(1/δ) / n)^n, and the final S-set constant is
    9 · C · 2 · M · 4^n. -/
lemma tail_uniformisation_sset_consumer
    {n : ℕ} (hn : 0 < n)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (nδ : ℕ) (hδ_eq : δ = dyadicDelta nδ)
    (Δ : Fin (n + 1) → ℝ)
    (hΔ_dyadic : ∀ i, Δ i ∈ dyadicScales)
    (hΔ_pos : ∀ i, 0 < Δ i)
    (hΔ_strict : ∀ j : Fin n, Δ (Fin.succ j) < Δ j.castSucc)
    (hΔ_end : Δ (Fin.last n) = δ)
    (hΔ_start : Δ 0 = 1)
    (a : Fin (n + 1) → ℕ)
    (ha_spec : ∀ i, Δ i = dyadicDelta (a i))
    (S S' : Finset (ℤ × ℤ))
    (N : Fin n → ℕ)
    (h_unif_S : RangeUniformityProp n a S N)
    (hS'_sub : S' ⊆ S)
    (K : ℝ) (hK_pos : 0 < K)
    (h_density : (S'.card : ℝ) ≥ (S.card : ℝ) / K)
    (s : ℝ) (hs_nonneg : 0 ≤ s)
    (C : ℝ) (hC_pos : 0 < C)
    (h_between : ∀ (j : Fin n),
      IsSetBetweenScales (setFromIndices δ S) (Δ (Fin.succ j)) (Δ j.castSucc) s C)
    (h_unit_S : ∀ idx ∈ S, 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
      idx.1 < (2 : ℤ)^(a (Fin.last n)) ∧ idx.2 < (2 : ℤ)^(a (Fin.last n))) :
    ∃ (S'' : Finset (ℤ × ℤ)) (N'' : Fin n → ℕ),
      S'' ⊆ S' ∧
      RangeUniformityProp n a S'' N'' ∧
      (∀ (j : Fin n),
        IsSetBetweenScales (setFromIndices δ S'') (Δ (Fin.succ j)) (Δ j.castSucc) s
          (9 * C * 2 * (K * (24 * Real.log (1 / δ) / (n : ℝ)) ^ n) * (4 : ℝ)^n)) := by
  have hlog_pos : 0 < Real.log (1 / δ) := Real.log_pos (by
    have h : 1 < 1 / δ := by
      apply one_lt_one_div
      <;> linarith
    exact h)
  let L_unif : ℝ := (24 * Real.log (1 / δ) / (n : ℝ)) ^ n
  have hL_pos : 0 < L_unif := by
    have h1 : 0 < 24 * Real.log (1 / δ) / (n : ℝ) := by
      apply div_pos
      · positivity
      · exact_mod_cast hn
    positivity
  let M : ℝ := K * L_unif
  have hM_pos : 0 < M := mul_pos hK_pos hL_pos
  let P' : Set EuclideanPlane := setFromIndices δ S'
  have hP'_bounded : Bornology.IsBounded P' := by
    have h_eq : P' = setFromIndices (dyadicDelta nδ) S' := by
      dsimp only [P']
      rw [hδ_eq]
    rw [h_eq]
    exact setFromIndices_isBounded nδ S'
  have hS_nonempty : S.Nonempty := h_unif_S.1
  have hS'_nonempty : S'.Nonempty := by
    by_contra h2
    have h3 : S' = ∅ := by simpa using h2
    rw [h3] at h_density
    have h4 : (S.card : ℝ) = 0 := by
      have h5 : (0 : ℝ) ≥ (S.card : ℝ) / K := by simpa using h_density
      have h6 : 0 ≤ (S.card : ℝ) := by positivity
      have h7 : (S.card : ℝ) / K ≤ 0 := by linarith
      have h8 : (S.card : ℝ) ≤ 0 := by
        calc (S.card : ℝ)
          = ((S.card : ℝ) / K) * K := by field_simp [hK_pos.ne'] <;> ring
        _ ≤ 0 * K := by gcongr
        _ = 0 := by ring
      linarith
    have h5 : S.card = 0 := by exact_mod_cast h4
    have h6 : S = ∅ := by simpa using h5
    rw [h6] at hS_nonempty
    simp at hS_nonempty
  have hP'_nonempty : P'.Nonempty := by
    rcases hS'_nonempty with ⟨idx, hidx⟩
    let x : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp (2 : ENNReal) fun k : Fin 2 =>
        if k = 0 then (idx.1 : ℝ) * δ else (idx.2 : ℝ) * δ
    have hx0 : x 0 = (idx.1 : ℝ) * δ := by
      simp [x, PiLp.toLp_apply] <;> norm_num
    have hx1 : x 1 = (idx.2 : ℝ) * δ := by
      simp [x, PiLp.toLp_apply] <;> norm_num
    have hx : x ∈ dyadicSquare δ idx.1 idx.2 := by
      simp only [dyadicSquare, Set.mem_setOf_eq]
      constructor
      · simp [Set.mem_Ico, hx0] <;> linarith
      · simp [Set.mem_Ico, hx1] <;> linarith
    exact ⟨x, Set.mem_iUnion₂.mpr ⟨idx, hidx, hx⟩⟩
  have hP'_union_squares : ∀ (x : EuclideanPlane), x ∈ P' →
      ∃ (i j : ℤ), x ∈ dyadicSquare δ i j ∧ (dyadicSquare δ i j : Set EuclideanPlane) ⊆ P' := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨idx, hidx, hx2⟩
    refine ⟨idx.1, idx.2, hx2, ?_⟩
    intro y hy
    exact Set.mem_iUnion₂.mpr ⟨idx, hidx, hy⟩
  rcases basic_uniformization_dyadic n hn δ hδ_pos hδ_lt_one nδ hδ_eq Δ hΔ_dyadic hΔ_pos
      hΔ_strict hΔ_end hΔ_start P' hP'_bounded hP'_nonempty hP'_union_squares
    with ⟨S'', N'', hS''_sub_set, h_unif_S'', h_cover_density⟩
  have hS''_sub' : S'' ⊆ S' := by
    have h : setFromIndices δ S'' ⊆ setFromIndices δ S' := hS''_sub_set
    exact (setFromIndices_subset_iff hδ_pos).mp h
  -- Define a_choice matching the Classical.choose used by basic_uniformization_dyadic
  let a_choice : Fin (n + 1) → ℕ := fun i =>
    Classical.choose (show ∃ (n : ℕ), Δ i = (2 : ℝ)^(-(n : ℤ)) from
      by simpa [dyadicScales] using hΔ_dyadic i)
  have ha'_spec : ∀ i, Δ i = dyadicDelta (a_choice i) := by
    intro i
    have h_exists : ∃ (n : ℕ), Δ i = (2 : ℝ)^(-(n : ℤ)) := by
      simpa [dyadicScales] using hΔ_dyadic i
    have h : Δ i = (2 : ℝ)^(-(a_choice i : ℤ)) := Classical.choose_spec h_exists
    have h2 : dyadicDelta (a_choice i) = (2 : ℝ)^(-(a_choice i : ℤ)) := by
      simp [dyadicDelta] <;> field_simp <;> ring
    rw [h, h2]
  have h_a_eq : a = a_choice := by
    funext i
    have h1 : Δ i = dyadicDelta (a i) := ha_spec i
    have h2 : Δ i = dyadicDelta (a_choice i) := ha'_spec i
    have h3 : dyadicDelta (a i) = dyadicDelta (a_choice i) := by rw [←h1, h2]
    exact dyadicDelta_injective h3
  have h_unif_S''_a : RangeUniformityProp n a S'' N'' := by
    have h4 : RangeUniformityProp n a_choice S'' N'' := h_unif_S''
    rw [h_a_eq.symm] at h4
    exact h4
  have hP'_eq2 : P' = setFromIndices (dyadicDelta nδ) S' := by
    dsimp only [P']
    rw [hδ_eq]
  have h_cover_S' : (DyadicCubes.dyadicCoveringNumber nδ P' hP'_bounded : ℝ) = (S'.card : ℝ) := by
    have h_gen : ∀ (X : Set EuclideanPlane) (hX : Bornology.IsBounded X),
        X = setFromIndices (dyadicDelta nδ) S' →
        (DyadicCubes.dyadicCoveringNumber nδ X hX : ℝ) = (S'.card : ℝ) := by
      intro X hX h_eq
      subst h_eq
      exact_mod_cast count_eq_card nδ S' hS'_nonempty
    exact h_gen P' hP'_bounded hP'_eq2
  have hS''_nonempty : S''.Nonempty := h_unif_S''_a.1
  have hP''_eq2 : setFromIndices δ S'' = setFromIndices (dyadicDelta nδ) S'' := by
    rw [hδ_eq]
  have hP''_bounded : Bornology.IsBounded (setFromIndices δ S'') := by
    have h_eq : setFromIndices δ S'' = setFromIndices (dyadicDelta nδ) S'' := hP''_eq2
    rw [h_eq]
    exact setFromIndices_isBounded nδ S''
  have h_cover_S'' : (DyadicCubes.dyadicCoveringNumber nδ (setFromIndices δ S'') hP''_bounded : ℝ) = (S''.card : ℝ) := by
    have h_gen : ∀ (X : Set EuclideanPlane) (hX : Bornology.IsBounded X),
        X = setFromIndices (dyadicDelta nδ) S'' →
        (DyadicCubes.dyadicCoveringNumber nδ X hX : ℝ) = (S''.card : ℝ) := by
      intro X hX h_eq
      subst h_eq
      exact_mod_cast count_eq_card nδ S'' hS''_nonempty
    exact h_gen (setFromIndices δ S'') hP''_bounded hP''_eq2
  have h_density_S'' : (S''.card : ℝ) ≥ (S'.card : ℝ) / L_unif := by
    rw [h_cover_S''] at h_cover_density
    rw [h_cover_S'] at h_cover_density
    exact h_cover_density
  have h_global_density : (S''.card : ℝ) ≥ (S.card : ℝ) / M := by
    calc (S''.card : ℝ)
      ≥ (S'.card : ℝ) / L_unif := h_density_S''
    _ ≥ ((S.card : ℝ) / K) / L_unif := by gcongr
    _ = (S.card : ℝ) / M := by
      have h : ((S.card : ℝ) / K) / L_unif = (S.card : ℝ) / (K * L_unif) := by
        calc
          ((S.card : ℝ) / K) / L_unif
            = (S.card : ℝ) / (K * L_unif) := by ring_nf
          _ = (S.card : ℝ) / (K * L_unif) := rfl
      rw [h]
      <;> rfl
  have hS''_sub_S : S'' ⊆ S :=
    Finset.Subset.trans hS''_sub' hS'_sub
  have h_a0 : a 0 = 0 := by
    have h1 : Δ 0 = dyadicDelta (a 0) := ha_spec 0
    rw [hΔ_start] at h1
    have h2 : dyadicDelta (a 0) = 1 := h1.symm
    have h3 : a 0 = 0 := by
      by_contra h4
      have h5 : 0 < a 0 := by omega
      have h6 : dyadicDelta (a 0) < 1 := by
        simp [dyadicDelta]
        have h7 : (1 : ℝ) < (2 : ℝ) ^ (a 0) := by
          have h8 : a 0 ≠ 0 := by omega
          have h9 : (1 : ℝ) < (2 : ℝ) := by norm_num
          exact one_lt_pow₀ h9 h8
        field_simp [h7.ne'] <;> linarith
      linarith
    exact h3
  have h_a_mono : ∀ (i : Fin n), a i.castSucc ≤ a (Fin.succ i) := by
    intro i
    have h1 : Δ (Fin.succ i) < Δ i.castSucc := hΔ_strict i
    have h2 : Δ (Fin.succ i) = dyadicDelta (a (Fin.succ i)) := ha_spec (Fin.succ i)
    have h3 : Δ i.castSucc = dyadicDelta (a i.castSucc) := ha_spec i.castSucc
    rw [h2, h3] at h1
    by_contra h4
    have h5 : a (Fin.succ i) ≤ a i.castSucc := by omega
    have h6 : dyadicDelta (a i.castSucc) ≤ dyadicDelta (a (Fin.succ i)) := dyadicDelta_anti h5
    linarith
  have h_a_last : ∀ (i : Fin (n + 1)), a i ≤ a (Fin.last n) := by
    have h_step : ∀ (k : ℕ), k < n →
        (h1 : k < n + 1) → (h2 : k + 1 < n + 1) →
        a ⟨k, h1⟩ ≤ a ⟨k + 1, h2⟩ := by
      intro k hk h1 h2
      let j : Fin n := ⟨k, hk⟩
      have h_eq1 : (j.castSucc : Fin (n + 1)) = ⟨k, h1⟩ := by
        apply Fin.ext
        simp [j]
        <;> omega
      have h_eq2 : (Fin.succ j : Fin (n + 1)) = ⟨k + 1, h2⟩ := by
        apply Fin.ext
        simp [j]
        <;> omega
      have h3 := h_a_mono j
      rw [h_eq1, h_eq2] at h3
      exact h3
    intro i
    let d : ℕ := n - i.val
    have hd : i.val + d = n := by omega
    have h_i_lt : i.val < n + 1 := i.is_lt
    have h_up : ∀ (j : ℕ), j ≤ d →
        (h_j : i.val + j < n + 1) → a ⟨i.val, h_i_lt⟩ ≤ a ⟨i.val + j, h_j⟩ := by
      intro j hj h_j
      induction j with
      | zero => rfl
      | succ j ih =>
        have h5 : i.val + j < n := by omega
        have h6 : i.val + j < n + 1 := by omega
        have h7 : i.val + j + 1 < n + 1 := by omega
        have h_step' := h_step (i.val + j) h5 h6 h7
        exact le_trans (ih (by omega) h6) h_step'
    have h_last_lt : i.val + d < n + 1 := by omega
    have h12 := h_up d (by linarith) h_last_lt
    have h13 : (⟨i.val + d, h_last_lt⟩ : Fin (n + 1)) = Fin.last n := by
      apply Fin.ext
      exact hd
    rw [h13] at h12
    exact h12
  have h_unit_S'' : ∀ idx ∈ S'', 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
      idx.1 < (2 : ℤ)^(a (Fin.last n)) ∧ idx.2 < (2 : ℤ)^(a (Fin.last n)) := by
    intro idx hidx
    have h5 : idx ∈ S := hS''_sub_S hidx
    exact h_unit_S idx h5
  have h_per_level : ∀ (j : Fin n), (N'' j : ℝ) ≥ (N j : ℝ) / (M * (4 : ℝ)^n) :=
    per_level_density hS''_sub_S h_unif_S h_unif_S''_a
      h_a0 h_a_mono h_a_last h_unit_S h_unit_S''
      M hM_pos h_global_density
  let c : ℝ := 1 / (2 * M * (4 : ℝ)^n)
  have hc_pos : 0 < c := by positivity
  have h_transfer : ∀ (j : Fin n),
      IsSetBetweenScales (setFromIndices δ S'') (Δ (Fin.succ j)) (Δ j.castSucc) s
        (9 * C * 2 * M * (4 : ℝ)^n) := by
    intro j
    have hδ_fine_pos : 0 < Δ (Fin.succ j) := hΔ_pos (Fin.succ j)
    have hδ_fine_dyadic : Δ (Fin.succ j) ∈ dyadicScales := hΔ_dyadic (Fin.succ j)
    have hδ_coarse_pos : 0 < Δ j.castSucc := hΔ_pos j.castSucc
    have hδ_fine_le_coarse : Δ (Fin.succ j) ≤ Δ j.castSucc := (hΔ_strict j).le
    have hP_bounded : Bornology.IsBounded (setFromIndices δ S) := by
      have h_eq : setFromIndices δ S = setFromIndices (dyadicDelta nδ) S := by rw [hδ_eq]
      rw [h_eq]
      exact setFromIndices_isBounded nδ S
    have hP''_bounded : Bornology.IsBounded (setFromIndices δ S'') := by
      have h_eq : setFromIndices δ S'' = setFromIndices (dyadicDelta nδ) S'' := by rw [hδ_eq]
      rw [h_eq]
      exact setFromIndices_isBounded nδ S''
    have hsub : setFromIndices δ S'' ⊆ setFromIndices δ S := setFromIndices_subset hS''_sub_S
    have h_k_eq_nδ : a (Fin.last n) = nδ := by
      have h1 : Δ (Fin.last n) = dyadicDelta (a (Fin.last n)) := ha_spec (Fin.last n)
      have h2 : Δ (Fin.last n) = δ := hΔ_end
      have h3 : dyadicDelta (a (Fin.last n)) = δ := by rw [←h1, h2]
      have h4 : dyadicDelta (a (Fin.last n)) = dyadicDelta nδ := by rw [h3, hδ_eq]
      exact dyadicDelta_injective h4
    have hdensity_dyadic : ∀ (a b : ℤ), (setFromIndices δ S'' ∩ dyadicSquare (Δ j.castSucc) a b).Nonempty →
        (dyadicSquareCount (Δ (Fin.succ j)) (setFromIndices δ S'' ∩ dyadicSquare (Δ j.castSucc) a b) : ENNReal) ≥
        ENNReal.ofReal c * (dyadicSquareCount (Δ (Fin.succ j)) (setFromIndices δ S ∩ dyadicSquare (Δ j.castSucc) a b) : ENNReal) := by
      intro a_idx b_idx h_nonempty
      let g : ℤ × ℤ := (a_idx, b_idx)
      let a_fine := a (Fin.succ j)
      let a_coarse := a j.castSucc
      let k := a (Fin.last n)
      have h_k_eq_nδ' : k = nδ := h_k_eq_nδ
      have h_coarse_le_fine : a_coarse ≤ a_fine := h_a_mono j
      have h_fine_le_k : a_fine ≤ k := h_a_last (Fin.succ j)
      let m_fine := k - a_fine
      let m_coarse := a_fine - a_coarse
      let fineSq_S'' := S''.image (parentBy m_fine)
      let filtered_S'' := fineSq_S''.filter (fun idx => parentBy m_coarse idx = g)
      let fineSq_S := S.image (parentBy m_fine)
      let filtered_S := fineSq_S.filter (fun idx => parentBy m_coarse idx = g)
      -- Bridge equalities
      have h_bridge_S'' := dyadicSquareCount_setFromIndices_inter k a_fine a_coarse h_coarse_le_fine h_fine_le_k S'' g
      have h_bridge_S := dyadicSquareCount_setFromIndices_inter k a_fine a_coarse h_coarse_le_fine h_fine_le_k S g
      have h_fine_eq : dyadicDelta a_fine = Δ (Fin.succ j) := (ha_spec (Fin.succ j)).symm
      have h_coarse_eq : dyadicDelta a_coarse = Δ j.castSucc := (ha_spec j.castSucc).symm
      have h_k_eq2 : dyadicDelta k = δ := by
        rw [h_k_eq_nδ', hδ_eq]
      have h_count_S'' : dyadicSquareCount (Δ (Fin.succ j)) (setFromIndices δ S'' ∩ dyadicSquare (Δ j.castSucc) a_idx b_idx) = ↑filtered_S''.card := by
        simpa [h_fine_eq, h_coarse_eq, h_k_eq2] using h_bridge_S''
      have h_count_S : dyadicSquareCount (Δ (Fin.succ j)) (setFromIndices δ S ∩ dyadicSquare (Δ j.castSucc) a_idx b_idx) = ↑filtered_S.card := by
        simpa [h_fine_eq, h_coarse_eq, h_k_eq2] using h_bridge_S
      -- Prove filtered_S'' nonempty from h_nonempty
      rcases h_nonempty with ⟨x, hx⟩
      have hx_in_S'' : x ∈ setFromIndices δ S'' := hx.1
      have hx_coarse : x ∈ dyadicSquare (Δ j.castSucc) a_idx b_idx := hx.2
      rcases Set.mem_iUnion₂.mp hx_in_S'' with ⟨idx, hidx, hx_square⟩
      have hx_square_k : x ∈ dyadicSquare (dyadicDelta k) idx.1 idx.2 := by
        have hδk : δ = dyadicDelta k := by rw [h_k_eq_nδ', hδ_eq]
        rw [hδk] at hx_square
        exact hx_square
      have hx_coarse_k : x ∈ dyadicSquare (dyadicDelta a_coarse) a_idx b_idx := by
        simpa [h_coarse_eq] using hx_coarse
      let p := parentBy m_fine idx
      have hp_in_img : p ∈ fineSq_S'' := Finset.mem_image.mpr ⟨idx, hidx, rfl⟩
      have h_inter : (dyadicSquare (dyadicDelta k) idx.1 idx.2 ∩
                      dyadicSquare (dyadicDelta a_coarse) a_idx b_idx).Nonempty :=
        ⟨x, hx_square_k, hx_coarse_k⟩
      have h_rewrite : k - (m_fine + m_coarse) = a_coarse := by
        dsimp only [m_fine, m_coarse]
        omega
      have h_le : m_fine + m_coarse ≤ k := by
        dsimp only [m_fine, m_coarse]
        omega
      have h_total : parentBy (m_fine + m_coarse) idx = g := by
        have h_inter' : (dyadicSquare (dyadicDelta k) idx.1 idx.2 ∩
                        dyadicSquare (dyadicDelta (k - (m_fine + m_coarse))) g.1 g.2).Nonempty := by
          rw [h_rewrite]
          exact h_inter
        exact dyadicSquare_inter_parentBy h_le idx g h_inter'
      have hp_filter : parentBy m_coarse p = g := by
        have h_comp : parentBy m_coarse (parentBy m_fine idx) = parentBy (m_fine + m_coarse) idx := by
          have h := parentBy_comp m_coarse m_fine idx
          rw [add_comm m_coarse m_fine] at h
          exact h
        exact h_comp.trans h_total
      have h_p_in_filtered : p ∈ filtered_S'' := by
        simp only [filtered_S'', Finset.mem_filter]
        exact ⟨hp_in_img, hp_filter⟩
      have hS''_nonzero : filtered_S''.card ≠ 0 :=
        Finset.card_ne_zero.mpr ⟨p, h_p_in_filtered⟩
      -- Apply single_level_density
      have h_sl : (filtered_S''.card : ℝ) ≥ c * (filtered_S.card : ℝ) :=
        single_level_density h_unif_S h_unif_S''_a M hM_pos h_per_level j g hS''_sub_S hS''_nonzero
      -- Convert to ENNReal
      rw [h_count_S'', h_count_S]
      have h_enn : (↑filtered_S''.card : ENNReal) ≥ ENNReal.ofReal c * (↑filtered_S.card : ENNReal) := by
        have h1 : (↑filtered_S''.card : ENNReal) = ENNReal.ofReal (filtered_S''.card : ℝ) := by
          simp
        have h2 : (↑filtered_S.card : ENNReal) = ENNReal.ofReal (filtered_S.card : ℝ) := by
          simp
        rw [h1, h2]
        have h3 : ENNReal.ofReal (filtered_S''.card : ℝ) ≥ ENNReal.ofReal (c * (filtered_S.card : ℝ)) :=
          ENNReal.ofReal_le_ofReal h_sl
        have h4 : ENNReal.ofReal (c * (filtered_S.card : ℝ)) = ENNReal.ofReal c * ENNReal.ofReal (filtered_S.card : ℝ) := by
          rw [ENNReal.ofReal_mul] <;> positivity
        rw [h4] at h3
        exact h3
      exact h_enn
    have h_result : IsSetBetweenScales (setFromIndices δ S'') (Δ (Fin.succ j)) (Δ j.castSucc) s (9 * C / c) :=
      uniformisation_Sset_transfer hδ_fine_pos hδ_fine_dyadic hδ_coarse_pos hδ_fine_le_coarse
        hs_nonneg hC_pos hc_pos hP_bounded hP''_bounded (h_between j) hsub hdensity_dyadic
    have h_const : 9 * C / c = 9 * C * 2 * M * (4 : ℝ)^n := by
      dsimp only [c]
      have hpos : (0 : ℝ) < 2 * M * (4 : ℝ)^n := by positivity
      field_simp [hpos.ne'] <;> ring
    rw [h_const] at h_result
    exact h_result
  exact ⟨S'', N'', hS''_sub', h_unif_S''_a, h_transfer⟩

/-- Tail uniformisation consumer with mixed transfer (OS Lemma 5 + good scales).

    Produces ONE common retained subset S'' that is uniform at all levels.
    At every level, the S-set property at exponent s is transferred.
    At good levels only, regularity at exponent t_j is also transferred.

    The S-set constant is amplified by `9/c`. For good levels, both the
    S-set and half-scale constants of the output regularity are set to
    `max(9*C_reg/c, K_reg)`, which is ≥ both transferred constants. -/
lemma tail_uniformisation_regular_consumer
    {n : ℕ} (hn : 0 < n)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (nδ : ℕ) (hδ_eq : δ = dyadicDelta nδ)
    (Δ : Fin (n + 1) → ℝ)
    (hΔ_dyadic : ∀ i, Δ i ∈ dyadicScales)
    (hΔ_pos : ∀ i, 0 < Δ i)
    (hΔ_strict : ∀ j : Fin n, Δ (Fin.succ j) < Δ j.castSucc)
    (hΔ_end : Δ (Fin.last n) = δ)
    (hΔ_start : Δ 0 = 1)
    (a : Fin (n + 1) → ℕ)
    (ha_spec : ∀ i, Δ i = dyadicDelta (a i))
    (S S' : Finset (ℤ × ℤ))
    (N : Fin n → ℕ)
    (h_unif_S : RangeUniformityProp n a S N)
    (hS'_sub : S' ⊆ S)
    (K : ℝ) (hK_pos : 0 < K)
    (h_density : (S'.card : ℝ) ≥ (S.card : ℝ) / K)
    (s : ℝ) (hs_nonneg : 0 ≤ s)
    (C : ℝ) (hC_pos : 0 < C)
    (h_between : ∀ (j : Fin n),
      IsSetBetweenScales (setFromIndices δ S) (Δ (Fin.succ j)) (Δ j.castSucc) s C)
    -- Scale classification and per-good-level regularity
    (scaleClass : Fin n → CombiningTheorem.ScaleClass)
    (C_reg K_reg : Fin n → ℝ)
    (hC_reg_pos : ∀ j, 0 < C_reg j)
    (hK_reg_pos : ∀ j, 0 < K_reg j)
    (h_regular : ∀ (j : Fin n) (t_j : ℝ),
      scaleClass j = CombiningTheorem.ScaleClass.good t_j →
        IsRegularBetweenScales (setFromIndices δ S) (Δ (Fin.succ j)) (Δ j.castSucc)
          t_j (C_reg j) (K_reg j))
    (h_unit_S : ∀ idx ∈ S, 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
      idx.1 < (2 : ℤ)^(a (Fin.last n)) ∧ idx.2 < (2 : ℤ)^(a (Fin.last n))) :
    ∃ (S'' : Finset (ℤ × ℤ)) (N'' : Fin n → ℕ),
      S'' ⊆ S' ∧
      RangeUniformityProp n a S'' N'' ∧
      (∀ (j : Fin n),
        IsSetBetweenScales (setFromIndices δ S'') (Δ (Fin.succ j)) (Δ j.castSucc) s
          (9 * C * 2 * (K * (24 * Real.log (1 / δ) / (n : ℝ)) ^ n) * (4 : ℝ)^n)) ∧
      (∀ (j : Fin n) (t_j : ℝ),
        scaleClass j = CombiningTheorem.ScaleClass.good t_j →
          IsRegularBetweenScales (setFromIndices δ S'') (Δ (Fin.succ j)) (Δ j.castSucc)
            t_j
            (max (9 * (C_reg j) * 2 * (K * (24 * Real.log (1 / δ) / (n : ℝ)) ^ n) * (4 : ℝ)^n) (K_reg j))
            (max (9 * (C_reg j) * 2 * (K * (24 * Real.log (1 / δ) / (n : ℝ)) ^ n) * (4 : ℝ)^n) (K_reg j))) := by
  have hlog_pos : 0 < Real.log (1 / δ) := Real.log_pos (by
    have h : 1 < 1 / δ := by
      apply one_lt_one_div <;> linarith
    exact h)
  let L_unif : ℝ := (24 * Real.log (1 / δ) / (n : ℝ)) ^ n
  have hL_pos : 0 < L_unif := by
    have h1 : 0 < 24 * Real.log (1 / δ) / (n : ℝ) := by
      apply div_pos <;> positivity
    positivity
  let M : ℝ := K * L_unif
  have hM_pos : 0 < M := mul_pos hK_pos hL_pos
  let P' : Set EuclideanPlane := setFromIndices δ S'
  have hP'_bounded : Bornology.IsBounded P' := by
    have h_eq : P' = setFromIndices (dyadicDelta nδ) S' := by
      dsimp only [P']; rw [hδ_eq]
    rw [h_eq]; exact setFromIndices_isBounded nδ S'
  have hS_nonempty : S.Nonempty := h_unif_S.1
  have hS'_nonempty : S'.Nonempty := by
    by_contra h2
    have h3 : S' = ∅ := by simpa using h2
    rw [h3] at h_density
    have h4 : (S.card : ℝ) = 0 := by
      have h5 : (0 : ℝ) ≥ (S.card : ℝ) / K := by simpa using h_density
      have h6 : 0 ≤ (S.card : ℝ) := by positivity
      have h7 : (S.card : ℝ) / K ≤ 0 := by linarith
      have h8 : (S.card : ℝ) ≤ 0 := by
        calc (S.card : ℝ)
          = ((S.card : ℝ) / K) * K := by field_simp [hK_pos.ne'] <;> ring
        _ ≤ 0 * K := by gcongr
        _ = 0 := by ring
      linarith
    have h5 : S.card = 0 := by exact_mod_cast h4
    have h6 : S = ∅ := by simpa using h5
    rw [h6] at hS_nonempty; simp at hS_nonempty
  have hP'_nonempty : P'.Nonempty := by
    rcases hS'_nonempty with ⟨idx, hidx⟩
    let x : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp (2 : ENNReal) fun k : Fin 2 =>
        if k = 0 then (idx.1 : ℝ) * δ else (idx.2 : ℝ) * δ
    have hx0 : x 0 = (idx.1 : ℝ) * δ := by simp [x, PiLp.toLp_apply] <;> norm_num
    have hx1 : x 1 = (idx.2 : ℝ) * δ := by simp [x, PiLp.toLp_apply] <;> norm_num
    have hx : x ∈ dyadicSquare δ idx.1 idx.2 := by
      simp only [dyadicSquare, Set.mem_setOf_eq]
      constructor
      · simp [Set.mem_Ico, hx0] <;> linarith
      · simp [Set.mem_Ico, hx1] <;> linarith
    exact ⟨x, Set.mem_iUnion₂.mpr ⟨idx, hidx, hx⟩⟩
  have hP'_union_squares : ∀ (x : EuclideanPlane), x ∈ P' →
      ∃ (i j : ℤ), x ∈ dyadicSquare δ i j ∧ (dyadicSquare δ i j : Set EuclideanPlane) ⊆ P' := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨idx, hidx, hx2⟩
    refine ⟨idx.1, idx.2, hx2, ?_⟩
    intro y hy
    exact Set.mem_iUnion₂.mpr ⟨idx, hidx, hy⟩
  rcases basic_uniformization_dyadic n hn δ hδ_pos hδ_lt_one nδ hδ_eq Δ hΔ_dyadic hΔ_pos
      hΔ_strict hΔ_end hΔ_start P' hP'_bounded hP'_nonempty hP'_union_squares
    with ⟨S'', N'', hS''_sub_set, h_unif_S'', h_cover_density⟩
  have hS''_sub' : S'' ⊆ S' := by
    have h : setFromIndices δ S'' ⊆ setFromIndices δ S' := hS''_sub_set
    exact (setFromIndices_subset_iff hδ_pos).mp h
  let a_choice : Fin (n + 1) → ℕ := fun i =>
    Classical.choose (show ∃ (n : ℕ), Δ i = (2 : ℝ)^(-(n : ℤ)) from
      by simpa [dyadicScales] using hΔ_dyadic i)
  have ha'_spec : ∀ i, Δ i = dyadicDelta (a_choice i) := by
    intro i
    have h_exists : ∃ (n : ℕ), Δ i = (2 : ℝ)^(-(n : ℤ)) := by
      simpa [dyadicScales] using hΔ_dyadic i
    have h : Δ i = (2 : ℝ)^(-(a_choice i : ℤ)) := Classical.choose_spec h_exists
    have h2 : dyadicDelta (a_choice i) = (2 : ℝ)^(-(a_choice i : ℤ)) := by
      simp [dyadicDelta] <;> field_simp <;> ring
    rw [h, h2]
  have h_a_eq : a = a_choice := by
    funext i
    have h1 : Δ i = dyadicDelta (a i) := ha_spec i
    have h2 : Δ i = dyadicDelta (a_choice i) := ha'_spec i
    have h3 : dyadicDelta (a i) = dyadicDelta (a_choice i) := by rw [←h1, h2]
    exact dyadicDelta_injective h3
  have h_unif_S''_a : RangeUniformityProp n a S'' N'' := by
    have h4 : RangeUniformityProp n a_choice S'' N'' := h_unif_S''
    rw [h_a_eq.symm] at h4
    exact h4
  have hP'_eq2 : P' = setFromIndices (dyadicDelta nδ) S' := by
    dsimp only [P']; rw [hδ_eq]
  have h_cover_S' : (DyadicCubes.dyadicCoveringNumber nδ P' hP'_bounded : ℝ) = (S'.card : ℝ) := by
    have h_gen : ∀ (X : Set EuclideanPlane) (hX : Bornology.IsBounded X),
        X = setFromIndices (dyadicDelta nδ) S' →
        (DyadicCubes.dyadicCoveringNumber nδ X hX : ℝ) = (S'.card : ℝ) := by
      intro X hX h_eq; subst h_eq; exact_mod_cast count_eq_card nδ S' hS'_nonempty
    exact h_gen P' hP'_bounded hP'_eq2
  have hS''_nonempty : S''.Nonempty := h_unif_S''_a.1
  have hP''_bounded : Bornology.IsBounded (setFromIndices δ S'') := by
    have h_eq : setFromIndices δ S'' = setFromIndices (dyadicDelta nδ) S'' := by rw [hδ_eq]
    rw [h_eq]; exact setFromIndices_isBounded nδ S''
  have h_cover_S'' : (DyadicCubes.dyadicCoveringNumber nδ (setFromIndices δ S'') hP''_bounded : ℝ) = (S''.card : ℝ) := by
    have h_gen : ∀ (X : Set EuclideanPlane) (hX : Bornology.IsBounded X),
        X = setFromIndices (dyadicDelta nδ) S'' →
        (DyadicCubes.dyadicCoveringNumber nδ X hX : ℝ) = (S''.card : ℝ) := by
      intro X hX h_eq; subst h_eq; exact_mod_cast count_eq_card nδ S'' hS''_nonempty
    exact h_gen (setFromIndices δ S'') hP''_bounded (by rw [hδ_eq])
  have h_density_S'' : (S''.card : ℝ) ≥ (S'.card : ℝ) / L_unif := by
    rw [h_cover_S''] at h_cover_density
    rw [h_cover_S'] at h_cover_density
    exact h_cover_density
  have h_global_density : (S''.card : ℝ) ≥ (S.card : ℝ) / M := by
    calc (S''.card : ℝ)
      ≥ (S'.card : ℝ) / L_unif := h_density_S''
    _ ≥ ((S.card : ℝ) / K) / L_unif := by gcongr
    _ = (S.card : ℝ) / M := by
      have h : ((S.card : ℝ) / K) / L_unif = (S.card : ℝ) / (K * L_unif) := by ring_nf
      rw [h] <;> rfl
  have hS''_sub_S : S'' ⊆ S := Finset.Subset.trans hS''_sub' hS'_sub
  have h_a0 : a 0 = 0 := by
    have h1 : Δ 0 = dyadicDelta (a 0) := ha_spec 0
    rw [hΔ_start] at h1
    have h2 : dyadicDelta (a 0) = 1 := h1.symm
    have h3 : a 0 = 0 := by
      by_contra h4
      have h5 : 0 < a 0 := by omega
      have h6 : dyadicDelta (a 0) < 1 := by
        simp [dyadicDelta]
        have h7 : (1 : ℝ) < (2 : ℝ) ^ (a 0) := by
          have h8 : a 0 ≠ 0 := by omega
          have h9 : (1 : ℝ) < (2 : ℝ) := by norm_num
          exact one_lt_pow₀ h9 h8
        field_simp [h7.ne'] <;> linarith
      linarith
    exact h3
  have h_a_mono : ∀ (j : Fin n), a j.castSucc < a (Fin.succ j) := by
    intro j
    have h1 : Δ (Fin.succ j) < Δ j.castSucc := hΔ_strict j
    have h2 : Δ (Fin.succ j) = dyadicDelta (a (Fin.succ j)) := ha_spec (Fin.succ j)
    have h3 : Δ j.castSucc = dyadicDelta (a j.castSucc) := ha_spec j.castSucc
    rw [h2, h3] at h1
    by_contra h4
    have h5 : a (Fin.succ j) ≤ a j.castSucc := by omega
    have h6 : dyadicDelta (a j.castSucc) ≤ dyadicDelta (a (Fin.succ j)) := dyadicDelta_anti h5
    linarith
  have h_a_mono_le : ∀ (i : Fin n), a i.castSucc ≤ a (Fin.succ i) := fun i => (h_a_mono i).le
  have h_a_last : ∀ (i : Fin (n + 1)), a i ≤ a (Fin.last n) := by
    have h_step : ∀ (k : ℕ), k < n →
        (h1 : k < n + 1) → (h2 : k + 1 < n + 1) →
        a ⟨k, h1⟩ ≤ a ⟨k + 1, h2⟩ := by
      intro k hk h1 h2
      let j : Fin n := ⟨k, hk⟩
      have h_eq1 : (j.castSucc : Fin (n + 1)) = ⟨k, h1⟩ := by
        apply Fin.ext; simp [j] <;> omega
      have h_eq2 : (Fin.succ j : Fin (n + 1)) = ⟨k + 1, h2⟩ := by
        apply Fin.ext; simp [j] <;> omega
      have h3 := h_a_mono j
      rw [h_eq1, h_eq2] at h3
      exact h3.le
    intro i
    let d : ℕ := n - i.val
    have hd : i.val + d = n := by omega
    have h_i_lt : i.val < n + 1 := i.is_lt
    have h_up : ∀ (j : ℕ), j ≤ d →
        (h_j : i.val + j < n + 1) → a ⟨i.val, h_i_lt⟩ ≤ a ⟨i.val + j, h_j⟩ := by
      intro j hj h_j
      induction j with
      | zero => rfl
      | succ j ih =>
        have h5 : i.val + j < n := by omega
        have h6 : i.val + j < n + 1 := by omega
        have h7 : i.val + j + 1 < n + 1 := by omega
        have h_step' := h_step (i.val + j) h5 h6 h7
        exact le_trans (ih (by omega) h6) h_step'
    have h_last_lt : i.val + d < n + 1 := by omega
    have h12 := h_up d (by linarith) h_last_lt
    have h13 : (⟨i.val + d, h_last_lt⟩ : Fin (n + 1)) = Fin.last n := by
      apply Fin.ext; exact hd
    rw [h13] at h12
    exact h12
  have h_unit_S'' : ∀ idx ∈ S'', 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
      idx.1 < (2 : ℤ)^(a (Fin.last n)) ∧ idx.2 < (2 : ℤ)^(a (Fin.last n)) := by
    intro idx hidx
    have h5 : idx ∈ S := hS''_sub_S hidx
    exact h_unit_S idx h5
  have h_per_level : ∀ (j : Fin n), (N'' j : ℝ) ≥ (N j : ℝ) / (M * (4 : ℝ)^n) :=
    per_level_density hS''_sub_S h_unif_S h_unif_S''_a
      h_a0 h_a_mono_le h_a_last h_unit_S h_unit_S''
      M hM_pos h_global_density
  let c : ℝ := 1 / (2 * M * (4 : ℝ)^n)
  have hc_pos : 0 < c := by positivity
  have h_k_eq_nδ : a (Fin.last n) = nδ := by
    have h1 : Δ (Fin.last n) = dyadicDelta (a (Fin.last n)) := ha_spec (Fin.last n)
    have h2 : Δ (Fin.last n) = δ := hΔ_end
    have h3 : dyadicDelta (a (Fin.last n)) = δ := by rw [←h1, h2]
    have h4 : dyadicDelta (a (Fin.last n)) = dyadicDelta nδ := by rw [h3, hδ_eq]
    exact dyadicDelta_injective h4
  have hP_bounded : Bornology.IsBounded (setFromIndices δ S) := by
    have h_eq : setFromIndices δ S = setFromIndices (dyadicDelta nδ) S := by rw [hδ_eq]
    rw [h_eq]; exact setFromIndices_isBounded nδ S
  have hP''_bounded2 : Bornology.IsBounded (setFromIndices δ S'') := hP''_bounded
  have hsub : setFromIndices δ S'' ⊆ setFromIndices δ S := setFromIndices_subset hS''_sub_S
  have h_transfer_set : ∀ (j : Fin n),
      IsSetBetweenScales (setFromIndices δ S'') (Δ (Fin.succ j)) (Δ j.castSucc) s
        (9 * C * 2 * M * (4 : ℝ)^n) := by
    intro j
    have hδ_fine_pos : 0 < Δ (Fin.succ j) := hΔ_pos (Fin.succ j)
    have hδ_fine_dyadic : Δ (Fin.succ j) ∈ dyadicScales := hΔ_dyadic (Fin.succ j)
    have hδ_coarse_pos : 0 < Δ j.castSucc := hΔ_pos j.castSucc
    have hδ_fine_le_coarse : Δ (Fin.succ j) ≤ Δ j.castSucc := (hΔ_strict j).le
    have hdensity_dyadic : ∀ (a_idx b_idx : ℤ),
        (setFromIndices δ S'' ∩ dyadicSquare (Δ j.castSucc) a_idx b_idx).Nonempty →
        (dyadicSquareCount (Δ (Fin.succ j)) (setFromIndices δ S'' ∩ dyadicSquare (Δ j.castSucc) a_idx b_idx) : ENNReal) ≥
        ENNReal.ofReal c * (dyadicSquareCount (Δ (Fin.succ j)) (setFromIndices δ S ∩ dyadicSquare (Δ j.castSucc) a_idx b_idx) : ENNReal) := by
      intro a_idx b_idx h_nonempty
      let g : ℤ × ℤ := (a_idx, b_idx)
      let a_fine := a (Fin.succ j)
      let a_coarse := a j.castSucc
      let k := a (Fin.last n)
      have h_k_eq_nδ' : k = nδ := h_k_eq_nδ
      have h_coarse_le_fine : a_coarse ≤ a_fine := (h_a_mono j).le
      have h_fine_le_k : a_fine ≤ k := h_a_last (Fin.succ j)
      let m_fine := k - a_fine
      let m_coarse := a_fine - a_coarse
      let fineSq_S'' := S''.image (parentBy m_fine)
      let filtered_S'' := fineSq_S''.filter (fun idx => parentBy m_coarse idx = g)
      let fineSq_S := S.image (parentBy m_fine)
      let filtered_S := fineSq_S.filter (fun idx => parentBy m_coarse idx = g)
      have h_bridge_S'' := dyadicSquareCount_setFromIndices_inter k a_fine a_coarse h_coarse_le_fine h_fine_le_k S'' g
      have h_bridge_S := dyadicSquareCount_setFromIndices_inter k a_fine a_coarse h_coarse_le_fine h_fine_le_k S g
      have h_fine_eq : dyadicDelta a_fine = Δ (Fin.succ j) := (ha_spec (Fin.succ j)).symm
      have h_coarse_eq : dyadicDelta a_coarse = Δ j.castSucc := (ha_spec j.castSucc).symm
      have h_k_eq2 : dyadicDelta k = δ := by rw [h_k_eq_nδ', hδ_eq]
      have h_count_S'' : dyadicSquareCount (Δ (Fin.succ j)) (setFromIndices δ S'' ∩ dyadicSquare (Δ j.castSucc) a_idx b_idx) = ↑filtered_S''.card := by
        simpa [h_fine_eq, h_coarse_eq, h_k_eq2] using h_bridge_S''
      have h_count_S : dyadicSquareCount (Δ (Fin.succ j)) (setFromIndices δ S ∩ dyadicSquare (Δ j.castSucc) a_idx b_idx) = ↑filtered_S.card := by
        simpa [h_fine_eq, h_coarse_eq, h_k_eq2] using h_bridge_S
      rcases h_nonempty with ⟨x, hx⟩
      have hx_in_S'' : x ∈ setFromIndices δ S'' := hx.1
      have hx_coarse : x ∈ dyadicSquare (Δ j.castSucc) a_idx b_idx := hx.2
      rcases Set.mem_iUnion₂.mp hx_in_S'' with ⟨idx, hidx, hx_square⟩
      have hx_square_k : x ∈ dyadicSquare (dyadicDelta k) idx.1 idx.2 := by
        have hδk : δ = dyadicDelta k := by rw [h_k_eq_nδ', hδ_eq]
        rw [hδk] at hx_square; exact hx_square
      have hx_coarse_k : x ∈ dyadicSquare (dyadicDelta a_coarse) a_idx b_idx := by
        simpa [h_coarse_eq] using hx_coarse
      let p := parentBy m_fine idx
      have hp_in_img : p ∈ fineSq_S'' := Finset.mem_image.mpr ⟨idx, hidx, rfl⟩
      have h_inter : (dyadicSquare (dyadicDelta k) idx.1 idx.2 ∩ dyadicSquare (dyadicDelta a_coarse) a_idx b_idx).Nonempty :=
        ⟨x, hx_square_k, hx_coarse_k⟩
      have h_rewrite : k - (m_fine + m_coarse) = a_coarse := by dsimp only [m_fine, m_coarse]; omega
      have h_le : m_fine + m_coarse ≤ k := by dsimp only [m_fine, m_coarse]; omega
      have h_total : parentBy (m_fine + m_coarse) idx = g := by
        have h_inter' : (dyadicSquare (dyadicDelta k) idx.1 idx.2 ∩ dyadicSquare (dyadicDelta (k - (m_fine + m_coarse))) g.1 g.2).Nonempty := by
          rw [h_rewrite]; exact h_inter
        exact dyadicSquare_inter_parentBy h_le idx g h_inter'
      have hp_filter : parentBy m_coarse p = g := by
        have h_comp : parentBy m_coarse (parentBy m_fine idx) = parentBy (m_fine + m_coarse) idx := by
          have h := parentBy_comp m_coarse m_fine idx
          rw [add_comm m_coarse m_fine] at h; exact h
        exact h_comp.trans h_total
      have h_p_in_filtered : p ∈ filtered_S'' := by
        simp only [filtered_S'', Finset.mem_filter]; exact ⟨hp_in_img, hp_filter⟩
      have hS''_nonzero : filtered_S''.card ≠ 0 := Finset.card_ne_zero.mpr ⟨p, h_p_in_filtered⟩
      have h_sl : (filtered_S''.card : ℝ) ≥ c * (filtered_S.card : ℝ) :=
        single_level_density h_unif_S h_unif_S''_a M hM_pos h_per_level j g hS''_sub_S hS''_nonzero
      rw [h_count_S'', h_count_S]
      have h_enn : (↑filtered_S''.card : ENNReal) ≥ ENNReal.ofReal c * (↑filtered_S.card : ENNReal) := by
        have h1 : (↑filtered_S''.card : ENNReal) = ENNReal.ofReal (filtered_S''.card : ℝ) := by simp
        have h2 : (↑filtered_S.card : ENNReal) = ENNReal.ofReal (filtered_S.card : ℝ) := by simp
        rw [h1, h2]
        have h3 : ENNReal.ofReal (filtered_S''.card : ℝ) ≥ ENNReal.ofReal (c * (filtered_S.card : ℝ)) :=
          ENNReal.ofReal_le_ofReal h_sl
        have h4 : ENNReal.ofReal (c * (filtered_S.card : ℝ)) = ENNReal.ofReal c * ENNReal.ofReal (filtered_S.card : ℝ) := by
          rw [ENNReal.ofReal_mul] <;> positivity
        rw [h4] at h3; exact h3
      exact h_enn
    have h_result : IsSetBetweenScales (setFromIndices δ S'') (Δ (Fin.succ j)) (Δ j.castSucc) s (9 * C / c) :=
      uniformisation_Sset_transfer hδ_fine_pos hδ_fine_dyadic hδ_coarse_pos hδ_fine_le_coarse
        hs_nonneg hC_pos hc_pos hP_bounded hP''_bounded2 (h_between j) hsub hdensity_dyadic
    have h_const : 9 * C / c = 9 * C * 2 * M * (4 : ℝ)^n := by
      dsimp only [c]
      have hpos : (0 : ℝ) < 2 * M * (4 : ℝ)^n := by positivity
      field_simp [hpos.ne'] <;> ring
    rw [h_const] at h_result
    exact h_result
  have h_transfer_reg : ∀ (j : Fin n) (t_j : ℝ),
      scaleClass j = CombiningTheorem.ScaleClass.good t_j →
        IsRegularBetweenScales (setFromIndices δ S'') (Δ (Fin.succ j)) (Δ j.castSucc)
          t_j (9 * (C_reg j) / c) (K_reg j) := by
    intro j t_j hgood
    have hδ_fine_pos : 0 < Δ (Fin.succ j) := hΔ_pos (Fin.succ j)
    have hδ_fine_dyadic : Δ (Fin.succ j) ∈ dyadicScales := hΔ_dyadic (Fin.succ j)
    have hδ_coarse_pos : 0 < Δ j.castSucc := hΔ_pos j.castSucc
    have hδ_fine_le_coarse : Δ (Fin.succ j) ≤ Δ j.castSucc := (hΔ_strict j).le
    have hdensity_dyadic : ∀ (a_idx b_idx : ℤ),
        (setFromIndices δ S'' ∩ dyadicSquare (Δ j.castSucc) a_idx b_idx).Nonempty →
        (dyadicSquareCount (Δ (Fin.succ j)) (setFromIndices δ S'' ∩ dyadicSquare (Δ j.castSucc) a_idx b_idx) : ENNReal) ≥
        ENNReal.ofReal c * (dyadicSquareCount (Δ (Fin.succ j)) (setFromIndices δ S ∩ dyadicSquare (Δ j.castSucc) a_idx b_idx) : ENNReal) := by
      intro a_idx b_idx h_nonempty
      let g : ℤ × ℤ := (a_idx, b_idx)
      let a_fine := a (Fin.succ j)
      let a_coarse := a j.castSucc
      let k := a (Fin.last n)
      have h_k_eq_nδ' : k = nδ := h_k_eq_nδ
      have h_coarse_le_fine : a_coarse ≤ a_fine := (h_a_mono j).le
      have h_fine_le_k : a_fine ≤ k := h_a_last (Fin.succ j)
      let m_fine := k - a_fine
      let m_coarse := a_fine - a_coarse
      let fineSq_S'' := S''.image (parentBy m_fine)
      let filtered_S'' := fineSq_S''.filter (fun idx => parentBy m_coarse idx = g)
      let fineSq_S := S.image (parentBy m_fine)
      let filtered_S := fineSq_S.filter (fun idx => parentBy m_coarse idx = g)
      have h_bridge_S'' := dyadicSquareCount_setFromIndices_inter k a_fine a_coarse h_coarse_le_fine h_fine_le_k S'' g
      have h_bridge_S := dyadicSquareCount_setFromIndices_inter k a_fine a_coarse h_coarse_le_fine h_fine_le_k S g
      have h_fine_eq : dyadicDelta a_fine = Δ (Fin.succ j) := (ha_spec (Fin.succ j)).symm
      have h_coarse_eq : dyadicDelta a_coarse = Δ j.castSucc := (ha_spec j.castSucc).symm
      have h_k_eq2 : dyadicDelta k = δ := by rw [h_k_eq_nδ', hδ_eq]
      have h_count_S'' : dyadicSquareCount (Δ (Fin.succ j)) (setFromIndices δ S'' ∩ dyadicSquare (Δ j.castSucc) a_idx b_idx) = ↑filtered_S''.card := by
        simpa [h_fine_eq, h_coarse_eq, h_k_eq2] using h_bridge_S''
      have h_count_S : dyadicSquareCount (Δ (Fin.succ j)) (setFromIndices δ S ∩ dyadicSquare (Δ j.castSucc) a_idx b_idx) = ↑filtered_S.card := by
        simpa [h_fine_eq, h_coarse_eq, h_k_eq2] using h_bridge_S
      rcases h_nonempty with ⟨x, hx⟩
      have hx_in_S'' : x ∈ setFromIndices δ S'' := hx.1
      have hx_coarse : x ∈ dyadicSquare (Δ j.castSucc) a_idx b_idx := hx.2
      rcases Set.mem_iUnion₂.mp hx_in_S'' with ⟨idx, hidx, hx_square⟩
      have hx_square_k : x ∈ dyadicSquare (dyadicDelta k) idx.1 idx.2 := by
        have hδk : δ = dyadicDelta k := by rw [h_k_eq_nδ', hδ_eq]
        rw [hδk] at hx_square; exact hx_square
      have hx_coarse_k : x ∈ dyadicSquare (dyadicDelta a_coarse) a_idx b_idx := by
        simpa [h_coarse_eq] using hx_coarse
      let p := parentBy m_fine idx
      have hp_in_img : p ∈ fineSq_S'' := Finset.mem_image.mpr ⟨idx, hidx, rfl⟩
      have h_inter : (dyadicSquare (dyadicDelta k) idx.1 idx.2 ∩ dyadicSquare (dyadicDelta a_coarse) a_idx b_idx).Nonempty :=
        ⟨x, hx_square_k, hx_coarse_k⟩
      have h_rewrite : k - (m_fine + m_coarse) = a_coarse := by dsimp only [m_fine, m_coarse]; omega
      have h_le : m_fine + m_coarse ≤ k := by dsimp only [m_fine, m_coarse]; omega
      have h_total : parentBy (m_fine + m_coarse) idx = g := by
        have h_inter' : (dyadicSquare (dyadicDelta k) idx.1 idx.2 ∩ dyadicSquare (dyadicDelta (k - (m_fine + m_coarse))) g.1 g.2).Nonempty := by
          rw [h_rewrite]; exact h_inter
        exact dyadicSquare_inter_parentBy h_le idx g h_inter'
      have hp_filter : parentBy m_coarse p = g := by
        have h_comp : parentBy m_coarse (parentBy m_fine idx) = parentBy (m_fine + m_coarse) idx := by
          have h := parentBy_comp m_coarse m_fine idx
          rw [add_comm m_coarse m_fine] at h; exact h
        exact h_comp.trans h_total
      have h_p_in_filtered : p ∈ filtered_S'' := by
        simp only [filtered_S'', Finset.mem_filter]; exact ⟨hp_in_img, hp_filter⟩
      have hS''_nonzero : filtered_S''.card ≠ 0 := Finset.card_ne_zero.mpr ⟨p, h_p_in_filtered⟩
      have h_sl : (filtered_S''.card : ℝ) ≥ c * (filtered_S.card : ℝ) :=
        single_level_density h_unif_S h_unif_S''_a M hM_pos h_per_level j g hS''_sub_S hS''_nonzero
      rw [h_count_S'', h_count_S]
      have h_enn : (↑filtered_S''.card : ENNReal) ≥ ENNReal.ofReal c * (↑filtered_S.card : ENNReal) := by
        have h1 : (↑filtered_S''.card : ENNReal) = ENNReal.ofReal (filtered_S''.card : ℝ) := by simp
        have h2 : (↑filtered_S.card : ENNReal) = ENNReal.ofReal (filtered_S.card : ℝ) := by simp
        rw [h1, h2]
        have h3 : ENNReal.ofReal (filtered_S''.card : ℝ) ≥ ENNReal.ofReal (c * (filtered_S.card : ℝ)) :=
          ENNReal.ofReal_le_ofReal h_sl
        have h4 : ENNReal.ofReal (c * (filtered_S.card : ℝ)) = ENNReal.ofReal c * ENNReal.ofReal (filtered_S.card : ℝ) := by
          rw [ENNReal.ofReal_mul] <;> positivity
        rw [h4] at h3; exact h3
      exact h_enn
    have h_reg_j : IsRegularBetweenScales (setFromIndices δ S) (Δ (Fin.succ j)) (Δ j.castSucc)
        t_j (C_reg j) (K_reg j) := h_regular j t_j hgood
    have ht_j_nonneg : 0 ≤ t_j := h_reg_j.1.2.2.2.1
    exact uniformisation_regular_transfer hδ_fine_pos hδ_fine_dyadic hδ_coarse_pos hδ_fine_le_coarse
      ht_j_nonneg (hC_reg_pos j) (hK_reg_pos j) hc_pos hP_bounded hP''_bounded2 h_reg_j hsub hdensity_dyadic
  have h_const_set : 9 * C / c = 9 * C * 2 * M * (4 : ℝ)^n := by
    dsimp only [c]
    have hpos : (0 : ℝ) < 2 * M * (4 : ℝ)^n := by positivity
    field_simp [hpos.ne'] <;> ring
  have h_const_reg : ∀ (j : Fin n), 9 * (C_reg j) / c = 9 * (C_reg j) * 2 * M * (4 : ℝ)^n := by
    intro j; dsimp only [c]
    have hpos : (0 : ℝ) < 2 * M * (4 : ℝ)^n := by positivity
    field_simp [hpos.ne'] <;> ring
  have h_final_set : ∀ (j : Fin n),
      IsSetBetweenScales (setFromIndices δ S'') (Δ (Fin.succ j)) (Δ j.castSucc) s
        (9 * C * 2 * M * (4 : ℝ)^n) := by
    intro j
    have h := h_transfer_set j
    exact h
  have h_final_reg : ∀ (j : Fin n) (t_j : ℝ),
      scaleClass j = CombiningTheorem.ScaleClass.good t_j →
        IsRegularBetweenScales (setFromIndices δ S'') (Δ (Fin.succ j)) (Δ j.castSucc)
          t_j
          (max (9 * (C_reg j) * 2 * M * (4 : ℝ)^n) (K_reg j))
          (max (9 * (C_reg j) * 2 * M * (4 : ℝ)^n) (K_reg j)) := by
    intro j t_j hgood
    let C_amp := 9 * (C_reg j) * 2 * M * (4 : ℝ)^n
    let C_both := max C_amp (K_reg j)
    have hC_amp_pos : 0 < C_amp := by
      dsimp only [C_amp]
      exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (hC_reg_pos j)) (by norm_num)) hM_pos) (by positivity)
    have hC_both_pos : 0 < C_both := by positivity
    have h1 : C_amp ≤ C_both := le_max_left _ _
    have h2 : K_reg j ≤ C_both := le_max_right _ _
    have h_transferred : IsRegularBetweenScales (setFromIndices δ S'') (Δ (Fin.succ j)) (Δ j.castSucc)
        t_j C_amp (K_reg j) := by
      have h := h_transfer_reg j t_j hgood
      rw [h_const_reg j] at h
      exact h
    exact CombiningTheoremRework.IsRegularBetweenScales.weaken h_transferred hC_both_pos h1 hC_both_pos h2
  exact ⟨S'', N'', hS''_sub', h_unif_S''_a, h_final_set, h_final_reg⟩

end DiscretisedFurstenbergEstimate.OSUniformisation
