module

/-
  Transfer between-scales properties from a point set to its dyadic thickening.

  Given a set P of representative points (one per dyadic square) and a
  NiceConfiguration whose pointSet is the union of those dyadic squares,
  transfer the multiscale decomposition properties (uniformity, between-scales
  S-set, regularity) from P to config.pointSet.

  This is needed because:
  - The Root multiscale decomposition produces properties for P' (representative points)
  - The combining theorem requires properties for config.pointSet (union of dyadic squares)
  - config.pointSet is a dyadic thickening of P' at scale dyadicDelta k

  The between-scales constants increase by at most thickeningGeomFactor(2) = 900,
  which is accounted for in the absorption hypotheses (base constant 72900 = 900 * 81).

  Whiteprint node: section9 / thickening_transfer
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Root
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.ExactDyadicCount
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.BetweenScalesThickening
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.ThickeningAbsorption
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal


noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate.MultiscaleDecomposition
open DirecretisedFurstenbergEstimate.A10

/-- Weaken the constant in CombiningTheorem.IsSetBetweenScales. -/
lemma IsSetBetweenScales_weaken_constant {P : Set EuclideanPlane} {δ Δ s C C' : ℝ}
    (h : CombiningTheorem.IsSetBetweenScales P δ Δ s C) (hC : C ≤ C') :
    CombiningTheorem.IsSetBetweenScales P δ Δ s C' := by
  rcases h with ⟨hδ_f, hδ_c, hδ_le, hs, hC_pos, hmain⟩
  have hC'_pos : 0 < C' := by linarith
  refine ⟨hδ_f, hδ_c, hδ_le, hs, hC'_pos, ?_⟩
  intro i j hnonempty
  exact LemmaE.IsDeltaSSet.weaken_constant (hmain i j hnonempty) hC

/-- Weaken the K constant in CombiningTheorem.IsRegularBetweenScales. -/
lemma IsRegularBetweenScales_weaken_K {P : Set EuclideanPlane} {δ Δ s C K K' : ℝ}
    (h : CombiningTheorem.IsRegularBetweenScales P δ Δ s C K) (hK : K ≤ K') :
    CombiningTheorem.IsRegularBetweenScales P δ Δ s C K' := by
  rcases h with ⟨hset, hK_pos, hcover⟩
  have hK'_pos : 0 < K' := by linarith
  have hδ_pos : 0 < δ := hset.1
  have hΔ_pos : 0 < Δ := hset.2.1
  have hδ_le : δ ≤ Δ := hset.2.2.1
  have hdiv_nonneg : 0 ≤ δ / Δ := by positivity
  refine ⟨hset, hK'_pos, ?_⟩
  intro i j hnonempty
  have h := hcover i j hnonempty
  have hpos : 0 ≤ Real.rpow (δ / Δ) (-s / 2) := Real.rpow_nonneg hdiv_nonneg _
  have h' : K * Real.rpow (δ / Δ) (-s / 2) ≤ K' * Real.rpow (δ / Δ) (-s / 2) := by
    gcongr
  exact le_trans h (ENNReal.ofReal_le_ofReal h')

/-- Convert MultiscaleDecomposition.IsRegularBetweenScales to CombiningTheorem.IsRegularBetweenScales. -/
lemma regularBetweenScales_msToComb {P : Set EuclideanPlane} {δ Δ s C K : ℝ}
    (h : MultiscaleDecomposition.IsRegularBetweenScales P δ Δ s C K) :
    CombiningTheorem.IsRegularBetweenScales P δ Δ s C K := by
  rcases h with ⟨hset, hK_pos, hcover⟩
  have hsq_eq : ∀ (i j : ℤ), MultiscaleDecomposition.dyadicSquare Δ i j = CombiningTheorem.dyadicSquare Δ i j := by
    intro i j; ext x; simp [MultiscaleDecomposition.dyadicSquare, CombiningTheorem.dyadicSquare] <;> rfl
  have hhom_eq : ∀ (i j : ℤ), MultiscaleDecomposition.homothetyS Δ i j = CombiningTheorem.homothetyS Δ i j := by
    intro i j; funext x; simp [MultiscaleDecomposition.homothetyS, CombiningTheorem.homothetyS] <;> rfl
  have hset' : CombiningTheorem.IsSetBetweenScales P δ Δ s C := by
    rcases hset with ⟨hδ_f, hδ_c, hδ_le, hs, hC_pos, hmain⟩
    refine ⟨hδ_f, hδ_c, hδ_le, hs, hC_pos, ?_⟩
    intro i j hnonempty
    have hne : (P ∩ MultiscaleDecomposition.dyadicSquare Δ i j).Nonempty := by
      rw [hsq_eq i j] at *; exact hnonempty
    have h := hmain i j hne
    rw [hhom_eq i j] at h
    exact h
  refine ⟨hset', hK_pos, ?_⟩
  intro i j hnonempty
  have hne : (P ∩ MultiscaleDecomposition.dyadicSquare Δ i j).Nonempty := by
    rw [hsq_eq i j] at *; exact hnonempty
  have h := hcover i j hne
  rw [hhom_eq i j] at h
  exact h

/-- Weaken exponent in IsDeltaSSet from t to s when s ≤ t and C ≥ 1. -/
lemma IsDeltaSSet_weaken_exponent {X : Type*} [PseudoMetricSpace X]
    {δ s t C : ℝ} {P : Set X}
    (h : IsDeltaSSet δ t C P) (hs : 0 ≤ s) (hst : s ≤ t) (hC : 1 ≤ C) :
    IsDeltaSSet δ s C P := by
  rcases h with ⟨hne, hδ_pos, hC_pos, ht_nonneg, hmain⟩
  refine ⟨hne, hδ_pos, hC_pos, hs, ?_⟩
  intro x r hr
  by_cases h_r1 : r ≤ 1
  · -- Case r ≤ 1: r^t ≤ r^s since s ≤ t and 0 ≤ r ≤ 1
    have h_old := hmain x r hr
    have h_r_pos : 0 < r := lt_of_lt_of_le hδ_pos hr
    have h_real : r ^ t ≤ r ^ s :=
      Real.rpow_le_rpow_of_exponent_ge h_r_pos h_r1 (by linarith)
    have h_ennreal_t : (ENNReal.ofReal r) ^ t = ENNReal.ofReal (r ^ t) :=
      ENNReal.ofReal_rpow_of_pos h_r_pos
    have h_ennreal_s : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) :=
      ENNReal.ofReal_rpow_of_pos h_r_pos
    have h_rpow_le : (ENNReal.ofReal r) ^ t ≤ (ENNReal.ofReal r) ^ s := by
      rw [h_ennreal_t, h_ennreal_s]
      exact ENNReal.ofReal_le_ofReal h_real
    calc _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * _ := h_old
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * _ := by gcongr
  · -- Case r > 1: covering(P ∩ ball) ≤ covering(P) ≤ C * r^s * covering(P)
    have h_r_gt_one : 1 < r := by linarith
    have h_r_pos : 0 < r := by linarith
    have h_sub : (P ∩ Metric.closedBall x r) ⊆ P := by simp
    have h_mono_nat : Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) ≤
        Metric.externalCoveringNumber δ.toNNReal P :=
      Metric.externalCoveringNumber_mono_set h_sub
    have h1 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
        Metric.externalCoveringNumber δ.toNNReal P := by
      exact_mod_cast h_mono_nat
    have h2 : (1 : ENNReal) ≤ ENNReal.ofReal C := by
      have h2' : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC
      simpa using h2'
    have h3 : (1 : ENNReal) ≤ (ENNReal.ofReal r) ^ s := by
      have h4 : (1 : ENNReal) ≤ ENNReal.ofReal r := by
        have h4' : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal (by linarith)
        simpa using h4'
      have h5 : (1 : ENNReal) ^ s ≤ (ENNReal.ofReal r) ^ s := by gcongr <;> linarith
      have h6 : (1 : ENNReal) ^ s = 1 := by simp [hs]
      rw [h6] at h5
      exact h5
    have h_step1 : Metric.externalCoveringNumber δ.toNNReal P ≤
        ENNReal.ofReal C * Metric.externalCoveringNumber δ.toNNReal P := by
      calc Metric.externalCoveringNumber δ.toNNReal P
        = (1 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P := by simp
      _ ≤ ENNReal.ofReal C * Metric.externalCoveringNumber δ.toNNReal P := by gcongr
    have h_step2 : ENNReal.ofReal C * Metric.externalCoveringNumber δ.toNNReal P ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal P := by
      calc ENNReal.ofReal C * Metric.externalCoveringNumber δ.toNNReal P
        = ENNReal.ofReal C * ((1 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P) := by simp
      _ ≤ ENNReal.ofReal C * ((ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal P) := by gcongr
      _ = ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal P := by ring
    exact le_trans h1 (le_trans h_step1 h_step2)

/-- Weaken exponent in IsSetBetweenScales from t to s when s ≤ t and C ≥ 1. -/
lemma IsSetBetweenScales_weaken_exponent {P : Set EuclideanPlane} {δ Δ s t C : ℝ}
    (h : CombiningTheorem.IsSetBetweenScales P δ Δ t C)
    (hs : 0 ≤ s) (hst : s ≤ t) (hC : 1 ≤ C) :
    CombiningTheorem.IsSetBetweenScales P δ Δ s C := by
  rcases h with ⟨hδ_f, hδ_c, hδ_le, ht, hC_pos, hmain⟩
  refine ⟨hδ_f, hδ_c, hδ_le, hs, hC_pos, ?_⟩
  intro i j hnonempty
  exact IsDeltaSSet_weaken_exponent (hmain i j hnonempty) hs hst hC

/-- Transfer multiscale decomposition properties from representative points P
    to the dyadic thickening config.pointSet.

    This is a drop-in replacement for `multiscaleToCombining` where
    `h_point_set : config.pointSet = P` is replaced by the weaker thickening
    hypotheses.

    The absorption hypotheses use base constant 72900 = 900 * 81 to account
    for the thickening factor thickeningGeomFactor(t_j) ≤ 900. -/
lemma multiscaleToCombining_thickened
    {s t τ : ℝ} (hs : 0 < s) (hst : s < t) (ht2 : t ≤ 2) (hτ_pos : 0 < τ)
    {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hΔ_dyadic : Δ ∈ dyadicScales)
    {ε_bad : ℝ} (hε_bad_pos : 0 < ε_bad)
    {m n : ℕ}
    {i : ℕ → ℕ} {t_j : ℕ → ℝ}
    {S B : Finset (Fin n)}
    {P : Set EuclideanPlane} {N : ℕ → ℕ}
    {k M : ℕ} {lam ε_G η ε_N C_P : ℝ}
    (hεG_pos : 0 < ε_G)
    (h_εG_small : ε_G < 2 * (t - s))
    (config : NiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
    -- Scale index properties
    (h_i0 : i 0 = 0)
    (h_in : i n = m)
    (h_i_strict : ∀ j < n, i j < i (j + 1))
    -- t_j range
    (h_tj_range : ∀ j : Fin n, t_j j.val ∈ Set.Icc s 2)
    -- S/B partition
    (h_SB_univ : S ∪ B = Finset.univ)
    (h_SB_disj : Disjoint S B)
    -- Ratio bound for structured scales
    (h_ratio : ∀ j : Fin n, j ∈ S →
      (Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1)) ≥ Real.rpow (Δ ^ m) (-τ))
    -- Bad product bound
    (h_bad_product : ∏ j ∈ B, ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ≤
        Real.rpow (Δ ^ m) (-ε_bad))
    -- Between-scales properties (for P, the representative points)
    (h_set_between : ∀ j : Fin n, j ∈ S →
      CombiningTheorem.IsSetBetweenScales P (Δ ^ i (j.val + 1)) (Δ ^ i j.val) (t_j j.val)
        ((81 : ℝ) * Real.rpow Δ (-4) *
             Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ε_bad))
    (h_regular : ∀ j : Fin n, j ∈ S → t_j j.val > s →
      CombiningTheorem.IsRegularBetweenScales P (Δ ^ i (j.val + 1)) (Δ ^ i j.val) (t_j j.val)
        ((81 : ℝ) * Real.rpow Δ (-4) *
             Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ε_bad)
        ((81 : ℝ) * Real.rpow Δ (-4) *
             Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ε_bad))
    -- Product bound
    (h_product : ∏ j ∈ S, Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) (t_j j.val) ≥
        Real.rpow (Δ ^ m) (ε_bad - t))
    -- No consecutive bad
    (h_no_consec_bad : ∀ j : Fin n, j ∈ B →
      ∀ k : Fin n, k.val = j.val + 1 → k ∉ B)
    -- Uniformity (for P)
    (h_uniform : IsDyadicUniform P m Δ N)
    -- Thickening hypotheses
    (hP_sub : P ⊆ config.pointSet)
    (h_each_square : ∀ q ∈ config.P₀, (q.toSet ∩ P).Nonempty)
    (h_k_m : dyadicDelta k = Δ ^ m)
    -- Constant absorption bounds (post-thickening: 72900 = 900 * 81)
    (h_absorb_normal : ∀ (j : Fin n), j ∈ S → t_j j.val < t - ε_G / 2 →
      (72900 : ℝ) * Real.rpow Δ (-4) *
        ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ^ ε_bad ≤
      Real.log (1 / dyadicDelta k) ^ C_P *
        ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ^ ε_N)
    (h_absorb_good_high : ∀ (j : Fin n), j ∈ S → t_j j.val ≥ t →
      (72900 : ℝ) * Real.rpow Δ (-4) *
        ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ^ ε_bad ≤
      Real.log (1 / dyadicDelta k) ^ C_P *
        ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ^ ε_G)
    (h_absorb_good_low : ∀ (j : Fin n), j ∈ S →
      t - ε_G / 2 ≤ t_j j.val → t_j j.val < t →
      ((72900 : ℝ) * Real.rpow Δ (-4) *
        ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ^ ε_bad) *
        ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ^ (ε_G / 2) ≤
      Real.log (1 / dyadicDelta k) ^ C_P *
        ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ^ ε_G)
    :
    ∃ (C_between : Fin n → ℝ) (scaleClass : Fin n → ScaleClass) (N' : Fin n → ℕ),
      CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config
        (fun j : Fin (n + 1) => Δ ^ i j.val) scaleClass N' ∧
      (∀ (j : Fin n) (t_j' : ℝ), scaleClass j = ScaleClass.good t_j' → t ≤ t_j') ∧
      (∀ (j : Fin n) (t_j' : ℝ), scaleClass j = ScaleClass.good t_j' → t_j' ≤ 2) ∧
      (Finset.univ.filter (fun j : Fin n => (scaleClass j).isGood) =
        S.filter (fun j : Fin n => t_j j.val ≥ t - ε_G / 2)) ∧
      (Finset.univ.filter (fun j : Fin n => (scaleClass j).isBad) = B) := by
  let Q := config.pointSet
  let ratio_j : Fin n → ℝ := fun j =>
    (Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))
  let C0 : Fin n → ℝ := fun j =>
    (81 : ℝ) * Real.rpow Δ (-4) * Real.rpow (ratio_j j) ε_bad
  let C_uniform : Fin n → ℝ := fun j => (900 : ℝ) * C0 j

  have hC_uniform_pos_all : ∀ j : Fin n, 0 < C_uniform j := by
    intro j
    dsimp only [C_uniform, C0]
    have h1 : 0 < Real.rpow Δ (-4) := Real.rpow_pos_of_pos hΔ_pos (-4)
    have h2 : 0 < ratio_j j := by dsimp only [ratio_j] <;> positivity
    have h3 : 0 < ratio_j j ^ ε_bad := Real.rpow_pos_of_pos h2 ε_bad
    have h4 : 0 < (81 : ℝ) * Real.rpow Δ (-4) := mul_pos (by norm_num) h1
    have h5 : 0 < (81 : ℝ) * Real.rpow Δ (-4) * ratio_j j ^ ε_bad := mul_pos h4 h3
    exact mul_pos (by norm_num) h5

  have hΔ_le_one : Δ ≤ 1 := le_of_lt hΔ_lt_one
  have hΔ_nonneg : 0 ≤ Δ := le_of_lt hΔ_pos

  -- ========================================================================
  -- Step 1: Common dyadic base
  -- ========================================================================
  have hΔ_dyadic_copy := hΔ_dyadic
  rcases hΔ_dyadic with ⟨k_dyadic, hk_eq⟩
  let n_dyadic : ℕ := 2 ^ k_dyadic
  have hn_dyadic_pos : 0 < n_dyadic := by positivity
  have hΔ_int : (1 : ℝ) = (n_dyadic : ℝ) * Δ := by
    have h1 : Δ = (2 : ℝ) ^ (-(k_dyadic : ℤ)) := hk_eq
    have h2 : (n_dyadic : ℝ) = (2 : ℝ) ^ (k_dyadic : ℕ) := by
      simp [n_dyadic] <;> norm_cast
    rw [h2, h1]
    have h3 : (2 : ℝ) ^ (k_dyadic : ℕ) * (2 : ℝ) ^ (-(k_dyadic : ℤ)) = 1 := by
      simp [zpow_neg, zpow_ofNat] <;> field_simp <;> ring
    exact h3.symm

  -- ========================================================================
  -- Step 2: Construct hQ_thick
  -- ========================================================================
  have hQ_thick : ∀ y ∈ Q, ∃ (S : Set EuclideanPlane),
      (∃ (a b : ℤ), S = MultiscaleDecomposition.dyadicSquare (Δ ^ m) a b) ∧
      y ∈ S ∧ (P ∩ S).Nonempty := by
    intro y hy
    have hQ_def : Q = ⋃ p ∈ config.P₀, (p.toSet : Set EuclideanPlane) := by rfl
    have h1 : ∃ (q : DyadicSquare k), q ∈ config.P₀ ∧ y ∈ q.toSet := by
      rw [hQ_def] at hy
      simpa [NiceConfiguration.pointSet, Set.mem_iUnion] using hy
    rcases h1 with ⟨q, hqP, hyq⟩
    have h_inter : (P ∩ q.toSet).Nonempty := by
      have h := h_each_square q hqP
      rw [Set.inter_comm] at h
      exact h
    refine ⟨q.toSet, ⟨q.i, q.j, ?_⟩, hyq, h_inter⟩
    have h2 : q.toSet = MultiscaleDecomposition.dyadicSquare (dyadicDelta k) q.i q.j := by
      ext x
      simp only [DyadicSquare.toSet, MultiscaleDecomposition.dyadicSquare, Set.mem_setOf_eq, Set.mem_Ico]
      <;> tauto
    rw [h2, h_k_m]

  -- ========================================================================
  -- Step 3: Transfer uniformity
  -- ========================================================================
  have h_uniform_Q : IsDyadicUniform Q m Δ N :=
    h_uniform.thickening_transfer hP_sub hn_dyadic_pos hΔ_int hQ_thick

  -- ========================================================================
  -- Step 4: Transfer between-scales properties
  -- ========================================================================
  have h_i_mono_strict : ∀ (k l : ℕ), k < l → l ≤ n → i k < i l := by
    intro k l hkl hln
    induction l with
    | zero => exfalso; linarith
    | succ l ih =>
      by_cases h : k < l
      · have h6 : i k < i l := ih h (by linarith)
        have h7 : i l < i (l + 1) := h_i_strict l (by linarith)
        exact lt_trans h6 h7
      · have h' : k = l := by omega
        rw [h']
        exact h_i_strict l (by linarith)
  have h_i_mono : ∀ (k l : ℕ), k ≤ l → l ≤ n → i k ≤ i l := by
    intro k l hkl hln
    by_cases h : k < l
    · exact le_of_lt (h_i_mono_strict k l h hln)
    · have h' : k = l := by omega
      rw [h'] <;> rfl

  have h_set_Q : ∀ (j : Fin n), j ∈ S →
      CombiningTheorem.IsSetBetweenScales Q (Δ ^ i (j.val + 1)) (Δ ^ i j.val) (t_j j.val)
        (thickeningGeomFactor (t_j j.val) * C0 j) := by
    intro j hj
    set a := i (j.val + 1) with ha_def
    set b := i j.val with hb_def
    have hba : b ≤ a := by
      simp [ha_def, hb_def] <;> exact le_of_lt (h_i_strict j.val j.is_lt)
    have ham : a ≤ m := by
      have h4 : j.val + 1 ≤ n := by omega
      have h5 : i (j.val + 1) ≤ i n := h_i_mono (j.val + 1) n (by omega) (by linarith)
      rw [h_in] at h5 <;> exact h5
    exact MultiscaleDecomposition.IsSetBetweenScales.thickening_transfer
      (h_set_between j hj) hP_sub hn_dyadic_pos hΔ_int hΔ_lt_one rfl rfl hba ham hQ_thick

  have h_regular_Q : ∀ (j : Fin n), j ∈ S → t_j j.val > s →
      CombiningTheorem.IsRegularBetweenScales Q (Δ ^ i (j.val + 1)) (Δ ^ i j.val) (t_j j.val)
        (thickeningGeomFactor (t_j j.val) * C0 j) ((100 : ℝ) * C0 j) := by
    intro j hj htj
    set a := i (j.val + 1) with ha_def
    set b := i j.val with hb_def
    have hba : b ≤ a := by
      simp [ha_def, hb_def] <;> exact le_of_lt (h_i_strict j.val j.is_lt)
    have ham : a ≤ m := by
      have h4 : j.val + 1 ≤ n := by omega
      have h5 : i (j.val + 1) ≤ i n := h_i_mono (j.val + 1) n (by omega) (by linarith)
      rw [h_in] at h5 <;> exact h5
    have h_ms : MultiscaleDecomposition.IsRegularBetweenScales Q (Δ ^ i (j.val + 1)) (Δ ^ i j.val) (t_j j.val)
        (thickeningGeomFactor (t_j j.val) * C0 j) ((2 * (2 + 1) + 4) ^ 2 * C0 j) :=
      MultiscaleDecomposition.IsRegularBetweenScales.thickening_transfer
        (h_regular j hj htj) hP_sub hn_dyadic_pos hΔ_int hΔ_lt_one rfl rfl hba ham hQ_thick
    have h_comb : CombiningTheorem.IsRegularBetweenScales Q (Δ ^ i (j.val + 1)) (Δ ^ i j.val) (t_j j.val)
        (thickeningGeomFactor (t_j j.val) * C0 j) ((2 * (2 + 1) + 4) ^ 2 * C0 j) :=
      regularBetweenScales_msToComb h_ms
    have hK_eq : (2 * (2 + 1) + 4) ^ 2 * C0 j = (100 : ℝ) * C0 j := by
      have h : (2 * (2 + 1) + 4) ^ 2 = (100 : ℝ) := by norm_num
      rw [h] <;> ring
    rw [hK_eq] at h_comb
    exact h_comb

  -- ========================================================================
  -- Step 5: Weaken to uniform constant 900 * C0
  -- ========================================================================
  have h_tj_le_two : ∀ j : Fin n, t_j j.val ≤ 2 := by
    intro j
    have h := h_tj_range j
    exact h.2

  have h_factor_le : ∀ j : Fin n, thickeningGeomFactor (t_j j.val) ≤ (900 : ℝ) := by
    intro j
    have h1 : t_j j.val ≤ 2 := h_tj_le_two j
    have h2 : 0 ≤ t_j j.val := by
      have h21 : s ≤ t_j j.val := (h_tj_range j).1
      linarith [hs]
    dsimp only [thickeningGeomFactor]
    have h_geom : (2 * (2 + 1) + 4) ^ 2 * (1 + 2) ^ (t_j j.val) = (100 : ℝ) * (3 : ℝ) ^ (t_j j.val) := by
      have h1 : (2 * (2 + 1) + 4) ^ 2 = (100 : ℝ) := by norm_num
      have h2 : (1 + 2 : ℝ) = (3 : ℝ) := by norm_num
      rw [h1, h2] <;> ring
    rw [h_geom]
    have h3 : (3 : ℝ) ^ (t_j j.val) ≤ (3 : ℝ) ^ (2 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      <;> norm_num <;> linarith
    have h4 : (100 : ℝ) * (3 : ℝ) ^ (t_j j.val) ≤ (100 : ℝ) * (3 : ℝ) ^ (2 : ℝ) := by
      gcongr
    have h5 : (100 : ℝ) * (3 : ℝ) ^ (2 : ℝ) = (900 : ℝ) := by norm_num
    rw [h5] at h4
    exact h4

  have h_set_uniform : ∀ (j : Fin n), j ∈ S →
      CombiningTheorem.IsSetBetweenScales Q (Δ ^ i (j.val + 1)) (Δ ^ i j.val) (t_j j.val) (C_uniform j) := by
    intro j hj
    have hC0_pos : 0 < C0 j := by
      have h : 0 < C_uniform j := hC_uniform_pos_all j
      dsimp only [C_uniform] at h
      have h' : (900 : ℝ) * C0 j > 0 := h
      linarith
    have h1 : thickeningGeomFactor (t_j j.val) * C0 j ≤ C_uniform j := by
      dsimp only [C_uniform]
      have h3 : thickeningGeomFactor (t_j j.val) ≤ (900 : ℝ) := h_factor_le j
      nlinarith
    exact IsSetBetweenScales_weaken_constant (h_set_Q j hj) h1

  have h_regular_uniform : ∀ (j : Fin n), j ∈ S → t_j j.val > s →
      CombiningTheorem.IsRegularBetweenScales Q (Δ ^ i (j.val + 1)) (Δ ^ i j.val) (t_j j.val)
        (C_uniform j) (C_uniform j) := by
    intro j hj htj
    have hreg := h_regular_Q j hj htj
    have hC0_pos : 0 < C0 j := by
      have h : 0 < C_uniform j := hC_uniform_pos_all j
      dsimp only [C_uniform] at h
      have h' : (900 : ℝ) * C0 j > 0 := h
      linarith
    have hC : thickeningGeomFactor (t_j j.val) * C0 j ≤ C_uniform j := by
      dsimp only [C_uniform]
      have h3 : thickeningGeomFactor (t_j j.val) ≤ (900 : ℝ) := h_factor_le j
      nlinarith
    have hK : (100 : ℝ) * C0 j ≤ C_uniform j := by
      dsimp only [C_uniform]
      nlinarith
    rcases hreg with ⟨hset, hK_pos, hcover⟩
    have hset' := IsSetBetweenScales_weaken_constant hset hC
    have hC_uniform_pos : 0 < C_uniform j := hC_uniform_pos_all j
    refine ⟨hset', hC_uniform_pos, ?_⟩
    intro i' j' hnonempty
    have h4 := hcover i' j' hnonempty
    set δ_ratio := (Δ ^ i (j.val + 1)) / (Δ ^ i j.val) with hδr_def
    have hδr_pos2 : 0 ≤ δ_ratio := by
      dsimp only [δ_ratio]
      positivity
    have h7 : 0 ≤ Real.rpow δ_ratio (-(t_j j.val) / 2) :=
      Real.rpow_nonneg hδr_pos2 _
    have h6 : (100 : ℝ) * C0 j * Real.rpow δ_ratio (-(t_j j.val) / 2) ≤
        C_uniform j * Real.rpow δ_ratio (-(t_j j.val) / 2) := by
      nlinarith
    exact le_trans h4 (ENNReal.ofReal_le_ofReal h6)

  -- ========================================================================
  -- Step 6: Define scale classification, C_between, N', Δ'
  -- ========================================================================
  have h_threshold_pos : s < t - ε_G / 2 := by linarith

  let C_between : Fin n → ℝ := fun j =>
    if h : j ∈ S ∧ t_j j.val ≥ t - ε_G / 2 ∧ t_j j.val < t then
      C_uniform j * ratio_j j ^ (ε_G / 2)
    else
      C_uniform j

  let scaleClass : Fin n → ScaleClass := fun j =>
    if h : j ∈ S then
      if h2 : t_j j.val ≥ t - ε_G / 2 then
        if t_j j.val ≥ t then ScaleClass.good (t_j j.val)
        else ScaleClass.good t
      else ScaleClass.normal
    else ScaleClass.bad

  let N' : Fin n → ℕ := fun j =>
    ∏ l ∈ Finset.Ico (i j.val) (i (j.val + 1)), N l

  let Δ' : Fin (n + 1) → ℝ := fun j => Δ ^ i j.val

  -- Helper lemmas for scaleClass simplification
  have h_scale_bad : ∀ (j : Fin n), j ∉ S → scaleClass j = ScaleClass.bad := by
    intro j h
    dsimp only [scaleClass]
    rw [dif_neg h]

  have h_scale_good_high : ∀ (j : Fin n), j ∈ S → t_j j.val ≥ t →
      scaleClass j = ScaleClass.good (t_j j.val) := by
    intro j hS h_high
    dsimp only [scaleClass]
    rw [dif_pos hS]
    have h2 : t_j j.val ≥ t - ε_G / 2 := by linarith
    rw [dif_pos h2]
    rw [if_pos h_high]

  have h_scale_good_low : ∀ (j : Fin n), j ∈ S →
      t_j j.val ≥ t - ε_G / 2 → t_j j.val < t → scaleClass j = ScaleClass.good t := by
    intro j hS h_low h_high
    dsimp only [scaleClass]
    rw [dif_pos hS]
    rw [dif_pos h_low]
    have h_ge : ¬(t_j j.val ≥ t) := by linarith
    rw [if_neg h_ge]

  have h_scale_normal : ∀ (j : Fin n), j ∈ S → t_j j.val < t - ε_G / 2 →
      scaleClass j = ScaleClass.normal := by
    intro j hS h_low
    dsimp only [scaleClass]
    rw [dif_pos hS]
    have h2 : ¬(t_j j.val ≥ t - ε_G / 2) := by linarith
    rw [dif_neg h2]

  have h_C_uniform_eq : ∀ (j : Fin n),
      C_uniform j = (72900 : ℝ) * Real.rpow Δ (-4) * ratio_j j ^ ε_bad := by
    intro j
    have h1 : C_uniform j = (900 : ℝ) * C0 j := by rfl
    have h2 : C0 j = (81 : ℝ) * Real.rpow Δ (-4) * ratio_j j ^ ε_bad := by rfl
    rw [h1, h2]
    <;> ring

  have h_C_uniform : ∀ (j : Fin n),
      ¬(j ∈ S ∧ t_j j.val ≥ t - ε_G / 2 ∧ t_j j.val < t) → C_between j = C_uniform j := by
    intro j h
    dsimp only [C_between]
    rw [dif_neg h]

  have h_C_boosted : ∀ (j : Fin n),
      (j ∈ S ∧ t_j j.val ≥ t - ε_G / 2 ∧ t_j j.val < t) →
        C_between j = C_uniform j * ratio_j j ^ (ε_G / 2) := by
    intro j h
    dsimp only [C_between]
    rw [dif_pos h]

  -- ========================================================================
  -- Step 7: Prove CombiningConfig fields
  -- ========================================================================

  -- hM_pos from config
  have hP_nonempty : P.Nonempty := h_uniform.2.2.1
  have hQ_nonempty : Q.Nonempty := hP_nonempty.mono hP_sub
  have hP₀_nonempty : config.P₀.Nonempty := by
    by_contra h
    have h' : config.P₀ = ∅ := by simpa using h
    have h_empty : Q = ∅ := by
      simp [NiceConfiguration.pointSet, h', Q] <;> rfl
    rw [h_empty] at hQ_nonempty
    simp at hQ_nonempty
  have hM_pos : 0 < M := by
    rcases hP₀_nonempty with ⟨p, hp⟩
    have h_ds : IsDeltaSSet (dyadicDelta k) s (Real.rpow (dyadicDelta k) (-lam))
        (config.tubeFamily p hp : Set (DyadicTube k)) := config.h_delta_s_set p hp
    have h_tube_nonempty : (config.tubeFamily p hp : Set (DyadicTube k)).Nonempty := h_ds.1
    have h_finset_nonempty : (config.tubeFamily p hp).Nonempty := by
      simpa [Finset.Nonempty] using h_tube_nonempty
    have h_card_pos : 0 < (config.tubeFamily p hp).card := Finset.Nonempty.card_pos h_finset_nonempty
    have h_size_eq : (config.tubeFamily p hp).card = M := config.h_size p hp
    rw [h_size_eq] at h_card_pos
    exact h_card_pos

  -- Scale properties
  have hΔ_strict : ∀ j : Fin n, Δ' (Fin.succ j) < Δ' j.castSucc := by
    intro j
    have h1 : i (j.val + 1) > i j.val := h_i_strict j.val j.is_lt
    have h2 : Δ ^ i (j.val + 1) < Δ ^ i j.val := by
      exact pow_lt_pow_right_of_lt_one₀ hΔ_pos hΔ_lt_one h1
    simpa [Δ'] using h2

  have hΔ_end : Δ' (Fin.last n) = dyadicDelta k := by
    have h1 : Δ' (Fin.last n) = Δ ^ i n := by simp [Δ']
    rw [h1, h_in]
    exact h_k_m.symm

  have hΔ_start : Δ' 0 = 1 := by
    have h1 : Δ' 0 = Δ ^ i 0 := by simp [Δ']
    rw [h1, h_i0] <;> simp

  have hΔ_pos' : ∀ j : Fin (n + 1), 0 < Δ' j := by
    intro j; positivity

  have hΔ_dyadic' : ∀ j : Fin (n + 1), Δ' j ∈ dyadicScales := by
    intro j
    rcases hΔ_dyadic_copy with ⟨k_exp, hk_eq2⟩
    have h_goal : Δ' j = (2 : ℝ) ^ (-(k_exp * i j.val : ℤ)) := by
      have h1 : Δ' j = Δ ^ i j.val := by simp [Δ']
      rw [h1, hk_eq2]
      simp [zpow_mul, zpow_ofNat] <;> ring
    exact ⟨k_exp * i j.val, h_goal⟩

  have h_scale_ratio : ∀ j : Fin n, ¬(scaleClass j).isBad →
      Δ' (Fin.succ j) / Δ' j.castSucc ≤ Real.rpow (dyadicDelta k) τ := by
    intro j h_not_bad
    have h_j_in_S : j ∈ S := by
      by_cases h : j ∈ S
      · exact h
      · have h_j_in_B : j ∈ B := by
          have h1 : j ∈ S ∪ B := by
            rw [h_SB_univ] <;> exact Finset.mem_univ j
          exact (Finset.mem_union.mp h1).resolve_left h
        have h_bad : scaleClass j = ScaleClass.bad := by
          dsimp only [scaleClass]
          rw [dif_neg h]
        rw [h_bad] at h_not_bad
        exact False.elim (h_not_bad rfl)
    set a := (Δ ^ i j.val : ℝ) with ha_def
    set b := (Δ ^ i (j.val + 1) : ℝ) with hb_def
    set c := (Δ ^ m : ℝ) with hc_def
    have h_pos1 : 0 < a := by positivity
    have h_pos2 : 0 < b := by positivity
    have h_pos3 : 0 < c := by positivity
    have h_cτ : 0 < Real.rpow c τ := Real.rpow_pos_of_pos h_pos3 _
    have h_neg_rpow : Real.rpow c (-τ) = (Real.rpow c τ)⁻¹ := by
      exact Real.rpow_neg h_pos3.le τ
    have h_main : a / b ≥ Real.rpow c (-τ) := h_ratio j h_j_in_S
    have h1 : a / b ≥ (Real.rpow c τ)⁻¹ := by
      rw [h_neg_rpow] at h_main; exact h_main
    have h_ba_eq : b / a = (a / b)⁻¹ := by
      field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
    have h_inv : b / a ≤ Real.rpow c τ := by
      rw [h_ba_eq]
      have h3 : (a / b)⁻¹ ≤ ((Real.rpow c τ)⁻¹)⁻¹ := by gcongr
      have h4 : ((Real.rpow c τ)⁻¹)⁻¹ = Real.rpow c τ := by
        field_simp [h_cτ.ne'] <;> ring
      rw [h4] at h3
      exact h3
    have h_k : c = dyadicDelta k := h_k_m.symm
    rw [h_k] at h_inv
    simpa [Δ', ha_def, hb_def] using h_inv

  -- Uniformity bridge: IsDyadicUniform Q → IsUniformAtScales Q
  have hN_pos : ∀ i < m, N i ≥ 1 := h_uniform_Q.2.2.2.1

  have h_strict_mono : ∀ (k l : ℕ), k < l → l ≤ n → i k < i l := h_i_mono_strict


  have h2 : ∀ j : Fin n, 1 ≤ N' j := by
    intro j
    have h_strict : i j.val < i (j.val + 1) := h_i_strict j.val j.is_lt
    have h_ico_nonempty : (Finset.Ico (i j.val) (i (j.val + 1))).Nonempty :=
      ⟨i j.val, Finset.mem_Ico.mpr ⟨by linarith, h_strict⟩⟩
    have h_last_le_m : i (j.val + 1) ≤ m := by
      have h4 : j.val + 1 ≤ n := by omega
      have h5 : i (j.val + 1) ≤ i n := h_i_mono (j.val + 1) n (by omega) (by linarith)
      rw [h_in] at h5 <;> exact h5
    have h_all_pos : ∀ l ∈ Finset.Ico (i j.val) (i (j.val + 1)), 1 ≤ N l := by
      intro l hl
      have h_lt_last : l < i (j.val + 1) := (Finset.mem_Ico.mp hl).2
      have h_lt_m : l < m := lt_of_lt_of_le h_lt_last h_last_le_m
      exact hN_pos l h_lt_m
    exact Finset.one_le_prod h_all_pos

  have h_square_eq : ∀ (δ : ℝ) (a b : ℤ),
      CombiningTheorem.dyadicSquare δ a b = MultiscaleDecomposition.dyadicSquare δ a b := by
    intro δ a b
    ext x
    simp [CombiningTheorem.dyadicSquare, MultiscaleDecomposition.dyadicSquare] <;> rfl

  have h_count_eq : ∀ (δ : ℝ) (A : Set EuclideanPlane),
      CombiningTheorem.dyadicSquareCount δ A = MultiscaleDecomposition.dyadicSquareCount δ A := by
    intro δ A
    simp [CombiningTheorem.dyadicSquareCount, MultiscaleDecomposition.dyadicSquareCount, h_square_eq] <;> rfl

  have h_uniform_at_scales : IsUniformAtScales Q n Δ' N' := by
    refine ⟨hQ_nonempty, h2, ?_⟩
    intro j a b
    let coarse_square := MultiscaleDecomposition.dyadicSquare (Δ ^ i j.val) a b
    let Q_inter := Q ∩ coarse_square
    by_cases hQ : Q_inter.Nonempty
    · have h_last_le_m : i (j.val + 1) ≤ m := by
        have h4 : j.val + 1 ≤ n := by omega
        have h5 : i (j.val + 1) ≤ i n := h_i_mono (j.val + 1) n (by omega) (by linarith)
        rw [h_in] at h5 <;> exact h5
      have h_count_mult : MultiscaleDecomposition.dyadicSquareCount (Δ ^ i (j.val + 1)) Q_inter = ↑(N' j) := by
        exact dyadicSquareCount_multilevel h_uniform_Q hn_dyadic_pos hΔ_int
          (le_of_lt (h_i_strict j.val j.is_lt)) h_last_le_m a b hQ
      have h_set_eq : Q ∩ CombiningTheorem.dyadicSquare (Δ ^ i j.val) a b = Q_inter := by
        have h2 : CombiningTheorem.dyadicSquare (Δ ^ i j.val) a b = coarse_square :=
          h_square_eq (Δ ^ i j.val) a b
        rw [h2] <;> rfl
      have h_main : CombiningTheorem.dyadicSquareCount (Δ ^ i (j.val + 1))
          (Q ∩ CombiningTheorem.dyadicSquare (Δ ^ i j.val) a b) = ↑(N' j) := by
        rw [h_set_eq]
        rw [h_count_eq (Δ ^ i (j.val + 1)) Q_inter, h_count_mult]
      have h_main' : CombiningTheorem.dyadicSquareCount (Δ' (Fin.succ j))
          (Q ∩ CombiningTheorem.dyadicSquare (Δ' j.castSucc) a b) = ↑(N' j) := by
        have h_eq1 : Δ' (Fin.succ j) = Δ ^ i (j.val + 1) := by simp [Δ']
        have h_eq2 : Δ' j.castSucc = Δ ^ i j.val := by simp [Δ']
        rw [h_eq1, h_eq2]
        exact h_main
      rw [h_main']
      have hN'_pos : 1 ≤ N' j := h2 j
      exact Or.inr ⟨by rfl, by exact_mod_cast (show N' j < 2 * N' j from by omega)⟩
    · have h_empty : Q_inter = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using hQ
      have h_set_eq : Q ∩ CombiningTheorem.dyadicSquare (Δ ^ i j.val) a b = ∅ := by
        have h2 : CombiningTheorem.dyadicSquare (Δ ^ i j.val) a b = coarse_square :=
          h_square_eq (Δ ^ i j.val) a b
        rw [h2]
        simpa [Q_inter] using h_empty
      have h_count_zero : CombiningTheorem.dyadicSquareCount (Δ ^ i (j.val + 1))
          (Q ∩ CombiningTheorem.dyadicSquare (Δ ^ i j.val) a b) = 0 := by
        rw [h_set_eq]
        rw [h_count_eq]
        simp [MultiscaleDecomposition.dyadicSquareCount]
        <;> rfl
      have h_main' : CombiningTheorem.dyadicSquareCount (Δ' (Fin.succ j))
          (Q ∩ CombiningTheorem.dyadicSquare (Δ' j.castSucc) a b) = 0 := by
        have h_eq1 : Δ' (Fin.succ j) = Δ ^ i (j.val + 1) := by simp [Δ']
        have h_eq2 : Δ' j.castSucc = Δ ^ i j.val := by simp [Δ']
        rw [h_eq1, h_eq2]
        exact h_count_zero
      rw [h_main']
      exact Or.inl rfl

  -- ========================================================================
  -- Step 8: Normal and good scale properties
  -- ========================================================================

  -- Helper: exponent weakening for IsSetBetweenScales
  have h_exp_weaken : ∀ (j : Fin n), j ∈ S →
      t_j j.val ≥ t - ε_G / 2 → t_j j.val < t →
      CombiningTheorem.IsSetBetweenScales Q (Δ ^ i (j.val + 1)) (Δ ^ i j.val) t
        (C_uniform j * ratio_j j ^ (ε_G / 2)) := by
    intro j hj hlow hhigh
    have hreg := h_set_uniform j hj
    rcases hreg with ⟨hδ_f_pos, hδ_c_pos, hδ_f_le_c, hs', hC_pos, hmain⟩
    set δ_ratio := (Δ ^ i (j.val + 1)) / (Δ ^ i j.val) with hδr_def
    have hδr_pos : 0 < δ_ratio := by positivity
    have hratio_ge_one : 1 ≤ ratio_j j := by
      dsimp only [ratio_j]
      have h1 : i j.val ≤ i (j.val + 1) := le_of_lt (h_i_strict j.val j.is_lt)
      have h2 : Δ ^ i (j.val + 1) ≤ Δ ^ i j.val :=
        pow_le_pow_of_le_one hΔ_nonneg hΔ_le_one h1
      have h3 : 0 < Δ ^ i j.val := by positivity
      have h4 : (Δ ^ i (j.val + 1)) / (Δ ^ i j.val) ≤ 1 := by
        rw [div_le_one h3] <;> exact h2
      have h5 : 1 ≤ ratio_j j := by
        dsimp only [ratio_j]
        have h6 : 0 < Δ ^ i (j.val + 1) := by positivity
        rw [one_le_div h6]
        exact h2
      exact h5
    have hdiff : t - t_j j.val ≤ ε_G / 2 := by linarith
    have hC_pos' : 0 < C_uniform j * ratio_j j ^ (ε_G / 2) := by positivity
    refine ⟨hδ_f_pos, hδ_c_pos, hδ_f_le_c, by linarith, hC_pos', ?_⟩
    intro a b hnonempty
    have hA_sset := hmain a b hnonempty
    have h_old : IsDeltaSSet δ_ratio (t_j j.val) (C_uniform j)
        (MultiscaleDecomposition.homothetyS (Δ ^ i j.val) a b '' (Q ∩ MultiscaleDecomposition.dyadicSquare (Δ ^ i j.val) a b)) := hA_sset
    rcases h_old with ⟨hP_nonempty, hδ_pos, hC_old_pos, hs_old, hmain_old⟩
    refine ⟨hP_nonempty, hδ_pos, hC_pos', by linarith, ?_⟩
    intro x r hr
    have h_bound_old := hmain_old x r hr
    have hr_geδ : δ_ratio ≤ r := hr
    have hpos_r : 0 < r := by linarith
    have h9 : r ^ (t_j j.val - t) ≤ ratio_j j ^ (ε_G / 2) := by
      set y := t - t_j j.val with hy_def
      have hy_nonneg : 0 ≤ y := by linarith
      have h1 : δ_ratio ^ y ≤ r ^ y := by gcongr <;> linarith
      have h11 : r ^ (t_j j.val - t) ≤ δ_ratio ^ (t_j j.val - t) := by
        have h2 : r ^ (t_j j.val - t) = (r ^ y)⁻¹ := by
          have h3 : t_j j.val - t = -y := by linarith
          rw [h3, Real.rpow_neg hpos_r.le] <;> ring
        have h4 : δ_ratio ^ (t_j j.val - t) = (δ_ratio ^ y)⁻¹ := by
          have h5 : t_j j.val - t = -y := by linarith
          rw [h5, Real.rpow_neg hδr_pos.le] <;> ring
        rw [h2, h4]
        have hpos1 : 0 < δ_ratio ^ y := by positivity
        have hpos2 : 0 < r ^ y := by positivity
        gcongr
      have h12 : δ_ratio = (ratio_j j)⁻¹ := by
        dsimp only [ratio_j, δ_ratio]
        field_simp
        <;> ring
      rw [h12] at h11
      have h13 : (ratio_j j)⁻¹ ^ (t_j j.val - t) = ratio_j j ^ (t - t_j j.val) := by
        have hpos_ratio : 0 < ratio_j j := by positivity
        have h_neg : t_j j.val - t = -(t - t_j j.val) := by linarith
        rw [h_neg]
        have h1 : (ratio_j j)⁻¹ ^ (-(t - t_j j.val)) = ((ratio_j j)⁻¹ ^ (t - t_j j.val))⁻¹ := by
          rw [Real.rpow_neg (by positivity)] <;> ring
        rw [h1]
        have h2 : (ratio_j j)⁻¹ ^ (t - t_j j.val) = (ratio_j j ^ (t - t_j j.val))⁻¹ := by
          have h3 : (ratio_j j)⁻¹ = ratio_j j ^ (-1 : ℝ) := by
            rw [Real.rpow_neg hpos_ratio.le] <;> simp
          rw [h3]
          have h4 : (ratio_j j ^ (-1 : ℝ)) ^ (t - t_j j.val) =
              ratio_j j ^ ((-1 : ℝ) * (t - t_j j.val)) := by
            rw [Real.rpow_mul hpos_ratio.le]
          rw [h4]
          have h5 : (-1 : ℝ) * (t - t_j j.val) = -(t - t_j j.val) := by ring
          rw [h5, Real.rpow_neg hpos_ratio.le]
        rw [h2]
        have h4 : ((ratio_j j ^ (t - t_j j.val))⁻¹)⁻¹ = ratio_j j ^ (t - t_j j.val) := by
          apply inv_inv
        rw [h4]
      rw [h13] at h11
      have h14 : ratio_j j ^ (t - t_j j.val) ≤ ratio_j j ^ (ε_G / 2) := by
        gcongr <;> linarith
      exact le_trans h11 h14
    have h10 : r ^ (t_j j.val) = r ^ t * r ^ (t_j j.val - t) := by
      rw [← Real.rpow_add hpos_r] <;> ring_nf
    have h15 : (C_uniform j) * r ^ (t_j j.val) ≤
        (C_uniform j * ratio_j j ^ (ε_G / 2)) * r ^ t := by
      rw [h10]
      have h18 : C_uniform j * (r ^ t * r ^ (t_j j.val - t)) ≤
          C_uniform j * (r ^ t * ratio_j j ^ (ε_G / 2)) := by
        gcongr
        <;> linarith
      have h19 : C_uniform j * (r ^ t * ratio_j j ^ (ε_G / 2)) =
          (C_uniform j * ratio_j j ^ (ε_G / 2)) * r ^ t := by ring
      have h_goal : C_uniform j * (r ^ t * r ^ (t_j j.val - t)) ≤
          (C_uniform j * ratio_j j ^ (ε_G / 2)) * r ^ t := by
        calc C_uniform j * (r ^ t * r ^ (t_j j.val - t))
          ≤ C_uniform j * (r ^ t * ratio_j j ^ (ε_G / 2)) := h18
        _ = (C_uniform j * ratio_j j ^ (ε_G / 2)) * r ^ t := by ring
      exact h_goal
    have h20 : ENNReal.ofReal (C_uniform j) * (ENNReal.ofReal r) ^ (t_j j.val) =
        ENNReal.ofReal (C_uniform j * r ^ (t_j j.val)) := by
      have h20a : (ENNReal.ofReal r) ^ (t_j j.val) = ENNReal.ofReal (r ^ (t_j j.val)) :=
        ENNReal.ofReal_rpow_of_pos hpos_r
      rw [h20a, ENNReal.ofReal_mul (show 0 ≤ C_uniform j from by linarith [hC_uniform_pos_all j])]
    have h21 : ENNReal.ofReal ((C_uniform j * ratio_j j ^ (ε_G / 2)) * r ^ t) =
        ENNReal.ofReal (C_uniform j * ratio_j j ^ (ε_G / 2)) * (ENNReal.ofReal r) ^ t := by
      have h21a : (ENNReal.ofReal r) ^ t = ENNReal.ofReal (r ^ t) :=
        ENNReal.ofReal_rpow_of_pos hpos_r
      rw [h21a, ENNReal.ofReal_mul (show 0 ≤ C_uniform j * ratio_j j ^ (ε_G / 2) from by
        have hpos1 : 0 < C_uniform j := hC_uniform_pos_all j
        have hpos2 : 0 < ratio_j j ^ (ε_G / 2) := Real.rpow_pos_of_pos (by positivity) _
        positivity)]
    calc _ ≤ ENNReal.ofReal (C_uniform j) * (ENNReal.ofReal r) ^ (t_j j.val) * _ := h_bound_old
      _ = ENNReal.ofReal (C_uniform j * r ^ (t_j j.val)) * _ := by rw [h20]
      _ ≤ ENNReal.ofReal ((C_uniform j * ratio_j j ^ (ε_G / 2)) * r ^ t) * _ := by
        gcongr <;> exact ENNReal.ofReal_le_ofReal h15
      _ = ENNReal.ofReal (C_uniform j * ratio_j j ^ (ε_G / 2)) * (ENNReal.ofReal r) ^ t *
          (Metric.externalCoveringNumber δ_ratio.toNNReal
             (MultiscaleDecomposition.homothetyS (Δ ^ i j.val) a b ''
               (Q ∩ MultiscaleDecomposition.dyadicSquare (Δ ^ i j.val) a b)) : ENNReal) := by
        rw [h21]

  -- Normal scales
  have h_normal : ∀ (j : Fin n), scaleClass j = ScaleClass.normal →
      CombiningTheorem.IsSetBetweenScales Q (Δ' (Fin.succ j)) (Δ' j.castSucc) s (C_between j) := by
    intro j hj
    have h_j_in_S : j ∈ S := by
      by_cases h : j ∈ S
      · exact h
      · have h_bad : scaleClass j = ScaleClass.bad := by
          dsimp only [scaleClass]
          rw [dif_neg h]
        rw [h_bad] at hj
        cases hj
    have h_tj_low : t_j j.val < t - ε_G / 2 := by
      by_cases h : t_j j.val ≥ t - ε_G / 2
      · have h2 : scaleClass j ≠ ScaleClass.normal := by
          have h_sc : scaleClass j = ScaleClass.good (if t_j j.val ≥ t then t_j j.val else t) := by
            dsimp only [scaleClass]
            rw [dif_pos h_j_in_S]
            rw [dif_pos h]
            by_cases h_ge : t_j j.val ≥ t
            · rw [if_pos h_ge, if_pos h_ge] <;> rfl
            · rw [if_neg h_ge, if_neg h_ge] <;> rfl
          rw [h_sc]
          intro h3
          cases h3
        exact False.elim (h2 hj)
      · linarith
    have h_C_eq : C_between j = C_uniform j := by
      have h_false : ¬(j ∈ S ∧ t_j j.val ≥ t - ε_G / 2 ∧ t_j j.val < t) := by
        intro h_cont
        have h_ge : t_j j.val ≥ t - ε_G / 2 := h_cont.2.1
        exact not_lt.mpr h_ge h_tj_low
      exact dif_neg h_false
    rw [h_C_eq]
    have h_tj_ge_s : s ≤ t_j j.val := (h_tj_range j).1
    have hC_pos : 0 < C_uniform j := hC_uniform_pos_all j
    have hC_ge_one : 1 ≤ C_uniform j := by
      dsimp only [C_uniform, C0]
      have h1 : 1 ≤ Real.rpow Δ (-4) := by
        have h11 : 0 < Δ := hΔ_pos
        have h12 : Δ ≤ 1 := le_of_lt hΔ_lt_one
        exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos h11 h12 (by norm_num)
      have h2 : 1 ≤ ratio_j j ^ ε_bad := by
        have h3 : 1 ≤ ratio_j j := by
          dsimp only [ratio_j]
          have h4 : i j.val ≤ i (j.val + 1) := le_of_lt (h_i_strict j.val j.is_lt)
          have h5 : Δ ^ i (j.val + 1) ≤ Δ ^ i j.val := pow_le_pow_of_le_one hΔ_nonneg hΔ_le_one h4
          have h6 : 0 < Δ ^ i (j.val + 1) := by positivity
          rw [one_le_div h6] <;> exact h5
        have h4 : 0 ≤ ε_bad := by linarith [hε_bad_pos]
        exact Real.one_le_rpow h3 h4
      have h_pos1 : 0 < Real.rpow Δ (-4) := by positivity
      have h_pos2 : 0 < ratio_j j ^ ε_bad := by positivity
      have h7 : 1 ≤ (81 : ℝ) * Real.rpow Δ (-4) := by
        have h8 : (81 : ℝ) * Real.rpow Δ (-4) ≥ (81 : ℝ) * 1 := by gcongr
        have h9 : (81 : ℝ) * 1 = (81 : ℝ) := by ring
        rw [h9] at h8
        linarith
      have h10 : 1 ≤ (81 : ℝ) * Real.rpow Δ (-4) * ratio_j j ^ ε_bad := by
        have h11 : (81 : ℝ) * Real.rpow Δ (-4) * ratio_j j ^ ε_bad ≥
            (81 : ℝ) * Real.rpow Δ (-4) * 1 := by gcongr
        have h12 : (81 : ℝ) * Real.rpow Δ (-4) * 1 = (81 : ℝ) * Real.rpow Δ (-4) := by ring
        rw [h12] at h11
        linarith [h7, h11]
      have h13 : 1 ≤ (900 : ℝ) * ((81 : ℝ) * Real.rpow Δ (-4) * ratio_j j ^ ε_bad) := by
        have h14 : (900 : ℝ) * ((81 : ℝ) * Real.rpow Δ (-4) * ratio_j j ^ ε_bad) ≥
            (900 : ℝ) * 1 := by gcongr
        have h15 : (900 : ℝ) * 1 = (900 : ℝ) := by ring
        rw [h15] at h14
        linarith
      exact h13
    have h_set_tj := h_set_uniform j h_j_in_S
    have h_set_s : CombiningTheorem.IsSetBetweenScales Q (Δ ^ i (j.val + 1)) (Δ ^ i j.val) s (C_uniform j) :=
      IsSetBetweenScales_weaken_exponent h_set_tj (by linarith [hs]) h_tj_ge_s hC_ge_one
    simpa [Δ'] using h_set_s

  -- Good scales
  have h_good : ∀ (j : Fin n) (t_j' : ℝ),
      scaleClass j = ScaleClass.good t_j' →
      CombiningTheorem.IsRegularBetweenScales Q (Δ' (Fin.succ j)) (Δ' j.castSucc) t_j'
        (C_between j) (C_between j) := by
    intro j t_j' hsc
    by_cases h_high : t_j j.val ≥ t
    · -- Good-high: t_j ≥ t, scaleClass = .good (t_j j)
      have h_j_in_S : j ∈ S := by
        by_cases h : j ∈ S
        · exact h
        · have h_bad : scaleClass j = ScaleClass.bad := h_scale_bad j h
          rw [h_bad] at hsc
          cases hsc
      have h_tj'_eq : t_j' = t_j j.val := by
        have h_sc : scaleClass j = ScaleClass.good (t_j j.val) :=
          h_scale_good_high j h_j_in_S h_high
        rw [h_sc] at hsc
        injection hsc with h_inj
        exact h_inj.symm
      have h_C_eq : C_between j = C_uniform j := by
        have h_false : ¬(j ∈ S ∧ t_j j.val ≥ t - ε_G / 2 ∧ t_j j.val < t) := by
          intro h_cont
          have h_not_lt : ¬(t_j j.val < t) := by linarith
          exact h_not_lt h_cont.2.2
        exact dif_neg h_false
      rw [h_tj'_eq, h_C_eq]
      simpa [Δ'] using h_regular_uniform j h_j_in_S (by linarith [(h_tj_range j).1])
    · -- Good-low: t_j < t, scaleClass = .good t
      have h_j_in_S : j ∈ S := by
        by_cases h : j ∈ S
        · exact h
        · have h_bad : scaleClass j = ScaleClass.bad := h_scale_bad j h
          rw [h_bad] at hsc
          cases hsc
      have h_low : t_j j.val ≥ t - ε_G / 2 := by
        by_cases h : t_j j.val ≥ t - ε_G / 2
        · exact h
        · have h_normal : scaleClass j = ScaleClass.normal :=
            h_scale_normal j h_j_in_S (by linarith)
          rw [h_normal] at hsc
          cases hsc
      have h_tj'_eq : t_j' = t := by
        have h_sc : scaleClass j = ScaleClass.good t :=
          h_scale_good_low j h_j_in_S h_low (by linarith)
        rw [h_sc] at hsc
        injection hsc with h_inj
        exact h_inj.symm
      have h_high2 : t_j j.val < t := by linarith
      have h_C_eq : C_between j = C_uniform j * ratio_j j ^ (ε_G / 2) := by
        have h_true : j ∈ S ∧ t_j j.val ≥ t - ε_G / 2 ∧ t_j j.val < t := ⟨h_j_in_S, h_low, h_high2⟩
        exact dif_pos h_true
      rw [h_tj'_eq, h_C_eq]
      have h_set := h_exp_weaken j h_j_in_S h_low h_high2
      have hreg_old := h_regular_uniform j h_j_in_S (by linarith [(h_tj_range j).1])
      have hδ'_pos : 0 < (Δ ^ i (j.val + 1)) / (Δ ^ i j.val) := by positivity
      have hratio_ge_one : 1 ≤ ratio_j j := by
        dsimp only [ratio_j]
        have h1 : i j.val ≤ i (j.val + 1) := le_of_lt (h_i_strict j.val j.is_lt)
        have h2 : Δ ^ i (j.val + 1) ≤ Δ ^ i j.val :=
          pow_le_pow_of_le_one hΔ_nonneg hΔ_le_one h1
        have h3 : 0 < Δ ^ i j.val := by positivity
        have h4 : (Δ ^ i (j.val + 1)) / (Δ ^ i j.val) ≤ 1 := by
          rw [div_le_one h3] <;> exact h2
        have h5 : 1 ≤ ratio_j j := by
          dsimp only [ratio_j]
          have h6 : 0 < Δ ^ i (j.val + 1) := by positivity
          rw [one_le_div h6]
          exact h2
        exact h5
      have hK_pos : 0 < C_uniform j * ratio_j j ^ (ε_G / 2) := by
        have h1 : 0 < C_uniform j := hC_uniform_pos_all j
        have h2 : 0 < ratio_j j ^ (ε_G / 2) := Real.rpow_pos_of_pos (by positivity) _
        exact mul_pos h1 h2
      have h_cover : ∀ (a b : ℤ), (Q ∩ MultiscaleDecomposition.dyadicSquare (Δ ^ i j.val) a b).Nonempty →
          (Metric.externalCoveringNumber (Real.sqrt ((Δ ^ i (j.val + 1)) / (Δ ^ i j.val))).toNNReal
             (MultiscaleDecomposition.homothetyS (Δ ^ i j.val) a b '' (Q ∩ MultiscaleDecomposition.dyadicSquare (Δ ^ i j.val) a b)) : ENNReal) ≤
          ENNReal.ofReal ((C_uniform j * ratio_j j ^ (ε_G / 2)) *
            Real.rpow ((Δ ^ i (j.val + 1)) / (Δ ^ i j.val)) (-t / 2)) := by
        intro a b hnonempty
        have h_old := hreg_old.2.2 a b hnonempty
        have h_bound_old : (Metric.externalCoveringNumber _ _ : ENNReal) ≤
            ENNReal.ofReal (C_uniform j * Real.rpow ((Δ ^ i (j.val + 1)) / (Δ ^ i j.val)) (-(t_j j.val) / 2)) := h_old
        have h1 : C_uniform j * Real.rpow ((Δ ^ i (j.val + 1)) / (Δ ^ i j.val)) (-(t_j j.val) / 2) ≤
            C_uniform j * ratio_j j ^ (ε_G / 2) *
              Real.rpow ((Δ ^ i (j.val + 1)) / (Δ ^ i j.val)) (-t / 2) := by
          set x := (Δ ^ i (j.val + 1)) / (Δ ^ i j.val) with hx_def
          have hx_pos : 0 < x := by positivity
          have hx_le_one : x ≤ 1 := by
            have h5 : Δ ^ i (j.val + 1) ≤ Δ ^ i j.val := pow_le_pow_of_le_one hΔ_nonneg hΔ_le_one (le_of_lt (h_i_strict j.val j.is_lt))
            have h6 : 0 < Δ ^ i j.val := by positivity
            rw [div_le_one h6] <;> exact h5
          have h_exp_ge : -(t_j j.val) / 2 ≥ -t / 2 := by linarith
          have h4 : Real.rpow x (-(t_j j.val) / 2) ≤ Real.rpow x (-t / 2) :=
            Real.rpow_le_rpow_of_exponent_le_or_ge (Or.inr ⟨hx_pos, hx_le_one, by linarith⟩)
          have h5 : 0 < C_uniform j := hC_uniform_pos_all j
          have h6 : 1 ≤ ratio_j j ^ (ε_G / 2) := by
            have h7 : 1 ≤ ratio_j j := hratio_ge_one
            have h8 : 0 ≤ ε_G / 2 := by linarith [hεG_pos]
            exact Real.one_le_rpow h7 h8
          have h10 : 0 ≤ Real.rpow x (-t / 2) := Real.rpow_nonneg (by positivity) _
          have h11 : C_uniform j * Real.rpow x (-t / 2) ≤ C_uniform j * ratio_j j ^ (ε_G / 2) * Real.rpow x (-t / 2) := by
            have h12 : C_uniform j ≤ C_uniform j * ratio_j j ^ (ε_G / 2) := by
              have h13 : C_uniform j > 0 := h5
              have h14 : 1 ≤ ratio_j j ^ (ε_G / 2) := h6
              calc C_uniform j
                = C_uniform j * 1 := by ring
              _ ≤ C_uniform j * ratio_j j ^ (ε_G / 2) := by gcongr
            exact mul_le_mul_of_nonneg_right h12 h10
          have h15 : C_uniform j * Real.rpow x (-(t_j j.val) / 2) ≤ C_uniform j * Real.rpow x (-t / 2) := by
            exact mul_le_mul_of_nonneg_left h4 (by linarith)
          exact le_trans h15 h11
        exact le_trans h_bound_old (ENNReal.ofReal_le_ofReal h1)
      exact ⟨h_set, hK_pos, h_cover⟩

  -- ========================================================================
  -- Step 9: Absorption bounds
  -- ========================================================================
  have h_abs_bounds : ∀ (j : Fin n),
      (scaleClass j = ScaleClass.normal →
        C_between j ≤ Real.log (1 / dyadicDelta k) ^ C_P * (Δ' j.castSucc / Δ' (Fin.succ j)) ^ ε_N) ∧
      (∀ (t_j' : ℝ), scaleClass j = ScaleClass.good t_j' →
        C_between j ≤ Real.log (1 / dyadicDelta k) ^ C_P * (Δ' j.castSucc / Δ' (Fin.succ j)) ^ ε_G) := by
    intro j
    exact thickening_absorption_bounds j S t_j t ε_G ε_N C_P ε_bad Δ k
      (C_uniform j) (ratio_j j) (Δ' j.castSucc / Δ' (Fin.succ j)) (C_between j) (scaleClass j)
      (by rfl)
      (h_scale_bad j) (h_scale_normal j) (h_scale_good_high j) (h_scale_good_low j)
      (h_C_uniform j)
      (h_C_boosted j)
      (h_C_uniform_eq j)
      (h_absorb_normal j) (h_absorb_good_high j) (h_absorb_good_low j)

  have h_C_between_normal : ∀ (j : Fin n), scaleClass j = ScaleClass.normal →
      C_between j ≤ Real.log (1 / dyadicDelta k) ^ C_P * (Δ' j.castSucc / Δ' (Fin.succ j)) ^ ε_N :=
    fun j => (h_abs_bounds j).1

  have h_C_between_good : ∀ (j : Fin n) (t_j' : ℝ),
      scaleClass j = ScaleClass.good t_j' →
      C_between j ≤ Real.log (1 / dyadicDelta k) ^ C_P * (Δ' j.castSucc / Δ' (Fin.succ j)) ^ ε_G :=
    fun j => (h_abs_bounds j).2

  -- ========================================================================
  -- Step 10: Good scale property (t ≤ t_j')
  -- ========================================================================
  have h_good_prop : ∀ (j : Fin n) (t_j' : ℝ),
      scaleClass j = ScaleClass.good t_j' → t ≤ t_j' :=
    fun j t_j' hsc =>
      thickening_good_property j S t_j t ε_G (scaleClass j) t_j' hsc
        (h_scale_bad j) (h_scale_normal j) (h_scale_good_high j) (h_scale_good_low j)

  -- ========================================================================
  -- Conclusion
  -- ========================================================================
  have h_good_upper_bound : ∀ (j : Fin n) (t_j' : ℝ),
      scaleClass j = ScaleClass.good t_j' → t_j' ≤ 2 := by
    intro j t_j' hsc
    by_cases h_high : t_j j.val ≥ t
    · -- Good-high: t_j' = t_j j.val
      have h_j_in_S : j ∈ S := by
        by_cases h : j ∈ S
        · exact h
        · have h_bad : scaleClass j = ScaleClass.bad := h_scale_bad j h
          rw [h_bad] at hsc
          cases hsc
      have h_tj'_eq : t_j' = t_j j.val := by
        have h_sc : scaleClass j = ScaleClass.good (t_j j.val) :=
          h_scale_good_high j h_j_in_S h_high
        rw [h_sc] at hsc
        injection hsc with h_inj
        exact h_inj.symm
      rw [h_tj'_eq]
      exact (h_tj_range j).2
    · -- Good-low: t_j' = t
      have h_j_in_S : j ∈ S := by
        by_cases h : j ∈ S
        · exact h
        · have h_bad : scaleClass j = ScaleClass.bad := h_scale_bad j h
          rw [h_bad] at hsc
          cases hsc
      have h_low : t_j j.val ≥ t - ε_G / 2 := by
        by_cases h : t_j j.val ≥ t - ε_G / 2
        · exact h
        · have h_normal : scaleClass j = ScaleClass.normal :=
            h_scale_normal j h_j_in_S (by linarith)
          rw [h_normal] at hsc
          cases hsc
      have h_tj'_eq : t_j' = t := by
        have h_sc : scaleClass j = ScaleClass.good t :=
          h_scale_good_low j h_j_in_S h_low (by linarith)
        rw [h_sc] at hsc
        injection hsc with h_inj
        exact h_inj.symm
      rw [h_tj'_eq]
      exact ht2

  -- Index identity: good scales = S ∩ {j | t_j j.val ≥ t - ε_G/2}
  have h_good_indices : Finset.univ.filter (fun j : Fin n => (scaleClass j).isGood) =
      S.filter (fun j : Fin n => t_j j.val ≥ t - ε_G / 2) := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h_good
      have h_j_in_S : j ∈ S := by
        by_cases h : j ∈ S
        · exact h
        · have h_bad_sc : scaleClass j = ScaleClass.bad := h_scale_bad j h
          have h_contra : (scaleClass j).isGood = false := by
            rw [h_bad_sc]; rfl
          rw [h_contra] at h_good; contradiction
      have h_low : t_j j.val ≥ t - ε_G / 2 := by
        by_cases h : t_j j.val ≥ t - ε_G / 2
        · exact h
        · have h_normal : scaleClass j = ScaleClass.normal :=
            h_scale_normal j h_j_in_S (by linarith)
          have h_contra : (scaleClass j).isGood = false := by
            rw [h_normal]; rfl
          rw [h_contra] at h_good; contradiction
      exact ⟨h_j_in_S, h_low⟩
    · rintro ⟨h_j_in_S, h_low⟩
      by_cases h_high : t_j j.val ≥ t
      · have h_sc : scaleClass j = ScaleClass.good (t_j j.val) :=
          h_scale_good_high j h_j_in_S h_high
        rw [h_sc]; simp [ScaleClass.isGood]
      · have h_sc : scaleClass j = ScaleClass.good t :=
          h_scale_good_low j h_j_in_S h_low (by linarith)
        rw [h_sc]; simp [ScaleClass.isGood]

  -- Index identity: bad scales = B
  have h_bad_indices : Finset.univ.filter (fun j : Fin n => (scaleClass j).isBad) = B := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h_bad
      have h_j_notin_S : j ∉ S := by
        by_cases h : j ∈ S
        · by_cases h2 : t_j j.val ≥ t - ε_G / 2
          · by_cases h3 : t_j j.val ≥ t
            · have h_sc : scaleClass j = ScaleClass.good (t_j j.val) :=
                h_scale_good_high j h h3
              have h_contra : (scaleClass j).isBad = false := by rw [h_sc]; rfl
              rw [h_contra] at h_bad; contradiction
            · have h_sc : scaleClass j = ScaleClass.good t :=
                h_scale_good_low j h h2 (by linarith)
              have h_contra : (scaleClass j).isBad = false := by rw [h_sc]; rfl
              rw [h_contra] at h_bad; contradiction
          · have h_sc : scaleClass j = ScaleClass.normal :=
              h_scale_normal j h (by linarith)
            have h_contra : (scaleClass j).isBad = false := by rw [h_sc]; rfl
            rw [h_contra] at h_bad; contradiction
        · exact h
      have h1 : j ∈ S ∪ B := by
        rw [h_SB_univ] <;> exact Finset.mem_univ j
      exact (Finset.mem_union.mp h1).resolve_left h_j_notin_S
    · intro h_j_in_B
      have h_j_notin_S : j ∉ S := by
        intro h
        exact Finset.disjoint_left.mp h_SB_disj h h_j_in_B
      have h_sc : scaleClass j = ScaleClass.bad := h_scale_bad j h_j_notin_S
      rw [h_sc]; simp [ScaleClass.isBad]

  refine ⟨C_between, scaleClass, N', ?_⟩
  constructor
  · exact ⟨hM_pos, hΔ_strict, hΔ_end, hΔ_start, hΔ_pos', hΔ_dyadic', h_scale_ratio,
        h_uniform_at_scales, h_normal, h_good, h_C_between_normal, h_C_between_good⟩
  constructor
  · exact h_good_prop
  constructor
  · exact h_good_upper_bound
  constructor
  · exact h_good_indices
  · exact h_bad_indices

end DirecretisedFurstenbergEstimate.Section9
