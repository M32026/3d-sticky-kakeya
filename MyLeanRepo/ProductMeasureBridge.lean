module

/-
# Product-Measure Bridge — Proof Assembly

Assembles the final `product_measure_bridge_uniform` from:
1. Pelican's representative construction → μ_A with FiniteScaleIntervalBound
2. Support-free product ball bound (SupportFreeFrostman.lean)
3. Bacon's finite-scale energy bound

## Status
- Step 1: pending pelican
- Step 2: done (SupportFreeFrostman.lean)
- Step 3: pending bacon
- Assembly: skeleton below, fills once 1 and 3 are ready
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.CubeIndexSet
public import MyLeanRepo.FrostmanEnergy
public import MyLeanRepo.ProductMeasureEnergy
public import MyLeanRepo.MarstrandArbitraryDim
public import MyLeanRepo.SupportFreeFrostman
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Classical Bornology BigOperators
open bourgain_projection_theorem (realCubeIndexSet realCubeIndexSet_finite
  realCoveringNumber_eq_card)

namespace WeakTwoEndsSumProduct

/-! ## Step 1: Representative measure construction -/

/-- Existence of dyadic scale r' ∈ [r, 2r] with r' ≥ δ. -/
private lemma exists_dyadic_scale_between_reps {δ r : ℝ} (hδ : 0 < δ)
    (hδ_dyadic : δ ∈ dyadicScales) (hr_pos : 0 < r) (hδ_le_r : δ ≤ r)
    (hr_le_one : r ≤ 1) :
    ∃ (r' : ℝ), r' ∈ dyadicScales ∧ δ ≤ r' ∧ r' ≤ 1 ∧ r ≤ r' ∧ r' < 2 * r := by
  rcases hδ_dyadic with ⟨nδ, hnδ⟩
  have hδ_eq : δ = (2 : ℝ)^(-(nδ : ℝ)) := by simpa [dyadicScales] using hnδ
  let P : ℕ → Prop := fun n => (2 : ℝ)^(-(n : ℝ)) < r
  have hP_succ : P (nδ + 1) := by
    dsimp only [P]
    have h_exp : ((nδ + 1 : ℕ) : ℝ) = (nδ : ℝ) + 1 := by simp
    rw [h_exp]
    have h : (2 : ℝ)^(-((nδ : ℝ) + 1)) = δ / 2 := by
      rw [hδ_eq]
      have h2 : (2 : ℝ)^(-((nδ : ℝ) + 1)) = (2 : ℝ)^(-(nδ : ℝ)) / 2 := by
        have h3 : -((nδ : ℝ) + 1) = -(nδ : ℝ) - 1 := by ring
        rw [h3, Real.rpow_sub (by norm_num)] <;> norm_num
      exact h2
    rw [h]; linarith
  have h1 : ∃ n, P n := ⟨nδ + 1, hP_succ⟩
  let n : ℕ := Nat.find h1
  have hn_prop : P n := Nat.find_spec h1
  have hn_pos : 0 < n := by
    by_contra h
    have h9 : n = 0 := by omega
    have h10 : P 0 := by rw [h9] at hn_prop; exact hn_prop
    dsimp only [P] at h10
    norm_num at h10
    linarith
  let n' : ℕ := n - 1
  have h_n'_lt_n : n' < n := by omega
  have h_n'_not_P : ¬ P n' := Nat.find_min h1 h_n'_lt_n
  have h_n'_prop : (2 : ℝ)^(-(n' : ℝ)) ≥ r := by simpa [P] using h_n'_not_P
  set r' := (2 : ℝ)^(-(n' : ℝ)) with hr'_def
  have hr'_dyadic : r' ∈ dyadicScales := ⟨n', by simp [hr'_def, dyadicScales]⟩
  have hr'_ge_r : r ≤ r' := h_n'_prop
  have hr'_lt_2r : r' < 2 * r := by
    have h14 : (n : ℝ) = (n' : ℝ) + 1 := by simp [n', hn_pos] <;> omega
    have h15 : (2 : ℝ)^(-(n : ℝ)) = r' / 2 := by
      rw [hr'_def, h14]
      have h16 : -((n' : ℝ) + 1) = -(n' : ℝ) - 1 := by ring
      rw [h16, Real.rpow_sub (by norm_num)] <;> norm_num
    have h13 : r' = 2 * (2 : ℝ)^(-(n : ℝ)) := by linarith
    rw [h13]
    exact mul_lt_mul_of_pos_left hn_prop (by norm_num)
  have h_n'_le_nδ : n' ≤ nδ := by
    by_contra h
    have h15 : n' > nδ := by omega
    have h16 : n' ≥ nδ + 1 := by omega
    have h17 : (2 : ℝ)^(-(n' : ℝ)) ≤ (2 : ℝ)^(-((nδ + 1 : ℕ) : ℝ)) := by
      gcongr <;> norm_num <;> omega
    have h18 : (2 : ℝ)^(-((nδ + 1 : ℕ) : ℝ)) < r := hP_succ
    have h19 : (2 : ℝ)^(-(n' : ℝ)) < r := by linarith
    exact h_n'_not_P (by simpa [P] using h19)
  have hδ_le_r' : δ ≤ r' := by
    rw [hδ_eq, hr'_def]
    have h20 : (n' : ℝ) ≤ (nδ : ℝ) := by exact_mod_cast h_n'_le_nδ
    have h21 : -(nδ : ℝ) ≤ -(n' : ℝ) := by linarith
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h21
  have hr'_le_one : r' ≤ 1 := by
    have h25 : r' = (2 : ℝ)^(-(n' : ℝ)) := hr'_def
    rw [h25]
    have h26 : (n' : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le n'
    have h27 : -(n' : ℝ) ≤ 0 := by linarith
    have h28 : (2 : ℝ)^(-(n' : ℝ)) ≤ (2 : ℝ)^(0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h27
    have h29 : (2 : ℝ)^(0 : ℝ) = 1 := by norm_num
    rw [h29] at h28
    exact h28
  exact ⟨r', hr'_dyadic, hδ_le_r', hr'_le_one, hr'_ge_r, hr'_lt_2r⟩

/-- Cover Icc(c-r, c+r) by 3 adjacent half-open intervals of scale r'. -/
private lemma interval_covered_by_three_reps {r r' c : ℝ} (hr_pos : 0 < r) (hr'_pos : 0 < r')
    (hle : r ≤ r') :
    ∃ (k : ℤ), Set.Icc (c - r) (c + r) ⊆
      Set.Ico (r' * ((k - 1 : ℤ) : ℝ)) (r' * ((k : ℝ))) ∪
      Set.Ico (r' * ((k : ℝ))) (r' * (((k : ℝ) + 1))) ∪
      Set.Ico (r' * (((k : ℝ) + 1))) (r' * (((k : ℝ) + 2))) := by
  let k : ℤ := Int.floor (c / r')
  have h1 : (k : ℝ) ≤ c / r' := Int.floor_le (c / r')
  have h2 : c / r' < (k : ℝ) + 1 := Int.lt_floor_add_one (c / r')
  have h3 : r' * (k : ℝ) ≤ c := by
    calc r' * (k : ℝ) ≤ r' * (c / r') := by gcongr
      _ = c := by field_simp [hr'_pos.ne'] <;> ring
  have h4 : c < r' * ((k : ℝ) + 1) := by
    calc c = r' * (c / r') := by field_simp [hr'_pos.ne'] <;> ring
      _ < r' * ((k : ℝ) + 1) := by gcongr
  refine ⟨k, ?_⟩
  intro x hx
  have h5 : c - r ≤ x := hx.1
  have h6 : x ≤ c + r := hx.2
  have h7 : r' * ((k : ℝ) - 1) ≤ x := by linarith
  have h8 : x < r' * (((k : ℝ) + 1) + 1) := by linarith
  by_cases h9 : x < r' * (k : ℝ)
  · have h_goal : x ∈ Set.Ico (r' * ((k - 1 : ℤ) : ℝ)) (r' * ((k : ℝ))) := by
      simp only [Set.mem_Ico]; constructor
      · have h7' : r' * ((k - 1 : ℤ) : ℝ) ≤ x := by
          have h_eq : r' * ((k - 1 : ℤ) : ℝ) = r' * ((k : ℝ) - 1) := by simp <;> ring
          rw [h_eq]; exact h7
        exact h7'
      · exact h9
    exact Or.inl (Or.inl h_goal)
  · by_cases h10 : x < r' * ((k : ℝ) + 1)
    · have h_goal : x ∈ Set.Ico (r' * ((k : ℝ))) (r' * (((k : ℝ) + 1))) := by
        simp only [Set.mem_Ico]; constructor <;> linarith
      exact Or.inl (Or.inr h_goal)
    · have h_goal : x ∈ Set.Ico (r' * (((k : ℝ) + 1))) (r' * (((k : ℝ) + 2))) := by
        simp only [Set.mem_Ico]; constructor <;> linarith
      exact Or.inr h_goal

/-- Helper: `ENat.toENNReal ↑n = ENNReal.ofReal (n : ℝ)` for `n : ℕ`. -/
private lemma enat_to_ennreal_ofReal (n : ℕ) :
    ENat.toENNReal (↑n : ENat) = ENNReal.ofReal (n : ℝ) := by
  simp

/-- From a (δ,κ,C_A)-set A ⊆ [1,2], construct μ on representatives with
    finite-scale interval bound, support ⊆ A, and finite support. -/
lemma finite_scale_frostman_from_reps
    {δ κ C_A : ℝ} {A : Set ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hκ_pos : 0 < κ) (hC_A_pos : 0 < C_A)
    (hA_sub : A ⊆ Set.Icc 1 2)
    (hA_delta : IsRealDeltaSet δ κ C_A A) :
    ∃ (μ : Measure ℝ),
      FiniteScaleIntervalBound δ κ (3 * (2 : ℝ)^κ * C_A) μ ∧
      μ.support ⊆ A ∧
      μ.support.Finite := by
  rcases hA_delta with ⟨hP_bdd, hP_nonempty, _, hδ_dyadic, _, hκ_nonneg, _, _, h_reg_prop⟩
  have hA_nonempty : A.Nonempty := by
    rcases hP_nonempty with ⟨x, hx⟩
    have h2 : x 0 ∈ A := by simpa [realLineCopy] using hx
    exact ⟨x 0, h2⟩
  have hA_bdd : Bornology.IsBounded A :=
    (Metric.isBounded_Icc (1 : ℝ) 2).subset hA_sub
  let Idx : Set ℤ := realCubeIndexSet δ A
  have hIdx_fin : Idx.Finite := realCubeIndexSet_finite hδ_pos hA_bdd
  -- Choose one representative per cell
  have h_exists : ∀ (k : ℤ), k ∈ Idx →
      ∃ (x : ℝ), x ∈ A ∧ x ∈ Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := by
    intro k hk
    have h1 : k ∈ realCubeIndexSet δ A := hk
    have h2 : (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ A).Nonempty := by
      simpa [realCubeIndexSet, Set.mem_setOf_eq] using h1
    rcases h2 with ⟨x, hx1, hx2⟩
    exact ⟨x, hx2, hx1⟩
  choose a ha_in_A ha_in_cell using h_exists
  let a' : ℤ → ℝ := fun k =>
    if hk : k ∈ Idx then a k hk else 0
  have ha'_eq : ∀ (k : ℤ) (hk : k ∈ Idx), a' k = a k hk := by
    intro k hk
    dsimp only [a']
    rw [dif_pos hk]
  let A_rep : Set ℝ := a' '' Idx
  have hA_rep_sub : A_rep ⊆ A := by
    intro y hy
    rcases hy with ⟨k, hk, rfl⟩
    have h_eq : a' k = a k hk := ha'_eq k hk
    rw [h_eq]
    exact ha_in_A k hk
  have hA_rep_fin : A_rep.Finite := Set.Finite.image _ hIdx_fin
  have hA_rep_nonempty : A_rep.Nonempty := by
    rcases hA_nonempty with ⟨x, hx⟩
    let k : ℤ := Int.floor (x / δ)
    have h3 : x ∈ Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := by
      have h4 : δ * (k : ℝ) ≤ x := by
        have h5 : (k : ℝ) ≤ x / δ := Int.floor_le (x / δ)
        have h6 : δ * (k : ℝ) ≤ δ * (x / δ) := by gcongr
        have h7 : δ * (x / δ) = x := by field_simp [hδ_pos.ne'] <;> ring
        rw [h7] at h6; exact h6
      have h5 : x < δ * ((k : ℝ) + 1) := by
        have h6 : x / δ < (k : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
        have h7 : δ * (x / δ) < δ * ((k : ℝ) + 1) := by gcongr
        have h8 : δ * (x / δ) = x := by field_simp [hδ_pos.ne'] <;> ring
        rw [h8] at h7; exact h7
      exact ⟨h4, h5⟩
    have hk : k ∈ Idx := by
      change k ∈ realCubeIndexSet δ A
      simp only [realCubeIndexSet, Set.mem_setOf_eq]
      exact ⟨x, h3, hx⟩
    exact ⟨a' k, k, hk, rfl⟩
  have h_a'_inj : Set.InjOn a' Idx := by
    intro k1 hk1 k2 hk2 h
    have h_eq1 : a' k1 = a k1 hk1 := ha'_eq k1 hk1
    have h_eq2 : a' k2 = a k2 hk2 := ha'_eq k2 hk2
    rw [h_eq1, h_eq2] at h
    have h1 : a k1 hk1 ∈ Set.Ico (δ * (k1 : ℝ)) (δ * ((k1 : ℝ) + 1)) := ha_in_cell k1 hk1
    have h2 : a k2 hk2 ∈ Set.Ico (δ * (k2 : ℝ)) (δ * ((k2 : ℝ) + 1)) := ha_in_cell k2 hk2
    rw [h] at h1
    have h11 : δ * (k1 : ℝ) ≤ a k2 hk2 := h1.1
    have h12 : a k2 hk2 < δ * ((k1 : ℝ) + 1) := h1.2
    have h21 : δ * (k2 : ℝ) ≤ a k2 hk2 := h2.1
    have h22 : a k2 hk2 < δ * ((k2 : ℝ) + 1) := h2.2
    have h_k2_le_k1 : k2 ≤ k1 := by
      have h_pos2 : 0 < δ := hδ_pos
      have h_div1 : (δ * (k2 : ℝ)) / δ ≤ (a k2 hk2) / δ :=
        div_le_div_of_nonneg_right h21 (by linarith)
      have h_div2 : (a k2 hk2) / δ < (δ * ((k1 : ℝ) + 1)) / δ :=
        div_lt_div_of_pos_right h12 h_pos2
      have h_eq1 : (δ * (k2 : ℝ)) / δ = (k2 : ℝ) := by field_simp [h_pos2.ne'] <;> ring
      have h_eq2 : (δ * ((k1 : ℝ) + 1)) / δ = (k1 : ℝ) + 1 := by field_simp [h_pos2.ne'] <;> ring
      have h_strict : (δ * (k2 : ℝ)) / δ < (δ * ((k1 : ℝ) + 1)) / δ :=
        lt_of_le_of_lt h_div1 h_div2
      have h : (k2 : ℝ) < (k1 : ℝ) + 1 := by
        rw [h_eq1, h_eq2] at h_strict
        exact h_strict
      have h' : k2 < k1 + 1 := by exact_mod_cast h
      omega
    have h_k1_le_k2 : k1 ≤ k2 := by
      have h_pos2 : 0 < δ := hδ_pos
      have h_div1 : (δ * (k1 : ℝ)) / δ ≤ (a k2 hk2) / δ :=
        div_le_div_of_nonneg_right h11 (by linarith)
      have h_div2 : (a k2 hk2) / δ < (δ * ((k2 : ℝ) + 1)) / δ :=
        div_lt_div_of_pos_right h22 h_pos2
      have h_eq1 : (δ * (k1 : ℝ)) / δ = (k1 : ℝ) := by field_simp [h_pos2.ne'] <;> ring
      have h_eq2 : (δ * ((k2 : ℝ) + 1)) / δ = (k2 : ℝ) + 1 := by field_simp [h_pos2.ne'] <;> ring
      have h_strict : (δ * (k1 : ℝ)) / δ < (δ * ((k2 : ℝ) + 1)) / δ :=
        lt_of_le_of_lt h_div1 h_div2
      have h : (k1 : ℝ) < (k2 : ℝ) + 1 := by
        rw [h_eq1, h_eq2] at h_strict
        exact h_strict
      have h' : k1 < k2 + 1 := by exact_mod_cast h
      omega
    have h7 : k1 = k2 := by omega
    exact h7
  let nA := hIdx_fin.toFinset.card
  have h_nA_pos : 0 < nA := by
    have h1 : Idx.Nonempty := by
      rcases hA_nonempty with ⟨x, hx⟩
      let k : ℤ := Int.floor (x / δ)
      have h3 : x ∈ Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := by
        have h4 : δ * (k : ℝ) ≤ x := by
          have h5 : (k : ℝ) ≤ x / δ := Int.floor_le (x / δ)
          have h6 : δ * (k : ℝ) ≤ δ * (x / δ) := by gcongr
          have h7 : δ * (x / δ) = x := by field_simp [hδ_pos.ne'] <;> ring
          rw [h7] at h6; exact h6
        have h5 : x < δ * ((k : ℝ) + 1) := by
          have h6 : x / δ < (k : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
          have h7 : δ * (x / δ) < δ * ((k : ℝ) + 1) := by gcongr
          have h8 : δ * (x / δ) = x := by field_simp [hδ_pos.ne'] <;> ring
          rw [h8] at h7; exact h7
        exact ⟨h4, h5⟩
      have hk : k ∈ Idx := by
        change k ∈ realCubeIndexSet δ A
        simp only [realCubeIndexSet, Set.mem_setOf_eq]
        exact ⟨x, h3, hx⟩
      exact ⟨k, hk⟩
    have h2 : (hIdx_fin.toFinset : Set ℤ).Nonempty := by
      have h3 : (hIdx_fin.toFinset : Set ℤ) = Idx := Set.Finite.coe_toFinset hIdx_fin
      rw [h3]
      exact h1
    exact Finset.card_pos.mpr h2
  let Idx_finset := hIdx_fin.toFinset
  let A_rep_finset := Idx_finset.image a'
  have h_card_finset : A_rep_finset.card = Idx_finset.card :=
    Finset.card_image_of_injOn (s := Idx_finset) (f := a')
      (by simpa [Idx_finset, hIdx_fin.coe_toFinset] using h_a'_inj)
  have h_card_A_rep : A_rep.encard = ↑nA := by
    have h1 : A_rep = (A_rep_finset : Set ℝ) := by
      ext z; simp [A_rep, A_rep_finset, Idx_finset]
    rw [h1, Set.encard_coe_eq_coe_finsetCard A_rep_finset, h_card_finset]
    <;> rfl
  have hN_A : Nreal δ A = ENat.toENNReal Idx.encard := by
    exact realCoveringNumber_eq_card hδ_pos hA_bdd
  -- Uniform measure
  let μ : Measure ℝ := (ENat.toENNReal A_rep.encard)⁻¹ • Measure.count.restrict A_rep
  have hμ_prob : μ Set.univ = 1 := by
    dsimp only [μ]
    rw [Measure.smul_apply]
    have h1 : Measure.count.restrict A_rep Set.univ = ENat.toENNReal A_rep.encard := by
      rw [Measure.restrict_apply (by simp : MeasurableSet (Set.univ : Set ℝ))]
      <;> simp [Set.inter_univ]
      <;> exact Measure.count_apply hA_rep_fin.measurableSet
    rw [h1, h_card_A_rep]
    exact ENNReal.inv_mul_cancel (by simp [h_nA_pos.ne']) (by simp)
  have hμ_support : μ.support ⊆ A_rep := by
    dsimp only [μ]
    have h4 : IsOpen (A_repᶜ : Set ℝ) :=
      (Set.Finite.isClosed hA_rep_fin).isOpen_compl
    have h4_meas : MeasurableSet (A_repᶜ : Set ℝ) := h4.measurableSet
    have h7 : (Measure.count.restrict A_rep) (A_repᶜ) = 0 := by
      rw [Measure.restrict_apply h4_meas]
      have h_disj : A_repᶜ ∩ A_rep = ∅ := by
        ext z; simp [Set.mem_compl_iff] <;> tauto
      rw [h_disj] <;> simp
    have h6 : μ (A_repᶜ) = 0 := by
      rw [Measure.smul_apply, h7] <;> simp
    have hA_rep_closed : IsClosed A_rep := hA_rep_fin.isClosed
    have h_ae : A_rep ∈ MeasureTheory.ae μ := by
      simpa [MeasureTheory.mem_ae_iff] using h6
    exact MeasureTheory.Measure.support_subset_of_isClosed hA_rep_closed h_ae
  have hμ_support_A : μ.support ⊆ A := by
    intro y hy
    exact hA_rep_sub (hμ_support hy)
  have hμ_support_fin : μ.support.Finite := hA_rep_fin.subset hμ_support
  -- Interval bound
  let C_frost : ℝ := 3 * (2 : ℝ)^κ * C_A
  have hC_frost_pos : 0 < C_frost := by positivity
  have h_bound : ∀ (x r : ℝ), δ ≤ r → r ≤ 1 →
      μ (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (C_frost * r ^ κ) := by
    intro x r hδ_le_r hr_le_one
    have hr_pos : 0 < r := by linarith
    let J : Set ℝ := Set.Icc (x - r) (x + r)
    rcases exists_dyadic_scale_between_reps hδ_pos hδ_dyadic hr_pos hδ_le_r hr_le_one
      with ⟨r', hr'_dyadic, hδ_le_r', hr'_le_one, hr_le_r', hr'_lt_2r⟩
    have hr'_pos : 0 < r' := by linarith
    rcases interval_covered_by_three_reps hr_pos hr'_pos hr_le_r' with ⟨k0, h_cover⟩
    let I0 := Set.Ico (r' * ((k0 - 1 : ℤ) : ℝ)) (r' * ((k0 : ℝ)))
    let I1 := Set.Ico (r' * ((k0 : ℝ))) (r' * (((k0 : ℝ) + 1)))
    let I2 := Set.Ico (r' * (((k0 : ℝ) + 1))) (r' * (((k0 : ℝ) + 2)))
    let S0 := realCubeIndexSet δ (A ∩ I0)
    let S1 := realCubeIndexSet δ (A ∩ I1)
    let S2 := realCubeIndexSet δ (A ∩ I2)
    let SJ := realCubeIndexSet δ (A ∩ J)
    have hAJ_bdd : ∀ (I : Set ℝ), Bornology.IsBounded (A ∩ I) := by
      intro I
      apply hA_bdd.subset
      simp
    have h_fin0 : S0.Finite := realCubeIndexSet_finite hδ_pos (hAJ_bdd I0)
    have h_fin1 : S1.Finite := realCubeIndexSet_finite hδ_pos (hAJ_bdd I1)
    have h_fin2 : S2.Finite := realCubeIndexSet_finite hδ_pos (hAJ_bdd I2)
    have h_finJ : SJ.Finite := realCubeIndexSet_finite hδ_pos (hAJ_bdd J)
    -- Map representatives in J to their cell indices
    let Idx_J := Idx ∩ {k | a' k ∈ J}
    have h_Idx_J_sub : Idx_J ⊆ SJ := by
      intro k hk
      have h_k_in_Idx : k ∈ Idx := hk.1
      have h_a'_in_J : a' k ∈ J := hk.2
      have h_a'_in_A : a' k ∈ A := by
        rw [ha'_eq k h_k_in_Idx]; exact ha_in_A k h_k_in_Idx
      have h_a'_in_cell : a' k ∈ Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := by
        rw [ha'_eq k h_k_in_Idx]; exact ha_in_cell k h_k_in_Idx
      have h_goal : k ∈ realCubeIndexSet δ (A ∩ J) := by
        simp only [realCubeIndexSet, Set.mem_setOf_eq]
        exact ⟨a' k, h_a'_in_cell, ⟨h_a'_in_A, h_a'_in_J⟩⟩
      exact h_goal
    have h_image : a' '' Idx_J = A_rep ∩ J := by
      ext z
      simp only [A_rep, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨k, hk.1, rfl⟩, hk.2⟩
      · rintro ⟨⟨k, hk, rfl⟩, hzJ⟩
        exact ⟨k, ⟨hk, hzJ⟩, rfl⟩
    have h_inj_on : Set.InjOn a' Idx_J := by
      intro k1 hk1 k2 hk2 h
      exact h_a'_inj hk1.1 hk2.1 h
    have h_rep_encard : (A_rep ∩ J).encard = Idx_J.encard := by
      rw [← h_image]
      exact h_inj_on.encard_image
    have h_rep_bound : (A_rep ∩ J).encard ≤ SJ.encard := by
      rw [h_rep_encard]
      exact Set.encard_le_encard h_Idx_J_sub
    -- Covering number bound via 3 cubes
    have h1 : SJ ⊆ S0 ∪ S1 ∪ S2 := by
      intro k hk
      rcases hk with ⟨z, hz_cell, hzAJ⟩
      have h5 : z ∈ (I0 ∪ I1) ∪ I2 := h_cover hzAJ.2
      rcases h5 with (h5 | h5)
      · rcases h5 with (h5 | h5)
        · have hg : k ∈ S0 := ⟨z, hz_cell, ⟨hzAJ.1, h5⟩⟩
          exact Or.inl (Or.inl hg)
        · have hg : k ∈ S1 := ⟨z, hz_cell, ⟨hzAJ.1, h5⟩⟩
          exact Or.inl (Or.inr hg)
      · have hg : k ∈ S2 := ⟨z, hz_cell, ⟨hzAJ.1, h5⟩⟩
        exact Or.inr hg
    have h_encard_union : (S0 ∪ S1 ∪ S2).encard ≤ S0.encard + S1.encard + S2.encard := by
      have h_u1 : (S0 ∪ S1 ∪ S2).encard ≤ (S0 ∪ S1).encard + S2.encard := Set.encard_union_le _ _
      have h_u2 : (S0 ∪ S1).encard ≤ S0.encard + S1.encard := Set.encard_union_le _ _
      calc (S0 ∪ S1 ∪ S2).encard
        ≤ (S0 ∪ S1).encard + S2.encard := h_u1
      _ ≤ S0.encard + S1.encard + S2.encard := by
        gcongr
    have h_cover_num : SJ.encard ≤ S0.encard + S1.encard + S2.encard :=
      le_trans (Set.encard_le_encard h1) h_encard_union
    -- Delta-set bounds for each cube
    let Q0 : Set (EuclideanSpace ℝ (Fin 1)) := dyadicCube r' (fun _ => k0 - 1)
    let Q1 : Set (EuclideanSpace ℝ (Fin 1)) := dyadicCube r' (fun _ => k0)
    let Q2 : Set (EuclideanSpace ℝ (Fin 1)) := dyadicCube r' (fun _ => k0 + 1)
    have hQ0_in : Q0 ∈ dyadicCubes 1 r' := ⟨(fun _ => k0 - 1), rfl⟩
    have hQ1_in : Q1 ∈ dyadicCubes 1 r' := ⟨(fun _ => k0), rfl⟩
    have hQ2_in : Q2 ∈ dyadicCubes 1 r' := ⟨(fun _ => k0 + 1), rfl⟩
    have hQ_eq : ∀ (k : ℤ), realLineCopy (A ∩ Set.Ico (r' * (k : ℝ)) (r' * ((k : ℝ) + 1))) =
        realLineCopy A ∩ dyadicCube r' (fun _ => k) := by
      intro k
      ext z
      simp only [realLineCopy, Set.mem_inter_iff, Set.mem_setOf_eq, dyadicCube]
      have h : (∀ (i : Fin 1), z i ∈ Set.Ico (r' * (k : ℝ)) (r' * ((k : ℝ) + 1))) ↔
          z 0 ∈ Set.Ico (r' * (k : ℝ)) (r' * ((k : ℝ) + 1)) := by
        simp [Fin.forall_fin_one]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h.mpr h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h.mp h2⟩
    have h_I0_eq : I0 = Set.Ico (r' * ((k0 - 1 : ℤ) : ℝ)) (r' * (((k0 - 1 : ℤ) : ℝ) + 1)) := by
      have h_upper : r' * ((k0 : ℝ)) = r' * (((k0 - 1 : ℤ) : ℝ) + 1) := by
        have h : (k0 : ℝ) = ((k0 - 1 : ℤ) : ℝ) + 1 := by
          simp <;> ring
        rw [h]
      ext y
      simp only [I0, Set.mem_Ico, h_upper]
      <;> rfl
    have h_I2_eq : I2 = Set.Ico (r' * ((k0 + 1 : ℤ) : ℝ)) (r' * (((k0 + 1 : ℤ) : ℝ) + 1)) := by
      dsimp only [I2]
      congr 1
      · congr 1; norm_cast <;> omega
      · congr 1; norm_cast <;> omega
    have h_eq0 : realLineCopy (A ∩ I0) = realLineCopy A ∩ Q0 := by
      rw [h_I0_eq]; exact hQ_eq (k0 - 1)
    have h_eq1 : realLineCopy (A ∩ I1) = realLineCopy A ∩ Q1 := by
      exact hQ_eq k0
    have h_eq2 : realLineCopy (A ∩ I2) = realLineCopy A ∩ Q2 := by
      rw [h_I2_eq]; exact hQ_eq (k0 + 1)
    have h_bound0 : Nreal δ (A ∩ I0) ≤ ENNReal.ofReal C_A * Nreal δ A * ENNReal.ofReal (r' ^ κ) := by
      have h := h_reg_prop (r := r') (Q := Q0) hr'_dyadic hQ0_in hδ_le_r' hr'_le_one
      rw [←h_eq0] at h; exact h
    have h_bound1 : Nreal δ (A ∩ I1) ≤ ENNReal.ofReal C_A * Nreal δ A * ENNReal.ofReal (r' ^ κ) := by
      have h := h_reg_prop (r := r') (Q := Q1) hr'_dyadic hQ1_in hδ_le_r' hr'_le_one
      rw [←h_eq1] at h; exact h
    have h_bound2 : Nreal δ (A ∩ I2) ≤ ENNReal.ofReal C_A * Nreal δ A * ENNReal.ofReal (r' ^ κ) := by
      have h := h_reg_prop (r := r') (Q := Q2) hr'_dyadic hQ2_in hδ_le_r' hr'_le_one
      rw [←h_eq2] at h; exact h
    have hN0 : Nreal δ (A ∩ I0) = ENat.toENNReal S0.encard := by
      have h : Nreal δ (A ∩ I0) = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy (A ∩ I0))) := by rfl
      rw [h]
      exact realCoveringNumber_eq_card hδ_pos (hAJ_bdd I0)
    have hN1 : Nreal δ (A ∩ I1) = ENat.toENNReal S1.encard := by
      have h : Nreal δ (A ∩ I1) = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy (A ∩ I1))) := by rfl
      rw [h]
      exact realCoveringNumber_eq_card hδ_pos (hAJ_bdd I1)
    have hN2 : Nreal δ (A ∩ I2) = ENat.toENNReal S2.encard := by
      have h : Nreal δ (A ∩ I2) = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy (A ∩ I2))) := by rfl
      rw [h]
      exact realCoveringNumber_eq_card hδ_pos (hAJ_bdd I2)
    let n0 := h_fin0.toFinset.card
    let n1 := h_fin1.toFinset.card
    let n2 := h_fin2.toFinset.card
    have h_encard_idx : Idx.encard = ↑nA := by
      have h1 : Idx.encard = ↑hIdx_fin.toFinset.card := hIdx_fin.encard_eq_coe_toFinset_card
      have h2 : hIdx_fin.toFinset.card = nA := by rfl
      rw [h1, h2]
    have h_encard0 : S0.encard = ↑n0 := by
      have h1 : S0.encard = ↑h_fin0.toFinset.card := h_fin0.encard_eq_coe_toFinset_card
      have h2 : h_fin0.toFinset.card = n0 := by rfl
      rw [h1, h2]
    have h_encard1 : S1.encard = ↑n1 := by
      have h1 : S1.encard = ↑h_fin1.toFinset.card := h_fin1.encard_eq_coe_toFinset_card
      have h2 : h_fin1.toFinset.card = n1 := by rfl
      rw [h1, h2]
    have h_encard2 : S2.encard = ↑n2 := by
      have h1 : S2.encard = ↑h_fin2.toFinset.card := h_fin2.encard_eq_coe_toFinset_card
      have h2 : h_fin2.toFinset.card = n2 := by rfl
      rw [h1, h2]
    have h_rhs_eq : ENNReal.ofReal C_A * Nreal δ A * ENNReal.ofReal (r' ^ κ) =
        ENNReal.ofReal (C_A * (nA : ℝ) * (r' ^ κ)) := by
      have hN_A' : Nreal δ A = ENNReal.ofReal (nA : ℝ) := by
        rw [hN_A, h_encard_idx]
        exact enat_to_ennreal_ofReal nA
      rw [hN_A']
      have h_pos1 : 0 ≤ C_A := by linarith
      have h_pos2 : 0 ≤ (nA : ℝ) := by positivity
      rw [← ENNReal.ofReal_mul h_pos1, ← ENNReal.ofReal_mul (mul_nonneg h_pos1 h_pos2)]
      <;> congr 1 <;> ring
    have h_real0 : (n0 : ℝ) ≤ C_A * (nA : ℝ) * (r' ^ κ) := by
      have h_n0_cast : ENat.toENNReal S0.encard = ENNReal.ofReal (n0 : ℝ) := by
        rw [h_encard0]
        exact enat_to_ennreal_ofReal n0
      have h' : ENat.toENNReal S0.encard ≤ ENNReal.ofReal (C_A * (nA : ℝ) * (r' ^ κ)) := by
        have h_bound0' : Nreal δ (A ∩ I0) ≤ ENNReal.ofReal C_A * Nreal δ A * ENNReal.ofReal (r' ^ κ) := h_bound0
        rw [hN0, h_rhs_eq] at h_bound0'
        exact h_bound0'
      rw [h_n0_cast] at h'
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h'
    have h_real1 : (n1 : ℝ) ≤ C_A * (nA : ℝ) * (r' ^ κ) := by
      have h_n1_cast : ENat.toENNReal S1.encard = ENNReal.ofReal (n1 : ℝ) := by
        rw [h_encard1]
        exact enat_to_ennreal_ofReal n1
      have h' : ENat.toENNReal S1.encard ≤ ENNReal.ofReal (C_A * (nA : ℝ) * (r' ^ κ)) := by
        have h_bound1' : Nreal δ (A ∩ I1) ≤ ENNReal.ofReal C_A * Nreal δ A * ENNReal.ofReal (r' ^ κ) := h_bound1
        rw [hN1, h_rhs_eq] at h_bound1'
        exact h_bound1'
      rw [h_n1_cast] at h'
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h'
    have h_real2 : (n2 : ℝ) ≤ C_A * (nA : ℝ) * (r' ^ κ) := by
      have h_n2_cast : ENat.toENNReal S2.encard = ENNReal.ofReal (n2 : ℝ) := by
        rw [h_encard2]
        exact enat_to_ennreal_ofReal n2
      have h' : ENat.toENNReal S2.encard ≤ ENNReal.ofReal (C_A * (nA : ℝ) * (r' ^ κ)) := by
        have h_bound2' : Nreal δ (A ∩ I2) ≤ ENNReal.ofReal C_A * Nreal δ A * ENNReal.ofReal (r' ^ κ) := h_bound2
        rw [hN2, h_rhs_eq] at h_bound2'
        exact h_bound2'
      rw [h_n2_cast] at h'
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h'
    have h_sum : (n0 + n1 + n2 : ℝ) ≤ 3 * C_A * (nA : ℝ) * (r' ^ κ) := by linarith
    have h_r'_pow : (r' ^ κ) ≤ (2 * r) ^ κ := by
      have h1 : 0 ≤ r' := by linarith
      have h2 : r' ≤ 2 * r := by linarith
      have h3 : 0 ≤ κ := by linarith
      gcongr
    have h_2r_pow : (2 * r) ^ κ = (2 : ℝ) ^ κ * r ^ κ := by
      rw [Real.mul_rpow (by norm_num) (by linarith)] <;> ring
    have hAJ_fin : (A_rep ∩ J).Finite := hA_rep_fin.subset (show A_rep ∩ J ⊆ A_rep from by simp)
    let mJ := hAJ_fin.toFinset.card
    have h_mJ_le : mJ ≤ n0 + n1 + n2 := by
      have h5 : (A_rep ∩ J).encard ≤ S0.encard + S1.encard + S2.encard :=
        le_trans h_rep_bound h_cover_num
      have h6 : (A_rep ∩ J).encard = ↑mJ := by
        have h7 : (A_rep ∩ J).encard = ↑hAJ_fin.toFinset.card :=
          hAJ_fin.encard_eq_coe_toFinset_card
        have h8 : hAJ_fin.toFinset.card = mJ := by rfl
        rw [h7, h8]
      have h7 : S0.encard + S1.encard + S2.encard = ↑(n0 + n1 + n2) := by
        rw [h_encard0, h_encard1, h_encard2] <;> norm_cast
      have h10 : (↑mJ : ENat) ≤ (↑(n0 + n1 + n2) : ENat) := by
        calc (↑mJ : ENat)
          = (A_rep ∩ J).encard := h6.symm
        _ ≤ S0.encard + S1.encard + S2.encard := h5
        _ = ↑(n0 + n1 + n2) := h7
      have h9 : mJ ≤ n0 + n1 + n2 := by
        exact_mod_cast h10
      exact h9
    have h_measure : μ J = (↑nA : ENNReal)⁻¹ * ↑mJ := by
      dsimp only [μ]
      rw [Measure.smul_apply]
      have h3 : MeasurableSet J := measurableSet_Icc
      have h1 : Measure.count.restrict A_rep J = Measure.count (A_rep ∩ J) := by
        rw [Measure.restrict_apply h3] <;> congr 1 <;> rw [Set.inter_comm]
      rw [h1]
      have h4 : Measure.count (A_rep ∩ J) = ↑mJ := by
        have h_mble : MeasurableSet (A_rep ∩ J) := hAJ_fin.measurableSet
        have h_count : Measure.count (A_rep ∩ J) = ↑hAJ_fin.toFinset.card :=
          Measure.count_apply_finite' hAJ_fin h_mble
        rw [h_count]
        <;> rfl
      have h6 : ENat.toENNReal A_rep.encard = ↑nA := by
        rw [h_card_A_rep]
        have h7 : ENat.toENNReal (↑nA : ENat) = ENNReal.ofReal (nA : ℝ) := enat_to_ennreal_ofReal nA
        have h8 : (↑nA : ENNReal) = ENNReal.ofReal (nA : ℝ) := by simp
        rw [h7, h8]
      rw [h4, h6] <;> rfl
    rw [h_measure]
    have h_final : (↑nA : ENNReal)⁻¹ * ↑mJ ≤ ENNReal.ofReal (C_frost * r ^ κ) := by
      have h5 : (↑nA : ENNReal)⁻¹ * ↑mJ ≤ (↑nA : ENNReal)⁻¹ * ↑(n0 + n1 + n2) := by
        gcongr
      have h_pos_nA : 0 < (nA : ℝ) := by exact_mod_cast h_nA_pos
      have h_inv : (↑nA : ENNReal)⁻¹ = ENNReal.ofReal ((nA : ℝ)⁻¹) := by
        have h7 : (↑nA : ENNReal) = ENNReal.ofReal (nA : ℝ) := by simp
        rw [h7, ENNReal.ofReal_inv_of_pos h_pos_nA]
      have h_coe : (↑(n0 + n1 + n2) : ENNReal) = ENNReal.ofReal ((n0 + n1 + n2 : ℝ)) := by norm_cast
      have h6 : (↑nA : ENNReal)⁻¹ * ↑(n0 + n1 + n2) =
          ENNReal.ofReal (((n0 + n1 + n2 : ℝ) / (nA : ℝ))) := by
        rw [h_inv, h_coe, ← ENNReal.ofReal_mul (by positivity)] <;> ring_nf
      rw [h6] at h5
      have h9 : ((n0 + n1 + n2 : ℝ) / (nA : ℝ)) ≤ C_frost * r ^ κ := by
        calc ((n0 + n1 + n2 : ℝ) / (nA : ℝ))
            ≤ (3 * C_A * (nA : ℝ) * (r' ^ κ)) / (nA : ℝ) := by gcongr
          _ = 3 * C_A * (r' ^ κ) := by field_simp [h_nA_pos.ne'] <;> ring
          _ ≤ 3 * C_A * ((2 * r) ^ κ) := by gcongr
          _ = 3 * C_A * (2 : ℝ) ^ κ * r ^ κ := by rw [h_2r_pow] <;> ring
          _ = C_frost * r ^ κ := by
            dsimp only [C_frost]
            <;> ring
      exact le_trans h5 ((ENNReal.ofReal_le_ofReal_iff (by positivity)).mpr h9)
    exact h_final
  have h_main : FiniteScaleIntervalBound δ κ C_frost μ :=
    ⟨hμ_prob, h_bound⟩
  exact ⟨μ, h_main, hμ_support_A, hμ_support_fin⟩

/-! ## Step 3: Finite-scale energy bound (proved in SupportFreeFrostman) -/

-- frostman_energy_finite_scale is imported from MyLeanRepo.SupportFreeFrostman

/-! ## Step 4: Assembly -/

/-- **Uniform product-measure bridge**: From a delta-set A, construct a
    probability measure on A^m with regularized Riesz energy bound.

    C_energy is chosen BEFORE δ and A and depends only on κ, m. -/
lemma product_measure_bridge_uniform
    {κ : ℝ} (hκ_pos : 0 < κ)
    {m : ℕ} (hm_pos : 0 < m) (hmκ : 1 < (m : ℝ) * κ) :
    ∃ (C_energy : ℝ), 0 < C_energy ∧
      ∀ (δ ε : ℝ) (A : Set ℝ),
        (hδ_pos : 0 < δ) → (hδ_le_one : δ ≤ 1) → (hε_nonneg : 0 ≤ ε) →
        (hA_sub : A ⊆ Set.Icc 1 2) →
        (hA_delta : IsRealDeltaSet δ κ (δ ^ (-ε)) A) →
        ∃ (ν : Measure (EuclideanSpace ℝ (Fin m)))
          (_ : IsProbabilityMeasure ν),
          ν.support ⊆ {x | ∀ i, x i ∈ A} ∧
          IsCompact ν.support ∧
          robust_projection_main.rieszEnergy (α := 1) (hδ := hδ_pos) ν ≤
            ENNReal.ofReal (C_energy * δ ^ (-ε * (m : ℝ))) := by
  -- C_Frost = 3 * 2^κ * δ^{-ε}
  -- C_prod = C_Frost^m = (3 * 2^κ)^m * δ^{-ε*m}
  -- C_energy = 1 + C_prod / (mκ - 1)  [but need to factor out δ^{-ε*m}]
  -- C_dim = (3 * 2^κ)^m
  -- C_energy = 1 + C_dim / (mκ - 1)
  let C_dim : ℝ := (3 * (2 : ℝ) ^ κ) ^ m
  let C_energy : ℝ := 1 + C_dim / ((m : ℝ) * κ - 1)
  have hC_energy_pos : 0 < C_energy := by
    dsimp only [C_energy, C_dim] <;> positivity
  refine ⟨C_energy, hC_energy_pos, ?_⟩
  intro δ ε A hδ_pos hδ_le_one hε_nonneg hA_sub hA_delta
  -- Step 1: Get μ_A from reps
  rcases finite_scale_frostman_from_reps
      hδ_pos hδ_le_one hκ_pos (by positivity) hA_sub hA_delta
    with ⟨μ_A, h_frost, h_supp_A, h_finite⟩
  -- Step 2: Product measure
  let ν : Measure (EuclideanSpace ℝ (Fin m)) :=
    ProductMeasureEnergy.productMeasure μ_A
  have hν_prob : ν Set.univ = 1 :=
    ProductMeasureEnergy.product_measure_univ h_frost.prob
  letI : IsProbabilityMeasure ν := ⟨hν_prob⟩
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (Fin m) ℝ
  letI : IsProbabilityMeasure μ_A := ⟨h_frost.prob⟩
  -- Support ⊆ A^m via closed-set argument:
  -- S := {x | ∀ i, x i ∈ μ_A.support} is closed (finite support → closed),
  -- and ν(Sᶜ) = 0, so ν.support ⊆ S ⊆ {x | ∀ i, x i ∈ A}.
  have h_suppA_closed : IsClosed μ_A.support := h_finite.isClosed
  let S : Set (EuclideanSpace ℝ (Fin m)) := {x | ∀ i, x i ∈ μ_A.support}
  have hS_closed : IsClosed S := by
    have h1 : S = ⋂ i : Fin m, {x | x i ∈ μ_A.support} := by
      ext x; simp [S] <;> aesop
    rw [h1]
    apply isClosed_iInter
    intro i
    have h_cont : Continuous (fun x : EuclideanSpace ℝ (Fin m) => x i) := by fun_prop
    exact h_suppA_closed.preimage h_cont
  have h_cyl_zero : ∀ (i : Fin m), ν {x : EuclideanSpace ℝ (Fin m) | x i ∉ μ_A.support} = 0 := by
    intro i
    have h_msupp_compl : μ_A (μ_A.supportᶜ) = 0 :=
      MeasureTheory.Measure.measure_compl_support (μ := μ_A)
    let V : Set (EuclideanSpace ℝ (Fin m)) := {x | x i ∉ μ_A.support}
    let U : Set (Fin m → ℝ) := {f | f i ∉ μ_A.support}
    have hV_meas : MeasurableSet V := by
      have h_cont : Continuous (fun x : EuclideanSpace ℝ (Fin m) => x i) := by fun_prop
      have h_open_compl : IsOpen (μ_A.supportᶜ) := h_suppA_closed.isOpen_compl
      have h : IsOpen V := h_open_compl.preimage h_cont
      exact h.measurableSet
    have hU_meas : MeasurableSet U := by
      have h' : IsOpen (μ_A.supportᶜ) := h_suppA_closed.isOpen_compl
      have h_cont : Continuous (fun f : Fin m → ℝ => f i) := continuous_apply i
      have h_open : IsOpen U := h'.preimage h_cont
      exact h_open.measurableSet
    have h_preimage : e.symm ⁻¹' V = U := by
      ext f; simp [V, U, e] <;> rfl
    have h_me : Measurable (e.symm) := e.symm.continuous.measurable
    have h_eq1 : ν V = MeasureTheory.Measure.pi (fun (_ : Fin m) => μ_A) U := by
      have h : ν V = MeasureTheory.Measure.pi (fun (_ : Fin m) => μ_A) (e.symm ⁻¹' V) :=
        Measure.map_apply_of_aemeasurable h_me.aemeasurable hV_meas
      rw [h, h_preimage]
    rw [h_eq1]
    let g : Fin m → Set ℝ := fun j => if j = i then μ_A.supportᶜ else Set.univ
    have hU_eq : U = Set.pi Set.univ g := by
      ext f; simp [U, g] <;> aesop
    rw [hU_eq]
    rw [MeasureTheory.Measure.pi_pi (μ := fun (_ : Fin m) => μ_A) g]
    have h_prod : ∏ j : Fin m, μ_A (g j) = μ_A (μ_A.supportᶜ) := by
      have h2 : ∀ (j : Fin m), j ∈ Finset.univ → j ≠ i → μ_A (g j) = 1 := by
        intro j _ hne
        have hgj : g j = Set.univ := by
          dsimp only [g]
          rw [if_neg hne]
        rw [hgj, h_frost.prob] <;> norm_num
      have h1 : ∏ j : Fin m, μ_A (g j) = μ_A (g i) :=
        Finset.prod_eq_single_of_mem i (Finset.mem_univ i) h2
      rw [h1]
      have hgi : g i = μ_A.supportᶜ := by
        dsimp only [g]
        rw [if_pos rfl]
      rw [hgi]
    rw [h_prod, h_msupp_compl] <;> simp
  have h_Scompl : ν Sᶜ = 0 := by
    have h2 : Sᶜ = ⋃ i : Fin m, {x : EuclideanSpace ℝ (Fin m) | x i ∉ μ_A.support} := by
      ext x; simp [S] <;> aesop
    rw [h2]
    have h3 : ν (⋃ i : Fin m, {x | x i ∉ μ_A.support}) ≤
        ∑ i : Fin m, ν {x | x i ∉ μ_A.support} := by
      have h := MeasureTheory.measure_iUnion_le (μ := ν) (s := fun i : Fin m => {x | x i ∉ μ_A.support})
      simpa [tsum_fintype] using h
    have h4 : ∑ i : Fin m, ν {x | x i ∉ μ_A.support} = 0 := by
      rw [Finset.sum_congr rfl (fun i _ => h_cyl_zero i)] <;> simp
    rw [h4] at h3
    exact le_zero_iff.mp h3
  have h_supp_in_S : ν.support ⊆ S := by
    have h9 : Sᶜ ⊆ ν.supportᶜ :=
      MeasureTheory.Measure.subset_compl_support_of_isOpen hS_closed.isOpen_compl h_Scompl
    intro x hx
    by_contra h13
    have h14 : x ∈ Sᶜ := h13
    have h15 : x ∈ ν.supportᶜ := h9 h14
    exact h15 hx
  have h_S_sub_A : S ⊆ {x | ∀ i, x i ∈ A} := by
    intro x hx
    intro i
    have h9 : x i ∈ μ_A.support := hx i
    exact h_supp_A h9
  have h_supp : ν.support ⊆ {x | ∀ i, x i ∈ A} :=
    subset_trans h_supp_in_S h_S_sub_A
  -- Compact support: ν.support is closed, subset of compact (Icc 1 2)^m
  have h_supp_closed : IsClosed ν.support := MeasureTheory.Measure.isClosed_support
  have h_box : {x : EuclideanSpace ℝ (Fin m) | ∀ i, x i ∈ A} ⊆
      {x | ∀ i, x i ∈ Set.Icc (1 : ℝ) 2} := by
    intro x hx
    intro i
    exact hA_sub (hx i)
  have h_supp_in_box : ν.support ⊆ {x | ∀ i, x i ∈ Set.Icc (1 : ℝ) 2} :=
    subset_trans h_supp h_box
  have h_compact_box : IsCompact {x : EuclideanSpace ℝ (Fin m) | ∀ i, x i ∈ Set.Icc (1 : ℝ) 2} := by
    have h1 : IsCompact (Set.pi Set.univ (fun i : Fin m => Set.Icc (1 : ℝ) 2)) :=
      isCompact_univ_pi (fun i => isCompact_Icc)
    have h2 : {x : EuclideanSpace ℝ (Fin m) | ∀ i, x i ∈ Set.Icc (1 : ℝ) 2} =
        (fun x : EuclideanSpace ℝ (Fin m) => e x) ⁻¹' (Set.pi Set.univ (fun i : Fin m => Set.Icc (1 : ℝ) 2)) := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi]
      <;> rfl
    rw [h2]
    have h3 : (fun x : EuclideanSpace ℝ (Fin m) => e x) ⁻¹' (Set.pi Set.univ (fun i : Fin m => Set.Icc (1 : ℝ) 2)) =
        e.symm '' (Set.pi Set.univ (fun i : Fin m => Set.Icc (1 : ℝ) 2)) := by
      ext z
      simp [e, Set.mem_preimage, Set.mem_image]
      <;> aesop
    rw [h3]
    exact h1.image e.symm.continuous
  have h_compact : IsCompact ν.support :=
    IsCompact.of_isClosed_subset h_compact_box h_supp_closed h_supp_in_box
  -- Product ball bound: ν(ball x r) ≤ C_dim * δ^{-ε*m} * r^{mκ}
  have h_prod_bound : ∀ (x : EuclideanSpace ℝ (Fin m)) (r : ℝ),
      δ ≤ r → r ≤ 1 →
      ν (Metric.ball x r) ≤
        ENNReal.ofReal (C_dim * δ ^ (-ε * (m : ℝ)) * r ^ ((m : ℝ) * κ)) := by
    intro x r hr_ge_delta hr_le_one
    have h1 := product_ball_bound_support_free
      (hδ_pos := hδ_pos) (hκ_pos := hκ_pos) (hC_pos := by positivity)
      (h := h_frost) (m := m) (x := x) (r := r)
      hr_ge_delta hr_le_one
    have hC_frost : (3 * (2 : ℝ) ^ κ * δ ^ (-ε)) ^ m =
        C_dim * δ ^ (-ε * (m : ℝ)) := by
      have h2 : (3 * (2 : ℝ) ^ κ * δ ^ (-ε)) ^ m =
          (3 * (2 : ℝ) ^ κ) ^ m * (δ ^ (-ε)) ^ m := by
        rw [mul_pow]
      rw [h2]
      have h3 : (δ ^ (-ε)) ^ m = δ ^ (-ε * (m : ℝ)) := by
        have h4 : (δ ^ (-ε)) ^ m = (δ ^ (-ε)) ^ (m : ℝ) := by norm_cast
        rw [h4]
        rw [Real.rpow_mul hδ_pos.le] <;> ring
      rw [h3] <;> rfl
    rw [hC_frost] at h1
    exact h1
  -- Step 3: Energy bound
  have h_energy : ∀ (x : EuclideanSpace ℝ (Fin m)),
      ∫⁻ (y : EuclideanSpace ℝ (Fin m)),
        ENNReal.ofReal ((max (dist x y) δ) ^ (-1 : ℝ)) ∂ν ≤
      ENNReal.ofReal (1 + (C_dim * δ ^ (-ε * (m : ℝ))) / ((m : ℝ) * κ - 1)) := by
    intro x
    exact frostman_energy_finite_scale
      (hν_prob := hν_prob) (hs := hmκ)
      (hC'_pos := by positivity) (hδ := hδ_pos) (hδ_le_one := hδ_le_one)
      (hFrost := h_prod_bound) x
  -- Integrate over x
  have h_main : robust_projection_main.rieszEnergy (α := 1) (hδ := hδ_pos) ν ≤
      ENNReal.ofReal (C_energy * δ ^ (-ε * (m : ℝ))) := by
    dsimp only [robust_projection_main.rieszEnergy]
    have h_ae : ∀ᵐ (x : EuclideanSpace ℝ (Fin m)) ∂ν,
        (∫⁻ (y : EuclideanSpace ℝ (Fin m)),
          ENNReal.ofReal ((max (dist x y) δ) ^ (-1 : ℝ)) ∂ν) ≤
        ENNReal.ofReal (1 + C_dim * δ ^ (-ε * (m : ℝ)) / ((m : ℝ) * κ - 1)) :=
      Filter.Eventually.of_forall h_energy
    have h_mono : ∫⁻ (x : EuclideanSpace ℝ (Fin m)),
        ∫⁻ (y : EuclideanSpace ℝ (Fin m)),
          ENNReal.ofReal ((max (dist x y) δ) ^ (-1 : ℝ)) ∂ν ∂ν ≤
        ∫⁻ (x : EuclideanSpace ℝ (Fin m)),
          ENNReal.ofReal (1 + C_dim * δ ^ (-ε * (m : ℝ)) / ((m : ℝ) * κ - 1)) ∂ν :=
      MeasureTheory.lintegral_mono_ae h_ae
    have h_const : ∫⁻ (x : EuclideanSpace ℝ (Fin m)),
        ENNReal.ofReal (1 + C_dim * δ ^ (-ε * (m : ℝ)) / ((m : ℝ) * κ - 1)) ∂ν =
      ENNReal.ofReal (1 + C_dim * δ ^ (-ε * (m : ℝ)) / ((m : ℝ) * κ - 1)) := by
      rw [MeasureTheory.lintegral_const, hν_prob] <;> simp
    have h_final : ENNReal.ofReal (1 + C_dim * δ ^ (-ε * (m : ℝ)) / ((m : ℝ) * κ - 1)) ≤
        ENNReal.ofReal (C_energy * δ ^ (-ε * (m : ℝ))) := by
      have h9 : 1 + C_dim * δ ^ (-ε * (m : ℝ)) / ((m : ℝ) * κ - 1) ≤
          C_energy * δ ^ (-ε * (m : ℝ)) := by
        dsimp only [C_energy]
        have h12 : 0 ≤ ε * (m : ℝ) := by positivity
        have h13 : 1 ≤ δ⁻¹ := by
          have h : δ ≤ 1 := hδ_le_one
          have h' : 0 < δ := hδ_pos
          have : δ⁻¹ ≥ 1 := by
            rw [inv_eq_one_div]
            apply one_le_one_div h'
            exact h
          exact this
        have h11 : (1 : ℝ) ≤ δ ^ (-ε * (m : ℝ)) := by
          have h14 : δ ^ (-ε * (m : ℝ)) = (δ⁻¹) ^ (ε * (m : ℝ)) := by
            have h15 : δ ^ (-ε * (m : ℝ)) = (δ ^ (ε * (m : ℝ)))⁻¹ := by
              have h16 : (-ε * (m : ℝ)) = -(ε * (m : ℝ)) := by ring
              rw [h16]
              rw [Real.rpow_neg hδ_pos.le]
            have h17 : (δ⁻¹) ^ (ε * (m : ℝ)) = (δ ^ (ε * (m : ℝ)))⁻¹ := by
              rw [Real.inv_rpow hδ_pos.le]
            rw [h15, h17]
          rw [h14]
          exact Real.one_le_rpow h13 h12
        have h_pos_denom : 0 < (m : ℝ) * κ - 1 := by linarith
        have h_ineq : 1 + C_dim * δ ^ (-ε * (m : ℝ)) / ((m : ℝ) * κ - 1) ≤
            (1 + C_dim / ((m : ℝ) * κ - 1)) * δ ^ (-ε * (m : ℝ)) := by
          have hX : (1 : ℝ) ≤ δ ^ (-ε * (m : ℝ)) := h11
          have hD_pos : 0 < C_dim / ((m : ℝ) * κ - 1) := by positivity
          have h : 1 + C_dim * δ ^ (-ε * (m : ℝ)) / ((m : ℝ) * κ - 1) ≤
              δ ^ (-ε * (m : ℝ)) + C_dim * δ ^ (-ε * (m : ℝ)) / ((m : ℝ) * κ - 1) := by
            linarith
          have h2 : δ ^ (-ε * (m : ℝ)) + C_dim * δ ^ (-ε * (m : ℝ)) / ((m : ℝ) * κ - 1) =
              (1 + C_dim / ((m : ℝ) * κ - 1)) * δ ^ (-ε * (m : ℝ)) := by ring
          rw [h2] at h
          exact h
        exact h_ineq
      exact ENNReal.ofReal_le_ofReal h9
    calc _ ≤ ENNReal.ofReal (1 + C_dim * δ ^ (-ε * (m : ℝ)) / ((m : ℝ) * κ - 1)) :=
        h_mono.trans_eq h_const
    _ ≤ ENNReal.ofReal (C_energy * δ ^ (-ε * (m : ℝ))) := h_final
  exact ⟨ν, inferInstance, h_supp, h_compact, h_main⟩

end WeakTwoEndsSumProduct
