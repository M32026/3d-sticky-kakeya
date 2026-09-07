module

/-
# Box Bridge Lemmas

Bridge between Phase0 V2 popularity outputs and the quantitative box theorem.
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.FrostmanFromDeltaSet
public import MyLeanRepo.ProductLikeIncidence.Phase0.QuantitativeBox
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ProductLikeIncidence ENNReal Set Bornology Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-! ## Normalized counting measure conversion -/

/-- Convert ENNReal multiplicity bound to normalized counting measure bound. -/
lemma normalized_measure_multiplicity
    {Y S : Set ℝ} (hY_fin : Y.Finite) (hY_nonempty : Y.Nonempty)
    (hS_sub : S ⊆ Y) (hS_fin : S.Finite)
    {c : ℝ} (hc_nonneg : 0 ≤ c)
    (h_mult : ENat.toENNReal S.encard ≥ ENNReal.ofReal (c / 2) * ENat.toENNReal Y.encard) :
    ENNReal.ofReal (c / 2) ≤ (normalizedCountingMeasure Y hY_fin hY_nonempty) S := by
  let μ : Measure ℝ := normalizedCountingMeasure Y hY_fin hY_nonempty
  have hY_encard_pos : 0 < ENat.toENNReal Y.encard := by
    have h : 0 < Y.encard := Set.encard_pos.mpr hY_nonempty
    exact_mod_cast h
  have hY_encard_ne_zero : ENat.toENNReal Y.encard ≠ 0 := ne_of_gt hY_encard_pos
  have hY_encard_ne_top : ENat.toENNReal Y.encard ≠ ⊤ := by
    exact_mod_cast hY_fin.encard_lt_top.ne
  have hms : MeasurableSet S := hS_fin.measurableSet
  have h_count : Measure.count.restrict Y S = ENat.toENNReal S.encard := by
    rw [Measure.restrict_apply hms]
    have h2 : S ∩ Y = S := Set.inter_eq_left.mpr hS_sub
    rw [h2]
    exact Measure.count_apply hms
  have hμS : μ S = (ENat.toENNReal Y.encard)⁻¹ * ENat.toENNReal S.encard := by
    dsimp only [μ, normalizedCountingMeasure]
    rw [Measure.smul_apply, h_count]
    <;> rfl
  rw [hμS]
  have h3 : (ENat.toENNReal Y.encard)⁻¹ * ENat.toENNReal S.encard ≥
      (ENat.toENNReal Y.encard)⁻¹ * (ENNReal.ofReal (c / 2) * ENat.toENNReal Y.encard) := by
    gcongr
  have h4 : (ENat.toENNReal Y.encard)⁻¹ * (ENNReal.ofReal (c / 2) * ENat.toENNReal Y.encard) =
      ENNReal.ofReal (c / 2) := by
    have h5 : (ENat.toENNReal Y.encard)⁻¹ * (ENNReal.ofReal (c / 2) * ENat.toENNReal Y.encard) =
        ENNReal.ofReal (c / 2) * ((ENat.toENNReal Y.encard)⁻¹ * ENat.toENNReal Y.encard) := by
      ring
    rw [h5, ENNReal.inv_mul_cancel hY_encard_ne_zero hY_encard_ne_top]
    <;> ring
  rw [h4] at h3
  exact h3

/-! ## Grid diameter lemma -/

/-- A finite subset of the δ-grid with at least 2 points has diameter ≥ δ. -/
lemma grid_diam_ge_delta_of_ncard_ge_two
    {δ : ℝ} {S : Set ℝ} (hδ_pos : 0 < δ)
    (hS_sub : S ⊆ productLikeIntegerGrid δ)
    (hS_fin : S.Finite) (hS_card : 2 ≤ S.ncard) :
    δ ≤ (hS_fin.toFinset).max' (by
      have h : 0 < (hS_fin.toFinset).card := by
        have h' : S.ncard = (hS_fin.toFinset).card := Set.ncard_eq_toFinset_card S (hs := hS_fin)
        rw [← h'] <;> omega
      exact Finset.card_pos.mp h) -
      (hS_fin.toFinset).min' (by
      have h : 0 < (hS_fin.toFinset).card := by
        have h' : S.ncard = (hS_fin.toFinset).card := Set.ncard_eq_toFinset_card S (hs := hS_fin)
        rw [← h'] <;> omega
      exact Finset.card_pos.mp h) := by
  let Sf : Finset ℝ := hS_fin.toFinset
  have hSf_card : 2 ≤ Sf.card := by
    have h_eq : S.ncard = Sf.card := Set.ncard_eq_toFinset_card S (hs := hS_fin)
    omega
  have hSf_nonempty : Sf.Nonempty := by
    have h : 0 < Sf.card := by linarith
    exact Finset.card_pos.mp h
  set a : ℝ := Sf.min' hSf_nonempty with ha_def
  set b : ℝ := Sf.max' hSf_nonempty with hb_def
  have ha_in : a ∈ S := by
    have h : a ∈ Sf := Finset.min'_mem Sf hSf_nonempty
    simpa [Sf] using h
  have hb_in : b ∈ S := by
    have h : b ∈ Sf := Finset.max'_mem Sf hSf_nonempty
    simpa [Sf] using h
  have ha_le_b : a ≤ b := Finset.min'_le Sf b (Finset.max'_mem Sf hSf_nonempty)
  have h_a_lt_b : a < b := by
    by_contra h
    have h_eq : a = b := by linarith
    have h_all : ∀ x ∈ Sf, x = a := by
      intro x hx
      have h1 : a ≤ x := Finset.min'_le Sf x hx
      have h2 : x ≤ b := Finset.le_max' Sf x hx
      have h2' : x ≤ a := by linarith [h_eq, h2]
      linarith
    have h_singleton : Sf = {a} := by
      ext x
      simp only [Finset.mem_singleton]
      constructor
      · intro hx
        exact h_all x hx
      · intro hx
        rw [hx]
        exact Finset.min'_mem Sf hSf_nonempty
    have h_card1 : Sf.card = 1 := by
      rw [h_singleton] <;> simp
    rw [h_card1] at hSf_card
    <;> norm_num at hSf_card
  rcases hS_sub ha_in with ⟨ka, ha_eq⟩
  rcases hS_sub hb_in with ⟨kb, hb_eq⟩
  have h1 : δ * (ka : ℝ) < δ * (kb : ℝ) := by
    have h2 : a < b := h_a_lt_b
    have h3 : a = δ * (ka : ℝ) := ha_eq
    have h4 : b = δ * (kb : ℝ) := hb_eq
    rw [h3, h4] at h2
    exact h2
  have h2 : (ka : ℝ) < (kb : ℝ) := by
    have h21 : δ * (ka : ℝ) < δ * (kb : ℝ) := h1
    nlinarith
  have h2' : ka < kb := by exact_mod_cast h2
  have h_k_diff : 1 ≤ kb - ka := by omega
  have h_main : δ ≤ b - a := by
    have h_goal : δ ≤ δ * ((kb : ℝ) - (ka : ℝ)) := by
      have h3 : (1 : ℝ) ≤ (kb : ℝ) - (ka : ℝ) := by exact_mod_cast h_k_diff
      have h4 : δ * 1 ≤ δ * ((kb : ℝ) - (ka : ℝ)) := by gcongr
      linarith
    have h5 : δ * ((kb : ℝ) - (ka : ℝ)) = b - a := by
      have h6 : δ * ((kb : ℝ) - (ka : ℝ)) = δ * (kb : ℝ) - δ * (ka : ℝ) := by ring
      rw [h6, hb_eq, ha_eq] <;> ring
    rw [h5] at h_goal
    exact h_goal
  exact h_main

/-! ## Cardinality ≥ 2 from multiplicity -/

/-- If |S| ≥ (c/2)·|Y| in ENNReal and c·|Y| > 2, then |S| ≥ 2. -/
lemma ncard_ge_two_from_multiplicity
    {Y S : Set ℝ} (hY_fin : Y.Finite) (hS_fin : S.Finite)
    {c : ℝ} (hc_pos : 0 < c)
    (h_mult : ENat.toENNReal S.encard ≥ ENNReal.ofReal (c / 2) * ENat.toENNReal Y.encard)
    (h_large : 2 < c * (Y.ncard : ℝ)) :
    2 ≤ S.ncard := by
  by_contra h
  have h1 : S.ncard ≤ 1 := by linarith
  have hS_encard : S.encard = ↑(S.ncard) := by
    rw [Set.Finite.encard_eq_coe_toFinset_card hS_fin, Set.ncard_eq_toFinset_card S (hs := hS_fin)]
    <;> rfl
  have hY_encard : Y.encard = ↑(Y.ncard) := by
    rw [Set.Finite.encard_eq_coe_toFinset_card hY_fin, Set.ncard_eq_toFinset_card Y (hs := hY_fin)]
    <;> rfl
  rw [hS_encard, hY_encard] at h_mult
  have h2 : (↑(S.ncard) : ENNReal) ≤ 1 := by exact_mod_cast h1
  have h3 : ENNReal.ofReal (c / 2) * (↑(Y.ncard) : ENNReal) ≤ (↑(S.ncard) : ENNReal) := h_mult
  have h4 : ENNReal.ofReal (c / 2) * (↑(Y.ncard) : ENNReal) ≤ 1 := le_trans h3 h2
  have h_cast : (↑(Y.ncard) : ENNReal) = ENNReal.ofReal (Y.ncard : ℝ) := by norm_cast
  have h5 : ENNReal.ofReal ((c / 2) * (Y.ncard : ℝ)) ≤ 1 := by
    have h_eq : ENNReal.ofReal (c / 2) * (↑(Y.ncard) : ENNReal) = ENNReal.ofReal ((c / 2) * (Y.ncard : ℝ)) := by
      rw [h_cast, ← ENNReal.ofReal_mul (by positivity)] <;> rfl
    rw [h_eq] at h4
    exact h4
  have h6 : 0 ≤ (c / 2) * (Y.ncard : ℝ) := by positivity
  have h7 : (c / 2) * (Y.ncard : ℝ) ≤ 1 := by
    by_contra h8
    have h9 : 1 < (c / 2) * (Y.ncard : ℝ) := by linarith
    have h_pos2 : 0 < (c / 2) * (Y.ncard : ℝ) := by linarith
    have h10 : ENNReal.ofReal 1 < ENNReal.ofReal ((c / 2) * (Y.ncard : ℝ)) := by
      exact (ofReal_lt_ofReal_iff h_pos2).mpr h9
    have h11 : (1 : ENNReal) < ENNReal.ofReal ((c / 2) * (Y.ncard : ℝ)) := by
      simpa using h10
    exact not_le.mpr h11 h5
  linarith

/-! ## Power of two -/

private lemma pow2_ge_nat (n : ℕ) : (n : ℝ) ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h2 : 1 ≤ (2 : ℝ) ^ n := by
      have h3 : ∀ m : ℕ, 1 ≤ (2 : ℝ) ^ m := by
        intro m
        induction m with
        | zero => norm_num
        | succ m ih => simp [pow_succ] at * <;> nlinarith
      exact h3 n
    calc ((n + 1 : ℕ) : ℝ)
      = (n : ℝ) + 1 := by simp
    _ ≤ (2 : ℝ) ^ n + 1 := by linarith
    _ ≤ (2 : ℝ) ^ n + (2 : ℝ) ^ n := by linarith
    _ = (2 : ℝ) ^ (n + 1) := by ring

private lemma exists_pow2_ge (R : ℝ) (hR_pos : 0 < R) : ∃ (n : ℕ), R ≤ (2 : ℝ) ^ n := by
  by_cases hR_le_one : R ≤ 1
  · exact ⟨0, by norm_num <;> linarith⟩
  · obtain ⟨k, hk⟩ := exists_nat_ge R
    have hk' : (k : ℝ) ≥ R := by exact_mod_cast hk
    have h_pow_ge : (k : ℝ) ≤ (2 : ℝ) ^ k := pow2_ge_nat k
    exact ⟨k, by linarith⟩

/-- **Power-of-two rounding**: there exists k such that R ≤ 2^k < 2·max(1,R).

    The rounding costs at most a factor of 2, absorbable by qAbsorb. -/
lemma exists_pow2_rounding (R : ℝ) (hR_pos : 0 < R) :
    ∃ (k : ℕ), R ≤ (2 : ℝ) ^ k ∧ (2 : ℝ) ^ k < 2 * max 1 R := by
  let P : ℕ → Prop := fun n => R ≤ (2 : ℝ) ^ n
  have h_exists : ∃ n, P n := exists_pow2_ge R hR_pos
  let k : ℕ := Nat.find h_exists
  have hk : P k := Nat.find_spec h_exists
  have h_min : ∀ m < k, ¬ P m := fun m hm => Nat.find_min h_exists hm
  by_cases hR_le_one : R ≤ 1
  · refine ⟨0, by simpa [P] using hR_le_one, ?_⟩
    have h_max : max 1 R = 1 := by rw [max_eq_left] <;> linarith
    rw [h_max] <;> norm_num
  · have hR_gt_one : 1 < R := by linarith
    have hk_pos : 0 < k := by
      by_contra h
      have h' : k = 0 := by omega
      have h'' : P 0 := by
        simpa [h'] using hk
      have : R ≤ 1 := by simpa [P] using h''
      linarith
    have h_k1 : ¬ P (k - 1) := h_min (k - 1) (by omega)
    have h_lt : (2 : ℝ) ^ (k - 1) < R := by simpa [P] using h_k1
    have h_eq : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ (k - 1) := by
      have h : k = (k - 1) + 1 := by omega
      rw [h]
      simp [pow_succ] <;> ring
    refine ⟨k, hk, ?_⟩
    rw [h_eq]
    have h_max : max 1 R = R := by rw [max_eq_right] <;> linarith
    rw [h_max]
    have h_goal : 2 * (2 : ℝ) ^ (k - 1) < 2 * R := by gcongr
    exact h_goal

end ProductLikeIncidence.ProductReduction
