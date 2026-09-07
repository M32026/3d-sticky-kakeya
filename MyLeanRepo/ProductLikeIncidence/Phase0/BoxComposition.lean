module

/-
# Box Composition for Phase0 V2

Composes the quantitative box theorem with bridge lemmas to produce a
uniform power-of-two box radius Rpow such that Pbar = ⋃₀ Tbar ⊆ [-Rpow,Rpow]^2.

## Main lemma

`phase0_box_composition`: Given V2 popularity/refinement outputs, produces
Rpow = 2^k with Pbar ⊆ box(Rpow) and Rpow ≤ 2·(1 + R_box + 6δ) where
R_box = (1+12δ) / ((c/2)/(3·C·2^τ))^(1/τ).

## Whiteprint node
Helper for `phase0_quantitative_box` integration.
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.FrostmanFromDeltaSet
public import MyLeanRepo.ProductLikeIncidence.Phase0.QuantitativeBox
public import MyLeanRepo.ProductLikeIncidence.Phase0.BoxBridge
public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ProductLikeIncidence ENNReal Set Bornology Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- **Phase0 box composition**: From V2 outputs, produce a power-of-two box
    containing the entire popular parameter set Pbar = ⋃₀ Tbar.

    Given:
    - Y is a (δ, τ, C)-set on the δ-grid
    - For each Q ∈ Tbar, S_Q = {y ∈ Y | Q ∈ U_y y} has |S_Q| ≥ (c/2)|Y|
    - V2 incidence: ∀ y ∈ Y, ∀ p ∈ ⋃₀(Tbar ∩ U_y y), ∃x ∈ X_y, |p₀y+p₁-x| ≤ 4δ
    - c·|Y| > 2 (ensures |S_Q| ≥ 2, hence diam ≥ δ)

    Produces Rpow = 2^k such that:
    - ∀ p ∈ ⋃₀ Tbar, |p₀| ≤ Rpow ∧ |p₁| ≤ Rpow
    - Rpow < 2·max(1, 1 + R_box + 6δ)
    where R_box = (1+12δ) / ((c/2)/(3·C·2^τ))^(1/τ).

    The factor 2 from power-of-two rounding is absorbable by qAbsorb. -/
lemma phase0_box_composition
    {δ τ C c : ℝ}
    {Y : Set ℝ} {X : ℝ → Set ℝ}
    {Tbar : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    {U_y : ℝ → Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales) (hδ_le_one : δ ≤ 1)
    (hτ_pos : 0 < τ) (hC_pos : 0 < C) (hc_pos : 0 < c)
    (hY_grid : Y ⊆ productLikeUnitGrid δ)
    (hY_delta : IsProductLikeRealDeltaSCSet δ τ C Y)
    (hXy_sub : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ)
    -- Multiplicity: each Q ∈ Tbar appears in ≥ (c/2)|Y| fibers
    (h_mult : ∀ Q ∈ Tbar,
      ENat.toENNReal ({y ∈ Y | Q ∈ U_y y}.encard) ≥
        ENNReal.ofReal (c / 2) * ENat.toENNReal Y.encard)
    -- Tbar consists of dyadic cubes (from V2 construction)
    (hTbar_dyadic : ∀ Q ∈ Tbar, Q ∈ dyadicCubes 2 δ)
    -- Incidence from V2
    (h_incidence : ∀ y ∈ Y, ∀ p ∈ ⋃₀ (Tbar ∩ U_y y),
      ∃ (x : ℝ), x ∈ X y ∧ |p 0 * y + p 1 - x| ≤ 4 * δ)
    -- Large enough Y for cardinality ≥ 2
    (h_large_Y : 2 < c * (Y.ncard : ℝ)) :
    ∃ (Rpow : ℝ), (∃ (k : ℕ), Rpow = (2 : ℝ) ^ k) ∧
      (∀ (p : EuclideanSpace ℝ (Fin 2)), p ∈ ⋃₀ Tbar →
        |p 0| ≤ Rpow ∧ |p 1| ≤ Rpow) ∧
      Rpow < 2 * max 1 (1 + (1 + 12 * δ) / (((c / 2) / (3 * C * 2 ^ τ)) ^ (1 / τ)) + 6 * δ) := by
  -- Get Frostman measure from delta-set (with point-mass formula)
  obtain ⟨μ, hFrost, hsupport, hpoint⟩ :=
    frostman_from_delta_set hδ_pos hδ_dyadic hδ_le_one hτ_pos le_rfl hC_pos hY_grid hY_delta
  have hY_fin : Y.Finite := Set.Finite.subset (productLikeUnitGrid_finite hδ_pos) hY_grid
  have hY_nonempty : Y.Nonempty := by
    rcases hY_delta.2.1 with ⟨x, hx⟩
    exact ⟨x 0, hx⟩
  have hY_encard_ne_zero : ENat.toENNReal Y.encard ≠ 0 := by
    have h : 0 < Y.encard := Set.encard_pos.mpr hY_nonempty
    have h' : 0 < ENat.toENNReal Y.encard := by exact_mod_cast h
    exact ne_of_gt h'
  have hY_encard_ne_top : ENat.toENNReal Y.encard ≠ ⊤ := by
    exact_mod_cast hY_fin.encard_lt_top.ne
  have hY_ncard_pos : 0 < Y.ncard := by
    have h : 0 < Y.ncard := by exact Nonempty.ncard_pos hY_fin hY_nonempty
    exact h
  have hY_encard_real : ENat.toENNReal Y.encard = ENNReal.ofReal (Y.ncard : ℝ) := by
    rw [Set.Finite.encard_eq_coe_toFinset_card hY_fin, Set.ncard_eq_toFinset_card Y (hs := hY_fin)]
    <;> norm_cast
  let C_F : ℝ := 3 * C * 2 ^ τ
  have hC_F_pos : 0 < C_F := by positivity
  let c' : ℝ := c / 2
  have hc'_pos : 0 < c' := by
    dsimp only [c']
    exact half_pos hc_pos
  let d : ℝ := (c' / C_F) ^ (1 / τ)
  have hd_pos : 0 < d := by positivity
  let R_box : ℝ := (1 + 12 * δ) / d
  -- Helper: μ(S) = |S| / |Y| for finite S ⊆ Y
  have h_measure_finite : ∀ (S : Set ℝ), S ⊆ Y → S.Finite →
      μ S = ENat.toENNReal S.encard * (ENat.toENNReal Y.encard)⁻¹ := by
    intro S hS_sub hS_fin
    have h1 : μ S = ∑ y ∈ hS_fin.toFinset, μ {y} := by
      let Sf : Finset ℝ := hS_fin.toFinset
      have h2 : (S : Set ℝ) = (Sf : Set ℝ) := by simp [Sf]
      have h3 : μ S = μ (Sf : Set ℝ) := by
        congr
        <;> exact h2
      rw [h3]
      have h4 : μ (Sf : Set ℝ) = ∑ y ∈ Sf, μ {y} := by
        exact Eq.symm sum_measure_singleton
      exact h4
    rw [h1]
    have h3 : ∑ y ∈ hS_fin.toFinset, μ {y} = ∑ y ∈ hS_fin.toFinset, ENNReal.ofReal (1 / (Y.ncard : ℝ)) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hpoint y (hS_sub (by simpa using hy))
    rw [h3]
    have h4 : ∑ y ∈ hS_fin.toFinset, ENNReal.ofReal (1 / (Y.ncard : ℝ)) =
        (hS_fin.toFinset.card : ENNReal) * ENNReal.ofReal (1 / (Y.ncard : ℝ)) := by
      simp [Finset.sum_const] <;> ring
    rw [h4]
    have h5 : (hS_fin.toFinset.card : ENNReal) = ENat.toENNReal S.encard := by
      rw [Set.Finite.encard_eq_coe_toFinset_card hS_fin] <;> norm_cast
    rw [h5]
    have h6 : ENNReal.ofReal (1 / (Y.ncard : ℝ)) = (ENat.toENNReal Y.encard)⁻¹ := by
      rw [hY_encard_real]
      have h_pos' : 0 < (Y.ncard : ℝ) := by exact_mod_cast hY_ncard_pos
      have h8 : (1 / (Y.ncard : ℝ)) = (Y.ncard : ℝ)⁻¹ := by
        field_simp [h_pos'.ne'] <;> ring
      rw [h8]
      exact ENNReal.ofReal_inv_of_pos h_pos'
    rw [h6] <;> ring
  -- Per-cube box bound
  have h_per_cube : ∀ Q ∈ Tbar, ∀ (p : EuclideanSpace ℝ (Fin 2)), p ∈ Q →
      |p 0| ≤ R_box ∧ |p 1| ≤ 1 + R_box + 6 * δ := by
    intro Q hQ
    let S_Q : Set ℝ := {y ∈ Y | Q ∈ U_y y}
    have hS_Q_sub : S_Q ⊆ Y := by intro y hy; exact hy.1
    have hS_Q_fin : S_Q.Finite := hY_fin.subset hS_Q_sub
    have h_mult' : ENat.toENNReal S_Q.encard ≥ ENNReal.ofReal c' * ENat.toENNReal Y.encard :=
      h_mult Q hQ
    have hμS_Q_eq : μ S_Q = ENat.toENNReal S_Q.encard * (ENat.toENNReal Y.encard)⁻¹ :=
      h_measure_finite S_Q hS_Q_sub hS_Q_fin
    have hμS : ENNReal.ofReal c' ≤ μ S_Q := by
      rw [hμS_Q_eq]
      have h3 : ENat.toENNReal S_Q.encard * (ENat.toENNReal Y.encard)⁻¹ ≥
          (ENNReal.ofReal c' * ENat.toENNReal Y.encard) * (ENat.toENNReal Y.encard)⁻¹ := by gcongr
      have h4 : (ENNReal.ofReal c' * ENat.toENNReal Y.encard) * (ENat.toENNReal Y.encard)⁻¹ =
          ENNReal.ofReal c' := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hY_encard_ne_zero hY_encard_ne_top] <;> ring
      rw [h4] at h3
      exact h3
    have h_card2 : 2 ≤ S_Q.ncard :=
      ncard_ge_two_from_multiplicity hY_fin hS_Q_fin hc_pos h_mult' h_large_Y
    have hS_Q_nonempty : S_Q.Nonempty := by
      by_contra h
      have h_empty : S_Q = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h
      have h_card0 : S_Q.ncard = 0 := by rw [h_empty] <;> simp
      omega
    have h_diam : δ ≤ (hS_Q_fin.toFinset).max' _ - (hS_Q_fin.toFinset).min' _ :=
      grid_diam_ge_delta_of_ncard_ge_two hδ_pos
        (fun y hy => (hY_grid (hS_Q_sub hy)).1) hS_Q_fin h_card2
    have hQ_dyadic : Q ∈ dyadicCubes 2 δ := hTbar_dyadic Q hQ
    have hQ_nonempty : Q.Nonempty := by
      rcases hQ_dyadic with ⟨k, hk⟩
      let p0 : EuclideanSpace ℝ (Fin 2) :=
        (EuclideanSpace.equiv (Fin 2) ℝ).symm fun i : Fin 2 => δ * (k i : ℝ)
      have hp0_in : p0 ∈ Q := by
        rw [hk]
        intro i
        simp only [p0, Set.mem_setOf_eq]
        have h_lower : δ * (k i : ℝ) ∈ Set.Ico (δ * (k i : ℝ)) (δ * ((k i : ℝ) + 1)) := by
          exact ⟨by rfl, by linarith [hδ_pos]⟩
        exact h_lower
      exact ⟨p0, hp0_in⟩
    have h_incidence' : ∀ y ∈ S_Q, ∃ (x : ℝ) (p : EuclideanSpace ℝ (Fin 2)),
        x ∈ Set.Icc (0 : ℝ) 1 ∧ p ∈ Q ∧ |x - (p 0 * y + p 1)| ≤ 4 * δ := by
      intro y hy
      have h_y_in_Y : y ∈ Y := hy.1
      have h_Q_in_Uy : Q ∈ U_y y := hy.2
      have hQ_in_Tbar : Q ∈ Tbar := hQ
      rcases hQ_nonempty with ⟨p0, hp0⟩
      have h_p_in_union : p0 ∈ ⋃₀ (Tbar ∩ U_y y) := by
        apply mem_sUnion.mpr
        exact ⟨Q, ⟨hQ_in_Tbar, h_Q_in_Uy⟩, hp0⟩
      rcases h_incidence y h_y_in_Y p0 h_p_in_union with ⟨x, hx_in_X, h_approx⟩
      have hx_in_Icc : x ∈ Set.Icc (0 : ℝ) 1 :=
        (hXy_sub y h_y_in_Y hx_in_X).2
      have h_abs : |x - (p0 0 * y + p0 1)| ≤ 4 * δ := by
        have h_sym : |x - (p0 0 * y + p0 1)| = |p0 0 * y + p0 1 - x| := by
          rw [show x - (p0 0 * y + p0 1) = -(p0 0 * y + p0 1 - x) by ring]
          rw [abs_neg]
        rw [h_sym]
        exact h_approx
      exact ⟨x, p0, hx_in_Icc, hp0, h_abs⟩
    have hS_sub_support : S_Q ⊆ μ.support := by
      rw [hsupport]
      exact hS_Q_sub
    have h_box_raw := quantitative_box_from_popular_cubes
      (hδ_pos := hδ_pos)
      (hκ_pos := hτ_pos)
      (hC_F_pos := hC_F_pos)
      (hc_pos := hc'_pos)
      (hε_nonneg := by positivity)
      (hFrost := hFrost)
      (hS_sub := hS_sub_support)
      (hμS := hμS)
      (hS_fin := hS_Q_fin)
      (hS_nonempty := hS_Q_nonempty)
      (h_diam_ge_delta := h_diam)
      (hQ_dyadic := hQ_dyadic)
      (h_incidence := h_incidence')
    have h_eq1 : (1 + 2 * (4 * δ + 2 * δ)) = 1 + 12 * δ := by ring
    have h_eq2 : (4 * δ + 2 * δ) = 6 * δ := by ring
    have h_eq3 : (c' / C_F) ^ (1 / τ) = d := by rfl
    intro p hp
    have h_raw := h_box_raw p hp
    rw [h_eq1, h_eq3] at h_raw
    exact ⟨h_raw.1, by rw [h_eq2] at h_raw; exact h_raw.2⟩
  -- Union bound
  let R_full : ℝ := 1 + R_box + 6 * δ
  have h_R_full_pos : 0 < R_full := by positivity
  have h_union : ∀ (p : EuclideanSpace ℝ (Fin 2)), p ∈ ⋃₀ Tbar →
      |p 0| ≤ R_full ∧ |p 1| ≤ R_full := by
    intro p hp
    rcases mem_sUnion.mp hp with ⟨Q, hQ_in_Tbar, hp_in_Q⟩
    have h_bound := h_per_cube Q hQ_in_Tbar p hp_in_Q
    have h1 : |p 0| ≤ R_box := h_bound.1
    have h2 : |p 1| ≤ 1 + R_box + 6 * δ := h_bound.2
    have h3 : |p 0| ≤ R_full := by
      dsimp only [R_full]
      have h4 : R_box ≤ 1 + R_box + 6 * δ := by linarith
      linarith
    exact ⟨h3, h2⟩
  -- Power-of-two rounding
  obtain ⟨k, hk_le, hk_lt⟩ := exists_pow2_rounding R_full h_R_full_pos
  refine ⟨(2 : ℝ) ^ k, ⟨k, rfl⟩, ?_⟩
  have h_final : ∀ (p : EuclideanSpace ℝ (Fin 2)), p ∈ ⋃₀ Tbar →
      |p 0| ≤ (2 : ℝ) ^ k ∧ |p 1| ≤ (2 : ℝ) ^ k := by
    intro p hp
    have h_bound := h_union p hp
    have h1 : |p 0| ≤ R_full := h_bound.1
    have h2 : |p 1| ≤ R_full := h_bound.2
    have h3 : R_full ≤ (2 : ℝ) ^ k := hk_le
    exact ⟨by linarith, by linarith⟩
  exact ⟨h_final, hk_lt⟩

end ProductLikeIncidence.ProductReduction
