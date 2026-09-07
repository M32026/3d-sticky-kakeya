module

/-
# Expansion Theorem — Recursive Assembly

Consumes the bounded expansion lemma factory (Lemma 3.2) and runs the
n-1 stage recursive elimination, producing a final iterated difference
with positive uniform volume lower bound.

## Proof route

1. Compute V_min from Marstrand constants (same as `expansion_theorem_with_marstrand`).
2. Use `marstrand_uniform_lower_bound` to get weights v with volume ≥ V_min.
3. Call `quantitative_elimination_induction` with the bounded factory,
   R0 = C (radius bound from μ.support ⊆ [-C,C]), V0 = V_min.
4. Apply to μ.support to get the final volume bound.

## Dependencies

- `MyLeanRepo.RecursiveElimination` — `quantitative_elimination_induction`
- `MyLeanRepo.ExpansionTheoremAssembly` — Marstrand bound
- `MyLeanRepo.UniformExpansionLemma` — bounded factory `expansion_lemma_uniform`
-/

public import MyLeanRepo.RecursiveElimination
public import MyLeanRepo.ExpansionTheoremAssembly
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Metric Classical BigOperators
open scoped BigOperators Pointwise

namespace WeakTwoEndsSumProduct

/-- Bounded expansion lemma factory type.

For each m ≥ 2, diameter bound d_max > 0, and projection volume bound lam_min > 0,
there exists N_max (depending on m, d_max, lam_min) such that the one-step
expansion holds for all A, v satisfying the bounds. -/
abbrev BoundedExpansionFactory : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (d_max lam_min : ℝ),
    0 < d_max → 0 < lam_min →
      ∃ (N_max : ℕ), 0 < N_max ∧
        ∀ (A : Set ℝ), IsCompact A → A.Nonempty → diam A ≤ d_max →
          ∀ (v : Fin m → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) →
            ENNReal.ofReal lam_min ≤ volume (ExpansionLemma.scaledSumset v A) →
              ∃ (j : Fin m),
                volume (ExpansionLemma.scaledSumsetExcept v j
                  (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N_max)) ≥
                ENNReal.ofReal (diam A) * volume (ExpansionLemma.scaledSumset v A)

/-- Convert `BoundedExpansionFactory` to the signature used by
`quantitative_elimination_induction` (strips the `0 < N_max` conjunct). -/
lemma factory_to_induction (h_factory : BoundedExpansionFactory) :
    ∀ (m : ℕ), 2 ≤ m → ∀ (d_max lam_min : ℝ),
      0 < d_max → 0 < lam_min →
      ∃ (N_max : ℕ), ∀ (A : Set ℝ), IsCompact A → A.Nonempty → diam A ≤ d_max →
        ∀ (v : Fin m → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) →
          ENNReal.ofReal lam_min ≤ volume (ExpansionLemma.scaledSumset v A) →
            ∃ (j : Fin m),
              volume (ExpansionLemma.scaledSumsetExcept v j
                (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N_max)) ≥
              ENNReal.ofReal (diam A) * volume (ExpansionLemma.scaledSumset v A) := by
  intro m hm d_max lam_min h_dmax h_lam
  rcases h_factory m hm d_max lam_min h_dmax h_lam with ⟨N_max, _, hN⟩
  exact ⟨N_max, hN⟩

/-- **Recursive expansion theorem**.

Given the bounded expansion lemma factory and Marstrand data, produces
`d, M, V_final` such that for any Frostman measure μ with support in [-C,C],
`volume(iteratedDifference (productSet μ.support d) M) ≥ V_final`.

This replaces the old `expansion_theorem_almost_complete` which incorrectly
assumed a universal fixed N_max. -/
theorem expansion_theorem_recursive
    {κ C : ℝ} (hκ_pos : 0 < κ) (hκ_lt_one : κ < 1) (hC_pos : 0 < C)
    {n : ℕ} (hn_pos : 0 < n) (hnκ : 1 < (n : ℝ) * κ)
    (h_factory : BoundedExpansionFactory) :
    ∃ (d M : ℕ) (V_final : ℝ), 1 ≤ d ∧ 0 < V_final ∧
      ∀ (μ : Measure ℝ), IsAllScaleFrostman κ C μ →
        μ.support ⊆ Set.Icc (-C) C →
          ENNReal.ofReal V_final ≤ volume (ExpansionLemma.iteratedDifference
            (ExpansionLemma.productSet μ.support d) M) := by
  let B_val : ℝ := 1 + C ^ n / ((n : ℝ) * κ - 1)
  let V_min : ℝ := (ProductLikeIncidence.sphereProbabilityMeasure n
      (ProductLikeIncidence.ratioCapOpen n)).toReal /
    (ProductLikeIncidence.marstrandSphereConstant n * B_val) * Real.sqrt n / 2
  have hB_val_pos : 0 < B_val := by positivity
  have hV_min_pos : 0 < V_min := by
    dsimp only [V_min, B_val]
    have hα_pos : 0 < (ProductLikeIncidence.sphereProbabilityMeasure n
        (ProductLikeIncidence.ratioCapOpen n)).toReal := by
      have hU_pos : 0 < ProductLikeIncidence.sphereProbabilityMeasure n
          (ProductLikeIncidence.ratioCapOpen n) :=
        ProductLikeIncidence.ratioCapOpen_positiveMeasure hn_pos
      have h_ne : (ProductLikeIncidence.sphereProbabilityMeasure n
          (ProductLikeIncidence.ratioCapOpen n)) ≠ 0 := hU_pos.ne'
      letI : IsProbabilityMeasure (ProductLikeIncidence.sphereProbabilityMeasure n) :=
        ProductLikeIncidence.sphereProbabilityMeasure_isProbability (by linarith)
      have h_bdd : (ProductLikeIncidence.sphereProbabilityMeasure n
          (ProductLikeIncidence.ratioCapOpen n)) ≤ 1 := by
        have h3 : (ProductLikeIncidence.sphereProbabilityMeasure n
            (ProductLikeIncidence.ratioCapOpen n)) ≤
            (ProductLikeIncidence.sphereProbabilityMeasure n Set.univ) :=
          measure_mono (subset_univ (ProductLikeIncidence.ratioCapOpen n))
        have h4 : (ProductLikeIncidence.sphereProbabilityMeasure n Set.univ) = 1 := measure_univ
        rw [h4] at h3; exact h3
      have h_top : _ ≠ ⊤ := ne_top_of_le_ne_top (by simp) h_bdd
      exact ENNReal.toReal_pos h_ne h_top
    have hC_pos' : 0 < ProductLikeIncidence.marstrandSphereConstant n := by
      dsimp only [ProductLikeIncidence.marstrandSphereConstant]
      have h_d_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n from by linarith)
      exact mul_pos (mul_pos (by positivity) h_d_pos) Real.pi_pos
    have h_sqrt_pos : 0 < Real.sqrt (n : ℝ) := by positivity
    positivity
  let h_marstrand_uniform : ∀ (μ : Measure ℝ), IsAllScaleFrostman κ C μ →
      μ.support ⊆ Set.Icc (-C) C →
      ∃ (v : Fin n → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) ∧
        ENNReal.ofReal V_min ≤ volume (ExpansionLemma.scaledSumset v μ.support) :=
    fun μ hμ hμ_supp =>
      marstrand_uniform_lower_bound hκ_pos hκ_lt_one hC_pos hn_pos hnκ μ hμ hμ_supp
  let h_induction_factory := factory_to_induction h_factory
  rcases RecursiveElimination.quantitative_elimination_induction h_induction_factory
      n C V_min (by linarith) hV_min_pos
    with ⟨d, M, V_final, hd_ge_one, hV_final_pos, h_main⟩
  refine ⟨d, M, V_final, hd_ge_one, hV_final_pos, ?_⟩
  intro μ hμ hμ_supp
  have hμ_univ : μ Set.univ = 1 := hμ.1
  have hK_compact : IsCompact μ.support := by
    have h1 : IsCompact (Set.Icc (-C) C) := isCompact_Icc
    exact h1.of_isClosed_subset MeasureTheory.Measure.isClosed_support hμ_supp
  have hK_nonempty : μ.support.Nonempty := by
    by_contra h
    have h_empty : μ.support = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have h_zero : μ = 0 :=
      MeasureTheory.Measure.support_eq_empty_iff.mp h_empty
    rw [h_zero] at hμ_univ
    simp at hμ_univ
  have hK_bdd : μ.support ⊆ Set.Icc (-C) C := hμ_supp
  rcases h_marstrand_uniform μ hμ hμ_supp with ⟨v, hv, hvol_ge⟩
  exact h_main μ.support hK_compact hK_nonempty hK_bdd v hv hvol_ge

/-- Given compact nonempty `A` with `diam A ≥ D`, there exists `a ∈ A`
with `|a| ≥ D / 2`. -/
lemma exists_large_abs_of_diam_lower {A : Set ℝ} {D : ℝ}
    (hA : IsCompact A) (hA_nonempty : A.Nonempty) (hD_pos : 0 < D)
    (h_diam : D ≤ diam A) : ∃ (a : ℝ), a ∈ A ∧ D / 2 ≤ |a| := by
  -- |x| attains its maximum on compact A
  have h1 : ∃ (a : ℝ), a ∈ A ∧ ∀ (x : ℝ), x ∈ A → |x| ≤ |a| := by
    have h_cont : Continuous (fun x : ℝ => |x|) := continuous_abs
    rcases hA.exists_isMaxOn hA_nonempty (h_cont.continuousOn) with ⟨a, ha, hmax⟩
    have hmax' : ∀ x ∈ A, |x| ≤ |a| := isMaxOn_iff.mp hmax
    exact ⟨a, ha, fun x hx => hmax' x hx⟩
  rcases h1 with ⟨a, ha, hmax⟩
  -- For all x, y ∈ A: dist x y ≤ |x| + |y| ≤ 2|a|
  have h2 : ∀ (x y : ℝ), x ∈ A → y ∈ A → dist x y ≤ 2 * |a| := by
    intro x y hx hy
    have h3 : dist x y = |x - y| := by simp [Real.dist_eq]
    rw [h3]
    have h4 : |x - y| ≤ |x| + |y| := abs_sub _ _
    have h5 : |x| ≤ |a| := hmax x hx
    have h6 : |y| ≤ |a| := hmax y hy
    linarith
  have h2' : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 2 * |a| := by
    intro x hx y hy
    exact h2 x y hx hy
  have h3 : diam A ≤ 2 * |a| := Metric.diam_le_of_forall_dist_le_of_nonempty hA_nonempty h2'
  have h4 : D ≤ 2 * |a| := le_trans h_diam h3
  have h5 : D / 2 ≤ |a| := by linarith
  exact ⟨a, ha, h5⟩

/-- **Recursive expansion theorem (flattened to single N)**.

Like `expansion_theorem_recursive`, but flattens the separate product depth `d`
and difference count `M` to a single `N = max d M`. The volume lower bound
is adjusted by the dilation factor `(V_min / (4 * n))^(N - d)`. -/
theorem expansion_theorem_recursive_flat
    {κ C : ℝ} (hκ_pos : 0 < κ) (hκ_lt_one : κ < 1) (hC_pos : 0 < C)
    {n : ℕ} (hn_pos : 0 < n) (hnκ : 1 < (n : ℝ) * κ)
    (h_factory : BoundedExpansionFactory) :
    ∃ (N : ℕ) (c_X : ℝ), 0 < N ∧ 0 < c_X ∧
      ∀ (μ : Measure ℝ), IsAllScaleFrostman κ C μ →
        μ.support ⊆ Set.Icc (-C) C →
          ENNReal.ofReal c_X ≤ volume (ExpansionLemma.iteratedDifference
            (ExpansionLemma.productSet μ.support N) N) := by
  rcases expansion_theorem_recursive hκ_pos hκ_lt_one hC_pos hn_pos hnκ h_factory
    with ⟨d, M, V_final, hd_ge_one, hV_final_pos, h_main⟩
  let N : ℕ := max d M
  have hN_pos : 0 < N := by
    have h : 0 < d := by linarith
    have h' : d ≤ N := Nat.le_max_left d M
    omega
  have hd_le : d ≤ N := Nat.le_max_left d M
  have hM_le : M ≤ N := Nat.le_max_right d M
  -- Uniform diameter lower bound from Marstrand: diam(A) ≥ V_min / (2 * n)
  -- We use V_final and the induction to extract V_min implicitly.
  -- Actually, we need V_min from the recursive theorem. Let's recompute it.
  let B_val : ℝ := 1 + C ^ n / ((n : ℝ) * κ - 1)
  let V_min : ℝ := (ProductLikeIncidence.sphereProbabilityMeasure n
      (ProductLikeIncidence.ratioCapOpen n)).toReal /
    (ProductLikeIncidence.marstrandSphereConstant n * B_val) * Real.sqrt n / 2
  have hV_min_pos : 0 < V_min := by
    dsimp only [V_min, B_val]
    have hα_pos : 0 < (ProductLikeIncidence.sphereProbabilityMeasure n
        (ProductLikeIncidence.ratioCapOpen n)).toReal := by
      have hU_pos : 0 < ProductLikeIncidence.sphereProbabilityMeasure n
          (ProductLikeIncidence.ratioCapOpen n) :=
        ProductLikeIncidence.ratioCapOpen_positiveMeasure hn_pos
      have h_ne : (ProductLikeIncidence.sphereProbabilityMeasure n
          (ProductLikeIncidence.ratioCapOpen n)) ≠ 0 := hU_pos.ne'
      letI : IsProbabilityMeasure (ProductLikeIncidence.sphereProbabilityMeasure n) :=
        ProductLikeIncidence.sphereProbabilityMeasure_isProbability (by linarith)
      have h_bdd : (ProductLikeIncidence.sphereProbabilityMeasure n
          (ProductLikeIncidence.ratioCapOpen n)) ≤ 1 := by
        have h3 : (ProductLikeIncidence.sphereProbabilityMeasure n
            (ProductLikeIncidence.ratioCapOpen n)) ≤
          (ProductLikeIncidence.sphereProbabilityMeasure n Set.univ) :=
          measure_mono (Set.subset_univ (ProductLikeIncidence.ratioCapOpen n))
        have h4 : (ProductLikeIncidence.sphereProbabilityMeasure n Set.univ) = 1 := measure_univ
        rw [h4] at h3; exact h3
      have h_top : _ ≠ ⊤ := ne_top_of_le_ne_top (by simp) h_bdd
      exact ENNReal.toReal_pos h_ne h_top
    have hC_pos' : 0 < ProductLikeIncidence.marstrandSphereConstant n := by
      dsimp only [ProductLikeIncidence.marstrandSphereConstant]
      have h_d_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n from by linarith)
      exact mul_pos (mul_pos (by positivity) h_d_pos) Real.pi_pos
    have h_sqrt_pos : 0 < Real.sqrt (n : ℝ) := by positivity
    positivity
  -- Uniform lower bound on |a| for a ∈ μ.support
  let abs_lower : ℝ := V_min / (4 * (n : ℝ))
  have h_abs_lower_pos : 0 < abs_lower := by positivity
  -- Dilation factor
  let dilation_factor : ℝ := abs_lower ^ (N - d)
  have h_df_pos : 0 < dilation_factor := by positivity
  let c_X : ℝ := dilation_factor * V_final
  have hcX_pos : 0 < c_X := mul_pos h_df_pos hV_final_pos
  refine ⟨N, c_X, hN_pos, hcX_pos, ?_⟩
  intro μ hμ hμ_supp
  have hμ_univ : μ Set.univ = 1 := hμ.1
  have hK_compact : IsCompact μ.support := by
    have h1 : IsCompact (Set.Icc (-C) C) := isCompact_Icc
    exact h1.of_isClosed_subset MeasureTheory.Measure.isClosed_support hμ_supp
  have hK_nonempty : μ.support.Nonempty := by
    by_contra h
    have h_empty : μ.support = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have h_zero : μ = 0 :=
      MeasureTheory.Measure.support_eq_empty_iff.mp h_empty
    rw [h_zero] at hμ_univ
    simp at hμ_univ
  have hK_bdd : μ.support ⊆ Set.Icc (-C) C := hμ_supp
  -- Get Marstrand weights and volume bound
  let h_marstrand_uniform : ∀ (μ : Measure ℝ), IsAllScaleFrostman κ C μ →
      μ.support ⊆ Set.Icc (-C) C →
      ∃ (v : Fin n → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) ∧
        ENNReal.ofReal V_min ≤ volume (ExpansionLemma.scaledSumset v μ.support) :=
    fun μ hμ hμ_supp =>
      marstrand_uniform_lower_bound hκ_pos hκ_lt_one hC_pos hn_pos hnκ μ hμ hμ_supp
  rcases h_marstrand_uniform μ hμ hμ_supp with ⟨v, hv, hvol_ge⟩
  -- Get volume bound from recursive theorem
  have h_vol : ENNReal.ofReal V_final ≤ volume (ExpansionLemma.iteratedDifference
      (ExpansionLemma.productSet μ.support d) M) :=
    h_main μ hμ hμ_supp
  -- Diameter lower bound (ENNReal then convert to Real)
  have h_diam_lower_enn : ENNReal.ofReal (V_min / (2 * (n : ℝ))) ≤
      ENNReal.ofReal (diam μ.support) :=
    WeakTwoEndsSumProduct.diam_lower_from_scaledSumset_volume
      hK_nonempty (IsCompact.isBounded hK_compact) hv hvol_ge hV_min_pos (by linarith)
  have h_diam_nonneg : 0 ≤ diam μ.support := diam_nonneg
  have h_diam_lower : V_min / (2 * (n : ℝ)) ≤ diam μ.support := by
    have h_pos1 : 0 ≤ V_min / (2 * (n : ℝ)) := by positivity
    exact (ENNReal.ofReal_le_ofReal_iff (h := h_diam_nonneg)).mp h_diam_lower_enn
  -- Find a ∈ μ.support with |a| ≥ V_min / (4 * n)
  have hD_pos : 0 < V_min / (2 * (n : ℝ)) := by positivity
  rcases exists_large_abs_of_diam_lower hK_compact hK_nonempty hD_pos h_diam_lower
    with ⟨a, ha, h_abs_a⟩
  have h_abs_a2 : abs_lower ≤ |a| := by
    dsimp only [abs_lower]
    have h_eq : (V_min / (2 * (n : ℝ))) / 2 = V_min / (4 * (n : ℝ)) := by ring
    rw [h_eq] at h_abs_a
    exact h_abs_a
  have ha_ne_zero : a ≠ 0 := by
    have h_pos_abs : 0 < |a| := lt_of_lt_of_le h_abs_lower_pos h_abs_a2
    intro h
    rw [h] at h_pos_abs
    simp at h_pos_abs
  -- Product padding: dilated set is in iteratedDifference(productSet A N) M
  let S := ExpansionLemma.iteratedDifference (ExpansionLemma.productSet μ.support d) M
  have h_pad_prod : (fun x : ℝ => a ^ (N - d) * x) '' S ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet μ.support N) M :=
    WeakTwoEndsSumProduct.iteratedDifference_pad_product a ha hd_le
  -- Volume of dilated set: image under c*x is preimage under y*c⁻¹
  let c : ℝ := a ^ (N - d)
  have hc_ne_zero : c ≠ 0 := pow_ne_zero (N - d) ha_ne_zero
  have h_vol_dilated : volume ((fun x : ℝ => c * x) '' S) =
      ENNReal.ofReal (|c|) * volume S := by
    have h_image_eq : (fun x : ℝ => c * x) '' S = (fun y : ℝ => y * c⁻¹) ⁻¹' S := by
      ext z
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        field_simp [hc_ne_zero] <;> exact hx
      · intro hz
        refine ⟨z * c⁻¹, hz, ?_⟩
        field_simp [hc_ne_zero] <;> ring
    rw [h_image_eq]
    rw [Real.volume_preimage_mul_right (inv_ne_zero hc_ne_zero) S]
    have h_abs : |(c⁻¹)⁻¹| = |c| := by rw [inv_inv]
    rw [h_abs]
  have h_abs_pow : |c| = |a| ^ (N - d) := by
    simp [c, abs_pow]
    <;> rfl
  rw [h_abs_pow] at h_vol_dilated
  -- Sum padding: direct containment
  have hPS_nonempty : (ExpansionLemma.productSet μ.support N).Nonempty :=
    WeakTwoEndsSumProduct.productSet_nonempty hK_nonempty
  have h_pad_sum : ExpansionLemma.iteratedDifference (ExpansionLemma.productSet μ.support N) M ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet μ.support N) N :=
    WeakTwoEndsSumProduct.iteratedDifference_pad_sum hPS_nonempty hM_le
  -- Chain the bounds
  have h1 : ENNReal.ofReal (|a| ^ (N - d)) * volume S ≤
      volume (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet μ.support N) M) := by
    rw [←h_vol_dilated]
    exact measure_mono h_pad_prod
  have h2 : ENNReal.ofReal (|a| ^ (N - d)) * volume S ≥
      ENNReal.ofReal dilation_factor * ENNReal.ofReal V_final := by
    have h3 : ENNReal.ofReal dilation_factor ≤ ENNReal.ofReal (|a| ^ (N - d)) :=
      ENNReal.ofReal_le_ofReal (by
        dsimp only [dilation_factor]
        gcongr <;> linarith)
    have h4 : ENNReal.ofReal V_final ≤ volume S := h_vol
    calc ENNReal.ofReal dilation_factor * ENNReal.ofReal V_final
      ≤ ENNReal.ofReal (|a| ^ (N - d)) * ENNReal.ofReal V_final := by gcongr
    _ ≤ ENNReal.ofReal (|a| ^ (N - d)) * volume S := by gcongr
  have h5 : ENNReal.ofReal c_X ≤ volume (ExpansionLemma.iteratedDifference
      (ExpansionLemma.productSet μ.support N) N) := by
    have h6 : ENNReal.ofReal c_X = ENNReal.ofReal dilation_factor * ENNReal.ofReal V_final := by
      rw [←ENNReal.ofReal_mul h_df_pos.le]
      <;> rfl
    rw [h6]
    exact le_trans h2 (le_trans h1 (measure_mono h_pad_sum))
  exact h5

end WeakTwoEndsSumProduct
