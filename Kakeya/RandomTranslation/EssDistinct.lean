/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.TranslationProb
public import Kakeya.Probability
public import Kakeya.Tube.EDPacking.BadAgainstSet

/-!
# ED failure counts under random translation

The probabilistic half of the essentially-distinct (ED) machinery used by the
random-translation refinement lemmas:

`edFailCountSet`, the number of tubes of the family that are `BadAgainstSet` a
reference set after a random translation, with the Chernoff tail bound
`productEdFailCountSet_chernoff_tail` for the `J`-fold sum.

The predicate `BadAgainstSet` itself and its purely geometric packing bound
`badAgainstSet_count_le_of_ED_thinBox` live in
`Kakeya/Tube/EDPacking/BadAgainstSet.lean`.
-/

@[expose] public section

open MeasureTheory Metric ProbabilityTheory

namespace Kakeya

universe u

/-! ### ED failure counts against a reference set `K` -/

section EdFailCountSet

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*} [DecidableEq ι] {δ : NNReal}

/-- **ED failure count against a reference set `K` (single translation).** -/
noncomputable def edFailCountSet
    (s : Finset ι) (T : ι → Tube δ E) (K : Set E) (c : ℝ) (v : E) : ℝ :=
  ((@Finset.filter ι
      (fun i => BadAgainstSet ((T i).translate v) K c)
      (Classical.decPred _) s).card : ℝ)

omit [DecidableEq ι] in
lemma edFailCountSet_nonneg
    (s : Finset ι) (T : ι → Tube δ E) (K : Set E) (c : ℝ) (v : E) :
    0 ≤ edFailCountSet s T K c v := by
  unfold edFailCountSet; exact Nat.cast_nonneg _

omit [DecidableEq ι] in
lemma edFailCountSet_eq_filter_card
    (s : Finset ι) (T : ι → Tube δ E) (K : Set E) (c : ℝ) (v : E) :
    edFailCountSet s T K c v =
      ((@Finset.filter ι
          (fun i => BadAgainstSet ((T i).translate v) K c)
          (Classical.decPred _) s).card : ℝ) := rfl

/-- `edFailCountSet` read off the `j`-th coordinate of the product space. -/
noncomputable def productEdFailCountSet
    (s : Finset ι) (T : ι → Tube δ E) (K : Set E) (c : ℝ) (ρ : ℝ)
    (J : ℕ) (j : Fin J) (ω : Fin J → E) : ℝ :=
  edFailCountSet s T K c (ρ • ω j)

omit [DecidableEq ι] in
lemma productEdFailCountSet_nonneg
    (s : Finset ι) (T : ι → Tube δ E) (K : Set E) (c : ℝ) (ρ : ℝ)
    (J : ℕ) (j : Fin J) (ω : Fin J → E) :
    0 ≤ productEdFailCountSet s T K c ρ J j ω :=
  edFailCountSet_nonneg s T K c _

omit [DecidableEq ι] in
/-- Measurability of the J-fold version of `edFailCountSet`, derived from a
hypothesis on `edFailCountSet` itself. -/
lemma productEdFailCountSet_measurable
    (s : Finset ι) (T : ι → Tube δ E) (K : Set E) (c : ℝ) (ρ : ℝ)
    (hmeas_ed : Measurable (fun v : E => edFailCountSet s T K c v))
    (J : ℕ) (j : Fin J) :
    Measurable (fun ω : Fin J → E => productEdFailCountSet s T K c ρ J j ω) := by
  have hsmul : Measurable (fun v : E => ρ • v) := (continuous_const_smul ρ).measurable
  have hcomp : Measurable (fun v : E => edFailCountSet s T K c (ρ • v)) :=
    hmeas_ed.comp hsmul
  exact hcomp.comp (measurable_pi_apply j)

omit [DecidableEq ι] in
/-- The product ED-fail-set counts `(X_j)_j` are jointly independent. -/
lemma productEdFailCountSet_iIndepFun
    (s : Finset ι) (T : ι → Tube δ E) (K : Set E) (c : ℝ) (ρ : ℝ)
    (hmeas_ed : Measurable (fun v : E => edFailCountSet s T K c v))
    (J : ℕ) :
    iIndepFun (fun j (ω : Fin J → E) => productEdFailCountSet s T K c ρ J j ω)
      (HasUniformTranslation.productMeasure E E J) := by
  unfold HasUniformTranslation.productMeasure productEdFailCountSet
  have hsmul : Measurable (fun v : E => ρ • v) := (continuous_const_smul ρ).measurable
  have hcomp : Measurable (fun v : E => edFailCountSet s T K c (ρ • v)) :=
    hmeas_ed.comp hsmul
  exact iIndepFun_pi
    (μ := fun _ : Fin J => HasUniformTranslation.measure (Ω := E) (E := E))
    (X := fun _ : Fin J => fun v : E => edFailCountSet s T K c (ρ • v))
    (fun _ => hcomp.aemeasurable)

omit [DecidableEq ι] in
/-- The product ED-fail-set counts `(X_j)_j` are identically distributed. -/
lemma productEdFailCountSet_identDistrib
    (s : Finset ι) (T : ι → Tube δ E) (K : Set E) (c : ℝ) (ρ : ℝ)
    (hmeas_ed : Measurable (fun v : E => edFailCountSet s T K c v))
    (J : ℕ) (j₁ j₂ : Fin J) :
    IdentDistrib
      (fun ω : Fin J → E => productEdFailCountSet s T K c ρ J j₁ ω)
      (fun ω : Fin J → E => productEdFailCountSet s T K c ρ J j₂ ω)
      (HasUniformTranslation.productMeasure E E J)
      (HasUniformTranslation.productMeasure E E J) := by
  have hsmul : Measurable (fun v : E => ρ • v) := (continuous_const_smul ρ).measurable
  have hcomp : Measurable (fun v : E => edFailCountSet s T K c (ρ • v)) :=
    hmeas_ed.comp hsmul
  refine ⟨(productEdFailCountSet_measurable s T K c ρ hmeas_ed J j₁).aemeasurable,
          (productEdFailCountSet_measurable s T K c ρ hmeas_ed J j₂).aemeasurable, ?_⟩
  have h₁ : (fun ω : Fin J → E => productEdFailCountSet s T K c ρ J j₁ ω) =
      (fun v : E => edFailCountSet s T K c (ρ • v)) ∘ Function.eval j₁ := rfl
  have h₂ : (fun ω : Fin J → E => productEdFailCountSet s T K c ρ J j₂ ω) =
      (fun v : E => edFailCountSet s T K c (ρ • v)) ∘ Function.eval j₂ := rfl
  rw [h₁, h₂,
      ← Measure.map_map hcomp (measurable_pi_apply j₁),
      ← Measure.map_map hcomp (measurable_pi_apply j₂),
      HasUniformTranslation.productMeasure_map_eval,
      HasUniformTranslation.productMeasure_map_eval]

omit [DecidableEq ι] in
/-- **Deterministic `J`-fold bound.**

If the single-translation count is bounded pointwise by `C`, then the `J`-fold
sum is bounded by `J · C` for *every* sample point, with no probabilistic input.

This is the bound the Chernoff route of `productEdFailCountSet_chernoff_tail`
has to beat.  It does not: that route's precondition `hJm` already forces
`J · m < M` with `M` the same pointwise cap `C`, so its conclusion holds only
above the threshold `J · C`, and the surviving cap is a further multiple of it. -/
lemma productEdFailCountSet_sum_le_of_pointwise
    (s : Finset ι) (T : ι → Tube δ E) (K : Set E) (c : ℝ) (ρ : ℝ)
    {J : ℕ} (C : ℝ)
    (hC : ∀ v : E, edFailCountSet s T K c v ≤ C) (ω : Fin J → E) :
    ∑ j : Fin J, productEdFailCountSet s T K c ρ J j ω ≤ (J : ℝ) * C := by
  unfold productEdFailCountSet
  calc
    ∑ j : Fin J, edFailCountSet s T K c (ρ • ω j) ≤ ∑ _ : Fin J, C := by
      exact Finset.sum_le_sum fun j _ => hC (ρ • ω j)
    _ = (J : ℝ) * C := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [DecidableEq ι] in
/-- Chernoff tail bound for the product-space `edFailCountSet`, in the
reference-set form.

The caller supplies measurability of the per-fibre event (`hmeas_ed`), the
pointwise cap (`hM_upper`), and the Chernoff precondition `J · mean < M`
(`hJm`). -/
lemma productEdFailCountSet_chernoff_tail [ProperSpace E]
    (_hδ : 0 < δ)
    (s : Finset ι) (T : ι → Tube δ E) (K : Set E) (c : ℝ)
    (ρ : ℝ) (_hρ : 0 < ρ)
    {J : ℕ} [NeZero J]
    (M : ℝ) (hM_pos : 0 < M)
    (hM_upper : ∀ v : E, edFailCountSet s T K c v ≤ M)
    (hmeas_ed : Measurable (fun v : E => edFailCountSet s T K c v))
    (hJm : (J : ℝ) *
        (∫ v : E, edFailCountSet s T K c (ρ • v)
          ∂(uniformBallMeasure E)) < M)
    (S : ℝ) :
    ((HasUniformTranslation.productMeasure E E J)
        {ω | ∑ j : Fin J,
          productEdFailCountSet s T K c ρ J j ω > S}).toReal ≤
      Real.exp (10 * Real.exp 1 - S / M) := by
  set μ : Measure (Fin J → E) := HasUniformTranslation.productMeasure E E J with hμ
  set X : Fin J → (Fin J → E) → ℝ := fun j ω =>
    productEdFailCountSet s T K c ρ J j ω with hX
  set m : ℝ := ∫ ω, X 0 ω ∂μ with hm_def
  have hmeas : ∀ j, Measurable (X j) := fun j =>
    productEdFailCountSet_measurable s T K c ρ hmeas_ed J j
  have hbound : ∀ j, ∀ᵐ ω ∂μ, 0 ≤ X j ω ∧ X j ω ≤ M := fun j =>
    Filter.Eventually.of_forall fun ω =>
      ⟨productEdFailCountSet_nonneg s T K c ρ J j ω, hM_upper (ρ • ω j)⟩
  have hm_nn : 0 ≤ m :=
    MeasureTheory.integral_nonneg fun ω => productEdFailCountSet_nonneg s T K c ρ J 0 ω
  have hsmul : Measurable (fun v : E => ρ • v) :=
    (continuous_const_smul ρ).measurable
  have hcomp : Measurable (fun v : E => edFailCountSet s T K c (ρ • v)) :=
    hmeas_ed.comp hsmul
  have hm_eq : m = ∫ v : E, edFailCountSet s T K c (ρ • v) ∂(uniformBallMeasure E) := by
    -- Push the integral down to the marginal on coordinate 0.
    have hmap_int :
        ∫ v : E, edFailCountSet s T K c (ρ • v)
            ∂((HasUniformTranslation.productMeasure E E J).map
              (Function.eval (0 : Fin J))) =
          ∫ ω : Fin J → E,
            edFailCountSet s T K c (ρ • Function.eval (0 : Fin J) ω) ∂μ := by
      rw [show μ = HasUniformTranslation.productMeasure E E J from hμ]
      exact MeasureTheory.integral_map (measurable_pi_apply (0 : Fin J)).aemeasurable
        hcomp.aestronglyMeasurable
    have hmap_eq : (HasUniformTranslation.productMeasure E E J).map
        (Function.eval (0 : Fin J)) =
          HasUniformTranslation.measure (Ω := E) (E := E) :=
      HasUniformTranslation.productMeasure_map_eval J 0
    change m = _
    rw [show m = ∫ ω : Fin J → E,
          edFailCountSet s T K c (ρ • Function.eval (0 : Fin J) ω) ∂μ from rfl,
        ← hmap_int, hmap_eq]
    rfl
  have hJm' : (J : ℝ) * m < M := by rw [hm_eq]; exact hJm
  have hmM : m ≤ M := by
    have h1 : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne J)
    have : m ≤ (J : ℝ) * m := by
      have := mul_le_mul_of_nonneg_right h1 hm_nn
      simpa using this
    linarith [hJm']
  have hindep : iIndepFun X μ :=
    productEdFailCountSet_iIndepFun s T K c ρ hmeas_ed J
  have hident : ∀ j : Fin J, IdentDistrib (X j) (X 0) μ μ := fun j =>
    productEdFailCountSet_identDistrib s T K c ρ hmeas_ed J j 0
  exact Probability.lemma_A1_case_lt J X hmeas M hM_pos m hm_nn hmM hbound rfl hindep hident S hJm'

end EdFailCountSet

end Kakeya
