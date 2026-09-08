/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Step5
public import Kakeya.Factoring.Step2Measurable

/-! # Assembly of the factoring pipeline

This file assembles the already proved Steps 0--5 of the factoring construction.  It contains no
Frostman or essential-distinctness hypothesis: those belong to applications of the construction,
not to the pigeonholing itself.
-/

@[expose] public section

open MeasureTheory Convexity Kakeya
open scoped ENNReal NNReal

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

open Classical in
/-- A finite family of finite `ENNReal` values has a dyadic subfamily carrying a logarithmic
fraction of its total mass, with no a priori positive lower bound on its nonzero values. -/
theorem exists_self_dyadic (s : Finset ι) (f : ι → ENNReal)
    (hf : ∀ i ∈ s, f i ≠ ⊤) :
    ∃ s' ⊆ s,
      ∑ i ∈ s, f i ≤
          (2 * Kakeya.factoringStep1FiberPigeonholeConstant 1 s.card : NNReal) *
            ∑ i ∈ s', f i ∧
        (∀ i ∈ s', ∀ j ∈ s', f i ≤ 2 * f j) ∧
        ∀ i ∈ s', f i ≠ 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨∅, Finset.empty_subset _, by simp, by simp, by simp⟩
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image s f hs
  by_cases hzero : f i₀ = 0
  · have hall : ∀ i ∈ s, f i = 0 := fun i hi ↦
      nonpos_iff_eq_zero.mp ((hmax i hi).trans_eq hzero)
    refine ⟨∅, Finset.empty_subset _, ?_, by simp, by simp⟩
    simp [Finset.sum_eq_zero hall]
  have hcard : 0 < s.card := Finset.card_pos.mpr hs
  let M : NNReal := (f i₀).toNNReal
  have hM : (M : ENNReal) = f i₀ := ENNReal.coe_toNNReal (hf i₀ hi₀)
  have hMpos : 0 < M := ENNReal.toNNReal_pos hzero (hf i₀ hi₀)
  let a : NNReal := M / s.card
  have hapos : 0 < a := div_pos hMpos (by exact_mod_cast hcard)
  let t : Finset ι := {i ∈ s | (a : ENNReal) ≤ f i}
  let l : Finset ι := {i ∈ s | ¬ (a : ENNReal) ≤ f i}
  have hi₀t : i₀ ∈ t := by
    refine Finset.mem_filter.mpr ⟨hi₀, ?_⟩
    rw [← hM]
    exact ENNReal.coe_le_coe.mpr
      (div_le_self hMpos.le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcard.ne'))
  have hlight : ∑ i ∈ l, f i ≤ (M : ENNReal) := by
    calc
      ∑ i ∈ l, f i ≤ ∑ _i ∈ l, (a : ENNReal) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2)
      _ = (l.card : ENNReal) * (a : ENNReal) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (s.card : ENNReal) * (a : ENNReal) := by
        gcongr
        simpa only [l] using Finset.filter_subset (fun i ↦ ¬ (a : ENNReal) ≤ f i) s
      _ = (M : ENNReal) := by
        simp only [a]
        rw [ENNReal.coe_div (by exact_mod_cast hcard.ne'), ENNReal.coe_natCast]
        exact ENNReal.mul_div_cancel (by exact_mod_cast hcard.ne') (ENNReal.natCast_ne_top _)
  have hsplit : ∑ i ∈ s, f i = ∑ i ∈ t, f i + ∑ i ∈ l, f i := by
    simpa only [t, l] using
      (Finset.sum_filter_add_sum_filter_not s (fun i ↦ (a : ENNReal) ≤ f i) f).symm
  have htotal : ∑ i ∈ s, f i ≤ 2 * ∑ i ∈ t, f i := by
    rw [hsplit]
    have hMle : (M : ENNReal) ≤ ∑ i ∈ t, f i := by
      rw [hM]
      exact Finset.single_le_sum (fun i _ ↦ bot_le) hi₀t
    calc
      ∑ i ∈ t, f i + ∑ i ∈ l, f i
          ≤ ∑ i ∈ t, f i + (M : ENNReal) := add_le_add le_rfl hlight
      _ ≤ ∑ i ∈ t, f i + ∑ i ∈ t, f i := add_le_add_right hMle _
      _ = 2 * ∑ i ∈ t, f i := by ring
  have htIcc : ∀ i ∈ t, f i ∈ Set.Icc (a : ENNReal) (M : ENNReal) := by
    intro i hi
    exact ⟨(Finset.mem_filter.mp hi).2, by
      rw [hM]
      exact hmax i (Finset.mem_filter.mp hi).1⟩
  obtain ⟨s', hs't, hsum, hcomp⟩ :=
    ENNReal.dyadic_pigeonhole₁'' (s := t) (w := f) (f := f) hapos htIcc
  have hsum' : ∑ i ∈ t, f i ≤
      (Kakeya.factoringStep1FiberPigeonholeConstant a M : ENNReal) * ∑ i ∈ s', f i := by
    simpa [Kakeya.coe_factoringStep1FiberPigeonholeConstant] using hsum
  have hratio : M / a = (s.card : NNReal) := by
    simp only [a]
    field_simp
  have hconst : Kakeya.factoringStep1FiberPigeonholeConstant a M =
      Kakeya.factoringStep1FiberPigeonholeConstant 1 s.card := by
    apply ENNReal.coe_injective
    rw [Kakeya.coe_factoringStep1FiberPigeonholeConstant,
      Kakeya.coe_factoringStep1FiberPigeonholeConstant]
    congr 2
    rw [show (M : ℝ) / (a : ℝ) = (s.card : ℝ) by exact_mod_cast hratio]
    norm_num
  refine ⟨s', hs't.trans (Finset.filter_subset _ _), ?_, hcomp, ?_⟩
  · calc
      ∑ i ∈ s, f i ≤ 2 * ∑ i ∈ t, f i := htotal
      _ ≤ 2 * ((Kakeya.factoringStep1FiberPigeonholeConstant a M : ENNReal) *
          ∑ i ∈ s', f i) := by gcongr
      _ = (2 * Kakeya.factoringStep1FiberPigeonholeConstant 1 s.card : NNReal) *
          ∑ i ∈ s', f i := by
        simp only [hconst, ENNReal.coe_mul]
        norm_num
        rw [mul_assoc]
  · intro i hi
    exact ne_of_gt ((ENNReal.coe_pos.mpr hapos).trans_le (htIcc i (hs't hi)).1)

open Classical in
/-- Restricting a finite shaded family to a measurable set preserves a pointwise lower
multiplicity bound after integration. -/
theorem mul_volume_iUnionShade_inter_le_sum_volume_inter (s : Finset ι)
    (V : ι → ShadedBody E) (B : Set E) (hB : MeasurableSet B) (L : ENNReal)
    (hlow : ∀ x ∈ iUnionShade s V, L ≤ (pointwiseMultiplicity s V x : ENNReal)) :
    L * volume (iUnionShade s V ∩ B) ≤ ∑ i ∈ s, volume ((V i).shade ∩ B) := by
  let W : ι → ShadedBody E := fun i ↦ (V i).restrictShade B hB
  have hU : iUnionShade s W = iUnionShade s V ∩ B := iUnionShade_restrictShade s V B hB
  by_cases hzero : volume (iUnionShade s W) = 0
  · rw [← hU, hzero, mul_zero]
    exact bot_le
  have hpoint : ∀ x ∈ iUnionShade s W,
      L ≤ (pointwiseMultiplicity s W x : ENNReal) := by
    intro x hx
    have hx' : x ∈ iUnionShade s V := by
      rw [hU] at hx
      exact hx.1
    have hxB : x ∈ B := by
      rw [hU] at hx
      exact hx.2
    simpa [W, pointwiseMultiplicity, shade_restrictShade, hxB] using hlow x hx'
  have hm := le_multiplicity_of_le_pointwiseMultiplicity s W hzero hpoint
  calc
    L * volume (iUnionShade s V ∩ B) = L * volume (iUnionShade s W) := by rw [hU]
    _ ≤ multiplicity s W * volume (iUnionShade s W) := by gcongr
    _ = ∑ i ∈ s, volume (W i).shade := (sum_shade_eq_multiplicity_mul_union s W).symm
    _ = ∑ i ∈ s, volume ((V i).shade ∩ B) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show (W i).shade = (V i).shade ∩ B by rfl]

open Classical in
/-- Restricting a finite shaded family to a measurable set preserves a pointwise upper
multiplicity bound after integration. -/
theorem sum_volume_inter_le_mul_volume_iUnionShade_inter (s : Finset ι)
    (V : ι → ShadedBody E) (B : Set E) (hB : MeasurableSet B) (U : ENNReal)
    (hupp : ∀ x ∈ iUnionShade s V, (pointwiseMultiplicity s V x : ENNReal) ≤ U) :
    (∑ i ∈ s, volume ((V i).shade ∩ B)) ≤ U * volume (iUnionShade s V ∩ B) := by
  let W : ι → ShadedBody E := fun i ↦ (V i).restrictShade B hB
  have hU : iUnionShade s W = iUnionShade s V ∩ B := iUnionShade_restrictShade s V B hB
  have hpoint : ∀ x ∈ iUnionShade s W,
      (pointwiseMultiplicity s W x : ENNReal) ≤ U := by
    intro x hx
    have hx' : x ∈ iUnionShade s V := by
      rw [hU] at hx
      exact hx.1
    have hxB : x ∈ B := by
      rw [hU] at hx
      exact hx.2
    simpa [W, pointwiseMultiplicity, shade_restrictShade, hxB] using hupp x hx'
  have hm := multiplicity_le_of_pointwiseMultiplicity_le s W hpoint
  calc
    ∑ i ∈ s, volume ((V i).shade ∩ B) = ∑ i ∈ s, volume (W i).shade := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show (W i).shade = (V i).shade ∩ B by rfl]
    _ = multiplicity s W * volume (iUnionShade s W) := sum_shade_eq_multiplicity_mul_union s W
    _ ≤ U * volume (iUnionShade s W) := by gcongr
    _ = U * volume (iUnionShade s V ∩ B) := by rw [hU]

/-- The positive Step 5 ball masses admit positive finite lower and upper bounds.

When there are no positive balls, the assertion is vacuous and the bounds are both chosen to be
one.  Otherwise the bounds are the minimum and maximum of the finitely many masses, transported
from `ENNReal` to `NNReal`. -/
theorem exists_step5PositiveBalls_bounds (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) (T : Finset E)
    (w₁ : ℝ≥0) :
    ∃ a b : ℝ≥0, 0 < a ∧
      ∀ c ∈ step5PositiveBalls F u t' Ω hΩ k T w₁,
        volume (iUnionShade {i ∈ u | F.parent i ∈ t'}
            (step3InnerBody F u t' Ω hΩ k) ∩ Metric.closedBall c (w₁ : ℝ)) ∈
          Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞) := by
  classical
  let P := step5PositiveBalls F u t' Ω hΩ k T w₁
  let m : E → ℝ≥0∞ := fun c ↦
    volume (iUnionShade {i ∈ u | F.parent i ∈ t'}
      (step3InnerBody F u t' Ω hΩ k) ∩ Metric.closedBall c (w₁ : ℝ))
  by_cases hP : P.Nonempty
  · let f : E → ℝ≥0 := fun c ↦ (m c).toNNReal
    refine ⟨P.inf' hP f, P.sup' hP f, ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro c hc
      apply ENNReal.toNNReal_pos
      · have hc' : c ∈ step5PositiveBalls F u t' Ω hΩ k T w₁ := by simpa [P] using hc
        exact (Finset.mem_filter.mp hc').2
      · apply ne_top_of_le_ne_top
          (volume_iUnion_shade_ne_top {i ∈ u | F.parent i ∈ t'}
            (step3InnerBody F u t' Ω hΩ k))
        exact measure_mono Set.inter_subset_left
    · intro c hc
      have hm_top : m c ≠ ⊤ := by
        apply ne_top_of_le_ne_top
            (volume_iUnion_shade_ne_top {i ∈ u | F.parent i ∈ t'}
              (step3InnerBody F u t' Ω hΩ k))
        exact measure_mono Set.inter_subset_left
      change m c ∈ Set.Icc
        ((P.inf' hP f : ℝ≥0) : ℝ≥0∞) ((P.sup' hP f : ℝ≥0) : ℝ≥0∞)
      rw [← ENNReal.coe_toNNReal hm_top]
      exact ⟨ENNReal.coe_le_coe.mpr (Finset.inf'_le f hc),
        ENNReal.coe_le_coe.mpr (Finset.le_sup' f hc)⟩
  · refine ⟨1, 1, zero_lt_one, ?_⟩
    intro c hc
    exact (hP ⟨c, hc⟩).elim

/-! ### The open-ball Step 2 specialization used only by the pipeline -/

/-- The pipeline uses open balls for the neighbourhood component of Step 2.  This leaves the
closed-ball specialization in `Step2.lean` unchanged while making the selected level set Borel. -/
def pipelineNhd (r : ℝ) : κ → E → Set E := fun _ x ↦ Metric.ball x r

/-- A Step 2 level set for the pipeline's open-ball neighbourhood assignment. -/
noncomputable def pipelineLevelSet (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (r : ℝ) (N k l l' : ℕ) : Set E :=
  {x | MultiplicityFamily.IsScaleTriple t'
    (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) (pipelineNhd r) N k l l' x}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [DecidableEq κ] in
private theorem isOpen_setOf_exists_mem_pipelineNhd (f : E → ℕ) (j : κ) (r : ℝ)
    (v : ℕ) : IsOpen {x | ∃ y ∈ pipelineNhd r j x, f y = v} := by
  rw [show {x : E | ∃ y ∈ pipelineNhd r j x, f y = v} =
      ⋃ y, ⋃ (_ : f y = v), Metric.ball y r by
    ext x
    constructor
    · rintro ⟨y, hy, hyv⟩
      refine Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hyv, ?_⟩⟩
      simpa only [pipelineNhd, Metric.mem_ball_comm] using hy
    · intro hx
      obtain ⟨y, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hyv, hxy⟩ := Set.mem_iUnion.mp hx
      exact ⟨y, by simpa only [pipelineNhd, Metric.mem_ball_comm] using hxy, hyv⟩]
  exact isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball

omit [FiniteDimensional ℝ E] in
private theorem measurableSet_pipelineLevelSet (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (r : ℝ) (N k l l' : ℕ) :
    MeasurableSet (pipelineLevelSet F u t' r N k l l') := by
  apply Kakeya.MultiplicityFamily.measurableSet_setOf_isScaleTriple
  · intro j _
    exact measurable_pointwiseMultiplicity _ _
  · intro j _ v
    exact (isOpen_setOf_exists_mem_pipelineNhd
      (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j) j r v).measurableSet

namespace FactorFamily

/-- The inner index set fed to Steps 2--5: the Step 0 survivors over the outer set selected by
Step 1. -/
noncomputable def pipelineInnerSet [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) : Finset ι :=
  {i ∈ F.step0.innerSet | F.parent i ∈ (F.step1 hδ hdisc).outerSet}

/-- The triple of dyadic exponents selected for the pipeline's open-ball Step 2 data. -/
noncomputable def pipelineScaleTriple [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (r : ℝ) (hr : 0 < r) :
    ℕ × ℕ × ℕ :=
  (MultiplicityFamily.exists_isScaleTriple_lintegral_le
    (t := (F.step1 hδ hdisc).outerSet)
    (m := fiberMultiplicity F
      {i ∈ F.step0.innerSet | F.parent i ∈ (F.step1 hδ hdisc).outerSet})
    (nhd := pipelineNhd r) (μ := volume) (M := F.innerSet.card)
    (fun j _ y ↦ fiberMultiplicity_le_card F F.innerSet_step0_subset
      (F.step1 hδ hdisc).outerSet j y)
    (fun _ _ _ ↦ Metric.mem_ball_self hr)).choose

private theorem pipelineScaleTriple_spec [Nontrivial E] (F : FactorFamily E ι κ)
    {δ : ℝ≥0} (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (r : ℝ)
    (hr : 0 < r) :
    F.pipelineScaleTriple hδ hdisc r hr ∈
        MultiplicityFamily.scaleTripleBox F.innerSet.card (F.step1 hδ hdisc).outerSet.card ∧
      ((MultiplicityFamily.scalePigeonholeConstant F.innerSet.card
        (F.step1 hδ hdisc).outerSet.card : ℝ≥0∞))⁻¹ *
          ∫⁻ x, ((∑ j ∈ (F.step1 hδ hdisc).outerSet,
            fiberMultiplicity F
              {i ∈ F.step0.innerSet | F.parent i ∈ (F.step1 hδ hdisc).outerSet} j x : ℕ) :
              ℝ≥0∞)
        ≤ ∫⁻ x in pipelineLevelSet F F.step0.innerSet (F.step1 hδ hdisc).outerSet r
            F.innerSet.card (F.pipelineScaleTriple hδ hdisc r hr).1
            (F.pipelineScaleTriple hδ hdisc r hr).2.1
            (F.pipelineScaleTriple hδ hdisc r hr).2.2,
            ((∑ j ∈ (F.step1 hδ hdisc).outerSet,
              fiberMultiplicity F
                {i ∈ F.step0.innerSet | F.parent i ∈ (F.step1 hδ hdisc).outerSet} j x :
                ℕ) : ℝ≥0∞) :=
  (MultiplicityFamily.exists_isScaleTriple_lintegral_le
    (t := (F.step1 hδ hdisc).outerSet)
    (m := fiberMultiplicity F
      {i ∈ F.step0.innerSet | F.parent i ∈ (F.step1 hδ hdisc).outerSet})
    (nhd := pipelineNhd r) (μ := volume) (M := F.innerSet.card)
    (fun j _ y ↦ fiberMultiplicity_le_card F F.innerSet_step0_subset
      (F.step1 hδ hdisc).outerSet j y)
    (fun _ _ _ ↦ Metric.mem_ball_self hr)).choose_spec

/-- The Step 2 level set used by the factoring pipeline. -/
noncomputable def pipelineSet [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (r : ℝ) (hr : 0 < r) : Set E :=
  pipelineLevelSet F F.step0.innerSet (F.step1 hδ hdisc).outerSet r F.innerSet.card
    (F.pipelineScaleTriple hδ hdisc r hr).1
    (F.pipelineScaleTriple hδ hdisc r hr).2.1
    (F.pipelineScaleTriple hδ hdisc r hr).2.2

/-- The inner dyadic exponent selected by Step 2 and used by Steps 3--5. -/
noncomputable def pipelineExponent [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (r : ℝ) (hr : 0 < r) : ℕ :=
  (F.pipelineScaleTriple hδ hdisc r hr).1

/-- The ordinary outer dyadic exponent selected by the pipeline's Step 2 pigeonholing. -/
noncomputable def pipelineOuterExponent [Nontrivial E] (F : FactorFamily E ι κ)
    {δ : ℝ≥0} (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (r : ℝ)
    (hr : 0 < r) : ℕ :=
  (F.pipelineScaleTriple hδ hdisc r hr).2.1

/-- The shaded family obtained after all five factoring steps, for a fixed Step 5 selection. -/
noncomputable def pipelineFamily [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (r : ℝ) (hr : 0 < r)
    (hΩ : MeasurableSet (F.pipelineSet hδ hdisc r hr)) (T' : Finset E) (w₁ : ℝ≥0) :
    ShadedFactorFamily E ι κ :=
  step5ShadedFactorFamily F F.innerSet_step0_subset (F.step1 hδ hdisc).outerSet
    (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr) T' w₁

/-- The Step 2 level set used by the factoring pipeline is measurable. -/
theorem measurableSet_pipelineSet [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (r : ℝ) (hr : 0 < r) :
    MeasurableSet (F.pipelineSet hδ hdisc r hr) := by
  exact measurableSet_pipelineLevelSet F F.step0.innerSet (F.step1 hδ hdisc).outerSet r
    F.innerSet.card (F.pipelineScaleTriple hδ hdisc r hr).1
    (F.pipelineScaleTriple hδ hdisc r hr).2.1
    (F.pipelineScaleTriple hδ hdisc r hr).2.2

/-- Pointwise Step 2 estimates for the triple selected by the open-ball pipeline. -/
theorem bounds_of_mem_pipelineSet [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (r : ℝ) (hr : 0 < r)
    {x : E} (hx : x ∈ F.pipelineSet hδ hdisc r hr) :
    2 ^ F.pipelineExponent hδ hdisc r hr * 2 ^ F.pipelineOuterExponent hδ hdisc r hr
        ≤ pointwiseMultiplicity (F.pipelineInnerSet hδ hdisc) F.innerBody x ∧
      pointwiseMultiplicity (F.pipelineInnerSet hδ hdisc) F.innerBody x ≤
        Kakeya.factoringStep2PointwiseConstant F.innerSet.card *
          (2 ^ F.pipelineExponent hδ hdisc r hr *
            2 ^ F.pipelineOuterExponent hδ hdisc r hr) ∧
      2 ^ F.pipelineOuterExponent hδ hdisc r hr ≤
        (MultiplicityFamily.dyadicLevel (F.step1 hδ hdisc).outerSet
          (fiberMultiplicity F (F.pipelineInnerSet hδ hdisc))
          (F.pipelineExponent hδ hdisc r hr) x).card ∧
      (MultiplicityFamily.dyadicLevel (F.step1 hδ hdisc).outerSet
        (fiberMultiplicity F (F.pipelineInnerSet hδ hdisc))
        (F.pipelineExponent hδ hdisc r hr) x).card <
          2 * 2 ^ F.pipelineOuterExponent hδ hdisc r hr := by
  have hst : MultiplicityFamily.IsScaleTriple (F.step1 hδ hdisc).outerSet
      (fiberMultiplicity F (F.pipelineInnerSet hδ hdisc)) (pipelineNhd r)
      F.innerSet.card (F.pipelineExponent hδ hdisc r hr)
      (F.pipelineOuterExponent hδ hdisc r hr)
      (F.pipelineScaleTriple hδ hdisc r hr).2.2 x := hx
  have hsum := sum_fiberMultiplicity_eq_pointwiseMultiplicity F F.step0.innerSet
    (F.step1 hδ hdisc).outerSet x
  rw [show pointwiseMultiplicity (F.pipelineInnerSet hδ hdisc) F.innerBody x =
      ∑ j ∈ (F.step1 hδ hdisc).outerSet,
        fiberMultiplicity F (F.pipelineInnerSet hδ hdisc) j x by
    simpa only [pipelineInnerSet] using hsum.symm]
  exact ⟨hst.mul_le_sum, hst.sum_le_mul, hst.le_card_dyadicLevel,
    hst.card_dyadicLevel_lt⟩

end FactorFamily

open Classical in
/-- The Step 3 family in the fixed pipeline has pointwise multiplicity in a factor-four interval
on its shaded union. -/
private theorem pipelineStep3_multiplicity [Nontrivial E] (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (r : ℝ) (hr : 0 < r)
    (hΩ : MeasurableSet (F.pipelineSet hδ hdisc r hr)) {x : E}
    (hx : x ∈ iUnionShade (F.pipelineInnerSet hδ hdisc)
      (step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
        (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr))) :
    let L := 2 ^ F.pipelineExponent hδ hdisc r hr *
      2 ^ F.pipelineOuterExponent hδ hdisc r hr
    L ≤ pointwiseMultiplicity (F.pipelineInnerSet hδ hdisc)
        (step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
          (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr)) x ∧
      pointwiseMultiplicity (F.pipelineInnerSet hδ hdisc)
          (step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
            (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr)) x < 4 * L := by
  let u := F.step0.innerSet
  let t' := (F.step1 hδ hdisc).outerSet
  let Ω := F.pipelineSet hδ hdisc r hr
  let k := F.pipelineExponent hδ hdisc r hr
  let l := F.pipelineOuterExponent hδ hdisc r hr
  let d := MultiplicityFamily.dyadicLevel t'
    (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) k x
  have hxΩ : x ∈ Ω := by
    obtain ⟨i, _, hxi⟩ := Set.mem_iUnion₂.mp hx
    change x ∈ (F.innerBody i).shade ∩ Ω ∩ step3DyadicSet F u t' k (F.parent i) at hxi
    exact hxi.1.2
  have hb := F.bounds_of_mem_pipelineSet hδ hdisc r hr hxΩ
  have hd : 2 ^ l ≤ d.card ∧ d.card < 2 * 2 ^ l := by
    constructor
    · simpa [d, l, k, t', Ω, u, FactorFamily.pipelineInnerSet] using hb.2.2.1
    · simpa [d, l, k, t', Ω, u, FactorFamily.pipelineInnerSet] using hb.2.2.2
  have hsand := Nat.dyadic_class_card_sandwich d
    (fun j ↦ fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x) k
    (fun j hj ↦ (Finset.mem_filter.mp hj).2)
  have hpm : pointwiseMultiplicity (F.pipelineInnerSet hδ hdisc)
      (step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
        (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr)) x =
      ∑ j ∈ d, fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x := by
    have h := pointwiseMultiplicity_step3FactorFamily
      F F.innerSet_step0_subset t' Ω hΩ k x
    rw [if_pos hxΩ] at h
    simpa [u, t', Ω, k, d, FactorFamily.pipelineInnerSet] using h
  dsimp only
  rw [hpm]
  constructor
  · exact (Nat.mul_le_mul_left _ hd.1).trans hsand.1
  · calc
      ∑ j ∈ d, fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x
          ≤ 2 ^ (k + 1) * d.card := hsand.2
      _ < 2 ^ (k + 1) * (2 * 2 ^ l) := Nat.mul_lt_mul_of_pos_left hd.2 (by positivity)
      _ = 4 * (2 ^ k * 2 ^ l) := by simp [pow_succ]; ring

/-- **The common Step 0--Step 5 assembly.** It chooses the bounded-overlap Step 5 cover, obtains
positive finite bounds for its nonzero ball masses, performs the last pigeonholing, and returns the
resulting shaded factor family.  The conclusion retains the cover data needed by ball estimates and
the Step 5 refinement needed to compose the complete mass ledger. -/
theorem exists_factoringPipeline [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (r : ℝ) (hr : 0 < r)
    (hΩ : MeasurableSet (F.pipelineSet hδ hdisc r hr)) {w₁ : ℝ≥0} (hw₁ : 0 < w₁) :
    ∃ (a b : ℝ≥0) (T T' : Finset E),
      0 < a ∧
      (T : Set E) ⊆ step4OuterUnion F F.innerSet_step0_subset
        (F.step1 hδ hdisc).outerSet (F.pipelineSet hδ hdisc r hr) hΩ
        (F.pipelineExponent hδ hdisc r hr) ∧
      Metric.IsSeparated (w₁ : ℝ≥0∞) (T : Set E) ∧
      IsStep5Cover F F.innerSet_step0_subset (F.step1 hδ hdisc).outerSet
        (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr) T w₁
        (Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E)) ∧
      T' ⊆ step5PositiveBalls F F.step0.innerSet (F.step1 hδ hdisc).outerSet
        (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr) T w₁ ∧
      Metric.IsSeparated (w₁ : ℝ≥0∞) (T' : Set E) ∧
      IsCRefinement (F.pipelineInnerSet hδ hdisc)
        (step5InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
          (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr) T' w₁)
        (F.pipelineInnerSet hδ hdisc)
        (step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
          (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr))
        (Kakeya.factoringStep5PigeonholeConstant
          (Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E)) a b)⁻¹ ∧
      (∀ c ∈ T', ∀ c' ∈ T',
        volume (iUnionShade (F.pipelineInnerSet hδ hdisc)
            (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerBody ∩
              Metric.closedBall c (w₁ : ℝ)) ≤
          2 * volume (iUnionShade (F.pipelineInnerSet hδ hdisc)
            (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerBody ∩
              Metric.closedBall c' (w₁ : ℝ))) := by
  classical
  obtain ⟨T, hTsub, hTsep, hT⟩ := exists_isStep5Cover F F.innerSet_step0_subset
    (F.step1 hδ hdisc).outerSet (F.pipelineSet hδ hdisc r hr) hΩ
    (F.pipelineExponent hδ hdisc r hr) hw₁
  obtain ⟨a, b, ha, hballs⟩ := exists_step5PositiveBalls_bounds F F.step0.innerSet
    (F.step1 hδ hdisc).outerSet (F.pipelineSet hδ hdisc r hr) hΩ
    (F.pipelineExponent hδ hdisc r hr) T w₁
  obtain ⟨T', hT'pos, href, hcomp⟩ := exists_isCRefinement_step5FactorFamily F
    F.innerSet_step0_subset (F.step1 hδ hdisc).outerSet
    (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr) hT ha hballs
  have hT'T : T' ⊆ T := hT'pos.trans (by
    rw [step5PositiveBalls]
    exact Finset.filter_subset _ _)
  refine ⟨a, b, T, T', ha, hTsub, hTsep, hT, hT'pos, hTsep.subset ?_, ?_, ?_⟩
  · exact_mod_cast hT'T
  · simpa only [FactorFamily.pipelineInnerSet] using href
  · intro c hc c' hc'
    have hcomp' := volume_iUnionShade_step5_inter_closedBall_le_two_mul F F.step0.innerSet
      (F.step1 hδ hdisc).outerSet (F.pipelineSet hδ hdisc r hr) hΩ
      (F.pipelineExponent hδ hdisc r hr) hcomp hc hc'
    simpa only [FactorFamily.pipelineInnerSet, FactorFamily.pipelineFamily,
      step5ShadedFactorFamily_innerBody] using hcomp'

namespace Kakeya

/-- The fixed Step 5 loss obtained by self-pigeonholing ball masses. -/
public noncomputable def factoringStep5SelfPigeonholeConstant (n : ℕ) (M : NNReal) : NNReal :=
  4 * factoringStep5OverlapConstant n *
    (2 * factoringStep1FiberPigeonholeConstant 1 M)

/-- The self-pigeonholed Step 5 loss is positive once its finite cover is nonempty. -/
theorem factoringStep5SelfPigeonholeConstant_pos {n : ℕ} {M : NNReal} (hM : 1 ≤ M) :
    0 < factoringStep5SelfPigeonholeConstant n M := by
  have hpigeon : 0 < factoringStep1FiberPigeonholeConstant 1 M :=
    lt_of_lt_of_le zero_lt_one (one_le_factoringStep1FiberPigeonholeConstant hM)
  have hoverNat : 0 < factoringStep5OverlapConstant n := by
    unfold factoringStep5OverlapConstant
    positivity
  have hover : (0 : NNReal) < factoringStep5OverlapConstant n := by
    exact_mod_cast hoverNat
  unfold factoringStep5SelfPigeonholeConstant
  exact mul_pos (mul_pos (by norm_num) hover) (mul_pos (by norm_num) hpigeon)

/-- The self-pigeonholing loss is monotone in an upper bound for the cover cardinality. -/
public theorem factoringStep5SelfPigeonholeConstant_mono {n : ℕ} {M M' : NNReal}
    (hM : M ≤ M') (hM' : 1 ≤ M') :
    factoringStep5SelfPigeonholeConstant n M ≤
      factoringStep5SelfPigeonholeConstant n M' := by
  unfold factoringStep5SelfPigeonholeConstant
  gcongr
  rw [← ENNReal.coe_le_coe]
  rw [coe_factoringStep1FiberPigeonholeConstant,
    coe_factoringStep1FiberPigeonholeConstant]
  apply ENNReal.ofReal_le_ofReal
  by_cases hM0 : M = 0
  · subst M
    have hlog : 0 ≤ Real.logb 2 (M' : ℝ) :=
      Real.logb_nonneg one_lt_two (by exact_mod_cast hM')
    simp only [NNReal.coe_zero, NNReal.coe_one, div_one, Real.logb_zero, add_zero]
    exact le_add_of_nonneg_right hlog
  · gcongr
    norm_num

/-- The self-pigeonholing loss is positive when its cardinality argument is a natural number,
including the empty-cover value zero. -/
public theorem factoringStep5SelfPigeonholeConstant_pos_natCast (n M : ℕ) :
    0 < factoringStep5SelfPigeonholeConstant n (M : NNReal) := by
  rcases M with _ | M
  · have hpigeon : 0 < factoringStep1FiberPigeonholeConstant 1 (0 : NNReal) := by
      rw [← ENNReal.coe_pos, coe_factoringStep1FiberPigeonholeConstant]
      simp
    have hover : (0 : NNReal) < factoringStep5OverlapConstant n := by
      exact_mod_cast (show 0 < factoringStep5OverlapConstant n by
        unfold factoringStep5OverlapConstant
        positivity)
    unfold factoringStep5SelfPigeonholeConstant
    simpa only [Nat.cast_zero] using
      mul_pos (mul_pos (by norm_num) hover) (mul_pos (by norm_num) hpigeon)
  · apply factoringStep5SelfPigeonholeConstant_pos
    exact_mod_cast Nat.succ_pos M

end Kakeya

open Classical in
/-- A sound Step 5 pipeline with loss depending only logarithmically on the cover cardinality.
Unlike `exists_factoringPipeline`, this form does not expose arbitrary lower and upper bounds for
positive ball masses. -/
theorem exists_factoringPipelineSelf [Nontrivial E] (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (r : ℝ) (hr : 0 < r)
    (hΩ : MeasurableSet (F.pipelineSet hδ hdisc r hr)) {w₁ : NNReal} (hw₁ : 0 < w₁) :
    ∃ T T' : Finset E,
      (T : Set E) ⊆ iUnionShade (F.pipelineInnerSet hδ hdisc)
        (step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
          (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr)) ∧
      Metric.IsSeparated (w₁ : ENNReal) (T : Set E) ∧
      iUnionShade (F.pipelineInnerSet hδ hdisc)
          (step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
            (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr)) ⊆
        ⋃ c ∈ T, Metric.closedBall c (w₁ : ℝ) ∧
      (∀ x : E, {c ∈ T | x ∈ Metric.closedBall c (w₁ : ℝ)}.card ≤
        Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E)) ∧
      T' ⊆ T ∧
      (∀ c ∈ T', volume (iUnionShade (F.pipelineInnerSet hδ hdisc)
        (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerBody ∩
          Metric.closedBall c (w₁ : ℝ)) ≠ 0) ∧
      Metric.IsSeparated (w₁ : ENNReal) (T' : Set E) ∧
      IsCRefinement (F.pipelineInnerSet hδ hdisc)
        (step5InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
          (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr) T' w₁)
        (F.pipelineInnerSet hδ hdisc)
        (step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
          (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr))
        (Kakeya.factoringStep5SelfPigeonholeConstant (Module.finrank ℝ E) T.card)⁻¹ ∧
      (∀ c ∈ T', ∀ c' ∈ T',
        volume (iUnionShade (F.pipelineInnerSet hδ hdisc)
            (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerBody ∩
              Metric.closedBall c (w₁ : ℝ)) ≤
          2 * volume (iUnionShade (F.pipelineInnerSet hδ hdisc)
            (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerBody ∩
              Metric.closedBall c' (w₁ : ℝ))) := by
  classical
  let s := F.pipelineInnerSet hδ hdisc
  let V := step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
    (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr)
  let U := iUnionShade s V
  obtain ⟨T, hTsub, hTsep, hTcover, hToverlap⟩ :=
    (isBounded_iUnionShade (s := s) (V := V)).exists_finset_isSeparated_isCover_closedBall hw₁
  let f : E → ENNReal := fun c ↦ volume (U ∩ Metric.closedBall c (w₁ : ℝ))
  have hf : ∀ c ∈ T, f c ≠ ⊤ := by
    intro c _
    exact ne_top_of_le_ne_top (volume_iUnion_shade_ne_top s V)
      (measure_mono Set.inter_subset_left)
  obtain ⟨T', hT'T, hsumf, hcomp, hposf⟩ := exists_self_dyadic T f hf
  let L : ℕ := 2 ^ F.pipelineExponent hδ hdisc r hr *
    2 ^ F.pipelineOuterExponent hδ hdisc r hr
  let w : E → ENNReal := fun c ↦ step5BallMass F F.step0.innerSet
    (F.step1 hδ hdisc).outerSet (F.pipelineSet hδ hdisc r hr) hΩ
    (F.pipelineExponent hδ hdisc r hr) w₁ c
  have hlow : ∀ c : E, (L : ENNReal) * f c ≤ w c := by
    intro c
    exact mul_volume_iUnionShade_inter_le_sum_volume_inter s V _
      Metric.isClosed_closedBall.measurableSet L fun x hx ↦ by
        exact_mod_cast (pipelineStep3_multiplicity F hδ hdisc r hr hΩ hx).1
  have hupp : ∀ c : E, w c ≤ (4 * L : ℕ) * f c := by
    intro c
    simpa [w, f, U, V, s, FactorFamily.pipelineInnerSet, step5BallMass] using
      (sum_volume_inter_le_mul_volume_iUnionShade_inter s V _
        Metric.isClosed_closedBall.measurableSet (4 * L) fun x hx ↦ by
          exact_mod_cast (pipelineStep3_multiplicity F hδ hdisc r hr hΩ hx).2.le)
  have hsumw : ∑ c ∈ T, w c ≤
      (4 * (2 * Kakeya.factoringStep1FiberPigeonholeConstant 1 T.card) : NNReal) *
        ∑ c ∈ T', w c := by
    calc
      ∑ c ∈ T, w c ≤ ∑ c ∈ T, (4 * L : ℕ) * f c :=
        Finset.sum_le_sum fun c _ ↦ hupp c
      _ = (4 * L : ℕ) * ∑ c ∈ T, f c := by rw [Finset.mul_sum]
      _ ≤ (4 * L : ℕ) *
          ((2 * Kakeya.factoringStep1FiberPigeonholeConstant 1 T.card : NNReal) *
            ∑ c ∈ T', f c) := by gcongr
      _ = (4 * (2 * Kakeya.factoringStep1FiberPigeonholeConstant 1 T.card) : NNReal) *
          ((L : ENNReal) * ∑ c ∈ T', f c) := by
        push_cast
        ring
      _ ≤ (4 * (2 * Kakeya.factoringStep1FiberPigeonholeConstant 1 T.card) : NNReal) *
          ∑ c ∈ T', w c := by
        gcongr
        calc
          (L : ENNReal) * ∑ c ∈ T', f c = ∑ c ∈ T', (L : ENNReal) * f c := by
            rw [Finset.mul_sum]
          _ ≤ ∑ c ∈ T', w c := Finset.sum_le_sum fun c _ ↦ hlow c
  have hshade_le_T : ∑ i ∈ s, volume (V i).shade ≤ ∑ c ∈ T, w c := by
    calc
      ∑ i ∈ s, volume (V i).shade ≤
          ∑ i ∈ s, ∑ c ∈ T, volume ((V i).shade ∩ Metric.closedBall c (w₁ : ℝ)) := by
        exact Finset.sum_le_sum fun i hi ↦
          MeasureTheory.measure_le_sum_measure_inter_of_subset_biUnion volume T
            (fun c ↦ Metric.closedBall c (w₁ : ℝ))
            ((Set.subset_iUnion₂_of_subset i hi (Set.Subset.refl _)).trans hTcover)
      _ = ∑ c ∈ T, w c := by
        rw [Finset.sum_comm]
        rfl
  have hT'overlap : ∑ c ∈ T', w c ≤
      (Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E) : ENNReal) *
        ∑ i ∈ s, volume ((step5InnerBody F F.step0.innerSet
          (F.step1 hδ hdisc).outerSet (F.pipelineSet hδ hdisc r hr) hΩ
          (F.pipelineExponent hδ hdisc r hr) T' w₁ i).shade) := by
    simp only [w, step5BallMass]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i hi
    rw [shade_step5InnerBody]
    exact MeasureTheory.sum_measure_inter_le_mul_measure_inter_biUnion
      (μ := volume) hT'T (B := fun c ↦ Metric.closedBall c (w₁ : ℝ))
      (hB := fun _ ↦ Metric.isClosed_closedBall.measurableSet)
      (A := (V i).shade) (hA := (V i).measurableSet_shade)
      (hK := fun x ↦ by
        simpa [Kakeya.factoringStep5OverlapConstant] using hToverlap x)
  have hmass : ∑ i ∈ s, volume (V i).shade ≤
      (Kakeya.factoringStep5SelfPigeonholeConstant (Module.finrank ℝ E) T.card : ENNReal) *
        ∑ i ∈ s, volume ((step5InnerBody F F.step0.innerSet
          (F.step1 hδ hdisc).outerSet (F.pipelineSet hδ hdisc r hr) hΩ
          (F.pipelineExponent hδ hdisc r hr) T' w₁ i).shade) := by
    calc
      ∑ i ∈ s, volume (V i).shade ≤ ∑ c ∈ T, w c := hshade_le_T
      _ ≤ (4 * (2 * Kakeya.factoringStep1FiberPigeonholeConstant 1 T.card) : NNReal) *
          ∑ c ∈ T', w c := hsumw
      _ ≤ (4 * (2 * Kakeya.factoringStep1FiberPigeonholeConstant 1 T.card) : NNReal) *
          ((Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E) : ENNReal) *
            ∑ i ∈ s, volume ((step5InnerBody F F.step0.innerSet
              (F.step1 hδ hdisc).outerSet (F.pipelineSet hδ hdisc r hr) hΩ
              (F.pipelineExponent hδ hdisc r hr) T' w₁ i).shade)) := by gcongr
      _ = (Kakeya.factoringStep5SelfPigeonholeConstant
            (Module.finrank ℝ E) T.card : ENNReal) *
          ∑ i ∈ s, volume ((step5InnerBody F F.step0.innerSet
            (F.step1 hδ hdisc).outerSet (F.pipelineSet hδ hdisc r hr) hΩ
            (F.pipelineExponent hδ hdisc r hr) T' w₁ i).shade) := by
        simp only [Kakeya.factoringStep5SelfPigeonholeConstant]
        push_cast
        ring
  have href : IsCRefinement s (step5InnerBody F F.step0.innerSet
      (F.step1 hδ hdisc).outerSet (F.pipelineSet hδ hdisc r hr) hΩ
      (F.pipelineExponent hδ hdisc r hr) T' w₁) s V
      (Kakeya.factoringStep5SelfPigeonholeConstant (Module.finrank ℝ E) T.card)⁻¹ := by
    refine isCRefinement_of_isRefinement_of_sum_le
      (s' := s) (V' := step5InnerBody F F.step0.innerSet
        (F.step1 hδ hdisc).outerSet (F.pipelineSet hδ hdisc r hr) hΩ
        (F.pipelineExponent hδ hdisc r hr) T' w₁)
      (s := s) (V := V)
      (C := Kakeya.factoringStep5SelfPigeonholeConstant (Module.finrank ℝ E) T.card) ?_ hmass
    exact isRefinement_step5FactorFamily F F.step0.innerSet
      (F.step1 hδ hdisc).outerSet (F.pipelineSet hδ hdisc r hr) hΩ
      (F.pipelineExponent hδ hdisc r hr) T' w₁ s
  refine ⟨T, T', hTsub, hTsep, hTcover, ?_, hT'T, ?_, hTsep.subset ?_, ?_, ?_⟩
  · simpa [Kakeya.factoringStep5OverlapConstant] using hToverlap
  · intro c hc
    have heq := congrArg volume
      (iUnionShade_step5FactorFamily_inter_closedBall F F.step0.innerSet
        (F.step1 hδ hdisc).outerSet (F.pipelineSet hδ hdisc r hr) hΩ
        (F.pipelineExponent hδ hdisc r hr) (w₁ := w₁)
        (F.pipelineInnerSet hδ hdisc) hc)
    change volume (iUnionShade (F.pipelineInnerSet hδ hdisc)
      (step5InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
        (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr) T' w₁) ∩
          Metric.closedBall c (w₁ : ℝ)) ≠ 0
    rw [heq]
    simpa only [f, U, V, s] using hposf c hc
  · exact_mod_cast hT'T
  · simpa only [s, V] using href
  · intro c hc c' hc'
    have hcomp' := volume_iUnionShade_step5_inter_closedBall_le_two_mul
      F F.step0.innerSet (F.step1 hδ hdisc).outerSet
      (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr)
      hcomp hc hc'
    simpa only [s, V, f, FactorFamily.pipelineInnerSet, FactorFamily.pipelineFamily,
      step5ShadedFactorFamily_innerBody] using hcomp'

namespace FactorFamily

variable [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
  (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (r : ℝ) (hr : 0 < r)
  (hΩ : MeasurableSet (F.pipelineSet hδ hdisc r hr)) (T' : Finset E) (w₁ : ℝ≥0)

/-- The outer indices selected by the pipeline form a subfamily of the input outer family. -/
theorem pipelineFamily_outerSet_subset :
    (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).outerSet ⊆ F.outerSet := by
  intro j hj
  change j ∈ (F.step1 hδ hdisc).outerSet at hj
  obtain ⟨i, hi, hpi⟩ := Finset.mem_image.mp (F.outerSet_step1_subset_image hδ hdisc hj)
  rw [← hpi]
  exact F.parent_mem i (F.innerSet_step0_subset hi)

/-- The output inner set is the Step 0 family over the selected Step 1 outer set. -/
@[simp]
theorem pipelineFamily_innerSet :
    (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerSet =
      F.pipelineInnerSet hδ hdisc := rfl

/-- The pipeline keeps the parent map of the input factor family. -/
@[simp]
theorem pipelineFamily_parent :
    (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).parent = F.parent := rfl

/-- The outer carriers before application-specific trimming are the canonical closed
neighbourhood enlargements of the input outer bodies. -/
@[simp]
theorem pipelineFamily_outerBody_toConvexSpaceBody (j : κ) :
    ((F.pipelineFamily hδ hdisc r hr hΩ T' w₁).outerBody j).toConvexSpaceBody =
      (F.outerBody j).cthickening (F.outerBody j).scale := rfl

/-- The pipeline changes inner shadings but not their convex carriers. -/
@[simp]
theorem pipelineFamily_innerBody_toConvexSpaceBody (i : ι) :
    ((F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody := rfl

/-- Every output index survived Step 0, hence its original shading has at least half the original
family's average relative density. -/
theorem pipelineFamily_originalDensity {i : ι}
    (hi : i ∈ (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerSet) :
    ((2⁻¹ : ℝ≥0) : ℝ≥0∞) * (fullness F.innerSet F.innerBody : ℝ≥0∞) *
        volume (F.innerBody i).carrier ≤ volume (F.innerBody i).shade := by
  apply F.le_volume_shade_of_mem_innerSet_step0
  rw [pipelineFamily_innerSet, pipelineInnerSet] at hi
  exact (Finset.mem_filter.mp hi).1

/-- The total carrier volumes of any two surviving fibers are comparable by the sharp Step 1
factor `2`. -/
theorem pipelineFamily_fiberVolume_le_two_mul {j j' : κ}
    (hj : j ∈ (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).outerSet)
    (hj' : j' ∈ (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).outerSet) :
    fiberVolume F (F.pipelineInnerSet hδ hdisc) j ≤
      2 * fiberVolume F (F.pipelineInnerSet hδ hdisc) j' := by
  simpa only [pipelineInnerSet, innerSet_step1] using
    F.fiberVolume_step1_le_two_mul hδ hdisc hj hj'

/-- On the shaded union of each output fiber, its pointwise multiplicity remains in the dyadic
interval selected by Step 2.  Restricting every Step 3 shade by the same Step 5 selection set does
not change the count at a point which survives that restriction. -/
theorem pipelineFamily_fiber_multiplicity {j : κ} {x : E}
    (hx : x ∈ iUnionShade ((F.pipelineFamily hδ hdisc r hr hΩ T' w₁).fiber j)
      (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerBody) :
    2 ^ F.pipelineExponent hδ hdisc r hr ≤
        pointwiseMultiplicity ((F.pipelineFamily hδ hdisc r hr hΩ T' w₁).fiber j)
          (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerBody x ∧
      pointwiseMultiplicity ((F.pipelineFamily hδ hdisc r hr hΩ T' w₁).fiber j)
          (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerBody x <
        2 ^ (F.pipelineExponent hδ hdisc r hr + 1) := by
  classical
  let u := F.step0.innerSet
  let t' := (F.step1 hδ hdisc).outerSet
  let Ω := F.pipelineSet hδ hdisc r hr
  let k := F.pipelineExponent hδ hdisc r hr
  let G := F.pipelineFamily hδ hdisc r hr hΩ T' w₁
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  have hi' : i ∈ G.innerSet ∧ G.parent i = j := by
    simpa only [ShadedFactorFamily.fiber, Finset.mem_filter] using hi
  have hiG : i ∈ G.innerSet := hi'.1
  have hp : G.parent i = j := hi'.2
  have hj : j ∈ t' := by
    have := G.parent_mem i hiG
    simpa [G, t', pipelineFamily] using hp ▸ this
  have hsfiber : G.fiber j = {i ∈ u | F.parent i = j} := by
    rw [ShadedFactorFamily.fiber]
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hqG, hpq⟩
      have hqG' : q ∈ F.pipelineInnerSet hδ hdisc := by
        simpa [G] using hqG
      rw [pipelineInnerSet] at hqG'
      exact ⟨(Finset.mem_filter.mp hqG').1, by simpa [G, pipelineFamily] using hpq⟩
    · rintro ⟨hqu, hpq⟩
      have hqG : q ∈ G.innerSet := by
        change q ∈ F.pipelineInnerSet hδ hdisc
        rw [pipelineInnerSet]
        exact Finset.mem_filter.mpr ⟨hqu, by simpa [hpq] using hj⟩
      exact ⟨hqG, by simpa [G, pipelineFamily] using hpq⟩
  have h3fiber :
      (step3FactorFamily F F.innerSet_step0_subset t' Ω hΩ k).fiber j =
        {i ∈ u | F.parent i = j} :=
    step3FactorFamily_fiber F F.innerSet_step0_subset t' Ω hΩ k hj
  have hxi5 : x ∈ (step5InnerBody F u t' Ω hΩ k T' w₁ i).shade := by
    simpa [G, u, t', Ω, k, pipelineFamily] using hxi
  rw [shade_step5InnerBody] at hxi5
  have hxi' : x ∈ (step3InnerBody F u t' Ω hΩ k i).shade := hxi5.1
  have hx3 : x ∈ iUnionShade
      ((step3FactorFamily F F.innerSet_step0_subset t' Ω hΩ k).fiber j)
      (step3FactorFamily F F.innerSet_step0_subset t' Ω hΩ k).innerBody := by
    refine Set.mem_iUnion₂.mpr ⟨i, ?_, ?_⟩
    · rw [h3fiber, ← hsfiber]
      exact hi
    · simpa only [step3FactorFamily_innerBody] using hxi'
  have hbound := step3FactorFamily_fiber_multiplicity F F.innerSet_step0_subset
    t' Ω hΩ k hx3
  have hsel : x ∈ step5Selection T' w₁ := hxi5.2
  rw [h3fiber] at hbound
  rw [hsfiber]
  simpa [G, u, t', Ω, k, pipelineFamily, pointwiseMultiplicity,
    shade_step5InnerBody, hsel] using hbound

/-- On its shaded union, the complete pipeline family retains the global dyadic multiplicity
interval selected in Steps 2--3.  Step 5 intersects every inner shade with one common selection
set, so at a surviving point it does not change the pointwise count. -/
theorem pipelineFamily_multiplicity {x : E}
    (hx : x ∈ iUnionShade (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerSet
      (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerBody) :
    let L := 2 ^ F.pipelineExponent hδ hdisc r hr *
      2 ^ F.pipelineOuterExponent hδ hdisc r hr
    L ≤ pointwiseMultiplicity (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerSet
        (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerBody x ∧
      pointwiseMultiplicity (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerSet
          (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerBody x < 4 * L := by
  classical
  let V₃ := step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
    (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr)
  let G := F.pipelineFamily hδ hdisc r hr hΩ T' w₁
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  have hxi₅ : x ∈ (step5InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
      (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr) T' w₁ i).shade := by
    simpa [G, pipelineFamily] using hxi
  rw [shade_step5InnerBody] at hxi₅
  have hx₃ : x ∈ iUnionShade (F.pipelineInnerSet hδ hdisc) V₃ := by
    refine Set.mem_iUnion₂.mpr ⟨i, ?_, hxi₅.1⟩
    simpa [G] using hi
  have hbound := pipelineStep3_multiplicity F hδ hdisc r hr hΩ hx₃
  have hsel : x ∈ step5Selection T' w₁ := hxi₅.2
  simpa [G, V₃, pipelineFamily, pipelineInnerSet, pointwiseMultiplicity,
    shade_step5InnerBody, hsel] using hbound

private theorem pipelineStep2Step3_mass
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (r : ℝ) (hr : 0 < r)
    (hΩ : MeasurableSet (F.pipelineSet hδ hdisc r hr)) :
    ((Kakeya.factoringStep2Step3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
        ∑ i ∈ F.pipelineInnerSet hδ hdisc, volume (F.innerBody i).shade ≤
      ∑ i ∈ F.pipelineInnerSet hδ hdisc,
        volume (step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
          (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr) i).shade := by
  let u := F.step0.innerSet
  let t' := (F.step1 hδ hdisc).outerSet
  let Ω := F.pipelineSet hδ hdisc r hr
  let k := F.pipelineExponent hδ hdisc r hr
  let G := step3FactorFamily F F.innerSet_step0_subset t' Ω hΩ k
  have hstep2 :
      ((Kakeya.factoringStep2PigeonholeConstant F.innerSet.card : ℝ≥0∞))⁻¹ *
          ∑ i ∈ F.pipelineInnerSet hδ hdisc, volume (F.innerBody i).shade ≤
        ∫⁻ x in Ω,
          (pointwiseMultiplicity (F.pipelineInnerSet hδ hdisc) F.innerBody x : ℝ≥0∞) := by
    have h := (F.pipelineScaleTriple_spec hδ hdisc r hr).2
    simp_rw [sum_fiberMultiplicity_eq_pointwiseMultiplicity F F.step0.innerSet
      (F.step1 hδ hdisc).outerSet] at h
    have h' := ENNReal.inv_natCast_mul_le_of_le
      (scalePigeonholeConstant_le_factoringStep2PigeonholeConstant le_rfl
        (Finset.card_le_card_of_subset_image F.innerSet_step0_subset
          (F.outerSet_step1_subset_image hδ hdisc))) h
    rw [lintegral_pointwiseMultiplicity_eq_sum_volume_shade F F.step0.innerSet
      (F.step1 hδ hdisc).outerSet] at h'
    simpa only [Ω, pipelineSet, pipelineInnerSet] using h'
  have hC₃0 : (Kakeya.factoringStep3Constant F.innerSet.card : ℝ≥0∞) ≠ 0 := by
    have hpos : 4 ≤ Kakeya.factoringStep3Constant F.innerSet.card :=
      (Kakeya.factoringStep2Constant_pos F.innerSet.card).2
    exact_mod_cast (by omega : Kakeya.factoringStep3Constant F.innerSet.card ≠ 0)
  have hC₃top : (Kakeya.factoringStep3Constant F.innerSet.card : ℝ≥0∞) ≠ ⊤ := by simp
  have hpoint : ∀ x ∈ Ω,
      (pointwiseMultiplicity (F.pipelineInnerSet hδ hdisc) F.innerBody x : ℝ≥0∞) ≤
        (Kakeya.factoringStep3Constant F.innerSet.card : ℝ≥0∞) *
          (pointwiseMultiplicity G.innerSet G.innerBody x : ℝ≥0∞) := by
    intro x hx
    have hb := F.bounds_of_mem_pipelineSet hδ hdisc r hr hx
    have hlower :
        2 ^ F.pipelineExponent hδ hdisc r hr *
            2 ^ F.pipelineOuterExponent hδ hdisc r hr ≤
          pointwiseMultiplicity G.innerSet G.innerBody x := by
      calc
        2 ^ F.pipelineExponent hδ hdisc r hr *
              2 ^ F.pipelineOuterExponent hδ hdisc r hr ≤
            2 ^ F.pipelineExponent hδ hdisc r hr *
              (MultiplicityFamily.dyadicLevel t'
                (fiberMultiplicity F (F.pipelineInnerSet hδ hdisc)) k x).card :=
          Nat.mul_le_mul_left _ hb.2.2.1
        _ ≤ pointwiseMultiplicity G.innerSet G.innerBody x := by
          simpa only [G, u, t', Ω, k, pipelineInnerSet] using
            mul_card_dyadicLevel_le_pointwiseMultiplicity_step3FactorFamily F
              F.innerSet_step0_subset t' Ω hΩ k hx
    exact_mod_cast calc
      pointwiseMultiplicity (F.pipelineInnerSet hδ hdisc) F.innerBody x ≤
          Kakeya.factoringStep2PointwiseConstant F.innerSet.card *
            (2 ^ F.pipelineExponent hδ hdisc r hr *
              2 ^ F.pipelineOuterExponent hδ hdisc r hr) := hb.2.1
      _ ≤ Kakeya.factoringStep2PointwiseConstant F.innerSet.card *
          pointwiseMultiplicity G.innerSet G.innerBody x := Nat.mul_le_mul_left _ hlower
      _ = Kakeya.factoringStep3Constant F.innerSet.card *
          pointwiseMultiplicity G.innerSet G.innerBody x := rfl
  have hstep3 :
      ((Kakeya.factoringStep3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
          ∫⁻ x in Ω,
            (pointwiseMultiplicity (F.pipelineInnerSet hδ hdisc) F.innerBody x : ℝ≥0∞) ≤
        ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
    have hintegral :
        ∫⁻ x in Ω, (Kakeya.factoringStep3Constant F.innerSet.card : ℝ≥0∞)⁻¹ *
            (pointwiseMultiplicity (F.pipelineInnerSet hδ hdisc) F.innerBody x : ℝ≥0∞) ≤
          ∫⁻ x in Ω, (pointwiseMultiplicity G.innerSet G.innerBody x : ℝ≥0∞) := by
      refine lintegral_mono_ae ((ae_restrict_iff' hΩ).2 ?_)
      exact Filter.Eventually.of_forall fun x hx ↦
        (ENNReal.inv_mul_le_iff hC₃0 hC₃top).mpr (hpoint x hx)
    have hsupp : Function.support
        (fun x ↦ (pointwiseMultiplicity G.innerSet G.innerBody x : ℝ≥0∞)) ⊆ Ω := by
      intro x hx
      have hxnat : pointwiseMultiplicity G.innerSet G.innerBody x ≠ 0 := Nat.cast_ne_zero.mp hx
      obtain ⟨i, _, hxi⟩ := (pointwiseMultiplicity_pos_iff G.innerSet G.innerBody x).mp
        (Nat.pos_iff_ne_zero.mpr hxnat)
      change x ∈ (F.innerBody i).shade ∩ Ω ∩ step3DyadicSet F u t' k (F.parent i) at hxi
      exact hxi.1.2
    calc
      ((Kakeya.factoringStep3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
            ∫⁻ x in Ω,
              (pointwiseMultiplicity (F.pipelineInnerSet hδ hdisc) F.innerBody x : ℝ≥0∞) =
          ∫⁻ x in Ω, (Kakeya.factoringStep3Constant F.innerSet.card : ℝ≥0∞)⁻¹ *
            (pointwiseMultiplicity (F.pipelineInnerSet hδ hdisc) F.innerBody x : ℝ≥0∞) := by
        symm
        exact lintegral_const_mul' (μ := volume.restrict Ω)
          (Kakeya.factoringStep3Constant F.innerSet.card : ℝ≥0∞)⁻¹ _ (by simp [hC₃0])
      _ ≤ ∫⁻ x in Ω, (pointwiseMultiplicity G.innerSet G.innerBody x : ℝ≥0∞) :=
        hintegral
      _ = ∫⁻ x, (pointwiseMultiplicity G.innerSet G.innerBody x : ℝ≥0∞) :=
        setLIntegral_eq_of_support_subset hsupp
      _ = ∑ i ∈ G.innerSet, volume (G.innerBody i).shade :=
        (sum_volume_shade_eq_lintegral_pointwiseMultiplicity G.innerSet G.innerBody).symm
  have hC₂0 : (Kakeya.factoringStep2PigeonholeConstant F.innerSet.card : ℝ≥0∞) ≠ 0 := by
    have hpos := (Kakeya.factoringStep2Constant_pos F.innerSet.card).1
    exact_mod_cast (by omega : Kakeya.factoringStep2PigeonholeConstant F.innerSet.card ≠ 0)
  have hC₂top :
      (Kakeya.factoringStep2PigeonholeConstant F.innerSet.card : ℝ≥0∞) ≠ ⊤ := by simp
  calc
    ((Kakeya.factoringStep2Step3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
          ∑ i ∈ F.pipelineInnerSet hδ hdisc, volume (F.innerBody i).shade =
        ((Kakeya.factoringStep3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
          (((Kakeya.factoringStep2PigeonholeConstant F.innerSet.card : ℝ≥0∞))⁻¹ *
            ∑ i ∈ F.pipelineInnerSet hδ hdisc, volume (F.innerBody i).shade) := by
      simp only [Kakeya.factoringStep2Step3Constant, Nat.cast_mul]
      rw [ENNReal.mul_inv (Or.inl hC₂0) (Or.inl hC₂top)]
      ac_rfl
    _ ≤ ((Kakeya.factoringStep3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
        ∫⁻ x in Ω,
          (pointwiseMultiplicity (F.pipelineInnerSet hδ hdisc) F.innerBody x : ℝ≥0∞) :=
      mul_le_mul_right hstep2 _
    _ ≤ ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := hstep3
    _ = ∑ i ∈ F.pipelineInnerSet hδ hdisc,
        volume (step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
          (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr) i).shade := rfl

end FactorFamily

namespace Kakeya

/-- The retained mass fraction of the complete factoring pipeline.  The three factors are the
losses of Step 1 (which already includes Step 0), Steps 2--3, and Step 5. -/
noncomputable def factoringPipelineRefinementConstant (n N : ℕ) (δ a b : ℝ≥0) : ℝ≥0 :=
  (factoringStep1AtScaleConstant n N δ)⁻¹ *
    ((factoringStep2Step3Constant N : ℕ) : ℝ≥0)⁻¹ *
      (factoringStep5PigeonholeConstant (factoringStep5OverlapConstant n) a b)⁻¹

/-- The retained mass fraction of the self-pigeonholed factoring pipeline. -/
noncomputable def factoringPipelineSelfRefinementConstant
    (n N : ℕ) (δ : NNReal) (M : NNReal) : NNReal :=
  (factoringStep1AtScaleConstant n N δ)⁻¹ *
    ((factoringStep2Step3Constant N : ℕ) : NNReal)⁻¹ *
      (factoringStep5SelfPigeonholeConstant n M)⁻¹

end Kakeya

namespace FactorFamily

variable [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
  (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (r : ℝ) (hr : 0 < r)
  (hΩ : MeasurableSet (F.pipelineSet hδ hdisc r hr)) (T' : Finset E) (w₁ : ℝ≥0)

/-- Compose the Step 1, Steps 2--3, and Step 5 refinement ledgers. -/
theorem pipelineFamily_isCRefinement {a b : ℝ≥0}
    (href5 : IsCRefinement (F.pipelineInnerSet hδ hdisc)
      (step5InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
        (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr) T' w₁)
      (F.pipelineInnerSet hδ hdisc)
      (step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
        (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr))
      (Kakeya.factoringStep5PigeonholeConstant
        (Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E)) a b)⁻¹) :
    IsCRefinement (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerSet
      (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerBody F.innerSet F.innerBody
      (Kakeya.factoringPipelineRefinementConstant
        (Module.finrank ℝ E) F.innerSet.card δ a b) := by
  have href23 : IsCRefinement (F.pipelineInnerSet hδ hdisc)
      (step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
        (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr))
      (F.step1 hδ hdisc).innerSet (F.step1 hδ hdisc).innerBody
      ((Kakeya.factoringStep2Step3Constant F.innerSet.card : ℕ) : ℝ≥0)⁻¹ := by
    constructor
    · constructor
      · rw [pipelineInnerSet, innerSet_step1]
      · intro i hi
        rw [innerBody_step1]
        refine ⟨rfl, ?_⟩
        intro x hx
        exact hx.1.1
    · have hCnat : Kakeya.factoringStep2Step3Constant F.innerSet.card ≠ 0 := by
        rw [Kakeya.factoringStep2Step3Constant_eq]
        positivity
      have hC : (Kakeya.factoringStep2Step3Constant F.innerSet.card : ℝ≥0) ≠ 0 := by
        exact_mod_cast hCnat
      have hmass := pipelineStep2Step3_mass F hδ hdisc r hr hΩ
      rw [ENNReal.coe_inv hC]
      simpa only [pipelineInnerSet, innerBody_step1, innerSet_step1,
        ENNReal.coe_natCast] using hmass
  have href35 := href5.trans href23
  have href := href35.trans (F.isCRefinement_step1 hδ hdisc)
  rw [pipelineFamily_innerSet]
  simpa only [pipelineFamily, step5ShadedFactorFamily_innerBody,
    Kakeya.factoringPipelineRefinementConstant, mul_assoc] using href

/-- Compose the Step 1, Steps 2--3, and self-pigeonholed Step 5 refinement ledgers. -/
theorem pipelineFamily_isCRefinementSelf {M : NNReal}
    (href5 : IsCRefinement (F.pipelineInnerSet hδ hdisc)
      (step5InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
        (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr) T' w₁)
      (F.pipelineInnerSet hδ hdisc)
      (step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
        (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr))
      (Kakeya.factoringStep5SelfPigeonholeConstant (Module.finrank ℝ E) M)⁻¹) :
    IsCRefinement (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerSet
      (F.pipelineFamily hδ hdisc r hr hΩ T' w₁).innerBody F.innerSet F.innerBody
      (Kakeya.factoringPipelineSelfRefinementConstant
        (Module.finrank ℝ E) F.innerSet.card δ M) := by
  have href23 : IsCRefinement (F.pipelineInnerSet hδ hdisc)
      (step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
        (F.pipelineSet hδ hdisc r hr) hΩ (F.pipelineExponent hδ hdisc r hr))
      (F.step1 hδ hdisc).innerSet (F.step1 hδ hdisc).innerBody
      ((Kakeya.factoringStep2Step3Constant F.innerSet.card : ℕ) : NNReal)⁻¹ := by
    constructor
    · constructor
      · rw [pipelineInnerSet, innerSet_step1]
      · intro i hi
        rw [innerBody_step1]
        refine ⟨rfl, ?_⟩
        intro x hx
        exact hx.1.1
    · have hCnat : Kakeya.factoringStep2Step3Constant F.innerSet.card ≠ 0 := by
        rw [Kakeya.factoringStep2Step3Constant_eq]
        positivity
      have hC : (Kakeya.factoringStep2Step3Constant F.innerSet.card : NNReal) ≠ 0 := by
        exact_mod_cast hCnat
      have hmass := pipelineStep2Step3_mass F hδ hdisc r hr hΩ
      rw [ENNReal.coe_inv hC]
      simpa only [pipelineInnerSet, innerBody_step1, innerSet_step1,
        ENNReal.coe_natCast] using hmass
  have href35 := href5.trans href23
  have href := href35.trans (F.isCRefinement_step1 hδ hdisc)
  rw [pipelineFamily_innerSet]
  simpa only [pipelineFamily, step5ShadedFactorFamily_innerBody,
    Kakeya.factoringPipelineSelfRefinementConstant, mul_assoc] using href

end FactorFamily

end ShadedBody
