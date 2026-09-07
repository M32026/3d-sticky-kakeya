/-
# Perimeter equals total variation

Helper lemmas for `perimeter_eq_variation`.

## Main lemmas

- `boundedFunc_variation_bound`: norm bound for vector measure integrals
- `signed_abs_le_totalVariation`: `|s E| ≤ s.totalVariation E`
- `perimeter_le_variation_of_integral_formula`: `P(S) ≤ |Dχ_S|(univ)` (conditional)
-/

import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.SmoothApprox
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Tactic

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.Perimeter

variable {n : ℕ}

/-- The inner product as a continuous bilinear map `E n → E n → ℝ`. -/
noncomputable def innerBilinear : (E n) →L[ℝ] (E n) →L[ℝ] ℝ :=
  IsBoundedBilinearMap.toContinuousLinearMap
    (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E n))

lemma innerBilinear_apply (v w : E n) :
    innerBilinear v w = inner ℝ v w := by
  rfl

/-- The norm of the functional `v ↦ inner(v, w)` equals `‖w‖`. -/
lemma innerFunctional_norm (w : E n) :
    ‖(innerBilinear.flip w)‖ = ‖w‖ := by
  let f : (E n) →L[ℝ] ℝ := innerBilinear.flip w
  have h1 : ∀ (v : E n), f v = inner ℝ v w := by
    intro v; rfl
  have h_upper : ‖f‖ ≤ ‖w‖ := by
    apply ContinuousLinearMap.opNorm_le_bound
    · exact norm_nonneg w
    · intro v
      rw [h1]
      have hcs : |inner ℝ v w| ≤ ‖v‖ * ‖w‖ := abs_real_inner_le_norm v w
      have h_abs : ‖inner ℝ v w‖ = |inner ℝ v w| := by simp
      rw [h_abs]
      have hcs' : |inner ℝ v w| ≤ ‖w‖ * ‖v‖ := by
        rw [mul_comm ‖w‖] at * <;> exact hcs
      exact hcs'
  have h_lower : ‖w‖ ≤ ‖f‖ := by
    by_cases h0 : w = 0
    · rw [h0] <;> simp
    · have hpos : 0 < ‖w‖ := norm_pos_iff.mpr h0
      have h2 : ‖f w‖ = ‖w‖ ^ 2 := by
        have h3 : f w = inner ℝ w w := h1 w
        rw [h3, inner_self_eq_norm_sq_to_K]
        <;> simp [abs_of_nonneg (show 0 ≤ ‖w‖ ^ 2 by positivity)]
      have h3 : ‖f w‖ ≤ ‖f‖ * ‖w‖ := f.le_opNorm w
      rw [h2] at h3
      have h4 : ‖w‖ ^ 2 ≤ ‖f‖ * ‖w‖ := h3
      have h5 : ‖w‖ ≤ ‖f‖ := by
        calc
          ‖w‖ = ‖w‖ ^ 2 / ‖w‖ := by
            field_simp [hpos.ne'] <;> ring
          _ ≤ (‖f‖ * ‖w‖) / ‖w‖ := by gcongr
          _ = ‖f‖ := by
            field_simp [hpos.ne'] <;> ring
      exact h5
  exact le_antisymm h_upper h_lower

/-- For any vector measure `μ`, the transpose by `innerBilinear` is dominated
by `μ.variation` with constant 1. -/
lemma innerBilinear_domination {X : Type*} [MeasurableSpace X]
    (μ : VectorMeasure X (E n)) :
    DominatedFinMeasAdditive μ.variation (μ.transpose innerBilinear) 1 := by
  refine ⟨fun s t hs ht _ _ hdisj ↦ cbmApplyMeasure_union μ innerBilinear hs ht hdisj,
    fun s hs hsf ↦ ?_⟩
  have h1 : (μ.transpose innerBilinear) s = innerBilinear.flip (μ s) := by rfl
  rw [h1, innerFunctional_norm (μ s)]
  have h2 : ‖μ s‖ ≤ μ.variation.real s :=
    VectorMeasure.norm_measure_le_variation (hE := hsf.ne)
  simpa [one_mul] using h2

/-- If `‖f x‖ ≤ 1` a.e., then `‖∫ᵛ x, f x ∂[innerBilinear; μ]‖ₑ ≤ μ.variation(univ)`. -/
lemma boundedFunc_variation_bound {X : Type*} [MeasurableSpace X]
    (μ : VectorMeasure X (E n)) (f : X → E n)
    (hf : μ.Integrable f) (hg : ∀ᵐ x ∂μ.variation, ‖f x‖ₑ ≤ 1) :
    ‖∫ᵛ x, f x ∂[innerBilinear; μ]‖ₑ ≤ μ.variation Set.univ := by
  let h_dom := innerBilinear_domination μ
  let h_default := dominatedFinMeasAdditive_cbmApplyMeasure μ innerBilinear
  have h_eq1 : ∫ᵛ x, f x ∂[innerBilinear; μ] =
      setToFun μ.variation (μ.transpose innerBilinear) h_default f :=
    VectorMeasure.integral_eq_setToFun (f := f)
  have h_switch : setToFun μ.variation (μ.transpose innerBilinear) h_default f =
      setToFun μ.variation (μ.transpose innerBilinear) h_dom f :=
    setToFun_congr_left' h_default h_dom
      (fun s _ _ => rfl) f
  rw [h_eq1, h_switch]
  have h_main : ‖setToFun μ.variation (μ.transpose innerBilinear) h_dom f‖ₑ ≤
      (1 : ENNReal) * ∫⁻ x, ‖f x‖ₑ ∂μ.variation :=
    enorm_setToFun_le h_dom (by positivity)
  have h1 : ∫⁻ x, ‖f x‖ₑ ∂μ.variation ≤ μ.variation Set.univ := by
    have h2 : ∀ᵐ x ∂μ.variation, ‖f x‖ₑ ≤ 1 := hg
    have h3 : ∫⁻ x, ‖f x‖ₑ ∂μ.variation ≤ ∫⁻ x, (1 : ENNReal) ∂μ.variation :=
      lintegral_mono_ae h2
    simpa using h3
  have h_main' : ‖setToFun μ.variation (μ.transpose innerBilinear) h_dom f‖ₑ ≤
      ∫⁻ x, ‖f x‖ₑ ∂μ.variation := by
    simpa [one_mul] using h_main
  exact h_main'.trans h1

/-- For a signed measure `s` and measurable set `E`,
`ENNReal.ofReal |s E| ≤ s.totalVariation E`. -/
lemma signed_abs_le_totalVariation (s : SignedMeasure (E n)) {E : Set (E n)}
    (hE : MeasurableSet E) :
    ENNReal.ofReal |s E| ≤ s.totalVariation E := by
  let jd := s.toJordanDecomposition
  let p := jd.posPart
  let q := jd.negPart
  haveI : IsFiniteMeasure p := jd.posPart_finite
  haveI : IsFiniteMeasure q := jd.negPart_finite
  have hpos : 0 ≤ (p E).toReal := by positivity
  have hneg : 0 ≤ (q E).toReal := by positivity
  have h4 : s E = (p E).toReal - (q E).toReal := by
    have h_eq1 : jd.toSignedMeasure = s := SignedMeasure.toSignedMeasure_toJordanDecomposition s
    have h : jd.toSignedMeasure E = (p E).toReal - (q E).toReal := by
      rw [JordanDecomposition.toSignedMeasure]
      exact Measure.toSignedMeasure_sub_apply hE
    rw [h_eq1] at h
    exact h
  rw [h4]
  have h5 : |(p E).toReal - (q E).toReal| ≤ (p E).toReal + (q E).toReal := by
    calc |(p E).toReal - (q E).toReal|
      ≤ |(p E).toReal| + |(q E).toReal| := by exact abs_sub _ _
    _ = (p E).toReal + (q E).toReal := by
      rw [abs_of_nonneg hpos, abs_of_nonneg hneg]
  have h7 : (p E + q E).toReal = (p E).toReal + (q E).toReal :=
    ENNReal.toReal_add (measure_lt_top p E).ne (measure_lt_top q E).ne
  have hp_lt : p E < ⊤ := measure_lt_top p E
  have hq_lt : q E < ⊤ := measure_lt_top q E
  have hfin : p E + q E ≠ ⊤ := (ENNReal.add_lt_top.mpr ⟨hp_lt, hq_lt⟩).ne
  have h6 : ENNReal.ofReal |(p E).toReal - (q E).toReal| ≤ p E + q E := by
    rw [ENNReal.ofReal_le_iff_le_toReal hfin]
    rw [h7]
    exact h5
  simpa [SignedMeasure.totalVariation] using h6

/-- Standard coordinate embedding `r ↦ r·e_i`. -/
noncomputable def coordHom (i : Fin n) : ℝ →+ E n :=
  { toFun := fun r : ℝ => r • EuclideanSpace.single i (1 : ℝ)
    map_zero' := by simp
    map_add' := by intro a b; simp [add_smul] }

/-- Continuity of `coordHom`. -/
lemma coordHom_cont (i : Fin n) : Continuous (coordHom i) := by
  simp [coordHom]
  fun_prop

/-- The De Giorgi perimeter is bounded by the total variation of a vector measure `D`
that represents `Dχ_S`.

Takes as hypotheses:
- `D`: the vector measure (typically `distributionalDerivative S`)
- `μs`: coordinate signed measures
- `hD`: `D = ∑ mapRange (coordHom i) (μs i)`
- `hμ_bound`: each `μs i.totalVariation univ ≤ perimeter S`
- `h_int`: integration formula `∫ᵛ φ · dD = ∫_S div φ`
-/
lemma perimeter_le_variation_of_integral_formula
    (S : Set (E n)) (hfin : perimeter S < ⊤)
    (D : VectorMeasure (E n) (E n))
    (μs : Fin n → SignedMeasure (E n))
    (hD : D = ∑ i : Fin n, (μs i).mapRange (coordHom i) (coordHom_cont i))
    (hμ_bound : ∀ i : Fin n, (μs i).totalVariation Set.univ ≤ perimeter S)
    (h_int : ∀ (φ : E n → E n), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ᵛ x, φ x ∂[innerBilinear; D] = ∫ x in S, divergence φ x) :
    perimeter S ≤ D.variation Set.univ := by
  let μ := D.variation

  have h_mapRange_bound : ∀ i : Fin n,
      ((μs i).mapRange (coordHom i) (coordHom_cont i)).variation ≤ (μs i).totalVariation := by
    intro i
    let ν := (μs i).mapRange (coordHom i) (coordHom_cont i)
    apply Measure.le_iff.mpr
    intro s hs
    have h1 : ∀ (E : Set (E n)), MeasurableSet E → E ⊆ s →
        ‖ν E‖ₑ ≤ (μs i).totalVariation E := by
      intro E hE _
      have h21 : ν E = (coordHom i) ((μs i) E) := by rw [VectorMeasure.mapRange_apply]
      rw [h21]
      have h22 : (coordHom i) ((μs i) E) = (μs i) E • EuclideanSpace.single i (1 : ℝ) := by rfl
      rw [h22]
      have hnorm : ‖(μs i) E • EuclideanSpace.single i (1 : ℝ)‖ = |(μs i) E| := by
        simp [norm_smul, PiLp.norm_single]
      have henorm : ‖(μs i) E • EuclideanSpace.single i (1 : ℝ)‖ₑ =
          ENNReal.ofReal ‖(μs i) E • EuclideanSpace.single i (1 : ℝ)‖ := by
        simp [enorm] <;> rfl
      rw [henorm, hnorm]
      exact signed_abs_le_totalVariation (μs i) hE
    exact VectorMeasure.variation_apply_le_of_forall_enorm_le hs h1

  have h_sum_measure : D.variation ≤ ∑ i : Fin n, ((μs i).mapRange (coordHom i) (coordHom_cont i)).variation := by
    rw [hD]
    exact VectorMeasure.variation_finsetSum_le (Finset.univ) _

  have hμ_fin : μ Set.univ < ⊤ := by
    have hcard_lt : (Finset.card (Finset.univ : Finset (Fin n)) : ENNReal) < ⊤ :=
      ENNReal.natCast_lt_top _
    calc μ Set.univ
      ≤ (∑ i : Fin n, ((μs i).mapRange (coordHom i) (coordHom_cont i)).variation) Set.univ :=
        h_sum_measure Set.univ
    _ = ∑ i : Fin n, ((μs i).mapRange (coordHom i) (coordHom_cont i)).variation Set.univ := by
        simp [Finset.sum_apply] <;> rfl
    _ ≤ ∑ i : Fin n, (μs i).totalVariation Set.univ := by
        gcongr with i _
        exact h_mapRange_bound i
    _ ≤ ∑ i : Fin n, perimeter S := by gcongr with i _; exact hμ_bound i
    _ = (Finset.card (Finset.univ : Finset (Fin n)) : ENNReal) * perimeter S := by simp
    _ < ⊤ := ENNReal.mul_lt_top hcard_lt hfin

  letI : IsFiniteMeasure μ := ⟨hμ_fin⟩

  apply iSup_le
  intro φ
  have hsmooth : ContDiff ℝ ∞ φ.toFun := φ.smooth
  have h_eq : ∫ x in S, divergence φ.toFun x =
      ∫ᵛ x, φ.toFun x ∂[innerBilinear; D] :=
    (h_int φ.toFun hsmooth φ.compact).symm
  have h_integrable : D.Integrable φ.toFun := by
    have h_cont : Continuous φ.toFun := φ.smooth.continuous
    exact h_cont.integrable_of_hasCompactSupport φ.compact
  have h_bound : ∀ᵐ x ∂μ, ‖φ.toFun x‖ₑ ≤ 1 := by
    filter_upwards with x
    have h : ‖φ.toFun x‖ ≤ 1 := φ.bound x
    simpa [enorm, Real.norm_eq_abs] using ENNReal.ofReal_le_one.mpr h
  have h_main : ‖∫ᵛ x, φ.toFun x ∂[innerBilinear; D]‖ₑ ≤ μ Set.univ :=
    boundedFunc_variation_bound D φ.toFun h_integrable h_bound
  have h_final : ‖∫ x in S, divergence φ.toFun x‖ₑ ≤ μ Set.univ := by
    rw [h_eq]
    exact h_main
  have h_goal : ENNReal.ofReal |∫ x in S, divergence φ.toFun x| ≤ D.variation Set.univ := by
    have h9 : ‖∫ x in S, divergence φ.toFun x‖ₑ = ENNReal.ofReal |∫ x in S, divergence φ.toFun x| :=
      Real.enorm_eq_ofReal_abs (∫ x in S, divergence φ.toFun x)
    rw [h9] at h_final
    exact h_final
  exact h_goal

/-- Absolute value bound for vector measure integrals:
`|∫ᵛ f dD| ≤ ∫ ‖f‖ d|D|`. -/
lemma vectorMeasure_integral_abs_bound
    (D : VectorMeasure (E n) (E n)) (f : E n → E n) (hf : D.Integrable f) :
    |∫ᵛ x, f x ∂[innerBilinear; D]| ≤ ∫ x, ‖f x‖ ∂D.variation := by
  let ν := D.variation
  let h_dom := innerBilinear_domination D
  let h_default := dominatedFinMeasAdditive_cbmApplyMeasure D innerBilinear
  have h1 : ∫ᵛ x, f x ∂[innerBilinear; D] =
      setToFun ν (D.transpose innerBilinear) h_dom f := by
    rw [VectorMeasure.integral_eq_setToFun]
    exact setToFun_congr_left' h_default h_dom (fun s _ _ => rfl) f
  rw [h1]
  have h2 : ‖setToFun ν (D.transpose innerBilinear) h_dom f‖ ≤
      (1 : ℝ) * ‖hf.toL1 f‖ := norm_setToFun_le h_dom hf (by norm_num)
  have h3 : ‖hf.toL1 f‖ = ∫ x, ‖f x‖ ∂ν := by
    rw [Integrable.norm_toL1_eq_lintegral_enorm f hf]
    have h41 : ∫ x, ‖f x‖ ∂ν = (∫⁻ x, ‖f x‖ₑ ∂ν).toReal :=
      integral_norm_eq_lintegral_enorm hf.1
    exact h41.symm
  rw [h3] at h2
  simpa [one_mul] using h2

/-- Norm bound for a finite sum of functions with pairwise disjoint supports,
each bounded by 1. -/
lemma norm_sum_disjoint_le_one {X : Type*} {E : Type*} [NormedAddCommGroup E]
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → X → E}
    (h_disj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (f i)) (Function.support (f j)))
    (h_bound : ∀ i ∈ s, ∀ x, ‖f i x‖ ≤ 1) :
    ∀ x, ‖∑ i ∈ s, f i x‖ ≤ 1 := by
  intro x
  by_cases h : ∃ i ∈ s, f i x ≠ 0
  · rcases h with ⟨i, hi, hne⟩
    have h1 : ∀ j ∈ s, j ≠ i → f j x = 0 := by
      intro j hj hne2
      have h_supp_disj : Disjoint (Function.support (f i)) (Function.support (f j)) :=
        h_disj i hi j hj hne2.symm
      have h_i_in : x ∈ Function.support (f i) := by simpa [Function.support] using hne
      have h_j_not : x ∉ Function.support (f j) := Set.disjoint_left.mp h_supp_disj h_i_in
      simpa [Function.support] using h_j_not
    have hsum : ∑ j ∈ s, f j x = f i x := by
      have h2 : ∑ j ∈ s, f j x = f i x + ∑ j ∈ s.erase i, f j x := by
        have h4 : ∑ j ∈ insert i (s.erase i), f j x = f i x + ∑ j ∈ s.erase i, f j x :=
          Finset.sum_insert (by simp)
        have h5 : insert i (s.erase i) = s := Finset.insert_erase hi
        rw [h5] at h4
        exact h4
      have h3 : ∑ j ∈ s.erase i, f j x = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact h1 j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
      rw [h2, h3, add_zero]
    rw [hsum]
    exact h_bound i hi x
  · have h_all_zero : ∀ i ∈ s, f i x = 0 := by
      intro i hi
      by_contra hne
      exact h ⟨i, hi, hne⟩
    have hsum : ∑ i ∈ s, f i x = 0 := by
      rw [Finset.sum_congr rfl h_all_zero]
      simp
    rw [hsum] <;> simp

/-- Integral of an indicator function against a vector measure. -/
lemma indicatorIntegral
    (D : VectorMeasure (E n) (E n)) [IsFiniteMeasure D.variation]
    {p : Set (E n)} (hpm : MeasurableSet p) (hνp : D.variation p ≠ ⊤)
    (v : E n) :
    ∫ᵛ x, (Set.indicator p (fun _ : E n => v)) x ∂[innerBilinear; D] =
      innerBilinear v (D p) := by
  let h_dom := innerBilinear_domination D
  let h_default := dominatedFinMeasAdditive_cbmApplyMeasure D innerBilinear
  have h_eq1 : ∫ᵛ x, (Set.indicator p (fun _ : E n => v)) x ∂[innerBilinear; D] =
      setToFun D.variation (D.transpose innerBilinear) h_default
        (Set.indicator p (fun _ : E n => v)) :=
    VectorMeasure.integral_eq_setToFun (f := Set.indicator p (fun _ : E n => v))
  have h_switch : setToFun D.variation (D.transpose innerBilinear) h_default
        (Set.indicator p (fun _ : E n => v)) =
      setToFun D.variation (D.transpose innerBilinear) h_dom
        (Set.indicator p (fun _ : E n => v)) :=
    setToFun_congr_left' h_default h_dom (fun s _ _ => rfl)
      (Set.indicator p (fun _ : E n => v))
  have h_final : setToFun D.variation (D.transpose innerBilinear) h_dom
        (Set.indicator p (fun _ : E n => v)) =
      innerBilinear v (D p) :=
    setToFun_indicator_const h_dom hpm hνp v
  rw [h_eq1, h_switch, h_final]

/-- Finite sum linearity for vector measure integrals. -/
lemma vectorMeasure_integral_finsetSum
    (D : VectorMeasure (E n) (E n)) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → E n → E n)
    (hf : ∀ i ∈ s, D.Integrable (f i)) :
    ∫ᵛ x, (∑ i ∈ s, f i) x ∂[innerBilinear; D] =
      ∑ i ∈ s, ∫ᵛ x, f i x ∂[innerBilinear; D] := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h4 : ∀ i ∈ s, D.Integrable (f i) := fun i hi => hf i (Finset.mem_insert.mpr (Or.inr hi))
    have h5 : D.Integrable (∑ i ∈ s, f i) := VectorMeasure.Integrable.finsetSum s h4
    have h_sum : (∑ i ∈ insert a s, f i) = f a + ∑ i ∈ s, f i := by
      funext x; simp [Finset.sum_insert ha]
    rw [h_sum]
    rw [VectorMeasure.integral_add (hf a (Finset.mem_insert.mpr (Or.inl rfl))) h5]
    rw [ih h4]
    <;> simp [Finset.sum_insert ha]

/-- Given pairwise disjoint measurable sets `P` and unit vectors `v p`,
construct `g = ∑ v_p · 1_p` with norm bound, integrability, and integral formula. -/
lemma partitionSimpleFunc
    (D : VectorMeasure (E n) (E n)) [IsFiniteMeasure D.variation]
    (P : Finset (Set (E n)))
    (hP_meas : ∀ p ∈ P, MeasurableSet p)
    (hP_disj : (P : Set (Set (E n))).PairwiseDisjoint id)
    (v : Set (E n) → E n)
    (hv_bound : ∀ p ∈ P, ‖v p‖ ≤ 1) :
    ∃ (g : E n → E n), (∀ x, ‖g x‖ ≤ 1) ∧ D.Integrable g ∧
      (∫ᵛ x, g x ∂[innerBilinear; D] = ∑ p ∈ P, innerBilinear (v p) (D p)) := by
  let g_p (p : Set (E n)) : E n → E n := Set.indicator p (fun _ : E n => v p)
  let g : E n → E n := ∑ p ∈ P, g_p p
  have h_supp_disj : ∀ (p : Set (E n)) (hp : p ∈ P) (q : Set (E n)) (hq : q ∈ P),
      p ≠ q → Disjoint (Function.support (g_p p)) (Function.support (g_p q)) := by
    intro p hp q hq hne
    have h1 : Function.support (g_p p) ⊆ p := by
      intro x hx
      by_contra h4
      have h5 : g_p p x = 0 := by
        dsimp only [g_p]
        exact if_neg h4
      exact hx h5
    have h2 : Function.support (g_p q) ⊆ q := by
      intro x hx
      by_contra h4
      have h5 : g_p q x = 0 := by
        dsimp only [g_p]
        exact if_neg h4
      exact hx h5
    have h3 : Disjoint p q := hP_disj hp hq hne
    exact Disjoint.mono h1 h2 h3
  have h_bound_all : ∀ (p : Set (E n)) (hp : p ∈ P) (x : E n), ‖g_p p x‖ ≤ 1 := by
    intro p hp x
    by_cases hx : x ∈ p
    · have h4 : g_p p x = v p := by
        dsimp only [g_p]
        exact if_pos hx
      rw [h4]; exact hv_bound p hp
    · have h4 : g_p p x = 0 := by
        dsimp only [g_p]
        exact if_neg hx
      rw [h4] <;> simp
  have hg_bound : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    have h_eq : g x = ∑ p ∈ P, g_p p x := by
      simp only [g, Finset.sum_apply]
    rw [h_eq]
    exact norm_sum_disjoint_le_one h_supp_disj h_bound_all x
  have hgp_int : ∀ p ∈ P, D.Integrable (g_p p) := by
    intro p hp
    have hpm : MeasurableSet p := hP_meas p hp
    have h3 : Measurable (g_p p) := measurable_const.indicator hpm
    have h4 : AEStronglyMeasurable (g_p p) D.variation := h3.aestronglyMeasurable
    have h6 : ∀ x, ‖g_p p x‖ₑ ≤ 1 := by
      intro x
      by_cases hx : x ∈ p
      · have h7 : g_p p x = v p := by
          dsimp only [g_p]; exact if_pos hx
        rw [h7]
        simpa [enorm] using ENNReal.ofReal_le_one.mpr (hv_bound p hp)
      · have h7 : g_p p x = 0 := by
          dsimp only [g_p]; exact if_neg hx
        rw [h7]; simp
    have h7 : ∫⁻ x, ‖g_p p x‖ₑ ∂D.variation ≤ D.variation univ := by
      calc ∫⁻ x, ‖g_p p x‖ₑ ∂D.variation
          ≤ ∫⁻ x, (1 : ENNReal) ∂D.variation := lintegral_mono h6
        _ = D.variation univ := by simp
    have h10 : ∫⁻ x, ‖g_p p x‖ₑ ∂D.variation < ⊤ :=
      h7.trans_lt (measure_lt_top D.variation univ)
    exact ⟨h4, h10⟩
  have hg_int : D.Integrable g :=
    VectorMeasure.Integrable.finsetSum P hgp_int
  have h_indicator_int : ∀ p ∈ P, ∫ᵛ x, g_p p x ∂[innerBilinear; D] =
      innerBilinear (v p) (D p) := by
    intro p hp
    have hpm : MeasurableSet p := hP_meas p hp
    have hνp : D.variation p ≠ ⊤ := measure_ne_top D.variation p
    exact indicatorIntegral D hpm hνp (v p)
  have h_g : g = ∑ p ∈ P, g_p p := by rfl
  have h_integral : ∫ᵛ x, g x ∂[innerBilinear; D] = ∑ p ∈ P, innerBilinear (v p) (D p) := by
    rw [h_g]
    rw [vectorMeasure_integral_finsetSum D P g_p hgp_int]
    apply Finset.sum_congr rfl
    intro p hp
    exact h_indicator_int p hp
  exact ⟨g, hg_bound, hg_int, h_integral⟩

/-- The total variation of `D` is bounded by the De Giorgi perimeter. -/
lemma variation_le_perimeter_of_integral_formula
    (S : Set (E n)) (hfin : perimeter S < ⊤)
    (D : VectorMeasure (E n) (E n))
    (hD_fin : D.variation Set.univ < ⊤)
    [D.variation.Regular]
    (h_int : ∀ (φ : E n → E n), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ᵛ x, φ x ∂[innerBilinear; D] = ∫ x in S, divergence φ x) :
    D.variation Set.univ ≤ perimeter S := by
  let ν := D.variation
  letI : IsFiniteMeasure ν := ⟨hD_fin⟩
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hP_lt
  set ε2 : NNReal := ε / 2 with hε2_def
  have hε2_pos : 0 < ε2 := by positivity
  set ε2r : ℝ := (ε2 : ℝ) with hε2r_def
  have hε2r_pos : 0 < ε2r := by positivity
  rcases VectorMeasure.exists_variation_le_add D MeasurableSet.univ hε2_pos hD_fin.ne with
    ⟨P, hP_sub, hP_disj, hP_meas, hP_sum⟩
  let v : Set (E n) → E n := fun p =>
    if h : D p = 0 then 0 else (‖D p‖⁻¹ : ℝ) • D p
  have hv_bound : ∀ p ∈ P, ‖v p‖ ≤ 1 := by
    intro p _
    dsimp only [v]
    by_cases h : D p = 0
    · rw [dif_pos h]; simp
    · rw [dif_neg h]
      have hpos : 0 < ‖D p‖ := norm_pos_iff.mpr h
      have hnorm : ‖(‖D p‖⁻¹ : ℝ) • D p‖ = 1 := by
        rw [norm_smul]
        have h5 : ‖(‖D p‖⁻¹ : ℝ)‖ = ‖D p‖⁻¹ := by
          simp [abs_of_pos (show 0 < (‖D p‖⁻¹ : ℝ) from by positivity)]
        rw [h5]
        field_simp [hpos.ne'] <;> ring
      rw [hnorm] <;> norm_num
  have hv_inner : ∀ p ∈ P, inner ℝ (v p) (D p) = ‖D p‖ := by
    intro p _
    dsimp only [v]
    by_cases h : D p = 0
    · rw [dif_pos h, h]; simp
    · rw [dif_neg h]
      have hpos : 0 < ‖D p‖ := norm_pos_iff.mpr h
      have h1 : inner ℝ ((‖D p‖⁻¹ : ℝ) • D p) (D p) = (‖D p‖⁻¹ : ℝ) * inner ℝ (D p) (D p) := by
        rw [inner_smul_left] <;> simp
      rw [h1]
      have h2 : inner ℝ (D p) (D p) = ‖D p‖ ^ 2 := by
        have h21 : inner ℝ (D p) (D p) = ↑‖D p‖ ^ 2 := inner_self_eq_norm_sq_to_K (D p)
        exact_mod_cast h21
      rw [h2]
      field_simp [hpos.ne'] <;> ring
  rcases partitionSimpleFunc D P hP_meas hP_disj v hv_bound with
    ⟨g, hg_bound, hg_int, hg_integral⟩
  have h_integral : ∫ᵛ x, g x ∂[innerBilinear; D] = ∑ p ∈ P, ‖D p‖ := by
    rw [hg_integral]
    apply Finset.sum_congr rfl
    intro p hp
    rw [innerBilinear_apply, hv_inner p hp]
  rcases smooth_approx_simpleFunc D g hg_int hg_bound (hε := hε2r_pos) with
    ⟨φ, hφ_smooth, hφ_supp, hφ_bound, hφ_L1⟩
  have hφ_int : D.Integrable φ :=
    hφ_smooth.continuous.integrable_of_hasCompactSupport hφ_supp
  have h_int_sub : ∫ᵛ x, g x - φ x ∂[innerBilinear; D] =
      ∫ᵛ x, g x ∂[innerBilinear; D] - ∫ᵛ x, φ x ∂[innerBilinear; D] :=
    VectorMeasure.integral_fun_sub hg_int hφ_int
  have h_diff : |∫ᵛ x, g x ∂[innerBilinear; D] - ∫ᵛ x, φ x ∂[innerBilinear; D]| < ε2r := by
    rw [← h_int_sub]
    have h_norm : ∫ x, ‖g x - φ x‖ ∂D.variation = ∫ x, ‖φ x - g x‖ ∂D.variation := by
      congr with x; exact norm_sub_rev (g x) (φ x)
    have h := vectorMeasure_integral_abs_bound D (fun x => g x - φ x) (hg_int.sub hφ_int)
    rw [h_norm] at h
    exact h.trans_lt hφ_L1
  have h_phi_eq : ∫ᵛ x, φ x ∂[innerBilinear; D] = ∫ x in S, divergence φ x :=
    h_int φ hφ_smooth hφ_supp
  let θ : TestVectorField :=
    { toFun := φ
      smooth := hφ_smooth
      compact := hφ_supp
      bound := hφ_bound }
  have h_phi_le : ENNReal.ofReal |∫ᵛ x, φ x ∂[innerBilinear; D]| ≤ perimeter S := by
    rw [h_phi_eq]
    exact le_iSup (fun (ψ : TestVectorField) => ENNReal.ofReal |∫ x in S, divergence ψ.toFun x|) θ
  have h_phi_bound : |∫ᵛ x, φ x ∂[innerBilinear; D]| ≤ (perimeter S).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hP_lt.ne).mp h_phi_le
  have hI : ∫ᵛ x, g x ∂[innerBilinear; D] = ∑ p ∈ P, ‖D p‖ := h_integral
  have h_abs_lt : (∫ᵛ x, g x ∂[innerBilinear; D]) - (∫ᵛ x, φ x ∂[innerBilinear; D]) < ε2r :=
    calc (∫ᵛ x, g x ∂[innerBilinear; D]) - (∫ᵛ x, φ x ∂[innerBilinear; D])
      ≤ |(∫ᵛ x, g x ∂[innerBilinear; D]) - (∫ᵛ x, φ x ∂[innerBilinear; D])| := le_abs_self _
    _ < ε2r := h_diff
  have h_phi_le_real : (∫ᵛ x, φ x ∂[innerBilinear; D]) ≤ (perimeter S).toReal :=
    calc (∫ᵛ x, φ x ∂[innerBilinear; D])
      ≤ |∫ᵛ x, φ x ∂[innerBilinear; D]| := le_abs_self _
    _ ≤ (perimeter S).toReal := h_phi_bound
  have hI_le : (∑ p ∈ P, ‖D p‖) ≤ (perimeter S).toReal + ε2r := by
    rw [hI.symm]
    have h_sum : (∫ᵛ x, g x ∂[innerBilinear; D]) =
        (∫ᵛ x, φ x ∂[innerBilinear; D]) + ((∫ᵛ x, g x ∂[innerBilinear; D]) - (∫ᵛ x, φ x ∂[innerBilinear; D])) := by ring
    rw [h_sum]
    exact add_le_add h_phi_le_real h_abs_lt.le
  have h_sum_enorm : ∀ p ∈ P, ‖D p‖ₑ = ENNReal.ofReal ‖D p‖ := by
    intro p _; simp [enorm] <;> rfl
  have h_nonneg : ∀ p ∈ P, 0 ≤ ‖D p‖ := by intro p _; positivity
  have h_sum_ennreal : ∑ p ∈ P, ‖D p‖ₑ = ENNReal.ofReal (∑ p ∈ P, ‖D p‖) := by
    rw [Finset.sum_congr rfl h_sum_enorm]
    rw [ENNReal.ofReal_sum_of_nonneg h_nonneg]
  have h_sum_lt_top : perimeter S + ↑ε2 < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨hP_lt, ENNReal.coe_lt_top⟩
  have h9 : ENNReal.ofReal (∑ p ∈ P, ‖D p‖) ≤ perimeter S + ↑ε2 := by
    rw [ENNReal.ofReal_le_iff_le_toReal h_sum_lt_top.ne]
    have h10 : (perimeter S + ↑ε2).toReal = (perimeter S).toReal + ε2r := by
      simp [ENNReal.toReal_add hP_lt.ne] <;> norm_cast
    rw [h10]
    exact hI_le
  have h11 : ε2 + ε2 = ε := by
    apply NNReal.coe_injective
    simp [hε2_def] <;> ring
  have h12 : (↑ε2 : ENNReal) + (↑ε2 : ENNReal) = (↑ε : ENNReal) := by
    have h13 : (↑(ε2 + ε2) : ENNReal) = (↑ε2 : ENNReal) + (↑ε2 : ENNReal) := by
      simpa using NNReal.coe_add ε2 ε2
    rw [←h13, h11]
  calc ν Set.univ
    ≤ ∑ p ∈ P, ‖D p‖ₑ + ↑ε2 := hP_sum
    _ = ENNReal.ofReal (∑ p ∈ P, ‖D p‖) + ↑ε2 := by rw [h_sum_ennreal]
    _ ≤ perimeter S + ↑ε2 + ↑ε2 := by gcongr
    _ = perimeter S + (↑ε2 + ↑ε2) := by exact add_assoc (perimeter S) (↑ε2) (↑ε2)
    _ = perimeter S + ↑ε := by rw [h12]

end Geometry.Perimeter
