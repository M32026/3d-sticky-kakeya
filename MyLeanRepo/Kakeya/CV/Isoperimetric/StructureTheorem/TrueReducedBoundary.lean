import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DistributionalDerivative
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.Tactic


/-!
# True Reduced Boundary

Defines the true reduced boundary as points where the perimeter measure has
positive density in every ball AND the measure-theoretic normal has unit norm.

Proves that `perimeterMeasure S (frontier S \\ trueReducedBoundary S) = 0`.

## Proof route

1. Show `distributionalDerivative S = perimeterMeasure S.withDensityᵥ (measureTheoreticNormal S)`
   using the Radon-Nikodym theorem on each coordinate signed measure.

2. Show `‖measureTheoreticNormal S‖ ≥ 1` a.e.:
   `ν.variation ≤ μ.withDensity ‖f‖` by the triangle inequality on partitions.
   Since `ν.variation = μ`, get `μ ≤ μ.withDensity ‖f‖`, hence `‖f‖ ≥ 1` a.e.

3. Show `‖measureTheoreticNormal S‖ ≤ 1` a.e.:
   For any `v` with `‖v‖ ≤ 1`, the scalar signed measure `A ↦ inner v (D A)` satisfies
   `|s(A)| ≤ μ(A)`. This implies `|inner v f| ≤ 1` a.e.
   A countable dense set of the closed unit ball then gives `‖f‖ ≤ 1` a.e.

4. Conclude `‖f‖ = 1` a.e.

5. The set where `perimeterMeasure S (ball x r) = 0` for some `r > 0` has measure zero.

## Whiteprint
Node `true_reduced_boundary`, depended on by the structure theorem.
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry.Perimeter

variable {n : ℕ} {S : Set (E n)}

-- ============================================================================
-- True reduced boundary
-- ============================================================================

/-- The true reduced boundary: points where the perimeter measure has positive
measure in every ball and the measure-theoretic normal has unit norm. -/
def trueReducedBoundary (S : Set (E n)) : Set (E n) :=
  {x | (∀ r > 0, 0 < perimeterMeasure S (ball x r)) ∧
       ‖measureTheoreticNormal S x‖ = 1}

-- ============================================================================
-- Helper: norm ≤ 1 from inner product bounds
-- ============================================================================

/-- If `|inner ℝ v x| ≤ 1` for all `v` in a set `B` dense in the closed unit ball,
then `‖x‖ ≤ 1`. -/
lemma norm_le_one_of_inner_le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B : Set E} (hB : closedBall (0 : E) 1 ⊆ closure B)
    {x : E} (h : ∀ v ∈ B, |inner ℝ v x| ≤ 1) : ‖x‖ ≤ 1 := by
  by_contra hgt
  have h_gt : 1 < ‖x‖ := by linarith
  let u : E := (‖x‖)⁻¹ • x
  have hu_norm : ‖u‖ = 1 := by
    have h_ne : ‖x‖ ≠ 0 := by linarith
    simp [u, norm_smul, h_ne] <;> field_simp [h_ne] <;> ring
  have h_inner_u : inner ℝ u x = ‖x‖ := by
    simp [u, inner_smul_left, h_gt.ne'] <;> field_simp [h_gt.ne'] <;> ring
  have hu_in : u ∈ closedBall (0 : E) 1 := by
    simp [mem_closedBall, hu_norm]
  have h_closure : u ∈ closure B := hB hu_in
  let V : Set E := {v | inner ℝ v x > 1}
  have hV_open : IsOpen V := by
    have h_cont : Continuous (fun v : E => inner ℝ v x) := by fun_prop
    exact h_cont.isOpen_preimage _ isOpen_Ioi
  have hV_mem : u ∈ V := by
    simpa [V, h_inner_u] using h_gt
  have h_inter : (V ∩ B).Nonempty := by
    have h_iff : u ∈ closure B ↔ ∀ (o : Set E), IsOpen o → u ∈ o → (o ∩ B).Nonempty :=
      _root_.mem_closure_iff
    exact (h_iff.mp h_closure) V hV_open hV_mem
  rcases h_inter with ⟨v, hvV, hvB⟩
  have h6 : inner ℝ v x > 1 := hvV
  have h7 : 1 < |inner ℝ v x| := by
    have h8 : 0 < inner ℝ v x := by linarith
    rw [abs_of_pos h8] <;> linarith
  have h9 : |inner ℝ v x| ≤ 1 := h v hvB
  linarith

-- ============================================================================
-- Helper: variation of withDensityᵥ is bounded by withDensity of norm
-- ============================================================================

/-- The total variation of `μ.withDensityᵥ f` is bounded by `μ.withDensity (‖f‖)`. -/
lemma withDensityᵥ_variation_le {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → E} (hf : Integrable f μ) :
    (μ.withDensityᵥ f).variation ≤ μ.withDensity (fun x => ENNReal.ofReal ‖f x‖) := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro A hA
  have h_norm_int : Integrable (fun x => ‖f x‖) μ := hf.norm
  have h1 : ‖(μ.withDensityᵥ f) A‖ ≤ ∫ x in A, ‖f x‖ ∂μ := by
    rw [withDensityᵥ_apply hf hA]
    exact MeasureTheory.norm_integral_le_integral_norm (μ := μ.restrict A) f
  have h_enorm : ‖(μ.withDensityᵥ f) A‖ₑ = ENNReal.ofReal ‖(μ.withDensityᵥ f) A‖ := by
    rw [enorm_eq_nnnorm]
    have h_eq : ENNReal.ofReal ‖(μ.withDensityᵥ f) A‖ = (↑(‖(μ.withDensityᵥ f) A‖₊) : ENNReal) := by
      rw [← ENNReal.ofReal_coe_nnreal] <;> rfl
    exact h_eq.symm
  rw [h_enorm]
  have h51 : 0 ≤ᵐ[μ.restrict A] fun x => ‖f x‖ := by filter_upwards with x; exact norm_nonneg _
  have h52 : AEStronglyMeasurable (fun x => ‖f x‖) (μ.restrict A) :=
    h_norm_int.integrableOn.aestronglyMeasurable
  have h53 : (∫ x in A, ‖f x‖ ∂μ) = (∫⁻ x in A, ENNReal.ofReal ‖f x‖ ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae h51 h52]
  have h54 : (∫⁻ x in A, ENNReal.ofReal ‖f x‖ ∂μ) < ⊤ := by
    have hfi : HasFiniteIntegral (fun x => ‖f x‖) (μ.restrict A) :=
      h_norm_int.integrableOn.hasFiniteIntegral
    simpa [HasFiniteIntegral] using hfi
  have h_eq : ENNReal.ofReal (∫ x in A, ‖f x‖ ∂μ) = ∫⁻ x in A, ENNReal.ofReal ‖f x‖ ∂μ := by
    rw [h53, ENNReal.ofReal_toReal h54.ne]
  have h9 : ENNReal.ofReal ‖(μ.withDensityᵥ f) A‖ ≤ ENNReal.ofReal (∫ x in A, ‖f x‖ ∂μ) :=
    ENNReal.ofReal_le_ofReal h1
  have h11 : (μ.withDensity (fun x => ENNReal.ofReal ‖f x‖)) A = ∫⁻ x in A, ENNReal.ofReal ‖f x‖ ∂μ := by
    rw [withDensity_apply (fun x => ENNReal.ofReal ‖f x‖) hA]
  rw [h11, ←h_eq]
  exact h9

-- ============================================================================
-- Helper: integral bound implies a.e. bound
-- ============================================================================

/-- If `∫_A g dμ ≤ μ(A).toReal` for all measurable `A`, then `g ≤ 1` a.e. -/
lemma integral_bound_implies_ae_le_one {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] {g : α → ℝ} (hg : Integrable g μ) (hgm : Measurable g)
    (h : ∀ (A : Set α), MeasurableSet A → (∫ x in A, g x ∂μ) ≤ (μ A).toReal) :
    ∀ᵐ x ∂μ, g x ≤ 1 := by
  have h_pos : ∀ (c : ℝ), c > 1 → μ {x | g x > c} = 0 := by
    intro c hc
    let A := {x | g x > c}
    have hAm : MeasurableSet A := by
      have h : MeasurableSet (g ⁻¹' (Ioi c)) := hgm isOpen_Ioi.measurableSet
      have h2 : g ⁻¹' (Ioi c) = A := by ext x; simp [A]
      exact h2 ▸ h
    by_cases hμA : μ A = 0
    · exact hμA
    · have hμA_pos : 0 < (μ A).toReal := by
        have h_pos : 0 < μ A := by positivity
        exact ENNReal.toReal_pos (ne_of_gt h_pos) (ne_of_lt (measure_lt_top μ A))
      have h3 : c * (μ A).toReal ≤ ∫ x in A, g x ∂μ := by
        have h4 : ∀ x ∈ A, c ≤ g x := by
          intro x hx
          exact le_of_lt (by simpa [A] using hx)
        have h_const_int : IntegrableOn (fun x : α => c) A μ :=
          MeasureTheory.integrableOn_const (hs := (measure_lt_top μ A).ne)
        haveI : IntegrableOn (fun x : α => c) A μ := h_const_int
        haveI : IntegrableOn g A μ := hg.integrableOn
        have h5 : ∫ x in A, (c : ℝ) ∂μ ≤ ∫ x in A, g x ∂μ := by
          have h_diff_int : IntegrableOn (fun x => g x - c) A μ :=
            hg.integrableOn.sub h_const_int
          have h_nonneg_ae : ∀ᵐ x ∂(μ.restrict A), 0 ≤ g x - c := by
            apply (ae_restrict_iff' hAm).mpr
            filter_upwards with x
            intro hxA
            have h : c ≤ g x := h4 x hxA
            linarith
          have h_nonneg_int : 0 ≤ ∫ x in A, (g x - c) ∂μ :=
            integral_nonneg_of_ae h_nonneg_ae
          have h_eq : ∫ x in A, (g x - c) ∂μ = ∫ x in A, g x ∂μ - ∫ x in A, (c : ℝ) ∂μ :=
            integral_sub hg.integrableOn h_const_int
          rw [h_eq] at h_nonneg_int
          linarith
        have h_const : ∫ x in A, (c : ℝ) ∂μ = c * (μ A).toReal := by
          have hc : ∫ x in A, (c : ℝ) ∂μ = (μ A).toReal • c :=
            MeasureTheory.setIntegral_const (c : ℝ)
          rw [hc, smul_eq_mul, mul_comm]
        rw [h_const] at h5
        exact h5
      have h6 : ∫ x in A, g x ∂μ ≤ (μ A).toReal := h A hAm
      have h7 : c * (μ A).toReal ≤ (μ A).toReal := le_trans h3 h6
      have h8 : c ≤ 1 := by
        by_contra h
        have h' : 1 < c := by linarith
        have h9 : 0 < (μ A).toReal := hμA_pos
        have h10 : 1 * (μ A).toReal < c * (μ A).toReal := by gcongr
        have h11 : c * (μ A).toReal ≤ (μ A).toReal := h7
        linarith
      exact False.elim (not_le.mpr hc h8)
  have h_union : {x | g x > 1} = ⋃ k : ℕ, {x | g x > 1 + 1 / (k + 1 : ℝ)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      have h9 : 1 < g x := h
      have h10 : 0 < g x - 1 := by linarith
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt h10
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have hk' : g x > 1 + 1 / (k + 1 : ℝ) := by simpa using hk
      have h11 : (1 : ℝ) ≤ 1 + 1 / (k + 1 : ℝ) := by
        have h12 : 0 ≤ (1 / (k + 1 : ℝ)) := by positivity
        linarith
      exact lt_of_le_of_lt h11 hk'
  have h9 : μ (⋃ k : ℕ, {x | g x > 1 + 1 / (k + 1 : ℝ)}) = 0 :=
    measure_iUnion_null fun k =>
      h_pos (1 + 1 / (k + 1 : ℝ)) (by linarith [one_div_pos.mpr (show 0 < (k + 1 : ℝ) from by positivity)])
  have h10 : μ {x | g x > 1} = 0 := by
    rw [h_union]
    exact h9
  simpa [ae_iff] using h10

/-- If `∫_A g dμ ≥ -μ(A).toReal` for all measurable `A`, then `g ≥ -1` a.e. -/
lemma integral_bound_implies_ae_ge_neg_one {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] {g : α → ℝ} (hg : Integrable g μ) (hgm : Measurable g)
    (h : ∀ (A : Set α), MeasurableSet A → (∫ x in A, g x ∂μ) ≥ -(μ A).toReal) :
    ∀ᵐ x ∂μ, g x ≥ -1 := by
  have h' : ∀ (A : Set α), MeasurableSet A → (∫ x in A, (-g) x ∂μ) ≤ (μ A).toReal := by
    intro A hA
    have h_neg : ∫ x in A, (-g) x ∂μ = -∫ x in A, g x ∂μ :=
      MeasureTheory.integral_neg (μ := μ.restrict A) g
    rw [h_neg]
    have h9 : ∫ x in A, g x ∂μ ≥ -(μ A).toReal := h A hA
    linarith
  have h_ae : ∀ᵐ x ∂μ, (-g) x ≤ 1 := integral_bound_implies_ae_le_one hg.neg hgm.neg h'
  filter_upwards [h_ae] with x hx
  have h10 : -g x ≤ 1 := hx
  linarith

-- ============================================================================
-- Helper: countable "for all" almost everywhere
-- ============================================================================

/-- If `B` is countable, then `P v x` holds for all `v ∈ B` a.e. iff
for each `v ∈ B`, `P v x` holds a.e. -/
lemma ae_ball_iff {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {β : Type*}
    {B : Set β} (hB : B.Countable) {P : β → α → Prop} :
    (∀ᵐ x ∂μ, ∀ v ∈ B, P v x) ↔ (∀ v ∈ B, ∀ᵐ x ∂μ, P v x) := by
  constructor
  · intro h v hv
    filter_upwards [h] with x hx
    exact hx v hv
  · intro h
    have h_null : μ (⋃ v ∈ B, {x | ¬P v x}) = 0 := by
      rw [MeasureTheory.measure_biUnion_null_iff hB]
      intro v _
      simpa [ae_iff] using h v ‹_›
    have h2 : {x | ∃ v ∈ B, ¬P v x} = ⋃ v ∈ B, {x | ¬P v x} := by
      ext x; simp
    have h3 : μ {x | ∃ v ∈ B, ¬P v x} = 0 := by
      rw [h2]
      exact h_null
    simpa [ae_iff] using h3

-- ============================================================================
-- Decomposition lemma
-- ============================================================================

/-- **Decomposition**: `distributionalDerivative S = perimeterMeasure S.withDensityᵥ f`
where `f = measureTheoreticNormal S`, and `f` is integrable. -/
lemma measureTheoreticNormal_withDensity (hfin : perimeter S < ⊤) :
    Integrable (measureTheoreticNormal S) (perimeterMeasure S) ∧
    distributionalDerivative S =
      (perimeterMeasure S).withDensityᵥ (measureTheoreticNormal S) := by
  let μ := perimeterMeasure S
  let ν := distributionalDerivative S
  let f := measureTheoreticNormal S

  have hμ_univ : μ Set.univ < ⊤ := by
    have h_perim_eq : perimeter S = μ Set.univ := perimeter_eq_variation S hfin
    rw [h_perim_eq] at hfin
    exact hfin
  haveI : IsFiniteMeasure μ := ⟨hμ_univ⟩

  let μ_i : Fin n → SignedMeasure (E n) := fun i =>
    Classical.choose (distributionalDerivative_signedMeasure S i hfin)

  have h_ac : ∀ (i : Fin n), μ_i i ≪ᵥ μ.toENNRealVectorMeasure := by
    intro i
    apply VectorMeasure.AbsolutelyContinuous.mk
    intro A hA hμA
    have hμA' : μ A = 0 := by
      have h_fn : MeasurableSet A → μ A = 0 := by simpa using hμA
      exact h_fn hA
    have h_eq_var : ν.variation = μ := by
      simp [μ, ν, perimeterMeasure] <;> rfl
    have h1 : ν.variation A = 0 := by
      rw [h_eq_var]; exact hμA'
    have h2 : ν A = 0 := by
      have h3 : ‖ν A‖ₑ ≤ ν.variation A := VectorMeasure.enorm_measure_le_variation ν A
      rw [h1] at h3
      have h4 : ‖ν A‖ₑ = 0 := by simpa using h3
      exact (enorm_eq_zero).mp h4
    have h6 : ν A = ∑ j : Fin n, (μ_i j) A • EuclideanSpace.single j (1 : ℝ) := by
      unfold ν distributionalDerivative
      rw [dif_pos hfin]
      dsimp only
      simp [VectorMeasure.mapRange_apply] <;> rfl
    rw [h6] at h2
    have h7 : ((∑ j : Fin n, (μ_i j) A • EuclideanSpace.single j (1 : ℝ)) i) = 0 := by
      rw [h2] <;> simp
    have h8 : ((∑ j : Fin n, (μ_i j) A • EuclideanSpace.single j (1 : ℝ)) i) = (μ_i i) A := by
      let eval_i : (E n) →+ ℝ :=
        { toFun := fun x => x i
          map_zero' := by simp
          map_add' := by intro x y; simp [Pi.add_apply] }
      have h9 : (∑ j : Fin n, (μ_i j) A • EuclideanSpace.single j (1 : ℝ)) i =
          ∑ j : Fin n, ((μ_i j) A • EuclideanSpace.single j (1 : ℝ)) i := by
        exact map_sum eval_i (fun j => (μ_i j) A • EuclideanSpace.single j (1 : ℝ)) Finset.univ
      rw [h9]
      have h10 : ∑ j : Fin n, ((μ_i j) A • EuclideanSpace.single j (1 : ℝ)) i = (μ_i i) A := by
        simp [PiLp.single_apply, Finset.sum_ite_eq'] <;> ring
      exact h10
    rw [h8] at h7
    exact h7

  have h_f_def : f = fun x => ∑ i : Fin n,
      (μ_i i).rnDeriv μ x • EuclideanSpace.single i (1 : ℝ) := by
    funext x
    simp [f, measureTheoreticNormal, hfin] <;> rfl

  have h_int_total : Integrable f μ := by
    rw [h_f_def]
    exact integrable_finset_sum _ (fun i _ =>
      (SignedMeasure.integrable_rnDeriv (μ_i i) μ).smul_const _)

  have h_main1 : ν = μ.withDensityᵥ f := by
    ext1 A hA
    have h6 : ν A = ∑ j : Fin n, (μ_i j) A • EuclideanSpace.single j (1 : ℝ) := by
      unfold ν distributionalDerivative
      rw [dif_pos hfin]
      dsimp only
      simp [VectorMeasure.mapRange_apply] <;> rfl
    rw [h6]
    have h7 : (μ.withDensityᵥ f) A = ∫ x in A, f x ∂μ := by
      rw [withDensityᵥ_apply h_int_total hA]
    rw [h7, h_f_def]
    have h_int : ∀ (i : Fin n), IntegrableOn
        (fun x : E n => (μ_i i).rnDeriv μ x • EuclideanSpace.single i (1 : ℝ)) A μ := by
      intro i
      exact (SignedMeasure.integrable_rnDeriv (μ_i i) μ).smul_const _ |>.integrableOn
    rw [integral_finset_sum Finset.univ (fun i _ => h_int i)]
    apply Finset.sum_congr rfl
    intro i _
    have h_rn : (μ_i i) A = ∫ x in A, (μ_i i).rnDeriv μ x ∂μ := by
      have h : μ.withDensityᵥ ((μ_i i).rnDeriv μ) = μ_i i :=
        SignedMeasure.withDensityᵥ_rnDeriv_eq (μ_i i) μ (h_ac i)
      have h' := congr_arg (fun (v : VectorMeasure (E n) ℝ) => v A) h
      have h'' : (μ.withDensityᵥ ((μ_i i).rnDeriv μ)) A =
          ∫ x in A, (μ_i i).rnDeriv μ x ∂μ := by
        rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv (μ_i i) μ) hA]
      rw [h''] at h'
      exact h'.symm
    have h_smul : ∫ x in A, (μ_i i).rnDeriv μ x • EuclideanSpace.single i (1 : ℝ) ∂μ =
        (∫ x in A, (μ_i i).rnDeriv μ x ∂μ) • EuclideanSpace.single i (1 : ℝ) := by
      have h_integrable : IntegrableOn ((μ_i i).rnDeriv μ) A μ :=
        (SignedMeasure.integrable_rnDeriv (μ_i i) μ).integrableOn
      let v : E n := EuclideanSpace.single i (1 : ℝ)
      have h : ∫ x in A, (μ_i i).rnDeriv μ x • v ∂μ = (∫ x in A, (μ_i i).rnDeriv μ x ∂μ) • v :=
        integral_smul_const ((μ_i i).rnDeriv μ) v
      exact h
    rw [h_rn, h_smul]

  exact ⟨h_int_total, h_main1⟩

/-- The measure-theoretic normal is a measurable function. -/
lemma measureTheoreticNormal_measurable (hfin : perimeter S < ⊤) :
    Measurable (measureTheoreticNormal S) := by
  let μ_i : Fin n → SignedMeasure (E n) := fun i =>
    Classical.choose (distributionalDerivative_signedMeasure S i hfin)
  have h_f_def : measureTheoreticNormal S = fun x : E n => ∑ i : Fin n,
      (μ_i i).rnDeriv (perimeterMeasure S) x • EuclideanSpace.single i (1 : ℝ) := by
    funext x
    simp [measureTheoreticNormal, hfin] <;> rfl
  rw [h_f_def]
  fun_prop

-- ============================================================================
-- Lower bound: ‖f‖ ≥ 1 a.e.
-- ============================================================================

/-- **Lower bound**: `‖measureTheoreticNormal S‖ ≥ 1` a.e. -/
lemma norm_measureTheoreticNormal_ge_one (hfin : perimeter S < ⊤)
    (h_main1 : distributionalDerivative S =
      (perimeterMeasure S).withDensityᵥ (measureTheoreticNormal S))
    (h_int_total : Integrable (measureTheoreticNormal S) (perimeterMeasure S)) :
    ∀ᵐ x ∂(perimeterMeasure S), 1 ≤ ‖measureTheoreticNormal S x‖ := by
  let μ := perimeterMeasure S
  let ν := distributionalDerivative S
  let f := measureTheoreticNormal S
  have hfm : Measurable f := measureTheoreticNormal_measurable hfin
  have hfm' : Measurable (fun x : E n => ‖f x‖) := hfm.norm
  have hμ_univ : μ Set.univ < ⊤ := by
    have h_perim_eq : perimeter S = μ Set.univ := perimeter_eq_variation S hfin
    rw [h_perim_eq] at hfin
    exact hfin
  letI : IsFiniteMeasure μ := ⟨hμ_univ⟩
  have h_var_le : ν.variation ≤ μ.withDensity (fun x => ENNReal.ofReal ‖f x‖) := by
    have h_eq1 : ν = μ.withDensityᵥ f := h_main1
    rw [h_eq1]
    have h : (μ.withDensityᵥ f).variation ≤ μ.withDensity (fun x => ENNReal.ofReal ‖f x‖) :=
      withDensityᵥ_variation_le h_int_total
    exact h
  have h_ν_var : ν.variation = μ := by rfl
  have h_μ_le : μ ≤ μ.withDensity (fun x => ENNReal.ofReal ‖f x‖) := by
    rw [←h_ν_var]
    exact h_var_le
  have h_main : ∀ (A : Set (E n)), MeasurableSet A →
      μ A ≤ ∫⁻ x in A, ENNReal.ofReal ‖f x‖ ∂μ := by
    intro A hA
    have h_le : μ A ≤ (μ.withDensity (fun x => ENNReal.ofReal ‖f x‖)) A := h_μ_le A
    have h_eq : (μ.withDensity (fun x => ENNReal.ofReal ‖f x‖)) A = ∫⁻ x in A, ENNReal.ofReal ‖f x‖ ∂μ := by
      rw [withDensity_apply _ hA]
    rw [h_eq] at h_le
    exact h_le
  have h_null_c : ∀ (c : ℝ), 0 ≤ c → c < 1 → μ {x | ‖f x‖ < c} = 0 := by
    intro c hc0 hc1
    let A := {x | ‖f x‖ < c}
    have hA_meas : MeasurableSet A := by
      have h : MeasurableSet ((fun x => ‖f x‖) ⁻¹' (Iio c)) := hfm' isOpen_Iio.measurableSet
      have h2 : (fun x => ‖f x‖) ⁻¹' (Iio c) = A := by ext x; simp [A]
      exact h2 ▸ h
    by_cases hμA : μ A = 0
    · exact hμA
    · have hμA_pos : 0 < μ A := by
        exact pos_iff_ne_zero.mpr hμA
      have h_all : ∀ x, x ∈ A → ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal c := by
        intro x hx
        have h2 : ‖f x‖ < c := by simpa [A, Set.mem_setOf_eq] using hx
        exact ENNReal.ofReal_le_ofReal (le_of_lt h2)
      have h_aeμ : ∀ᵐ x ∂μ, x ∈ A → ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal c := by
        filter_upwards with x
        exact h_all x
      have h1 : ∫⁻ x in A, ENNReal.ofReal ‖f x‖ ∂μ ≤ ENNReal.ofReal c * μ A := by
        calc
          ∫⁻ x in A, ENNReal.ofReal ‖f x‖ ∂μ
            ≤ ∫⁻ x in A, ENNReal.ofReal c ∂μ :=
              MeasureTheory.setLIntegral_mono_ae' hA_meas h_aeμ
          _ = ENNReal.ofReal c * μ A := by simp
      have h2 : μ A ≤ ∫⁻ x in A, ENNReal.ofReal ‖f x‖ ∂μ := h_main A hA_meas
      have h4 : ENNReal.ofReal c < 1 := by
        have h41 : c < (1 : ℝ) := hc1
        exact ENNReal.ofReal_lt_one.mpr h41
      have h3 : ENNReal.ofReal c * μ A < μ A := by
        have h_ne_top : μ A ≠ ⊤ := (measure_lt_top μ A).ne
        have h : ENNReal.ofReal c * μ A < (1 : ENNReal) * μ A :=
          ENNReal.mul_lt_mul_left hμA_pos.ne' h_ne_top h4
        simpa using h
      have h_contra : μ A ≤ ENNReal.ofReal c * μ A := le_trans h2 h1
      exact False.elim (not_le.mpr h3 h_contra)
  have h_union : {x | ‖f x‖ < 1} = ⋃ n : ℕ, {x | ‖f x‖ < 1 - 1 / (n + 1 : ℝ)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      have h9 : ‖f x‖ < 1 := h
      have h10 : 0 < 1 - ‖f x‖ := by linarith
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt h10
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have h9 : (1 - 1 / (n + 1 : ℝ)) < 1 := by
        have h10 : 0 < (1 : ℝ) / (n + 1 : ℝ) := by positivity
        linarith
      linarith
  have h_null : μ {x | ‖f x‖ < 1} = 0 := by
    rw [h_union]
    apply measure_iUnion_null
    intro n
    have h_pos' : 0 < (n + 1 : ℝ) := by positivity
    have h10 : 0 ≤ (1 - 1 / (n + 1 : ℝ)) := by
      have h11 : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 := by
        apply (div_le_one h_pos').mpr
        <;> linarith
      linarith
    have h11 : (1 - 1 / (n + 1 : ℝ)) < 1 := by
      have h12 : 0 < (1 : ℝ) / (n + 1 : ℝ) := by positivity
      linarith
    exact h_null_c (1 - 1 / (n + 1 : ℝ)) h10 h11
  simpa [ae_iff] using h_null

-- ============================================================================
-- Upper bound: ‖f‖ ≤ 1 a.e.
-- ============================================================================

/-- **Upper bound**: `‖measureTheoreticNormal S‖ ≤ 1` a.e. -/
lemma norm_measureTheoreticNormal_le_one (hfin : perimeter S < ⊤)
    (h_main1 : distributionalDerivative S =
      (perimeterMeasure S).withDensityᵥ (measureTheoreticNormal S))
    (h_int_total : Integrable (measureTheoreticNormal S) (perimeterMeasure S)) :
    ∀ᵐ x ∂(perimeterMeasure S), ‖measureTheoreticNormal S x‖ ≤ 1 := by
  let μ := perimeterMeasure S
  let ν := distributionalDerivative S
  let f := measureTheoreticNormal S
  have hfm : Measurable f := measureTheoreticNormal_measurable hfin
  have hμ_univ : μ Set.univ < ⊤ := by
    have h_perim_eq : perimeter S = μ Set.univ := perimeter_eq_variation S hfin
    rw [h_perim_eq] at hfin
    exact hfin
  letI : IsFiniteMeasure μ := ⟨hμ_univ⟩
  obtain ⟨D, hDc, hDd⟩ : ∃ (D : Set (E n)), D.Countable ∧ Dense D :=
    TopologicalSpace.exists_countable_dense (E n)
  let B := D ∩ closedBall (0 : E n) 1
  have hBc : B.Countable := hDc.mono (show B ⊆ D from by simp [B])
  have hB_dense : closedBall (0 : E n) 1 ⊆ closure B := by
    have h1 : ball (0 : E n) 1 ⊆ closure (D ∩ ball (0 : E n) 1) := by
      intro x hx
      rw [_root_.mem_closure_iff]
      intro o ho xo
      have h_inter_open : IsOpen (o ∩ ball (0 : E n) 1) := IsOpen.inter ho isOpen_ball
      have h_inter_nonempty : (o ∩ ball (0 : E n) 1).Nonempty := ⟨x, xo, hx⟩
      have h : (o ∩ ball (0 : E n) 1 ∩ D).Nonempty :=
        hDd.inter_open_nonempty (o ∩ ball (0 : E n) 1) h_inter_open h_inter_nonempty
      have h' : (o ∩ (D ∩ ball (0 : E n) 1)).Nonempty := by
        have h_eq : o ∩ (D ∩ ball (0 : E n) 1) = o ∩ ball (0 : E n) 1 ∩ D := by
          ext y
          simp [Set.mem_inter_iff, and_assoc, and_comm, and_left_comm]
          <;> tauto
        rw [h_eq]
        exact h
      exact h'
    have h2 : closure (ball (0 : E n) 1) ⊆ closure (D ∩ ball (0 : E n) 1) :=
      closure_minimal h1 isClosed_closure
    have h3 : closure (ball (0 : E n) 1) = closedBall (0 : E n) 1 :=
      closure_ball (0 : E n) (by norm_num)
    have h4 : D ∩ ball (0 : E n) 1 ⊆ B := by
      intro x hx
      exact ⟨hx.1, ball_subset_closedBall hx.2⟩
    have h5 : closure (D ∩ ball (0 : E n) 1) ⊆ closure B := closure_mono h4
    rw [←h3]
    exact h2.trans h5
  have h_upper : ∀ (v : E n), ‖v‖ ≤ 1 → ∀ (A : Set (E n)), MeasurableSet A →
      (∫ x in A, inner ℝ v (f x) ∂μ) ≤ (μ A).toReal := by
    intro v hv A hA
    have h_eq : (∫ x in A, inner ℝ v (f x) ∂μ) = inner ℝ v (ν A) := by
      have h9 : (∫ x in A, inner ℝ v (f x) ∂μ) = inner ℝ v (∫ x in A, f x ∂μ) :=
        integral_inner (h_int_total.integrableOn) v
      rw [h9]
      have h10 : (∫ x in A, f x ∂μ) = ν A := by
        have h11 : (μ.withDensityᵥ f) A = ∫ x in A, f x ∂μ := withDensityᵥ_apply h_int_total hA
        have h12 : ν = μ.withDensityᵥ f := h_main1
        rw [h12]
        exact h11.symm
      rw [h10]
    rw [h_eq]
    have h : inner ℝ v (ν A) ≤ ‖v‖ * ‖ν A‖ := real_inner_le_norm v (ν A)
    have h2 : ‖v‖ * ‖ν A‖ ≤ ‖ν A‖ := by
      have h3 : ‖v‖ ≤ 1 := hv
      have h4 : 0 ≤ ‖ν A‖ := by positivity
      calc
        ‖v‖ * ‖ν A‖ ≤ 1 * ‖ν A‖ := by gcongr
        _ = ‖ν A‖ := by ring
    have h5 : ‖ν A‖ ≤ (μ A).toReal := by
      have h6 : ‖ν A‖ₑ ≤ ν.variation A := VectorMeasure.enorm_measure_le_variation ν A
      have h7 : ν.variation A = μ A := by rfl
      rw [h7] at h6
      have h8 : ‖ν A‖ₑ = ENNReal.ofReal ‖ν A‖ := by
        have h9 : ‖ν A‖ₑ = (↑‖ν A‖₊ : ENNReal) := enorm_eq_nnnorm (ν A)
        have h10 : ‖ν A‖ = (↑‖ν A‖₊ : ℝ) := by simp [nnnorm]
        rw [h9, h10]
        rw [ENNReal.ofReal_coe_nnreal]
      rw [h8] at h6
      have hμA_ne_top : μ A ≠ ⊤ := (measure_lt_top μ A).ne
      have h9 : (ENNReal.ofReal ‖ν A‖).toReal ≤ (μ A).toReal :=
        ENNReal.toReal_mono hμA_ne_top h6
      have h10 : (ENNReal.ofReal ‖ν A‖).toReal = ‖ν A‖ := by
        rw [ENNReal.toReal_ofReal (norm_nonneg _)]
      rw [h10] at h9
      exact h9
    linarith
  have h_lower : ∀ (v : E n), ‖v‖ ≤ 1 → ∀ (A : Set (E n)), MeasurableSet A →
      (∫ x in A, inner ℝ v (f x) ∂μ) ≥ -(μ A).toReal := by
    intro v hv A hA
    have h_up : ∫ x in A, inner ℝ (-v) (f x) ∂μ ≤ (μ A).toReal :=
      h_upper (-v) (by simpa [norm_neg] using hv) A hA
    have h_eq : ∫ x in A, inner ℝ (-v) (f x) ∂μ = -∫ x in A, inner ℝ v (f x) ∂μ := by
      have h1 : ∀ x, inner ℝ (-v) (f x) = -inner ℝ v (f x) := by
        intro x; rw [inner_neg_left]
      have h2 : ∫ x in A, inner ℝ (-v) (f x) ∂μ = ∫ x in A, -(inner ℝ v (f x)) ∂μ := by
        apply integral_congr_ae; filter_upwards with x; exact h1 x
      rw [h2, integral_neg]
    have h_up2 : -∫ x in A, inner ℝ v (f x) ∂μ ≤ (μ A).toReal := by
      calc
        -∫ x in A, inner ℝ v (f x) ∂μ
          = ∫ x in A, inner ℝ (-v) (f x) ∂μ := h_eq.symm
        _ ≤ (μ A).toReal := h_up
    linarith
  have h_le_per_v : ∀ (v : E n), ‖v‖ ≤ 1 → ∀ᵐ x ∂μ, |inner ℝ v (f x)| ≤ 1 := by
    intro v hv
    let g := fun x : E n => inner ℝ v (f x)
    let inner_v : E n →L[ℝ] ℝ :=
      { toFun := fun y => inner ℝ v y
        map_add' := by
          intro x y
          exact inner_add_right v x y
        map_smul' := fun c x => inner_smul_right_eq_smul v x c }
    have hg : Integrable g μ := inner_v.integrable_comp h_int_total
    have hgm : Measurable g := by fun_prop
    have h1 : ∀ (A : Set (E n)), MeasurableSet A → (∫ x in A, g x ∂μ) ≤ (μ A).toReal :=
      h_upper v hv
    have h2 : ∀ (A : Set (E n)), MeasurableSet A → (∫ x in A, g x ∂μ) ≥ -(μ A).toReal :=
      h_lower v hv
    have h_ae1 : ∀ᵐ x ∂μ, g x ≤ 1 := integral_bound_implies_ae_le_one hg hgm h1
    have h_ae2 : ∀ᵐ x ∂μ, g x ≥ -1 := integral_bound_implies_ae_ge_neg_one hg hgm h2
    filter_upwards [h_ae1, h_ae2] with x h1 h2
    exact abs_le.mpr ⟨h2, h1⟩
  have h_all : ∀ᵐ x ∂μ, ∀ v ∈ B, |inner ℝ v (f x)| ≤ 1 := by
    rw [ae_ball_iff hBc]
    intro v hv
    have h_v_in_ball : ‖v‖ ≤ 1 := by
      have h : v ∈ closedBall (0 : E n) 1 := hv.2
      simpa [mem_closedBall] using h
    exact h_le_per_v v h_v_in_ball
  have h_final : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1 := by
    filter_upwards [h_all] with x hx
    exact norm_le_one_of_inner_le_one hB_dense hx
  exact h_final

-- ============================================================================
-- Main theorem: norm is 1 a.e.
-- ============================================================================

/-- The measure-theoretic normal has unit norm `perimeterMeasure`-a.e. -/
theorem norm_measureTheoreticNormal_eq_one (hfin : perimeter S < ⊤) :
    ∀ᵐ x ∂(perimeterMeasure S), ‖measureTheoreticNormal S x‖ = 1 := by
  rcases measureTheoreticNormal_withDensity hfin with ⟨h_int, h_main1⟩
  have h_ge : ∀ᵐ x ∂(perimeterMeasure S), 1 ≤ ‖measureTheoreticNormal S x‖ :=
    norm_measureTheoreticNormal_ge_one hfin h_main1 h_int
  have h_le : ∀ᵐ x ∂(perimeterMeasure S), ‖measureTheoreticNormal S x‖ ≤ 1 :=
    norm_measureTheoreticNormal_le_one hfin h_main1 h_int
  filter_upwards [h_ge, h_le] with x hge hle
  exact le_antisymm hle hge

-- ============================================================================
-- Main theorem
-- ============================================================================

/-- The perimeter measure of the complement of the true reduced boundary is zero. -/
theorem perimeterMeasure_compl_trueReducedBoundary (S : Set (E n)) :
    perimeterMeasure S (frontier S \ trueReducedBoundary S) = 0 := by
  by_cases hfin : perimeter S < ⊤
  · -- Hard case: finite perimeter
    let μ := perimeterMeasure S
    let f := measureTheoreticNormal S
    have h_norm_one : ∀ᵐ x ∂μ, ‖f x‖ = 1 := norm_measureTheoreticNormal_eq_one hfin
    have h1 : μ {x | ‖f x‖ ≠ 1} = 0 := by
      simpa [ae_iff] using h_norm_one
    let Z := {x : E n | ∃ r > 0, μ (ball x r) = 0}
    have hZ_sub : Z ⊆ (μ.support)ᶜ := by
      intro x hx
      rcases hx with ⟨r, hr, hμr⟩
      have h_x_in : x ∈ ball x r := by simp [hr]
      have h_not_support : x ∉ μ.support := by
        intro h
        have h_char : ∀ (U : Set (E n)), U ∈ nhds x → 0 < μ U :=
          (MeasureTheory.Measure.mem_support_iff_forall x).mp h
        have h_pos : 0 < μ (ball x r) := h_char (ball x r) (ball_mem_nhds x hr)
        rw [hμr] at h_pos
        <;> simpa using h_pos
      exact h_not_support
    have hZ_null : μ Z = 0 := by
      have h : μ Z ≤ μ (μ.support)ᶜ := measure_mono hZ_sub
      have h2 : μ (μ.support)ᶜ = 0 := by
        exact Measure.measure_compl_support
      rw [h2] at h
      simpa using h
    have h_sub : (frontier S \ trueReducedBoundary S) ⊆ Z ∪ {x | ‖f x‖ ≠ 1} := by
      intro x hx
      have h_not_in : x ∉ trueReducedBoundary S := hx.2
      by_cases hZ : x ∈ Z
      · exact Or.inl hZ
      · have h_pos : ∀ r > 0, 0 < μ (ball x r) := by
          intro r hr
          by_contra h
          have h' : μ (ball x r) = 0 := by simpa using h
          exact hZ ⟨r, hr, h'⟩
        have h_norm : ‖f x‖ ≠ 1 := by
          intro h
          exact h_not_in ⟨h_pos, h⟩
        exact Or.inr h_norm
    have h_union_null : μ (Z ∪ {x | ‖f x‖ ≠ 1}) = 0 := by
      have h : μ (Z ∪ {x | ‖f x‖ ≠ 1}) ≤ μ Z + μ {x | ‖f x‖ ≠ 1} := measure_union_le _ _
      rw [hZ_null, h1] at h
      simpa using h
    exact measure_mono_null h_sub h_union_null
  · -- Easy case: infinite perimeter implies perimeterMeasure = 0
    have h_top : ¬ perimeter S < ⊤ := hfin
    have hν_zero : distributionalDerivative S = 0 := by
      rw [distributionalDerivative, dif_neg h_top]
    have hμ_zero : perimeterMeasure S = 0 := by
      simp [perimeterMeasure, hν_zero]
    rw [hμ_zero]
    <;> simp

end Geometry.Perimeter
