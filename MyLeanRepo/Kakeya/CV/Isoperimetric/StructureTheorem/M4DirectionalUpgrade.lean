import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DistributionalDerivative
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.TrueReducedBoundary
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Tactic

/-!
# M4 Directional Upgrade Lemmas

From weak Lebesgue differentiation, prove directional strong forms for
inner(w, ν_U(y)) and |inner(w, ν_U(y))|.
-/


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry.StructureTheorem

open Perimeter

variable {n : ℕ}

-- Weak M4 copied here for self-contained compilation
theorem lebesgue_diff_perimeter_measure_weak'
    {U : Set (E n)} (h_perim_finite : perimeter U < ⊤)
    (g : E n → ℝ) (hg : Integrable g (perimeterMeasure U)) :
    ∀ᵐ (x : E n) ∂(perimeterMeasure U),
      Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, g y ∂(perimeterMeasure U)) /
          (perimeterMeasure U (closedBall x r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (g x)) := by
  let μ := perimeterMeasure U
  have h_fin : μ Set.univ < ⊤ := by
    have h_eq : perimeter U = μ Set.univ := perimeter_eq_variation U h_perim_finite
    rw [h_eq] at h_perim_finite
    exact h_perim_finite
  letI : IsFiniteMeasure μ := ⟨h_fin⟩
  let v := Besicovitch.vitaliFamily μ
  have hgl : LocallyIntegrable g μ := hg.locallyIntegrable
  have h_avg : ∀ᵐ (x : E n) ∂μ,
      Tendsto (fun A : Set (E n) => ⨍ (y : E n) in A, g y ∂μ)
        (v.filterAt x) (nhds (g x)) :=
    VitaliFamily.ae_tendsto_average v hgl
  have h_ball_tendsto : ∀ (x : E n),
      Tendsto (fun r : ℝ => closedBall x r)
        (nhdsWithin 0 (Set.Ioi 0)) (v.filterAt x) := by
    intro x
    have h_basis : (v.filterAt x).HasBasis (fun ε : ℝ => 0 < ε)
        (fun ε => {t : Set (E n) | t ∈ v.setsAt x ∧ t ⊆ closedBall x ε}) :=
      VitaliFamily.filterAt_basis_closedBall v x
    rw [h_basis.tendsto_right_iff]
    intro ε hε
    have h_event : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
        closedBall x r ∈ v.setsAt x ∧ closedBall x r ⊆ closedBall x ε := by
      have h_nhds : Set.Ioo (0 : ℝ) ε ∈ nhdsWithin 0 (Set.Ioi 0) := by
        have h1 : Set.Iio ε ∈ nhds (0 : ℝ) := Iio_mem_nhds hε
        have h2 : Set.Iio ε ∈ nhdsWithin 0 (Set.Ioi 0) := Filter.mem_inf_of_left h1
        have h3 : Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0) := self_mem_nhdsWithin
        have h4 : Set.Ioo (0 : ℝ) ε = Set.Iio ε ∩ Set.Ioi (0 : ℝ) := by
          ext z; simp [Set.mem_Ioo, Set.mem_Iio, Set.mem_Ioi] <;> tauto
        rw [h4]; exact inter_mem h2 h3
      filter_upwards [h_nhds] with r hr
      have hr_pos : 0 < r := hr.1
      have hr_lt : r < ε := hr.2
      have h1 : closedBall x r ∈ v.setsAt x := by
        simpa [Besicovitch.vitaliFamily, Set.mem_image] using ⟨r, hr_pos, rfl⟩
      have h2 : closedBall x r ⊆ closedBall x ε := closedBall_subset_closedBall hr_lt.le
      exact ⟨h1, h2⟩
    exact h_event
  filter_upwards [h_avg] with x hx
  have h_comp : Tendsto (fun r : ℝ => ⨍ (y : E n) in closedBall x r, g y ∂μ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (g x)) :=
    hx.comp (h_ball_tendsto x)
  have h_eq_avg : (fun r : ℝ => ⨍ (y : E n) in closedBall x r, g y ∂μ) =
      (fun r : ℝ => (∫ y in closedBall x r, g y ∂μ) / (μ (closedBall x r)).toReal) := by
    funext r
    simp [MeasureTheory.average, div_eq_inv_mul] <;> ring
  rw [h_eq_avg] at h_comp
  exact h_comp

/-- **Directional Lebesgue differentiation** for inner products. -/
lemma inner_lebesgue_diff_ae
    {U : Set (E n)} (h_perim_finite : perimeter U < ⊤) :
    ∀ᵐ (x : E n) ∂(perimeterMeasure U),
      ∀ (w : E n),
        Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, inner ℝ w (measureTheoreticNormal U y) ∂(perimeterMeasure U)) /
            (perimeterMeasure U (closedBall x r)).toReal)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (inner ℝ w (measureTheoreticNormal U x))) := by
  let μ := perimeterMeasure U
  let ν_U := measureTheoreticNormal U
  have hνU_int : Integrable ν_U μ := (measureTheoreticNormal_withDensity h_perim_finite).1

  let g : Fin n → (E n → ℝ) := fun i y => (ν_U y) i
  have hg_int : ∀ i : Fin n, Integrable (g i) μ := by
    intro i
    let proj : (E n) →L[ℝ] ℝ :=
      { toFun := fun v => v i
        map_add' := fun v w => by simp
        map_smul' := fun c v => by simp }
    exact proj.integrable_comp hνU_int

  have h_diff : ∀ i : Fin n, ∀ᵐ (x : E n) ∂μ,
      Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, g i y ∂μ) / (μ (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (g i x)) := by
    intro i
    exact lebesgue_diff_perimeter_measure_weak' h_perim_finite (g i) (hg_int i)

  have h_all : ∀ᵐ (x : E n) ∂μ, ∀ i : Fin n,
      Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, g i y ∂μ) / (μ (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (g i x)) := by
    exact ae_all_iff.mpr h_diff

  filter_upwards [h_all] with x hx
  intro w
  have h_sum : ∀ (z : E n), inner ℝ w z = ∑ i : Fin n, w i * z i := by
    intro z
    have h : inner ℝ w z = ∑ i : Fin n, z i * w i := by
      simpa [PiLp.inner_apply] using rfl
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h1 : (fun y : E n => inner ℝ w (ν_U y)) = fun y : E n => ∑ i : Fin n, w i * g i y := by
    funext y
    rw [h_sum (ν_U y)]
    <;> rfl
  rw [h1]
  have h2 : (fun r : ℝ =>
      (∫ y in closedBall x r, (∑ i : Fin n, w i * g i y) ∂μ) / (μ (closedBall x r)).toReal) =
      fun r : ℝ => ∑ i : Fin n, w i * ((∫ y in closedBall x r, g i y ∂μ) / (μ (closedBall x r)).toReal) := by
    funext r
    have h3 : (∫ y in closedBall x r, (∑ i : Fin n, w i * g i y) ∂μ) =
        ∑ i : Fin n, w i * (∫ y in closedBall x r, g i y ∂μ) := by
      have h_int : ∀ i ∈ Finset.univ, Integrable (fun y : E n => w i * g i y) (μ.restrict (closedBall x r)) := by
        intro i _
        have h_i : Integrable (g i) μ := hg_int i
        have h_i_restrict : Integrable (g i) (μ.restrict (closedBall x r)) := h_i.restrict
        exact h_i_restrict.const_mul (w i)
      rw [integral_finset_sum Finset.univ h_int]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul]
    rw [h3]
    have h4 : (∑ i : Fin n, w i * (∫ y in closedBall x r, g i y ∂μ)) / (μ (closedBall x r)).toReal =
        ∑ i : Fin n, w i * ((∫ y in closedBall x r, g i y ∂μ) / (μ (closedBall x r)).toReal) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    exact h4
  rw [h2]
  have h4 : inner ℝ w (ν_U x) = ∑ i : Fin n, w i * g i x := by
    rw [h_sum (ν_U x)] <;> rfl
  rw [h4]
  have h_tendsto_sum : Tendsto (fun r : ℝ => ∑ i : Fin n, w i * ((∫ y in closedBall x r, g i y ∂μ) / (μ (closedBall x r)).toReal))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∑ i : Fin n, w i * g i x)) := by
    have h5 : ∀ i : Fin n, Tendsto (fun r : ℝ => w i * ((∫ y in closedBall x r, g i y ∂μ) / (μ (closedBall x r)).toReal))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (w i * g i x)) := by
      intro i
      exact (hx i).const_mul (w i)
    exact tendsto_finsetSum Finset.univ (fun i _ => h5 i)
  exact h_tendsto_sum

/-- **Directional Lebesgue differentiation** for absolute inner products.

For `perimeterMeasure`-a.e. `x`, differentiation holds simultaneously for
all `h_w(y) = |inner ℝ w (measureTheoreticNormal U y)|`.

Uses countable dense subset of `E n` plus `‖ν_U‖ ≤ 1` a.e. -/
lemma abs_inner_lebesgue_diff_ae
    {U : Set (E n)} (h_perim_finite : perimeter U < ⊤) :
    ∀ᵐ (x : E n) ∂(perimeterMeasure U),
      ∀ (w : E n),
        Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, |inner ℝ w (measureTheoreticNormal U y)| ∂(perimeterMeasure U)) /
            (perimeterMeasure U (closedBall x r)).toReal)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds |inner ℝ w (measureTheoreticNormal U x)|) := by
  let μ := perimeterMeasure U
  let ν_U := measureTheoreticNormal U
  have h_fin : μ Set.univ < ⊤ := by
    have h_eq : perimeter U = μ Set.univ := perimeter_eq_variation U h_perim_finite
    rw [h_eq] at h_perim_finite
    exact h_perim_finite
  letI : IsFiniteMeasure μ := ⟨h_fin⟩
  have hνU_int : Integrable ν_U μ := (measureTheoreticNormal_withDensity h_perim_finite).1
  have h_main1 : distributionalDerivative U = μ.withDensityᵥ ν_U :=
    (measureTheoreticNormal_withDensity h_perim_finite).2
  have h_norm_le_one : ∀ᵐ (y : E n) ∂μ, ‖ν_U y‖ ≤ 1 :=
    norm_measureTheoreticNormal_le_one h_perim_finite h_main1 hνU_int
  have hνU_meas : Measurable ν_U := measureTheoreticNormal_measurable h_perim_finite

  haveI : TopologicalSpace.SeparableSpace (E n) := by infer_instance
  rcases TopologicalSpace.exists_countable_dense (E n) with ⟨D, hD_count, hD_dense⟩

  let h_w : E n → (E n → ℝ) := fun w y => |inner ℝ w (ν_U y)|

  -- Reverse triangle inequality for abs: ||a| - |b|| ≤ |a - b|
  have h_rev_abs : ∀ (a b : ℝ), |abs a - abs b| ≤ |a - b| := by
    intro a b
    have h1 : abs a ≤ abs b + abs (a - b) := by
      calc abs a = abs (b + (a - b)) := by rw [show b + (a - b) = a by ring]
        _ ≤ abs b + abs (a - b) := by simpa [Real.norm_eq_abs] using norm_add_le b (a - b)
    have h2_raw : abs b ≤ abs a + abs (b - a) := by
      calc abs b = abs (a + (b - a)) := by rw [show a + (b - a) = b by ring]
        _ ≤ abs a + abs (b - a) := by simpa [Real.norm_eq_abs] using norm_add_le a (b - a)
    have h_comm : abs (b - a) = abs (a - b) := by
      have h4 : b - a = -(a - b) := by ring
      rw [h4, abs_neg]
    have h2 : abs b ≤ abs a + abs (a - b) := by
      rw [h_comm] at h2_raw
      exact h2_raw
    have h3 : abs a - abs b ≤ abs (a - b) := by linarith
    have h4 : abs b - abs a ≤ abs (a - b) := by linarith
    have h5 : |abs a - abs b| ≤ abs (a - b) := by
      rw [abs_le] <;> constructor <;> linarith
    exact h5

  -- Integrability of h_w w
  have h_int : ∀ (w : E n), Integrable (h_w w) μ := by
    intro w
    have h1 : Measurable (h_w w) := by
      have hinner : Measurable (fun y : E n => inner ℝ w (ν_U y)) :=
        Measurable.const_inner (𝕜 := ℝ) hνU_meas
      simpa [h_w, Real.norm_eq_abs] using hinner.norm
    have h2 : ∀ᵐ (y : E n) ∂μ, ‖h_w w y‖ ≤ ‖(fun y : E n => ‖w‖ * ‖ν_U y‖) y‖ := by
      filter_upwards with y
      have h3 : |inner ℝ w (ν_U y)| ≤ ‖w‖ * ‖ν_U y‖ := abs_real_inner_le_norm w (ν_U y)
      simpa [h_w] using h3
    have h3 : Integrable (fun y : E n => ‖w‖ * ‖ν_U y‖) μ :=
      hνU_int.norm.const_mul ‖w‖
    exact Integrable.mono h3 h1.aestronglyMeasurable h2

  -- Weak differentiation for each w ∈ D
  have h_diff_D : ∀ (w : E n), w ∈ D → ∀ᵐ (x : E n) ∂μ,
      Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, h_w w y ∂μ) / (μ (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (h_w w x)) := by
    intro w _
    exact lebesgue_diff_perimeter_measure_weak' h_perim_finite (h_w w) (h_int w)

  -- Countable union of null sets
  have h_all_D : ∀ᵐ (x : E n) ∂μ, ∀ (w : E n), w ∈ D →
      Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, h_w w y ∂μ) / (μ (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (h_w w x)) := by
    let D' : Set (E n) := D
    have hD'_count : Countable D' := hD_count
    letI : Countable D' := hD'_count
    have h : ∀ᵐ (x : E n) ∂μ, ∀ (w : D'),
        Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, h_w w.val y ∂μ) / (μ (closedBall x r)).toReal)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (h_w w.val x)) := by
      rw [ae_all_iff]
      intro w
      exact h_diff_D w.val w.prop
    simpa [Subtype.forall] using h

  -- Lipschitz bound: |h_w w y - h_w w' y| ≤ ‖w - w'‖ a.e.
  have h_lip : ∀ (w w' : E n), ∀ᵐ (y : E n) ∂μ,
      |h_w w y - h_w w' y| ≤ ‖w - w'‖ := by
    intro w w'
    filter_upwards [h_norm_le_one] with y hy
    have h_eq : inner ℝ w (ν_U y) - inner ℝ w' (ν_U y) = inner ℝ (w - w') (ν_U y) := by
      rw [inner_sub_left]
    have h1 : |inner ℝ w (ν_U y) - inner ℝ w' (ν_U y)| ≤ ‖w - w'‖ * ‖ν_U y‖ := by
      rw [h_eq]
      exact abs_real_inner_le_norm (w - w') (ν_U y)
    have h2 : |h_w w y - h_w w' y| ≤ |inner ℝ w (ν_U y) - inner ℝ w' (ν_U y)| :=
      h_rev_abs (inner ℝ w (ν_U y)) (inner ℝ w' (ν_U y))
    have h3 : ‖w - w'‖ * ‖ν_U y‖ ≤ ‖w - w'‖ := by
      have h4 : 0 ≤ ‖w - w'‖ := by positivity
      nlinarith
    exact h2.trans (h1.trans h3)

  -- Average Lipschitz bound
  have h_avg_lip : ∀ (w w' : E n) (x : E n) (r : ℝ),
      |((∫ y in closedBall x r, h_w w y ∂μ) / (μ (closedBall x r)).toReal) -
       ((∫ y in closedBall x r, h_w w' y ∂μ) / (μ (closedBall x r)).toReal)| ≤ ‖w - w'‖ := by
    intro w w' x r
    by_cases hμ0 : μ (closedBall x r) = 0
    · simp [hμ0] <;> norm_num
    · have hμ_ne : (0 : ENNReal) ≠ μ (closedBall x r) := Ne.symm hμ0
      have hμ_pos : 0 < μ (closedBall x r) := by
        exact lt_of_le_of_ne (by positivity) hμ_ne
      have hμr_pos : 0 < (μ (closedBall x r)).toReal :=
        ENNReal.toReal_pos_iff.mpr ⟨hμ_pos, measure_lt_top μ _⟩
      have h_sub_int : (∫ y in closedBall x r, h_w w y ∂μ) - (∫ y in closedBall x r, h_w w' y ∂μ) =
          ∫ y in closedBall x r, (h_w w y - h_w w' y) ∂μ := by
        rw [integral_sub (h_int w).restrict (h_int w').restrict]
      have h4 : |((∫ y in closedBall x r, h_w w y ∂μ) / (μ (closedBall x r)).toReal) -
                 ((∫ y in closedBall x r, h_w w' y ∂μ) / (μ (closedBall x r)).toReal)| =
          |(∫ y in closedBall x r, (h_w w y - h_w w' y) ∂μ)| / (μ (closedBall x r)).toReal := by
        have h5 : ((∫ y in closedBall x r, h_w w y ∂μ) / (μ (closedBall x r)).toReal) -
              ((∫ y in closedBall x r, h_w w' y ∂μ) / (μ (closedBall x r)).toReal) =
            (((∫ y in closedBall x r, h_w w y ∂μ) - (∫ y in closedBall x r, h_w w' y ∂μ)) / (μ (closedBall x r)).toReal) := by
          field_simp [hμr_pos.ne'] <;> ring
        have h6 : ((∫ y in closedBall x r, h_w w y ∂μ) - (∫ y in closedBall x r, h_w w' y ∂μ)) =
            ∫ y in closedBall x r, (h_w w y - h_w w' y) ∂μ := by
          rw [integral_sub (h_int w).restrict (h_int w').restrict]
        rw [h5, h6]
        have h7 : |(∫ y in closedBall x r, (h_w w y - h_w w' y) ∂μ) / (μ (closedBall x r)).toReal| =
            |(∫ y in closedBall x r, (h_w w y - h_w w' y) ∂μ)| / (μ (closedBall x r)).toReal := by
          rw [abs_div]
          <;> rw [abs_of_pos hμr_pos]
        exact h7
      rw [h4]
      have h6 : |(∫ y in closedBall x r, (h_w w y - h_w w' y) ∂μ)| ≤
          ∫ y in closedBall x r, |h_w w y - h_w w' y| ∂μ :=
        abs_integral_le_integral_abs
      have h8 : ∀ᵐ (y : E n) ∂(μ.restrict (closedBall x r)), |h_w w y - h_w w' y| ≤ ‖w - w'‖ := by
        have h9 : ∀ᵐ (y : E n) ∂μ, |h_w w y - h_w w' y| ≤ ‖w - w'‖ := h_lip w w'
        have h_ac : μ.restrict (closedBall x r) ≪ μ := by
          intro t ht
          have h_le : μ.restrict (closedBall x r) t ≤ μ t := by exact Measure.restrict_apply_le (closedBall x r) t
          rw [ht] at h_le
          simpa using h_le
        exact h9.filter_mono h_ac.ae_le
      have h7 : ∫ y in closedBall x r, |h_w w y - h_w w' y| ∂μ ≤
          ∫ y in closedBall x r, (‖w - w'‖ : ℝ) ∂μ :=
        integral_mono_ae ((h_int w).restrict.sub (h_int w').restrict).norm
          (integrable_const ‖w - w'‖) h8
      have h9 : ∫ y in closedBall x r, (‖w - w'‖ : ℝ) ∂μ =
          (μ (closedBall x r)).toReal * ‖w - w'‖ := by
        have h10 : ∫ y in closedBall x r, (‖w - w'‖ : ℝ) ∂μ =
            μ.real (closedBall x r) * ‖w - w'‖ := by
          simp [integral_const]
        have h11 : μ.real (closedBall x r) = (μ (closedBall x r)).toReal := by rfl
        rw [h10, h11]
        <;> ring
      rw [h9] at h7
      calc |(∫ y in closedBall x r, (h_w w y - h_w w' y) ∂μ)| / (μ (closedBall x r)).toReal
          ≤ (∫ y in closedBall x r, |h_w w y - h_w w' y| ∂μ) / (μ (closedBall x r)).toReal := by gcongr
        _ ≤ ((μ (closedBall x r)).toReal * ‖w - w'‖) / (μ (closedBall x r)).toReal := by gcongr
        _ = ‖w - w'‖ := by
          field_simp [hμr_pos.ne'] <;> ring

  -- Pointwise Lipschitz bound
  have h_pt_lip : ∀ᵐ (x : E n) ∂μ, ∀ (w w' : E n),
      |h_w w x - h_w w' x| ≤ ‖w - w'‖ := by
    filter_upwards [h_norm_le_one] with x hx w w'
    have h_eq2 : inner ℝ w (ν_U x) - inner ℝ w' (ν_U x) = inner ℝ (w - w') (ν_U x) := by
      rw [inner_sub_left]
    have h1 : |inner ℝ w (ν_U x) - inner ℝ w' (ν_U x)| ≤ ‖w - w'‖ * ‖ν_U x‖ := by
      rw [h_eq2]
      exact abs_real_inner_le_norm (w - w') (ν_U x)
    have h2 : |h_w w x - h_w w' x| ≤ |inner ℝ w (ν_U x) - inner ℝ w' (ν_U x)| :=
      h_rev_abs (inner ℝ w (ν_U x)) (inner ℝ w' (ν_U x))
    have h3 : ‖w - w'‖ * ‖ν_U x‖ ≤ ‖w - w'‖ := by
      have h4 : 0 ≤ ‖w - w'‖ := by positivity
      nlinarith
    exact h2.trans (h1.trans h3)

  filter_upwards [h_all_D, h_pt_lip] with x hx_D hx_lip
  intro w

  -- For ε > 0, find w' ∈ D close to w
  have h_approx : ∀ (ε : ℝ), 0 < ε → ∃ (w' : E n), w' ∈ D ∧ ‖w - w'‖ < ε := by
    intro ε hε
    have h_dense' : w ∈ closure D := hD_dense w
    have h : ∃ (w' : E n), w' ∈ D ∧ dist w w' < ε :=
      Metric.mem_closure_iff.mp h_dense' ε hε
    rcases h with ⟨w', hw'_D, hdist⟩
    exact ⟨w', hw'_D, by simpa [dist_eq_norm] using hdist⟩

  have h_tendsto : Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, h_w w y ∂μ) / (μ (closedBall x r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (h_w w x)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rcases h_approx (ε / 3) (by linarith) with ⟨w', hw'_D, h_close⟩
    have h_diff_w' : Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, h_w w' y ∂μ) / (μ (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (h_w w' x)) := hx_D w' hw'_D
    have h_event : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
        dist ((∫ y in closedBall x r, h_w w' y ∂μ) / (μ (closedBall x r)).toReal) (h_w w' x) < ε / 3 := by
      rw [Metric.tendsto_nhds] at h_diff_w'
      exact h_diff_w' (ε / 3) (by linarith)
    filter_upwards [h_event] with r hr
    let A := ((∫ y in closedBall x r, h_w w y ∂μ) / (μ (closedBall x r)).toReal)
    let B := ((∫ y in closedBall x r, h_w w' y ∂μ) / (μ (closedBall x r)).toReal)
    let C := h_w w x
    let D := h_w w' x
    have h1 : dist A C ≤ dist A B + dist B D + dist D C := by
      calc dist A C = dist A C := rfl
        _ ≤ dist A B + dist B C := dist_triangle A B C
        _ ≤ dist A B + (dist B D + dist D C) := by gcongr <;> exact dist_triangle B D C
        _ = dist A B + dist B D + dist D C := by ring
    have h2 : dist A B ≤ ‖w - w'‖ := h_avg_lip w w' x r
    have h3 : dist B D < ε / 3 := hr
    have h4 : dist D C ≤ ‖w - w'‖ := by
      have h5 : dist D C = |D - C| := by simp [Real.dist_eq]
      rw [h5]
      have h6 : |h_w w' x - h_w w x| ≤ ‖w' - w‖ := hx_lip w' w
      have h7 : ‖w' - w‖ = ‖w - w'‖ := norm_sub_rev w' w
      rw [h7] at h6
      exact h6
    have h5 : dist A C < ε := by
      calc dist A C ≤ dist A B + dist B D + dist D C := h1
        _ ≤ ‖w - w'‖ + (ε / 3) + ‖w - w'‖ := by gcongr
        _ < ε / 3 + ε / 3 + ε / 3 := by linarith [h_close]
        _ = ε := by ring
    exact h5

  exact h_tendsto

end Geometry.StructureTheorem
