import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Tactic

/-!
# Local Coarea Inequality (Clean Version)

At a point x₀ where ‖∇f(x₀)‖ = 1, for any ε > 0 there exists r > 0 such that
for all a < b:

  volume {x ∈ B(x₀,r) | a < f(x) ≤ b} ≤ (1+ε) · ∫ₐᵇ μHE[n-1]({x ∈ B(x₀,r) | f(x)=s}) ds

Uses:
- Inverse function theorem for F(y) = π(y) + f(y)·e
- Area formula (same-dimensional)
- EuclideanHausdorffMeasure_eq_lintegral for Fubini
- Lipschitz bound on level sets
-/

open MeasureTheory Metric Set ENNReal
open scoped MeasureTheory ContDiff

namespace Geometry

variable {n : ℕ} [Nonempty (Fin n)]

/-- Lipschitz image bound for Euclidean Hausdorff measure. -/
lemma lipschitzOnWith_euclideanHausdorffMeasure_image_le
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {K : NNReal} {f : X → Y} {s : Set X} {d : ℕ}
    (h : LipschitzOnWith K f s) :
    μHE[d] (f '' s) ≤ (K : ENNReal) ^ (d : ℝ) * μHE[d] s := by
  have h1 : μH[d] (f '' s) ≤ (K : ENNReal) ^ (d : ℝ) * μH[d] s :=
    h.hausdorffMeasure_image_le (by positivity)
  have h2 : ∀ (c : ENNReal), c * μH[d] (f '' s) ≤ (K : ENNReal) ^ (d : ℝ) * (c * μH[d] s) := by
    intro c
    have h3 : c * μH[d] (f '' s) ≤ c * ((K : ENNReal) ^ (d : ℝ) * μH[d] s) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : c * ((K : ENNReal) ^ (d : ℝ) * μH[d] s) = (K : ENNReal) ^ (d : ℝ) * (c * μH[d] s) := by ring
    exact le_trans h3 (le_of_eq h4)
  simpa [MeasureTheory.Measure.euclideanHausdorffMeasure_def, Measure.smul_apply] using h2 _

/-- **Local coarea inequality** at a unit-gradient point, for arbitrary measurable subsets. -/
theorem local_coarea_inequality
    (f : E n → ℝ) (hf : ContDiff ℝ 1 f)
    (x₀ : E n) (h₁ : ‖fderiv ℝ f x₀‖ = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (r : ℝ), 0 < r ∧ ∀ (C : Set (E n)), MeasurableSet C → C ⊆ closedBall x₀ r →
      ∀ (a b : ℝ), a < b →
        volume {x ∈ C | a < f x ∧ f x ≤ b} ≤
          ENNReal.ofReal (1 + ε) * ∫⁻ s in Set.Ioc a b,
            μHE[n - 1] {x ∈ C | f x = s} := by
  -- Step 1: Set up e, H, π, F
  let e : E n := (InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ f x₀)
  have he_norm : ‖e‖ = 1 := by
    have h : ‖e‖ = ‖fderiv ℝ f x₀‖ := (InnerProductSpace.toDual ℝ (E n)).symm.norm_map _
    rw [h, h₁]
  have he_ne_zero : e ≠ 0 := by
    intro h; rw [h] at he_norm; simp at he_norm <;> linarith
  let H : Submodule ℝ (E n) := (Submodule.span ℝ {e})ᗮ
  let πCL : E n →L[ℝ] H := H.orthogonalProjection
  let incl_H : H →L[ℝ] E n :=
    ⟨Submodule.subtype H, continuous_subtype_val⟩
  let π' : E n →L[ℝ] E n := incl_H.comp πCL
  let π : E n → E n := fun y => (πCL y : E n)
  let F : E n → E n := fun y => π y + f y • e
  let coordE : E n → ℝ := fun y => inner ℝ y e
  let f' := fderiv ℝ f x₀

  have h_inner_e : ∀ (x : E n), inner ℝ e x = f' x := by
    intro x; exact InnerProductSpace.toDual_symm_apply (x := x) (y := f')

  -- Step 2: DF(x₀) = id
  let DF : E n →L[ℝ] E n := π' + f'.smulRight e
  have hDF_id : DF = ContinuousLinearMap.id ℝ (E n) := by
    apply ContinuousLinearMap.ext
    intro v
    have h1 : f' v = inner ℝ e v := (h_inner_e v).symm
    have h2 : DF v = π v + f' v • e := by rfl
    have h3 : inner ℝ e v = inner ℝ v e := (real_inner_comm e v).symm
    rw [h2, h1, h3]
    have h_decomp : v = π v + inner ℝ v e • e := by
      have h_sub : v - π v ∈ Hᗮ := H.sub_starProjection_mem_orthogonal v
      have hH' : Hᗮ = Submodule.span ℝ {e} := by
        have h1 : H = (Submodule.span ℝ {e})ᗮ := by rfl
        rw [h1]
        exact Submodule.orthogonal_orthogonal (Submodule.span ℝ {e})
      rw [hH'] at h_sub
      have h5 : ∃ (c : ℝ), v - π v = c • e := by
        have h51 : v - π v ∈ Submodule.span ℝ {e} := h_sub
        have h52 : ∃ (a : ℝ), a • e = v - π v := Submodule.mem_span_singleton.mp h51
        rcases h52 with ⟨a, ha⟩
        exact ⟨a, ha.symm⟩
      rcases h5 with ⟨c, hc⟩
      have hc' : c = inner ℝ v e := by
        have h7 : inner ℝ (v - π v) e = inner ℝ v e - inner ℝ (π v) e := by
          simp [inner_sub_left] <;> ring
        have h8 : inner ℝ (v - π v) e = c := by
          rw [hc]
          have h9 : inner ℝ (c • e) e = c * inner ℝ e e := by
            simp [inner_smul_left]
          rw [h9]
          have h10 : inner ℝ e e = ‖e‖ ^ 2 := real_inner_self_eq_norm_sq e
          rw [h10, he_norm] <;> ring
        have hπ : inner ℝ (π v) e = 0 := by
          have hπmem : π v ∈ H := (πCL v).property
          have h2 : e ∈ Submodule.span ℝ {e} := by
            exact Submodule.mem_span_singleton.mpr ⟨1, by simp⟩
          have hπmem' : π v ∈ (Submodule.span ℝ {e})ᗮ := by simpa [H] using hπmem
          have h3 : inner ℝ e (π v) = 0 := hπmem' e h2
          have h4 : inner ℝ (π v) e = inner ℝ e (π v) :=
            (real_inner_comm (π v) e).symm
          rw [h4]; exact h3
        linarith [h7, h8, hπ]
      have h9 : v - π v = inner ℝ v e • e := by
        exact hc.trans (congr_arg (fun x : ℝ => x • e) hc')
      calc v = π v + (v - π v) := by abel
           _ = π v + inner ℝ v e • e := by rw [h9]
    exact h_decomp.symm
  have hdet : DF.det = 1 := by
    rw [hDF_id]
    simpa [ContinuousLinearMap.det] using LinearMap.det_id

  -- Step 3: IFT
  have hF_strict : HasStrictFDerivAt F DF x₀ := by
    have h1 : HasStrictFDerivAt f f' x₀ := hf.hasStrictFDerivAt (by simp)
    have hπ_strict : HasStrictFDerivAt π π' x₀ := π'.hasStrictFDerivAt
    have h2 : HasStrictFDerivAt (fun y : E n => f y • e) (f'.smulRight e) x₀ := by
      have h_scale : HasStrictFDerivAt (fun x : ℝ => x • e)
          ((ContinuousLinearMap.id ℝ ℝ).smulRight e) (f x₀) := by
        exact (hasStrictFDerivAt_id (f x₀)).smul_const e
      exact h_scale.comp x₀ h1
    exact hπ_strict.add h2

  let DF_equiv : E n ≃L[ℝ] E n :=
    DF.toContinuousLinearEquivOfDetNeZero (by rw [hdet] <;> norm_num)
  have h_eq_df : (DF_equiv : E n →L[ℝ] E n) = DF := by ext y; rfl
  have hF_strict_equiv : HasStrictFDerivAt F (DF_equiv : E n →L[ℝ] E n) x₀ := by
    rw [h_eq_df]; exact hF_strict
  let φ : OpenPartialHomeomorph (E n) (E n) :=
    hF_strict_equiv.toOpenPartialHomeomorph F
  have hx_source : x₀ ∈ φ.source :=
    hF_strict_equiv.mem_toOpenPartialHomeomorph_source
  have h_coe : (φ : E n → E n) = F :=
    hF_strict_equiv.toOpenPartialHomeomorph_coe

  -- Step 4: Choose r
  let δ : ℝ := ε / (1 + ε)
  have hδ_pos : 0 < δ := by positivity
  have h1mpδ : 0 < 1 - δ := by
    have h : 1 - δ = 1 / (1 + ε) := by
      dsimp only [δ]
      field_simp [hε.ne'] <;> ring
    rw [h]; positivity
  have h_bound : 1 / (1 - δ) = 1 + ε := by
    have h1 : 1 - δ = 1 / (1 + ε) := by
      dsimp only [δ]
      field_simp [hε.ne'] <;> ring
    rw [h1]
    field_simp [hε.ne'] <;> ring

  -- F is C¹
  have hπ_eq2 : π = π' := by funext x; rfl
  have hπ_smooth : ContDiff ℝ 1 π := by
    have h : ContDiff ℝ ∞ π' := π'.contDiff
    have h' : ContDiff ℝ 1 π' := h.of_le (by simp)
    rw [hπ_eq2]
    exact h'
  have h_smul : ContDiff ℝ 1 (fun y : E n => f y • e) := hf.smul_const e
  have hF_c1 : ContDiff ℝ 1 F := hπ_smooth.add h_smul

  have h_cont_det : Continuous (fun y : E n => |(fderiv ℝ F y).det|) := by
    have h1 : Continuous (fderiv ℝ F) := (contDiff_one_iff_fderiv.mp hF_c1).2
    have h2 : Continuous (fun (f' : E n →L[ℝ] E n) => f'.det) :=
      ContinuousLinearMap.continuous_det
    exact Continuous.abs (h2.comp h1)
  have h_at : |(fderiv ℝ F x₀).det| = 1 := by
    have h_eq : fderiv ℝ F x₀ = DF := HasFDerivAt.fderiv hF_strict.hasFDerivAt
    rw [h_eq, hdet] <;> norm_num
  have h_gt : 1 - δ < |(fderiv ℝ F x₀).det| := by
    rw [h_at]
    have h : 1 - δ < 1 := by linarith [hδ_pos]
    exact h
  have h_nhds : ∀ᶠ (y : E n) in nhds x₀, 1 - δ < |(fderiv ℝ F y).det| :=
    h_cont_det.continuousAt.eventually (Ioi_mem_nhds h_gt)
  have h_source_nhds : φ.source ∈ nhds x₀ := φ.open_source.mem_nhds hx_source
  have h_source_eventually : ∀ᶠ (y : E n) in nhds x₀, y ∈ φ.source :=
    h_source_nhds
  have h_both : ∀ᶠ (y : E n) in nhds x₀, y ∈ φ.source ∧ 1 - δ < |(fderiv ℝ F y).det| :=
    h_source_eventually.and h_nhds
  rcases Metric.mem_nhds_iff.mp h_both with ⟨r0, hr0_pos, hr0⟩
  let r := r0 / 2
  have hr_pos : 0 < r := half_pos hr0_pos
  let B := closedBall x₀ r
  have hB_in_ball : B ⊆ ball x₀ r0 := by
    intro y hy
    have hdist : dist y x₀ ≤ r := by simpa [B, dist_comm] using hy
    have h : dist y x₀ < r0 := by
      calc dist y x₀ ≤ r := hdist
           _ = r0 / 2 := by rfl
           _ < r0 := by linarith [hr0_pos]
    exact mem_ball.mp h
  have hB_sub_source : B ⊆ φ.source := fun y hy => (hr0 (hB_in_ball hy)).1
  have hB_det : ∀ y ∈ B, 1 - δ < |(fderiv ℝ F y).det| := fun y hy => (hr0 (hB_in_ball hy)).2
  have hB_inj : Set.InjOn F B := by
    intro y hy z hz h_eq
    have hys : y ∈ φ.source := hB_sub_source hy
    have hzs : z ∈ φ.source := hB_sub_source hz
    have h1 : φ y = F y := by rw [←h_coe] <;> rfl
    have h2 : φ z = F z := by rw [←h_coe] <;> rfl
    have h3 : φ y = φ z := by rw [h1, h2, h_eq]
    exact φ.injOn hys hzs h3

  refine' ⟨r, hr_pos, _⟩
  intro C hC_meas hC_sub a b hab

  let A' : Set (E n) := {x ∈ C | a < f x ∧ f x ≤ b}
  have hA'_meas : MeasurableSet A' := by
    have h2 : MeasurableSet {x : E n | a < f x} :=
      isOpen_Ioi.measurableSet.preimage hf.continuous.measurable
    have h3 : MeasurableSet {x : E n | f x ≤ b} :=
      isClosed_Iic.measurableSet.preimage hf.continuous.measurable
    exact hC_meas.inter (h2.inter h3)
  let S : Set (E n) := F '' A'

  have hS_meas : MeasurableSet S := by
    have h2 : A' ⊆ φ.source := fun y hy => hB_sub_source (hC_sub hy.1)
    have h_eq_image : S = φ '' A' := by ext z; simp [S, h_coe]
    rw [h_eq_image]
    have h4 : φ '' A' = φ.target ∩ (φ.symm) ⁻¹' A' := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hys : y ∈ φ.source := h2 hy
        have hyt : φ y ∈ φ.target := φ.mapsTo hys
        have hsymm : φ.symm (φ y) = y := φ.left_inv hys
        exact ⟨hyt, by rw [hsymm] <;> exact hy⟩
      · rintro ⟨hzt, hsymm⟩
        have h5 : φ.symm z ∈ A' := hsymm
        have h6 : φ (φ.symm z) = z := φ.right_inv hzt
        exact ⟨φ.symm z, h5, h6⟩
    rw [h4]
    let g : φ.target → E n := fun x => φ.symm x
    have hg_cont : Continuous g := continuousOn_iff_continuous_restrict.mp φ.continuousOn_invFun
    have hg_meas : Measurable g := hg_cont.measurable
    have hpreim : MeasurableSet (g ⁻¹' A') := hA'_meas.preimage hg_meas
    have h_img : (Subtype.val : φ.target → E n) '' (g ⁻¹' A') = φ.target ∩ (φ.symm) ⁻¹' A' := by
      ext z
      simp only [g, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.property, hx⟩
      · rintro ⟨hzt, hpre⟩
        exact ⟨⟨z, hzt⟩, hpre, rfl⟩
    rw [←h_img]
    have h_target_meas : MeasurableSet φ.target := φ.open_target.measurableSet
    exact MeasurableSet.subtype_image h_target_meas hpreim

  -- Step 5: Area formula
  have hF_diff : ∀ (y : E n), HasStrictFDerivAt F (fderiv ℝ F y) y := by
    intro y
    have h : ContDiffAt ℝ 1 F y := hF_c1.contDiffAt
    exact h.hasStrictFDerivAt (by norm_num)
  have h_fderiv_on : ∀ y ∈ A', HasFDerivWithinAt F (fderiv ℝ F y) A' y := by
    intro y _
    exact (hF_diff y).hasFDerivAt.hasFDerivWithinAt
  have hA'_sub_B : A' ⊆ B := fun x hx => hC_sub hx.1
  have hA'_inj : Set.InjOn F A' := Set.InjOn.mono hA'_sub_B hB_inj
  have h_cov_raw : ∫⁻ x in F '' A', (1 : ENNReal) =
      ∫⁻ x in A', ENNReal.ofReal |(fderiv ℝ F x).det| * 1 :=
    MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
      volume hA'_meas h_fderiv_on hA'_inj (fun _ => 1)
  have h_cov : volume S = ∫⁻ y in A', ENNReal.ofReal |(fderiv ℝ F y).det| := by
    have h1 : ∫⁻ x in S, (1 : ENNReal) = volume S := by simp
    have h2 : ∫⁻ x in A', ENNReal.ofReal |(fderiv ℝ F x).det| * 1 =
        ∫⁻ x in A', ENNReal.ofReal |(fderiv ℝ F x).det| := by
      apply lintegral_congr
      intro x; ring
    rw [h1, h2] at h_cov_raw
    exact h_cov_raw

  have h_lower : ∫⁻ y in A', ENNReal.ofReal |(fderiv ℝ F y).det| ≥
      ENNReal.ofReal (1 - δ) * volume A' := by
    have h' : ∀ᵐ y ∂volume.restrict A',
        ENNReal.ofReal (1 - δ) ≤ ENNReal.ofReal |(fderiv ℝ F y).det| := by
      filter_upwards [ae_restrict_mem hA'_meas] with y hy
      have h9 : y ∈ B := hC_sub hy.1
      have h10 : 1 - δ < |(fderiv ℝ F y).det| := hB_det y h9
      exact ENNReal.ofReal_le_ofReal (le_of_lt h10)
    have h'' : ∫⁻ y in A', ENNReal.ofReal (1 - δ) ≤
        ∫⁻ y in A', ENNReal.ofReal |(fderiv ℝ F y).det| :=
      lintegral_mono_ae h'
    have h3 : ∫⁻ y in A', ENNReal.ofReal (1 - δ) =
        ENNReal.ofReal (1 - δ) * volume A' := by
      simp [lintegral_const]
      <;> ring
    rw [h3] at h''
    exact h''

  have h_vol_bound : volume A' ≤ ENNReal.ofReal (1 / (1 - δ)) * volume S := by
    have h_pos : 0 < 1 - δ := h1mpδ
    have h_mul : ENNReal.ofReal (1 / (1 - δ)) * ENNReal.ofReal (1 - δ) = 1 := by
      rw [←ENNReal.ofReal_mul (by positivity)]
      <;> field_simp [h_pos.ne'] <;> norm_num
    have h_main : ENNReal.ofReal (1 - δ) * volume A' ≤ volume S := by
      rw [h_cov]; exact h_lower
    have h9 : ENNReal.ofReal (1 / (1 - δ)) * (ENNReal.ofReal (1 - δ) * volume A') = volume A' := by
      have h10 : ENNReal.ofReal (1 / (1 - δ)) * (ENNReal.ofReal (1 - δ) * volume A') =
          (ENNReal.ofReal (1 / (1 - δ)) * ENNReal.ofReal (1 - δ)) * volume A' := by
        rw [mul_assoc]
      rw [h10, h_mul, one_mul]
    have h_le : ENNReal.ofReal (1 / (1 - δ)) * (ENNReal.ofReal (1 - δ) * volume A') ≤
        ENNReal.ofReal (1 / (1 - δ)) * volume S := mul_le_mul_left' h_main _
    rw [h9] at h_le
    exact h_le

  -- Step 6: coordE ∘ F = f
  have h_coordF : ∀ y, coordE (F y) = f y := by
    intro y
    have hπmem : π y ∈ H := (πCL y).property
    have h2 : e ∈ Submodule.span ℝ {e} := by
      exact Submodule.mem_span_singleton.mpr ⟨1, by simp⟩
    have h3 : π y ∈ (Submodule.span ℝ {e})ᗮ := by simpa [H] using hπmem
    have h4 : inner ℝ e (π y) = 0 := h3 e h2
    have h5 : inner ℝ (π y) e = 0 := by
      have h6 : inner ℝ (π y) e = inner ℝ e (π y) := (real_inner_comm _ _).symm
      rw [h6, h4]
    have h7 : coordE (F y) = inner ℝ (π y + f y • e) e := by rfl
    rw [h7]
    have h8 : inner ℝ (π y + f y • e) e = inner ℝ (π y) e + f y * inner ℝ e e := by
      have h81 : inner ℝ (π y + f y • e) e = inner ℝ (π y) e + inner ℝ (f y • e) e := inner_add_left _ _ _
      have h82 : inner ℝ (f y • e) e = f y * inner ℝ e e := inner_smul_left _ _ _
      rw [h81, h82]
    rw [h8, h5]
    have h9 : inner ℝ e e = ‖e‖ ^ 2 := real_inner_self_eq_norm_sq e
    rw [h9, he_norm] <;> ring

  -- Step 7: Fubini via euclideanHausdorffMeasure_eq_lintegral
  have h_affine_eq : ∀ (t : ℝ),
      (AffineSubspace.mk' (t • e) (ℝ ∙ e)ᗮ : Set (E n)) = {y | coordE y = t} := by
    intro t
    ext y
    have h_mem : y ∈ (AffineSubspace.mk' (t • e) (ℝ ∙ e)ᗮ : Set (E n)) ↔
        y - t • e ∈ (ℝ ∙ e)ᗮ := by
      simp [AffineSubspace.mem_mk', vsub_eq_sub]
      <;> rfl
    rw [h_mem]
    have h1 : y - t • e ∈ (ℝ ∙ e)ᗮ ↔ inner ℝ e (y - t • e) = 0 := by
      constructor
      · intro h
        have he : e ∈ (ℝ ∙ e) := by
          exact Submodule.mem_span_singleton.mpr ⟨1, by simp⟩
        exact h e he
      · intro h
        intro v hv
        have hve : ∃ (a : ℝ), a • e = v := Submodule.mem_span_singleton.mp hv
        rcases hve with ⟨c, hc⟩
        have hcv : v = c • e := hc.symm
        rw [hcv]
        simpa [inner_smul_left] using mul_eq_zero.mpr (Or.inr h)
    rw [h1]
    have h2 : inner ℝ e (y - t • e) = inner ℝ e y - t := by
      have h3 : inner ℝ e (y - t • e) = inner ℝ e y - inner ℝ e (t • e) := by
        rw [inner_sub_right] <;> rfl
      rw [h3]
      have h4 : inner ℝ e (t • e) = t * inner ℝ e e := by
        rw [inner_smul_right] <;> ring
      rw [h4]
      have h5 : inner ℝ e e = ‖e‖ ^ 2 := real_inner_self_eq_norm_sq e
      rw [h5, he_norm] <;> ring
    rw [h2]
    constructor
    · intro h
      have h3 : inner ℝ e y = t := by linarith
      have h4 : coordE y = inner ℝ y e := by rfl
      have h5 : inner ℝ y e = inner ℝ e y := (real_inner_comm y e).symm
      have h6 : coordE y = t := by rw [h4, h5, h3]
      simpa using h6
    · intro h
      have h4 : coordE y = inner ℝ y e := by rfl
      have h5 : inner ℝ y e = inner ℝ e y := (real_inner_comm y e).symm
      have h6 : inner ℝ e y = t := by
        rw [←h5, ←h4, h]
      linarith

  have h_fubini : volume S = ∫⁻ t : ℝ, μHE[n - 1] (S ∩ {y | coordE y = t}) := by
    have h_main : μHE[Module.finrank ℝ (E n)] S =
        ‖e‖ₑ * ∫⁻ t : ℝ, μHE[Module.finrank ℝ (E n) - 1]
          (S ∩ (AffineSubspace.mk' (t • e +ᵥ (0 : E n)) (ℝ ∙ e)ᗮ : Set (E n))) :=
      EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral (0 : E n) (v := e) he_ne_zero (ht := hS_meas)
    have h_affine : ∀ (x : ℝ), (AffineSubspace.mk' (x • e +ᵥ (0 : E n)) (ℝ ∙ e)ᗮ : Set (E n)) = {y | coordE y = x} := by
      intro x
      have h_zero : x • e +ᵥ (0 : E n) = x • e := by simp
      rw [h_zero]
      exact h_affine_eq x
    simp_rw [h_affine] at h_main
    have h_enorm : ‖e‖ₑ = 1 := by
      have h : ‖e‖ₑ = ENNReal.ofReal ‖e‖ := by simp
      rw [h, he_norm]
      <;> simp
    rw [h_enorm, one_mul] at h_main
    have h_finrank : Module.finrank ℝ (E n) = n := by simp
    have h1 : μHE[n] S = volume S := by
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume n] <;> rfl
    have h_main2 : μHE[n] S = ∫⁻ t : ℝ, μHE[n - 1] (S ∩ {y | coordE y = t}) := by
      simpa [h_finrank] using h_main
    exact h1.symm.trans h_main2

  -- Step 8: S ∩ {coordE = t} = F '' (C ∩ {f = t}) for t ∈ Ioc a b
  have h_slice : ∀ (t : ℝ), t ∈ Set.Ioc a b →
      S ∩ {y | coordE y = t} = F '' {x ∈ C | f x = t} := by
    intro t ht
    ext z
    simp only [S, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨y, hyA, rfl⟩, hct⟩
      have hft : f y = t := by
        have h : coordE (F y) = f y := h_coordF y
        rw [h] at hct <;> exact hct
      exact ⟨y, ⟨hyA.1, hft⟩, rfl⟩
    · rintro ⟨y, ⟨hyC, hft⟩, rfl⟩
      have hct : coordE (F y) = t := by
        rw [h_coordF y, hft]
      have h_ay : a < f y := by rw [hft]; exact ht.1
      have h_by : f y ≤ b := by rw [hft]; exact ht.2
      have hyA : y ∈ A' := ⟨hyC, ⟨h_ay, h_by⟩⟩
      exact ⟨⟨y, hyA, rfl⟩, hct⟩

  -- Step 9: F restricted to level sets is 1-Lipschitz
  have hπ_lipschitz : LipschitzWith 1 π := by
    have h1 : LipschitzWith 1 πCL := H.lipschitzWith_orthogonalProjectionOnto
    have h2 : LipschitzWith 1 (fun x : H => (x : E n)) := by
      intro x y
      have h_edist : edist (x : E n) (y : E n) = edist x y := by rfl
      rw [h_edist] <;> simp
    have h_comp : LipschitzWith (1 * 1) ((fun x : H => (x : E n)) ∘ πCL) := h2.comp h1
    have h_eq : (fun x : H => (x : E n)) ∘ πCL = π := by funext x; rfl
    rw [h_eq] at h_comp
    simpa using h_comp
  have hF_lipschitz : ∀ (t : ℝ), LipschitzOnWith 1 F {x : E n | f x = t} := by
    intro t
    intro y hy z hz
    have hfy : f y = t := hy
    have hfz : f z = t := hz
    have h_sub : F y - F z = π y - π z := by
      simp [F, hfy, hfz, sub_add_sub_cancel] <;> abel
    have h_edist : edist (F y) (F z) = edist (π y) (π z) := by
      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, h_sub]
    rw [h_edist]
    exact hπ_lipschitz y z
  have h_hausdorff : ∀ (t : ℝ), μHE[n - 1] (F '' {x ∈ C | f x = t}) ≤ μHE[n - 1] {x ∈ C | f x = t} := by
    intro t
    have h_sub : {x ∈ C | f x = t} ⊆ {x : E n | f x = t} := by
      intro x hx; exact hx.2
    have h_restrict : LipschitzOnWith 1 F ({x ∈ C | f x = t}) :=
      (hF_lipschitz t).mono h_sub
    have h := lipschitzOnWith_euclideanHausdorffMeasure_image_le (d := n - 1) h_restrict
    simpa using h

  -- Step 10: Combine
  have h_support : ∀ (t : ℝ), t ∉ Set.Ioc a b → μHE[n - 1] (S ∩ {y | coordE y = t}) = 0 := by
    intro t ht
    have h_empty : S ∩ {y | coordE y = t} = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      intro ⟨hz1, hz2⟩
      rcases hz1 with ⟨y, hyA, rfl⟩
      have hft : a < f y ∧ f y ≤ b := hyA.2
      have hct : coordE (F y) = f y := h_coordF y
      have hz2' : coordE (F y) = t := by simpa using hz2
      rw [hct] at hz2'
      have h_contra : t ∈ Set.Ioc a b := by
        exact ⟨by linarith [hft.1], by linarith [hft.2]⟩
      exact ht h_contra
    rw [h_empty]; simp
  have h_fubini_restricted : volume S = ∫⁻ t in Set.Ioc a b, μHE[n - 1] (S ∩ {y | coordE y = t}) := by
    rw [h_fubini]
    let g : ℝ → ENNReal := fun t => μHE[n - 1] (S ∩ {y | coordE y = t})
    have h1 : (∫⁻ t : ℝ, g t) = ∫⁻ t : ℝ, Set.indicator (Set.Ioc a b) g t := by
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ Set.Ioc a b
      · simp [ht, Set.indicator_apply]
      · have hz : g t = 0 := h_support t ht
        simp [ht, hz, Set.indicator_apply]
    rw [h1]
    exact MeasureTheory.lintegral_indicator (by simp : MeasurableSet (Set.Ioc a b)) g
  have h_mono : ∀ (t : ℝ), μHE[n - 1] (S ∩ {y | coordE y = t}) ≤ μHE[n - 1] {x ∈ C | f x = t} := by
    intro t
    by_cases ht : t ∈ Set.Ioc a b
    · have h_eq : μHE[n - 1] (S ∩ {y | coordE y = t}) = μHE[n - 1] (F '' {x ∈ C | f x = t}) := by
        rw [h_slice t ht]
      rw [h_eq]
      exact h_hausdorff t
    · have hz : μHE[n - 1] (S ∩ {y | coordE y = t}) = 0 := h_support t ht
      rw [hz]
      positivity
  have h_final : volume S ≤ ∫⁻ t in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = t} := by
    rw [h_fubini_restricted]
    exact lintegral_mono h_mono

  calc volume A'
    ≤ ENNReal.ofReal (1 / (1 - δ)) * volume S := h_vol_bound
  _ ≤ ENNReal.ofReal (1 / (1 - δ)) * (∫⁻ t in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = t}) :=
    mul_le_mul_left' h_final _
  _ = ENNReal.ofReal (1 + ε) * (∫⁻ t in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = t}) := by
    rw [h_bound] <;> rfl

end Geometry
