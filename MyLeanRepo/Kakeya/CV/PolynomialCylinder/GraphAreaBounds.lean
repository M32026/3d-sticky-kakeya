import MyLeanRepo.Kakeya.CV.PolynomialCylinder.GraphAreaLipschitz
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Order.Disjointed
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Graph area: weighted integral, area bounds, cover decomposition
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

-- ============================================================================
-- Weighted Lipschitz integral
-- ============================================================================

lemma weighted_lipschitz_integral {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {F : X → Y} {S : Set X} {L : NNReal} (hL : LipschitzOnWith L F S)
    (hS : MeasurableSet S) (hF : AEMeasurable F (μH[2].restrict S)) (w : Y → ENNReal) :
    ∫⁻ y in F '' S, w y ∂μH[2] ≤ (L : ENNReal)^2 * ∫⁻ x in S, w (F x) ∂μH[2] := by
  let μS := (μH[2] : Measure X).restrict S
  let ν : Measure Y := Measure.map F μS
  have h_meas_ineq : (μH[2] : Measure Y).restrict (F '' S) ≤ (L : ENNReal)^2 • ν := by
    rw [Measure.le_iff]
    intro A hA
    have h1 : A ∩ F '' S ⊆ F '' (F ⁻¹' A ∩ S) := by
      intro y hy
      rcases hy.2 with ⟨x, hxS, rfl⟩
      exact ⟨x, ⟨hy.1, hxS⟩, rfl⟩
    have h2 : (μH[2] : Measure Y) (A ∩ F '' S) ≤ (μH[2] : Measure Y) (F '' (F ⁻¹' A ∩ S)) :=
      measure_mono h1
    have h3 : (μH[2] : Measure Y) (F '' (F ⁻¹' A ∩ S)) ≤ (L : ENNReal)^2 * (μH[2] : Measure X) (F ⁻¹' A ∩ S) := by
      have hL' : LipschitzOnWith L F (F ⁻¹' A ∩ S) := by
        have h_sub : (F ⁻¹' A ∩ S) ⊆ S := by intro x hx; exact hx.2
        exact hL.mono h_sub
      have h3_raw := hL'.hausdorffMeasure_image_le (d := 2) (by norm_num)
      have h_eq : (L : ENNReal)^(2 : ℝ) = (L : ENNReal)^(2 : ℕ) := by
        simp [ENNReal.rpow_two]
        <;> ring
      rw [h_eq] at h3_raw
      exact h3_raw
    have h4 : ν A = (μH[2] : Measure X) (F ⁻¹' A ∩ S) := by
      rw [Measure.map_apply_of_aemeasurable hF hA]
      exact MeasureTheory.Measure.restrict_apply₀' hS.nullMeasurableSet
    calc (μH[2] : Measure Y).restrict (F '' S) A
      = (μH[2] : Measure Y) (A ∩ F '' S) := by rw [Measure.restrict_apply hA]
    _ ≤ (μH[2] : Measure Y) (F '' (F ⁻¹' A ∩ S)) := h2
    _ ≤ (L : ENNReal)^2 * (μH[2] : Measure X) (F ⁻¹' A ∩ S) := h3
    _ = (L : ENNReal)^2 * ν A := by rw [h4] <;> ring
  have h_integral : ∫⁻ y, w y ∂((μH[2] : Measure Y).restrict (F '' S)) ≤
      ∫⁻ y, w y ∂((L : ENNReal)^2 • ν) := lintegral_mono' h_meas_ineq le_rfl
  have h_smul : ∫⁻ y, w y ∂((L : ENNReal)^2 • ν) = (L : ENNReal)^2 * ∫⁻ y, w y ∂ν := by
    simpa [Measure.smul_apply] using rfl
  rw [h_smul] at h_integral
  have h_map : ∫⁻ y, w y ∂ν ≤ ∫⁻ x in S, w (F x) ∂μH[2] :=
    MeasureTheory.lintegral_map_le w F
  calc ∫⁻ y, w y ∂((μH[2] : Measure Y).restrict (F '' S))
    ≤ (L : ENNReal)^2 * ∫⁻ y, w y ∂ν := h_integral
  _ ≤ (L : ENNReal)^2 * ∫⁻ x in S, w (F x) ∂μH[2] := by gcongr

-- ============================================================================
-- Convex region bounds
-- ============================================================================

lemma graph_area_bound_on_convex {U : Set R2} {f : R2 → ℝ} {p : MvPolynomial (Fin 3) ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    (V : Set R2) (hV : Convex ℝ V) (hV_sub : V ⊆ U)
    (h1 : ∀ y ∈ V, (fderiv ℝ f y e02)^2 ≥ (81 / 100 : ℝ) * (fderiv ℝ f y e12)^2)
    (h2 : ∀ y ∈ V, (fderiv ℝ f y e02)^2 ≥ (9025 / 10000 : ℝ))
    (h_zero : ∀ y ∈ U, polynomialValue p (graphMap f y) = 0)
    (h_reg : ∀ y ∈ U, (polynomialGradient p (graphMap f y)) 2 ≠ 0)
    (S : Set R2) (hS : S ⊆ V) (hS_meas : MeasurableSet S) :
    ∫⁻ x in graphMap f '' S, graphAreaW p x ∂μH[2] ≤ 4 * planeConstant * volume S := by
  set G : R2 → R2 := graphG f with hG_def
  set H : R2 → R3 := fun y => graphMap f (Function.invFunOn G V y) with hH_def
  set φ : R2 → ENNReal := fun y => graphAreaW p (H y) with hφ_def
  have h_e02_ne_zero : ∀ y ∈ V, fderiv ℝ f y e02 ≠ 0 := by
    intro y hy
    have h_pos : (fderiv ℝ f y e02)^2 ≥ (9025 / 10000 : ℝ) := h2 y hy
    have h : (fderiv ℝ f y e02)^2 > 0 := by linarith
    by_contra h_contra
    rw [h_contra] at h
    norm_num at h
  have h_inj_V : Set.InjOn G V := graphG_injective_on_convex hU hf hV hV_sub h_e02_ne_zero
  have h_inj_S : Set.InjOn G S := h_inj_V.mono hS
  have h_cont_G : ContinuousOn G S := by
    have h_diff : DifferentiableOn ℝ G S := by
      intro x hx
      exact (hasFDerivAt_graphG (hf.differentiableAt (hU.mem_nhds (hV_sub (hS hx))))).differentiableAt.differentiableWithinAt
    exact h_diff.continuousOn
  have h_me : MeasurableEmbedding (S.restrict G) :=
    ContinuousOn.measurableEmbedding hS_meas h_cont_G h_inj_S
  have hG_image_meas : MeasurableSet (G '' S) := by
    have h_eq : (S.restrict G) '' Set.univ = G '' S := by
      ext y; simp [Set.restrict, Set.mem_image] <;> tauto
    have h : MeasurableSet ((S.restrict G) '' Set.univ) :=
      (MeasurableEmbedding.measurableSet_image h_me).mpr MeasurableSet.univ
    rw [h_eq] at h
    exact h
  have h_lip_H : LipschitzOnWith (2 : NNReal) H (G '' S) := by
    intro y1 hy1 y2 hy2
    rcases hy1 with ⟨x1, hx1, rfl⟩
    rcases hy2 with ⟨x2, hx2, rfl⟩
    have hx1V : x1 ∈ V := hS hx1
    have hx2V : x2 ∈ V := hS hx2
    have h_inv1 : Function.invFunOn G V (G x1) = x1 := by
      apply h_inj_V (Function.invFunOn_apply_mem hx1V) hx1V
      exact Function.invFunOn_apply_eq hx1V
    have h_inv2 : Function.invFunOn G V (G x2) = x2 := by
      apply h_inj_V (Function.invFunOn_apply_mem hx2V) hx2V
      exact Function.invFunOn_apply_eq hx2V
    have h_norm : ‖H (G x1) - H (G x2)‖ ≤ (2 : ℝ) * ‖G x1 - G x2‖ := by
      simpa [hH_def, h_inv1, h_inv2] using graph_lipschitz_after_change_C hU hf hV hV_sub h1 h2 x1 x2 hx1V hx2V
    have h_edist : edist (H (G x1)) (H (G x2)) ≤ (2 : NNReal) * edist (G x1) (G x2) := by
      have h5 : edist (H (G x1)) (H (G x2)) = ENNReal.ofReal ‖H (G x1) - H (G x2)‖ := by
        simp [edist_dist, dist_eq_norm]
      have h62 : edist (G x1) (G x2) = ENNReal.ofReal ‖G x1 - G x2‖ := by
        simp [edist_dist, dist_eq_norm]
      have h6 : (2 : NNReal) * edist (G x1) (G x2) = (2 : ENNReal) * ENNReal.ofReal ‖G x1 - G x2‖ := by
        rw [h62] <;> norm_cast
      rw [h5, h6]
      have h7 : ENNReal.ofReal ‖H (G x1) - H (G x2)‖ ≤ ENNReal.ofReal ((2 : ℝ) * ‖G x1 - G x2‖) :=
        ENNReal.ofReal_le_ofReal h_norm
      have h8 : ENNReal.ofReal ((2 : ℝ) * ‖G x1 - G x2‖) = (2 : ENNReal) * ENNReal.ofReal ‖G x1 - G x2‖ := by
        rw [ENNReal.ofReal_mul] <;> norm_cast
      rw [h8] at h7
      exact h7
    exact h_edist
  have h_cont_H : ContinuousOn H (G '' S) := h_lip_H.continuousOn
  have hH_ae : AEMeasurable H (μH[2].restrict (G '' S)) :=
    h_cont_H.aemeasurable hG_image_meas
  have h_image : H '' (G '' S) = graphMap f '' S := by
    ext z
    simp only [Set.mem_image, hH_def]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      have h_inv : Function.invFunOn G V (G x) = x := by
        apply h_inj_V (Function.invFunOn_apply_mem (hS hx)) (hS hx)
        exact Function.invFunOn_apply_eq (hS hx)
      exact ⟨x, hx, by rw [h_inv]⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨G x, ⟨x, hx, rfl⟩, ?_⟩
      have h_inv : Function.invFunOn G V (G x) = x := by
        apply h_inj_V (Function.invFunOn_apply_mem (hS hx)) (hS hx)
        exact Function.invFunOn_apply_eq (hS hx)
      rw [h_inv]
  have h_diff_G : ∀ x ∈ S, DifferentiableAt ℝ G x := by
    intro x hx
    exact (hasFDerivAt_graphG (hf.differentiableAt (hU.mem_nhds (hV_sub (hS hx))))).differentiableAt
  have h_fderiv_within : ∀ x ∈ S, HasFDerivWithinAt G (fderiv_graphG f x) S x := by
    intro x hx
    exact (hasFDerivAt_graphG (hf.differentiableAt (hU.mem_nhds (hV_sub (hS hx))))).hasFDerivWithinAt
  have h_det_eq : ∀ x ∈ S, (fderiv_graphG f x).det = - (fderiv ℝ f x e02) := by
    intro x _
    exact det_fderiv_graphG f x
  have h_phi_G : ∀ x ∈ S, φ (G x) = graphAreaW p (graphMap f x) := by
    intro x hx
    have h_inv : Function.invFunOn G V (G x) = x := by
      apply h_inj_V (Function.invFunOn_apply_mem (hS hx)) (hS hx)
      exact Function.invFunOn_apply_eq (hS hx)
    simp [φ, H, h_inv]
  have h_step1 : ∫⁻ z in graphMap f '' S, graphAreaW p z ∂μH[2] ≤
      (4 : ENNReal) * ∫⁻ y in G '' S, φ y ∂μH[2] := by
    rw [←h_image]
    have h := weighted_lipschitz_integral h_lip_H hG_image_meas hH_ae (graphAreaW p)
    have h' : ∫⁻ y in H '' (G '' S), graphAreaW p y ∂μH[2] ≤ (4 : ENNReal) * ∫⁻ x in G '' S, graphAreaW p (H x) ∂μH[2] := by
      convert h using 1 <;> norm_num
    simpa [φ] using h'
  letI haarI : (μH[2] : Measure R2).IsAddHaarMeasure := by
    have h : (μH[2] : Measure R2) = μH[(2 : ℕ)] := by rfl
    rw [h] <;> infer_instance
  have h_area : ∫⁻ y in G '' S, φ y ∂μH[2] =
      ∫⁻ x in S, ENNReal.ofReal |(fderiv_graphG f x).det| * φ (G x) ∂μH[2] :=
    MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
      (μH[2]) hS_meas h_fderiv_within h_inj_S φ
  have h_pointwise : ∀ x ∈ S,
      ENNReal.ofReal |(fderiv_graphG f x).det| * φ (G x) ≤ 1 := by
    intro x hx
    rw [h_det_eq x hx, h_phi_G x hx]
    have h_abs : |-(fderiv ℝ f x e02)| = |fderiv ℝ f x e02| := by rw [abs_neg]
    rw [h_abs]
    have h_bound : graphAreaW p (graphMap f x) * ENNReal.ofReal |fderiv ℝ f x e02| ≤ 1 :=
      graph_weight_bound hU hf h_zero h_reg (hV_sub (hS hx))
    have h_comm : ENNReal.ofReal |fderiv ℝ f x e02| * graphAreaW p (graphMap f x) =
        graphAreaW p (graphMap f x) * ENNReal.ofReal |fderiv ℝ f x e02| := mul_comm _ _
    rw [h_comm]
    exact h_bound
  have h_ae : ∀ᵐ x ∂μH[2].restrict S, ENNReal.ofReal |(fderiv_graphG f x).det| * φ (G x) ≤ 1 := by
    filter_upwards [self_mem_ae_restrict hS_meas] with x hx
    exact h_pointwise x hx
  have h_mono : ∫⁻ x in S, ENNReal.ofReal |(fderiv_graphG f x).det| * φ (G x) ∂μH[2] ≤ μH[2] S := by
    have h : ∫⁻ x in S, ENNReal.ofReal |(fderiv_graphG f x).det| * φ (G x) ∂μH[2] ≤
        ∫⁻ x in S, (1 : ENNReal) ∂μH[2] := lintegral_mono_ae h_ae
    have h2 : ∫⁻ x in S, (1 : ENNReal) ∂μH[2] = μH[2] S := by simp
    rw [h2] at h
    exact h
  have h_vol : μH[2] S = planeConstant * volume S := μH2_eq S
  calc
    ∫⁻ x in graphMap f '' S, graphAreaW p x ∂μH[2]
      ≤ 4 * ∫⁻ y in G '' S, φ y ∂μH[2] := h_step1
    _ = 4 * ∫⁻ x in S, ENNReal.ofReal |(fderiv_graphG f x).det| * φ (G x) ∂μH[2] := by rw [h_area]
    _ ≤ 4 * μH[2] S := by gcongr
    _ = 4 * planeConstant * volume S := by rw [h_vol] <;> ring

lemma graph_area_bound_on_convex' {U : Set R2} {f : R2 → ℝ} {p : MvPolynomial (Fin 3) ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    (V : Set R2) (hV : Convex ℝ V) (hV_sub : V ⊆ U)
    (h1 : ∀ y ∈ V, (fderiv ℝ f y e12)^2 ≥ (81 / 100 : ℝ) * (fderiv ℝ f y e02)^2)
    (h2 : ∀ y ∈ V, (fderiv ℝ f y e12)^2 ≥ (9025 / 10000 : ℝ))
    (h_zero : ∀ y ∈ U, polynomialValue p (graphMap f y) = 0)
    (h_reg : ∀ y ∈ U, (polynomialGradient p (graphMap f y)) 2 ≠ 0)
    (S : Set R2) (hS : S ⊆ V) (hS_meas : MeasurableSet S) :
    ∫⁻ x in graphMap f '' S, graphAreaW p x ∂μH[2] ≤ 4 * planeConstant * volume S := by
  set G : R2 → R2 := graphG' f with hG_def
  set H : R2 → R3 := fun y => graphMap f (Function.invFunOn G V y) with hH_def
  set φ : R2 → ENNReal := fun y => graphAreaW p (H y) with hφ_def
  have h_e12_ne_zero : ∀ y ∈ V, fderiv ℝ f y e12 ≠ 0 := by
    intro y hy
    have h_pos : (fderiv ℝ f y e12)^2 ≥ (9025 / 10000 : ℝ) := h2 y hy
    by_contra h_contra
    rw [h_contra] at h_pos
    norm_num at h_pos
  have h_inj_V : Set.InjOn G V := graphG'_injective_on_convex hU hf hV hV_sub h_e12_ne_zero
  have h_inj_S : Set.InjOn G S := h_inj_V.mono hS
  have h_cont_G : ContinuousOn G S := by
    have h_diff : DifferentiableOn ℝ G S := by
      intro x hx
      exact (hasFDerivAt_graphG' (hf.differentiableAt (hU.mem_nhds (hV_sub (hS hx))))).differentiableAt.differentiableWithinAt
    exact h_diff.continuousOn
  have h_me : MeasurableEmbedding (S.restrict G) :=
    ContinuousOn.measurableEmbedding hS_meas h_cont_G h_inj_S
  have hG_image_meas : MeasurableSet (G '' S) := by
    have h_eq : (S.restrict G) '' Set.univ = G '' S := by
      ext y; simp [Set.restrict, Set.mem_image] <;> tauto
    have h : MeasurableSet ((S.restrict G) '' Set.univ) :=
      (MeasurableEmbedding.measurableSet_image h_me).mpr MeasurableSet.univ
    rw [h_eq] at h
    exact h
  have h_lip_H : LipschitzOnWith (2 : NNReal) H (G '' S) := by
    intro y1 hy1 y2 hy2
    rcases hy1 with ⟨x1, hx1, rfl⟩
    rcases hy2 with ⟨x2, hx2, rfl⟩
    have hx1V : x1 ∈ V := hS hx1
    have hx2V : x2 ∈ V := hS hx2
    have h_inv1 : Function.invFunOn G V (G x1) = x1 := by
      apply h_inj_V (Function.invFunOn_apply_mem hx1V) hx1V
      exact Function.invFunOn_apply_eq hx1V
    have h_inv2 : Function.invFunOn G V (G x2) = x2 := by
      apply h_inj_V (Function.invFunOn_apply_mem hx2V) hx2V
      exact Function.invFunOn_apply_eq hx2V
    have h_norm : ‖H (G x1) - H (G x2)‖ ≤ (2 : ℝ) * ‖G x1 - G x2‖ := by
      simpa [hH_def, h_inv1, h_inv2] using graph_lipschitz_after_change_C' hU hf hV hV_sub h1 h2 x1 x2 hx1V hx2V
    have h_edist : edist (H (G x1)) (H (G x2)) ≤ (2 : NNReal) * edist (G x1) (G x2) := by
      have h5 : edist (H (G x1)) (H (G x2)) = ENNReal.ofReal ‖H (G x1) - H (G x2)‖ := by
        simp [edist_dist, dist_eq_norm]
      have h62 : edist (G x1) (G x2) = ENNReal.ofReal ‖G x1 - G x2‖ := by
        simp [edist_dist, dist_eq_norm]
      have h6 : (2 : NNReal) * edist (G x1) (G x2) = (2 : ENNReal) * ENNReal.ofReal ‖G x1 - G x2‖ := by
        rw [h62] <;> norm_cast
      rw [h5, h6]
      have h7 : ENNReal.ofReal ‖H (G x1) - H (G x2)‖ ≤ ENNReal.ofReal ((2 : ℝ) * ‖G x1 - G x2‖) :=
        ENNReal.ofReal_le_ofReal h_norm
      have h8 : ENNReal.ofReal ((2 : ℝ) * ‖G x1 - G x2‖) = (2 : ENNReal) * ENNReal.ofReal ‖G x1 - G x2‖ := by
        rw [ENNReal.ofReal_mul] <;> norm_cast
      rw [h8] at h7
      exact h7
    exact h_edist
  have h_cont_H : ContinuousOn H (G '' S) := h_lip_H.continuousOn
  have hH_ae : AEMeasurable H (μH[2].restrict (G '' S)) :=
    h_cont_H.aemeasurable hG_image_meas
  have h_image : H '' (G '' S) = graphMap f '' S := by
    ext z
    simp only [Set.mem_image, hH_def]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      have h_inv : Function.invFunOn G V (G x) = x := by
        apply h_inj_V (Function.invFunOn_apply_mem (hS hx)) (hS hx)
        exact Function.invFunOn_apply_eq (hS hx)
      exact ⟨x, hx, by rw [h_inv]⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨G x, ⟨x, hx, rfl⟩, ?_⟩
      have h_inv : Function.invFunOn G V (G x) = x := by
        apply h_inj_V (Function.invFunOn_apply_mem (hS hx)) (hS hx)
        exact Function.invFunOn_apply_eq (hS hx)
      rw [h_inv]
  have h_fderiv_within : ∀ x ∈ S, HasFDerivWithinAt G (fderiv_graphG' f x) S x := by
    intro x hx
    exact (hasFDerivAt_graphG' (hf.differentiableAt (hU.mem_nhds (hV_sub (hS hx))))).hasFDerivWithinAt
  have h_det_eq : ∀ x ∈ S, (fderiv_graphG' f x).det = fderiv ℝ f x e12 := by
    intro x _
    exact det_fderiv_graphG' f x
  have h_phi_G : ∀ x ∈ S, φ (G x) = graphAreaW p (graphMap f x) := by
    intro x hx
    have h_inv : Function.invFunOn G V (G x) = x := by
      apply h_inj_V (Function.invFunOn_apply_mem (hS hx)) (hS hx)
      exact Function.invFunOn_apply_eq (hS hx)
    simp [φ, H, h_inv]
  have h_step1 : ∫⁻ z in graphMap f '' S, graphAreaW p z ∂μH[2] ≤
      (4 : ENNReal) * ∫⁻ y in G '' S, φ y ∂μH[2] := by
    rw [←h_image]
    have h := weighted_lipschitz_integral h_lip_H hG_image_meas hH_ae (graphAreaW p)
    have h' : ∫⁻ y in H '' (G '' S), graphAreaW p y ∂μH[2] ≤ (4 : ENNReal) * ∫⁻ x in G '' S, graphAreaW p (H x) ∂μH[2] := by
      convert h using 1 <;> norm_num
    simpa [φ] using h'
  letI haarI : (μH[2] : Measure R2).IsAddHaarMeasure := by
    have h : (μH[2] : Measure R2) = μH[(2 : ℕ)] := by rfl
    rw [h] <;> infer_instance
  have h_area : ∫⁻ y in G '' S, φ y ∂μH[2] =
      ∫⁻ x in S, ENNReal.ofReal |(fderiv_graphG' f x).det| * φ (G x) ∂μH[2] :=
    MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
      (μH[2]) hS_meas h_fderiv_within h_inj_S φ
  have h_pointwise : ∀ x ∈ S,
      ENNReal.ofReal |(fderiv_graphG' f x).det| * φ (G x) ≤ 1 := by
    intro x hx
    rw [h_det_eq x hx, h_phi_G x hx]
    have h_bound : graphAreaW p (graphMap f x) * ENNReal.ofReal |fderiv ℝ f x e12| ≤ 1 :=
      graph_weight_bound' hU hf h_zero h_reg (hV_sub (hS hx))
    have h_comm : ENNReal.ofReal |fderiv ℝ f x e12| * graphAreaW p (graphMap f x) =
        graphAreaW p (graphMap f x) * ENNReal.ofReal |fderiv ℝ f x e12| := mul_comm _ _
    rw [h_comm]
    exact h_bound
  have h_ae : ∀ᵐ x ∂μH[2].restrict S, ENNReal.ofReal |(fderiv_graphG' f x).det| * φ (G x) ≤ 1 := by
    filter_upwards [self_mem_ae_restrict hS_meas] with x hx
    exact h_pointwise x hx
  have h_mono : ∫⁻ x in S, ENNReal.ofReal |(fderiv_graphG' f x).det| * φ (G x) ∂μH[2] ≤ μH[2] S := by
    have h : ∫⁻ x in S, ENNReal.ofReal |(fderiv_graphG' f x).det| * φ (G x) ∂μH[2] ≤
        ∫⁻ x in S, (1 : ENNReal) ∂μH[2] := lintegral_mono_ae h_ae
    have h2 : ∫⁻ x in S, (1 : ENNReal) ∂μH[2] = μH[2] S := by simp
    rw [h2] at h
    exact h
  have h_vol : μH[2] S = planeConstant * volume S := μH2_eq S
  calc
    ∫⁻ x in graphMap f '' S, graphAreaW p x ∂μH[2]
      ≤ 4 * ∫⁻ y in G '' S, φ y ∂μH[2] := h_step1
    _ = 4 * ∫⁻ x in S, ENNReal.ofReal |(fderiv_graphG' f x).det| * φ (G x) ∂μH[2] := by rw [h_area]
    _ ≤ 4 * μH[2] S := by gcongr
    _ = 4 * planeConstant * volume S := by rw [h_vol] <;> ring

lemma flat_region_bound {U : Set R2} {f : R2 → ℝ} {p : MvPolynomial (Fin 3) ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    (V : Set R2) (hV : Convex ℝ V) (hV_sub : V ⊆ U)
    (hfx : ∀ y ∈ V, (fderiv ℝ f y e02)^2 ≤ 1)
    (hfy : ∀ y ∈ V, (fderiv ℝ f y e12)^2 ≤ 1)
    (T : Set R2) (hT : T ⊆ V) (hT_meas : MeasurableSet T) :
    ∫⁻ x in graphMap f '' T, graphAreaW p x ∂μH[2] ≤ 3 * planeConstant * volume T := by
  have h_lip_V : LipschitzOnWith (⟨Real.sqrt 3, Real.sqrt_nonneg 3⟩ : NNReal) (graphMap f) V :=
    graphMap_flat_lipschitz hU hf hV hV_sub hfx hfy
  have h_lip_T : LipschitzOnWith (⟨Real.sqrt 3, Real.sqrt_nonneg 3⟩ : NNReal) (graphMap f) T :=
    h_lip_V.mono hT
  have h_cont_on : ContinuousOn (graphMap f) T := by
    have h1 : ContinuousOn f U := hf.continuousOn
    have h_proj0 : Continuous (fun x : R2 => x 0) := by fun_prop
    have h_proj1 : Continuous (fun x : R2 => x 1) := by fun_prop
    have h_vec : ContinuousOn (fun x : R2 => ![x 0, x 1, f x]) U := by
      rw [continuousOn_pi]
      intro i
      fin_cases i
      · simpa using h_proj0.continuousOn
      · simpa using h_proj1.continuousOn
      · simpa using h1
    have h_equiv : Continuous (EuclideanSpace.equiv (Fin 3) ℝ).symm := by fun_prop
    have h2 : ContinuousOn (graphMap f) U := h_equiv.comp_continuousOn h_vec
    exact h2.mono (subset_trans hT hV_sub)
  have h_meas_on : AEMeasurable (graphMap f) (μH[2].restrict T) :=
    h_cont_on.aemeasurable hT_meas
  have h_w_le : ∀ (y : R3), graphAreaW p y ≤ 1 := by
    intro y
    have h1 : ‖inner ℝ e3 (polynomialUnitNormal p y)‖ ≤ 1 := by
      have h_cs : |inner ℝ e3 (polynomialUnitNormal p y)| ≤ ‖e3‖ * ‖polynomialUnitNormal p y‖ :=
        abs_real_inner_le_norm e3 (polynomialUnitNormal p y)
      have h_norm_abs : ‖inner ℝ e3 (polynomialUnitNormal p y)‖ = |inner ℝ e3 (polynomialUnitNormal p y)| := by
        rw [Real.norm_eq_abs]
      rw [h_norm_abs] at *
      have h_e3 : ‖e3‖ = 1 := by
        simp [e3, EuclideanSpace.norm_eq] <;> norm_num
      have h_pun : ‖polynomialUnitNormal p y‖ ≤ 1 := by
        rw [polynomialUnitNormal]
        split_ifs <;> simp [norm_smul] <;> bound
      rw [h_e3] at h_cs
      linarith
    have h2 : graphAreaW p y = ENNReal.ofReal ‖inner ℝ e3 (polynomialUnitNormal p y)‖ := by rfl
    rw [h2]
    exact ENNReal.ofReal_le_one.mpr h1
  let L : NNReal := ⟨Real.sqrt 3, Real.sqrt_nonneg 3⟩
  have h_main := weighted_lipschitz_integral h_lip_T hT_meas h_meas_on (graphAreaW p)
  have hL2 : L ^ 2 = (3 : NNReal) := by
    apply NNReal.coe_injective
    have h1 : ((L ^ 2 : NNReal) : ℝ) = (L : ℝ) ^ 2 := by
      exact NNReal.coe_pow L 2
    rw [h1]
    have h2 : (L : ℝ) = Real.sqrt 3 := by
      simp [L] <;> rfl
    rw [h2]
    have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [h3] <;> norm_num
  have hL_sq : (L : ENNReal)^2 = 3 := by
    have h : (L : ENNReal)^2 = ↑(L ^ 2) := by simp
    rw [h, hL2] <;> norm_num
  rw [hL_sq] at h_main
  have h4 : ∫⁻ x in T, graphAreaW p (graphMap f x) ∂μH[2] ≤ ∫⁻ x in T, (1 : ENNReal) ∂μH[2] :=
    lintegral_mono (fun x => h_w_le (graphMap f x))
  have h5 : ∫⁻ x in T, (1 : ENNReal) ∂μH[2] = μH[2] T := by simp
  have h6 : μH[2] T = planeConstant * volume T := μH2_eq T
  calc ∫⁻ x in graphMap f '' T, graphAreaW p x ∂μH[2]
    ≤ 3 * ∫⁻ x in T, graphAreaW p (graphMap f x) ∂μH[2] := h_main
  _ ≤ 3 * ∫⁻ x in T, (1 : ENNReal) ∂μH[2] := by gcongr
  _ = 3 * μH[2] T := by rw [h5] <;> ring
  _ = 3 * planeConstant * volume T := by rw [h6] <;> ring

lemma flat_region_bound_gen {U : Set R2} {f : R2 → ℝ} {p : MvPolynomial (Fin 3) ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    (V : Set R2) (hV : Convex ℝ V) (hV_sub : V ⊆ U)
    (Cx Cy : ℝ) (hCx_nonneg : 0 ≤ Cx) (hCy_nonneg : 0 ≤ Cy)
    (hfx : ∀ y ∈ V, (fderiv ℝ f y e02)^2 ≤ Cx)
    (hfy : ∀ y ∈ V, (fderiv ℝ f y e12)^2 ≤ Cy)
    (T : Set R2) (hT : T ⊆ V) (hT_meas : MeasurableSet T) :
    ∫⁻ x in graphMap f '' T, graphAreaW p x ∂μH[2] ≤
        (ENNReal.ofReal (1 + Cx + Cy)) * planeConstant * volume T := by
  let L : NNReal := ⟨Real.sqrt (1 + Cx + Cy), Real.sqrt_nonneg _⟩
  have h_lip_V : LipschitzOnWith L (graphMap f) V :=
    graphMap_gen_lipschitz hU hf hV hV_sub Cx Cy hCx_nonneg hCy_nonneg hfx hfy
  have h_lip_T : LipschitzOnWith L (graphMap f) T := h_lip_V.mono hT
  have h_cont_on : ContinuousOn (graphMap f) T := by
    have h1 : ContinuousOn f U := hf.continuousOn
    have h_proj0 : Continuous (fun x : R2 => x 0) := by fun_prop
    have h_proj1 : Continuous (fun x : R2 => x 1) := by fun_prop
    have h_vec : ContinuousOn (fun x : R2 => ![x 0, x 1, f x]) U := by
      rw [continuousOn_pi]
      intro i
      fin_cases i
      · simpa using h_proj0.continuousOn
      · simpa using h_proj1.continuousOn
      · simpa using h1
    have h_equiv : Continuous (EuclideanSpace.equiv (Fin 3) ℝ).symm := by fun_prop
    have h2 : ContinuousOn (graphMap f) U := h_equiv.comp_continuousOn h_vec
    exact h2.mono (subset_trans hT hV_sub)
  have h_meas_on : AEMeasurable (graphMap f) (μH[2].restrict T) :=
    h_cont_on.aemeasurable hT_meas
  have h_w_le : ∀ (y : R3), graphAreaW p y ≤ 1 := by
    intro y
    have h1 : ‖inner ℝ e3 (polynomialUnitNormal p y)‖ ≤ 1 := by
      have h_cs : |inner ℝ e3 (polynomialUnitNormal p y)| ≤ ‖e3‖ * ‖polynomialUnitNormal p y‖ :=
        abs_real_inner_le_norm e3 (polynomialUnitNormal p y)
      have h_norm_abs : ‖inner ℝ e3 (polynomialUnitNormal p y)‖ = |inner ℝ e3 (polynomialUnitNormal p y)| := by
        rw [Real.norm_eq_abs]
      rw [h_norm_abs] at *
      have h_e3 : ‖e3‖ = 1 := by
        simp [e3, EuclideanSpace.norm_eq] <;> norm_num
      have h_pun : ‖polynomialUnitNormal p y‖ ≤ 1 := by
        rw [polynomialUnitNormal]
        split_ifs <;> simp [norm_smul] <;> bound
      rw [h_e3] at h_cs
      linarith
    have h2 : graphAreaW p y = ENNReal.ofReal ‖inner ℝ e3 (polynomialUnitNormal p y)‖ := by rfl
    rw [h2]
    exact ENNReal.ofReal_le_one.mpr h1
  have h_pos : 0 ≤ 1 + Cx + Cy := by linarith
  have h_main := weighted_lipschitz_integral h_lip_T hT_meas h_meas_on (graphAreaW p)
  have hL2 : (L : ENNReal)^2 = ENNReal.ofReal (1 + Cx + Cy) := by
    have h1 : (L : ENNReal)^2 = (L : ENNReal) * (L : ENNReal) := by ring
    rw [h1]
    have h2 : (L : ENNReal) * (L : ENNReal) = ↑(L * L) := by
      exact Eq.symm (ENNReal.coe_mul L L)
    rw [h2]
    have h3 : ((L * L : NNReal) : ℝ) = 1 + Cx + Cy := by
      have h31 : ((L * L : NNReal) : ℝ) = (L : ℝ) * (L : ℝ) := by
        exact NNReal.coe_mul L L
      rw [h31]
      have h32 : (L : ℝ) = Real.sqrt (1 + Cx + Cy) := by simp [L] <;> rfl
      rw [h32]
      have h33 : Real.sqrt (1 + Cx + Cy) * Real.sqrt (1 + Cx + Cy) = 1 + Cx + Cy := by
        have h_sq : Real.sqrt (1 + Cx + Cy) * Real.sqrt (1 + Cx + Cy) = (Real.sqrt (1 + Cx + Cy)) ^ 2 := by ring
        rw [h_sq]
        exact Real.sq_sqrt h_pos
      exact h33
    have h4 : (↑(L * L) : ENNReal) = ENNReal.ofReal ((L * L : NNReal) : ℝ) :=
      ENNReal.coe_nnreal_eq (L * L)
    rw [h4, h3]
  rw [hL2] at h_main
  have h4 : ∫⁻ x in T, graphAreaW p (graphMap f x) ∂μH[2] ≤ ∫⁻ x in T, (1 : ENNReal) ∂μH[2] :=
    lintegral_mono (fun x => h_w_le (graphMap f x))
  have h5 : ∫⁻ x in T, (1 : ENNReal) ∂μH[2] = μH[2] T := by simp
  have h6 : μH[2] T = planeConstant * volume T := μH2_eq T
  calc ∫⁻ x in graphMap f '' T, graphAreaW p x ∂μH[2]
    ≤ ENNReal.ofReal (1 + Cx + Cy) * ∫⁻ x in T, graphAreaW p (graphMap f x) ∂μH[2] := h_main
  _ ≤ ENNReal.ofReal (1 + Cx + Cy) * ∫⁻ x in T, (1 : ENNReal) ∂μH[2] := by gcongr
  _ = ENNReal.ofReal (1 + Cx + Cy) * μH[2] T := by rw [h5] <;> ring
  _ = ENNReal.ofReal (1 + Cx + Cy) * planeConstant * volume T := by rw [h6] <;> ring

-- ============================================================================
-- Countable convex cover
-- ============================================================================

lemma open_eq_iUnion_balls (U : Set R2) (hU : IsOpen U) :
    ∃ (Q : ℕ → Set R2), (∀ i, IsOpen (Q i) ∧ Convex ℝ (Q i)) ∧
      (∀ i, Q i ⊆ U) ∧ U = ⋃ i, Q i := by
  by_cases hU_empty : U = ∅
  · refine' ⟨fun _ => ∅, _, _, _⟩
    · intro i; exact ⟨isOpen_empty, convex_empty⟩
    · intro i; exact empty_subset _
    · rw [hU_empty]; simp
  · let B : Set (Set R2) := {b | ∃ (x : R2) (r : ℝ), 0 < r ∧ b = Metric.ball x r}
    have h_open : ∀ (b : Set R2), b ∈ B → IsOpen b := by
      intro b hb
      rcases hb with ⟨x, r, hr, rfl⟩
      exact Metric.isOpen_ball
    have h_nhds : ∀ (a : R2) (u : Set R2), a ∈ u → IsOpen u → ∃ v ∈ B, a ∈ v ∧ v ⊆ u := by
      intro a u ha hu
      rcases Metric.isOpen_iff.mp hu a ha with ⟨r, hr, hball⟩
      have h_ball_in_B : Metric.ball a r ∈ B := by
        exact ⟨a, r, hr, rfl⟩
      exact ⟨Metric.ball a r, h_ball_in_B, Metric.mem_ball_self hr, hball⟩
    have hB_basis : TopologicalSpace.IsTopologicalBasis B :=
      TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds h_open h_nhds
    have h_main : ∃ (s : Set (Set R2)), s ⊆ B ∧ s.Countable ∧ U = ⋃ a ∈ s, a :=
      hB_basis.exists_countable_biUnion_of_isOpen hU
    rcases h_main with ⟨s, hs_sub, hs_count, hU_eq⟩
    have h_s_nonempty : s.Nonempty := by
      have hU_ne : U.Nonempty := Set.nonempty_iff_ne_empty.mpr hU_empty
      rw [hU_eq] at hU_ne
      rcases hU_ne with ⟨x, hx⟩
      simp only [Set.mem_iUnion] at hx
      rcases hx with ⟨a, ha, _⟩
      exact ⟨a, ha⟩
    have h_range : ∃ (g : ℕ → Set R2), s = Set.range g := hs_count.exists_eq_range h_s_nonempty
    rcases h_range with ⟨g, hg⟩
    refine' ⟨g, _, _, _⟩
    · intro i
      have h_i : g i ∈ s := by
        simpa [hg] using Set.mem_range_self i
      have h_gi : g i ∈ B := hs_sub h_i
      have h_gi' : ∃ (x : R2) (r : ℝ), 0 < r ∧ g i = Metric.ball x r := by
        simpa [B] using h_gi
      rcases h_gi' with ⟨x, r, hr, h_eq⟩
      rw [h_eq]
      exact ⟨Metric.isOpen_ball, convex_ball _ _⟩
    · intro i
      have h_i : g i ∈ s := by
        simpa [hg] using Set.mem_range_self i
      have h_gi_sub : g i ⊆ U := by
        have h : g i ⊆ (⋃ a ∈ s, a) := by
          intro x hx
          exact Set.mem_iUnion₂.mpr ⟨g i, h_i, hx⟩
        have h' : (⋃ a ∈ s, a) = U := hU_eq.symm
        rw [h'] at h
        exact h
      exact h_gi_sub
    · rw [hU_eq, hg] <;> simp

lemma apply_cover_bound {W : Set R2} {f : R2 → ℝ} (hW : IsOpen W)
    (w : R3 → ENNReal)
    (S : Set R2) (hS : S ⊆ W) (hS_meas : MeasurableSet S)
    (C : ENNReal)
    (h_bound : ∀ (V : Set R2), Convex ℝ V → V ⊆ W → ∀ (T : Set R2), T ⊆ V → MeasurableSet T →
      ∫⁻ x in graphMap f '' T, w x ∂μH[2] ≤ C * planeConstant * volume T) :
    ∫⁻ x in graphMap f '' S, w x ∂μH[2] ≤ C * planeConstant * volume S := by
  rcases open_eq_iUnion_balls W hW with ⟨Q, hQ_open_conv, hQ_sub, hW_eq⟩
  let D : ℕ → Set R2 := fun i => disjointed Q i
  have hD_disj : Set.PairwiseDisjoint (Set.univ : Set ℕ) D := by
    have h : ∀ (i j : ℕ), i ≠ j → Disjoint (D i) (D j) := by
      intro i j hne
      exact disjoint_disjointed Q hne
    intro i _ j _ hne
    exact h i j hne
  have hD_sub : ∀ i, D i ⊆ Q i := by
    intro i
    have h_def : D i = disjointed Q i := rfl
    rw [h_def, disjointed_apply]
    intro x hx
    exact hx.1
  have hD_iUnion : (⋃ i, D i) = W := by
    have h : (⋃ i, disjointed Q i) = (⋃ i, Q i) := iUnion_disjointed
    rw [h, hW_eq]
  have hD_meas : ∀ i, MeasurableSet (D i) := by
    intro i
    have h_def : D i = disjointed Q i := rfl
    rw [h_def, disjointed_apply]
    have hQ_meas : ∀ j, MeasurableSet (Q j) := fun j => (hQ_open_conv j).1.measurableSet
    have h_union_meas : MeasurableSet ((Finset.Iio i).sup Q) := by
      have h : ∀ (s : Finset ℕ), MeasurableSet (s.sup Q) := by
        intro s
        induction s using Finset.induction with
        | empty => simp
        | @insert a s ha ih =>
          rw [Finset.sup_insert (s := s) (f := Q) (b := a)]
          exact (hQ_meas a).union ih
      exact h (Finset.Iio i)
    exact (hQ_meas i).diff h_union_meas
  let T : ℕ → Set R2 := fun i => S ∩ D i
  have hT_meas : ∀ i, MeasurableSet (T i) := fun i =>
    hS_meas.inter (hD_meas i)
  have hT_sub_Q : ∀ i, T i ⊆ Q i := fun i =>
    have h1 : T i ⊆ D i := by
      intro x hx
      exact hx.2
    subset_trans h1 (hD_sub i)
  have hT_iUnion : (⋃ i, T i) = S := by
    have h_eq1 : (⋃ i, T i) = S ∩ (⋃ i, D i) := by
      ext x
      simp [T, Set.mem_iUnion]
      <;> tauto
    rw [h_eq1]
    rw [hD_iUnion]
    rw [Set.inter_eq_left.mpr hS]
  have h_each : ∀ i, ∫⁻ x in graphMap f '' (T i), w x ∂μH[2] ≤ C * planeConstant * volume (T i) := by
    intro i
    have hQi_conv : Convex ℝ (Q i) := (hQ_open_conv i).2
    have hQi_subW : Q i ⊆ W := hQ_sub i
    exact h_bound (Q i) hQi_conv hQi_subW (T i) (hT_sub_Q i) (hT_meas i)
  have h_image_iUnion : graphMap f '' S = ⋃ i, graphMap f '' (T i) := by
    rw [←hT_iUnion]
    rw [Set.image_iUnion]
  rw [h_image_iUnion]
  have h_subadd : ∫⁻ x in (⋃ i, graphMap f '' (T i)), w x ∂μH[2] ≤
      ∑' i, ∫⁻ x in graphMap f '' (T i), w x ∂μH[2] :=
    lintegral_iUnion_le _ _
  have h_sum : ∑' i, ∫⁻ x in graphMap f '' (T i), w x ∂μH[2] ≤
      ∑' i, (C * planeConstant * volume (T i)) := by
    apply ENNReal.tsum_le_tsum h_each
  have h_sum2 : ∑' i, (C * planeConstant * volume (T i)) =
      C * planeConstant * ∑' i, volume (T i) := by
    rw [ENNReal.tsum_mul_left]
    <;> ring
  have h_vol : ∑' i, volume (T i) = volume S := by
    have h_disj : Set.PairwiseDisjoint (Set.univ : Set ℕ) T := by
      intro i _ j _ hne
      have h : Disjoint (D i) (D j) := hD_disj (by simp) (by simp) hne
      have hTi : T i ⊆ D i := by intro x hx; exact hx.2
      have hTj : T j ⊆ D j := by intro x hx; exact hx.2
      exact h.mono hTi hTj
    have h_eq : ∑' i, volume (T i) = volume (⋃ i, T i) := by
      exact Eq.symm (measure_iUnion (fun ⦃i j⦄ => h_disj trivial trivial) hT_meas)
    rw [h_eq, hT_iUnion]
  calc ∫⁻ x in (⋃ i, graphMap f '' (T i)), w x ∂μH[2]
    ≤ ∑' i, ∫⁻ x in graphMap f '' (T i), w x ∂μH[2] := h_subadd
  _ ≤ ∑' i, (C * planeConstant * volume (T i)) := h_sum
  _ = C * planeConstant * ∑' i, volume (T i) := h_sum2
  _ = C * planeConstant * volume S := by rw [h_vol] <;> ring

-- ============================================================================
-- Main theorem
-- ============================================================================

end Kakeya.CV
