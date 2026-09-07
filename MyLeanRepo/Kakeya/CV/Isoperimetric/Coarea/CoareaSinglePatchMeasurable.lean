import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaSinglePatch
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.Eilenberg
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.LevelSetMeasurability
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic

/-!
# Globalization of the Single-Patch Coarea Formula

Extends `coarea_single_patch` from compact subsets of a single patch
to measurable subsets.

## Main lemma

`coarea_single_patch_measurable`: equality for measurable subsets of a patch.
-/

open MeasureTheory Metric Set ENNReal
open scoped MeasureTheory

namespace Geometry

variable {m : ℕ} [Nonempty (Fin m)]

/-- Coarea formula for bounded measurable subsets of a single patch. -/
lemma coarea_single_patch_bounded
    (f : E (m + 1) → ℝ)
    (hf : ContDiff ℝ 1 f)
    (φ : OpenPartialHomeomorph (E (m + 1)) (E (m + 1)))
    (hφ_coe : (φ : E (m + 1) → E (m + 1)) =
        fun y => projHCL y + f y • (eLast : E (m + 1)))
    (hφ_symm_diff : ContDiffOn ℝ 1 φ.symm φ.target)
    {V : Set (E (m + 1))}
    (hV_source : V ⊆ φ.source)
    (hV_reg : ∀ y ∈ V, (fderiv ℝ f y) (eLast : E (m + 1)) ≠ 0)
    (B : Set (E (m + 1)))
    (hB : MeasurableSet B)
    (hB_sub : B ⊆ V)
    (hB_bdd : Bornology.IsBounded B) :
    ∫⁻ (t : ℝ), μHE[m] (B ∩ {y | f y = t}) =
    ∫⁻ (y : E (m + 1)) in B, ENNReal.ofReal ‖fderiv ℝ f y‖ := by
  by_cases h_empty : B = ∅
  · rw [h_empty]; simp
  -- Step 1: Find closed ball containing B and bound derivative
  rcases hB_bdd.subset_closedBall 0 with ⟨R0, hR0⟩
  let R : ℝ := max R0 0
  have hR_nonneg : 0 ≤ R := le_max_right _ _
  have hR : B ⊆ closedBall (0 : E (m + 1)) R := by
    have h1 : closedBall (0 : E (m + 1)) R0 ⊆ closedBall (0 : E (m + 1)) R :=
      closedBall_subset_closedBall (le_max_left _ _)
    exact hR0.trans h1
  let ball : Set (E (m + 1)) := closedBall 0 R
  have hball_conv : Convex ℝ ball := convex_closedBall 0 R
  have hball_compact : IsCompact ball := isCompact_closedBall 0 R
  have hB_sub_ball : B ⊆ ball := hR
  have h_diff : ∀ y ∈ ball, DifferentiableAt ℝ f y :=
    fun y _ => (hf.differentiable (by norm_num)).differentiableAt
  have h_cont_deriv : Continuous (fun y : E (m + 1) => ‖fderiv ℝ f y‖) :=
    (hf.continuous_fderiv (by norm_num)).norm
  have h_bdd1 : BddAbove ((fun y : E (m + 1) => ‖fderiv ℝ f y‖) '' ball) :=
    hball_compact.bddAbove_image h_cont_deriv.continuousOn
  rcases h_bdd1 with ⟨M, hM⟩
  have hM_bound : ∀ y ∈ ball, ‖fderiv ℝ f y‖ ≤ M := by
    intro y hy
    have h5 : ‖fderiv ℝ f y‖ ∈ (fun y : E (m + 1) => ‖fderiv ℝ f y‖) '' ball :=
      ⟨y, hy, rfl⟩
    exact hM h5
  have h0_in_ball : (0 : E (m + 1)) ∈ ball := by
    simp [ball, Metric.mem_closedBall, dist_zero_right, hR_nonneg]
  have hM_nonneg : 0 ≤ M := by
    have h2 : 0 ≤ ‖fderiv ℝ f (0 : E (m + 1))‖ := by positivity
    have h3 : ‖fderiv ℝ f (0 : E (m + 1))‖ ≤ M := hM_bound 0 h0_in_ball
    linarith
  let M_nn : NNReal := ⟨M, hM_nonneg⟩
  have hM_nn_bound : ∀ y ∈ ball, ‖fderiv ℝ f y‖₊ ≤ M_nn := by
    intro y hy
    have h : ‖fderiv ℝ f y‖ ≤ M := hM_bound y hy
    have h' : (‖fderiv ℝ f y‖₊ : ℝ) ≤ (M_nn : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have h_lip_ball : LipschitzOnWith M_nn f ball :=
    hball_conv.lipschitzOnWith_of_nnnorm_fderiv_le h_diff hM_nn_bound
  have h_lip_B : LipschitzOnWith M_nn f B := h_lip_ball.mono hB_sub_ball
  -- M_nn ≠ 0 since B nonempty and ∂_last f ≠ 0 on V
  have hM_nn_ne_zero : M_nn ≠ 0 := by
    rcases Set.nonempty_iff_ne_empty.mpr h_empty with ⟨y, hy⟩
    have h2 : 0 < ‖fderiv ℝ f y‖ := by
      have h3 : (fderiv ℝ f y) (eLast : E (m + 1)) ≠ 0 := hV_reg y (hB_sub hy)
      have h4 : fderiv ℝ f y ≠ 0 := by
        intro h5; exact h3 (congr_arg (fun (h : E (m + 1) →L[ℝ] ℝ) => h (eLast)) h5)
      exact norm_pos_iff.mpr h4
    have h4 : y ∈ ball := hB_sub_ball hy
    have h5 : ‖fderiv ℝ f y‖ ≤ M := hM_bound y h4
    have h6 : 0 < M := lt_of_lt_of_le h2 h5
    have h7 : (M_nn : ℝ) ≠ 0 := h6.ne'
    exact_mod_cast h7
  -- Step 2: McShane extension
  rcases h_lip_B.extend_real with ⟨g, hg_lip, hg_eq⟩
  -- Step 3: Eilenberg inequality for g
  have h_m_pos : 0 < m := by
    exact Fin.pos'
  have h_n : 2 ≤ m + 1 := by
    have h : m ≥ 1 := by exact Nat.succ_le_iff.mp h_m_pos
    linarith
  rcases eilenberg_μHE h_n hg_lip hM_nn_ne_zero with ⟨C_eil, hC_eil_ne_top, _, h_eil⟩
  have h_level_eq : ∀ (A : Set (E (m + 1))), A ⊆ B →
      ∀ (s : ℝ), A ∩ {y | g y = s} = A ∩ {y | f y = s} := by
    intro A hA_sub s
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hxA, hgs⟩
      have hfx : f x = g x := hg_eq (hA_sub hxA)
      have h_goal : f x = s := by
        calc f x = g x := hfx
             _ = s := hgs
      exact ⟨hxA, h_goal⟩
    · rintro ⟨hxA, hfs⟩
      have hgx : g x = f x := (hg_eq (hA_sub hxA)).symm
      have h_goal : g x = s := by
        calc g x = f x := hgx
             _ = s := hfs
      exact ⟨hxA, h_goal⟩
  have h_eil_B : ∀ (A : Set (E (m + 1))), A ⊆ B →
      ∫⁻ (s : ℝ), μHE[m] (A ∩ {y | f y = s}) ≤ C_eil * volume A := by
    intro A hA_sub
    have h1 : ∫⁻ (s : ℝ), μHE[m] (A ∩ {y | g y = s}) ≤ C_eil * volume A := h_eil A
    have h2 : (fun s : ℝ => μHE[m] (A ∩ {y | g y = s})) =
        (fun s : ℝ => μHE[m] (A ∩ {y | f y = s})) := by
      funext s; rw [h_level_eq A hA_sub s]
    rw [h2] at h1; exact h1
  -- Define density and μ₂ as a measure for subadditivity
  let hden : E (m + 1) → ENNReal := fun y => ENNReal.ofReal ‖fderiv ℝ f y‖
  let ν : Measure (E (m + 1)) := volume.withDensity hden
  have hμ2_eq : ∀ (A : Set (E (m + 1))), MeasurableSet A →
      (∫⁻ (y : E (m + 1)) in A, hden y) = ν A := by
    intro A hA
    have h : ν A = ∫⁻ (y : E (m + 1)) in A, hden y :=
      MeasureTheory.withDensity_apply₀ hden (hA.nullMeasurableSet)
    exact h.symm
  -- Density bound
  have h_density_bound : ∀ y ∈ B, hden y ≤ (M_nn : ENNReal) := by
    intro y hy
    have h1 : y ∈ ball := hB_sub_ball hy
    have h2 : ‖fderiv ℝ f y‖ ≤ M := hM_bound y h1
    have h3 : hden y ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal h2
    have h4 : ENNReal.ofReal M = (M_nn : ENNReal) := by
      have h5 : (M_nn : ENNReal) = ENNReal.ofReal (M_nn : ℝ) := by
        exact coe_nnreal_eq M_nn
      have h6 : (M_nn : ℝ) = M := by rfl
      rw [h5, h6]
    rw [h4] at h3; exact h3
  have h_volume_B_lt_top : volume B ≠ ⊤ := hB_bdd.measure_lt_top.ne
  let μ₁ : Set (E (m + 1)) → ENNReal := fun A =>
    ∫⁻ (t : ℝ), μHE[m] (A ∩ {y | f y = t})
  let μ₂ : Set (E (m + 1)) → ENNReal := fun A =>
    ∫⁻ (y : E (m + 1)) in A, hden y
  -- Both sides finite
  have hμ1_B_lt_top : μ₁ B ≠ ⊤ := by
    have h : μ₁ B ≤ C_eil * volume B := h_eil_B B Subset.rfl
    have h' : C_eil * volume B ≠ ⊤ := ENNReal.mul_ne_top hC_eil_ne_top h_volume_B_lt_top
    exact ne_top_of_le_ne_top h' h
  have hμ2_B_lt_top : μ₂ B ≠ ⊤ := by
    have h : μ₂ B ≤ (M_nn : ENNReal) * volume B := by
      calc
        μ₂ B ≤ ∫⁻ y in B, (M_nn : ENNReal) :=
          setLIntegral_mono' hB h_density_bound
        _ = (M_nn : ENNReal) * volume B := by
          simpa [setLIntegral_one] using by ring
    have h' : (M_nn : ENNReal) * volume B ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top h_volume_B_lt_top
    exact ne_top_of_le_ne_top h' h
  -- Main inequality for arbitrary ε > 0
  have h_main_ineq : ∀ (ε : ENNReal), ε ≠ 0 → ε ≠ ⊤ →
      (μ₁ B ≤ μ₂ B + C_eil * ε) ∧ (μ₂ B ≤ μ₁ B + (M_nn : ENNReal) * ε) := by
    intro ε hε hε_top
    rcases hB.exists_isCompact_sdiff_lt h_volume_B_lt_top (hε := hε) with ⟨K, hK_sub, hK_compact, hK_vol⟩
    have hK_sub_V : K ⊆ V := hK_sub.trans hB_sub
    have hK_meas : MeasurableSet K := hK_compact.measurableSet
    have h_eq_K : μ₁ K = μ₂ K :=
      coarea_single_patch f hf φ hφ_coe hφ_symm_diff hV_source hV_reg K hK_meas hK_compact hK_sub_V
    -- Measurability of compact level-set function
    have h_meas_K : Measurable (fun t : ℝ => μHE[m] (K ∩ {y | f y = t})) :=
      levelSetMeasure_compact_measurable h_n hK_compact hf.continuous
    have hBK_meas : MeasurableSet (B \ K) := hB.diff hK_meas
    have hBK_sub : B \ K ⊆ B := by
      intro x hx; exact hx.1
    -- Subadditivity of μ₁ using measurability of K component
    have h_sub1 : μ₁ B ≤ μ₁ K + μ₁ (B \ K) := by
      have h : ∀ t, μHE[m] (B ∩ {y | f y = t}) ≤
          μHE[m] (K ∩ {y | f y = t}) + μHE[m] ((B \ K) ∩ {y | f y = t}) := by
        intro t
        have h5 : B ∩ {y | f y = t} ⊆
            (K ∩ {y | f y = t}) ∪ ((B \ K) ∩ {y | f y = t}) := by
          intro x hx
          have h6 : x ∈ B := hx.1
          by_cases h7 : x ∈ K
          · exact Or.inl ⟨h7, hx.2⟩
          · exact Or.inr ⟨⟨h6, h7⟩, hx.2⟩
        exact (measure_mono h5).trans (measure_union_le _ _)
      calc
        μ₁ B ≤ ∫⁻ t, (μHE[m] (K ∩ {y | f y = t}) + μHE[m] ((B \ K) ∩ {y | f y = t})) :=
          lintegral_mono h
        _ = μ₁ K + μ₁ (B \ K) := by
          rw [lintegral_add_left h_meas_K] <;> rfl
    -- μ₂ subadditivity via ν measure
    have h_sub2 : μ₂ B ≤ μ₂ K + μ₂ (B \ K) := by
      have h_union : K ∪ (B \ K) = B := by ext x; simp [hK_sub] <;> tauto
      have h : ν B ≤ ν K + ν (B \ K) := by
        have h' : ν (K ∪ (B \ K)) ≤ ν K + ν (B \ K) := measure_union_le _ _
        rw [h_union] at h'; exact h'
      have h5 : μ₂ B = ν B := hμ2_eq B hB
      have h6 : μ₂ K = ν K := hμ2_eq K hK_meas
      have h7 : μ₂ (B \ K) = ν (B \ K) := hμ2_eq (B \ K) hBK_meas
      rw [h5, h6, h7]
      exact h
    -- Bounds
    have h1 : μ₁ (B \ K) ≤ C_eil * volume (B \ K) := h_eil_B (B \ K) hBK_sub
    have h_vol_le : volume (B \ K) ≤ ε := le_of_lt hK_vol
    have h2 : μ₁ (B \ K) ≤ C_eil * ε := by
      calc μ₁ (B \ K) ≤ C_eil * volume (B \ K) := h1
           _ ≤ C_eil * ε := by
             exact mul_le_mul_left' h_vol_le _
    have h3 : μ₂ (B \ K) ≤ (M_nn : ENNReal) * volume (B \ K) := by
      calc
        μ₂ (B \ K) ≤ ∫⁻ y in (B \ K), (M_nn : ENNReal) :=
          setLIntegral_mono' hBK_meas (fun y hy => h_density_bound y (hBK_sub hy))
        _ = (M_nn : ENNReal) * volume (B \ K) := by
          simpa [setLIntegral_one] using by ring
    have h4 : μ₂ (B \ K) ≤ (M_nn : ENNReal) * ε := by
      calc μ₂ (B \ K) ≤ (M_nn : ENNReal) * volume (B \ K) := h3
           _ ≤ (M_nn : ENNReal) * ε := by
             exact mul_le_mul_left' h_vol_le _
    have h51 : μ₂ K ≤ μ₂ B := by
      have h511 : ν K ≤ ν B := measure_mono hK_sub
      have h512 : μ₂ K = ν K := hμ2_eq K hK_meas
      have h513 : μ₂ B = ν B := hμ2_eq B hB
      rw [h512, h513]; exact h511
    have h52 : μ₁ K ≤ μ₁ B := by
      have h6 : ∀ t, μHE[m] (K ∩ {y | f y = t}) ≤ μHE[m] (B ∩ {y | f y = t}) := by
        intro t; exact measure_mono (inter_subset_inter_left _ hK_sub)
      exact lintegral_mono h6
    have h_ineq1 : μ₁ B ≤ μ₂ B + C_eil * ε := by
      calc μ₁ B ≤ μ₁ K + μ₁ (B \ K) := h_sub1
           _ = μ₂ K + μ₁ (B \ K) := by rw [h_eq_K]
           _ ≤ μ₂ K + C_eil * ε := by
             exact add_le_add (le_refl (μ₂ K)) h2
           _ ≤ μ₂ B + C_eil * ε := by
             exact add_le_add h51 (le_refl (C_eil * ε))
    have h_ineq2 : μ₂ B ≤ μ₁ B + (M_nn : ENNReal) * ε := by
      calc μ₂ B ≤ μ₂ K + μ₂ (B \ K) := h_sub2
           _ = μ₁ K + μ₂ (B \ K) := by rw [h_eq_K]
           _ ≤ μ₁ K + (M_nn : ENNReal) * ε := by
             exact add_le_add (le_refl (μ₁ K)) h4
           _ ≤ μ₁ B + (M_nn : ENNReal) * ε := by
             exact add_le_add h52 (le_refl ((M_nn : ENNReal) * ε))
    exact ⟨h_ineq1, h_ineq2⟩
  -- Let ε → 0 using real conversion
  have h_final1 : μ₁ B ≤ μ₂ B := by
    by_cases htop : μ₂ B = ⊤
    · simp [htop]
    · have h : ∀ (δ : ℝ), 0 < δ → (μ₁ B).toReal ≤ (μ₂ B).toReal + δ := by
        intro δ hδ
        set c : ℝ := C_eil.toReal with hc_def
        have hc_nonneg : 0 ≤ c := by positivity
        let ε : ENNReal := ENNReal.ofReal (δ / (c + 1))
        have hε_pos : 0 < δ / (c + 1) := by positivity
        have hε : ε ≠ 0 := by
          simp [ε, hε_pos.ne'] <;> positivity
        have hε_top : ε ≠ ⊤ := ENNReal.ofReal_ne_top
        have h9 := (h_main_ineq ε hε hε_top).1
        have h_prod_ne_top : C_eil * ε ≠ ⊤ :=
          ENNReal.mul_ne_top hC_eil_ne_top hε_top
        have h_rhs_ne_top : μ₂ B + C_eil * ε ≠ ⊤ := by
          rw [ENNReal.add_ne_top]; exact ⟨hμ2_B_lt_top, h_prod_ne_top⟩
        have h10 : (μ₁ B).toReal ≤ (μ₂ B + C_eil * ε).toReal :=
          ENNReal.toReal_mono h_rhs_ne_top h9
        have h11 : (μ₂ B + C_eil * ε).toReal = (μ₂ B).toReal + (C_eil * ε).toReal :=
          ENNReal.toReal_add hμ2_B_lt_top h_prod_ne_top
        rw [h11] at h10
        have h12 : (C_eil * ε).toReal = c * (δ / (c + 1)) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] <;> ring
        rw [h12] at h10
        have h13 : c * (δ / (c + 1)) < δ := by
          have h14 : c + 1 > 0 := by positivity
          have h15 : c * (δ / (c + 1)) = δ * (c / (c + 1)) := by ring
          rw [h15]
          have h16 : c / (c + 1) < 1 := by
            apply (div_lt_one h14).mpr
            linarith
          have h17 : δ * (c / (c + 1)) < δ * (1 : ℝ) := mul_lt_mul_of_pos_left h16 hδ
          simpa using h17
        linarith
      have h13 : (μ₁ B).toReal ≤ (μ₂ B).toReal := le_of_forall_pos_le_add h
      have h14 : μ₁ B = ENNReal.ofReal (μ₁ B).toReal := by
        rw [ENNReal.ofReal_toReal hμ1_B_lt_top]
      have h15 : μ₂ B = ENNReal.ofReal (μ₂ B).toReal := by
        rw [ENNReal.ofReal_toReal hμ2_B_lt_top]
      rw [h14, h15]
      exact ENNReal.ofReal_le_ofReal h13
  have h_final2 : μ₂ B ≤ μ₁ B := by
    by_cases htop : μ₁ B = ⊤
    · simp [htop]
    · have h : ∀ (δ : ℝ), 0 < δ → (μ₂ B).toReal ≤ (μ₁ B).toReal + δ := by
        intro δ hδ
        set c : ℝ := (M_nn : ℝ) with hc_def
        have hc_nonneg : 0 ≤ c := by positivity
        let ε : ENNReal := ENNReal.ofReal (δ / (c + 1))
        have hε_pos : 0 < δ / (c + 1) := by positivity
        have hε : ε ≠ 0 := by
          simp [ε, hε_pos.ne'] <;> positivity
        have hε_top : ε ≠ ⊤ := ENNReal.ofReal_ne_top
        have h9 := (h_main_ineq ε hε hε_top).2
        have h_prod_ne_top : (M_nn : ENNReal) * ε ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.coe_ne_top hε_top
        have h_rhs_ne_top : μ₁ B + (M_nn : ENNReal) * ε ≠ ⊤ := by
          rw [ENNReal.add_ne_top]; exact ⟨hμ1_B_lt_top, h_prod_ne_top⟩
        have h10 : (μ₂ B).toReal ≤ (μ₁ B + (M_nn : ENNReal) * ε).toReal :=
          ENNReal.toReal_mono h_rhs_ne_top h9
        have h11 : (μ₁ B + (M_nn : ENNReal) * ε).toReal =
            (μ₁ B).toReal + ((M_nn : ENNReal) * ε).toReal :=
          ENNReal.toReal_add hμ1_B_lt_top h_prod_ne_top
        rw [h11] at h10
        have h12 : ((M_nn : ENNReal) * ε).toReal = c * (δ / (c + 1)) := by
          have h121 : ((M_nn : ENNReal) * ε).toReal = (M_nn : ENNReal).toReal * ε.toReal :=
            ENNReal.toReal_mul
          rw [h121]
          have h122 : (M_nn : ENNReal).toReal = (M_nn : ℝ) := by
            exact coe_toReal M_nn
          rw [h122]
          have h123 : ε.toReal = δ / (c + 1) := by
            rw [ENNReal.toReal_ofReal (by positivity)]
            <;> rfl
          rw [h123]
          <;> ring
        rw [h12] at h10
        have h13 : c * (δ / (c + 1)) < δ := by
          have h14 : c + 1 > 0 := by positivity
          have h15 : c * (δ / (c + 1)) = δ * (c / (c + 1)) := by ring
          rw [h15]
          have h16 : c / (c + 1) < 1 := by
            apply (div_lt_one h14).mpr
            linarith
          have h17 : δ * (c / (c + 1)) < δ * (1 : ℝ) := mul_lt_mul_of_pos_left h16 hδ
          simpa using h17
        linarith
      have h13 : (μ₂ B).toReal ≤ (μ₁ B).toReal := le_of_forall_pos_le_add h
      have h14 : μ₂ B = ENNReal.ofReal (μ₂ B).toReal := by
        rw [ENNReal.ofReal_toReal hμ2_B_lt_top]
      have h15 : μ₁ B = ENNReal.ofReal (μ₁ B).toReal := by
        rw [ENNReal.ofReal_toReal hμ1_B_lt_top]
      rw [h14, h15]
      exact ENNReal.ofReal_le_ofReal h13
  exact le_antisymm h_final1 h_final2

end Geometry
