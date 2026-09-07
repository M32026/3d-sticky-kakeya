import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.Mollification
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.MollificationContraction
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.MollificationGoodLevelHausdorff
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


/-!
# Isoperimetric Inequality via Mollification and Coarea

Proves `P(S) ≥ n · V(S)^((n-1)/n) · V(B₁)^(1/n)` for measurable bounded `S`
by mollifying `χ_S`, selecting good level sets via the coarea formula,
and taking limits.

This is the "mollification route" that bypasses the outer Minkowski content
upper bound needed by the Brunn–Minkowski route.

## Dependencies

- `mollification_good_level_sequence_hausdorff` (pelican): level set selection
  with Hausdorff isoperimetric inequality and limsup bound.
- `mollification_gradient_convergence'`: gradient integral → perimeter.
- Standard mollification properties from `Coarea.Mollification`.
-/

namespace Geometry

open MeasureTheory ENNReal Metric Set Filter
open scoped MeasureTheory Pointwise

/-- **Sharp isoperimetric inequality (perimeter form) via mollification.**

For measurable bounded `S` with `0 < P(S) < ⊤`:
`P(S) ≥ n · V(S)^((n-1)/n) · V(B₁)^(1/n)`.

Proof: mollify `χ_S`, apply coarea-based good level set selection to get
smooth open `U_k` with `V(U_k) → V(S)` and
`limsup H(∂U_k) ≤ P(S)`, then take limits. -/
theorem isoperimetric_from_mollification (n : ℕ) (hn : 2 ≤ n)
    (S : Set (E n)) (hS : MeasurableSet S) (hBdd : Bornology.IsBounded S)
    (hP_pos : 0 < Perimeter.perimeter S) (hP_lt_top : Perimeter.perimeter S < ⊤) :
    (n : ENNReal) * (volume S)^((n - 1 : ℝ) / n) *
      (volume (unitBall n))^(1 / (n : ℝ)) ≤ Perimeter.perimeter S := by
  -- Decompose n = m + 1 so pelican's theorem (parameterized by boundary dim m)
  -- applies directly in ambient dimension m + 1 = n.
  cases n with
  | zero => omega
  | succ m =>
    have hm : 1 ≤ m := by omega
    letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩

    set ω : ENNReal := volume (unitBall (m + 1)) with hω_def
    set α : ℝ := (m : ℝ) / (m + 1) with hα_def
    set β : ℝ := 1 / ((m + 1 : ℝ)) with hβ_def
    set C : ENNReal := ((m + 1 : ℕ) : ENNReal) * ω^β with hC_def

    -- ======================================================================
    -- Compact K containing a neighborhood of S
    -- ======================================================================
    rcases hBdd.subset_closedBall 0 with ⟨R, hR⟩
    let K : Set (E (m + 1)) := closedBall (0 : E (m + 1)) (R + 1)
    have hK_compact : IsCompact K := isCompact_closedBall _ _
    have hS_sub_K : S ⊆ K := by
      intro x hx
      have h1 : dist x 0 ≤ R := hR hx
      have h2 : dist x 0 ≤ R + 1 := by linarith
      exact h2

    -- ======================================================================
    -- Mollification sequence u_k = χ_S * ρ_{1/(k+2)}
    -- ======================================================================
    let u : ℕ → E (m + 1) → ℝ := fun k => Mollification.mollificationSeq hS k
    let χ : E (m + 1) → ℝ := Set.indicator S (fun _ => (1 : ℝ))

    -- Smoothness: mollification is C^∞
    have h_u_smooth : ∀ k, ContDiff ℝ (↑(⊤ : ℕ∞)) (u k) := by
      intro k
      simpa [u, Mollification.mollificationSeq] using
        Mollification.mollify_contDiff hS (1 / (k + 2 : ℝ)) (by positivity)

    -- Bounds: 0 ≤ u_k ≤ 1
    have h_u_bound : ∀ k x, 0 ≤ u k x ∧ u k x ≤ 1 := by
      intro k
      exact Mollification.mollify_bound hS (1 / (k + 2 : ℝ)) (by positivity)

    -- ======================================================================
    -- Support: supp(u_k) ⊆ K for all k
    -- ======================================================================
    have h_supp_sub_K : ∀ k, Function.support (u k) ⊆ K := by
      intro k
      let ε : ℝ := 1 / (k + 2 : ℝ)
      have hε_pos : 0 < ε := by positivity
      have hε_le_one : ε ≤ 1 := by
        have h3 : (1 : ℝ) ≤ (k + 2 : ℝ) := by exact_mod_cast (by linarith)
        exact (div_le_one (by positivity)).mpr h3
      let ρ : E (m + 1) → ℝ := Mollification.rho (ε := ε) (hε := hε_pos)
      let φ : ContDiffBump (0 : E (m + 1)) := Mollification.mollifier ε hε_pos
      have h_conv : u k = MeasureTheory.convolution ρ χ
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        simp [u, Mollification.mollificationSeq, Mollification.mollify, ρ] <;> rfl
      have h1 : Function.support (u k) ⊆ Function.support ρ + Function.support χ := by
        rw [h_conv]
        exact MeasureTheory.support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)
      have h2 : Function.support ρ ⊆ closedBall (0 : E (m + 1)) ε := by
        have h21 : Function.support ρ = Metric.ball (0 : E (m + 1)) ε :=
          ContDiffBump.support_normed_eq φ
        rw [h21] <;> exact ball_subset_closedBall
      have h3 : Function.support χ ⊆ closure S := by
        intro x hx
        have hxS : x ∈ S := by
          simpa [χ, Function.mem_support, Set.indicator_apply] using hx
        exact subset_closure hxS
      have h4 : Function.support ρ + Function.support χ ⊆
          closedBall (0 : E (m + 1)) ε + closure S := Set.add_subset_add h2 h3
      have h5 : closedBall (0 : E (m + 1)) ε + closure S ⊆ K := by
        intro z hz
        rcases hz with ⟨a, ha, b, hb, rfl⟩
        have h6 : dist a 0 ≤ ε := ha
        have h7 : b ∈ closure S := hb
        have h8 : dist b 0 ≤ R := by
          have h9 : closure S ⊆ closedBall (0 : E (m + 1)) R :=
            closure_minimal hR isClosed_closedBall
          exact h9 h7
        have h11 : dist (a + b) 0 ≤ R + 1 := by
          calc dist (a + b) 0
            ≤ dist a 0 + dist b 0 := by simpa [dist_eq_norm] using norm_add_le a b
          _ ≤ ε + R := by gcongr
          _ ≤ 1 + R := by gcongr
          _ = R + 1 := by ring
        exact h11
      exact h1.trans (h4.trans h5)

    -- Compact support from support ⊆ compact K
    have h_u_support : ∀ k, HasCompactSupport (u k) := by
      intro k
      have h_tsupport : tsupport (u k) ⊆ K :=
        closure_minimal (h_supp_sub_K k) hK_compact.isClosed
      exact IsCompact.of_isClosed_subset hK_compact isClosed_closure h_tsupport

    -- Vanishing outside K
    have h_supp_K : ∀ k, ∀ x ∉ K, u k x = 0 := by
      intro k x hx
      have h2 : x ∉ Function.support (u k) := by
        intro h3; exact hx (h_supp_sub_K k h3)
      simpa [Function.mem_support] using h2

    -- ======================================================================
    -- L¹ convergence on compact sets
    -- ======================================================================
    have h_u_L1 : ∀ (L : Set (E (m + 1))), IsCompact L →
        Filter.Tendsto (fun k => ∫ x in L, |u k x - χ x|)
          Filter.atTop (nhds 0) := by
      intro L hL
      exact Mollification.mollify_tendsto_L1 hS hL

    -- ======================================================================
    -- Gradient integral convergence: ∫⁻ ‖∇u_k‖ → P(S)
    -- ======================================================================
    have h_grad_conv : Filter.Tendsto
        (fun k => ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ (u k) x‖)
        Filter.atTop (nhds (Perimeter.perimeter S)) :=
      Perimeter.mollification_gradient_convergence' hS hBdd hP_lt_top u rfl

    -- ======================================================================
    -- Good level set selection (pelican's theorem)
    -- ======================================================================
    rcases mollification_good_level_sequence_hausdorff
        hm hS hBdd hP_pos hP_lt_top
        K hK_compact hS_sub_K u
        h_u_smooth h_u_bound h_u_support h_supp_K h_u_L1 h_grad_conv
      with ⟨s, hs_range, hs_props, hs_iso, hs_vol, hs_limsup⟩

    let U : ℕ → Set (E (m + 1)) := fun k => {x | u k x > s k}

    -- ======================================================================
    -- Limit argument: C · V(U_k)^α ≤ H(∂U_k), take limsup
    -- ======================================================================
    let a_k : ℕ → ENNReal := fun k => C * (volume (U k))^α
    let a : ENNReal := C * (volume S)^α

    have hα_pos : 0 < α := by
      rw [hα_def]
      have h1 : 0 < (m : ℝ) := by exact_mod_cast hm
      have h2 : 0 < ((m + 1 : ℝ)) := by positivity
      exact div_pos h1 h2

    -- Per-level inequality
    have h_ineq : ∀ k, a_k k ≤ μHE[m] (frontier (U k)) := by
      intro k
      by_cases hVk : volume (U k) = 0
      · have h : a_k k = 0 := by
          simp only [a_k, hVk, ENNReal.zero_rpow_of_pos hα_pos, mul_zero]
        rw [h]; simp
      · have hVk_pos : 0 < volume (U k) := Ne.bot_lt hVk
        have h_eq : a_k k = ((m + 1 : ℕ) : ENNReal) * (volume (U k))^α * ω^β := by
          simp only [a_k, C, hC_def] <;> ring
        rw [h_eq]
        exact hs_iso k hVk_pos

    -- C ≠ ⊤ for continuity
    have hω_lt_top : ω < ⊤ := Metric.isBounded_closedBall.measure_lt_top
    have hβ_pos : 0 < β := by
      rw [hβ_def]
      have h1 : 0 < ((m + 1 : ℝ)) := by positivity
      exact div_pos zero_lt_one h1
    have hωβ_lt_top : ω^β < ⊤ :=
      (ENNReal.rpow_lt_top_iff_of_pos hβ_pos).mpr hω_lt_top
    have hC_ne_top : C ≠ ⊤ := by
      simp only [C, hC_def]
      exact ENNReal.mul_ne_top (by simp) hωβ_lt_top.ne

    -- Continuity: V_k → V implies C · V_k^α → C · V^α
    have h_cont_rpow : Continuous (fun x : ENNReal => x^α) :=
      ENNReal.continuous_rpow_const (y := α)
    have h_cont_mul : Continuous (fun x : ENNReal => C * x) :=
      ENNReal.continuous_const_mul hC_ne_top
    have h_cont : Continuous (fun x : ENNReal => C * x^α) :=
      h_cont_mul.comp h_cont_rpow
    have h_a_conv : Tendsto a_k atTop (nhds a) :=
      h_cont.continuousAt.tendsto.comp hs_vol

    -- limsup a_k ≤ limsup H(∂U_k) ≤ P(S)
    have h_limsup_mono : Filter.limsup a_k atTop ≤
        Filter.limsup (fun k => μHE[m] (frontier (U k))) atTop :=
      Filter.limsup_le_limsup (Eventually.of_forall h_ineq)
    have h_a_limsup : Filter.limsup a_k atTop = a :=
      h_a_conv.limsup_eq
    have h1 : a ≤ Filter.limsup (fun k => μHE[m] (frontier (U k))) atTop := by
      rw [←h_a_limsup] <;> exact h_limsup_mono
    have h_main : a ≤ Perimeter.perimeter S := le_trans h1 hs_limsup

    -- Unfold to goal
    have h_final : a = ((m + 1 : ℕ) : ENNReal) * (volume S)^α * ω^β := by
      simp only [a, C, hC_def] <;> ring
    rw [h_final] at h_main
    simpa [hα_def, hβ_def] using h_main

end Geometry
