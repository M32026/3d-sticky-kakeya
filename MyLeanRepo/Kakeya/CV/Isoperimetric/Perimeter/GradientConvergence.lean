import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.GradientHelpers
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterDefinition
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.Mollification
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory Convolution ContDiff

namespace Geometry.Perimeter

variable {n : ℕ} [Nonempty (Fin n)]

/-- Riesz representative of a continuous linear functional on E n. -/
noncomputable def riesz (l : E n →L[ℝ] ℝ) : E n :=
  (InnerProductSpace.toDual ℝ (E n)).symm l

lemma riesz_apply (l : E n →L[ℝ] ℝ) (v : E n) :
    l v = inner ℝ (riesz l) v := by
  simpa [riesz] using rfl

lemma riesz_norm (l : E n →L[ℝ] ℝ) : ‖riesz l‖ = ‖l‖ :=
  (InnerProductSpace.toDual ℝ (E n)).symm.norm_map l

/-- Vector mollification via Bochner integral. -/
noncomputable def mollifyVec (ρ : E n → ℝ) (w : E n → E n) : E n → E n :=
  fun x => ∫ t, ρ t • w (x - t)

lemma mollifyVec_component {ρ : E n → ℝ} {w : E n → E n}
    (hρ_support : HasCompactSupport ρ) (hρ_cont : Continuous ρ) (hw_cont : Continuous w)
    (x : E n) (i : Fin n) :
    (mollifyVec ρ w x) i = ∫ t, ρ t * (w (x - t) i) := by
  let proj_i : E n →L[ℝ] ℝ :=
    { toFun := fun z => z i
      map_add' := by intro a b; simp
      map_smul' := by intro c a; simp }
  have h_int : Integrable (fun t : E n => ρ t • w (x - t)) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · apply hρ_support.mono
      intro t ht
      have h5 : ρ t • w (x - t) ≠ 0 := ht
      have h6 : ρ t ≠ 0 := by
        intro h7
        have h8 : ρ t • w (x - t) = 0 := by rw [h7]; simp
        exact h5 h8
      simpa [Function.mem_support] using h6
  have h1 : proj_i (∫ t, ρ t • w (x - t)) = ∫ t, proj_i (ρ t • w (x - t)) :=
    (proj_i.integral_comp_comm h_int).symm
  have h2 : ∀ t, proj_i (ρ t • w (x - t)) = ρ t * (w (x - t) i) := by
    intro t; simp [proj_i] <;> ring
  have h3 : ∫ t, proj_i (ρ t • w (x - t)) = ∫ t, ρ t * (w (x - t) i) := by
    apply integral_congr_ae; filter_upwards with t; exact h2 t
  have h4 : (mollifyVec ρ w x) i = proj_i (mollifyVec ρ w x) := by rfl
  have h5 : mollifyVec ρ w x = ∫ t, ρ t • w (x - t) := by rfl
  rw [h4, h5, h1, h3]

lemma mollifyVec_smooth {ρ : E n → ℝ} {w : E n → E n}
    (hρ_smooth : ContDiff ℝ ∞ ρ) (hρ_support : HasCompactSupport ρ)
    (hw_cont : Continuous w) : ContDiff ℝ ∞ (mollifyVec ρ w) := by
  have h : ∀ (i : Fin n), ContDiff ℝ ∞ (fun x => (mollifyVec ρ w x) i) := by
    intro i
    have h1 : (fun x => (mollifyVec ρ w x) i) = fun x => ∫ t, ρ t * (w (x - t) i) := by
      funext x
      exact mollifyVec_component hρ_support hρ_smooth.continuous hw_cont x i
    rw [h1]
    have hwi_cont : Continuous (fun y : E n => w y i) := by fun_prop
    exact hρ_support.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      hρ_smooth hwi_cont.locallyIntegrable
  exact contDiff_euclidean.mpr h

lemma mollifyVec_hasCompactSupport {ρ : E n → ℝ} {w : E n → E n}
    (hρ_support : HasCompactSupport ρ) (hw_support : HasCompactSupport w) :
    HasCompactSupport (mollifyVec ρ w) := by
  let S : Set (E n) := Set.image2 (· + ·) (tsupport ρ) (tsupport w)
  have hρ_compact : IsCompact (tsupport ρ) := hρ_support
  have hw_compact : IsCompact (tsupport w) := hw_support
  have hS_compact : IsCompact S := hρ_compact.add hw_compact
  have h1 : Function.support (mollifyVec ρ w) ⊆ S := by
    intro x hx
    by_contra h_notin
    have h2 : x ∉ S := h_notin
    -- For all t, if t ∈ tsupport ρ then x - t ∉ tsupport w
    have h3 : ∀ t ∈ tsupport ρ, x - t ∉ tsupport w := by
      intro t ht
      by_contra h4
      have h_contr : x ∈ S := ⟨t, ht, x - t, h4, by abel_nf⟩
      exact h_notin h_contr
    -- Hence ρ t • w(x - t) = 0 for all t
    have h4 : ∀ t, ρ t • w (x - t) = 0 := by
      intro t
      by_cases h5 : t ∈ tsupport ρ
      · have h6 : w (x - t) = 0 := by
          have h7 : x - t ∉ tsupport w := h3 t h5
          have h8 : x - t ∉ Function.support w := fun h9 => h7 (subset_closure h9)
          simpa [Function.mem_support] using h8
        rw [h6]; simp
      · have h7 : ρ t = 0 := by
          have h8 : t ∉ Function.support ρ := fun h9 => h5 (subset_closure h9)
          simpa [Function.mem_support] using h8
        rw [h7]; simp
    have h5 : mollifyVec ρ w x = 0 := by
      rw [mollifyVec]
      have h6 : (fun t : E n => ρ t • w (x - t)) = 0 := by
        funext t; exact h4 t
      rw [h6]
      simp
    exact hx h5
  exact hS_compact.of_isClosed_subset isClosed_closure (closure_minimal h1 hS_compact.isClosed)

/-- Support of vector mollification is contained in the Minkowski sum of
the support of the mollifier and the topological support of the function. -/
lemma mollifyVec_support_bound {ρ : E n → ℝ} {w : E n → E n}
    (hρ_support : HasCompactSupport ρ) (hw_support : HasCompactSupport w) :
    Function.support (mollifyVec ρ w) ⊆ Set.image2 (· + ·) (Function.support ρ) (tsupport w) := by
  intro x hx
  by_contra h_notin
  have h3 : ∀ t ∈ Function.support ρ, x - t ∉ tsupport w := by
    intro t ht
    by_contra h4
    have h_contr : x ∈ Set.image2 (· + ·) (Function.support ρ) (tsupport w) :=
      ⟨t, ht, x - t, h4, by abel_nf⟩
    exact h_notin h_contr
  have h4 : ∀ t, ρ t • w (x - t) = 0 := by
    intro t
    by_cases h5 : t ∈ Function.support ρ
    · have h6 : w (x - t) = 0 := by
        have h7 : x - t ∉ tsupport w := h3 t h5
        have h8 : x - t ∉ Function.support w := fun h9 => h7 (subset_closure h9)
        simpa [Function.mem_support] using h8
      rw [h6]; simp
    · have h7 : ρ t = 0 := by simpa [Function.mem_support] using h5
      rw [h7]; simp
  have h5 : mollifyVec ρ w x = 0 := by
    rw [mollifyVec]
    have h6 : (fun t : E n => ρ t • w (x - t)) = 0 := by funext t; exact h4 t
    rw [h6]; simp
  exact hx h5

lemma mollifyVec_norm_bound {ρ : E n → ℝ} {w : E n → E n}
    (hρ_nonneg : ∀ x, 0 ≤ ρ x) (hρ_int : ∫ x, ρ x = 1)
    (hρ_support : HasCompactSupport ρ) (hρ_cont : Continuous ρ)
    (hw_cont : Continuous w) (hw_bound : ∀ x, ‖w x‖ ≤ 1) :
    ∀ x, ‖mollifyVec ρ w x‖ ≤ 1 := by
  intro x
  have h_supp : Function.support (fun t : E n => ρ t • w (x - t)) ⊆ Function.support ρ := by
    intro t ht
    have h5 : ρ t • w (x - t) ≠ 0 := ht
    have h6 : ρ t ≠ 0 := by
      intro h7
      have h8 : ρ t • w (x - t) = 0 := by rw [h7]; simp
      exact h5 h8
    exact h6
  have h_int : Integrable (fun t : E n => ρ t • w (x - t)) volume :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (hρ_support.mono h_supp)
  have h1 : ‖mollifyVec ρ w x‖ ≤ ∫ t : E n, ‖ρ t • w (x - t)‖ := by
    have h_eq1 : mollifyVec ρ w x = ∫ t, ρ t • w (x - t) := by rfl
    rw [h_eq1]
    exact norm_integral_le_integral_norm fun a => ρ a • w (x - a)
  have h2 : ∀ t, ‖ρ t • w (x - t)‖ = ρ t * ‖w (x - t)‖ := by
    intro t
    have h3 : ‖ρ t • w (x - t)‖ = |ρ t| * ‖w (x - t)‖ := norm_smul (ρ t) (w (x - t))
    rw [h3]
    have h4 : |ρ t| = ρ t := abs_of_nonneg (hρ_nonneg t)
    rw [h4] <;> ring
  have h3 : ∫ t : E n, ‖ρ t • w (x - t)‖ = ∫ t : E n, ρ t * ‖w (x - t)‖ := by
    apply integral_congr_ae; filter_upwards with t; exact h2 t
  rw [h3] at h1
  have hρ_int' : Integrable ρ volume := hρ_cont.integrable_of_hasCompactSupport hρ_support
  have h4 : ∫ t : E n, ρ t * ‖w (x - t)‖ ≤ ∫ t : E n, ρ t := by
    have h_cont : Continuous (fun t : E n => ρ t * ‖w (x - t)‖) := by fun_prop
    have h_supp : Function.support (fun t : E n => ρ t * ‖w (x - t)‖) ⊆ Function.support ρ := by
      intro t ht; by_contra h5
      have h6 : ρ t = 0 := by simpa [Function.mem_support] using h5
      have h7 : ρ t * ‖w (x - t)‖ = 0 := by rw [h6] <;> ring
      exact ht h7
    have h_compact : HasCompactSupport (fun t : E n => ρ t * ‖w (x - t)‖) :=
      hρ_support.mono h_supp
    have h_int2 : Integrable (fun t : E n => ρ t * ‖w (x - t)‖) volume :=
      h_cont.integrable_of_hasCompactSupport h_compact
    apply integral_mono h_int2 hρ_int'
    intro t
    have h5 : ‖w (x - t)‖ ≤ 1 := hw_bound (x - t)
    have h6 : 0 ≤ ρ t := hρ_nonneg t
    nlinarith
  rw [hρ_int] at h4
  exact h1.trans h4

/-- **Uniform convergence of vector mollification**.

If `g : E n → E n` is continuous with compact support, and `ρ_ε` is the standard
mollifier family with `ε → 0`, then `mollifyVec ρ_ε g → g` uniformly. -/
lemma mollifyVec_uniform_convergence {g : E n → E n}
    (hg_cont : Continuous g) (hg_support : HasCompactSupport g) :
    ∀ (δ : ℝ), 0 < δ → ∃ (ε₀ : ℝ), 0 < ε₀ ∧
      ∀ (ε : ℝ) (hε : 0 < ε), ε < ε₀ →
        ∀ (x : E n), ‖mollifyVec (Mollification.rho (n := n) ε hε) g x - g x‖ < δ := by
  intro δ hδ
  -- Uniform continuity of g
  have hK_compact : IsCompact (tsupport g) := hg_support
  have hK_bdd : Bornology.IsBounded (tsupport g) := hK_compact.isBounded
  rcases hK_bdd.subset_closedBall 0 with ⟨R, hR⟩
  let K' : Set (E n) := closedBall 0 (R + 1)
  have hK'_compact : IsCompact K' := isCompact_closedBall 0 (R + 1)
  have hK_sub : tsupport g ⊆ K' := by
    intro x hx
    have h1 : dist x 0 ≤ R := hR hx
    have h2 : dist x 0 ≤ R + 1 := by linarith
    exact Metric.mem_closedBall.mpr h2
  have h_uc_on : UniformContinuousOn g K' :=
    hK'_compact.uniformContinuousOn_of_continuous hg_cont.continuousOn
  have hδ2_pos : 0 < δ / 2 := by linarith
  have h1 : ∃ δ₁ > 0, ∀ (x y : E n), x ∈ K' → y ∈ K' → dist x y < δ₁ → ‖g x - g y‖ < δ / 2 := by
    have h_iff : ∀ ε > 0, ∃ δ₁ > 0, ∀ x ∈ K', ∀ y ∈ K', dist x y < δ₁ → dist (g x) (g y) < ε :=
      Metric.uniformContinuousOn_iff.mp h_uc_on
    rcases h_iff (δ / 2) hδ2_pos with ⟨δ₁, hδ₁_pos, hδ₁⟩
    refine ⟨δ₁, hδ₁_pos, fun x y hx hy hdist => ?_⟩
    have h : dist (g x) (g y) < δ / 2 := hδ₁ x hx y hy hdist
    simpa [dist_eq_norm] using h
  rcases h1 with ⟨δ₁, hδ₁_pos, hδ₁⟩
  let ε₀ : ℝ := min δ₁ 1
  have hε₀_pos : 0 < ε₀ := by positivity
  refine ⟨ε₀, hε₀_pos, fun ε hε hε_lt x => ?_⟩
  let ρ : E n → ℝ := Mollification.rho (n := n) ε hε
  let b : ContDiffBump (0 : E n) := Mollification.mollifier (n := n) ε hε
  have hρ_nonneg : ∀ t, 0 ≤ ρ t := b.nonneg_normed
  have hρ_int : ∫ t, ρ t = 1 := b.integral_normed
  have hρ_support : HasCompactSupport ρ := b.hasCompactSupport_normed
  have hρ_cont : Continuous ρ := b.continuous_normed
  have h_supp_ρ : Function.support ρ = Metric.ball (0 : E n) ε := b.support_normed_eq
  have h_ε_lt_1 : ε < 1 := by
    have h : ε < ε₀ := hε_lt
    have h2 : ε₀ ≤ 1 := min_le_right _ _
    linarith
  -- Integrability helpers
  have h_supp_int : Function.support (fun t : E n => ρ t • g (x - t)) ⊆ Function.support ρ := by
    intro t ht
    have h5 : ρ t • g (x - t) ≠ 0 := ht
    have h6 : ρ t ≠ 0 := by
      intro h7
      have h8 : ρ t • g (x - t) = 0 := by rw [h7]; simp
      exact h5 h8
    exact h6
  have h_int : Integrable (fun t : E n => ρ t • g (x - t)) volume :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (hρ_support.mono h_supp_int)
  have h_supp3 : Function.support (fun t : E n => ρ t • g x) ⊆ Function.support ρ := by
    intro t ht
    have h5 : ρ t • g x ≠ 0 := ht
    have h6 : ρ t ≠ 0 := by
      intro h7
      have h8 : ρ t • g x = 0 := by rw [h7]; simp
      exact h5 h8
    exact h6
  have h_int3 : Integrable (fun t : E n => ρ t • g x) volume :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (hρ_support.mono h_supp3)
  have h_supp2 : Function.support (fun t : E n => ρ t • (g (x - t) - g x)) ⊆ Function.support ρ := by
    intro t ht
    have h5 : ρ t • (g (x - t) - g x) ≠ 0 := ht
    have h6 : ρ t ≠ 0 := by
      intro h7
      have h8 : ρ t • (g (x - t) - g x) = 0 := by rw [h7]; simp
      exact h5 h8
    exact h6
  have h_int2 : Integrable (fun t : E n => ρ t • (g (x - t) - g x)) volume :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (hρ_support.mono h_supp2)
  -- Key equation: mollifyVec ρ g x - g x = ∫ t, ρ t • (g(x-t) - g x)
  have h2 : ∫ t, ρ t • g x = (∫ t, ρ t) • g x := integral_smul_const ρ (g x)
  have h3 : g x = ∫ t, ρ t • g x := by
    rw [h2, hρ_int] <;> simp
  have h4 : ∫ t, ρ t • (g (x - t) - g x) = (∫ t, ρ t • g (x - t)) - ∫ t, ρ t • g x := by
    have h5 : (fun t : E n => ρ t • (g (x - t) - g x)) = fun t => (ρ t • g (x - t)) - (ρ t • g x) := by
      funext t; exact smul_sub (ρ t) (g (x - t)) (g x)
    rw [h5]
    exact integral_sub h_int h_int3
  have h_eq : mollifyVec ρ g x - g x = ∫ t, ρ t • (g (x - t) - g x) := by
    have h1 : mollifyVec ρ g x = ∫ t, ρ t • g (x - t) := by rfl
    have h_step1 : mollifyVec ρ g x - g x = (∫ t, ρ t • g (x - t)) - g x := by
      rw [h1]
    have h_step2 : (∫ t, ρ t • g (x - t)) - g x = (∫ t, ρ t • g (x - t)) - ∫ t, ρ t • g x := by
      exact congr_arg (fun y : E n => (∫ t, ρ t • g (x - t)) - y) h3
    rw [h_step1, h_step2]
    exact h4.symm
  rw [h_eq]
  -- Norm bound
  have h_bound : ‖∫ t, ρ t • (g (x - t) - g x)‖ ≤ ∫ t, ρ t * ‖g (x - t) - g x‖ := by
    have h_norm1 : ‖∫ t, ρ t • (g (x - t) - g x)‖ ≤ ∫ t, ‖ρ t • (g (x - t) - g x)‖ := by
      exact norm_integral_le_integral_norm fun a => ρ a • (g (x - a) - g x)
    have h_norm2 : ∫ t, ‖ρ t • (g (x - t) - g x)‖ = ∫ t, ρ t * ‖g (x - t) - g x‖ := by
      apply integral_congr_ae
      filter_upwards with t
      have h4 : ‖ρ t • (g (x - t) - g x)‖ = |ρ t| * ‖g (x - t) - g x‖ := norm_smul _ _
      rw [h4]
      have h5 : |ρ t| = ρ t := abs_of_nonneg (hρ_nonneg t)
      rw [h5] <;> ring
    rw [h_norm2] at h_norm1
    exact h_norm1
  -- Pointwise bound: ‖g(x-t) - g(x)‖ < δ whenever ρ t ≠ 0
  have h_point : ∀ t, ρ t * ‖g (x - t) - g x‖ ≤ ρ t * (δ / 2) := by
    intro t
    by_cases h6 : ρ t = 0
    · have h7 : ρ t * ‖g (x - t) - g x‖ = 0 := by rw [h6] <;> ring
      have h8 : ρ t * (δ / 2) = 0 := by rw [h6] <;> ring
      rw [h7, h8] <;> exact zero_le_zero
    · have h7 : t ∈ Function.support ρ := by simpa [Function.mem_support] using h6
      have h8 : t ∈ Metric.ball (0 : E n) ε := by
        rw [h_supp_ρ] at h7; exact h7
      have h9 : dist t 0 < ε := Metric.mem_ball.mp h8
      have h10 : dist (x - t) x < ε₀ := by
        have h11 : dist (x - t) x = dist t 0 := by
          have h12 : (x - t) - x = -t := by abel
          simp [dist_eq_norm, h12, norm_neg]
        rw [h11]; linarith
      -- If both g values are zero, the bound is trivial
      by_cases h_both : g x = 0 ∧ g (x - t) = 0
      · have h13 : ‖g (x - t) - g x‖ = 0 := by
          rw [h_both.2, h_both.1] <;> simp
        rw [h13]
        have h14 : 0 ≤ ρ t := hρ_nonneg t
        have h15 : 0 ≤ δ := by linarith
        nlinarith
      · -- At least one is nonzero, so both points are in K'
        have h12 : x - t ∈ K' := by
          by_cases h13 : g (x - t) ≠ 0
          · have h14 : x - t ∈ Function.support g := by
              simpa [Function.mem_support] using h13
            have h15 : x - t ∈ tsupport g := subset_closure h14
            have h16 : dist (x - t) 0 ≤ R := hR h15
            have h17 : dist (x - t) 0 ≤ R + 1 := by linarith
            exact Metric.mem_closedBall.mpr h17
          · -- g(x-t) = 0, so g(x) ≠ 0
            have h14 : g x ≠ 0 := by tauto
            have h15 : x ∈ Function.support g := by
              simpa [Function.mem_support] using h14
            have h16 : x ∈ tsupport g := subset_closure h15
            have h17 : dist x 0 ≤ R := hR h16
            have h18 : dist (x - t) 0 ≤ dist (x - t) x + dist x 0 := dist_triangle (x - t) x 0
            have h185 : dist (x - t) x = dist t 0 := by
              have h22 : (x - t) - x = -t := by abel
              simp [dist_eq_norm, h22, norm_neg]
            rw [h185] at h18
            have h19 : dist (x - t) 0 ≤ R + 1 := by linarith
            exact Metric.mem_closedBall.mpr h19
        have h13 : x ∈ K' := by
          by_cases h14 : g x ≠ 0
          · have h15 : x ∈ Function.support g := by
              simpa [Function.mem_support] using h14
            have h16 : x ∈ tsupport g := subset_closure h15
            have h17 : dist x 0 ≤ R := hR h16
            have h18 : dist x 0 ≤ R + 1 := by linarith
            exact Metric.mem_closedBall.mpr h18
          · -- g(x) = 0, so g(x-t) ≠ 0
            have h15 : g (x - t) ≠ 0 := by tauto
            have h16 : x - t ∈ Function.support g := by
              simpa [Function.mem_support] using h15
            have h17 : x - t ∈ tsupport g := subset_closure h16
            have h18 : dist (x - t) 0 ≤ R := hR h17
            have h19 : dist x 0 ≤ dist (x - t) 0 + dist t 0 := by
              have h20 : dist x 0 ≤ dist x (x - t) + dist (x - t) 0 := dist_triangle x (x - t) 0
              have h21 : dist x (x - t) = dist t 0 := by
                have h22 : x - (x - t) = t := by abel
                simp [dist_eq_norm, h22]
              linarith
            have h23 : dist x 0 ≤ R + 1 := by linarith
            exact Metric.mem_closedBall.mpr h23
        have h105 : dist (x - t) x < δ₁ := by
          have h106 : ε₀ ≤ δ₁ := min_le_left _ _
          linarith
        have h14 : ‖g (x - t) - g x‖ < δ / 2 := hδ₁ (x - t) x h12 h13 h105
        have h15 : 0 ≤ ρ t := hρ_nonneg t
        nlinarith
  have h_cont1 : Continuous (fun t : E n => ρ t * ‖g (x - t) - g x‖) := by fun_prop
  have h_supp1 : Function.support (fun t : E n => ρ t * ‖g (x - t) - g x‖) ⊆ Function.support ρ := by
    intro t ht
    by_contra h5
    have h6 : ρ t = 0 := by simpa [Function.mem_support] using h5
    have h7 : ρ t * ‖g (x - t) - g x‖ = 0 := by rw [h6] <;> ring
    exact ht h7
  have h_compact1 : HasCompactSupport (fun t : E n => ρ t * ‖g (x - t) - g x‖) :=
    hρ_support.mono h_supp1
  have h_int1 : Integrable (fun t : E n => ρ t * ‖g (x - t) - g x‖) volume :=
    h_cont1.integrable_of_hasCompactSupport h_compact1
  have hρ_int' : Integrable ρ volume := hρ_cont.integrable_of_hasCompactSupport hρ_support
  have h_intδ : Integrable (fun t : E n => ρ t * (δ / 2)) volume :=
    hρ_int'.mul_const (δ / 2)
  have h_final : ∫ t, ρ t * ‖g (x - t) - g x‖ ≤ ∫ t, ρ t * (δ / 2) :=
    integral_mono h_int1 h_intδ h_point
  have hδ_int : ∫ t, ρ t * (δ / 2) = δ / 2 := by
    have h : ∫ t, ρ t * (δ / 2) = (δ / 2) * ∫ t, ρ t := by
      simpa [mul_comm] using integral_const_mul (δ / 2) ρ
    rw [h, hρ_int] <;> ring
  rw [hδ_int] at h_final
  have h_last : ‖∫ t, ρ t • (g (x - t) - g x)‖ < δ := by
    calc
      ‖∫ t, ρ t • (g (x - t) - g x)‖ ≤ ∫ t, ρ t * ‖g (x - t) - g x‖ := h_bound
      _ ≤ δ / 2 := h_final
      _ < δ := by linarith
  exact h_last

end Geometry.Perimeter
