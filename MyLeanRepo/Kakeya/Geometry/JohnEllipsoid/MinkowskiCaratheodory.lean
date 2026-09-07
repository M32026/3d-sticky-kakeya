module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Data.Int.Star
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.SetNotationForOrder

public section

open Set

namespace JohnEllipsoid.MinkowskiCaratheodory

/-!
# Minkowski-Caratheodory theorem for compact convex sets

In a finite-dimensional real normed vector space, every point of a compact
convex set lies in the convex hull of finitely many extreme points. We include
the finite Caratheodory bound `finrank + 1`.

## Main results

* `JohnEllipsoid.MinkowskiCaratheodory.minkowski_theorem`:
  a compact convex set is the convex hull of its extreme points in finite
  dimension.
* `JohnEllipsoid.MinkowskiCaratheodory.caratheodory_finite_convexHull`:
  a finite Caratheodory theorem using at most `finrank + 1` points.
* `JohnEllipsoid.MinkowskiCaratheodory.mem_convexHull_finset_extremePoints_of_mem_compact_convex`:
  every point of a compact convex set belongs to the convex hull of finitely
  many extreme points of the set.
-/

namespace SupportingHyperplane
lemma exists_fun_vanish_on_proper_submodule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K : Submodule ℝ E} (hK : K ≠ ⊤) :
  ∃ (f : E →L[ℝ] ℝ), f ≠ 0 ∧ ∀ v ∈ K, f v = 0 := by
  have h1 : ∃ (x : E), x ∉ K := by
    by_contra h
    push Not at h
    have h2 : K = ⊤ := by simpa [Submodule.eq_top_iff'] using h
    exact hK h2
  rcases h1 with ⟨x, hx⟩
  have h_main : ∃ (f : E →ₗ[ℝ] ℝ), f x ≠ 0 ∧ K.map f = ⊥ := by
    apply Submodule.exists_dual_map_eq_bot_of_notMem hx
    ; infer_instance
  rcases h_main with ⟨f_lin, hfx, hfK⟩
  have h_f_vanish : ∀ v ∈ K, f_lin v = 0 := by
    intro v hv
    have h6 : f_lin v ∈ (K.map f_lin) := by
      exact Submodule.mem_map_of_mem hv
    rw [hfK] at h6
    simpa using h6
  have h_f_ne_zero : f_lin ≠ 0 := by
    intro h
    have h7 : f_lin x = 0 := by rw [h]; simp
    exact hfx h7
  have h_cont : Continuous f_lin := by
    exact LinearMap.continuous_of_finiteDimensional f_lin
  let f : E →L[ℝ] ℝ := ⟨f_lin, h_cont⟩
  have h1_f_ne_zero : f ≠ 0 := by
    intro h
    have h9 : f x = 0 := by rw [h]; simp
    have h10 : f x = f_lin x := by rfl
    rw [h10] at h9
    exact hfx h9
  have h2_f_vanish : ∀ v ∈ K, f v = 0 := by
    intro v hv
    have h11 : f v = f_lin v := by rfl
    rw [h11]
    exact h_f_vanish v hv
  exact ⟨f, h1_f_ne_zero, h2_f_vanish⟩

theorem supporting_hyperplane_boundary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {s : Set E} {x : E} (hscomp : IsCompact s) (hsconv : Convex ℝ s) (hx : x ∈ frontier s) :
  ∃ (f : E →L[ℝ] ℝ), f ≠ 0 ∧ ∀ y ∈ s, f y ≤ f x := by

  have hxs1 : x ∈ closure s := frontier_subset_closure hx
  have hxs2 : x ∉ interior s := by
    have h : frontier s = closure s \ interior s := by rfl
    rw [h] at hx
    exact hx.2
  have h_closed : IsClosed s := IsCompact.isClosed hscomp
  have h_closure : closure s = s := h_closed.closure_eq
  have hxs : x ∈ s := by
    rw [h_closure] at hxs1
    exact hxs1
  have hsne : s.Nonempty := ⟨x, hxs⟩
  by_cases h : (interior s).Nonempty
  ·
    have h_main : ∃ (f : E →L[ℝ] ℝ), f ≠ 0 ∧ ∀ y ∈ s, f y ≤ f x := by
      exact geometric_hahn_banach_of_nonempty_interior_point hsconv hxs2 h
    exact h_main
  ·
    have h' : ¬ (interior s).Nonempty := h
    have hS : affineSpan ℝ s ≠ (⊤ : AffineSubspace ℝ E) := by
      have h_iff : (interior s).Nonempty ↔ affineSpan ℝ s = (⊤ : AffineSubspace ℝ E) :=
        hsconv.interior_nonempty_iff_affineSpan_eq_top
      tauto
    let S : AffineSubspace ℝ E := affineSpan ℝ s
    have hS_ne_top : S ≠ ⊤ := hS
    have hxS : x ∈ S := by
      have h1 : s ⊆ (S : Set E) := subset_affineSpan ℝ s
      exact h1 hxs
    let K : Submodule ℝ E := S.direction
    have hK_ne_top : K ≠ ⊤ := by
      by_contra hK_top
      have h_all : ∀ (z : E), z ∈ S := by
        intro z
        have h2 : z -ᵥ x ∈ K := by
          rw [hK_top]
          trivial
        have h3 : (z -ᵥ x) +ᵥ x ∈ S := S.vadd_mem_of_mem_direction h2 hxS
        have h4 : (z -ᵥ x) +ᵥ x = z := by simp
        rw [h4] at h3
        exact h3
      have hS_top : S = (⊤ : AffineSubspace ℝ E) := by
        ext z
        simpa using h_all z
      exact hS_ne_top hS_top
    rcases exists_fun_vanish_on_proper_submodule hK_ne_top with ⟨f, hf_ne_zero, hf_vanish⟩
    have h_main : ∀ y ∈ s, f y = f x := by
      intro y hy
      have h1 : s ⊆ (S : Set E) := subset_affineSpan ℝ s
      have hyS : y ∈ S := h1 hy
      have h_vsub : y -ᵥ x ∈ K := by
        exact S.vsub_mem_direction hyS hxS
      have h1' : f (y - x) = 0 := hf_vanish (y - x) h_vsub
      have h2 : f (y - x) = f y - f x := by
        simp
      linarith
    have h_final : ∀ y ∈ s, f y ≤ f x := by
      intro y hy
      have h3 : f y = f x := h_main y hy
      linarith
    exact ⟨f, hf_ne_zero, h_final⟩

end SupportingHyperplane

namespace Face
open SupportingHyperplane (supporting_hyperplane_boundary)

lemma convex_combination_eq_max_iff (u v M r : ℝ) (hr_pos : 0 < r) (hr_lt_one : r < 1)
    (hu : u ≤ M) (hv : v ≤ M) (h_eq : r * u + (1 - r) * v = M) : u = M ∧ v = M := by
  have h1 : 0 < 1 - r := by linarith
  have h2 : r * u + (1 - r) * v ≤ r * M + (1 - r) * M := by
    gcongr
  have h3 : r * M + (1 - r) * M = M := by ring
  have h4 : r * u + (1 - r) * v ≤ M := by linarith
  have h5 : r * u ≥ r * M := by
    nlinarith
  have h6 : u ≥ M := by nlinarith
  have hu_eq : u = M := by linarith
  have h7 : (1 - r) * v ≥ (1 - r) * M := by
    rw [hu_eq] at h_eq
    nlinarith
  have h8 : v ≥ M := by nlinarith
  have hv_eq : v = M := by linarith
  exact ⟨hu_eq, hv_eq⟩

theorem max_linear_preimage_is_face {E : Type*} [AddCommGroup E] [Module ℝ E]
  {s : Set E} (hsconv : Convex ℝ s) (f : E →ₗ[ℝ] ℝ) (M : ℝ) (hM : ∀ y ∈ s, f y ≤ M) :
  Convex ℝ { y ∈ s | f y = M } ∧ { y ∈ s | f y = M } ⊆ s ∧
  ∀ x, x ∈ { y ∈ s | f y = M } → ∀ a b, a ∈ s → b ∈ s → ∀ (r : ℝ), 0 < r → r < 1 → x = r • a + (1 - r) • b → a ∈ { y ∈ s | f y = M } ∧ b ∈ { y ∈ s | f y = M } := by

  set t : Set E := { y ∈ s | f y = M } with ht
  have h1 : Convex ℝ t := by
    intro x hx y hy a b ha0 hb0 hab
    have hx1 : x ∈ s := hx.1
    have hx2 : f x = M := hx.2
    have hy1 : y ∈ s := hy.1
    have hy2 : f y = M := hy.2
    have hz1 : a • x + b • y ∈ s := hsconv hx1 hy1 ha0 hb0 hab
    have hz2 : f (a • x + b • y) = M := by
      have h : f (a • x + b • y) = a * f x + b * f y := by
        simp [map_add, map_smul]
      rw [h, hx2, hy2]
      have h' : a * M + b * M = M := by
        calc
          a * M + b * M = (a + b) * M := by ring
          _ = 1 * M := by rw [hab]
          _ = M := by ring
      exact h'
    exact ⟨hz1, hz2⟩
  have h2 : t ⊆ s := by
    intro y hy
    exact hy.1
  have h3 : ∀ x, x ∈ t → ∀ a b, a ∈ s → b ∈ s → ∀ (r : ℝ), 0 < r → r < 1 → x = r • a + (1 - r) • b → a ∈ t ∧ b ∈ t := by
    intro x hx a b ha hb r hr_pos hr_lt_one h_eq
    have hx1 : x ∈ s := hx.1
    have hx2 : f x = M := hx.2
    have hfa_le : f a ≤ M := hM a ha
    have hfb_le : f b ≤ M := hM b hb
    have h_eq2 : f x = r * f a + (1 - r) * f b := by
      rw [h_eq]
      simp [map_add, map_smul]
    have h_eq3 : r * f a + (1 - r) * f b = M := by
      linarith [hx2, h_eq2]
    have h_main : f a = M ∧ f b = M := convex_combination_eq_max_iff (f a) (f b) M r hr_pos hr_lt_one hfa_le hfb_le h_eq3
    exact ⟨⟨ha, h_main.1⟩, ⟨hb, h_main.2⟩⟩
  exact ⟨h1, h2, h3⟩

end Face

namespace ExtremeFace
open SupportingHyperplane (supporting_hyperplane_boundary)
open Face (max_linear_preimage_is_face)

theorem extreme_points_face_subset {E : Type*} [AddCommGroup E] [Module ℝ E]
  {s : Set E} {F : Set E} (_hsconv : Convex ℝ s)
  (hF : Convex ℝ F ∧ F ⊆ s ∧ ∀ x, x ∈ F → ∀ a b, a ∈ s → b ∈ s → ∀ (r : ℝ), 0 < r → r < 1 → x = r • a + (1 - r) • b → a ∈ F ∧ b ∈ F) :
  F.extremePoints ℝ ⊆ s.extremePoints ℝ := by

  intro z hz
  have hzF : z ∈ F := hz.1
  have hzS : z ∈ s := hF.2.1 hzF
  have h_iff : ∀ ⦃x₁ : E⦄, x₁ ∈ F → ∀ ⦃x₂ : E⦄, x₂ ∈ F → z ∈ openSegment ℝ x₁ x₂ → x₁ = z := hz.2
  have h_goal : ∀ ⦃x₁ : E⦄, x₁ ∈ s → ∀ ⦃x₂ : E⦄, x₂ ∈ s → z ∈ openSegment ℝ x₁ x₂ → x₁ = z := by
    intro x₁ hx₁ x₂ hx₂ h_open
    have h_exists : ∃ (a b : ℝ), 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a • x₁ + b • x₂ = z := by
      simpa [openSegment] using h_open
    rcases h_exists with ⟨r, b, hr_pos, hb_pos, h_sum, h_eq⟩
    have hr_lt_one : r < 1 := by
      have h : b = 1 - r := by linarith
      rw [h] at hb_pos
      linarith
    have h_eq2 : z = r • x₁ + (1 - r) • x₂ := by
      have h : b = 1 - r := by linarith
      rw [h] at h_eq
      exact h_eq.symm
    have h1 : x₁ ∈ F := (hF.2.2 z hzF x₁ x₂ hx₁ hx₂ r hr_pos hr_lt_one h_eq2).1
    have h2 : x₂ ∈ F := (hF.2.2 z hzF x₁ x₂ hx₁ hx₂ r hr_pos hr_lt_one h_eq2).2
    exact h_iff h1 h2 h_open
  exact ⟨hzS, h_goal⟩

end ExtremeFace

namespace BoundaryDecomposition
open SupportingHyperplane (supporting_hyperplane_boundary)
open Face (max_linear_preimage_is_face)
open ExtremeFace (extreme_points_face_subset)

theorem interior_point_convex_comb_boundary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {s : Set E} (hscomp : IsCompact s) (_hsconv : Convex ℝ s) (h_dim : 0 < Module.finrank ℝ E) {x : E} (hx : x ∈ interior s) :
  ∃ (a b : E) (r : ℝ), a ∈ frontier s ∧ b ∈ frontier s ∧ 0 < r ∧ r < 1 ∧ x = r • a + (1 - r) • b := by

  have h1 : ∃ (v : E), v ≠ 0 := by
    by_contra h_contra
    push Not at h_contra
    have h_subsingleton : Subsingleton E := by
      exact _root_.subsingleton_of_forall_eq 0 h_contra
    have h_finrank_zero : Module.finrank ℝ E = 0 := by
      exact (Module.finrank_eq_zero_iff_of_free ℝ E).mpr h_subsingleton
    linarith
  rcases h1 with ⟨v, hv⟩
  have hnv : 0 < ‖v‖ := by exact norm_pos_iff.mpr hv
  have hnv' : ‖v‖ ≠ 0 := hnv.ne'
  let g : ℝ → E := fun t ↦ x + t • v
  let T : Set ℝ := g ⁻¹' s
  have hsc : IsClosed s := hscomp.isClosed
  have hT_closed : IsClosed T := hsc.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hs_bdd : Bornology.IsBounded s := hscomp.isBounded
  have h_bdd : ∃ (B : ℝ), ∀ (z : E), z ∈ s → ‖z‖ ≤ B := hs_bdd.exists_norm_le
  rcases h_bdd with ⟨B, hB⟩
  let C : ℝ := (B + ‖x‖) / ‖v‖
  have hT_subset : T ⊆ Metric.ball (0 : ℝ) (C + 1) := by
    intro t ht
    have h2 : g t ∈ s := ht
    have h3 : ‖g t‖ ≤ B := hB (g t) h2
    have h4 : ‖t • v‖ ≤ B + ‖x‖ := by
      have h5 : g t = x + t • v := by rfl
      rw [h5] at h3
      have h6 : ‖t • v‖ - ‖x‖ ≤ ‖x + t • v‖ := by
        have h7 : ‖(t • v) - (-x)‖ ≥ ‖t • v‖ - ‖-x‖ := norm_sub_norm_le (t • v) (-x)
        have h8 : ‖-x‖ = ‖x‖ := by simp
        have h9 : (t • v) - (-x) = x + t • v := by abel
        rw [h9, h8] at h7
        linarith
      linarith
    have h7 : |t| * ‖v‖ ≤ B + ‖x‖ := by
      have h8 : ‖t • v‖ = |t| * ‖v‖ := by simp [norm_smul]
      rw [h8] at h4
      exact h4
    have h9 : |t| ≤ C := by
      dsimp only [C]
      calc
        |t| = (|t| * ‖v‖) / ‖v‖ := by field_simp [hnv']
        _ ≤ ((B + ‖x‖) / ‖v‖) := by gcongr
    have h10 : dist t (0 : ℝ) < C + 1 := by
      rw [Real.dist_eq]
      calc
        |t - 0| = |t| := by ring_nf
        _ ≤ C := h9
        _ < C + 1 := by linarith
    exact h10
  have h_ball_bdd : Bornology.IsBounded (Metric.ball (0 : ℝ) (C + 1)) := Metric.isBounded_ball
  have hT_bdd : Bornology.IsBounded T := Bornology.IsBounded.subset h_ball_bdd hT_subset
  have hT_compact : IsCompact T := Metric.isCompact_of_isClosed_isBounded hT_closed hT_bdd
  have h2 : ∃ ε > 0, Metric.ball x ε ⊆ interior s := Metric.isOpen_iff.mp isOpen_interior x hx
  rcases h2 with ⟨ε, hε_pos, hε_subset_interior⟩
  have hε_subset : Metric.ball x ε ⊆ s := by
    calc
      Metric.ball x ε ⊆ interior s := hε_subset_interior
      _ ⊆ s := interior_subset
  let δ : ℝ := ε / ‖v‖
  have hδ_pos : 0 < δ := by positivity
  have hδ_mul : δ * ‖v‖ = ε := by
    dsimp only [δ]
    field_simp [hnv']
  have h_ball : ∀ (t : ℝ), |t| < δ → g t ∈ s := by
    intro t ht
    have h10 : ‖g t - x‖ < ε := by
      have h11 : g t - x = t • v := by simp [g]
      rw [h11]
      have h12 : ‖t • v‖ = |t| * ‖v‖ := by simp [norm_smul]
      rw [h12]
      calc
        |t| * ‖v‖ < δ * ‖v‖ := by gcongr
        _ = ε := hδ_mul
    have h14 : g t ∈ Metric.ball x ε := by
      have h : ‖g t - x‖ < ε := h10
      exact mem_ball_iff_norm.mpr h
    exact hε_subset h14
  have h0_in_T : (0 : ℝ) ∈ T := by
    have h15 : g 0 = x := by simp [g]
    have h16 : g 0 ∈ s := by
      rw [h15]
      exact interior_subset hx
    exact h16
  have hT_nonempty : T.Nonempty := ⟨0, h0_in_T⟩
  have h1_pos : 0 < δ / 2 := by positivity
  have h_abs1 : |(δ / 2 : ℝ)| = δ / 2 := abs_of_pos h1_pos
  have hδ2_in_T : δ / 2 ∈ T := h_ball (δ / 2) (by rw [h_abs1] ; linarith)
  have h1_neg : -(δ / 2 : ℝ) < 0 := by linarith
  have h_abs2 : |(-(δ / 2 : ℝ))| = δ / 2 := by
    rw [abs_neg, h_abs1]
  have h_negδ2_in_T : - (δ / 2) ∈ T := h_ball (-(δ / 2)) (by rw [h_abs2] ; linarith)
  set tmax : ℝ := sSup T with htmax_def
  set tmin : ℝ := sInf T with htmin_def
  have h_bdd_above : BddAbove T := hT_compact.bddAbove
  have h_bdd_below : BddBelow T := hT_compact.bddBelow
  have h_tmax_in_T : tmax ∈ T := hT_compact.sSup_mem hT_nonempty
  have h_tmin_in_T : tmin ∈ T := hT_compact.sInf_mem hT_nonempty
  have h_tmax_upper : ∀ t ∈ T, t ≤ tmax := fun t ht ↦ le_csSup h_bdd_above ht
  have h_tmin_lower : ∀ t ∈ T, tmin ≤ t := fun t ht ↦ csInf_le h_bdd_below ht
  have h_tmax_pos : 0 < tmax := by
    have h17 : δ / 2 ∈ T := hδ2_in_T
    have h18 : δ / 2 ≤ tmax := h_tmax_upper (δ / 2) h17
    linarith
  have h_tmin_neg : tmin < 0 := by
    have h19 : -(δ / 2) ∈ T := h_negδ2_in_T
    have h20 : tmin ≤ -(δ / 2) := h_tmin_lower (-(δ / 2)) h19
    linarith
  set a : E := g tmax with ha_def
  set b : E := g tmin with hb_def
  have ha_in_s : a ∈ s := h_tmax_in_T
  have hb_in_s : b ∈ s := h_tmin_in_T
  have ha_not_interior : a ∉ interior s := by
    by_contra h
    have h21 : ∃ ε' > 0, Metric.ball a ε' ⊆ interior s := Metric.isOpen_iff.mp isOpen_interior a h
    rcases h21 with ⟨ε', hε'_pos, hε'_subset_interior⟩
    have hε'_subset : Metric.ball a ε' ⊆ s := by
      calc
        Metric.ball a ε' ⊆ interior s := hε'_subset_interior
        _ ⊆ s := interior_subset
    let δ' : ℝ := ε' / ‖v‖
    have hδ'_pos : 0 < δ' := by positivity
    have hδ'_mul : δ' * ‖v‖ = ε' := by
      dsimp only [δ']
      field_simp [hnv']
    set t' : ℝ := δ' / 2 with ht'_def
    have ht'_pos : 0 < t' := by positivity
    have hlt : t' < δ' := by linarith [ht'_def]
    have h22 : ‖(t' • v)‖ < ε' := by
      have h23 : ‖t' • v‖ = |t'| * ‖v‖ := by simp [norm_smul]
      rw [h23, abs_of_pos ht'_pos]
      calc
        t' * ‖v‖ < δ' * ‖v‖ := by gcongr
        _ = ε' := hδ'_mul
    have h25 : a + t' • v ∈ Metric.ball a ε' := by
      have h : ‖(a + t' • v) - a‖ < ε' := by simpa using h22
      simpa [Metric.mem_ball, dist_eq_norm] using h
    have h26 : a + t' • v ∈ s := hε'_subset h25
    have h271 : g (tmax + t') = x + (tmax + t') • v := by rfl
    have h272 : x + (tmax + t') • v = (x + tmax • v) + t' • v := by
      simp [add_smul]
      abel
    have h273 : (x + tmax • v) + t' • v = a + t' • v := by
      have h : a = x + tmax • v := by simp [a, g, ha_def]
      rw [h]
    have h27 : g (tmax + t') = a + t' • v := by
      rw [h271, h272, h273]
    have h28 : tmax + t' ∈ T := by
      have h : g (tmax + t') ∈ s := by rw [h27] ; exact h26
      exact h
    have h29 : tmax + t' ≤ tmax := h_tmax_upper (tmax + t') h28
    linarith
  have hb_not_interior : b ∉ interior s := by
    by_contra h
    have h21 : ∃ ε' > 0, Metric.ball b ε' ⊆ interior s := Metric.isOpen_iff.mp isOpen_interior b h
    rcases h21 with ⟨ε', hε'_pos, hε'_subset_interior⟩
    have hε'_subset : Metric.ball b ε' ⊆ s := by
      calc
        Metric.ball b ε' ⊆ interior s := hε'_subset_interior
        _ ⊆ s := interior_subset
    let δ' : ℝ := ε' / ‖v‖
    have hδ'_pos : 0 < δ' := by positivity
    have hδ'_mul : δ' * ‖v‖ = ε' := by
      dsimp only [δ']
      field_simp [hnv']
    set t' : ℝ := δ' / 2 with ht'_def
    have ht'_pos : 0 < t' := by positivity
    have hlt : t' < δ' := by linarith [ht'_def]
    have h22 : ‖((-t') • v)‖ < ε' := by
      have h23 : ‖(-t') • v‖ = |(-t')| * ‖v‖ := by simp [norm_smul]
      rw [h23]
      have h24 : |(-t')| = t' := by
        rw [abs_neg, abs_of_pos ht'_pos]
      rw [h24]
      calc
        t' * ‖v‖ < δ' * ‖v‖ := by gcongr
        _ = ε' := hδ'_mul
    have h25 : b + (-t') • v ∈ Metric.ball b ε' := by
      have h : ‖(b + (-t') • v) - b‖ < ε' := by simpa using h22
      simpa [Metric.mem_ball, dist_eq_norm] using h
    have h26 : b + (-t') • v ∈ s := hε'_subset h25
    have h271 : g (tmin - t') = x + (tmin - t') • v := by rfl
    have h272 : x + (tmin - t') • v = (x + tmin • v) + (-t') • v := by
      simp [sub_smul]
      abel
    have h273 : (x + tmin • v) + (-t') • v = b + (-t') • v := by
      have h : b = x + tmin • v := by simp [b, g, hb_def]
      rw [h]
    have h27 : g (tmin - t') = b + (-t') • v := by
      rw [h271, h272, h273]
    have h28 : tmin - t' ∈ T := by
      have h : g (tmin - t') ∈ s := by rw [h27] ; exact h26
      exact h
    have h29 : tmin ≤ tmin - t' := h_tmin_lower (tmin - t') h28
    linarith
  have h_closure_s : closure s = s := hsc.closure_eq
  have ha_frontier : a ∈ frontier s := by
    have h : a ∈ closure s ∧ a ∉ interior s := by
      constructor
      · rw [h_closure_s] ; exact ha_in_s
      · exact ha_not_interior
    exact h
  have hb_frontier : b ∈ frontier s := by
    have h : b ∈ closure s ∧ b ∉ interior s := by
      constructor
      · rw [h_closure_s] ; exact hb_in_s
      · exact hb_not_interior
    exact h
  have h_pos2 : 0 < tmax - tmin := by linarith
  have h_pos2' : (tmax - tmin) ≠ 0 := by linarith
  have h_pos3 : 0 < -tmin := by linarith
  set r : ℝ := (-tmin) / (tmax - tmin) with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def] ; positivity
  have hr_lt_one : r < 1 := by
    rw [hr_def]
    have h : (-tmin) < tmax - tmin := by linarith
    have h' : (-tmin) / (tmax - tmin) < (tmax - tmin) / (tmax - tmin) := by
      gcongr
    have h'' : (tmax - tmin) / (tmax - tmin) = 1 := by
      field_simp [h_pos2']
    rw [h''] at h'
    exact h'
  have ha_eq : a = x + tmax • v := by simp [a, g, ha_def]
  have hb_eq : b = x + tmin • v := by simp [b, g, hb_def]
  have h31 : r * tmax + (1 - r) * tmin = 0 := by
    rw [hr_def]
    field_simp [h_pos2']
    ring
  have h_sum_coeff : r + (1 - r) = 1 := by linarith
  have h_main : r • a + (1 - r) • b = x := by
    rw [ha_eq, hb_eq]
    have h30 : r • (x + tmax • v) + (1 - r) • (x + tmin • v)
        = (r + (1 - r)) • x + (r * tmax + (1 - r) * tmin) • v := by
      calc
        r • (x + tmax • v) + (1 - r) • (x + tmin • v)
          = r • x + r • (tmax • v) + ((1 - r) • x + (1 - r) • (tmin • v)) := by
            rw [smul_add, smul_add]
        _ = r • x + (r * tmax) • v + ((1 - r) • x + ((1 - r) * tmin) • v) := by
            rw [smul_smul, smul_smul]
        _ = (r • x + (1 - r) • x) + ((r * tmax) • v + ((1 - r) * tmin) • v) := by abel
        _ = (r + (1 - r)) • x + ((r * tmax + (1 - r) * tmin) • v) := by
            rw [add_smul, add_smul]
    rw [h30, h_sum_coeff, h31]
    simp
  exact ⟨a, b, r, ha_frontier, hb_frontier, hr_pos, hr_lt_one, h_main.symm⟩

end BoundaryDecomposition

namespace Minkowski
open SupportingHyperplane (supporting_hyperplane_boundary)
open Face (max_linear_preimage_is_face)
open ExtremeFace (extreme_points_face_subset)
open BoundaryDecomposition (interior_point_convex_comb_boundary)

lemma extreme_point_affine_map {E₁ E₂ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [AddCommGroup E₂] [Module ℝ E₂]
  (L : E₁ →ₗ[ℝ] E₂) (hL_inj : Function.Injective L) (z₀ : E₂)
  (s₂ : Set E₂) (_hs₂conv : Convex ℝ s₂)
  (h_affine : ∀ (z : E₂), z ∈ s₂ → ∃ (y : E₁), z₀ + L y = z) :
  let φ : E₁ → E₂ := fun y ↦ z₀ + L y
  let s₁ : Set E₁ := φ ⁻¹' s₂
  ∀ (y₀ : E₁), y₀ ∈ s₁.extremePoints ℝ → φ y₀ ∈ s₂.extremePoints ℝ := by
  let φ : E₁ → E₂ := fun y ↦ z₀ + L y
  let s₁ : Set E₁ := φ ⁻¹' s₂
  have h_claim : ∀ (y₀ : E₁), y₀ ∈ s₁.extremePoints ℝ → φ y₀ ∈ s₂.extremePoints ℝ := by
    intro y₀ hy₀
    have h_y₀_in_s₁ : y₀ ∈ s₁ := hy₀.1
    have h1 : φ y₀ ∈ s₂ := h_y₀_in_s₁
    have h_forall : ∀ (x₁ : E₂), x₁ ∈ s₂ → ∀ (x₂ : E₂), x₂ ∈ s₂ → φ y₀ ∈ openSegment ℝ x₁ x₂ → x₁ = φ y₀ := by
      intro x₁ hx₁ x₂ hx₂ h_in_openSegment
      rcases h_in_openSegment with ⟨r, r', hr_pos, hr'_pos, h_add, h_eq⟩
      have h_r'_eq : r' = 1 - r := by linarith
      have hr_lt_one : r < 1 := by
        have h : r' > 0 := hr'_pos
        linarith
      have hx1' : ∃ (x₁' : E₁), φ x₁' = x₁ := h_affine x₁ hx₁
      have hx2' : ∃ (x₂' : E₁), φ x₂' = x₂ := h_affine x₂ hx₂
      rcases hx1' with ⟨x₁', hx1_eq⟩
      rcases hx2' with ⟨x₂', hx2_eq⟩
      have hx1'_in_s₁ : x₁' ∈ s₁ := by
        have h : φ x₁' ∈ s₂ := by rw [hx1_eq] ; exact hx₁
        exact h
      have hx2'_in_s₁ : x₂' ∈ s₁ := by
        have h : φ x₂' ∈ s₂ := by rw [hx2_eq] ; exact hx₂
        exact h
      have h_eq2 : r • x₁ + r' • x₂ = φ y₀ := h_eq
      rw [h_r'_eq] at h_eq2
      have h_eq3 : r • (φ x₁') + (1 - r) • (φ x₂') = r • x₁ + (1 - r) • x₂ := by
        rw [hx1_eq, hx2_eq]
      have h4 : φ (r • x₁' + (1 - r) • x₂') = r • (φ x₁') + (1 - r) • (φ x₂') := by
        simp only [φ, L.map_smul, L.map_add]
        have h : r • (z₀ + L x₁') + (1 - r) • (z₀ + L x₂')
            = (r • z₀ + (1 - r) • z₀) + (r • L x₁' + (1 - r) • L x₂') := by
          calc
            r • (z₀ + L x₁') + (1 - r) • (z₀ + L x₂')
              = (r • z₀ + r • (L x₁')) + ((1 - r) • z₀ + (1 - r) • (L x₂')) := by
                simp [smul_add]
            _ = (r • z₀ + (1 - r) • z₀) + (r • (L x₁') + (1 - r) • (L x₂')) := by abel
        rw [h]
        have h5 : (r • z₀ + (1 - r) • z₀) = (1 : ℝ) • z₀ := by
          have h6 : r + (1 - r) = 1 := by ring
          calc
            r • z₀ + (1 - r) • z₀ = (r + (1 - r)) • z₀ := by rw [add_smul]
            _ = (1 : ℝ) • z₀ := by rw [h6]
        rw [h5]
        ; simp
      have h_eq5 : φ (r • x₁' + (1 - r) • x₂') = φ y₀ := by
        calc
          φ (r • x₁' + (1 - r) • x₂')
            = r • (φ x₁') + (1 - r) • (φ x₂') := h4
          _ = r • x₁ + (1 - r) • x₂ := h_eq3
          _ = φ y₀ := h_eq2
      have h_eq6 : y₀ = r • x₁' + (1 - r) • x₂' := by
        have h : L y₀ = L (r • x₁' + (1 - r) • x₂') := by
          simpa [φ] using congr_arg (fun z : E₂ ↦ z - z₀) h_eq5.symm
        exact hL_inj h
      have h_in_openSegment' : y₀ ∈ openSegment ℝ x₁' x₂' := by
        refine ⟨r, 1 - r, hr_pos, by linarith, by linarith, h_eq6.symm⟩
      have h_x1'_eq : x₁' = y₀ := hy₀.2 hx1'_in_s₁ hx2'_in_s₁ h_in_openSegment'
      have h_goal : x₁ = φ y₀ := by
        calc
          x₁ = φ x₁' := hx1_eq.symm
          _ = φ y₀ := by rw [h_x1'_eq]
      exact h_goal
    have h_goal : φ y₀ ∈ s₂.extremePoints ℝ := by
      exact ⟨h1, h_forall⟩
    exact h_goal
  exact h_claim

lemma convexHull_affine_image {E₁ E₂ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [AddCommGroup E₂] [Module ℝ E₂]
  (L : E₁ →ₗ[ℝ] E₂) (z₀ : E₂) (A : Set E₁) (y : E₁) (hy : y ∈ convexHull ℝ A) :
  z₀ + L y ∈ convexHull ℝ ((fun x : E₁ ↦ z₀ + L x) '' A) := by
  let ψ : E₁ → E₂ := fun x ↦ z₀ + L x
  let ψ_affine : E₁ →ᵃ[ℝ] E₂ :=
    { toFun := ψ
      linear := L
      map_vadd' := by
        intro p v
        simp [ψ, vadd_eq_add]
        abel
        }
  have h1 : ∀ (S : Set E₂), Convex ℝ S → (ψ '' A ⊆ S) → ψ '' (convexHull ℝ A) ⊆ S := by
    intro S hS h2
    have h3 : convexHull ℝ A ⊆ ψ ⁻¹' S := by
      apply convexHull_min
      · intro z hz
        exact h2 (mem_image_of_mem ψ hz)
      · exact hS.affine_preimage ψ_affine
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    have h4 : w ∈ convexHull ℝ A := hw
    have h5 : w ∈ ψ ⁻¹' S := h3 h4
    exact h5
  have h_main : ψ '' (convexHull ℝ A) ⊆ convexHull ℝ (ψ '' A) := by
    exact h1 (convexHull ℝ (ψ '' A)) (convex_convexHull ℝ (ψ '' A)) (subset_convexHull ℝ (ψ '' A))
  have h2 : ψ y ∈ ψ '' (convexHull ℝ A) := mem_image_of_mem ψ hy
  exact h_main h2

lemma convexHull_extremePoints_subset_by_finrank_induction :
  ∀ (n : ℕ), ∀ (E : Type _) (_inst1 : NormedAddCommGroup E) (_inst2 : NormedSpace ℝ E)
    (_inst3 : FiniteDimensional ℝ E), (Module.finrank ℝ E = n) →
    ∀ (s : Set E), IsCompact s → Convex ℝ s → s ⊆ convexHull ℝ (s.extremePoints ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E _inst1 _inst2 _inst3 h_fin s hscomp hsconv
    have hS_closed : IsClosed s := hscomp.isClosed
    have h_closure_s : closure s = s := hS_closed.closure_eq
    have h_main_goal : s ⊆ convexHull ℝ (s.extremePoints ℝ) := by
      by_cases h_n : n = 0
      ·
        have hE : Module.finrank ℝ E = 0 := by rw [h_fin] ; exact h_n
        have h_subsingleton : Subsingleton E := by
          rw [Module.finrank_zero_iff] at hE
          exact hE
        letI : Subsingleton E := h_subsingleton
        intro x hx
        have h_x_extreme : x ∈ s.extremePoints ℝ := by
          have h1 : x ∈ s := hx
          refine ⟨h1, fun x₁ hx₁ x₂ hx₂ _ => ?_⟩
          exact Subsingleton.elim x₁ x
        exact subset_convexHull ℝ (s.extremePoints ℝ) h_x_extreme
      ·
        have h_n_pos : 0 < n := Nat.pos_of_ne_zero h_n
        have h_dim_pos : 0 < Module.finrank ℝ E := by
          rw [h_fin] ; exact h_n_pos
        have h_frontier_goal : ∀ (z : E), z ∈ frontier s → z ∈ convexHull ℝ (s.extremePoints ℝ) := by
          intro z hz_front
          have hz_in_s : z ∈ s := by
            have h1 : z ∈ closure s := hz_front.1
            rw [h_closure_s] at h1
            exact h1
          rcases supporting_hyperplane_boundary hscomp hsconv hz_front with ⟨f, hf_ne_zero, hM⟩
          let M : ℝ := f z
          let F : Set E := {y ∈ s | f y = M}
          have hF_conv : Convex ℝ F := (max_linear_preimage_is_face hsconv (f : E →ₗ[ℝ] ℝ) M hM).1
          have hF_subset : F ⊆ s := (max_linear_preimage_is_face hsconv (f : E →ₗ[ℝ] ℝ) M hM).2.1
          have hF_face : ∀ x', x' ∈ F → ∀ a b, a ∈ s → b ∈ s → ∀ (r : ℝ), 0 < r → r < 1 → x' = r • a + (1 - r) • b → a ∈ F ∧ b ∈ F :=
            (max_linear_preimage_is_face hsconv (f : E →ₗ[ℝ] ℝ) M hM).2.2
          have hF_compact : IsCompact F := by
            have h1 : IsClosed {y : E | f y = M} := by
              apply isClosed_eq f.continuous continuous_const
            exact hscomp.inter_right h1
          have hz_F : z ∈ F := ⟨hz_in_s, rfl⟩
          let H' : Submodule ℝ E := LinearMap.ker (f : E →ₗ[ℝ] ℝ)
          have h_exists : ∃ (x₀ : E), f x₀ ≠ 0 := by
            by_contra h
            push Not at h
            have h9 : f = 0 := by
              ext x
              exact h x
            exact hf_ne_zero h9
          rcases h_exists with ⟨x₀, hx₀⟩
          have h_surj : Function.Surjective (f : E →ₗ[ℝ] ℝ) := by
            intro t
            use (t / f x₀) • x₀
            have h_calc : f ((t / f x₀) • x₀) = t := by
              calc
                f ((t / f x₀) • x₀) = (t / f x₀) • (f x₀) := by rw [f.map_smul]
                _ = (t / f x₀) * (f x₀) := by exact smul_eq_mul (t / f x₀) (f x₀)
                _ = t := by
                  field_simp [hx₀]
            exact h_calc
          have h_range_f : LinearMap.range (f : E →ₗ[ℝ] ℝ) = ⊤ := by
            rwa [LinearMap.range_eq_top]
          have h_finrank_eq : Module.finrank ℝ (LinearMap.range (f : E →ₗ[ℝ] ℝ)) + Module.finrank ℝ H' = Module.finrank ℝ E :=
            LinearMap.finrank_range_add_finrank_ker (f : E →ₗ[ℝ] ℝ)
          have h_finrank_range : Module.finrank ℝ (LinearMap.range (f : E →ₗ[ℝ] ℝ)) = 1 := by
            rw [h_range_f] ; simp
          have h_finrank_H'_lt : Module.finrank ℝ H' < Module.finrank ℝ E := by
            rw [← h_finrank_eq, h_finrank_range] ; omega
          let m : ℕ := Module.finrank ℝ H'
          have hmltn : m < n := by
            rw [h_fin] at * ; exact h_finrank_H'_lt
          let L : H' →ₗ[ℝ] E := Submodule.subtype H'
          have hL_inj : Function.Injective L := by exact Subtype.coe_injective
          let z₀ : E := z
          let φ : H' → E := fun y : H' ↦ z₀ + L y
          let ψ_affine : H' →ᵃ[ℝ] E :=
            { toFun := φ
              linear := L
              map_vadd' := by
                intro p v
                simp [φ, vadd_eq_add]
                abel }
          let s₁ : Set H' := φ ⁻¹' F
          have h_affine : ∀ (w : E), w ∈ F → ∃ (y : H'), φ y = w := by
            intro w hw
            have hz2 : f w = M := hw.2
            have h3 : f (w - z₀) = 0 := by
              rw [map_sub, hz2]
              simp [M, z₀]
            let y : H' := ⟨w - z₀, h3⟩
            refine ⟨y, ?_⟩
            simp [φ, L, y]
          have hs₁_conv : Convex ℝ s₁ := by
            exact hF_conv.affine_preimage ψ_affine
          have h_cont_φ : Continuous φ := by fun_prop
          have hF_closed : IsClosed F := hF_compact.isClosed
          have hs₁_closed : IsClosed s₁ := hF_closed.preimage h_cont_φ
          have hs_bounded : Bornology.IsBounded s := IsCompact.isBounded hscomp
          have hF_bounded : Bornology.IsBounded F := by
            exact Bornology.IsBounded.subset hs_bounded hF_subset
          have h1 : ∃ (C : ℝ), F ⊆ Metric.closedBall (0 : E) C := (Metric.isBounded_iff_subset_closedBall (0 : E)).mp hF_bounded
          rcases h1 with ⟨C, hC⟩
          have hC2 : ∀ (x : E), x ∈ F → ‖x‖ ≤ C := by
            intro x hx
            have h2 : x ∈ Metric.closedBall (0 : E) C := hC hx
            simp [Metric.mem_closedBall] at h2 ⊢
            exact h2
          let D : ℝ := C + ‖z₀‖
          have h_s₁_norm : ∀ (y : H'), y ∈ s₁ → ‖(y : E)‖ ≤ D := by
            intro y hy
            have h1 : φ y ∈ F := hy
            have h3 : ‖φ y‖ ≤ C := hC2 (φ y) h1
            have h4 : ‖L y‖ = ‖(φ y) - z₀‖ := by
              simp [φ]
            have h5 : ‖L y‖ ≤ ‖φ y‖ + ‖z₀‖ := by
              rw [h4]
              exact norm_sub_le _ _
            have h6 : ‖L y‖ ≤ D := by
              calc
                ‖L y‖ ≤ ‖φ y‖ + ‖z₀‖ := h5
                _ ≤ C + ‖z₀‖ := by linarith
                _ = D := by rfl
            change ‖L y‖ ≤ D
            exact h6
          have h_s₁_subset : s₁ ⊆ Metric.closedBall (0 : H') D := by
            intro y hy
            have h8 : ‖(y : E)‖ ≤ D := h_s₁_norm y hy
            have h9 : ‖y‖ ≤ D := by exact_mod_cast h8
            have h13 : dist y (0 : H') = ‖y‖ := dist_zero_right y
            have h14 : dist y (0 : H') ≤ D := by
              rw [h13]
              exact h9
            exact h14
          have h_ball_bounded : Bornology.IsBounded (Metric.closedBall (0 : H') D) := by
            exact Metric.isBounded_closedBall
          have hs₁_bounded : Bornology.IsBounded s₁ := h_ball_bounded.subset h_s₁_subset
          have hs₁_compact : IsCompact s₁ := Metric.isCompact_of_isClosed_isBounded hs₁_closed hs₁_bounded
          have ih_H' : s₁ ⊆ convexHull ℝ (s₁.extremePoints ℝ) := by
            exact ih m hmltn H' (inferInstance) (inferInstance) (inferInstance) rfl s₁ hs₁_compact hs₁_conv
          have h_exists_y1 : ∃ (y1 : H'), φ y1 = z := h_affine z hz_F
          rcases h_exists_y1 with ⟨y1, hy1_eq⟩
          have hy1_in_s₁ : y1 ∈ s₁ := by
            simpa [s₁] using hy1_eq ▸ hz_F
          have hy1_in_ch : y1 ∈ convexHull ℝ (s₁.extremePoints ℝ) := ih_H' hy1_in_s₁
          have h_image1 : ∀ (y0 : H'), y0 ∈ s₁.extremePoints ℝ → φ y0 ∈ F.extremePoints ℝ :=
            extreme_point_affine_map L hL_inj z₀ F hF_conv h_affine
          have h_image2 : (fun y0 : H' ↦ φ y0) '' (s₁.extremePoints ℝ) ⊆ F.extremePoints ℝ := by
            intro w hw
            rcases hw with ⟨y0, hy0, rfl⟩
            exact h_image1 y0 hy0
          have h_z_in1 : φ y1 ∈ convexHull ℝ ((fun y0 : H' ↦ φ y0) '' (s₁.extremePoints ℝ)) :=
            convexHull_affine_image L z₀ (s₁.extremePoints ℝ) y1 hy1_in_ch
          have h_z_in2 : φ y1 ∈ convexHull ℝ (F.extremePoints ℝ) := by
            apply convexHull_mono h_image2
            exact h_z_in1
          have hF_extreme_subset : F.extremePoints ℝ ⊆ s.extremePoints ℝ :=
            extreme_points_face_subset hsconv ⟨hF_conv, hF_subset, hF_face⟩
          have h_final : convexHull ℝ (F.extremePoints ℝ) ⊆ convexHull ℝ (s.extremePoints ℝ) :=
            convexHull_mono hF_extreme_subset
          have h_goal : φ y1 ∈ convexHull ℝ (s.extremePoints ℝ) := h_final h_z_in2
          have h_last : φ y1 = z := hy1_eq
          rw [h_last] at h_goal
          exact h_goal
        intro x hx
        by_cases hx_int : x ∈ interior s
        ·
          rcases interior_point_convex_comb_boundary hscomp hsconv h_dim_pos hx_int with ⟨a, b, r, ha_front, hb_front, hr_pos, hr_lt_one, h_eq⟩
          have h_a_goal : a ∈ convexHull ℝ (s.extremePoints ℝ) := h_frontier_goal a ha_front
          have h_b_goal : b ∈ convexHull ℝ (s.extremePoints ℝ) := h_frontier_goal b hb_front
          have h_conv : Convex ℝ (convexHull ℝ (s.extremePoints ℝ)) := convex_convexHull ℝ (s.extremePoints ℝ)
          have hr_nonneg : 0 ≤ r := by linarith
          have h1mr_nonneg : 0 ≤ 1 - r := by linarith
          have hr_add : r + (1 - r) = 1 := by ring
          have h : r • a + (1 - r) • b ∈ convexHull ℝ (s.extremePoints ℝ) :=
            h_conv h_a_goal h_b_goal hr_nonneg h1mr_nonneg hr_add
          have h9 : x = r • a + (1 - r) • b := h_eq
          rw [h9]
          exact h
        ·
          have h1 : x ∈ closure s := by
            rw [h_closure_s] ; exact hx
          have h_x_frontier : x ∈ frontier s := ⟨h1, hx_int⟩
          exact h_frontier_goal x h_x_frontier
    exact h_main_goal

theorem minkowski_theorem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s) :
  s = convexHull ℝ (s.extremePoints ℝ) := by

  have h_aux : ∀ (E' : Type _) [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'],
    ∀ (s' : Set E'), IsCompact s' → Convex ℝ s' → s' ⊆ convexHull ℝ (s'.extremePoints ℝ) := by
    intro E' _i1 _i2 _i3 s' hs'_comp hs'_conv
    let n : ℕ := Module.finrank ℝ E'
    exact convexHull_extremePoints_subset_by_finrank_induction n E' _i1 _i2 _i3 rfl s' hs'_comp hs'_conv
  have h_main : s ⊆ convexHull ℝ (s.extremePoints ℝ) := h_aux E s hscomp hsconv
  have h2 : convexHull ℝ (s.extremePoints ℝ) ⊆ s := by
    have h3 : s.extremePoints ℝ ⊆ s := by
      intro x hx
      exact hx.1
    exact convexHull_min h3 hsconv
  exact Set.Subset.antisymm h_main h2

end Minkowski

namespace CaratheodoryFinite
open SupportingHyperplane (supporting_hyperplane_boundary)
open Face (max_linear_preimage_is_face)
open ExtremeFace (extreme_points_face_subset)
open BoundaryDecomposition (interior_point_convex_comb_boundary)
open Minkowski (minkowski_theorem)

theorem caratheodory_finite_convexHull {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {A : Set E} {x : E} (hx : x ∈ convexHull ℝ A) :
  ∃ (t : Finset E), (↑t : Set E) ⊆ A ∧ t.card ≤ Module.finrank ℝ E + 1 ∧ x ∈ convexHull ℝ (↑t : Set E) := by

  let t : Finset E := Caratheodory.minCardFinsetOfMemConvexHull hx
  have h1 : (↑t : Set E) ⊆ A := Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  have h2 : x ∈ convexHull ℝ (↑t : Set E) := Caratheodory.mem_minCardFinsetOfMemConvexHull hx
  have h3 : AffineIndependent ℝ ((↑) : (↑t : Type _) → E) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  let V : Submodule ℝ E := vectorSpan ℝ (Set.range (Subtype.val : (↑t : Type _) → E))
  have hfin : Module.finrank ℝ V ≤ Module.finrank ℝ E := by
    exact Submodule.finrank_le V
  have h5 : Fintype.card (↑t) ≤ Module.finrank ℝ V + 1 := AffineIndependent.card_le_finrank_succ h3
  have h6 : Fintype.card (↑t) ≤ Module.finrank ℝ E + 1 := by
    linarith
  have h4 : t.card ≤ Module.finrank ℝ E + 1 := by
    simpa using h6
  exact ⟨t, h1, h4, h2⟩

end CaratheodoryFinite

section
open SupportingHyperplane (supporting_hyperplane_boundary)
open Face (max_linear_preimage_is_face)
open ExtremeFace (extreme_points_face_subset)
open BoundaryDecomposition (interior_point_convex_comb_boundary)
open Minkowski (minkowski_theorem)
open CaratheodoryFinite (caratheodory_finite_convexHull)

theorem mem_convexHull_finset_extremePoints_of_mem_compact_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} {x : E}
    (hscomp : IsCompact s)
    (hsconv : Convex ℝ s)
    (hx : x ∈ s) :
    ∃ t : Finset E,
      (↑t : Set E) ⊆ s.extremePoints ℝ ∧
      t.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑t : Set E) := by

  have h1 : x ∈ convexHull ℝ (s.extremePoints ℝ) := by
    have h2 : s = convexHull ℝ (s.extremePoints ℝ) := minkowski_theorem hscomp hsconv
    rw [h2] at hx
    exact hx
  exact caratheodory_finite_convexHull (hx := h1)

end

end JohnEllipsoid.MinkowskiCaratheodory
