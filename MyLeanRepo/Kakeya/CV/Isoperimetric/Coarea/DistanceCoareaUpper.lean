import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.DistanceGradient
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.LocalLipschitzCoarea
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaInequalityGlobalization
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Tactic

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ} [Nonempty (Fin n)]

/-!
# Distance Function Coarea Formula

Step 1: Uniqueness of nearest point
Step 2: Gradient continuity relative to differentiability set
-/

-- ============================================================================
-- Step 1: Uniqueness of nearest point at differentiability points
-- ============================================================================

/-- If a continuous linear functional `f'` on a real inner product space has
norm 1 and `f' v = 1` for some unit vector `v`, then `f' w = inner w v`. -/
lemma norm_one_functional_riesz {v : E n} (hv : ‖v‖ = 1)
    (f' : E n →L[ℝ] ℝ) (hnorm : ‖f'‖ = 1) (hattain : f' v = 1) :
    ∀ (w : E n), f' w = inner ℝ w v := by
  let u : E n := (InnerProductSpace.toDual ℝ (E n)).symm f'
  have h_dual : (InnerProductSpace.toDual ℝ (E n)) u = f' :=
    (InnerProductSpace.toDual ℝ (E n)).apply_symm_apply f'
  have h1 : ∀ w, f' w = inner ℝ u w := by
    intro w
    have h2 : (InnerProductSpace.toDual ℝ (E n)) u w = inner ℝ u w :=
      InnerProductSpace.toDual_apply_apply (𝕜 := ℝ)
    rw [←h_dual] <;> exact h2
  have h2 : ‖u‖ = ‖f'‖ := (InnerProductSpace.toDual ℝ (E n)).symm.norm_map f'
  have h3 : ‖u‖ = 1 := by rw [h2, hnorm]
  have h4 : inner ℝ u v = 1 := by
    have h5 : f' v = inner ℝ u v := h1 v
    rw [h5] at hattain
    exact hattain
  have h7 : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * inner ℝ u v := by
    have h8 : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u v + ‖v‖ ^ 2 := by
      simpa [real_inner_comm] using norm_sub_sq_real u v
    linarith
  have h9 : ‖u - v‖ ^ 2 = 0 := by
    rw [h7, h3, hv, h4] <;> norm_num
  have h10 : u = v := by
    have h11 : ‖u - v‖ = 0 := by simpa [pow_eq_zero_iff] using h9
    have h12 : u - v = 0 := norm_eq_zero.mp h11
    exact sub_eq_zero.mp h12
  intro w
  have h12 : f' w = inner ℝ u w := h1 w
  rw [h12, h10]
  have h13 : inner ℝ v w = inner ℝ w v := (real_inner_comm v w).symm
  exact h13

/-- At a differentiability point x of d with d(x)>0, if y is a nearest point,
then `fderiv d x(v) = 1` where `v = (x-y)/d(x)`. -/
lemma fderiv_infDist_at_nearest_point {C : Set (E n)} (hC : IsClosed C)
    (hne : C.Nonempty) {x : E n}
    (hdiff : DifferentiableAt ℝ (fun x => infDist x C) x)
    (hpos : 0 < infDist x C) {y : E n} (hyC : y ∈ C)
    (hydist : dist x y = infDist x C) :
    (fderiv ℝ (fun x => infDist x C) x) ((infDist x C)⁻¹ • (x - y)) = 1 := by
  let d : E n → ℝ := fun x => infDist x C
  let f' := fderiv ℝ d x
  set v : E n := (d x)⁻¹ • (x - y) with hv_def
  have hv_norm : ‖v‖ = 1 := by
    have h : ‖v‖ = |(d x)⁻¹| * ‖x - y‖ := by
      rw [hv_def, norm_smul] <;> rfl
    rw [h]
    have h3 : ‖x - y‖ = d x := by simpa [dist_eq_norm] using hydist
    rw [h3]
    have h4 : 0 < d x := hpos
    have h5 : |(d x)⁻¹| = (d x)⁻¹ := abs_of_pos (inv_pos.mpr h4)
    rw [h5]
    field_simp [h4.ne'] <;> ring
  have h3 : (d x) • v = x - y := by
    rw [hv_def]
    have h6 : (d x) • ((d x)⁻¹ • (x - y)) = ((d x) * (d x)⁻¹) • (x - y) := by rw [smul_smul]
    rw [h6]
    have h7 : (d x) * (d x)⁻¹ = 1 := by
      have h8 : d x ≠ 0 := hpos.ne'
      field_simp [h8] <;> exact h8
    rw [h7, one_smul]
  have h1 : ∀ (s : ℝ), 0 < s → s < d x → d (x - s • v) ≤ d x - s := by
    intro s hs hlt
    have h4 : (x - s • v) - y = (d x - s) • v := by
      calc
        (x - s • v) - y = (x - y) - s • v := by abel
        _ = (d x) • v - s • v := by rw [←h3]
        _ = (d x - s) • v := by rw [←sub_smul]
    have h2 : ‖(x - s • v) - y‖ = d x - s := by
      rw [h4, norm_smul, Real.norm_eq_abs]
      have h6 : 0 ≤ d x - s := by linarith
      rw [abs_of_nonneg h6, hv_norm] <;> linarith
    have h5 : d (x - s • v) ≤ ‖(x - s • v) - y‖ := infDist_le_dist_of_mem hyC
    rw [h2] at h5
    exact h5
  let g : ℝ → E n := fun s => x - s • v
  have hg_deriv : HasDerivAt g (-v) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s • v) v 0 := by
      have h2 : HasDerivAt (fun s : ℝ => s • v) ((1 : ℝ) • v) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const v
      have h3 : (1 : ℝ) • v = v := one_smul ℝ v
      rw [h3] at h2
      exact h2
    exact h1.const_sub x
  have hg : HasFDerivAt g (ContinuousLinearMap.toSpanSingleton ℝ (-v)) 0 :=
    hg_deriv.hasFDerivAt
  have h_fderiv : HasFDerivAt d f' x := hdiff.hasFDerivAt
  have h_g0 : g 0 = x := by simp [g]
  have h_fderiv' : HasFDerivAt d f' (g 0) := by
    rw [h_g0] <;> exact h_fderiv
  have h_comp_fderiv : HasFDerivAt (d ∘ g)
      (f'.comp (ContinuousLinearMap.toSpanSingleton ℝ (-v))) 0 :=
    HasFDerivAt.comp (x := 0) h_fderiv' hg
  have h_comp : HasDerivAt (d ∘ g)
      ((f'.comp (ContinuousLinearMap.toSpanSingleton ℝ (-v))) 1) 0 :=
    h_comp_fderiv.hasDerivAt
  have h_val : (f'.comp (ContinuousLinearMap.toSpanSingleton ℝ (-v))) 1 = f' (-v) := by
    simp [f'] <;> rfl
  rw [h_val] at h_comp
  have h_neg : f' (-v) = -f' v := by exact map_neg f' v
  rw [h_neg] at h_comp
  have h6 : ∀ (s : ℝ), 0 < s → s < d x →
      ((d ∘ g) s - (d ∘ g) 0) / s ≤ -1 := by
    intro s hs hlt
    have h7 : d (g s) ≤ d x - s := h1 s hs hlt
    have h8 : (d (g s) - d x) / s ≤ -1 := by
      have h9 : (d (g s) - d x) / s ≤ ((d x - s) - d x) / s := by gcongr
      have h10 : ((d x - s) - d x) / s = -1 := by
        field_simp [hs.ne'] <;> linarith
      rw [h10] at h9
      exact h9
    simpa [g] using h8
  have h_nhds : Set.Ioo (0 : ℝ) (d x) ∈ nhdsWithin 0 (Set.Ioi 0) := by
    apply mem_nhdsWithin.mpr
    refine ⟨Set.Iio (d x), isOpen_Iio, ?_, ?_⟩
    · exact hpos
    · intro y hy
      exact ⟨hy.2, hy.1⟩
  have h_event : ∀ᶠ (s : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      ((d ∘ g) s - (d ∘ g) 0) / s ≤ -1 := by
    filter_upwards [h_nhds] with s hs
    exact h6 s hs.1 hs.2
  have h_tendsto1 : Tendsto (slope (d ∘ g) 0)
      (nhdsWithin 0 {0}ᶜ) (nhds (-f' v)) :=
    h_comp.tendsto_slope
  have h_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin (0 : ℝ) {0}ᶜ := by
    apply nhdsWithin_mono
    intro s hs
    exact ne_of_gt hs
  have h_tendsto : Tendsto (slope (d ∘ g) 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-f' v)) :=
    h_tendsto1.mono_left h_le_nhds
  have h_slope_eq : ∀ (s : ℝ), slope (d ∘ g) 0 s = ((d ∘ g) s - (d ∘ g) 0) / s := by
    intro s
    simp [slope] <;> ring
  have h_event' : ∀ᶠ (s : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      slope (d ∘ g) 0 s ≤ -1 := by
    filter_upwards [h_event] with s hs
    rw [h_slope_eq s]
    exact hs
  have h11 : -f' v ≤ -1 := le_of_tendsto h_tendsto h_event'
  have h12 : 1 ≤ f' v := by linarith
  have h13 : |f' v| ≤ ‖f'‖ * ‖v‖ := f'.le_opNorm v
  have hnorm1 : ‖f'‖ = 1 := norm_fderiv_infDist_eq_one hC hne hdiff hpos
  rw [hnorm1, hv_norm] at h13
  have h14 : |f' v| ≤ 1 := by simpa using h13
  have h15 : 0 ≤ f' v := by linarith
  have h16 : |f' v| = f' v := abs_of_nonneg h15
  rw [h16] at h14
  have h17 : f' v ≤ 1 := by linarith
  linarith

/-- **Uniqueness of nearest point.** At a differentiability point `x` of
`d(x) = infDist x C` with `d(x) > 0`, there is a unique nearest point in `C`. -/
theorem nearest_point_unique {C : Set (E n)} (hC : IsClosed C) (hne : C.Nonempty)
    {x : E n} (hdiff : DifferentiableAt ℝ (fun x => infDist x C) x)
    (hpos : 0 < infDist x C) :
    ∃! (y : E n), y ∈ C ∧ dist x y = infDist x C := by
  let d : E n → ℝ := fun x => infDist x C
  have h1 : ‖fderiv ℝ d x‖ = 1 :=
    norm_fderiv_infDist_eq_one hC hne hdiff hpos
  rcases exists_nearest_point hC hne hpos with ⟨y, hyC, hydist⟩
  set v : E n := (d x)⁻¹ • (x - y) with hv_def
  have hv_norm : ‖v‖ = 1 := by
    have h : ‖v‖ = |(d x)⁻¹| * ‖x - y‖ := by
      rw [hv_def, norm_smul] <;> rfl
    rw [h]
    have h3 : ‖x - y‖ = d x := by simpa [dist_eq_norm] using hydist
    rw [h3]
    have h4 : 0 < d x := hpos
    have h5 : |(d x)⁻¹| = (d x)⁻¹ := abs_of_pos (inv_pos.mpr h4)
    rw [h5]
    field_simp [h4.ne'] <;> ring
  have h_fderiv_v : (fderiv ℝ d x) v = 1 :=
    fderiv_infDist_at_nearest_point hC hne hdiff hpos hyC hydist
  have h_riesz : ∀ (w : E n), (fderiv ℝ d x) w = inner ℝ w v :=
    norm_one_functional_riesz hv_norm (fderiv ℝ d x) h1 h_fderiv_v
  refine' ⟨y, ⟨hyC, hydist⟩, _⟩
  intro y' hy'
  have hy'C : y' ∈ C := hy'.1
  have hydist' : dist x y' = d x := hy'.2
  set v' : E n := (d x)⁻¹ • (x - y') with hv'_def
  have hv'_norm : ‖v'‖ = 1 := by
    have h : ‖v'‖ = |(d x)⁻¹| * ‖x - y'‖ := by
      rw [hv'_def, norm_smul] <;> rfl
    rw [h]
    have h3 : ‖x - y'‖ = d x := by simpa [dist_eq_norm] using hydist'
    rw [h3]
    have h4 : 0 < d x := hpos
    have h5 : |(d x)⁻¹| = (d x)⁻¹ := abs_of_pos (inv_pos.mpr h4)
    rw [h5]
    field_simp [h4.ne'] <;> ring
  have h_fderiv_v' : (fderiv ℝ d x) v' = 1 :=
    fderiv_infDist_at_nearest_point hC hne hdiff hpos hy'C hydist'
  have h_eq : (fderiv ℝ d x) v' = inner ℝ v' v := h_riesz v'
  rw [h_eq] at h_fderiv_v'
  have h_inner : inner ℝ v' v = 1 := h_fderiv_v'
  have h10 : ‖v' - v‖ ^ 2 = ‖v'‖ ^ 2 + ‖v‖ ^ 2 - 2 * inner ℝ v' v := by
    have h11 : ‖v' - v‖ ^ 2 = ‖v'‖ ^ 2 - 2 * inner ℝ v' v + ‖v‖ ^ 2 := by
      simpa [real_inner_comm] using norm_sub_sq_real v' v
    linarith
  have h12 : ‖v' - v‖ ^ 2 = 0 := by
    rw [h10, hv'_norm, hv_norm, h_inner] <;> norm_num
  have h13 : v' = v := by
    have h14 : ‖v' - v‖ = 0 := by simpa [pow_eq_zero_iff] using h12
    have h15 : v' - v = 0 := norm_eq_zero.mp h14
    exact sub_eq_zero.mp h15
  have h15 : (d x)⁻¹ • (x - y') = (d x)⁻¹ • (x - y) := by
    simpa [hv'_def, hv_def] using h13
  have h16 : (d x)⁻¹ ≠ 0 := by positivity
  have h17 : x - y' = x - y := smul_right_injective (E n) h16 h15
  have h18 : y' = y := by
    simpa [sub_eq_sub_iff_sub_eq_sub] using h17
  exact h18

/-- The Riesz representative vector of `fderiv d x` at a differentiability point
with nearest point `y`. -/
lemma fderiv_infDist_riesz {C : Set (E n)} (hC : IsClosed C) (hne : C.Nonempty)
    {x : E n} (hdiff : DifferentiableAt ℝ (fun x => infDist x C) x)
    (hpos : 0 < infDist x C) {y : E n} (hyC : y ∈ C)
    (hydist : dist x y = infDist x C) :
    ∀ (w : E n), (fderiv ℝ (fun x => infDist x C) x) w =
      inner ℝ w ((infDist x C)⁻¹ • (x - y)) := by
  let d : E n → ℝ := fun x => infDist x C
  let f' := fderiv ℝ d x
  set v : E n := (d x)⁻¹ • (x - y) with hv_def
  have hv_norm : ‖v‖ = 1 := by
    have h : ‖v‖ = |(d x)⁻¹| * ‖x - y‖ := by
      rw [hv_def, norm_smul] <;> rfl
    rw [h]
    have h3 : ‖x - y‖ = d x := by simpa [dist_eq_norm] using hydist
    rw [h3]
    have h4 : 0 < d x := hpos
    have h5 : |(d x)⁻¹| = (d x)⁻¹ := abs_of_pos (inv_pos.mpr h4)
    rw [h5]
    field_simp [h4.ne'] <;> ring
  have h1 : ‖f'‖ = 1 := norm_fderiv_infDist_eq_one hC hne hdiff hpos
  have h2 : f' v = 1 := fderiv_infDist_at_nearest_point hC hne hdiff hpos hyC hydist
  exact norm_one_functional_riesz hv_norm f' h1 h2

-- ============================================================================
-- Step 2: Gradient continuity relative to differentiability set
-- ============================================================================

/-- **Gradient continuity of the distance function.**

If `x_k → x` are all differentiability points of `d(z) = infDist z C` with
`d(x) > 0`, then `fderiv d x_k → fderiv d x`. -/
theorem fderiv_infDist_continuous {C : Set (E n)} (hC : IsClosed C) (hne : C.Nonempty)
    {x : E n} (hdiff_x : DifferentiableAt ℝ (fun x => infDist x C) x)
    (hpos_x : 0 < infDist x C)
    {x_k : ℕ → E n} (hxk_diff : ∀ k, DifferentiableAt ℝ (fun x => infDist x C) (x_k k))
    (hxk_pos : ∀ k, 0 < infDist (x_k k) C)
    (hxk_tendsto : Filter.Tendsto x_k Filter.atTop (nhds x)) :
    Filter.Tendsto (fun k => fderiv ℝ (fun x => infDist x C) (x_k k))
      Filter.atTop (nhds (fderiv ℝ (fun x => infDist x C) x)) := by
  let d : E n → ℝ := fun x => infDist x C
  let f'_x := fderiv ℝ d x

  -- Unique nearest point y for x
  have h_main_uniq : ∃! (y : E n), y ∈ C ∧ dist x y = d x :=
    nearest_point_unique hC hne hdiff_x hpos_x
  rcases h_main_uniq with ⟨y, ⟨hyC, hydist⟩, h_y_uniq⟩
  set v : E n := (d x)⁻¹ • (x - y) with hv_def

  -- Choose nearest point y_k for each x_k
  choose y_k hyk_C hyk_dist using fun k =>
    exists_nearest_point hC hne (hxk_pos k)

  -- d(x_k) → d(x)
  have hd_tendsto : Tendsto (fun k => d (x_k k)) atTop (nhds (d x)) :=
    (continuous_infDist_pt (s := C)).continuousAt.tendsto.comp hxk_tendsto

  have h_xk_range_bdd : Bornology.IsBounded (Set.range x_k) :=
    Metric.isBounded_range_of_tendsto x_k hxk_tendsto
  have h_xk_bdd : ∃ (B : ℝ), Set.range x_k ⊆ Metric.closedBall (0 : E n) B :=
    h_xk_range_bdd.subset_closedBall 0
  rcases h_xk_bdd with ⟨B, hB⟩
  have hB' : ∀ k, ‖x_k k‖ ≤ B := by
    intro k
    have h : x_k k ∈ Set.range x_k := Set.mem_range_self k
    have h2 : x_k k ∈ Metric.closedBall (0 : E n) B := hB h
    simpa [Metric.mem_closedBall] using h2
  have h_d_range_bdd : Bornology.IsBounded (Set.range (fun k => d (x_k k))) :=
    Metric.isBounded_range_of_tendsto (fun k => d (x_k k)) hd_tendsto
  have h_d_bdd : ∃ (D : ℝ), Set.range (fun k => d (x_k k)) ⊆ Metric.closedBall (0 : ℝ) D :=
    h_d_range_bdd.subset_closedBall 0
  rcases h_d_bdd with ⟨D, hD⟩
  have hD' : ∀ k, |d (x_k k)| ≤ D := by
    intro k
    have h : d (x_k k) ∈ Set.range (fun k => d (x_k k)) := Set.mem_range_self k
    have h2 : d (x_k k) ∈ Metric.closedBall (0 : ℝ) D := hD h
    simpa [Metric.mem_closedBall, Real.norm_eq_abs] using h2
  have hD'' : ∀ k, d (x_k k) ≤ D := by
    intro k
    have h : |d (x_k k)| ≤ D := hD' k
    linarith [abs_le.mp h]
  have hyk_bdd : ∀ k, ‖y_k k‖ ≤ B + D := by
    intro k
    have h1 : ‖x_k k - y_k k‖ = d (x_k k) := by
      simpa [dist_eq_norm] using hyk_dist k
    have h2 : ‖y_k k‖ ≤ ‖x_k k‖ + ‖y_k k - x_k k‖ := by
      calc
        ‖y_k k‖ = ‖x_k k + (y_k k - x_k k)‖ := by abel_nf
        _ ≤ ‖x_k k‖ + ‖y_k k - x_k k‖ := norm_add_le _ _
    have h3 : ‖y_k k - x_k k‖ = ‖x_k k - y_k k‖ := by rw [show y_k k - x_k k = -(x_k k - y_k k) by abel, norm_neg]
    rw [h3] at h2
    rw [h1] at h2
    linarith [hB' k, hD'' k]

  -- Claim: y_k → y. Proof by contradiction using Bolzano-Weierstrass.
  have hy_tendsto : Tendsto y_k atTop (nhds y) := by
    by_contra h
    have h_not : ∃ (ε : ℝ), 0 < ε ∧ ∀ (N : ℕ), ∃ (k : ℕ), N ≤ k ∧ ε ≤ dist (y_k k) y := by
      simpa [Metric.tendsto_atTop] using h
    rcases h_not with ⟨ε, hε_pos, h_exists⟩
    have h_exists' : ∀ (N : ℕ), ∃ (k : ℕ), N ≤ k ∧ ε ≤ ‖y_k k - y‖ := by
      intro N
      rcases h_exists N with ⟨k, hNk, hfar⟩
      have h_eq : dist (y_k k) y = ‖y_k k - y‖ := by simp [dist_eq_norm]
      rw [h_eq] at hfar
      exact ⟨k, hNk, hfar⟩
    let find_far : ℕ → ℕ := fun N => Nat.find (h_exists' N)
    have h_find_far_prop : ∀ N, N ≤ find_far N ∧ ε ≤ ‖y_k (find_far N) - y‖ := by
      intro N
      exact Nat.find_spec (h_exists' N)
    -- Construct strictly monotone ψ recursively
    let ψ : ℕ → ℕ := fun n => Nat.recOn n (find_far 0) fun n prev => find_far (prev + 1)
    have hψ0 : ψ 0 = find_far 0 := by rfl
    have hψ_succ : ∀ n, ψ (n + 1) = find_far (ψ n + 1) := by
      intro n; rfl
    have hψ1 : ∀ n, ψ n < ψ (n + 1) := by
      intro n
      have h1 : ψ n + 1 ≤ find_far (ψ n + 1) := (h_find_far_prop (ψ n + 1)).1
      have h2 : ψ n < ψ n + 1 := by linarith
      linarith
    have hψ_strict_mono : StrictMono ψ := by
      intro a b h
      induction' h with b h ih
      · exact hψ1 a
      · exact lt_trans ih (hψ1 b)
    have hfar : ∀ k, ε ≤ ‖y_k (ψ k) - y‖ := by
      intro k
      cases k with
      | zero =>
        have h : ψ 0 = find_far 0 := hψ0
        rw [h]
        exact (h_find_far_prop 0).2
      | succ k =>
        have h : ψ (k + 1) = find_far (ψ k + 1) := hψ_succ k
        rw [h]
        exact (h_find_far_prop (ψ k + 1)).2
    -- Bounded subsequence via explicit norm bound
    have h_bdd_sub : Bornology.IsBounded (Set.range (y_k ∘ ψ)) := by
      rw [Metric.isBounded_iff]
      refine ⟨2 * (B + D), ?_⟩
      intro z hz w hw
      rcases hz with ⟨k, rfl⟩
      rcases hw with ⟨l, rfl⟩
      have h1 : ‖y_k (ψ k)‖ ≤ B + D := hyk_bdd (ψ k)
      have h2 : ‖y_k (ψ l)‖ ≤ B + D := hyk_bdd (ψ l)
      calc
        dist (y_k (ψ k)) (y_k (ψ l))
          = ‖y_k (ψ k) - y_k (ψ l)‖ := by simp [dist_eq_norm]
        _ ≤ ‖y_k (ψ k)‖ + ‖y_k (ψ l)‖ := norm_sub_le _ _
        _ ≤ 2 * (B + D) := by linarith
    -- Extract convergent subsubsequence
    let s : Set (E n) := Metric.closedBall 0 (B + D)
    have hs : Bornology.IsBounded s := by
      rw [Metric.isBounded_iff]
      refine ⟨2 * (B + D), ?_⟩
      intro z hz w hw
      have h1 : dist z w ≤ dist z 0 + dist 0 w := dist_triangle z 0 w
      have h2 : dist z 0 ≤ B + D := by simpa [s, Metric.mem_closedBall] using hz
      have h3 : dist 0 w ≤ B + D := by simpa [s, Metric.mem_closedBall] using hw
      linarith
    have h_all_in : ∀ k, (y_k ∘ ψ) k ∈ s := by
      intro k
      simpa [s, Metric.mem_closedBall] using hyk_bdd (ψ k)
    rcases tendsto_subseq_of_bounded (s := s) hs (x := y_k ∘ ψ) h_all_in
      with ⟨z, hz_in, θ, hθ, hz_tendsto⟩
    -- z ∈ C
    have hzC : z ∈ C := by
      have h_in_C : ∀ᶠ k in atTop, (y_k ∘ ψ ∘ θ) k ∈ C := by
        filter_upwards with k
        exact hyk_C (ψ (θ k))
      have h_closure : z ∈ closure C := mem_closure_of_tendsto hz_tendsto h_in_C
      have h_eq : closure C = C := IsClosed.closure_eq hC
      rw [h_eq] at h_closure
      exact h_closure
    -- ψ ∘ θ is strictly monotone, hence tends to atTop
    have hψθ_strict_mono : StrictMono (ψ ∘ θ) := hψ_strict_mono.comp hθ
    have h_tendsto_ψθ : Tendsto (ψ ∘ θ) atTop atTop := hψθ_strict_mono.tendsto_atTop
    -- dist x z = d x
    have hzdist : dist x z = d x := by
      have h_tendsto_x : Tendsto (fun k => x_k (ψ (θ k))) atTop (nhds x) :=
        hxk_tendsto.comp h_tendsto_ψθ
      have h_tendsto_yz : Tendsto (fun k => y_k (ψ (θ k))) atTop (nhds z) := hz_tendsto
      have h2 : Tendsto (fun k => dist (x_k (ψ (θ k))) (y_k (ψ (θ k)))) atTop (nhds (dist x z)) :=
        h_tendsto_x.dist h_tendsto_yz
      have h3 : (fun k => dist (x_k (ψ (θ k))) (y_k (ψ (θ k)))) = fun k => d (x_k (ψ (θ k))) := by
        funext k; exact hyk_dist (ψ (θ k))
      rw [h3] at h2
      have h4 : Tendsto (fun k => d (x_k (ψ (θ k)))) atTop (nhds (d x)) :=
        hd_tendsto.comp h_tendsto_ψθ
      exact tendsto_nhds_unique h2 h4
    have hz_eq_y : z = y := h_y_uniq z ⟨hzC, hzdist⟩
    -- Contradiction: avoid rewriting the large hz_tendsto term
    have h_ball_eq : Metric.ball z ε = Metric.ball y ε :=
      congrArg (fun x : E n => Metric.ball x ε) hz_eq_y
    have h_eventually_z : ∀ᶠ k in atTop, (y_k ∘ ψ ∘ θ) k ∈ Metric.ball z ε :=
      hz_tendsto.eventually (Metric.ball_mem_nhds z hε_pos)
    have h_eventually_y : ∀ᶠ k in atTop, (y_k ∘ ψ ∘ θ) k ∈ Metric.ball y ε := by
      rw [h_ball_eq] at h_eventually_z
      exact h_eventually_z
    have h_always : ∀ k, ‖y_k (ψ (θ k)) - y‖ ≥ ε := fun k => hfar (θ k)
    have h_eventually' : ∀ᶠ k in atTop, ‖y_k (ψ (θ k)) - y‖ < ε :=
      h_eventually_y.mono (fun k hk => by simpa [Metric.mem_ball, dist_eq_norm] using hk)
    have h_contra : ∀ᶠ k in atTop, False := h_eventually'.mono (fun k hk => by linarith [h_always k])
    rcases Filter.eventually_atTop.mp h_contra with ⟨N, hN⟩
    exact hN N (by linarith)

  -- v_k = (x_k - y_k) / d(x_k) → v
  have hv_tendsto : Tendsto (fun k => (d (x_k k))⁻¹ • (x_k k - y_k k)) atTop (nhds v) := by
    have h1 : Tendsto (fun k => x_k k - y_k k) atTop (nhds (x - y)) :=
      hxk_tendsto.sub hy_tendsto
    have h2 : Tendsto (fun k => (d (x_k k))⁻¹) atTop (nhds ((d x)⁻¹)) := by
      apply Tendsto.inv₀
      · exact hd_tendsto
      · exact hpos_x.ne'
    exact h2.smul h1

  -- fderiv d(x_k) = toDual(v_k), fderiv d(x) = toDual(v)
  have h_toDual_eq : ∀ (u : E n), (InnerProductSpace.toDual ℝ (E n)) u =
      fun w => inner ℝ u w := by
    intro u
    ext w
    exact InnerProductSpace.toDual_apply_apply (𝕜 := ℝ)
  have h_riesz_k : ∀ k, fderiv ℝ d (x_k k) =
      (InnerProductSpace.toDual ℝ (E n)) ((d (x_k k))⁻¹ • (x_k k - y_k k)) := by
    intro k
    ext w
    have h_eq1 : (fderiv ℝ d (x_k k)) w =
        inner ℝ w ((d (x_k k))⁻¹ • (x_k k - y_k k)) :=
      fderiv_infDist_riesz hC hne (hxk_diff k) (hxk_pos k) (hyk_C k) (hyk_dist k) w
    have h_eq2 : ((InnerProductSpace.toDual ℝ (E n)) ((d (x_k k))⁻¹ • (x_k k - y_k k))) w =
        inner ℝ ((d (x_k k))⁻¹ • (x_k k - y_k k)) w :=
      InnerProductSpace.toDual_apply_apply (𝕜 := ℝ)
    have h_comm : inner ℝ ((d (x_k k))⁻¹ • (x_k k - y_k k)) w =
        inner ℝ w ((d (x_k k))⁻¹ • (x_k k - y_k k)) :=
      (real_inner_comm _ _).symm
    rw [h_eq2, h_comm]
    exact h_eq1
  have h_riesz_x : f'_x = (InnerProductSpace.toDual ℝ (E n)) v := by
    ext w
    have h_eq1 : f'_x w = inner ℝ w v :=
      fderiv_infDist_riesz hC hne hdiff_x hpos_x hyC hydist w
    have h_eq2 : ((InnerProductSpace.toDual ℝ (E n)) v) w = inner ℝ v w :=
      InnerProductSpace.toDual_apply_apply (𝕜 := ℝ)
    have h_comm : inner ℝ v w = inner ℝ w v := (real_inner_comm v w).symm
    rw [h_eq2, h_comm]
    exact h_eq1

  have h_map : Continuous (fun (u : E n) => (InnerProductSpace.toDual ℝ (E n)) u) :=
    (InnerProductSpace.toDual ℝ (E n)).continuous
  have h_main : Tendsto (fun k => fderiv ℝ d (x_k k)) atTop (nhds f'_x) := by
    rw [h_riesz_x]
    have h_eq : (fun k => fderiv ℝ d (x_k k)) =
        fun k => (InnerProductSpace.toDual ℝ (E n))
          ((d (x_k k))⁻¹ • (x_k k - y_k k)) := by
      funext k
      exact h_riesz_k k
    rw [h_eq]
    exact h_map.continuousAt.tendsto.comp hv_tendsto
  exact h_main

-- ============================================================================
-- Step 3: Gradient closeness balls and covering
-- ============================================================================

/-- At a differentiability point `x₀` of `d` with `d(x₀) > 0`, for any `ε > 0`,
there exists `r > 0` such that for all differentiability points `x` with
`d(x) > 0` in `ball x₀ r`, the gradient is `ε`-close to `fderiv d x₀`. -/
lemma grad_close_at_point {C : Set (E n)} (hC : IsClosed C) (hne : C.Nonempty)
    {x₀ : E n} (hdiff : DifferentiableAt ℝ (fun x => infDist x C) x₀)
    (hpos : 0 < infDist x₀ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℝ), 0 < r ∧ ∀ (x : E n), DifferentiableAt ℝ (fun x => infDist x C) x →
      0 < infDist x C → x ∈ ball x₀ r →
        ‖fderiv ℝ (fun x => infDist x C) x - fderiv ℝ (fun x => infDist x C) x₀‖ ≤ ε := by
  let d := fun x : E n => infDist x C
  by_contra h
  push Not at h
  choose x hdiff_x hpos_x hx_ball hfar using fun k : ℕ =>
    h (1 / (k + 1 : ℝ)) (by positivity)
  have h_tendsto : Tendsto x atTop (nhds x₀) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    let N := Nat.ceil (1 / δ)
    refine ⟨N, fun k hk => ?_⟩
    have h2 : dist (x k) x₀ < 1 / (k + 1 : ℝ) := by simpa [Metric.mem_ball] using hx_ball k
    have h4 : N ≤ k := hk
    have h5 : (N : ℝ) ≥ 1 / δ := Nat.le_ceil (1 / δ)
    have h6 : (k : ℝ) ≥ 1 / δ := by
      have h7 : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast h4
      linarith [h5]
    have h7 : (k : ℝ) + 1 > 1 / δ := by linarith
    have h8 : 1 / ((k : ℝ) + 1) < δ := by
      have h9 : 0 < 1 / δ := by positivity
      have h10 : 1 / ((k : ℝ) + 1) < 1 / (1 / δ) := one_div_lt_one_div_of_lt (by positivity) h7
      have h11 : 1 / (1 / δ) = δ := by field_simp [hδ.ne'] <;> ring
      rw [h11] at h10
      exact h10
    linarith
  have h_cont := fderiv_infDist_continuous hC hne hdiff hpos hdiff_x hpos_x h_tendsto
  have h_eventually1 : ∀ᶠ k in atTop, fderiv ℝ d (x k) ∈ Metric.ball (fderiv ℝ d x₀) ε :=
    h_cont.eventually (Metric.ball_mem_nhds (fderiv ℝ d x₀) hε)
  have h_eventually : ∀ᶠ k in atTop, ‖fderiv ℝ d (x k) - fderiv ℝ d x₀‖ < ε :=
    h_eventually1.mono (fun k hk => by simpa [Metric.mem_ball, dist_eq_norm] using hk)
  rcases Filter.eventually_atTop.mp h_eventually with ⟨N, hN⟩
  have h9 : ‖fderiv ℝ d (x N) - fderiv ℝ d x₀‖ < ε := hN N (by linarith)
  have h10 : ‖fderiv ℝ d (x N) - fderiv ℝ d x₀‖ > ε := hfar N
  linarith

/-- At a differentiability point `x₀` of `d` with `d(x₀) > 0`, for any `ε > 0`,
there exists `r > 0` such that `ball x₀ r ⊆ {d > 0}` and the gradient is
`ε`-close a.e. on `ball x₀ r`. -/
lemma grad_close_ball {C : Set (E n)} (hC : IsClosed C) (hne : C.Nonempty)
    {x₀ : E n} (hdiff : DifferentiableAt ℝ (fun x => infDist x C) x₀)
    (hpos : 0 < infDist x₀ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℝ), 0 < r ∧ ball x₀ r ⊆ {x | 0 < infDist x C} ∧
      ∀ᵐ (x : E n) ∂volume.restrict (ball x₀ r),
        ‖fderiv ℝ (fun x => infDist x C) x - fderiv ℝ (fun x => infDist x C) x₀‖ ≤ ε := by
  let d := fun x : E n => infDist x C
  have h_d_cont : Continuous d := infDist_lipschitz.continuous
  have h1 : ∃ (r₁ : ℝ), 0 < r₁ ∧ ∀ x ∈ ball x₀ r₁, 0 < d x := by
    have h_nhds : {x | 0 < d x} ∈ nhds x₀ := h_d_cont.continuousAt (Ioi_mem_nhds hpos)
    rcases Metric.mem_nhds_iff.mp h_nhds with ⟨r₁, hr₁_pos, hr₁⟩
    exact ⟨r₁, hr₁_pos, fun x hx => hr₁ hx⟩
  rcases h1 with ⟨r₁, hr₁_pos, h_d_pos⟩
  rcases grad_close_at_point hC hne hdiff hpos hε with ⟨r₂, hr₂_pos, h_grad⟩
  let r := min r₁ r₂
  have hr_pos : 0 < r := lt_min hr₁_pos hr₂_pos
  have h_ball_sub : ball x₀ r ⊆ {x | 0 < d x} := by
    intro x hx
    have h3 : x ∈ ball x₀ r₁ := ball_subset_ball (by exact min_le_left r₁ r₂) hx
    exact h_d_pos x h3
  have h_diff_ae : ∀ᵐ (x : E n) ∂volume, DifferentiableAt ℝ d x :=
    infDist_lipschitz.ae_differentiableAt
  have h4 : ∀ᵐ (x : E n) ∂volume.restrict (ball x₀ r), DifferentiableAt ℝ d x :=
    ae_restrict_of_ae h_diff_ae
  have h_ae : ∀ᵐ (x : E n) ∂volume.restrict (ball x₀ r),
      ‖fderiv ℝ d x - fderiv ℝ d x₀‖ ≤ ε := by
    filter_upwards [h4, self_mem_ae_restrict isOpen_ball.measurableSet] with x hdiff_x hx_ball
    have h5 : 0 < d x := h_ball_sub hx_ball
    have h6 : x ∈ ball x₀ r₂ := ball_subset_ball (by exact min_le_right r₁ r₂) hx_ball
    exact h_grad x hdiff_x h5 h6
  exact ⟨r, hr_pos, h_ball_sub, h_ae⟩

-- ============================================================================
-- Step 4: Local coarea upper bound for measurable bounded sets
-- ============================================================================

/-- Local coarea upper bound extended from compact to measurable bounded sets. -/
lemma local_coarea_measurable_upper
    {f : E n → ℝ} (hf : LipschitzWith 1 f)
    {x₀ : E n} (h₁ : ‖fderiv ℝ f x₀‖ = 1)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε2 : ε < 1)
    (h_grad_close : ∀ᵐ (x : E n) ∂volume.restrict (ball x₀ r),
      ‖fderiv ℝ f x - fderiv ℝ f x₀‖ ≤ ε)
    {C : Set (E n)} (hC : MeasurableSet C) (hC_sub : C ⊆ closedBall x₀ (r / 2))
    (hC_bdd : Bornology.IsBounded C)
    {a b : ℝ} (hab : a < b) :
    volume {x ∈ C | a < f x ∧ f x ≤ b} ≤
      ENNReal.ofReal (((1 + ε) ^ (n - 1 : ℕ)) / ((1 - ε) ^ n)) *
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} := by
  let K_up := ENNReal.ofReal (((1 + ε) ^ (n - 1 : ℕ)) / ((1 - ε) ^ n))
  let C_slice : Set (E n) := {x ∈ C | a < f x ∧ f x ≤ b}
  have hC_slice_meas : MeasurableSet C_slice := by
    have h1 : MeasurableSet {x : E n | a < f x} :=
      measurableSet_Ioi.preimage hf.continuous.measurable
    have h2 : MeasurableSet {x : E n | f x ≤ b} :=
      measurableSet_Iic.preimage hf.continuous.measurable
    exact hC.inter (h1.inter h2)
  have h_inner : volume C_slice = ⨆ (K : Set (E n)), ⨆ (_ : K ⊆ C_slice), ⨆ (_ : IsCompact K), volume K :=
    hC_slice_meas.measure_eq_iSup_isCompact volume
  rw [h_inner]
  apply iSup_le
  intro K
  apply iSup_le
  intro hK_sub_slice
  apply iSup_le
  intro hK_compact
  have hK_sub_C : K ⊆ C := by
    intro x hx
    exact (hK_sub_slice hx).1
  have hK_sub2 : K ⊆ closedBall x₀ (r / 2) := subset_trans hK_sub_C hC_sub
  have hK_eq : {x ∈ K | a < f x ∧ f x ≤ b} = K := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hx, _⟩; exact hx
    · intro hx
      have h2 : x ∈ C_slice := hK_sub_slice hx
      exact ⟨hx, h2.2⟩
  have h_local := local_coarea_lipschitz f hf x₀ h₁ r ε hr hε hε2 h_grad_close
    K hK_compact hK_sub2 a b hab
  have h_vol_eq : volume K = volume {x | x ∈ K ∧ a < f x ∧ f x ≤ b} := by
    apply congr_arg volume
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    have h9 : {x ∈ K | a < f x ∧ f x ≤ b} = K := hK_eq
    have h10 : (y ∈ K ∧ a < f y ∧ f y ≤ b) ↔ y ∈ K := by
      constructor
      · rintro ⟨hy, _⟩; exact hy
      · intro hy
        have h2 : y ∈ C_slice := hK_sub_slice hy
        exact ⟨hy, h2.2⟩
    exact h10.symm
  have h_mono : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ K | f x = s} ≤
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} := by
    apply lintegral_mono
    intro s
    apply MeasureTheory.measure_mono
    intro y hy
    exact ⟨hK_sub_C hy.1, hy.2⟩
  calc
    volume K
      = volume {x | x ∈ K ∧ a < f x ∧ f x ≤ b} := h_vol_eq
    _ ≤ K_up * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ K | f x = s} := h_local
    _ ≤ K_up * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} := by
      exact mul_le_mul_left' h_mono K_up

-- ============================================================================
-- Step 5: Global distance coarea upper bound via Lindelöf covering + assembly
-- ============================================================================

/-- **Global distance coarea upper bound.**

For a nonempty closed `C`, bounded measurable `A ⊆ {d > 0}`, and `0 < ε < 1`:

```
volume {x ∈ A | a < d x ≤ b} ≤
  ((1+ε)^(n-1) / (1-ε)^n) * ∫⁻ s in Ioc a b, μHE[n-1] {x ∈ A | d x = s}
```

where `d(x) = infDist x C`. -/
theorem distance_coarea_upper {C : Set (E n)} (hC : IsClosed C) (hne : C.Nonempty)
    {A : Set (E n)} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (hA_sub : A ⊆ {x | 0 < infDist x C})
    {a b : ℝ} (hab : a < b) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1) :
    volume {x ∈ A | a < infDist x C ∧ infDist x C ≤ b} ≤
      ENNReal.ofReal (((1 + ε) ^ (n - 1 : ℕ)) / ((1 - ε) ^ n)) *
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | infDist x C = s} := by
  let d := fun x : E n => infDist x C
  let K_up : ℝ := ((1 + ε) ^ (n - 1 : ℕ)) / ((1 - ε) ^ n)
  have hK_up_pos : 0 < K_up := by positivity
  have hK_up_gt_one : 1 < K_up := by
    have h3 : (1 + ε) ^ (n - 1) ≥ 1 := by
      have h31 : 1 ≤ 1 + ε := by linarith
      have h : ∀ m : ℕ, 1 ≤ (1 + ε) ^ m := by
        intro m
        induction m with
        | zero => norm_num
        | succ m ih => simp [pow_succ] at * <;> nlinarith
      exact h (n - 1)
    have h4 : 0 < (1 - ε) ^ n := by positivity
    have h5 : (1 - ε) ^ n < 1 := by
      have h51 : 0 < 1 - ε := by linarith
      have h52 : 1 - ε < 1 := by linarith
      have h53 : 0 < n := by
        have hne : Nonempty (Fin n) := inferInstance
        rcases hne with ⟨i⟩
        have h6 : i.val < n := i.is_lt
        omega
      have h : ∀ m : ℕ, 0 < m → (1 - ε) ^ m < 1 := by
        intro m hm
        induction' hm with m hm ih
        · simpa using h52
        · simp [pow_succ] at * <;> nlinarith
      exact h n h53
    have h6 : K_up ≥ 1 / (1 - ε) ^ n := by
      apply div_le_div_of_nonneg_right h3
      positivity
    have h7 : 1 / (1 - ε) ^ n > 1 := by
      have h8 : (1 - ε) ^ n < 1 := h5
      have h9 : 0 < (1 - ε) ^ n := h4
      have h10 : 1 < 1 / (1 - ε) ^ n := one_lt_one_div h9 h8
      exact h10
    linarith
  let ε' : ℝ := K_up - 1
  have hε'_pos : 0 < ε' := by linarith
  have h1pε' : 1 + ε' = K_up := by ring
  -- Differentiability set
  let D : Set (E n) := {x | DifferentiableAt ℝ d x}
  have hD_ae : ∀ᵐ x ∂volume, x ∈ D := infDist_lipschitz.ae_differentiableAt
  -- For each x ∈ D ∩ A, choose a ball with gradient closeness
  have h_ball_exists : ∀ (x : E n), x ∈ D ∩ A →
      ∃ (r : ℝ), 0 < r ∧ ball x (r / 2) ⊆ {z | 0 < d z} ∧
        ∀ᵐ (z : E n) ∂volume.restrict (ball x r),
          ‖fderiv ℝ d z - fderiv ℝ d x‖ ≤ ε := by
    intro x hx
    have hxD : DifferentiableAt ℝ d x := hx.1
    have hxA : x ∈ A := hx.2
    have hpos : 0 < d x := hA_sub hxA
    rcases grad_close_ball hC hne hxD hpos hε with ⟨r, hr_pos, h_ball_sub, h_grad⟩
    refine ⟨r, hr_pos, ?_, h_grad⟩
    exact subset_trans (ball_subset_ball (by linarith)) h_ball_sub
  choose r hr_pos h_ball_sub h_grad_close using h_ball_exists
  -- Open cover of D ∩ A
  let idx : Type _ := {x : E n // x ∈ D ∩ A}
  let U_idx : idx → Set (E n) := fun i => ball i.val (r i.val i.property / 2)
  have hU_open : ∀ (i : idx), IsOpen (U_idx i) := fun _ => isOpen_ball
  have h_cover : (D ∩ A : Set (E n)) ⊆ ⋃ (i : idx), U_idx i := by
    intro x hx
    let i : idx := ⟨x, hx⟩
    have h2 : x ∈ U_idx i := by
      have h4 : 0 < r x hx / 2 := by linarith [hr_pos x hx]
      have h5 : dist x x < r x hx / 2 := by
        simpa using h4
      exact h5
    exact Set.mem_iUnion.mpr ⟨i, h2⟩
  have h_lindelof : IsLindelof (D ∩ A : Set (E n)) :=
    HereditarilyLindelofSpace.isLindelof (D ∩ A)
  rcases h_lindelof.elim_countable_subcover U_idx hU_open h_cover with ⟨S, hS_count, hS_cover⟩
  by_cases hDA_empty : (D ∩ A : Set (E n)) = ∅
  · -- D ∩ A is empty, so A has measure zero
    have h1 : A ⊆ {x | x ∉ D} := by
      intro x hx
      by_contra h2
      have h2' : x ∈ D := by simpa using h2
      have h3 : x ∈ D ∩ A := ⟨h2', hx⟩
      rw [hDA_empty] at h3
      simpa using h3
    have h4 : volume {x : E n | x ∉ D} = 0 := by
      have h5 : ∀ᵐ (x : E n) ∂volume, x ∈ D := hD_ae
      exact h5
    have hA_null : volume A = 0 := measure_mono_null h1 h4
    have h5 : volume {x ∈ A | a < d x ∧ d x ≤ b} = 0 :=
      measure_mono_null (fun x hx => hx.1) hA_null
    rw [h5] <;> simp
  · -- D ∩ A is nonempty, hence S is nonempty
    have hDA_nonempty : (D ∩ A : Set (E n)).Nonempty := by
      rw [Set.nonempty_iff_ne_empty] <;> exact hDA_empty
    have hS_nonempty : S.Nonempty := by
      by_contra h
      have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      rw [hS_empty] at hS_cover
      simp at hS_cover
      have hDA_empty2 : (D ∩ A : Set (E n)) = ∅ := by
        simpa using hS_cover
      exact Set.nonempty_iff_ne_empty.mp hDA_nonempty hDA_empty2
    rcases hS_count.exists_eq_range hS_nonempty with ⟨e : ℕ → idx, he_range⟩
    let U : ℕ → Set (E n) := fun k => U_idx (e k)
    have hU_open' : ∀ k, IsOpen (U k) := fun k => hU_open (e k)
    have hS_cover' : (D ∩ A : Set (E n)) ⊆ ⋃ k, U k := by
      calc
        (D ∩ A : Set (E n)) ⊆ ⋃ i ∈ S, U_idx i := hS_cover
        _ = ⋃ k, U k := by
          ext z
          simp only [Set.mem_iUnion, U, he_range]
          <;> aesop
    let A' := A ∩ (⋃ k, U k)
    have hA'_meas : MeasurableSet A' := hA.inter (MeasurableSet.iUnion (fun k => (hU_open' k).measurableSet))
    have hA'_sub : A' ⊆ ⋃ k, U k := fun x hx => hx.2
    have hA_diff_null : volume (A \ A') = 0 := by
      have h1 : A \ A' ⊆ {x | x ∉ D} := by
        intro x hx
        have hxA : x ∈ A := hx.1
        have h2 : x ∉ A' := hx.2
        by_contra h3
        have h3' : x ∈ D := by simpa using h3
        have h4 : x ∈ D ∩ A := ⟨h3', hxA⟩
        have h5 : x ∈ ⋃ k, U k := hS_cover' h4
        have h6 : x ∈ A' := ⟨hxA, h5⟩
        exact h2 h6
      have h7 : volume {x : E n | x ∉ D} = 0 := by
        have h8 : ∀ᵐ (x : E n) ∂volume, x ∈ D := hD_ae
        exact h8
      exact measure_mono_null h1 h7
    have h_local : ∀ (k : ℕ) (C' : Set (E n)), MeasurableSet C' → C' ⊆ U k →
        volume {x ∈ C' | a < d x ∧ d x ≤ b} ≤
          ENNReal.ofReal (1 + ε') * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C' | d x = s} := by
      intro k C' hC'_meas hC'_sub
      let i : idx := e k
      let x₀ : E n := i.val
      have hx₀_in : x₀ ∈ D ∩ A := i.property
      have hx₀_diff : DifferentiableAt ℝ d x₀ := by simpa [D] using hx₀_in.1
      have hx₀_pos : 0 < d x₀ := hA_sub hx₀_in.2
      let r₀ := r x₀ hx₀_in
      have hr₀_pos : 0 < r₀ := hr_pos x₀ hx₀_in
      have h_grad : ∀ᵐ (z : E n) ∂volume.restrict (ball x₀ r₀),
          ‖fderiv ℝ d z - fderiv ℝ d x₀‖ ≤ ε := h_grad_close x₀ hx₀_in
      have h₁ : ‖fderiv ℝ d x₀‖ = 1 := norm_fderiv_infDist_eq_one hC hne hx₀_diff hx₀_pos
      have hU_eq : U k = ball x₀ (r₀ / 2) := by
        dsimp only [U, U_idx]
        <;> congr
        <;> rfl
      have hC'_sub2 : C' ⊆ closedBall x₀ (r₀ / 2) := by
        rw [hU_eq] at hC'_sub
        intro z hz
        have h3 : z ∈ ball x₀ (r₀ / 2) := hC'_sub hz
        have h4 : dist z x₀ < r₀ / 2 := by simpa [Metric.mem_ball] using h3
        simpa [Metric.mem_closedBall] using le_of_lt h4
      have hC'_bdd : Bornology.IsBounded C' := by
        rw [hU_eq] at hC'_sub
        rw [Metric.isBounded_iff]
        refine ⟨2 * (r₀ / 2), ?_⟩
        intro z hz w hw
        have hz2 : z ∈ ball x₀ (r₀ / 2) := hC'_sub hz
        have hw2 : w ∈ ball x₀ (r₀ / 2) := hC'_sub hw
        have h1 : dist z w ≤ dist z x₀ + dist x₀ w := dist_triangle z x₀ w
        have h2 : dist z x₀ < r₀ / 2 := by simpa [Metric.mem_ball] using hz2
        have h3 : dist x₀ w < r₀ / 2 := by
          have h4 : dist w x₀ < r₀ / 2 := by simpa [Metric.mem_ball] using hw2
          rwa [dist_comm] at h4
        linarith
      have h_main := local_coarea_measurable_upper
        (hf := infDist_lipschitz) (h₁ := h₁) (hr := hr₀_pos) (hε := hε) (hε2 := hε2)
        (h_grad_close := h_grad) (hC := hC'_meas) (hC_sub := hC'_sub2) (hC_bdd := hC'_bdd) (hab := hab)
      have h_const : ENNReal.ofReal K_up = ENNReal.ofReal (1 + ε') := by rw [h1pε']
      rw [h_const] at h_main
      exact h_main
    have h_assembly := countable_coarea_inequality_assembly
      (hA := hA'_meas) (f := d) (hf := infDist_lipschitz.continuous.measurable)
      (ε := ε') (hε := hε'_pos) (a := a) (b := b) (hab := hab)
      (U := U) (hU_open := hU_open') (h_cover := hA'_sub) (h_local := h_local)
    let A_slice := {x ∈ A | a < d x ∧ d x ≤ b}
    let A'_slice := {x ∈ A' | a < d x ∧ d x ≤ b}
    have hA_slice_eq : volume A_slice = volume A'_slice := by
      have h1 : A_slice \ A'_slice ⊆ A \ A' := by
        intro x hx
        have hxA_slice : x ∈ A_slice := hx.1
        have hx_not_A'_slice : x ∉ A'_slice := hx.2
        have hxA : x ∈ A := hxA_slice.1
        have hxf : a < d x ∧ d x ≤ b := hxA_slice.2
        have hx_not_A' : x ∉ A' := by
          by_contra h3
          have h4 : x ∈ A'_slice := ⟨h3, hxf⟩
          exact hx_not_A'_slice h4
        exact ⟨hxA, hx_not_A'⟩
      have h2 : volume (A_slice \ A'_slice) = 0 := measure_mono_null h1 hA_diff_null
      have h_sub : A'_slice ⊆ A_slice := by
        intro x hx
        exact ⟨hx.1.1, hx.2⟩
      have h3 : A_slice = A'_slice ∪ (A_slice \ A'_slice) := by
        ext x
        simp only [Set.mem_union, Set.mem_diff]
        constructor
        · intro hx
          by_cases h4 : x ∈ A'_slice
          · exact Or.inl h4
          · exact Or.inr ⟨hx, h4⟩
        · rintro (h | ⟨h, _⟩)
          · exact h_sub h
          · exact h
      rw [h3]
      have h4 : volume (A'_slice ∪ (A_slice \ A'_slice)) = volume A'_slice := by
        have hIoc_meas : MeasurableSet (Set.Ioc a b) := by
          have h1 : MeasurableSet (Set.Ioi a) := isOpen_Ioi.measurableSet
          have h2 : MeasurableSet (Set.Iic b) := isClosed_Iic.measurableSet
          exact h1.inter h2
        have hpreim : MeasurableSet (d ⁻¹' (Set.Ioc a b)) :=
          hIoc_meas.preimage infDist_lipschitz.continuous.measurable
        have h_slice_meas : MeasurableSet (A'_slice) :=
          hA'_meas.inter hpreim
        have h_diff_meas : MeasurableSet (A_slice \ A'_slice) :=
          (hA.inter hpreim).diff h_slice_meas
        have h_disj : Disjoint A'_slice (A_slice \ A'_slice) := by
          rw [Set.disjoint_left]
          intro x hx1 hx2
          exact hx2.2 hx1
        have h_union : volume (A'_slice ∪ (A_slice \ A'_slice)) =
            volume A'_slice + volume (A_slice \ A'_slice) :=
          measure_union h_disj h_diff_meas
        rw [h_union, h2, add_zero]
      exact h4
    have h_mono : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A' | d x = s} ≤
        ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | d x = s} := by
      apply lintegral_mono
      intro s
      apply MeasureTheory.measure_mono
      intro y hy
      exact ⟨hy.1.1, hy.2⟩
    calc
      volume A_slice
        = volume A'_slice := hA_slice_eq
      _ ≤ ENNReal.ofReal (1 + ε') * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A' | d x = s} := h_assembly
      _ = ENNReal.ofReal K_up * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A' | d x = s} := by
        rw [show (1 + ε') = K_up from h1pε']
      _ ≤ ENNReal.ofReal K_up * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | d x = s} := by
        exact mul_le_mul_left' h_mono _

/-- Helper: for finite `x : ENNReal`, if `∀ δ > 0, y ≤ ofReal(1+δ) * x` then `y ≤ x`. -/
lemma le_of_forall_one_plus_delta_mul {x y : ENNReal} (hx : x ≠ ⊤)
    (h : ∀ (δ : ℝ), 0 < δ → y ≤ ENNReal.ofReal (1 + δ) * x) : y ≤ x := by
  by_cases hy : y = ⊤
  · have h1 : ENNReal.ofReal (1 + (1 : ℝ)) * x ≠ ⊤ :=
      mul_ne_top ENNReal.ofReal_ne_top hx
    have h2 : y ≤ ENNReal.ofReal (1 + (1 : ℝ)) * x := h 1 (by norm_num)
    rw [hy] at h2
    exact False.elim (h1 (top_le_iff.mp h2))
  · have hy_ne_top : y ≠ ⊤ := hy
    by_contra h'
    have hxy : x < y := lt_of_not_ge h'
    let xr : ℝ := x.toReal
    let yr : ℝ := y.toReal
    have hxr_nonneg : 0 ≤ xr := by positivity
    have hxy_real : xr < yr := (ENNReal.toReal_lt_toReal hx hy_ne_top).mpr hxy
    have h_exists : ∃ (δ : ℝ), 0 < δ ∧ (1 + δ) * xr < yr := by
      by_cases hxr0 : xr = 0
      · refine ⟨1, by norm_num, ?_⟩
        rw [hxr0] <;> linarith
      · have hxr_pos : 0 < xr := by positivity
        let δ : ℝ := (yr - xr) / (2 * xr)
        have hδ_pos : 0 < δ := by positivity
        have h5 : (1 + δ) * xr < yr := by
          have h6 : (yr - xr) / (2 * xr) * xr = (yr - xr) / 2 := by
            field_simp [hxr_pos.ne'] <;> ring
          simp only [δ, add_mul]
          linarith
        exact ⟨δ, hδ_pos, h5⟩
    rcases h_exists with ⟨δ, hδ_pos, h_lt⟩
    have hx_eq : x = ENNReal.ofReal xr := by
      rw [ENNReal.ofReal_toReal hx]
    have hy_eq : y = ENNReal.ofReal yr := by
      rw [ENNReal.ofReal_toReal hy_ne_top]
    have h_pos1 : 0 ≤ (1 + δ) * xr := by positivity
    have h6 : ENNReal.ofReal ((1 + δ) * xr) < ENNReal.ofReal yr :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h_pos1).mpr h_lt
    have h7 : ENNReal.ofReal (1 + δ) * x = ENNReal.ofReal ((1 + δ) * xr) := by
      rw [hx_eq, ENNReal.ofReal_mul (by positivity)] <;> ring
    have h8 : ENNReal.ofReal (1 + δ) * x < y := by
      rw [h7, hy_eq]
      exact h6
    have h9 : y ≤ ENNReal.ofReal (1 + δ) * x := h δ hδ_pos
    exact not_le.mpr h8 h9

/-- **Exact global distance coarea upper bound (ε → 0).**

For a nonempty closed `C`, bounded measurable `A ⊆ {d > 0}`:

```
volume {x ∈ A | a < d x ≤ b} ≤ ∫⁻ s in Ioc a b, μHE[n-1] {x ∈ A | d x = s}
```

where `d(x) = infDist x C`. -/
theorem distance_coarea_upper_exact {C : Set (E n)} (hC : IsClosed C) (hne : C.Nonempty)
    {A : Set (E n)} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (hA_sub : A ⊆ {x | 0 < infDist x C})
    {a b : ℝ} (hab : a < b) :
    volume {x ∈ A | a < infDist x C ∧ infDist x C ≤ b} ≤
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | infDist x C = s} := by
  let d := fun x : E n => infDist x C
  let ν : ENNReal := ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | d x = s}
  let S : Set (E n) := {x ∈ A | a < d x ∧ d x ≤ b}
  by_cases hν_top : ν = ⊤
  · have h_goal : volume S ≤ ν := by
      have h9 : ν = ⊤ := hν_top
      rw [h9]
      exact le_top
    exact h_goal
  · have hν_ne_top : ν ≠ ⊤ := hν_top
    have h_main : ∀ (ε : ℝ), 0 < ε → ε < 1 →
        volume S ≤ ENNReal.ofReal (((1 + ε) ^ (n - 1 : ℕ)) / ((1 - ε) ^ n)) * ν := by
      intro ε hε hε2
      exact distance_coarea_upper hC hne hA hA_bdd hA_sub hab hε hε2
    let f : ℝ → ℝ := fun ε => ((1 + ε) ^ (n - 1 : ℕ)) / ((1 - ε) ^ n)
    have h_f0 : f 0 = 1 := by
      simp [f]
      <;> field_simp
      <;> ring
    have h1_cont : Continuous (fun ε : ℝ => (1 + ε) ^ (n - 1 : ℕ)) := by
      have h : Continuous (fun ε : ℝ => 1 + ε) := continuous_const.add continuous_id
      exact h.pow (n - 1)
    have h2_cont : Continuous (fun ε : ℝ => (1 - ε) ^ n) := by
      have h : Continuous (fun ε : ℝ => 1 - ε) := continuous_const.sub continuous_id
      exact h.pow n
    have h_cont : ContinuousAt f 0 := by
      have h1 : ContinuousAt (fun ε : ℝ => (1 + ε) ^ (n - 1 : ℕ)) 0 := h1_cont.continuousAt
      have h2 : ContinuousAt (fun ε : ℝ => (1 - ε) ^ n) 0 := h2_cont.continuousAt
      have h3 : (1 - (0 : ℝ)) ^ n ≠ 0 := by
        have h4 : (1 - (0 : ℝ)) ^ n = 1 := by simp
        rw [h4]; norm_num
      exact h1.div h2 h3
    have h_goal : ∀ (δ : ℝ), 0 < δ → volume S ≤ ENNReal.ofReal (1 + δ) * ν := by
      intro δ hδ
      have h_tendsto : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 1) := by
        have h11 : Filter.Tendsto f (nhds 0) (nhds 1) := by
          simpa [h_f0] using h_cont.tendsto
        exact h11.mono_left nhdsWithin_le_nhds
      have h1_ev0 : ∀ᶠ (ε : ℝ) in nhdsWithin 0 (Ioi (0 : ℝ)), f ε ∈ Metric.ball (1 : ℝ) δ :=
        h_tendsto (Metric.ball_mem_nhds 1 hδ)
      have h1_ev : ∀ᶠ (ε : ℝ) in nhdsWithin 0 (Ioi (0 : ℝ)), f ε < 1 + δ :=
        h1_ev0.mono (fun ε hε => by
          have h : dist (f ε) 1 < δ := by simpa [Metric.mem_ball] using hε
          have h2 : |f ε - 1| < δ := by simpa [dist_eq_norm] using h
          linarith [abs_lt.mp h2])
      have h2_ev : ∀ᶠ (ε : ℝ) in nhdsWithin 0 (Ioi (0 : ℝ)), ε < 1 := by
        have h_open : IsOpen (Iio (1 : ℝ)) := isOpen_Iio
        have h_mem : (0 : ℝ) ∈ Iio (1 : ℝ) := by norm_num
        have h_nhds : Iio (1 : ℝ) ∈ nhds (0 : ℝ) := IsOpen.mem_nhds h_open h_mem
        have h_nhds' : ∀ᶠ (ε : ℝ) in nhds (0 : ℝ), ε ∈ Iio (1 : ℝ) := h_nhds
        have h_nhds'' : ∀ᶠ (ε : ℝ) in nhds (0 : ℝ), ε < 1 := h_nhds'.mono (fun ε hε => hε)
        exact h_nhds''.filter_mono nhdsWithin_le_nhds
      have h_ev : ∀ᶠ (ε : ℝ) in nhdsWithin 0 (Ioi (0 : ℝ)), 0 < ε ∧ f ε < 1 + δ ∧ ε < 1 := by
        have h_pos : ∀ᶠ (ε : ℝ) in nhdsWithin 0 (Ioi (0 : ℝ)), 0 < ε := self_mem_nhdsWithin
        exact h_pos.and (h1_ev.and h2_ev)
      rcases h_ev.exists with ⟨ε, hε_pos, h_and⟩
      have hK_lt : f ε < 1 + δ := h_and.1
      have hε_lt1 : ε < 1 := h_and.2
      have hK_le : f ε ≤ 1 + δ := le_of_lt hK_lt
      have h1' : ENNReal.ofReal (f ε) ≤ ENNReal.ofReal (1 + δ) := ENNReal.ofReal_le_ofReal hK_le
      have h2' := h_main ε hε_pos hε_lt1
      exact le_trans h2' (mul_le_mul_right' h1' ν)
    exact le_of_forall_one_plus_delta_mul hν_ne_top h_goal

end Geometry
