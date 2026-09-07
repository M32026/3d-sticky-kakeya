module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.MainAssembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.TubeNull
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.ProcessIntervalsResult
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.TotalSlope
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.IntervalUtils
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# General adapter for Combinatorial Kaufman decomposition

Removes the monotonicity requirement from the established theorem components.

1. `tubeNull_general`: quantitative Rademacher for arbitrary 2-Lipschitz functions,
   proved by reducing to the monotone case via `h(x) = f(x)/2 + x`.

2. `combinatorialKaufman_general`: full interval decomposition for arbitrary
   2-Lipschitz functions satisfying a lower slope bound.

Whiteprint node: multiscale_decomp/tube_null + multiscale_decomp/combinatorial_kaufman
Depends on: CombinatorialKaufman/TubeNull, CombinatorialKaufman/ProcessIntervals
-/

noncomputable section

open CombinatorialKaufman
open CombinatorialKaufman.MainAssembly
open CombinatorialKaufman.TubeNull
open CombinatorialKaufman.ProcessIntervalsResult

namespace DirecretisedFurstenbergEstimate.GeneralAdapter

/-! ========================================================================
   General tube-null lemma (no monotonicity required)
   ======================================================================== -/

/-- Quantitative Rademacher theorem for arbitrary 2-Lipschitz functions.

Given ε > 0, there exists τ > 0 such that every 2-Lipschitz f on [a,b]
admits a finite family of disjoint ε-linear intervals of length ≥ τ·(b-a)
covering all but ε·(b-a) of [a,b]. -/
theorem tubeNull_general {ε : ℝ} (hε : 0 < ε) :
    ∃ (τ : ℝ), 0 < τ ∧ ∀ (f : ℝ → ℝ) (a b : ℝ),
      a < b →
      (∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → |f x - f y| ≤ 2 * |x - y|) →
      ∃ (I : Finset (ℝ × ℝ)),
        (∀ p ∈ I, EpsilonLinear f ε p.1 p.2) ∧
        (∀ p ∈ I, p.2 - p.1 ≥ τ * (b - a)) ∧
        (∀ p ∈ I, a ≤ p.1 ∧ p.2 ≤ b) ∧
        (∀ p ∈ I, ∀ q ∈ I, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1) ∧
        (b - a) - ∑ p ∈ I, (p.2 - p.1) ≤ ε * (b - a) := by
  have hε2 : 0 < ε / 2 := by positivity
  rcases tubeNull_uniform hε2 with ⟨τ, hτ_pos, h_main⟩
  refine ⟨τ, hτ_pos, ?_⟩
  intro f a b hab hlip
  -- Define h(x) = f(x)/2 + x. Then h is 2-Lipschitz and monotone on [a,b].
  let h : ℝ → ℝ := fun x => f x / 2 + x
  have h_lip_h : ∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → |h x - h y| ≤ 2 * |x - y| := by
    intro x y hx hy
    have h1 : |f x - f y| ≤ 2 * |x - y| := hlip x y hx hy
    have h2 : |h x - h y| = |(f x - f y) / 2 + (x - y)| := by
      dsimp only [h]
      have h_eq : f x / 2 + x - (f y / 2 + y) = (f x - f y) / 2 + (x - y) := by ring
      rw [h_eq]
    have h3 : |(f x - f y) / 2 + (x - y)| ≤ |(f x - f y) / 2| + |x - y| := by
      exact abs_add_le ((f x - f y) / 2) (x - y)
    have h4 : |(f x - f y) / 2| ≤ |x - y| := by
      have h5 : |(f x - f y) / 2| = |f x - f y| / 2 := by
        rw [abs_div] <;> norm_num
      rw [h5]
      linarith
    calc |h x - h y|
      = |(f x - f y) / 2 + (x - y)| := h2
    _ ≤ |(f x - f y) / 2| + |x - y| := h3
    _ ≤ |x - y| + |x - y| := by gcongr
    _ = 2 * |x - y| := by ring
  have h_mon_h : ∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y → h x ≤ h y := by
    intro x y hx hy hxy
    have h1 : f x - f y ≤ 2 * (y - x) := by
      have h2 : |f x - f y| ≤ 2 * |x - y| := hlip x y hx hy
      have h3 : x - y ≤ 0 := by linarith [hxy]
      have h4 : |x - y| = y - x := by
        rw [abs_of_nonpos h3] <;> linarith
      rw [h4] at h2
      have h5 : f x - f y ≤ |f x - f y| := le_abs_self _
      linarith
    dsimp only [h]
    linarith
  rcases h_main h a b hab h_lip_h h_mon_h with ⟨I0, hI0_eps, hI0_len, hI0_cont, hI0_nonover, hI0_cover⟩
  -- Key relation: h is (ε/2)-linear on [c,d] iff f is ε-linear on [c,d]
  have h_transfer : ∀ (c d : ℝ), c < d → EpsilonLinear h (ε / 2) c d → EpsilonLinear f ε c d := by
    intro c d hcd h_eps_h
    intro x hx
    have h_slope : chordSlope h c d = chordSlope f c d / 2 + 1 := by
      dsimp only [chordSlope, h]
      field_simp [show d - c ≠ 0 by linarith] <;> ring
    have h_cv : chordValue h c d x = chordValue f c d x / 2 + x := by
      dsimp only [chordValue, h]
      rw [h_slope] <;> ring
    have h_eq1 : h x - chordValue h c d x = (f x - chordValue f c d x) / 2 := by
      rw [h_cv] <;> ring
    have h6 : |h x - chordValue h c d x| ≤ (ε / 2) * (d - c) := h_eps_h x hx
    rw [h_eq1] at h6
    have h7 : |(f x - chordValue f c d x) / 2| = |f x - chordValue f c d x| / 2 := by
      rw [abs_div] <;> norm_num
    rw [h7] at h6
    linarith
  have hI_eps : ∀ p ∈ I0, EpsilonLinear f ε p.1 p.2 := by
    intro p hp
    have hcd : p.1 < p.2 := by
      have h_len : p.2 - p.1 ≥ τ * (b - a) := hI0_len p hp
      have h_pos : 0 < τ * (b - a) := by positivity
      linarith
    exact h_transfer p.1 p.2 hcd (hI0_eps p hp)
  have hI0_cover' : (b - a) - ∑ p ∈ I0, (p.2 - p.1) ≤ ε * (b - a) := by
    have h9 : (b - a) - ∑ p ∈ I0, (p.2 - p.1) ≤ (ε / 2) * (b - a) := hI0_cover
    have h10 : (ε / 2) * (b - a) ≤ ε * (b - a) := by
      have h11 : 0 < b - a := by linarith
      gcongr <;> linarith
    exact h9.trans h10
  exact ⟨I0, hI_eps, hI0_len, hI0_cont, hI0_nonover, hI0_cover'⟩

/-! ========================================================================
   General combinatorial Kaufman decomposition (no monotonicity required)
   ======================================================================== -/

/-- Convert main-file Lipschitz condition to `LipschitzOnWith`. -/
lemma lip_to_lipschitzOnWith {f : ℝ → ℝ} {m : ℝ}
    (hlip : ∀ x y, x ∈ Set.Icc 0 m → y ∈ Set.Icc 0 m → |f x - f y| ≤ 2 * |x - y|) :
    LipschitzOnWith 2 f (Set.Icc 0 m) := by
  intro x hx y hy
  have h : |f x - f y| ≤ 2 * |x - y| := hlip x y hx hy
  have h' : dist (f x) (f y) ≤ 2 * dist x y := by
    simpa [Real.dist_eq] using h
  have h_d1 : 0 ≤ dist (f x) (f y) := dist_nonneg
  have h_d2 : 0 ≤ dist x y := dist_nonneg
  have h2 : ENNReal.ofReal (dist (f x) (f y)) ≤ ENNReal.ofReal (2 * dist x y) := by
    exact ENNReal.ofReal_le_ofReal h'
  have h3 : ENNReal.ofReal (2 * dist x y) = (2 : ENNReal) * ENNReal.ofReal (dist x y) := by
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    <;> norm_cast
  rw [edist_dist, edist_dist]
  rw [h3] at h2
  exact h2

/-- Extract pairwise disjointness for arbitrary pair from List.Pairwise. -/
lemma pairwise_disjoint_all {J : List (ℝ × ℝ)}
    (hJ_disj : PairwiseInteriorDisjointList J) :
    ∀ (p q : ℝ × ℝ), p ∈ J → q ∈ J → p ≠ q →
      Disjoint (Set.Ioo p.1 p.2) (Set.Ioo q.1 q.2) := by
  induction hJ_disj with
  | nil =>
    intro p q hp hq hne
    contradiction
  | @cons x l hx hl ih =>
    intro p q hp hq hne
    simp only [List.mem_cons] at hp hq
    rcases hp with (rfl | hp') <;> rcases hq with (rfl | hq')
    · contradiction
    · exact hx q hq'
    · exact (hx p hp').symm
    · exact ih p q hp' hq' hne

/-- Combinatorial Kaufman decomposition for arbitrary 2-Lipschitz functions.

Given 0 < s < t ≤ 2 and ε > 0, set C = 2 + 2/(t-s) and δ = ε/C.
For any 2-Lipschitz f with f(0)=0 and f(x) ≥ t*x - δ*m, there exists τ > 0
and a finite family of disjoint intervals such that:
- Each interval is either ε-linear with slope ≥ s, or ε-superlinear with slope = s
- Each interval has length ≥ τ*m
- The complement has measure ≤ ε*m
-/
theorem combinatorialKaufman_general {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t ≤ 2)
    {ε : ℝ} (hε : 0 < ε) :
    let C := 2 + 2 / (t - s)
    ∃ (τ : ℝ), 0 < τ ∧
    ∀ (f : ℝ → ℝ) (m : ℝ),
      0 < m →
      (∀ x y, x ∈ Set.Icc 0 m → y ∈ Set.Icc 0 m → |f x - f y| ≤ 2 * |x - y|) →
      f 0 = 0 →
      (∀ x ∈ Set.Icc 0 m, f x ≥ t * x - (ε / C) * m) →
      ∃ (I : Finset (ℝ × ℝ)),
        (∀ p ∈ I,
          (EpsilonLinear f ε p.1 p.2 ∧ s ≤ chordSlope f p.1 p.2) ∨
          (EpsilonSuperlinear f ε p.1 p.2 ∧ chordSlope f p.1 p.2 = s)) ∧
        (∀ p ∈ I, p.2 - p.1 ≥ τ * m) ∧
        (∀ p ∈ I, 0 ≤ p.1 ∧ p.2 ≤ m) ∧
        (∀ p ∈ I, ∀ q ∈ I, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1) ∧
        m - ∑ p ∈ I, (p.2 - p.1) ≤ ε * m := by
  dsimp only
  let C := 2 + 2 / (t - s)
  let r := t - s
  have hr_pos : 0 < r := by linarith
  have hC_pos : 0 < C := by positivity
  have hC2 : C ≥ 2 := by
    dsimp only [C]
    have h_pos : 0 < 2 / r := by positivity
    linarith
  by_cases h_triv : ε ≥ 1
  · -- Trivial case: empty Finset works since m ≤ ε*m
    refine ⟨1, by positivity, fun f m hm_pos _ _ _ => ?_⟩
    have h_goal : m ≤ ε * m := by
      have h1 : (1 : ℝ) ≤ ε := by linarith
      calc m = 1 * m := by ring
        _ ≤ ε * m := by gcongr
    exact ⟨∅, by simp, by simp, by simp, by simp, by simpa using h_goal⟩
  · -- ε < 1
    have hε_lt1 : ε < 1 := by linarith
    let δ : ℝ := ε / C
    have hδ_pos : 0 < δ := by positivity
    have hδ_lt1 : δ < 1 := by
      dsimp only [δ]
      have h1 : ε / C ≤ ε / 2 := by gcongr <;> linarith
      linarith
    have h2δ_le_ε : 2 * δ ≤ ε := by
      dsimp only [δ]
      have h1 : 2 / C ≤ 1 := by
        apply (div_le_one hC_pos).mpr
        linarith
      have h2 : 2 * (ε / C) = (2 / C) * ε := by ring
      rw [h2]
      have h3 : (2 / C) * ε ≤ 1 * ε := by gcongr
      linarith
    -- Get general tubeNull with quality δ²
    rcases tubeNull_general (hε := show 0 < δ^2 by positivity) with ⟨τ0, hτ0_pos, h_tubeNull⟩
    let τ_out : ℝ := δ * τ0
    have hτ_out_pos : 0 < τ_out := by positivity
    refine ⟨τ_out, hτ_out_pos, fun f m hm_pos hlip hf0 h_lower => ?_⟩
    have hlip' : LipschitzOnWith 2 f (Set.Icc 0 m) := lip_to_lipschitzOnWith hlip
    -- Apply tubeNull
    rcases h_tubeNull f 0 m (by linarith) hlip with ⟨I_finset, hI_eps, hI_len, hI_cont, hI_nonover, hI_cover⟩
    have hI_len' : ∀ p ∈ I_finset, p.2 - p.1 ≥ τ0 * m := by
      intro p hp
      have h := hI_len p hp
      simpa using h
    have hI_cover' : m - ∑ p ∈ I_finset, (p.2 - p.1) ≤ δ^2 * m := by
      have h : (m - 0) - ∑ p ∈ I_finset, (p.2 - p.1) ≤ δ^2 * (m - 0) := hI_cover
      simpa using h
    -- Convert Finset to sorted List
    rcases adapt_finset_to_list hτ0_pos hm_pos hI_eps hI_len' hI_cont hI_nonover hI_cover' with
      ⟨L, hL_lin, hL_len, hL_bound, hL_sorted, hL_disj, hL_gap⟩
    -- Extend f to continuous g
    rcases extend_continuous f hm_pos hlip' with ⟨g, hg_cont, hg_agree⟩
    have hg0 : g 0 = 0 := by
      have h0_in : (0 : ℝ) ∈ Set.Icc 0 m := by exact ⟨by linarith, by linarith⟩
      have h : g 0 = f 0 := hg_agree 0 h0_in
      rw [h, hf0]
    have hg_lower : ∀ x ∈ Set.Icc 0 m, t * x - δ * m ≤ g x := by
      intro x hx
      have h1 : g x = f x := hg_agree x hx
      rw [h1]
      exact h_lower x hx
    have hg_lip : LipschitzOnWith 2 g (Set.Icc 0 m) := by
      intro x hx y hy
      have h_eq : edist (g x) (g y) = edist (f x) (f y) := by
        rw [hg_agree x hx, hg_agree y hy]
      rw [h_eq]
      exact Metric.mem_closedEBall.mp (hlip' hx hy)
    -- Transfer linearity from f to g
    have hL_lin_g : ∀ (p : ℝ × ℝ), p ∈ L → EpsilonLinear g (δ^2) p.1 p.2 := by
      intro p hp
      have h_f_lin : EpsilonLinear f (δ^2) p.1 p.2 := hL_lin p hp
      have hpb : 0 ≤ p.1 ∧ p.2 ≤ m :=
        ⟨(hL_bound p hp).1, (hL_bound p hp).2.1⟩
      have hpl : p.1 < p.2 := (hL_bound p hp).2.2
      have h_agree : ∀ x ∈ Set.Icc p.1 p.2, g x = f x := by
        intro x hx
        have h_x_in : x ∈ Set.Icc 0 m := by
          exact ⟨by linarith [hpb.1, hx.1], by linarith [hpb.2, hx.2]⟩
        exact hg_agree x h_x_in
      intro x hx
      have h_eq1 : g x = f x := h_agree x hx
      have h_ga : g p.1 = f p.1 := h_agree p.1 ⟨by linarith, by linarith [hpl]⟩
      have h_gb : g p.2 = f p.2 := h_agree p.2 ⟨by linarith [hpl], by linarith⟩
      have h_eq2 : chordValue g p.1 p.2 x = chordValue f p.1 p.2 x := by
        simp [chordValue, chordSlope, h_ga, h_gb] <;> ring
      rw [h_eq1, h_eq2]
      exact h_f_lin x hx
    -- Apply process_intervals (now monotonicity-free)
    rcases CombinatorialKaufman.ProcessIntervalsResult.processIntervals_result g s t m δ δ τ0 hs hst ht hδ_pos hδ_lt1 hm_pos hτ0_pos hδ_pos
        hg_cont hg_lip hg0 hg_lower
        L hL_sorted hL_disj hL_lin_g hL_len hL_bound hL_gap
      with ⟨J, hJ_good, hJ_len, hJ_bound, hJ_sorted, hJ_disj, hJ_gap⟩
    -- Convert quality from 2δ to ε
    have hJ_good' : ∀ p ∈ J,
        (EpsilonLinear f ε p.1 p.2 ∧ s ≤ chordSlope f p.1 p.2) ∨
        (EpsilonSuperlinear f ε p.1 p.2 ∧ chordSlope f p.1 p.2 = s) := by
      intro p hp
      have hpb : 0 ≤ p.1 ∧ p.2 ≤ m ∧ p.1 < p.2 := hJ_bound p hp
      have h_agree : ∀ x ∈ Set.Icc p.1 p.2, g x = f x := by
        intro x hx
        have h_x_in : x ∈ Set.Icc 0 m := by
          exact ⟨by linarith [hpb.1, hx.1], by linarith [hpb.2.1, hx.2]⟩
        exact hg_agree x h_x_in
      have h_slope_eq : chordSlope g p.1 p.2 = chordSlope f p.1 p.2 := by
        have h1 : g p.1 = f p.1 := h_agree p.1 ⟨by linarith, by linarith [hpb.2.2]⟩
        have h2 : g p.2 = f p.2 := h_agree p.2 ⟨by linarith [hpb.2.2], by linarith⟩
        simp [chordSlope, h1, h2] <;> ring
      rcases hJ_good p hp with (h | h)
      · -- Linear case
        have h_lin_g : EpsilonLinear g (2 * δ) p.1 p.2 := h.1
        have h_lin_f : EpsilonLinear f (2 * δ) p.1 p.2 := by
          intro x hx
          have h4 := h_lin_g x hx
          have h_eq1 : g x = f x := h_agree x hx
          have h_ga : g p.1 = f p.1 := h_agree p.1 ⟨by linarith, by linarith [hpb.2.2]⟩
          have h_gb : g p.2 = f p.2 := h_agree p.2 ⟨by linarith [hpb.2.2], by linarith⟩
          have h_eq2 : chordValue g p.1 p.2 x = chordValue f p.1 p.2 x := by
            simp [chordValue, chordSlope, h_ga, h_gb] <;> ring
          rw [h_eq1, h_eq2] at h4
          exact h4
        have h_slope_ge : s ≤ chordSlope f p.1 p.2 := by
          rw [←h_slope_eq]
          exact h.2
        have h_lin_ε : EpsilonLinear f ε p.1 p.2 := by
          intro x hx
          have h6 : |f x - chordValue f p.1 p.2 x| ≤ (2 * δ) * (p.2 - p.1) := h_lin_f x hx
          have h7 : (2 * δ) * (p.2 - p.1) ≤ ε * (p.2 - p.1) := by
            gcongr <;> linarith [h2δ_le_ε]
          exact h6.trans h7
        exact Or.inl ⟨h_lin_ε, h_slope_ge⟩
      · -- Superlinear case
        have h_super_g : EpsilonSuperlinear g (2 * δ) p.1 p.2 := h.1
        have h_super_f : EpsilonSuperlinear f (2 * δ) p.1 p.2 := by
          intro x hx
          have h4 := h_super_g x hx
          have h_eq1 : g x = f x := h_agree x hx
          have h_ga : g p.1 = f p.1 := h_agree p.1 ⟨by linarith, by linarith [hpb.2.2]⟩
          have h_gb : g p.2 = f p.2 := h_agree p.2 ⟨by linarith [hpb.2.2], by linarith⟩
          have h_eq2 : chordValue g p.1 p.2 x = chordValue f p.1 p.2 x := by
            simp [chordValue, chordSlope, h_ga, h_gb] <;> ring
          rw [h_eq1, h_eq2] at h4
          exact h4
        have h_slope_eq_s : chordSlope f p.1 p.2 = s := by
          rw [←h_slope_eq]
          exact h.2
        have h_super_ε : EpsilonSuperlinear f ε p.1 p.2 := by
          intro x hx
          have h6 : chordValue f p.1 p.2 x - (2 * δ) * (p.2 - p.1) ≤ f x := h_super_f x hx
          have h7 : (2 * δ) * (p.2 - p.1) ≤ ε * (p.2 - p.1) := by
            gcongr <;> linarith [h2δ_le_ε]
          linarith
        exact Or.inr ⟨h_super_ε, h_slope_eq_s⟩
    -- Coverage gap check: δ + δ² + δ/r ≤ ε
    have h_gap_le : δ + δ^2 + δ / r ≤ ε := by
      dsimp only [δ, C, r]
      have hr_pos' : 0 < r := hr_pos
      have hC_pos' : 0 < C := hC_pos
      have hC_def : C = 2 + 2 / r := by rfl
      have hCr : C * r = 2 * r + 2 := by
        calc C * r
          = (2 + 2 / r) * r := by rw [hC_def]
        _ = 2 * r + (2 / r) * r := by ring
        _ = 2 * r + 2 := by
          have hdiv : (2 / r) * r = 2 := by
            field_simp [hr_pos'.ne'] <;> ring
          rw [hdiv] <;> ring
      have h4 : 1 / C + 1 / (C * r) = 1 / 2 := by
        have h_sum : 1 / C + 1 / (C * r) = (r + 1) / (C * r) := by
          field_simp [hC_pos'.ne', hr_pos'.ne'] <;> ring
        rw [h_sum, hCr]
        field_simp [hr_pos'.ne'] <;> ring
      have h5 : C ≥ 2 := hC2
      have h6 : 1 / C^2 ≤ 1 / 4 := by
        have h7 : C^2 ≥ 4 := by nlinarith
        have h8 : (0 : ℝ) < C^2 := by positivity
        rw [one_div_le_one_div] <;> nlinarith
      have h9 : ε < 1 := hε_lt1
      have h10 : ε / C^2 ≤ 1 / C^2 := by
        have h11 : 0 < C^2 := by positivity
        gcongr <;> linarith
      have h12 : 1 / C + ε / C^2 + 1 / (C * r) ≤ 1 := by
        calc 1 / C + ε / C^2 + 1 / (C * r)
          ≤ 1 / C + 1 / C^2 + 1 / (C * r) := by gcongr
        _ = (1 / C + 1 / (C * r)) + 1 / C^2 := by ring
        _ = 1 / 2 + 1 / C^2 := by rw [h4]
        _ ≤ 1 / 2 + 1 / 4 := by gcongr
        _ = 3 / 4 := by norm_num
        _ ≤ 1 := by norm_num
      have h13 : ε / C + (ε / C)^2 + (ε / C) / r = ε * (1 / C + ε / C^2 + 1 / (C * r)) := by
        have h14 : (ε / C) / r = ε / (C * r) := by
          field_simp [hC_pos'.ne', hr_pos'.ne'] <;> ring
        rw [h14]
        <;> field_simp [hC_pos'.ne'] <;> ring
      rw [h13]
      have h15 : ε * (1 / C + ε / C^2 + 1 / (C * r)) ≤ ε * 1 := by
        gcongr <;> linarith
      linarith
    have hJ_gap' : m - (J.map (fun p : ℝ × ℝ => p.2 - p.1)).sum ≤ ε * m := by
      have h : m - (J.map (fun p : ℝ × ℝ => p.2 - p.1)).sum ≤ (δ + δ^2 + δ / r) * m := hJ_gap
      have h2 : (δ + δ^2 + δ / r) * m ≤ ε * m := by gcongr <;> linarith [h_gap_le]
      exact h.trans h2
    -- Convert List to Finset
    let I : Finset (ℝ × ℝ) := J.toFinset
    have hJ_nodup : J.Nodup := hJ_sorted.nodup
    have h_mem_iff : ∀ {p : ℝ × ℝ}, p ∈ I ↔ p ∈ J := by
      intro p; simp [I, List.mem_toFinset, hJ_nodup]
    have h1 : ∀ p ∈ I, (EpsilonLinear f ε p.1 p.2 ∧ s ≤ chordSlope f p.1 p.2) ∨
        (EpsilonSuperlinear f ε p.1 p.2 ∧ chordSlope f p.1 p.2 = s) := by
      intro p hp; exact hJ_good' p (h_mem_iff.mp hp)
    have h2 : ∀ p ∈ I, p.2 - p.1 ≥ τ_out * m := by
      intro p hp
      have h3 : p.2 - p.1 ≥ δ * τ0 * m := hJ_len p (h_mem_iff.mp hp)
      simpa [τ_out] using h3
    have h3 : ∀ p ∈ I, 0 ≤ p.1 ∧ p.2 ≤ m := by
      intro p hp
      let h := hJ_bound p (h_mem_iff.mp hp)
      exact ⟨h.1, h.2.1⟩
    have h4 : ∀ p ∈ I, ∀ q ∈ I, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1 := by
      intro p hp q hq hne
      have hpl : p.1 < p.2 := (hJ_bound p (h_mem_iff.mp hp)).2.2
      have hql : q.1 < q.2 := (hJ_bound q (h_mem_iff.mp hq)).2.2
      have h_disj : Disjoint (Set.Ioo p.1 p.2) (Set.Ioo q.1 q.2) :=
        pairwise_disjoint_all hJ_disj p q (h_mem_iff.mp hp) (h_mem_iff.mp hq) hne
      by_cases h : p.2 ≤ q.1
      · exact Or.inl h
      · have h' : q.1 < p.2 := by linarith
        by_cases h2 : q.2 ≤ p.1
        · exact Or.inr h2
        · have h2' : p.1 < q.2 := by linarith
          have h_max_lt_min : max p.1 q.1 < min p.2 q.2 := by
            simp [max_lt_iff, lt_min_iff] <;> tauto
          set mid : ℝ := (max p.1 q.1 + min p.2 q.2) / 2 with hmid_def
          have hmid1 : max p.1 q.1 < mid := by
            rw [hmid_def]; linarith [h_max_lt_min]
          have hmid2 : mid < min p.2 q.2 := by
            rw [hmid_def]; linarith [h_max_lt_min]
          have hmp : mid ∈ Set.Ioo p.1 p.2 := by
            have h1 : p.1 ≤ max p.1 q.1 := le_max_left _ _
            have h2 : min p.2 q.2 ≤ p.2 := min_le_left _ _
            have h3 : p.1 < mid := by linarith
            have h4 : mid < p.2 := by linarith
            exact ⟨h3, h4⟩
          have hmq : mid ∈ Set.Ioo q.1 q.2 := by
            have h1 : q.1 ≤ max p.1 q.1 := le_max_right _ _
            have h2 : min p.2 q.2 ≤ q.2 := min_le_right _ _
            have h3 : q.1 < mid := by linarith
            have h4 : mid < q.2 := by linarith
            exact ⟨h3, h4⟩
          have h_contra : mid ∈ (Set.Ioo p.1 p.2 ∩ Set.Ioo q.1 q.2) := ⟨hmp, hmq⟩
          exact False.elim (Set.not_disjoint_iff.mpr ⟨mid, h_contra⟩ h_disj)
    have h5 : ∑ p ∈ I, (p.2 - p.1) = (J.map (fun p : ℝ × ℝ => p.2 - p.1)).sum := by
      have h_dedup : J.dedup = J := List.dedup_eq_self.mpr hJ_nodup
      have h_val : I.val = (J.dedup : Multiset (ℝ × ℝ)) := by
        have h_I : I = J.toFinset := by rfl
        rw [h_I]
        exact List.toFinset_val J
      have h_sum : ∑ p ∈ I, (p.2 - p.1) = (I.val.map (fun p : ℝ × ℝ => p.2 - p.1)).sum :=
        Finset.sum_eq_multiset_sum I (fun x => x.2 - x.1)
      rw [h_sum, h_val, h_dedup] <;> rfl
    have h6 : m - ∑ p ∈ I, (p.2 - p.1) ≤ ε * m := by
      rw [h5]; exact hJ_gap'
    exact ⟨I, h1, h2, h3, h4, h6⟩

end DirecretisedFurstenbergEstimate.GeneralAdapter
