module

/-
  Main theorem assembly for the Combinatorial Kaufman Decomposition.

  This module provides the proof structure that ties together:
  - tube_null (quantitative Rademacher)
  - processIntervals (merging and classification)
  - total_slope (slope sum bound)
  - Fin conversion utilities

  Constant selection:
    r = t - s
    A = 1 + 6 / r
    δ = ε / r

  With A*ε < r, we have ε/r < 1/A < 1, so δ < 1.

  processIntervals uses the target's lower bound f(x) ≥ tx - εm,
  giving threshold discard ε/r.

  Coverage gap: δ + δ² + ε/r = 2ε/r + (ε/r)² ≤ 3ε/r = (A-1)ε/2.

  Quality: output is 2δ = 2ε/r ≤ A*ε.

  Slope sum: ≥ f(m) - 2*gap ≥ (tm - εm) - 2*(3ε/r*m)
           = (t - (1 + 6/r)*ε)*m = (t - A*ε)*m.

  Whiteprint node: main_theorem
  Depends on: process_intervals, total_slope
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.DefinitionProperties
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.IntervalUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.FinConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.TotalSlope
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open scoped BigOperators

namespace CombinatorialKaufman.MainAssembly

/-- The type of the tube-null lemma we need. -/
def TubeNullResult : Prop :=
  ∀ (ε' : ℝ), 0 < ε' →
    ∃ (τ0 : ℝ), 0 < τ0 ∧
      ∀ (f : ℝ → ℝ) (m : ℝ), 0 < m →
        LipschitzOnWith 2 f (Set.Icc 0 m) →
        MonotoneOn f (Set.Icc 0 m) →
        ∃ (L : List (ℝ × ℝ)),
          (∀ p ∈ L, EpsilonLinear f ε' p.1 p.2) ∧
          (∀ p ∈ L, p.2 - p.1 ≥ τ0 * m) ∧
          (∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ≤ m ∧ p.1 < p.2) ∧
          SortedByLeft L ∧
          PairwiseInteriorDisjointList L ∧
          m - (L.map (fun p => p.2 - p.1)).sum ≤ ε' * m

/-- The type of the processIntervals lemma we need.

  `δ` is the processing quality (tube_null runs at δ², output at 2δ).
  `ε'` is the lower-bound error from the theorem statement.
  The threshold discard is ε'/(t-s), so the total gap is δ + δ² + ε'/(t-s).
-/
def ProcessIntervalsResult : Prop :=
  ∀ (f : ℝ → ℝ) (s t m δ ε' τ0 : ℝ),
    0 < s → s < t → t ≤ 2 → 0 < δ → δ < 1 → 0 < m → 0 < τ0 → 0 < ε' →
    Continuous f →
    LipschitzOnWith 2 f (Set.Icc 0 m) →
    f 0 = 0 →
    (∀ x ∈ Set.Icc 0 m, t * x - ε' * m ≤ f x) →
    ∀ (L : List (ℝ × ℝ)),
      SortedByLeft L →
      PairwiseInteriorDisjointList L →
      (∀ p ∈ L, EpsilonLinear f (δ^2) p.1 p.2) →
      (∀ p ∈ L, p.2 - p.1 ≥ τ0 * m) →
      (∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ≤ m ∧ p.1 < p.2) →
      m - (L.map (fun p => p.2 - p.1)).sum ≤ δ^2 * m →
      ∃ (J : List (ℝ × ℝ)),
        (∀ p ∈ J,
          (EpsilonLinear f (2*δ) p.1 p.2 ∧ s ≤ chordSlope f p.1 p.2) ∨
          (EpsilonSuperlinear f (2*δ) p.1 p.2 ∧ chordSlope f p.1 p.2 = s)) ∧
        (∀ p ∈ J, p.2 - p.1 ≥ δ * τ0 * m) ∧
        (∀ p ∈ J, 0 ≤ p.1 ∧ p.2 ≤ m ∧ p.1 < p.2) ∧
        SortedByLeft J ∧
        PairwiseInteriorDisjointList J ∧
        m - (J.map (fun p => p.2 - p.1)).sum ≤ (δ + δ^2 + ε'/(t-s)) * m

/-- Extend a function that is 2-Lipschitz on [0,m] to a continuous function on ℝ. -/
lemma extend_continuous (f : ℝ → ℝ) {m : ℝ} (hm : 0 < m)
    (hlip : LipschitzOnWith 2 f (Set.Icc 0 m)) :
    ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ Set.Icc 0 m, g x = f x := by
  have hf_cont : ContinuousOn f (Set.Icc 0 m) := hlip.continuousOn
  let clamp : ℝ → ℝ := fun x => max 0 (min x m)
  have h_clamp_cont : Continuous clamp := by fun_prop
  have h_clamp_range : ∀ x, clamp x ∈ Set.Icc 0 m := by
    intro x
    have h1 : 0 ≤ clamp x := by simp [clamp] <;> linarith
    have h2 : clamp x ≤ m := by simp [clamp] <;> linarith [hm]
    exact ⟨h1, h2⟩
  let g : ℝ → ℝ := f ∘ clamp
  have h1 : ContinuousOn g Set.univ :=
    hf_cont.comp h_clamp_cont.continuousOn (fun x _ => h_clamp_range x)
  have hg_cont : Continuous g := by
    exact ContinuousOn.comp_continuous hf_cont h_clamp_cont h_clamp_range
  have hg_agree : ∀ x ∈ Set.Icc 0 m, g x = f x := by
    intro x hx
    have h_clamp_id : clamp x = x := by
      simp only [clamp]
      have hmin : min x m = x := by apply min_eq_left; linarith [hx.2]
      rw [hmin]
      have hmax : max 0 x = x := by apply max_eq_right; linarith [hx.1]
      rw [hmax]
    simp [g, h_clamp_id]
  exact ⟨g, hg_cont, hg_agree⟩

/-- Convert PairwiseInteriorDisjointList to the forall-disj form needed by total_slope. -/
lemma disj_list_to_forall {L : List (ℝ × ℝ)}
    (h_sorted : SortedByLeft L)
    (h_disj : PairwiseInteriorDisjointList L)
    (h_valid : ∀ p ∈ L, p.1 < p.2) :
    ∀ p ∈ L, ∀ q ∈ L, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1 := by
  have h_main : ∀ (L' : List (ℝ × ℝ)),
      SortedByLeft L' →
      PairwiseInteriorDisjointList L' →
      (∀ p ∈ L', p.1 < p.2) →
      ∀ p ∈ L', ∀ q ∈ L', p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1 := by
    intro L'
    induction L' with
    | nil => simp
    | cons a t ih =>
      intro h_sorted' h_disj' h_valid'
      have h_a_valid : a.1 < a.2 := h_valid' a (by simp)
      have h_t_valid : ∀ p ∈ t, p.1 < p.2 := fun p hp => h_valid' p (by simp [hp])
      have h_left_rel : ∀ p ∈ t, a.1 < p.1 := by
        have h := List.pairwise_cons.mp h_sorted'
        exact h.1
      have h_t_sorted : SortedByLeft t := by
        have h := List.pairwise_cons.mp h_sorted'
        exact h.2
      have h_t_disj : PairwiseInteriorDisjointList t := by
        have h := List.pairwise_cons.mp h_disj'
        exact h.2
      have h_disj_a : ∀ p ∈ t, Disjoint (Set.Ioo a.1 a.2) (Set.Ioo p.1 p.2) := by
        have h := List.pairwise_cons.mp h_disj'
        exact h.1
      intro p hp q hq hne
      by_cases hpa : p = a
      · have hq_ne_a : q ≠ a := by
          intro h_eq; apply hne; rw [hpa, h_eq]
        have hq_t : q ∈ t := by
          simp only [List.mem_cons] at hq; tauto
        have h : p.2 ≤ q.1 := by
          rw [hpa]
          exact sorted_disjoint_consecutive h_a_valid (h_t_valid q hq_t) (h_left_rel q hq_t) (h_disj_a q hq_t)
        exact Or.inl h
      · by_cases hqa : q = a
        · have hp_ne_a : p ≠ a := hpa
          have hp_t : p ∈ t := by
            simp only [List.mem_cons] at hp; tauto
          have h : q.2 ≤ p.1 := by
            rw [hqa]
            exact sorted_disjoint_consecutive h_a_valid (h_t_valid p hp_t) (h_left_rel p hp_t) (h_disj_a p hp_t)
          exact Or.inr h
        · have hp_t : p ∈ t := by
            simp only [List.mem_cons] at hp; tauto
          have hq_t : q ∈ t := by
            simp only [List.mem_cons] at hq; tauto
          exact ih h_t_sorted h_t_disj h_t_valid p hp_t q hq_t hne
  exact h_main L h_sorted h_disj h_valid

/-- Main assembly: given tube_null and processIntervals, prove the target theorem. -/
theorem combinatorial_kaufman_assembly
    (s t : ℝ)
    (hs : 0 < s) (hst : s < t) (ht : t ≤ 2)
    (h_tubeNull : TubeNullResult)
    (h_processIntervals : ProcessIntervalsResult) :
    ∃ (A : ℝ), A = 1 + 6 / (t - s) ∧
      ∀ (ε : ℝ), 0 < ε → A * ε < t - s →
        ∃ (τ : ℝ), 0 < τ ∧ τ ≤ ε ∧
          ∀ (m : ℝ) (f : ℝ → ℝ),
            0 < m →
            LipschitzOnWith 2 f (Set.Icc 0 m) →
            MonotoneOn f (Set.Icc 0 m) →
            f 0 = 0 →
            (∀ x ∈ Set.Icc 0 m, t * x - ε * m ≤ f x) →
            ∃ (n : ℕ) (I : Fin n → ℝ × ℝ),
              0 < n ∧
              PairwiseInteriorDisjoint I ∧
              (∀ i,
                0 ≤ (I i).1 ∧
                (I i).1 < (I i).2 ∧
                (I i).2 ≤ m ∧
                τ * m ≤ (I i).2 - (I i).1) ∧
              (1 - A * ε) * m ≤
                Finset.sum Finset.univ (fun i : Fin n => (I i).2 - (I i).1) ∧
              (t - A * ε) * m ≤
                Finset.sum Finset.univ (fun i : Fin n =>
                  ((I i).2 - (I i).1) * chordSlope f (I i).1 (I i).2) ∧
              (∀ i,
                (EpsilonLinear f (A * ε) (I i).1 (I i).2 ∧
                    s ≤ chordSlope f (I i).1 (I i).2 ∧
                    chordSlope f (I i).1 (I i).2 ≤ 2) ∨
                (EpsilonSuperlinear f (A * ε) (I i).1 (I i).2 ∧
                    chordSlope f (I i).1 (I i).2 = s)) := by
  set r : ℝ := t - s with hr_def
  have hr_pos : 0 < r := by linarith [hst]
  set A : ℝ := 1 + 6 / r with hA_def
  have hA_eq : A = 1 + 6 / (t - s) := by
    simp [hA_def, hr_def] <;> ring
  have hA_pos : 0 < A := by
    dsimp only [A, hA_def]
    have h : 0 < 6 / r := by positivity
    linarith
  refine' ⟨A, hA_eq, _⟩
  intro ε hε hAε_lt_r
  set δ : ℝ := ε / r with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have hε_r_lt1 : ε / r < 1 := by
    have h1 : A * ε < r := hAε_lt_r
    have h2 : ε / r < 1 / A := by
      have h3 : 0 < A * r := by positivity
      calc ε / r
        = (A * ε) / (A * r) := by field_simp [hA_pos.ne', hr_pos.ne'] <;> ring
      _ < r / (A * r) := by gcongr
      _ = 1 / A := by
        field_simp [hr_pos.ne', hA_pos.ne'] <;> ring
    have h3 : 1 < A := by
      have h4 : 0 < 6 / r := by positivity
      linarith
    have h5 : 1 / A < 1 := by
      apply (div_lt_one (by linarith)).mpr
      linarith
    exact h2.trans h5
  have hδ_le1 : δ ≤ 1 := by
    simpa [hδ_def] using hε_r_lt1.le
  rcases h_tubeNull (δ^2) (by positivity) with ⟨τ0, hτ0_pos, h_tubeNull⟩
  set τ : ℝ := min (δ * τ0) ε with hτ_def
  have hτ_pos : 0 < τ := by
    have h1 : 0 < δ * τ0 := by positivity
    exact lt_min h1 hε
  have hτ_le_ε : τ ≤ ε := min_le_right _ _
  have hτ_le_δτ0 : τ ≤ δ * τ0 := min_le_left _ _
  refine' ⟨τ, hτ_pos, hτ_le_ε, _⟩
  intro m f hm_pos hlip hmon hf0 h_lower
  rcases extend_continuous f hm_pos hlip with ⟨g, hg_cont, hg_agree⟩
  have hg0 : g 0 = 0 := by
    have h0_in : (0 : ℝ) ∈ Set.Icc 0 m := by exact ⟨by linarith, by linarith⟩
    have h : g 0 = f 0 := hg_agree 0 h0_in
    rw [h, hf0]
  have hg_lower : ∀ x ∈ Set.Icc 0 m, t * x - ε * m ≤ g x := by
    intro x hx
    have h1 : g x = f x := hg_agree x hx
    rw [h1]
    exact h_lower x hx
  rcases h_tubeNull f m hm_pos hlip hmon with ⟨L, hL_lin, hL_len, hL_bound, hL_sorted, hL_disj, hL_coverage⟩
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
    have hp1_in : p.1 ∈ Set.Icc p.1 p.2 := ⟨by linarith, by linarith [hpl]⟩
    have hp2_in : p.2 ∈ Set.Icc p.1 p.2 := ⟨by linarith [hpl], by linarith⟩
    intro x hx
    have h_eq1 : g x = f x := h_agree x hx
    have h_g1 : g p.1 = f p.1 := h_agree p.1 hp1_in
    have h_g2 : g p.2 = f p.2 := h_agree p.2 hp2_in
    have h_eq2 : chordValue g p.1 p.2 x = chordValue f p.1 p.2 x := by
      simp [chordValue, chordSlope, h_g1, h_g2] <;> ring
    have h_goal : |g x - chordValue g p.1 p.2 x| ≤ δ^2 * (p.2 - p.1) := by
      rw [h_eq1, h_eq2]
      exact h_f_lin x hx
    exact h_goal
  have hδ_lt_one : δ < 1 := by
    simpa [hδ_def] using hε_r_lt1
  have hg_lip : LipschitzOnWith 2 g (Set.Icc 0 m) := by
    intro x hx y hy
    have h_eq : edist (g x) (g y) = edist (f x) (f y) := by
      rw [hg_agree x hx, hg_agree y hy]
    rw [h_eq]
    exact Metric.mem_closedEBall.mp (hlip hx hy)
  have hg_mon : MonotoneOn g (Set.Icc 0 m) := by
    intro x hx y hy hxy
    have hgx : g x = f x := hg_agree x hx
    have hgy : g y = f y := hg_agree y hy
    rw [hgx, hgy]
    exact hmon hx hy hxy
  rcases h_processIntervals g s t m δ ε τ0 hs hst ht hδ_pos hδ_lt_one hm_pos hτ0_pos hε hg_cont hg_lip hg0 hg_lower
      L hL_sorted hL_disj hL_lin_g
      hL_len hL_bound hL_coverage
    with ⟨J, hJ_class, hJ_len, hJ_bound, hJ_sorted, hJ_disj, hJ_coverage⟩
  have hJ_nonempty : J ≠ [] := by
    by_contra h
    rw [h] at hJ_coverage
    simp at hJ_coverage
    have h6 : δ + δ^2 + ε / r < 1 := by
      have h7 : δ = ε / r := by simp [hδ_def]
      rw [h7]
      set x := ε / r with hx_def
      have hx_lt : x < 1 / A := by
        have h1 : A * ε < r := hAε_lt_r
        have h2 : 0 < A * r := by positivity
        have h3 : ε / r < 1 / A := by
          have h4 : A * ε < r := h1
          have h5 : (A * ε) / (A * r) < r / (A * r) := by gcongr
          have h6 : (A * ε) / (A * r) = ε / r := by
            field_simp [hA_pos.ne', hr_pos.ne'] <;> ring
          have h7 : r / (A * r) = 1 / A := by
            field_simp [hr_pos.ne', hA_pos.ne'] <;> ring
          rw [h6, h7] at h5
          exact h5
        simpa [hx_def] using h3
      have hr_le2 : r ≤ 2 := by linarith [ht]
      have hA_eq : A = 1 + 6 / r := hA_def
      have h_x_bound : x < r / (r + 6) := by
        have h9 : 1 / A = r / (r + 6) := by
          rw [hA_eq]
          field_simp [hr_pos.ne'] <;> ring
        rw [h9] at hx_lt
        exact hx_lt
      have h10 : 2 * x + x^2 < 1 := by
        have h11 : 0 < r + 6 := by linarith
        have h12 : 2 * x + x^2 < 2 * (r / (r + 6)) + (r / (r + 6))^2 := by
          gcongr <;> linarith
        have h13 : 2 * (r / (r + 6)) + (r / (r + 6))^2 ≤ 1 := by
          have h14 : r^2 ≤ 18 := by nlinarith
          field_simp [h11.ne'] <;> nlinarith
        linarith
      have h14 : ε / r + (ε / r)^2 + ε / r = 2 * (ε / r) + (ε / r)^2 := by ring
      rw [h14]
      exact h10
    have h9 : (δ + δ^2 + ε / r) * m < m := by
      exact mul_lt_of_lt_one_left hm_pos h6
    linarith
  set n : ℕ := J.length with hn_def
  have hn_pos : 0 < n := by
    rw [hn_def]
    simpa [List.length_pos_iff_ne_nil] using hJ_nonempty
  let I : Fin n → ℝ × ℝ := listToFin J
  have h_main1 : PairwiseInteriorDisjoint I :=
    pairwise_disjoint_list_to_fin J hJ_disj
  have h_main2 : ∀ (i : Fin n), 0 ≤ (I i).1 ∧ (I i).1 < (I i).2 ∧ (I i).2 ≤ m ∧ τ * m ≤ (I i).2 - (I i).1 := by
    intro i
    have h := hJ_bound (I i) (List.get_mem J i)
    have h_len : τ * m ≤ (I i).2 - (I i).1 := by
      have h4 : (I i).2 - (I i).1 ≥ δ * τ0 * m := hJ_len (I i) (List.get_mem J i)
      have h5 : τ * m ≤ δ * τ0 * m := by
        gcongr <;> linarith [hτ_le_δτ0]
      linarith
    exact ⟨h.1, h.2.2, h.2.1, h_len⟩
  have h_sum_len : Finset.sum Finset.univ (fun i : Fin n => (I i).2 - (I i).1) =
      (J.map (fun p => p.2 - p.1)).sum :=
    sum_fin_eq_sum_map J (fun p => p.2 - p.1)
  have h_gap_le : δ + δ^2 + ε / r ≤ 3 * (ε / r) := by
    have h1 : (ε / r)^2 ≤ ε / r := by
      have h2 : 0 ≤ ε / r := by positivity
      have h3 : ε / r < 1 := hε_r_lt1
      nlinarith
    have h4 : δ = ε / r := by simp [hδ_def]
    rw [h4]
    nlinarith
  have h_3εr_le_Aε : 3 * (ε / r) ≤ A * ε := by
    have hA : A = 1 + 6 / r := hA_def
    rw [hA]
    have hpos : 0 < ε := hε
    have hr : 0 < r := hr_pos
    have h : 3 * (ε / r) ≤ (1 + 6 / r) * ε := by
      have h5 : (1 + 6 / r) * ε = ε + 6 * (ε / r) := by field_simp [hr.ne'] <;> ring
      rw [h5]
      linarith
    exact h
  have h_main4 : (1 - A * ε) * m ≤
      Finset.sum Finset.univ (fun i : Fin n => (I i).2 - (I i).1) := by
    rw [h_sum_len]
    have h_gap : m - (J.map (fun p => p.2 - p.1)).sum ≤ (δ + δ^2 + ε / r) * m := hJ_coverage
    have h_bound : (δ + δ^2 + ε / r) * m ≤ A * ε * m := by
      gcongr
      <;> linarith [h_gap_le, h_3εr_le_Aε]
    linarith
  have h_gap_slope : m - (J.map (fun p => p.2 - p.1)).sum ≤ (A - 1) * ε / 2 * m := by
    have h1 : m - (J.map (fun p => p.2 - p.1)).sum ≤ (δ + δ^2 + ε / r) * m := hJ_coverage
    have h2 : (δ + δ^2 + ε / r) ≤ (A - 1) * ε / 2 := by
      have h3 : δ + δ^2 + ε / r ≤ 3 * (ε / r) := h_gap_le
      have h4 : 3 * (ε / r) = (A - 1) * ε / 2 := by
        have h5 : A = 1 + 6 / r := hA_def
        rw [h5]
        field_simp [hr_pos.ne'] <;> ring
      linarith [h3, h4]
    have h9 : (δ + δ^2 + ε / r) * m ≤ ((A - 1) * ε / 2) * m := by gcongr
    linarith
  have hJ_disj_forall : ∀ p ∈ J, ∀ q ∈ J, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1 :=
    disj_list_to_forall hJ_sorted hJ_disj (fun p hp => (hJ_bound p hp).2.2)
  have h_sum_slope : Finset.sum Finset.univ (fun i : Fin n =>
        ((I i).2 - (I i).1) * chordSlope f (I i).1 (I i).2) =
      (J.map (fun p => (p.2 - p.1) * chordSlope f p.1 p.2)).sum :=
    sum_fin_eq_sum_map J (fun p => (p.2 - p.1) * chordSlope f p.1 p.2)
  have h_main5 : (t - A * ε) * m ≤
      Finset.sum Finset.univ (fun i : Fin n =>
        ((I i).2 - (I i).1) * chordSlope f (I i).1 (I i).2) := by
    rw [h_sum_slope]
    have h_m_in : m ∈ Set.Icc 0 m := by exact ⟨by linarith, by linarith⟩
    have h_fm_lower : f m ≥ t * m - ε * m := h_lower m h_m_in
    have h_slope_sum := total_slope_list f m ((A - 1) * ε / 2) hm_pos hlip hf0 J
      hJ_sorted
      (fun p hp => let h := hJ_bound p hp; ⟨h.1, h.2.2, h.2.1⟩)
      hJ_disj_forall
      h_gap_slope
    linarith [h_fm_lower]
  have h_2δ_le_Aε : 2 * δ ≤ A * ε := by
    have hδ_eq : δ = ε / r := by simp [hδ_def]
    rw [hδ_eq]
    have hA : A = 1 + 6 / r := hA_def
    rw [hA]
    have hpos : 0 < ε := hε
    have hr : 0 < r := hr_pos
    have h : 2 * (ε / r) ≤ (1 + 6 / r) * ε := by
      have h5 : (1 + 6 / r) * ε = ε + 6 * (ε / r) := by field_simp [hr.ne'] <;> ring
      rw [h5]
      linarith
    exact h
  have h_g_agree_on_interval : ∀ (a b : ℝ), 0 ≤ a → b ≤ m → a < b →
      (∀ x ∈ Set.Icc a b, g x = f x) := by
    intro a b ha hb hab x hx
    have h_x_in : x ∈ Set.Icc 0 m := by
      exact ⟨by linarith [ha, hx.1], by linarith [hb, hx.2]⟩
    exact hg_agree x h_x_in
  have h_main6 : ∀ (i : Fin n),
      (EpsilonLinear f (A * ε) (I i).1 (I i).2 ∧
          s ≤ chordSlope f (I i).1 (I i).2 ∧
          chordSlope f (I i).1 (I i).2 ≤ 2) ∨
      (EpsilonSuperlinear f (A * ε) (I i).1 (I i).2 ∧
          chordSlope f (I i).1 (I i).2 = s) := by
    intro i
    let a := (I i).1
    let b := (I i).2
    have ha : 0 ≤ a := (hJ_bound (I i) (List.get_mem J i)).1
    have hb : b ≤ m := (hJ_bound (I i) (List.get_mem J i)).2.1
    have hab : a < b := (hJ_bound (I i) (List.get_mem J i)).2.2
    have h_agree : ∀ x ∈ Set.Icc a b, g x = f x := h_g_agree_on_interval a b ha hb hab
    have ha_in : a ∈ Set.Icc a b := ⟨by linarith, by linarith [hab]⟩
    have hb_in : b ∈ Set.Icc a b := ⟨by linarith [hab], by linarith⟩
    have h_slope_eq : chordSlope g a b = chordSlope f a b := by
      have h1 : g a = f a := h_agree a ha_in
      have h2 : g b = f b := h_agree b hb_in
      simp [chordSlope, h1, h2]
      <;> ring
    have h4 := hJ_class (I i) (List.get_mem J i)
    cases h4 with
    | inl h4 =>
      have h_lin_g : EpsilonLinear g (2 * δ) a b := h4.1
      have h_slope_ge_s_g : s ≤ chordSlope g a b := h4.2
      have h_lin_f : EpsilonLinear f (2 * δ) a b := by
        intro x hx
        have h_eq1 : g x = f x := h_agree x hx
        have h_ga : g a = f a := h_agree a ha_in
        have h_gb : g b = f b := h_agree b hb_in
        have h_eq2 : chordValue g a b x = chordValue f a b x := by
          simp [chordValue, chordSlope, h_ga, h_gb] <;> ring
        have h_from_g : |g x - chordValue g a b x| ≤ (2 * δ) * (b - a) := h_lin_g x hx
        rw [h_eq1, h_eq2] at h_from_g
        exact h_from_g
      have h_slope_ge_s : s ≤ chordSlope f a b := by
        rw [←h_slope_eq]
        exact h_slope_ge_s_g
      have hlip_sub : LipschitzOnWith 2 f (Set.Icc a b) :=
        hlip.mono (fun x hx => ⟨by linarith [ha, hx.1], by linarith [hb, hx.2]⟩)
      have h_slope_le_2 : chordSlope f a b ≤ 2 := chordSlope_le_two hab hlip_sub
      have h_lin_Aε : EpsilonLinear f (A * ε) a b := by
        intro x hx
        have h6 : |f x - chordValue f a b x| ≤ (2 * δ) * (b - a) := h_lin_f x hx
        have h7 : (2 * δ) * (b - a) ≤ (A * ε) * (b - a) := by
          gcongr <;> linarith [h_2δ_le_Aε]
        exact h6.trans h7
      exact Or.inl ⟨h_lin_Aε, h_slope_ge_s, h_slope_le_2⟩
    | inr h4 =>
      have h_super_g : EpsilonSuperlinear g (2 * δ) a b := h4.1
      have h_slope_eq_s_g : chordSlope g a b = s := h4.2
      have h_super_f : EpsilonSuperlinear f (2 * δ) a b := by
        intro x hx
        have h_eq1 : g x = f x := h_agree x hx
        have h_ga : g a = f a := h_agree a ha_in
        have h_gb : g b = f b := h_agree b hb_in
        have h_eq2 : chordValue g a b x = chordValue f a b x := by
          simp [chordValue, chordSlope, h_ga, h_gb] <;> ring
        have h_from_g : chordValue g a b x - (2 * δ) * (b - a) ≤ g x := h_super_g x hx
        rw [h_eq1, h_eq2] at h_from_g
        exact h_from_g
      have h_slope_eq_s : chordSlope f a b = s := by
        rw [←h_slope_eq]
        exact h_slope_eq_s_g
      have h_super_Aε : EpsilonSuperlinear f (A * ε) a b := by
        intro x hx
        have h6 : chordValue f a b x - (2 * δ) * (b - a) ≤ f x := h_super_f x hx
        have h7 : (A * ε) * (b - a) ≥ (2 * δ) * (b - a) := by
          gcongr <;> linarith [h_2δ_le_Aε]
        linarith
      exact Or.inr ⟨h_super_Aε, h_slope_eq_s⟩
  exact ⟨n, I, hn_pos, h_main1, h_main2, h_main4, h_main5, h_main6⟩

end CombinatorialKaufman.MainAssembly
