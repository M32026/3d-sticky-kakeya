module

/-
# Maximal Density Interval

Finds an interval `[x₀, x₀+r₀]` maximizing the density ratio
`μ(I) / r^(κ/2)` among all intervals with `δ ≤ r ≤ 1` contained in `[0,1]`.

Provides:
- `measure_interval_usc`: upper semicontinuity of interval measure
- `maximal_density_interval_C`: generalized version with arbitrary Frostman constant C
- `maximal_density_interval`: corollary setting `C = δ^(-ε)`

## Dependencies
- `MyLeanRepo.ProjectionBasic` — `IsDirectionFrostman`, `Nreal`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Classical

namespace WeakTwoEndsSumProduct

noncomputable section

/-- Helper: for finite μ, `(x, r) ↦ μ(Icc x (x+r))` is upper semicontinuous. -/
lemma measure_interval_usc {μ : Measure ℝ} (hμ_fin : μ Set.univ < ⊤) :
    UpperSemicontinuous (fun p : ℝ × ℝ => μ (Set.Icc p.1 (p.1 + p.2))) := by
  intro p y hxy
  by_cases hy_top : y = ⊤
  · rw [hy_top]
    filter_upwards with q
    have h : μ (Set.Icc q.1 (q.1 + q.2)) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    exact lt_of_le_of_lt h hμ_fin
  · set a : ℝ := p.1 with ha
    set b : ℝ := p.1 + p.2 with hb
    let S : ℕ → Set ℝ := fun n => Set.Icc (a - 1 / (n + 1 : ℝ)) (b + 1 / (n + 1 : ℝ))
    have hS_decr : ∀ n m : ℕ, n ≤ m → S m ⊆ S n := by
      intro n m hnm z hz
      have h1 : (1 : ℝ) / (m + 1) ≤ 1 / (n + 1) := by gcongr <;> norm_cast
      simp only [S, Set.mem_Icc] at hz ⊢
      exact ⟨by linarith, by linarith⟩
    have h_dir : Directed (· ⊇ ·) S := by
      intro n m
      refine ⟨max n m, hS_decr n (max n m) (le_max_left n m), hS_decr m (max n m) (le_max_right n m)⟩
    have h_inter : (⋂ n, S n) = Set.Icc a b := by
      ext z
      simp only [Set.mem_iInter, S, Set.mem_Icc]
      constructor
      · intro h
        have h1 : a ≤ z := by
          by_contra h2
          have h3 : z < a := by linarith
          have h4 : 0 < a - z := by linarith
          obtain ⟨k, hk⟩ := exists_nat_gt (1 / (a - z))
          have h5 : (1 : ℝ) / (k + 1) < a - z := by
            have h6 : (k : ℝ) + 1 > 1 / (a - z) := by linarith [hk]
            have h7 : 0 < a - z := h4
            have h8 : 1 / ((k : ℝ) + 1) < 1 / (1 / (a - z)) := one_div_lt_one_div_of_lt (by positivity) h6
            have h9 : 1 / (1 / (a - z)) = a - z := by field_simp [h7.ne'] <;> ring
            rw [h9] at h8; exact h8
          have h7 := (h k).1
          linarith
        have h2 : z ≤ b := by
          by_contra h3
          have h4 : b < z := by linarith
          have h5 : 0 < z - b := by linarith
          obtain ⟨k, hk⟩ := exists_nat_gt (1 / (z - b))
          have h6 : (1 : ℝ) / (k + 1) < z - b := by
            have h7 : (k : ℝ) + 1 > 1 / (z - b) := by linarith [hk]
            have h8 : 0 < z - b := h5
            have h9 : 1 / ((k : ℝ) + 1) < 1 / (1 / (z - b)) := one_div_lt_one_div_of_lt (by positivity) h7
            have h10 : 1 / (1 / (z - b)) = z - b := by field_simp [h8.ne'] <;> ring
            rw [h10] at h9; exact h9
          have h8 := (h k).2
          linarith
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩ n
        have h3 : 0 ≤ (1 : ℝ) / (n + 1) := by positivity
        exact ⟨by linarith, by linarith⟩
    have h_fin : ∃ n, μ (S n) ≠ ⊤ :=
      ⟨0, ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ _)) hμ_fin)⟩
    have h_nullmeas : ∀ n, NullMeasurableSet (S n) μ :=
      fun _ => measurableSet_Icc.nullMeasurableSet
    have h_eq : μ (⋂ n, S n) = ⨅ n, μ (S n) :=
      Directed.measure_iInter h_nullmeas h_dir h_fin
    have h_inf_lt_y : (⨅ n, μ (S n)) < y := by
      rw [← h_eq, h_inter] <;> exact hxy
    have h_exists : ∃ n, μ (S n) < y := by
      by_contra h
      have h' : ∀ n, ¬ μ (S n) < y := by simpa using h
      have h'' : ∀ n, y ≤ μ (S n) := by
        intro n
        have h4 : ¬ μ (S n) < y := h' n
        have h5 : y ≤ μ (S n) := by exact Std.not_lt.mp (h' n)
        exact h5
      have h3 : y ≤ ⨅ n, μ (S n) := le_iInf_iff.mpr h''
      exact not_le.mpr h_inf_lt_y h3
    rcases h_exists with ⟨n, hn⟩
    set ε : ℝ := 1 / (n + 1) with hε_def
    have hε_pos : 0 < ε := by positivity
    let U : Set (ℝ × ℝ) := {q | a - ε < q.1 ∧ q.1 + q.2 < b + ε}
    have hU_open : IsOpen U := by
      have h1 : IsOpen {q : ℝ × ℝ | a - ε < q.1} := isOpen_lt continuous_const continuous_fst
      have h2 : IsOpen {q : ℝ × ℝ | q.1 + q.2 < b + ε} := isOpen_lt (continuous_fst.add continuous_snd) continuous_const
      exact h1.inter h2
    have hU_nhd : U ∈ nhds p := by
      have h1 : a - ε < a := by linarith
      have h2 : (p.1 + p.2) < b + ε := by simp [ha, hb] <;> linarith
      exact hU_open.mem_nhds ⟨h1, h2⟩
    filter_upwards [hU_nhd] with q hq
    have h_sub : Set.Icc q.1 (q.1 + q.2) ⊆ S n := by
      intro z hz
      have h3 : a - ε < q.1 := hq.1
      have h4 : q.1 + q.2 < b + ε := hq.2
      simp only [S, Set.mem_Icc] at hz ⊢
      exact ⟨by linarith, by linarith⟩
    calc μ (Set.Icc q.1 (q.1 + q.2)) ≤ μ (S n) := measure_mono h_sub
         _ < y := hn

/-- Generalized maximal density interval for arbitrary Frostman constant C.

Among all intervals `[a, a+r]` with `δ ≤ r ≤ 1` contained in `[0,1]`, find one
`I₀ = [x₀, x₀+r₀]` maximizing the density ratio `μ(I) / r^(κ/2)`.

The maximizer satisfies:
- `δ ≤ r₀ ≤ 1`
- `μ(I₀) > 0`
- `r₀ ≥ C^(-2/κ)` (lower bound from Frostman vs. density)
- Every subinterval `J ⊆ I₀` of length `r ≥ δ` has
  `μ(J) ≤ μ(I₀) · (r/r₀)^(κ/2)` (self-similarity / near-Frostman at exponent κ/2)
-/
lemma maximal_density_interval_C
    {δ : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    {κ C : ℝ} (hκ_pos : 0 < κ) (hC_pos : 0 < C)
    {μ : Measure ℝ} (hμ : IsDirectionFrostman δ κ C μ) :
    ∃ (x₀ r₀ : ℝ),
      δ ≤ r₀ ∧ r₀ ≤ 1 ∧
      0 < μ (Set.Icc x₀ (x₀ + r₀)) ∧
      C ^ (-2 / κ) ≤ r₀ ∧
      ENNReal.ofReal (r₀ ^ (κ / 2)) ≤ μ (Set.Icc x₀ (x₀ + r₀)) ∧
      ∀ (a b : ℝ), Set.Icc a b ⊆ Set.Icc x₀ (x₀ + r₀) → δ ≤ b - a →
        μ (Set.Icc a b) ≤
          μ (Set.Icc x₀ (x₀ + r₀)) *
            ENNReal.ofReal (((b - a) / r₀) ^ (κ / 2)) := by
  have hμ_univ : μ Set.univ = 1 := hμ.1
  have hμ_support : μ.support ⊆ Set.Icc 0 1 := hμ.2.1
  have hμ_frost := hμ.2.2
  have hμ_fin : μ Set.univ < ⊤ := by rw [hμ_univ] <;> simp
  have hμ_Icc01 : μ (Set.Icc (0 : ℝ) 1) = 1 := by
    have h1 : (Set.Icc (0 : ℝ) 1)ᶜ ⊆ μ.supportᶜ := by
      intro x hx
      exact fun h => hx (hμ_support h)
    have h2 : μ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 :=
      measure_mono_null h1 Measure.measure_compl_support
    have h3 : μ (Set.Icc (0 : ℝ) 1) + μ ((Set.Icc (0 : ℝ) 1)ᶜ) = μ Set.univ := by
      rw [← measure_union (disjoint_compl_right) measurableSet_Icc.compl] <;> simp
    have h4 : μ (Set.Icc (0 : ℝ) 1) = μ Set.univ := by
      rw [h2] at h3
      simpa using h3
    rw [h4, hμ_univ]
  let g : ℝ × ℝ → ENNReal := fun p => μ (Set.Icc p.1 (p.1 + p.2))
  have hg_usc : UpperSemicontinuous g := measure_interval_usc hμ_fin
  let d : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (p.2 ^ (κ / 2))
  have h1_cont : Continuous (fun p : ℝ × ℝ => p.2) := continuous_snd
  have h2_cont : Continuous (fun x : ℝ => x ^ (κ / 2)) :=
    Real.continuous_rpow_const (by linarith)
  have h3_cont : Continuous ENNReal.ofReal := ENNReal.continuous_ofReal
  have hd_cont : Continuous d :=
    h3_cont.comp (h2_cont.comp h1_cont)
  let S : Set (ℝ × ℝ) := {p | δ ≤ p.2 ∧ p.2 ≤ 1 ∧ 0 ≤ p.1 ∧ p.1 + p.2 ≤ 1}
  have hS_closed : IsClosed S := by
    apply IsClosed.inter (isClosed_le continuous_const continuous_snd)
    apply IsClosed.inter (isClosed_le continuous_snd continuous_const)
    apply IsClosed.inter (isClosed_le continuous_const continuous_fst)
    exact isClosed_le (continuous_fst.add continuous_snd) continuous_const
  have hS_subset : S ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro p hp
    have h2 : 0 ≤ p.1 := hp.2.2.1
    have h3 : p.1 ≤ 1 := by linarith [hp.2.2.2, hp.1]
    have h4 : 0 ≤ p.2 := by linarith [hp.1]
    have h5 : p.2 ≤ 1 := hp.2.1
    exact ⟨⟨h2, h3⟩, ⟨h4, h5⟩⟩
  have hK_compact : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hS_compact : IsCompact S := IsCompact.of_isClosed_subset hK_compact hS_closed hS_subset
  have hS_nonempty : S.Nonempty := by
    refine ⟨(0, 1), ?_⟩
    simp only [S, Set.mem_setOf_eq]
    exact ⟨hδ_le_one, by norm_num, by norm_num, by norm_num⟩
  let f : ℝ × ℝ → ENNReal := fun p => g p / d p
  have hd_pos_on : ∀ p ∈ S, 0 < d p := by
    intro p hp
    have h1 : 0 < p.2 := by linarith [hp.1]
    have h2 : 0 < p.2 ^ (κ / 2) := Real.rpow_pos_of_pos h1 _
    exact ENNReal.ofReal_pos.mpr h2
  have hd_ne_top : ∀ p, d p ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hg_ne_top : ∀ p, g p ≠ ⊤ := by
    intro p
    have h : g p ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    rw [hμ_univ] at h
    exact ne_top_of_le_ne_top (by simp) h
  have hf_usc_on : UpperSemicontinuousOn f S := by
    intro p hp y hpy
    by_cases hy_top : y = ⊤
    · rw [hy_top]
      have h_main : ∀ q ∈ S, f q < ⊤ := by
        intro q hq
        have hg_top : g q ≠ ⊤ := hg_ne_top q
        have hd_pos : 0 < d q := hd_pos_on q hq
        exact div_lt_top hg_top hd_pos.ne'
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact h_main q hq
    · have h_y_ne_top : y ≠ ⊤ := hy_top
      have hdp_pos : 0 < d p := hd_pos_on p hp
      have hdp_ne_top : d p ≠ ⊤ := hd_ne_top p
      have h1 : g p < y * d p := by
        have h_eq : f p = g p / d p := rfl
        rw [h_eq] at hpy
        rw [ENNReal.div_lt_iff (Or.inl hdp_pos.ne') (Or.inl hdp_ne_top)] at hpy
        exact hpy
      have hgp_ne_top : g p ≠ ⊤ := hg_ne_top p
      have h_ydp_ne_top : y * d p ≠ ⊤ := mul_ne_top h_y_ne_top hdp_ne_top
      have h2 : (g p).toReal < (y * d p).toReal :=
        ENNReal.toReal_lt_toReal hgp_ne_top h_ydp_ne_top |>.mpr h1
      obtain ⟨r, hr1, hr2⟩ : ∃ r : ℝ, (g p).toReal < r ∧ r < (y * d p).toReal :=
        exists_between h2
      have hr_nonneg : 0 ≤ r := by
        have h_nonneg : 0 ≤ (g p).toReal := ENNReal.toReal_nonneg
        linarith
      let z : ENNReal := ENNReal.ofReal r
      have hz_toReal : z.toReal = r := by
        simp [z, hr_nonneg]
      have hz1 : g p < z := by
        have h : (g p).toReal < z.toReal := by
          rw [hz_toReal] <;> exact hr1
        exact (ENNReal.toReal_lt_toReal hgp_ne_top ENNReal.ofReal_ne_top).mp h
      have hz2 : z < y * d p := by
        have h : z.toReal < (y * d p).toReal := by
          rw [hz_toReal] <;> exact hr2
        exact (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top h_ydp_ne_top).mp h
      have h3 : ∀ᶠ q in nhds p, g q < z := hg_usc p z hz1
      have h_cont : Continuous (fun q => y * d q) :=
        (ENNReal.continuous_const_mul h_y_ne_top).comp hd_cont
      have h4 : ∀ᶠ q in nhds p, z < y * d q :=
        h_cont.continuousAt (Ioi_mem_nhds hz2)
      have h3' : ∀ᶠ q in nhdsWithin p S, g q < z :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds h3
      have h4' : ∀ᶠ q in nhdsWithin p S, z < y * d q :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds h4
      filter_upwards [h3', h4', self_mem_nhdsWithin] with q hq3 hq4 hqS
      have hdq_pos : 0 < d q := hd_pos_on q hqS
      have hdq_ne_top : d q ≠ ⊤ := hd_ne_top q
      have h5 : g q < y * d q := lt_trans hq3 hq4
      have h6 : g q / d q < y := by
        rw [ENNReal.div_lt_iff (Or.inl hdq_pos.ne') (Or.inl hdq_ne_top)]
        exact h5
      exact h6
  have h_max_exists : ∃ p₀ ∈ S, ∀ p ∈ S, f p ≤ f p₀ := by
    have h : ∃ p₀ ∈ S, IsMaxOn f S p₀ := hf_usc_on.exists_isMaxOn hS_nonempty hS_compact
    rcases h with ⟨p₀, hp₀S, hmax⟩
    refine ⟨p₀, hp₀S, fun p hp => ?_⟩
    exact hmax hp
  rcases h_max_exists with ⟨p₀, hp₀S, h_maximizer⟩
  let x₀ : ℝ := p₀.1
  let r₀ : ℝ := p₀.2
  have hr₀_geδ : δ ≤ r₀ := hp₀S.1
  have hr₀_le1 : r₀ ≤ 1 := hp₀S.2.1
  have hx₀_nonneg : 0 ≤ x₀ := hp₀S.2.2.1
  have hx₀_plus : x₀ + r₀ ≤ 1 := hp₀S.2.2.2
  have hr₀_pos : 0 < r₀ := by linarith
  let I₀ := Set.Icc x₀ (x₀ + r₀)
  have h_p01_in_S : (0, 1) ∈ S := by
    simp only [S, Set.mem_setOf_eq]
    exact ⟨hδ_le_one, by norm_num, by norm_num, by norm_num⟩
  have h_f01 : f (0, 1) = 1 := by
    have hg : g (0, 1) = 1 := by
      simp [g, hμ_Icc01] <;> norm_num
    have hd : d (0, 1) = 1 := by
      simp [d] <;> norm_num
    have h : g (0, 1) / d (0, 1) = 1 := by
      rw [hg, hd] <;> simp
    exact h
  have h_f_max_ge1 : f p₀ ≥ 1 := by
    have h : f (0, 1) ≤ f p₀ := h_maximizer (0, 1) h_p01_in_S
    rw [h_f01] at h
    exact h
  have hμI₀_pos : 0 < μ I₀ := by
    have h1 : 0 < d p₀ := hd_pos_on p₀ hp₀S
    have h2 : 0 < f p₀ := by
      have h3 : 1 ≤ f p₀ := h_f_max_ge1
      exact zero_lt_one.trans_le h3
    have h3 : 0 < g p₀ / d p₀ := h2
    have h4 : 0 < g p₀ := by
      by_contra h5
      have h6 : g p₀ = 0 := by simpa using h5
      rw [h6] at h3
      simp at h3
    simpa [g, I₀] using h4
  have hμI₀_ne_top : μ I₀ ≠ ⊤ := hg_ne_top p₀
  have h_ge_density : ENNReal.ofReal (r₀ ^ (κ / 2)) ≤ μ I₀ := by
    have h1 : f p₀ ≥ 1 := h_f_max_ge1
    have h2 : g p₀ / d p₀ ≥ 1 := h1
    have hdp_pos : 0 < d p₀ := hd_pos_on p₀ hp₀S
    have hdp_ne_top : d p₀ ≠ ⊤ := hd_ne_top p₀
    have h3 : (g p₀ / d p₀) * d p₀ ≥ 1 * d p₀ := by gcongr
    have h4 : (g p₀ / d p₀) * d p₀ = g p₀ := ENNReal.div_mul_cancel hdp_pos.ne' hdp_ne_top
    have h5 : g p₀ ≥ d p₀ := by
      rw [h4] at h3
      simpa using h3
    simpa [d, g, I₀] using h5
  -- Frostman upper bound: μ(I₀) ≤ C * r₀^κ
  -- I₀ = [x₀, x₀+r₀] ⊆ [x₀-r₀, x₀+r₀], and Frostman gives bound on centered interval
  have h_frostman_upper : μ I₀ ≤ ENNReal.ofReal (C * r₀ ^ κ) := by
    have h1 : I₀ ⊆ Set.Icc (x₀ - r₀) (x₀ + r₀) := by
      intro y hy
      simp only [I₀, Set.mem_Icc] at hy ⊢
      constructor <;> linarith
    have h2 : μ I₀ ≤ μ (Set.Icc (x₀ - r₀) (x₀ + r₀)) := measure_mono h1
    have h3 : μ (Set.Icc (x₀ - r₀) (x₀ + r₀)) ≤ ENNReal.ofReal (C * r₀ ^ κ) :=
      hμ_frost x₀ r₀ hr₀_geδ hr₀_le1
    exact h2.trans h3
  have h4 : ENNReal.ofReal (r₀ ^ (κ / 2)) ≤ ENNReal.ofReal (C * r₀ ^ κ) :=
    h_ge_density.trans h_frostman_upper
  have h5 : r₀ ^ (κ / 2) ≤ C * r₀ ^ κ := by
    have h6 : 0 ≤ r₀ ^ (κ / 2) := by positivity
    have h7 : 0 ≤ C * r₀ ^ κ := by positivity
    have h_iff : ENNReal.ofReal (r₀ ^ (κ / 2)) ≤ ENNReal.ofReal (C * r₀ ^ κ) ↔
        r₀ ^ (κ / 2) ≤ C * r₀ ^ κ := by
      rw [ENNReal.ofReal_le_ofReal_iff h7]
      <;> positivity
    exact h_iff.mp h4
  have h_rpos : 0 < r₀ := hr₀_pos
  have h8 : 0 < r₀ ^ (κ / 2) := Real.rpow_pos_of_pos h_rpos _
  have h9 : 1 ≤ C * r₀ ^ (κ / 2) := by
    have h10 : r₀ ^ κ / r₀ ^ (κ / 2) = r₀ ^ (κ / 2) := by
      have h101 : r₀ ^ κ = r₀ ^ (κ / 2) * r₀ ^ (κ / 2) := by
        have h : r₀ ^ (κ / 2 + κ / 2) = r₀ ^ (κ / 2) * r₀ ^ (κ / 2) :=
          Real.rpow_add h_rpos (κ / 2) (κ / 2)
        have hsum : κ / 2 + κ / 2 = κ := by ring
        rw [hsum] at h
        exact h
      rw [h101]
      field_simp [h8.ne'] <;> ring
    calc (1 : ℝ)
      = (r₀ ^ (κ / 2)) / (r₀ ^ (κ / 2)) := by field_simp [h8.ne']
    _ ≤ (C * r₀ ^ κ) / (r₀ ^ (κ / 2)) := by gcongr
    _ = C * (r₀ ^ κ / r₀ ^ (κ / 2)) := by ring
    _ = C * r₀ ^ (κ / 2) := by rw [h10]
  -- From 1 ≤ C * r₀^(κ/2), derive C^(-2/κ) ≤ r₀
  have h10 : C ^ (-1 : ℝ) ≤ r₀ ^ (κ / 2) := by
    have hC_pos' : 0 < C := hC_pos
    have h11 : C ^ (-1 : ℝ) = 1 / C := by
      simp [Real.rpow_neg_one]
    rw [h11]
    have h12 : 1 ≤ C * r₀ ^ (κ / 2) := h9
    have h13 : 0 < C := hC_pos'
    have h14 : 0 < r₀ ^ (κ / 2) := h8
    calc 1 / C
      ≤ (C * r₀ ^ (κ / 2)) / C := by gcongr
    _ = r₀ ^ (κ / 2) := by
      field_simp [h13.ne'] <;> ring
  have h15 : (C ^ (-1 : ℝ)) ^ (2 / κ) ≤ (r₀ ^ (κ / 2)) ^ (2 / κ) := by gcongr
  have h16 : (C ^ (-1 : ℝ)) ^ (2 / κ) = C ^ (-2 / κ) := by
    rw [← Real.rpow_mul hC_pos.le] <;> ring_nf
  have h17 : (r₀ ^ (κ / 2)) ^ (2 / κ) = r₀ := by
    rw [← Real.rpow_mul h_rpos.le]
    have h18 : (κ / 2) * (2 / κ) = 1 := by
      field_simp [hκ_pos.ne'] <;> ring
    rw [h18] <;> exact Real.rpow_one _
  rw [h16, h17] at h15
  have h_lower_bound : C ^ (-2 / κ) ≤ r₀ := h15
  -- Self-similarity property
  have h_self_sim : ∀ (a b : ℝ), Set.Icc a b ⊆ I₀ → δ ≤ b - a →
      μ (Set.Icc a b) ≤ μ I₀ * ENNReal.ofReal (((b - a) / r₀) ^ (κ / 2)) := by
    intro a b h_sub h_len
    let q : ℝ × ℝ := (a, b - a)
    have hqS : q ∈ S := by
      simp only [S, Set.mem_setOf_eq]
      have h1 : δ ≤ b - a := h_len
      have h2 : b - a ≤ 1 := by
        have ha_in : a ∈ Set.Icc a b := by simp [h_len] <;> linarith
        have hb_in : b ∈ Set.Icc a b := by simp [h_len] <;> linarith
        have ha : x₀ ≤ a := (h_sub ha_in).1
        have hb : b ≤ x₀ + r₀ := (h_sub hb_in).2
        linarith
      have h3 : 0 ≤ a := by
        have ha_in : a ∈ Set.Icc a b := by simp <;> linarith
        have h_x0_le_a : x₀ ≤ a := (h_sub ha_in).1
        linarith [hx₀_nonneg]
      have h4 : a + (b - a) ≤ 1 := by
        have hb_in : b ∈ Set.Icc a b := by simp [h_len] <;> linarith
        have hb : b ≤ x₀ + r₀ := (h_sub hb_in).2
        linarith
      exact ⟨h1, h2, h3, h4⟩
    have h_ineq : f q ≤ f p₀ := h_maximizer q hqS
    have hdq_pos : 0 < d q := hd_pos_on q hqS
    have hdq_ne_top : d q ≠ ⊤ := hd_ne_top q
    have h10 : g q / d q ≤ g p₀ / d p₀ := h_ineq
    have h11 : g q ≤ g p₀ * (d q / d p₀) := by
      have h_eq1 : (g q / d q) * d q = g q := ENNReal.div_mul_cancel hdq_pos.ne' hdq_ne_top
      have h_eq2 : (g p₀ / d p₀) * d q = g p₀ * (d q / d p₀) := by
        have h1 : (g p₀ / d p₀) * d q = g p₀ * ((d p₀)⁻¹ * d q) := by
          simp [div_eq_mul_inv, mul_assoc]
        rw [h1]
        have h2 : (d p₀)⁻¹ * d q = d q * (d p₀)⁻¹ := mul_comm _ _
        rw [h2]
        have h3 : g p₀ * (d q * (d p₀)⁻¹) = g p₀ * (d q / d p₀) := by
          congr 1 <;> simp [div_eq_mul_inv]
        exact h3
      calc g q
        = (g q / d q) * d q := h_eq1.symm
      _ ≤ (g p₀ / d p₀) * d q := by gcongr
      _ = g p₀ * (d q / d p₀) := h_eq2
    have h13 : 0 < r₀ := hr₀_pos
    have h14 : 0 ≤ b - a := by linarith
    have h15 : 0 < r₀ ^ (κ / 2) := Real.rpow_pos_of_pos h13 _
    have h16 : (ENNReal.ofReal (r₀ ^ (κ / 2)))⁻¹ = ENNReal.ofReal ((r₀ ^ (κ / 2))⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos h15]
    have h12 : d q / d p₀ = ENNReal.ofReal (((b - a) / r₀) ^ (κ / 2)) := by
      simp only [d]
      have h17 : ENNReal.ofReal ((b - a) ^ (κ / 2)) / ENNReal.ofReal (r₀ ^ (κ / 2)) =
          ENNReal.ofReal ((b - a) ^ (κ / 2)) * (ENNReal.ofReal (r₀ ^ (κ / 2)))⁻¹ := by
        rw [div_eq_mul_inv]
      rw [h17, h16]
      have h18 : ENNReal.ofReal ((b - a) ^ (κ / 2)) * ENNReal.ofReal ((r₀ ^ (κ / 2))⁻¹) =
          ENNReal.ofReal (((b - a) ^ (κ / 2)) * (r₀ ^ (κ / 2))⁻¹) := by
        rw [ENNReal.ofReal_mul] <;> positivity
      rw [h18]
      have h191 : ((b - a) ^ (κ / 2)) * (r₀ ^ (κ / 2))⁻¹ =
          ((b - a) ^ (κ / 2)) / (r₀ ^ (κ / 2)) := by
        exact (div_eq_mul_inv ((b - a) ^ (κ / 2)) (r₀ ^ (κ / 2))).symm
      have h19 : ((b - a) ^ (κ / 2)) / (r₀ ^ (κ / 2)) = ((b - a) / r₀) ^ (κ / 2) := by
        rw [← Real.div_rpow h14 h13.le]
      rw [h191, h19]
    rw [h12] at h11
    have h_final : g q ≤ g p₀ * ENNReal.ofReal (((b - a) / r₀) ^ (κ / 2)) := h11
    have h_goal : μ (Set.Icc a b) ≤ μ I₀ * ENNReal.ofReal (((b - a) / r₀) ^ (κ / 2)) := by
      have hq1 : q.1 = a := by simp [q]
      have hq2 : q.1 + q.2 = b := by simp [q] <;> linarith
      have h_eq : g q = μ (Set.Icc a b) := by
        have h_set : Set.Icc q.1 (q.1 + q.2) = Set.Icc a b := by
          have h1 : q.1 = a := by simp [q]
          have h2 : q.1 + q.2 = b := by simp [q] <;> linarith
          rw [h1, h2]
        have h_gq : g q = μ (Set.Icc q.1 (q.1 + q.2)) := by rfl
        rw [h_gq, h_set]
      have h_eq2 : g p₀ = μ I₀ := by
        simp [g, I₀] <;> rfl
      rw [h_eq, h_eq2] at h_final
      exact h_final
    exact h_goal
  exact ⟨x₀, r₀, hr₀_geδ, hr₀_le1, hμI₀_pos, h_lower_bound, h_ge_density, h_self_sim⟩

/-- Original maximal density interval as a corollary of the generalized version.
    Sets `C = δ^(-ε)`, giving `r₀ ≥ δ^(2ε/κ)`. -/
lemma maximal_density_interval
    {δ : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    {κ ε : ℝ} (hκ_pos : 0 < κ) (hε_pos : 0 < ε)
    {μ : Measure ℝ} (hμ : IsDirectionFrostman δ κ (δ ^ (-ε)) μ) :
    ∃ (x₀ r₀ : ℝ),
      δ ≤ r₀ ∧ r₀ ≤ 1 ∧
      0 < μ (Set.Icc x₀ (x₀ + r₀)) ∧
      δ ^ (2 * ε / κ) ≤ r₀ ∧
      ENNReal.ofReal (r₀ ^ (κ / 2)) ≤ μ (Set.Icc x₀ (x₀ + r₀)) ∧
      ∀ (a b : ℝ), Set.Icc a b ⊆ Set.Icc x₀ (x₀ + r₀) → δ ≤ b - a →
        μ (Set.Icc a b) ≤
          μ (Set.Icc x₀ (x₀ + r₀)) *
            ENNReal.ofReal (((b - a) / r₀) ^ (κ / 2)) := by
  have hC_pos : 0 < (δ ^ (-ε)) := by positivity
  have h_main := maximal_density_interval_C hδ hδ_le_one hκ_pos hC_pos hμ
  rcases h_main with ⟨x₀, r₀, hr₀_geδ, hr₀_le1, hμ_pos, h_lower, h_density, h_self_sim⟩
  have h_convert : (δ ^ (-ε)) ^ (-2 / κ) = δ ^ (2 * ε / κ) := by
    rw [← Real.rpow_mul (by linarith : 0 ≤ δ)] <;> ring_nf
  have h_lower' : δ ^ (2 * ε / κ) ≤ r₀ := by
    rw [← h_convert]
    exact h_lower
  exact ⟨x₀, r₀, hr₀_geδ, hr₀_le1, hμ_pos, h_lower', h_density, h_self_sim⟩

end

end WeakTwoEndsSumProduct
