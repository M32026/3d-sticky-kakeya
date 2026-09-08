/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Analysis.ProjectiveNormal
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Projective-cap packing bound on unit vectors

A set of unit vectors lying inside an `R`-projective-cap around a fixed
unit vector `e` and pairwise `r`-projective-separated has cardinality
bounded by a dim-only constant times a polynomial in `R / r`.

The "projective" qualifier means we identify antipodes via the symmetric
distance `projNormalDist x y = min ‖x - y‖ ‖x + y‖`
(`Kakeya.Mathlib.Analysis.ProjectiveNormal`).

Proof sketch. Two unit vectors `x, y` with `r ≤ min ‖x - y‖ ‖x + y‖`
satisfy `r ≤ ‖x - y‖`, so `V` is ordinary `r`-separated. The cap
condition `min ‖v - e‖ ‖v + e‖ ≤ R` means `V ⊆ closedBall e R ∪
closedBall (-e) R`. Volume packing balls of radius `r/2` around each
`v ∈ V` (which are pairwise disjoint by `r`-separation and lie inside
`closedBall e (R + r/2) ∪ closedBall (-e) (R + r/2)`) gives a
polynomial bound.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped InnerProductSpace RealInnerProductSpace ENNReal NNReal

namespace Kakeya

/-- The dimensional constant in `card_le_of_projective_separated_in_cap`. -/
noncomputable def projectiveCapPackingConstant
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : ℝ :=
  2 * 5 ^ Module.finrank ℝ E

/-- The projective-cap packing constant is positive. -/
lemma projectiveCapPackingConstant_pos
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    0 < projectiveCapPackingConstant E := by
  unfold projectiveCapPackingConstant
  positivity

/-- **Projective-cap packing bound.**

For unit vectors all lying in an `R`-projective-cap around a fixed unit
vector `e` and pairwise `r`-projective-separated (in the sign-blind
distance `projNormalDist`), the cardinality is bounded by a dim-only
constant times `(R / r)^n` plus an additive dim-only constant, where
`n := Module.finrank ℝ E`.

The named positive dimensional constant `projectiveCapPackingConstant E`
works whenever `V ⊆ {x : E | ‖x‖ = 1}` is
`r`-projective-separated and inside an `R`-projective-cap around a
unit `e`, then `V.card ≤ C_cap * (R / r) ^ n + C_cap`.  The consumer
only needs a polynomial bound (in the application `R` and `r` are both
proportional to `δ`, so `R/r` is a fixed dim-only constant), so we use
the non-sharp exponent `n` rather than `n - 1`. -/
theorem card_le_of_projective_separated_in_cap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] :
    ∀ {V : Finset E} {e : E} (_he_unit : ‖e‖ = 1)
      (_hV_unit : ∀ v ∈ V, ‖v‖ = 1)
      {R r : ℝ} (_hr_pos : 0 < r) (_hR_pos : 0 < R)
      (_hV_sep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → r ≤ projNormalDist x y)
      (_hV_cap : ∀ x ∈ V, projNormalDist x e ≤ R),
      (V.card : ℝ) ≤ projectiveCapPackingConstant E *
        (R / r) ^ Module.finrank ℝ E + projectiveCapPackingConstant E := by
  -- The bound comes from a volume-packing argument: balls of radius `r/2` around
  -- the points of `V` are pairwise disjoint (by `r`-separation) and lie
  -- inside `closedBall e (R + r/2) ∪ closedBall (-e) (R + r/2)`.  Using
  -- the (non-sharp) exponent `n` rather than `n - 1` makes the proof
  -- closeable using only volume scaling on ambient Euclidean balls.
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  intro V e _he_unit _hV_unit R r hr_pos hR_pos hV_sep hV_cap
  simp only [projNormalDist] at hV_sep hV_cap
  change (V.card : ℝ) ≤ 2 * 5 ^ n * (R / r) ^ n + 2 * 5 ^ n
  -- Set up: `V` is `r`-separated in the ordinary norm (taking the min with
  -- `‖x + y‖` only weakens the bound).  Split `V` according to which cap
  -- side each element lies in: `V_pos` ⊆ `closedBall e R`, `V_neg` ⊆
  -- `closedBall (-e) R`.  For each side, a volume-packing argument bounds
  -- the cardinality by `(2R/r + 1)^n`.
  have hnpos : 0 < n := Module.finrank_pos
  borelize E
  let μ : Measure E := MeasureTheory.Measure.addHaar
  -- Ordinary `r`-separation from the projective `r`-separation.
  have hV_sep' : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → r ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    exact (hV_sep x hx y hy hxy).trans (min_le_left _ _)
  -- Cap inclusion: every `v ∈ V` lies in one of the two closed balls.
  have hV_or : ∀ v ∈ V, ‖v - e‖ ≤ R ∨ ‖v - (-e)‖ ≤ R := by
    intro v hv
    have hmin := hV_cap v hv
    rcases le_total ‖v - e‖ ‖v + e‖ with hle | hle
    · left
      have := min_eq_left hle ▸ hmin
      simpa using this
    · right
      have := min_eq_right hle ▸ hmin
      simpa [sub_neg_eq_add] using this
  -- Split V into the two cap sides using classical filter.
  let V_pos : Finset E := V.filter (fun v => ‖v - e‖ ≤ R)
  let V_neg : Finset E := V.filter (fun v => ¬ ‖v - e‖ ≤ R)
  have hV_split : V = V_pos ∪ V_neg := by
    ext v
    simp only [V_pos, V_neg, Finset.mem_union, Finset.mem_filter]
    tauto
  have hVcard : V.card ≤ V_pos.card + V_neg.card := by
    have : V.card = (V_pos ∪ V_neg).card := by rw [← hV_split]
    rw [this]; exact Finset.card_union_le _ _
  -- For each side, set up the cap inclusion in closedBall(±e, R).
  have hV_pos_in : ∀ v ∈ V_pos, ‖v - e‖ ≤ R := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hV_neg_in : ∀ v ∈ V_neg, ‖v + e‖ ≤ R := by
    intro v hv
    have hv' := Finset.mem_filter.mp hv
    rcases hV_or v hv'.1 with hpos | hneg
    · exact absurd hpos hv'.2
    · simpa [sub_neg_eq_add] using hneg
  -- The volume-packing argument as a reusable lemma.  Given a finset `s`
  -- of points in `closedBall c R` that are `r`-separated, we bound
  -- `s.card * vol(ball(0, r/2)) ≤ vol(ball(c, R + r/2)) =
  --   (R + r/2)^n * vol(ball(0, 1))`.
  have hr2pos : (0 : ℝ) < r / 2 := by linarith
  have hRr2pos : (0 : ℝ) < R + r / 2 := by linarith
  have hpack : ∀ (s : Finset E) (c : E),
      (∀ v ∈ s, ‖v - c‖ ≤ R) →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ ‖x - y‖) →
      (s.card : ℝ) ≤ ((R + r/2) / (r/2)) ^ n := by
    intro s c hs_in hs_sep
    -- Pairwise disjoint open balls of radius r/2.
    have hD : Set.Pairwise (s : Set E) (fun x y => Disjoint (ball x (r/2)) (ball y (r/2))) := by
      intro x hx y hy hxy
      apply ball_disjoint_ball
      have hxy' : r ≤ ‖x - y‖ := hs_sep x hx y hy hxy
      have heq : r/2 + r/2 = r := by ring
      rw [heq, dist_eq_norm]
      exact hxy'
    -- Each ball ball(v, r/2) ⊆ ball(c, R + r/2).
    have hsub : (⋃ v ∈ s, ball v (r/2)) ⊆ ball c (R + r/2) := by
      refine Set.iUnion₂_subset (fun v hv => ?_)
      refine ball_subset_ball' ?_
      have hvc : ‖v - c‖ ≤ R := hs_in v hv
      have hdist : dist v c ≤ R := by rw [dist_eq_norm]; exact hvc
      linarith
    -- Volume computation: μ(⋃ v ∈ s, ball v (r/2)) = card · (r/2)^n · μ(ball 0 1).
    have hμball : ∀ v : E, μ (ball v (r/2)) = ENNReal.ofReal ((r/2) ^ n) * μ (ball (0 : E) 1) :=
      fun v => MeasureTheory.Measure.addHaar_ball_of_pos μ v hr2pos
    have hvol_eq : μ (⋃ v ∈ s, ball v (r/2))
        = (s.card : ℝ≥0∞) * (ENNReal.ofReal ((r/2) ^ n) * μ (ball (0 : E) 1)) := by
      have hpwd : (s : Set E).PairwiseDisjoint (fun v : E => ball v (r/2)) := hD
      rw [measure_biUnion_finset hpwd (fun v _ => measurableSet_ball)]
      simp only [hμball, Finset.sum_const, nsmul_eq_mul]
    have hvol_target : μ (ball c (R + r/2))
        = ENNReal.ofReal ((R + r/2) ^ n) * μ (ball (0 : E) 1) :=
      MeasureTheory.Measure.addHaar_ball_of_pos μ c hRr2pos
    have hle : (s.card : ℝ≥0∞) * (ENNReal.ofReal ((r/2) ^ n) * μ (ball (0 : E) 1))
        ≤ ENNReal.ofReal ((R + r/2) ^ n) * μ (ball (0 : E) 1) := by
      calc (s.card : ℝ≥0∞) * (ENNReal.ofReal ((r/2) ^ n) * μ (ball (0 : E) 1))
          = μ (⋃ v ∈ s, ball v (r/2)) := hvol_eq.symm
        _ ≤ μ (ball c (R + r/2)) := measure_mono hsub
        _ = ENNReal.ofReal ((R + r/2) ^ n) * μ (ball (0 : E) 1) := hvol_target
    -- Cancel the unit-ball volume.
    have hμunit_pos : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ _ zero_lt_one).ne'
    have hμunit_lt : μ (ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
    have hle2 : (s.card : ℝ≥0∞) * ENNReal.ofReal ((r/2) ^ n) * μ (ball (0 : E) 1)
        ≤ ENNReal.ofReal ((R + r/2) ^ n) * μ (ball (0 : E) 1) := by
      rw [mul_assoc]; exact hle
    have hle' : (s.card : ℝ≥0∞) * ENNReal.ofReal ((r/2) ^ n)
        ≤ ENNReal.ofReal ((R + r/2) ^ n) :=
      (ENNReal.mul_le_mul_iff_left hμunit_pos hμunit_lt).1 hle2
    -- Convert to real numbers and divide.
    have hr2n_pos : (0 : ℝ) < (r/2) ^ n := pow_pos hr2pos n
    have hRr2n_nonneg : (0 : ℝ) ≤ (R + r/2) ^ n := pow_nonneg hRr2pos.le n
    have hcard_nonneg : (0 : ℝ) ≤ (s.card : ℝ) := by positivity
    have hcard_real : (s.card : ℝ) * (r/2) ^ n ≤ (R + r/2) ^ n := by
      have h_lhs : (s.card : ℝ≥0∞) * ENNReal.ofReal ((r/2) ^ n)
          = ENNReal.ofReal ((s.card : ℝ) * (r/2) ^ n) := by
        rw [ENNReal.ofReal_mul hcard_nonneg]
        congr 1
        exact (ENNReal.ofReal_natCast s.card).symm
      rw [h_lhs] at hle'
      exact (ENNReal.ofReal_le_ofReal_iff hRr2n_nonneg).mp hle'
    have hcard_real' : (s.card : ℝ) ≤ (R + r/2) ^ n / (r/2) ^ n := by
      rw [le_div_iff₀ hr2n_pos]; exact hcard_real
    calc (s.card : ℝ) ≤ (R + r/2) ^ n / (r/2) ^ n := hcard_real'
      _ = ((R + r/2) / (r/2)) ^ n := (div_pow _ _ _).symm
  -- Apply hpack to V_pos and V_neg.
  have hV_pos_sep : ∀ x ∈ V_pos, ∀ y ∈ V_pos, x ≠ y → r ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    exact hV_sep' x (Finset.mem_of_mem_filter _ hx) y (Finset.mem_of_mem_filter _ hy) hxy
  have hV_neg_sep : ∀ x ∈ V_neg, ∀ y ∈ V_neg, x ≠ y → r ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    exact hV_sep' x (Finset.mem_of_mem_filter _ hx) y (Finset.mem_of_mem_filter _ hy) hxy
  have hV_neg_in' : ∀ v ∈ V_neg, ‖v - (-e)‖ ≤ R := by
    intro v hv
    have : ‖v + e‖ ≤ R := hV_neg_in v hv
    simpa [sub_neg_eq_add] using this
  have hbound_pos : (V_pos.card : ℝ) ≤ ((R + r/2) / (r/2)) ^ n :=
    hpack V_pos e hV_pos_in hV_pos_sep
  have hbound_neg : (V_neg.card : ℝ) ≤ ((R + r/2) / (r/2)) ^ n :=
    hpack V_neg (-e) hV_neg_in' hV_neg_sep
  -- Combine and simplify `(R + r/2) / (r/2) = 2R/r + 1`.
  have hsimp : (R + r/2) / (r/2) = 2 * R / r + 1 := by
    field_simp
  have hsum : (V.card : ℝ) ≤ 2 * (2 * R / r + 1) ^ n := by
    have h1 : (V.card : ℝ) ≤ (V_pos.card : ℝ) + (V_neg.card : ℝ) := by
      exact_mod_cast hVcard
    calc (V.card : ℝ)
        ≤ (V_pos.card : ℝ) + (V_neg.card : ℝ) := h1
      _ ≤ ((R + r/2) / (r/2)) ^ n + ((R + r/2) / (r/2)) ^ n :=
          add_le_add hbound_pos hbound_neg
      _ = 2 * ((R + r/2) / (r/2)) ^ n := by ring
      _ = 2 * (2 * R / r + 1) ^ n := by rw [hsimp]
  -- Bound `(2R/r + 1)^n ≤ 3^n * (R/r)^n + 3^n` by case split.
  have hRr_pos : 0 < R / r := div_pos hR_pos hr_pos
  have h2Rr_nonneg : 0 ≤ 2 * R / r := by
    have : 2 * R / r = 2 * (R / r) := by ring
    rw [this]; linarith
  have hbase_nonneg : (0 : ℝ) ≤ 2 * R / r + 1 := by linarith
  have hbound_aux : (2 * R / r + 1) ^ n ≤ 3 ^ n * (R / r) ^ n + 3 ^ n := by
    have h3pow_nonneg : (0 : ℝ) ≤ 3 ^ n := by positivity
    have hRrpow_nonneg : (0 : ℝ) ≤ (R / r) ^ n := pow_nonneg hRr_pos.le n
    rcases lt_or_ge (R / r) 1 with hlt | hge
    · -- R/r < 1: bound (2R/r + 1) ≤ 3.
      have h2R : 2 * R / r = 2 * (R / r) := by ring
      have h1 : 2 * R / r + 1 ≤ 3 := by rw [h2R]; linarith
      have hpow : (2 * R / r + 1) ^ n ≤ (3 : ℝ) ^ n :=
        pow_le_pow_left₀ hbase_nonneg h1 n
      have : 0 ≤ 3 ^ n * (R / r) ^ n := mul_nonneg h3pow_nonneg hRrpow_nonneg
      linarith
    · -- R/r ≥ 1: bound (2R/r + 1) ≤ 3R/r.
      have h2R : 2 * R / r = 2 * (R / r) := by ring
      have h1 : 2 * R / r + 1 ≤ 3 * (R / r) := by rw [h2R]; linarith
      have hpow : (2 * R / r + 1) ^ n ≤ (3 * (R / r)) ^ n :=
        pow_le_pow_left₀ hbase_nonneg h1 n
      have hsplit : (3 * (R / r)) ^ n = 3 ^ n * (R / r) ^ n := by rw [mul_pow]
      linarith
  -- Combine to get the bound with 3^n.
  have h_final : (V.card : ℝ) ≤ 2 * 3 ^ n * (R / r) ^ n + 2 * 3 ^ n := by
    have h3pow_nonneg : (0 : ℝ) ≤ 3 ^ n := by positivity
    have hRrpow_nonneg : (0 : ℝ) ≤ (R / r) ^ n := pow_nonneg hRr_pos.le n
    have hcombine : 2 * (2 * R / r + 1) ^ n ≤ 2 * (3 ^ n * (R / r) ^ n + 3 ^ n) := by
      have h2nn : (0 : ℝ) ≤ 2 := by norm_num
      exact mul_le_mul_of_nonneg_left hbound_aux h2nn
    calc (V.card : ℝ) ≤ 2 * (2 * R / r + 1) ^ n := hsum
      _ ≤ 2 * (3 ^ n * (R / r) ^ n + 3 ^ n) := hcombine
      _ = 2 * 3 ^ n * (R / r) ^ n + 2 * 3 ^ n := by ring
  -- Absorb 3^n ≤ 5^n.
  have h35 : (3 : ℝ) ^ n ≤ (5 : ℝ) ^ n :=
    pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) (by norm_num : (3:ℝ) ≤ 5) n
  have hRrpow_nonneg : (0 : ℝ) ≤ (R / r) ^ n := pow_nonneg hRr_pos.le n
  have h35_mul : 2 * 3 ^ n * (R / r) ^ n ≤ 2 * 5 ^ n * (R / r) ^ n := by
    have h0 : (0 : ℝ) ≤ 2 * 3 ^ n := by positivity
    have h1 : (2 : ℝ) * 3 ^ n ≤ 2 * 5 ^ n := by linarith
    exact mul_le_mul_of_nonneg_right h1 hRrpow_nonneg
  calc (V.card : ℝ) ≤ 2 * 3 ^ n * (R / r) ^ n + 2 * 3 ^ n := h_final
    _ ≤ 2 * 5 ^ n * (R / r) ^ n + 2 * 5 ^ n := by linarith

end Kakeya
