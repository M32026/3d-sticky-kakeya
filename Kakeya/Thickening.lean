/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Convex.Body
public import Kakeya.Mathlib.Topology.CoveringNumber
public import Kakeya.Thickness.Volume
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Convex.Measure

/-!
In this file we collect facts about how volume grows when we thicken a (convex) set.
-/

@[expose] public section

open MeasureTheory Metric

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace Convexity.IsConvexSet

/-- The multiplicative constant in `volume_cthickening_ge_of_volume_ge'`.
It depends only on the dimension of the Euclidean space. -/
@[nolint defsWithUnderscore]
noncomputable abbrev volume_cthickening_ge_of_volume_ge'.c (dim : ℕ) : NNReal :=
  lt_volume_convexHull.c dim *
    coveringNumber_mul_pow_le_volume_cthickening.C dim *
    (1 / 8 : NNReal) ^ dim

theorem volume_cthickening_ge_of_volume_ge'.c_pos (dim : ℕ) : 0 < c dim := by
  unfold c
  refine mul_pos (mul_pos ?_ ?_) ?_
  · exact lt_volume_convexHull.c_pos dim
  · exact coveringNumber_mul_pow_le_volume_cthickening.C_pos dim
  · exact pow_pos (by norm_num) dim

end Convexity.IsConvexSet

/--
Supporting lemma for `Convex.fullness_thickening` (point 1 of the blueprint proof).

Cover `Y` by `N := coveringNumber r Y` closed balls of radius `r` (the centers lie in `Y`,
hence in `V`). Each piece `V ∩ Bᵢ` has `ethickness` bounded by `min r (ethickness V k)` at
every rank `k` (monotonicity in the set plus the closed-ball bound), so
`volume_le_prod_ethickness` gives the per-piece volume bound. Summing over the `N` pieces
yields:

  `volume Y ≤ 2 ^ n * coveringNumber r Y * ∏_{k=0}^{n-1} min r (ethickness V k)`.

We require `0 < r` and `V` bounded. Boundedness of `V` (combined with `Y ⊆ V` and `0 < r`)
ensures the covering number is finite, so we obtain a genuine finite cover.
-/
private theorem volume_le_coveringNumber_prod_min_ethickness [Nontrivial E]
    {V Y : Set E} (hVb : Bornology.IsBounded V) (hY : Y ⊆ V) {r : NNReal} (hr : 0 < r) :
    volume Y ≤ (2 : ENNReal) ^ Module.finrank ℝ E *
      coveringNumber r Y *
      ∏ k ∈ Finset.range (Module.finrank ℝ E),
        min (r : ENNReal) (ethickness ℝ V k) := by
  set n := Module.finrank ℝ E
  set P : ENNReal := ∏ k ∈ Finset.range n, min (r : ENNReal) (ethickness ℝ V k)
  obtain ⟨C, _hCY, hCcov, hCcard⟩ :=
    Bornology.IsBounded.exists_finset_card_eq_coveringNumber (hVb.subset hY) hr
  replace hCcov : Y ⊆ ⋃ x ∈ C, V ∩ closedBall x r := fun y hy => by
    obtain ⟨x, hxC, hxB⟩ := by simpa using hCcov.subset_iUnion_closedBall hy
    exact Set.mem_biUnion hxC ⟨hY hy, hxB⟩
  have hpiece : ∀ x : E, volume (V ∩ closedBall x r) ≤ 2 ^ n * P := fun x =>
    (volume_le_prod_ethickness (V ∩ closedBall x r)).trans <| mul_le_mul_right
      (Finset.prod_le_prod (fun _ _ => zero_le) fun k _ =>
        le_min (ethickness_le_of_subset_closedBall r Set.inter_subset_right k)
          (ethickness_monotone Set.inter_subset_left k)) _
  calc volume Y
      ≤ ∑ x ∈ C, volume (V ∩ closedBall x r) :=
        (measure_mono hCcov).trans (MeasureTheory.measure_biUnion_finset_le C _)
    _ ≤ ∑ _x ∈ C, 2 ^ n * P := Finset.sum_le_sum fun x _ => hpiece x
    _ = 2 ^ n * (coveringNumber r Y : ENNReal) * P := by
        rw [Finset.sum_const, nsmul_eq_mul,
          show (C.card : ENNReal) = (coveringNumber r Y : ENNReal) from by exact_mod_cast hCcard]
        ring

/-- Upper bound on the volume of the `r`-thickening of a set in terms of the
`max(r, ethickness V k)` quantities.

Follows from `volume_le_prod_ethickness` applied to `Metric.cthickening r V`, combined with
`ethickness_cthickening_le` (giving `ethickness (Metric.cthickening r V) k ≤ r + ethickness V k`)
and the bound `r + δ ≤ 2 * max r δ`. The constant `4 ^ n` decomposes as `2 ^ n` from
`volume_le_prod_ethickness` times `2 ^ n` from the inequality `r + δ ≤ 2 max(r, δ)` applied
in each of the `n` factors. -/
private theorem volume_cthickening_le_prod_max_ethickness [Nontrivial E]
    (V : Set E) (r : NNReal) :
    volume (Metric.cthickening r V) ≤
      (4 : ENNReal) ^ Module.finrank ℝ E *
      ∏ k ∈ Finset.range (Module.finrank ℝ E),
        max (r : ENNReal) (ethickness ℝ V k) := by
  set n := Module.finrank ℝ E
  refine (volume_le_prod_ethickness (Metric.cthickening r V)).trans ?_
  have hfactor : ∀ k, ethickness ℝ (Metric.cthickening r V) k ≤
      (2 : ENNReal) * max (r : ENNReal) (ethickness ℝ V k) := fun k =>
    (ethickness_cthickening_le r k).trans <| by
      rw [two_mul]; exact add_le_add (le_max_left _ _) (le_max_right _ _)
  calc 2 ^ n *
        ∏ k ∈ Finset.range n, ethickness ℝ (Metric.cthickening r V) k
      ≤ 2 ^ n *
          ∏ k ∈ Finset.range n,
            ((2 : ENNReal) * max (r : ENNReal) (ethickness ℝ V k)) :=
        mul_le_mul_right (Finset.prod_le_prod (fun _ _ => zero_le) fun k _ => hfactor k) _
    _ = 4 ^ n *
          ∏ k ∈ Finset.range n, max (r : ENNReal) (ethickness ℝ V k) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
            ← mul_assoc, ← mul_pow]
        norm_num

/-- The dimensional constant in `Convex.volume_cthickening_le_of_le_scale`: it depends only on the
ambient dimension `n` and on the ratio `M` between the thickening radius and the least width. -/
@[nolint defsWithUnderscore]
noncomputable abbrev volume_cthickening_le_of_le_scale.C (n : ℕ) (M : NNReal) : NNReal :=
  4 ^ n * (1 + M) ^ n / lt_volume_convexHull.c n

/-- **Thickening a convex set by at most a bounded multiple of its least width inflates its volume
by at most an absolute factor.**

If every affine thickness of `K` is at least `w` (that is, `w ≤ ethickness.scale ℝ K`) and the
radius satisfies `r ≤ M * w`, then `max r (ethickness ℝ K k) ≤ (1 + M) * ethickness ℝ K k` at every
rank, so the product bound `volume_cthickening_le_prod_max_ethickness` loses only `(1 + M) ^ n`
against `∏ ethickness ℝ K k`, which `Convex.ethickness_prod_le_volume` compares to `volume K`. -/
theorem Convex.volume_cthickening_le_of_le_scale [Nontrivial E] {K : Set E} (hK : Convex ℝ K)
    {w : NNReal} (hw : 0 < w) {r M : NNReal} (hrM : r ≤ M * w)
    (hwidth : (w : ENNReal) ≤ Metric.ethickness.scale ℝ K) :
    volume (Metric.cthickening (r : ℝ) K) ≤
      ((volume_cthickening_le_of_le_scale.C (Module.finrank ℝ E) M : NNReal) : ENNReal) *
        volume K := by
  set n := Module.finrank ℝ E
  set B : ENNReal := ((volume_cthickening_le_of_le_scale.C n M : NNReal) : ENNReal)
  set Peth : ENNReal := ∏ k ∈ Finset.range n, ethickness ℝ K k
  -- For every rank `k < n`, bound `max r (ethickness ℝ K k)` by `(1 + M) * ethickness ℝ K k`.
  have hfactor : ∀ k ∈ Finset.range n,
      max (r : ENNReal) (ethickness ℝ K k) ≤
        ((1 + M : NNReal) : ENNReal) * ethickness ℝ K k := by
    intro k hk
    have hk' : k < Module.finrank ℝ E := by simpa [n] using (Finset.mem_range.mp hk)
    have hweth : (w : ENNReal) ≤ ethickness ℝ K k :=
      le_trans hwidth (Metric.ethickness.scale_le K hk')
    have hrw : (r : ENNReal) ≤ (M : ENNReal) * (w : ENNReal) := by
      rw [← ENNReal.coe_mul]
      exact ENNReal.coe_le_coe.2 hrM
    have hreth : (r : ENNReal) ≤ (M : ENNReal) * ethickness ℝ K k :=
      hrw.trans (mul_le_mul' le_rfl hweth)
    have hone_le : (1 : ENNReal) ≤ ((1 + M : NNReal) : ENNReal) := by simp
    have hMle : (M : ENNReal) ≤ ((1 + M : NNReal) : ENNReal) := by simp
    have hEth_le : ethickness ℝ K k ≤ ((1 + M : NNReal) : ENNReal) * ethickness ℝ K k := by
      simpa [one_mul] using
        (mul_le_mul' hone_le (le_rfl : ethickness ℝ K k ≤ ethickness ℝ K k))
    exact max_le (hreth.trans (mul_le_mul' hMle le_rfl)) hEth_le
  -- The product of the `max` factors is at most `(1 + M) ^ n * ∏ ethickness`.
  have hprod : ∏ k ∈ Finset.range n, max (r : ENNReal) (ethickness ℝ K k) ≤
      ((1 + M : NNReal) : ENNReal) ^ n * Peth := by
    calc ∏ k ∈ Finset.range n, max (r : ENNReal) (ethickness ℝ K k)
        ≤ ∏ k ∈ Finset.range n, ((1 + M : NNReal) : ENNReal) * ethickness ℝ K k :=
            Finset.prod_le_prod (fun _ _ => zero_le) hfactor
      _ = ((1 + M : NNReal) : ENNReal) ^ n * Peth := by
            simp [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Peth]
  -- Casting facts: B * c = 4^n * (1+M)^n, with `c = lt_volume_convexHull.c n`.
  have hc0 : (lt_volume_convexHull.c n : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (lt_volume_convexHull.c_pos n).ne'
  have hctop : (lt_volume_convexHull.c n : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hC : B * (lt_volume_convexHull.c n : ENNReal) =
      (4 : ENNReal) ^ n * ((1 + M : NNReal) : ENNReal) ^ n := by
    change ((volume_cthickening_le_of_le_scale.C n M : NNReal) : ENNReal) *
        (lt_volume_convexHull.c n : ENNReal) =
      (4 : ENNReal) ^ n * ((1 + M : NNReal) : ENNReal) ^ n
    unfold volume_cthickening_le_of_le_scale.C
    rw [ENNReal.coe_div (lt_volume_convexHull.c_pos n).ne']
    rw [ENNReal.div_mul_cancel hc0 hctop]
    norm_num
  -- B * (c * ∏ eth) = 4^n * ((1+M)^n * ∏ eth).
  have hC' : B * ((lt_volume_convexHull.c n : ENNReal) * Peth) =
      (4 : ENNReal) ^ n * (((1 + M : NNReal) : ENNReal) ^ n * Peth) := by
    calc B * ((lt_volume_convexHull.c n : ENNReal) * Peth)
        = (B * (lt_volume_convexHull.c n : ENNReal)) * Peth := by rw [← mul_assoc]
      _ = ((4 : ENNReal) ^ n * ((1 + M : NNReal) : ENNReal) ^ n) * Peth := by rw [hC]
      _ = (4 : ENNReal) ^ n * (((1 + M : NNReal) : ENNReal) ^ n * Peth) := by rw [mul_assoc]
  calc volume (Metric.cthickening (r : ℝ) K)
      ≤ (4 : ENNReal) ^ n *
          ∏ k ∈ Finset.range n, max (r : ENNReal) (ethickness ℝ K k) :=
        volume_cthickening_le_prod_max_ethickness K r
    _ ≤ (4 : ENNReal) ^ n * (((1 + M : NNReal) : ENNReal) ^ n * Peth) := by
        exact mul_le_mul' le_rfl hprod
    _ = B * ((lt_volume_convexHull.c n : ENNReal) * Peth) := hC'.symm
    _ ≤ B * volume K := by
        exact mul_le_mul' le_rfl hK.ethickness_prod_le_volume

namespace Convexity.IsConvexSet

/-- The proportion of a shading inside a convex set is roughly monotone when we thicken
both the shading and the convex set. Special case `0 < r`; see
`volume_cthickening_ge_of_volume_ge` for the version that also covers `r = 0`. -/
theorem volume_cthickening_ge_of_volume_ge' [Nontrivial E] {V Y : Set E} (hV : IsConvexSet ℝ V)
    (hVb : Bornology.IsBounded V) (hVvol : 0 < volume V)
    (hY : Y ⊆ V) {r : NNReal} (hr_pos : 0 < r)
    {a : ENNReal} (h : volume Y ≥ a * volume V) :
    volume (Metric.cthickening r Y) ≥
      volume_cthickening_ge_of_volume_ge'.c (Module.finrank ℝ E) * a *
        volume (Metric.cthickening r V) := by
  set n := Module.finrank ℝ E
  set δ : ℕ → ENNReal := fun k => ethickness ℝ V k
  set a₀ : NNReal := lt_volume_convexHull.c n
  set b₀ : NNReal := coveringNumber_mul_pow_le_volume_cthickening.C n
  -- Abbreviate
  set N : ENNReal := (coveringNumber r Y : ENNReal)
  set M : ENNReal := ∏ k ∈ Finset.range n, min (r : ENNReal) (δ k)
  set X : ENNReal := ∏ k ∈ Finset.range n, max (r : ENNReal) (δ k)
  set Pδ : ENNReal := ∏ k ∈ Finset.range n, δ k
  -- Pδ is finite (δ k is finite for each k since V is bounded).
  have hPδ_ne_top : Pδ ≠ ⊤ :=
    ENNReal.prod_ne_top fun k _ => ethickness_ne_top hVb k
  -- Pδ ≠ 0 (since each `ethickness ℝ V k` is nonzero when `0 < volume V`).
  have hPδ_ne_zero : Pδ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun _ hk =>
    ethickness_ne_zero_of_volume_pos hVvol hk
  -- Key identity: M * X = r^n * Pδ (since min a b * max a b = a * b pointwise).
  have hMX : M * X = (r : ENNReal) ^ n * Pδ := by
    change (∏ k ∈ Finset.range n, min (r : ENNReal) (δ k)) *
        (∏ k ∈ Finset.range n, max (r : ENNReal) (δ k)) = _
    rw [← Finset.prod_mul_distrib,
        Finset.prod_congr rfl (fun k _ => min_mul_max (r : ENNReal) (δ k)),
        Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  -- Point 1: volume Y ≤ 2^n * N * M.
  have hpoint1 : volume Y ≤ 2 ^ n * N * M :=
    volume_le_coveringNumber_prod_min_ethickness hVb hY hr_pos
  -- Point 3: volume (cth r V) ≤ 4^n * X.
  have hpoint3 : volume (Metric.cthickening r V) ≤ 4 ^ n * X :=
    volume_cthickening_le_prod_max_ethickness V r
  -- Point 2: b₀ * N * r^n ≤ volume (cth r Y).
  have hpoint2 : (b₀ : ENNReal) * N * (r : ENNReal) ^ n ≤ volume (Metric.cthickening r Y) :=
    coveringNumber_mul_pow_le_volume_cthickening r Y
  -- Volume V lower bound: a₀ * Pδ ≤ volume V.
  have hpointV : (a₀ : ENNReal) * Pδ ≤ volume V :=
    hV.convex.ethickness_prod_le_volume
  -- Combine: bound `vol(cth r V) ≤ 4^n * X`, then bound `a * a₀ * X` by `2^n * N * r^n`
  -- via Pδ-cancellation, then plug in `b₀ * N * r^n ≤ vol(cth r Y)`. We use
  -- `c n = a₀ * b₀ * (1/8)^n` and `(1/8)^n * 4^n * 2^n = 1`.
  have h_inv8 : ((1 / 8 : NNReal) ^ n : ENNReal) * (4 ^ n * 2 ^ n) = 1 := by
    rw [show ((1 / 8 : NNReal) ^ n : ENNReal) = ((1 / 8 : ENNReal)) ^ n by norm_num,
        show (4 : ENNReal) ^ n * 2 ^ n = 8 ^ n from by rw [← mul_pow]; norm_num,
        ← mul_pow, ENNReal.div_mul_cancel (by norm_num) (by norm_num), one_pow]
  -- The chain `a * (a₀ * Pδ) ≤ a * vol V ≤ vol Y ≤ 2^n * N * M`, multiplied by
  -- `vol(cth r V) ≤ 4^n * X`, yields a single combined inequality.
  have hbig : a * ((a₀ : ENNReal) * Pδ) * volume (Metric.cthickening r V) ≤
      (2 ^ n * N * M) * (4 ^ n * X) :=
    mul_le_mul' (((mul_le_mul_right hpointV a).trans h).trans hpoint1) hpoint3
  refine (ENNReal.mul_le_mul_iff_left hPδ_ne_zero hPδ_ne_top).mp ?_
  -- Pull `(1/8)^n` to the front and `b₀` next, then chain via `hbig` and `h_inv8`/`hMX`.
  calc ((a₀ * b₀ * (1 / 8 : NNReal) ^ n : NNReal) : ENNReal) * a *
          volume (Metric.cthickening r V) * Pδ
      = ((1 / 8 : NNReal) ^ n : ENNReal) * ((b₀ : ENNReal) *
          (a * ((a₀ : ENNReal) * Pδ) * volume (Metric.cthickening r V))) := by
        simp only [ENNReal.coe_mul, ENNReal.coe_pow]; ring
    _ ≤ ((1 / 8 : NNReal) ^ n : ENNReal) * ((b₀ : ENNReal) *
          ((2 ^ n * N * M) * (4 ^ n * X))) :=
        mul_le_mul_right (mul_le_mul_right hbig _) _
    _ = (((1 / 8 : NNReal) ^ n : ENNReal) * (4 ^ n * 2 ^ n)) *
          ((b₀ : ENNReal) * N * (M * X)) := by ring
    _ = ((b₀ : ENNReal) * N * (r : ENNReal) ^ n) * Pδ := by
          rw [h_inv8, one_mul, hMX, ← mul_assoc]
    _ ≤ volume (Metric.cthickening r Y) * Pδ := mul_le_mul_left hpoint2 _

/-- The multiplicative constant in `volume_cthickening_ge_of_volume_ge`, clamped at `1` so
that the inequality also holds in the degenerate case `r = 0`. -/
@[nolint defsWithUnderscore]
noncomputable abbrev volume_cthickening_ge_of_volume_ge.c (dim : ℕ) : NNReal :=
  min 1 (volume_cthickening_ge_of_volume_ge'.c dim)

theorem volume_cthickening_ge_of_volume_ge.c_pos (dim : ℕ) : 0 < c dim :=
  lt_min one_pos (volume_cthickening_ge_of_volume_ge'.c_pos dim)

theorem volume_cthickening_ge_of_volume_ge.c_le_one (dim : ℕ) : c dim ≤ 1 := min_le_left _ _

/-- The proportion of a shading inside a convex set is roughly monotone when we thicken
both the shading and the convex set, valid for any `r ≥ 0`. -/
theorem volume_cthickening_ge_of_volume_ge [Nontrivial E] {V Y : Set E} (hV : IsConvexSet ℝ V)
    (hVb : Bornology.IsBounded V) (hVvol : 0 < volume V)
    (hY : Y ⊆ V) (r : NNReal)
    {a : ENNReal} (h : volume Y ≥ a * volume V) :
    volume (Metric.cthickening r Y) ≥
      volume_cthickening_ge_of_volume_ge.c (Module.finrank ℝ E) * a *
        volume (Metric.cthickening r V) := by
  by_cases hr : r = 0
  -- rcases (zero_le r).eq_or_lt with hr0 | hr_pos
  · -- r = 0: cthickening 0 = closure; use that `closure V` has the same volume as `V`.
    subst hr
    norm_cast
    rw [Metric.cthickening_zero, Metric.cthickening_zero]
    calc
      _  = (volume_cthickening_ge_of_volume_ge.c (Module.finrank ℝ E) : ENNReal) * a *
            volume V := by
            rw [measure_closure_of_null_frontier]
            apply hV.convex.addHaar_frontier (μ := volume)
      _ ≤ (1 : ENNReal) * a * volume V := by
            gcongr
            exact_mod_cast volume_cthickening_ge_of_volume_ge.c_le_one _
      _ = a * volume V := by rw [one_mul]
      _ ≤ volume Y := h
      _ ≤ volume (closure Y) := measure_mono subset_closure
  · -- 0 < r: invoke the primed version and weaken the constant via `c ≤ c'`.
    replace hr : 0 < r := by positivity
    calc
      _  ≤ (volume_cthickening_ge_of_volume_ge'.c (Module.finrank ℝ E) : ENNReal) * a *
            volume (Metric.cthickening r V) := by
          gcongr
          exact min_le_right _ _
      _ ≤ volume (Metric.cthickening r Y) :=
          volume_cthickening_ge_of_volume_ge' hV hVb hVvol hY hr h

end Convexity.IsConvexSet
