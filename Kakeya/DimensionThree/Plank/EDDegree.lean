/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank
public import Kakeya.DimensionThree.Plank.EDExtraction
public import Kakeya.Tube.Basic

/-!
# The direction step of the ED conflict-degree bound

`Kakeya/DimensionThree/Plank/EDExtraction.lean` reduces essential distinctness of the inner plank
family to a bound on the *conflict degree*: the number of planks that fail to be essentially
distinct from a fixed one.  The route to that bound recorded there has four steps, of which this
file supplies step 3.

The reason step 3 matters is quantitative.  The generic count
`Kakeya.card_le_of_ED_subset` bounds pairwise-ED `δ`-tubes in a container by
`C · M · δ ^ (-(n-1))`, the factor `δ ^ (-(n-1))` being the number of *direction caps* needed to
cover the sphere.  That factor is fatal here: it makes the conflict degree `δ ^ (-2)` in `ℝ³` and
no power of `δ` can absorb it.  But it is also unnecessary, because all the tubes being counted are
nearly parallel.  `Kakeya.position_count_le_of_bad_directionClass'` is the sharp count for a
*single* direction cap, and it returns `C · M / c` — an absolute constant once the container is
tube-shaped.  Its hypothesis is exactly

`∀ i ∈ s, min ‖(T i).direction - e‖ ‖(T i).direction + e‖ ≤ c_slide * δ`,

a *projective* cap: directions are compared up to sign, since a tube does not remember which of its
two endpoints is which.

This file proves that hypothesis from containment.  `Kakeya.projective_cap_of_orthogonal_le` is the
linear-algebra core — a unit vector whose component orthogonal to another unit vector is small is
projectively close to it — and
`Kakeya.Tube.direction_projective_cap_of_subset_cthickening` is the tube-level statement: a
`δ`-tube contained in the `r`-neighbourhood of another `δ`-tube has direction in the
`√2 · 2 (r + δ)` projective cap around it.

The sign ambiguity is why the bound is stated with `min` and why the constant carries a `√2`: at
the extreme `r = 1` the two unit vectors may be antipodal, and `min ‖v - u‖ ‖v + u‖` is then `0`,
which the estimate must not contradict.

## The assembly interface

`Kakeya.exists_inner_plank_ED_subfamily_of_bounded_conflict_degree` is the seam at which the
combinatorics and the geometry meet.  It takes a finite family of shaded planks and a bound `d` on
`Kakeya.edConflictDegree` and returns an essentially distinct subfamily at cardinality loss
`d + 1`.  It contains no geometry: `d` is an arbitrary natural number, not a constant, so the
statement is agnostic about whether the eventual bound is absolute or scale-dependent.  Producing a
`d` is the job of the geometric steps 1--3 above.
-/

@[expose] public section

open MeasureTheory Metric

noncomputable section

namespace Kakeya

/-- **A unit vector with small orthogonal component lies in a projective cap.**

If `u`, `v` are unit vectors and the component of `v` orthogonal to `u` has norm at most `r`, then
`v` is within `√2 · r` of `u` *or of* `-u`.

Both alternatives are genuinely needed: `v = -u` has zero orthogonal component, so no bound on
`‖v - u‖` alone can hold.  This is the projective form consumed by
`Kakeya.position_count_le_of_bad_directionClass'`.

The proof is the identity `min ‖v - u‖² ‖v + u‖² = 2 - 2 |⟪u, v⟫|` for unit vectors, together with
`|⟪u, v⟫| = √(1 - ‖v - ⟪u, v⟫ • u‖²) ≥ √(1 - r²)` and `2 - 2√(1 - r²) ≤ 2 r²` on `[0, 1]`. -/
theorem projective_cap_of_orthogonal_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {r : ℝ} (hr0 : 0 ≤ r)
    (h : ‖v - (inner ℝ u v : ℝ) • u‖ ≤ r) :
    min ‖v - u‖ ‖v + u‖ ≤ Real.sqrt 2 * r := by
  let c : ℝ := inner ℝ u v
  let w : E := v - c • u
  have hnorm_sub : ‖v - u‖ ^ 2 = 2 - 2 * c := by
    rw [norm_sub_sq_real, hv, hu, real_inner_comm]
    dsimp [c]
    ring
  have hnorm_add : ‖v + u‖ ^ 2 = 2 + 2 * c := by
    rw [norm_add_sq_real, hv, hu, real_inner_comm]
    dsimp [c]
    ring
  have horth : inner ℝ u w = 0 := by
    dsimp [w, c]
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu]
    ring
  have hv_eq : v = c • u + w := by
    dsimp [w]
    abel
  have hnorm_smul : ‖c • u‖ ^ 2 = c ^ 2 := by
    simp [norm_smul, hu, Real.norm_eq_abs, sq_abs]
  have horth' : inner ℝ (c • u) w = 0 := by
    simp [real_inner_smul_left, horth]
  have hc2 : c ^ 2 = 1 - ‖w‖ ^ 2 := by
    have hnorm : ‖v‖ ^ 2 = c ^ 2 + ‖w‖ ^ 2 := by
      rw [hv_eq, norm_add_sq_real, hnorm_smul, horth']
      ring
    rw [hv] at hnorm
    nlinarith
  let m : ℝ := min ‖v - u‖ ‖v + u‖
  have hm_nonneg : 0 ≤ m := by
    dsimp [m]
    exact le_min (norm_nonneg _) (norm_nonneg _)
  have hm2_abs : m ^ 2 ≤ 2 - 2 * |c| := by
    rcases le_or_gt 0 c with hc | hc
    · calc
        m ^ 2 ≤ ‖v - u‖ ^ 2 :=
          pow_le_pow_left₀ hm_nonneg (min_le_left ‖v - u‖ ‖v + u‖) 2
        _ = 2 - 2 * c := hnorm_sub
        _ = 2 - 2 * |c| := by rw [abs_of_nonneg hc]
    · calc
        m ^ 2 ≤ ‖v + u‖ ^ 2 :=
          pow_le_pow_left₀ hm_nonneg (min_le_right ‖v - u‖ ‖v + u‖) 2
        _ = 2 + 2 * c := hnorm_add
        _ = 2 - 2 * |c| := by rw [abs_of_neg hc]; ring
  by_cases h1 : 1 ≤ r
  · have hm2le2 : m ^ 2 ≤ 2 := by
      calc
        m ^ 2 ≤ 2 - 2 * |c| := hm2_abs
        _ ≤ 2 := by nlinarith [abs_nonneg c]
    have hr2 : 1 ≤ r ^ 2 := by nlinarith [h1, hr0]
    have hm2le : m ^ 2 ≤ 2 * r ^ 2 := by nlinarith [hm2le2, hr2, hr0]
    have hm2le' : m ^ 2 ≤ (Real.sqrt 2 * r) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      exact hm2le
    have hsqrt_nonneg : 0 ≤ Real.sqrt 2 * r := mul_nonneg (Real.sqrt_nonneg 2) hr0
    have h_abs : |m| ≤ |Real.sqrt 2 * r| := sq_le_sq.mp hm2le'
    rwa [abs_of_nonneg hm_nonneg, abs_of_nonneg hsqrt_nonneg] at h_abs
  · have hr1 : r < 1 := lt_of_not_ge h1
    have h1r2 : 0 ≤ 1 - r ^ 2 := by nlinarith [hr0, hr1]
    have hw2 : ‖w‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg w) h 2
    have hc2ge : 1 - r ^ 2 ≤ c ^ 2 := by nlinarith [hc2, hw2]
    have hcabs : Real.sqrt (1 - r ^ 2) ≤ |c| := by
      have htmp : Real.sqrt (1 - r ^ 2) ≤ Real.sqrt (c ^ 2) :=
        Real.sqrt_le_sqrt hc2ge
      rwa [Real.sqrt_sq_eq_abs] at htmp
    have hs_nonneg : 0 ≤ Real.sqrt (1 - r ^ 2) := Real.sqrt_nonneg _
    have hs_le1 : Real.sqrt (1 - r ^ 2) ≤ 1 :=
      (Real.sqrt_le_one).2 (by nlinarith [hr0, hr1])
    have hsq_le : Real.sqrt (1 - r ^ 2) ^ 2 ≤ Real.sqrt (1 - r ^ 2) := by
      nlinarith [hs_nonneg, hs_le1]
    have hmain : 2 - 2 * Real.sqrt (1 - r ^ 2) ≤ 2 * r ^ 2 := by
      have hsq : Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt h1r2
      nlinarith [hsq, hsq_le]
    have hm2le : m ^ 2 ≤ 2 * r ^ 2 := by
      calc
        m ^ 2 ≤ 2 - 2 * |c| := hm2_abs
        _ ≤ 2 - 2 * Real.sqrt (1 - r ^ 2) := by nlinarith [hcabs]
        _ ≤ 2 * r ^ 2 := hmain
    have hm2le' : m ^ 2 ≤ (Real.sqrt 2 * r) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      exact hm2le
    have hsqrt_nonneg : 0 ≤ Real.sqrt 2 * r := mul_nonneg (Real.sqrt_nonneg 2) hr0
    have h_abs : |m| ≤ |Real.sqrt 2 * r| := sq_le_sq.mp hm2le'
    rwa [abs_of_nonneg hm_nonneg, abs_of_nonneg hsqrt_nonneg] at h_abs

/-- **A tube inside a neighbourhood of another tube is projectively parallel to it.**

Step 3 of the conflict-degree route.  If `T'` lies in the `r`-neighbourhood of `T`, then both
endpoints of `T'` are within `r + δ` of the line spanned by `T.direction` through `T.x`; the
difference of the two endpoints is `T'.direction`, so its component orthogonal to `T.direction` has
norm at most `2 (r + δ)`, and `Kakeya.projective_cap_of_orthogonal_le` finishes.

In the application `r` is a fixed multiple of `δ` — the pullback of the bounded dilate produced by
step 1 — so the conclusion is a cap of radius `c_slide · δ` with `c_slide` absolute, which is
exactly the shape `Kakeya.position_count_le_of_bad_directionClass'` consumes. -/
theorem Tube.direction_projective_cap_of_subset_cthickening
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    {δ : NNReal} (T T' : Tube δ E) {r : ℝ} (hr0 : 0 ≤ r)
    (hsub : (T'.carrier : Set E) ⊆ Metric.cthickening r (T.carrier : Set E)) :
    min ‖T'.direction - T.direction‖ ‖T'.direction + T.direction‖
      ≤ Real.sqrt 2 * (2 * (r + (δ : ℝ))) := by
  set u : E := T.direction with hu
  set v : E := T'.direction with hv
  have hunorm : ‖u‖ = 1 := by rw [hu]; exact T.norm_direction
  have hvnorm : ‖v‖ = 1 := by rw [hv]; exact T'.norm_direction
  -- orthogonal projection off `u` is a contraction
  have huu : (inner ℝ u u : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hunorm, one_pow]
  have key : ∀ w : E, ‖w - (inner ℝ w u) • u‖ ^ 2 = ‖w‖ ^ 2 - (inner ℝ w u) ^ 2 := fun w => by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hunorm, mul_one,
      sq_abs]
    ring
  have hproj_le : ∀ w : E, ‖w - (inner ℝ w u) • u‖ ≤ ‖w‖ := fun w =>
    le_of_sq_le_sq (by rw [key w]; linarith only [sq_nonneg (inner ℝ w u : ℝ)]) (norm_nonneg _)
  have proj_add : ∀ a b : E, (a + b) - (inner ℝ (a + b) u) • u
      = (a - (inner ℝ a u) • u) + (b - (inner ℝ b u) • u) := by
    intro a b; rw [inner_add_left, add_smul]; exact (sub_add_sub_comm _ _ _ _).symm
  have proj_neg : ∀ w : E, (-w) - (inner ℝ (-w) u) • u = -(w - (inner ℝ w u) • u) := by
    intro w
    rw [inner_neg_left, neg_smul]
    abel
  have proj_sub : ∀ a b : E, (a - b) - (inner ℝ (a - b) u) • u
      = (a - (inner ℝ a u) • u) - (b - (inner ℝ b u) • u) := by
    intro a b
    calc
      (a - b) - (inner ℝ (a - b) u) • u
          = (a + (-b)) - (inner ℝ (a + (-b)) u) • u := by
            simp [sub_eq_add_neg]
        _ = (a - (inner ℝ a u) • u) + ((-b) - (inner ℝ (-b) u) • u) := proj_add a (-b)
        _ = (a - (inner ℝ a u) • u) - (b - (inner ℝ b u) • u) := by
            rw [proj_neg b]
            abel
  have proj_smul_u : ∀ c : ℝ, (c • u) - (inner ℝ (c • u) u) • u = 0 := by
    intro c; rw [real_inner_smul_left, huu, mul_one, sub_self]
  -- endpoints of `T'` lie in its carrier
  have hx_mem : T'.x ∈ T'.carrier := by
    rw [T'.carrier_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨T'.x, left_mem_segment ℝ T'.x T'.y, Metric.mem_closedBall_self δ.coe_nonneg⟩
  have hy_mem : T'.y ∈ T'.carrier := by
    rw [T'.carrier_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨T'.y, right_mem_segment ℝ T'.x T'.y, Metric.mem_closedBall_self δ.coe_nonneg⟩
  -- `T.carrier` is closed, so the `r`-thickening is a union of radius-`r` balls
  have hclosed : IsClosed (T.carrier : Set E) := T.isCompact.isClosed
  have hcth : Metric.cthickening r (T.carrier : Set E)
      = ⋃ z ∈ (T.carrier : Set E), closedBall z r :=
    hclosed.cthickening_eq_biUnion_closedBall hr0
  -- any point `p` in the `r`-neighbourhood of `T` has small orthogonal component off `u`
  have horth_le : ∀ p : E, p ∈ Metric.cthickening r (T.carrier : Set E) →
      ‖(p - T.x) - (inner ℝ (p - T.x) u) • u‖ ≤ r + (δ : ℝ) := by
    intro p hp
    rw [hcth] at hp
    obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.mp hp
    rw [Metric.mem_closedBall] at hpz
    rw [T.carrier_eq] at hz
    obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hz
    rw [Metric.mem_closedBall] at hzw
    obtain ⟨a, b, ha, hb, hab, hweq⟩ := hw
    have hwsub : w - T.x = b • u := by
      rw [hu, Tube.direction, ← hweq]
      conv_lhs =>
        rhs
        rw [show T.x = (a + b) • T.x from by rw [hab, one_smul]]
      rw [add_smul, add_sub_add_comm, sub_self, zero_add, ← smul_sub]
    have horth_w : (w - T.x) - (inner ℝ (w - T.x) u) • u = 0 := by
      rw [hwsub, proj_smul_u]
    have hle : ‖(p - T.x) - (inner ℝ (p - T.x) u) • u‖ ≤ dist p w := by
      calc
        ‖(p - T.x) - (inner ℝ (p - T.x) u) • u‖
            = ‖(p - T.x) - (inner ℝ (p - T.x) u) • u
                - ((w - T.x) - (inner ℝ (w - T.x) u) • u)‖ := by
              rw [horth_w, sub_zero]
          _ = ‖(p - w) - (inner ℝ (p - w) u) • u‖ := by
              rw [← proj_sub (p - T.x) (w - T.x)]
              congr 1
              abel
          _ ≤ ‖p - w‖ := hproj_le (p - w)
          _ = dist p w := by rw [dist_eq_norm]
    calc
      ‖(p - T.x) - (inner ℝ (p - T.x) u) • u‖ ≤ dist p w := hle
      _ ≤ dist p z + dist z w := dist_triangle p z w
      _ ≤ r + (δ : ℝ) := add_le_add hpz hzw
  have hx_le := horth_le T'.x (hsub hx_mem)
  have hy_le := horth_le T'.y (hsub hy_mem)
  -- the orthogonal component of `v` is the difference of the two endpoint components
  have hv_orth : v - (inner ℝ v u) • u
      = (T'.y - T.x) - (inner ℝ (T'.y - T.x) u) • u
        - ((T'.x - T.x) - (inner ℝ (T'.x - T.x) u) • u) := by
    rw [hv, Tube.direction]
    rw [← proj_sub (T'.y - T.x) (T'.x - T.x)]
    exact congrArg (fun z : E => z - (inner ℝ z u) • u) (by abel)
  have hv_orth_le : ‖v - (inner ℝ v u) • u‖ ≤ 2 * (r + (δ : ℝ)) := by
    rw [hv_orth]
    refine (norm_sub_le _ _).trans ?_
    linarith only [hx_le, hy_le]
  -- conclude with the projective-cap lemma (switching the inner product to `u` first)
  have hv_orth_le' : ‖v - (inner ℝ u v) • u‖ ≤ 2 * (r + (δ : ℝ)) := by
    simpa [real_inner_comm] using hv_orth_le
  exact projective_cap_of_orthogonal_le hunorm hvnorm
    (mul_nonneg (by norm_num) (add_nonneg hr0 (NNReal.coe_nonneg δ))) hv_orth_le'

/-- **Interface lemma for the ED-degree assembly.**

Given a finite family `P` of shaded planks indexed by `q` and a bound `d` on the ED conflict degree
of every member, there is a subfamily `s ⊆ q` that is pairwise essentially distinct and loses only a
factor `d + 1` in cardinality.

This is the exact shape the inner plank family of GWZ Proposition 6.6(B) is missing after
normalisation, and the exact shape the geometric half of the argument has to feed: the only input
beyond the family itself is the numerical hypothesis `hdeg`.

The lemma is deliberately geometry-free.  `d` is an arbitrary natural number rather than an absolute
constant, so nothing here presumes that the eventual conflict-degree bound is `O(1)`; a bound
depending on `δ`, on the plank eccentricity, or on the ambient dimension instantiates it just as
well.  The intended producers of `hdeg` are the plank-overlap step (a conflicting plank lies in a
bounded dilate of its partner) together with the direction step
`Kakeya.Tube.direction_projective_cap_of_subset_cthickening` and the single-cap count
`Kakeya.position_count_le_of_bad_directionClass'`; none of that is assumed or used below. -/
theorem exists_inner_plank_ED_subfamily_of_bounded_conflict_degree
    {ι : Type*} {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    (q : Finset ι) (P : ι → ShadedPlank a b hab hb1) {d : ℕ}
    (hdeg : ∀ i ∈ q, edConflictDegree q (fun j => (P j).carrier) i ≤ d) :
    ∃ s ⊆ q,
      (s : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (P i).carrier (P j).carrier) ∧
      q.card ≤ (d + 1) * s.card := by
  exact exists_essentiallyDistinct_subset q (fun j => (P j).carrier) hdeg

end Kakeya

end

end
