/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallFactoringLemma92
public import Kakeya.DimensionThree.MainLemma2.SetupWithDims

/-!
# The dimensions pigeonhole: fixing `(a, b)` across the balls after the per-ball factoring

General-branch steps G4. GWZ §9.3, `gwz.txt`
l.2039-2041: "by pigeonholing, we can suppose that for each `B`, the convex sets `W ∈ 𝕎_B` have
dimensions `a × b × r₁`". The per-ball factoring
(`Kakeya.VeryNotSticky.exists_ballFactoring_core`, G2) already gives, *inside* one ball, the
comparability of the whole thickness profile of its bodies at Lemma 9.2's `δ`-free constant
`Kakeya.VeryNotSticky.lemma92Constant cfg.ϱ` (its clause `simDims`, GWZ Lemma 9.2's last
assertion "each of approximately the same dimensions"). What is missing is a **single** pair
`(a, b)` valid across the balls, and that is bought by a pigeonhole: the two short thicknesses
of a ball are rounded to a geometric class of ratio `ρ > 1`, the class carrying the most
retained mass is kept, and the other balls are dropped.

## Contents

* `scaleClass`, `scaleValue`: the ratio-`ρ` geometric class of a positive real and its
  representative value, with the two-sided spec `scaleValue (scaleClass x) / ρ < x ≤
  scaleValue (scaleClass x)` and antitonicity of the class.
* `exists_maxMass_fiber`: the pigeonhole itself — a label with at most `N` values has a fibre
  carrying at least `N⁻¹` of the total mass.
* `bodyMinThickness`: the smallest `k`-thickness among the bodies of one ball (defined through
  `Metric.ethickness`, so that `Finset.inf` is total), with its attainment and lower bound.
* `dimsConstant C₀ ρ CF = max C₀ (ρ * CF)`: the thickness-comparison constant the pigeonhole
  delivers, and `dimsClassLoss ρ δ = (⌊log_ρ (1/δ)⌋₊ + 1) ^ 2`: the **explicit** pigeonhole
  loss (two classes, each with `⌊log_ρ (1/δ)⌋₊ + 1` values). It is polylogarithmic:
  `dimsClassLoss_le_polylog` bounds it by `(1 + log_ρ (1/δ)) ^ 2` and
  `eventually_dimsClassLoss_le_rpow` absorbs it into `δ ^ (-ε)` for every `ε > 0`.
* **`exists_dimsClass`**: the pigeonhole, on abstract per-ball body data in the shape
  `Kakeya.VeryNotSticky.BallDataCore.toBallData` reads. Output: `(a, b)` with
  `δ ≤ a ≤ b ≤ r₁`, a retained ball set `bs'` carrying `dimsClassLoss⁻¹` of the mass, the
  binder `bodies_thickness` at `dimsConstant C₀ ρ CF` on every body of every retained ball,
  and — under the budget `ρ * CF ≤ 4` — a `w₁` with `δ ≤ w₁ ≤ 2 r₁` satisfying the factor-2
  window `bodies_w₁`.
* `bodyProfile_of_core`: the two profile inputs of `exists_dimsClass` (the long thickness
  bounded below by `C₀⁻¹ r₁`, the short one bounded below by `δ`) derived from the
  `BallDataCore` fields `segs_thickness` and `segs_scale` through `segs_le`.
* `exists_dimsClass_core`: the two combined on a `BallDataCore`, with the profile stated
  against `Kakeya.VeryNotSticky.withDims cfg a b hdims` — literally the `bodies_thickness`
  binder of `toBallData` for the transported configuration, which a tripwire `example`
  records.
* `exists_heavyBalls`, `exists_heavyBalls_at`: the *other* ball deletion of GWZ §9.3 — the
  fullness cut of l.2029-2032, which keeps the balls carrying the per-ball fullness at half the
  global threshold and half of the shade mass. On the balls it discards the per-ball fullness is
  genuinely false, so this too can only ever be a property of a retained ball set.
* **`exists_dimsClass_heavy`**: the two deletions composed in the only admissible order —
  fullness cut first, dims class second — at the single explicit loss
  `Cg₂ = 2 * dimsClassLoss ρ δ`. A per-ball property of the input ball set survives the second
  deletion because it passes to a subset; the reverse order retains nothing.

## What this does not do

It does not restrict the core to the retained ball set `bs'` (the `(C2)`/`(C5)` clauses on
fewer balls, with the matching cut of the working shading `Yg` — G3/G5's `tierCore`), it does
not glue the per-ball bodies of G2 into one `Wb` on a shared index type, and it asserts nothing
about essential distinctness of a ball's bodies — the field that once carried that assertion,
`BallData.bodies_essDistinct`, no longer exists, statement question R26 having deleted it. The
selection order is GWZ's and the
plan's §2.3: the class is chosen **after** the factoring and deletes whole *balls*, never
members of a block, so `frostman`, `biasedDensity` and `bodies_antiClustering` are read on
exactly Lemma 9.2's blocks. Nothing here changes a existing statement.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology Asymptotics
open scoped NNReal ENNReal

universe u

namespace Kakeya.VeryNotSticky


/-- The ratio-`ρ` scale class of a real number. -/
noncomputable def scaleClass (ρ : ℝ≥0) (x : ℝ) : ℕ := ⌊Real.logb (ρ : ℝ) x⁻¹⌋₊

/-- The representative value of the ratio-`ρ` scale class `n`. -/
noncomputable def scaleValue (ρ : ℝ≥0) (n : ℕ) : ℝ≥0 := ρ⁻¹ ^ n

/-- The class values are positive. -/
theorem scaleValue_pos {ρ : ℝ≥0} (hρ : 0 < ρ) (n : ℕ) : 0 < scaleValue ρ n := by
  simpa [scaleValue] using pow_pos (inv_pos.2 hρ) n

/-- `scaleValue` in `ℝ`. -/
theorem coe_scaleValue {ρ : ℝ≥0} (n : ℕ) : ((scaleValue ρ n : ℝ≥0) : ℝ) = ((ρ : ℝ)⁻¹) ^ n := by
  simp [scaleValue]

/-- **Upper half of the class spec**: `x` does not exceed the value of its own class. -/
theorem le_scaleValue {ρ : ℝ≥0} (hρ : 1 < ρ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    x ≤ (scaleValue ρ (scaleClass ρ x) : ℝ) := by
  have hρ' : (1 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  have hρ0 : (0 : ℝ) < (ρ : ℝ) := lt_trans zero_lt_one hρ'
  have hxinv : (1 : ℝ) ≤ x⁻¹ := by
    rw [le_inv_comm₀ zero_lt_one hx]; simpa using hx1
  have hL0 : 0 ≤ Real.logb (ρ : ℝ) x⁻¹ := Real.logb_nonneg hρ' hxinv
  have hfl : ((scaleClass ρ x : ℕ) : ℝ) ≤ Real.logb (ρ : ℝ) x⁻¹ := Nat.floor_le hL0
  have h1 : (ρ : ℝ) ^ ((scaleClass ρ x : ℕ) : ℝ) ≤ (ρ : ℝ) ^ Real.logb (ρ : ℝ) x⁻¹ :=
    (Real.rpow_le_rpow_left_iff hρ').2 hfl
  rw [Real.rpow_logb hρ0 (ne_of_gt hρ') (inv_pos.2 hx), Real.rpow_natCast] at h1
  have hpos : (0 : ℝ) < (ρ : ℝ) ^ (scaleClass ρ x : ℕ) := pow_pos hρ0 _
  have h2 := (le_inv_comm₀ hpos hx).1 h1
  rw [coe_scaleValue, inv_pow]
  exact h2

/-- **Lower half of the class spec**: the value of the class of `x` is below `ρ x`, so the
class determines `x` up to the factor `ρ`. -/
theorem scaleValue_lt {ρ : ℝ≥0} (hρ : 1 < ρ) {x : ℝ} (hx : 0 < x) :
    (scaleValue ρ (scaleClass ρ x) : ℝ) < (ρ : ℝ) * x := by
  have hρ' : (1 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  have hρ0 : (0 : ℝ) < (ρ : ℝ) := lt_trans zero_lt_one hρ'
  have hlt : Real.logb (ρ : ℝ) x⁻¹ < ((scaleClass ρ x : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have h1 : (ρ : ℝ) ^ Real.logb (ρ : ℝ) x⁻¹ <
      (ρ : ℝ) ^ (((scaleClass ρ x : ℕ) : ℝ) + 1) :=
    (Real.rpow_lt_rpow_left_iff hρ').2 hlt
  rw [Real.rpow_logb hρ0 (ne_of_gt hρ') (inv_pos.2 hx)] at h1
  have hrw : (ρ : ℝ) ^ (((scaleClass ρ x : ℕ) : ℝ) + 1)
      = (ρ : ℝ) ^ (scaleClass ρ x : ℕ) * (ρ : ℝ) := by
    rw [Real.rpow_add hρ0, Real.rpow_natCast, Real.rpow_one]
  rw [hrw] at h1
  have hpos : (0 : ℝ) < (ρ : ℝ) ^ (scaleClass ρ x : ℕ) := pow_pos hρ0 _
  -- x⁻¹ < A * ρ  ⟹  (A * ρ)⁻¹ < x  ⟹  A⁻¹ < ρ * x
  have h2 : ((ρ : ℝ) ^ (scaleClass ρ x : ℕ) * (ρ : ℝ))⁻¹ < x := by
    have hAρ : (0 : ℝ) < (ρ : ℝ) ^ (scaleClass ρ x : ℕ) * (ρ : ℝ) := by positivity
    exact (inv_lt_comm₀ hx hAρ).1 h1
  rw [coe_scaleValue, inv_pow]
  rw [mul_inv] at h2
  have h3 : ((ρ : ℝ) ^ (scaleClass ρ x : ℕ))⁻¹ * (ρ : ℝ)⁻¹ * (ρ : ℝ) < x * (ρ : ℝ) :=
    mul_lt_mul_of_pos_right h2 hρ0
  have h4 : ((ρ : ℝ) ^ (scaleClass ρ x : ℕ))⁻¹ * (ρ : ℝ)⁻¹ * (ρ : ℝ)
      = ((ρ : ℝ) ^ (scaleClass ρ x : ℕ))⁻¹ := by
    field_simp
  rw [h4, mul_comm] at h3
  exact h3

/-- The class index is antitone: a larger number sits in a smaller class. This is what bounds
the number of classes met by a family of numbers bounded below. -/
theorem scaleClass_le_of_le {ρ : ℝ≥0} (hρ : 1 < ρ) {m x : ℝ} (hm : 0 < m) (hmx : m ≤ x) :
    scaleClass ρ x ≤ scaleClass ρ m := by
  have hρ' : (1 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  have hx : 0 < x := lt_of_lt_of_le hm hmx
  have hinv : x⁻¹ ≤ m⁻¹ := by
    exact inv_anti₀ hm hmx
  exact Nat.floor_le_floor ((Real.logb_le_logb hρ' (inv_pos.2 hx) (inv_pos.2 hm)).2 hinv)


/-! ### The mass pigeonhole over class labels -/

/-- **The pigeonhole.** If a label takes at most `N` values on `bs`, one of its fibres carries
at least `N⁻¹` of the total mass. `N` enters the conclusion as an explicit factor, which is
what makes the loss of the dims class selection writable down. -/
theorem exists_maxMass_fiber {κ β : Type*} [DecidableEq κ]
    (bs : Finset β) (lab : β → κ) (mass : β → ENNReal) (hbs : bs.Nonempty)
    {N : ℕ} (hN : (bs.image lab).card ≤ N) :
    ∃ c ∈ bs.image lab,
      ((N : ENNReal))⁻¹ * ∑ B ∈ bs, mass B ≤ ∑ B ∈ bs with lab B = c, mass B := by
  classical
  have hts : (bs.image lab).Nonempty := hbs.image lab
  obtain ⟨c, hc, hmax⟩ :=
    Finset.exists_max_image (bs.image lab)
      (fun c => ∑ B ∈ bs with lab B = c, mass B) hts
  refine ⟨c, hc, ?_⟩
  have hsum : ∑ c' ∈ bs.image lab, (∑ B ∈ bs with lab B = c', mass B) = ∑ B ∈ bs, mass B :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem lab hi) mass
  have hle : ∑ B ∈ bs, mass B
      ≤ ((bs.image lab).card : ENNReal) * (∑ B ∈ bs with lab B = c, mass B) := by
    rw [← hsum]
    calc ∑ c' ∈ bs.image lab, (∑ B ∈ bs with lab B = c', mass B)
        ≤ (bs.image lab).card • (∑ B ∈ bs with lab B = c, mass B) :=
          Finset.sum_le_card_nsmul _ _ _ hmax
      _ = ((bs.image lab).card : ENNReal) * (∑ B ∈ bs with lab B = c, mass B) := by
          simp [nsmul_eq_mul]
  have hcard : ((bs.image lab).card : ENNReal) ≤ (N : ENNReal) := by exact_mod_cast hN
  have hN0 : (N : ENNReal) ≠ 0 := by
    have : 1 ≤ N := le_trans (Finset.card_pos.2 hts) hN
    exact_mod_cast Nat.one_le_iff_ne_zero.1 this
  calc (N : ENNReal)⁻¹ * ∑ B ∈ bs, mass B
      ≤ (N : ENNReal)⁻¹ * (((bs.image lab).card : ENNReal) *
          ∑ B ∈ bs with lab B = c, mass B) := by
        gcongr
    _ ≤ (N : ENNReal)⁻¹ * ((N : ENNReal) * ∑ B ∈ bs with lab B = c, mass B) := by
        gcongr
    _ = ∑ B ∈ bs with lab B = c, mass B := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hN0 (ENNReal.natCast_ne_top N), one_mul]

/-! ### The smallest `k`-thickness of the bodies of a ball -/

/-- The smallest affine `k`-thickness of the bodies of the ball `B`. Defined through
`Metric.ethickness` (a complete lattice, so `Finset.inf` is total) and read back in `ℝ`. -/
noncomputable def bodyMinThickness {bι ω : Type*} (bodies : bι → Finset ω)
    (Wb : ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (k : ℕ) (B : bι) : ℝ :=
  ((bodies B).inf fun j => ethickness ℝ (Wb j).carrier k).toReal

variable {bι ω : Type*} {bodies : bι → Finset ω}
  {Wb : ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}

/-- `bodyMinThickness` is a lower bound for the `k`-thickness of every body of the ball. -/
theorem bodyMinThickness_le {k : ℕ} {B : bι} {j : ω} (hj : j ∈ bodies B) :
    bodyMinThickness bodies Wb k B ≤ thickness ℝ (Wb j).carrier k := by
  have hbdd : Bornology.IsBounded (Wb j).carrier := (Wb j).isCompact'.isBounded
  have h := Finset.inf_le (f := fun j => ethickness ℝ (Wb j).carrier k) hj
  have := ENNReal.toReal_mono (Metric.ethickness_ne_top (𝕜 := ℝ) hbdd k) h
  rwa [Metric.toReal_ethickness hbdd] at this

/-- `bodyMinThickness` is attained, the ball having at least one body. Attainment is what makes
the within-ball comparability of Lemma 9.2 usable against the *minimum* rather than against an
arbitrary representative — with a representative the two-sided comparison would cost `CF ^ 2`
and the factor-2 window of `bodies_w₁` would be out of reach. -/
theorem exists_bodyMinThickness_eq {k : ℕ} {B : bι} (hne : (bodies B).Nonempty) :
    ∃ j ∈ bodies B, bodyMinThickness bodies Wb k B = thickness ℝ (Wb j).carrier k := by
  obtain ⟨j, hj, hj'⟩ :=
    Finset.exists_mem_eq_inf (bodies B) hne (fun j => ethickness ℝ (Wb j).carrier k)
  refine ⟨j, hj, ?_⟩
  have hbdd : Bornology.IsBounded (Wb j).carrier := (Wb j).isCompact'.isBounded
  rw [bodyMinThickness, hj', Metric.toReal_ethickness hbdd]

/-- `bodyMinThickness` is non-negative. -/
theorem bodyMinThickness_nonneg {k : ℕ} {B : bι} : 0 ≤ bodyMinThickness bodies Wb k B :=
  ENNReal.toReal_nonneg


/-- The thickness-comparison constant of the dims pigeonhole. -/
noncomputable def dimsConstant (C₀ ρ CF : ℝ≥0) : ℝ≥0 := max C₀ (ρ * CF)

/-- The pigeonhole loss of the dims class selection. -/
noncomputable def dimsClassLoss (ρ δ : ℝ≥0) : ℕ := (scaleClass ρ (δ : ℝ) + 1) ^ 2

/-- `C₀ ≤ dimsConstant C₀ ρ CF`. -/
theorem le_dimsConstant_left {C₀ ρ CF : ℝ≥0} : C₀ ≤ dimsConstant C₀ ρ CF := le_max_left _ _

/-- `ρ CF ≤ dimsConstant C₀ ρ CF`. -/
theorem le_dimsConstant_right {C₀ ρ CF : ℝ≥0} : ρ * CF ≤ dimsConstant C₀ ρ CF := le_max_right _ _

/-- `dimsConstant` is at least `1` as soon as `C₀` is. -/
theorem one_le_dimsConstant {C₀ ρ CF : ℝ≥0} (hC₀ : 1 ≤ C₀) : 1 ≤ dimsConstant C₀ ρ CF :=
  le_trans hC₀ le_dimsConstant_left

/-- Division-free rearrangement used to read `Kakeya.HasThicknesses`' lower halves. -/
private theorem invMul_le {C x y : ℝ} (hC : 0 < C) (h : x ≤ C * y) : C⁻¹ * x ≤ y := by
  have h2 := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hC.le)
  rwa [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] at h2

/-- **The dimensions pigeonhole** (GWZ §9.3, `gwz.txt` l.2039-2041).

Input, per ball `B ∈ bs` and per body `j ∈ bodies B` — exactly the shape
`Kakeya.VeryNotSticky.BallDataCore.toBallData` reads, and exactly what
`Kakeya.VeryNotSticky.exists_ballFactoring_core` delivers on one ball:

* `hball` — the bodies sit in the ball of radius `r₁` (its clause `bodies_subset_ball`);
* `hlong`, `hscale` — the longest thickness is at least `C₀⁻¹ r₁` and the shortest is at least
  `δ`, both coming from a segment inside the body (`bodyProfile_of_core`);
* `hsim` — within one ball the whole thickness profile is comparable at `CF` (Lemma 9.2's
  `simDims` clause).

Output: a pair `(a, b)` with `δ ≤ a ≤ b ≤ r₁`, a retained ball set `bs'` carrying at least
the fraction `(dimsClassLoss ρ δ)⁻¹` of the mass, the binder `bodies_thickness` at
`dimsConstant C₀ ρ CF` for every body of every retained ball, and — **under the budget
`ρ CF ≤ 4`** — a common shortest dimension `w₁` with `δ ≤ w₁ ≤ 2 r₁` satisfying the factor-2
window `bodies_w₁`.

The budget is where the `w₁` window is paid for: the retained bodies' shortest thicknesses
span a factor `ρ CF` (the class rounding times the within-ball comparability), while the window
`[w₁/2, 2 w₁]` spans a factor `4`. The thickness profile itself needs no budget.

Only whole *balls* are dropped, never members of a block: that is what keeps the per-block
clauses of the factoring (`frostman`, `biasedDensity`, `bodies_antiClustering`) readable on
exactly Lemma 9.2's blocks, and it is the order GWZ use. -/
theorem exists_dimsClass {bι ω : Type*}
    {ρ δ r₁ C₀ CF : ℝ≥0} (hρ : 1 < ρ) (hδ : 0 < δ) (hr₁ : r₁ ≤ 1)
    (hC₀ : 1 ≤ C₀) (hCF : 1 ≤ CF)
    (bs : Finset bι) (hbs : bs.Nonempty)
    (bodies : bι → Finset ω) (hbodies : ∀ B ∈ bs, (bodies B).Nonempty)
    (Wb : ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (ctr : bι → EuclideanSpace ℝ (Fin 3)) (mass : bι → ENNReal)
    (hball : ∀ B ∈ bs, ∀ j ∈ bodies B, (Wb j).carrier ⊆ closedBall (ctr B) (r₁ : ℝ))
    (hlong : ∀ B ∈ bs, ∀ j ∈ bodies B, (C₀ : ℝ)⁻¹ * (r₁ : ℝ) ≤ thickness ℝ (Wb j).carrier 0)
    (hscale : ∀ B ∈ bs, ∀ j ∈ bodies B, (δ : ℝ) ≤ thickness ℝ (Wb j).carrier 2)
    (hsim : ∀ B ∈ bs, ∀ j ∈ bodies B, ∀ j' ∈ bodies B,
      ethickness ℝ (Wb j).carrier ≤ CF • ethickness ℝ (Wb j').carrier) :
    ∃ (a b w₁ : ℝ≥0) (bs' : Finset bι), bs' ⊆ bs ∧ bs'.Nonempty ∧
      δ ≤ a ∧ a ≤ b ∧ b ≤ r₁ ∧
      (∀ B ∈ bs', ∀ j ∈ bodies B,
        HasThicknesses (Wb j).carrier (dimsConstant C₀ ρ CF) ![(r₁ : ℝ), (b : ℝ), (a : ℝ)]) ∧
      (ρ * CF ≤ 4 →
        δ ≤ w₁ ∧ w₁ ≤ 2 * r₁ ∧
        ∀ B ∈ bs', ∀ j ∈ bodies B,
          thickness ℝ (Wb j).carrier (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1)
              ≤ 2 * (w₁ : ℝ) ∧
            (w₁ : ℝ) ≤ 2 * thickness ℝ (Wb j).carrier
              (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1)) ∧
      ((dimsClassLoss ρ δ : ENNReal))⁻¹ * ∑ B ∈ bs, mass B ≤ ∑ B ∈ bs', mass B := by
  classical
  have hρ0 : (0 : ℝ) < (ρ : ℝ) := lt_trans zero_lt_one (by exact_mod_cast hρ)
  have hρ1 : (1 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ.le
  have hCF1 : (1 : ℝ) ≤ (CF : ℝ) := by exact_mod_cast hCF
  have hr₁1 : (r₁ : ℝ) ≤ 1 := by exact_mod_cast hr₁
  have hδ0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  obtain ⟨m, hm⟩ : ∃ m : ℕ → bι → ℝ, ∀ k B, m k B = bodyMinThickness bodies Wb k B :=
    ⟨_, fun _ _ => rfl⟩
  -- every body sits in the ball, so every thickness is at most `r₁`
  have hthr : ∀ B ∈ bs, ∀ j ∈ bodies B, ∀ k : ℕ, thickness ℝ (Wb j).carrier k ≤ (r₁ : ℝ) :=
    fun B hB j hj k =>
      Metric.thickness_le_of_subset_closedBall (hball B hB j hj) (by positivity) k
  have hδr₁ : (δ : ℝ) ≤ (r₁ : ℝ) := by
    obtain ⟨B, hB⟩ := hbs
    obtain ⟨j, hj⟩ := hbodies B hB
    exact le_trans (hscale B hB j hj) (hthr B hB j hj 2)
  -- the minima over the bodies of a ball
  have hmle : ∀ (k : ℕ) (B : bι), ∀ j ∈ bodies B, m k B ≤ thickness ℝ (Wb j).carrier k := by
    intro k B j hj; rw [hm]; exact bodyMinThickness_le hj
  have hmspread : ∀ (k : ℕ), ∀ B ∈ bs, ∀ j ∈ bodies B,
      thickness ℝ (Wb j).carrier k ≤ (CF : ℝ) * m k B := by
    intro k B hB j hj
    obtain ⟨j₀, hj₀, hj₀eq⟩ := exists_bodyMinThickness_eq (bodies := bodies) (Wb := Wb) (k := k)
      (B := B) (hbodies B hB)
    have h := hsim B hB j hj j₀ hj₀ k
    simp only [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    have hbj : Bornology.IsBounded (Wb j).carrier := (Wb j).isCompact'.isBounded
    have hbj₀ : Bornology.IsBounded (Wb j₀).carrier := (Wb j₀).isCompact'.isBounded
    rw [Metric.ethickness_thickness' hbj, Metric.ethickness_thickness' hbj₀,
      ← ENNReal.ofReal_coe_nnreal (p := CF), ← ENNReal.ofReal_mul (NNReal.coe_nonneg CF)] at h
    have h2 := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (NNReal.coe_nonneg CF) (Metric.thickness_nonneg _ _))).1 h
    rw [hm, hj₀eq]
    exact h2
  have hm2δ : ∀ B ∈ bs, (δ : ℝ) ≤ m 2 B := by
    intro B hB
    obtain ⟨j₀, hj₀, hj₀eq⟩ := exists_bodyMinThickness_eq (bodies := bodies) (Wb := Wb) (k := 2)
      (B := B) (hbodies B hB)
    rw [hm, hj₀eq]
    exact hscale B hB j₀ hj₀
  have hm21 : ∀ B ∈ bs, m 2 B ≤ m 1 B := by
    intro B hB
    obtain ⟨j₁, hj₁, hj₁eq⟩ := exists_bodyMinThickness_eq (bodies := bodies) (Wb := Wb) (k := 1)
      (B := B) (hbodies B hB)
    have hbj₁ : Bornology.IsBounded (Wb j₁).carrier := (Wb j₁).isCompact'.isBounded
    calc m 2 B ≤ thickness ℝ (Wb j₁).carrier 2 := hmle 2 B j₁ hj₁
      _ ≤ thickness ℝ (Wb j₁).carrier 1 := Metric.thickness_antitone hbj₁ (by norm_num)
      _ = m 1 B := by rw [hm, hj₁eq]
  have hm1r : ∀ B ∈ bs, m 1 B ≤ (r₁ : ℝ) := by
    intro B hB
    obtain ⟨j₀, hj₀, hj₀eq⟩ := exists_bodyMinThickness_eq (bodies := bodies) (Wb := Wb) (k := 1)
      (B := B) (hbodies B hB)
    rw [hm, hj₀eq]
    exact hthr B hB j₀ hj₀ 1
  have hm2r : ∀ B ∈ bs, m 2 B ≤ (r₁ : ℝ) := fun B hB => le_trans (hm21 B hB) (hm1r B hB)
  have hm1δ : ∀ B ∈ bs, (δ : ℝ) ≤ m 1 B := fun B hB => le_trans (hm2δ B hB) (hm21 B hB)
  have hδr₁N : δ ≤ r₁ := by exact_mod_cast hδr₁
  -- the class labels and the pigeonhole over the retained mass
  have hlabmem : ∀ B ∈ bs,
      (scaleClass ρ (m 1 B), scaleClass ρ (m 2 B)) ∈
        (Finset.range (scaleClass ρ (δ : ℝ) + 1)) ×ˢ (Finset.range (scaleClass ρ (δ : ℝ) + 1)) := by
    intro B hB
    simp only [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff]
    exact ⟨scaleClass_le_of_le hρ hδ0 (hm1δ B hB), scaleClass_le_of_le hρ hδ0 (hm2δ B hB)⟩
  have hcard : (bs.image (fun B => (scaleClass ρ (m 1 B), scaleClass ρ (m 2 B)))).card
      ≤ dimsClassLoss ρ δ := by
    have h := Finset.card_le_card (Finset.image_subset_iff.2 hlabmem)
    simpa [dimsClassLoss, Finset.card_product, pow_two] using h
  obtain ⟨c, hc, hmass⟩ :=
    exists_maxMass_fiber bs (fun B => (scaleClass ρ (m 1 B), scaleClass ρ (m 2 B))) mass hbs hcard
  obtain ⟨B₀, hB₀, hB₀c⟩ := Finset.mem_image.1 hc
  set w : ℝ≥0 := scaleValue ρ c.1 with hwdef
  set v : ℝ≥0 := scaleValue ρ c.2 with hvdef
  -- the two class values, read on any ball of the winning class
  have hclass : ∀ B ∈ bs, (scaleClass ρ (m 1 B), scaleClass ρ (m 2 B)) = c →
      m 2 B ≤ (v : ℝ) ∧ (v : ℝ) < (ρ : ℝ) * m 2 B ∧
        m 1 B ≤ (w : ℝ) ∧ (w : ℝ) < (ρ : ℝ) * m 1 B := by
    intro B hB hlab
    have h1 : scaleClass ρ (m 1 B) = c.1 := by rw [← hlab]
    have h2 : scaleClass ρ (m 2 B) = c.2 := by rw [← hlab]
    have hm2pos : 0 < m 2 B := lt_of_lt_of_le hδ0 (hm2δ B hB)
    have hm1pos : 0 < m 1 B := lt_of_lt_of_le hδ0 (hm1δ B hB)
    have hm2one : m 2 B ≤ 1 := le_trans (hm2r B hB) hr₁1
    have hm1one : m 1 B ≤ 1 := le_trans (hm1r B hB) hr₁1
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h := le_scaleValue hρ hm2pos hm2one
      rwa [h2, ← hvdef] at h
    · have h := scaleValue_lt hρ hm2pos
      rwa [h2, ← hvdef] at h
    · have h := le_scaleValue hρ hm1pos hm1one
      rwa [h1, ← hwdef] at h
    · have h := scaleValue_lt hρ hm1pos
      rwa [h1, ← hwdef] at h
  refine ⟨max δ (min v (min w r₁)), max (max δ (min v (min w r₁))) (min r₁ w),
    max δ (CF * v / 2),
    bs.filter (fun B => (scaleClass ρ (m 1 B), scaleClass ρ (m 2 B)) = c),
    Finset.filter_subset _ _, ⟨B₀, Finset.mem_filter.2 ⟨hB₀, hB₀c⟩⟩, le_max_left _ _,
    le_max_left _ _, ?_, ?_, ?_, hmass⟩
  · -- `b ≤ r₁`
    exact max_le (max_le hδr₁N (le_trans (min_le_right _ _) (min_le_right _ _)))
      (min_le_left _ _)
  · -- the thickness profile of every body of every retained ball
    intro B hB' j hj
    have hB : B ∈ bs := (Finset.mem_filter.1 hB').1
    obtain ⟨h2v, hv2, h1w, hw1⟩ := hclass B hB ((Finset.mem_filter.1 hB').2)
    have hbj : Bornology.IsBounded (Wb j).carrier := (Wb j).isCompact'.isBounded
    have ht21 : thickness ℝ (Wb j).carrier 2 ≤ thickness ℝ (Wb j).carrier 1 :=
      Metric.thickness_antitone hbj (by norm_num)
    have ht2m := hmle 2 B j hj
    have ht1m := hmle 1 B j hj
    have ht2sp := hmspread 2 B hB j hj
    have ht1sp := hmspread 1 B hB j hj
    have ht2δ := hscale B hB j hj
    have ht2n : 0 ≤ thickness ℝ (Wb j).carrier 2 := Metric.thickness_nonneg _ _
    have ht1n : 0 ≤ thickness ℝ (Wb j).carrier 1 := Metric.thickness_nonneg _ _
    have hCF0 : (0 : ℝ) ≤ (CF : ℝ) := NNReal.coe_nonneg CF
    have hR0 : (0 : ℝ) ≤ (r₁ : ℝ) := NNReal.coe_nonneg r₁
    have hca : ((max δ (min v (min w r₁)) : ℝ≥0) : ℝ)
        = max (δ : ℝ) (min (v : ℝ) (min (w : ℝ) (r₁ : ℝ))) := by push_cast; ring_nf
    have hcb : ((max (max δ (min v (min w r₁))) (min r₁ w) : ℝ≥0) : ℝ)
        = max (max (δ : ℝ) (min (v : ℝ) (min (w : ℝ) (r₁ : ℝ)))) (min (r₁ : ℝ) (w : ℝ)) := by
      push_cast; ring_nf
    -- the constant
    have honeC : (1 : ℝ) ≤ ((dimsConstant C₀ ρ CF : ℝ≥0) : ℝ) := by
      have h := NNReal.coe_le_coe.2 (one_le_dimsConstant (C₀ := C₀) (ρ := ρ) (CF := CF) hC₀)
      simpa using h
    have hC0 : (0 : ℝ) < ((dimsConstant C₀ ρ CF : ℝ≥0) : ℝ) := lt_of_lt_of_le zero_lt_one honeC
    have hρCFC : (ρ : ℝ) * (CF : ℝ) ≤ ((dimsConstant C₀ ρ CF : ℝ≥0) : ℝ) := by
      have h := NNReal.coe_le_coe.2 (le_dimsConstant_right (C₀ := C₀) (ρ := ρ) (CF := CF))
      simpa using h
    have hC₀C : (C₀ : ℝ) ≤ ((dimsConstant C₀ ρ CF : ℝ≥0) : ℝ) :=
      NNReal.coe_le_coe.2 le_dimsConstant_left
    have hρC : (ρ : ℝ) ≤ ((dimsConstant C₀ ρ CF : ℝ≥0) : ℝ) := by nlinarith
    -- `m 2 B ≤ a`, `m 1 B ≤ b'`
    have hm2A : m 2 B ≤ min (v : ℝ) (min (w : ℝ) (r₁ : ℝ)) :=
      le_min h2v (le_min (le_trans (hm21 B hB) h1w) (hm2r B hB))
    have hm2a : m 2 B ≤ max (δ : ℝ) (min (v : ℝ) (min (w : ℝ) (r₁ : ℝ))) :=
      le_trans hm2A (le_max_right _ _)
    have hm1B : m 1 B ≤ min (r₁ : ℝ) (w : ℝ) := le_min (hm1r B hB) h1w
    have hAA0 : (0 : ℝ) ≤ max (δ : ℝ) (min (v : ℝ) (min (w : ℝ) (r₁ : ℝ))) :=
      le_trans (NNReal.coe_nonneg δ) (le_max_left _ _)
    have hBB0 : (0 : ℝ)
        ≤ max (max (δ : ℝ) (min (v : ℝ) (min (w : ℝ) (r₁ : ℝ)))) (min (r₁ : ℝ) (w : ℝ)) :=
      le_trans hAA0 (le_max_left _ _)
    -- the four core comparisons, at the ratio `ρ` and at `ρ · CF`
    have hav : max (δ : ℝ) (min (v : ℝ) (min (w : ℝ) (r₁ : ℝ)))
        ≤ (ρ : ℝ) * thickness ℝ (Wb j).carrier 2 := by
      refine max_le ?_ ?_
      · nlinarith
      · calc min (v : ℝ) (min (w : ℝ) (r₁ : ℝ)) ≤ (v : ℝ) := min_le_left _ _
          _ ≤ (ρ : ℝ) * m 2 B := hv2.le
          _ ≤ (ρ : ℝ) * thickness ℝ (Wb j).carrier 2 :=
              mul_le_mul_of_nonneg_left ht2m hρ0.le
    have hvρa : (v : ℝ) ≤ (ρ : ℝ) * max (δ : ℝ) (min (v : ℝ) (min (w : ℝ) (r₁ : ℝ))) :=
      le_trans hv2.le (mul_le_mul_of_nonneg_left hm2a hρ0.le)
    have hva : thickness ℝ (Wb j).carrier 2
        ≤ (ρ : ℝ) * (CF : ℝ) * max (δ : ℝ) (min (v : ℝ) (min (w : ℝ) (r₁ : ℝ))) := by
      calc thickness ℝ (Wb j).carrier 2 ≤ (CF : ℝ) * m 2 B := ht2sp
        _ ≤ (CF : ℝ) * (v : ℝ) := mul_le_mul_of_nonneg_left h2v hCF0
        _ ≤ (CF : ℝ) * ((ρ : ℝ) * max (δ : ℝ) (min (v : ℝ) (min (w : ℝ) (r₁ : ℝ)))) :=
            mul_le_mul_of_nonneg_left hvρa hCF0
        _ = (ρ : ℝ) * (CF : ℝ) * max (δ : ℝ) (min (v : ℝ) (min (w : ℝ) (r₁ : ℝ))) := by ring
    have hbw : max (max (δ : ℝ) (min (v : ℝ) (min (w : ℝ) (r₁ : ℝ)))) (min (r₁ : ℝ) (w : ℝ))
        ≤ (ρ : ℝ) * thickness ℝ (Wb j).carrier 1 := by
      refine max_le (le_trans hav (mul_le_mul_of_nonneg_left ht21 hρ0.le)) ?_
      calc min (r₁ : ℝ) (w : ℝ) ≤ (w : ℝ) := min_le_right _ _
        _ ≤ (ρ : ℝ) * m 1 B := hw1.le
        _ ≤ (ρ : ℝ) * thickness ℝ (Wb j).carrier 1 := mul_le_mul_of_nonneg_left ht1m hρ0.le
    have hwρb : (w : ℝ)
        ≤ (ρ : ℝ) *
          max (max (δ : ℝ) (min (v : ℝ) (min (w : ℝ) (r₁ : ℝ)))) (min (r₁ : ℝ) (w : ℝ)) :=
      le_trans hw1.le
        (mul_le_mul_of_nonneg_left (le_trans hm1B (le_max_right _ _)) hρ0.le)
    have hwb : thickness ℝ (Wb j).carrier 1
        ≤ (ρ : ℝ) * (CF : ℝ) *
          max (max (δ : ℝ) (min (v : ℝ) (min (w : ℝ) (r₁ : ℝ)))) (min (r₁ : ℝ) (w : ℝ)) := by
      calc thickness ℝ (Wb j).carrier 1 ≤ (CF : ℝ) * m 1 B := ht1sp
        _ ≤ (CF : ℝ) * (w : ℝ) := mul_le_mul_of_nonneg_left h1w hCF0
        _ ≤ (CF : ℝ) * ((ρ : ℝ) *
              max (max (δ : ℝ) (min (v : ℝ) (min (w : ℝ) (r₁ : ℝ)))) (min (r₁ : ℝ) (w : ℝ))) :=
            mul_le_mul_of_nonneg_left hwρb hCF0
        _ = (ρ : ℝ) * (CF : ℝ) *
              max (max (δ : ℝ) (min (v : ℝ) (min (w : ℝ) (r₁ : ℝ)))) (min (r₁ : ℝ) (w : ℝ)) := by
            ring
    -- assemble `Kakeya.HasThicknesses`
    rw [hcb, hca]
    intro k
    fin_cases k
    · refine ⟨?_, ?_⟩
      · have hC₀0 : (0 : ℝ) < (C₀ : ℝ) := by
          have h : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
          linarith
        exact le_trans
          (mul_le_mul_of_nonneg_right (inv_anti₀ hC₀0 hC₀C) hR0) (hlong B hB j hj)
      · exact le_trans (hthr B hB j hj 0)
          (le_trans (le_of_eq (one_mul _).symm) (mul_le_mul_of_nonneg_right honeC hR0))
    · refine ⟨?_, ?_⟩
      · exact invMul_le hC0 (le_trans hbw (mul_le_mul_of_nonneg_right hρC ht1n))
      · exact le_trans hwb (mul_le_mul_of_nonneg_right hρCFC hBB0)
    · refine ⟨?_, ?_⟩
      · exact invMul_le hC0 (le_trans hav (mul_le_mul_of_nonneg_right hρC ht2n))
      · exact le_trans hva (mul_le_mul_of_nonneg_right hρCFC hAA0)
  · -- the `w₁` window, under the budget `ρ · CF ≤ 4`
    intro hbud
    have hbudR : (ρ : ℝ) * (CF : ℝ) ≤ 4 := by
      have h := NNReal.coe_le_coe.2 hbud
      simpa using h
    have hCF0 : (0 : ℝ) ≤ (CF : ℝ) := NNReal.coe_nonneg CF
    have hR0 : (0 : ℝ) ≤ (r₁ : ℝ) := NNReal.coe_nonneg r₁
    obtain ⟨h2v₀, hv₀, _, _⟩ := hclass B₀ hB₀ hB₀c
    refine ⟨le_max_left _ _, ?_, ?_⟩
    · -- `w₁ ≤ 2 r₁`
      rw [← NNReal.coe_le_coe]
      push_cast
      refine max_le (by linarith) ?_
      have hm2r₀ := hm2r B₀ hB₀
      have h1 : (v : ℝ) ≤ (ρ : ℝ) * (r₁ : ℝ) :=
        le_trans hv₀.le (mul_le_mul_of_nonneg_left hm2r₀ hρ0.le)
      nlinarith
    · intro B hB' j hj
      have hB : B ∈ bs := (Finset.mem_filter.1 hB').1
      obtain ⟨h2v, hv2, _, _⟩ := hclass B hB ((Finset.mem_filter.1 hB').2)
      have hidx : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1 = 2 := by simp
      rw [hidx]
      have ht2sp := hmspread 2 B hB j hj
      have ht2m := hmle 2 B j hj
      have ht2δ := hscale B hB j hj
      have ht2n : 0 ≤ thickness ℝ (Wb j).carrier 2 := Metric.thickness_nonneg _ _
      have hcw : ((max δ (CF * v / 2) : ℝ≥0) : ℝ) = max (δ : ℝ) ((CF : ℝ) * (v : ℝ) / 2) := by
        push_cast; ring_nf
      rw [hcw]
      have hCFv : (CF : ℝ) * (v : ℝ) ≤ (CF : ℝ) * ((ρ : ℝ) * thickness ℝ (Wb j).carrier 2) :=
        mul_le_mul_of_nonneg_left
          (le_trans hv2.le (mul_le_mul_of_nonneg_left ht2m hρ0.le)) hCF0
      refine ⟨?_, max_le (by linarith) ?_⟩
      · have h1 : thickness ℝ (Wb j).carrier 2 ≤ (CF : ℝ) * (v : ℝ) :=
          le_trans ht2sp (mul_le_mul_of_nonneg_left h2v hCF0)
        have h2 : (CF : ℝ) * (v : ℝ) / 2 ≤ max (δ : ℝ) ((CF : ℝ) * (v : ℝ) / 2) :=
          le_max_right _ _
        linarith
      · nlinarith

/-! ### The two profile inputs, from the `BallDataCore` fields -/

/-- **The two profile inputs of `exists_dimsClass`, from the core.** A body containing a segment
inherits the segment's lower thickness bounds:
`Kakeya.VeryNotSticky.BallDataCore.segs_thickness` gives `C₀⁻¹ r₁` at the long end and
`Kakeya.VeryNotSticky.BallDataCore.segs_scale` gives the constant-free `δ` at the short end.

The hypothesis `hinhab` — every body is the block of some retained segment — is a property of
the factoring's partition that `Kakeya.VeryNotSticky.exists_ballFactoring_core` does not
currently expose among its conclusions; it is passed in here rather than assumed away. -/
theorem bodyProfile_of_core (cfg : VeryNotSticky.{u}) (core : BallDataCore cfg)
    {ω : Type u} (bodies : core.bι → Finset ω)
    (Wb : ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (blk : core.σ → ω)
    (hinhab : ∀ B ∈ core.bs, ∀ j ∈ bodies B, ∃ p ∈ core.segs B, blk p = j)
    (hsegs_le : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, (core.Y p).toConvexSpaceBody ≤ Wb (blk p)) :
    (∀ B ∈ core.bs, ∀ j ∈ bodies B,
        (core.C₀ : ℝ)⁻¹ * (cfg.r₁ : ℝ) ≤ thickness ℝ (Wb j).carrier 0) ∧
      (∀ B ∈ core.bs, ∀ j ∈ bodies B, (cfg.δ : ℝ) ≤ thickness ℝ (Wb j).carrier 2) := by
  have hsub : ∀ B ∈ core.bs, ∀ j ∈ bodies B,
      ∃ p ∈ core.segs B, (core.Y p).carrier ⊆ (Wb j).carrier := by
    intro B hB j hj
    obtain ⟨p, hp, hpj⟩ := hinhab B hB j hj
    refine ⟨p, hp, ?_⟩
    have h := hsegs_le B hB p hp
    rw [hpj] at h
    exact h
  constructor
  · intro B hB j hj
    obtain ⟨p, hp, hpsub⟩ := hsub B hB j hj
    have h0 := (core.segs_thickness B hB p hp 0).1
    simp only [Matrix.cons_val_zero, Fin.val_zero] at h0
    exact le_trans h0
      (Metric.thickness_monotone (Wb j).isCompact'.isBounded hpsub 0)
  · intro B hB j hj
    obtain ⟨p, hp, hpsub⟩ := hsub B hB j hj
    have hsc := core.segs_scale B hB p hp
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    have h2 : (cfg.δ : ENNReal) ≤ Metric.ethickness ℝ (core.Y p).carrier 2 := by
      refine le_trans hsc ?_
      rw [Metric.ethickness.scale, hfr]
      exact Finset.inf_le (by norm_num)
    have hbp : Bornology.IsBounded (core.Y p).carrier := by
      have := (core.segs_thickness B hB p hp)
      exact ((core.Y p).toConvexSpaceBody).isCompact'.isBounded
    rw [Metric.ethickness_thickness' hbp, ← ENNReal.ofReal_coe_nnreal (p := cfg.δ)] at h2
    have h3 := (ENNReal.ofReal_le_ofReal_iff (Metric.thickness_nonneg _ _)).1 h2
    exact le_trans h3 (Metric.thickness_monotone (Wb j).isCompact'.isBounded hpsub 2)

/-! ### The dims pigeonhole on a `BallDataCore`, in the shape `withDims` and `toBallData` read -/

/-- **The dimensions pigeonhole on a `BallDataCore`**, at Lemma 9.2's constant
`Kakeya.VeryNotSticky.lemma92Constant cfg.ϱ`. The thickness profile is stated against
`Kakeya.VeryNotSticky.withDims cfg a b hdims`, so it *is* the `bodies_thickness` binder of
`Kakeya.VeryNotSticky.BallDataCore.toBallData` for the transported configuration. -/
theorem exists_dimsClass_core (cfg : VeryNotSticky.{u}) (core : BallDataCore cfg)
    {ρ : ℝ≥0} (hρ : 1 < ρ)
    {ω : Type u} (bodies : core.bι → Finset ω)
    (Wb : ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (blk : core.σ → ω)
    (mass : core.bι → ENNReal)
    (hbodies : ∀ B ∈ core.bs, (bodies B).Nonempty)
    (hinhab : ∀ B ∈ core.bs, ∀ j ∈ bodies B, ∃ p ∈ core.segs B, blk p = j)
    (hsegs_le : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, (core.Y p).toConvexSpaceBody ≤ Wb (blk p))
    (hball : ∀ B ∈ core.bs, ∀ j ∈ bodies B,
      (Wb j).carrier ⊆ closedBall (core.ctr B) (cfg.r₁ : ℝ))
    (hsim : ∀ B ∈ core.bs, ∀ j ∈ bodies B, ∀ j' ∈ bodies B,
      ethickness ℝ (Wb j).carrier ≤ lemma92Constant cfg.ϱ • ethickness ℝ (Wb j').carrier) :
    ∃ (a b w₁ : ℝ≥0) (hdims : cfg.δ ≤ a ∧ a ≤ b ∧ b ≤ cfg.δ ^ cfg.exscal)
      (bs' : Finset core.bι), bs' ⊆ core.bs ∧ bs'.Nonempty ∧
      (∀ B ∈ bs', ∀ j ∈ bodies B,
        HasThicknesses (Wb j).carrier
          (dimsConstant core.C₀ ρ (lemma92Constant cfg.ϱ))
          ![((withDims cfg a b hdims).r₁ : ℝ), ((withDims cfg a b hdims).b : ℝ),
            ((withDims cfg a b hdims).a : ℝ)]) ∧
      (ρ * lemma92Constant cfg.ϱ ≤ 4 →
        cfg.δ ≤ w₁ ∧ w₁ ≤ 2 * cfg.r₁ ∧
        ∀ B ∈ bs', ∀ j ∈ bodies B,
          thickness ℝ (Wb j).carrier (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1)
              ≤ 2 * (w₁ : ℝ) ∧
            (w₁ : ℝ) ≤ 2 * thickness ℝ (Wb j).carrier
              (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1)) ∧
      ((dimsClassLoss ρ cfg.δ : ENNReal))⁻¹ * ∑ B ∈ core.bs, mass B ≤ ∑ B ∈ bs', mass B := by
  obtain ⟨hlong, hscale⟩ := bodyProfile_of_core cfg core bodies Wb blk hinhab hsegs_le
  have hr₁ : cfg.r₁ ≤ 1 := by exact_mod_cast r₁_le_one cfg
  obtain ⟨a, b, w₁, bs', hsub, hne, hδa, hab, hbr, hprof, hw, hmass⟩ :=
    exists_dimsClass (ρ := ρ) (δ := cfg.δ) (r₁ := cfg.r₁) (C₀ := core.C₀)
      (CF := lemma92Constant cfg.ϱ) hρ cfg.hδ hr₁ core.hC₀
      (one_le_lemma92Constant cfg.hϱ.le) core.bs core.bs_nonempty bodies hbodies Wb core.ctr
      mass hball hlong hscale hsim
  exact ⟨a, b, w₁, ⟨hδa, hab, hbr⟩, bs', hsub, hne, hprof, hw, hmass⟩

/-- Tripwire: the profile `exists_dimsClass_core` delivers is byte-exactly the
`bodies_thickness` binder of `Kakeya.VeryNotSticky.BallDataCore.toBallData` read on the
transported configuration `Kakeya.VeryNotSticky.withDims cfg a b h`, at the constant
`dimsConstant`. -/
example (cfg : VeryNotSticky.{u}) (a b : ℝ≥0)
    (h : cfg.δ ≤ a ∧ a ≤ b ∧ b ≤ cfg.δ ^ cfg.exscal) (core : BallDataCore cfg)
    {ω : Type u} (bodies : core.bι → Finset ω)
    (Wb : ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (C : ℝ≥0)
    (hprof : ∀ B ∈ core.bs, ∀ j ∈ bodies B,
      HasThicknesses (Wb j).carrier C
        ![((withDims cfg a b h).r₁ : ℝ), ((withDims cfg a b h).b : ℝ),
          ((withDims cfg a b h).a : ℝ)]) :
    ∀ B ∈ (BallDataCore.withDims cfg a b h core).bs,
      ∀ j ∈ bodies B, HasThicknesses (Wb j).carrier C
        ![((withDims cfg a b h).r₁ : ℝ), ((withDims cfg a b h).b : ℝ),
          ((withDims cfg a b h).a : ℝ)] := hprof

/-! ### The pigeonhole loss is polylogarithmic in `1/δ` -/

/-- A square of a logarithm is eventually below any positive power. -/
theorem polylog_rpow_atTop {ρ : ℝ} (hρ : 1 < ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, (1 + Real.logb ρ x) ^ 2 ≤ x ^ ε := by
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  have hε2 : 0 < ε / 2 := by linarith
  have hlog := isLittleO_log_rpow_atTop (r := ε / 2) hε2
  have hconst : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun x : ℝ => x ^ (ε / 2) := by
    rw [isLittleO_const_left]
    right
    simpa [Real.norm_eq_abs, Function.comp_def] using
      tendsto_abs_atTop_atTop.comp (tendsto_rpow_atTop hε2)
  have hsum : (fun x : ℝ => 1 + Real.logb ρ x) =o[atTop] fun x : ℝ => x ^ (ε / 2) := by
    have : (fun x : ℝ => 1 + Real.logb ρ x)
        = fun x : ℝ => (1 : ℝ) + (Real.log ρ)⁻¹ * Real.log x := by
      funext x; simp [Real.logb, div_eq_inv_mul]
    rw [this]
    exact hconst.add (hlog.const_mul_left _)
  have hb := hsum.bound (by norm_num : (0:ℝ) < 1)
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx1
  have hnn : 0 ≤ 1 + Real.logb ρ x := by
    have : 0 ≤ Real.logb ρ x := Real.logb_nonneg hρ hx1
    linarith
  have hxr : (0 : ℝ) ≤ x ^ (ε / 2) := Real.rpow_nonneg hx0 _
  have h1 : 1 + Real.logb ρ x ≤ x ^ (ε / 2) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg hnn,
      abs_of_nonneg hxr] at hx
    exact hx
  calc (1 + Real.logb ρ x) ^ 2 ≤ (x ^ (ε / 2)) ^ 2 := by
        exact pow_le_pow_left₀ hnn h1 2
    _ = x ^ ε := by
        rw [← Real.rpow_natCast (x ^ (ε / 2)) 2, ← Real.rpow_mul hx0]
        norm_num

/-- The pigeonhole loss in closed form: `(⌊log_ρ (1/δ)⌋₊ + 1) ^ 2 ≤ (1 + log_ρ (1/δ)) ^ 2`. -/
theorem dimsClassLoss_le_polylog {ρ δ : ℝ≥0} (hρ : 1 < ρ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((dimsClassLoss ρ δ : ℕ) : ℝ) ≤ (1 + Real.logb (ρ : ℝ) (δ : ℝ)⁻¹) ^ 2 := by
  have hρR : (1 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hinv : (1 : ℝ) ≤ (δ : ℝ)⁻¹ := by
    rw [le_inv_comm₀ zero_lt_one hδR]; simpa using hδ1R
  have hL0 : 0 ≤ Real.logb (ρ : ℝ) (δ : ℝ)⁻¹ := Real.logb_nonneg hρR hinv
  have hfl : ((scaleClass ρ (δ : ℝ) : ℕ) : ℝ) ≤ Real.logb (ρ : ℝ) (δ : ℝ)⁻¹ :=
    Nat.floor_le hL0
  rw [dimsClassLoss]
  push_cast
  nlinarith

/-- **The pigeonhole loss is absorbable**: being polylogarithmic in `1/δ`, it is eventually
below `δ ^ (-ε)` for every `ε > 0`. This is the form in which the consumers of the working
shading's loss constant read it. -/
theorem eventually_dimsClassLoss_le_rpow {ρ : ℝ≥0} (hρ : 1 < ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ((dimsClassLoss ρ d : ℕ) : ENNReal) ≤ (d : ENNReal) ^ (-ε) := by
  have hρR : (1 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (polylog_rpow_atTop hρR hε)
  have hmax : (0 : ℝ) < max x₀ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have ht0 : (0 : ℝ≥0) < ((max x₀ 1)⁻¹).toNNReal := Real.toNNReal_pos.2 (inv_pos.2 hmax)
  have htc : (((max x₀ 1)⁻¹).toNNReal : ℝ) = (max x₀ 1)⁻¹ :=
    Real.coe_toNNReal _ (le_of_lt (inv_pos.2 hmax))
  filter_upwards [Ioo_mem_nhdsGT ht0] with d hd
  have hd0 : 0 < d := hd.1
  have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hdt : (d : ℝ) < (max x₀ 1)⁻¹ := by
    have h := NNReal.coe_lt_coe.2 hd.2
    rwa [htc] at h
  have hx : max x₀ 1 ≤ ((d : ℝ))⁻¹ := by
    rw [le_inv_comm₀ hmax hd0R]
    exact hdt.le
  have hd1 : d ≤ 1 := by
    have h1 : (d : ℝ) ≤ 1 := by
      have : (max x₀ 1)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        exact Or.inr (le_max_right _ _)
      linarith
    exact_mod_cast h1
  have key := hx₀ ((d : ℝ))⁻¹ (le_trans (le_max_left _ _) hx)
  have henv := dimsClassLoss_le_polylog hρ hd0 hd1
  have hreal : ((dimsClassLoss ρ d : ℕ) : ℝ) ≤ ((d : ℝ))⁻¹ ^ ε := le_trans henv key
  -- transport to `ENNReal`
  have hnn : ((dimsClassLoss ρ d : ℕ) : ℝ≥0) ≤ d ^ (-ε) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_rpow, Real.rpow_neg hd0R.le,
      ← Real.inv_rpow hd0R.le]
    simpa using hreal
  calc ((dimsClassLoss ρ d : ℕ) : ENNReal)
      = ((((dimsClassLoss ρ d : ℕ) : ℝ≥0)) : ENNReal) := by simp
    _ ≤ ((d ^ (-ε) : ℝ≥0) : ENNReal) := by exact_mod_cast hnn
    _ = (d : ENNReal) ^ (-ε) := ENNReal.coe_rpow_of_ne_zero hd0.ne' _

/-! ### The fullness cut: deleting the balls GWZ discard -/

/-- **The heavy-ball cut** (GWZ §9.3, `gwz.txt` l.2029-2032: `𝔅` is the family of balls on which
`λ(𝕋_B, Y_B) ⪆ δ^η`).

Given the fullness of the whole family at `α` — `α ∑_B C B ≤ ∑_B S B`, with `C B` the carrier
mass and `S B` the shade mass of the ball `B` — the balls on which the *per-ball* fullness holds
at `α / 2` carry at least half of the shade mass. The threshold has to drop by a factor `2`
(Markov): on the discarded balls the per-ball fullness is genuinely false, which is why it can
only ever be a property of a *retained* ball set and never a field. -/
theorem exists_heavyBalls {bι : Type*} (bs : Finset bι) (C S : bι → ENNReal)
    {α : ENNReal} (hα : α ≠ ⊤) (hCtop : ∑ B ∈ bs, C B ≠ ⊤)
    (hfull : α * ∑ B ∈ bs, C B ≤ ∑ B ∈ bs, S B) :
    (2 : ENNReal)⁻¹ * ∑ B ∈ bs, S B
      ≤ ∑ B ∈ bs with (2 : ENNReal)⁻¹ * α * C B ≤ S B, S B := by
  classical
  have hsplit :
      (∑ B ∈ bs with (2 : ENNReal)⁻¹ * α * C B ≤ S B, S B)
        + ∑ B ∈ bs with ¬ ((2 : ENNReal)⁻¹ * α * C B ≤ S B), S B = ∑ B ∈ bs, S B :=
    Finset.sum_filter_add_sum_filter_not bs
      (fun B => (2 : ENNReal)⁻¹ * α * C B ≤ S B) S
  have hbad : (∑ B ∈ bs with ¬ ((2 : ENNReal)⁻¹ * α * C B ≤ S B), S B)
      ≤ (2 : ENNReal)⁻¹ * (α * ∑ B ∈ bs, C B) := by
    calc (∑ B ∈ bs with ¬ ((2 : ENNReal)⁻¹ * α * C B ≤ S B), S B)
        ≤ ∑ B ∈ bs with ¬ ((2 : ENNReal)⁻¹ * α * C B ≤ S B), (2 : ENNReal)⁻¹ * α * C B := by
          refine Finset.sum_le_sum ?_
          intro B hB
          exact (not_le.1 (Finset.mem_filter.1 hB).2).le
      _ = (2 : ENNReal)⁻¹ * α * ∑ B ∈ bs with ¬ ((2 : ENNReal)⁻¹ * α * C B ≤ S B), C B := by
          rw [Finset.mul_sum]
      _ ≤ (2 : ENNReal)⁻¹ * α * ∑ B ∈ bs, C B := by
          have hsub : (∑ B ∈ bs with ¬ ((2 : ENNReal)⁻¹ * α * C B ≤ S B), C B)
              ≤ ∑ B ∈ bs, C B :=
            Finset.sum_le_sum_of_subset
              (Finset.filter_subset (fun B => ¬ ((2 : ENNReal)⁻¹ * α * C B ≤ S B)) bs)
          gcongr
      _ = (2 : ENNReal)⁻¹ * (α * ∑ B ∈ bs, C B) := by rw [mul_assoc]
  have hbadtop : (∑ B ∈ bs with ¬ ((2 : ENNReal)⁻¹ * α * C B ≤ S B), S B) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hbad
    exact ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top hα hCtop)
  have hbad2 : (∑ B ∈ bs with ¬ ((2 : ENNReal)⁻¹ * α * C B ≤ S B), S B)
      ≤ (2 : ENNReal)⁻¹ * ∑ B ∈ bs, S B := le_trans hbad (by gcongr)
  by_cases hgt : (∑ B ∈ bs with (2 : ENNReal)⁻¹ * α * C B ≤ S B, S B) = ⊤
  · rw [hgt]; exact le_top
  · have hStop : (∑ B ∈ bs, S B) ≠ ⊤ := by
      rw [← hsplit]
      exact ENNReal.add_ne_top.2 ⟨hgt, hbadtop⟩
    have hhalftop : (2 : ENNReal)⁻¹ * ∑ B ∈ bs, S B ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) hStop
    have hhalves : (2 : ENNReal)⁻¹ * (∑ B ∈ bs, S B) + (2 : ENNReal)⁻¹ * (∑ B ∈ bs, S B)
        = ∑ B ∈ bs, S B := by
      rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
    have hkey : (2 : ENNReal)⁻¹ * (∑ B ∈ bs, S B) + (2 : ENNReal)⁻¹ * (∑ B ∈ bs, S B)
        ≤ (∑ B ∈ bs with (2 : ENNReal)⁻¹ * α * C B ≤ S B, S B)
          + (2 : ENNReal)⁻¹ * ∑ B ∈ bs, S B :=
      calc (2 : ENNReal)⁻¹ * (∑ B ∈ bs, S B) + (2 : ENNReal)⁻¹ * (∑ B ∈ bs, S B)
          = ∑ B ∈ bs, S B := hhalves
        _ = (∑ B ∈ bs with (2 : ENNReal)⁻¹ * α * C B ≤ S B, S B)
              + ∑ B ∈ bs with ¬ ((2 : ENNReal)⁻¹ * α * C B ≤ S B), S B := hsplit.symm
        _ ≤ (∑ B ∈ bs with (2 : ENNReal)⁻¹ * α * C B ≤ S B, S B)
              + (2 : ENNReal)⁻¹ * ∑ B ∈ bs, S B := by gcongr
    exact (ENNReal.add_le_add_iff_right hhalftop).1 hkey

/-- The heavy-ball cut with the threshold written as the consumers read it: the fullness of the
whole family at `4 θ` yields the per-ball fullness at `2 θ` on a ball set carrying half the
shade mass. -/
theorem exists_heavyBalls_at {bι : Type*} (bs : Finset bι) (C S : bι → ENNReal)
    {θ : ENNReal} (hθ : θ ≠ ⊤) (hCtop : ∑ B ∈ bs, C B ≠ ⊤)
    (hfull : 4 * θ * ∑ B ∈ bs, C B ≤ ∑ B ∈ bs, S B) :
    (2 : ENNReal)⁻¹ * ∑ B ∈ bs, S B ≤ ∑ B ∈ bs with 2 * θ * C B ≤ S B, S B := by
  have h4 : (4 : ENNReal) = 2 * 2 := by norm_num
  have hrw : (2 : ENNReal)⁻¹ * (4 * θ) = 2 * θ := by
    rw [h4, ← mul_assoc, ← mul_assoc,
      ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
  have h := exists_heavyBalls bs C S (α := 4 * θ) (ENNReal.mul_ne_top (by simp) hθ) hCtop hfull
  simpa [hrw] using h

/-- **The two ball deletions composed**: the fullness cut first, the dims class second.

This is the order the construction needs, and it is what discharges the per-ball fullness the
Markov tier reads: the fullness cut produces a ball
set on which the per-ball fullness at `2 θ` is *true*, and the dims pigeonhole then deletes
further balls inside it — so the fullness survives, being a per-ball property and the second
deletion being a passage to a subset. Both deletions are on the same mass functional `Sm`, so the
two losses multiply into the single explicit constant

`Cg₂ = 2 * dimsClassLoss ρ δ = 2 (⌊log_ρ (1/δ)⌋₊ + 1) ^ 2`,

`2` from Markov and `(⌊log_ρ (1/δ)⌋₊ + 1) ^ 2` from the two class indices. Nothing here is a
field of any structure: on the balls GWZ discard the per-ball fullness is false. -/
theorem exists_dimsClass_heavy {bι ω : Type*}
    {ρ δ r₁ C₀ CF : ℝ≥0} (hρ : 1 < ρ) (hδ : 0 < δ) (hr₁ : r₁ ≤ 1)
    (hC₀ : 1 ≤ C₀) (hCF : 1 ≤ CF)
    (bs : Finset bι)
    (bodies : bι → Finset ω) (hbodies : ∀ B ∈ bs, (bodies B).Nonempty)
    (Wb : ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (ctr : bι → EuclideanSpace ℝ (Fin 3))
    (Cm Sm : bι → ENNReal) {θ : ENNReal} (hθ : θ ≠ ⊤)
    (hCtop : ∑ B ∈ bs, Cm B ≠ ⊤) (hS0 : (∑ B ∈ bs, Sm B) ≠ 0)
    (hfull : 4 * θ * ∑ B ∈ bs, Cm B ≤ ∑ B ∈ bs, Sm B)
    (hball : ∀ B ∈ bs, ∀ j ∈ bodies B, (Wb j).carrier ⊆ closedBall (ctr B) (r₁ : ℝ))
    (hlong : ∀ B ∈ bs, ∀ j ∈ bodies B, (C₀ : ℝ)⁻¹ * (r₁ : ℝ) ≤ thickness ℝ (Wb j).carrier 0)
    (hscale : ∀ B ∈ bs, ∀ j ∈ bodies B, (δ : ℝ) ≤ thickness ℝ (Wb j).carrier 2)
    (hsim : ∀ B ∈ bs, ∀ j ∈ bodies B, ∀ j' ∈ bodies B,
      ethickness ℝ (Wb j).carrier ≤ CF • ethickness ℝ (Wb j').carrier) :
    ∃ (a b w₁ : ℝ≥0) (bs' : Finset bι), bs' ⊆ bs ∧ bs'.Nonempty ∧
      (∀ B ∈ bs', 2 * θ * Cm B ≤ Sm B) ∧
      δ ≤ a ∧ a ≤ b ∧ b ≤ r₁ ∧
      (∀ B ∈ bs', ∀ j ∈ bodies B,
        HasThicknesses (Wb j).carrier (dimsConstant C₀ ρ CF) ![(r₁ : ℝ), (b : ℝ), (a : ℝ)]) ∧
      (ρ * CF ≤ 4 →
        δ ≤ w₁ ∧ w₁ ≤ 2 * r₁ ∧
        ∀ B ∈ bs', ∀ j ∈ bodies B,
          thickness ℝ (Wb j).carrier (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1)
              ≤ 2 * (w₁ : ℝ) ∧
            (w₁ : ℝ) ≤ 2 * thickness ℝ (Wb j).carrier
              (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1)) ∧
      (2 * (dimsClassLoss ρ δ : ENNReal))⁻¹ * ∑ B ∈ bs, Sm B ≤ ∑ B ∈ bs', Sm B := by
  classical
  have hheavy := exists_heavyBalls_at bs Cm Sm hθ hCtop hfull
  have hhsub : (bs.filter fun B => 2 * θ * Cm B ≤ Sm B) ⊆ bs := Finset.filter_subset _ _
  have hhne : (bs.filter fun B => 2 * θ * Cm B ≤ Sm B).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (bs.filter fun B => 2 * θ * Cm B ≤ Sm B) with hemp | h
    · rw [hemp, Finset.sum_empty, le_zero_iff, mul_eq_zero] at hheavy
      rcases hheavy with h2 | hS
      · exact absurd h2 (by simp)
      · exact absurd hS hS0
    · exact h
  obtain ⟨a, b, w₁, bs', hsub', hne', hδa, hab, hbr, hprof, hw, hmass⟩ :=
    exists_dimsClass hρ hδ hr₁ hC₀ hCF (bs.filter fun B => 2 * θ * Cm B ≤ Sm B) hhne bodies
      (fun B hB => hbodies B (hhsub hB)) Wb ctr Sm
      (fun B hB => hball B (hhsub hB)) (fun B hB => hlong B (hhsub hB))
      (fun B hB => hscale B (hhsub hB)) (fun B hB => hsim B (hhsub hB))
  refine ⟨a, b, w₁, bs', hsub'.trans hhsub, hne', ?_, hδa, hab, hbr, hprof, hw, ?_⟩
  · intro B hB
    exact (Finset.mem_filter.1 (hsub' hB)).2
  · calc (2 * (dimsClassLoss ρ δ : ENNReal))⁻¹ * ∑ B ∈ bs, Sm B
        = (dimsClassLoss ρ δ : ENNReal)⁻¹ * ((2 : ENNReal)⁻¹ * ∑ B ∈ bs, Sm B) := by
          rw [ENNReal.mul_inv (by simp) (by simp)]; ring
      _ ≤ (dimsClassLoss ρ δ : ENNReal)⁻¹ *
            ∑ B ∈ bs with 2 * θ * Cm B ≤ Sm B, Sm B := by gcongr
      _ ≤ ∑ B ∈ bs', Sm B := hmass

/-- Tripwire recording the composition order: any per-ball property of the input ball set of
`exists_dimsClass` survives its deletion, the output ball set being a subset. This is why the
fullness cut must run *before* the dims class and not after. -/
example {bι : Type*} (bs bs' : Finset bι) (hsub : bs' ⊆ bs) (P : bι → Prop)
    (hP : ∀ B ∈ bs, P B) : ∀ B ∈ bs', P B := fun B hB => hP B (hsub hB)

/-! ### Discharging the `w₁` budget at Lemma 9.2's constant -/

/-- **The `w₁` budget is available at the ratio `ρ = 3/2`.** Lemma 9.2's constant is
`Kakeya.VeryNotSticky.lemma92Constant ϱ = 2 * 384 ^ ϱ` (`Metric.volume_comparison.C 3 = 384`),
so `ρ CF ≤ 4` at `ρ = 3/2` amounts to `384 ^ ϱ ≤ 4/3`, i.e. to `384 ≤ (4/3) ^ 21` — a `norm_num`
fact — as soon as `ϱ ≤ 1/21`. Since `Kakeya.VNSUniform.CaseParams.slabBias` reads
`2 ^ 20 * ϱ < exscal`, any admissible parameter set with `exscal ≤ 2 ^ 20 / 21` satisfies it with
room to spare, so the budget is not a restriction on the construction. -/
theorem three_halves_mul_lemma92Constant_le {ϱ : ℝ} (hϱ : ϱ ≤ 1 / 21) :
    (3 / 2 : ℝ≥0) * lemma92Constant ϱ ≤ 4 := by
  have hC : Metric.volume_comparison.C 3 = (384 : ℝ≥0) := by
    norm_num [Metric.volume_comparison.C]
  have h1 : (384 : ℝ≥0) ^ ϱ ≤ (384 : ℝ≥0) ^ (1 / 21 : ℝ) :=
    NNReal.rpow_le_rpow_of_exponent_le (by norm_num) hϱ
  have h2 : 3 * (384 : ℝ≥0) ^ (1 / 21 : ℝ) ≤ 4 := by
    have hpow : ((384 : ℝ≥0) ^ (1 / 21 : ℝ)) ^ (21 : ℕ) = 384 := by
      rw [← NNReal.rpow_natCast _ 21, ← NNReal.rpow_mul]
      norm_num
    have hle : (3 * (384 : ℝ≥0) ^ (1 / 21 : ℝ)) ^ (21 : ℕ) ≤ (4 : ℝ≥0) ^ (21 : ℕ) := by
      rw [mul_pow, hpow]
      norm_num
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hle
  rw [lemma92Constant_eq, hC]
  calc (3 / 2 : ℝ≥0) * (2 * (384 : ℝ≥0) ^ ϱ) = 3 * (384 : ℝ≥0) ^ ϱ := by ring
    _ ≤ 3 * (384 : ℝ≥0) ^ (1 / 21 : ℝ) := by gcongr
    _ ≤ 4 := h2

/-- The ratio `3/2` is admissible for the class construction. -/
theorem one_lt_three_halves : (1 : ℝ≥0) < 3 / 2 := by norm_num

end Kakeya.VeryNotSticky
