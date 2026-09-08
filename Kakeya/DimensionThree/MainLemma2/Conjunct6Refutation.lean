/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.LooseUniformProducer

/-!
# Conjunct 6 of `SideDataObligations`: what the Katz–Tao density field permits

The evidence offered for that is
`Kakeya.LooseUniform.bush_obstruction`: `n ≈ 1/(2ρ_k)` unit `δ`-tubes through a common point
`x`, **all with the same direction**, pairwise in no common exact `ρ_k`-tube, so `n` distinct
exact classes each of size one, while the angular cone at `(x, v)` contains all `n`. The
missing step — never compiled, and flagged as such by  — is that such a
family is *admissible*: that it can be the `s`/`T` of a `Kakeya.VeryNotSticky`.

This file settles that step, and the answer is **negative for the parallel bush**.  The field
that blocks it is `Kakeya.VeryNotSticky.maxDensity_le`, GWZ's `Δ_max(𝕋) ≤ δ^{-η}`:

* `Kakeya.VeryNotSticky.card_cone_le` — in **every** configuration, the members of `cfg.s`
  passing through a point `x` with direction within `θ` of `v` are confined to the `4`-dilate
  of a single `ρ`-tube whenever `2δ + θ ≤ 4ρ`, and `maxDensity_le` then caps their number by
  `coneCardConstant · δ^{-η} · (ρ/δ)²`.
* `Kakeya.VeryNotSticky.card_parallel_le` — at `θ = 0` the containing body is a `δ`-tube, so
  the cap collapses to `coneCardConstant · δ^{-η}`: **a parallel bush in an admissible
  configuration has at most `O(δ^{-η})` members.**  The `n ≈ 1/(2ρ_k) ≈ δ^{-2·exscal}` of the
  cited argument is polynomially larger than that, so the parallel bush is not admissible at
  the size the refutation needs.
* `Kakeya.VeryNotSticky.parallel_bush_forces_delta_large` /
  `Kakeya.VeryNotSticky.not_parallel_bush_family` — with `tube_count` (`|𝕋| ≥ δ^{-1}`) the
  parallel bush is not admissible **at all** below an explicit threshold on `δ`: a bush plus
  boundedly many further tubes cannot even reach the configuration's own cardinality floor.

What this does **not** show is that conjunct 6 is true.  `card_cone_le` at the split scale
(`Kakeya.VeryNotSticky.card_angularFibre_le`) leaves the angular fibre as large as
`δ^{-η}(ρ₂*/δ)²`, which is polynomially above the `Cang ≤ δ^{-η}` conjunct 6 allows; the
geometry that realises it is a bush whose members are spread in **direction** as well as in
axial offset, and `Kakeya.VeryNotSticky.twisted_bush` compiles exactly that configuration —
`n` tubes through `x`, pairwise in no common exact `ρ`-tube (so `n` distinct exact classes,
as `bush_obstruction` gives), all inside the angular cone of radius `ρ₂*` at `(x, v)`, and
with pairwise distinct directions, so that `card_parallel_le` does **not** apply to it.  The
honest statement is therefore: *the family the R18/argument names is refuted by the
compiler; the conclusion it draws is not, and a corrected family exists.*

Nothing here is an `∀ᶠ δ` statement and nothing here discharges or refutes conjunct 6.  No
declaration of `SetupSideData.lean`, `LooseUniform.lean` or `LooseUniformProducer.lean` is
changed; this file only adds.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal RealInnerProductSpace

/-!
## The corrected geometry: a bush that the density cap does **not** kill

`card_nearly_parallel_le` refutes the family the R18/ argument names, not the claim
it draws from it.  A family escaping the cap must have directional spread beyond `2δ`, and one
does exist that keeps every other feature of `Kakeya.LooseUniform.bush_obstruction`: `n` unit
`δ`-tubes through a common point `x`, pairwise in **no** common exact `ρ`-tube (hence `n`
distinct exact classes, each a singleton in the bush), all inside an angular cone of radius
`π n α` about `e₁` (hence all inside one `angularFibre` once `π n α ≤ ρ₂*`), and with
directions pairwise separated by more than `4δ`, so that no unit `v` puts them all inside a
`2δ`-cone.  The axial offsets are `i · sp` and the directions are `√(1 - s²) e₁ + s e₂` at
`s = i · α`: a *twisted* bush.

The admissible parameter window is `4δ < α`, `nα ≤ 1/2`, `2ρ + 2α < sp`, `n·sp ≤ 1/4`, which
at the split scale `ρ ≈ ρ₂*` gives `n ≈ 1/(4ρ₂*)` — the same polynomial size
`bush_obstruction` claims, now compatible with `Δ_max ≤ δ^{-η}` (the `n` tubes then span a
`ρ₂*`-cylinder of volume `≍ ρ₂*²` rather than a `δ`-cylinder of volume `≍ δ²`, so the density
they force is `≍ n δ²/ρ₂*² ≪ 1`; that last comparison is arithmetic on the exponents and is
**not** compiled here).

So this file does not decide conjunct 6.  It decides which family the decision must use.
-/

namespace Kakeya.LooseUniform.Twisted

open Kakeya.LooseUniform Kakeya.LooseUniform.NonVacuity Kakeya.LooseUniform.Producer

/-- `‖a e₁ + b e₂‖² = a² + b²`. -/
lemma norm_comb_sq (a b : ℝ) : ‖a • e₁ + b • e₂‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    inner_e₁_e₂, norm_e₁, norm_e₂]
  simp [Real.norm_eq_abs, sq_abs]

/-- The unit direction at transversal parameter `s`. -/
noncomputable def dir (s : ℝ) : E3 := Real.sqrt (1 - s ^ 2) • e₁ + s • e₂

lemma sqrt_sq_of_abs_le_one {s : ℝ} (hs : |s| ≤ 1) : Real.sqrt (1 - s ^ 2) ^ 2 = 1 - s ^ 2 :=
  Real.sq_sqrt (by nlinarith [abs_le.mp hs, sq_abs s, abs_nonneg s])

lemma norm_dir {s : ℝ} (hs : |s| ≤ 1) : ‖dir s‖ = 1 := by
  have h1 : ‖dir s‖ ^ 2 = 1 := by
    rw [dir, norm_comb_sq, sqrt_sq_of_abs_le_one hs]; ring
  nlinarith [norm_nonneg (dir s), h1]

lemma inner_dir_e₂ (s : ℝ) : ⟪dir s, e₂⟫ = s := by
  rw [dir, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_e₁_e₂,
    real_inner_self_eq_norm_sq, norm_e₂]
  ring

lemma inner_dir_e₁ (s : ℝ) : ⟪dir s, e₁⟫ = Real.sqrt (1 - s ^ 2) := by
  rw [dir, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_e₂_e₁,
    real_inner_self_eq_norm_sq, norm_e₁]
  ring

lemma sqrt_ge_of_abs_le_half {s : ℝ} (hs : |s| ≤ 1 / 2) : (4 : ℝ) / 5 ≤ Real.sqrt (1 - s ^ 2) := by
  have hs2 : s ^ 2 ≤ 1 / 4 := by nlinarith [abs_le.mp hs, sq_abs s]
  have hle : ((4 : ℝ) / 5) ^ 2 ≤ 1 - s ^ 2 := by nlinarith
  have h1 : Real.sqrt (((4 : ℝ) / 5) ^ 2) ≤ Real.sqrt (1 - s ^ 2) := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4 / 5)] at h1

/-- Distinct parameters give directions at chord distance at least `|s - t|`. -/
lemma le_norm_dir_sub_dir (s t : ℝ) : |s - t| ≤ ‖dir s - dir t‖ := by
  have h : ⟪dir s - dir t, e₂⟫ = s - t := by
    rw [inner_sub_left, inner_dir_e₂, inner_dir_e₂]
  calc |s - t| = |⟪dir s - dir t, e₂⟫| := by rw [h]
    _ ≤ ‖dir s - dir t‖ * ‖e₂‖ := abs_real_inner_le_norm _ _
    _ = ‖dir s - dir t‖ := by rw [norm_e₂, mul_one]

/-- …and at chord distance at most `2 |s - t|`, on the parameter range `|·| ≤ 1/2`. -/
lemma norm_dir_sub_dir_le {s t : ℝ} (hs : |s| ≤ 1 / 2) (ht : |t| ≤ 1 / 2) :
    ‖dir s - dir t‖ ≤ 2 * |s - t| := by
  set A := Real.sqrt (1 - s ^ 2) with hA
  set B := Real.sqrt (1 - t ^ 2) with hB
  have hA2 : A ^ 2 = 1 - s ^ 2 := sqrt_sq_of_abs_le_one (hs.trans (by norm_num))
  have hB2 : B ^ 2 = 1 - t ^ 2 := sqrt_sq_of_abs_le_one (ht.trans (by norm_num))
  have hAg : (4 : ℝ) / 5 ≤ A := sqrt_ge_of_abs_le_half hs
  have hBg : (4 : ℝ) / 5 ≤ B := sqrt_ge_of_abs_le_half ht
  have hsq : ‖dir s - dir t‖ ^ 2 = (A - B) ^ 2 + (s - t) ^ 2 := by
    have hz : dir s - dir t = (A - B) • e₁ + (s - t) • e₂ := by
      rw [dir, dir, hA, hB]; module
    rw [hz, norm_comb_sq]
  have hprod : (A - B) * (A + B) = t ^ 2 - s ^ 2 := by nlinarith [hA2, hB2]
  have hts : (t ^ 2 - s ^ 2) ^ 2 ≤ (s - t) ^ 2 := by
    have h1 : (t ^ 2 - s ^ 2) ^ 2 = (s - t) ^ 2 * (t + s) ^ 2 := by ring
    have h2 : (t + s) ^ 2 ≤ 1 := by nlinarith [abs_le.mp hs, abs_le.mp ht]
    nlinarith [sq_nonneg (s - t)]
  have hABsq : (A - B) ^ 2 * (A + B) ^ 2 = (t ^ 2 - s ^ 2) ^ 2 := by
    rw [← mul_pow, hprod]
  have hABg : (1 : ℝ) ≤ (A + B) ^ 2 := by nlinarith
  have hAB : (A - B) ^ 2 ≤ (s - t) ^ 2 := by nlinarith [sq_nonneg (A - B)]
  have hle : ‖dir s - dir t‖ ^ 2 ≤ (2 * |s - t|) ^ 2 := by
    rw [hsq]
    have : (2 * |s - t|) ^ 2 = 4 * (s - t) ^ 2 := by
      rw [mul_pow, sq_abs]; ring
    rw [this]; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hle

/-- Every direction of the family is within chord `2|s|` of `e₁`. -/
lemma norm_dir_sub_e₁_le {s : ℝ} (hs : |s| ≤ 1 / 2) : ‖dir s - e₁‖ ≤ 2 * |s| := by
  have h0 : dir 0 = e₁ := by
    rw [dir]; norm_num
  have := norm_dir_sub_dir_le hs (t := 0) (by norm_num)
  rw [h0] at this
  simpa using this

/-- Two directions of the family are never nearly antipodal. -/
lemma one_le_norm_dir_add_dir {s t : ℝ} (hs : |s| ≤ 1 / 2) (ht : |t| ≤ 1 / 2) :
    1 ≤ ‖dir s + dir t‖ := by
  have h : ⟪dir s + dir t, e₁⟫ = Real.sqrt (1 - s ^ 2) + Real.sqrt (1 - t ^ 2) := by
    rw [inner_add_left, inner_dir_e₁, inner_dir_e₁]
  have hge : (8 : ℝ) / 5 ≤ ⟪dir s + dir t, e₁⟫ := by
    rw [h]; linarith [sqrt_ge_of_abs_le_half hs, sqrt_ge_of_abs_le_half ht]
  calc (1 : ℝ) ≤ ⟪dir s + dir t, e₁⟫ := by linarith
    _ ≤ |⟪dir s + dir t, e₁⟫| := le_abs_self _
    _ ≤ ‖dir s + dir t‖ * ‖e₁‖ := abs_real_inner_le_norm _ _
    _ = ‖dir s + dir t‖ := by rw [norm_e₁, mul_one]

/-- **Two bush tubes with different directions lie in no common exact `ρ`-tube**, once the
axial gap exceeds `2ρ` plus the directional slack.  This is
`Kakeya.LooseUniform.bushTube_not_common` with the parallelism hypothesis removed. -/
lemma bushTube_not_common_dir {δ ρ : NNReal} (x : E3) {u w : E3} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    {t t' : ℝ} (hlt : t ≤ t')
    (hgap : 2 * (ρ : ℝ) + |t' + 1 / 2| * ‖u - w‖ < t' - t) :
    ¬ ∃ W : Tube ρ E3, (bushTube δ x u hu t).toConvexSpaceBody ≤ W.toConvexSpaceBody ∧
        (bushTube δ x w hw t').toConvexSpaceBody ≤ W.toConvexSpaceBody := by
  rintro ⟨W, hW0, hW1⟩
  have hx0 : (bushTube δ x u hu t).x ∈ W.carrier := hW0 (Tube.x_mem_carrier _)
  have hy1 : (bushTube δ x w hw t').y ∈ W.carrier := hW1 (Tube.y_mem_carrier _)
  have hb0 := Tube.carrier_subset_closedBall_midpoint _ W hx0
  have hb1 := Tube.carrier_subset_closedBall_midpoint _ W hy1
  rw [Metric.mem_closedBall] at hb0 hb1
  set a : ℝ := t - 1 / 2 with ha
  set b : ℝ := t' + 1 / 2 with hb
  have hdiff : (bushTube δ x u hu t).x - (bushTube δ x w hw t').y = a • u - b • w := by
    change (x + (t - 1 / 2) • u) - (x + (t' + 1 / 2) • w) = a • u - b • w
    rw [ha, hb]; module
  have hsplit : a • u - b • w = (a - b) • u + b • (u - w) := by module
  have hlow : |a - b| - |b| * ‖u - w‖ ≤ ‖a • u - b • w‖ := by
    have h1 : ‖(a - b) • u‖ = |a - b| := by rw [norm_smul, hu, Real.norm_eq_abs, mul_one]
    have h2 : ‖b • (u - w)‖ = |b| * ‖u - w‖ := by rw [norm_smul, Real.norm_eq_abs]
    have h3 : ‖(a - b) • u‖ - ‖b • (u - w)‖ ≤ ‖(a - b) • u + b • (u - w)‖ := by
      have hx : (a - b) • u = ((a - b) • u + b • (u - w)) - b • (u - w) := by module
      have := norm_sub_le ((a - b) • u + b • (u - w)) (b • (u - w))
      rw [← hx] at this
      linarith
    rw [hsplit, ← h1, ← h2]
    exact h3
  have hd : 1 + (t' - t) - |b| * ‖u - w‖
      ≤ dist (bushTube δ x u hu t).x (bushTube δ x w hw t').y := by
    rw [dist_eq_norm, hdiff]
    have habs : |a - b| = 1 + (t' - t) := by
      rw [ha, hb, abs_of_nonpos (by linarith)]; ring
    linarith [hlow, habs.ge, habs.le]
  have htri := dist_triangle_right (bushTube δ x u hu t).x (bushTube δ x w hw t').y
    (midpoint ℝ W.x W.y)
  linarith

/-- **The twisted bush.** -/
theorem twisted_bush {δ ρ : NNReal} (x : E3) (n : ℕ)
    {α sp : ℝ} (hα : 0 < α) (hαn : (n : ℝ) * α ≤ 1 / 2) (hδα : 4 * (δ : ℝ) < α)
    (hsp : 2 * (ρ : ℝ) + 2 * α < sp) (hn : (n : ℝ) * sp ≤ 1 / 4) :
    ∃ T : Fin n → Tube δ E3,
      (∀ i, x ∈ (T i).carrier) ∧
      (∀ i, NonSlab.lineAngle (T i).direction e₁ ≤ Real.pi * ((n : ℝ) * α)) ∧
      (∀ i j : Fin n, i ≠ j → (T i).direction ≠ (T j).direction) ∧
      (∀ i j : Fin n, i ≠ j → ¬ ∃ W : Tube ρ E3,
        (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody ∧
          (T j).toConvexSpaceBody ≤ W.toConvexSpaceBody) ∧
      (∀ v : E3, ‖v‖ = 1 → 2 ≤ n →
        ¬ (∀ i : Fin n, NonSlab.lineAngle (T i).direction v ≤ 2 * (δ : ℝ))) := by
  have hα0 : (0 : ℝ) ≤ α := hα.le
  have hsp0 : (0 : ℝ) < sp := by
    have : (0 : ℝ) ≤ 2 * (ρ : ℝ) := by positivity
    linarith
  have hs : ∀ i : Fin n, |((i : ℕ) : ℝ) * α| ≤ 1 / 2 := by
    intro i
    have hi : ((i : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt i.isLt)
    calc |((i : ℕ) : ℝ) * α| = ((i : ℕ) : ℝ) * α := abs_of_nonneg (by positivity)
      _ ≤ (n : ℝ) * α := by nlinarith
      _ ≤ 1 / 2 := hαn
  have ht : ∀ i : Fin n, |((i : ℕ) : ℝ) * sp| ≤ 1 / 4 := by
    intro i
    rw [abs_of_nonneg (by positivity)]
    have hi : ((i : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt i.isLt)
    nlinarith
  refine ⟨fun i => bushTube δ x (dir (((i : ℕ) : ℝ) * α)) (norm_dir ((hs i).trans (by norm_num)))
    (((i : ℕ) : ℝ) * sp), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact x_mem_bushTube _ _ _ _ ((ht i).trans (by norm_num))
  · intro i
    rw [bushTube_direction]
    refine (NonSlab.lineAngle_le_pi_div_two_mul_norm_sub
      (norm_dir ((hs i).trans (by norm_num))) norm_e₁).trans ?_
    have h1 : ‖dir (((i : ℕ) : ℝ) * α) - e₁‖ ≤ 2 * |((i : ℕ) : ℝ) * α| :=
      norm_dir_sub_e₁_le (hs i)
    have h2 : |((i : ℕ) : ℝ) * α| ≤ (n : ℝ) * α := by
      rw [abs_of_nonneg (by positivity)]
      have hi : ((i : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt i.isLt)
      nlinarith
    nlinarith [Real.pi_pos, norm_nonneg (dir (((i : ℕ) : ℝ) * α) - e₁),
      abs_nonneg (((i : ℕ) : ℝ) * α)]
  · intro i j hij hdir
    rw [bushTube_direction, bushTube_direction] at hdir
    have h := congrArg (fun z : E3 => (inner ℝ z e₂ : ℝ)) hdir
    simp only [inner_dir_e₂] at h
    have hcast : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := mul_right_cancel₀ hα.ne' h
    exact hij (Fin.ext (by exact_mod_cast hcast))
  · -- no common exact ρ-tube
    have key : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → ¬ ∃ W : Tube ρ E3,
        (bushTube δ x (dir (((i : ℕ) : ℝ) * α)) (norm_dir ((hs i).trans (by norm_num)))
            (((i : ℕ) : ℝ) * sp)).toConvexSpaceBody ≤ W.toConvexSpaceBody ∧
          (bushTube δ x (dir (((j : ℕ) : ℝ) * α)) (norm_dir ((hs j).trans (by norm_num)))
            (((j : ℕ) : ℝ) * sp)).toConvexSpaceBody ≤ W.toConvexSpaceBody := by
      intro i j hij
      have hij1 : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
      refine bushTube_not_common_dir x _ _ (by nlinarith) ?_
      have hb : |((j : ℕ) : ℝ) * sp + 1 / 2| ≤ 3 / 4 := by
        have := ht j
        rw [abs_le] at this ⊢
        constructor <;> linarith [this.1, this.2]
      have hd : ‖dir (((i : ℕ) : ℝ) * α) - dir (((j : ℕ) : ℝ) * α)‖
          ≤ 2 * (((j : ℕ) : ℝ) * α - ((i : ℕ) : ℝ) * α) := by
        have := norm_dir_sub_dir_le (hs i) (hs j)
        rw [abs_of_nonpos (by nlinarith)] at this
        linarith
      have hdnn : (0 : ℝ) ≤ ‖dir (((i : ℕ) : ℝ) * α) - dir (((j : ℕ) : ℝ) * α)‖ := norm_nonneg _
      have hgapm : 2 * (ρ : ℝ) + (3 / 4) * (2 * (((j : ℕ) : ℝ) * α - ((i : ℕ) : ℝ) * α))
          < ((j : ℕ) : ℝ) * sp - ((i : ℕ) : ℝ) * sp := by
        nlinarith [hij1, hα, hsp]
      calc 2 * (ρ : ℝ) + |((j : ℕ) : ℝ) * sp + 1 / 2|
              * ‖dir (((i : ℕ) : ℝ) * α) - dir (((j : ℕ) : ℝ) * α)‖
          ≤ 2 * (ρ : ℝ) + (3 / 4) * (2 * (((j : ℕ) : ℝ) * α - ((i : ℕ) : ℝ) * α)) := by
            have : |((j : ℕ) : ℝ) * sp + 1 / 2|
                * ‖dir (((i : ℕ) : ℝ) * α) - dir (((j : ℕ) : ℝ) * α)‖
                ≤ (3 / 4) * (2 * (((j : ℕ) : ℝ) * α - ((i : ℕ) : ℝ) * α)) := by
              refine mul_le_mul hb hd hdnn (by norm_num)
            linarith
        _ < _ := hgapm
    intro i j hij
    rcases lt_or_gt_of_ne (fun h : (i : ℕ) = (j : ℕ) => hij (Fin.ext h)) with h | h
    · exact key i j h
    · intro ⟨W, hWi, hWj⟩
      exact key j i h ⟨W, hWj, hWi⟩
  · -- the family is in no `2δ`-cone
    intro v hv hn2 hall
    have h0 : (0 : ℕ) < n := by omega
    have h1 : (1 : ℕ) < n := by omega
    set i0 : Fin n := ⟨0, h0⟩
    set i1 : Fin n := ⟨1, h1⟩
    have ha0 := hall i0
    have ha1 := hall i1
    rw [bushTube_direction] at ha0 ha1
    have htri : NonSlab.lineAngle (dir (((i0 : ℕ) : ℝ) * α)) (dir (((i1 : ℕ) : ℝ) * α))
        ≤ 4 * (δ : ℝ) := by
      have := NonSlab.lineAngle_le_add (dir (((i0 : ℕ) : ℝ) * α)) v (dir (((i1 : ℕ) : ℝ) * α))
      have hsym : NonSlab.lineAngle v (dir (((i1 : ℕ) : ℝ) * α))
          = NonSlab.lineAngle (dir (((i1 : ℕ) : ℝ) * α)) v := NonSlab.lineAngle_comm _ _
      rw [hsym] at this
      linarith
    rcases NonSlab.norm_sub_or_norm_add_le_of_lineAngle_le
      (norm_dir ((hs i0).trans (by norm_num))) (norm_dir ((hs i1).trans (by norm_num))) htri
      with hsub | hadd
    · have hge := le_norm_dir_sub_dir (((i0 : ℕ) : ℝ) * α) (((i1 : ℕ) : ℝ) * α)
      have habs : |((i0 : ℕ) : ℝ) * α - ((i1 : ℕ) : ℝ) * α| = α := by
        have h00 : ((i0 : ℕ) : ℝ) = 0 := by simp [i0]
        have h11 : ((i1 : ℕ) : ℝ) = 1 := by simp [i1]
        rw [h00, h11, zero_mul, one_mul, zero_sub, abs_neg, abs_of_nonneg hα0]
      rw [habs] at hge
      linarith
    · have hge := one_le_norm_dir_add_dir (hs i0) (hs i1)
      have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have hδ1 : 4 * (δ : ℝ) < 1 := by nlinarith
      linarith

end Kakeya.LooseUniform.Twisted


namespace Kakeya.VeryNotSticky

universe u

open Kakeya.LooseUniform Kakeya.LooseUniform.NonVacuity

/-! ## The dimensional constant -/

/-- The ambient dimension of Section 9. -/
theorem finrank_E3 : Module.finrank ℝ E3 = 3 := by simp [E3]

/-- The constant of `Kakeya.VeryNotSticky.card_cone_le`: `4³` for the dilation, the tube
volume upper bound over the tube volume lower bound. -/
noncomputable abbrev coneCardConstant : NNReal :=
  64 * Tube.volume_le.C 3 / Tube.le_volume.c 3

theorem coneCardConstant_pos : 0 < coneCardConstant :=
  div_pos (by positivity) (Tube.le_volume.c_pos 3)

theorem coneCardConstant_ne_zero : (coneCardConstant : NNReal) ≠ 0 := coneCardConstant_pos.ne'

/-! ## The two elementary inputs -/

/-- The Katz–Tao density field, in the form used below: the total volume of any subfamily of
`cfg.s` contained in a convex body `K` is at most `δ^{-η} · |K|`. -/
theorem sum_volume_le_of_le_body (cfg : VeryNotSticky.{u}) {t : Finset cfg.ι} (ht : t ⊆ cfg.s)
    (K : ConvexSpaceBody E3) (hK : ∀ i ∈ t, (cfg.T i).toConvexSpaceBody ≤ K) :
    ∑ i ∈ t, volume (cfg.T i).toConvexSpaceBody.carrier
      ≤ (cfg.δ : ENNReal) ^ (-cfg.η) * volume K.carrier := by
  classical
  calc ∑ i ∈ t, volume (cfg.T i).toConvexSpaceBody.carrier
      ≤ maxDensity t (fun i ↦ (cfg.T i).toConvexSpaceBody) * volume K.carrier :=
        sum_volume_le_maxDensity_mul_volume' hK
    _ ≤ maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody) * volume K.carrier := by
        gcongr
        exact maxDensity_mono _ ht
    _ ≤ _ := by
        gcongr
        exact cfg.maxDensity_le

/-- **The cone containment.**  A member of the family through `x` whose direction is within
`θ` of `v` lies in the `4`-dilate of the `ρ`-tube through `x` in the direction `v`, provided
`2δ + θ ≤ 4ρ`.  This is `Kakeya.LooseUniform.le_dilate_of_through_point` at `r = 0`,
`s₀ = 0`, `K' = 4`, with the `lineAngle` hypothesis converted by
`Kakeya.LooseUniform.exists_sign_norm_sub_le_of_lineAngle_le`. -/
theorem cone_le_dilate (cfg : VeryNotSticky.{u}) {ρ : NNReal} {θ : ℝ}
    (x v : E3) (hv : ‖v‖ = 1) {i : cfg.ι}
    (hx : x ∈ (cfg.T i).carrier)
    (hang : NonSlab.lineAngle (cfg.T i).direction v ≤ θ)
    (hrad : 2 * (cfg.δ : ℝ) + θ ≤ 4 * (ρ : ℝ)) :
    (cfg.T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate (bushTube ρ x v hv 0) 4 := by
  obtain ⟨σ, hσ, hσle⟩ :=
    exists_sign_norm_sub_le_of_lineAngle_le (Tube.norm_direction (cfg.T i).toTube) hv hang
  refine le_dilate_of_through_point (bushTube ρ x v hv 0) (K' := 4) (r := 0) (θ := θ)
    (by norm_num) (s₀ := 0) (by norm_num) ?_ (cfg.T i).toTube hx (σ := σ) hσ ?_ (by linarith)
  · rw [bushTube_center]; simp
  · rw [bushTube_direction]; exact hσle

/-! ## The density cap on a subfamily inside a dilated tube -/

/-- **The cardinality cap inside a `4`-dilated `ρ`-tube.**  Every member has volume at least
`c₃ δ²` (`Tube.le_volume`), the dilate has volume at most `64 · C₃ ρ²`
(`Tube.tubeDilateVolume` and `Tube.volume_le`), and `maxDensity_le` compares the two. -/
theorem card_le_of_le_dilate (cfg : VeryNotSticky.{u}) {ρ : NNReal} (hρ1 : ρ ≤ 1)
    {t : Finset cfg.ι} (ht : t ⊆ cfg.s) (V : Tube ρ E3)
    (hV : ∀ i ∈ t, (cfg.T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V 4) :
    (t.card : ENNReal) * (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2)
      ≤ (cfg.δ : ENNReal) ^ (-cfg.η) *
          (64 * (((Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2)) := by
  classical
  have hlow : ∀ i ∈ t, ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2
      ≤ volume (cfg.T i).toConvexSpaceBody.carrier := by
    intro i _
    have := Tube.le_volume (cfg.T i).toTube
    rw [finrank_E3] at this
    simpa using this
  have hsum : (t.card : ENNReal) *
      (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2)
      ≤ ∑ i ∈ t, volume (cfg.T i).toConvexSpaceBody.carrier := by
    calc (t.card : ENNReal) *
          (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2)
        = ∑ _i ∈ t, (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hlow
  have hdil : volume (Kakeya.Tube.dilate V 4).carrier
      ≤ 64 * (((Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2) := by
    rw [Tube.tubeDilateVolume V (show (1:ℝ) < 4 by norm_num)]
    have hvol : volume V.carrier
        ≤ ((Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2 := by
      have := Tube.volume_le hρ1 V
      rw [finrank_E3] at this
      simpa using this
    have hC : ENNReal.ofReal (Tube.tubeDilateVolume.C' (Module.finrank ℝ E3) 4)
        = (64 : ENNReal) := by
      norm_num [Tube.tubeDilateVolume.C', finrank_E3]
    rw [hC]
    gcongr
  exact hsum.trans ((cfg.sum_volume_le_of_le_body ht _ hV).trans (by gcongr))

/-! ## The cap on an angular cone at a point -/

open scoped Classical in
/-- **The cone cap.**  In every admissible configuration, the members of `cfg.s` passing
through a point `x` with direction within `θ` of `v` number at most
`coneCardConstant · δ^{-η} · (ρ/δ)²`, for any `ρ ≤ 1` with `2δ + θ ≤ 4ρ`.

This is stated in the cleared form (`· δ²` on the left, `· ρ²` on the right) so that no
`ENNReal` division appears; `Kakeya.VeryNotSticky.card_parallel_le` is the cancelled
instance at `ρ = δ`. -/
theorem card_cone_le (cfg : VeryNotSticky.{u}) {ρ : NNReal} (hρ1 : ρ ≤ 1) {θ : ℝ}
    (x v : E3) (hv : ‖v‖ = 1) (hrad : 2 * (cfg.δ : ℝ) + θ ≤ 4 * (ρ : ℝ))
    {t : Finset cfg.ι} (ht : t ⊆ cfg.s)
    (hx : ∀ i ∈ t, x ∈ (cfg.T i).carrier)
    (hang : ∀ i ∈ t, NonSlab.lineAngle (cfg.T i).direction v ≤ θ) :
    (t.card : ENNReal) * (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2)
      ≤ (cfg.δ : ENNReal) ^ (-cfg.η) *
          (64 * (((Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2)) :=
  cfg.card_le_of_le_dilate hρ1 ht (bushTube ρ x v hv 0)
    (fun i hi ↦ cfg.cone_le_dilate x v hv (hx i hi) (hang i hi) hrad)

/-- **The parallel bush cap** — the headline.  A subfamily of `cfg.s` all of whose members
pass through a common point `x` with the **same** direction `v` has at most
`coneCardConstant · δ^{-η}` members, in every admissible configuration.

This is `card_cone_le` at `θ = 0`, `ρ = δ`: the containing body is then the `4`-dilate of a
single `δ`-tube, of volume `O(δ²)`, so `maxDensity_le` (`Δ_max ≤ δ^{-η}`) caps the count by
`O(δ^{-η})`.  `Kakeya.LooseUniform.bush_obstruction` produces `n ≈ 1/(2ρ_k)` such tubes; at
the split scale `ρ_k ≈ ρ₂*` that is polynomially larger than `δ^{-η}`, so the configuration
the R18/ argument names does not exist. -/
theorem card_parallel_le (cfg : VeryNotSticky.{u}) (x v : E3) (hv : ‖v‖ = 1)
    {t : Finset cfg.ι} (ht : t ⊆ cfg.s)
    (hx : ∀ i ∈ t, x ∈ (cfg.T i).carrier)
    (hpar : ∀ i ∈ t, (cfg.T i).direction = v) :
    (t.card : ENNReal) ≤ (coneCardConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-cfg.η) := by
  classical
  have hv0 : v ≠ 0 := fun h => by simp [h] at hv
  have hang : ∀ i ∈ t, NonSlab.lineAngle (cfg.T i).direction v ≤ 0 := by
    intro i hi
    rw [hpar i hi, NonSlab.lineAngle_self hv0]
  have hkey := cfg.card_cone_le (ρ := cfg.δ) cfg.hδ1 x v hv (by linarith) ht hx hang
  -- cancel the common `δ²`
  have hδ2ne : ((cfg.δ : ENNReal) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast cfg.hδ.ne')
  have hδ2top : ((cfg.δ : ENNReal) ^ 2) ≠ ⊤ := by
    exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hcancel : (t.card : ENNReal) * ((Tube.le_volume.c 3 : NNReal) : ENNReal)
      ≤ (cfg.δ : ENNReal) ^ (-cfg.η) * (64 * ((Tube.volume_le.C 3 : NNReal) : ENNReal)) := by
    refine (ENNReal.mul_le_mul_iff_left hδ2ne hδ2top).mp ?_
    calc (t.card : ENNReal) * ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2
        = (t.card : ENNReal) *
            (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2) := by ring
      _ ≤ (cfg.δ : ENNReal) ^ (-cfg.η) *
            (64 * (((Tube.volume_le.C 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2)) := hkey
      _ = (cfg.δ : ENNReal) ^ (-cfg.η) * (64 * ((Tube.volume_le.C 3 : NNReal) : ENNReal))
            * (cfg.δ : ENNReal) ^ 2 := by ring
  have hcne : ((Tube.le_volume.c 3 : NNReal) : ENNReal) ≠ 0 := by
    exact_mod_cast (Tube.le_volume.c_pos 3).ne'
  have hctop : ((Tube.le_volume.c 3 : NNReal) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  rw [← ENNReal.le_div_iff_mul_le (Or.inl hcne) (Or.inl hctop)] at hcancel
  refine hcancel.trans_eq ?_
  rw [show ((coneCardConstant : NNReal) : ENNReal)
      = ((64 * Tube.volume_le.C 3 : NNReal) : ENNReal)
        / ((Tube.le_volume.c 3 : NNReal) : ENNReal) by
    rw [coneCardConstant, ENNReal.coe_div (Tube.le_volume.c_pos 3).ne']]
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  push_cast
  ring

/-- **`Kakeya.LooseUniform.bush_obstruction`'s output, read inside a configuration.**  If the
`n` tubes it produces are members of an admissible `cfg` — an injection `e : Fin n → cfg.ι`
into `cfg.s` matching them — then `n ≤ coneCardConstant · δ^{-η}`.

`bush_obstruction` supplies exactly the two hypotheses used here (`∀ i, x ∈ (T i).carrier` and
`∀ i, (T i).direction = V.direction`) and asks for `n ≈ 1/(2ρ_k)`.  At conjunct 6's level
`ρ_k ≈ ρ₂*` and, with the conjunct's own pin `cfg.b = cfg.δ`, `ρ₂* = 2⁷ C₀⁴ δ^{1-exscal}`, so
`1/(2ρ_k) ≈ δ^{-(1-exscal)}` with `exscal < 1/2`: polynomially above the cap.  The named family
is therefore not admissible at the size the argument needs. -/
theorem card_le_of_bush (cfg : VeryNotSticky.{u}) {n : ℕ}
    (e : Fin n → cfg.ι) (hinj : Function.Injective e) (he : ∀ i, e i ∈ cfg.s)
    (x v : E3) (hv : ‖v‖ = 1)
    (hx : ∀ i, x ∈ (cfg.T (e i)).carrier)
    (hpar : ∀ i, (cfg.T (e i)).direction = v) :
    (n : ENNReal) ≤ (coneCardConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-cfg.η) := by
  have hcard : (Finset.univ.map ⟨e, hinj⟩).card = n := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have := cfg.card_parallel_le x v hv (t := Finset.univ.map ⟨e, hinj⟩)
    (by intro i hi; obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi; exact he j)
    (by intro i hi; obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi; exact hx j)
    (by intro i hi; obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi; exact hpar j)
  rwa [hcard] at this

/-! ## Two strengthenings and the general ceiling on conjunct 6's left-hand side -/

/-- **The cap holds for a `2δ`-cone, not just for exact parallels.**  At `ρ = δ` the side
condition of `card_cone_le` is `2δ + θ ≤ 4δ`, so any subfamily through a common point whose
directions lie within angle `2δ` of one line is capped by `coneCardConstant · δ^{-η}`.
`Kakeya.VeryNotSticky.card_parallel_le` is the case `θ = 0`.  A family escaping this cap must
therefore have **directional** spread exceeding `2δ` — which is exactly the feature the
parallel bush of `Kakeya.LooseUniform.bush_obstruction` lacks. -/
theorem card_nearly_parallel_le (cfg : VeryNotSticky.{u}) (x v : E3) (hv : ‖v‖ = 1)
    {t : Finset cfg.ι} (ht : t ⊆ cfg.s)
    (hx : ∀ i ∈ t, x ∈ (cfg.T i).carrier)
    (hang : ∀ i ∈ t, NonSlab.lineAngle (cfg.T i).direction v ≤ 2 * (cfg.δ : ℝ)) :
    (t.card : ENNReal) ≤ (coneCardConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-cfg.η) := by
  classical
  have hkey := cfg.card_cone_le (ρ := cfg.δ) cfg.hδ1 x v hv (by linarith) ht hx hang
  have hδ2ne : ((cfg.δ : ENNReal) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast cfg.hδ.ne')
  have hδ2top : ((cfg.δ : ENNReal) ^ 2) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hcancel : (t.card : ENNReal) * ((Tube.le_volume.c 3 : NNReal) : ENNReal)
      ≤ (cfg.δ : ENNReal) ^ (-cfg.η) * (64 * ((Tube.volume_le.C 3 : NNReal) : ENNReal)) := by
    refine (ENNReal.mul_le_mul_iff_left hδ2ne hδ2top).mp ?_
    calc (t.card : ENNReal) * ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2
        = (t.card : ENNReal) *
            (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2) := by ring
      _ ≤ (cfg.δ : ENNReal) ^ (-cfg.η) *
            (64 * (((Tube.volume_le.C 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2)) := hkey
      _ = (cfg.δ : ENNReal) ^ (-cfg.η) * (64 * ((Tube.volume_le.C 3 : NNReal) : ENNReal))
            * (cfg.δ : ENNReal) ^ 2 := by ring
  have hcne : ((Tube.le_volume.c 3 : NNReal) : ENNReal) ≠ 0 := by
    exact_mod_cast (Tube.le_volume.c_pos 3).ne'
  have hctop : ((Tube.le_volume.c 3 : NNReal) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  rw [← ENNReal.le_div_iff_mul_le (Or.inl hcne) (Or.inl hctop)] at hcancel
  refine hcancel.trans_eq ?_
  rw [show ((coneCardConstant : NNReal) : ENNReal)
      = ((64 * Tube.volume_le.C 3 : NNReal) : ENNReal)
        / ((Tube.le_volume.c 3 : NNReal) : ENNReal) by
    rw [coneCardConstant, ENNReal.coe_div (Tube.le_volume.c_pos 3).ne']]
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  push_cast
  ring

open scoped Classical in
/-- **The general ceiling on conjunct 6's left-hand side.**  At the split scale the angular
fibre `Kakeya.VeryNotSticky.angularFibre x v ρ₂*` — the very set conjunct 6 counts — is capped
by `coneCardConstant · δ^{-η} · (ρ₂*/δ)²` in every admissible configuration (cleared form).

Two readings.  *Upwards*: `maxDensity_le` does **not** by itself give conjunct 6, because the
factor `(ρ₂*/δ)²` is polynomially larger than the `Cang ≤ δ^{-η}` the conjunct allows — so the
present result leaves conjunct 6 open.  *Downwards*: it is the exact budget any refuting family
must respect, and `card_nearly_parallel_le` says the budget is spent entirely on **directional**
spread, of which the parallel bush has none. -/
theorem card_angularFibre_le (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀)
    (hρ1 : cfg.rho2Star C₀ ≤ 1) (x v : E3) (hv : ‖v‖ = 1) :
    ((cfg.angularFibre x v (cfg.rho2Star C₀ : ℝ)).card : ENNReal) *
        (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2)
      ≤ (cfg.δ : ENNReal) ^ (-cfg.η) *
          (64 * (((Tube.volume_le.C 3 : NNReal) : ENNReal)
            * ((cfg.rho2Star C₀ : NNReal) : ENNReal) ^ 2)) := by
  have h4 : 4 * (cfg.δ : ℝ) ≤ (cfg.rho2Star C₀ : ℝ) := cfg.four_mul_delta_le_rho2Star hC₀
  refine cfg.card_cone_le (θ := (cfg.rho2Star C₀ : ℝ)) hρ1 x v hv (by linarith) ?_ ?_ ?_
  · exact Finset.filter_subset _ _
  · intro i hi
    have := (Finset.mem_filter.mp hi).2.1
    exact (cfg.T i).shade_subset this
  · intro i hi
    exact (Finset.mem_filter.mp hi).2.2

/-! ## Consequence for the cardinality floor `tube_count` -/

/-- **A parallel bush plus a remainder cannot meet the configuration's cardinality floor.**
`Kakeya.VeryNotSticky.tube_count` demands `1 ≤ δ|𝕋|`, i.e. `|𝕋| ≥ δ^{-1}`; the parallel part
of `𝕋` is capped at `coneCardConstant · δ^{-η}` by `card_parallel_le`, so the remaining `r`
members of `𝕋` have to make up the difference. -/
theorem parallel_bush_tube_count (cfg : VeryNotSticky.{u}) (x v : E3) (hv : ‖v‖ = 1)
    {t : Finset cfg.ι} (ht : t ⊆ cfg.s)
    (hx : ∀ i ∈ t, x ∈ (cfg.T i).carrier)
    (hpar : ∀ i ∈ t, (cfg.T i).direction = v)
    {r : ℕ} (hr : cfg.s.card ≤ t.card + r) :
    (1 : ENNReal) ≤ (cfg.δ : ENNReal) *
      ((coneCardConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-cfg.η) + (r : ENNReal)) := by
  refine cfg.tube_count.trans ?_
  gcongr
  calc (cfg.s.card : ENNReal) ≤ ((t.card + r : ℕ) : ENNReal) := by exact_mod_cast hr
    _ = (t.card : ENNReal) + (r : ENNReal) := by push_cast; ring
    _ ≤ (coneCardConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-cfg.η) + (r : ENNReal) := by
        gcongr
        exact cfg.card_parallel_le x v hv ht hx hpar

/-- **The whole family cannot be a parallel bush**, quantitatively: if every member of `𝕋`
passes through one point with one direction then `1 ≤ coneCardConstant² · δ`.  In particular
this is impossible for `δ < coneCardConstant⁻²`: below that threshold there is **no**
admissible configuration whose family is a parallel bush.

The hypothesis `η ≤ 1/2` is far weaker than anything `Kakeya.VNSUniform.CaseParams` allows
(`slabDensity : 6η < exscal` with `scale : exscal < 1/2` forces `η < 1/12`). -/
theorem parallel_bush_forces_delta_large (cfg : VeryNotSticky.{u}) (hη : cfg.η ≤ 1 / 2)
    (x v : E3) (hv : ‖v‖ = 1)
    (hx : ∀ i ∈ cfg.s, x ∈ (cfg.T i).carrier)
    (hpar : ∀ i ∈ cfg.s, (cfg.T i).direction = v) :
    (1 : ENNReal) ≤ ((coneCardConstant : ENNReal)) ^ 2 * (cfg.δ : ENNReal) := by
  classical
  have hδ0 : (cfg.δ : ENNReal) ≠ 0 := by exact_mod_cast cfg.hδ.ne'
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1 : (cfg.δ : ENNReal) ≤ 1 := by exact_mod_cast cfg.hδ1
  have hstep : (1 : ENNReal) ≤ (coneCardConstant : ENNReal) * (cfg.δ : ENNReal) ^ (1 - cfg.η) := by
    have h := cfg.parallel_bush_tube_count x v hv (Finset.Subset.refl _) hx hpar
      (r := 0) (by omega)
    simp only [Nat.cast_zero, add_zero] at h
    calc (1 : ENNReal) ≤ (cfg.δ : ENNReal) *
          ((coneCardConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-cfg.η)) := h
      _ = (coneCardConstant : ENNReal)
            * ((cfg.δ : ENNReal) ^ (1 : ℝ) * (cfg.δ : ENNReal) ^ (-cfg.η)) := by
          rw [ENNReal.rpow_one]; ring
      _ = (coneCardConstant : ENNReal) * (cfg.δ : ENNReal) ^ (1 - cfg.η) := by
          rw [← ENNReal.rpow_add _ _ hδ0 hδtop]; ring_nf
  have hsq : (1 : ENNReal) ≤ ((coneCardConstant : ENNReal) * (cfg.δ : ENNReal) ^ (1 - cfg.η)) ^ 2 :=
    one_le_pow₀ hstep
  refine hsq.trans ?_
  have hexp : ((cfg.δ : ENNReal) ^ (1 - cfg.η)) ^ 2 ≤ (cfg.δ : ENNReal) := by
    calc ((cfg.δ : ENNReal) ^ (1 - cfg.η)) ^ 2
        = (cfg.δ : ENNReal) ^ ((1 - cfg.η) + (1 - cfg.η)) := by
          rw [ENNReal.rpow_add _ _ hδ0 hδtop, sq]
      _ ≤ (cfg.δ : ENNReal) ^ (1 : ℝ) :=
          ENNReal.rpow_le_rpow_of_exponent_ge hδ1 (by linarith)
      _ = (cfg.δ : ENNReal) := ENNReal.rpow_one _
  calc ((coneCardConstant : ENNReal) * (cfg.δ : ENNReal) ^ (1 - cfg.η)) ^ 2
      = (coneCardConstant : ENNReal) ^ 2 * ((cfg.δ : ENNReal) ^ (1 - cfg.η)) ^ 2 := by ring
    _ ≤ (coneCardConstant : ENNReal) ^ 2 * (cfg.δ : ENNReal) := by gcongr

/-- **No admissible configuration is a parallel bush, below an explicit threshold on `δ`.**
The threshold is `coneCardConstant² · δ < 1`, i.e. `δ < coneCardConstant⁻²`, with
`coneCardConstant = 64 · 2⁴ / (|B₁|/3) = 3072 / |B₁| = 2304/π` — a fixed dimensional number,
no `∀ᶠ δ` and no unnamed constant. -/
theorem not_parallel_bush_family (cfg : VeryNotSticky.{u}) (hη : cfg.η ≤ 1 / 2)
    (hsmall : ((coneCardConstant : ENNReal)) ^ 2 * (cfg.δ : ENNReal) < 1)
    (x v : E3) (hv : ‖v‖ = 1)
    (hx : ∀ i ∈ cfg.s, x ∈ (cfg.T i).carrier)
    (hpar : ∀ i ∈ cfg.s, (cfg.T i).direction = v) : False :=
  absurd (cfg.parallel_bush_forces_delta_large hη x v hv hx hpar) (not_le.mpr hsmall)

/-! ## The residual comparison `hlow` of the (86) bridge, on a parallel bush -/

/-- **Branching numbers are bounded below on any nonempty class.**  For an exact GWZ
Definition-2.1 hierarchy at constant `C`, `card_class_le` reads `|class| ≤ C · branchingN k`,
so a single nonempty class forces `1 ≤ C · branchingN k`.  This holds for **every** hierarchy
on the family, not only for `cfg.uniform.some.tubeUniform`. -/
theorem one_le_mul_branchingN {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E3}
    {N : ℕ} {C : NNReal} (𝒰 : Tube.UniformTubeSet s T N C) {k : ℕ} (hk : k ≤ N)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet k)
    (hne : (Tube.coverClass s (𝒰.cover.assign k) j).Nonempty) :
    (1 : NNReal) ≤ C * 𝒰.branchingN k := by
  have h1 : (1 : NNReal) ≤ ((Tube.coverClass s (𝒰.cover.assign k) j).card : NNReal) := by
    exact_mod_cast Finset.card_pos.mpr hne
  exact h1.trans (𝒰.card_class_le k hk j hj)

/-- **On a parallel bush, the residual comparison `hlow` of the (86) bridge is a theorem, for
every exact hierarchy.**  The angular count on the left is capped by `card_nearly_parallel_le`
at `coneCardConstant · δ^{-η}`, and the branching number on the right is at least `C⁻¹` by
`one_le_mul_branchingN`; so `hlow` holds at `C₁ = C · coneCardConstant · δ^{-η}`.

The quantification over `𝒰` is universal: the conclusion does not mention
`Kakeya.VeryNotSticky.splitHierarchy`, so it is insensitive to the `Classical.choice` pick at
`SplitInputsProduce.lean:100–110`.  Consequently `hlow` is **not** the clause that fails on a
parallel bush; nothing about conjunct 6 fails there. -/
theorem hlow_of_parallel (cfg : VeryNotSticky.{u}) {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C)
    {k : ℕ} (hk : k ≤ N) {j : cfg.ι} (hj : j ∈ 𝒰.cover.indexSet k)
    (hne : (Tube.coverClass cfg.s (𝒰.cover.assign k) j).Nonempty)
    (x v : E3) (hv : ‖v‖ = 1)
    {t : Finset cfg.ι} (ht : t ⊆ cfg.s)
    (hx : ∀ i ∈ t, x ∈ (cfg.T i).carrier)
    (hang : ∀ i ∈ t, NonSlab.lineAngle (cfg.T i).direction v ≤ 2 * (cfg.δ : ℝ)) :
    (t.card : ENNReal)
      ≤ ((C : ENNReal) * (coneCardConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-cfg.η))
          * ((𝒰.branchingN k : NNReal) : ENNReal) := by
  have hbr : (1 : ENNReal) ≤ (C : ENNReal) * ((𝒰.branchingN k : NNReal) : ENNReal) := by
    have := one_le_mul_branchingN 𝒰 hk hj hne
    exact_mod_cast this
  calc (t.card : ENNReal)
      ≤ (coneCardConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-cfg.η) :=
        cfg.card_nearly_parallel_le x v hv ht hx hang
    _ = (coneCardConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-cfg.η) * 1 := by ring
    _ ≤ (coneCardConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-cfg.η) *
          ((C : ENNReal) * ((𝒰.branchingN k : NNReal) : ENNReal)) := by gcongr
    _ = ((C : ENNReal) * (coneCardConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-cfg.η))
          * ((𝒰.branchingN k : NNReal) : ENNReal) := by ring

end Kakeya.VeryNotSticky
